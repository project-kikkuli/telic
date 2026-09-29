(* telic-core: the native verification engine.

   stdin:  {"modules": [...], "program": {...}, "theory": {...}, "tasks": [...],
            "timeout_ms": N, "jobs": N, "salt": S, "cached": [key, ...]}
   stdout: {"results": [...], "terms": {"sorts": [...], "terms": [...]}}

   VC generation runs on the main domain; obligations are solved on up to
   [jobs] domains, each driving its own z3 process. *)

open Term

(* -- reading terms ---------------------------------------------------------- *)

let read_terms (j : Json.t) : term array =
  let sorts = ref [||] in
  let sl = Json.to_list (Json.member "sorts" j) in
  let sa = Array.make (List.length sl) Int in
  List.iteri
    (fun i enc ->
      sa.(i) <-
        (match enc with
         | Json.List [ Json.String "Array"; ix; e ] -> Array (sa.(Json.to_int ix), sa.(Json.to_int e))
         | Json.List [ Json.String "Rec"; Json.String n; Json.List fs ] -> Rec (n, List.map (function Json.List [ Json.String f; s ] -> (f, sa.(Json.to_int s)) | _ -> failwith "rec field") fs)
         | Json.List [ Json.String "Int" ] -> Int
         | Json.List [ Json.String "Real" ] -> Real
         | Json.List [ Json.String "Bool" ] -> Bool
         | Json.List [ Json.String "Str" ] -> Str
         | Json.List [ Json.String "Opaque" ] -> Opaque
         | Json.List [ Json.String "None" ] -> Unit
         | _ -> failwith ("unknown sort " ^ Json.to_string enc)))
    sl;
  sorts := sa;
  let tl = Json.to_list (Json.member "terms" j) in
  let ta = Array.make (List.length tl) tt in
  let ids xs = Array.of_list (List.map (fun x -> ta.(Json.to_int x)) (Json.to_list xs)) in
  List.iteri
    (fun i enc ->
      ta.(i) <-
        (match enc with
         | Json.List [ Json.String "c"; Json.String n; s ] -> const n !sorts.(Json.to_int s)
         | Json.List [ Json.String "i"; Json.String v ] -> ( match int_of_string_opt v with Some n -> int_ n | None -> mk (Big v) Int)
         | Json.List [ Json.String "r"; Json.String n; Json.String d ] -> (
           match (int_of_string_opt n, int_of_string_opt d) with Some n, Some d -> real (Q.make n d) | _ -> mk (Big (n ^ "/" ^ d)) Real)
         | Json.List [ Json.String "b"; Json.Bool b ] -> bool_ b
         | Json.List [ Json.String "s"; Json.String s ] -> str s
         | Json.List [ Json.String "a"; Json.String op; s; xs ] -> app op (ids xs) !sorts.(Json.to_int s)
         | Json.List [ Json.String "f"; Json.String n; s; xs ] -> fn n (ids xs) !sorts.(Json.to_int s)
         | Json.List [ Json.String "q"; Json.String k; vs; b; ps ] -> quant k (Array.to_list (ids vs)) ta.(Json.to_int b) (List.map ids (Json.to_list ps))
         | _ -> failwith ("unknown term " ^ Json.to_string enc)))
    tl;
  ta

(* -- writing terms (a DAG table) ---------------------------------------------- *)

type writer = { sorts : (sort, int) Hashtbl.t; mutable sl : Json.t list; mutable ns : int; tids : (int, int) Hashtbl.t; mutable tl : Json.t list; mutable nt : int }

let writer () = { sorts = Hashtbl.create 16; sl = []; ns = 0; tids = Hashtbl.create 1024; tl = []; nt = 0 }

let rec wsort w s =
  match Hashtbl.find_opt w.sorts s with
  | Some i -> i
  | None ->
    let enc =
      match s with
      | Array (i, e) -> Json.List [ Json.String "Array"; Json.Int (wsort w i); Json.Int (wsort w e) ]
      | Rec (n, fs) -> Json.List [ Json.String "Rec"; Json.String n; Json.List (List.map (fun (f, fs) -> Json.List [ Json.String f; Json.Int (wsort w fs) ]) fs) ]
      | s -> Json.List [ Json.String (sort_name s) ]
    in
    let i = w.ns in
    Hashtbl.add w.sorts s i;
    w.sl <- enc :: w.sl;
    w.ns <- i + 1;
    i

let rec wterm w (t : term) =
  match Hashtbl.find_opt w.tids t.id with
  | Some i -> i
  | None ->
    let ids xs = Json.List (Array.to_list (Array.map (fun x -> Json.Int (wterm w x)) xs)) in
    let enc =
      match t.node with
      | Const n -> Json.List [ Json.String "c"; Json.String n; Json.Int (wsort w t.sort) ]
      | Num q -> if t.sort = Int then Json.List [ Json.String "i"; Json.String (string_of_int q.n) ] else Json.List [ Json.String "r"; Json.String (string_of_int q.n); Json.String (string_of_int q.d) ]
      | Big s -> (
        match String.index_opt s '/' with
        | Some k -> Json.List [ Json.String "r"; Json.String (String.sub s 0 k); Json.String (String.sub s (k + 1) (String.length s - k - 1)) ]
        | None -> Json.List [ Json.String "i"; Json.String s ])
      | BoolV b -> Json.List [ Json.String "b"; Json.Bool b ]
      | StrV s -> Json.List [ Json.String "s"; Json.String s ]
      | App (op, xs) -> Json.List [ Json.String "a"; Json.String op; Json.Int (wsort w t.sort); ids xs ]
      | Fn (n, xs) -> Json.List [ Json.String "f"; Json.String n; Json.Int (wsort w t.sort); ids xs ]
      | Quant (k, vs, b, ps) -> Json.List [ Json.String "q"; Json.String k; ids vs; Json.Int (wterm w b); Json.List (List.map ids ps) ]
    in
    let i = w.nt in
    Hashtbl.add w.tids t.id i;
    w.tl <- enc :: w.tl;
    w.nt <- i + 1;
    i


(* -- the request ------------------------------------------------------------ *)

let loc_json (l : Ir.loc) = Json.List [ Json.Int l.line; Json.Int l.col; Json.Int l.end_col ]

type job = { ob : Vc.obligation; neg_goal : term; phases : (Smt.fundef list * Smt.axiom list * int) list; probes : (string * Vc.value) list; state_consts : term list }

let solve_job z (jb : job) : Smt.result =
  let t0 = Unix.gettimeofday () in
  let rec go = function
    | [] -> { Smt.status = "unknown"; seconds = Unix.gettimeofday () -. t0; model = []; state = []; reason = "no phases" }
    | (defs, axioms, timeout) :: rest -> (
      let text = Smt.script defs axioms jb.ob.hyps jb.neg_goal in
      (match Sys.getenv_opt "TELIC_CORE_DUMP" with
       | Some dir -> Out_channel.with_open_text (Filename.concat dir (String.map (fun c -> if c = '/' || c = '>' || c = '#' then '_' else c) jb.ob.oid ^ Printf.sprintf ".%d.smt2" timeout)) (fun oc -> output_string oc text)
       | None -> ());
      let ans, err = Smt.check z ~timeout_ms:timeout text in
      match ans with
      | "unsat" -> { status = "proved"; seconds = Unix.gettimeofday () -. t0; model = []; state = []; reason = "" }
      | "sat" ->
        (* inputs: scalars first, then list lengths, then list elements *)
        let too_big = ref false in
        let model =
          List.map
            (fun (name, v) ->
              match v with
              | Vc.T t -> (
                (* an input the obligation never mentions is not in the script: any value will do *)
                match (Smt.value_json t.sort (List.hd (Smt.get_values_raw z [ Smt.term_text t ])), t.sort) with
                | Json.Null, Int -> (name, Json.Int 0)
                | Json.Null, Real -> (name, Json.Assoc [ ("__real__", Json.List [ Json.Int 0; Json.Int 1 ]) ])
                | Json.Null, Bool -> (name, Json.Bool false)
                | Json.Null, Str -> (name, Json.String "")
                | v, _ -> (name, v))
              | Vc.L l ->
                let n = match Smt.get_values_raw z [ Smt.term_text l.len ] with [ v ] -> (match Smt.value_json Int v with Json.Int n -> n | _ -> 0) | _ -> 0 in
                if n > 256 then too_big := true;
                let n = max 0 (min n 256) in
                let arr = Smt.term_text l.arr and off = Smt.term_text l.off in
                let es = List.init n (fun i -> Printf.sprintf "(select %s (+ %s %d))" arr off i) in
                let vals = Smt.get_values_raw z es in
                (name, Json.List (List.map (Smt.value_json (elem_sort l.arr.sort)) vals))
              | Vc.NoneV | Vc.O _ | Vc.D _ -> (name, Json.Null))
            jb.probes
        in
        let state =
          if jb.state_consts = [] then []
          else
            let vals = Smt.get_values_raw z (List.map Smt.term_text jb.state_consts) in
            List.map2 (fun (c : term) v -> ((match c.node with Const n -> n | _ -> "?"), Smt.value_json c.sort v)) jb.state_consts vals
        in
        { status = "refuted"; seconds = Unix.gettimeofday () -. t0; model; state; reason = (if !too_big then "the model's list input is too large to replay" else "") }
      | _ ->
        if rest <> [] then go rest
        else { status = "unknown"; seconds = Unix.gettimeofday () -. t0; model = []; state = []; reason = (if err <> "" then err else Smt.reason_unknown z) })
  in
  go jb.phases

let make_job th timeout (ob : Vc.obligation) =
  let terms_ = ob.hyps @ [ ob.goal ] in
  let with_l = Smt.closure th terms_ ob.exclude true and without = Smt.closure th terms_ ob.exclude false in
  let phases =
    if List.length (snd with_l) = List.length (snd without) then [ (fst with_l, snd with_l, timeout) ]
    else [ (fst without, snd without, max 300 (min 800 (timeout / 10))); (fst with_l, snd with_l, timeout) ]
  in
  let input_consts = List.concat_map (fun (_, v) -> Vc.flatten v) ob.inputs in
  let state_consts =
    List.concat_map consts terms_
    |> List.sort_uniq (fun (a : term) b -> compare (match a.node with Const n -> n | _ -> "") (match b.node with Const n -> n | _ -> ""))
    |> List.filter (fun (c : term) ->
           (not (List.memq c input_consts))
           && (match c.node with Const n -> not (String.contains n '!') | _ -> false)
           && match c.sort with Array _ | Rec _ -> false | _ -> true)
  in
  { ob; neg_goal = not_ ob.goal; phases; probes = ob.inputs; state_consts }

(* A job's cache key: a structural digest of everything the solver sees
   (definitions, axioms, hypotheses, goal) and [salt] (the toolchain), so it
   does not depend on term ids or on the rest of the request. *)
let job_key salt (jb : job) : string =
  let memo = Hashtbl.create 1024 in
  let rec h (t : term) =
    match Hashtbl.find_opt memo t.id with
    | Some d -> d
    | None ->
      let kids xs = String.concat "," (Array.to_list (Array.map h xs)) in
      let node =
        match t.node with
        | Const n -> "c" ^ n
        | Num q -> Printf.sprintf "n%d/%d" q.n q.d
        | Big s -> "B" ^ s
        | BoolV b -> if b then "T" else "F"
        | StrV s -> "s" ^ String.escaped s
        | App (op, xs) -> "a" ^ op ^ "(" ^ kids xs ^ ")"
        | Fn (n, xs) -> "f" ^ n ^ "(" ^ kids xs ^ ")"
        | Quant (k, vs, b, ps) -> "q" ^ k ^ "(" ^ kids vs ^ ")" ^ h b ^ "[" ^ String.concat ";" (List.map kids ps) ^ "]"
      in
      let d = Digest.to_hex (Digest.string (node ^ ":" ^ Smt.sort_smt t.sort)) in
      Hashtbl.add memo t.id d;
      d
  in
  let b = Buffer.create 1024 in
  Buffer.add_string b salt;
  List.iter
    (fun ((defs : Smt.fundef list), (axioms : Smt.axiom list), _) ->
      List.iter (fun (d : Smt.fundef) -> Buffer.add_string b ("\ndef " ^ d.fname ^ "(" ^ String.concat "," (List.map h d.params) ^ ")" ^ Smt.sort_smt d.fsort ^ "=" ^ match d.body with Some x -> h x | None -> "?")) defs;
      List.iter (fun (a : Smt.axiom) -> Buffer.add_string b ("\nax " ^ h a.formula)) axioms)
    jb.phases;
  List.iter (fun x -> Buffer.add_string b ("\nhyp " ^ h x)) jb.ob.hyps;
  Buffer.add_string b ("\ngoal " ^ h jb.neg_goal);
  Digest.to_hex (Digest.string (Buffer.contents b))

(* Solve jobs on up to [jobs_n] domains, each driving its own z3. *)
let debug = Sys.getenv_opt "TELIC_CORE_DEBUG" <> None

let rec solve_parallel jobs_n (jobs_arr : job array) : Smt.result array =
  let t0 = Unix.gettimeofday () in
  let res = solve_parallel_ jobs_n jobs_arr in
  if debug then begin
    let slow = Array.to_list (Array.mapi (fun i (r : Smt.result) -> (r.seconds, jobs_arr.(i).ob.oid, r.status)) res) |> List.sort compare |> List.rev in
    Printf.eprintf "batch: %d jobs in %.2fs; slowest: %s\n%!" (Array.length jobs_arr) (Unix.gettimeofday () -. t0)
      (String.concat ", " (List.filteri (fun i _ -> i < 3) (List.map (fun (s, id, st) -> Printf.sprintf "%s %s %.2fs" id st s) slow)))
  end;
  res

and solve_parallel_ jobs_n (jobs_arr : job array) : Smt.result array =
  let n = Array.length jobs_arr in
  let out = Array.make n None in
  let next = Atomic.make 0 in
  let worker () =
    let z = Smt.spawn () in
    let rec loop () =
      let i = Atomic.fetch_and_add next 1 in
      if i < n then begin
        out.(i) <- Some (try solve_job z jobs_arr.(i) with e -> { Smt.status = "unknown"; seconds = 0.; model = []; state = []; reason = "engine: " ^ Printexc.to_string e });
        loop ()
      end
    in
    loop ();
    Smt.close z
  in
  let k = max 1 (min jobs_n n) in
  let doms = List.init (k - 1) (fun _ -> (Domain.spawn [@alert "-do_not_spawn_domains"] [@alert "-unsafe_multidomain"]) worker) in
  if n > 0 then worker ();
  List.iter Domain.join doms;
  Array.map Option.get out

(* -- inference: Houdini over candidate invariants, then loop variants and
   recursion measures, batch-synchronous across every function: each round
   generates VCs on this domain and solves all candidate obligations at once *)

type itask = {
  ikey : string;
  iinfo : Vc.finfo;
  mutable cands : (int * Ir.clause list) list;
  vcands : (int * Ir.expr list) list;
  mcands : Ir.expr list;
  mutable istatus : string;  (** ok | fallback *)
  mutable why : string;
  mutable variant : (int * int) list;
  mutable measure : int option;
  mutable calls : int;
}

let max_rounds = 8

let infer prog th jobs_n timeout (tasks : itask list) =
  let gen (t : itask) opts = match Vc.run (Vc.make prog t.iinfo opts) with obs -> Ok obs | exception Vc.Vc_error _ -> Error `Vc | exception Vc.Fallback w -> Error (`Fallback w) in
  let fallback t w = t.istatus <- "fallback"; t.why <- w in
  (* 1. Houdini: failing candidates drop out; a function goes round again only if something of it failed *)
  let rec rounds_some r (only : itask list) =
    let only = List.filter (fun t -> t.istatus = "ok" && t.cands <> []) only in
    if r < max_rounds && only <> [] then begin
      let batch =
        List.filter_map
          (fun t ->
            match gen t { Vc.extra_invariants = t.cands; variants = []; measures = [] } with
            | Error `Vc -> t.cands <- []; None
            | Error (`Fallback w) -> fallback t w; None
            | Ok obs -> Some (t, List.filter (fun (o : Vc.obligation) -> (o.kind = "inv.entry" || o.kind = "inv.step") && match o.clause with Some c -> c.inferred | None -> false) obs))
          only
      in
      let jobs = Array.of_list (List.concat_map (fun (_, obs) -> List.map (make_job th timeout) obs) batch) in
      let res = solve_parallel jobs_n jobs in
      let failed = Hashtbl.create 64 in
      Array.iteri (fun i (jb : job) -> if res.(i).status <> "proved" then match jb.ob.clause with Some c -> Hashtbl.replace failed (Obj.repr c) () | None -> ()) jobs;
      let next_round = ref [] in
      List.iter
        (fun (t, obs) ->
          t.calls <- t.calls + List.length obs;
          let bad c = Hashtbl.mem failed (Obj.repr c) in
          if List.exists (fun (_, cs) -> List.exists bad cs) t.cands then begin
            t.cands <- List.filter (fun (_, cs) -> cs <> []) (List.map (fun (l, cs) -> (l, List.filter (fun c -> not (bad c)) cs)) t.cands);
            next_round := t :: !next_round
          end)
        batch;
      rounds_some (r + 1) (List.rev !next_round)
    end
  in
  rounds_some 0 tasks;
  (* 2. loop variants: every (loop, candidate) at once; the first candidate
     (in order) whose obligations all prove wins, and a candidate the
     generator rejects ends the search for that loop *)
  let spec_batch (mk_opts : itask -> int -> Ir.expr -> Vc.options) (select : itask -> int -> Vc.obligation -> bool) (sites : itask -> (int * Ir.expr list) list) (choose : itask -> int -> int -> unit) =
    let entries = ref [] in
    List.iter
      (fun t ->
        if t.istatus = "ok" then
          List.iter
            (fun (line, cs) ->
              let stop = ref false in
              List.iteri
                (fun i cand ->
                  if not !stop then
                    match gen t (mk_opts t line cand) with
                    | Error `Vc -> stop := true; entries := (t, line, i, None) :: !entries
                    | Error (`Fallback w) -> stop := true; fallback t w
                    | Ok obs -> entries := (t, line, i, Some (List.filter (select t line) obs)) :: !entries)
                cs)
            (sites t))
      tasks;
    let entries = List.rev !entries in
    let jobs = Array.of_list (List.concat_map (fun (_, _, _, obs) -> match obs with Some obs -> List.map (make_job th timeout) obs | None -> []) entries) in
    let res = solve_parallel jobs_n jobs in
    let pos = ref 0 in
    let decided = Hashtbl.create 16 in
    List.iter
      (fun (t, line, i, obs) ->
        let k = (t.ikey, line) in
        match obs with
        | None -> Hashtbl.replace decided k ()
        | Some obs ->
          let n = List.length obs in
          let ok = n > 0 && Array.for_all (fun (r : Smt.result) -> r.status = "proved") (Array.sub res !pos n) in
          pos := !pos + n;
          t.calls <- t.calls + n;
          if ok && (not (Hashtbl.mem decided k)) && t.istatus = "ok" then begin
            Hashtbl.replace decided k ();
            choose t line i
          end)
      entries
  in
  spec_batch
    (fun t line cand -> { Vc.extra_invariants = t.cands; variants = [ (line, cand) ]; measures = [] })
    (fun _ line (o : Vc.obligation) -> o.kind = "variant" && o.oloc.line = line)
    (fun t -> t.vcands)
    (fun t line i -> t.variant <- (line, i) :: t.variant);
  (* 3. recursion measures for self-recursive functions *)
  spec_batch
    (fun t _ cand -> { Vc.extra_invariants = t.cands; variants = List.map (fun (l, i) -> (l, List.nth (List.assoc l t.vcands) i)) t.variant; measures = [ (t.ikey, cand) ] })
    (fun _ _ (o : Vc.obligation) -> o.kind = "variant" && o.site = None && (let m = o.message in let rec has i = i + 6 <= String.length m && (String.sub m i 6 = "recurs" || has (i + 1)) in has 0))
    (fun t -> if t.mcands <> [] && t.iinfo.recursive && t.iinfo.fn.decreases = None && t.iinfo.scc = [] then [ (0, t.mcands) ] else [])
    (fun t _ i -> t.measure <- Some i)


let () =
  let input = In_channel.input_all stdin in
  let req = Json.parse input in
  let terms = read_terms (Json.member "theory" req) in
  let th =
    let fundefs = Hashtbl.create 16 in
    List.iter
      (fun d ->
        let name = Json.to_str (Json.member "name" d) in
        let body = match Json.member "body" d with Json.Int i -> Some terms.(i) | _ -> None in
        let params = List.map (fun i -> terms.(Json.to_int i)) (Json.to_list (Json.member "params" d)) in
        let fsort = match body with Some b -> b.sort | None -> Int in
        let fsort = match Json.member "sort" d with Json.Int i -> terms.(i).sort | _ -> fsort in
        Hashtbl.replace fundefs name { Smt.fname = name; params; fsort; body };
        Hashtbl.replace Smt.defined_fns name ())
      (Json.to_list (Json.member "fundefs" (Json.member "theory" req)));
    let axioms =
      List.map
        (fun a ->
          { Smt.aname = Json.to_str (Json.member "name" a); formula = terms.(Json.to_int (Json.member "formula" a)); about = Json.to_str (Json.member "about" a); symbol = (match Json.member "symbol" a with Json.String s -> s | _ -> "") })
        (Json.to_list (Json.member "axioms" (Json.member "theory" req)))
    in
    { Smt.fundefs; axioms }
  in
  let modules = List.map Ir.module_of (Json.to_list (Json.member "modules" req)) in
  let funcs = Hashtbl.create 64 in
  let pinfo = Json.member "program" req in
  List.iter
    (fun (m : Ir.modul) ->
      List.iter
        (fun (f : Ir.func) ->
          let key = m.path ^ "::" ^ f.name in
          let pj = Json.member key pinfo in
          let strs k = List.map Json.to_str (Json.to_list (Json.member k pj)) in
          Hashtbl.replace funcs key
            {
              Vc.key;
              fn = f;
              modpath = m.path;
              mutated = strs "mutated";
              appends = strs "appends";
              definitional = Json.to_bool (Json.member "definitional" pj);
              logic_name = (match Json.member "logic_name" pj with Json.String s -> s | _ -> f.name);
              scc = strs "scc";
              recursive = Json.to_bool (Json.member "recursive" pj);
              resolve = (match Json.member "resolve" pj with Json.Assoc kvs -> List.map (fun (k, v) -> (k, Json.to_str v)) kvs | _ -> []);
            })
        m.functions)
    modules;
  let classes =
    List.map
      (fun c ->
        let opt k = match Json.member k c with Json.String s -> Some s | _ -> None in
        {
          Vc.cname = Json.to_str (Json.member "name" c);
          cmod = Json.to_str (Json.member "module" c);
          cfields = List.map (function Json.List [ Json.String f; t ] -> (f, Ir.ty_of t) | _ -> failwith "class field") (Json.to_list (Json.member "fields" c));
          cinvs = List.map Ir.clause_of (Json.to_list (Json.member "invariants" c));
          init = opt "init";
          post_init = opt "post_init";
          cbases = (match Json.member "bases" c with Json.List l -> List.map Json.to_str l | _ -> []);
          owner = (match Json.member "owner" c with Json.Assoc kvs -> List.map (fun (f, o) -> (f, Json.to_str o)) kvs | _ -> []);
        })
      (match Json.member "classes" req with Json.List l -> l | _ -> [])
  in
  let resolve_tbl = Hashtbl.create 256 in
  (match Json.member "resolve" req with
   | Json.Assoc mods -> List.iter (fun (m, tbl) -> match tbl with Json.Assoc kvs -> List.iter (fun (n, k) -> Hashtbl.replace resolve_tbl (m, n) (Json.to_str k)) kvs | _ -> ()) mods
   | _ -> ());
  let heap_writes = Hashtbl.create 64 in
  (match Json.member "heap_writes" req with
   | Json.Assoc kvs -> List.iter (fun (k, w) -> match w with Json.Assoc cfs -> Hashtbl.replace heap_writes k (List.map (fun (cf, ts) -> (cf, List.map Json.to_str (Json.to_list ts))) cfs) | _ -> ()) kvs
   | _ -> ());
  let allocates = Hashtbl.create 16 in
  (match Json.member "allocates" req with Json.List l -> List.iter (fun k -> Hashtbl.replace allocates (Json.to_str k) ()) l | _ -> ());
  let def_heap = Hashtbl.create 16 in
  (match Json.member "def_heap" req with Json.Assoc kvs -> List.iter (fun (k, v) -> Hashtbl.replace def_heap k (List.map Json.to_str (Json.to_list v))) kvs | _ -> ());
  let prog = { Vc.funcs; classes; resolve_tbl; heap_writes; allocates; def_heap } in
  let timeout = match Json.member "timeout_ms" req with Json.Int t -> t | _ -> 8000 in
  let jobs_n = match Json.member "jobs" req with Json.Int j when j > 0 -> j | _ -> Domain.recommended_domain_count () in
  if Json.member "mode" req = Json.String "infer" then begin
    let by_line f j = match j with Json.Assoc kvs -> List.map (fun (l, xs) -> (int_of_string l, List.map f (Json.to_list xs))) kvs | _ -> [] in
    let tasks =
      List.map
        (fun t ->
          let key = Json.to_str (Json.member "key" t) in
          {
            ikey = key;
            iinfo = Hashtbl.find funcs key;
            cands = by_line Ir.clause_of (Json.member "invariants" t);
            vcands = by_line Ir.expr_of (Json.member "variants" t);
            mcands = List.map Ir.expr_of (match Json.member "measures" t with Json.List l -> l | _ -> []);
            istatus = "ok";
            why = "";
            variant = [];
            measure = None;
            calls = 0;
          })
        (Json.to_list (Json.member "tasks" req))
    in
    (* remember candidate positions: survivors are reported by index *)
    let original = List.map (fun t -> (t.ikey, t.cands)) tasks in
    infer prog th jobs_n timeout tasks;
    let res =
      List.map
        (fun t ->
          if t.istatus <> "ok" then Json.Assoc [ ("key", Json.String t.ikey); ("status", Json.String t.istatus); ("reason", Json.String t.why) ]
          else begin
            let orig = List.assoc t.ikey original in
            let inv =
              List.map
                (fun (line, cs) ->
                  let all = List.assoc line orig in
                  (string_of_int line, Json.List (List.filter_map (fun c -> Option.map (fun i -> Json.Int i) (List.find_index (fun c' -> c' == c) all)) cs)))
                t.cands
            in
            Json.Assoc
              [
                ("key", Json.String t.ikey);
                ("status", Json.String "ok");
                ("invariants", Json.Assoc inv);
                ("variants", Json.Assoc (List.map (fun (l, i) -> (string_of_int l, Json.Int i)) t.variant));
                ("measure", match t.measure with Some i -> Json.Int i | None -> Json.Null);
                ("solver_calls", Json.Int t.calls);
              ]
          end)
        tasks
    in
    print_string (Json.to_string (Json.Assoc [ ("results", Json.List res) ]));
    exit 0
  end;
  (* 1. VC generation, sequentially *)
  let results = ref [] and all_jobs = ref [] in
  List.iter
    (fun task ->
      let key = Json.to_str (Json.member "key" task) in
      let info = Hashtbl.find funcs key in
      let oj = Json.member "options" task in
      let opts =
        {
          Vc.extra_invariants = (match Json.member "extra_invariants" oj with Json.Assoc kvs -> List.map (fun (l, cs) -> (int_of_string l, List.map Ir.clause_of (Json.to_list cs))) kvs | _ -> []);
          variants = (match Json.member "variants" oj with Json.Assoc kvs -> List.map (fun (l, e) -> (int_of_string l, Ir.expr_of e)) kvs | _ -> []);
          measures = (match Json.member "measures" oj with Json.Assoc kvs -> List.map (fun (k, e) -> (k, Ir.expr_of e)) kvs | _ -> []);
        }
      in
      let g = Vc.make prog info opts in
      match Vc.run g with
      | obs ->
        let jobs =
          List.map (make_job th timeout) obs
        in
        all_jobs := List.rev_append jobs !all_jobs;
        results := (key, `Ok (g, jobs)) :: !results
      | exception Vc.Fallback why -> results := (key, `Fallback why) :: !results
      | exception Vc.Vc_error (msg, loc) -> results := (key, `Error (msg, loc)) :: !results)
    (Json.to_list (Json.member "tasks" req));
  (* 2. solve, in parallel, what the cache has not proved already *)
  let salt = match Json.member "salt" req with Json.String s -> s | _ -> "" in
  let cached = Hashtbl.create 256 in
  (match Json.member "cached" req with Json.List l -> List.iter (fun k -> Hashtbl.replace cached (Json.to_str k) ()) l | _ -> ());
  let key_of = Hashtbl.create 256 in
  let result_of = Hashtbl.create 256 in
  let todo =
    List.filter
      (fun jb ->
        let k = job_key salt jb in
        Hashtbl.replace key_of jb.ob.oid k;
        if Hashtbl.mem cached k then begin
          Hashtbl.replace result_of jb.ob.oid { Smt.status = "proved"; seconds = 0.; model = []; state = []; reason = "cache" };
          false
        end
        else true)
      (List.rev !all_jobs)
  in
  let jobs_arr = Array.of_list todo in
  let solved = solve_parallel jobs_n jobs_arr in
  Array.iteri (fun i jb -> Hashtbl.replace result_of jb.ob.oid solved.(i)) jobs_arr;
  (* 3. answer *)
  let w = writer () in
  let clause_json = function
    | None -> Json.Null
    | Some (c : Ir.clause) -> Json.Assoc [ ("kind", Json.String c.ckind); ("loc", loc_json c.cloc); ("text", Json.String c.text); ("inferred", Json.Bool c.inferred) ]
  in
  let res_json =
    List.rev_map
      (fun (key, r) ->
        match r with
        | `Fallback why -> Json.Assoc [ ("key", Json.String key); ("status", Json.String "fallback"); ("reason", Json.String why) ]
        | `Error (msg, loc) -> Json.Assoc [ ("key", Json.String key); ("status", Json.String "error"); ("reason", Json.String msg); ("loc", loc_json loc) ]
        | `Ok ((g : Vc.gen), jobs) ->
          let obs =
            List.map
              (fun jb ->
                let ob = jb.ob in
                let r = Hashtbl.find result_of ob.oid in
                Json.Assoc
                  [
                    ("id", Json.String ob.oid);
                    ("kind", Json.String ob.kind);
                    ("loc", loc_json ob.oloc);
                    ("site", match ob.site with Some s -> loc_json s | None -> Json.Null);
                    ("message", Json.String ob.message);
                    ("clause", clause_json ob.clause);
                    ("intents", Json.List (List.map (fun s -> Json.String s) ob.intents));
                    ("inferred", Json.Bool ob.inferred);
                    ("deps", Json.List (List.map (fun s -> Json.String s) ob.deps));
                    ("exclude", Json.List (List.map (fun s -> Json.String s) ob.exclude));
                    ("status", Json.String r.status);
                    ("key", Json.String (Hashtbl.find key_of ob.oid));
                    ("seconds", Json.Float r.seconds);
                    ("reason", Json.String r.reason);
                    ("model", Json.Assoc r.model);
                    ("state", Json.Assoc r.state);
                    ("hyps", Json.List (List.map (fun h -> Json.Int (wterm w h)) ob.hyps));
                    ("goal", Json.Int (wterm w ob.goal));
                    ( "inputs",
                      Json.List
                        (List.map
                           (fun (name, v) ->
                             match v with
                             | Vc.T t -> Json.List [ Json.String name; Json.Assoc [ ("t", Json.Int (wterm w t)) ] ]
                             | Vc.L l -> Json.List [ Json.String name; Json.Assoc [ ("list", Json.List [ Json.Int (wterm w l.arr); Json.Int (wterm w l.off); Json.Int (wterm w l.len) ]) ] ]
                             | Vc.NoneV | Vc.O _ | Vc.D _ -> Json.List [ Json.String name; Json.Null ])
                           ob.inputs) );
                  ])
              jobs
          in
          Json.Assoc
            [
              ("key", Json.String key);
              ("status", Json.String "ok");
              ("obligations", Json.List obs);
              ("assumptions", Json.List (List.map (fun (l, t) -> Json.List [ Json.Int l; Json.String t ]) (List.rev g.assumptions)));
              ("deps", Json.List (List.map (fun s -> Json.String s) g.deps));
              ("loop_notes", Json.List (List.map (fun (l, t) -> Json.List [ Json.Int l; Json.String t ]) (List.rev g.loop_notes)));
            ])
      !results
  in
  let answer = Json.Assoc [ ("results", Json.List res_json); ("terms", Json.Assoc [ ("sorts", Json.List (List.rev w.sl)); ("terms", Json.List (List.rev w.tl)) ]) ] in
  print_string (Json.to_string answer)
