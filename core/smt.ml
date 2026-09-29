(* SMT-LIB 2 for z3: theory closure, printing with sharing, a z3 process
   per worker, and model decoding into the JSON values Python expects. *)

open Term

type fundef = { fname : string; params : term list; fsort : sort; body : term option }
type axiom = { aname : string; formula : term; about : string; symbol : string }
type theory = { fundefs : (string, fundef) Hashtbl.t; axioms : axiom list }

(* Definitions and axioms reachable from [terms] (mirrors Theory.closure). *)
let closure th (terms : term list) (exclude : string list) (lemmas : bool) : fundef list * axiom list =
  let need = Hashtbl.create 16 in
  let todo = ref terms in
  let axioms = ref [] and seen_ax = Hashtbl.create 16 in
  while !todo <> [] do
    let t = List.hd !todo in
    todo := List.tl !todo;
    List.iter
      (fun name ->
        if not (Hashtbl.mem need name) then begin
          Hashtbl.add need name ();
          (match Hashtbl.find_opt th.fundefs name with Some { body = Some b; _ } -> todo := b :: !todo | _ -> ());
          List.iter
            (fun ax ->
              if not ((ax.about <> "" && List.mem ax.about exclude) || Hashtbl.mem seen_ax ax.aname) then
                if ax.aname = name ^ "_spec" || (lemmas && ax.symbol = name) then begin
                  Hashtbl.add seen_ax ax.aname ();
                  axioms := ax :: !axioms;
                  todo := ax.formula :: !todo
                end)
            th.axioms
        end)
      (fns t)
  done;
  let names = Hashtbl.fold (fun n () acc -> n :: acc) need [] |> List.sort compare in
  (List.filter_map (fun n -> Hashtbl.find_opt th.fundefs n) names, List.rev !axioms)

(* -- printing ---------------------------------------------------------------- *)

let quote name = "|" ^ String.concat "" (List.map (fun c -> if c = '|' || c = '\\' then "_" else String.make 1 c) (List.init (String.length name) (String.get name))) ^ "|"

(* Every user symbol gets a namespace prefix, so no program name can collide
   with SMT-LIB's own (a user function called abs, a variable called div). *)
let q_const n = quote ("c!" ^ n)
let q_fn n = quote ("f!" ^ n)
let q_rec n = quote ("r!" ^ n)
let q_mk n = quote ("mk!" ^ n)
let q_field r f = quote ("fld!" ^ r ^ "." ^ f)

let rec sort_smt = function
  | Int | Unit -> "Int"
  | Real -> "Real"
  | Bool -> "Bool"
  | Str -> "String"
  | Opaque -> "Opaque"
  | Array (i, e) -> Printf.sprintf "(Array %s %s)" (sort_smt i) (sort_smt e)
  | Rec (n, _) -> q_rec n

let str_lit s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (fun c ->
      if c = '"' then Buffer.add_string b "\"\""
      else if Char.code c < 32 || Char.code c > 126 || c = '\\' then Buffer.add_string b (Printf.sprintf "\\u{%x}" (Char.code c))
      else Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b

let num_smt sort (q : Q.t) =
  let pos n = if sort = Real then Printf.sprintf "%d.0" n else string_of_int n in
  let body n = if q.d = 1 then pos n else Printf.sprintf "(/ %d.0 %d.0)" n q.d in
  if q.n < 0 then Printf.sprintf "(- %s)" (body (-q.n)) else body q.n

type printer = { buf : Buffer.t; names : (int, string) Hashtbl.t  (** shared subterms defined up front *) }

let op_smt op =
  match op with
  | "add" -> "+" | "sub" -> "-" | "mul" -> "*" | "neg" -> "-" | "rdiv" -> "/" | "ediv" -> "div" | "emod" -> "mod"
  | "lt" -> "<" | "le" -> "<=" | "eq" -> "=" | "not" -> "not" | "and" -> "and" | "or" -> "or" | "implies" -> "=>"
  | "ite" -> "ite" | "to_real" -> "to_real" | "floor" -> "to_int" | "is_int" -> "is_int" | "select" -> "select" | "store" -> "store"
  | "str.++" -> "str.++" | "str.len" -> "str.len" | "str.contains" -> "str.contains" | "str.prefixof" -> "str.prefixof"
  | "str.suffixof" -> "str.suffixof" | "str.substr" -> "str.substr" | "str.indexof" -> "str.indexof" | "str.lt" -> "str.<" | "str.le" -> "str.<="
  | op -> op

let rec pr p (t : term) =
  match Hashtbl.find_opt p.names t.id with
  | Some n -> Buffer.add_string p.buf n
  | None -> pr_node p t

and pr_node p t =
  let b = p.buf in
  let args xs = Array.iter (fun x -> Buffer.add_char b ' '; pr p x) xs in
  match t.node with
  | Const n -> Buffer.add_string b (q_const n)
  | Num q -> Buffer.add_string b (num_smt t.sort q)
  | Big s -> (
    match String.index_opt s '/' with
    | Some k -> Buffer.add_string b (Printf.sprintf "(/ %s.0 %s.0)" (String.sub s 0 k) (String.sub s (k + 1) (String.length s - k - 1)))
    | None -> Buffer.add_string b (if String.length s > 0 && s.[0] = '-' then Printf.sprintf "(- %s)" (String.sub s 1 (String.length s - 1)) else s))
  | BoolV v -> Buffer.add_string b (if v then "true" else "false")
  | StrV s -> Buffer.add_string b (str_lit s)
  | App ("K", [| v |]) -> Buffer.add_string b (Printf.sprintf "((as const %s) " (sort_smt t.sort)); pr p v; Buffer.add_char b ')'
  | App ("str.from_int", [| a |]) ->
    Buffer.add_string b "(ite (>= "; pr p a; Buffer.add_string b " 0) (str.from_int "; pr p a; Buffer.add_string b ") (str.++ \"-\" (str.from_int (- "; pr p a; Buffer.add_string b "))))"
  | App ("str.at", [| s; i |]) -> Buffer.add_string b "(str.substr "; pr p s; Buffer.add_char b ' '; pr p i; Buffer.add_string b " 1)"
  | App (op, xs) when String.length op > 6 && String.sub op 0 6 = "field:" -> (
    match xs.(0).sort with
    | Rec (rn, _) -> Buffer.add_string b ("(" ^ q_field rn (String.sub op 6 (String.length op - 6))); args xs; Buffer.add_char b ')'
    | _ -> failwith "field of a non-record")
  | App (op, xs) when String.length op > 3 && String.sub op 0 3 = "mk:" ->
    let rn = String.sub op 3 (String.length op - 3) in
    if Array.length xs = 0 then Buffer.add_string b (q_mk rn) else (Buffer.add_string b ("(" ^ q_mk rn); args xs; Buffer.add_char b ')')
  | App (op, xs) -> Buffer.add_string b ("(" ^ op_smt op); args xs; Buffer.add_char b ')'
  | Fn (n, xs) -> if Array.length xs = 0 then Buffer.add_string b (q_fn n) else (Buffer.add_string b ("(" ^ q_fn n); args xs; Buffer.add_char b ')')
  | Quant (k, vs, body, pats) ->
    Buffer.add_string b ("(" ^ k ^ " (");
    Array.iter (fun v -> match v.node with Const n -> Buffer.add_string b (Printf.sprintf "(%s %s)" (q_const n) (sort_smt v.sort)) | _ -> ()) vs;
    Buffer.add_string b ") ";
    if pats = [] || k <> "forall" then pr p body
    else begin
      Buffer.add_string b "(! ";
      pr p body;
      List.iter (fun ps -> Buffer.add_string b " :pattern ("; Array.iteri (fun i x -> if i > 0 then Buffer.add_char b ' '; pr p x) ps; Buffer.add_char b ')') pats;
      Buffer.add_char b ')'
    end;
    Buffer.add_char b ')'

(* -- scripts ------------------------------------------------------------------- *)

(* [neg_goal] is built by the caller: workers must not construct terms (the
   hash-cons table belongs to the main domain). *)
let script (defs : fundef list) (axioms : axiom list) (hyps : term list) (neg_goal : term) : string =
  let b = Buffer.create 8192 in
  let add s = Buffer.add_string b s; Buffer.add_char b '\n' in
  let roots = List.map (fun a -> a.formula) axioms @ hyps @ [ neg_goal ] in
  let def_bodies = List.filter_map (fun d -> d.body) defs in
  (* sorts: records in dependency order, and the opaque sort *)
  let recs = ref [] and opaque = ref false in
  let rec see_sort s =
    match s with
    | Opaque -> opaque := true
    | Array (i, e) -> see_sort i; see_sort e
    | Rec (n, fs) -> if not (List.mem_assoc n !recs) then (List.iter (fun (_, fs) -> see_sort fs) fs; recs := (n, fs) :: !recs)
    | _ -> ()
  in
  let seen = Hashtbl.create 1024 in
  let bound = Hashtbl.create 64 in
  let consts = ref [] and ufs = Hashtbl.create 16 in
  let defined = Hashtbl.create 16 in
  List.iter (fun d -> Hashtbl.replace defined d.fname ()) defs;
  let rec visit t =
    if not (Hashtbl.mem seen t.id) then begin
      Hashtbl.add seen t.id ();
      see_sort t.sort;
      match t.node with
      | Const _ -> if not (Hashtbl.mem bound t.id) then consts := t :: !consts
      | App (_, xs) -> Array.iter visit xs
      | Fn (n, xs) ->
        Array.iter visit xs;
        if not (Hashtbl.mem defined n) && not (Hashtbl.mem ufs n) then Hashtbl.add ufs n (Array.to_list (Array.map (fun x -> x.sort) xs), t.sort)
      | Quant (_, vs, body, pats) ->
        Array.iter (fun v -> Hashtbl.replace bound v.id (); see_sort v.sort) vs;
        visit body;
        List.iter (Array.iter visit) pats
      | _ -> ()
    end
  in
  (* bound variables are known to the printer; which constants are free is
     decided per root, respecting binders (a hash-consed variable may be
     bound in one place and free in another) *)
  let rec binders t = match t.node with Quant (_, vs, body, _) -> Array.iter (fun v -> Hashtbl.replace bound v.id ()) vs; binders body | App (_, xs) | Fn (_, xs) -> Array.iter binders xs | _ -> () in
  List.iter binders (roots @ def_bodies);
  List.iter (fun d -> see_sort d.fsort; List.iter (fun p -> see_sort p.sort) d.params) defs;
  List.iter visit roots;
  List.iter visit def_bodies;
  let declared = Hashtbl.create 64 in
  consts := [];
  let declare (c : term) = if not (Hashtbl.mem declared c.id) then (Hashtbl.add declared c.id (); consts := c :: !consts) in
  List.iter (fun r -> List.iter declare (Term.consts r)) roots;
  List.iter (fun d -> match d.body with Some b -> List.iter (fun c -> if not (List.memq c d.params) then declare c) (Term.consts b) | None -> ()) defs;
  add "(set-option :model.completion true)";
  if !opaque then add "(declare-sort Opaque 0)";
  List.iter
    (fun (n, fs) ->
      let fields = String.concat " " (List.map (fun (f, s) -> Printf.sprintf "(%s %s)" (q_field n f) (sort_smt s)) fs) in
      add (Printf.sprintf "(declare-datatypes ((%s 0)) (((%s %s))))" (q_rec n) (q_mk n) fields))
    (List.rev !recs);
  List.iter (fun c -> match c.node with Const n -> add (Printf.sprintf "(declare-const %s %s)" (q_const n) (sort_smt c.sort)) | _ -> ()) (List.rev !consts);
  Hashtbl.iter (fun n (args, r) -> add (Printf.sprintf "(declare-fun %s (%s) %s)" (q_fn n) (String.concat " " (List.map sort_smt args)) (sort_smt r))) ufs;
  let p = { buf = b; names = Hashtbl.create 64 } in
  if defs <> [] then begin
    Buffer.add_string b "(define-funs-rec (";
    List.iter
      (fun d ->
        let ps = String.concat " " (List.map (fun v -> match v.node with Const n -> Printf.sprintf "(%s %s)" (q_const n) (sort_smt v.sort) | _ -> "") d.params) in
        Buffer.add_string b (Printf.sprintf "(%s (%s) %s)" (q_fn d.fname) ps (sort_smt d.fsort)))
      defs;
    Buffer.add_string b ") (";
    let q = { buf = b; names = Hashtbl.create 1 } in
    List.iter (fun d -> match d.body with Some body -> Buffer.add_char b ' '; pr q body | None -> ()) defs;
    Buffer.add_string b "))\n"
  end;
  (* shared ground subterms (no bound variables) become define-funs *)
  let refs = Hashtbl.create 1024 and has_bound = Hashtbl.create 1024 in
  let rec hb t =
    match Hashtbl.find_opt has_bound t.id with
    | Some v -> v
    | None ->
      let v = match t.node with Const _ -> Hashtbl.mem bound t.id | Quant _ -> true | App (_, xs) | Fn (_, xs) -> Array.exists hb xs | _ -> false in
      Hashtbl.add has_bound t.id v;
      v
  in
  let order = ref [] in
  let seen2 = Hashtbl.create 1024 in
  let rec count t =
    Hashtbl.replace refs t.id (1 + try Hashtbl.find refs t.id with Not_found -> 0);
    if not (Hashtbl.mem seen2 t.id) then begin
      Hashtbl.add seen2 t.id ();
      (match t.node with App (_, xs) | Fn (_, xs) -> Array.iter count xs | _ -> ());
      order := t :: !order
    end
  in
  List.iter count roots;
  List.iter
    (fun t ->
      match t.node with
      | (App _ | Fn _) when Hashtbl.find refs t.id > 1 && not (hb t) ->
        let nm = Printf.sprintf "|$%d|" t.id in
        Buffer.add_string b (Printf.sprintf "(define-fun %s () %s " nm (sort_smt t.sort));
        pr_node p t;
        Buffer.add_string b ")\n";
        Hashtbl.replace p.names t.id nm
      | _ -> ())
    (List.rev !order);
  List.iter (fun t -> Buffer.add_string b "(assert "; pr p t; Buffer.add_string b ")\n") roots;
  Buffer.contents b

(* -- s-expressions (z3's answers) ------------------------------------------------ *)

type sx = Atom of string | Str of string | Sx of sx list

let parse_sx (s : string) : sx list =
  let n = String.length s and i = ref 0 in
  let rec ws () = if !i < n && (s.[!i] = ' ' || s.[!i] = '\n' || s.[!i] = '\t' || s.[!i] = '\r') then (incr i; ws ()) in
  let rec one () =
    ws ();
    if s.[!i] = '(' then begin
      incr i;
      let items = ref [] in
      ws ();
      while !i < n && s.[!i] <> ')' do items := one () :: !items; ws () done;
      incr i;
      Sx (List.rev !items)
    end
    else if s.[!i] = '"' then begin
      incr i;
      let b = Buffer.create 16 in
      let fin = ref false in
      while not !fin do
        if s.[!i] = '"' then (if !i + 1 < n && s.[!i + 1] = '"' then (Buffer.add_char b '"'; i := !i + 2) else (incr i; fin := true))
        else if s.[!i] = '\\' && !i + 2 < n && s.[!i + 1] = 'u' && s.[!i + 2] = '{' then begin
          let j = String.index_from s !i '}' in
          let hex = String.sub s (!i + 3) (j - !i - 3) in
          let cp = int_of_string ("0x" ^ hex) in
          if cp < 128 then Buffer.add_char b (Char.chr cp) else Buffer.add_utf_8_uchar b (Uchar.of_int cp);
          i := j + 1
        end
        else (Buffer.add_char b s.[!i]; incr i)
      done;
      Str (Buffer.contents b)
    end
    else if s.[!i] = '|' then begin
      let j = String.index_from s (!i + 1) '|' in
      let a = String.sub s (!i + 1) (j - !i - 1) in
      i := j + 1;
      Atom a
    end
    else begin
      let st = !i in
      while !i < n && not (List.mem s.[!i] [ ' '; '\n'; '\t'; '\r'; '('; ')' ]) do incr i done;
      Atom (String.sub s st (!i - st))
    end
  in
  let out = ref [] in
  ws ();
  while !i < n do out := one () :: !out; ws () done;
  List.rev !out

(* a model value -> the JSON Python's decoder produces *)
let rec value_json (sort : sort) (v : sx) : Json.t =
  let num_q v =
    let rec q = function
      | Atom a -> (
        match String.index_opt a '.' with
        | Some k ->
          let ip = String.sub a 0 k and fp = String.sub a (k + 1) (String.length a - k - 1) in
          let fp = if fp = "" then "0" else fp in
          let d = int_of_float (10. ** float_of_int (String.length fp)) in
          Some (Q.make ((int_of_string ip * d) + int_of_string fp) d)
        | None -> Option.map Q.of_int (int_of_string_opt a))
      | Sx [ Atom "-"; x ] -> Option.bind (q x) Q.neg
      | Sx [ Atom "/"; a; b ] -> ( match (q a, q b) with Some a, Some b -> Q.div a b | _ -> None)
      | _ -> None
    in
    q v
  in
  match sort with
  | Int | Unit -> ( match num_q v with Some q -> Json.Int q.n | None -> Json.Null)
  | Real -> ( match num_q v with Some q -> Json.Assoc [ ("__real__", Json.List [ Json.Int q.n; Json.Int q.d ]) ] | None -> Json.Null)
  | Bool -> ( match v with Atom "true" -> Json.Bool true | Atom "false" -> Json.Bool false | _ -> Json.Null)
  | Str -> ( match v with Str s -> Json.String s | _ -> Json.Null)
  | Opaque -> Json.Assoc [ ("__opaque__", Json.Bool true) ]
  | Rec (n, fs) -> (
    let args = match v with Sx (_ :: args) -> args | _ -> [] in
    if String.length n > 4 && String.sub n 0 4 = "Opt_" then
      match args with [ Atom "true"; x ] -> value_json (List.assoc "val" fs) x | _ -> Json.Null
    else if List.length args = List.length fs then Json.Assoc (List.map2 (fun (f, fs) a -> (f, value_json fs a)) fs args)
    else Json.Null)
  | Array _ -> Json.Null

(* -- a z3 process -------------------------------------------------------------- *)

type z3 = { inp : out_channel; out : in_channel; pid : int }

let z3_path () = match Sys.getenv_opt "TELIC_Z3" with Some p -> p | None -> "z3"

let spawn () =
  let r0, w0 = Unix.pipe ~cloexec:true () and r1, w1 = Unix.pipe ~cloexec:true () in
  let pid = Unix.create_process (z3_path ()) [| z3_path (); "-in"; "-smt2" |] r0 w1 Unix.stderr in
  Unix.close r0;
  Unix.close w1;
  { inp = Unix.out_channel_of_descr w0; out = Unix.in_channel_of_descr r1; pid }

let send z s = output_string z.inp s; output_char z.inp '\n'; flush z.inp

(* Send commands and read everything z3 prints for them, up to a marker:
   error lines can never leave the stream out of step. *)
let marker = "telic-sync-7f3a"

let exchange z (cmds : string) : string list =
  send z cmds;
  send z (Printf.sprintf "(echo \"%s\")" marker);
  let lines = ref [] in
  let fin = ref false in
  while not !fin do
    let line = input_line z.out in
    if String.trim line = marker then fin := true else lines := line :: !lines
  done;
  List.rev !lines

let read_answer_lines lines = String.concat "\n" lines

let close z = (try send z "(exit)" with _ -> ()); (try ignore (Unix.waitpid [] z.pid) with _ -> ())

type result = { status : string; seconds : float; model : (string * Json.t) list; state : (string * Json.t) list; reason : string }

(* Check one script; on sat, evaluate [probe] terms (inputs etc.). *)
let check z ~timeout_ms (text : string) =
  let out = exchange z (Printf.sprintf "(reset)\n(set-option :timeout %d)\n%s\n(check-sat)" timeout_ms text) in
  let out = List.filter (fun l -> String.trim l <> "") out in
  let errors = List.filter (fun l -> String.length l > 6 && String.sub (String.trim l) 0 6 = "(error") out in
  (* any error means z3 did not see the whole problem: its answer is void *)
  if errors <> [] then ("unknown", "z3 rejected the script: " ^ String.concat " " errors)
  else
    match List.rev out with
    | last :: _ when List.mem (String.trim last) [ "sat"; "unsat"; "unknown" ] -> (String.trim last, "")
    | _ -> ("unknown", "z3: " ^ String.concat " " out)

let get_values z (ts : term list) : sx list =
  if ts = [] then []
  else begin
    let p = { buf = Buffer.create 256; names = Hashtbl.create 1 } in
    Buffer.add_string p.buf "(get-value (";
    List.iter (fun t -> Buffer.add_char p.buf ' '; pr p t) ts;
    Buffer.add_string p.buf "))";
    match parse_sx (read_answer_lines (exchange z (Buffer.contents p.buf))) with
    | [ Sx pairs ] -> List.map (function Sx [ _; v ] -> v | x -> x) pairs
    | _ -> List.map (fun _ -> Atom "?") ts
  end

(* get-value of raw SMT-LIB expressions (no term construction) *)
let get_values_raw z (exprs : string list) : sx list =
  if exprs = [] then []
  else begin
    match parse_sx (read_answer_lines (exchange z ("(get-value (" ^ String.concat " " exprs ^ "))"))) with
    | [ Sx pairs ] -> List.map (function Sx [ _; v ] -> v | x -> x) pairs
    | _ -> List.map (fun _ -> Atom "?") exprs
  end

let term_text (t : term) =
  let p = { buf = Buffer.create 64; names = Hashtbl.create 1 } in
  pr p t;
  Buffer.contents p.buf

let reason_unknown z =
  match parse_sx (read_answer_lines (exchange z "(get-info :reason-unknown)")) with [ Sx [ _; Str r ] ] -> r | [ Sx [ _; Atom r ] ] -> r | _ -> "unknown"
