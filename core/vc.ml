(* Verification-condition generation by symbolic execution: a port of
   telic/vcgen.py. Each function is executed from a state where its
   parameters are fresh constants and its @requires hold; every point where
   the program or its contract can go wrong becomes one obligation. Branches
   are merged with ite, calls are modular (prove the callee's @requires,
   assume its @ensures), loops are cut by their invariants. *)

open Term
module SM = Map.Make (String)

exception Vc_error of string * Ir.loc
exception Fallback of string  (** outside what this engine models yet *)

(* -- values ------------------------------------------------------------ *)

type lv = { arr : term; off : term; len : term; lty : Ir.ty }

type value =
  | T of term
  | L of lv
  | NoneV

let at (arr, off) i = select arr (add off i)

let term_of loc = function T t -> t | NoneV -> raise (Vc_error ("None used as a value", loc)) | L _ -> raise (Vc_error ("a list used as a scalar", loc))

let rec sort_of (ty : Ir.ty) : sort =
  match ty with
  | TInt -> Int
  | TReal -> Real
  | TBool -> Bool
  | TStr -> Str
  | TRecord (n, fs) -> Rec (n, List.map (fun (f, t) -> (f, field_sort t)) fs)
  | TList e -> Array (Int, sort_of e)
  | TClass _ -> Int
  | TOpaque -> Opaque
  | TEnum _ -> Int
  | TNone -> Unit
  | TOption _ | TDict _ -> raise (Fallback "optional/dict values")

and field_sort (ty : Ir.ty) : sort =
  match ty with
  | TOption inner ->
    let s = sort_of inner in
    Rec ("Opt_" ^ sort_tag s, [ ("some", Bool); ("val", s) ])
  | t -> sort_of t

and sort_tag = function Rec (n, _) -> n | Array (_, e) -> "Arr" ^ sort_tag e | s -> sort_name s

let flatten = function T t -> [ t ] | L l -> [ l.arr; l.off; l.len ] | NoneV -> []

let ite_val c a b =
  match (a, b) with
  | L x, L y -> L { arr = ite c x.arr y.arr; off = ite c x.off y.off; len = ite c x.len y.len; lty = x.lty }
  | T x, T y -> T (ite c x y)
  | NoneV, NoneV -> NoneV
  | _ -> raise (Vc_error ("branches disagree on a value's shape", Ir.noloc))

let value_equal a b = match (a, b) with T x, T y -> x == y | L x, L y -> x.arr == y.arr && x.off == y.off && x.len == y.len | NoneV, NoneV -> true | _ -> false

(* Python/JS arithmetic in terms of Euclidean division *)
let floordiv a b = ite (lt zero b) (ediv a b) (ediv (neg a) (neg b))

let truncdiv a b =
  let q = ediv (abs_ a) (abs_ b) in
  ite (eq (le zero a) (lt zero b)) q (neg q)

let round_even x =
  let f = floor x in
  let d = sub x (to_real f) in
  let half = real (Q.make 1 2) in
  ite (lt d half) f (ite (lt half d) (add f one) (ite (eq (emod f (int_ 2)) zero) f (add f one)))

let rec rec_equal a b =
  match a.sort with
  | Rec (n, fields) when String.length n > 4 && String.sub n 0 4 = "Opt_" ->
    let sa = field a "some" and sb = field b "some" in
    and_ [ eq sa sb; implies sa (rec_equal (field a "val") (field b "val")) ]
  | Rec (_, fields) -> and_ (List.map (fun (f, _) -> rec_equal (field a f) (field b f)) fields)
  | _ -> eq a b

(* -- program information (computed by the Python side) ------------------ *)

type finfo = {
  key : string;
  fn : Ir.func;
  modpath : string;
  mutated : string list;
  appends : string list;
  definitional : bool;
  logic_name : string;
  scc : string list;
  recursive : bool;
  resolve : (string * string) list;  (** call name -> function key *)
}

type program = { funcs : (string, finfo) Hashtbl.t }

type options = {
  extra_invariants : (int * Ir.clause list) list;
  variants : (int * Ir.expr) list;
  measures : (string * Ir.expr) list;
}

let no_options = { extra_invariants = []; variants = []; measures = [] }

(* -- obligations ---------------------------------------------------------- *)

type obligation = {
  oid : string;
  func : string;
  kind : string;
  oloc : Ir.loc;
  site : Ir.loc option;
  message : string;
  hyps : term list;
  goal : term;
  clause : Ir.clause option;
  intents : string list;
  inputs : (string * value) list;
  deps : string list;
  exclude : string list;
  inferred : bool;
}

(* -- states and contexts --------------------------------------------------- *)

type state = { mutable env : value SM.t; facts : term Dynarray.t; mutable alive : bool }

let copy_state (st : state) : state = { env = st.env; facts = Dynarray.copy st.facts; alive = st.alive }

type ctx = {
  base : term Dynarray.t;
  env : value SM.t;
  live : state option;  (** read variables from this state (they may change mid-expression) *)
  guard : term list;
  bound : value SM.t;
  old_env : value SM.t option;
  result : value option;
  spec : bool;
  quiet : bool;
  state : state option;
  finfo : finfo;  (** whose names calls resolve against *)
}

let hyps ctx = Dynarray.to_list ctx.base @ ctx.guard
let assume ctx t = Dynarray.add_last ctx.base (if ctx.guard = [] then t else implies (and_ ctx.guard) t)
let sub_ctx ?cond ctx = { ctx with guard = (match cond with Some c -> ctx.guard @ [ c ] | None -> ctx.guard) }
let cur_env ctx = match ctx.live with Some st -> st.env | None -> ctx.env

type frame = { mutable breaks : state list; mutable continues : state list }

type exit = { efacts : term list; value : value option; eenv : value SM.t; eloc : Ir.loc }

(* -- the generator ---------------------------------------------------------- *)

type gen = {
  prog : program;
  info : finfo;
  opts : options;
  mutable obligations : obligation list;  (** reversed *)
  mutable exits : exit list;  (** reversed *)
  mutable loops : frame list;
  mutable counter : int;
  ids : (string, int) Hashtbl.t;
  mutable deps : string list;
  mutable entry : value SM.t;
  mutable inputs : (string * value) list;
  mutable assumptions : (int * string) list;
  mutable loop_notes : (int * string) list;
  mutable definitional_mode : bool;
}

let next g =
  g.counter <- g.counter + 1;
  g.counter

let tyname = function
  | Ir.TInt -> "int" | TReal -> "real" | TBool -> "bool" | TStr -> "str" | TNone -> "none"
  | _ -> "?"

let fresh g base (ty : Ir.ty) ?len () =
  let n = next g in
  match ty with
  | TList e ->
    let arr = const (Printf.sprintf "%s@%d.arr" base n) (Array (Int, sort_of e)) in
    let ln = match len with Some l -> l | None -> const (Printf.sprintf "%s@%d.len" base n) Int in
    L { arr; off = zero; len = ln; lty = ty }
  | TNone -> NoneV
  | t -> T (const (Printf.sprintf "%s@%d" base n) (sort_of t))

let param_val name (ty : Ir.ty) =
  match ty with
  | TList e -> L { arr = const (name ^ ".arr") (Array (Int, sort_of e)); off = zero; len = const (name ^ ".len") Int; lty = ty }
  | TNone -> NoneV
  | t -> T (const name (sort_of t))

let finfo_of g key = try Hashtbl.find g.prog.funcs key with Not_found -> raise (Fallback ("unknown function " ^ key))
let same_scc g a b = a = b || List.mem b (finfo_of g a).scc

let oblige g ?site ?clause ?(inferred = false) kind ctx goal (loc : Ir.loc) message =
  if not (ctx.quiet || g.definitional_mode) then begin
    let base =
      Printf.sprintf "%s@%d%s" kind loc.line (match site with Some (s : Ir.loc) when s.line <> loc.line -> Printf.sprintf ">%d" s.line | _ -> "")
    in
    let k = try Hashtbl.find g.ids base with Not_found -> 0 in
    Hashtbl.replace g.ids base (k + 1);
    let oid = Printf.sprintf "%s/%s%s" g.info.fn.name base (if k > 0 then Printf.sprintf "#%d" (k + 1) else "") in
    let excl = g.info.key :: g.info.scc in
    let intents = match clause with Some (c : Ir.clause) -> c.intents | None -> [] in
    let inferred = inferred || match clause with Some c -> c.inferred | None -> false in
    g.obligations <-
      { oid; func = g.info.key; kind; oloc = loc; site; message; hyps = hyps ctx; goal; clause; intents; inputs = List.rev g.inputs; deps = g.deps; exclude = excl; inferred }
      :: g.obligations
  end

let note g (loc : Ir.loc) text = if not (List.mem (loc.line, text) g.assumptions) then g.assumptions <- (loc.line, text) :: g.assumptions

let lookup ctx name (loc : Ir.loc) =
  match SM.find_opt name ctx.bound with
  | Some v -> v
  | None -> (
    match SM.find_opt name (cur_env ctx) with
    | Some v -> v
    | None -> raise (Vc_error (Printf.sprintf "'%s' may be used before it is assigned" name, loc)))

let expr_name (e : Ir.expr) = match e.e with Var n -> n | Field (_, f) -> f | Call (f, _) -> f ^ "(...)" | _ -> "value"

let index_of g (arr, off, len) i wrap ctx loc what =
  if wrap then begin
    oblige g "index" ctx (and_ [ le (neg len) i; lt i len ]) loc (Printf.sprintf "index into '%s' is within -len..len-1" what);
    ite (lt i zero) (add i len) i
  end else begin
    oblige g "index" ctx (and_ [ le zero i; lt i len ]) loc (Printf.sprintf "index into '%s' is within 0..len-1" what);
    i
  end

let lit_value (e : Ir.expr) =
  match e.e with
  | Lit (LInt s) -> (
    match int_of_string_opt s with
    | Some n -> ( match e.ty with TReal -> T (real (Q.of_int n)) | _ -> T (int_ n))
    | None -> T (mk (Big s) (if e.ty = TReal then Real else Int)))
  | Lit (LFrac (n, d)) -> (
    match (int_of_string_opt n, int_of_string_opt d) with
    | Some n, Some d -> T (real (Q.make n d))
    | _ -> T (mk (Big (n ^ "/" ^ d)) Real))
  | Lit (LBool b) -> T (bool_ b)
  | Lit (LStr s) -> T (str s)
  | Lit LNone -> NoneV
  | _ -> assert false

let rec ev g ctx (e : Ir.expr) : value =
  let loc = e.loc in
  let tm x = term_of loc x in
  match e.e with
  | Lit _ -> lit_value e
  | Var n -> lookup ctx n loc
  | Result -> ( match ctx.result with Some r -> r | None -> raise (Vc_error ("'result' is not available here", loc)))
  | Old x -> (
    match ctx.old_env with
    | Some oe -> ev g { ctx with env = oe; live = None } x
    | None -> raise (Vc_error ("old(...) is only meaningful in '@ensures'", loc)))
  | Unary ("neg", x) -> T (neg (tm (ev g ctx x)))
  | Unary ("not", x) -> T (not_ (tm (ev g ctx x)))
  | Unary (op, _) -> raise (Vc_error ("unknown unary operator " ^ op, loc))
  | Binary (("and" | "or" | "implies") as op, a, b) ->
    let x = tm (ev g ctx a) in
    let y = tm (ev g (sub_ctx ~cond:(if op = "or" then not_ x else x) ctx) b) in
    T (match op with "and" -> and_ [ x; y ] | "or" -> or_ [ x; y ] | _ -> implies x y)
  | Binary (op, a, b) -> (
    let x = ev g ctx a and y = ev g ctx b in
    match op with
    | "eq" -> T (equal g x y)
    | "ne" -> T (not_ (equal g x y))
    | _ -> (
      let x = tm x and y = tm y in
      match op with
      | "add" -> T (add x y)
      | "sub" -> T (sub x y)
      | "mul" -> T (mul x y)
      | "lt" -> T (lt x y)
      | "le" -> T (le x y)
      | "gt" -> T (gt x y)
      | "ge" -> T (ge x y)
      | "rdiv" | "floordiv" | "fmod" | "tmod" ->
        let z = lit_of_int 0 y.sort in
        let sym = match op with "rdiv" -> "/" | "floordiv" -> "//" | _ -> "%" in
        oblige g "div" ctx (ne y z) loc (Printf.sprintf "divisor of '%s' is non-zero" sym);
        if op = "rdiv" then T (rdiv x y)
        else if x.sort = Real then begin
          let q = rdiv x y in
          let qi = if op = "fmod" || op = "floordiv" then floor q else ite (le (real (Q.of_int 0)) q) (floor q) (neg (floor (neg q))) in
          if op = "floordiv" then T (to_real qi) else T (sub x (mul y (to_real qi)))
        end
        else if op = "floordiv" then T (floordiv x y)
        else if op = "fmod" then T (sub x (mul y (floordiv x y)))
        else T (sub x (mul y (truncdiv x y)))
      | _ -> raise (Vc_error ("unknown operator " ^ op, loc))))
  | Ite (c, a, b) ->
    let c = tm (ev g ctx c) in
    let x = ev g (sub_ctx ~cond:c ctx) a in
    let y = ev g (sub_ctx ~cond:(not_ c) ctx) b in
    ite_val c x y
  | Index (s, i, wrap) -> (
    match ev g ctx s with
    | L l ->
      let i = tm (ev g ctx i) in
      let j = index_of g (l.arr, l.off, l.len) i wrap ctx loc (expr_name s) in
      T (at (l.arr, l.off) j)
    | _ -> raise (Fallback "indexing a non-list"))
  | Field (o, f) -> (
    match o.ty with
    | TClass _ -> raise (Fallback "objects")
    | _ ->
      let raw = field (tm (ev g ctx o)) f in
      (match e.ty with TOption _ -> raise (Fallback "optional record fields") | _ -> T raw))
  | RecordLit fs ->
    let vals = List.map (fun (_, x) -> tm (ev g ctx x)) fs in
    T (mkrec (sort_of e.ty) vals)
  | ListLit elems ->
    let ty = match e.ty with TList TNone -> Ir.TList TInt | t -> t in
    let base = match fresh g "lit" ty ~len:zero () with L l -> l | _ -> assert false in
    let arr = ref base.arr in
    List.iteri (fun i x -> arr := store !arr (int_ i) (tm (ev g ctx x))) elems;
    L { arr = !arr; off = zero; len = int_ (List.length elems); lty = ty }
  | Quant q ->
    let lo = tm (ev g ctx q.lo) and hi = tm (ev g ctx q.hi) in
    let base = match String.index_opt q.idx '$' with Some k -> String.sub q.idx 0 k | None -> q.idx in
    let i = const (Printf.sprintf "%s!%d" base (next g)) Int in
    let rng = and_ [ le lo i; lt i hi ] in
    let sub = sub_ctx ~cond:rng ctx in
    let bound = SM.add q.idx (T i) sub.bound in
    let bound =
      match (q.seq, q.elem) with
      | Some s, Some el -> ( match ev g ctx s with L l -> SM.add el (T (at (l.arr, l.off) i)) bound | _ -> raise (Fallback "quantifier over a non-list"))
      | _ -> bound
    in
    let body = tm (ev g { sub with bound } q.body) in
    if q.kind = "forall" then T (forall [ i ] (implies rng body)) else T (exists [ i ] (and_ [ rng; body ]))
  | Builtin (name, args) -> builtin g ctx e name args
  | Call (f, args) ->
    let key = try List.assoc f ctx.finfo.resolve with Not_found -> raise (Vc_error (Printf.sprintf "unknown function '%s'" f, loc)) in
    let callee = finfo_of g key in
    let vals = List.map (ev g ctx) args in
    call g callee vals args ctx loc
  | New _ | Extern _ -> raise (Fallback "objects and unchecked calls")

and equal g a b =
  match (a, b) with
  | L x, L y ->
    let i = const (Printf.sprintf "eq!%d" (next g)) Int in
    let same = forall [ i ] (implies (and_ [ le zero i; lt i x.len ]) (eq (at (x.arr, x.off) i) (at (y.arr, y.off) i))) in
    and_ [ eq x.len y.len; same ]
  | T x, T y -> rec_equal x y
  | NoneV, NoneV -> tt
  | _ -> raise (Fallback "comparing values of different shapes")

and builtin g ctx (e : Ir.expr) name args =
  let loc = e.loc in
  let vals = List.map (ev g ctx) args in
  let tm x = term_of loc x in
  let lst = function L l -> l | _ -> raise (Fallback ("builtin on a non-list: " ^ name)) in
  match (name, vals) with
  | "len", [ xs ] -> T (lst xs).len
  | "abs", [ x ] -> T (abs_ (tm x))
  | ("min" | "max"), x :: rest ->
    let f = if name = "min" then min_ else max_ in
    T (List.fold_left (fun acc y -> f acc (tm y)) (tm x) rest)
  | "sum", [ xs ] ->
    let l = lst xs in
    let elem = match l.lty with TList t -> t | _ -> TInt in
    let fd = if elem = TInt then "seqsum" else "seqsum_r" in
    T (fn fd [| l.arr; l.off; add l.off l.len |] (sort_of elem))
  | "count", [ xs; v ] ->
    let l = lst xs in
    let elem = match l.lty with TList t -> t | _ -> TInt in
    let fd = "seqcount_" ^ String.lowercase_ascii (sort_name (sort_of elem)) in
    T (fn fd [| l.arr; l.off; add l.off l.len; tm v |] Int)
  | "contains", [ xs; v ] ->
    let l = lst xs in
    let i = const (Printf.sprintf "in!%d" (next g)) Int in
    T (exists [ i ] (and_ [ le zero i; lt i l.len; eq (at (l.arr, l.off) i) (tm v) ]))
  | "slice", [ xs; lo; hi ] ->
    let l = lst xs in
    let n = l.len in
    let norm b default = match b with NoneV -> default | b -> let b = tm b in ite (lt b zero) (max_ (add b n) zero) (min_ b n) in
    let lo2 = norm lo zero and hi2 = norm hi n in
    L { l with off = add l.off lo2; len = max_ (sub hi2 lo2) zero }
  | "to_real", [ x ] -> T (to_real (tm x))
  | "floor", [ x ] -> T (floor (tm x))
  | "ceil", [ x ] -> T (neg (floor (neg (tm x))))
  | "trunc", [ x ] -> let x = tm x in T (ite (le (real (Q.of_int 0)) x) (floor x) (neg (floor (neg x))))
  | "round_even", [ x ] -> T (round_even (tm x))
  | "round_up", [ x ] -> T (floor (add (tm x) (real (Q.make 1 2))))
  | "is_int", [ x ] -> T (is_int (tm x))
  | "list_append", [ xs; v ] -> let l = lst xs in L { l with arr = store l.arr (add l.off l.len) (tm v); len = add l.len one }
  | "list_set", [ xs; i; v ] ->
    let l = lst xs in
    let j = index_of g (l.arr, l.off, l.len) (tm i) true ctx loc (expr_name (List.hd args)) in
    L { l with arr = store l.arr (add l.off j) (tm v) }
  | _ -> raise (Fallback ("builtin " ^ name))

and call g (callee : finfo) (args : value list) (arg_exprs : Ir.expr list) ctx loc : value =
  let fn = callee.fn in
  (* a list argument is a reference: a later argument's mutation shows *)
  let args =
    match ctx.state with
    | Some st -> List.map2 (fun (a_e : Ir.expr) a -> match (a_e.e, a) with Var n, L _ -> (match SM.find_opt n st.env with Some v -> v | None -> a) | _ -> a) arg_exprs args
    | None -> args
  in
  let muts = callee.mutated in
  let list_vars = List.filter_map (fun ((a_e : Ir.expr), (_, pty)) -> match (a_e.e, pty) with Var n, Ir.TList _ -> Some n | _ -> None) (List.combine arg_exprs fn.params) in
  if muts <> [] && List.length list_vars <> List.length (List.sort_uniq compare list_vars) then
    raise (Vc_error (Printf.sprintf "the same list is passed twice to '%s', which mutates a list parameter; the two parameters would alias" fn.name, loc));
  List.iter2
    (fun (p, _) (a_e : Ir.expr) ->
      let fresh_expr = match a_e.e with ListLit _ | Call _ | New _ -> true | Builtin (("slice" | "dict_lit"), _) -> true | _ -> false in
      if List.mem p muts && (match a_e.e with Var _ -> false | _ -> true) && not fresh_expr then
        raise (Vc_error (Printf.sprintf "'%s' mutates its list parameter '%s'; pass a variable (or a copy) so the change is tracked" fn.name p, loc)))
    fn.params arg_exprs;
  let pmap = List.fold_left2 (fun m (p, _) a -> SM.add p a m) SM.empty fn.params args in
  let definitional = callee.definitional in
  if ctx.spec && not definitional then raise (Vc_error (Printf.sprintf "specs may only call pure (loop-free, mutation-free) functions; '%s' is not" fn.name, loc));
  let cctx = { ctx with env = pmap; live = None; bound = SM.empty; old_env = None; result = None; spec = true; quiet = true; state = None; finfo = callee } in
  List.iter
    (fun (rq : Ir.clause) ->
      let gl = term_of loc (ev g cctx rq.cexpr) in
      oblige g ~clause:rq "call" ctx gl loc (Printf.sprintf "call to '%s' satisfies '@requires %s'" fn.name rq.text))
    fn.requires;
  if fn.raises <> [] && not ctx.spec then begin
    let rc = or_ (List.map (fun (r : Ir.clause) -> term_of loc (ev g cctx r.cexpr)) fn.raises) in
    oblige g "call" ctx (not_ rc) loc (Printf.sprintf "call to '%s' cannot raise ('@raises %s')" fn.name (List.hd fn.raises).text)
  end;
  if same_scc g g.info.key callee.key then recursion_check g callee pmap ctx loc;
  if not (List.mem callee.key g.deps) then g.deps <- g.deps @ [ callee.key ];
  let r =
    if definitional then apply_def callee args
    else if fn.ret = TNone then NoneV
    else begin
      let short = match String.rindex_opt fn.name '.' with Some k -> String.sub fn.name (k + 1) (String.length fn.name - k - 1) | None -> fn.name in
      fresh g (short ^ "()") fn.ret ()
    end
  in
  let post = ref pmap in
  (match ctx.state with
   | Some st when not ctx.spec ->
     List.iter2
       (fun (p, pty) (a_e : Ir.expr) ->
         match a_e.e with
         | Var n when List.mem p muts ->
           let old = match SM.find_opt n st.env with Some (L l) -> l | _ -> raise (Vc_error ("mutated argument is not a list", loc)) in
           let keep = if List.mem p callee.appends then None else Some old.len in
           let nv = match fresh g n pty ?len:keep () with L l -> l | _ -> assert false in
           let nv = match keep with Some k -> { nv with off = old.off; len = k } | None -> assume ctx (le zero nv.len); nv in
           st.env <- SM.add n (L nv) st.env;
           post := SM.add p (L nv) !post
         | _ -> ())
       fn.params arg_exprs
   | _ -> ());
  if (not ctx.spec) && fn.ensures <> [] && not g.definitional_mode then begin
    let ectx = { cctx with env = !post; old_env = Some pmap; result = (match r with NoneV -> None | r -> Some r) } in
    List.iter (fun (en : Ir.clause) -> assume ctx (term_of loc (ev g ectx en.cexpr))) fn.ensures
  end;
  r

and apply_def (callee : finfo) args = T (fn callee.logic_name (Array.of_list (List.concat_map flatten args)) (sort_of callee.fn.ret))

and recursion_check g (callee : finfo) pmap ctx loc =
  let me = match List.assoc_opt g.info.key g.opts.measures with Some m -> Some m | None -> Option.map (fun (c : Ir.clause) -> c.cexpr) g.info.fn.decreases in
  let them = match List.assoc_opt callee.key g.opts.measures with Some m -> Some m | None -> Option.map (fun (c : Ir.clause) -> c.cexpr) callee.fn.decreases in
  match (me, them) with
  | Some me, Some them ->
    let mctx = { ctx with env = g.entry; live = None; bound = SM.empty; spec = true; quiet = true; state = None; finfo = g.info } in
    let m0 = term_of loc (ev g mctx me) in
    let cctx = { ctx with env = pmap; live = None; bound = SM.empty; spec = true; quiet = true; state = None; finfo = callee } in
    let m1 = term_of loc (ev g cctx them) in
    let inferred = g.info.fn.decreases = None in
    oblige g ~inferred "variant" ctx (le zero m0) loc "recursion measure is non-negative";
    oblige g ~inferred "variant" ctx (lt m1 m0) loc (Printf.sprintf "recursive call to '%s' decreases the measure" callee.fn.name)
  | _ -> oblige g "variant" ctx ff loc (Printf.sprintf "recursive call to '%s' terminates (add '@decreases <measure>')" callee.fn.name)

(* -- statements ----------------------------------------------------------- *)

let state_ctx g ?(spec = false) (st : state) = { base = st.facts; env = st.env; live = Some st; guard = []; bound = SM.empty; old_env = None; result = None; spec; quiet = false; state = Some st; finfo = g.info }

let rec block g stmts (st : state) : state = List.fold_left (fun st s -> if st.alive then stmt g s st else st) st stmts

and stmt g (s : Ir.stmt) (st : state) : state =
  match s with
  | Assign (_, name, v) ->
    let x = ev g (state_ctx g st) v in
    st.env <- SM.add name x st.env;
    st
  | IndexAssign (loc, name, i, v, wrap) -> (
    match SM.find_opt name st.env with
    | Some (L l) ->
      let ctx = state_ctx g st in
      let j = index_of g (l.arr, l.off, l.len) (term_of loc (ev g ctx i)) wrap ctx loc name in
      let x = term_of loc (ev g ctx v) in
      let l = match SM.find_opt name st.env with Some (L l) -> l | _ -> l in
      st.env <- SM.add name (L { l with arr = store l.arr (add l.off j) x }) st.env;
      st
    | _ -> raise (Fallback "dict assignment"))
  | Append (loc, name, v) -> (
    match SM.find_opt name st.env with
    | Some (L _) ->
      let x = term_of loc (ev g (state_ctx g st) v) in
      let l = match SM.find_opt name st.env with Some (L l) -> l | _ -> assert false in
      st.env <- SM.add name (L { l with arr = store l.arr (add l.off l.len) x; len = add l.len one }) st.env;
      st
    | _ -> raise (Vc_error ("append to a non-list", loc)))
  | If (loc, c, a, b) ->
    let c = term_of loc (ev g (state_ctx g st) c) in
    let t = copy_state st in
    Dynarray.add_last t.facts c;
    let t = block g a t in
    let e = copy_state st in
    Dynarray.add_last e.facts (not_ c);
    let e = block g b e in
    merge g [ t; e ]
  | While _ -> loop_while g s st
  | ForRange _ -> loop_range g s st
  | ForEach _ -> loop_each g s st
  | Return (loc, v) ->
    let x = match v with Some v -> Some (ev g (state_ctx g st) v) | None -> None in
    g.exits <- { efacts = Dynarray.to_list st.facts; value = x; eenv = st.env; eloc = loc } :: g.exits;
    st.alive <- false;
    st
  | Break _ ->
    (match g.loops with f :: _ -> f.breaks <- copy_state st :: f.breaks | [] -> ());
    st.alive <- false;
    st
  | Continue _ ->
    (match g.loops with f :: _ -> f.continues <- copy_state st :: f.continues | [] -> ());
    st.alive <- false;
    st
  | AssertStmt (_, c, native) ->
    let ctx = state_ctx g ~spec:(not native) st in
    let gl = term_of c.cloc (ev g ctx c.cexpr) in
    oblige g ~clause:c "assert" ctx gl c.cloc (Printf.sprintf "%s %s" (if native then "assert" else "@assert") c.text);
    Dynarray.add_last st.facts gl;
    st
  | AssumeStmt (_, c) ->
    let gl = term_of c.cloc (ev g (state_ctx g ~spec:true st) c.cexpr) in
    Dynarray.add_last st.facts gl;
    note g c.cloc c.text;
    st
  | Raise (loc, what, caught) ->
    if caught then (st.alive <- false; st)
    else begin
      let ctx = state_ctx g st in
      (if g.info.fn.raises <> [] then begin
         let ectx = { ctx with env = g.entry; live = None; spec = true; quiet = true } in
         let cond = or_ (List.map (fun (r : Ir.clause) -> term_of loc (ev g ectx r.cexpr)) g.info.fn.raises) in
         oblige g "raise" ctx cond loc (Printf.sprintf "raise %s outside '@raises %s'" what (List.hd g.info.fn.raises).text)
       end
       else oblige g "raise" ctx ff loc (Printf.sprintf "raise %s is reachable (add '@raises <condition>' if intended)" what));
      st.alive <- false;
      st
    end
  | ExprStmt (_, e) ->
    ignore (ev g (state_ctx g st) e);
    st
  | Unsupported (loc, reason) -> raise (Vc_error (reason, loc))
  | FieldAssign _ | DictDel _ | Try _ -> raise (Fallback "objects, dicts and try")

and merge _g (states : state list) : state =
  let live = List.filter (fun s -> s.alive) states in
  match live with
  | [] ->
    let d = copy_state (List.hd states) in
    d.alive <- false;
    d
  | [ s ] -> s
  | first :: _ ->
    let k = ref 0 in
    let len s = Dynarray.length s.facts in
    while List.for_all (fun s -> len s > !k && Dynarray.get s.facts !k == Dynarray.get first.facts !k) live do incr k done;
    let suffix s = List.init (len s - !k) (fun i -> Dynarray.get s.facts (!k + i)) in
    let guards = List.map (fun s -> and_ (suffix s)) live in
    let facts = Dynarray.create () in
    for i = 0 to !k - 1 do Dynarray.add_last facts (Dynarray.get first.facts i) done;
    Dynarray.add_last facts (or_ guards);
    let names = List.fold_left (fun acc (s : state) -> SM.fold (fun n _ acc -> if List.mem n acc then acc else n :: acc) s.env acc) [] live in
    let env =
      List.fold_left
        (fun env name ->
          let vals = List.map (fun (s : state) -> SM.find_opt name s.env) live in
          if List.exists Option.is_none vals then env
          else
            let vals = List.map Option.get vals in
            let v0 = List.hd vals in
            if List.for_all (value_equal v0) vals then SM.add name v0 env
            else begin
              let rv = List.rev vals and rg = List.rev guards in
              let last = List.hd rv in
              let out = List.fold_left2 (fun out gd v -> ite_val gd v out) last (List.tl rg) (List.tl rv) in
              SM.add name out env
            end)
        SM.empty names
    in
    { env; facts; alive = true }

(* -- loops ---------------------------------------------------------------- *)

and modified g body =
  let names = ref (Ir.assigned_names body) and appends = ref [] in
  let addn n = if not (List.mem n !names) then names := n :: !names in
  let adda n = if not (List.mem n !appends) then appends := n :: !appends in
  Ir.walk_stmts
    (fun s ->
      (match s with
       | Append (_, n, _) -> adda n
       | Assign (_, n, _) -> ( match Hashtbl.find_opt g.info.fn.locals n with Some (TList _) -> adda n | _ -> ())
       | _ -> ());
      List.iter
        (fun e ->
          Ir.walk_expr
            (fun (x : Ir.expr) ->
              match x.e with
              | Call (f, args) -> (
                match List.assoc_opt f g.info.resolve with
                | Some key ->
                  let tgt = finfo_of g key in
                  List.iter2
                    (fun (p, _) (a : Ir.expr) ->
                      match a.e with
                      | Var n when List.mem p tgt.mutated -> addn n; if List.mem p tgt.appends then adda n
                      | _ -> ())
                    tgt.fn.params
                    (if List.length args = List.length tgt.fn.params then args else List.filteri (fun i _ -> i < List.length tgt.fn.params) args)
                | None -> ())
              | _ -> ())
            e)
        (Ir.stmt_exprs s))
    body;
  (!names, !appends)

and havoc g (st : state) names appends : state =
  let h = copy_state st in
  List.iter
    (fun name ->
      match SM.find_opt name h.env with
      | None -> ()
      | Some old -> (
        match Hashtbl.find_opt g.info.fn.locals name with
        | None -> ()
        | Some ty -> (
          match old with
          | L o ->
            let keep = if List.mem name appends then None else Some o.len in
            let nv = match fresh g name ty ?len:keep () with L l -> l | _ -> assert false in
            let nv = match keep with None -> Dynarray.add_last h.facts (le zero nv.len); nv | Some k -> { nv with off = o.off; len = k } in
            h.env <- SM.add name (L nv) h.env
          | _ -> h.env <- SM.add name (fresh g name ty ()) h.env)))
    (List.sort compare names);
  h

and invariants_for g line (user : Ir.clause list) = user @ (try List.assoc line g.opts.extra_invariants with Not_found -> [])

and check_invs g invs (st : state) kind (site : Ir.loc) overrides =
  let env = List.fold_left (fun m (k, v) -> SM.add k v m) st.env overrides in
  List.iter
    (fun (inv : Ir.clause) ->
      let ctx = { base = st.facts; env; live = None; guard = []; bound = SM.empty; old_env = Some g.entry; result = None; spec = true; quiet = false; state = None; finfo = g.info } in
      let gl = term_of inv.cloc (ev g ctx inv.cexpr) in
      let what = if kind = "inv.entry" then "holds on entry" else "is preserved" in
      oblige g ~site ~clause:inv kind ctx gl inv.cloc (Printf.sprintf "loop invariant '%s' %s" inv.text what))
    invs

and assume_invs g invs (st : state) overrides =
  let env = List.fold_left (fun m (k, v) -> SM.add k v m) st.env overrides in
  List.iter
    (fun (inv : Ir.clause) ->
      let ctx = { base = st.facts; env; live = None; guard = []; bound = SM.empty; old_env = Some g.entry; result = None; spec = true; quiet = true; state = None; finfo = g.info } in
      Dynarray.add_last st.facts (term_of inv.cloc (ev g ctx inv.cexpr)))
    invs

and run_iteration g body st =
  let frame = { breaks = []; continues = [] } in
  g.loops <- frame :: g.loops;
  let finish () = g.loops <- List.tl g.loops in
  match block g body st with
  | e -> finish (); (e, frame)
  | exception ex -> finish (); raise ex

and loop_while g (w : Ir.stmt) (st : state) : state =
  let (loc : Ir.loc), cond, invariants, decreases, body, step = match w with Ir.While w -> (w.loc, w.cond, w.invariants, w.decreases, w.body, w.step) | _ -> assert false in
  let invs = invariants_for g loc.line invariants in
  check_invs g invs st "inv.entry" loc [];
  let names, appends = modified g (body @ step @ [ Ir.ExprStmt (loc, cond) ]) in
  let head = havoc g st names appends in
  assume_invs g invs head [];
  let c = term_of loc (ev g (state_ctx g head) cond) in
  let body_st = copy_state head in
  Dynarray.add_last body_st.facts c;
  let variant = match decreases with Some d -> Some d.cexpr | None -> List.assoc_opt loc.line g.opts.variants in
  let vloc = match decreases with Some d -> d.cloc | None -> loc in
  let vtext = match (decreases, variant) with Some d, _ -> d.text | None, Some _ -> "measure" | _ -> "" in
  let inferred = decreases = None in
  let v0 =
    match variant with
    | Some v ->
      let vctx = state_ctx g ~spec:true body_st in
      let v0 = term_of loc (ev g vctx v) in
      oblige g ~inferred "variant" vctx (le zero v0) vloc (Printf.sprintf "loop measure '%s' is non-negative" vtext);
      Some v0
    | None -> None
  in
  let end_, frame = run_iteration g body body_st in
  List.iter
    (fun it_end ->
      if it_end.alive then begin
        let it_end = block g step it_end in
        if it_end.alive then begin
          check_invs g invs it_end "inv.step" loc [];
          match (v0, variant) with
          | Some v0, Some v ->
            let vctx = state_ctx g ~spec:true it_end in
            let v1 = term_of loc (ev g vctx v) in
            oblige g ~inferred "variant" vctx (lt v1 v0) vloc (Printf.sprintf "loop measure '%s' decreases" vtext)
          | _ -> ()
        end
      end)
    (end_ :: List.rev frame.continues);
  if v0 = None then g.loop_notes <- (loc.line, "no-variant") :: g.loop_notes;
  let out = copy_state head in
  Dynarray.add_last out.facts (not_ c);
  merge g (out :: List.rev frame.breaks)

and counted_loop g (loc : Ir.loc) invariants body (st : state) lo_v hi_v idx (bind : state -> term -> unit) : state =
  let invs = invariants_for g loc.line invariants in
  let counter = idx ^ "$k" in
  let entry = copy_state st in
  entry.env <- SM.add counter (T lo_v) entry.env;
  check_invs g invs entry "inv.entry" loc [ (idx, T lo_v) ];
  let names, appends = modified g body in
  let names = if List.mem counter names then names else counter :: names in
  if not (Hashtbl.mem g.info.fn.locals counter) then Hashtbl.replace g.info.fn.locals counter TInt;
  let head = havoc g entry names appends in
  let k = match SM.find_opt counter head.env with Some (T k) -> k | _ -> assert false in
  Dynarray.add_last head.facts (le lo_v k);
  Dynarray.add_last head.facts (le k (max_ lo_v hi_v));
  assume_invs g invs head [ (idx, T k) ];
  let c = lt k hi_v in
  let body_st = copy_state head in
  Dynarray.add_last body_st.facts c;
  bind body_st k;
  let end_, frame = run_iteration g body body_st in
  List.iter
    (fun it_end ->
      if it_end.alive then begin
        let k1 = add k one in
        it_end.env <- SM.add counter (T k1) it_end.env;
        check_invs g invs it_end "inv.step" loc [ (idx, T k1) ]
      end)
    (end_ :: List.rev frame.continues);
  let out = copy_state head in
  Dynarray.add_last out.facts (not_ c);
  merge g (out :: List.rev frame.breaks)

and loop_range g (r : Ir.stmt) (st : state) : state =
  let loc, var, lo, hi, invariants, body, reeval = match r with Ir.ForRange r -> (r.loc, r.var, r.lo, r.hi, r.invariants, r.body, r.reeval) | _ -> assert false in
  let ctx = state_ctx g st in
  let lo_v = term_of loc (ev g ctx lo) and hi_v = term_of loc (ev g ctx hi) in
  let prior = SM.find_opt var st.env in
  if reeval then bound_fixed g hi body loc;
  let out = counted_loop g loc invariants body st lo_v hi_v var (fun bst k -> bst.env <- SM.add var (T k) bst.env) in
  out.env <- SM.remove (var ^ "$k") out.env;
  let has_break = ref false in
  Ir.walk_stmts (function Ir.Break _ -> has_break := true | _ -> ()) body;
  (match prior with
   | None -> out.env <- SM.remove var out.env
   | Some prior ->
     if !has_break || List.mem var (Ir.assigned_names body) then out.env <- SM.add var (fresh g var TInt ()) out.env
     else out.env <- SM.add var (T (ite (lt lo_v hi_v) (sub hi_v one) (term_of loc prior))) out.env);
  out

and bound_fixed g hi body (loc : Ir.loc) =
  let names, appends = modified g body in
  let rec changed (e : Ir.expr) =
    match e.e with
    | Builtin ("len", [ { e = Var v; _ } ]) -> if List.mem v appends then [ v ] else []
    | Var n -> if List.mem n names then [ n ] else []
    | _ ->
      let out = ref [] in
      let kids =
        match e.e with
        | Old x | Unary (_, x) | Field (x, _) -> [ x ]
        | Binary (_, a, b) | Index (a, b, _) -> [ a; b ]
        | Ite (a, b, c) -> [ a; b; c ]
        | Call (_, xs) | Builtin (_, xs) | ListLit xs -> xs
        | _ -> []
      in
      List.iter (fun k -> out := !out @ changed k) kids;
      !out
  in
  match changed hi with
  | [] -> ()
  | bad -> raise (Vc_error (Printf.sprintf "the loop bound depends on %s, which the loop body changes" (String.concat ", " (List.sort_uniq compare bad)), loc))

and loop_each g (r : Ir.stmt) (st : state) : state =
  let loc, elem, idx, seq, invariants, body = match r with Ir.ForEach r -> (r.loc, r.elem, r.idx, r.seq, r.invariants, r.body) | _ -> assert false in
  let ctx = state_ctx g st in
  let l = match ev g ctx seq with L l -> l | _ -> raise (Fallback "for-each over a non-list") in
  let names, _ = modified g body in
  let seq_vars = ref [] in
  Ir.walk_expr (fun (x : Ir.expr) -> match x.e with Var n -> seq_vars := n :: !seq_vars | _ -> ()) seq;
  let clash = List.sort_uniq compare (List.filter (fun n -> List.mem n !seq_vars) names) in
  if clash <> [] then raise (Vc_error (Printf.sprintf "the loop body changes %s while iterating over it" (String.concat ", " clash), loc));
  let before = st.env in
  let out =
    counted_loop g loc invariants body st zero l.len idx (fun bst k ->
        bst.env <- SM.add elem (T (at (l.arr, l.off) k)) bst.env;
        bst.env <- SM.add idx (T k) bst.env)
  in
  out.env <- SM.remove (idx ^ "$k") out.env;
  List.iter
    (fun name ->
      if SM.mem name before && Hashtbl.mem g.info.fn.locals name then out.env <- SM.add name (fresh g name (Hashtbl.find g.info.fn.locals name) ()) out.env
      else out.env <- SM.remove name out.env)
    [ elem; idx ];
  out

(* -- a function ------------------------------------------------------------- *)

let post_env g exit_env =
  List.fold_left (fun m (p, ty) -> SM.add p (match (ty : Ir.ty) with TList _ | TDict _ -> SM.find p exit_env | _ -> SM.find p g.entry) m) SM.empty g.info.fn.params

let check_exits g =
  let fn = g.info.fn in
  List.iter
    (fun ex ->
      if ex.value = None && fn.ret <> TNone then ()
      else begin
        let facts = Dynarray.of_list ex.efacts in
        let penv = post_env g ex.eenv in
        List.iter
          (fun (en : Ir.clause) ->
            let ctx = { base = facts; env = penv; live = None; guard = []; bound = SM.empty; old_env = Some g.entry; result = ex.value; spec = true; quiet = false; state = None; finfo = g.info } in
            let gl = term_of en.cloc (ev g ctx en.cexpr) in
            oblige g ~site:ex.eloc ~clause:en "ensures" ctx gl en.cloc (Printf.sprintf "postcondition '%s'" en.text))
          fn.ensures;
        if fn.raises <> [] then begin
          let ctx = { base = facts; env = g.entry; live = None; guard = []; bound = SM.empty; old_env = None; result = None; spec = true; quiet = true; state = None; finfo = g.info } in
          let cond = or_ (List.map (fun (r : Ir.clause) -> term_of r.cloc (ev g ctx r.cexpr)) fn.raises) in
          let r0 = List.hd fn.raises in
          oblige g ~site:ex.eloc ~clause:r0 "raises" { ctx with quiet = false } (not_ cond) r0.cloc (Printf.sprintf "returns normally although '@raises %s' holds" r0.text)
        end
      end)
    (List.rev g.exits)

let make prog info opts =
  {
    prog; info; opts; obligations = []; exits = []; loops = []; counter = 0; ids = Hashtbl.create 32; deps = []; entry = SM.empty;
    inputs = []; assumptions = []; loop_notes = []; definitional_mode = false;
  }

let run g =
  let fn = g.info.fn in
  let st = { env = SM.empty; facts = Dynarray.create (); alive = true } in
  List.iter
    (fun (p, ty) ->
      (match (ty : Ir.ty) with TClass _ | TOption _ | TDict _ | TOpaque -> raise (Fallback "object/optional/dict/opaque parameters") | _ -> ());
      let v = param_val p ty in
      st.env <- SM.add p v st.env;
      g.inputs <- (p, v) :: g.inputs;
      match v with L l -> Dynarray.add_last st.facts (le zero l.len) | _ -> ())
    fn.params;
  g.entry <- st.env;
  let ctx = state_ctx g ~spec:true st in
  List.iter (fun (r : Ir.clause) -> Dynarray.add_last st.facts (term_of r.cloc (ev g ctx r.cexpr))) fn.requires;
  let st = block g fn.body st in
  if st.alive && fn.ret <> TNone then
    oblige g "return" (state_ctx g st) ff { Ir.noloc with line = fn.end_line } (Printf.sprintf "'%s' can reach its end without returning a value" fn.name);
  if st.alive then g.exits <- { efacts = Dynarray.to_list st.facts; value = None; eenv = st.env; eloc = { Ir.noloc with line = fn.end_line } } :: g.exits;
  check_exits g;
  List.rev g.obligations
