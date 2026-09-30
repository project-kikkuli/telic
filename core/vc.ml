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
type ov = { some : term; v : term; oty : Ir.ty }  (** an optional: present iff [some] *)
type dv = { vals : term; has : term; dty : Ir.ty }  (** a finite map: [has k] says whether k is a key *)

type value =
  | T of term
  | L of lv
  | O of ov
  | D of dv
  | NoneV

let at (arr, off) i = select arr (add off i)

let term_of loc = function
  | T t -> t
  | NoneV -> raise (Vc_error ("None used as a value", loc))
  | L _ -> raise (Vc_error ("a list used as a scalar", loc))
  | O _ -> raise (Vc_error ("an optional used as a plain value", loc))
  | D _ -> raise (Vc_error ("a dict used as a scalar", loc))

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
  | TOption _ | TDict _ -> raise (Vc_error ("no single logical sort for an optional/dict", Ir.noloc))

and field_sort (ty : Ir.ty) : sort =
  match ty with
  | TOption inner ->
    let s = sort_of inner in
    Rec ("Opt_" ^ sort_tag s, [ ("some", Bool); ("val", s) ])
  | t -> sort_of t

and sort_tag = function Rec (n, _) -> n | Array (_, e) -> "Arr" ^ sort_tag e | s -> sort_name s

let complex = function Ir.TList _ | TDict _ | TOption _ -> true | _ -> false

(* how a value of [ty] is represented in logic, as named components *)
let components (ty : Ir.ty) : (string * sort) list =
  match ty with
  | TList e -> [ ("arr", Array (Int, sort_of e)); ("off", Int); ("len", Int) ]
  | TOption inner ->
    if complex inner then raise (Vc_error ("optional containers are not supported yet", Ir.noloc));
    [ ("some", Bool); ("val", sort_of inner) ]
  | TDict (k, v) ->
    if complex v then raise (Vc_error ("dict values that are containers are not supported yet", Ir.noloc));
    let ks = sort_of k in
    [ ("vals", Array (ks, sort_of v)); ("has", Array (ks, Bool)) ]
  | t -> [ ("", sort_of t) ]

let pack (ty : Ir.ty) comps =
  match (ty, comps) with
  | TList _, [ a; o; l ] -> L { arr = a; off = o; len = l; lty = ty }
  | TOption _, [ s; v ] -> O { some = s; v; oty = ty }
  | TDict _, [ v; h ] -> D { vals = v; has = h; dty = ty }
  | _, [ t ] -> T t
  | _ -> invalid_arg "pack"

let flatten = function T t -> [ t ] | L l -> [ l.arr; l.off; l.len ] | O o -> [ o.some; o.v ] | D d -> [ d.vals; d.has ] | NoneV -> []

let ite_val c a b =
  match (a, b) with
  | L x, L y -> L { arr = ite c x.arr y.arr; off = ite c x.off y.off; len = ite c x.len y.len; lty = x.lty }
  | O x, O y -> O { some = ite c x.some y.some; v = ite c x.v y.v; oty = x.oty }
  | D x, D y -> D { vals = ite c x.vals y.vals; has = ite c x.has y.has; dty = x.dty }
  | T x, T y -> T (ite c x y)
  | NoneV, NoneV -> NoneV
  | _ -> raise (Vc_error ("branches disagree on a value's shape", Ir.noloc))

let value_equal a b =
  match (a, b) with
  | T x, T y -> x == y
  | L x, L y -> x.arr == y.arr && x.off == y.off && x.len == y.len
  | O x, O y -> x.some == y.some && x.v == y.v
  | D x, D y -> x.vals == y.vals && x.has == y.has
  | NoneV, NoneV -> true
  | _ -> false

let rec default_term (s : sort) =
  match s with
  | Int -> zero
  | Real -> real (Q.of_int 0)
  | Bool -> ff
  | Str -> str ""
  | Array (_, e) -> const_array s (default_term e)
  | Rec (_, fs) -> mkrec s (List.map (fun (_, fs) -> default_term fs) fs)
  | Opaque -> const "opaque!default" Opaque
  | Unit -> zero

(* lift a plain value into an optional slot: None -> absent, x -> present x *)
let coerce v (ty : Ir.ty option) =
  match (ty, v) with
  (* an empty [] / {} takes the type of the variable it is stored in *)
  | Some (TList e as lty), L l when l.lty = TList TNone && e <> TNone -> L { arr = const_array (Array (Int, sort_of e)) (default_term (sort_of e)); off = zero; len = l.len; lty }
  | Some (TDict (k, vt) as dty), D d when (match d.dty with TDict (TNone, _) -> true | _ -> false) && k <> TNone ->
    let ks = sort_of k and vs = sort_of vt in
    D { vals = const_array (Array (ks, vs)) (default_term vs); has = const_array (Array (ks, Bool)) ff; dty }
  | Some (TOption inner as oty), NoneV -> O { some = ff; v = default_term (sort_of inner); oty }
  | Some (TOption _ as oty), T t -> O { some = tt; v = t; oty }
  | Some (TOption _), (L _ | D _) -> raise (Vc_error ("optional containers are not supported yet", Ir.noloc))
  | _ -> v

let rec ty_str (t : Ir.ty) =
  match t with
  | TInt -> "int" | TReal -> "real" | TBool -> "bool" | TStr -> "str" | TNone -> "none" | TOpaque -> "opaque"
  | TList e -> "list[" ^ ty_str e ^ "]"
  | TRecord (n, _) | TClass n | TEnum (n, _, _) -> n
  | TOption i -> ty_str i ^ "|None"
  | TDict (k, v) -> "dict[" ^ ty_str k ^ "," ^ ty_str v ^ "]"

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
  termination : bool;  (** does its recursion group need a termination proof *)
  resolve : (string * string) list;  (** call name -> function key *)
  untrusted : (string * int) list;  (** (class, index) of invariants a call through a base does not establish on self *)
}

type classinfo = {
  cname : string;
  cmod : string;  (** the module the class lives in (its invariants resolve there) *)
  cfields : (string * Ir.ty) list;
  cinvs : Ir.clause list;
  init : string option;  (** key of Cls.__init__, its own or inherited *)
  post_init : string option;
  cbases : string list;  (** checked base classes *)
  owner : (string * string) list;  (** field -> the class that introduced it *)
}

type program = {
  funcs : (string, finfo) Hashtbl.t;
  classes : classinfo list;  (** in program order *)
  resolve_tbl : (string * string, string) Hashtbl.t;  (** (module, name) -> function key *)
  heap_writes : (string, (string * string list) list) Hashtbl.t;  (** key -> [Cls.field, targets] *)
  allocates : (string, unit) Hashtbl.t;
  def_heap : (string, string list) Hashtbl.t;  (** definitional key -> heap keys its body reads *)
  by_name : (string, classinfo) Hashtbl.t;  (** classes by name *)
  hkeys : (string * string, (string * sort) list option) Hashtbl.t;  (** heap_keys, memoized (None: not modelled) *)
}

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
  aims : string list;
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
  modpath : string;  (** where names resolve *)
  env : value SM.t;
  live : state option;  (** read variables from this state (they may change mid-expression) *)
  guard : term list;
  bound : value SM.t;
  old_env : value SM.t option;
  result : value option;
  spec : bool;
  quiet : bool;
  state : state option;
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
  mutable written : (term * term * string * Ir.loc) list;  (** (path condition, object, class, where), reversed *)
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
  | t -> (
    match components t with
    | [ (_, s) ] -> T (const (Printf.sprintf "%s@%d" base n) s)
    | cs -> pack t (List.map (fun (suffix, s) -> const (Printf.sprintf "%s@%d.%s" base n suffix) s) cs))

let param_val name (ty : Ir.ty) =
  match ty with
  | TList e -> L { arr = const (name ^ ".arr") (Array (Int, sort_of e)); off = zero; len = const (name ^ ".len") Int; lty = ty }
  | TNone -> NoneV
  | t -> (
    match components t with
    | [ (_, s) ] -> T (const name s)
    | cs -> pack t (List.map (fun (suffix, s) -> const (name ^ "." ^ suffix) s) cs))

let finfo_of g key = try Hashtbl.find g.prog.funcs key with Not_found -> raise (Fallback ("unknown function " ^ key))
let resolve g modpath name = Option.map (finfo_of g) (Hashtbl.find_opt g.prog.resolve_tbl (modpath, name))
let class_of g name = Hashtbl.find_opt g.prog.by_name name
let is_init g = let n = g.info.fn.name in String.length n >= 9 && String.sub n (String.length n - 9) 9 = ".__init__"

let starts_with p s = String.length s >= String.length p && String.sub s 0 (String.length p) = p
let is_heap k = String.length k > 0 && k.[0] = '@'
let heap_env env = SM.filter (fun k _ -> is_heap k) env

(* -- the heap: one map per class field (per component), keyed by reference *)

let field_type g cls fname =
  match class_of g cls with
  | None -> raise (Vc_error ("unknown class '" ^ cls ^ "'", Ir.noloc))
  | Some c -> ( match List.assoc_opt fname c.cfields with Some t -> t | None -> raise (Vc_error (Printf.sprintf "%s has no field '%s'" cls fname, Ir.noloc)))

(* subclasses keep inherited fields where the base class does *)
let field_owner g cls fname = match class_of g cls with Some c -> (match List.assoc_opt fname c.owner with Some o -> o | None -> cls) | None -> cls

(* A field telic cannot model has no maps: only code that reads or writes it
   ([strict]) fails. *)
let heap_keys ?(strict = false) g cls fname =
  let keys =
    match Hashtbl.find_opt g.prog.hkeys (cls, fname) with
    | Some k -> k
    | None ->
      let owner = field_owner g cls fname in
      let k =
        match components (field_type g cls fname) with
        | comps -> Some (List.map (fun (suffix, srt) -> (Printf.sprintf "@%s.%s%s" owner fname (if suffix = "" then "" else "." ^ suffix), Array (Int, srt))) comps)
        | exception Vc_error _ -> None
      in
      Hashtbl.replace g.prog.hkeys (cls, fname) k;
      k
  in
  match keys with
  | Some k -> k
  | None when strict -> ignore (components (field_type g cls fname)); []
  | None -> []

let mro g cls =
  let out = ref [] in
  let rec walk c = if not (List.mem c !out) then match class_of g c with Some ci -> out := !out @ [ c ]; List.iter walk ci.cbases | None -> () in
  walk cls;
  !out

let in_hierarchy g cls = (match class_of g cls with Some c -> c.cbases <> [] | None -> false) || List.exists (fun c -> List.mem cls c.cbases) g.prog.classes

let heap_read g env cls fname r =
  pack (field_type g cls fname) (List.map (fun (k, _) -> match SM.find_opt k env with Some (T m) -> select m r | _ -> raise (Vc_error ("heap map " ^ k ^ " missing", Ir.noloc))) (heap_keys ~strict:true g cls fname))

let heap_write g (env : value SM.t) cls fname r v =
  List.fold_left2 (fun env (k, _) comp -> match SM.find_opt k env with Some (T m) -> SM.add k (T (store m r comp)) env | _ -> env) env (heap_keys ~strict:true g cls fname) (flatten v)

let all_heap_keys g = List.concat_map (fun c -> List.concat_map (fun (f, _) -> List.map fst (heap_keys g c.cname f)) c.cfields) g.prog.classes
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
    let aims = match clause with Some (c : Ir.clause) -> c.aims | None -> [] in
    let inferred = inferred || match clause with Some c -> c.inferred | None -> false in
    g.obligations <-
      { oid; func = g.info.key; kind; oloc = loc; site; message; hyps = hyps ctx; goal; clause; aims; inputs = List.rev g.inputs; deps = g.deps; exclude = excl; inferred }
      :: g.obligations
  end

let note g (loc : Ir.loc) text = if not (List.mem (loc.line, text) g.assumptions) then g.assumptions <- (loc.line, text) :: g.assumptions
let note_assumed g loc text = note g loc ("assumed: " ^ text)

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
  | Lit LNone -> coerce NoneV (Some e.ty)
  | _ -> assert false

(* zip that stops at the shorter list, like Python's *)
let rec zip xs ys = match (xs, ys) with x :: xs, y :: ys -> (x, y) :: zip xs ys | _ -> []

let spec_ctx g ?(modpath = g.info.modpath) ?old_env ?result ?(quiet = true) ?(guard = []) ~base ~env () =
  { base; modpath; env; live = None; guard; bound = SM.empty; old_env; result; spec = true; quiet; state = None }

let alloc_of env = match SM.find_opt "@alloc" env with Some (T a) -> a | _ -> raise (Vc_error ("no allocation map", Ir.noloc))

(* objects handed to a function already exist; enum values are in range *)
let rec alloc_facts g v (ty : Ir.ty) env =
  match (ty, v) with
  | TEnum (_, ms, _), T t -> [ le zero t; lt t (int_ (List.length ms)) ]
  (* an enum field of a record (a union's tag) is one of its members *)
  | TRecord (_, fs), T t -> List.concat_map (fun (n, (ft : Ir.ty)) -> match ft with TEnum _ | TRecord _ -> alloc_facts g (T (field t n)) ft env | _ -> []) fs
  | TOption (TEnum (_, ms, _)), O o -> [ implies o.some (and_ [ le zero o.v; lt o.v (int_ (List.length ms)) ]) ]
  | TClass _, T t ->
    let self_ = match SM.find_opt "self" g.entry with Some (T s) -> s == t | _ -> false in
    if is_init g && self_ then [] else [ select (alloc_of env) t ]
  | TOption (TClass _), O o -> [ implies o.some (select (alloc_of env) o.v) ]
  | _ -> []

let rec reaches_objects (t : Ir.ty) = match t with TClass _ | TOpaque -> true | TList e -> reaches_objects e | TDict (_, v) -> reaches_objects v | TOption i -> reaches_objects i | _ -> false
let extern_touches_heap g (args : Ir.expr list) = g.prog.classes <> [] && List.exists (fun (a : Ir.expr) -> reaches_objects a.ty) args

let fresh_expr (e : Ir.expr option) = match e with Some { e = ListLit _ | Call _ | New _; _ } -> true | Some { e = Builtin (("slice" | "dict_lit"), _); _ } -> true | _ -> false

let monotone_alloc pre_ new_ r = quant "forall" [ r ] (implies (select pre_ r) (select new_ r)) [ [| select new_ r |] ]

let rec first_select_on r (t : term) =
  match t.node with
  | App ("select", [| _; i |]) when i == r -> Some t
  | App (_, xs) | Fn (_, xs) -> Array.fold_left (fun acc x -> match acc with Some _ -> acc | None -> first_select_on r x) None xs
  | Quant (_, _, b, _) -> first_select_on r b
  | _ -> None

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
      | "rdiv" | "floordiv" | "fmod" | "tmod" | "tdiv" ->
        let z = lit_of_int 0 y.sort in
        let sym = match op with "rdiv" | "tdiv" -> "/" | "floordiv" -> "//" | _ -> "%" in
        oblige g "div" ctx (ne y z) loc (Printf.sprintf "divisor of '%s' is non-zero" sym);
        if not (ctx.quiet || ctx.spec) then assume ctx (ne y z);
        if op = "rdiv" then T (rdiv x y)
        else if x.sort = Real then begin
          let q = rdiv x y in
          let qi = if op = "fmod" || op = "floordiv" then floor q else ite (le (real (Q.of_int 0)) q) (floor q) (neg (floor (neg q))) in
          if op = "floordiv" then T (to_real qi) else T (sub x (mul y (to_real qi)))
        end
        else if op = "floordiv" then T (floordiv x y)
        else if op = "tdiv" then T (truncdiv x y)
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
    | D d ->
      let k = tm (ev g ctx i) in
      oblige g "key" ctx (select d.has k) loc (Printf.sprintf "key looked up in '%s' is present" (expr_name s));
      T (select d.vals k)
    | L l ->
      let i = tm (ev g ctx i) in
      let j = index_of g (l.arr, l.off, l.len) i wrap ctx loc (expr_name s) in
      T (at (l.arr, l.off) j)
    | _ -> raise (Vc_error ("indexing a non-list", loc)))
  | Field (o, f) -> (
    let obj = tm (ev g ctx o) in
    match o.ty with
    | TClass cls ->
      let env = match ctx.state with Some st -> st.env | None -> ctx.env in
      heap_read g env cls f obj
    | _ -> (
      let raw = field obj f in
      match e.ty with TOption _ -> O { some = field raw "some"; v = field raw "val"; oty = e.ty } | _ -> T raw))
  | RecordLit fs ->
    let ftys = match e.ty with TRecord (_, ftys) -> ftys | _ -> raise (Vc_error ("record literal of a non-record type", loc)) in
    let vals =
      List.map
        (fun ((_, fty), (_, x)) ->
          match coerce (ev g ctx x) (Some fty) with
          | O o -> mkrec (field_sort fty) [ o.some; o.v ]
          | v -> tm v)
        (zip ftys fs)
    in
    T (mkrec (sort_of e.ty) vals)
  | ListLit elems ->
    (* an empty [] of unknown type is a placeholder until it is stored (see coerce) *)
    let ty = match e.ty with TList TNone -> Ir.TList TInt | t -> t in
    let base = match fresh g "lit" ty ~len:zero () with L l -> l | _ -> assert false in
    let arr = ref base.arr in
    List.iteri (fun i x -> arr := store !arr (int_ i) (tm (ev g ctx x))) elems;
    L { arr = !arr; off = zero; len = int_ (List.length elems); lty = e.ty }
  | Quant q when (match q.seq with Some { ty = TDict _; _ } -> true | _ -> false) -> (
    (* over a dict's keys: every k it holds *)
    match (q.seq, q.elem) with
    | Some s, Some el -> (
      match (ev g ctx s, s.ty) with
      | D d, TDict (kty, _) ->
        let k = const (Printf.sprintf "%s!%d" el (next g)) (sort_of kty) in
        let held = select d.has k in
        let sub = sub_ctx ~cond:held ctx in
        let body = tm (ev g { sub with bound = SM.add el (T k) sub.bound } q.body) in
        if q.kind = "forall" then T (forall [ k ] (implies held body)) else T (exists [ k ] (and_ [ held; body ]))
      | _ -> raise (Vc_error ("quantifier over a non-dict", loc)))
    | _ -> raise (Vc_error ("quantifier over a dict needs a name", loc)))
  | Quant q ->
    let lo = tm (ev g ctx q.lo) and hi = tm (ev g ctx q.hi) in
    let base = match String.index_opt q.idx '$' with Some k -> String.sub q.idx 0 k | None -> q.idx in
    let i = const (Printf.sprintf "%s!%d" base (next g)) Int in
    let rng = and_ [ le lo i; lt i hi ] in
    let sub = sub_ctx ~cond:rng ctx in
    let bound = SM.add q.idx (T i) sub.bound in
    let bound =
      match (q.seq, q.elem) with
      | Some s, Some el -> ( match ev g ctx s with L l -> SM.add el (T (at (l.arr, l.off) i)) bound | _ -> raise (Vc_error ("quantifier over a non-list", loc)))
      | _ -> bound
    in
    let body = tm (ev g { sub with bound } q.body) in
    if q.kind = "forall" then T (forall [ i ] (implies rng body)) else T (exists [ i ] (and_ [ rng; body ]))
  | Builtin (name, args) -> builtin g ctx e name args
  | Call (f, args) ->
    let callee = match resolve g ctx.modpath f with Some c -> c | None -> raise (Vc_error (Printf.sprintf "unknown function '%s'" f, loc)) in
    let vals = List.map (fun (a, (_, pty)) -> coerce (ev g ctx a) (Some pty)) (zip args callee.fn.params) in
    (* a base constructor run on the object this constructor is building *)
    let ends s suffix = String.length s >= String.length suffix && String.sub s (String.length s - String.length suffix) (String.length suffix) = suffix in
    let new_self = is_init g && ends callee.fn.name ".__init__" && (match args with { e = Var "self"; _ } :: _ -> true | _ -> false) in
    call g ~new_self callee vals (List.map Option.some args) ctx loc
  | New (cls, args) -> new_object g ctx loc cls args
  | Extern (name, args) -> extern g ctx e name args

and equal g a b =
  match (a, b) with
  | L x, L y ->
    let i = const (Printf.sprintf "eq!%d" (next g)) Int in
    let same = forall [ i ] (implies (and_ [ le zero i; lt i x.len ]) (eq (at (x.arr, x.off) i) (at (y.arr, y.off) i))) in
    and_ [ eq x.len y.len; same ]
  | O o, NoneV | NoneV, O o -> not_ o.some
  | O x, O y -> and_ [ eq x.some y.some; implies x.some (eq x.v y.v) ]
  | O o, T t | T t, O o -> and_ [ o.some; eq o.v t ]
  | D _, _ | _, D _ -> raise (Vc_error ("comparing whole dicts with == is not supported", Ir.noloc))
  | T x, T y -> rec_equal x y
  | NoneV, NoneV -> tt
  | _ -> raise (Vc_error ("comparing values of different shapes", Ir.noloc))

and class_invariants ?(skip = []) g cls r env base =
  let e = SM.add "self" (T r) (heap_env env) in
  List.concat_map
    (fun cn ->
      match class_of g cn with
      | Some c when c.cinvs <> [] ->
        let ctx = spec_ctx g ~modpath:c.cmod ~base ~env:e () in
        List.concat (List.mapi (fun i (inv : Ir.clause) -> if List.mem (cn, i) skip then [] else [ (inv, term_of inv.cloc (ev g ctx inv.cexpr)) ]) c.cinvs)
      | _ -> [])
    (mro g cls)

and builtin g ctx (e : Ir.expr) name args =
  let loc = e.loc in
  let tm x = term_of loc x in
  let lit_str (a : Ir.expr) = match a.e with Lit (LStr s) -> s | Lit (LInt s) -> s | _ -> raise (Vc_error ("expected a literal", loc)) in
  let assume_ t = assume ctx t in
  match name with
  | "comp" -> comprehension g ctx e (ev g ctx (List.hd args))
  | "dict_lit" when (match e.ty with TDict (TNone, _) -> true | _ -> false) ->
    D { vals = const_array (Array (Int, Int)) zero; has = const_array (Array (Int, Bool)) ff; dty = e.ty }
  | "dict_lit" ->
    let kt, vt = match e.ty with TDict (k, v) -> (k, v) | _ -> raise (Vc_error ("dict literal of a non-dict type", loc)) in
    let ks = sort_of kt and vs = sort_of vt in
    let vals = ref (const_array (Array (ks, vs)) (default_term vs)) and has = ref (const_array (Array (ks, Bool)) ff) in
    let rec pairs = function
      | k :: v :: rest ->
        let k = tm (ev g ctx k) in
        let v = tm (coerce (ev g ctx v) (Some vt)) in
        vals := store !vals k v;
        has := store !has k tt;
        pairs rest
      | _ -> ()
    in
    pairs args;
    D { vals = !vals; has = !has; dty = e.ty }
  | _ -> (
    let vals = List.map (ev g ctx) args in
    let lst = function L l -> l | _ -> raise (Vc_error ("builtin on a non-list: " ^ name, loc)) in
    let dct = function D d -> d | _ -> raise (Vc_error ("builtin on a non-dict: " ^ name, loc)) in
    let dval d = match d.dty with TDict (_, v) -> v | _ -> assert false in
    let dkey d = match d.dty with TDict (k, _) -> k | _ -> assert false in
    let flat_rest = List.concat_map flatten (List.tl vals) in
    match (name, vals) with
    | "some", [ x ] -> coerce x (Some e.ty)
    | "is_none", [ o ] -> ( match o with NoneV -> T tt | O o -> T (not_ o.some) | _ -> T ff)
    | "unwrap", [ o ] -> (
      match o with
      | O o ->
        oblige g "none" ctx o.some loc (Printf.sprintf "'%s' is not None here" (expr_name (List.hd args)));
        T o.v
      | NoneV ->
        oblige g "none" ctx ff loc (Printf.sprintf "'%s' is not None here" (expr_name (List.hd args)));
        raise (Vc_error ("value is always None here", loc))
      | v -> v)
    | "from_opaque", [ x ] ->
      let ty = e.ty in
      let tag = ty_str ty in
      let v = pack ty (List.map (fun (suffix, srt) -> fn (Printf.sprintf "unbox.%s.%s" tag suffix) (Array.of_list (flatten x)) srt) (components ty)) in
      (match v with L l -> assume_ (le zero l.len) | _ -> ());
      (match ctx.state with
       | Some st ->
         List.iter assume_ (alloc_facts g v ty st.env);
         (match (ty, v) with TClass c, T r -> List.iter (fun (_, t) -> assume_ t) (class_invariants g c r st.env ctx.base) | _ -> ())
       | None -> ());
      note_assumed g loc "values from unchecked code have the types they are used at";
      v
    | "to_opaque", [ x ] -> T (fn ("box." ^ ty_str (List.hd args).ty) (Array.of_list (flatten x)) Opaque)
    | "opaque_op", _ ->
      let op = lit_str (List.hd args) in
      let srt = sort_of e.ty in
      let r = fn (Printf.sprintf "opaque.%s.%s" op (sort_name srt)) (Array.of_list flat_rest) srt in
      if (not ctx.spec) && not ctx.quiet then note_assumed g loc "operations on values from unchecked code do not raise";
      if e.ty = TInt && op = "len" then assume_ (le zero r);
      T r
    | "await", x :: _ ->
      (match ctx.state with Some _ when not ctx.spec -> await_havoc g ctx loc | _ -> ());
      x
    | ("enum_name" | "enum_value"), [ x ] ->
      let x = tm x in
      let items =
        match (List.hd args).ty with
        | TEnum (_, ms, vs) -> if name = "enum_name" then List.map (fun m -> str m) ms else List.map (function Json.Int i -> int_ i | Json.String s -> str s | _ -> raise (Fallback "enum values that are neither ints nor strings")) vs
        | _ -> raise (Vc_error ("enum operation on a non-enum", loc))
      in
      let n = List.length items in
      let arr = Array.of_list items in
      let out = ref arr.(n - 1) in
      for i = n - 2 downto 0 do out := ite (eq x (int_ i)) arr.(i) !out done;
      T !out
    | ("dict_keys" | "dict_values"), [ d ] ->
      let d = dct d in
      let n = next g in
      let keys = const (Printf.sprintf "keys@%d" n) (Array (Int, sort_of (dkey d))) in
      let ln = const (Printf.sprintf "keys@%d.len" n) Int in
      let i = const (Printf.sprintf "i!%d" n) Int in
      let rng = and_ [ le zero i; lt i ln ] in
      assume_ (le zero ln);
      assume_ (quant "forall" [ i ] (implies rng (select d.has (select keys i))) [ [| select keys i |] ]);
      if name = "dict_keys" then L { arr = keys; off = zero; len = ln; lty = TList (dkey d) }
      else begin
        let vs = const (Printf.sprintf "values@%d" n) (Array (Int, sort_of (dval d))) in
        let j = const (Printf.sprintf "j!%d" n) Int in
        assume_ (quant "forall" [ j ] (implies (and_ [ le zero j; lt j ln ]) (eq (select vs j) (select d.vals (select keys j)))) [ [| select vs j |] ]);
        L { arr = vs; off = zero; len = ln; lty = TList (dval d) }
      end
    | "checked", [ v; lo; hi; _ ] ->
      let tyname = match List.nth args 3 with { e = Lit (LStr t); _ } -> t | _ -> "integer" in
      let v = tm v in
      let fits = and_ [ le (tm lo) v; le v (tm hi) ] in
      oblige g "overflow" ctx fits loc (Printf.sprintf "%s arithmetic does not overflow" tyname);
      assume_ fits;
      T v
    | "in_range", [ v; lo; hi ] ->
      let v = tm v in
      assume_ (and_ [ le (tm lo) v; le v (tm hi) ]);
      T v
    | "same_len", [ xs; r ] -> let a = lst xs and b = lst r in L { b with len = a.len }
    | "list_concat", [ xs; ys ] ->
      let a = lst xs and b = lst ys in
      let n = next g in
      let arr = const (Printf.sprintf "cat@%d.arr" n) a.arr.sort in
      let ln = add a.len b.len in
      let i = const (Printf.sprintf "i!%d" n) Int and k = const (Printf.sprintf "k!%d" n) Int in
      assume_ (quant "forall" [ i ] (implies (and_ [ le zero i; lt i a.len ]) (eq (select arr i) (at (a.arr, a.off) i))) [ [| select arr i |] ]);
      assume_ (quant "forall" [ k ] (implies (and_ [ le a.len k; lt k ln ]) (eq (select arr k) (at (b.arr, b.off) (sub k a.len)))) [ [| select arr k |] ]);
      L { arr; off = zero; len = ln; lty = a.lty }
    | "dict_copy", [ d ] -> d
    | "dict_set", [ d; k; v ] ->
      let d = dct d in
      let v = tm (coerce v (Some (dval d))) in
      D { d with vals = store d.vals (tm k) v; has = store d.has (tm k) tt }
    | "dict_remove", [ d; k ] -> let d = dct d in D { d with has = store d.has (tm k) ff }
    | "dict_del", [ d; k ] ->
      let d = dct d in
      oblige g "key" ctx (select d.has (tm k)) loc (Printf.sprintf "key being deleted from '%s' is present" (expr_name (List.hd args)));
      D { d with has = store d.has (tm k) ff }
    | ("dict_has" | "dict_get_opt" | "dict_get_or"), d :: k :: rest -> (
      let d = dct d in
      let has = select d.has (tm k) and v = select d.vals (tm k) in
      match (name, rest) with
      | "dict_has", _ -> T has
      | "dict_get_opt", _ -> O { some = has; v; oty = TOption (dval d) }
      | _, [ dflt ] -> T (ite has v (tm (coerce dflt (Some (dval d)))))
      | _ -> raise (Vc_error ("dict_get_or needs a default", loc)))
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
    | "list_append", [ xs; v ] -> let l = lst xs in L { l with arr = store l.arr (add l.off l.len) (tm v); len = add l.len one }
    | "list_set", [ xs; i; v ] ->
      let l = lst xs in
      let j = index_of g (l.arr, l.off, l.len) (tm i) true ctx loc (expr_name (List.hd args)) in
      L { l with arr = store l.arr (add l.off j) (tm v) }
    | "str_concat", _ -> T (app "str.++" (Array.of_list (List.map tm vals)) Str)
    | "str_len", [ s ] -> T (app "str.len" [| tm s |] Int)
    | "str_contains", [ a; b ] -> T (app "str.contains" [| tm a; tm b |] Bool)
    | "str_startswith", [ a; b ] -> T (app "str.prefixof" [| tm b; tm a |] Bool)
    | "str_endswith", [ a; b ] -> T (app "str.suffixof" [| tm b; tm a |] Bool)
    | "str_of_int", [ a ] -> T (app "str.from_int" [| tm a |] Str)
    | "str_lt", [ a; b ] -> T (app "str.lt" [| tm a; tm b |] Bool)
    | "str_le", [ a; b ] -> T (app "str.le" [| tm a; tm b |] Bool)
    | "str_find", [ a; b ] -> T (app "str.indexof" [| tm a; tm b; zero |] Int)
    | "str_index", [ s; i ] ->
      let s = tm s and i = tm i in
      let n = app "str.len" [| s |] Int in
      oblige g "index" ctx (and_ [ le (neg n) i; lt i n ]) loc (Printf.sprintf "index into '%s' is within -len..len-1" (expr_name (List.hd args)));
      T (app "str.at" [| s; ite (lt i zero) (add i n) i |] Str)
    | "str_slice", [ s; lo; hi ] ->
      let s = tm s in
      let n = app "str.len" [| s |] Int in
      let norm b default = match b with NoneV -> default | b -> let b = tm b in ite (lt b zero) (max_ (add b n) zero) (min_ b n) in
      let lo2 = norm lo zero and hi2 = norm hi n in
      T (app "str.substr" [| s; lo2; max_ (sub hi2 lo2) zero |] Str)
    | "str_fn", _ -> T (fn ("str." ^ lit_str (List.hd args)) (Array.of_list flat_rest) (sort_of e.ty))
    | "to_real", [ x ] -> T (to_real (tm x))
    | "floor", [ x ] -> T (floor (tm x))
    | "ceil", [ x ] -> T (neg (floor (neg (tm x))))
    | "trunc", [ x ] -> let x = tm x in T (ite (le (real (Q.of_int 0)) x) (floor x) (neg (floor (neg x))))
    | "round_even", [ x ] -> T (round_even (tm x))
    | "round_up", [ x ] -> T (floor (add (tm x) (real (Q.make 1 2))))
    | "is_int", [ x ] -> T (is_int (tm x))
    | _ -> raise (Fallback ("builtin " ^ name)))

and pure g (e : Ir.expr) =
  let ok = ref true in
  Ir.walk_expr
    (fun (x : Ir.expr) ->
      match x.e with
      | Extern _ | New _ -> ok := false
      | Builtin (("await" | "from_opaque" | "comp" | "dict_keys" | "dict_values"), _) -> ok := false
      | Call (f, _) -> ( match resolve g g.info.modpath f with Some t when t.definitional -> () | _ -> ok := false)
      | _ -> ())
    e;
  !ok

and comprehension g ctx (e : Ir.expr) seq =
  let loc = e.loc in
  let seq = match seq with L l -> l | _ -> raise (Vc_error ("comprehension over a non-list", loc)) in
  let elem, body, cond =
    match e.e with
    | Builtin (_, [ _; { e = Lit (LStr el); _ }; body ]) -> (el, body, None)
    | Builtin (_, [ _; { e = Lit (LStr el); _ }; body; cond ]) -> (el, body, Some cond)
    | _ -> raise (Fallback "comprehension shape")
  in
  let n = next g in
  let arr = const (Printf.sprintf "comp@%d.arr" n) (sort_of e.ty) in
  let is_pure = pure g body && match cond with Some c -> pure g c | None -> true in
  let ln =
    match cond with
    | None -> seq.len
    | Some _ ->
      let ln = const (Printf.sprintf "comp@%d.len" n) Int in
      assume ctx (and_ [ le zero ln; le ln seq.len ]);
      ln
  in
  let i = const (Printf.sprintf "%s!%d" elem n) Int in
  let rng = and_ [ le zero i; lt i seq.len ] in
  let sub = sub_ctx ~cond:rng { ctx with spec = true; quiet = ctx.quiet || not is_pure } in
  let sub = { sub with bound = SM.add elem (T (at (seq.arr, seq.off) i)) sub.bound } in
  let result = L { arr; off = zero; len = ln; lty = e.ty } in
  if not is_pure then begin
    (match ctx.state with Some _ -> havoc_heap g ctx | None -> ());
    result
  end
  else begin
    let b = term_of loc (ev g sub body) in
    (match cond with
     | None -> assume ctx (quant "forall" [ i ] (implies rng (eq (select arr i) b)) [ [| select arr i |] ])
     | Some c ->
       ignore (ev g sub c);
       let k = const (Printf.sprintf "k!%d" n) Int and j = const (Printf.sprintf "j!%d" n) Int in
       let sub_j = { ctx with spec = true; quiet = true; bound = SM.add elem (T (at (seq.arr, seq.off) j)) ctx.bound } in
       let bj = term_of loc (ev g sub_j body) and cj = term_of loc (ev g sub_j c) in
       assume ctx
         (quant "forall" [ k ]
            (implies (and_ [ le zero k; lt k ln ]) (exists [ j ] (and_ [ le zero j; lt j seq.len; cj; eq (select arr k) bj ])))
            [ [| select arr k |] ]));
    result
  end

and await_havoc g ctx (loc : Ir.loc) =
  match ctx.state with
  | None -> ()
  | Some st ->
    if g.prog.classes <> [] then begin
      note_assumed g loc "objects created during this call are not shared with concurrent tasks";
      let alloc0 = alloc_of g.entry in
      SM.iter
        (fun key v ->
          match v with
          | T old when is_heap key && key <> "@alloc" ->
            let nw = const (Printf.sprintf "%s@await%d.%d" (String.sub key 1 (String.length key - 1)) loc.line (next g)) old.sort in
            let r = const (Printf.sprintf "r!%d" (next g)) Int in
            assume ctx (quant "forall" [ r ] (implies (not_ (select alloc0 r)) (eq (select nw r) (select old r))) [ [| select nw r |] ]);
            st.env <- SM.add key (T nw) st.env
          | _ -> ())
        st.env;
      List.iter
        (fun c ->
          if c.cinvs <> [] && not (in_hierarchy g c.cname) then begin
            let r = const (Printf.sprintf "r!%d" (next g)) Int in
            List.iter
              (fun (_, t) ->
                match first_select_on r t with
                | None -> ()
                | Some sel ->
                  note_assumed g loc "other tasks do not await while an object's invariant is broken";
                  assume ctx (quant "forall" [ r ] (implies (select alloc0 r) t) [ [| sel |] ]))
              (class_invariants g c.cname r st.env ctx.base)
          end)
        g.prog.classes
    end

and havoc_heap g ctx =
  match ctx.state with
  | None -> ()
  | Some st ->
    SM.iter
      (fun key v ->
        match v with
        | T old when is_heap key && key <> "@alloc" -> st.env <- SM.add key (T (const (Printf.sprintf "%s@%d" (String.sub key 1 (String.length key - 1)) (next g)) old.sort)) st.env
        | _ -> ())
      st.env;
    let pre_ = alloc_of st.env in
    let na = const (Printf.sprintf "alloc@%d" (next g)) (Array (Int, Bool)) in
    let r = const (Printf.sprintf "r!%d" (next g)) Int in
    assume ctx (monotone_alloc pre_ na r);
    st.env <- SM.add "@alloc" (T na) st.env

and extern g ctx (e : Ir.expr) name args =
  let loc = e.loc in
  let _vals = List.map (ev g ctx) args in
  if ctx.spec then raise (Vc_error (Printf.sprintf "specifications cannot call unchecked code ('%s')" name, loc));
  if not (starts_with "caught exception" name || starts_with "default of" name) then note_assumed g loc ("call:" ^ name);
  let fn = g.info.fn in
  (match ctx.state with
   | Some st ->
     (* it may change any list/dict it is handed (and, if it can reach
        objects, any object); escaped closures may run now *)
     let escaped = List.sort compare fn.escaped in
     List.iter
       (fun n ->
         match (SM.find_opt n st.env, Hashtbl.find_opt fn.locals n) with
         | Some (L _ | D _), _ | None, _ | _, None -> ()
         | Some _, Some ty -> st.env <- SM.add n (fresh g n ty ()) st.env)
       escaped;
     let touched = List.filter_map (fun (a : Ir.expr) -> match a.e with Var n -> Some (n, a.ty) | _ -> None) args @ List.filter_map (fun n -> Option.map (fun t -> (n, t)) (Hashtbl.find_opt fn.locals n)) escaped in
     List.iter
       (fun (n, aty) ->
         match SM.find_opt n st.env with
         | Some (L _ | D _) ->
           let ty = match Hashtbl.find_opt fn.locals n with Some t -> t | None -> aty in
           let nv = fresh g n ty () in
           (match nv with L l -> assume ctx (le zero l.len) | _ -> ());
           st.env <- SM.add n nv st.env
         | _ -> ())
       touched;
     if extern_touches_heap g args || (g.prog.classes <> [] && fn.escaped <> []) then havoc_heap g ctx
   | None -> ());
  let r =
    if e.ty = TNone then NoneV
    else
      let short = match String.rindex_opt name '.' with Some k -> String.sub name (k + 1) (String.length name - k - 1) | None -> name in
      fresh g (short ^ "()") e.ty ()
  in
  (match r with L l -> assume ctx (le zero l.len) | _ -> ());
  (match (ctx.state, r) with
   | Some st, r when r <> NoneV ->
     List.iter (assume ctx) (alloc_facts g r e.ty st.env);
     (match (e.ty, r) with TClass c, T t -> List.iter (fun (_, x) -> assume ctx x) (class_invariants g c t st.env ctx.base) | _ -> ())
   | _ -> ());
  r

and new_object g ctx loc cls args =
  if ctx.spec then raise (Vc_error ("specifications cannot create objects", loc));
  let st = match ctx.state with Some st -> st | None -> raise (Vc_error ("objects can only be created in code", loc)) in
  let c = match class_of g cls with Some c -> c | None -> raise (Vc_error (Printf.sprintf "unknown class '%s'" cls, loc)) in
  let ptys = match c.init with Some k -> List.map snd (List.tl (finfo_of g k).fn.params) | None -> List.map snd c.cfields in
  let vals = List.map (fun (a, t) -> coerce (ev g ctx a) (Some t)) (zip args ptys) in
  let alloc = alloc_of st.env in
  let r = const (Printf.sprintf "%s@new%d" cls (next g)) Int in
  assume ctx (not_ (select alloc r));
  st.env <- SM.add "@alloc" (T (store alloc r tt)) st.env;
  let check_invariants () =
    List.iter
      (fun ((inv : Ir.clause), t) ->
        oblige g ~site:loc ~clause:inv "class.inv" ctx t inv.cloc (Printf.sprintf "new %s satisfies its invariant '%s'" cls inv.text);
        assume ctx t)
      (class_invariants g cls r st.env ctx.base)
  in
  match c.init with
  | Some k ->
    ignore (call g ~new_self:true (finfo_of g k) (T r :: vals) (None :: List.map Option.some args) ctx loc);
    (* an inherited constructor establishes its own class's invariants; this class's are shown here *)
    let own = "::" ^ cls ^ ".__init__" in
    if not (String.length k >= String.length own && String.sub k (String.length k - String.length own) (String.length own) = own) then check_invariants ();
    T r
  | None -> (
    List.iter (fun ((f, _), v) -> st.env <- heap_write g st.env cls f r v) (zip c.cfields vals);
    match c.post_init with
    | Some k ->
      ignore (call g ~new_self:true (finfo_of g k) [ T r ] [ None ] ctx loc);
      T r
    | None ->
      check_invariants ();
      T r)

and call g ?(new_self = false) (callee : finfo) (args : value list) (arg_exprs : Ir.expr option list) ctx loc : value =
  let fn = callee.fn in
  (* a list/dict argument is a reference: a later argument's mutation shows *)
  let args =
    match ctx.state with
    | Some st -> List.map (fun (a_e, a) -> match (a_e, a) with Some { Ir.e = Var n; _ }, (L _ | D _) -> (match SM.find_opt n st.env with Some v -> v | None -> a) | _ -> a) (zip arg_exprs args)
    | None -> args
  in
  let muts = callee.mutated in
  let list_vars = List.filter_map (fun (a_e, (_, pty)) -> match (a_e, pty) with Some { Ir.e = Var n; _ }, (Ir.TList _ | TDict _) -> Some n | _ -> None) (zip arg_exprs fn.params) in
  if muts <> [] && List.length list_vars <> List.length (List.sort_uniq compare list_vars) then
    raise (Vc_error (Printf.sprintf "the same list is passed twice to '%s', which mutates a list parameter; the two parameters would alias" fn.name, loc));
  List.iter
    (fun ((p, _), a_e) ->
      let is_var = match a_e with Some { Ir.e = Var _; _ } -> true | _ -> false in
      if List.mem p muts && (not is_var) && not (fresh_expr a_e) then
        raise (Vc_error (Printf.sprintf "'%s' mutates its list parameter '%s'; pass a variable (or a copy) so the change is tracked" fn.name p, loc)))
    (zip fn.params arg_exprs);
  let pmap = List.fold_left (fun m ((p, _), a) -> SM.add p a m) SM.empty (zip fn.params args) in
  let heap_pre = heap_env (match ctx.state with Some st -> st.env | None -> ctx.env) in
  let with_pmap h = SM.union (fun _ _ b -> Some b) h pmap in
  let definitional = callee.definitional in
  if ctx.spec && not definitional then raise (Vc_error (Printf.sprintf "specs may only call pure (loop-free, mutation-free) functions; '%s' is not" fn.name, loc));
  let cctx = { ctx with env = with_pmap heap_pre; modpath = callee.modpath; live = None; bound = SM.empty; old_env = None; result = None; spec = true; quiet = true; state = None } in
  List.iter
    (fun (rq : Ir.clause) ->
      let gl = term_of loc (ev g cctx rq.cexpr) in
      oblige g ~clause:rq "call" ctx gl loc (Printf.sprintf "call to '%s' satisfies '@requires %s'" fn.name rq.text))
    fn.requires;
  if not ctx.spec then
    List.iteri
      (fun i ((p, pty), a) ->
        match (pty, a) with
        | Ir.TClass c, T r when not (new_self && i = 0) ->
          List.iter
            (fun ((inv : Ir.clause), t) -> oblige g ~clause:inv "call" ctx t loc (Printf.sprintf "'%s' satisfies the invariant of %s ('%s') when calling '%s'" p c inv.text fn.name))
            (class_invariants g c r heap_pre ctx.base)
        | _ -> ())
      (zip fn.params args);
  if fn.raises <> [] && not ctx.spec then begin
    let rc = or_ (List.map (fun (r : Ir.clause) -> term_of loc (ev g cctx r.cexpr)) fn.raises) in
    oblige g "call" ctx (not_ rc) loc (Printf.sprintf "call to '%s' cannot raise ('@raises %s')" fn.name (List.hd fn.raises).text)
  end;
  if same_scc g g.info.key callee.key && g.info.termination then recursion_check g callee pmap ctx loc;
  if not (List.mem callee.key g.deps) then g.deps <- g.deps @ [ callee.key ];
  let r =
    if definitional then apply_def g callee args heap_pre
    else if fn.ret = TNone then NoneV
    else begin
      let short = match String.rindex_opt fn.name '.' with Some k -> String.sub fn.name (k + 1) (String.length fn.name - k - 1) | None -> fn.name in
      let r = fresh g (short ^ "()") fn.ret () in
      (match ctx.state with Some st -> List.iter (assume ctx) (alloc_facts g r fn.ret st.env) | None -> ());
      r
    end
  in
  let post = ref pmap in
  (match ctx.state with
   | Some st when not ctx.spec ->
     List.iter
       (fun ((p, pty), a_e) ->
         match a_e with
         | Some { Ir.e = Var n; _ } when List.mem p muts -> (
           match SM.find_opt n st.env with
           | Some (D _) ->
             let nd = fresh g n pty () in
             st.env <- SM.add n nd st.env;
             post := SM.add p nd !post
           | Some (L old) ->
             let keep = if List.mem p callee.appends then None else Some old.len in
             let nv = match fresh g n pty ?len:keep () with L l -> l | _ -> assert false in
             let nv = match keep with Some k -> { nv with off = old.off; len = k } | None -> assume ctx (le zero nv.len); nv in
             st.env <- SM.add n (L nv) st.env;
             post := SM.add p (L nv) !post
           | _ -> raise (Vc_error ("mutated argument is not a list", loc)))
         | _ -> ())
       (zip fn.params arg_exprs);
     havoc_call g callee args ctx;
     post := SM.union (fun _ _ b -> Some b) !post (heap_env st.env)
   | _ -> ());
  if (not ctx.spec) && fn.ensures <> [] && not g.definitional_mode then begin
    let ectx = { cctx with env = !post; old_env = Some (with_pmap heap_pre); result = (match r with NoneV -> None | r -> Some r) } in
    List.iter (fun (en : Ir.clause) -> assume ctx (term_of loc (ev g ectx en.cexpr))) fn.ensures
  end;
  (match ctx.state with
   | Some st when not ctx.spec ->
     List.iter
       (fun ((_, pty), a) -> match (pty, a) with Ir.TClass c, T r -> List.iter (fun (_, t) -> assume ctx t) (class_invariants g c r st.env ctx.base) | _ -> ())
       (zip fn.params args)
   | _ -> ());
  r

(* the heap after a call: only the fields the callee may write change, and
   only on the objects it may write them on *)
and havoc_call g (callee : finfo) args ctx =
  match ctx.state with
  | None -> ()
  | Some st ->
    let alloc_pre = alloc_of st.env in
    let names = List.map fst callee.fn.params in
    let writes = try Hashtbl.find g.prog.heap_writes callee.key with Not_found -> [] in
    List.iter
      (fun (cls_field, targets) ->
        let k = String.index cls_field '.' in
        let c = String.sub cls_field 0 k and f = String.sub cls_field (k + 1) (String.length cls_field - k - 1) in
        let refs =
          List.filter_map
            (fun t ->
              match List.find_index (( = ) t) names with
              | Some i -> ( match List.nth_opt args i with Some (T x) -> Some x | Some _ -> raise (Fallback "write through an optional object") | None -> None)
              | None -> None)
            targets
        in
        List.iter
          (fun (key, srt) ->
            match SM.find_opt key st.env with
            | Some (T old) ->
              let nw = const (Printf.sprintf "%s@%d" (String.sub key 1 (String.length key - 1)) (next g)) srt in
              st.env <- SM.add key (T nw) st.env;
              if not (List.mem "*" targets) then begin
                let r = const (Printf.sprintf "r!%d" (next g)) Int in
                let untouched = and_ (select alloc_pre r :: List.map (fun x -> ne r x) refs) in
                assume ctx (quant "forall" [ r ] (implies untouched (eq (select nw r) (select old r))) [ [| select nw r |] ])
              end
            | _ -> ())
          (heap_keys g c f))
      writes;
    if Hashtbl.mem g.prog.allocates callee.key then begin
      let na = const (Printf.sprintf "alloc@%d" (next g)) (Array (Int, Bool)) in
      let r = const (Printf.sprintf "r!%d" (next g)) Int in
      assume ctx (monotone_alloc alloc_pre na r);
      st.env <- SM.add "@alloc" (T na) st.env
    end

and apply_def g (callee : finfo) args heap =
  let hk = try Hashtbl.find g.prog.def_heap callee.key with Not_found -> [] in
  let extra =
    List.map (fun k -> match SM.find_opt k heap with Some (T t) -> t | _ -> raise (Vc_error (Printf.sprintf "'%s' reads object fields that are not available here" callee.fn.name, Ir.noloc))) hk
  in
  T (fn callee.logic_name (Array.of_list (List.concat_map flatten args @ extra)) (sort_of callee.fn.ret))

and recursion_check g (callee : finfo) pmap ctx loc =
  let me = match List.assoc_opt g.info.key g.opts.measures with Some m -> Some m | None -> Option.map (fun (c : Ir.clause) -> c.cexpr) g.info.fn.decreases in
  let them = match List.assoc_opt callee.key g.opts.measures with Some m -> Some m | None -> Option.map (fun (c : Ir.clause) -> c.cexpr) callee.fn.decreases in
  match (me, them) with
  | Some me, Some them ->
    let mctx = { ctx with env = g.entry; modpath = g.info.modpath; live = None; bound = SM.empty; spec = true; quiet = true; state = None } in
    let m0 = term_of loc (ev g mctx me) in
    let cctx = { ctx with env = pmap; modpath = callee.modpath; live = None; bound = SM.empty; spec = true; quiet = true; state = None } in
    let m1 = term_of loc (ev g cctx them) in
    let inferred = g.info.fn.decreases = None in
    oblige g ~inferred "variant" ctx (le zero m0) loc "recursion measure is non-negative";
    oblige g ~inferred "variant" ctx (lt m1 m0) loc (Printf.sprintf "recursive call to '%s' decreases the measure" callee.fn.name)
  | _ -> oblige g "variant" ctx ff loc (Printf.sprintf "recursive call to '%s' terminates (add '@decreases <measure>')" callee.fn.name)

(* -- statements ----------------------------------------------------------- *)

let state_ctx g ?(spec = false) (st : state) =
  { base = st.facts; modpath = g.info.modpath; env = st.env; live = Some st; guard = []; bound = SM.empty; old_env = None; result = None; spec; quiet = false; state = Some st }

let rec block g stmts (st : state) : state = List.fold_left (fun st s -> if st.alive then stmt g s st else st) st stmts

and stmt g (s : Ir.stmt) (st : state) : state =
  match s with
  | Assign (_, name, v) ->
    let x = coerce (ev g (state_ctx g st) v) (Hashtbl.find_opt g.info.fn.locals name) in
    st.env <- SM.add name x st.env;
    st
  | FieldAssign (loc, obj, cls, f, v) ->
    let ctx = state_ctx g st in
    let r = term_of loc (ev g ctx obj) in
    let x = coerce (ev g ctx v) (Some (field_type g cls f)) in
    st.env <- heap_write g st.env cls f r x;
    g.written <- (and_ (Dynarray.to_list st.facts), r, cls, loc) :: g.written;
    st
  | DictDel (loc, name, k, strict) -> (
    match SM.find_opt name st.env with
    | Some (D d) ->
      let ctx = state_ctx g st in
      let k = term_of loc (ev g ctx k) in
      if strict then oblige g "key" ctx (select d.has k) loc (Printf.sprintf "key being deleted from '%s' is present" name);
      st.env <- SM.add name (D { d with has = store d.has k ff }) st.env;
      st
    | _ -> raise (Vc_error ("del on a non-dict", loc)))
  | IndexAssign (loc, name, i, v, wrap) -> (
    match SM.find_opt name st.env with
    | Some (D d) ->
      let ctx = state_ctx g st in
      let k = term_of loc (ev g ctx i) in
      let vt = match d.dty with TDict (_, vt) -> vt | _ -> assert false in
      let x = term_of loc (coerce (ev g ctx v) (Some vt)) in
      st.env <- SM.add name (D { d with vals = store d.vals k x; has = store d.has k tt }) st.env;
      st
    | Some (L l) ->
      let ctx = state_ctx g st in
      let j = index_of g (l.arr, l.off, l.len) (term_of loc (ev g ctx i)) wrap ctx loc name in
      let x = term_of loc (ev g ctx v) in
      let l = match SM.find_opt name st.env with Some (L l) -> l | _ -> l in
      st.env <- SM.add name (L { l with arr = store l.arr (add l.off j) x }) st.env;
      st
    | _ -> raise (Vc_error ("index assignment to a non-list", loc)))
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
    let x = match v with Some v -> Some (coerce (ev g (state_ctx g st) v) (Some g.info.fn.ret)) | None -> None in
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
  | Try (_, body, handlers, orelse, finalbody) ->
    let entry = copy_state st in
    (* which way control goes is a free choice: each branch carries its own path condition *)
    let choice = const (Printf.sprintf "raised@%d" (next g)) Int in
    Dynarray.add_last st.facts (eq choice zero);
    let normal = block g body st in
    let normal = if normal.alive then block g orelse normal else normal in
    let outs =
      if handlers = [] then [ normal ]
      else begin
        let names, appends = modified g body in
        normal
        :: List.mapi
             (fun i h ->
               let hst = havoc g entry names appends in
               Dynarray.add_last hst.facts (eq choice (int_ (i + 1)));
               block g h hst)
             handlers
      end
    in
    let out = merge g outs in
    if out.alive && finalbody <> [] then block g finalbody out else out
  | Raise (loc, what, caught) ->
    if caught then (st.alive <- false; st)
    else begin
      let ctx = state_ctx g st in
      (if g.info.fn.raises <> [] then begin
         let ectx = { ctx with env = g.entry; live = None; spec = true; quiet = true } in
         let cond = or_ (List.map (fun (r : Ir.clause) -> term_of loc (ev g ectx r.cexpr)) g.info.fn.raises) in
         oblige g "raise" ctx cond loc (Printf.sprintf "raise %s outside '@raises %s'" what (List.hd g.info.fn.raises).text)
       end
       else if g.info.fn.requires <> [] || g.info.fn.ensures <> [] then
         oblige g "raise" ctx ff loc (Printf.sprintf "raise %s is reachable (add '@raises <condition>' if intended)" what)
       (* without a contract, an explicit raise is what the function does, not a failure *));
      st.alive <- false;
      st
    end
  | ExprStmt (_, e) ->
    ignore (ev g (state_ctx g st) e);
    st
  | Unsupported (loc, reason) -> raise (Vc_error (reason, loc))

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
  (* sets kept as lists (their order names the havocked constants) plus a
     table for membership: a program with many classes has thousands of heap
     keys, and list membership made this quadratic *)
  let names = ref (Ir.assigned_names body) and appends = ref [] in
  let seen_n = Hashtbl.create 64 and seen_a = Hashtbl.create 16 in
  List.iter (fun n -> Hashtbl.replace seen_n n ()) !names;
  let addn n = if not (Hashtbl.mem seen_n n) then (Hashtbl.add seen_n n (); names := n :: !names) in
  let adda n = if not (Hashtbl.mem seen_a n) then (Hashtbl.add seen_a n (); appends := n :: !appends) in
  let add_writes key =
    List.iter
      (fun (cf, _) ->
        let k = String.index cf '.' in
        List.iter (fun (hk, _) -> addn hk) (heap_keys g (String.sub cf 0 k) (String.sub cf (k + 1) (String.length cf - k - 1))))
      (try Hashtbl.find g.prog.heap_writes key with Not_found -> [])
  in
  Ir.walk_stmts
    (fun s ->
      (match s with
       | Append (_, n, _) -> adda n
       | Assign (_, n, _) -> ( match Hashtbl.find_opt g.info.fn.locals n with Some (TList _) -> adda n | _ -> ())
       | FieldAssign (_, _, cls, f, _) -> List.iter (fun (hk, _) -> addn hk) (heap_keys g cls f)
       | _ -> ());
      List.iter
        (fun e ->
          Ir.walk_expr
            (fun (x : Ir.expr) ->
              match x.e with
              | New (cls, _) -> (
                addn "@alloc";
                match class_of g cls with
                | Some c -> (
                  match c.init with
                  | Some k -> add_writes k
                  | None ->
                    List.iter (fun (f, _) -> List.iter (fun (hk, _) -> addn hk) (heap_keys g cls f)) c.cfields;
                    Option.iter add_writes c.post_init)
                | None -> ())
              | Extern (_, args) ->
                List.iter (fun (a : Ir.expr) -> match (a.e, a.ty) with Var n, (TList _ | TDict _) -> addn n; adda n | _ -> ()) args;
                if extern_touches_heap g args then begin
                  addn "@alloc";
                  List.iter addn (all_heap_keys g)
                end
              | Call (f, args) -> (
                match resolve g g.info.modpath f with
                | Some tgt ->
                  if Hashtbl.mem g.prog.allocates tgt.key then addn "@alloc";
                  add_writes tgt.key;
                  List.iter
                    (fun ((p, _), (a : Ir.expr)) ->
                      match a.e with
                      | Var n when List.mem p tgt.mutated -> addn n; if List.mem p tgt.appends then adda n
                      | _ -> ())
                    (zip tgt.fn.params args)
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
      | Some old when is_heap name -> (
        match old with
        | T o ->
          let nw = const (Printf.sprintf "%s@%d" (String.sub name 1 (String.length name - 1)) (next g)) o.sort in
          h.env <- SM.add name (T nw) h.env;
          if name = "@alloc" then begin
            let r = const (Printf.sprintf "r!%d" (next g)) Int in
            Dynarray.add_last h.facts (monotone_alloc o nw r)
          end
        | _ -> ())
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
      let ctx = spec_ctx g ~old_env:g.entry ~quiet:false ~base:st.facts ~env () in
      let gl = term_of inv.cloc (ev g ctx inv.cexpr) in
      let what = if kind = "inv.entry" then "holds on entry" else "is preserved" in
      oblige g ~site ~clause:inv kind ctx gl inv.cloc (Printf.sprintf "loop invariant '%s' %s" inv.text what))
    invs

and assume_invs g invs (st : state) overrides =
  let env = List.fold_left (fun m (k, v) -> SM.add k v m) st.env overrides in
  List.iter
    (fun (inv : Ir.clause) ->
      let ctx = spec_ctx g ~old_env:g.entry ~base:st.facts ~env () in
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
  let l = match ev g ctx seq with L l -> l | _ -> raise (Vc_error ("for-each over a non-list", loc)) in
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

(* what a caller can observe: scalar parameters keep their entry values; list
   and dict parameters show their final contents; fields come from the final heap *)
let post_env g exit_env =
  List.fold_left
    (fun m (p, ty) -> SM.add p (match (ty : Ir.ty) with TList _ | TDict _ -> SM.find p exit_env | _ -> SM.find p g.entry) m)
    (heap_env exit_env) g.info.fn.params

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
            let ctx = spec_ctx g ~old_env:g.entry ?result:ex.value ~quiet:false ~base:facts ~env:penv () in
            let gl = term_of en.cloc (ev g ctx en.cexpr) in
            oblige g ~site:ex.eloc ~clause:en "ensures" ctx gl en.cloc (Printf.sprintf "postcondition '%s'" en.text))
          fn.ensures;
        (* objects the function could have changed satisfy their invariants again *)
        let param_refs = ref [] in
        List.iter
          (fun (p, (ty : Ir.ty)) ->
            match (ty, SM.find_opt p g.entry) with
            | TClass c, Some (T r) ->
              param_refs := r :: !param_refs;
              let ctx = spec_ctx g ~quiet:false ~base:facts ~env:ex.eenv () in
              List.iter
                (fun ((inv : Ir.clause), t) ->
                  oblige g ~site:ex.eloc ~clause:inv "class.inv" ctx t inv.cloc (Printf.sprintf "invariant of %s ('%s') holds for '%s' on return" c inv.text p))
                (class_invariants g c r ex.eenv facts)
            | _ -> ())
          fn.params;
        let seen = ref [] in
        List.iter
          (fun (pc, r, cls, (wloc : Ir.loc)) ->
            if not (List.memq r !param_refs || List.exists (fun (r', c') -> r' == r && c' = cls) !seen) then begin
              seen := (r, cls) :: !seen;
              let ctx = spec_ctx g ~quiet:false ~base:facts ~env:ex.eenv () in
              List.iter
                (fun ((inv : Ir.clause), t) ->
                  oblige g ~site:ex.eloc ~clause:inv "class.inv" ctx (implies pc t) inv.cloc
                    (Printf.sprintf "invariant of %s ('%s') holds on return for the object written at line %d" cls inv.text wloc.line))
                (class_invariants g cls r ex.eenv facts)
            end)
          (List.rev g.written);
        if fn.raises <> [] then begin
          let ctx = spec_ctx g ~base:facts ~env:g.entry () in
          let cond = or_ (List.map (fun (r : Ir.clause) -> term_of r.cloc (ev g ctx r.cexpr)) fn.raises) in
          let r0 = List.hd fn.raises in
          oblige g ~site:ex.eloc ~clause:r0 "raises" { ctx with quiet = false } (not_ cond) r0.cloc (Printf.sprintf "returns normally although '@raises %s' holds" r0.text)
        end
      end)
    (List.rev g.exits)

let make prog info opts =
  {
    prog; info; opts; obligations = []; exits = []; loops = []; counter = 0; ids = Hashtbl.create 32; deps = []; entry = SM.empty;
    inputs = []; assumptions = []; loop_notes = []; definitional_mode = false; written = [];
  }

let run g =
  let fn = g.info.fn in
  let st = { env = SM.empty; facts = Dynarray.create (); alive = true } in
  (* the heap: one map per class field component, and the allocation map *)
  List.iter
    (fun c -> List.iter (fun (f, _) -> List.iter (fun (k, srt) -> if not (SM.mem k st.env) then st.env <- SM.add k (T (const (String.sub k 1 (String.length k - 1)) srt)) st.env) (heap_keys g c.cname f)) c.cfields)
    g.prog.classes;
  st.env <- SM.add "@alloc" (T (const "alloc" (Array (Int, Bool)))) st.env;
  List.iter
    (fun (p, ty) ->
      let v = param_val p ty in
      st.env <- SM.add p v st.env;
      g.inputs <- (p, v) :: g.inputs;
      (match v with L l -> Dynarray.add_last st.facts (le zero l.len) | _ -> ());
      List.iter (Dynarray.add_last st.facts) (alloc_facts g v ty st.env))
    fn.params;
  g.entry <- st.env;
  (* callers establish the invariants of the objects they pass (a constructor's own self is still being built) *)
  List.iter
    (fun (p, (ty : Ir.ty)) ->
      match (ty, SM.find_opt p st.env) with
      | TClass c, Some (T r) when not (is_init g && p = "self") ->
        let skip = if p = "self" then g.info.untrusted else [] in
        List.iter (fun (_, t) -> Dynarray.add_last st.facts t) (class_invariants ~skip g c r st.env st.facts)
      | _ -> ())
    fn.params;
  let ctx = state_ctx g ~spec:true st in
  List.iter (fun (r : Ir.clause) -> Dynarray.add_last st.facts (term_of r.cloc (ev g ctx r.cexpr))) fn.requires;
  let st = block g fn.body st in
  if st.alive && fn.ret <> TNone then
    oblige g "return" (state_ctx g st) ff { Ir.noloc with line = fn.end_line } (Printf.sprintf "'%s' can reach its end without returning a value" fn.name);
  if st.alive then g.exits <- { efacts = Dynarray.to_list st.facts; value = None; eenv = st.env; eloc = { Ir.noloc with line = fn.end_line } } :: g.exits;
  check_exits g;
  List.rev g.obligations
