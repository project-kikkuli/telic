(* Verification-condition generation by symbolic execution: a port of
   telic/vcgen.py. Each function is executed from a state where its
   parameters are fresh constants and its @requires hold; every point where
   the program or its contract can go wrong becomes one obligation. Branches
   are merged with ite, calls are modular (prove the callee's @requires,
   assume its @ensures), loops are cut by their invariants. *)

open Term
open Ir
module SM = Map.Make (String)

exception Vc_error of string * Ir.loc
exception Fallback of string  (** outside what this engine models yet *)

(* how deep an immutable structure is: every part of it is shallower *)
let depth x = fn "struct.depth" [| x |] Int

(* -- values ------------------------------------------------------------ *)

type value =
  | T of term
  | L of lv
  | O of ov
  | D of dv
  | NoneV

and lv = { arr : term; off : term; len : term; py_tags : term; py_ints : term; py_floats : term; ref : term; view : term; lty : Ir.ty }
and ov = { some : term; v : value; oty : Ir.ty }  (** an optional: present iff [some] *)
and dv = { vals : term; has : term; ref : term; dty : Ir.ty }  (** a finite map: [has k] says whether k is a key *)

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
  | TReal -> Float64
  | TPythonNumber -> Rec ("PythonNumber", [ ("is_int", Bool); ("integer", Int); ("floating", Float64) ])
  | TFloat32 -> Float32
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
let rec components (ty : Ir.ty) : (string * sort) list =
  match ty with
  | TList TPythonNumber -> [ ("arr", Array (Int, sort_of TPythonNumber)); ("off", Int); ("len", Int); ("ref", Int); ("view", Bool) ]
  | TList e -> [ ("arr", Array (Int, sort_of e)); ("off", Int); ("len", Int); ("py_tags", Array (Int, Bool)); ("py_ints", Array (Int, Int)); ("py_floats", Array (Int, Float64)); ("ref", Int); ("view", Bool) ]
  | TOption inner ->
    ("some", Bool) :: List.map (fun (n, s) -> ((if n = "" then "val" else "val." ^ n), s)) (components inner)
  | TDict (k, v) ->
    let ks = sort_of k in
    [ ("vals", Array (ks, sort_of v)); ("has", Array (ks, Bool)); ("ref", Int) ]
  | t -> [ ("", sort_of t) ]

let rec pack (ty : Ir.ty) comps =
  match (ty, comps) with
  | TList TPythonNumber, [ a; o; l; r; view ] -> L { arr = a; off = o; len = l; py_tags = const_array (Array (Int, Bool)) ff; py_ints = const_array (Array (Int, Int)) zero; py_floats = const_array (Array (Int, Float64)) (fval 0.0); ref = r; view; lty = ty }
  | TList _, [ a; o; l; tags; ints; floats; r; view ] -> L { arr = a; off = o; len = l; py_tags = tags; py_ints = ints; py_floats = floats; ref = r; view; lty = ty }
  | TOption inner, s :: rest -> O { some = s; v = pack inner rest; oty = ty }
  | TDict _, [ v; h; r ] -> D { vals = v; has = h; ref = r; dty = ty }
  | _, [ t ] -> T t
  | _ -> invalid_arg "pack"

let rec flatten = function T t -> [ t ] | L l when l.lty = TList TPythonNumber -> [ l.arr; l.off; l.len; l.ref; l.view ] | L l -> [ l.arr; l.off; l.len; l.py_tags; l.py_ints; l.py_floats; l.ref; l.view ] | O o -> o.some :: flatten o.v | D d -> [ d.vals; d.has; d.ref ] | NoneV -> []

let list_value ?(view = ff) arr off len ref (lty : Ir.ty) =
  let tags, ints, floats =
    match lty with
    | Ir.TList Ir.TInt -> (const_array (Array (Int, Bool)) tt, arr, const_array (Array (Int, Float64)) (fval 0.0))
    | Ir.TList (Ir.TReal | Ir.TFloat32) -> (const_array (Array (Int, Bool)) ff, const_array (Array (Int, Int)) zero, arr)
    | _ -> (const_array (Array (Int, Bool)) ff, const_array (Array (Int, Int)) zero, const_array (Array (Int, Float64)) (fval 0.0))
  in
  { arr; off; len; py_tags = tags; py_ints = ints; py_floats = floats; ref; view; lty }

let wrap_reference ty ref h =
  match ty with
  | TList elem ->
    let tag = Printf.sprintf "heap_view_%d" ref.id in
    L { arr = const (tag ^ ".arr") (Array (Int, sort_of elem)); off = zero; len = Heap.read_len h ref;
        py_tags = const (tag ^ ".tags") (Array (Int, Bool)); py_ints = const (tag ^ ".ints") (Array (Int, Int));
        py_floats = const (tag ^ ".floats") (Array (Int, Float64)); ref; view = ff; lty = ty }
  | TDict (key, value) ->
    D { vals = const (Printf.sprintf "heap_view_%d.vals" ref.id) (Array (sort_of key, sort_of value));
        has = const (Printf.sprintf "heap_view_%d.has" ref.id) (Array (sort_of key, Bool)); ref; dty = ty }
  | _ -> T ref

let numeric_store l index value =
  match l.lty with
  | Ir.TList Ir.TReal when value.sort = Int ->
    { l with arr = store l.arr index (as_float_to Float64 value); py_tags = store l.py_tags index tt; py_ints = store l.py_ints index value }
  | Ir.TList Ir.TReal ->
    { l with arr = store l.arr index (as_float_to Float64 value); py_tags = store l.py_tags index ff; py_floats = store l.py_floats index (as_float_to Float64 value) }
  | _ -> { l with arr = store l.arr index value }

let rec ite_val c a b =
  match (a, b) with
  | L x, L y -> L { arr = ite c x.arr y.arr; off = ite c x.off y.off; len = ite c x.len y.len; py_tags = ite c x.py_tags y.py_tags; py_ints = ite c x.py_ints y.py_ints; py_floats = ite c x.py_floats y.py_floats; ref = ite c x.ref y.ref; view = ite c x.view y.view; lty = x.lty }
  | O x, O y -> O { some = ite c x.some y.some; v = ite_val c x.v y.v; oty = x.oty }
  | D x, D y -> D { vals = ite c x.vals y.vals; has = ite c x.has y.has; ref = ite c x.ref y.ref; dty = x.dty }
  | T x, T y -> T (ite c x y)
  | NoneV, NoneV -> NoneV
  | _ -> raise (Vc_error ("branches disagree on a value's shape", Ir.noloc))

let rec value_equal a b =
  match (a, b) with
  | T x, T y -> x == y
  | L x, L y -> x.ref == y.ref
  | O x, O y -> x.some == y.some && value_equal x.v y.v
  | D x, D y -> x.ref == y.ref
  | NoneV, NoneV -> true
  | _ -> false

let rec default_term (s : sort) =
  match s with
  | Int -> zero
  | Real -> real (Q.of_int 0)
  | Float32 -> fval_for Float32 0.0
  | Float64 -> fval 0.0
  | Bool -> ff
  | Str -> str ""
  | Array (_, e) -> const_array s (default_term e)
  | Rec (_, fs) -> mkrec s (List.map (fun (_, fs) -> default_term fs) fs)
  | Opaque -> const "opaque!default" Opaque
  | Unit -> zero

let rec default_value (ty : Ir.ty) =
  pack ty (List.map (fun (_, s) -> default_term s) (components ty))

let rec valid_container_facts v (ty : Ir.ty) =
  match (ty, v) with
  | TList _, L l -> [ le zero l.len ]
  | TOption inner, O o ->
    let facts = valid_container_facts o.v inner in
    if facts = [] then [] else [ implies o.some (and_ facts) ]
  | _ -> []

(* lift a plain value into an optional slot: None -> absent, x -> present x *)
let coerce v (ty : Ir.ty option) =
  match (ty, v) with
  (* an empty [] / {} takes the type of the variable it is stored in *)
  | Some (TList e as lty), L l when l.lty = TList TNone && e <> TNone -> L (list_value ~view:l.view (const_array (Array (Int, sort_of e)) (default_term (sort_of e))) zero l.len l.ref lty)
  | Some (TDict (k, vt) as dty), D d when (match d.dty with TDict (TNone, _) -> true | _ -> false) && k <> TNone ->
    let ks = sort_of k and vs = sort_of vt in
    D { vals = const_array (Array (ks, vs)) (default_term vs); has = const_array (Array (ks, Bool)) ff; ref = d.ref; dty }
  | Some (TOption inner as oty), NoneV -> O { some = ff; v = default_value inner; oty }
  | Some (TOption _ as oty), ((T _ | L _ | D _ | O _) as value) -> O { some = tt; v = value; oty }
  | _ -> v

let rec ty_str (t : Ir.ty) =
  match t with
  | TInt -> "int" | TReal -> "real" | TPythonNumber -> "python_number" | TFloat32 -> "float32" | TBool -> "bool" | TStr -> "str" | TNone -> "none" | TOpaque -> "opaque"
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

let py_num_sort = Rec ("PythonNumber", [ ("is_int", Bool); ("integer", Int); ("floating", Float64) ])
let py_parts x = (field x "is_int", field x "integer", field x "floating")
let py_as_float x = let tag, i, f = py_parts x in ite tag (as_float i) f
let py_lt x y =
  let xt, xi, xf = py_parts x and yt, yi, yf = py_parts y in
  or_ [ and_ [ xt; yt; lt xi yi ]; and_ [ xt; not_ yt; xcmp "fp.lt" xi yf ]; and_ [ not_ xt; yt; xcmp "fp.lt" xf yi ]; and_ [ not_ xt; not_ yt; fcmp "fp.lt" xf yf ] ]

let rec rec_equal a b =
  match a.sort with
  | Rec ("PythonNumber", _) ->
    let at, ai, af = py_parts a and bt, bi, bf = py_parts b in
    or_ [
      and_ [ at; bt; eq ai bi ];
      and_ [ at; not_ bt; xcmp "fp.eq" bf ai ];
      and_ [ not_ at; bt; xcmp "fp.eq" af bi ];
      and_ [ not_ at; not_ bt; fcmp "fp.eq" af bf ];
    ]
  | Rec (n, fields) when String.length n > 4 && String.sub n 0 4 = "Opt_" ->
    let sa = field a "some" and sb = field b "some" in
    and_ [ eq sa sb; implies sa (rec_equal (field a "val") (field b "val")) ]
  | Rec (_, fields) -> and_ (List.map (fun (f, _) -> rec_equal (field a f) (field b f)) fields)
  | _ -> eq a b

(* -- program information (computed by the Python side) ------------------ *)

type finfo = {
  key : string;
  fn : Ir.func;
  language : string;
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
  language : string;
  cfields : (string * Ir.ty) list;
  cinvs : Ir.clause list;
  init : string option;  (** key of Cls.__init__, its own or inherited *)
  post_init : string option;
  cbases : string list;  (** checked base classes *)
  owner : (string * string) list;  (** field -> the class that introduced it *)
  clcs : (string * Ir.clause) list;  (** (owner, relation) for every lifecycle its objects keep *)
}

type program = {
  funcs : (string, finfo) Hashtbl.t;
  classes : classinfo list;  (** in program order *)
  resolve_tbl : (string * string, string) Hashtbl.t;  (** (module, name) -> function key *)
  heap_writes : (string, (string * string list) list) Hashtbl.t;  (** key -> [Cls.field, targets] *)
  allocates : (string, unit) Hashtbl.t;
  hands_out : (string, unit) Hashtbl.t;  (** may hand a checked object to unchecked code *)
  def_heap : (string, string list) Hashtbl.t;  (** definitional key -> heap keys its body reads *)
  field_slots : (string * string * int) list;
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
  binders : term list;  (** enclosing quantifier variables *)
}

let hyps ctx = Dynarray.to_list ctx.base @ ctx.guard
let assume ctx t = Dynarray.add_last ctx.base (if ctx.guard = [] then t else implies (and_ ctx.guard) t)
(* assume t for every value of the enclosing quantifier variables: sound only
   when every fresh symbol in t is a function of them *)
(* [t] for every value of the enclosing quantifier variables. One quantifier,
   triggered where the inner one is: a quantifier over the variables alone
   has nothing to trigger on. *)
let assume_for_all_binders ctx t =
  let guard = and_ ctx.guard in
  let covers pats = List.for_all (fun b -> List.exists (Array.exists (fun u -> occurs b u)) pats) ctx.binders in
  match t.node with
  | Quant ("forall", vs, body, (_ :: _ as pats)) when covers pats -> Dynarray.add_last ctx.base (quant "forall" (ctx.binders @ Array.to_list vs) (implies guard body) pats)
  | _ -> Dynarray.add_last ctx.base (forall ctx.binders (implies guard t))
(* a new symbol and how to assume its definition: under a quantifier, a
   function of its variables, defined for all of them at once *)
let defined_symbol ?(pure = true) ctx name srt =
  if ctx.binders <> [] && pure then (fn name (Array.of_list ctx.binders) srt, assume_for_all_binders) else (const name srt, assume)

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
  mutable written : (string * int) list;  (** (class, line) of each field write to a class with an invariant, reversed *)
  mutable created : term list;  (** objects this call allocated *)
  mutable lc_written : string list;  (** classes of the non-parameter objects it writes a field of *)
  comp_memo : (string, term) Hashtbl.t;  (** what a pure comprehension computes -> its array *)
  comp_bodies : (int, string * term list) Hashtbl.t;  (** comprehension array -> its body, quantifier variables *)
  comp_sums : (string, term * term * term * term list) Hashtbl.t;  (** body -> sums over such arrays (array, length, sum, variables) *)
}

let next g =
  g.counter <- g.counter + 1;
  g.counter

let tyname = function
  | Ir.TInt -> "int" | TReal -> "real" | TFloat32 -> "float32" | TBool -> "bool" | TStr -> "str" | TNone -> "none"
  | _ -> "?"

let fresh g base (ty : Ir.ty) ?len () =
  let n = next g in
  match ty with
  | TList e ->
    let arr = const (Printf.sprintf "%s@%d.arr" base n) (Array (Int, sort_of e)) in
    let ln = match len with Some l -> l | None -> const (Printf.sprintf "%s@%d.len" base n) Int in
    L { arr; off = zero; len = ln; py_tags = const (Printf.sprintf "%s@%d.py_tags" base n) (Array (Int, Bool)); py_ints = const (Printf.sprintf "%s@%d.py_ints" base n) (Array (Int, Int)); py_floats = const (Printf.sprintf "%s@%d.py_floats" base n) (Array (Int, Float64)); ref = const (Printf.sprintf "%s@%d.ref" base n) Int; view = ff; lty = ty }
  | TDict _ ->
    let ks = match ty with TDict (k, _) -> sort_of k | _ -> Int in
    let vt = match ty with TDict (_, v) -> sort_of v | _ -> Int in
    D { vals = const (Printf.sprintf "%s@%d.vals" base n) (Array (ks, vt)); has = const (Printf.sprintf "%s@%d.has" base n) (Array (ks, Bool)); ref = const (Printf.sprintf "%s@%d.ref" base n) Int; dty = ty }
  | TNone -> NoneV
  | t -> (
    match components t with
    | [ (_, s) ] -> T (const (Printf.sprintf "%s@%d" base n) s)
    | cs -> pack t (List.map (fun (suffix, s) -> const (Printf.sprintf "%s@%d.%s" base n suffix) s) cs))

let param_val name (ty : Ir.ty) =
  match ty with
  | TList e -> L { arr = const (name ^ ".arr") (Array (Int, sort_of e)); off = zero; len = const (name ^ ".len") Int; py_tags = const (name ^ ".py_tags") (Array (Int, Bool)); py_ints = const (name ^ ".py_ints") (Array (Int, Int)); py_floats = const (name ^ ".py_floats") (Array (Int, Float64)); ref = const (name ^ ".ref") Int; view = ff; lty = ty }
  | TDict (k, v) -> D { vals = const (name ^ ".vals") (Array (sort_of k, sort_of v)); has = const (name ^ ".has") (Array (sort_of k, Bool)); ref = const (name ^ ".ref") Int; dty = ty }
  | TNone -> NoneV
  | t -> (
    match components t with
    | [ (_, s) ] -> T (const name s)
    | cs -> pack t (List.map (fun (suffix, s) -> const (name ^ "." ^ suffix) s) cs))

let finfo_of g key = try Hashtbl.find g.prog.funcs key with Not_found -> raise (Fallback ("unknown function " ^ key))
let resolve g modpath name = Option.map (finfo_of g) (Hashtbl.find_opt g.prog.resolve_tbl (modpath, name))
let class_of g name = Hashtbl.find_opt g.prog.by_name name
let is_init g = let n = g.info.fn.name in String.length n >= 9 && String.sub n (String.length n - 9) 9 = ".__init__"

(* is 'self' an object this call is building? *)
let fresh_self g = is_init g || (let n = g.info.fn.name in String.length n >= 14 && String.sub n (String.length n - 14) 14 = ".__post_init__")

let starts_with p s = String.length s >= String.length p && String.sub s 0 (String.length p) = p
let ends_with x s = String.length s >= String.length x && String.sub s (String.length s - String.length x) (String.length x) = x
let is_heap k = String.length k > 0 && k.[0] = '@'
let heap_env env = SM.filter (fun k _ -> is_heap k) env

let current_heap ctx = match SM.find_opt "@heap" (cur_env ctx) with Some (T h) -> Some h | _ -> None

(* -- the heap: one map per class field (per component), keyed by reference *)

let field_type g cls fname =
  match class_of g cls with
  | None -> raise (Vc_error ("unknown class '" ^ cls ^ "'", Ir.noloc))
  | Some c -> ( match List.assoc_opt fname c.cfields with Some t -> t | None -> raise (Vc_error (Printf.sprintf "%s has no field '%s'" cls fname, Ir.noloc)))

(* subclasses keep inherited fields where the base class does *)
let field_owner g cls fname = match class_of g cls with Some c -> (match List.assoc_opt fname c.owner with Some o -> o | None -> cls) | None -> cls

let field_slot g cls fname =
  let owner = match class_of g cls with
    | Some c when c.language = "python" || c.language = "typescript" -> "property"
    | Some c -> field_owner g cls fname
    | None -> raise (Vc_error ("unknown class " ^ cls, Ir.noloc))
  in
  match List.find_opt (fun (namespace, name, _) -> namespace = owner && name = fname) g.prog.field_slots with
  | Some (_, _, slot) -> int_ slot
  | None -> raise (Vc_error (Printf.sprintf "missing field slot %s.%s" owner fname, Ir.noloc))

let record_field_slot g schema fname =
  let record_owner = "record:" ^ schema in
  let namespace = if List.exists (fun (owner, name, _) -> owner = record_owner && name = fname) g.prog.field_slots then record_owner else "property" in
  match List.find_opt (fun (owner, name, _) -> owner = namespace && name = fname) g.prog.field_slots with
  | Some (_, _, slot) -> int_ slot
  | None -> raise (Vc_error (Printf.sprintf "missing record field slot %s.%s" schema fname, Ir.noloc))

let rec project_record g h name fields ref =
  mkrec (sort_of (TRecord (name, fields)))
    (List.map (fun (fname, fty) ->
       term_of Ir.noloc (unbox_value g (Heap.read_field h ref (record_field_slot g name fname)) fty h)) fields)

and unbox_value g boxed ty h =
  match ty with
  | TOption inner ->
    let some = not_ (eq (field boxed "tag") (int_ 0)) in
    O { some; v = unbox_value g boxed inner h; oty = ty }
  | TList elem ->
    let ref = Heap.unbox boxed ty in
    let i = const (Printf.sprintf "heap.unbox.list.%d.%d" ref.id h.id) Int in
    let arr = array_lambda i (term_of Ir.noloc (unbox_value g (Heap.read_list h ref i) elem h)) in
    let len = Heap.read_len h ref in
    let tags, ints, floats =
      if elem = TInt then
        (const_array (Array (Int, Bool)) tt, arr, const_array (Array (Int, Float64)) (fval 0.0))
      else if elem = TReal && g.info.language <> "python" then
        (const_array (Array (Int, Bool)) ff, const_array (Array (Int, Int)) zero, arr)
      else if g.info.language = "python" && elem = TReal then begin
        let j = const (Printf.sprintf "heap.unbox.tags.%d.%d" ref.id h.id) Int in
        let pybox = Heap.read_list h ref j in
        let tag = field pybox "tag" and py = field pybox "python_number" in
        let is_py = eq tag (int_ Heap.python_number_tag) in
        let is_int = or_ [ eq tag (int_ Heap.integer_tag); eq tag (int_ Heap.boolean_tag); and_ [ is_py; field py "is_int" ] ] in
        let int_value = ite (eq tag (int_ Heap.boolean_tag)) (ite (field pybox "boolean") one zero) (ite is_py (field py "integer") (field pybox "integer")) in
        let float_value = ite is_py (field py "floating") (field pybox "real") in
        (array_lambda j is_int, array_lambda j int_value, array_lambda j float_value)
      end else
        (const_array (Array (Int, Bool)) ff, const_array (Array (Int, Int)) zero, const_array (Array (Int, Float64)) (fval 0.0))
    in
    L { arr; off = zero; len; py_tags = tags; py_ints = ints; py_floats = floats; ref; view = ff; lty = ty }
  | TDict (key_ty, value_ty) ->
    let ref = Heap.unbox boxed ty in
    let key_index = const (Printf.sprintf "heap.unbox.dict.%d.%d" ref.id h.id) (sort_of key_ty) in
    let key, _ = Heap.canonical_key key_index key_ty g.info.language in
    let vals = array_lambda key_index (term_of Ir.noloc (unbox_value g (Heap.read_dict h ref key) value_ty h)) in
    let has = array_lambda key_index (Heap.has_dict h ref key) in
    D { vals; has; ref; dty = ty }
  | TRecord (name, fields) -> T (project_record g h name fields (Heap.unbox boxed ty))
  | _ -> T (Heap.unbox boxed ty)

let class_tag g cls =
  let names = List.map (fun c -> c.cname) g.prog.classes |> List.sort_uniq compare in
  match List.find_index (( = ) cls) names with Some i -> int_ (i + 1) | None -> int_ 0

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

let rec accepts_view g h ty boxed =
  let cell ref = Heap.cell_at h ref in
  let compatible_class cls c =
    let actual = List.map (fun c -> c.cname) g.prog.classes in
    List.filter_map (fun actual -> if List.mem cls (mro g actual) then Some (eq (field c "class") (class_tag g actual)) else None) actual
  in
  let raw_ok = Heap.accepts boxed ty in
  match ty with
  | TOption inner ->
    let none = eq (field boxed "tag") (int_ 0) in
    or_ [ none; accepts_view g h inner boxed ]
  | TList _ | TDict _ | TRecord _ | TClass _ ->
    let ref = Heap.unbox boxed ty in
    let c = cell ref in
    let allocated = field c "allocated" in
    let kind = field c "kind" in
    let representation, contents = match ty with
      | TList elem ->
        let i = const (Printf.sprintf "heap.list.type.%d.%d" ref.id h.id) Int in
        let item = Heap.read_list h ref i in
        (eq kind (int_ 1), quant "forall" [ i ]
           (implies (and_ [ le zero i; lt i (Heap.read_len h ref) ]) (accepts_view g h elem item)) [ [| item |] ])
      | TDict (_, elem) ->
        let key = const (Printf.sprintf "heap.dict.type.%d.%d" ref.id h.id) Heap.key in
        let item = Heap.read_dict h ref key in
        (eq kind (int_ 2), quant "forall" [ key ] (implies (Heap.has_dict h ref key) (accepts_view g h elem item)) [ [| item |] ])
      | TRecord (name, fields) ->
        let structural = g.info.language = "typescript" in
        (or_ [ eq kind (int_ 3); if structural then eq kind (int_ 4) else ff ],
         and_ (List.map (fun (fname, fty) -> accepts_view g h fty (Heap.read_field h ref (record_field_slot g name fname))) fields))
      | TClass cls ->
        let structural = g.info.language = "typescript" in
        let class_kind = and_ [ eq kind (int_ 4); or_ (compatible_class cls c) ] in
        (or_ [ class_kind; if structural then eq kind (int_ 3) else ff ], tt)
      | _ -> (ff, ff)
    in
    and_ [ raw_ok; allocated; representation; contents ]
  | _ -> raw_ok

let dict_views g h d =
  match d.dty with
  | TDict (key_ty, value_ty) ->
    let key_index = const (Printf.sprintf "heap.dict.key.%d.%d" d.ref.id h.id) (sort_of key_ty) in
    let key, _ = Heap.canonical_key key_index key_ty g.info.language in
    let has = array_lambda key_index (Heap.has_dict h d.ref key) in
    let boxed = Heap.read_dict h d.ref key in
    let item = match value_ty with
      | TRecord (name, fields) -> project_record g h name fields (Heap.unbox boxed value_ty)
      | TOption inner ->
        let some = not_ (eq (field boxed "tag") (int_ 0)) in
        let value = match inner with
          | TRecord (name, fields) -> project_record g h name fields (Heap.unbox boxed inner)
          | _ -> Heap.unbox boxed inner
        in
        mkrec (field_sort value_ty) [ some; value ]
      | _ -> Heap.unbox boxed value_ty
    in
    { d with vals = array_lambda key_index item; has }
  | _ -> d

let refresh_list_view g _st h l =
  let elem = match l.lty with TList t -> t | _ -> TNone in
  let i = const (Printf.sprintf "heap.view.i.%d.%d" l.ref.id h.id) Int in
  let boxed = Heap.read_list h l.ref i in
  let item =
    match elem with
    | TRecord (name, fields) -> project_record g h name fields (Heap.unbox boxed elem)
    | _ -> Heap.unbox boxed elem
  in
  let arr = array_lambda i item in
  let tags, ints, floats =
    if g.info.language = "python" && elem = TReal then begin
      let tags_i = const (Printf.sprintf "heap.view.tags.i.%d.%d" l.ref.id h.id) Int in
      let ints_i = const (Printf.sprintf "heap.view.ints.i.%d.%d" l.ref.id h.id) Int in
      let floats_i = const (Printf.sprintf "heap.view.floats.i.%d.%d" l.ref.id h.id) Int in
      let tag = field boxed "tag" in
      let py = field boxed "python_number" in
      let is_python = eq tag (int_ Heap.python_number_tag) in
      let is_int = or_ [ eq tag (int_ Heap.integer_tag); eq tag (int_ Heap.boolean_tag); and_ [ is_python; field py "is_int" ] ] in
      let int_value = ite (eq tag (int_ Heap.boolean_tag)) (ite (field boxed "boolean") one zero) (ite is_python (field py "integer") (field boxed "integer")) in
      let float_value = ite is_python (field py "floating") (field boxed "real") in
      (array_lambda tags_i is_int, array_lambda ints_i int_value, array_lambda floats_i float_value)
    end else (l.py_tags, l.py_ints, l.py_floats)
  in
  { l with arr; len = ite l.view l.len (Heap.read_len h l.ref); py_tags = tags; py_ints = ints; py_floats = floats }

let rec refresh_value g st h = function
  | L l -> L (refresh_list_view g st h l)
  | D d -> D (dict_views g h d)
  | O o -> O { o with v = refresh_value g st h o.v }
  | value -> value

let set_current_heap g ctx h =
  match ctx.state with
  | Some st ->
    let env = SM.add "@heap" (T h) st.env in
    st.env <- SM.mapi (fun _ value -> refresh_value g st h value) env
  | None -> raise (Fallback "heap mutation outside a live state")

let list_len ctx l = match current_heap ctx with Some h -> ite l.view l.len (Heap.read_len h l.ref) | None -> l.len

let heap_read g env cls fname r =
  let ty = field_type g cls fname in
  match SM.find_opt "@heap" env with
  | Some (T h) ->
    let boxed = Heap.read_field h r (field_slot g cls fname) in
    unbox_value g boxed ty h
  | _ ->
    pack ty (List.map (fun (k, _) -> match SM.find_opt k env with Some (T m) -> select m r | _ -> raise (Vc_error ("heap map " ^ k ^ " missing", Ir.noloc))) (heap_keys ~strict:true g cls fname))

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

let require_python_float_at g ctx l index loc =
  match (g.info.language, l.lty) with
  | "python", Ir.TList Ir.TReal -> oblige g "numeric" ctx (not_ (select l.py_tags index)) loc "Python list element is a float, not an integer"
  | _ -> ()

let check_heap_kind g ctx ref kind loc what =
  match current_heap ctx with
  | None -> ()
  | Some h ->
    let c = Heap.cell_at h ref in
    let valid = and_ [ field c "allocated"; eq (field c "kind") (int_ kind) ] in
    oblige g "type" ctx valid loc what;
    assume ctx valid

let read_list_item g ctx l index loc =
  match current_heap ctx with
  | None -> T (at (l.arr, l.off) index)
  | Some h ->
    check_heap_kind g ctx l.ref 1 loc "list access refers to an allocated list";
    let boxed = Heap.read_list h l.ref (add l.off index) in
    let elem = match l.lty with TList t -> t | _ -> TNone in
    let valid = accepts_view g h elem boxed in
    oblige g "type" ctx valid loc "list element matches its typed view";
    assume ctx valid;
    unbox_value g boxed elem h

let allocate_heap_cell g ctx ref cell loc =
  match current_heap ctx with
  | None -> raise (Fallback "heap allocation without a live heap")
  | Some h ->
    let h, fresh = Heap.allocate h cell ref in
    List.iter (fun fact -> oblige g "allocation" ctx fact loc "new container has a fresh heap reference"; assume ctx fact) fresh;
    set_current_heap g ctx h

let value_ref loc = function L l -> l.ref | D d -> d.ref | T t -> t | _ -> raise (Vc_error ("expected a heap reference", loc))

let rec box_value g ctx loc ty value =
  match ty, value with
  | TNone, NoneV -> Heap.box zero TNone
  | TRecord (name, fields), T raw when raw.sort <> Int ->
    let ref = const (Printf.sprintf "record@%d.ref" (next g)) Int in
    let initial = const_array (Array (Int, Heap.value)) (Heap.box zero TNone) in
    let slots = List.fold_left (fun contents (field_name, field_ty) ->
      let source = field raw field_name in
      let field_value = match field_ty with
        | TOption inner -> O { some = field source "some"; v = T (field source "val"); oty = field_ty }
        | _ -> T source
      in
      let slot = record_field_slot g name field_name in
      store contents slot (box_value g ctx loc field_ty field_value)) initial fields
    in
    let current = match current_heap ctx with Some h -> h | None -> raise (Fallback "record allocation requires a shared heap") in
    let allocated, fresh = Heap.allocate current (Heap.record_cell slots) ref in
    List.iter (fun fact -> oblige g "allocation" ctx fact loc "record has a fresh heap reference"; assume ctx fact) fresh;
    set_current_heap g ctx allocated;
    Heap.box ref ty
  | TRecord _, T raw -> Heap.box raw ty
  | TOption inner, O o ->
    let present = box_value g ctx loc inner o.v in
    let absent = Heap.box zero TNone in
    ite o.some present absent
  | TOption _, NoneV -> Heap.box zero TNone
  | _, T raw when g.info.language = "python" ->
    let runtime_ty = match raw.sort with
      | Bool -> TBool
      | Int -> TInt
      | Float32 -> TFloat32
      | Float64 -> TReal
      | Rec ("PythonNumber", _) -> TPythonNumber
      | _ -> ty
    in
    Heap.box raw runtime_ty
  | _, v -> Heap.box (value_ref loc v) ty

let box_projection_item g (l : lv) index =
  match l.lty with
  | TList TReal when g.info.language = "python" ->
    let raw = ite (select l.py_tags index)
      (Heap.box (select l.py_ints index) TInt)
      (Heap.box (select l.py_floats index) TReal)
    in raw
  | TList (TOption inner) ->
    let raw = select l.arr index in
    let some = field raw "some" in
    let value = field raw "val" in
    (match inner with TRecord _ | TList _ | TDict _ -> raise (Fallback "nested optional list materialization requires boxed element witnesses") | _ -> ());
    ite some (Heap.box value inner) (Heap.box zero TNone)
  | TList (TRecord _) -> raise (Fallback "record list materialization requires boxed element witnesses")
  | TList (TList _ | TDict _) -> raise (Fallback "nested list materialization requires boxed element witnesses")
  | TList elem -> Heap.box (select l.arr index) elem
  | _ -> raise (Fallback "list materialization requires a list value")

let allocate_list_sequence g ctx loc (l : lv) boxed =
  allocate_heap_cell g ctx l.ref (Heap.list_cell l.len boxed) loc;
  match current_heap ctx, ctx.state with
  | Some h, Some st -> L (refresh_list_view g st h l)
  | _ -> raise (Fallback "list result allocation requires a shared heap")

let allocate_list_value g ctx loc (l : lv) =
  let i = const (Printf.sprintf "heap.list.output.%d.index" (next g)) Int in
  let boxed = array_lambda i (box_projection_item g l i) in
  allocate_list_sequence g ctx loc l boxed

let copy_list_value g ctx loc (l : lv) off len =
  match current_heap ctx, ctx.state with
  | Some h, Some st ->
    let ref = const (Printf.sprintf "list.copy@%d.ref" (next g)) Int in
    let i = const (Printf.sprintf "list.copy@%d.i" (next g)) Int in
    let seq = array_lambda i (Heap.read_list h l.ref (add off i)) in
    allocate_heap_cell g ctx ref (Heap.list_cell len seq) loc;
    let copied = { l with ref; off = zero; len; view = ff } in
    (match current_heap ctx with Some current -> L (refresh_list_view g st current copied) | None -> assert false)
  | _ -> raise (Fallback "list value copy requires the shared heap")

let copy_dict_value g ctx loc (d : dv) =
  match current_heap ctx with
  | Some h ->
    let ref = const (Printf.sprintf "dict.copy@%d.ref" (next g)) Int in
    allocate_heap_cell g ctx ref (Heap.cell_at h d.ref) loc;
    (match current_heap ctx with Some current -> D (dict_views g current { d with ref }) | None -> assert false)
  | None -> raise (Fallback "dictionary value copy requires the shared heap")

let rec copy_value g ctx loc = function
  | L l -> copy_list_value g ctx loc l l.off (list_len ctx l)
  | D d -> copy_dict_value g ctx loc d
  | O { v = (L _ | D _); _ } when g.info.language = "swift" ->
    raise (Fallback "copy of an optional Swift container requires a conditional heap transition")
  | O o -> O { o with v = copy_value g ctx loc o.v }
  | value -> value

let box_stored_value g ctx loc ty value =
  let value = if g.info.language = "swift" then copy_value g ctx loc value else value in
  box_value g ctx loc ty value

let heap_write g ctx (env : value SM.t) cls fname r v =
  let boxed = box_stored_value g ctx Ir.noloc (field_type g cls fname) v in
  let env = cur_env ctx in
  match current_heap ctx with
  | Some h -> SM.add "@heap" (T (Heap.write_field h r (field_slot g cls fname) boxed)) env
  | _ ->
    List.fold_left2 (fun env (k, _) comp -> match SM.find_opt k env with Some (T m) -> SM.add k (T (store m r comp)) env | _ -> env) env (heap_keys ~strict:true g cls fname) (flatten v)

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

(* min of two lengths, without a case split when one is the other plus a
   non-negative constant (a list and the same list appended to) *)
let rec shorter a b =
  let longer x y = match y.node with App ("add", [| u; c |]) -> u == x && (match num c with Some q -> Q.compare q (Q.of_int 0) >= 0 | None -> false) | _ -> false in
  if a == zero || b == zero then zero
  else if a == b || longer a b then a
  else if longer b a then b
  else match (a.node, b.node) with
    | App ("ite", [| c; x; y |]), _ -> ite c (shorter x b) (shorter y b)
    | _, App ("ite", [| c; x; y |]) -> ite c (shorter a x) (shorter a y)
    | _ -> min_ a b

(* [sum a k n], the sum of a[k:n], spelled out where [n] is [k] plus a small
   constant (a list appended to), branch by branch *)
let rec tail sum a k n =
  match n.node with
  | App ("ite", [| c; x; y |]) -> ite c (tail sum a k x) (tail sum a k y)
  | _ when n == k -> lit_of_int 0 (elem_sort a.sort)
  | App ("add", [| u; c |]) when u == k && (match num c with Some q -> q.d = 1 && q.n > 0 && q.n <= 4 | None -> false) ->
    let c = match num c with Some q -> q.n | None -> 0 in
    List.fold_left (fun acc j -> add acc (select a (add k (int_ j)))) (select a k) (List.init (c - 1) (fun j -> j + 1))
  | _ -> sum a k n

(* a conjunct of the guard says c <= i for a constant c >= 0 (a quantifier over range(c, ...)) *)
let nonneg_under i guard =
  let rec go g = match g.node with
    | App ("and", xs) -> Array.exists go xs
    | App ("le", [| c; j |]) -> j == i && (match num c with Some q -> Q.compare q (Q.of_int 0) >= 0 | None -> false)
    | _ -> false
  in
  List.exists go guard

let index_of g (arr, off, len) i wrap ctx loc what =
  if wrap then begin
    oblige g "index" ctx (and_ [ le (neg len) i; lt i len ]) loc (Printf.sprintf "index into '%s' is within -len..len-1" what);
    if nonneg_under i ctx.guard then i else ite (lt i zero) (add i len) i
  end else begin
    oblige g "index" ctx (and_ [ le zero i; lt i len ]) loc (Printf.sprintf "index into '%s' is within 0..len-1" what);
    i
  end

let lit_value (e : Ir.expr) =
  match e.e with
  | Lit (LInt s) -> (
    match int_of_string_opt s with
    | Some n -> ( match e.ty with TReal -> T (fval (float_of_int n)) | TFloat32 -> T (fval_for Float32 (float_of_int n)) | _ -> T (int_ n))
    | None -> T (mk (Big (match e.ty with TReal | TFloat32 -> "n:" ^ s | _ -> s)) (match e.ty with TReal -> Float64 | TFloat32 -> Float32 | _ -> Int)))
  | Lit (LFrac (n, d)) -> (
    match (int_of_string_opt n, int_of_string_opt d) with
    | Some n, Some d -> T (as_float_to (sort_of e.ty) (real (Q.make n d)))
    | _ -> T (mk (Big ("r:" ^ n ^ "/" ^ d)) (sort_of e.ty)))
  | Lit (LBool b) -> T (bool_ b)
  | Lit (LStr s) -> T (str s)
  | Lit LNone -> coerce NoneV (Some e.ty)
  | _ -> assert false

(* zip that stops at the shorter list, like Python's *)
let rec zip xs ys = match (xs, ys) with x :: xs, y :: ys -> (x, y) :: zip xs ys | _ -> []

let spec_ctx g ?(modpath = g.info.modpath) ?old_env ?result ?(quiet = true) ?(guard = []) ~base ~env () =
  { base; modpath; env; live = None; guard; bound = SM.empty; old_env; result; spec = true; quiet; state = None; binders = [] }

let alloc_of env = match SM.find_opt "@alloc" env with Some (T a) -> a | _ -> raise (Vc_error ("no allocation map", Ir.noloc))

(* objects handed to a function already exist; enum values are in range *)
let rec alloc_facts g v (ty : Ir.ty) env =
  match (ty, v) with
  | TEnum (_, ms, _), T t -> [ le zero t; lt t (int_ (List.length ms)) ]
  (* an enum field of a record (a union's tag) is one of its members *)
  | TRecord (_, fs), T t -> List.concat_map (fun (n, (ft : Ir.ty)) -> match ft with TEnum _ | TRecord _ -> alloc_facts g (T (field t n)) ft env | _ -> []) fs
  | TOption (TEnum (_, ms, _)), O o -> [ implies o.some (and_ [ le zero (term_of Ir.noloc o.v); lt (term_of Ir.noloc o.v) (int_ (List.length ms)) ]) ]
  | TClass _, T t ->
    let self_ = match SM.find_opt "self" g.entry with Some (T s) -> s == t | _ -> false in
    if is_init g && self_ then [] else [ select (alloc_of env) t ]
  | TOption (TClass _), O o -> [ implies o.some (select (alloc_of env) (term_of Ir.noloc o.v)) ]
  | TList (TClass _), L l ->
    let i = const (Printf.sprintf "i!%d" (next g)) Int in
    [ quant "forall" [ i ] (implies (and_ [ le zero i; lt i l.len ]) (select (alloc_of env) (at (l.arr, l.off) i))) [ [| at (l.arr, l.off) i |] ] ]
  | _ -> []

let rec reaches_objects (t : Ir.ty) = match t with TClass _ | TOpaque -> true | TList e -> reaches_objects e | TDict (_, v) -> reaches_objects v | TOption i -> reaches_objects i | _ -> false
let extern_touches_heap g (args : Ir.expr list) = g.prog.classes <> [] && List.exists (fun (a : Ir.expr) -> reaches_objects a.ty) args

let fresh_expr (e : Ir.expr option) = match e with Some { e = ListLit _ | Call _ | New _; _ } -> true | Some { e = Builtin (("slice" | "dict_lit"), _); _ } -> true | _ -> false

(* the objects of a class a function has written a field of (a ghost set, not
   heap: callees and other tasks do not add to it) *)
let written_key cls = "%written." ^ cls
let is_written_key k = String.length k > 9 && String.sub k 0 9 = "%written."

(* the heap when this run of the function last resumed (entry, or the latest
   await or yield): lifecycles bind each stretch that runs without suspending *)
let segment = "%segment"
let is_segment k = starts_with segment k
let suspends (x : Ir.expr) = match x.e with Builtin ("await", _) | Extern ("yield", _) -> true | _ -> false
let no_writes = const_array (Array (Int, Bool)) ff
let any_writes = const_array (Array (Int, Bool)) tt

(* can code other than this initializer reach the object it builds? *)
let self_escapes g =
  let out = ref false in
  Ir.walk_stmts
    (fun s ->
      List.iter
        (fun (e : Ir.expr) ->
          let skip = match s with FieldAssign (_, o, _, _, _) -> o == e | _ -> false in
          if not skip then begin
            let selfs = ref 0 and through = ref 0 and base_init = ref 0 in
            Ir.walk_expr
              (fun (x : Ir.expr) ->
                match x.e with
                | Var "self" -> incr selfs
                | Field ({ e = Var "self"; _ }, _) -> incr through
                | Call (f, { e = Var "self"; _ } :: _) when String.length f >= 8 && String.sub f (String.length f - 8) 8 = "__init__" -> incr base_init
                | _ -> ())
              e;
            if !selfs > !through + !base_init then out := true
          end)
        (Ir.stmt_exprs s))
    g.info.fn.body;
  !out

(* invariants of cls (or its bases) that read a field an ancestor introduced:
   code typed as the ancestor may break them unchecked *)
let held_skip g cls =
  List.concat_map
    (fun cn ->
      match class_of g cn with
      | Some c ->
        List.concat
          (List.mapi
             (fun i (inv : Ir.clause) ->
               let bad = ref false in
               Ir.walk_expr (fun (x : Ir.expr) -> match x.e with Field ({ e = Var "self"; _ }, f) when field_owner g cn f <> cn -> bad := true | _ -> ()) inv.cexpr;
               if !bad then [ (cn, i) ] else [])
             c.cinvs)
      | None -> [])
    (mro g cls)
let has_invariants g cls = List.exists (fun c -> match class_of g c with Some ci -> ci.cinvs <> [] | None -> false) (mro g cls)

(* parameters whose own return check covers every invariant of cls *)
let checked_params g cls =
  List.filter_map (fun (p, (ty : Ir.ty)) -> match (ty, SM.find_opt p g.entry) with TClass c, Some (T r) when List.mem cls (mro g c) -> Some r | _ -> None) g.info.fn.params

let written_in g names = List.filter_map (fun c -> if List.mem (written_key c.cname) names then Some c.cname else None) g.prog.classes

let monotone_alloc pre_ new_ r = quant "forall" [ r ] (implies (select pre_ r) (select new_ r)) [ [| select new_ r |] ]

(* an object this call created ([alloc] now, not at entry) keeps its field *)
let created_kept alloc0 alloc old new_ r = quant "forall" [ r ] (implies (and_ [ select alloc r; not_ (select alloc0 r) ]) (eq (select new_ r) (select old r))) [ [| select new_ r |] ]

let rec first_select_on r (t : term) =
  match t.node with
  | App ("select", [| _; i |]) when i == r -> Some t
  | App (_, xs) | Fn (_, xs) -> Array.fold_left (fun acc x -> match acc with Some _ -> acc | None -> first_select_on r x) None xs
  | ArrayLambda (_, body) -> first_select_on r body
  | Quant (_, _, b, _) -> first_select_on r b
  | _ -> None

let rec ev g ctx (e : Ir.expr) : value =
  let loc = e.loc in
  let tm x = term_of loc x in
  match e.e with
  | Lit _ -> lit_value e
  | Var n ->
    let value = lookup ctx n loc in
    (match current_heap ctx with
     | None -> value
     | Some h ->
       let value = refresh_value g ctx h value in
       let check_list l =
         let i = const (Printf.sprintf "heap.view.check.%d.%d" l.ref.id h.id) Int in
         let elem = match l.lty with TList t -> t | _ -> TNone in
         let boxed = Heap.read_list h l.ref (add l.off i) in
         let valid = quant "forall" [ i ] (implies (and_ [ le zero i; lt i l.len ]) (accepts_view g h elem boxed)) [ [| boxed |] ] in
         oblige g "type" ctx valid loc "list contents match their typed view";
         assume ctx valid
       in
       let check_dict d = match d.dty with
         | TDict (_, value_ty) ->
           let key = const (Printf.sprintf "heap.dict.check.%d.%d" d.ref.id h.id) Heap.key in
           let boxed = Heap.read_dict h d.ref key in
           let valid = quant "forall" [ key ] (implies (Heap.has_dict h d.ref key) (accepts_view g h value_ty boxed)) [ [| boxed |] ] in
           oblige g "type" ctx valid loc "dictionary values match their typed view";
           assume ctx valid
         | _ -> ()
       in
       let rec check = function L l -> check_list l | D d -> check_dict d | O o -> check o.v | _ -> () in
       check value;
       value)
  | Result -> ( match ctx.result with Some r -> r | None -> raise (Vc_error ("'result' is not available here", loc)))
  | Old x -> (
    match ctx.old_env with
    | Some oe -> ev g { ctx with env = oe; live = None } x
    | None -> raise (Vc_error ("old(...) is only meaningful in '@ensures'", loc)))
  | Unary ("neg", x) when x.ty = TPythonNumber ->
    let v = tm (ev g ctx x) in
    let tag, integer, floating = py_parts v in
    T (mkrec py_num_sort [ tag; neg integer; fneg floating ])
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
    | ("add" | "sub" | "mul" | "lt" | "le" | "gt" | "ge" | "py_rdiv") when a.ty = TPythonNumber || b.ty = TPythonNumber ->
      let x, y = tm x, tm y in
      let xt, xi, xf = py_parts x and yt, yi, yf = py_parts y in
      let both_int = and_ [ xt; yt ] in
      let cmp_lt = py_lt in
      let compare op flip =
        let l = if flip then cmp_lt y x else cmp_lt x y in
        if op = "lt" || op = "gt" then l else or_ [ l; rec_equal x y ]
      in
      (match op with
       | "lt" | "le" | "gt" | "ge" -> T (compare op (op = "gt" || op = "ge"))
       | "add" | "sub" | "mul" ->
         let conversion_limit = int_ ((1 lsl 1024) - (1 lsl 970)) in
         let xfits = lt (abs_ xi) conversion_limit and yfits = lt (abs_ yi) conversion_limit in
         let mixed = not_ both_int in
         let conversions = and_ [ implies (and_ [ xt; not_ yt ]) xfits; implies (and_ [ yt; not_ xt ]) yfits ] in
         oblige g "overflow" ctx (implies mixed conversions) loc "integer converted to float does not overflow";
         let ix = match op with "add" -> add xi yi | "sub" -> sub xi yi | _ -> mul xi yi in
         let fx, fy = py_as_float x, py_as_float y in
         let ff = match op with "add" -> add fx fy | "sub" -> sub fx fy | _ -> mul fx fy in
         T (mkrec py_num_sort [ both_int; ix; ff ])
       | "py_rdiv" ->
         let divisor_nonzero = or_ [ and_ [ yt; ne yi zero ]; and_ [ not_ yt; not_ (fpred "fp.isZero" yf) ] ] in
         oblige g "div" ctx divisor_nonzero loc "divisor of '/' is non-zero";
         let conversion_limit = int_ ((1 lsl 1024) - (1 lsl 970)) in
         let conversions = and_ [ implies (and_ [ xt; not_ yt ]) (lt (abs_ xi) conversion_limit); implies (and_ [ yt; not_ xt ]) (lt (abs_ yi) conversion_limit) ] in
         oblige g "overflow" ctx (implies (not_ both_int) conversions) loc "integer converted to float does not overflow";
         let exact_q = as_float (rdiv (to_real xi) (to_real yi)) in
         oblige g "overflow" ctx (implies both_int (is_finite exact_q)) loc "integer division result fits in a float";
         let negative_zero = and_ [ both_int; eq xi zero; lt yi zero ] in
         let exact_q = ite negative_zero (fneg (fval 0.0)) exact_q in
         let q = ite both_int exact_q (rdiv (py_as_float x) (py_as_float y)) in
         T q
       | _ -> raise (Vc_error ("unsupported tagged Python numeric operator " ^ op, loc)))
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
      | "rdiv" | "py_rdiv" | "floordiv" | "fmod" | "tmod" | "tdiv" ->
        let z = if List.mem y.sort [ Float32; Float64 ] then fval_for y.sort 0.0 else lit_of_int 0 y.sort in
        let sym = match op with "rdiv" | "py_rdiv" | "tdiv" -> "/" | "floordiv" -> "//" | _ -> "%" in
        if op = "py_rdiv" || (op <> "rdiv" && op <> "py_rdiv") || not (List.mem x.sort [ Float32; Float64 ]) then begin
          oblige g "div" ctx (ne y z) loc (Printf.sprintf "divisor of '%s' is non-zero" sym);
          if not (ctx.quiet || ctx.spec) then assume ctx (ne y z)
        end;
        if op = "rdiv" || op = "py_rdiv" then T (rdiv x y)
        else if List.mem x.sort [ Float32; Float64 ] then begin
          oblige g "finite" ctx (and_ [ not_ (fpred "fp.isNaN" x); not_ (fpred "fp.isInfinite" x); not_ (fpred "fp.isNaN" y); not_ (fpred "fp.isInfinite" y) ]) loc "floating remainder operands are finite";
          let xr = fto_real x and yr = fto_real y in
          let q = rdiv xr yr in
          let qi = if op = "fmod" || op = "floordiv" then floor q else ite (le (real (Q.of_int 0)) q) (floor q) (neg (floor (neg q))) in
          if op = "floordiv" then T (as_float_to x.sort (to_real qi)) else T (as_float_to x.sort (sub xr (mul yr (to_real qi))))
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
      let raw_key = tm (ev g ctx i) in
      let key_ty = match d.dty with TDict (k, _) -> k | _ -> TNone in
      let k, admissible = Heap.canonical_key raw_key key_ty g.info.language in
      oblige g "key" ctx admissible loc "dictionary key uses supported source equality";
      assume ctx admissible;
      let v = match current_heap ctx with
        | Some h ->
          check_heap_kind g ctx d.ref 2 loc "dictionary access refers to an allocated dictionary";
          oblige g "key" ctx (Heap.has_dict h d.ref k) loc (Printf.sprintf "key looked up in '%s' is present" (expr_name s));
          let boxed = Heap.read_dict h d.ref k in
          let value_ty = match d.dty with TDict (_, v) -> v | _ -> TNone in
          let valid = accepts_view g h value_ty boxed in
          oblige g "type" ctx valid loc "dictionary value matches its typed view";
          assume ctx valid;
          unbox_value g boxed value_ty h
        | None ->
          oblige g "key" ctx (select d.has raw_key) loc (Printf.sprintf "key looked up in '%s' is present" (expr_name s));
          T (select d.vals raw_key)
      in
      assume_held g ctx v e.ty;
      v
    | L l ->
      let i = tm (ev g ctx i) in
      let len = list_len ctx l in
      let j = index_of g (l.arr, l.off, len) i wrap ctx loc (expr_name s) in
      require_python_float_at g ctx l (add l.off j) loc;
      let v = read_list_item g ctx l j loc in
      assume_held g ctx v e.ty;
      v
    | _ -> raise (Vc_error ("indexing a non-list", loc)))
  | Field (o, f) -> (
    let obj_value = ev g ctx o in
    let obj = tm obj_value in
    match o.ty with
    | TRecord (schema, fields) when obj.sort = Int ->
      let h = match current_heap ctx with Some h -> h | None -> raise (Fallback "record field read requires the shared heap") in
      let cell = Heap.cell_at h obj in
      let record_kind = eq (field cell "kind") (int_ 3) in
      let structural = if g.info.language = "typescript" then eq (field cell "kind") (int_ 4) else ff in
      let valid = and_ [ field cell "allocated"; or_ [ record_kind; structural ] ] in
      oblige g "type" ctx valid loc "record field access uses an allocated compatible value";
      assume ctx valid;
      if not (List.mem_assoc f fields) then raise (Vc_error (Printf.sprintf "record has no field '%s'" f, loc));
      let boxed = Heap.read_field h obj (record_field_slot g schema f) in
          let accepted = accepts_view g h e.ty boxed in
      oblige g "type" ctx accepted loc (Printf.sprintf "record field can be viewed as %s" (ty_str e.ty));
      assume ctx accepted;
      unbox_value g boxed e.ty h
    | TClass cls ->
      let env = match ctx.state with Some st -> st.env | None -> ctx.env in
      (match SM.find_opt "@heap" env with
       | Some (T h) ->
         let cell = Heap.cell_at h obj in
         let compatible = List.filter_map (fun actual -> if List.mem cls (mro g actual) then Some (eq (field cell "class") (class_tag g actual)) else None) (List.map (fun c -> c.cname) g.prog.classes) in
         let class_match = and_ [ eq (field cell "kind") (int_ 4); or_ compatible ] in
         let structural = if g.info.language = "typescript" then eq (field cell "kind") (int_ 3) else ff in
         let valid = and_ [ field cell "allocated"; or_ [ class_match; structural ] ] in
         oblige g "type" ctx valid loc "field access uses an allocated compatible object";
         assume ctx valid
       | _ -> ());
      let v = heap_read g env cls f obj in
      (* the heap holds only allocated objects *)
      (match (ctx.state, e.ty) with
       | Some st, (TClass _ | TOption (TClass _)) -> List.iter (assume ctx) (alloc_facts g v e.ty st.env)
       | _ -> ());
      v
    | _ -> (
      let raw = field obj f in
      match e.ty with TOption _ -> O { some = field raw "some"; v = T (field raw "val"); oty = e.ty } | _ -> T raw))
  | RecordLit fs ->
    let ftys = match e.ty with TRecord (_, ftys) -> ftys | _ -> raise (Vc_error ("record literal of a non-record type", loc)) in
    let vals =
      List.map
        (fun ((_, fty), (_, x)) ->
          match coerce (ev g ctx x) (Some fty) with
          | O o -> mkrec (field_sort fty) [ o.some; term_of loc o.v ]
          | v -> tm v)
        (zip ftys fs)
    in
    T (mkrec (sort_of e.ty) vals)
  | ListLit elems ->
    (* an empty [] of unknown type is a placeholder until it is stored (see coerce) *)
    let ty = match e.ty with TList TNone -> Ir.TList TInt | t -> t in
    let base = match fresh g "lit" ty ~len:zero () with L l -> l | _ -> assert false in
    let arr = ref base.arr in
    let values = ref [] in
    List.iteri (fun i x ->
      let value = ev g ctx x in
      values := !values @ [ value ];
      arr := store !arr (int_ i) (tm value)) elems;
    let seq = ref (const_array (Array (Int, Heap.value)) (Heap.box zero TNone)) in
    let elem_ty = match ty with TList t -> t | _ -> TNone in
    List.iteri (fun i value -> seq := store !seq (int_ i) (box_stored_value g ctx loc elem_ty value)) !values;
    allocate_heap_cell g ctx base.ref (Heap.list_cell (int_ (List.length elems)) !seq) loc;
    L (list_value !arr zero (int_ (List.length elems)) base.ref e.ty)
  | Quant q when (not ctx.spec) && effectful g q.body ->
    (* an unknown truth value; the body's obligations and effects for every element *)
    let n = next g in
    (match q.seq with
     | Some ({ ty = TDict (kty, _); _ } as s) -> (
       match (ev g ctx s, q.elem) with
       | D d, Some el ->
         let k = const (Printf.sprintf "%s!%d" el n) (sort_of kty) in
         run_each g ctx loc (Some s) (select d.has k) [ (el, T k) ] q.body None
       | _ -> raise (Vc_error ("quantifier over a non-dict", loc)))
     | _ ->
       let lo = tm (ev g ctx q.lo) and hi = tm (ev g ctx q.hi) in
       let base = match String.index_opt q.idx '$' with Some k -> String.sub q.idx 0 k | None -> q.idx in
       let i = const (Printf.sprintf "%s!%d" base n) Int in
       let binds =
         match (q.seq, q.elem) with
         | Some s, Some el -> ( match ev g ctx s with L l -> [ (el, T (at (l.arr, l.off) i)) ] | _ -> raise (Vc_error ("quantifier over a non-list", loc)))
         | _ -> []
       in
       run_each g ctx loc q.seq (and_ [ le lo i; lt i hi ]) ((q.idx, T i) :: binds) q.body None);
    T (const (Printf.sprintf "%s@%d" q.kind n) Bool)
  | Quant q when (match q.seq with Some { ty = TDict _; _ } -> true | _ -> false) -> (
    (* over a dict's keys: every k it holds *)
    match (q.seq, q.elem) with
    | Some s, Some el -> (
      match (ev g ctx s, s.ty) with
      | D d, TDict (kty, _) ->
        let k = const (Printf.sprintf "%s!%d" el (next g)) (sort_of kty) in
        let held = select d.has k in
        let sub = sub_ctx ~cond:held ctx in
        let body = tm (ev g { sub with bound = SM.add el (T k) sub.bound; binders = ctx.binders @ [ k ] } q.body) in
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
    let body = tm (ev g { sub with bound; binders = ctx.binders @ [ i ] } q.body) in
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
  | O x, O y -> and_ [ eq x.some y.some; implies x.some (equal g x.v y.v) ]
  | O o, T t | T t, O o -> and_ [ o.some; equal g o.v (T t) ]
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

(* an enum field of an object holds one of its members *)
and enum_facts g cls r env =
  match class_of g cls with
  | None -> []
  | Some c ->
    List.concat_map
      (fun (f, (fty : Ir.ty)) ->
        match fty with
        | (TEnum _ | TOption (TEnum _)) when heap_keys g cls f <> [] -> alloc_facts g (heap_read g env cls f r) fty env
        | _ -> [])
      c.cfields

(* each lifecycle of cls as a relation between object r in heap pre and in heap post *)
and class_lifecycles g cls r pre post base =
  match class_of g cls with
  | None -> []
  | Some c ->
    let typed = and_ (enum_facts g cls r pre @ enum_facts g cls r post) in
    List.map
      (fun (owner, (cl : Ir.clause)) ->
        let modpath = match class_of g owner with Some o -> o.cmod | None -> c.cmod in
        let ctx = spec_ctx g ~modpath ~old_env:(SM.add "self" (T r) (heap_env pre)) ~base ~env:(SM.add "self" (T r) (heap_env post)) () in
        (cl, implies typed (term_of cl.cloc (ev g ctx cl.cexpr))))
      c.clcs

and builtin g ctx (e : Ir.expr) name args =
  let loc = e.loc in
  let tm x = term_of loc x in
  let lit_str (a : Ir.expr) = match a.e with Lit (LStr s) -> s | Lit (LInt s) -> s | _ -> raise (Vc_error ("expected a literal", loc)) in
  let assume_ t = assume ctx t in
  match name with
  | "py_mixed_list" ->
    let arr = ref (const_array (Array (Int, sort_of TPythonNumber)) (default_term (sort_of TPythonNumber))) in
    List.iteri (fun i x -> arr := store !arr (int_ i) (tm (ev g ctx x))) args;
    L (list_value !arr zero (int_ (List.length args)) (const (Printf.sprintf "py_mixed_list@%d.ref" (next g)) Int) e.ty)
  | "py_number" ->
    let x = List.hd args in
    let v = tm (ev g ctx x) in
    (match x.ty with
     | TPythonNumber -> T v
     | TInt -> T (mkrec py_num_sort [ tt; v; fval 0.0 ])
     | TReal | TFloat32 -> T (mkrec py_num_sort [ ff; zero; as_float v ])
     | _ -> raise (Vc_error ("Python numeric tag requires a number", loc)))
  | "py_is_kind" ->
    let x, kind = match args with [ x; k ] -> (tm (ev g ctx x), lit_str k) | _ -> raise (Vc_error ("py_is_kind takes a number and kind", loc)) in
    if kind = "int" then T (field x "is_int") else T (not_ (field x "is_int"))
  | "py_int_parse" | "py_float_parse" | "js_parse_int" | "js_parse_float" -> parse_number g ctx e name (tm (ev g ctx (List.hd args)))
  | "comp" -> comprehension g ctx e (ev g ctx (List.hd args))
  | "each" ->
    let seq = match ev g ctx (List.hd args) with L l -> l | _ -> raise (Vc_error ("comprehension over a non-list", loc)) in
    each_element g ctx e seq;
    (match e.ty with
     | TNone -> NoneV
     | t ->
       let r = fresh g "comprehension" t () in
       (match r with
        | L l -> assume ctx (le zero l.len); allocate_list_value g ctx loc l
        | _ -> r))
  | "range_list" ->
    let lo, hi = match args with [ a; b ] -> (tm (ev g ctx a), tm (ev g ctx b)) | _ -> raise (Vc_error ("range_list takes two bounds", loc)) in
    let n = next g in
    let arr, assume = defined_symbol ctx (Printf.sprintf "range@%d.arr" n) (sort_of e.ty) in
    let k = const (Printf.sprintf "i!%d" n) Int in
    let ln = max_ (Term.sub hi lo) zero in
    assume ctx (quant "forall" [ k ] (implies (and_ [ le zero k; lt k ln ]) (eq (select arr k) (add lo k))) [ [| select arr k |] ]);
    let value = list_value arr zero ln (const (Printf.sprintf "range@%d.ref" n) Int) e.ty in
    allocate_list_value g ctx loc value
  | "list_repeat" ->
    let xs, k = match args with [ a; b ] -> (ev g ctx a, tm (ev g ctx b)) | _ -> raise (Vc_error ("list_repeat takes a list and a count", loc)) in
    let xs = match xs with L l -> l | _ -> raise (Vc_error ("list_repeat of a non-list", loc)) in
    let width = match (List.hd args).e with
      | ListLit es -> List.length es
      | Builtin ("py_mixed_list", es) -> List.length es
      | _ -> raise (Fallback "list_repeat of a non-literal")
    in
    let n = next g in
    let arr, assume = defined_symbol ctx (Printf.sprintf "rep@%d.arr" n) (sort_of xs.lty) in
    let repeat_ref = const (Printf.sprintf "rep@%d.ref" n) Int in
    let materialize_repeat len =
      let h = match current_heap ctx with Some h -> h | None -> raise (Fallback "list repetition requires the shared heap") in
      let i = const (Printf.sprintf "rep@%d.heap_index" n) Int in
      let source = if width = 0 then zero else add xs.off (emod i (int_ width)) in
      let item = if width = 0 then Heap.box zero TNone else Heap.read_list h xs.ref source in
      allocate_list_sequence g ctx loc (list_value arr zero len repeat_ref xs.lty) (array_lambda i item)
    in
    if xs.lty = TList TPythonNumber then begin
      let i = const (Printf.sprintf "i!%d" n) Int in
      let ln = mul (int_ width) (max_ k zero) in
      let src_i = add xs.off (emod i (int_ width)) in
      let rng = and_ [ le zero i; lt i ln ] in
      assume ctx (quant "forall" [ i ] (implies rng (eq (select arr i) (select xs.arr src_i))) [ [| select arr i |] ]);
      materialize_repeat ln
    end else begin
    let tags, assume_tags = defined_symbol ctx (Printf.sprintf "rep@%d.py_tags" n) (Array (Int, Bool)) in
    let ints, assume_ints = defined_symbol ctx (Printf.sprintf "rep@%d.py_ints" n) (Array (Int, Int)) in
    let floats, assume_floats = defined_symbol ctx (Printf.sprintf "rep@%d.py_floats" n) (Array (Int, Float64)) in
    let i = const (Printf.sprintf "i!%d" n) Int in
    let ln = mul (int_ width) (max_ k zero) in
    let src_i = add xs.off (emod i (int_ width)) in
    let rng = and_ [ le zero i; lt i ln ] in
    assume ctx (quant "forall" [ i ] (implies rng (eq (select arr i) (select xs.arr src_i))) [ [| select arr i |] ]);
    List.iter2 (fun out (src, define) ->
      define ctx (quant "forall" [ i ] (implies rng (eq (select out i) (select src src_i))) [ [| select out i |] ])
    ) [ tags; ints; floats ] [ (xs.py_tags, assume_tags); (xs.py_ints, assume_ints); (xs.py_floats, assume_floats) ];
      materialize_repeat ln
    end
  | "threw" -> threw g ctx (List.hd args)
  | "dict_lit" when (match e.ty with TDict (TNone, _) -> true | _ -> false) ->
    let ref = const (Printf.sprintf "dict@%d.ref" (next g)) Int in
    allocate_heap_cell g ctx ref (Heap.dict_cell ()) loc;
    D { vals = const_array (Array (Int, Int)) zero; has = const_array (Array (Int, Bool)) ff; ref; dty = e.ty }
  | "dict_lit" ->
    let kt, vt = match e.ty with TDict (k, v) -> (k, v) | _ -> raise (Vc_error ("dict literal of a non-dict type", loc)) in
    let ks = sort_of kt and vs = sort_of vt in
    let vals = ref (const_array (Array (ks, vs)) (default_term vs)) and has = ref (const_array (Array (ks, Bool)) ff) in
    let ref = const (Printf.sprintf "dict@%d.ref" (next g)) Int in
    allocate_heap_cell g ctx ref (Heap.dict_cell ()) loc;
    let rec pairs = function
      | k :: v :: rest ->
        let raw_key = tm (ev g ctx k) in
        let key, admissible = Heap.canonical_key raw_key kt g.info.language in
        oblige g "key" ctx admissible loc "dictionary key uses supported source equality";
        assume ctx admissible;
        let value = coerce (ev g ctx v) (Some vt) in
        let raw_value = term_of loc value in
        vals := store !vals raw_key raw_value;
        has := store !has raw_key tt;
        let boxed_value = box_stored_value g ctx loc vt value in
        (match current_heap ctx with Some h -> set_current_heap g ctx (Heap.write_dict h ref key (Heap.box raw_key kt) boxed_value) | None -> ());
        pairs rest
      | _ -> ()
    in
    pairs args;
    D { vals = !vals; has = !has; ref; dty = e.ty }
  | _ -> (
    (match (name, ctx.state) with "await", Some st when not ctx.spec -> check_objects g ~guard:ctx.guard st.facts st.env loc "at the await" | _ -> ());
    let vals = List.map (ev g ctx) args in
    let lst = function L l -> l | _ -> raise (Vc_error ("builtin on a non-list: " ^ name, loc)) in
    let dct = function D d -> d | _ -> raise (Vc_error ("builtin on a non-dict: " ^ name, loc)) in
    let copy_list (l : lv) off len = match copy_list_value g ctx loc l off len with L copied -> copied | _ -> assert false in
    let copy_dict (d : dv) = copy_dict_value g ctx loc d in
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
        o.v
      | NoneV ->
        oblige g "none" ctx ff loc (Printf.sprintf "'%s' is not None here" (expr_name (List.hd args)));
        raise (Vc_error ("value is always None here", loc))
      | v -> v)
    | "from_opaque", [ x ] ->
      let ty = e.ty in
      let tag = ty_str ty in
      let v = pack ty (List.map (fun (suffix, srt) -> fn (Printf.sprintf "unbox.%s.%s" tag suffix) (Array.of_list (flatten x)) srt) (components ty)) in
      let scalar = function Ir.TInt -> Some "int" | TStr -> Some "str" | TBool -> Some "bool" | _ -> None in
      let v =
        match (x, ty, v) with
        | L xl, TList et, L vl when scalar et <> None ->
          (* a list of unchecked values seen at list[int]: element by element,
             where an element is one (whether it is is for the code to check) *)
          let kind = Option.get (scalar et) in
          let vl = { vl with off = zero; len = xl.len } in
          let i = const (Printf.sprintf "i!%d" (next g)) Int in
          let b = at (xl.arr, xl.off) i in
          assume_ (quant "forall" [ i ] (implies (and_ [ le zero i; lt i xl.len ]) (implies (fn "opaque.isinstance.Bool" [| b; str kind |] Bool) (eq (fn (Printf.sprintf "unbox.%s." kind) [| b |] (sort_of et)) (at (vl.arr, zero) i)))) [ [| at (vl.arr, zero) i |] ]);
          L vl
        | _ -> v
      in
      (match x with T b -> box_facts g ctx b v ty false | _ -> ());
      (match v with L l -> assume_ (le zero l.len) | _ -> ());
      (match ctx.state with
       | Some st ->
         List.iter assume_ (alloc_facts g v ty st.env);
         (match (ty, v) with TClass c, T r -> List.iter (fun (_, t) -> assume_ t) (class_invariants g c r st.env ctx.base) | _ -> ())
       | None -> ());
      note_assumed g loc "values from unchecked code have the types they are used at";
      v
    | "to_opaque", [ x ] ->
      let aty = (List.hd args).ty in
      let tag = ty_str aty in
      let comps = flatten x in
      let b = fn ("box." ^ tag) (Array.of_list comps) Opaque in
      box_facts g ctx b x aty true;
      (* unboxed at the type it was boxed at, a value is itself (a generic function's T) *)
      if aty <> TNone then List.iter2 (fun (suffix, srt) c -> assume_ (eq (fn (Printf.sprintf "unbox.%s.%s" tag suffix) [| b |] srt) c)) (components aty) comps;
      T b
    | "opaque_op", _ ->
      let op = lit_str (List.hd args) in
      let srt = sort_of e.ty in
      let part = String.length op > 5 && String.sub op 0 5 = "part." in
      let sym = if part then "attr." ^ String.sub op 5 (String.length op - 5) else op in
      let cmp = match op with "cmp.lt" -> Some lt | "cmp.le" | "cmp.lte" -> Some le | "cmp.gt" -> Some gt | "cmp.ge" | "cmp.gte" -> Some ge | "cmp.eq" -> Some eq | "cmp.ne" | "cmp.noteq" -> Some ne | _ -> None in
      (match (cmp, flat_rest) with
      | Some f, [ a; b ] when (a.sort = Opaque && b.sort = Int) || (a.sort = Int && b.sort = Opaque) ->
        (* against an int: an int compares as one; anything else stays unknown *)
        let x = if a.sort = Opaque then a else b in
        let ux = fn "unbox.int." [| x |] Int in
        let l, r = if a.sort = Opaque then (ux, b) else (a, ux) in
        T (ite (fn "opaque.isinstance.Bool" [| x; str "int" |] Bool) (f l r) (fn (Printf.sprintf "opaque.%s.%s" op (sort_name srt)) (Array.of_list flat_rest) srt))
      | _ ->
      let r = fn (Printf.sprintf "opaque.%s.%s" sym (sort_name srt)) (Array.of_list flat_rest) srt in
      if (not ctx.spec) && not ctx.quiet then note_assumed g loc "operations on values from unchecked code do not raise";
      if e.ty = TInt && op = "len" then assume_ (le zero r);
      (match flat_rest with
       | [ x ] when part && srt = Opaque ->
         assume_ (lt (depth r) (depth x));
         if (not ctx.spec) && not ctx.quiet then note_assumed g loc "a frozen dataclass or NamedTuple holds values built before it"
       | _ -> ());
      T r)
    | "depth", [ x ] ->
      let x = tm x in
      assume_ (le zero (depth x));
      T (depth x)
    | "await", x :: _ ->
      (match ctx.state with Some _ when not ctx.spec -> suspend g ctx loc | _ -> ());
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
    | "py_mixed_list", items ->
      let n = next g in
      let arr = ref (const_array (Array (Int, Float64)) (fval 0.0)) in
      let tags = ref (const_array (Array (Int, Bool)) ff) in
      let ints = ref (const_array (Array (Int, Int)) zero) in
      let floats = ref (const_array (Array (Int, Float64)) (fval 0.0)) in
      List.iteri (fun i item ->
        let x = tm item and index = int_ i in
        if x.sort = Int then begin
          arr := store !arr index (as_float_to Float64 x);
          tags := store !tags index tt;
          ints := store !ints index x
        end else begin
          let x = as_float_to Float64 x in
          arr := store !arr index x;
          floats := store !floats index x
        end
      ) items;
      L { arr = !arr; off = zero; len = int_ (List.length items); py_tags = !tags; py_ints = !ints; py_floats = !floats; ref = const (Printf.sprintf "mixed@%d.ref" n) Int; view = ff; lty = e.ty }
    | ("dict_keys" | "dict_values"), [ d ] ->
      let d = dct d in
      let n = next g in
      let out_ty = if name = "dict_keys" then dkey d else dval d in
      (match current_heap ctx with
       | Some h ->
         check_heap_kind g ctx d.ref 2 loc "dictionary iteration refers to an allocated dictionary";
         let cell = Heap.cell_at h d.ref in
         let history_len = field cell "key_count" and len = field cell "len" in
         let seq = const (Printf.sprintf "dict_%s@%d.seq" name n) (Array (Int, Heap.value)) in
         let j = const (Printf.sprintf "dict_%s@%d.history" name n) Int in
         let live = select (field cell "key_live") j in
         let rank = Heap.dict_rank h d.ref j in
         let key = select (field cell "keys") j in
         let item = if name = "dict_keys" then Heap.dict_original_key h d.ref j else Heap.read_dict h d.ref key in
         assume_ (quant "forall" [ j ]
           (implies (and_ [ le zero j; lt j history_len; live ]) (eq (select seq rank) item))
           [ [| select seq rank |] ]);
         let ref = const (Printf.sprintf "dict_%s@%d.ref" name n) Int in
         allocate_heap_cell g ctx ref (Heap.list_cell len seq) loc;
         let h = match current_heap ctx with Some h -> h | None -> h in
         let view = list_value (const (Printf.sprintf "dict_%s@%d.arr" name n) (Array (Int, sort_of out_ty))) zero len ref (TList out_ty) in
         let view = match ctx.state with Some st -> refresh_list_view g st h view | None -> view in
         L view
       | None ->
         let keys = const (Printf.sprintf "keys@%d" n) (Array (Int, sort_of (dkey d))) in
         let ln = const (Printf.sprintf "keys@%d.len" n) Int in
         let i = const (Printf.sprintf "i!%d" n) Int in
         let rng = and_ [ le zero i; lt i ln ] in
         assume_ (le zero ln);
         assume_ (quant "forall" [ i ] (implies rng (select d.has (select keys i))) [ [| select keys i |] ]);
         let arr = const (Printf.sprintf "dict_%s@%d.arr" name n) (Array (Int, sort_of out_ty)) in
         L (list_value arr zero ln (const (Printf.sprintf "dict_%s@%d.ref" name n) Int) (TList out_ty)))
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
    | "list_copy", [ xs ] -> let l = lst xs in L (copy_list l l.off (list_len ctx l))
    | "list_concat", [ xs; ys ] ->
      let a = lst xs and b = lst ys in
      let n = next g in
      let arr = const (Printf.sprintf "cat@%d.arr" n) a.arr.sort in
      let ln = add a.len b.len in
      let i = const (Printf.sprintf "i!%d" n) Int and k = const (Printf.sprintf "k!%d" n) Int in
      let ref = const (Printf.sprintf "cat@%d.ref" n) Int in
      let materialize_concat l =
        let h = match current_heap ctx with Some h -> h | None -> raise (Fallback "list concatenation requires the shared heap") in
        let j = const (Printf.sprintf "cat@%d.heap_index" n) Int in
        let left = Heap.read_list h a.ref (add a.off j) in
        let right = Heap.read_list h b.ref (add b.off (sub j a.len)) in
        let item = ite (lt j a.len) left right in
        allocate_list_sequence g ctx loc l (array_lambda j item)
      in
      assume_ (quant "forall" [ i ] (implies (and_ [ le zero i; lt i a.len ]) (eq (select arr i) (at (a.arr, a.off) i))) [ [| select arr i |] ]);
      assume_ (quant "forall" [ k ] (implies (and_ [ le a.len k; lt k ln ]) (eq (select arr k) (at (b.arr, b.off) (sub k a.len)))) [ [| select arr k |] ]);
      if a.lty = TList TPythonNumber then materialize_concat (list_value arr zero ln ref a.lty)
      else begin
      let tags = const (Printf.sprintf "cat@%d.py_tags" n) (Array (Int, Bool)) in
      let ints = const (Printf.sprintf "cat@%d.py_ints" n) (Array (Int, Int)) in
      let floats = const (Printf.sprintf "cat@%d.py_floats" n) (Array (Int, Float64)) in
      let outs = [ tags; ints; floats ] in
      let left = [ a.py_tags; a.py_ints; a.py_floats ] and right = [ b.py_tags; b.py_ints; b.py_floats ] in
      List.iter2 (fun out src ->
        let body = implies (and_ [ le zero i; lt i a.len ]) (eq (select out i) (select src (add a.off i))) in
        assume_ (quant "forall" [ i ] body [ [| select out i |] ])
      ) outs left;
      List.iter2 (fun out src ->
        let body = implies (and_ [ le a.len k; lt k ln ]) (eq (select out k) (select src (add b.off (sub k a.len)))) in
        assume_ (quant "forall" [ k ] body [ [| select out k |] ])
      ) outs right;
      materialize_concat { arr; off = zero; len = ln; py_tags = tags; py_ints = ints; py_floats = floats; ref; view = ff; lty = a.lty }
      end
    | "dict_copy", [ d ] -> copy_dict (dct d)
    | "dict_set", [ d; k; v ] ->
      let d = dct d in
      let raw_key = tm k and kt = dkey d in
      let key, valid = Heap.canonical_key raw_key kt g.info.language in
      oblige g "key" ctx valid loc "dictionary key uses supported source equality";
      assume ctx valid;
      let value = coerce v (Some (dval d)) in
      let raw_value = tm value in
      let boxed_value = box_stored_value g ctx loc (dval d) value in
      (match current_heap ctx with Some h -> set_current_heap g ctx (Heap.write_dict h d.ref key (Heap.box raw_key kt) boxed_value) | None -> ());
      (match current_heap ctx with Some h -> D (dict_views g h d) | None -> D { d with vals = store d.vals raw_key raw_value; has = store d.has raw_key tt })
    | "dict_remove", [ d; k ] ->
      let d = dct d in
      let key, valid = Heap.canonical_key (tm k) (dkey d) g.info.language in
      oblige g "key" ctx valid loc "dictionary key uses supported source equality";
      assume ctx valid;
      (match current_heap ctx with Some h -> set_current_heap g ctx (Heap.delete_dict h d.ref key) | None -> ());
      (match current_heap ctx with Some h -> D (dict_views g h d) | None -> D { d with has = store d.has (tm k) ff })
    | "dict_del", [ d; k ] ->
      let d = dct d in
      let key, valid = Heap.canonical_key (tm k) (dkey d) g.info.language in
      oblige g "key" ctx valid loc "dictionary key uses supported source equality";
      assume ctx valid;
      (match current_heap ctx with
       | Some h ->
         oblige g "key" ctx (Heap.has_dict h d.ref key) loc (Printf.sprintf "key being deleted from '%s' is present" (expr_name (List.hd args)));
         set_current_heap g ctx (Heap.delete_dict h d.ref key)
       | None -> oblige g "key" ctx (select d.has (tm k)) loc (Printf.sprintf "key being deleted from '%s' is present" (expr_name (List.hd args))));
      (match current_heap ctx with Some h -> D (dict_views g h d) | None -> D { d with has = store d.has (tm k) ff })
    | ("dict_has" | "dict_get_opt" | "dict_get_or"), d :: k :: rest -> (
      let d = dct d in
      let raw_key = tm k in
      let canonical, valid = Heap.canonical_key raw_key (dkey d) g.info.language in
      oblige g "key" ctx valid loc "dictionary key uses supported source equality";
      assume ctx valid;
      let has, v = match current_heap ctx with
        | Some h ->
          check_heap_kind g ctx d.ref 2 loc "dictionary lookup refers to an allocated dictionary";
          let has = Heap.has_dict h d.ref canonical in
          let boxed = Heap.read_dict h d.ref canonical in
          let vt = dval d in
          let valid = accepts_view g h vt boxed in
          oblige g "type" ctx valid loc "dictionary value matches its typed view";
          assume ctx valid;
          (has, unbox_value g boxed vt h)
        | None -> (select d.has raw_key, T (select d.vals raw_key))
      in
      match (name, rest) with
      | "dict_has", _ -> T has
      | "dict_get_opt", _ -> O { some = has; v; oty = TOption (dval d) }
      | _, [ dflt ] -> ite_val has v (coerce dflt (Some (dval d)))
      | _ -> raise (Vc_error ("dict_get_or needs a default", loc)))
    | "len", [ xs ] ->
      (match xs, current_heap ctx with
       | L l, Some _ -> T (list_len ctx l)
       | D d, Some h -> T (Heap.read_len h d.ref)
       | L l, None -> T l.len
       | D d, None -> T (fn "dict.len" [| d.ref |] Int)
       | _ -> raise (Vc_error ("len on a non-container", loc)))
    | "abs", [ T v ] when v.sort = py_num_sort ->
      let tag, integer, floating = py_parts v in
      T (mkrec py_num_sort [ tag; abs_ integer; fabs floating ])
    | "abs", [ x ] -> T (abs_ (tm x))
    | name, items when name = "py_sum_mixed" || starts_with "py_sum_mixed_cpython_" name ->
      let max_float_int = mk (Big "179769313486231580793728971405303415079934132710037826936173778980444968292764750946649017977587207096330286416692887910946555547851940402630657488671505820681908902000708383676273854845817711531764475730270069855571366959622842914819860834936475292719074168444365510704342711559699508093042880177904174497791") Int in
      let floatable x = le (abs_ x) max_float_int in
      let compensated =
        try
          let parts = String.split_on_char '_' name in
          let major = int_of_string (List.nth parts 4) and minor = int_of_string (List.nth parts 5) in
          major > 3 || (major = 3 && minor >= 12)
        with _ -> false
      in
      let long_min = mk (Big "-9223372036854775808") Int and long_max = mk (Big "9223372036854775807") Int in
      let zero_f = fval 0.0 in
      let rec fold total in_float int_total int_fast hi lo = function
        | [] ->
          let ordinary = as_float_to Float64 total in
          if compensated then
            let correction = ite (and_ [ ne lo zero_f; is_finite lo ]) (add hi lo) hi in
            T (ite int_fast correction ordinary)
          else T ordinary
        | item :: rest ->
          let x = tm item in
          let was_in_float = in_float in
          let enters_float = was_in_float || List.mem x.sort [ Float32; Float64 ] in
          let int_total, int_fast =
            if not was_in_float && x.sort = Int then
              let next = add int_total x in
              (next, and_ [ int_fast; le long_min x; le x long_max; le long_min next; le next long_max ])
            else int_total, int_fast
          in
          if enters_float then begin
            if x.sort = Int then oblige g "overflow" ctx (floatable x) loc "integer converted by sum fits in a float";
            if total.sort = Int then oblige g "overflow" ctx (floatable total) loc "integer total converted by sum fits in a float";
            let next_total = add (as_float_to Float64 total) (as_float_to Float64 x) in
            if compensated then begin
              if was_in_float then begin
                let xf = as_float_to Float64 x in
                let next_hi = add hi xf in
                let correction = ite (le (abs_ xf) (abs_ hi)) (add lo (add (sub hi next_hi) xf)) (add lo (add (sub xf next_hi) hi)) in
                fold next_total true int_total int_fast next_hi correction rest
              end else fold next_total true int_total int_fast next_total zero_f rest
            end else fold next_total true int_total int_fast hi lo rest
          end else fold (add total x) false int_total int_fast hi lo rest
      in
      fold (int_ 0) false (int_ 0) (tt) zero_f zero_f vals
    | ("min" | "max" | "py_min" | "py_max"), x :: rest ->
      let is_min = name = "min" || name = "py_min" in
      let py = name = "py_min" || name = "py_max" in
      let choose acc y =
        let y = tm y in
        if e.ty = TPythonNumber then
          let take_acc = if is_min then not_ (py_lt y acc) else not_ (py_lt acc y) in
          ite take_acc acc y
        else
        let take_acc = if is_min then (if py then not_ (lt y acc) else le acc y) else (if py then not_ (lt acc y) else le y acc) in
        ite take_acc acc y
      in
      T (List.fold_left choose (tm x) rest)
    | name, [ xs ] when String.length name > 7 && String.sub name 0 7 = "py_sum_" ->
      let l = lst xs in
      let version = String.sub name 7 (String.length name - 7) in
      let cpython = starts_with "py_sum_cpython_" name in
      let major, minor =
        try
          let parts = String.split_on_char '_' version in
          (int_of_string (List.nth parts 1), int_of_string (List.nth parts 2))
        with _ -> (0, 0)
      in
      if cpython && l.lty = TList TPythonNumber then begin
        let state_name = "py_numeric_sum_state_" ^ version and sum_name = "seqsum_py_numeric_" ^ version in
        let state_sort = Rec ("PyNumericSumState_" ^ version, [ ("in_float", Bool); ("int_total", Int); ("fast", Bool); ("ordinary", Float64); ("hi", Float64); ("lo", Float64) ]) in
        let i = const (Printf.sprintf "%d.sum_index" loc.line) Int in
        let prefix = fn state_name [| l.arr; l.off; i |] state_sort in
        let item = select l.arr i in
        let is_int = field item "is_int" and integer = field item "integer" in
        let limit = int_ ((1 lsl 1024) - (1 lsl 970)) in
        let safe = and_ [
          implies (and_ [ not_ (field prefix "in_float"); not_ is_int ]) (lt (abs_ (field prefix "int_total")) limit);
          implies (and_ [ field prefix "in_float"; is_int ]) (lt (abs_ integer) limit);
        ] in
        let range = and_ [ le l.off i; lt i (add l.off l.len) ] in
        oblige g "overflow" ctx (quant "forall" [ i ] (implies range safe) [ [| field prefix "int_total" |] ]) loc "integer values converted by sum fit in a float";
        T (fn sum_name [| l.arr; l.off; add l.off l.len |] py_num_sort)
      end else if cpython then begin
        match (num l.off, num l.len) with
        | Some off, Some len when off.d = 1 && len.d = 1 && len.n >= 0 ->
          let max_float_int = mk (Big "179769313486231580793728971405303415079934132710037826936173778980444968292764750946649017977587207096330286416692887910946555547851940402630657488671505820681908902000708383676273854845817711531764475730270069855571366959622842914819860834936475292719074168444365510704342711559699508093042880177904174497791") Int in
          let floatable x = le (abs_ x) max_float_int in
          let long_min = mk (Big "-9223372036854775808") Int and long_max = mk (Big "9223372036854775807") Int in
          let zero_f = fval 0.0 in
          let in_float = ref ff and int_total = ref zero and fast = ref tt in
          let ordinary = ref zero_f and hi = ref zero_f and lo = ref zero_f in
          let safe_prefix = ref tt and safe_items = ref tt in
          for i = 0 to len.n - 1 do
            let index = add l.off (int_ i) in
            let is_int = select l.py_tags index in
            let int_value = select l.py_ints index and float_value = select l.py_floats index in
            let was_in_float = !in_float and previous_int_total = !int_total in
            safe_prefix := and_ [ !safe_prefix; implies (not_ was_in_float) (floatable previous_int_total) ];
            safe_items := and_ [ !safe_items; implies is_int (floatable int_value) ];
            let start_int = and_ [ not_ !in_float; is_int ] in
            let start_float = and_ [ not_ !in_float; not_ is_int ] in
            let entered = ite is_int (as_float_to Float64 int_value) float_value in
            let next_int_total = add previous_int_total int_value in
            fast := ite start_int
              (and_ [ !fast; le long_min int_value; le int_value long_max; le long_min next_int_total; le next_int_total long_max ])
              !fast;
            let next_ordinary = ite was_in_float (add !ordinary entered) (add (as_float_to Float64 previous_int_total) entered) in
            ordinary := ite start_int !ordinary next_ordinary;
            let next_hi = add !hi entered in
            let correction = ite (le (abs_ entered) (abs_ !hi)) (add !lo (add (sub !hi next_hi) entered)) (add !lo (add (sub entered next_hi) !hi)) in
            hi := ite start_int !hi (ite start_float next_ordinary next_hi);
            lo := ite start_int !lo (ite start_float zero_f correction);
            int_total := ite start_int next_int_total previous_int_total;
            in_float := or_ [ was_in_float; not_ is_int ];
          done;
          safe_prefix := and_ [ !safe_prefix; implies (not_ !in_float) (floatable !int_total) ];
          oblige g "overflow" ctx (and_ [ !safe_prefix; !safe_items ]) loc "integer converted by sum fits in a float";
          let corrected = ite (and_ [ ne !lo zero_f; is_finite !lo ]) (add !hi !lo) !hi in
          let result = if (major, minor) >= (3, 12) then ite !fast corrected !ordinary else !ordinary in
          T result
        | _ -> raise (Fallback "symbolic CPython numeric-list sum state")
      end else
      let fd = "seqsum_py_" ^ version in
      let compensated =
        try
          let parts = String.split_on_char '_' version in
          let major = int_of_string (List.nth parts 1) and minor = int_of_string (List.nth parts 2) in
          major > 3 || (major = 3 && minor >= 12)
        with _ -> false
      in
      if not compensated then T (fn "seqsum_f64" [| l.arr; l.off; add l.off l.len |] Float64)
      else
      let rec fold i hi lo n =
        if i >= n then ite (and_ [ ne lo (fval 0.0); is_finite lo ]) (add hi lo) hi
        else
          let x = select l.arr (int_ (i + (match num l.off with Some q -> q.n | _ -> 0))) in
          let t = add hi x in
          let correction = ite (le (abs_ x) (abs_ hi)) (add lo (add (sub hi t) x)) (add lo (add (sub x t) hi)) in
          fold (i + 1) t correction n
      in
      (match (num l.off, num l.len) with
       | Some off, Some len when off.d = 1 && len.d = 1 && len.n >= 0 -> T (fold 0 (fval 0.0) (fval 0.0) len.n)
       | _ -> T (fn fd [| l.arr; l.off; add l.off l.len |] Float64))
    | "sum", [ xs ] ->
      let l = lst xs in
      let elem = match l.lty with TList t -> t | _ -> TInt in
      let fd = match sort_of elem with Int -> "seqsum" | Real -> "seqsum_r" | Float32 -> "seqsum_f32" | Float64 -> "seqsum_f64" | _ -> "seqsum_r" in
      let total = fn fd [| l.arr; l.off; add l.off l.len |] (sort_of elem) in
      comp_sum g ctx l total;
      T total
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
      let n = list_len ctx l in
      let norm b default = match b with NoneV -> default | b -> let b = tm b in ite (lt b zero) (max_ (add b n) zero) (min_ b n) in
      let lo2 = norm lo zero and hi2 = norm hi n in
      if (match (lo, hi) with NoneV, NoneV -> true | _ -> false) && g.info.language = "rust" then L { l with view = tt }
      else
        let len = max_ (sub hi2 lo2) zero in
        if g.info.language = "rust" then L { l with off = add l.off lo2; len; view = tt }
        else L (copy_list l (add l.off lo2) len)
    | "list_append", [ xs; v ] ->
      let l = lst xs in
      let ty = match l.lty with TList t -> t | _ -> TNone in
      let value = coerce v (Some ty) in
      let index = list_len ctx l in
      let boxed_value = box_stored_value g ctx loc ty value in
      (match current_heap ctx with Some h -> set_current_heap g ctx (Heap.append_list h l.ref boxed_value) | None -> ());
      L { (numeric_store l (add l.off index) (tm value)) with len = add index one }
    | "list_set", [ xs; i; v ] ->
      let l = lst xs in
      let len = list_len ctx l in
      let j = index_of g (l.arr, l.off, len) (tm i) true ctx loc (expr_name (List.hd args)) in
      let ty = match l.lty with TList t -> t | _ -> TNone in
      let value = coerce v (Some ty) in
      let boxed_value = box_stored_value g ctx loc ty value in
      (match current_heap ctx with Some h -> set_current_heap g ctx (Heap.write_list h l.ref (add l.off j) boxed_value) | None -> ());
      L (numeric_store l (add l.off j) (tm value))
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
    | "to_real", [ T v ] when v.sort = py_num_sort ->
      let tag, integer, floating = py_parts v in
      let converted = ite tag (as_float integer) floating in
      oblige g "overflow" ctx (implies tag (is_finite converted)) loc "integer converted to float does not overflow";
      T converted
    | "to_real", [ x ] -> T (as_float_to (sort_of e.ty) (tm x))
    | "floor", [ x ] ->
      let x = tm x in
      if List.mem x.sort [ Float32; Float64 ] then oblige g "finite" ctx (is_finite x) loc "number is finite where it is rounded to an integer";
      T (floor x)
    | "ceil", [ x ] -> T (neg (floor (neg (tm x))))
    | "trunc", [ T v ] when v.sort = py_num_sort ->
      let tag, integer, floating = py_parts v in
      oblige g "finite" ctx (implies (not_ tag) (is_finite floating)) loc "number is finite where it is rounded to an integer";
      let exact = fto_real floating in
      let rounded = ite (le (real (Q.of_int 0)) exact) (floor exact) (neg (floor (neg exact))) in
      T (ite tag integer rounded)
    | "trunc", [ x ] -> let x = tm x in T (ite (le (real (Q.of_int 0)) x) (floor x) (neg (floor (neg x))))
    | "trunc_sat", [ x; lo; hi ] ->
      let x = tm x and lo = tm lo and hi = tm hi in
      let exact = fto_real x in
      let truncated = ite (le (real (Q.of_int 0)) exact) (floor exact) (neg (floor (neg exact))) in
      T (ite (fpred "fp.isNaN" x) zero (ite (le x (as_float_to x.sort lo)) lo (ite (le (as_float_to x.sort hi) x) hi truncated)))
    | "round_even", [ x ] -> T (round_even (tm x))
    | "round_up", [ x ] -> T (floor (add (tm x) (real (Q.make 1 2))))
    | ("js_floor" | "js_ceil" | "js_trunc" | "js_round" as rounding), [ x ] ->
      let x = tm x in
      let exact = fto_real x in
      let rounded =
        match rounding with
        | "js_floor" -> floor exact
        | "js_ceil" -> neg (floor (neg exact))
        | "js_trunc" -> ite (le (real (Q.of_int 0)) exact) (floor exact) (neg (floor (neg exact)))
        | _ -> floor (add exact (real (Q.make 1 2)))
      in
      let result = as_float_to x.sort rounded in
      let negative_zero = and_ [ fpred_neg x; eq rounded zero ] in
      let result = ite negative_zero (neg (fval 0.0)) result in
      T (ite (is_finite x) result x)
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

and each_element g ctx (e : Ir.expr) seq =
  let src, names, body, cond =
    match e.e with
    | Builtin (_, [ src; { e = Lit (LStr el); _ }; body ]) -> (src, el, body, None)
    | Builtin (_, [ src; { e = Lit (LStr el); _ }; body; cond ]) -> (src, el, body, Some cond)
    | _ -> raise (Fallback "comprehension shape")
  in
  (* "x" or "x,i": the element and its index *)
  let elem, idx = match String.index_opt names ',' with Some k -> (String.sub names 0 k, Some (String.sub names (k + 1) (String.length names - k - 1))) | None -> (names, None) in
  let i = const (Printf.sprintf "%s!%d" elem (next g)) Int in
  let binds = (elem, T (at (seq.arr, seq.off) i)) :: (match idx with Some x -> [ (x, T i) ] | None -> []) in
  run_each g ctx e.loc (Some src) (and_ [ le zero i; lt i seq.len ]) binds body cond

(* A comprehension's body run on an arbitrary element (binds, within rng),
   from any state the earlier elements may have left: its obligations hold
   for every element, and what it may change is unknown afterwards. *)
and run_each g ctx loc (src : Ir.expr option) rng binds body cond =
  let parts = match cond with Some c -> [ c; body ] | None -> [ body ] in
  let names, appends = modified g (List.map (fun x -> Ir.ExprStmt (loc, x)) parts) in
  let calls_out = List.exists (fun x -> let hit = ref false in Ir.walk_expr (fun (y : Ir.expr) -> match y.e with Extern _ -> hit := true | _ -> ()) x; !hit) parts in
  let names = if calls_out then names @ List.filter (fun v -> Hashtbl.mem g.info.fn.locals v && not (List.mem v names)) g.info.fn.escaped else names in
  let rec container (x : Ir.expr) = match x.e with Builtin (("dict_keys" | "from_opaque"), [ a ]) -> container a | _ -> x in
  (match Option.map container src with
   | Some { e = Var n; ty = TList _ | TDict _; _ } when List.mem n names -> raise (Vc_error (Printf.sprintf "the comprehension changes '%s' while iterating over it" n, loc))
   | _ -> ());
  let framed =
    if Hashtbl.mem g.prog.hands_out g.info.key || g.info.fn.escaped <> [] then []
    else
      let checked, _ = modified ~extern_heap:false g (List.map (fun x -> Ir.ExprStmt (loc, x)) parts) in
      List.filter (fun n -> is_heap n && n <> "@alloc" && not (List.mem n checked)) names
  in
  let havoc_here () =
    match ctx.state with
    | Some st ->
      let n0 = Dynarray.length st.facts in
      let h = havoc ~framed g st names appends in
      for k = n0 to Dynarray.length h.facts - 1 do assume ctx (Dynarray.get h.facts k) done;
      st.env <- h.env
    | None -> ()
  in
  havoc_here ();
  let sub = sub_ctx ~cond:rng ctx in
  let sub = { sub with bound = List.fold_left (fun m (k, v) -> SM.add k v m) sub.bound binds } in
  let sub = match cond with Some c -> sub_ctx ~cond:(term_of loc (ev g sub c)) sub | None -> sub in
  ignore (ev g sub body);
  havoc_here ()

and modified ?(extern_heap = true) g body =
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
       | FieldAssign (_, _, cls, f, _) ->
         List.iter (fun (hk, _) -> addn hk) (heap_keys g cls f);
         if has_invariants g cls then addn (written_key cls)
       | _ -> ());
      List.iter
        (fun e ->
          Ir.walk_expr
            (fun (x : Ir.expr) ->
              if suspends x then begin
                addn segment;
                List.iter addn (all_heap_keys g)
              end;
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
                if extern_heap && extern_touches_heap g args then begin
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

(* [framed]: heap components only unchecked code changes, which cannot reach
   the objects this call created (it hands none out) *)
and havoc ?(framed = []) g (st : state) names appends : state =
  let h = copy_state st in
  let alloc0 = alloc_of g.entry in
  let fresh_l = fresh_lists g in
  List.iter
    (fun name ->
      match SM.find_opt name h.env with
      | _ when name = segment ->
        SM.iter
          (fun k v ->
            match v with
            | T o when is_segment k -> h.env <- SM.add k (T (const (Printf.sprintf "%s@%d" (String.sub k 1 (String.length k - 1)) (next g)) o.sort)) h.env
            | _ -> ())
          h.env
      | None -> ()
      | Some (T o) when is_written_key name -> h.env <- SM.add name (T (const (Printf.sprintf "%s@%d" (String.sub name 1 (String.length name - 1)) (next g)) o.sort)) h.env
      | Some old when is_heap name -> (
        match old with
        | T o ->
          let nw = const (Printf.sprintf "%s@%d" (String.sub name 1 (String.length name - 1)) (next g)) o.sort in
          h.env <- SM.add name (T nw) h.env;
          if name = "@alloc" then begin
            let r = const (Printf.sprintf "r!%d" (next g)) Int in
            Dynarray.add_last h.facts (monotone_alloc o nw r)
          end
          else if List.mem name framed then (
            match o.sort with
            | Array (Int, _) -> Dynarray.add_last h.facts (created_kept alloc0 (alloc_of st.env) o nw (const (Printf.sprintf "r!%d" (next g)) Int))
            | _ -> ())
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
          | _ -> h.env <- SM.add name (fresh g name ty ()) h.env);
          if SM.mem "@alloc" h.env then List.iter (Dynarray.add_last h.facts) (alloc_facts g (SM.find name h.env) ty h.env);
          (* its objects were all created by this call *)
          match SM.find name h.env with
          | L nv when List.mem name fresh_l ->
            let i = const (Printf.sprintf "i!%d" (next g)) Int in
            Dynarray.add_last h.facts (quant "forall" [ i ] (implies (and_ [ le zero i; lt i nv.len ]) (not_ (select alloc0 (at (nv.arr, nv.off) i)))) [ [| at (nv.arr, nv.off) i |] ])
          | _ -> ()))
    (List.sort compare names);
  h

(* local lists of objects that only ever hold objects this call creates:
   assigned only list literals of new objects, appended only new objects,
   never handed to unchecked code *)
and fresh_lists g =
  let fn = g.info.fn in
  let ok = ref (Hashtbl.fold (fun n (t : Ir.ty) acc -> match t with TList (TClass _) when not (List.mem_assoc n fn.params) -> n :: acc | _ -> acc) fn.locals []) in
  let drop n = ok := List.filter (fun x -> x <> n) !ok in
  Ir.walk_stmts
    (fun (st : Ir.stmt) ->
      (match st with
       | Assign (_, n, { e = ListLit es; _ }) when List.for_all (fun (x : Ir.expr) -> match x.e with New _ -> true | _ -> false) es -> ignore n
       | Assign (_, n, _) -> drop n
       | Append (_, n, { e = New _; _ }) -> ignore n
       | Append (_, n, _) | IndexAssign (_, n, _, _, _) -> drop n
       | _ -> ());
      List.iter (fun e -> Ir.walk_expr (fun (x : Ir.expr) -> match x.e with Extern (_, args) -> List.iter (fun (a : Ir.expr) -> match a.e with Var n -> drop n | _ -> ()) args | _ -> ()) e) (Ir.stmt_exprs st))
    fn.body;
  !ok

(* a loop that suspends splits its stretches at its head: each part keeps the
   lifecycles (checked on the way in and after each iteration), and the part
   after the head starts from the head's heap *)
and cut g ?(at_head = false) names (st : state) (site : Ir.loc) =
  if List.mem segment names then if at_head then resume st else check_lifecycles g st.facts st.env site

and effectful g (e : Ir.expr) =
  let hit = ref false in
  Ir.walk_expr
    (fun (x : Ir.expr) ->
      match x.e with
      | Extern _ | New _ | Builtin (("await" | "each"), _) -> hit := true
      | Call (f, _) -> ( match resolve g g.info.modpath f with Some t when t.definitional -> () | _ -> hit := true)
      | _ -> ())
    e;
  !hit

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
  let is_pure = pure g body && match cond with Some c -> pure g c | None -> true in
  (* under a quantifier the new list is a function of its variables, defined for all of them *)
  let under = ctx.binders <> [] && is_pure in
  let sym name srt = if under then fn name (Array.of_list ctx.binders) srt else const name srt in
  let assume = if under then assume_for_all_binders else assume in
  let arr = sym (Printf.sprintf "comp@%d.arr" n) (sort_of e.ty) in
  let filtered_state = ref None in
  let ln =
    match cond with
    | None -> seq.len
    | Some _ when is_pure ->
      let prefix = sym (Printf.sprintf "comp@%d.prefix" n) (Array (Int, Int)) in
      let j = const (Printf.sprintf "j!%d" n) Int in
      let sub_j = { ctx with spec = true; quiet = true; bound = SM.add elem (T (at (seq.arr, seq.off) j)) ctx.bound } in
      let cj = term_of loc (ev g sub_j (Option.get cond)) in
      assume ctx (eq (select prefix zero) zero);
      assume ctx
        (quant "forall" [ j ]
           (implies (and_ [ le zero j; lt j seq.len ])
              (eq (select prefix (add j one)) (add (select prefix j) (ite cj one zero))))
           [ [| select prefix (add j one) |] ]);
      filtered_state := Some (prefix, j, sub_j, cj);
      select prefix seq.len
    | Some _ ->
      let ln = sym (Printf.sprintf "comp@%d.len" n) Int in
      assume ctx (and_ [ le zero ln; le ln seq.len ]);
      ln
  in
  let i = const (Printf.sprintf "%s!%d" elem n) Int in
  let rng = and_ [ le zero i; lt i seq.len ] in
  let sub = sub_ctx ~cond:rng { ctx with spec = true } in
  let sub = { sub with bound = SM.add elem (T (at (seq.arr, seq.off) i)) sub.bound } in
  let result = L (list_value arr zero ln (const (Printf.sprintf "comp@%d.ref" n) Int) e.ty) in
  let comp_arr = ref arr in
  if under then raise (Fallback "comprehension allocation depends on quantified variables");
  if not is_pure then begin
    (* values unknown; obligations and effects as for any element *)
    each_element g ctx e seq;
    (match result with L l -> allocate_list_value g ctx loc l | _ -> assert false)
  end
  else begin
    (match cond with
     | None ->
       let b = term_of loc (ev g sub body) in
       let arr = same_comp g arr b seq i ctx in
       assume ctx (quant "forall" [ i ] (implies rng (eq (select arr i) b)) [ [| select arr i |] ]);
       Hashtbl.replace g.comp_bodies arr.id (elem ^ Ir.shape body, if under then ctx.binders else []);
       comp_arr := arr
     | Some c ->
       let cv = term_of loc (ev g sub c) in
       ignore (ev g (sub_ctx ~cond:cv sub) body);
       (match !filtered_state with
        | Some (prefix, j, sub_j, cj) ->
          let bj = term_of loc (ev g sub_j body) in
          let rank = select prefix j in
          assume ctx
            (quant "forall" [ j ]
               (implies (and_ [ le zero j; lt j seq.len; cj ]) (eq (select arr rank) bj))
               [ [| select arr rank |] ])
        | None -> raise (Fallback "filtered comprehension rank")));
    allocate_list_value g ctx loc (list_value !comp_arr zero ln (const (Printf.sprintf "comp@%d.ref" (next g)) Int) e.ty)
  end

(* how a checked value [v] of type [ty] looks through the operations telic
   leaves uninterpreted on its unchecked view [b] (the same object): length,
   indexing, isinstance; unless [known], only where [b] is an instance of that
   type (lists and scalars; the Python core also relates dicts) *)
and box_facts g ctx b v (ty : Ir.ty) known =
  let n = next g in
  let scalar = function Ir.TInt -> Some "int" | TStr -> Some "str" | TBool -> Some "bool" | _ -> None in
  let kind, facts =
    match (v, ty) with
    | L l, TList et when et = TOpaque || scalar et <> None ->
      let i = const (Printf.sprintf "i!%d" n) Int in
      let get = fn "opaque.getitem.Opaque" [| b; i |] Opaque in
      let rng = and_ [ le zero i; lt i l.len ] in
      let elem =
        match scalar et with
        | None -> quant "forall" [ i ] (implies rng (eq get (at (l.arr, l.off) i))) [ [| get |] ]
        | Some k -> quant "forall" [ i ] (implies rng (implies (fn "opaque.isinstance.Bool" [| get; str k |] Bool) (eq (fn (Printf.sprintf "unbox.%s." k) [| get |] (sort_of et)) (at (l.arr, l.off) i)))) [ [| get |]; [| at (l.arr, l.off) i |] ]
      in
      (Some "list", [ eq (fn "opaque.len.Int" [| b |] Int) l.len; elem ])
    | _, t -> (scalar t, [])
  in
  match kind with
  | None -> ()
  | Some k ->
    let is_kind = fn "opaque.isinstance.Bool" [| b; str k |] Bool in
    let fact = if known then and_ (is_kind :: facts) else if facts = [] then tt else implies is_kind (and_ facts) in
    if fact != tt then assume ctx fact

(* int(s)/float(s) (Python), parseInt(s)/parseFloat(s) (JavaScript) on a
   string: exact on plain decimal digits, otherwise a number telic does not
   compute. Python raises ValueError on text outside its grammar (checked like
   a raise statement); JavaScript gives NaN, which telic's numbers do not
   include (a listed assumption). *)
and parse_number g ctx (e : Ir.expr) name s =
  let loc = e.loc in
  let py = String.sub name 0 3 = "py_" in
  let real = name <> "py_int_parse" in
  let tail = app "str.substr" [| s; one; Term.sub (app "str.len" [| s |] Int) one |] Str in
  let other = fn name [| s |] (if real then Real else Int) in
  let exact = ite (in_re s "digits") (str_to_int s) (ite (in_re s "neg_digits") (neg (str_to_int tail)) (str_to_int tail)) in
  let known = or_ [ in_re s "digits"; in_re s "neg_digits"; in_re s "pos_digits" ] in
  (* (z3 does not find these itself: digits spell a number >= 0) *)
  assume ctx (implies (in_re s "digits") (le zero (str_to_int s)));
  assume ctx (implies (or_ [ in_re s "neg_digits"; in_re s "pos_digits" ]) (le zero (str_to_int tail)));
  let v = ite known (if real then to_real exact else exact) other in
  let what = match name with "py_int_parse" -> "int()" | "py_float_parse" -> "float()" | "js_parse_int" -> "parseInt" | _ -> "parseFloat" in
  if py then begin
    let ok = in_re s (if name = "py_int_parse" then "py_int" else "py_float") in
    let caught = match List.rev (match e.e with Builtin (_, a) -> a | _ -> []) with { e = Lit (LBool true); _ } :: _ -> true | _ -> false in
    (if (not caught) && (not ctx.spec) && ctx.state <> None then
       let arg = expr_name (match e.e with Builtin (_, a :: _) -> a | _ -> e) in
       if g.info.fn.raises <> [] then begin
         let ectx = { ctx with env = g.entry; live = None; spec = true; quiet = true } in
         let cond = or_ (List.map (fun (r : Ir.clause) -> term_of loc (ev g ectx r.cexpr)) g.info.fn.raises) in
         oblige g "raise" ctx (or_ [ ok; cond ]) loc (Printf.sprintf "%s of text it cannot parse raises ValueError outside '@raises %s'" what (List.hd g.info.fn.raises).text)
       end
       else if g.info.fn.requires <> [] || g.info.fn.ensures <> [] then
         oblige g "raise" ctx ok loc (Printf.sprintf "%s can parse '%s' (else it raises ValueError)" what arg));
    if name = "py_float_parse" then note_assumed g loc "float() of 'nan', 'inf' or an overflowing exponent is not a number telic models"
  end
  else begin
    assume ctx (implies (in_re s "js_nonneg_prefix") (le (Term.real (Q.of_int 0)) other));
    if name = "js_parse_int" then assume ctx (implies (in_re s "js_num_prefix") (is_int other));
    note_assumed g loc (Printf.sprintf "%s of text without a leading number is NaN, which telic models as an unknown number" what)
  end;
  T v

(* relate a sum over a comprehension to the earlier sums over ones with the
   same body: equal on their common prefix wherever the elements are
   (seqsum_ext, skolemized), and each the sum of that prefix and the rest
   (seqsum_split) *)
and comp_sum g ctx (l : lv) total =
  match (Hashtbl.find_opt g.comp_bodies l.arr.id, total.node) with
  | Some (key, binders), Fn (fd, _) when l.off == zero ->
    let earlier = Hashtbl.find_all g.comp_sums key in
    List.iter
      (fun (arr2, len2, total2, binders2) ->
        if List.map (fun (b : term) -> b.sort) binders2 = List.map (fun (b : term) -> b.sort) binders && l.len != zero && len2 != zero then begin
          let vs = List.map (fun (b : term) -> const (Printf.sprintf "%s!%d" (match String.index_opt (match b.node with Const n -> n | _ -> "v") '!' with Some k -> String.sub (match b.node with Const n -> n | _ -> "v") 0 k | None -> "v") (next g)) b.sort) binders in
          let s1 = subst (List.combine binders vs) and s2 = subst (List.combine binders2 vs) in
          let a1 = s1 l.arr and n1 = s1 l.len and t1 = s1 total and a2 = s2 arr2 and n2 = s2 len2 and t2 = s2 total2 in
          let sum a lo hi = fn fd [| a; lo; hi |] total.sort in
          let k = shorter n1 n2 in
          let d = fn (Printf.sprintf "diff!%d" (next g)) (Array.of_list vs) Int in
          let parts =
            or_ [ and_ [ le zero d; lt d k; ne (select a1 d) (select a2 d) ]; eq (sum a1 zero k) (sum a2 zero k) ]
            :: List.filter_map (fun (a, n, t) -> if n == k then None else Some (eq t (add (sum a zero k) (tail sum a k n)))) [ (a1, n1, t1); (a2, n2, t2) ]
          in
          let fact = implies (and_ [ le zero n1; le zero n2 ]) (and_ parts) in
          let fact = if vs = [] then fact else quant "forall" vs fact [ [| t1; t2 |] ] in
          Dynarray.add_last ctx.base fact
        end)
      earlier;
    Hashtbl.add g.comp_sums key (l.arr, l.len, total, binders)
  | _ -> ()

(* the array of an earlier comprehension computing the same elements from the
   same list ([b] is element [i]), else [arr]: then sums over both are one
   term. Both definitions agree wherever both apply. *)
and same_comp g arr b (seq : lv) i ctx =
  let x = const "@elem" (at (seq.arr, seq.off) i).sort in
  let m = (at (seq.arr, seq.off) i, x) :: List.mapi (fun k v -> (v, const (Printf.sprintf "@%d" k) v.sort)) ctx.binders in
  let shape = subst m b in
  if List.memq i (consts shape) then arr
  else begin
    let key = Printf.sprintf "%d/%d/%d/%d/%d/%b" shape.id seq.arr.id seq.off.id seq.len.id (List.length ctx.binders) (match arr.node with Fn _ -> true | _ -> false) in
    match Hashtbl.find_opt g.comp_memo key with
    | None -> Hashtbl.replace g.comp_memo key arr; arr
    | Some old -> ( match old.node with Fn (name, _) -> fn name (Array.of_list ctx.binders) arr.sort | _ -> old)
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

(* unchecked code may change any object; with [keep_created], not those this
   call created (it hands none out, so none it created can be reached) *)
and havoc_heap ?(keep_created = false) g ctx =
  match ctx.state with
  | None -> ()
  | Some st ->
    let alloc0 = alloc_of g.entry and alloc = alloc_of st.env in
    SM.iter
      (fun key v ->
        match v with
        | T old when is_heap key && key <> "@alloc" ->
          let nw = const (Printf.sprintf "%s@%d" (String.sub key 1 (String.length key - 1)) (next g)) old.sort in
          st.env <- SM.add key (T nw) st.env;
          (* (whether or not the code runs: unguarded) *)
          (match old.sort with
           | Array (Int, _) when keep_created && alloc != alloc0 -> Dynarray.add_last ctx.base (created_kept alloc0 alloc old nw (const (Printf.sprintf "r!%d" (next g)) Int))
           | _ -> ())
        | _ -> ())
      st.env;
    let na = const (Printf.sprintf "alloc@%d" (next g)) (Array (Int, Bool)) in
    let r = const (Printf.sprintf "r!%d" (next g)) Int in
    (* (allocation only grows, whether or not the code runs: unguarded) *)
    Dynarray.add_last ctx.base (monotone_alloc alloc na r);
    st.env <- SM.add "@alloc" (T na) st.env

and extern g ctx (e : Ir.expr) name args =
  let loc = e.loc in
  let vals = List.map (ev g ctx) args in
  if ctx.spec then raise (Vc_error (Printf.sprintf "specifications cannot call unchecked code ('%s')" name, loc));
  (* '@wrapper f' runs checked f with these arguments (a generator, a library decorator) *)
  (match if starts_with "@" name then resolve g ctx.modpath name else None with
   | Some callee when same_scc g g.info.key callee.key && g.info.termination ->
     recursion_check g callee (List.fold_left (fun m ((p, _), a) -> SM.add p a m) SM.empty (zip callee.fn.params vals)) ctx loc
   | _ -> ());
  if not (starts_with "caught exception" name || starts_with "default of" name) then note_assumed g loc ("call:" ^ name);
  (match ctx.state with
   | Some st when name = "yield" ->
     check_objects g ~guard:ctx.guard st.facts st.env loc "at the yield";
     suspend g ctx loc
   | _ -> ());
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
     if extern_touches_heap g args || (g.prog.classes <> [] && fn.escaped <> []) then begin
       havoc_heap ~keep_created:((not (Hashtbl.mem g.prog.hands_out g.info.key)) && fn.escaped = []) g ctx;
       if List.exists (fun c -> c.cinvs <> []) g.prog.classes then note_assumed g loc "unchecked code leaves objects satisfying their class invariants";
       if List.exists (fun c -> c.clcs <> []) g.prog.classes then note_assumed g loc "unchecked code changes objects only as their lifecycles allow"
     end
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
  g.created <- r :: g.created;
  assume ctx (not_ (select alloc r));
  st.env <- SM.add "@alloc" (T (store alloc r tt)) st.env;
  allocate_heap_cell g ctx r (Heap.class_cell (class_tag g cls)) loc;
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
    List.iter (fun ((f, _), v) -> st.env <- heap_write g ctx st.env cls f r v) (zip c.cfields vals);
    match c.post_init with
    | Some k ->
      ignore (call g ~new_self:true (finfo_of g k) [ T r ] [ None ] ctx loc);
      T r
    | None ->
      check_invariants ();
      T r)

and call g ?(new_self = false) (callee : finfo) (args : value list) (arg_exprs : Ir.expr option list) ctx loc : value =
  let fn = callee.fn in
  (* a comprehension's element is no variable of the state, whatever it shadows *)
  let arg_exprs = List.map (function Some { Ir.e = Var n; _ } when SM.mem n ctx.bound -> None | a -> a) arg_exprs in
  (* a list/dict argument is a reference: a later argument's mutation shows *)
  let args =
    match ctx.state with
    | Some st -> List.map (fun (a_e, a) -> match (a_e, a) with Some { Ir.e = Var n; _ }, (L _ | D _) -> (match SM.find_opt n st.env with Some v -> v | None -> a) | _ -> a) (zip arg_exprs args)
    | None -> args
  in
  let args = if g.info.language = "swift" && not ctx.spec then List.map (copy_value g ctx loc) args else args in
  let muts = callee.mutated in
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
  let cctx = { ctx with env = with_pmap heap_pre; modpath = callee.modpath; live = None; bound = SM.empty; old_env = None; result = None; spec = true; quiet = true; state = None; binders = [] } in
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
  (match ctx.state with
   | Some st when (not ctx.spec) && (not new_self) && List.exists (fun (_, pty) -> Ir.reaches_object pty) fn.params ->
     check_objects g ~guard:ctx.guard st.facts st.env loc (Printf.sprintf "when calling '%s'" fn.name)
   | _ -> ());
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
  (match ctx.state with Some st when not ctx.spec -> post := SM.union (fun _ _ b -> Some b) !post (call_effects g callee args arg_exprs ctx st loc) | _ -> ());
  if (not ctx.spec) && fn.ensures <> [] && not g.definitional_mode then begin
    let ectx = { cctx with env = !post; old_env = Some (with_pmap heap_pre); result = (match r with NoneV -> None | r -> Some r) } in
    List.iter (fun (en : Ir.clause) -> assume ctx (term_of loc (ev g ectx en.cexpr))) fn.ensures
  end;
  r

(* what a call leaves in the caller's state whether it returns or raises:
   mutated list arguments get fresh contents, the fields it may write change,
   and the objects it was passed satisfy their invariants (an object under
   construction only if it returns); the changed arguments and the heap *)
and call_effects g ?(new_self = false) ?(returned = true) (callee : finfo) args arg_exprs ctx (st : state) loc =
  let fn = callee.fn in
  let muts = callee.mutated in
  let post = ref SM.empty in
  let heap_pre = heap_env st.env in
  havoc_call g callee args ctx;
  List.iter
    (fun ((p, pty), a_e) ->
      match a_e with
      | Some { Ir.e = Var n; _ } when List.mem p muts -> (
        match SM.find_opt n st.env with
        | Some (D _) ->
          post := SM.add p (SM.find n st.env) !post
        | Some (L old) ->
          let _ = old in
          post := SM.add p (SM.find n st.env) !post
        | _ -> raise (Vc_error ("mutated argument is not a list", loc)))
      | _ -> ())
    (zip fn.params arg_exprs);
  List.iteri
    (fun i ((_, pty), a) ->
      match (pty, a) with
      | Ir.TClass c, T r when returned || not (new_self && i = 0) -> List.iter (fun (_, t) -> assume ctx t) (class_invariants g c r st.env ctx.base)
      | _ -> ())
    (zip fn.params args);
  (* ... changed only as their lifecycles allow *)
  List.iteri
    (fun i ((_, pty), a) ->
      match (pty, a) with
      | Ir.TClass c, T r when not (i = 0 && (ends_with ".__init__" fn.name || ends_with ".__post_init__" fn.name)) -> List.iter (fun (_, t) -> assume ctx t) (class_lifecycles g c r heap_pre st.env ctx.base)
      | _ -> ())
    (zip fn.params args);
  SM.union (fun _ _ b -> Some b) !post (heap_env st.env)

(* the state a call leaves when it raises: its contract describes normal
   returns only, so only what it may change, and the invariants of the
   objects it was passed, are known *)
and threw g ctx (e : Ir.expr) =
  match (e.e, ctx.state) with
  | Call (f, args), Some st when not ctx.spec ->
    let callee = match resolve g ctx.modpath f with Some c -> c | None -> raise (Vc_error (Printf.sprintf "unknown function '%s'" f, e.loc)) in
    let vals = List.map (fun (a, (_, pty)) -> coerce (ev g ctx a) (Some pty)) (zip args callee.fn.params) in
    if not (List.mem callee.key g.deps) then g.deps <- g.deps @ [ callee.key ];
    let ends s suffix = String.length s >= String.length suffix && String.sub s (String.length s - String.length suffix) (String.length suffix) = suffix in
    ignore (call_effects g ~new_self:(ends callee.fn.name ".__init__") ~returned:false callee vals (List.map Option.some args) ctx st e.loc);
    NoneV
  | Call _, _ -> NoneV
  | _ -> raise (Vc_error ("'threw' takes a call", e.loc))

(* the heap after a call: only the fields the callee may write change, and
   only on the objects it may write them on *)
and havoc_call g (callee : finfo) args ctx =
  match ctx.state with
  | None -> ()
  | Some st ->
    let alloc_pre = alloc_of st.env in
    let names = List.map fst callee.fn.params in
    let writes = try Hashtbl.find g.prog.heap_writes callee.key with Not_found -> [] in
    let heap = match current_heap ctx with Some h -> h | None -> raise (Fallback "call effects require the shared heap") in
    List.iter
      (fun (cls_field, targets) ->
        let k = String.index cls_field '.' in
        let c = String.sub cls_field 0 k and f = String.sub cls_field (k + 1) (String.length cls_field - k - 1) in
        let refs =
          List.filter_map
            (fun t ->
              match List.find_index (( = ) t) names with
              | Some i -> ( match List.nth_opt args i with Some (T x) -> Some x | Some _ -> raise (Fallback "write through a non-class object") | None -> None)
              | None -> None)
            targets
        in
        let slot = field_slot g c f in
        let ty = field_type g c f in
        if List.mem "*" targets then begin
          let next_heap = const (Printf.sprintf "heap.call.%d" (next g)) Heap.heap in
          let r = const (Printf.sprintf "heap.call.ref.%d" (next g)) Int in
          let ccell = Heap.cell_at heap r in
          let values = const (Printf.sprintf "heap.call.field.%d" (next g)) (Array (Int, Heap.value)) in
          let applicable =
            List.filter_map (fun actual ->
              if List.mem c (mro g actual) then Some (eq (field ccell "class") (class_tag g actual)) else None)
              (List.map (fun cls -> cls.cname) g.prog.classes)
          in
          let changed = store (field ccell "fields") slot (select values r) in
          let replacement = Heap.replace_record ccell [ ("fields", changed) ] in
          let structural = if g.info.language = "typescript" then eq (field ccell "kind") (int_ 3) else ff in
          let allowed = and_ [ field ccell "allocated"; or_ [ and_ [ eq (field ccell "kind") (int_ 4); or_ applicable ]; structural ] ] in
          assume ctx (quant "forall" [ r ] (implies allowed (accepts_view g heap ty (select values r))) [ [| select values r |] ]);
          assume ctx (quant "forall" [ r ]
            (eq (select next_heap r) (ite allowed replacement ccell)) [ [| select next_heap r |] ]);
          st.env <- SM.add "@heap" (T next_heap) st.env
        end else
          List.iter (fun r ->
            let value = const (Printf.sprintf "heap.call.field.%d" (next g)) Heap.value in
            let current = match current_heap ctx with Some h -> h | None -> assert false in
            assume ctx (accepts_view g current ty value);
            st.env <- SM.add "@heap" (T (Heap.write_field current r slot value)) st.env)
            refs)
      writes;
    List.iteri (fun i (p, ty) ->
      if List.mem p callee.mutated then
        match List.nth_opt args i with
        | Some (L l) ->
          let current = match current_heap ctx with Some h -> h | None -> assert false in
          let cell = Heap.cell_at current l.ref in
          let seq = const (Printf.sprintf "heap.call.list.%d.seq" (next g)) (Array (Int, Heap.value)) in
          let old_len = Heap.read_len current l.ref in
          let fresh_len = const (Printf.sprintf "heap.call.list.%d.len" (next g)) Int in
          if List.mem p callee.appends then assume ctx (implies (not_ l.view) (le old_len fresh_len));
          assume ctx (implies (not_ l.view) (le zero fresh_len));
          let cell_len = ite l.view old_len fresh_len in
          let i = const (Printf.sprintf "heap.call.list.%d.index" (next g)) Int in
          let elem = match ty with TList elem -> elem | _ -> TNone in
          let touched = ite l.view (and_ [ le l.off i; lt i (add l.off l.len) ]) (and_ [ le zero i; lt i fresh_len ]) in
          assume ctx (quant "forall" [ i ] (implies touched (accepts_view g current elem (select seq i))) [ [| select seq i |] ]);
          let outside_view = or_ [ lt i l.off; le (add l.off l.len) i ] in
          assume ctx (quant "forall" [ i ]
            (implies (and_ [ l.view; le zero i; lt i old_len; outside_view ]) (eq (select seq i) (Heap.read_list current l.ref i)))
            [ [| select seq i |] ]);
          let changes = [ ("seq", seq); ("len", cell_len) ] in
          let next_heap = store current l.ref (Heap.replace_record cell changes) in
          st.env <- SM.add "@heap" (T next_heap) st.env;
          if List.mem p callee.appends then assume ctx (le zero cell_len)
        | Some (D d) ->
          let current = match current_heap ctx with Some h -> h | None -> assert false in
          let cell = Heap.cell_at current d.ref in
          let suffix = string_of_int (next g) in
          let count = const ("heap.call.dict." ^ suffix ^ ".key_count") Int in
          let len = const ("heap.call.dict." ^ suffix ^ ".len") Int in
          let live = const ("heap.call.dict." ^ suffix ^ ".key_live") (Array (Int, Bool)) in
          let keys = const ("heap.call.dict." ^ suffix ^ ".keys") (Array (Int, Heap.key)) in
          let positions = const ("heap.call.dict." ^ suffix ^ ".key_position") (Array (Heap.key, Int)) in
          let has = const ("heap.call.dict." ^ suffix ^ ".has") (Array (Heap.key, Bool)) in
          let map = const ("heap.call.dict." ^ suffix ^ ".map") (Array (Heap.key, Heap.value)) in
          let history = const ("heap.call.dict." ^ suffix ^ ".original_keys") (Array (Int, Heap.value)) in
          let j = const ("heap.call.dict." ^ suffix ^ ".slot") Int in
          let key = select keys j in
          assume ctx (and_ [ le zero len; le len count; le zero count;
            eq len (fn "seqcount_bool" [| live; zero; count; tt |] Int);
            quant "forall" [ j ] (implies (and_ [ le zero j; lt j count; select live j ])
              (and_ [ select has (select keys j); eq (select positions (select keys j)) j ])) [ [| select live j |] ];
            quant "forall" [ j ] (implies (and_ [ le zero j; lt j count ])
              (accepts_view g current (match ty with TDict (key_ty, _) -> key_ty | _ -> TNone) (select history j))) [ [| select history j |] ];
            quant "forall" [ j ] (implies (and_ [ le zero j; lt j count; select live j ])
              (let raw = Heap.unbox (select history j) (match ty with TDict (key_ty, _) -> key_ty | _ -> TNone) in
               let canonical, admissible = Heap.canonical_key raw (match ty with TDict (key_ty, _) -> key_ty | _ -> TNone) g.info.language in
               and_ [ admissible; eq canonical (select keys j) ])) [ [| select keys j |] ] ]);
          let typed_key = const ("heap.call.dict." ^ suffix ^ ".typed_key") Heap.key in
          let value_ty = match ty with TDict (_, value_ty) -> value_ty | _ -> TNone in
          assume ctx (quant "forall" [ typed_key ]
            (implies (select has typed_key) (accepts_view g current value_ty (select map typed_key))) [ [| select map typed_key |] ]);
          assume ctx (quant "forall" [ typed_key ]
            (implies (select has typed_key)
              (and_ [ le zero (select positions typed_key); lt (select positions typed_key) count;
                select live (select positions typed_key);
                eq (select keys (select positions typed_key)) typed_key ])) [ [| select has typed_key |] ]);
          let changes = [ ("map", map); ("has", has); ("keys", keys); ("key_live", live);
            ("key_position", positions); ("seq", history); ("key_count", count); ("len", len) ] in
          st.env <- SM.add "@heap" (T (store current d.ref (Heap.replace_record cell changes))) st.env
        | _ -> ()) callee.fn.params;
    (match current_heap ctx with Some h -> set_current_heap g ctx h | None -> ());
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
    let mctx = { ctx with env = g.entry; modpath = g.info.modpath; live = None; bound = SM.empty; spec = true; quiet = true; state = None; binders = [] } in
    (* a list literal is a lexicographic measure, compared left to right *)
    let parts (m : Ir.expr) = match m.e with ListLit xs -> xs | _ -> [ m ] in
    let m0 = List.map (fun e -> term_of loc (ev g mctx e)) (parts me) in
    let cctx = { ctx with env = pmap; modpath = callee.modpath; live = None; bound = SM.empty; spec = true; quiet = true; state = None; binders = [] } in
    let m1 = List.map (fun e -> term_of loc (ev g cctx e)) (parts them) in
    if List.length m0 <> List.length m1 then
      raise (Vc_error (Printf.sprintf "'%s' and '%s' recurse into each other but their '@decreases' have different lengths" g.info.fn.name callee.fn.name, loc));
    let rec lex a b = match (a, b) with [ x ], [ y ] -> lt x y | x :: a', y :: b' -> or_ [ lt x y; and_ [ eq x y; lex a' b' ] ] | _ -> ff in
    let inferred = g.info.fn.decreases = None in
    oblige g ~inferred "variant" ctx (and_ (List.map (le zero) m0)) loc "recursion measure is non-negative";
    oblige g ~inferred "variant" ctx (lex m1 m0) loc (Printf.sprintf "recursive call to '%s' decreases the measure" callee.fn.name)
  | _ -> oblige g "variant" ctx ff loc (Printf.sprintf "recursive call to '%s' terminates (add '@decreases <measure>')" callee.fn.name)

(* -- statements ----------------------------------------------------------- *)

(* every object of cls this function wrote a field of, other than the
   parameters (checked on their own), satisfies each invariant *)
and written_claims g cls env base =
  let w = match SM.find_opt (written_key cls) env with Some (T w) -> w | _ -> raise (Vc_error ("no written set for " ^ cls, Ir.noloc)) in
  let r = const (Printf.sprintf "r!%d" (next g)) Int in
  let held = and_ (select w r :: List.map (fun p -> not_ (eq r p)) (checked_params g cls)) in
  (* a trigger only where the set is a havocked constant: in a goal it is not needed *)
  let pats = match w.node with Const _ -> [ [| select w r |] ] | _ -> [] in
  List.map (fun (inv, t) -> (inv, quant "forall" [ r ] (implies held t) pats)) (class_invariants g cls r env base)

(* the objects this function was passed, and every other object it wrote a
   field of, satisfy their invariants when control leaves it: on return, on
   raise, and while it is suspended (other tasks, or a generator's consumer,
   run then) *)
(* objects that existed at entry changed only as their lifecycles allow when control
   leaves: the parameters, and every object of a class written here (quantified: a
   write's path condition inside a loop says nothing about the state after it) *)
and check_lifecycles g ?(guard = []) facts env (site : Ir.loc) =
  let pre = SM.fold (fun k v m -> if is_segment k then SM.add (String.sub k 8 (String.length k - 8)) v m else m) env g.entry in
  let alloc0 = alloc_of pre in
  let lctx = spec_ctx g ~quiet:false ~guard ~base:facts ~env () in
  List.iter
    (fun (p, (ty : Ir.ty)) ->
      match (ty, SM.find_opt p g.entry) with
      | TClass c, Some (T r) when not (fresh_self g && p = "self") ->
        List.iter
          (fun ((cl : Ir.clause), t) ->
            oblige g ~site ~clause:cl "lifecycle" lctx t cl.cloc (Printf.sprintf "'%s' changes only as the lifecycle of %s allows ('%s')" p c cl.text))
          (class_lifecycles g c r pre env facts)
      | _ -> ())
    g.info.fn.params;
  List.iter
    (fun cls ->
      let r = const (Printf.sprintf "r!%d" (next g)) Int in
      List.iter
        (fun ((cl : Ir.clause), t) ->
          oblige g ~site ~clause:cl "lifecycle" lctx (forall [ r ] (implies (select alloc0 r) t)) cl.cloc
            (Printf.sprintf "every %s written here changes only as its lifecycle allows ('%s')" cls cl.text))
        (class_lifecycles g cls r pre env facts))
    (List.rev g.lc_written)

(* a new stretch without suspension begins in this heap *)
and resume (st : state) = SM.iter (fun k v -> if is_heap k then st.env <- SM.add (segment ^ k) v st.env) st.env

(* other code runs while this function is suspended (other tasks, or a
   generator's consumer): the stretch so far keeps the lifecycles, the heap
   changes, and the next stretch starts from what it finds *)
and suspend g ctx loc =
  match ctx.state with
  | None -> ()
  | Some st ->
    check_lifecycles g ~guard:ctx.guard st.facts st.env loc;
    await_havoc g ctx loc;
    resume st

and check_objects g ?(guard = []) facts env (site : Ir.loc) when_ =
  let ctx = spec_ctx g ~quiet:false ~guard ~base:facts ~env () in
  let calling = String.length when_ >= 12 && String.sub when_ 0 12 = "when calling" in
  List.iter
    (fun (p, (ty : Ir.ty)) ->
      match (ty, SM.find_opt p g.entry) with
      | TClass _, _ when calling && is_init g && p = "self" && not (self_escapes g) -> () (* the object being built: nothing else can reach it yet *)
      | TClass c, Some (T r) ->
        List.iter
          (fun ((inv : Ir.clause), t) -> oblige g ~site ~clause:inv "class.inv" ctx t inv.cloc (Printf.sprintf "invariant of %s ('%s') holds for '%s' %s" c inv.text p when_))
          (class_invariants g c r env facts)
      | _ -> ())
    g.info.fn.params;
  List.iter
    (fun c ->
      let cls = c.cname in
      match SM.find_opt (written_key cls) env with
      | Some (T w) when w != no_writes ->
        (* (not written on the paths that reach here otherwise) *)
        let lines = List.sort_uniq compare (List.filter_map (fun (c', l) -> if c' = cls then Some l else None) g.written) in
        let what = if lines = [] then "every object written so far" else "every object written at line " ^ String.concat ", " (List.map string_of_int lines) in
        List.iter
          (fun ((inv : Ir.clause), t) -> oblige g ~site ~clause:inv "class.inv" ctx t inv.cloc (Printf.sprintf "invariant of %s ('%s') holds %s for %s" cls inv.text when_ what))
          (written_claims g cls env facts)
      | _ -> ())
    g.prog.classes

(* an object read out of a list or dict satisfies its class invariants unless
   this function was passed it or wrote it: every other object was checked
   when last written, and callers check theirs at calls *)
and assume_held g ctx (v : value) (ty : Ir.ty) =
  match (ctx.state, ty, v) with
  | Some st, TClass cls, T r when (not ctx.spec) && has_invariants g cls -> (
    match List.map snd (class_invariants ~skip:(held_skip g cls) g cls r st.env ctx.base) with
    | [] -> ()
    | ts ->
      let exempt =
        List.filter_map (fun (k, w) -> match w with T w when is_written_key k && w != no_writes -> Some (select w r) | _ -> None) (SM.bindings st.env)
        @ List.filter_map (fun (p, (pty : Ir.ty)) -> match (pty, SM.find_opt p g.entry) with TClass _, Some (T x) -> Some (eq r x) | _ -> None) g.info.fn.params
      in
      assume ctx (if exempt = [] then and_ ts else implies (not_ (or_ exempt)) (and_ ts)))
  | _ -> ()

let state_ctx g ?(spec = false) (st : state) =
  { base = st.facts; modpath = g.info.modpath; env = st.env; live = Some st; guard = []; bound = SM.empty; old_env = None; result = None; spec; quiet = false; state = Some st; binders = [] }

let rec block g stmts (st : state) : state = List.fold_left (fun st s -> if st.alive then stmt g s st else st) st stmts

and stmt g (s : Ir.stmt) (st : state) : state =
  match s with
  | Assign (loc, name, v) ->
    let ctx = state_ctx g st in
    let x = coerce (ev g ctx v) (Hashtbl.find_opt g.info.fn.locals name) in
    let x = if g.info.language = "swift" then copy_value g ctx loc x else x in
    st.env <- SM.add name x st.env;
    st
  | FieldAssign (loc, obj, cls, f, v) ->
    let ctx = state_ctx g st in
    let r = term_of loc (ev g ctx obj) in
    let x = coerce (ev g ctx v) (Some (field_type g cls f)) in
    st.env <- heap_write g ctx st.env cls f r x;
    let params = List.filter_map (fun (p, (ty : Ir.ty)) -> match (ty, SM.find_opt p g.entry) with Ir.TClass _, Some (T pr) -> Some pr | _ -> None) g.info.fn.params in
    if not (List.memq r params || List.memq r g.created || List.mem cls g.lc_written) then g.lc_written <- cls :: g.lc_written;
    if has_invariants g cls && not (List.memq r (checked_params g cls)) then begin
      let key = written_key cls in
      (match SM.find_opt key st.env with Some (T w) -> st.env <- SM.add key (T (store w r tt)) st.env | _ -> ());
      g.written <- (cls, loc.line) :: g.written
    end;
    st
  | DictDel (loc, name, k, strict) -> (
    match SM.find_opt name st.env with
    | Some (D d) ->
      let ctx = state_ctx g st in
      let raw = term_of loc (ev g ctx k) in
      let key_ty = match d.dty with TDict (kt, _) -> kt | _ -> TNone in
      let key, valid = Heap.canonical_key raw key_ty g.info.language in
      oblige g "key" ctx valid loc "dictionary key uses supported source equality";
      assume ctx valid;
      (match current_heap ctx with
       | Some h ->
         check_heap_kind g ctx d.ref 2 loc "dictionary deletion refers to an allocated dictionary";
         if strict then oblige g "key" ctx (Heap.has_dict h d.ref key) loc (Printf.sprintf "key being deleted from '%s' is present" name);
         set_current_heap g ctx (Heap.delete_dict h d.ref key)
       | None ->
         if strict then oblige g "key" ctx (select d.has raw) loc (Printf.sprintf "key being deleted from '%s' is present" name));
      (match current_heap ctx with
       | Some _ -> ()
       | None -> st.env <- SM.add name (D { d with has = store d.has raw ff }) st.env);
      st
    | _ -> raise (Vc_error ("del on a non-dict", loc)))
  | IndexAssign (loc, name, i, v, wrap) -> (
    match SM.find_opt name st.env with
    | Some (D d) ->
      let ctx = state_ctx g st in
      let raw_key = term_of loc (ev g ctx i) in
      let kt, vt = match d.dty with TDict (kt, vt) -> (kt, vt) | _ -> assert false in
      let key, valid = Heap.canonical_key raw_key kt g.info.language in
      oblige g "key" ctx valid loc "dictionary key uses supported source equality";
      assume ctx valid;
      let value = coerce (ev g ctx v) (Some vt) in
      let x = term_of loc value in
      let boxed_value = box_stored_value g ctx loc vt value in
      (match current_heap ctx with
       | Some h ->
         check_heap_kind g ctx d.ref 2 loc "dictionary assignment refers to an allocated dictionary";
         set_current_heap g ctx (Heap.write_dict h d.ref key (Heap.box raw_key kt) boxed_value)
       | None -> ());
      (match current_heap ctx with
       | Some _ -> ()
       | None -> st.env <- SM.add name (D { d with vals = store d.vals raw_key x; has = store d.has raw_key tt }) st.env);
      st
    | Some (L l) ->
      let ctx = state_ctx g st in
      let len = list_len ctx l in
      let j = index_of g (l.arr, l.off, len) (term_of loc (ev g ctx i)) wrap ctx loc name in
      let value_ty = match l.lty with TList t -> t | _ -> TNone in
      let value = coerce (ev g ctx v) (Some value_ty) in
      let x = term_of loc value in
      let boxed_value = box_stored_value g ctx loc value_ty value in
      (match current_heap ctx with
       | Some h ->
         check_heap_kind g ctx l.ref 1 loc "list assignment refers to an allocated list";
         set_current_heap g ctx (Heap.write_list h l.ref (add l.off j) boxed_value)
       | None -> ());
      let l = match SM.find_opt name st.env with Some (L l) -> l | _ -> l in
      st.env <- SM.add name (L (numeric_store l (add l.off j) x)) st.env;
      st
    | _ -> raise (Vc_error ("index assignment to a non-list", loc)))
  | Append (loc, name, v) -> (
    match SM.find_opt name st.env with
    | Some (L _) ->
      let l = match SM.find_opt name st.env with Some (L l) -> l | _ -> assert false in
      let ctx = state_ctx g st in
      let value_ty = match l.lty with TList t -> t | _ -> TNone in
      let value = coerce (ev g ctx v) (Some value_ty) in
      let x = term_of loc value in
      let len = list_len ctx l in
      let boxed_value = box_stored_value g ctx loc value_ty value in
      (match current_heap ctx with
       | Some h ->
         check_heap_kind g ctx l.ref 1 loc "append refers to an allocated list";
         set_current_heap g ctx (Heap.append_list h l.ref boxed_value)
       | None -> ());
      st.env <- SM.add name (L { (numeric_store l (add l.off len) x) with len = add len one }) st.env;
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
               (* the body may have broken any object it wrote before raising *)
               List.iter (fun k -> if is_written_key k then hst.env <- SM.add k (T any_writes) hst.env) names;
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
       else if g.info.fn.unit then oblige g "raise" ctx ff loc (Printf.sprintf "raise %s is reachable, and no code telic sees catches it" what)
       (* without a contract, an explicit raise is what the function does, not a failure;
          a unit's caller is code telic does not see *));
      (* (an object whose initializer raises never reaches the caller) *)
      if not (is_init g) then begin
        check_objects g st.facts st.env loc "when it raises";
        check_lifecycles g st.facts st.env loc
      end;
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

(* objects a loop writes keep their invariants from one iteration to the next:
   the loop's exit state is a havocked head, so the conditions under which a
   write happened no longer describe it *)
and check_written g classes (st : state) (site : Ir.loc) ~entry =
  List.iter
    (fun cls ->
      if not (entry && (match SM.find_opt (written_key cls) st.env with Some (T w) -> w == no_writes | _ -> false)) then begin
        let when_ = if entry then "when the loop starts" else "after each iteration" in
        let ctx = spec_ctx g ~quiet:false ~base:st.facts ~env:st.env () in
        List.iter
          (fun ((inv : Ir.clause), t) ->
            oblige g ~site ~clause:inv "class.inv" ctx t inv.cloc (Printf.sprintf "invariant of %s ('%s') holds %s for every object written so far" cls inv.text when_))
          (written_claims g cls st.env st.facts)
      end)
    classes

and assume_written g classes (st : state) =
  List.iter
    (fun cls ->
      List.iter (fun (_, t) -> Dynarray.add_last st.facts t) (written_claims g cls st.env st.facts);
      (* (an object written so far exists: calls and allocations leave it alone unless they may write it) *)
      match SM.find_opt (written_key cls) st.env with
      | Some (T w) ->
        let r = const (Printf.sprintf "r!%d" (next g)) Int in
        Dynarray.add_last st.facts (quant "forall" [ r ] (implies (select w r) (select (alloc_of st.env) r)) [ [| select w r |] ])
      | _ -> ())
    classes

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
  let wrote = written_in g names in
  check_written g wrote st loc ~entry:true;
  cut g names st loc;
  let head = havoc g st names appends in
  cut g names head loc ~at_head:true;
  assume_invs g invs head [];
  assume_written g wrote head;
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
          check_written g wrote it_end loc ~entry:false;
          cut g names it_end loc;
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
  let wrote = written_in g names in
  check_written g wrote entry loc ~entry:true;
  cut g names entry loc;
  if not (Hashtbl.mem g.info.fn.locals counter) then Hashtbl.replace g.info.fn.locals counter TInt;
  let head = havoc g entry names appends in
  cut g names head loc ~at_head:true;
  let k = match SM.find_opt counter head.env with Some (T k) -> k | _ -> assert false in
  Dynarray.add_last head.facts (le lo_v k);
  Dynarray.add_last head.facts (le k (max_ lo_v hi_v));
  assume_invs g invs head [ (idx, T k) ];
  assume_written g wrote head;
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
        check_invs g invs it_end "inv.step" loc [ (idx, T k1) ];
        check_written g wrote it_end loc ~entry:false;
        cut g names it_end loc
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
        bst.env <- SM.add idx (T k) bst.env;
        assume_held g (state_ctx g bst) (T (at (l.arr, l.off) k)) (match seq.ty with TList t -> t | t -> t))
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
        check_objects g facts ex.eenv ex.eloc "on return";
        check_lifecycles g facts ex.eenv ex.eloc;
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
    inputs = []; assumptions = []; loop_notes = []; definitional_mode = false; written = []; created = []; lc_written = []; comp_memo = Hashtbl.create 8; comp_bodies = Hashtbl.create 8; comp_sums = Hashtbl.create 8;
  }

let run g =
  let fn = g.info.fn in
  let st = { env = SM.empty; facts = Dynarray.create (); alive = true } in
  (* the heap: one map per class field component, and the allocation map *)
  List.iter
    (fun c -> List.iter (fun (f, _) -> List.iter (fun (k, srt) -> if not (SM.mem k st.env) then st.env <- SM.add k (T (const (String.sub k 1 (String.length k - 1)) srt)) st.env) (heap_keys g c.cname f)) c.cfields)
    g.prog.classes;
  st.env <- SM.add "@alloc" (T (const "alloc" (Array (Int, Bool)))) st.env;
  st.env <- SM.add "@heap" (T (const "heap.entry" Heap.heap)) st.env;
  List.iter (fun c -> if has_invariants g c.cname then st.env <- SM.add (written_key c.cname) (T no_writes) st.env) g.prog.classes;
  List.iter
    (fun (p, ty) ->
      let v = match param_val p ty with
        | L l when List.mem p fn.view_params -> L { l with view = tt }
        | value -> value
      in
      let v = match v, SM.find_opt "@heap" st.env with
        | value, Some (T h) -> refresh_value g st h value
        | _ -> v
      in
      st.env <- SM.add p v st.env;
      g.inputs <- (p, v) :: g.inputs;
      (match v with
       | L l ->
         let h = match SM.find "@heap" st.env with T h -> h | _ -> assert false in
         let c = Heap.cell_at h l.ref in
         Dynarray.add_last st.facts (and_ [ field c "allocated"; eq (field c "kind") (int_ 1); implies (not_ l.view) (eq l.len (Heap.read_len h l.ref)); le zero l.len ]);
         let i = const (p ^ ".heap_index") Int in
         let boxed = Heap.read_list h l.ref (add l.off i) in
         let item = at (l.arr, l.off) i in
         let elem = match ty with TList elem -> elem | _ -> TNone in
         let projected, compatible = match elem with
           | TRecord (schema, fields) ->
             let ref = Heap.unbox boxed elem in
             let record = Heap.cell_at h ref in
             let record_kind = eq (field record "kind") (int_ 3) in
             let structural = if g.info.language = "typescript" then eq (field record "kind") (int_ 4) else ff in
             (project_record g h schema fields ref,
              and_ [ Heap.accepts boxed elem; field record "allocated"; or_ [ record_kind; structural ] ])
           | _ -> (Heap.unbox boxed elem, Heap.accepts boxed elem)
         in
         Dynarray.add_last st.facts (quant "forall" [ i ]
           (implies (and_ [ le zero i; lt i l.len ]) (and_ [ compatible; eq projected item ]))
           [ [| boxed |] ])
       | D d ->
         let h = match SM.find "@heap" st.env with T h -> h | _ -> assert false in
         let c = Heap.cell_at h d.ref in
         Dynarray.add_last st.facts (and_ [ field c "allocated"; eq (field c "kind") (int_ 2) ])
       | T r when (match ty with TClass _ -> true | _ -> false) ->
         let h = match SM.find "@heap" st.env with T h -> h | _ -> assert false in
         let cls = match ty with TClass c -> c | _ -> assert false in
         let cell = Heap.cell_at h r in
         let compatible = List.filter_map (fun actual -> if List.mem cls (mro g actual) then Some (eq (field cell "class") (class_tag g actual)) else None) (List.map (fun c -> c.cname) g.prog.classes) in
         Dynarray.add_last st.facts (and_ [ field cell "allocated"; eq (field cell "kind") (int_ 4); or_ compatible ])
       | _ -> ());
       (match (ty, v) with
        | TList TReal, L l ->
         let i = const (p ^ ".numeric_index") Int in
         let expected = ite (select l.py_tags i) (as_float_to Float64 (select l.py_ints i)) (select l.py_floats i) in
         Dynarray.add_last st.facts (quant "forall" [ i ] (implies (and_ [ le zero i; lt i l.len ]) (eq (select l.arr i) expected)) [ [| select l.arr i |] ])
        | _ -> ());
       List.iter (Dynarray.add_last st.facts) (valid_container_facts v ty);
       List.iter (Dynarray.add_last st.facts) (alloc_facts g v ty st.env))
    fn.params;
  g.entry <- st.env;
  let suspending = ref false in
  Ir.walk_stmts (fun s -> List.iter (Ir.walk_expr (fun x -> if suspends x then suspending := true)) (Ir.stmt_exprs s)) fn.body;
  if !suspending then resume st;
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
