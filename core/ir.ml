(* The IR, mirroring telic/ir.py, decoded from the shared JSON schema. *)

type ty =
  | TInt
  | TReal
  | TPythonNumber
  | TFloat32
  | TBool
  | TStr
  | TNone
  | TList of ty
  | TRecord of string * (string * ty) list
  | TOption of ty
  | TDict of ty * ty
  | TClass of string
  | TOpaque
  | TEnum of string * string list * Json.t list

type loc = { line : int; col : int; end_col : int }

let noloc = { line = 0; col = 0; end_col = 0 }

type lit = LInt of string | LFrac of string * string | LBool of bool | LStr of string | LNone

type expr = { e : enode; ty : ty; loc : loc }

and enode =
  | Lit of lit
  | Var of string
  | Result
  | Old of expr
  | Unary of string * expr
  | Binary of string * expr * expr
  | Ite of expr * expr * expr
  | Call of string * expr list
  | Builtin of string * expr list
  | Index of expr * expr * bool
  | Field of expr * string
  | Quant of { kind : string; idx : string; lo : expr; hi : expr; body : expr; elem : string option; seq : expr option }
  | ListLit of expr list
  | RecordLit of (string * expr) list
  | New of string * expr list
  | Extern of string * expr list

type clause = { ckind : string; cexpr : expr; cloc : loc; text : string; aims : string list; inferred : bool }

type stmt =
  | Assign of loc * string * expr
  | IndexAssign of loc * string * expr * expr * bool
  | Append of loc * string * expr
  | If of loc * expr * stmt list * stmt list
  | While of { loc : loc; cond : expr; invariants : clause list; decreases : clause option; body : stmt list; step : stmt list }
  | ForRange of { loc : loc; var : string; lo : expr; hi : expr; invariants : clause list; body : stmt list; reeval : bool }
  | ForEach of { loc : loc; elem : string; idx : string; seq : expr; invariants : clause list; body : stmt list; idx_visible : bool }
  | Return of loc * expr option
  | Break of loc
  | Continue of loc
  | AssertStmt of loc * clause * bool
  | AssumeStmt of loc * clause
  | Raise of loc * string * bool
  | ExprStmt of loc * expr
  | Unsupported of loc * string
  | FieldAssign of loc * expr * string * string * expr
  | DictDel of loc * string * expr * bool
  | Try of loc * stmt list * stmt list list * stmt list * stmt list

type func = {
  name : string;
  floc : loc;
  end_line : int;
  params : (string * ty) list;
  ret : ty;
  requires : clause list;
  ensures : clause list;
  decreases : clause option;
  raises : clause list;
  body : stmt list;
  faims : string list;
  unsupported : (string * int) list;
  trusted : bool;
  unit : bool;  (** code handed on as a value whose raise nothing telic sees catches *)
  locals : (string, ty) Hashtbl.t;
  escaped : string list;
}

type classdecl = { cname : string; fields : (string * ty) list; invariants : clause list }

type modul = {
  path : string;
  language : string;
  functions : func list;
  classes : classdecl list;
  imports : (string * (string * string)) list;
}

(* -- decoding --------------------------------------------------------- *)

open Json

(* can a value of this type lead to an object's fields? *)
let rec reaches_object = function
  | TClass _ -> true
  | TList t | TOption t -> reaches_object t
  | TDict (k, v) -> reaches_object k || reaches_object v
  | TRecord (_, fs) -> List.exists (fun (_, t) -> reaches_object t) fs
  | _ -> false

let rec ty_of j =
  match to_str (member "k" j) with
  | "int" -> TInt
  | "real" -> TReal
  | "python_number" -> TPythonNumber
  | "float32" -> TFloat32
  | "bool" -> TBool
  | "str" -> TStr
  | "none" -> TNone
  | "list" -> TList (ty_of (member "elem" j))
  | "record" -> TRecord (to_str (member "name" j), List.map (fun f -> match f with List [ String n; t ] -> (n, ty_of t) | _ -> raise (Error "field")) (to_list (member "fields" j)))
  | "option" -> TOption (ty_of (member "inner" j))
  | "dict" -> TDict (ty_of (member "key" j), ty_of (member "val" j))
  | "class" -> TClass (to_str (member "name" j))
  | "opaque" -> TOpaque
  | "enum" -> TEnum (to_str (member "name" j), List.map to_str (to_list (member "members" j)), to_list (member "values" j))
  | k -> raise (Error ("unknown type " ^ k))

let loc_of j =
  match j with
  | List (l :: rest) ->
    let c = match rest with c :: _ -> to_int c | [] -> 0 in
    let ec = match rest with _ :: e :: _ -> to_int e | _ -> 0 in
    { line = to_int l; col = c; end_col = ec }
  | Int l -> { noloc with line = l }
  | _ -> noloc

let rec expr_of j : expr =
  let ty = ty_of (member "ty" j) and loc = loc_of (member "loc" j) in
  let args k = List.map expr_of (to_list (member k j)) in
  let sub k = expr_of (member k j) in
  let e =
    match to_str (member "e" j) with
    | "Lit" -> (
      match member "frac" j with
      | List [ n; d ] -> Lit (LFrac (Json.to_string n, Json.to_string d))
      | _ -> (
        match member "value" j with
        | Null -> Lit LNone
        | Bool b -> Lit (LBool b)
        | Int i -> ( match ty with TReal | TFloat32 -> Lit (LFrac (string_of_int i, "1")) | _ -> Lit (LInt (string_of_int i)))
        | BigInt t -> ( match ty with TReal | TFloat32 -> Lit (LFrac (t, "1")) | _ -> Lit (LInt t))
        | Float f -> Lit (LInt (Printf.sprintf "%.0f" f))
        | String s -> Lit (LStr s)
        | _ -> raise (Error "literal")))
    | "Var" -> Var (to_str (member "name" j))
    | "Result" -> Result
    | "Old" -> Old (sub "expr")
    | "Unary" -> Unary (to_str (member "op" j), sub "arg")
    | "Binary" -> Binary (to_str (member "op" j), sub "left", sub "right")
    | "Ite" -> Ite (sub "cond", sub "then", sub "orelse")
    | "Call" -> Call (to_str (member "func" j), args "args")
    | "Builtin" -> Builtin (to_str (member "name" j), args "args")
    | "Index" -> Index (sub "seq", sub "idx", to_bool (member "wrap" j))
    | "Field" -> Field (sub "obj", to_str (member "name" j))
    | "Quant" ->
      Quant
        {
          kind = to_str (member "kind" j);
          idx = to_str (member "idx" j);
          lo = sub "lo";
          hi = sub "hi";
          body = sub "body";
          elem = str_opt (member "elem" j);
          seq = (if is_null (member "seq" j) then None else Some (sub "seq"));
        }
    | "ListLit" -> ListLit (args "elems")
    | "RecordLit" -> RecordLit (List.map (function List [ String n; v ] -> (n, expr_of v) | _ -> raise (Error "recordlit")) (to_list (member "fields" j)))
    | "New" -> New (to_str (member "cls" j), args "args")
    | "Extern" -> Extern (to_str (member "name" j), args "args")
    | k -> raise (Error ("unknown expression " ^ k))
  in
  { e; ty; loc }

let clause_of j =
  {
    ckind = to_str (member "kind" j);
    cexpr = expr_of (member "expr" j);
    cloc = loc_of (member "loc" j);
    text = to_str (member "text" j);
    aims = List.map to_str (to_list (member "aims" j));
    inferred = to_bool (member "inferred" j);
  }

let clause_opt j = if is_null j then None else Some (clause_of j)

let rec stmts_of j = List.map stmt_of (to_list j)

and stmt_of j : stmt =
  let loc = loc_of (member "loc" j) in
  let ex k = expr_of (member k j) in
  let invs () = List.map clause_of (to_list (member "invariants" j)) in
  match to_str (member "s" j) with
  | "Assign" -> Assign (loc, to_str (member "name" j), ex "value")
  | "IndexAssign" -> IndexAssign (loc, to_str (member "name" j), ex "idx", ex "value", to_bool (member "wrap" j))
  | "Append" -> Append (loc, to_str (member "name" j), ex "value")
  | "If" -> If (loc, ex "cond", stmts_of (member "then" j), stmts_of (member "orelse" j))
  | "While" -> While { loc; cond = ex "cond"; invariants = invs (); decreases = clause_opt (member "decreases" j); body = stmts_of (member "body" j); step = stmts_of (member "step" j) }
  | "ForRange" -> ForRange { loc; var = to_str (member "var" j); lo = ex "lo"; hi = ex "hi"; invariants = invs (); body = stmts_of (member "body" j); reeval = to_bool (member "reeval" j) }
  | "ForEach" -> ForEach { loc; elem = to_str (member "elem" j); idx = to_str (member "idx" j); seq = ex "seq"; invariants = invs (); body = stmts_of (member "body" j); idx_visible = to_bool (member "idx_visible" j) }
  | "Return" -> Return (loc, if is_null (member "value" j) then None else Some (ex "value"))
  | "Break" -> Break loc
  | "Continue" -> Continue loc
  | "AssertStmt" -> AssertStmt (loc, clause_of (member "clause" j), to_bool (member "native" j))
  | "AssumeStmt" -> AssumeStmt (loc, clause_of (member "clause" j))
  | "Raise" -> Raise (loc, (match member "what" j with String s -> s | _ -> "exception"), to_bool (member "caught" j))
  | "ExprStmt" -> ExprStmt (loc, ex "expr")
  | "Unsupported" -> Unsupported (loc, to_str (member "reason" j))
  | "FieldAssign" -> FieldAssign (loc, ex "obj", to_str (member "cls" j), to_str (member "field" j), ex "value")
  | "DictDel" -> DictDel (loc, to_str (member "name" j), ex "key", to_bool (member "strict" j))
  | "Try" -> Try (loc, stmts_of (member "body" j), List.map stmts_of (to_list (member "handlers" j)), stmts_of (member "orelse" j), stmts_of (member "finalbody" j))
  | k -> raise (Error ("unknown statement " ^ k))

let func_of j =
  let locals = Hashtbl.create 16 in
  (match member "locals" j with Assoc kvs -> List.iter (fun (k, v) -> Hashtbl.replace locals k (ty_of v)) kvs | _ -> ());
  {
    name = to_str (member "name" j);
    floc = loc_of (member "loc" j);
    end_line = to_int (member "end_line" j);
    params = List.map (function List [ String n; t ] -> (n, ty_of t) | _ -> raise (Error "param")) (to_list (member "params" j));
    ret = ty_of (member "ret" j);
    requires = List.map clause_of (to_list (member "requires" j));
    ensures = List.map clause_of (to_list (member "ensures" j));
    decreases = clause_opt (member "decreases" j);
    raises = List.map clause_of (to_list (member "raises" j));
    body = stmts_of (member "body" j);
    faims = List.map to_str (to_list (member "aims" j));
    unsupported = List.map (function List [ String m; l ] -> (m, to_int l) | _ -> ("?", 0)) (to_list (member "unsupported" j));
    trusted = to_bool (member "trusted" j);
    unit = (match member "unit" j with Bool b -> b | _ -> false);
    locals;
    escaped = List.map to_str (to_list (member "escaped" j));
  }

let module_of j =
  {
    path = to_str (member "path" j);
    language = (match member "language" j with String s -> s | _ -> "python");
    functions = List.map func_of (to_list (member "functions" j));
    classes =
      (match member "classes" j with
       | Assoc kvs ->
         List.map
           (fun (n, c) ->
             {
               cname = n;
               fields = List.map (function List [ String f; t ] -> (f, ty_of t) | _ -> raise (Error "class field")) (to_list (member "fields" c));
               invariants = List.map clause_of (to_list (member "invariants" c));
             })
           kvs
       | _ -> []);
    imports = (match member "imports" j with Assoc kvs -> List.map (fun (k, v) -> match v with List [ String p; String n ] -> (k, (p, n)) | _ -> raise (Error "import")) kvs | _ -> []);
  }

(* -- walking ---------------------------------------------------------- *)

let rec walk_stmts (f : stmt -> unit) (ss : stmt list) =
  List.iter
    (fun s ->
      f s;
      match s with
      | If (_, _, a, b) -> walk_stmts f a; walk_stmts f b
      | While w -> walk_stmts f w.body; walk_stmts f w.step
      | ForRange r -> walk_stmts f r.body
      | ForEach r -> walk_stmts f r.body
      | Try (_, b, hs, o, fin) -> walk_stmts f b; List.iter (walk_stmts f) hs; walk_stmts f o; walk_stmts f fin
      | _ -> ())
    ss

let rec walk_expr (f : expr -> unit) (e : expr) =
  f e;
  match e.e with
  | Old x | Unary (_, x) | Field (x, _) -> walk_expr f x
  | Binary (_, a, b) | Index (a, b, _) -> walk_expr f a; walk_expr f b
  | Ite (a, b, c) -> walk_expr f a; walk_expr f b; walk_expr f c
  | Call (_, xs) | Builtin (_, xs) | ListLit xs | New (_, xs) | Extern (_, xs) -> List.iter (walk_expr f) xs
  | RecordLit fs -> List.iter (fun (_, x) -> walk_expr f x) fs
  | Quant q -> walk_expr f q.lo; walk_expr f q.hi; walk_expr f q.body; Option.iter (walk_expr f) q.seq
  | _ -> ()

let stmt_exprs (s : stmt) : expr list =
  match s with
  | Assign (_, _, v) | Append (_, _, v) -> [ v ]
  | IndexAssign (_, _, i, v, _) -> [ i; v ]
  | If (_, c, _, _) -> [ c ]
  | While w -> [ w.cond ]
  | ForRange r -> [ r.lo; r.hi ]
  | ForEach r -> [ r.seq ]
  | Return (_, Some v) -> [ v ]
  | ExprStmt (_, e) -> [ e ]
  | FieldAssign (_, o, _, _, v) -> [ o; v ]
  | DictDel (_, _, k, _) -> [ k ]
  | AssertStmt (_, c, true) -> [ c.cexpr ]
  | _ -> []

let assigned_names (ss : stmt list) : string list =
  let out = ref [] in
  let add n = if not (List.mem n !out) then out := n :: !out in
  walk_stmts
    (function
      | Assign (_, n, _) | IndexAssign (_, n, _, _, _) | Append (_, n, _) | DictDel (_, n, _, _) -> add n
      | ForRange r -> add r.var
      | ForEach r -> add r.elem; add r.idx
      | _ -> ())
    ss;
  !out

(* an expression without its positions: equal for the same code written twice *)
let rec strip (x : expr) : expr =
  let s = strip in
  let e =
    match x.e with
    | Old a -> Old (s a)
    | Unary (o, a) -> Unary (o, s a)
    | Binary (o, a, b) -> Binary (o, s a, s b)
    | Ite (a, b, c) -> Ite (s a, s b, s c)
    | Call (f, xs) -> Call (f, List.map s xs)
    | Builtin (f, xs) -> Builtin (f, List.map s xs)
    | Index (a, b, w) -> Index (s a, s b, w)
    | Field (a, f) -> Field (s a, f)
    | Quant q -> Quant { q with lo = s q.lo; hi = s q.hi; body = s q.body; seq = Option.map s q.seq }
    | ListLit xs -> ListLit (List.map s xs)
    | RecordLit fs -> RecordLit (List.map (fun (n, a) -> (n, s a)) fs)
    | New (c, xs) -> New (c, List.map s xs)
    | Extern (f, xs) -> Extern (f, List.map s xs)
    | e -> e
  in
  { x with e; loc = noloc }

let shape (x : expr) = Marshal.to_string (strip x) []
