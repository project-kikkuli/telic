(* Logical terms, hash-consed: every distinct term exists once, so equality
   is physical ([==]) and a term's id is a perfect hash. Smart constructors
   fold and simplify exactly like telic/logic.py, so the two cores build the
   same obligations. *)

type sort =
  | Int
  | Real
  | Float32
  | Float64  (** IEEE binary64 *)
  | Bool
  | Str
  | Opaque
  | Unit  (** Python None *)
  | Array of sort * sort  (** index, element *)
  | Rec of string * (string * sort) list

let rec sort_name = function
  | Int -> "Int"
  | Real -> "Real"
  | Float32 -> "Float32"
  | Float64 -> "Float64"
  | Bool -> "Bool"
  | Str -> "Str"
  | Opaque -> "Opaque"
  | Unit -> "None"
  | Array (i, e) -> if i = Int then Printf.sprintf "Array[%s]" (sort_name e) else Printf.sprintf "Array[%s->%s]" (sort_name i) (sort_name e)
  | Rec (n, _) -> n

let elem_sort = function Array (_, e) -> e | s -> failwith ("not an array: " ^ sort_name s)
let index_sort = function Array (i, _) -> i | _ -> Int

(* exact rationals over native ints; None on overflow *)
module Q = struct
  type t = { n : int; d : int }

  let rec gcd a b = if b = 0 then abs a else gcd b (a mod b)

  let make n d =
    if d = 0 then invalid_arg "Q.make";
    let g = gcd n d in
    let g = if g = 0 then 1 else g in
    let n, d = (n / g, d / g) in
    if d < 0 then { n = -n; d = -d } else { n; d }

  let of_int n = { n; d = 1 }
  let is_int q = q.d = 1

  (* overflow-checked arithmetic *)
  let mul_ok a b = if a = 0 || b = 0 then Some 0 else let r = a * b in if r / b = a && not (a = -1 && b = min_int) && not (b = -1 && a = min_int) then Some r else None
  let add_ok a b = let r = a + b in if (a >= 0) = (b >= 0) && (r >= 0) <> (a >= 0) then None else Some r

  let ( let* ) = Option.bind

  let add x y =
    let* a = mul_ok x.n y.d in
    let* b = mul_ok y.n x.d in
    let* n = add_ok a b in
    let* d = mul_ok x.d y.d in
    Some (make n d)

  let neg x = if x.n = min_int then None else Some { x with n = -x.n }
  let sub x y = let* ny = neg y in add x ny

  let mul x y =
    let* n = mul_ok x.n y.n in
    let* d = mul_ok x.d y.d in
    Some (make n d)

  let div x y =
    if y.n = 0 then None
    else
      let* n = mul_ok x.n y.d in
      let* d = mul_ok x.d y.n in
      Some (make n d)

  let compare x y =
    (* sign of x - y without overflow worries for the common case *)
    match sub x y with Some r -> compare r.n 0 | None -> compare (float_of_int x.n /. float_of_int x.d) (float_of_int y.n /. float_of_int y.d)

  let floor x = if x.d = 1 then x.n else if x.n >= 0 then x.n / x.d else -(((-x.n) + x.d - 1) / x.d)
  let to_string x = if x.d = 1 then string_of_int x.n else Printf.sprintf "%d/%d" x.n x.d
end

type term = { id : int; node : node; sort : sort }

and node =
  | Const of string
  | Num of Q.t  (** Int or Real literal (by sort) *)
  | Big of string  (** a literal too large to fold: kept as text; at Float64, its bits in hex *)
  | BoolV of bool
  | StrV of string
  | App of string * term array
  | Fn of string * term array
  | ArrayLambda of term * term
  | Quant of string * term array * term * term array list  (** kind, bound vars, body, patterns *)

(* -- hash-consing ------------------------------------------------------ *)

module Key = struct
  type t = node * sort

  let equal (a, sa) (b, sb) =
    sa = sb
    &&
    match (a, b) with
    | Const x, Const y -> String.equal x y
    | Num x, Num y -> x.n = y.n && x.d = y.d
    | Big x, Big y -> String.equal x y
    | BoolV x, BoolV y -> x = y
    | StrV x, StrV y -> String.equal x y
    | App (o, xs), App (p, ys) | Fn (o, xs), Fn (p, ys) -> String.equal o p && Array.length xs = Array.length ys && Array.for_all2 ( == ) xs ys
    | ArrayLambda (b, x), ArrayLambda (c, y) -> b == c && x == y
    | Quant (k, vs, b, ps), Quant (k', vs', b', ps') ->
      String.equal k k' && b == b' && Array.length vs = Array.length vs' && Array.for_all2 ( == ) vs vs'
      && List.length ps = List.length ps'
      && List.for_all2 (fun p q -> Array.length p = Array.length q && Array.for_all2 ( == ) p q) ps ps'
    | _ -> false

  let ids xs = Array.fold_left (fun h (t : term) -> (h * 31) + t.id) 7 xs

  let hash (n, s) =
    let h =
      match n with
      | Const x -> Hashtbl.hash (0, x)
      | Num q -> Hashtbl.hash (1, q.n, q.d)
      | Big x -> Hashtbl.hash (2, x)
      | BoolV b -> Hashtbl.hash (3, b)
      | StrV x -> Hashtbl.hash (4, x)
      | App (o, xs) -> Hashtbl.hash (5, o, ids xs)
      | Fn (o, xs) -> Hashtbl.hash (6, o, ids xs)
      | ArrayLambda (b, x) -> Hashtbl.hash (7, b.id, x.id)
      | Quant (k, vs, b, ps) -> Hashtbl.hash (8, k, ids vs, b.id, List.length ps)
    in
    (h * 17) + Hashtbl.hash s
end

module H = Hashtbl.Make (Key)

let table : term H.t = H.create 65536
let counter = ref 0

let mk node sort =
  let key = (node, sort) in
  match H.find_opt table key with
  | Some t -> t
  | None ->
    incr counter;
    let t = { id = !counter; node; sort } in
    H.add table key t;
    t

(* -- leaves ------------------------------------------------------------- *)

let const name sort = mk (Const name) sort
let int_ n = mk (Num (Q.of_int n)) Int
let unit = mk (Num (Q.of_int 0)) Unit
let real q = mk (Num q) Real
let bool_ b = mk (BoolV b) Bool
let str s = mk (StrV s) Str
let tt = bool_ true
let ff = bool_ false
let zero = int_ 0
let one = int_ 1

let num t = match t.node with Num q -> Some q | _ -> None

let lit_q (q : Q.t) sort = match sort with Int -> int_ (Q.floor q) | Real -> real q | _ -> invalid_arg "lit_q"

let lit_or_app op sort (r : Q.t option) args = match r with Some q -> lit_q q sort | None -> mk (App (op, args)) sort

let app op args sort = mk (App (op, args)) sort
let fn name args sort = mk (Fn (name, args)) sort

let is_bool_lit t = match t.node with BoolV _ -> true | _ -> false

(* -- floating point (mirror telic/logic.py) ----------------------------- *)
(* A Float64 literal is [Big] of its bits in hex. Arithmetic and comparisons
   are IEEE's; constants fold with OCaml's floats, the same binary64
   operations. *)

let fround sort x = if sort = Float32 then Int32.float_of_bits (Int32.bits_of_float x) else x
let fval_for sort x =
  if sort = Float32 then mk (Big (Printf.sprintf "%08lx" (Int32.bits_of_float (fround sort x)))) Float32
  else mk (Big (Printf.sprintf "%016Lx" (Int64.bits_of_float x))) Float64
let fval x = fval_for Float64 x
let fconst t = match t.node with
  | Big s when t.sort = Float32 && not (String.length s >= 2 && (String.sub s 0 2 = "n:" || String.sub s 0 2 = "r:")) -> Some (Int32.float_of_bits (Int32.of_string ("0x" ^ s)))
  | Big s when t.sort = Float64 && not (String.length s >= 2 && (String.sub s 0 2 = "n:" || String.sub s 0 2 = "r:")) -> Some (Int64.float_of_bits (Int64.of_string ("0x" ^ s)))
  | _ -> None

let fbin op a b =
  match (fconst a, fconst b) with
  | Some x, Some y when op = "fp.add" -> fval_for a.sort (x +. y)
  | Some x, Some y when op = "fp.sub" -> fval_for a.sort (x -. y)
  | Some x, Some y when op = "fp.mul" -> fval_for a.sort (x *. y)
  | Some x, Some y when op = "fp.div" && y <> 0.0 && a.sort <> Float32 -> fval_for a.sort (x /. y)
  | _ -> app op [| a; b |] a.sort

let fneg a = match (fconst a, a.node) with Some x, _ -> fval_for a.sort (-.x) | _, App ("fp.neg", [| x |]) -> x | _ -> app "fp.neg" [| a |] a.sort
let fabs a = match fconst a with Some x -> fval_for a.sort (Float.abs x) | None -> app "fp.abs" [| a |] a.sort

(* of an integer rounded to a double these are integer facts: only 0 rounds
   to zero, and only a magnitude past the largest float to infinity *)
let fpred_hook : (string -> term -> term) ref = ref (fun op a -> app op [| a |] Bool)

let fpred op a =
  match fconst a with
  | Some x when op = "fp.isNegative" -> bool_ (Float.sign_bit x && not (Float.is_nan x))
  | Some x -> bool_ (if op = "fp.isNaN" then Float.is_nan x else if op = "fp.isInfinite" then Float.abs x = Float.infinity else x = 0.0)
  | None -> !fpred_hook op a

let fpred_neg a = fpred "fp.isNegative" a

(* decimal strings, for the exact value of a double *)
let dec_double s =
  let n = String.length s in
  let b = Bytes.create (n + 1) in
  let carry = ref 0 in
  for i = n - 1 downto 0 do
    let v = ((Char.code s.[i] - 48) * 2) + !carry in
    Bytes.set b (i + 1) (Char.chr (48 + (v mod 10)));
    carry := v / 10
  done;
  Bytes.set b 0 (Char.chr (48 + !carry));
  let r = Bytes.to_string b in
  if r.[0] = '0' && String.length r > 1 then String.sub r 1 (String.length r - 1) else r

let rec pow2_times s k = if k = 0 then s else pow2_times (dec_double s) (k - 1)

let fcmp_ref : (string -> term -> term -> term) ref = ref (fun _ _ _ -> assert false)

(* -- smart constructors (mirror telic/logic.py) ------------------------- *)

let rec add a b =
  if a.sort = Float64 || a.sort = Float32 then fbin "fp.add" a b else
  match (num a, num b) with
  | Some x, Some y -> lit_or_app "add" a.sort (Q.add x y) [| a; b |]
  | Some x, _ when x.n = 0 -> b
  | _, Some y when y.n = 0 -> a
  | _, Some y -> (
    match a.node with
    | App ("add", [| e; c |]) when num c <> None -> (
      match Q.add (Option.get (num c)) y with Some s -> add e (lit_q s a.sort) | None -> app "add" [| a; b |] a.sort)
    | _ -> if Q.compare y (Q.of_int 0) < 0 then (match Q.neg y with Some ny -> app "sub" [| a; lit_q ny a.sort |] a.sort | None -> app "add" [| a; b |] a.sort) else app "add" [| a; b |] a.sort)
  | _ -> app "add" [| a; b |] a.sort

and sub a b =
  if a.sort = Float64 || a.sort = Float32 then fbin "fp.sub" a b else
  match (num a, num b) with
  | Some x, Some y -> lit_or_app "sub" a.sort (Q.sub x y) [| a; b |]
  | _, Some y when y.n = 0 -> a
  | _ when a == b -> lit_q (Q.of_int 0) a.sort
  | _, Some y -> (
    match a.node with
    | App ("add", [| e; c |]) when num c <> None -> (
      match Q.sub (Option.get (num c)) y with Some s -> add e (lit_q s a.sort) | None -> app "sub" [| a; b |] a.sort)
    | App ("sub", [| e; c |]) when num c <> None -> (
      match Q.add (Option.get (num c)) y with Some s -> sub e (lit_q s a.sort) | None -> app "sub" [| a; b |] a.sort)
    | _ -> if Q.compare y (Q.of_int 0) < 0 then (match Q.neg y with Some ny -> add a (lit_q ny a.sort) | None -> app "sub" [| a; b |] a.sort) else app "sub" [| a; b |] a.sort)
  | _ -> app "sub" [| a; b |] a.sort

let mul a b =
  if a.sort = Float64 || a.sort = Float32 then fbin "fp.mul" a b else
  match (num a, num b) with
  | Some x, Some y -> lit_or_app "mul" a.sort (Q.mul x y) [| a; b |]
  | Some x, _ when x.n = 0 -> lit_q (Q.of_int 0) a.sort
  | _, Some y when y.n = 0 -> lit_q (Q.of_int 0) a.sort
  | Some x, _ when x.n = 1 && x.d = 1 -> b
  | _, Some y when y.n = 1 && y.d = 1 -> a
  | _ -> app "mul" [| a; b |] a.sort

let neg a =
  if a.sort = Float64 || a.sort = Float32 then fneg a else
  match (num a, a.node) with
  | Some x, _ -> lit_or_app "neg" a.sort (Q.neg x) [| a |]
  | _, App ("neg", [| x |]) -> x
  | _ -> app "neg" [| a |] a.sort

let rdiv a b =
  if a.sort = Float64 || a.sort = Float32 then fbin "fp.div" a b else
  match (num a, num b) with
  | Some x, Some y when y.n <> 0 -> (match Q.div x y with Some q -> real q | None -> app "rdiv" [| a; b |] Real)
  | _, Some y when y.n = 1 && y.d = 1 -> a
  | _ -> app "rdiv" [| a; b |] Real

let ediv a b =
  match (num a, num b) with
  | Some x, Some y when y.n <> 0 ->
    let fl p q = if (p >= 0) = (q > 0) || p mod q = 0 then p / q else (p / q) - 1 in
    let q = if y.n > 0 then fl x.n y.n else -fl x.n (-y.n) in
    int_ q
  | _, Some y when y.n = 1 -> a
  | _ -> app "ediv" [| a; b |] Int

let emod a b =
  match (num a, num b) with
  | Some x, Some y when y.n <> 0 ->
    let m = abs y.n in
    let r = x.n mod m in
    int_ (if r < 0 then r + m else r)
  | _ -> app "emod" [| a; b |] Int

let to_real a = match a.node with Num q when a.sort = Int -> real q | _ -> app "to_real" [| a |] Real

let rec floor a =
  match a.node with
  | Num q when a.sort = Real -> int_ (Q.floor q)
  | App ("to_real", [| x |]) -> x
  | _ when List.mem a.sort [ Float32; Float64 ] -> floor (app "fp.to_real" [| a |] Real)
  | _ -> app "floor" [| a |] Int

let is_int a =
  match a.node with
  | Num q when a.sort = Real -> bool_ (Q.is_int q)
  | App ("to_real", _) -> tt
  | _ -> app "is_int" [| a |] Bool

let lt a b =
  if List.mem a.sort [ Float32; Float64 ] || List.mem b.sort [ Float32; Float64 ] then !fcmp_ref "fp.lt" a b else
  match (num a, num b) with
  | Some x, Some y -> bool_ (Q.compare x y < 0)
  | _ when a == b -> ff
  | _ -> app "lt" [| a; b |] Bool

let le a b =
  if List.mem a.sort [ Float32; Float64 ] || List.mem b.sort [ Float32; Float64 ] then !fcmp_ref "fp.leq" a b else
  match (num a, num b) with
  | Some x, Some y -> bool_ (Q.compare x y <= 0)
  | _ when a == b -> tt
  | _ -> app "le" [| a; b |] Bool

let gt a b = lt b a
let ge a b = le b a

let not_ a = match a.node with BoolV b -> bool_ (not b) | App ("not", [| x |]) -> x | _ -> app "not" [| a |] Bool

let is_value t = match t.node with Num _ | BoolV _ | StrV _ -> true | _ -> false

let eq a b =
  if List.mem a.sort [ Float32; Float64 ] || List.mem b.sort [ Float32; Float64 ] then !fcmp_ref "fp.eq" a b
  else if a == b then tt
  else if is_value a && is_value b then ff (* distinct hash-consed values *)
  else if a.sort = Bool then
    if b == tt then a else if b == ff then not_ a else if a == tt then b else if a == ff then not_ b else app "eq" [| a; b |] Bool
  else app "eq" [| a; b |] Bool

let ne a b = not_ (eq a b)

let and_ (xs : term list) =
  let out = ref [] in
  let seen = Hashtbl.create 8 in
  let push y = if not (Hashtbl.mem seen y.id) then (Hashtbl.add seen y.id (); out := y :: !out) in
  let exception False in
  try
    List.iter
      (fun x ->
        if x == tt then ()
        else if x == ff then raise False
        else match x.node with App ("and", ys) -> Array.iter push ys | _ -> push x)
      xs;
    match List.rev !out with [] -> tt | [ y ] -> y | ys -> app "and" (Array.of_list ys) Bool
  with False -> ff

let or_ (xs : term list) =
  let out = ref [] in
  let seen = Hashtbl.create 8 in
  let push y = if not (Hashtbl.mem seen y.id) then (Hashtbl.add seen y.id (); out := y :: !out) in
  let exception True in
  try
    List.iter
      (fun x ->
        if x == ff then ()
        else if x == tt then raise True
        else match x.node with App ("or", ys) -> Array.iter push ys | _ -> push x)
      xs;
    match List.rev !out with [] -> ff | [ y ] -> y | ys -> app "or" (Array.of_list ys) Bool
  with True -> tt

let implies a b = if a == tt then b else if a == ff || b == tt then tt else if b == ff then not_ a else app "implies" [| a; b |] Bool

let ite c a b =
  if c == tt then a
  else if c == ff then b
  else if a == b then a
  else if a.sort = Bool && a == tt && b == ff then c
  else if a.sort = Bool && a == ff && b == tt then not_ c
  else app "ite" [| c; a; b |] a.sort

let rec select_raw arr idx =
  match arr.node with
  | App ("K", [| v |]) -> v
  | App ("store", [| base; k; v |]) ->
    if k == idx then v
    else if (match (k.node, idx.node) with Num _, Num _ -> true | _ -> false) && k.sort = Int then select_raw base idx
    else app "select" [| arr; idx |] (elem_sort arr.sort)
  | _ -> app "select" [| arr; idx |] (elem_sort arr.sort)

let store arr idx v = app "store" [| arr; idx; v |] arr.sort
let const_array sort v = app "K" [| v |] sort

let field obj name =
  match obj.sort with
  | Rec (rname, fields) -> (
    match obj.node with
    | App (op, args) when String.length op > 3 && String.sub op 0 3 = "mk:" ->
      let rec find i = function [] -> raise Not_found | (f, _) :: r -> if f = name then args.(i) else find (i + 1) r in
      find 0 fields
    | _ ->
      let fs = try List.assoc name fields with Not_found -> failwith (Printf.sprintf "%s has no field %s" rname name) in
      app ("field:" ^ name) [| obj |] fs)
  | s -> failwith ("field of a non-record " ^ sort_name s)

let mkrec sort vals = match sort with Rec (n, _) -> app ("mk:" ^ n) (Array.of_list vals) sort | _ -> invalid_arg "mkrec"

let rec occurs (v : term) (t : term) =
  t == v || match t.node with
  | App (_, xs) | Fn (_, xs) -> Array.exists (occurs v) xs
  | ArrayLambda (binder, body) -> v != binder && occurs v body
  | Quant (_, vs, b, _) -> not (Array.exists (( == ) v) vs) && occurs v b
  | _ -> false

let array_lambda binder body =
  match binder.node with
  | Const _ ->
    let sort = Array (binder.sort, body.sort) in
    mk (ArrayLambda (binder, body)) sort
  | _ -> invalid_arg "array lambda binder must be a constant"

let quant kind vs body pats = mk (Quant (kind, Array.of_list vs, body, pats)) Bool

let forall vs body =
  let vs = List.filter (fun v -> occurs v body) vs in
  if vs = [] || is_bool_lit body then body else quant "forall" vs body []

let exists vs body =
  let vs = List.filter (fun v -> occurs v body) vs in
  if vs = [] || is_bool_lit body then body else quant "exists" vs body []

let abs_ a = if List.mem a.sort [ Float32; Float64 ] then fabs a else ite (le (lit_q (Q.of_int 0) a.sort) a) a (neg a)

(* the exact value of a finite float (unspecified for NaN and infinities) *)
let fto_real a =
  match fconst a with
  | Some x when x = 0.0 -> real (Q.of_int 0)
  | Some x when Float.is_finite x ->
    let fr, e = Float.frexp (Float.abs x) in
    let m = ref (Int64.of_float (Float.ldexp fr 53)) and e = ref (e - 53) in
    while !m <> 0L && Int64.rem !m 2L = 0L && !e < 0 do
      m := Int64.div !m 2L;
      incr e
    done;
    let ms = Int64.to_string !m in
    let n, d = if !e >= 0 then (pow2_times ms !e, "1") else (ms, pow2_times "1" (- !e)) in
    let n = if Float.sign_bit x && !m <> 0L then "-" ^ n else n in
    (match (int_of_string_opt n, int_of_string_opt d) with
     | Some n, Some d when abs n < 1 lsl 61 && d < 1 lsl 61 -> real (Q.make n d)
     | _ -> mk (Big (n ^ "/" ^ d)) Real)
  | _ -> app "fp.to_real" [| a |] Real

let fnear_int (s : string) = fval (float_of_string s)

(* an Int or Real term at sort Float64, rounded to nearest *)
let as_float a =
  if a.sort = Float64 then a
  else
    match (a.node, a.sort) with
    | Num _, Int -> app "fp.of_int" [| a |] Float64
    | Num q, Real -> app "fp.of_real" [| real q |] Float64
    | Big _, Int -> app "fp.of_int" [| a |] Float64
    | _, Int -> app "fp.of_int" [| a |] Float64
    | _ -> app "fp.of_real" [| a |] Float64

(* a float against an exact number: NaN is unordered, the infinities lie
   beyond every number, a finite float compares by its exact value *)
let xcmp op a b =
  let flip = not (List.mem a.sort [ Float32; Float64 ]) in
  let f, x = if flip then (b, a) else (a, b) in
  let xr = if x.sort = Real then x else to_real x in
  let fr = fto_real f in
  let nan = fpred "fp.isNaN" f and inf = fpred "fp.isInfinite" f in
  let pos = not_ (fpred_neg f) in
  if op = "fp.eq" then and_ [ not_ nan; not_ inf; eq fr xr ]
  else
    let exact = if flip then (if op = "fp.lt" then lt xr fr else le xr fr) else if op = "fp.lt" then lt fr xr else le fr xr in
    let beyond = if flip then pos else not_ pos in
    and_ [ not_ nan; ite inf beyond exact ]

let is_float = function Float32 | Float64 -> true | _ -> false

let as_float_to target a =
  if a.sort = target then a
  else match a.node, a.sort with
  | Num _, Int -> app "fp.of_int" [| a |] target
  | Num q, Real -> app "fp.of_real" [| real q |] target
  | Big _, Int -> app "fp.of_int" [| a |] target
  | _ when is_float a.sort -> app "fp.cast" [| a |] target
  | _, Int -> app "fp.of_int" [| a |] target
  | _ -> app "fp.of_real" [| a |] target

let fcmp op a b =
  if is_float a.sort && is_float b.sort then
    (match (fconst a, fconst b) with
    | Some x, Some y -> bool_ (if op = "fp.lt" then x < y else if op = "fp.leq" then x <= y else x = y)
    | _ -> app op [| a; b |] Bool)
  else if not (is_float a.sort || is_float b.sort) then app op [| a; b |] Bool
  else xcmp op a b

let () = fcmp_ref := fcmp

let () =
  fpred_hook :=
    fun op a ->
      match a.node with
      | App ("ite", [| c; x; y |]) -> ite c (fpred op x) (fpred op y)
      | App ("fp.of_int", [| i |]) -> (
        match op with
        | "fp.isNaN" -> ff
        | "fp.isZero" -> eq i zero
        | "fp.isNegative" -> lt i zero
        | _ -> le (mk (Big "179769313486231580793728971405303415079934132710037826936173778980444968292764750946649017977587207096330286416692887910946555547851940402630657488671505820681908902000708383676273854845817711531764475730270069855571366959622842914819860834936475292719074168444365510704342711559699508093042880177904174497792") Int) (abs_ i))
      | _ -> app op [| a |] Bool
let feq a b = fcmp "fp.eq" a b
let is_finite a = and_ [ not_ (fpred "fp.isNaN" a); not_ (fpred "fp.isInfinite" a) ]
let min_ a b = ite (le a b) a b
let max_ a b = ite (le a b) b a

let lit_of_int n sort = lit_q (Q.of_int n) sort

(* -- traversal ---------------------------------------------------------- *)

let children t = match t.node with App (_, xs) | Fn (_, xs) -> Array.to_list xs | ArrayLambda (_, b) | Quant (_, _, b, _) -> [ b ] | _ -> []

(* does any subterm have sort [s]? *)
let mentions_sort s (t : term) =
  let seen = Hashtbl.create 64 in
  let rec go t =
    t.sort = s
    || (not (Hashtbl.mem seen t.id))
       && (Hashtbl.add seen t.id ();
           List.exists go (children t))
  in
  go t

(* free constants, respecting binders *)
let consts (t : term) : term list =
  let out = Hashtbl.create 64 in
  let order = ref [] in
  let rec go bound t =
    match t.node with
    | Const _ -> if not (List.memq t bound) && not (Hashtbl.mem out t.id) then (Hashtbl.add out t.id (); order := t :: !order)
    | ArrayLambda (v, b) -> go (v :: bound) b
    | Quant (_, vs, b, _) -> go (Array.to_list vs @ bound) b
    | App (_, xs) | Fn (_, xs) -> Array.iter (go bound) xs
    | _ -> ()
  in
  go [] t;
  List.rev !order

let fns (t : term) : string list =
  let seen = Hashtbl.create 64 and out = ref [] in
  let names = Hashtbl.create 16 in
  let rec go t =
    if not (Hashtbl.mem seen t.id) then begin
      Hashtbl.add seen t.id ();
      (match t.node with Fn (n, _) -> if not (Hashtbl.mem names n) then (Hashtbl.add names n (); out := n :: !out) | _ -> ());
      List.iter go (children t);
      match t.node with Quant (_, _, _, ps) -> List.iter (Array.iter go) ps | _ -> ()
    end
  in
  go t;
  List.rev !out

(* [t] with each key of [m] (by id) replaced by its value; bound variables are not replaced *)
let rec subst (m : (term * term) list) (t : term) : term =
  let memo = Hashtbl.create 64 in
  let m0 = m in
  let rec go m t =
    match List.find_opt (fun (k, _) -> k == t) m with
    | Some (_, v) -> v
    | None -> (
      match Hashtbl.find_opt memo t.id with
      | Some r when m == m0 -> r
      | _ ->
        let r =
          match t.node with
          | App (op, xs) -> let ys = Array.map (go m) xs in if Array.for_all2 ( == ) xs ys then t else mk (App (op, ys)) t.sort
          | Fn (f, xs) -> let ys = Array.map (go m) xs in if Array.for_all2 ( == ) xs ys then t else mk (Fn (f, ys)) t.sort
          | ArrayLambda (binder, body) ->
            let inner = List.filter (fun (k, _) -> k != binder) m in
            let replacements = List.concat_map (fun (_, v) -> consts v) inner in
            let binder, body =
              if List.exists (fun c -> c == binder) replacements then begin
                let used = consts body @ replacements @ [ binder ] in
                let stem = match binder.node with Const n -> n ^ "$alpha" | _ -> "lambda$alpha" in
                let rec name i = let n = if i = 0 then stem else stem ^ string_of_int i in if List.exists (fun c -> c.node = Const n) used then name (i + 1) else n in
                let fresh = const (name 0) binder.sort in
                (fresh, subst [ (binder, fresh) ] body)
              end else (binder, body)
            in
            let body' = go inner body in
            if binder == (match t.node with ArrayLambda (b, _) -> b | _ -> assert false) && body' == body then t else array_lambda binder body'
          | Quant (k, vs, b, ps) ->
            let inner = List.filter (fun (k, _) -> not (Array.exists (fun v -> v == k) vs)) m in
            let b' = go inner b in
            if b' == b then t else mk (Quant (k, vs, b', List.map (Array.map (go inner)) ps)) t.sort
          | _ -> t
        in
        if m == m0 then Hashtbl.replace memo t.id r;
        r)
  in
  go m t

let select arr idx =
  match arr.node with
  | ArrayLambda (binder, body) ->
    if binder.sort <> idx.sort then invalid_arg "array lambda index sort mismatch";
    subst [ (binder, idx) ] body
  | _ -> select_raw arr idx

(* regular languages of text the parsing builtins accept, by name (SMT-LIB
   syntax; the request carries them from telic/logic.py) *)
let regexes : (string, string) Hashtbl.t = Hashtbl.create 8

let in_re s name =
  match Hashtbl.find_opt regexes name with
  | Some text -> app "str.in_re" [| s; str text |] Bool
  | None -> failwith ("no regular language " ^ name)

let str_to_int s = app "str.to_int" [| s |] Int
