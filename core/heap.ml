(* Native encoding of telic.heap's versioned ABI. *)

open Term

let abi_version = 1

let language_tags = [ ("python", 1); ("typescript", 2); ("rust", 3); ("swift", 4) ]
let value_tags = [ ("none", 0); ("integer", 1); ("real", 2); ("boolean", 3); ("text", 4); ("reference", 5); ("opaque", 6); ("python_number", 7) ]
let cell_tags = [ ("free", 0); ("list", 1); ("dict", 2); ("record", 3); ("class", 4) ]

let number = Rec ("PythonNumber", [ ("is_int", Bool); ("integer", Int); ("floating", Float64) ])
let key = Rec ("TelicKeyV1", [ ("tag", Int); ("numeric", Real); ("text", Str) ])
let value =
  Rec
    ( "TelicValueV1",
      [ ("tag", Int); ("integer", Int); ("real", Float64); ("python_number", number); ("boolean", Bool); ("text", Str); ("reference", Int); ("opaque", Opaque) ] )

(* Dictionary history retains tombstones; key_position points at the live slot. *)
let cell =
  Rec
    ( "TelicCellV1",
      [ ("allocated", Bool); ("kind", Int); ("class", Int); ("len", Int); ("key_count", Int);
        ("seq", Array (Int, value)); ("map", Array (key, value)); ("has", Array (key, Bool));
        ("keys", Array (Int, key)); ("key_live", Array (Int, Bool));
        ("key_position", Array (key, Int)); ("fields", Array (Int, value)) ] )

let heap = Array (Int, cell)
let ref_sort = Int

let default sort =
  let rec make = function
    | Int | Unit -> zero
    | Real -> real (Q.of_int 0)
    | Float32 -> fval_for Float32 0.0
    | Float64 -> fval 0.0
    | Bool -> ff
    | Str -> str ""
    | Opaque -> const "opaque!default" Opaque
    | Array (_, elem) as s -> const_array s (make elem)
    | Rec (_, fields) as s -> mkrec s (List.map (fun (_, field_sort) -> make field_sort) fields)
  in
  make sort

let blank_cell () = default cell
let cell_at h r = select h r
let get h r name = Term.field (cell_at h r) name
let replace_record record changes =
  match record.sort with
  | Rec (_, fields) -> mkrec record.sort (List.map (fun (name, _) -> match List.assoc_opt name changes with Some value -> value | None -> Term.field record name) fields)
  | _ -> invalid_arg "heap record update"

let update h r changes = store h r (replace_record (cell_at h r) changes)
let read_len h r = get h r "len"
let read_list h r i = select (get h r "seq") i
let write_list h r i v = update h r [ ("seq", store (get h r "seq") i v) ]
let append_list h r v =
  let n = read_len h r in
  update h r [ ("seq", store (get h r "seq") n v); ("len", add n one) ]
let list_cell len seq =
  replace_record (blank_cell ()) [ ("kind", int_ 1); ("len", len); ("seq", seq) ]
let record_cell fields = replace_record (blank_cell ()) [ ("kind", int_ 3); ("fields", fields) ]
let dict_cell () =
  let none =
    let fields = [ int_ 0; zero; fval 0.0; default number; ff; str ""; zero; default Opaque ] in
    mkrec value fields
  in
  replace_record (blank_cell ())
    [ ("kind", int_ 2); ("map", const_array (Array (key, value)) none);
      ("has", const_array (Array (key, Bool)) ff); ("seq", const_array (Array (Int, value)) none);
      ("keys", const_array (Array (Int, key)) (default key));
      ("key_live", const_array (Array (Int, Bool)) ff);
      ("key_position", const_array (Array (key, Int)) zero) ]
let class_cell class_tag = replace_record (blank_cell ()) [ ("kind", int_ 4); ("class", class_tag) ]
let read_dict h r k = select (get h r "map") k
let has_dict h r k = select (get h r "has") k
let write_dict h r k original_key v =
  let present = has_dict h r k in
  let count = get h r "key_count" in
  let position = select (get h r "key_position") k in
  let slot = ite present position count in
  let keys = ite present (get h r "keys") (store (get h r "keys") count k) in
  let live = ite present (get h r "key_live") (store (get h r "key_live") count tt) in
  let seq = ite present (get h r "seq") (store (get h r "seq") count original_key) in
  update h r
    [ ("map", store (get h r "map") k v); ("has", store (get h r "has") k tt);
      ("keys", keys); ("key_live", live);
      ("key_position", store (get h r "key_position") k slot); ("seq", seq);
      ("key_count", ite present count (add count one)); ("len", ite present (get h r "len") (add (get h r "len") one)) ]
let delete_dict h r k =
  let present = has_dict h r k in
  let position = select (get h r "key_position") k in
  update h r
    [ ("has", store (get h r "has") k ff);
      ("key_live", store (get h r "key_live") position ff);
      ("len", ite present (sub (get h r "len") one) (get h r "len")) ]
let dict_original_key h r history_slot = select (get h r "seq") history_slot
let dict_rank h r history_slot = fn "seqcount_bool" [| get h r "key_live"; zero; history_slot; tt |] Int
let read_field h r slot = select (get h r "fields") slot
let write_field h r slot v = update h r [ ("fields", store (get h r "fields") slot v) ]
let allocate h contents r =
  let old = cell_at h r in
  let contents = replace_record contents [ ("allocated", tt) ] in
  (store h r contents, [ not_ (Term.field old "allocated") ])

let integer_tag = 1
let real_tag = 2
let boolean_tag = 3
let text_tag = 4
let reference_tag = 5
let python_number_tag = 7

let canonical_key raw ty language =
  let numeric n = mkrec key [ int_ 1; n; str "" ] in
  let text s = mkrec key [ int_ 2; real (Q.of_int 0); s ] in
  match ty with
  | Ir.TBool when language = "typescript" -> (mkrec key [ int_ 6; real (Q.of_int 0); str "" ], tt)
  | Ir.TBool -> (numeric (to_real (ite raw one zero)), tt)
  | Ir.TInt | Ir.TEnum _ -> (numeric (to_real raw), tt)
  | Ir.TPythonNumber ->
    let is_int = Term.field raw "is_int" and i = Term.field raw "integer" and f = Term.field raw "floating" in
    (numeric (ite is_int (to_real i) (fto_real f)), or_ [ is_int; is_finite f ])
  | Ir.TReal | Ir.TFloat32 when language = "typescript" ->
    let nan = fpred "fp.isNaN" raw in
    let negative = fpred_neg raw in
    let special = ite nan (mkrec key [ int_ 3; real (Q.of_int 0); str "" ])
      (ite negative (mkrec key [ int_ 5; real (Q.of_int 0); str "" ])
        (mkrec key [ int_ 4; real (Q.of_int 0); str "" ])) in
    (ite (is_finite raw) (numeric (fto_real raw)) special, tt)
  | Ir.TReal | Ir.TFloat32 -> (numeric (fto_real raw), is_finite raw)
  | Ir.TStr -> (text raw, tt)
  | Ir.TClass _ when language = "typescript" ->
    (mkrec key [ int_ 7; to_real raw; str "" ], tt)
  | _ -> invalid_arg ("unsupported dictionary key type in " ^ language)

let box raw ty =
  let fields = ref (List.map (fun (_, s) -> default s) (match value with Rec (_, fs) -> fs | _ -> [])) in
  let set name v =
    match value with
    | Rec (_, fs) ->
      let index = Option.get (List.find_index (fun (n, _) -> n = name) fs) in
      fields := List.mapi (fun i old -> if i = index then v else old) !fields
    | _ -> assert false
  in
  (match ty with
   | Ir.TNone -> set "tag" (int_ 0)
   | Ir.TInt | Ir.TEnum _ -> set "tag" (int_ integer_tag); set "integer" raw
   | Ir.TReal | Ir.TFloat32 -> set "tag" (int_ real_tag); set "real" (as_float_to Float64 raw)
   | Ir.TBool -> set "tag" (int_ boolean_tag); set "boolean" raw
   | Ir.TStr -> set "tag" (int_ text_tag); set "text" raw
   | Ir.TPythonNumber -> set "tag" (int_ python_number_tag); set "python_number" raw
   | Ir.TList _ | Ir.TDict _ | Ir.TClass _ | Ir.TRecord _ -> set "tag" (int_ reference_tag); set "reference" raw
   | Ir.TOpaque -> set "tag" (int_ 6); set "opaque" raw
   | Ir.TOption _ -> invalid_arg "optional boxing needs presence"
   );
  mkrec value !fields

let unbox boxed ty =
  let tag = Term.field boxed "tag" in
  let t n = eq tag (int_ n) in
  let python = Term.field boxed "python_number" in
  let py_int = Term.field python "is_int" and py_integer = Term.field python "integer" and py_float = Term.field python "floating" in
  match ty with
  | Ir.TNone -> bool_ (false)
  | Ir.TInt | Ir.TEnum _ -> ite (t boolean_tag) (ite (Term.field boxed "boolean") one zero)
      (ite (t python_number_tag) py_integer (Term.field boxed "integer"))
  | Ir.TReal | Ir.TFloat32 ->
    let value = ite (or_ [ t integer_tag; t boolean_tag ])
      (as_float_to Float64 (ite (t boolean_tag) (ite (Term.field boxed "boolean") one zero) (Term.field boxed "integer")))
      (ite (t python_number_tag) (ite py_int (as_float_to Float64 py_integer) py_float) (Term.field boxed "real")) in
    if ty = Ir.TFloat32 then as_float_to Float32 value else value
  | Ir.TBool -> Term.field boxed "boolean"
  | Ir.TStr -> Term.field boxed "text"
  | Ir.TPythonNumber ->
    let integer = ite (t boolean_tag) (ite (Term.field boxed "boolean") one zero) (Term.field boxed "integer") in
    let from_int = mkrec number [ tt; integer; fval 0.0 ] in
    let from_real = mkrec number [ ff; zero; Term.field boxed "real" ] in
    ite (t python_number_tag) python (ite (t integer_tag) from_int (ite (t boolean_tag) from_int from_real))
  | Ir.TList _ | Ir.TDict _ | Ir.TClass _ | Ir.TRecord _ -> Term.field boxed "reference"
  | Ir.TOpaque -> Term.field boxed "opaque"
  | Ir.TOption _ -> invalid_arg "optional unboxing needs presence"

let rec accepts boxed ty =
  let tag = Term.field boxed "tag" in
  let one_of tags = or_ (List.map (fun n -> eq tag (int_ n)) tags) in
  match ty with
  | Ir.TNone -> one_of [ 0 ]
  | Ir.TInt | Ir.TEnum _ -> or_ [ one_of [ integer_tag; boolean_tag ]; and_ [ eq tag (int_ python_number_tag); Term.field (Term.field boxed "python_number") "is_int" ] ]
  | Ir.TReal | Ir.TFloat32 -> one_of [ integer_tag; real_tag; boolean_tag; python_number_tag ]
  | Ir.TBool -> one_of [ boolean_tag ]
  | Ir.TStr -> one_of [ text_tag ]
  | Ir.TPythonNumber -> one_of [ integer_tag; real_tag; boolean_tag; python_number_tag ]
  | Ir.TList _ | Ir.TDict _ | Ir.TClass _ | Ir.TRecord _ -> one_of [ reference_tag ]
  | Ir.TOpaque -> one_of [ 6 ]
  | Ir.TOption inner -> or_ [ eq tag (int_ 0); accepts boxed inner ]
