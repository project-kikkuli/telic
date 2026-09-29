(* A small JSON reader/writer: telic's engine speaks JSON with the Python
   front end over a pipe, and needs nothing else. *)

type t =
  | Null
  | Bool of bool
  | Int of int
  | Float of float
  | String of string
  | List of t list
  | Assoc of (string * t) list

exception Error of string

let parse (s : string) : t =
  let n = String.length s in
  let pos = ref 0 in
  let peek () = if !pos < n then s.[!pos] else '\000' in
  let rec ws () =
    if !pos < n then
      match s.[!pos] with
      | ' ' | '\n' | '\r' | '\t' -> incr pos; ws ()
      | _ -> ()
  in
  let expect c =
    ws ();
    if peek () <> c then raise (Error (Printf.sprintf "expected '%c' at %d" c !pos));
    incr pos
  in
  let buf = Buffer.create 64 in
  let hex c =
    match c with
    | '0' .. '9' -> Char.code c - 48
    | 'a' .. 'f' -> Char.code c - 87
    | 'A' .. 'F' -> Char.code c - 55
    | _ -> raise (Error "bad \\u escape")
  in
  let add_utf8 cp =
    if cp < 0x80 then Buffer.add_char buf (Char.chr cp)
    else if cp < 0x800 then begin
      Buffer.add_char buf (Char.chr (0xC0 lor (cp lsr 6)));
      Buffer.add_char buf (Char.chr (0x80 lor (cp land 0x3F)))
    end else if cp < 0x10000 then begin
      Buffer.add_char buf (Char.chr (0xE0 lor (cp lsr 12)));
      Buffer.add_char buf (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
      Buffer.add_char buf (Char.chr (0x80 lor (cp land 0x3F)))
    end else begin
      Buffer.add_char buf (Char.chr (0xF0 lor (cp lsr 18)));
      Buffer.add_char buf (Char.chr (0x80 lor ((cp lsr 12) land 0x3F)));
      Buffer.add_char buf (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
      Buffer.add_char buf (Char.chr (0x80 lor (cp land 0x3F)))
    end
  in
  let string () =
    expect '"';
    Buffer.clear buf;
    let rec go () =
      if !pos >= n then raise (Error "unterminated string");
      let c = s.[!pos] in
      incr pos;
      match c with
      | '"' -> ()
      | '\\' ->
        let e = s.[!pos] in
        incr pos;
        (match e with
         | 'n' -> Buffer.add_char buf '\n'
         | 't' -> Buffer.add_char buf '\t'
         | 'r' -> Buffer.add_char buf '\r'
         | 'b' -> Buffer.add_char buf '\b'
         | 'f' -> Buffer.add_char buf '\012'
         | 'u' ->
           let cp = (hex s.[!pos] lsl 12) lor (hex s.[!pos + 1] lsl 8) lor (hex s.[!pos + 2] lsl 4) lor hex s.[!pos + 3] in
           pos := !pos + 4;
           let cp =
             if cp >= 0xD800 && cp <= 0xDBFF && !pos + 5 < n && s.[!pos] = '\\' && s.[!pos + 1] = 'u' then begin
               let lo = (hex s.[!pos + 2] lsl 12) lor (hex s.[!pos + 3] lsl 8) lor (hex s.[!pos + 4] lsl 4) lor hex s.[!pos + 5] in
               pos := !pos + 6;
               0x10000 + ((cp - 0xD800) lsl 10) + (lo - 0xDC00)
             end else cp
           in
           add_utf8 cp
         | c -> Buffer.add_char buf c);
        go ()
      | c -> Buffer.add_char buf c; go ()
    in
    go ();
    Buffer.contents buf
  in
  let number () =
    let start = !pos in
    let is_float = ref false in
    while !pos < n && (match s.[!pos] with '0' .. '9' | '-' | '+' -> true | '.' | 'e' | 'E' -> is_float := true; true | _ -> false) do
      incr pos
    done;
    let txt = String.sub s start (!pos - start) in
    if !is_float then Float (float_of_string txt)
    else match int_of_string_opt txt with Some i -> Int i | None -> Float (float_of_string txt)
  in
  let rec value () =
    ws ();
    match peek () with
    | '{' ->
      incr pos;
      ws ();
      if peek () = '}' then (incr pos; Assoc [])
      else begin
        let rec fields acc =
          let k = string () in
          expect ':';
          let v = value () in
          ws ();
          match peek () with
          | ',' -> incr pos; ws (); fields ((k, v) :: acc)
          | '}' -> incr pos; Assoc (List.rev ((k, v) :: acc))
          | _ -> raise (Error (Printf.sprintf "expected , or } at %d" !pos))
        in
        fields []
      end
    | '[' ->
      incr pos;
      ws ();
      if peek () = ']' then (incr pos; List [])
      else begin
        let rec items acc =
          let v = value () in
          ws ();
          match peek () with
          | ',' -> incr pos; items (v :: acc)
          | ']' -> incr pos; List (List.rev (v :: acc))
          | _ -> raise (Error (Printf.sprintf "expected , or ] at %d" !pos))
        in
        items []
      end
    | '"' -> String (string ())
    | 't' -> pos := !pos + 4; Bool true
    | 'f' -> pos := !pos + 5; Bool false
    | 'n' -> pos := !pos + 4; Null
    | _ -> number ()
  in
  value ()

let escape (b : Buffer.t) (s : string) =
  Buffer.add_char b '"';
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | '\r' -> Buffer.add_string b "\\r"
      | '\t' -> Buffer.add_string b "\\t"
      | c when Char.code c < 0x20 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c)
    s;
  Buffer.add_char b '"'

let rec write (b : Buffer.t) (v : t) =
  match v with
  | Null -> Buffer.add_string b "null"
  | Bool x -> Buffer.add_string b (if x then "true" else "false")
  | Int i -> Buffer.add_string b (string_of_int i)
  | Float f -> Buffer.add_string b (Printf.sprintf "%.17g" f)
  | String s -> escape b s
  | List xs ->
    Buffer.add_char b '[';
    List.iteri (fun i x -> if i > 0 then Buffer.add_char b ','; write b x) xs;
    Buffer.add_char b ']'
  | Assoc kvs ->
    Buffer.add_char b '{';
    List.iteri (fun i (k, x) -> if i > 0 then Buffer.add_char b ','; escape b k; Buffer.add_char b ':'; write b x) kvs;
    Buffer.add_char b '}'

let to_string v =
  let b = Buffer.create 4096 in
  write b v;
  Buffer.contents b

(* accessors *)
let member k = function Assoc kvs -> (try List.assoc k kvs with Not_found -> Null) | _ -> Null
let to_list = function List xs -> xs | Null -> [] | _ -> raise (Error "expected a list")
let to_str = function String s -> s | _ -> raise (Error "expected a string")
let to_int = function Int i -> i | Float f -> int_of_float f | _ -> raise (Error "expected an int")
let to_bool = function Bool b -> b | Null -> false | Int i -> i <> 0 | _ -> raise (Error "expected a bool")
let str_opt = function String s -> Some s | _ -> None
let is_null = function Null -> true | _ -> false
