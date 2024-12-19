let rec caml_bytestring_length_aux s acc =
  match s with
  | Lib.Bytestring.String.EmptyString -> acc
  | Lib.Bytestring.String.String (_, s) -> caml_bytestring_length_aux s (succ acc)

let caml_bytestring_length s = caml_bytestring_length_aux s 0

let caml_string_of_bytestring (l : Lib.Bytestring.String.t) : string =
  let len = caml_bytestring_length l in
  let buf = Bytes.create len in
  let rec aux i = function
    | Lib.Bytestring.String.EmptyString -> ()
    | Lib.Bytestring.String.String (c, cs) ->
      Bytes.set buf i (Caml_byte.char_of_byte c); aux (succ i) cs
  in
  aux 0 l;
  Bytes.to_string buf

let bytestring_of_caml_string (s : string) : Lib.Bytestring.String.t =
  let rec aux acc i =
    if i < 0 then acc
    else aux (Lib.Bytestring.String.String (Caml_byte.byte_of_char s.[i], acc)) (i - 1)
  in aux Lib.Bytestring.String.EmptyString (String.length s - 1)
