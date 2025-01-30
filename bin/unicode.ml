let hex_of_int i =
  i |> int_of_string |> Printf.sprintf "%X"

let utf8encode s =
    let prefs = [| 0x0; 0xc0; 0xe0 |] in
    let s1 n = String.make 1 (Char.chr n) in
    let rec ienc k sofar resid =
        let bct = if k = 0 then 7 else 6 - k in
        if resid < 1 lsl bct then
            (s1 (prefs.(k) + resid)) ^ sofar
        else
            ienc (k + 1) (s1 (0x80 + resid mod 64) ^ sofar) (resid / 64)
    in
    ienc 0 "" (int_of_string ("0x" ^ s))

let unescape_unicode s =
  let re = Str.regexp "\\\\[0-9][0-9][0-9]+" in
  let subst = function
  | Str.Delim s ->
    let s = String.sub s 1 (String.length s - 1) in
    utf8encode (hex_of_int s)
  | Str.Text s -> s
  in
  String.concat "" (List.map subst (Str.full_split re s))

let escape_unicode s =
  let re = Str.regexp "\\\\[0-9][0-9][0-9]+" in
  let subst = function
  | Str.Delim s -> "\\"^s
  | Str.Text s -> s
  in
  String.concat "" (List.map subst (Str.full_split re s))
