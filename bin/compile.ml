open Lib.Translations
open Lib.EAst
open Lib.ExAst
open Lib.SerializeEAst
open Lib.SerializeExAst


type verbose = Normal | Quiet | Verbose

type copts = {verbose: verbose; debug: bool; output_file: string option}
let mk_copts verbose debug output_file = { verbose; debug; output_file }

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

let read_ast f : program =
  let c = open_in f in
  let s = really_input_string c (in_channel_length c) in
  let s = escape_unicode s in
  close_in c;
  print_endline "Compiling:";
  print_endline s;
  let t = program_of_string (String.trim s) in
  match t with
  | Lib.Datatypes.Coq_inr t -> t
  | Lib.Datatypes.Coq_inl e ->
    let err_msg = Lib.CeresExtra.string_of_error true true e in
    print_endline "Failed parsing input program";
    print_endline err_msg;
    exit 1

let read_typed_ast f : global_env =
  let c = open_in f in
  let s = really_input_string c (in_channel_length c) in
  let s = escape_unicode s in
  close_in c;
  print_endline "Compiling:";
  print_endline s;
  let t = global_env_of_string (String.trim s) in
  match t with
  | Lib.Datatypes.Coq_inr t -> t
  | Lib.Datatypes.Coq_inl e ->
    let err_msg = Lib.CeresExtra.string_of_error true true e in
    print_endline "Failed parsing input program";
    print_endline err_msg;
    exit 1

let get_out_file opts f ext =
  let out_f =
    match opts.output_file with
    | Some f -> f
    | None -> (Filename.remove_extension f)^"."^ext
  in
  open_out out_f

let write_wasm_res opts f p =
  let f = get_out_file opts f "wasm" in
  let p = Caml_bytestring.caml_string_of_bytestring p in
  output_string f p;
  flush f;
  close_out f

let write_rust_res opts f p =
  let f = get_out_file opts f "rs" in
  List.iter (fun s -> output_string f ((unescape_unicode (Caml_bytestring.caml_string_of_bytestring s)) ^ "\n")) p;
  flush f;
  close_out f

let print_debug opts dbg =
  if opts.debug then
    (print_endline "Pipeline debug:";
    print_endline (Caml_bytestring.caml_string_of_bytestring dbg))

let compile_wasm opts f =
  let p = l_box_to_wasm (read_ast f) in
  match p with
  | (Lib.CompM.Ret prg, dbg) ->
    print_debug opts dbg;
    print_endline "Compiled successfully:";
    write_wasm_res opts f prg
  | (Lib.CompM.Err s, dbg) ->
    print_debug opts dbg;
    print_endline "Could not compile:";
    print_endline (Caml_bytestring.caml_string_of_bytestring s)

let compile_rust opts f =
  let p = l_box_to_rust (read_typed_ast f) Lib.LambdaBoxToRust.default_remaps in
  match p with
  | Lib.ResultMonad.Ok prg ->
    print_endline "Compiled successfully:";
    write_rust_res opts f prg
  | Lib.ResultMonad.Err e ->
    print_endline "Could not compile:";
    print_endline (Caml_bytestring.caml_string_of_bytestring e)
