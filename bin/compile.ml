open Lib.Translations
open Lib.EAst
open Lib.SerializeEAst


type verbose = Normal | Quiet | Verbose

type copts = {verbose: verbose; debug: bool; output_file: string option}
let mk_copts verbose debug output_file = { verbose; debug; output_file }

let read_ast f : program =
  let c = open_in f in
  let s = really_input_string c (in_channel_length c) in
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

let write_res opts f p =
  let out =
    match opts.output_file with
    | Some f -> f
    | None -> (Filename.remove_extension f)^".wasm"
    in
  let f = open_out out in
  let p = Caml_bytestring.caml_string_of_bytestring p in
  output_string f p;
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
    write_res opts f prg
  | (Lib.CompM.Err s, dbg) ->
    print_debug opts dbg;
    print_endline "Could not compile:";
    print_endline (Caml_bytestring.caml_string_of_bytestring s)
