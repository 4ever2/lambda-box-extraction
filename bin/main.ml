open Lib.Translations
open Lib.EAst
open Lib.SerializeEAst



let read_ast f : term =
  let c = open_in f in
  let s = really_input_string c (in_channel_length c) in
  close_in c;
  print_endline "Compiling:";
  print_endline s;
  let s = s |> String.trim |> String.to_seq |> List.of_seq in
  let t = term_of_string s in
  match t with
  | Lib.Datatypes.Coq_inr t -> t
  | _ -> failwith "Could not parse s-expr"

let write_wasm f p =
  let f = open_out f in
  let p = Caml_bytestring.caml_string_of_bytestring p in
  output_string f p;
  flush f;
  close_out f

let p = run_translation ([], (read_ast "test.ast"))
let () =
  match p with
  | (Lib.CompM.Ret prg, dbg) ->
    print_endline "Pipeline debug:";
    print_endline (Caml_bytestring.caml_string_of_bytestring dbg);
    print_endline "Compiled successfully:";
    write_wasm "test.wasm" prg
  | (Lib.CompM.Err s, dbg) ->
    print_endline "Pipeline debug:";
    print_endline (Caml_bytestring.caml_string_of_bytestring dbg);
    print_endline "Could not compile:";
    print_endline (Caml_bytestring.caml_string_of_bytestring s)
