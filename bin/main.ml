open Lib.Translations
open Lib.EAst
open Lib2.SerializeEAst




external convertTerm : Lib2.EAst.term -> term = "%identity"

let read_ast f : term =
  let c = open_in f in
  let s = really_input_string c (in_channel_length c) in
  close_in c;
  print_endline "Compiling:";
  print_endline s;
  (* Lib.EAst.term_of_sexp (Sexplib.Sexp.of_string (String.trim s)) *)
  let s = s |> String.trim |> String.to_seq |> List.of_seq in
  let t = term_of_string s in
  match t with
  | Lib2.Datatypes.Coq_inr t -> convertTerm t
  | _ -> failwith "Could not parse s-expr"

let write_wasm f p =
  let f = open_out f in
  let p = Caml_bytestring.caml_string_of_bytestring p in
  output_string f p;
  flush f;
  close_out f

(* let x : Lib.Kernames.ident = Lib.Caml_bytestring.bytestring_of_caml_string "x"
let zero : Lib.Datatypes.nat = Lib.Datatypes.O

let _ = (Coq_tLambda ((Coq_nNamed x), (Coq_tRel zero))) |>
  Lib.EAst.sexp_of_term |>
  Sexplib.Sexp.to_string|>
  print_endline *)

(* let p = run_translation ([], Coq_tLambda ((Coq_nNamed x), (Coq_tRel zero))) *)
let p = run_translation ([], (read_ast "test.ast"))
let () =
  match p with
  | (Lib.CompM.Ret prg, dbg) ->
  (* | (Lib.CompM.Ret _, dbg) -> *)
    print_endline "Pipeline debug:";
    print_endline (Caml_bytestring.caml_string_of_bytestring dbg);
    print_endline "Compiled successfully:";
    write_wasm "test.wasm" prg
(*     debug_msg debug "Finished compiling, printing to file.";
    let time = Unix.gettimeofday() in
    let suff = opts.ext in
    let fname = opts.filename in
    let file = fname ^ suff ^ ".wasm" in
    print_to_file_no_nl (string_of_bytestring prg) file;
    let time = (Unix.gettimeofday() -. time) in
    debug_msg debug (Printf.sprintf "Printed to file %s in %f s.." file time);
    debug_msg debug "Pipeline debug:";
    debug_msg debug (string_of_bytestring dbg) *)
  (* | (Lib.CompM.Err s, dbg) -> *)
  | (Lib.CompM.Err s, dbg) ->
    print_endline "Pipeline debug:";
    print_endline (Caml_bytestring.caml_string_of_bytestring dbg);
    print_endline "Could not compile:";
    print_endline (Caml_bytestring.caml_string_of_bytestring s)
