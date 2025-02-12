open Lib.Translations
open Lib.EAst
open Lib.ExAst
open Lib.SerializeEAst
open Lib.SerializeExAst
open Lib.CheckWf
open Unicode
open Common
open Caml_bytestring


let read_file f =
  let c = open_in f in
  let s = really_input_string c (in_channel_length c) in
  close_in c;
  escape_unicode s

let parse_ast p s =
  let t = p (String.trim s) in
  match t with
  | Lib.Datatypes.Coq_inr t -> t
  | Lib.Datatypes.Coq_inl e ->
    let err_msg = Lib.CeresExtra.string_of_error true true e in
    print_endline "Failed parsing input program";
    print_endline err_msg;
    exit 1

let read_ast f : program =
  let s = read_file f in
  print_endline "Compiling:";
  (* print_endline s; *)
  parse_ast program_of_string s

let read_typed_ast f : global_env =
  let s = read_file f in
  print_endline "Compiling:";
  (* print_endline s; *)
  parse_ast global_env_of_string s


let get_out_file opts f ext =
  match opts.output_file with
  | Some f -> f
  | None -> (Filename.remove_extension f)^"."^ext

let write_res f p =
  let f = open_out f in
  p f;
  flush f;
  close_out f

let write_wasm_res opts f p =
  let f = get_out_file opts f "wasm" in
  let p = caml_string_of_bytestring p in
  write_res f (fun f -> output_string f p)

let write_elm_res opts f p =
  let f = get_out_file opts f "elm" in
  let p = unescape_unicode (caml_string_of_bytestring p) in
  write_res f (fun f -> output_string f p)

let write_rust_res opts f p =
  let f = get_out_file opts f "rs" in
  write_res f (fun f ->
    List.iter (fun s -> output_string f ((unescape_unicode (caml_string_of_bytestring s)) ^ "\n")) p)

let print_debug opts dbg =
  if opts.debug then
    (print_endline "Pipeline debug:";
    print_endline (caml_string_of_bytestring dbg))


let mk_tparams topts =
  Lib.TypedTransforms.mk_params topts.optimize topts.optimize

let check_wf checker flags opts p =
  if opts.bypass_wf then ()
  else
  print_endline "Checking program wellformedness";
  if checker flags p then ()
  else
    (print_endline "Program not wellformed";
    exit 1)

let check_wf_untyped =
  check_wf check_wf_program agda_eflags

let check_wf_typed =
  check_wf CheckWfExAst.check_wf_typed_program agda_typed_eflags

let compile_wasm opts f =
  let p = (read_ast f) in
  check_wf_untyped opts p;
  let p = l_box_to_wasm p in
  (* let p = Lib.LambdaBoxToWasm.show_IR p in *)
  match p with
  | (Lib.CompM.Ret prg, dbg) ->
    print_debug opts dbg;
    print_endline "Compiled successfully:";
    write_wasm_res opts f prg
  | (Lib.CompM.Err s, dbg) ->
    print_debug opts dbg;
    print_endline "Could not compile:";
    print_endline (caml_string_of_bytestring s);
    exit 1

let compile_rust opts topts f =
  let p = (read_typed_ast f) in
  check_wf_typed opts p;
  let p = l_box_to_rust p Lib.LambdaBoxToRust.default_remaps (mk_tparams topts) in
  match p with
  | Lib.ResultMonad.Ok prg ->
    print_endline "Compiled successfully:";
    write_rust_res opts f prg
  | Lib.ResultMonad.Err e ->
    print_endline "Could not compile:";
    print_endline (caml_string_of_bytestring e);
    exit 1

let compile_elm opts topts f =
  let p = (read_typed_ast f) in
  check_wf_typed opts p;
  let p = l_box_to_elm p Lib.LambdaBoxToElm.default_preamble Lib.LambdaBoxToElm.default_remaps (mk_tparams topts) in
  match p with
  | Lib.ResultMonad.Ok prg ->
    print_endline "Compiled successfully:";
    write_elm_res opts f prg
  | Lib.ResultMonad.Err e ->
    print_endline "Could not compile:";
    print_endline (caml_string_of_bytestring e);
    exit 1




let eval_box opts f =
  let p = (read_ast f) in
  check_wf_untyped opts p;
  let p = Lib.Eval.eval_box p  in
  print_endline "Evaluating:";
  match p with
  | (Lib.ExceptionMonad.Ret t) ->
    print_endline "Evaluated program to:";
    print_endline (caml_string_of_bytestring t)
  | (Lib.ExceptionMonad.Exc e) ->
    print_endline "Could not evaluate program:";
    print_endline (caml_string_of_bytestring e);
    exit 1
