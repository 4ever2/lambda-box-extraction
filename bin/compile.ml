open LambdaBox.Translations
open LambdaBox.EAst
open LambdaBox.ExAst
open LambdaBox.SerializeEAst
open LambdaBox.SerializeExAst
open LambdaBox.CheckWf
open Unicode
open Common
open Caml_bytestring

module Datatypes = LambdaBox.Datatypes
module CeresExtra = LambdaBox.CeresExtra
module TypedTransforms = LambdaBox.TypedTransforms
module LambdaBoxToWasm = LambdaBox.LambdaBoxToWasm
module LambdaBoxToRust = LambdaBox.LambdaBoxToRust
module LambdaBoxToElm = LambdaBox.LambdaBoxToElm
module CompM = LambdaBox.CompM
module ResultMonad = LambdaBox.ResultMonad
module ExceptionMonad = LambdaBox.ExceptionMonad
module Cps = LambdaBox.Cps
module Eval = LambdaBox.Eval


let read_file f =
  let c = open_in f in
  let s = really_input_string c (in_channel_length c) in
  close_in c;
  escape_unicode s

let parse_ast p s =
  let t = p (String.trim s) in
  match t with
  | Datatypes.Coq_inr t -> t
  | Datatypes.Coq_inl e ->
    let err_msg = CeresExtra.string_of_error true true e in
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
  TypedTransforms.mk_params topts.optimize topts.optimize

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
  (* let p = LambdaBoxToWasm.show_IR p in *)
  match p with
  | (CompM.Ret prg, dbg) ->
    print_debug opts dbg;
    print_endline "Compiled successfully:";
    write_wasm_res opts f prg
  | (CompM.Err s, dbg) ->
    print_debug opts dbg;
    print_endline "Could not compile:";
    print_endline (caml_string_of_bytestring s);
    exit 1

let compile_rust opts topts f =
  let p = (read_typed_ast f) in
  check_wf_typed opts p;
  let p = l_box_to_rust p LambdaBoxToRust.default_remaps (mk_tparams topts) in
  match p with
  | ResultMonad.Ok prg ->
    print_endline "Compiled successfully:";
    write_rust_res opts f prg
  | ResultMonad.Err e ->
    print_endline "Could not compile:";
    print_endline (caml_string_of_bytestring e);
    exit 1

let compile_elm opts topts f =
  let p = (read_typed_ast f) in
  check_wf_typed opts p;
  let p = l_box_to_elm p LambdaBoxToElm.default_preamble LambdaBoxToElm.default_remaps (mk_tparams topts) in
  match p with
  | ResultMonad.Ok prg ->
    print_endline "Compiled successfully:";
    write_elm_res opts f prg
  | ResultMonad.Err e ->
    print_endline "Could not compile:";
    print_endline (caml_string_of_bytestring e);
    exit 1

let eval_box opts f =
  let p = (read_ast f) in
  check_wf_untyped opts p;
  let p = Eval.eval_box p  in
  print_endline "Evaluating:";
  match p with
  | (ExceptionMonad.Ret t) ->
    print_endline "Evaluated program to:";
    print_endline (caml_string_of_bytestring t)
  | (ExceptionMonad.Exc e) ->
    print_endline "Could not evaluate program:";
    print_endline (caml_string_of_bytestring e);
    exit 1

let printCProg prog names (dest : string) (imports : import list) =
  let imports' = List.map (fun i -> match i with
    | FromRelativePath s -> "#include \"" ^ s ^ "\""
    | FromLibrary (s, _) -> "#include <" ^ s ^ ">"
    | FromAbsolutePath _ ->
        failwith "Import with absolute path should have been filled") imports in
  PrintC.PrintClight.print_dest_names_imports prog (Cps.M.elements names) dest imports'

let compile_c opts f =
  let p = (read_ast f) in
  check_wf_untyped opts p;
  let p = l_box_to_c p in
  (* let p = LambdaBoxToWasm.show_IR p in *)
  match p with
  | (CompM.Ret ((nenv, header), prg), dbg) ->
    print_debug opts dbg;
    print_endline "Compiled successfully:";
    (* let runtime_imports = [FromLibrary ((if opts.cps then "gc.h" else "gc_stack.h"), None)] in *)
    let runtime_imports = [FromLibrary (("gc_stack.h"), None)] in
    let imports = runtime_imports in
    let hstr  = "test.h" in
    let cstr' = "test.c" in
    let hstr' = "test.h" in
    printCProg prg nenv cstr' (imports @ [FromRelativePath hstr]);
    printCProg header nenv hstr' (runtime_imports);
  | (CompM.Err s, dbg) ->
    print_debug opts dbg;
    print_endline "Could not compile:";
    print_endline (caml_string_of_bytestring s);
    exit 1
