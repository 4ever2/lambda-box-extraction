open LambdaBox.Translations
open LambdaBox.EAst
open LambdaBox.ExAst
open LambdaBox.SerializeEAst
open LambdaBox.SerializeExAst
open LambdaBox.CheckWf
open Unicode
open Common
open LambdaBox.Caml_bytestring

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
module Eval = LambdaBox.EvalBox


let string_of_cstring = LambdaBox.Camlcoq.camlstring_of_coqstring
let cstring_of_string = LambdaBox.Camlcoq.coqstring_of_camlstring

let cprint_endline s =
  print_endline (string_of_cstring s)

let mk_tparams eopts =
  TypedTransforms.mk_params eopts.optimize eopts.optimize

let convert_typed kn opt p =
  match LambdaBox.SerializeCommon.kername_of_string (cstring_of_string kn) with
  | Datatypes.Coq_inr kn ->
    let p =
      if opt
      then match TypedTransforms.typed_transfoms (mk_tparams (mk_typed_erasure_opts opt)) p with
           | ResultMonad.Ok p -> p
           | ResultMonad.Err e ->
             print_endline "Failed optimizing:";
             print_endline (caml_string_of_bytestring e);
             exit 1
      else p
    in
    (LambdaBox.ExAst.trans_env p, LambdaBox.EAst.Coq_tConst kn)
  | Datatypes.Coq_inl e ->
    let err_msg = CeresExtra.string_of_error true true e in
    print_endline "Failed parsing kername";
    cprint_endline err_msg;
    exit 1

let check_wf checker flags opts p =
  if opts.bypass_wf then ()
  else
  (print_endline "Checking program wellformedness";
  if checker flags p then ()
  else
    (print_endline "Program not wellformed";
    exit 1))

let check_wf_untyped =
  check_wf check_wf_program agda_eflags

let check_wf_typed =
  check_wf CheckWfExAst.check_wf_typed_program agda_typed_eflags

let read_file f =
  let c = open_in f in
  let s = really_input_string c (in_channel_length c) in
  close_in c;
  escape_unicode s

let parse_ast p s =
  let t = p (cstring_of_string (String.trim s)) in
  match t with
  | Datatypes.Coq_inr t -> t
  | Datatypes.Coq_inl e ->
    let err_msg = CeresExtra.string_of_error true true e in
    print_endline "Failed parsing input program";
    cprint_endline err_msg;
    exit 1

let get_ast opts eopts f : program =
  let s = read_file f in
  print_endline "Parsing AST:";
  match eopts.typed with
  | None ->
    let p = parse_ast program_of_string s in
    check_wf_untyped opts p;
    p
  | Some kn ->
    let p = parse_ast global_env_of_string s in
    check_wf_typed opts p;
    convert_typed kn eopts.optimize p

let get_typed_ast opts f : global_env =
  let s = read_file f in
  print_endline "Parsing AST:";
  let p = parse_ast global_env_of_string s in
  check_wf_typed opts p;
  p


let get_out_file opts f ext =
  match opts.output_file with
  | Some f -> f
  | None -> (Filename.remove_extension f)^"."^ext

let get_header_file opts f =
  match opts.output_file with
  | Some f -> (Filename.remove_extension f)^".h"
  | None -> (Filename.remove_extension f)^".h"

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

let write_anf_res opts f p =
  let f = get_out_file opts f "anf" in
  let p = caml_string_of_bytestring p in
  write_res f (fun f -> output_string f p)

let write_ocaml_res opts f p =
  let f = get_out_file opts f "mlf" in
  write_res f (fun f ->
    output_string f (caml_string_of_bytestring (snd p)))

let print_debug opts dbg =
  if opts.debug then
    (print_endline "Pipeline debug:";
    print_endline (caml_string_of_bytestring dbg))



let mk_copts opts copts =
  LambdaBox.CertiCoqPipeline.make_opts copts.cps opts.debug

let compile_wasm opts eopts copts f =
  let p = get_ast opts eopts f in
  print_endline "Compiling:";
  let p = LambdaBox.ErasurePipeline.implement_box agda_eflags p in
  let p = l_box_to_wasm (mk_copts opts copts) p in
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

let compile_ocaml opts eopts f =
  let p = get_ast opts eopts f in
  print_endline "Compiling:";
  l_box_to_ocaml p |>
  write_ocaml_res opts f

let compile_rust opts eopts f =
  let p = get_typed_ast opts f in
  print_endline "Compiling:";
  let p = l_box_to_rust LambdaBoxToRust.default_remaps (mk_tparams eopts) p in
  match p with
  | ResultMonad.Ok prg ->
    print_endline "Compiled successfully:";
    write_rust_res opts f prg
  | ResultMonad.Err e ->
    print_endline "Could not compile:";
    print_endline (caml_string_of_bytestring e);
    exit 1

let compile_elm opts eopts f =
  let p = get_typed_ast opts f in
  print_endline "Compiling:";
  let p = l_box_to_elm LambdaBoxToElm.default_preamble LambdaBoxToElm.default_remaps (mk_tparams eopts) p in
  match p with
  | ResultMonad.Ok prg ->
    print_endline "Compiled successfully:";
    write_elm_res opts f prg
  | ResultMonad.Err e ->
    print_endline "Could not compile:";
    print_endline (caml_string_of_bytestring e);
    exit 1

let eval_box opts eopts copts anf f =
  let p = get_ast opts eopts f in
  print_endline "Evaluating:";
  let p = LambdaBox.ErasurePipeline.implement_box agda_eflags p in
  let p = Eval.eval (mk_copts opts copts) anf p in
  match p with
  | (CompM.Ret t, dbg) ->
    print_debug opts dbg;
    print_endline "Evaluated program to:";
    print_endline (caml_string_of_bytestring t)
  | (CompM.Err s, dbg) ->
    print_debug opts dbg;
    print_endline "Could not compile:";
    print_endline (caml_string_of_bytestring s);
    exit 1

let printCProg prog names (dest : string) (imports : import list) =
  let imports' = List.map (fun i -> match i with
    | FromRelativePath s -> "#include \"" ^ s ^ "\""
    | FromLibrary (s, _) -> "#include <" ^ s ^ ">"
    | FromAbsolutePath _ ->
        failwith "Import with absolute path should have been filled") imports in
  LambdaBox.PrintClight.print_dest_names_imports prog (Cps.M.elements names) dest imports'

let compile_c opts eopts copts f =
  let p = get_ast opts eopts f in
  print_endline "Compiling:";
  let p = LambdaBox.ErasurePipeline.implement_box agda_eflags p in
  let p = l_box_to_c (mk_copts opts copts) p in
  match p with
  | (CompM.Ret ((nenv, header), prg), dbg) ->
    print_debug opts dbg;
    print_endline "Compiled successfully:";
    let runtime_imports = [FromLibrary ((if copts.cps then "gc.h" else "gc_stack.h"), None)] in
    let imports = runtime_imports in
    let cstr = get_out_file opts f "c" in
    let hstr = get_header_file opts f in
    printCProg prg nenv cstr (imports @ [FromRelativePath hstr]);
    printCProg header nenv hstr (runtime_imports);
  | (CompM.Err s, dbg) ->
    print_debug opts dbg;
    print_endline "Could not compile:";
    print_endline (caml_string_of_bytestring s);
    exit 1

let compile_anf opts eopts copts f =
  let p = get_ast opts eopts f in
  print_endline "Compiling:";
  let p = LambdaBox.ErasurePipeline.implement_box agda_eflags p in
  let p = LambdaBox.CertiCoqPipeline.show_IR (mk_copts opts copts) p in
  match p with
  | (CompM.Ret prg, dbg) ->
    print_debug opts dbg;
    print_endline "Compiled successfully:";
    write_anf_res opts f prg
  | (CompM.Err s, dbg) ->
    print_debug opts dbg;
    print_endline "Could not compile:";
    print_endline (caml_string_of_bytestring s);
    exit 1
