open LambdaBox.Translations
open LambdaBox.EAst
open LambdaBox.ExAst
open LambdaBox.SerializeEAst
open LambdaBox.SerializeExAst
open LambdaBox.CheckWf
open Unicode
open Common
open PrintC.Caml_bytestring

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


let string_of_cstring = PrintC.Camlcoq.camlstring_of_coqstring
let cstring_of_string = PrintC.Camlcoq.coqstring_of_camlstring

let cprint_endline s =
  print_endline (string_of_cstring s)

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


let mk_tparams topts =
  TypedTransforms.mk_params topts.optimize topts.optimize

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

let mk_copts opts copts =
  LambdaBox.CertiCoqPipeline.make_opts copts.cps opts.debug

let convert_typed f n opt =
  let p = read_typed_ast f in
  match LambdaBox.SerializeCommon.kername_of_string (cstring_of_string n) with
  | Datatypes.Coq_inr kn ->
    let p =
      if opt
      then match TypedTransforms.typed_transfoms (mk_tparams {optimize = opt}) p with
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

let compile_wasm opts copts f =
  let p =
    match copts.typed with
    | Some n -> convert_typed f n copts.optimize
    | None -> read_ast f
  in
  check_wf_untyped opts p;
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

let compile_ocaml opts f =
  let p = read_ast f in
  check_wf_untyped opts p;
  let p = l_box_to_ocaml p in
  write_ocaml_res opts f p

let compile_rust opts topts f =
  let p = read_typed_ast f in
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
  let p = read_typed_ast f in
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

let eval_box opts copts anf f =
  let p = read_ast f in
  check_wf_untyped opts p;
  let p = Eval.eval (mk_copts opts copts) anf p in
  print_endline "Evaluating:";
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
  PrintC.PrintClight.print_dest_names_imports prog (Cps.M.elements names) dest imports'

let compile_c opts copts f =
  let p =
    match copts.typed with
    | Some n -> convert_typed f n copts.optimize
    | None -> read_ast f
  in
  check_wf_untyped opts p;
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

let compile_anf opts copts f =
  let p =
    match copts.typed with
    | Some n -> convert_typed f n copts.optimize
    | None -> read_ast f
  in
  check_wf_untyped opts p;
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
