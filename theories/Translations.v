From MetaCoq.Erasure Require EAst.
From CertiCoq Require Import LambdaBoxMut.compile.
From CertiCoq Require Import LambdaBoxLocal.toplevel.
From CertiCoq Require Import LambdaANF.toplevel.
From CertiCoq Require Import Compiler.pipeline.
From CertiCoq Require Import CodegenWasm.toplevel.
Require Import ExtLib.Structures.Monad.
From Coq Require Import List.
From Coq Require Import ZArith.

Import ListNotations.
Import Monads.
Import MonadNotation.

From CertiCoq Require Import Common.Common Common.compM Common.Pipeline_utils.
From Wasm Require Import binary_format_printer.


Definition print_wasm p := (String.parse (binary_of_module p)).

Definition box_to_wasm (p : EAst.program) :=
    (* For simplicity we assume that the program contains no primitives *)
    let prims := [] in
    let next_id := 100%positive in
    let opts := default_opts in
    (* Translate lambda_box -> lambda_boxmut *)
    let p_mut := {| CertiCoq.Common.AstCommon.main := LambdaBoxMut.compile.compile (snd p) ; CertiCoq.Common.AstCommon.env := LambdaBoxMut.compile.compile_ctx (fst p) |} in
    check_axioms prims p_mut;;
    (* Translate lambda_boxmut -> lambda_boxlocal *)
    p_local <- compile_LambdaBoxLocal prims p_mut;;
    (* Translate lambda_boxlocal -> lambda_anf *)
    p_anf <- compile_LambdaANF_ANF next_id prims p_local;;
    (* Translate lambda_anf -> lambda_anf *)
    p_anf <- compile_LambdaANF next_id p_anf;;
    (* Compile lambda_anf -> WASM *)
    p_wasm <- compile_LambdaANF_to_Wasm prims p_anf;;
    ret (print_wasm p_wasm).

Definition run_translation (p : EAst.program) :=
    run_pipeline EAst.program string default_opts p box_to_wasm.



(* Eval vm_compute in run_translation ([], tLambda (nNamed "x") (tRel 0)). *)
