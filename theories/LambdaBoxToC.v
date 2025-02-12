From MetaCoq.Erasure Require EAst.
From CertiCoq Require Import LambdaBoxMut.compile.
From CertiCoq Require Import LambdaBoxLocal.toplevel.
From CertiCoq Require Import LambdaANF.toplevel.
From CertiCoq Require Import Compiler.pipeline.
From CertiCoq Require Import Common.Common.
From CertiCoq Require Import Common.compM.
From CertiCoq Require Import Common.Pipeline_utils.
From ExtLib.Structures Require Import Monad.
From Coq Require Import List.
From Coq Require Import ZArith.

Import ListNotations.
Import Monads.
Import MonadNotation.




Definition default_opts : Options :=
  {| erasure_config := Erasure.default_erasure_config;
     inductives_mapping := [];
     direct := true;
     c_args := 5;
     anf_conf := 0;
     show_anf := false;
     o_level := 0;
     time := false;
     time_anf := false;
     debug := false;
     dev := 0;
     Pipeline_utils.prefix := "";
     Pipeline_utils.body_name := "body";
     prims := [];
  |}.

Definition box_to_c (p : EAst.program) :=
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
    (* p_anf <- compile_LambdaANF_CPS next_id prims p_local;; *)
    (* Translate lambda_anf -> lambda_anf *)
    p_anf <- compile_LambdaANF next_id p_anf;;
    compile_Clight prims p_anf.

Definition run_translation (p : EAst.program) :=
    run_pipeline EAst.program Cprogram default_opts p box_to_c.
