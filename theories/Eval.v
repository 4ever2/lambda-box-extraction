(* This file provides utilises to evaluate lambda box programs *)

From Coq Require Import Nat.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Erasure Require Import EAst.
From CertiCoq.Common Require Import Common.
From CertiCoq.LambdaBoxMut Require Import compile.
From CertiCoq.LambdaBoxMut Require Import term.
From CertiCoq.LambdaBoxMut Require Import program.
From CertiCoq.LambdaBoxMut Require Import wcbvEval.



(* convert a lambda box program to certicoq lambda box mut, and run it *)

Definition box_to_mut (p : EAst.program) := {|
    env  := LambdaBoxMut.compile.compile_ctx (fst p);
    main := compile (snd p);
  |}.

Definition eval_box (p : EAst.program) : exception string :=
  let p := box_to_mut p in
  do p <- wcbvEval (env p) (2^18) (main p);
  ret (print_term p).

Definition eval_box_typed (p : ExAst.global_env) kn : exception string :=
  let p := (ExAst.trans_env p, tConst kn) in
  let p := box_to_mut p in
  do p <- wcbvEval (env p) (2^18) (main p);
  ret (print_term p).
