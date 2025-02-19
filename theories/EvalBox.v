(* This file provides utilises to evaluate lambda box programs *)

From Coq Require Import Nat.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Erasure Require Import EAst.
From CertiCoq.Common Require Import Common.
From CertiCoq.Common Require Import Pipeline_utils.
From CertiCoq.LambdaBoxMut Require Import compile.
From CertiCoq.LambdaBoxMut Require Import term.
From CertiCoq.LambdaBoxMut Require Import program.
From CertiCoq.LambdaBoxMut Require Import wcbvEval.
From CertiCoq.LambdaANF Require Import toplevel.
From CertiCoq.LambdaANF Require Import eval.
From CertiCoq.LambdaANF Require Import cps.
From LambdaBox Require Import CertiCoqPipeline.
From ExtLib.Structures Require Import Monad.

Import MonadNotation.



Definition next_id := 100%positive.
Definition fuel := (2^18)%nat.

Definition box_to_mut (p : EAst.program) : pipelineM (Program Term) :=
  ret {|
    CertiCoq.Common.AstCommon.env  := LambdaBoxMut.compile.compile_ctx (fst p);
    CertiCoq.Common.AstCommon.main := compile (snd p);
  |}.

Definition box_to_anf (p : EAst.program) :=
  let genv := fst p in
  '(prs, next_id) <- register_prims next_id genv;; (* TODO: better prim registration *)
  anf_pipeline p prs next_id.

Definition eval_box (n : nat) (p : Program Term) : pipelineM string :=
  match wcbvEval (AstCommon.env p) n (main p) with
  | Ret p => ret (print_term p)
  | Exc s => compM.failwith ("Could not evaluate program:\n" ^ s)
  end.

Definition eval_anf (n : nat) (p : LambdaANF_FullTerm) : pipelineM string :=
  let (env, p) := p in
  let '(prims, _, ctor_env, _, _, nenv, _, env) := env in
  match bstep_f prims ctor_env env p n with
  | Ret (inl (_, e)) => ret (cps_show.show_exp nenv ctor_env true e)
  | Ret (inr v) => ret (cps_show.show_val nenv ctor_env true v)
  | Exc s => compM.failwith ("Could not evaluate program:\n" ^ s)
  end.

Definition eval (opts : Options) (anf : bool) (p : EAst.program) : compM.error string * string :=
  let pipeline p :=
    if anf
    then
      p <- box_to_anf p;;
      eval_anf fuel p
    else
      p <- box_to_mut p;;
      eval_box fuel p
  in
  run_pipeline EAst.program string opts p pipeline.
