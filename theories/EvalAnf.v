(* This file provides utilises to evaluate lambda box programs *)

From Coq Require Import Nat.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Erasure Require Import EAst.
From CertiCoq.Common Require Import Common.
From CertiCoq.LambdaANF Require Import toplevel.
From CertiCoq.LambdaANF Require Import eval.
From CertiCoq.LambdaANF Require Import cps.


Definition eval_anf (p : LambdaANF_FullTerm) : exception ((env * exp) + val) :=
  let '(env, p) := p in
  let '(prims, _, ctor_env, _, _, _, _, env) := env in
  bstep_f prims ctor_env env p (2^18).

Definition next_id := 100%positive.

From ExtLib.Structures Require Import Monad.
Import MonadNotation.
From LambdaBox Require Import CertiCoqPipeline.
From CertiCoq Require Import Common.Pipeline_utils.



Definition eval_box opts (p : EAst.program) :=
  let eval p :=
    let genv := fst p in
    '(prs, next_id) <- register_prims next_id genv ;; (* TODO: better prim registration *)
    p_anf <- anf_pipeline p prs next_id;;
    ret (eval_anf p_anf, p_anf) in
  let (perr, log) := run_pipeline _ _ opts p eval in
  match perr with
  | compM.Ret (Ret (inl e), p) =>
    let '(pr, cenv, _, _, nenv, fenv, _,  e) := p in
    (compM.Ret (cps_show.show_exp nenv cenv true e), log)
  | compM.Ret (Ret (inr v), p) =>
    let '(pr, cenv, _, _, nenv, fenv, _,  _) := p in
    (compM.Ret (cps_show.show_val nenv cenv true v), log)
  | compM.Ret (Exc s, _) => (compM.Err s, log)
  | compM.Err s => (compM.Err s, log)
  end.
