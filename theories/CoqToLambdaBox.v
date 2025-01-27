From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import Loader.
From MetaCoq.ErasurePlugin Require Import Erasure.
From MetaCoq.ErasurePlugin Require Import Loader.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Erasure.Typed Require Import Optimize.
From MetaCoq.Erasure.Typed Require Import Extraction.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import String.

Import MCMonadNotation.
Import ListNotations.

Local Open Scope string.
Local Notation "'bs_to_s' s" := (bytestring.String.to_string s) (at level 200).
Local Notation "'s_to_bs' s" := (bytestring.String.of_string s) (at level 200).



Program Definition cic_to_box p :=
  run_erase_program default_erasure_config ([], p) _.
Next Obligation.
  split. easy.
  split.
  now eapply assume_that_we_only_erase_on_welltyped_programs.
  cbv [PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn].
  pose proof @PCUICSN.normalization.
  split; typeclasses eauto.
Qed.

Definition no_check_args :=
  {| check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     template_transforms := [];
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [dearg_transform (fun _ => None) true true false false false] |} |}.

Definition cic_to_box_typed p :=
  entry <- match p.2 with
           | tConst kn _ => Ok kn
           | tInd ind _ => Ok (inductive_mind ind)
           | _ => Err (s_to_bs "Expected program to be a tConst or tInd")
           end;;
  Σ <- extract_template_env
         no_check_args
         p.1
         (KernameSet.singleton entry)
         (fun k => false);;
  Ok Σ.



(* Example term *)
(* Definition t (X : Type) (x : X) := x. *)

(* Translate Coq def -> lambda_cic *)
(* MetaCoq Quote Recursively Definition ex1 := t. *)

(* Translate lambda_cic -> lambda_box *)
(* Eval vm_compute in cic_to_box ex1. *)

(* Translate lambda_cic -> lambda_boxtyped *)
(* Note that this only translates the environment *)
(* Eval vm_compute in cic_to_box_typed ex1. *)
