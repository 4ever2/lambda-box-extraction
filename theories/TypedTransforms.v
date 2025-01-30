From Coq Require Import List.
From Coq Require Import String.
From MetaCoq.Utils Require Import bytestring.
From MetaCoq.Utils Require Import monad_utils.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Erasure Require Import ExAst.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Erasure.Typed Require Import Extraction.
From MetaCoq.Erasure.Typed Require Import Transform.
From MetaCoq.Erasure.Typed Require Import Optimize.


Import ListNotations.
Import MCMonadNotation.

Local Open Scope bs_scope.

Definition mk_params (opt dearg : bool) :=
  {| optimize_prop_discr := opt;
     extract_transforms := if dearg then [dearg_transform (fun _ => None) true true true true false] else []
  |}.

Definition no_dearg :=
  {| optimize_prop_discr := false;
     extract_transforms := []
  |}.

Definition default_params :=
  {| optimize_prop_discr := true;
     extract_transforms := [dearg_transform (fun _ => None) true true true true false]
  |}.

Program Definition typed_transfoms (params : extract_pcuic_params)
                                   (Σ : global_env)
                                   : result ExAst.global_env _ :=
  if optimize_prop_discr params then
    let Σ := MetaCoq.Erasure.Typed.Utils.timed "Removal of prop discrimination" (fun _ => OptimizePropDiscr.remove_match_on_box_env Σ _) in
    compose_transforms (extract_transforms params) Σ
  else
    Ok Σ.
Next Obligation.
  admit.
Admitted.
