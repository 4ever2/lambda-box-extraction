From LambdaBox Require Import SerializePrimitives.
From LambdaBox Require Import CeresExtra.
From Ceres Require Import CeresRoundtrip.
From Ceres Require Import CeresSerialize.
From Ceres Require Import CeresDeserialize.
From MetaCoq.Common Require Import Primitive.
From MetaCoq.Erasure Require Import EPrimitive.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import ZArith_base.
From Coq Require Import String.
From Coq Require PrimInt63.
From Coq Require PrimFloat.



(* TODO: validate axioms *)
Axiom prim_int_ser_complete : forall x, (prim_int_of_string (string_of_prim_int x)) = x.
Axiom prim_float_ser_complete : forall x, (prim_float_of_string (string_of_prim_float x)) = x.



Instance Complete_prim_tag : CompleteClass prim_tag.
Proof.
  unfold CompleteClass, Complete.
  intros l x.
  destruct x; reflexivity.
Qed.

Instance Complete_prim_int : CompleteClass PrimInt63.int.
Proof.
  unfold CompleteClass, Complete.
  intros l x.
  cbn.
  rewrite prim_int_ser_complete.
  reflexivity.
Qed.

Instance Complete_prim_float : CompleteClass PrimFloat.float.
Proof.
  unfold CompleteClass, Complete.
  intros l x.
  cbn.
  rewrite prim_float_ser_complete.
  reflexivity.
Qed.

Instance Complete_array_model {T : Set} `{CompleteClass T} : CompleteClass (array_model T).
Proof.
  unfold CompleteClass, Complete.
  intros l a.
  cbn.
  rewrite !eqb_ascii_refl.
  rewrite complete_class.
  rewrite complete_class_list.
  destruct a; cbn.
  reflexivity.
Qed.

Instance Complete_prim_val {T : Set} `{CompleteClass T} : CompleteClass (prim_val T).
Proof.
  unfold CompleteClass, Complete.
  intros l p.
  destruct p.
  destruct p.
  - cbn -[Deserialize_prim_int].
    rewrite !eqb_ascii_refl.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_prim_float].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_array_model].
    rewrite !eqb_ascii_refl.
    rewrite !neqb_ascii_neq by congruence.
    rewrite complete_class.
    reflexivity.
Qed.
