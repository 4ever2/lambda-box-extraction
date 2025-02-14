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



Instance Complete_prim_tag : CompleteClass prim_tag.
Proof.
Admitted.

Instance Complete_prim_int : CompleteClass PrimInt63.int.
Proof.
Admitted.

Instance Complete_prim_float : CompleteClass PrimFloat.float.
Proof.
Admitted.

Instance Complete_array_model {T : Set} `{CompleteClass T} : CompleteClass (array_model T).
Proof.
Admitted.

Instance Complete_prim_val {T : Set} `{CompleteClass T} : CompleteClass (prim_val T).
Proof.
Admitted.
