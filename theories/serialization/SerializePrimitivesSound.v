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



Instance Sound_prim_tag : SoundClass prim_tag.
Proof.
Admitted.

Instance Sound_prim_int : SoundClass PrimInt63.int.
Proof.
Admitted.

Instance Sound_prim_float : SoundClass PrimFloat.float.
Proof.
Admitted.

Instance Sound_array_model {T : Set} `{SoundClass T} : SoundClass (array_model T).
Proof.
Admitted.

Instance Sound_prim_val {T : Set} `{SoundClass T} : SoundClass (prim_val T).
Proof.
Admitted.
