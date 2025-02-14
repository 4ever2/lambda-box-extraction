From LambdaBox Require Import SerializeCommon.
From LambdaBox Require Import SerializePrimitives.
From LambdaBox Require Import SerializeEAst.
From LambdaBox Require Import CeresExtra.
From Ceres Require Import CeresRoundtrip.
From Ceres Require Import CeresSerialize.
From Ceres Require Import CeresDeserialize.
From MetaCoq.Erasure Require Import EAst.
From Coq Require Import String.
From Coq Require Import List.



Instance Sound_def {T : Set} `{SoundClass T} : SoundClass (def T).
Proof.
Admitted.

Instance Sound_mfixpoint {T : Set} `{SoundClass T} : SoundClass (mfixpoint T).
Proof.
Admitted.

Instance Sound_term : SoundClass term.
Proof.
Admitted.



Instance Sound_constructor_body : SoundClass constructor_body.
Proof.
Admitted.

Instance Sound_projection_body : SoundClass projection_body.
Proof.
Admitted.

Instance Sound_one_inductive_body : SoundClass one_inductive_body.
Proof.
Admitted.

Instance Sound_mutual_inductive_body : SoundClass mutual_inductive_body.
Proof.
Admitted.

Instance Sound_constant_body : SoundClass constant_body.
Proof.
Admitted.

Instance Sound_global_decl : SoundClass global_decl.
Proof.
Admitted.

Instance Sound_global_declarations : SoundClass global_declarations.
Proof.
Admitted.



Instance Sound_program : SoundClass program.
Proof.
Admitted.
