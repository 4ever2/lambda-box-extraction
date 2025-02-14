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



Instance Complete_def {T : Set} `{CompleteClass T} : CompleteClass (def T).
Proof.
Admitted.

Instance Complete_mfixpoint {T : Set} `{CompleteClass T} : CompleteClass (mfixpoint T).
Proof.
Admitted.

Instance Complete_term : CompleteClass term.
Proof.
Admitted.



Instance Complete_constructor_body : CompleteClass constructor_body.
Proof.
Admitted.

Instance Complete_projection_body : CompleteClass projection_body.
Proof.
Admitted.

Instance Complete_one_inductive_body : CompleteClass one_inductive_body.
Proof.
Admitted.

Instance Complete_mutual_inductive_body : CompleteClass mutual_inductive_body.
Proof.
Admitted.

Instance Complete_constant_body : CompleteClass constant_body.
Proof.
Admitted.

Instance Complete_global_decl : CompleteClass global_decl.
Proof.
Admitted.

Instance Complete_global_declarations : CompleteClass global_declarations.
Proof.
Admitted.



Instance Complete_program : CompleteClass program.
Proof.
Admitted.
