From LambdaBox Require Import SerializeCommon.
From LambdaBox Require Import SerializePrimitives.
From LambdaBox Require Import SerializeEAst.
From LambdaBox Require Import SerializeExAst.
From LambdaBox Require Import CeresExtra.
From Ceres Require Import CeresRoundtrip.
From Ceres Require Import CeresSerialize.
From Ceres Require Import CeresDeserialize.
From MetaCoq.Erasure Require Import ExAst.
From Coq Require Import String.
From Coq Require Import List.



Instance Complete_box_type : CompleteClass box_type.
Proof.
Admitted.

Instance Complete_type_var_info : CompleteClass type_var_info.
Proof.
Admitted.

Instance Complete_constant_body : CompleteClass constant_body.
Proof.
Admitted.

Instance Complete_one_inductive_body : CompleteClass one_inductive_body.
Proof.
Admitted.

Instance Complete_mutual_inductive_body : CompleteClass mutual_inductive_body.
Proof.
Admitted.

Instance Complete_global_decl : CompleteClass global_decl.
Proof.
Admitted.

Instance Complete_global_env : CompleteClass global_env.
Proof.
Admitted.
