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



Instance Sound_box_type : SoundClass box_type.
Proof.
Admitted.

Instance Sound_type_var_info : SoundClass type_var_info.
Proof.
Admitted.

Instance Sound_constant_body : SoundClass constant_body.
Proof.
Admitted.

Instance Sound_one_inductive_body : SoundClass one_inductive_body.
Proof.
Admitted.

Instance Sound_mutual_inductive_body : SoundClass mutual_inductive_body.
Proof.
Admitted.

Instance Sound_global_decl : SoundClass global_decl.
Proof.
Admitted.

Instance Sound_global_env : SoundClass global_env.
Proof.
Admitted.
