From LambdaBox Require Import SerializeCommon.
From LambdaBox Require Import CeresExtra.
From Ceres Require Import CeresRoundtrip.
From Ceres Require Import CeresSerialize.
From Ceres Require Import CeresDeserialize.
From MetaCoq.Common Require Import BasicAst.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Common Require Import Universes.
From MetaCoq.Utils Require Import bytestring.
From Coq Require Import String.



Instance Sound_ident : SoundClass ident.
Proof.
Admitted.

Instance Sound_dirpath : SoundClass dirpath.
Proof.
Admitted.

Instance Sound_modpath : SoundClass modpath.
Proof.
Admitted.

Instance Sound_kername : SoundClass kername.
Proof.
Admitted.

Instance Sound_inductive : SoundClass inductive.
Proof.
Admitted.

Instance Sound_projection : SoundClass projection.
Proof.
Admitted.



Instance Sound_name : SoundClass name.
Proof.
Admitted.

Instance Sound_recursivity_kind : SoundClass recursivity_kind.
Proof.
Admitted.



Instance Sound_allowed_eliminations : SoundClass allowed_eliminations.
Proof.
Admitted.
