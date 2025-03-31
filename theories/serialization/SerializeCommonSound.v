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
  unfold SoundClass, Sound.
  intros l e a He.
  destruct e; cbn in He; try discriminate.
  destruct a0; cbn in He; try discriminate.
  injection He as <-.
  unfold to_sexp, Serialize_ident.
  rewrite bytestring_sound.
  reflexivity.
Qed.

Instance Sound_dirpath : SoundClass dirpath.
Proof.
  unfold SoundClass, Sound.
  intros l e d He.
  destruct e; cbn in He; try discriminate.
  apply sound_class_list with (fs := nil) in He.
  assumption.
  reflexivity.
Qed.

Instance Sound_modpath : SoundClass modpath.
Proof.
  unfold SoundClass, Sound.
  intros l e m He.
  generalize dependent l.
  generalize dependent m.
  induction e; intros.
  - cbn in He.
    destruct a; discriminate.
  - unfold _from_sexp, Deserialize_modpath in He.
    apply sound_match_con in He.
    destruct He as [He | He]; elim_Exists He.
    + destruct He as [es [<- He]].
      sound_field He.
      apply sound_class in Ea1.
      cbn.
      rewrite Ea1.
      reflexivity.
    + destruct He as [es [<- He]].
      sound_field He.
      apply sound_class in Ea0.
      apply sound_class in Ea1.
      apply sound_class in Ea2.
      cbn.
      rewrite Ea0, Ea1, Ea2.
      reflexivity.
    + destruct He as [es [H1 He]].
      inversion H1; subst; clear H1.
      sound_field He.
      apply sound_class in Ea0.
      cbn.
      rewrite Ea0; clear Ea0.
      apply List.Forall_cons_iff in H as [_ H].
      apply List.Forall_cons_iff in H as [H _].
      erewrite H.
      reflexivity.
      unfold _from_sexp, Deserialize_modpath.
      eassumption.
Qed.

Instance Sound_kername : SoundClass kername.
Proof.
  unfold SoundClass, Sound.
  apply SoundClass_prod.
Qed.

Instance Sound_inductive : SoundClass inductive.
Proof.
  unfold SoundClass, Sound.
  intros l e i He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  unfold to_sexp, Serialize_inductive.
  cbn.
  rewrite Ea0, Ea1.
  reflexivity.
Qed.

Instance Sound_projection : SoundClass projection.
Proof.
  unfold SoundClass, Sound.
  intros l e p He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  unfold to_sexp, Serialize_projection.
  cbn.
  rewrite Ea0, Ea1, Ea2.
  reflexivity.
Qed.



Instance Sound_name : SoundClass name.
Proof.
  unfold SoundClass, Sound.
  intros l e n He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [-> ->].
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    cbn.
    rewrite Ea1.
    reflexivity.
Qed.

Instance Sound_recursivity_kind : SoundClass recursivity_kind.
Proof.
  unfold SoundClass, Sound.
  intros l e x He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [-> ->].
    reflexivity.
  - destruct He as [-> ->].
    reflexivity.
  - destruct He as [-> ->].
    reflexivity.
Qed.



Instance Sound_allowed_eliminations : SoundClass allowed_eliminations.
Proof.
  unfold SoundClass, Sound.
  intros l e x He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [-> ->].
    reflexivity.
  - destruct He as [-> ->].
    reflexivity.
  - destruct He as [-> ->].
    reflexivity.
  - destruct He as [-> ->].
    reflexivity.
Qed.
