From Coq             Require Import List Logic.Decidable ssreflect.
From MetaCoq.Common  Require Import BasicAst Kernames Universes EnvMap.
From MetaCoq.Erasure Require Import EAst EWellformed.
From MetaCoq.Erasure.Typed Require ExAst.
From MetaCoq.Utils   Require Import ReflectEq.
From Equations       Require Import Equations.

Import ListNotations.
Import EnvMap.




Definition eflags : EEnvFlags :=
  {| has_axioms      := true;
     term_switches   :=
       {| has_tBox        := true
        ; has_tRel        := true
        ; has_tVar        := true
        ; has_tEvar       := true
        ; has_tLambda     := true
        ; has_tLetIn      := true
        ; has_tApp        := true
        ; has_tConst      := true
        ; has_tConstruct  := true
        ; has_tCase       := true
        ; has_tProj       := false (* Our backends shouldn't produce projections *)
        ; has_tFix        := true
        ; has_tCoFix      := true
        ; has_tPrim       := all_primitive_flags
        ; has_tLazy_Force := true
        |};
     has_cstr_params := false;  (* Agda already drops constructor params *)
     cstr_as_blocks  := true;   (* The backend fully applies ctors       *)
  |}.

Definition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.

Fixpoint check_fresh_global (k : kername) (decls : global_declarations) : bool :=
  match decls with
  | []    => true
  | p::ds => negb (eq_kername (fst p) k) && check_fresh_global k ds
  end.

Fixpoint check_wf_glob {efl : EEnvFlags} (decls : global_declarations) : bool :=
  match decls with
  | []    => true
  | p::ds => check_wf_glob ds && check_fresh_global (fst p) ds && wf_global_decl ds (snd p)
  end.

Definition check_wf_program {efl : EEnvFlags} (p : program) : bool :=
  check_wf_glob (fst p) && wellformed (fst p) 0 (snd p).

(* freshness boolean check coincides with the freshness property *)
Fixpoint check_fresh_globalP (k : kername) (decls : global_declarations)
  : reflectProp (fresh_global k decls) (check_fresh_global k decls).
Proof.
  dependent elimination decls; simpl.
- apply reflectP.
  apply Forall_nil.
- destruct (inspect (fst p == k)).
  destruct x; rewrite e; simpl.
  + apply reflectF => global_ds.
    dependent elimination global_ds.
    apply n.
    by apply eqb_eq.
  + destruct (check_fresh_globalP k l).
    * apply reflectP.
      apply Forall_cons; auto.
      destruct (neqb (fst p) k) as [Hneq _].
      apply Hneq.
      by rewrite e.
    * apply reflectF => gds.
      by dependent elimination gds.
Defined.

(* well-formedness boolean check coincides with the wf property *)
Fixpoint check_wf_globP {efl : EEnvFlags} (decls : global_declarations)
  : reflectProp (wf_glob decls) (check_wf_glob decls).
Proof.
dependent elimination decls.
- apply reflectP.
  apply wf_glob_nil.
- remember (check_wf_glob l).
  pose x := (check_wf_globP efl l).
  rewrite <-Heqb in x.
  destruct x; simpl; rewrite <-Heqb; simpl.
  + remember (check_fresh_global (fst p) l).
    pose x := (check_fresh_globalP (fst p) l).
    rewrite <-Heqb0 in x.
    destruct x => /=.
    remember (wf_global_decl l (snd p)).
    destruct b.
    apply reflectP.
    destruct p.
    by constructor.
    apply reflectF => gds.
    dependent elimination gds.
    simpl in Heqb1.
    rewrite <-Heqb1 in i.
    discriminate i.
    apply reflectF => gds.
    by dependent elimination gds.
  + apply reflectF => gds.
    by dependent elimination gds.
Defined.

