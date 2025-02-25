From Coq Require Import List.
From Coq Require Import Logic.Decidable.
From Coq Require Import ssreflect.
From MetaCoq.Utils Require Import ReflectEq.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Common Require Import EnvMap.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EWellformed.
From MetaCoq.Erasure.Typed Require ExAst.
From Equations Require Import Equations.

Import ListNotations.
Import EnvMap.



Definition agda_eflags : EEnvFlags :=
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

Definition agda_typed_eflags : EEnvFlags :=
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

From MetaCoq.Erasure Require Import EGlobalEnv.
From MetaCoq.Erasure Require Import EPrimitive.

From MetaCoq.Utils Require Import utils.
From MetaCoq.Erasure.Typed Require Import ResultMonad.

Import MCMonadNotation.

From MetaCoq.Common Require Import Primitive.


Section Wf.
  Context {efl  : EEnvFlags}.
  Variable Σ : global_context.

  Definition assert (b : bool) (s : unit -> string) : (fun T => result T string) unit :=
    if b then Ok tt else Err (s tt).

  Definition assert_some {A : Type} (b : option A) (s : unit -> string) : (fun T => result T string) unit :=
    match b with
    | Some _ =>  Ok tt
    | None => Err (s tt)
    end.

  Definition result_forall {A : Type} (f : A -> (fun T => result T string) unit ) (l : list A) :=
    List.fold_left (fun a t => a ;; f t) l (Ok tt).

  Definition wf_fix_gen_ (wf : nat -> term -> (fun T => result T string) unit) k mfix idx :=
    let k' := List.length mfix + k in
    assert (idx <? #|mfix|) (fun _ => "Fixpoint index out of bounds") ;;
    result_forall (fun d => (wf k') d.(dbody)) mfix.

  Definition bool_of_result {T E : Type} (r : result T E) : bool :=
    match r with
    | Ok _ => true
    | Err _ => false
    end.

  Definition has_prim_ {epfl : EPrimitiveFlags} (p : prim_val term) : (fun T => result T string) unit :=
    match prim_val_tag p with
    | primInt => assert has_primint (fun _ => "Program contains primitive integers")
    | primFloat => assert has_primfloat (fun _ => "Program contains primitive floats")
    | primArray => assert has_primarray (fun _ => "Program contains primitive arrays")
    end.

  Fixpoint wellformed (k : nat) (t : term) {struct t} : (fun T => result T string) unit :=
    match t with
    | tRel i => assert has_tRel (fun _ => "Program contains tRel") ;; assert (Nat.ltb i k) (fun _ => "Program not closed, invalid tRel " ^ (string_of_nat i))
    | tEvar ev args => assert has_tEvar (fun _ => "Program contains tEvar") ;; result_forall (wellformed k) args
    | tLambda _ M => assert has_tLambda (fun _ => "Program contains tLambda") ;; wellformed (S k) M
    | tApp u v =>
      assert has_tApp (fun _ => "Program contains tApp") ;;
      wellformed k u ;;
      wellformed k v
    | tLetIn na b b' =>
      assert has_tLetIn (fun _ => "Program contains tLetIn") ;;
      wellformed k b ;;
      wellformed (S k) b'
    | tCase ind c brs =>
      assert has_tCase (fun _ => "Program contains tCase") ;;
      let brs' := result_forall (fun br => wellformed (#|br.1| + k) br.2) brs in
      wf_brs Σ ind.1 #|brs| ;;
      wellformed k c ;;
      brs'
    | tProj p c =>
      assert has_tProj (fun _ => "Program contains tProj") ;;
      assert_some (lookup_projection Σ p) (fun _ => "Projection " ^ (string_of_inductive p.(proj_ind))^":"^(string_of_nat p.(proj_npars))^","^(string_of_nat p.(proj_arg)) ^ " not found") ;;
      wellformed k c
    | tFix mfix idx =>
      assert has_tFix (fun _ => "Program contains tFix") ;;
      result_forall (fun t => assert ((isLambda ∘ dbody) t) (fun _ => "Fixpoint body is not a lambda")) mfix ;;
      wf_fix_gen_ wellformed k mfix idx
    | tCoFix mfix idx =>
      assert has_tCoFix (fun _ => "Program contains tCoFix") ;;
      wf_fix_gen_ wellformed k mfix idx
    | tBox => assert has_tBox (fun _ => "Program contains tBox")
    | tConst kn =>
      assert has_tConst (fun _ => "Program contains tConst") ;;
      match lookup_constant Σ kn with
      | Some d => assert (has_axioms || isSome d.(cst_body)) (fun _ => "Invalid axiom " ^ (string_of_kername kn))
      | _ => Err ("Constant not found in environment " ^ (string_of_kername kn))
      end
    | tConstruct ind c block_args =>
      assert has_tConstruct (fun _ => "Program contains tConstruct") ;;
      assert_some (lookup_constructor Σ ind c) (fun _ => "Constructor " ^ (string_of_inductive ind)^":"^(string_of_nat c) ^ " not found") ;;
      if cstr_as_blocks then
        match lookup_constructor_pars_args Σ ind c with
        | Some (p, a) => assert ((p + a) == #|block_args|) (fun _ => "Constructor " ^ (string_of_inductive ind)^":"^(string_of_nat c) ^ " not fully applied")
        | _ => Ok tt end
        ;; result_forall (wellformed k) block_args
      else assert (is_nil block_args) (fun _ => "Constructor args non-empty")
    | tVar _ => assert has_tVar (fun _ => "Program contains tVar")
    | tPrim p => has_prim_ p ;; assert (test_prim (fun t => bool_of_result (wellformed k t)) p) (fun _ => "Invalid array primitive")
    | tLazy t => assert has_tLazy_Force (fun _ => "Program contains lazy/force") ;; wellformed k t
    | tForce t => assert has_tLazy_Force (fun _ => "Program contains lazy/force") ;; wellformed k t
    end.

(*   Theorem wellformed_equiv : forall k t,
    bool_of_result (wellformed k t) = EWellformed.wellformed Σ k t.
  Proof.
  Admitted. *)

  Definition wf_projections idecl : (fun T => result T string) unit :=
    match idecl.(ind_projs) with
    | [] => Ok tt
    | _ =>
      match idecl.(ind_ctors) with
      | [cstr] => assert (#|idecl.(ind_projs)| == cstr.(cstr_nargs)) (fun _ => "")
      | _ => Err ""
      end
    end.

  Definition wf_inductive (idecl : one_inductive_body) : (fun T => result T string) unit :=
    wf_projections idecl.

  Definition wf_minductive (mdecl : mutual_inductive_body) : (fun T => result T string) unit :=
    assert (has_cstr_params || (mdecl.(ind_npars) == 0)) (fun _ => "") ;;
    result_forall wf_inductive mdecl.(ind_bodies).

  Definition wf_global_decl d : (fun T => result T string) unit :=
    match d with
    | ConstantDecl cb =>
      match cb.(cst_body) with
      | None => assert has_axioms (fun _ => "Program contains axioms")
      | Some cb => wellformed 0 cb
      end
    | InductiveDecl idecl => wf_minductive idecl
    end.


End Wf.





Fixpoint check_fresh_global (k : kername) (decls : global_declarations) : (fun T => result T string) unit :=
  match decls with
  | []    => Ok tt
  | p::ds => assert (negb (eq_kername (fst p) k)) (fun _ => "Duplicate definition " ^ (string_of_kername (fst p)))  ;; check_fresh_global k ds
  end.

Fixpoint check_wf_glob {efl : EEnvFlags} (decls : global_declarations) : (fun T => result T string) unit :=
  match decls with
  | []    => Ok tt
  | p::ds => check_wf_glob ds ;; check_fresh_global (fst p) ;; map_error (fun e => "Error while checking " ^ (string_of_kername (fst p)) ^ ": " ^ e) (wf_global_decl ds (snd p))
  end.

Definition check_wf_program {efl : EEnvFlags} (p : program) : (fun T => result T string) unit :=
  check_wf_glob (fst p) ;; wellformed (fst p) 0 (snd p).

(* Definition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.

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
Defined. *)

Module CheckWfExAst.
  Import ExAst.

  Fixpoint check_fresh_global (k : kername) (decls : global_env) : (fun T => result T string) unit  :=
    match decls with
    | []    => Ok tt
    | (kn,_,_)::ds => assert (negb (eq_kername kn k)) (fun _ => "Duplicate definition " ^ (string_of_kername kn)) ;; check_fresh_global k ds
    end.

  Definition check_wf_typed_program {efl : EEnvFlags} (p : global_env) : (fun T => result T string) unit  :=
    check_wf_glob (trans_env p).

(*   Fixpoint check_fresh_globalP (k : kername) (decls : global_env)
    : reflectProp (fresh_global k decls) (check_fresh_global k decls).
  Proof.
    dependent elimination decls; simpl.
    - apply reflectP.
      apply Forall_nil.
    - destruct p as [[kn ?] ?].
      destruct (inspect (kn == k)).
      destruct x; rewrite e; simpl.
      + apply reflectF => global_ds.
        dependent elimination global_ds.
        apply y.
        by apply eqb_eq.
      + destruct (check_fresh_globalP k l).
        * apply reflectP.
          apply Forall_cons; auto.
          destruct (neqb kn k) as [Hneq _].
          apply Hneq.
          by rewrite e.
        * apply reflectF => gds.
          by dependent elimination gds.
  Defined. *)
End CheckWfExAst.
