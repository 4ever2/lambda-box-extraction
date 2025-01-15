From MetaCoq.Erasure Require Import EAst.
From Coq Require Import List ZArith String.
From Ceres Require Import Ceres.

Import ListNotations.
Local Open Scope string_scope.



Local Notation "'bs_to_s' s" := (bytestring.String.to_string s) (at level 200).
Local Notation "'s_to_bs' s" := (bytestring.String.of_string s) (at level 200).

(** * Serializers *)
(** ** Common definitions serializers *)

(** Kername definitions *)
Instance Serialize_ident : Serialize Kernames.ident :=
  fun i =>
    Atom (Str (bs_to_s i)).

Instance Serialize_dirpath : Serialize Kernames.dirpath :=
  fun d =>
    to_sexp d.

Instance Serialize_modpath : Serialize Kernames.modpath :=
  fix sz (m : Kernames.modpath) : sexp :=
    match m with
    | Kernames.MPfile dp => [ Atom "MPfile"; to_sexp dp ]
    | Kernames.MPbound dp id i => [ Atom "MPbound"; to_sexp dp; to_sexp id; to_sexp i ]
    | Kernames.MPdot mp id => [ Atom "MPdot"; sz mp; to_sexp id ]
    end%sexp.

Instance Serialize_kername : Serialize Kernames.kername :=
  fun kn =>
    to_sexp kn.

Instance Serialize_inductive : Serialize Kernames.inductive :=
  fun i =>
    [ Atom "inductive"; to_sexp (Kernames.inductive_mind i); to_sexp (Kernames.inductive_ind i) ]%sexp.

Instance Serialize_projection : Serialize Kernames.projection :=
  fun p =>
    [ Atom "projection"; to_sexp (Kernames.proj_ind p); to_sexp (Kernames.proj_npars p); to_sexp (Kernames.proj_arg p) ]%sexp.

(** BasicAst definitions *)
Instance Serialize_name : Serialize BasicAst.name :=
  fun n =>
    match n with
    | BasicAst.nAnon => Atom "nAnon"
    | BasicAst.nNamed i => [ Atom "nNamed"; to_sexp i ]
    end%sexp.

Instance Serialize_recursivity_kind : Serialize BasicAst.recursivity_kind :=
  fun x =>
    match x with
    | BasicAst.Finite => Atom "Finite"
    | BasicAst.CoFinite => Atom "CoFinite"
    | BasicAst.BiFinite => Atom "BiFinite"
    end%sexp.

(** Universe definitions *)
Instance Serialize_allowed_eliminations : Serialize Universes.allowed_eliminations :=
  fun x =>
    match x with
    | Universes.IntoSProp => Atom "IntoSProp"
    | Universes.IntoPropSProp => Atom "IntoPropSProp"
    | Universes.IntoSetPropSProp => Atom "IntoSetPropSProp"
    | Universes.IntoAny => Atom "IntoAny"
    end%sexp.



(** ** Term serializer *)
Instance Serialize_def {T : Set} `{Serialize T} : Serialize (def T) :=
  fun d =>
    [ Atom "def"; to_sexp (dname d); to_sexp (dbody d); to_sexp (rarg d) ]%sexp.

Instance Serialize_mfixpoint {T : Set} `{Serialize T} : Serialize (mfixpoint T) :=
  fun f =>
    to_sexp f.

Instance Serialize_term : Serialize term :=
  fix sz (t : term) : sexp :=
    match t with
    | tBox => Atom "tBox"
    | tRel n => [ Atom "tRel"; to_sexp n ]
    | tVar i => [ Atom "tVar"; to_sexp i]
    | tEvar n l => [ Atom "tEvar"; to_sexp n; List (map sz l) ]
    | tLambda na t => [ Atom "tLambda"; to_sexp na; sz t ]
    | tLetIn na b t => [ Atom "tLetIn"; to_sexp na; sz b; sz t ]
    | tApp u v => [ Atom "tApp"; sz u; sz v ]
    | tConst k => [ Atom "tConst"; to_sexp k ]
    | tConstruct ind n args => [ Atom "tConstruct"; to_sexp ind; to_sexp n; List (map sz args)  ]
    | tCase indn c brs => [ Atom "tCase"; to_sexp indn; sz c; List (map (fun '(ns,t) => [ to_sexp ns; sz t ]) brs) ]
    | tProj p c => [ Atom "tProj"; to_sexp p; sz c ]
    | tFix mfix idx => [ Atom "tFix"; @to_sexp _ (@Serialize_mfixpoint _ sz) mfix; to_sexp idx ]
    | tCoFix mfix idx => [ Atom "tCoFix"; @to_sexp _ (@Serialize_mfixpoint _ sz) mfix; to_sexp idx  ]
    (* | tPrim (prim : prim_val term) *)
    | tPrim prim => [ Atom "tPrim" ] (* Unsupported *)
    | tLazy t => [ Atom "tLazy"; sz t ]
    | tForce t => [ Atom "tForce"; sz t ]
    end%sexp.



(** ** Context serializer *)

Instance Serialize_constructor_body : Serialize constructor_body :=
  fun cb =>
    [ Atom "constructor_body"; to_sexp (cstr_name cb); to_sexp (cstr_nargs cb) ]%sexp.

Instance Serialize_projection_body : Serialize projection_body :=
  fun pb =>
    [ Atom "projection_body"; to_sexp (proj_name pb) ]%sexp.

Instance Serialize_one_inductive_body : Serialize one_inductive_body :=
  fun oib =>
    [ Atom "one_inductive_body"
    ; to_sexp (ind_name oib)
    ; to_sexp (ind_propositional oib)
    ; to_sexp (ind_kelim oib)
    ; to_sexp (ind_ctors oib)
    ; to_sexp (ind_projs oib)
    ]%sexp.

Instance Serialize_mutual_inductive_body : Serialize mutual_inductive_body :=
  fun mib =>
    [ Atom "mutual_inductive_body"
    ; to_sexp (ind_finite mib)
    ; to_sexp (ind_npars mib)
    ; to_sexp (ind_bodies mib)
    ]%sexp.

Instance Serialize_constant_body : Serialize constant_body :=
  fun cb =>
    [ Atom "constant_body"
    ; to_sexp (cst_body cb)
    ]%sexp.

Instance Serialize_global_decl : Serialize global_decl :=
  fun gd =>
    match gd with
    | ConstantDecl cb => [ Atom "ConstantDecl"; to_sexp cb ]
    | InductiveDecl mib => [ Atom "InductiveDecl"; to_sexp mib ]
    end%sexp.

Instance Serialize_global_declarations : Serialize global_declarations :=
  fun gd =>
    to_sexp gd.



(** ** Deserialize program *)

Instance Serialize_program : Serialize program :=
 fun p =>
    to_sexp p.



(** * Deserializers *)
(** ** Common definitions deserializers *)

(** Kername definitions *)
Instance Deserialize_ident : Deserialize Kernames.ident :=
  fun l e =>
    match e with
    | Atom_ (Str s) => inr (s_to_bs s)
    | _ => inl (DeserError l "error")
    end.

Instance Deserialize_dirpath : Deserialize Kernames.dirpath :=
 fun l e =>
    _from_sexp l e.

Instance Deserialize_modpath : Deserialize Kernames.modpath :=
  fix ds (l : loc) (e : sexp) : error + Kernames.modpath :=
    Deser.match_con "modpath" []
      [ ("MPfile", Deser.con1_ Kernames.MPfile)
      ; ("MPbound", Deser.con3_ Kernames.MPbound)
      ; ("MPdot", Deser.con2 Kernames.MPdot ds _from_sexp )
      ] l e.

Instance Deserialize_kername : Deserialize Kernames.kername :=
 fun l e =>
    _from_sexp l e.

Instance Deserialize_inductive : Deserialize Kernames.inductive :=
  fun l e =>
    Deser.match_con "inductive" []
      [ ("inductive", Deser.con2_ Kernames.mkInd) ]
      l e.

Instance Deserialize_projection : Deserialize Kernames.projection :=
  fun l e =>
    Deser.match_con "projection" []
      [ ("projection", Deser.con3_ Kernames.mkProjection) ]
      l e.

(** BasicAst definitions *)
Instance Deserialize_name : Deserialize BasicAst.name :=
  fun l e =>
    Deser.match_con "name"
      [ ("nAnon", BasicAst.nAnon) ]
      [ ("nNamed", Deser.con1_ BasicAst.nNamed) ]
      l e.

Instance Deserialize_recursivity_kind : Deserialize BasicAst.recursivity_kind :=
  fun l e =>
    Deser.match_con "recursivity_kind"
      [ ("Finite", BasicAst.Finite)
      ; ("CoFinite", BasicAst.CoFinite)
      ; ("BiFinite", BasicAst.BiFinite)
      ]
      []
      l e.

(** Universe definitions *)
Instance Deserialize_allowed_eliminations : Deserialize Universes.allowed_eliminations :=
  fun l e =>
    Deser.match_con "allowed_eliminations"
      [ ("IntoSProp", Universes.IntoSProp)
      ; ("IntoPropSProp", Universes.IntoPropSProp)
      ; ("IntoSetPropSProp", Universes.IntoSetPropSProp)
      ; ("IntoAny", Universes.IntoAny)
      ]
      []
      l e.



(** ** Term deserializer *)

Instance Deserialize_def {T : Set} `{Deserialize T} : Deserialize (def T) :=
  fun l e =>
    Deser.match_con "def" []
      [ ("def", Deser.con3_ (@Build_def T)) ]
      l e.

Instance Deserialize_mfixpoint {T : Set} `{Deserialize T} : Deserialize (mfixpoint T) :=
 fun l e =>
    _from_sexp l e.

#[bypass_check(guard)]
Fixpoint deserialize_term (l : loc) (e : sexp) {struct e} : error + term :=
    let ds := deserialize_term in
    let ds_term_list : FromSexp (list term) := fun l e => @_from_sexp (list term) (@Deserialize_list term ds) l e in
    let ds_mfixpoint : FromSexp (mfixpoint term) := @_from_sexp (mfixpoint term) (@Deserialize_mfixpoint term ds) in
    let ds_cases : FromSexp (list (list BasicAst.name * term)) := @_from_sexp (list (list BasicAst.name * term))
      (@Deserialize_list (list BasicAst.name * term) (@Deserialize_prod (list BasicAst.name) term _from_sexp ds)) in
    Deser.match_con "term"
      [ ("tBox", tBox) ]
      [ ("tRel", Deser.con1_ tRel)
      ; ("tVar", Deser.con1_ tVar)
      ; ("tEvar", Deser.con2 tEvar _from_sexp ds_term_list)
      ; ("tLambda", Deser.con2 tLambda _from_sexp ds)
      ; ("tLetIn", Deser.con3 tLetIn _from_sexp ds ds)
      ; ("tApp", Deser.con2 tApp ds ds)
      ; ("tConst", Deser.con1_ tConst)
      ; ("tConstruct", Deser.con3 tConstruct _from_sexp _from_sexp ds_term_list)
      ; ("tCase", Deser.con3 tCase _from_sexp ds ds_cases)
      ; ("tProj", Deser.con2 tProj _from_sexp ds)
      ; ("tFix", Deser.con2 tFix ds_mfixpoint _from_sexp)
      ; ("tCoFix", Deser.con2 tCoFix ds_mfixpoint _from_sexp)
      (* ; ("tPrim", Deser.con? tPrim) *) (* Unsupported *)
      ; ("tLazy", Deser.con1 tLazy ds)
      ; ("tForce", Deser.con1 tForce ds)
      ]
      l e.

Instance Deserialize_term : Deserialize term :=
  deserialize_term.



(** ** Context deserializer *)

Instance Deserialize_constructor_body : Deserialize constructor_body :=
  fun l e =>
    Deser.match_con "constructor_body" []
      [ ("constructor_body", Deser.con2_ mkConstructor) ]
      l e.

Instance Deserialize_projection_body : Deserialize projection_body :=
  fun l e =>
    Deser.match_con "projection_body" []
      [ ("projection_body", Deser.con1_ mkProjection) ]
      l e.

Instance Deserialize_one_inductive_body : Deserialize one_inductive_body :=
  fun l e =>
    Deser.match_con "one_inductive_body" []
      [ ("one_inductive_body", Deser.con5_ Build_one_inductive_body) ]
      l e.

Instance Deserialize_mutual_inductive_body : Deserialize mutual_inductive_body :=
  fun l e =>
    Deser.match_con "mutual_inductive_body" []
      [ ("mutual_inductive_body", Deser.con3_ Build_mutual_inductive_body) ]
      l e.

Instance Deserialize_constant_body : Deserialize constant_body :=
  fun l e =>
    Deser.match_con "constant_body" []
      [ ("constant_body", Deser.con1_ Build_constant_body) ]
      l e.

Instance Deserialize_global_decl : Deserialize global_decl :=
  fun l e =>
    Deser.match_con "global_decl"
      []
      [ ("ConstantDecl", Deser.con1_ ConstantDecl)
      ; ("InductiveDecl", Deser.con1_ InductiveDecl)
      ]
      l e.

Instance Deserialize_global_declarations : Deserialize global_declarations :=
 fun l e =>
    _from_sexp l e.



(** ** Deserialize program *)

Instance Deserialize_program : Deserialize program :=
 fun l e =>
    _from_sexp l e.



(** * Main deserialization functions *)
Definition term_of_string (s : string) : error + term :=
  from_string s.

Definition context_of_string (s : string) : error + global_declarations :=
  from_string s.

Definition program_of_string (s : string) : error + program :=
  from_string s.
