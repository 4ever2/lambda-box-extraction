From MetaCoq.Utils Require bytestring.
From MetaCoq.Common Require Import BasicAst.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Common Require Import Universes.
From Coq Require Import List.
From Coq Require Import String.
From Ceres Require Import Ceres.

Import ListNotations.
Local Open Scope string_scope.



(** * Serializers *)

(** ** Kername *)
Instance Serialize_ident : Serialize ident :=
  fun i =>
    Atom (Str (bytestring.String.to_string i)).

Instance Serialize_dirpath : Serialize dirpath :=
  fun d =>
    to_sexp d.

Instance Serialize_modpath : Serialize modpath :=
  fix sz (m : modpath) : sexp :=
    match m with
    | MPfile dp => [ Atom "MPfile"; to_sexp dp ]
    | MPbound dp id i => [ Atom "MPbound"; to_sexp dp; to_sexp id; to_sexp i ]
    | MPdot mp id => [ Atom "MPdot"; sz mp; to_sexp id ]
    end%sexp.

Instance Serialize_kername : Serialize kername :=
  fun kn =>
    to_sexp kn.

Instance Serialize_inductive : Serialize inductive :=
  fun i =>
    [ Atom "inductive"; to_sexp (inductive_mind i); to_sexp (inductive_ind i) ]%sexp.

Instance Serialize_projection : Serialize projection :=
  fun p =>
    [ Atom "projection"; to_sexp (proj_ind p); to_sexp (proj_npars p); to_sexp (proj_arg p) ]%sexp.

(** ** BasicAst *)
Instance Serialize_name : Serialize name :=
  fun n =>
    match n with
    | nAnon => Atom "nAnon"
    | nNamed i => [ Atom "nNamed"; to_sexp i ]
    end%sexp.

Instance Serialize_recursivity_kind : Serialize recursivity_kind :=
  fun x =>
    match x with
    | Finite => Atom "Finite"
    | CoFinite => Atom "CoFinite"
    | BiFinite => Atom "BiFinite"
    end%sexp.

(** ** Universe *)
Instance Serialize_allowed_eliminations : Serialize allowed_eliminations :=
  fun x =>
    match x with
    | IntoSProp => Atom "IntoSProp"
    | IntoPropSProp => Atom "IntoPropSProp"
    | IntoSetPropSProp => Atom "IntoSetPropSProp"
    | IntoAny => Atom "IntoAny"
    end%sexp.



(** * Deserializers *)

(** ** Kername *)
Instance Deserialize_ident : Deserialize ident :=
  fun l e =>
    match e with
    | Atom_ (Str s) => inr (bytestring.String.of_string s)
    | _ => inl (DeserError l "error")
    end.

Instance Deserialize_dirpath : Deserialize dirpath :=
 fun l e =>
    _from_sexp l e.

Instance Deserialize_modpath : Deserialize modpath :=
  fix ds (l : loc) (e : sexp) : error + modpath :=
    Deser.match_con "modpath" []
      [ ("MPfile", Deser.con1_ MPfile)
      ; ("MPbound", Deser.con3_ MPbound)
      ; ("MPdot", Deser.con2 MPdot ds _from_sexp )
      ] l e.

Instance Deserialize_kername : Deserialize kername :=
 fun l e =>
    _from_sexp l e.

Instance Deserialize_inductive : Deserialize inductive :=
  fun l e =>
    Deser.match_con "inductive" []
      [ ("inductive", Deser.con2_ mkInd) ]
      l e.

Instance Deserialize_projection : Deserialize projection :=
  fun l e =>
    Deser.match_con "projection" []
      [ ("projection", Deser.con3_ mkProjection) ]
      l e.

(** ** BasicAst *)
Instance Deserialize_name : Deserialize name :=
  fun l e =>
    Deser.match_con "name"
      [ ("nAnon", nAnon) ]
      [ ("nNamed", Deser.con1_ nNamed) ]
      l e.

Instance Deserialize_recursivity_kind : Deserialize recursivity_kind :=
  fun l e =>
    Deser.match_con "recursivity_kind"
      [ ("Finite", Finite)
      ; ("CoFinite", CoFinite)
      ; ("BiFinite", BiFinite)
      ]
      []
      l e.

(** ** Universe *)
Instance Deserialize_allowed_eliminations : Deserialize allowed_eliminations :=
  fun l e =>
    Deser.match_con "allowed_eliminations"
      [ ("IntoSProp", IntoSProp)
      ; ("IntoPropSProp", IntoPropSProp)
      ; ("IntoSetPropSProp", IntoSetPropSProp)
      ; ("IntoAny", IntoAny)
      ]
      []
      l e.
