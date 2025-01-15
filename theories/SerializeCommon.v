From MetaCoq.Erasure Require Import EAst.
From Coq Require Import List ZArith String.
From Ceres Require Import Ceres.

Import ListNotations.
Local Open Scope string_scope.



Local Notation "'bs_to_s' s" := (bytestring.String.to_string s) (at level 200).
Local Notation "'s_to_bs' s" := (bytestring.String.of_string s) (at level 200).

(** * Serializers *)

(** ** Kername *)
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

(** ** BasicAst *)
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

(** ** Universe *)
Instance Serialize_allowed_eliminations : Serialize Universes.allowed_eliminations :=
  fun x =>
    match x with
    | Universes.IntoSProp => Atom "IntoSProp"
    | Universes.IntoPropSProp => Atom "IntoPropSProp"
    | Universes.IntoSetPropSProp => Atom "IntoSetPropSProp"
    | Universes.IntoAny => Atom "IntoAny"
    end%sexp.



(** * Deserializers *)

(** ** Kername *)
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

(** ** BasicAst *)
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

(** ** Universe *)
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
