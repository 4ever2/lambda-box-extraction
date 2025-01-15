From Coq Require Import List.
From Coq Require Import ZArith_base.
From Coq Require Import String.
From Coq Require PrimInt63.
From Coq Require PrimFloat.
From Ceres Require Import Ceres.

From MetaCoq.Common Require Import Primitive.
From MetaCoq.Erasure Require Import EPrimitive.

Import ListNotations.
Local Open Scope string_scope.



(** * Axioms *)
(* TODO: resolve axioms *)
Axiom Z_of_prim_int : PrimInt63.int -> Z.
Axiom string_of_prim_float : PrimFloat.float -> string.
Axiom prim_int_of_Z : Z -> PrimInt63.int.
Axiom prim_float_of_string : string -> PrimFloat.float.



(** * Serializers *)

Instance Serialize_prim_tag : Serialize prim_tag :=
  fun t =>
    match t with
    | primInt => Atom "primInt"
    | primFloat => Atom "primFloat"
    | primArray => Atom "primArray"
    end%sexp.

Instance Serialize_prim_int : Serialize PrimInt63.int :=
  fun i => Atom (Num (Z_of_prim_int i)).

Instance Serialize_prim_float : Serialize PrimFloat.float :=
  fun f => Atom (Str (string_of_prim_float f)).

Instance Serialize_array_model {T : Set} `{Serialize T} : Serialize (array_model T) :=
  fun a =>
    [ Atom "array_model"; to_sexp (array_default a); to_sexp (array_value a) ]%sexp.

Instance Serialize_prim_val {T : Set} `{Serialize T} : Serialize (prim_val T) :=
  fun p =>
    let t := prim_val_tag p in
    match prim_val_model p with
    | primIntModel i => to_sexp (t, i)
    | primFloatModel f => to_sexp (t, f)
    | primArrayModel a => to_sexp (t, a)
    end.



(** * Deserializers *)

Instance Deerialize_prim_tag : Deserialize prim_tag :=
  fun l e =>
    Deser.match_con "prim_tag"
      [ ("primInt", primInt)
      ; ("primFloat", primFloat)
      ; ("primArray", primArray)
      ]
      [] l e.

Instance Deserialize_prim_int : Deserialize PrimInt63.int :=
  fun l e =>
    match e with
    | Atom_ (Num i) => inr (prim_int_of_Z i)
    | _ => inl (DeserError l "error")
    end.

Instance Deserialize_prim_float : Deserialize PrimFloat.float :=
  fun l e =>
    match e with
    | Atom_ (Str s) => inr (prim_float_of_string s)
    | _ => inl (DeserError l "error")
    end.

Instance Deserialize_array_model {T : Set} `{Deserialize T} : Deserialize (array_model T) :=
  fun l e =>
    Deser.match_con "array_model" []
      [ ("array_model", Deser.con2_ Build_array_model) ]
      l e.

Instance Deserialize_prim_val {T : Set} `{Deserialize T} : Deserialize (prim_val T) :=
  fun l e =>
    match e with
    | List (e1 :: e2 :: nil) =>
      let t := @_from_sexp prim_tag _ l e1 in
      match t with
      | inr primInt =>
        let v := @_from_sexp PrimInt63.int _ l e2 in
        match v with
        | inr v => inr (prim_int v)
        | inl e => inl e
        end
      | inr primFloat =>
        let v := @_from_sexp PrimFloat.float _ l e2 in
        match v with
        | inr v => inr (prim_float v)
        | inl e => inl e
        end
      | inr primArray =>
        let v := @_from_sexp (array_model T) _ l e2 in
        match v with
        | inr v => inr (prim_array v)
        | inl e => inl e
        end
      | inl e => inl e
      end
    | _ => inl (DeserError l "error")
    end.
