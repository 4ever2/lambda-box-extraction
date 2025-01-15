From MetaCoq.Erasure Require Import EAst.
From Coq Require Import List ZArith_base String.
From Ceres Require Import Ceres.
From LambdaBox Require Import SerializeCommon.

Import ListNotations.
Local Open Scope string_scope.



(** * Serializers *)

(* TODO *)
Axiom Z_of_prim_int : PrimInt63.int -> Z.
(* TODO *)
Axiom string_of_prim_float : PrimFloat.float -> string.

Instance Serialize_prim_tag : Serialize Primitive.prim_tag :=
  fun t =>
    match t with
    | Primitive.primInt => Atom "primInt"
    | Primitive.primFloat => Atom "primFloat"
    | Primitive.primArray => Atom "primArray"
    end%sexp.

Instance Serialize_prim_int : Serialize PrimInt63.int :=
  fun i => Atom (Num (Z_of_prim_int i)).

Instance Serialize_prim_float : Serialize PrimFloat.float :=
  fun f => Atom (Str (string_of_prim_float f)).

Instance Serialize_array_model {T : Set} `{Serialize T} : Serialize (EPrimitive.array_model T) :=
  fun a =>
    [ Atom "array_model"; to_sexp (EPrimitive.array_default a); to_sexp (EPrimitive.array_value a) ]%sexp.

Instance Serialize_prim_val {T : Set} `{Serialize T} : Serialize (EPrimitive.prim_val T) :=
  fun p =>
    let t := EPrimitive.prim_val_tag p in
    match EPrimitive.prim_val_model p with
    | EPrimitive.primIntModel i => to_sexp (t, i)
    | EPrimitive.primFloatModel f => to_sexp (t, f)
    | EPrimitive.primArrayModel a => to_sexp (t, a)
    end.



(** * Deserializers *)

(* TODO *)
Axiom prim_int_of_Z : Z -> PrimInt63.int.
(* TODO *)
Axiom prim_float_of_string : string -> PrimFloat.float.

Instance Deerialize_prim_tag : Deserialize Primitive.prim_tag :=
  fun l e =>
    Deser.match_con "prim_tag"
      [ ("primInt", Primitive.primInt)
      ; ("primFloat", Primitive.primFloat)
      ; ("primArray", Primitive.primArray)
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

Instance Deserialize_array_model {T : Set} `{Deserialize T} : Deserialize (EPrimitive.array_model T) :=
  fun l e =>
    Deser.match_con "array_model" []
      [ ("array_model", Deser.con2_ EPrimitive.Build_array_model) ]
      l e.

Instance Deserialize_prim_val {T : Set} `{Deserialize T} : Deserialize (EPrimitive.prim_val T) :=
  fun l e =>
    match e with
    | List (e1 :: e2 :: nil) =>
      let t := @_from_sexp Primitive.prim_tag _ l e1 in
      match t with
      | inr Primitive.primInt =>
        let v := @_from_sexp PrimInt63.int _ l e2 in
        match v with
        | inr v => inr (EPrimitive.prim_int v)
        | inl e => inl e
        end
      | inr Primitive.primFloat =>
        let v := @_from_sexp PrimFloat.float _ l e2 in
        match v with
        | inr v => inr (EPrimitive.prim_float v)
        | inl e => inl e
        end
      | inr Primitive.primArray =>
        let v := @_from_sexp (EPrimitive.array_model T) _ l e2 in
        match v with
        | inr v => inr (EPrimitive.prim_array v)
        | inl e => inl e
        end
      | inl e => inl e
      end
    | _ => inl (DeserError l "error")
    end.
