From MetaCoq.Erasure Require Import ExAst.
From Coq Require Import List ZArith String.
From Ceres Require Import Ceres.
From LambdaBox Require Import SerializeCommon.
From LambdaBox Require Import SerializeEAst.
From LambdaBox Require Import CeresExtra.

Import ListNotations.
Local Open Scope string_scope.



Local Notation "'bs_to_s' s" := (bytestring.String.to_string s) (at level 200).
Local Notation "'s_to_bs' s" := (bytestring.String.of_string s) (at level 200).


(** * Serializers *)

(* Inductive box_type :=
| TBox
| TAny
| TArr (dom : box_type) (codom : box_type)
| TApp (_ : box_type) (_ : box_type)
| TVar (_ : nat) (* Level of type variable *)
| TInd (_ : inductive)
| TConst (_ : kername). *)
Instance Serialize_box_type : Serialize box_type :=
  fix sz (bt : box_type) : sexp :=
    match bt with
    | TBox => Atom "TBox"
    | TAny => Atom "TAny"
    | TArr dom codom => [ Atom "TArr"; sz dom; sz codom ]
    | TApp u v => [ Atom "TApp"; sz u; sz v ]
    | TVar i => [ Atom "TVar"; to_sexp i ]
    | TInd ind => [ Atom "TInd"; to_sexp ind ]
    | TConst k => [ Atom "TConst"; to_sexp k ]
    end%sexp.

(* Record type_var_info :=
  { tvar_name : name;
    tvar_is_logical : bool;
    tvar_is_arity : bool;
    tvar_is_sort : bool; }. *)
Instance Serialize_type_var_info : Serialize type_var_info :=
  fun tv =>
    [ Atom "type_var_info"
    ; to_sexp (tvar_name tv)
    ; to_sexp (tvar_is_logical tv)
    ; to_sexp (tvar_is_arity tv)
    ; to_sexp (tvar_is_sort tv)
    ]%sexp.

(* Record constant_body :=
  { cst_type : list name * box_type;
    cst_body : option term; }. *)
Instance Serialize_constant_body : Serialize constant_body :=
  fun cb =>
    [ Atom "constant_body"
    ; to_sexp (cst_type cb)
    ; to_sexp (cst_body cb)
    ]%sexp.

(* Record one_inductive_body :=
  { ind_name : ident;
    ind_propositional : bool;
    ind_kelim : Universes.allowed_eliminations;
    ind_type_vars : list type_var_info;
    ind_ctors : list (ident *
                      list (name * box_type) *
                      nat (* original arities, unfortunately needed for erases_one_inductive_body *)
                     );
    ind_projs : list (ident * box_type); }. *)
Instance Serialize_one_inductive_body : Serialize one_inductive_body :=
  fun oib =>
    [ Atom "one_inductive_body"
    ; to_sexp (ind_name oib)
    ; to_sexp (ind_propositional oib)
    ; to_sexp (ind_kelim oib)
    ; to_sexp (ind_type_vars oib)
    ; to_sexp (ind_ctors oib)
    ; to_sexp (ind_projs oib)
    ]%sexp.

(* Record mutual_inductive_body :=
  { ind_finite : recursivity_kind;
    ind_npars : nat;
    ind_bodies : list one_inductive_body }. *)
Instance Serialize_mutual_inductive_body : Serialize mutual_inductive_body :=
  fun mib =>
    [ Atom "mutual_inductive_body"
    ; to_sexp (ind_finite mib)
    ; to_sexp (ind_npars mib)
    ; to_sexp (ind_bodies mib)
    ]%sexp.

(* Inductive global_decl :=
| ConstantDecl : constant_body -> global_decl
| InductiveDecl : mutual_inductive_body -> global_decl
| TypeAliasDecl : option (list type_var_info * box_type) -> global_decl. *)
Instance Serialize_global_decl : Serialize global_decl :=
  fun gd =>
    match gd with
    | ConstantDecl cb => [ Atom "ConstantDecl"; to_sexp cb ]
    | InductiveDecl mib => [ Atom "InductiveDecl"; to_sexp mib ]
    | TypeAliasDecl o => [ Atom "TypeAliasDecl"; to_sexp o ]
    end%sexp.

(* Definition global_env := list (kername * bool (* has_deps *) * global_decl). *)
Instance Serialize_global_env : Serialize global_env :=
  fun env =>
    to_sexp env.



(** * Deserializers *)

(* Inductive box_type :=
| TBox
| TAny
| TArr (dom : box_type) (codom : box_type)
| TApp (_ : box_type) (_ : box_type)
| TVar (_ : nat) (* Level of type variable *)
| TInd (_ : inductive)
| TConst (_ : kername). *)
Instance Deserialize_box_type : Deserialize box_type :=
  fix ds (l : loc) (e : sexp) : error + box_type :=
    Deser.match_con "box_type"
      [ ("TBox", TBox)
      ; ("TAny", TAny)
      ]
      [ ("TArr", Deser.con2 TArr ds ds)
      ; ("TApp", Deser.con2 TApp ds ds)
      ; ("TVar", Deser.con1_ TVar)
      ; ("TInd", Deser.con1_ TInd)
      ; ("TConst", Deser.con1_ TConst )
      ] l e.

(* Record type_var_info :=
  { tvar_name : name;
    tvar_is_logical : bool;
    tvar_is_arity : bool;
    tvar_is_sort : bool; }. *)
Instance Deserialize_type_var_info : Deserialize type_var_info :=
  fun l e =>
    Deser.match_con "type_var_info" []
      [ ("type_var_info", Deser.con4_ Build_type_var_info) ]
      l e.

(* Record constant_body :=
  { cst_type : list name * box_type;
    cst_body : option term; }. *)
Instance Deserialize_constant_body : Deserialize constant_body :=
  fun l e =>
    Deser.match_con "constant_body" []
      [ ("constant_body", Deser.con2_ Build_constant_body) ]
      l e.

(* Record one_inductive_body :=
  { ind_name : ident;
    ind_propositional : bool;
    ind_kelim : Universes.allowed_eliminations;
    ind_type_vars : list type_var_info;
    ind_ctors : list (ident *
                      list (name * box_type) *
                      nat (* original arities, unfortunately needed for erases_one_inductive_body *)
                     );
    ind_projs : list (ident * box_type); }. *)
Instance Deserialize_one_inductive_body : Deserialize one_inductive_body :=
  fun l e =>
    Deser.match_con "one_inductive_body" []
      [ ("one_inductive_body", con6_ Build_one_inductive_body) ]
      l e.

(* Record mutual_inductive_body :=
  { ind_finite : recursivity_kind;
    ind_npars : nat;
    ind_bodies : list one_inductive_body }. *)
Instance Deserialize_mutual_inductive_body : Deserialize mutual_inductive_body :=
  fun l e =>
    Deser.match_con "mutual_inductive_body" []
      [ ("mutual_inductive_body", Deser.con3_ Build_mutual_inductive_body) ]
      l e.

(* Inductive global_decl :=
| ConstantDecl : constant_body -> global_decl
| InductiveDecl : mutual_inductive_body -> global_decl
| TypeAliasDecl : option (list type_var_info * box_type) -> global_decl. *)
Instance Deserialize_global_decl : Deserialize global_decl :=
  fun l e =>
    Deser.match_con "global_decl"
      []
      [ ("ConstantDecl", Deser.con1_ ConstantDecl)
      ; ("InductiveDecl", Deser.con1_ InductiveDecl)
      ; ("TypeAliasDecl", Deser.con1_ TypeAliasDecl)
      ]
      l e.

(* Definition global_env := list (kername * bool (* has_deps *) * global_decl). *)
Instance Deserialize_global_env : Deserialize global_env :=
 fun l e =>
    _from_sexp l e.



(** * Main deserialization functions *)
Definition global_env_of_string (s : string) : error + global_env :=
  from_string s.
