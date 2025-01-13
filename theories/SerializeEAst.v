From MetaCoq.Erasure Require Import EAst.
From Coq Require Import List ZArith String.
From Ceres Require Import Ceres.

Import ListNotations.
Local Open Scope string_scope.



Local Notation "'bs_to_s' s" := (bytestring.String.to_string s) (at level 200).
Local Notation "'s_to_bs' s" := (bytestring.String.of_string s) (at level 200).

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

Instance Serialize_name : Serialize BasicAst.name :=
  fun n =>
    match n with
    | BasicAst.nAnon => Atom "nAnon"
    | BasicAst.nNamed i => [ Atom "nNamed"; to_sexp i ]
    end%sexp.

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
