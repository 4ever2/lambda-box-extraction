From Stdlib Require Import List.
From MetaRocq.Utils Require Import bytestring.

Import ListNotations.

Local Open Scope bs_scope.

Module Tree.
  Inductive t :=
  | string : String.t -> t
  | append : t -> t -> t
  | nl : t -> t -> t
  | indent : t -> t.

  Coercion string : String.t >-> t.

  Infix "++" := append.

  Definition new_line : String.t := String.String Byte.x0a String.EmptyString.

  Definition mk_parens (a b : String.t) : t -> t :=
    fun s => a ++ s ++ b.

  Definition parens := mk_parens "(" ")".
  Definition brackets := mk_parens "[" "]".
  Definition braces := mk_parens "{" "}".
  Definition record := mk_parens "{|" "|}".

  Fixpoint join (sep : String.t) (l : list t) : t :=
    match l with
    | [] => ""
    | x :: [] => x
    | x :: l => x ++ sep ++ (join sep l)
    end.

  Fixpoint join_nl (l : list t) : t :=
    match l with
    | [] => ""
    | x :: [] => x
    | x :: l => nl x (join_nl l)
    end.

  Inductive t' :=
  | string' : String.t -> t'
  | append' : t' -> t' -> t'.

  Definition t'_of_t t (ind : String.t) :=
    let fix aux t l (n : bool) :=
      match t with
      | string s =>
        if n
        then append' l (string' s)
        else string' s
      | append s s' =>
      let s := if n then append' l (aux s l false) else aux s l false in
      append' s (aux s' l false)
      | nl s s' =>
        let s := if n then append' l (aux s l false) else aux s l false in
        append' s (append' (string' new_line) (aux s' l true))
      | indent s => aux s (append' (string' ind) l) n
      end
    in aux t (string' "") false.

  Fixpoint to_rev_list_aux t acc :=
    match t with
    | string' s => cons s acc
    | append' s s' => to_rev_list_aux s' (to_rev_list_aux s acc)
    end.

  Fixpoint to_string_acc acc l :=
    match l with
    | nil => acc
    | cons s xs => to_string_acc (String.append s acc) xs
    end.

  Definition to_string t :=
    let t := t'_of_t t " " in
    let l := to_rev_list_aux t nil in
    to_string_acc "" l.
End Tree.

From Ceres Require Import CeresS.

Import Tree.

Fixpoint t_of_sexp (s : sexp) : Tree.t :=
  match s with
  | Atom_ a =>
    match a with
    | Num n => CeresString.string_of_Z n
    | Str s => CeresString.escape_string s
    | Raw s => s
    end
  | List nil => "()"
  | List (x :: nil) => parens (t_of_sexp x)
(*   | List (x1 :: x2 :: nil) =>
    let x1 := t_of_sexp x1 in
    let x2 := t_of_sexp x2 in
    parens (append x1 (append " " x2)) *)
  | List xs =>
    let xs' := map t_of_sexp xs in
    parens (indent (join_nl xs'))
  end.

From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Common Require Kernames.
From MetaRocq.Utils Require MRString.


Definition t_of_ident (id : Kernames.ident) : Tree.t := id.

Definition t_of_dirpath (dp : Kernames.dirpath) : Tree.t :=
  join "." (map t_of_ident (rev dp)).

Fixpoint t_of_modpath (mp : Kernames.modpath) : Tree.t :=
  match mp with
  | Kernames.MPfile dp => t_of_dirpath dp
  | Kernames.MPbound dp id n => t_of_dirpath dp ++ (String.String "." id) ++ (String.String "." (MRString.string_of_nat n))
  | Kernames.MPdot mp id => t_of_modpath mp ++ (String.String "." id)
  end.

Definition t_of_kername (kn : Kernames.kername) : Tree.t :=
  let (mp, id) := kn in
  let mp := t_of_modpath mp in
  mp ++ (String.String "." id).

Fixpoint t_of_term (t : term) : Tree.t :=
  match t with
  | tBox => "□"
  | tRel n => "@" ++ (MRString.string_of_nat n)
  | tVar i => "TODO"
  | tEvar n l => "TODO"
  | tLambda na t => "TODO"
  | tLetIn na b t => "TODO"
  | tApp u v => (t_of_term u) ++ " " ++ parens (t_of_term v)
  | tConst k => t_of_kername k
  | tConstruct ind n args => "TODO"
  | tCase indn c brs => "TODO"
  | tProj p c => "TODO"
  | tFix mfix idx => "TODO"
  | tCoFix mfix idx => "TODO"
  | tPrim prim => "TODO"
  | tLazy t => "lazy" ++ (parens (t_of_term t))
  | tForce t => "force" ++ (parens (t_of_term t))
  end.

Definition t_of_constant_body (cb : constant_body) : Tree.t :=
  let body :=
    match cb.(cst_body) with
    | None => "AXIOM"
    | Some b => t_of_term b
    end
  in
  nl "body:" (indent body).

Definition t_of_constructor_body (cstr : constructor_body) : Tree.t :=
  cstr.(cstr_name) ++ " " ++ (parens ((MRString.string_of_nat cstr.(cstr_nargs)) ++ " arg(s)")).

Definition t_of_one_inductive_body (ind : one_inductive_body) : Tree.t :=
  let cstrs := map t_of_constructor_body ind.(ind_ctors) in
  nl ind.(ind_name) (indent
    (nl "constructors:" (indent (join_nl cstrs))
    )).

Definition t_of_global_decl (d : global_decl) : Tree.t :=
  match d with
  | ConstantDecl cb =>
    let cb := t_of_constant_body cb in
    nl "constant declaration:" (indent cb)
  | InductiveDecl mib =>
    let oibs := map t_of_one_inductive_body mib.(ind_bodies) in
    nl "mutual inductive(s):" (indent (join_nl oibs))
  end.

Definition t_of_global_context (env : global_context) : Tree.t :=
  let env := map (fun '(kn, d) =>
    let kn := t_of_kername kn in
    let d := t_of_global_decl d in
    nl (nl (kn ++ ":") (indent d)) ""
  ) env in
  join_nl env.

Definition t_of_program (p : program) : Tree.t :=
  let env := t_of_global_context (fst p) in
  let t := t_of_term (snd p) in
  env ++
  (nl "Main program: " (indent t)).


From Ceres Require Import Ceres.

From Peregrine Require Import SerializeEAst.

Definition exp := SerializeEAst.program_of_string "(((((MPfile (""Exports"" ""Exports"")) ""eone"") (ConstantDecl (constant_body (Some (tLambda nAnon (tCase ((inductive ((MPfile (""Exports"")) ""Exports"") 0) 0) (tRel 0) (((nAnon nAnon nAnon nAnon) (tRel 3))))))))) (((MPfile (""Exports"" ""Exports"")) ""etwo"") (ConstantDecl (constant_body (Some (tLambda nAnon (tCase ((inductive ((MPfile (""Exports"")) ""Exports"") 0) 0) (tRel 0) (((nAnon nAnon nAnon nAnon) (tRel 2))))))))) (((MPfile (""Exports"" ""Exports"")) ""ethree"") (ConstantDecl (constant_body (Some (tLambda nAnon (tCase ((inductive ((MPfile (""Exports"")) ""Exports"") 0) 0) (tRel 0) (((nAnon nAnon nAnon nAnon) (tRel 1))))))))) (((MPfile (""Exports"" ""Exports"")) ""efour"") (ConstantDecl (constant_body (Some (tLambda nAnon (tCase ((inductive ((MPfile (""Exports"")) ""Exports"") 0) 0) (tRel 0) (((nAnon nAnon nAnon nAnon) (tRel 0))))))))) (((MPfile (""Exports"")) ""main"") (ConstantDecl (constant_body (Some (tConstruct (inductive ((MPfile (""Exports"")) ""Exports"") 0) 0 ((tConst ((MPfile (""Exports"")) ""one"")) (tConst ((MPfile (""Exports"")) ""two"")) (tConst ((MPfile (""Exports"")) ""three"")) (tConst ((MPfile (""Exports"")) ""four"")))))))) (((MPfile (""Exports"")) ""Exports"") (InductiveDecl (mutual_inductive_body Finite 0 ((one_inductive_body ""Exports"" false IntoAny ((constructor_body ""constructor"" 4)) ()))))) (((MPfile (""Exports"")) ""four"") (ConstantDecl (constant_body (Some (tFix ((def (nNamed ""four"") (tLambda nAnon (tLambda nAnon (tCase ((inductive ((MPfile (""Agda"" ""Builtin"" ""Nat"")) ""Nat"") 0) 0) (tRel 1) ((() (tRel 0)) ((nAnon) (tConstruct (inductive ((MPfile (""Agda"" ""Builtin"" ""Nat"")) ""Nat"") 0) 1 ((tApp (tApp (tRel 3) (tRel 0)) (tRel 1))))))))) 0)) 0))))) (((MPfile (""Exports"")) ""three"") (ConstantDecl (constant_body (Some (tLambda nAnon (tCase ((inductive ((MPfile (""Agda"" ""Builtin"" ""Nat"")) ""Nat"") 0) 0) (tRel 0) ((() (tConstruct (inductive ((MPfile (""Agda"" ""Builtin"" ""Nat"")) ""Nat"") 0) 0 ())) ((nAnon) (tRel 0))))))))) (((MPfile (""Exports"")) ""two"") (ConstantDecl (constant_body (Some (tConstruct (inductive ((MPfile (""Agda"" ""Builtin"" ""Nat"")) ""Nat"") 0) 1 ((tConstruct (inductive ((MPfile (""Agda"" ""Builtin"" ""Nat"")) ""Nat"") 0) 1 ((tConstruct (inductive ((MPfile (""Agda"" ""Builtin"" ""Nat"")) ""Nat"") 0) 0 ()))))))))) (((MPfile (""Exports"")) ""one"") (ConstantDecl (constant_body (Some (tConstruct (inductive ((MPfile (""Agda"" ""Builtin"" ""Nat"")) ""Nat"") 0) 1 ((tConstruct (inductive ((MPfile (""Agda"" ""Builtin"" ""Nat"")) ""Nat"") 0) 0 ()))))))) (((MPfile (""Agda"" ""Builtin"" ""Nat"")) ""Nat"") (InductiveDecl (mutual_inductive_body Finite 0 ((one_inductive_body ""Nat"" false IntoAny ((constructor_body ""zero"" 0) (constructor_body ""suc"" 1)) ()))))) (((MPfile (""LamBox"")) ""Empty"") (InductiveDecl (mutual_inductive_body Finite 0 ((one_inductive_body ""Empty"" false IntoAny () ())))))) (tConst ((MPfile (""Exports"")) ""main"")))".
Time Compute (match exp with
| inr p => Tree.to_string (t_of_program p)
| inl e => ""
end
).

Time Compute (match exp with
| inr p => to_string p
| inl e => ""
end
).
Time Compute (match exp with
| inr p => Tree.to_string (t_of_sexp (to_sexp p))
| inl e => ""
end
).

Definition exp := [
  [[0;0];[1;1]];
  [[2];[3;3]];
  [[4;4;4];[5];[6;6]]
].
(* Definition exp := [
1;2;3
]. *)

Definition exp' : sexp := to_sexp exp.
Time Compute to_string exp'.
Time Compute Tree.to_string (t_of_sexp exp').

(((0
   0)
  (1
   1))
 ((2)
  (3
   3))
 ((4
   4
   4)
  (5)
  (6
   6)))
