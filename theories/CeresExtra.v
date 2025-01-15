From Ceres Require Import Ceres.


Local Notation "p >>= f" := (Deser.bind_field p f) (at level 50, left associativity) : deser_scope.
Local Open Scope deser_scope.

Definition con6 {A B C D E F R} (f : A -> B -> C -> D -> E -> F -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F -> FromSexpList R :=
  fun pa pb pc pd pe pf =>
    Deser.fields (pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e => pf >>= fun f' =>
    Deser.ret (f a b c d e f')).

Definition con6_ {A B C D E F R} (f : A -> B -> C -> D -> E -> F -> R)
    `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E} `{Deserialize F}
  : FromSexpList R :=
  con6 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con7 {A B C D E F G R} (f : A -> B -> C -> D -> E -> F -> G -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F -> FromSexp G -> FromSexpList R :=
  fun pa pb pc pd pe pf pg =>
    Deser.fields (pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e => pf >>= fun f' => pg >>= fun g =>
    Deser.ret (f a b c d e f' g)).

Definition con7_ {A B C D E F G R} (f : A -> B -> C -> D -> E -> F -> G -> R)
    `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E} `{Deserialize F} `{Deserialize G}
  : FromSexpList R :=
  con7 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con8 {A B C D E F G H R} (f : A -> B -> C -> D -> E -> F -> G -> H -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F -> FromSexp G -> FromSexp H -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph =>
    Deser.fields (pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e => pf >>= fun f' => pg >>= fun g => ph >>= fun h =>
    Deser.ret (f a b c d e f' g h)).

Definition con8_ {A B C D E F G H R} (f : A -> B -> C -> D -> E -> F -> G -> H -> R)
    `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E} `{Deserialize F} `{Deserialize G} `{Deserialize H}
  : FromSexpList R :=
  con8 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con9 {A B C D E F G H I R} (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi =>
    Deser.fields (pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e => pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i =>
    Deser.ret (f a b c d e f' g h i)).

Definition con9_ {A B C D E F G H I R} (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> R)
    `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E} `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I}
  : FromSexpList R :=
  con9 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

Definition con10 {A B C D E F G H I J R} (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexp F -> FromSexp G -> FromSexp H -> FromSexp I -> FromSexp J -> FromSexpList R :=
  fun pa pb pc pd pe pf pg ph pi pj =>
    Deser.fields (pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e => pf >>= fun f' => pg >>= fun g => ph >>= fun h => pi >>= fun i => pj >>= fun j =>
    Deser.ret (f a b c d e f' g h i j)).

Definition con10_ {A B C D E F G H I J R} (f : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> R)
    `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E} `{Deserialize F} `{Deserialize G} `{Deserialize H} `{Deserialize I} `{Deserialize J}
  : FromSexpList R :=
  con10 f _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.
