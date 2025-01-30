From Coq Require Import List.
From Coq Require Import String.
From MetaCoq.Utils Require Import bytestring.
From MetaCoq.Erasure Require Import ExAst.

From ElmExtraction Require Import PrettyPrinterMonad.
From ElmExtraction Require Import ElmExtract.
From ElmExtraction Require Import Common.

Import ListNotations.

Local Open Scope bs_scope.


From MetaCoq Require ExAst.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Utils Require Import monad_utils.
From MetaCoq.Common Require Import Kernames.
Import MCMonadNotation.

#[local]
Instance ElmBoxes : ElmPrintConfig :=
  {| term_box_symbol := "()"; (* the inhabitant of the unit type *)
     type_box_symbol := "()"; (* unit type *)
     any_type_symbol := "()"; (* unit type *)
     false_elim_def := "false_rec ()"; (* predefined function *)
     print_full_names := false (* short names for readability *)|}.

Definition default_preamble : string := elm_false_rec.

Definition default_remaps : list (kername * string) := [].

Definition box_to_elm (Σ : ExAst.global_env) (preamble : string) (remaps : list (kername * string)) : result string string :=
  let remaps_fun kn := option_map snd (List.find (fun '(kn',v) => eq_kername kn kn') remaps) in
  '(_, s) <- (finish_print (print_env Σ remaps_fun));;
  ret (preamble ++ nl ++ s ++ nl).
