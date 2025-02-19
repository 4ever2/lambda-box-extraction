From Coq Require Import List.
From Coq Require Import String.
From MetaCoq.Utils Require Import bytestring.
From MetaCoq.Utils Require Import monad_utils.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Erasure Require Import ExAst.
From ElmExtraction Require Import PrettyPrinterMonad.
From ElmExtraction Require Import ElmExtract.
From ElmExtraction Require Import Common.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From LambdaBox Require Import TypedTransforms.

Import ListNotations.
Import MCMonadNotation.

Local Open Scope bs_scope.



#[local]
Instance ElmBoxes : ElmPrintConfig :=
  {| term_box_symbol := "()"; (* the inhabitant of the unit type *)
     type_box_symbol := "()"; (* unit type *)
     any_type_symbol := "()"; (* unit type *)
     false_elim_def := "false_rec ()"; (* predefined function *)
     print_full_names := false (* short names for readability *)|}.

Definition default_preamble : string := elm_false_rec.

Definition default_remaps : list (kername * string) := [].

Definition box_to_elm (preamble : string) (remaps : list (kername * string)) params (Σ : ExAst.global_env) : result string string :=
  let remaps_fun kn := option_map snd (List.find (fun '(kn',v) => eq_kername kn kn') remaps) in
  Σ <- typed_transfoms params Σ;;
  '(_, s) <- (finish_print (print_env Σ remaps_fun));;
  ret (preamble ++ nl ++ s ++ nl).
