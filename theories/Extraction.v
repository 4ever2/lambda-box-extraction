From MetaCoq.Erasure Require EAst.
From LambdaBox Require Translations.
From LambdaBox Require SerializePrimitives.
From LambdaBox Require SerializeEAst.
From LambdaBox Require SerializeExAst.
From LambdaBox Require CeresExtra.
From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOCamlFloats.
From Coq Require Import ExtrOCamlInt63.
From Coq Require Import ExtrOcamlNativeString.
From Coq Require Import Extraction.



Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

Extraction Inline Equations.Prop.Classes.noConfusion.
Extraction Inline Equations.Prop.Logic.eq_elim.
Extraction Inline Equations.Prop.Logic.eq_elim_r.
Extraction Inline Equations.Prop.Logic.transport.
Extraction Inline Equations.Prop.Logic.transport_r.
Extraction Inline Equations.Prop.Logic.False_rect_dep.
Extraction Inline Equations.Prop.Logic.True_rect_dep.
Extraction Inline Equations.Init.pr1.
Extraction Inline Equations.Init.pr2.
Extraction Inline Equations.Init.hidebody.
Extraction Inline Equations.Prop.DepElim.solution_left.

Extraction Blacklist config List String Nat Int Ast Universes UnivSubst Typing Retyping
           OrderedType Logic Common Equality Char char uGraph
           Instances Classes Term Monad Coqlib Errors Compile Checker Eq Classes0 Numeral
           Uint63 Number Values Bytes.


(* TODO: add time implementation if *)
Extract Constant MetaCoq.Common.Transform.time =>
  "(fun c f x -> f x)".

(* TODO: implement primitive integer serialization *)
Extract Constant SerializePrimitives.prim_int_of_Z =>
  "(fun x -> failwith ""AXIOM TO BE REALIZED"")".
Extract Constant SerializePrimitives.Z_of_prim_int =>
  "(fun x -> failwith ""AXIOM TO BE REALIZED"")".

(* TODO: implement primitive float serialization *)
Extract Constant SerializePrimitives.string_of_prim_float =>
  "(fun x -> failwith ""AXIOM TO BE REALIZED"")".
Extract Constant SerializePrimitives.prim_float_of_string =>
  "(fun x -> failwith ""AXIOM TO BE REALIZED"")".


Set Warnings "-extraction-reserved-identifier".
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-logical-axiom".
Set Extraction Output Directory "src/".

Separate Extraction Translations.l_box_to_wasm
                    Translations.l_box_to_rust LambdaBoxToRust.default_remaps
                    Translations.l_box_to_elm LambdaBoxToElm.default_remaps LambdaBoxToElm.default_preamble
                    SerializeEAst.program_of_string SerializeExAst.global_env_of_string CeresExtra.string_of_error.
