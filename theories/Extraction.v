From MetaCoq.Erasure Require EAst.
From LambdaBox Require Translations.
From Coq Require Import Ascii FSets ExtrOcamlBasic ExtrOCamlFloats ExtrOCamlInt63 Extraction.
From Coq Require Import ZArith NArith.

Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

Extract Inductive Decimal.int => "decimal_int" [ "DecimalPos" "DecimalNeg" ] "(fun hp hn d -> match d with DecimalPos p -> hp p | DecimalNeg p -> hn p)".
Extract Inductive Hexadecimal.int => "hexadecimal_int" [ "HexadecimalPos" "HexadecimalNeg" ] "(fun hp hn d -> match d with HexadecimalPos p -> hp p | HexadecimalNeg p -> hn p)".
Extract Inductive Number.int => "number_int" [ "IntDecimal" "IntHexadecimal" ] "(fun hp hn d -> match d with IntDecimal p -> hp p | IntHexadecimal p -> hn p)".

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

Set Warnings "-extraction-reserved-identifier".
Set Warnings "-extraction-opaque-accessed".




(* Extraction Library Zeven.
Extraction Library Zeven.
Extraction Library ZArith_dec.
Extraction Library Sumbool.
Extraction Library Zbool.
Extraction Library SpecFloat.
Separate Extraction FloatOps.Prim2SF. *)

Set Extraction Output Directory "src/".

Separate Extraction Translations.run_translation.

Recursive Extraction Library Ascii.
Recursive Extraction Library BinPos.
Recursive Extraction Library OrdersTac.
