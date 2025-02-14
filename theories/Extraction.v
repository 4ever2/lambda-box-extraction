From MetaCoq.Erasure Require EAst.
From LambdaBox Require CheckWf.
From LambdaBox Require Eval.
From LambdaBox Require Translations.
From LambdaBox Require SerializePrimitives.
From LambdaBox Require Serialize.
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

(* TODO: validate prim int implementations *)
Extract Constant SerializePrimitives.string_of_prim_int =>
  "(fun i -> i |> Uint63.to_int64 |> Int64.to_string)".
Extract Constant SerializePrimitives.prim_int_of_string =>
  "(fun s -> s |> Int64.of_string |> Uint63.of_int64)".

(* TODO: validate prim float implementations *)
Extract Constant SerializePrimitives.string_of_prim_float =>
  "(fun f -> f |> Float64.to_float |> Int64.bits_of_float |> Int64.to_string)".
Extract Constant SerializePrimitives.prim_float_of_string =>
  "(fun s -> s |> Int64.of_string |> Int64.float_of_bits |> Float64.of_float)".


Set Warnings "-extraction-reserved-identifier".
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-logical-axiom".
Set Extraction Output Directory "src/extraction/".

Require compcert.cfrontend.Csyntax
        compcert.cfrontend.Clight.

Separate Extraction Translations.l_box_to_wasm CertiCoqPipeline.show_IR CertiCoqPipeline.make_opts
                    Translations.l_box_to_rust LambdaBoxToRust.default_remaps
                    Translations.l_box_to_elm LambdaBoxToElm.default_remaps LambdaBoxToElm.default_preamble
                    Translations.l_box_to_c
                    TypedTransforms.mk_params
                    Eval.eval_box Eval.eval_box_typed
                    CheckWf.check_wf_program CheckWf.CheckWfExAst.check_wf_typed_program CheckWf.agda_eflags CheckWf.agda_typed_eflags
                    Serialize.program_of_string Serialize.global_env_of_string Serialize.kername_of_string Serialize.string_of_error
                    Floats.Float32.to_bits Floats.Float.to_bits
                    Floats.Float32.of_bits Floats.Float.of_bits
                    Csyntax
                    Clight.
