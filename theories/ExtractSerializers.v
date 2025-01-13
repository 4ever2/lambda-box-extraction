From Coq Require Import ExtrOcamlBasic ExtrOCamlFloats ExtrOCamlInt63 Extraction.
From Coq Require Import ExtrOcamlString.
From LambdaBox Require SerializeEAst.

Set Extraction Output Directory "src2/".
Separate Extraction SerializeEAst.term_of_string.
