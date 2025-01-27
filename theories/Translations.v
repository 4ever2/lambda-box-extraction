From MetaCoq.Erasure Require EAst.
From LambdaBox Require LambdaBoxToWASM.



Definition l_box_to_wasm :=
    LambdaBoxToWASM.run_translation.
