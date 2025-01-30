From MetaCoq.Erasure Require EAst.
From LambdaBox Require LambdaBoxToWASM.
From LambdaBox Require LambdaBoxToRust.
From LambdaBox Require LambdaBoxToElm.



Definition l_box_to_wasm :=
    LambdaBoxToWASM.run_translation.

Definition l_box_to_rust :=
    LambdaBoxToRust.box_to_rust.

Definition l_box_to_elm :=
    LambdaBoxToElm.box_to_elm.
