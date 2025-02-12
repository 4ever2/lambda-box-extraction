From MetaCoq.Erasure Require EAst.
From LambdaBox Require LambdaBoxToWasm.
From LambdaBox Require LambdaBoxToRust.
From LambdaBox Require LambdaBoxToElm.
From LambdaBox Require LambdaBoxToC.



Definition l_box_to_wasm :=
    LambdaBoxToWasm.run_translation.

Definition l_box_to_rust :=
    LambdaBoxToRust.box_to_rust.

Definition l_box_to_elm :=
    LambdaBoxToElm.box_to_elm.

Definition l_box_to_c :=
    LambdaBoxToC.run_translation.
