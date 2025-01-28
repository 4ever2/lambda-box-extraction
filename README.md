# lambda-box-extraction
A backend for compiling $\lambda_\square$ (LambdaBox) and $\lambda_\square^T$ (LambdaBox-typed) to webassembly, Rust and other languages. The compilation phases have been verified in the Coq proof assistant.

## Setup
The backend requires OCaml 4.13 or later to run. The development also depends on Coq 8.19, and developer builds of MetaCoq and CertiCoq.

To set up a development environment run:
```bash
git clone https://github.com/AU-COBRA/lambda-box-extraction.git
cd lambda-box-extraction
opam switch create . 4.14.2 --repositories default,coq-released=https://coq.inria.fr/opam/released
eval $(opam env)
opam install . --deps-only
```

You can then build the project by running `make`.

## Usage
```
dune exec lbox -- TARGETLANGUAGE FILE [--outfile FILE]
```
E.g.
```
dune exec lbox -- wasm prog.box --outfile prog.wasm
```

## Target languages

TODO
