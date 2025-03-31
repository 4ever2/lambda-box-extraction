# lambda-box-extraction
[![Build](https://github.com/AU-COBRA/lambda-box-extraction/actions/workflows/build.yml/badge.svg)](https://github.com/AU-COBRA/lambda-box-extraction/actions/workflows/build.yml)
[![GitHub](https://img.shields.io/github/license/AU-COBRA/lambda-box-extraction)](https://github.com/AU-COBRA/lambda-box-extraction/blob/master/LICENSE)

A backend for compiling $\lambda_\square$ (LambdaBox) and $\lambda_\square^T$ (LambdaBox-typed) to WebAssembly, C, Rust, OCaml and Elm. The compilation phases have been verified in the Coq proof assistant.

## Setup
The backend requires OCaml 4.13 or later to run. The development also depends on Coq 8.19, and developer builds of CertiCoq.

The backend can be installed using [Opam](https://opam.ocaml.org/doc/Install.html) with:
```bash
git clone https://github.com/AU-COBRA/lambda-box-extraction.git
cd lambda-box-extraction
opam switch create . 4.14.2 --repositories default,coq-released=https://coq.inria.fr/opam/released
eval $(opam env)
opam install .
```

## Usage
```
lbox TARGETLANGUAGE FILE [-o FILE]
```
E.g. compiling `prog.ast` file to WebAssembly.
```
lbox wasm prog.ast -o prog.wasm
```
Valid values for `TARGETLANGUAGE` are:
* `wasm`
* `c`
* `ocaml`
* `rust`
* `elm`

For detailed usage on all commands and flags see [here](#command-line-arguments) or use `lbox --help`.



## Command Line Interface
### Common arguments
* `-o FILE` output file for extracted program
* `--bypass-wf` bypass wellformedness check on input programs, note that the correctness guarantees of proofs don't apply when bypassing these checks
* `--quiet`, `--verbose`, `--debug` controls the level of feedback from the program
* `--typed=MAIN_FUNCTION` attempts to parse the input program as a $\lambda_\square^T$ program rather than $\lambda_\square$, only available for untyped extraction targets
* `--opt` enable extra optimizations

### Extraction commands
```
lbox TARGETLANGUAGE FILE [-o FILE]
```
Valid values for `TARGETLANGUAGE` are:
* `wasm`
* `c`
* `ocaml`
* `rust`
* `elm`

The `wasm` and `c` targets also supports the `--cps` flag that uses verified cps translation during compilation instead of the unverified direct translation.


