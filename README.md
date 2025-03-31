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


### Frontends
The lbox tool compiles $\lambda_\square$ and $\lambda_\square^T$ to various langauges, the $\lambda_\square$ programs can be obtained from either Coq or Agda using the frontends described here.

#### Agda (Agda2lambox)
[Agda2lambox](https://github.com/agda/agda2lambox) is a backend for [Agda](https://github.com/agda/agda) translating Agda programs into $\lambda_\square$ and $\lambda_\square^T$.

To use the Agda2lambox frontend you should first annotate the definition you wish to translate with `{-# COMPILE AGDA2LAMBOX DEF_NAME #-}`.
For example
```
test = ...
{-# COMPILE AGDA2LAMBOX test #-}
```

The program can then be translated to $\lambda_\square$ using
```
agda2lambox FILE
```
or to $\lambda_\square^T$ using
```
agda2lambox --typed --no-block FILE
```

#### Coq (MetaCoq)
[MetaCoq](https://github.com/MetaRocq/metarocq) is a project formalizing Coq in Coq and providing tools for manipulating Coq terms and developing certified plugins (i.e. translations, compilers or tactics) in Coq. It can be used to translate Coq programs into $\lambda_\square$ and $\lambda_\square^T$ using [CoqToLambdaBox.v](theories/CoqToLambdaBox.v).

For extracting Coq programs it is recommended to use the respective extraction backends in Coq rather than using the standalone lbox tool.


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

### Debug commands
These commands main purpose are for debugging $\lambda_\square$ programs and the compilation pipeline.

#### $\lambda_\square$ evaluator
This command evaluates $\lambda_\square$ programs, the `--anf` flag can be used to use an alternative evaluator which first translates the program to $\lambda_{ANF}$ before evaluating the program.
```
lbox eval FILE [-anf]
```

Also supports the `--cps, --opt, --typed` flags.

#### $\lambda_\square$ validator
```
lbox validate FILE
```
Validates that the program in `FILE` can be parsed and is wellformed.

Also supports the `--typed` flag.

#### $\lambda_{ANF}$ compiler
Compiles $\lambda_\square$ to $\lambda_{ANF}$, used for inspecting intermediate representations.
```
lbox anf FILE
```

Also supports the `--cps, --opt, --typed` flags.
