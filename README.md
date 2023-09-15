<div align="center">

  <h1><code>wasm-verify</code></h1>

  <p>
    <strong>A proof-of-concept formal verification tool for WebAssembly. Based on the researched performed during
the development of my master's thesis <a href="https://oa.upm.es/75802/1/TFM_DAVID_MUNUERA_MAZARRO.pdf">"<i>Specification and verification of WebAssembly programs</i>"</a>.</strong>
  </p>

  <p>
    <a href="https://github.com/DavidMazarro/wasm-verify/actions/workflows/build.yml"><img src="https://github.com/DavidMazarro/wasm-verify/actions/workflows/build.yml/badge.svg" alt="Build Status" /></a>
  </p>

</div>

________________________
To learn how to write specifications in **VerifiWASM**, the specification language supported in `wasm-verify`, you can take a look at some of the [examples](examples/) in this repo, or read Chapter 4 - "*VerifiWASM: the specification language*" in the thesis.

The verification results provided by `wasm-verify` are of **partial correctness**. That is: **assuming** the given function terminates, **then** it is correct. To achieve **total correctness**, you would also need to have some sort of termination proof for the function provided, which is not currently supported by `wasm-verify`.

# Installation

The release of `wasm-verify` does not currently ship with binary releases, so the only installation method is building from source.

## Building from source
To build the executable and library from the source code, you need to have GHC (the Haskell compiler) and Cabal
installed in your system. The current best way to do so is via [GHCup](https://www.haskell.org/ghcup/).

From within the project's root folder you can run the following command to build the project and automatically add the executable to your path:
```
cabal install
```
If you would rather not have it in your path, you can build and execute the program from within the repo folder by running:
```
cabal exec -- wasm-verify <the flags you want to use>
```
If for some reason Cabal isn't working for you, try doing a `cabal update` first. As an alternative, you can try with [Stack](https://docs.haskellstack.org/en/stable/).

## Dependencies
You also need to have the SMT solver [Z3](https://github.com/z3prover/z3) installed in your system
and included in your PATH, since `wasm-verify` relies on it for discharging the verification conditions as part of the verification process.

# Usage
To use `wasm-verify`, run the command providing it with the WebAssembly
module containing the functions you want to verify and the VerifiWASM
specification. Try it out with one of the [examples](examples/):
```
wasm-verify ./examples/fib.wasm --spec ./examples/fib.verifiwasm
```
(or you can use the short version of `--spec`, which is `-s`).

This will print the verification results of each of the functions in the command-line. 
## Available flags
|Flag|Description|
|-------|-----------|
|`--help` (short ver. `-h`)|Offers general help regarding usage and the available flags (described in this table).|
|`--debug-wasm-adt`|Prints into the command line the internal representation (the AST) of the WebAssembly module provided, as parsed by the [`parse`](https://hackage.haskell.org/package/wasm-1.1.1/docs/Language-Wasm.html#v:parse) function in the [wasm](https://hackage.haskell.org/package/wasm) library.| 
|`--debug-spec-adt`|Prints into the command line the internal representation of the VerifiWASM specification provided, as parsed by the `parseVerifiWASMFile` function.|
|`--debug-cfg`|Prints into the command line the internal representation of the **control flow graphs (CFGs)** corresponding to the WebAssembly functions in the module provided, as generated by the `functionToCFG` function.|
|`--debug-smt`|Prints into the command line the SMT scripts generated for each of the execution paths in the symbolic execution. Each SMT script represents the satisfiability of a **verification condition (VC)**.|

________
## Additional notes
### GHC versions
The project is tested to build for GHC versions 8.10.7 (latest GHC 8) and 9.2.6.

The project is most likely incompatible with GHC versions older than 8.2.1 because we make use of [naturalFromInteger](https://hackage.haskell.org/package/base-4.18.0.0/docs/GHC-Natural.html#v:naturalFromInteger) which was added in `base-4.10.0.0`.
