# wasm-verify

[![Build](https://github.com/DavidMazarro/wasm-verify/actions/workflows/build.yml/badge.svg)](https://github.com/DavidMazarro/wasm-verify/actions/workflows/build.yml)

A proof-of-concept formal verification tool for WASM.

## Building from source
To build the program from the source code, you need to have GHC (the Haskell compiler) and Cabal
installed in your system. The current best way to do so is via [GHCup](https://www.haskell.org/ghcup/).

From within the project's root folder you can run the following command to build the project and automatically add the executable to your path:
```
cabal install
```
If you'd rather not have it in your path, you can build and execute the program from within the repo folder by running:
```
cabal exec -- wasm-verify <the flags you want to use>
```
If for some reason Cabal isn't working for you, try doing a `cabal update` first, or just try with Stack (simply replace `cabal` in the previous command with `stack`).
