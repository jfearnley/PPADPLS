# The Complexity of Gradient Descent: CLS = PPAD ∩ PLS
## Source code for automated proof

This repository contains the full source code for the automated proof used in the paper. 

To compile and run the proof, you will need the following
* A working installation of `ghc`. This can be installed by using [ghcup](https://www.haskell.org/ghcup/).
* The `z3` theorem prover should be installed and available in the `PATH`. You can compile and install it from the source code found in the project's [Github repository](https://github.com/Z3Prover/z3).

To compile and run the proof, use the following commands
```
$ cabal update
$ cabal run
```

The program will output a proof report to `report/report.tex`, which is a Latex document that contains the output of the proof. 

If you don't want to run the proof yourself, you can find a precompiled version of the report in `report/report_static.pdf`.
