# lstar

A formally-verified implementation of [Dana Angluin's L* algorithm](https://doi.org/10.1016/0890-5401(87)90052-6).
The implementation is based on [these lecture notes](https://www.tifr.res.in/~shibashis.guha/courses/diwali2021/L-starMalharManagoli.pdf) and can be viewed [here](theories/Lstar.v).
Functions return sigma types, so each sub-component of the algorithm provides a proof of correctness alongside its computational outputs.
The extracted OCaml code can be seen [here](bin/Lstar.ml).

## Building

```bash
# Install Dependencies
opam switch create rocq 5.3.0
opam pin add rocq-runtime 9.1.0
opam install rocq-prover dune

# Clone and build
git clone https://github.com/CharlesAverill/lstar-rocq && cd lstar-rocq
./build.sh # will build lstar-rocq, promote, then build lstar
```

Optimizations during extraction (such as using OCaml integers) are enabled by
default, but can be disabled by commenting out this line in [Extraction.v](theories/Extraction.v):

```
From lstar Require Import ExtrOptimizations.
```
