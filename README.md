# lstar

A formally-verified implementation of [Dana Angluin's L* algorithm](https://doi.org/10.1016/0890-5401(87)90052-6).
The implementation is based on [these lecture notes](https://www.tifr.res.in/~shibashis.guha/courses/diwali2021/L-starMalharManagoli.pdf) and can be viewed [here](theories/Lstar.v).
Functions return sigma types, so each sub-component of the algorithm provides a proof of correctness alongside its computational outputs.
The extracted OCaml code can be seen [here](lib/Lstar.ml).

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

## Example

An example execution is provided in [alternating.ml](examples/alternating.ml).
The target language is alternating bit strings (e.g., "01", "10", "101", "0101", etc.).
Running `dune exec lstar.alternating` will start the learning algorithm, report that it has found a DFA that encodes the language, and then run some test cases for bit strings of length 3:

```
$ dune exec lstar.alternating
DFA found                          
Input       Expected  Got       Correct 
[000]       false     false     Y
[001]       false     false     Y
[010]       true      true      Y
[011]       false     false     Y
[100]       false     false     Y
[101]       true      true      Y
[110]       false     false     Y
[111]       false     false     Y
Accuracy: 8/8
```
