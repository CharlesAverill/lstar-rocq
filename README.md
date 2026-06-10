# lstar-rocq

A collection of formally-verified implementations of [automata learning](https://wcventure.github.io/Active-Automata-Learning/) algorithms.

| Algorithm | Resources | Proofs |
| --- | --- | --- |
| L* | [Angluin, 1987](https://doi.org/10.1016/0890-5401(87)90052-6), [Lecture Notes](https://www.tifr.res.in/~shibashis.guha/courses/diwali2021/L-starMalharManagoli.pdf) | [Lstar.v](theories/Lstar.v) |
| Kearns-Vazirani | [Kearns-Vazirani, 1994](https://doi.org/10.7551/mitpress/3897.003.0009), [Balle, 2010](https://borjaballe.github.io/papers/zulu10.pdf) | [KV.v](theories/KV.v) |

Functions return sigma types, so each sub-component of each algorithm provides a proof of correctness alongside its computational outputs.

## Building

```bash
# Install Dependencies
opam switch create rocq 5.3.0
opam pin add rocq-runtime 9.1.0
opam install rocq-prover dune

# Clone and build
git clone https://github.com/CharlesAverill/lstar-rocq && cd lstar-rocq
make # will build lstar-rocq, extract, then build lstar
```

Optimizations during extraction (such as using OCaml integers) are enabled by
default, but can be disabled by commenting out this line in [Extraction.v](lib/Extraction.v):

```
From lstar Require Import ExtrOptimizations.
```

The following example file will break without optimizations turned on.

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

Examples `lstar.div7` and `lstar.mod3` show the learning of DFAs for decimal strings divisible by 7, and binary strings where the number of `1`s is divisible by 3.
