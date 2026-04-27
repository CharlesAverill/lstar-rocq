# lstar

An implementation of the L* algorithm

## Building

```bash
# Install Dependencies
opam switch create rocq 4.14.1
opam pin add rocq-runtime 9.1.0
opam install rocq-prover dune

# Clone and build
git clone https://github.com/CharlesAverill/lstar && cd lstar
dune build
```
