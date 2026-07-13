From Stdlib Require Import Bool List String PeanoNat.
From Stdlib Require Import Extraction ExtrOcamlNativeString ExtrOcamlBasic ExtrOcamlNatInt.

From lstar Require Import Lstar Lstar_Moore KV Automata TTT NLstar.

Extraction Language OCaml.

#[local] Set Warnings "-extraction-opaque-accessed,-extraction-default-directory".

Extract Inlined Constant Bool.eqb => "(=)".

Separate Extraction Lstar Lstar_Moore KV DFA NFA RFSA Moore TTT NLstar.
