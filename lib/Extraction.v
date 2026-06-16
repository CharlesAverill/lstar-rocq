From Stdlib Require Import Extraction ExtrOcamlNativeString ExtrOcamlBasic ExtrOcamlNatInt.
From Stdlib Require Import Bool List PeanoNat String.

From lstar Require Import Lstar KV DFA.

Extraction Language OCaml.

#[local] Set Warnings "-extraction-opaque-accessed,-extraction-default-directory".

Extract Inlined Constant Bool.eqb => "(=)".

Separate Extraction Lstar KV DFA.
