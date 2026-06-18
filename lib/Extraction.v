From Stdlib Require Import Bool List String.
From Stdlib Require Import Extraction ExtrOcamlNativeString ExtrOcamlBasic ExtrOcamlNatInt.

From lstar Require Import Lstar KV DFA RS.

Extraction Language OCaml.

#[local] Set Warnings "-extraction-opaque-accessed,-extraction-default-directory".

Extract Inlined Constant Bool.eqb => "(=)".

Separate Extraction Lstar KV DFA RS.
