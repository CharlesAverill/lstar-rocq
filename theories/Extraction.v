From Stdlib Require Import Extraction.

From lstar Require Import Lstar DFA.

Extraction Language OCaml.

Set Extraction Output Directory "lib".

(* Uncomment to use some standard OCaml types for a small speedup *)
From lstar Require Import ExtrOptimizations.

Separate Extraction Lstar.
