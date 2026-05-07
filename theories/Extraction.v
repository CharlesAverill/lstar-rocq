From Stdlib Require Import Extraction.

From lstar Require Import Lstar.

Extraction Language OCaml.

Set Extraction Output Directory "bin".

(* Uncomment to use some standard OCaml types for a small speedup *)
From lstar Require Import ExtrOptimizations.

Separate Extraction Lstar.
