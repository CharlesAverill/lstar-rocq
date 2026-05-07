From Stdlib Require Import Extraction.

From lstar Require Import Lstar DFA.

Extraction Language OCaml.

Set Extraction Output Directory "lib".

(* Comment this line to turn off standard OCaml types *)
From lstar Require Import ExtrOptimizations.

Separate Extraction Lstar.
