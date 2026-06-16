From Stdlib Require Import Extraction ExtrOcamlNativeString ExtrOcamlBasic.
From Stdlib Require Import Bool List PeanoNat String.

From lstar Require Import Lstar KV DFA.

Extraction Language OCaml.

#[local] Set Warnings "-extraction-opaque-accessed,-extraction-default-directory".

Extract Inductive nat => int [ "0" "succ" ]
   "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive result => "result" ["Ok" "Error"].

Extract Inlined Constant Bool.eqb => "(=)".
Extract Inlined Constant negb => "not".
Extract Inlined Constant List.app => "(@)".
Extract Inlined Constant List.length => "Stdlib.List.length".
Extract Inlined Constant List.existsb => "Stdlib.List.exists".
Extract Inlined Constant List.forallb => "Stdlib.List.for_all".
Extract Inlined Constant List.find => "Stdlib.List.find_opt".
Extract Inlined Constant List.map => "Stdlib.List.map".
Extract Inlined Constant List.nth_error => "Stdlib.List.nth_opt".
Extract Constant Nat.pow =>
"let rec pow x n =
    if n = 0 then 1
    else x * pow x (n - 1)
   in pow".

Separate Extraction Lstar KV DFA.
