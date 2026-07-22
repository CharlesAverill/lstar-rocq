From Stdlib Require Import Bool List String PeanoNat.
From Stdlib Require Import Extraction ExtrOcamlNativeString ExtrOcamlBasic ExtrOcamlNatInt.

From lstar Require Import Lstar_DFA Lstar_Moore Lstar_Mealy
                          NLstar
                          KV_DFA KV_Moore_Binary KV_Mealy_Binary
                          TTT_DFA TTT_Moore_Binary TTT_Mealy_Binary
                          automata.DFA automata.NFA automata.Mealy automata.Moore.

Extraction Language OCaml.

#[local] Set Warnings "-extraction-opaque-accessed,-extraction-default-directory".

Extract Inlined Constant Bool.eqb => "(=)".

Separate Extraction Lstar_DFA Lstar_Moore Lstar_Mealy
                    KV_DFA KV_Moore_Binary KV_Mealy_Binary
                    TTT_DFA TTT_Moore_Binary TTT_Mealy_Binary
                    NLstar
                    DFA NFA RFSA Moore Mealy.
