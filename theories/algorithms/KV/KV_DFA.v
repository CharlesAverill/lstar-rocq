(** Kearns-Vazirani automata learning
    https://doi.org/10.7551/mitpress%2F3897.001.0001 *)

From lstar Require Import automata.DFA Teacher MooreDFA KV_Moore_Binary.

Module KV (s : Symbol) (L : RegularLanguage s) (Tch : DFATeacher s L).
Import s L.

(** The Moore view of [L] and [Tch] *)
Module V := MooreView s L Tch.

Module Type Learner.
    Parameter mkv : unit -> { m : V.ML.M.t nat | V.ML.minimal m }.
End Learner.

Module MImpl : Learner := KV_Moore_Binary s BoolOutput V.ML V.MT.

Definition kv (_ : unit) : { d : D.t nat | minimal d } :=
    let (m, pf) := MImpl.mkv tt in
    exist _ (V.ML.to_dfa m) (V.minimal_to_dfa m pf).

End KV.
