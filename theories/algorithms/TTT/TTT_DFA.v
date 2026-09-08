(** TTT automata learning
    https://doi.org/10.1007/978-3-319-11164-3 *)
From lstar Require Import automata.DFA Teacher MooreDFA TTT_Moore_Binary.

Module TTT (s : Symbol) (L : RegularLanguage s) (Tch : DFATeacher s L).
Import s L.

(** The Moore view of [L] and [Tch] *)
Module V := MooreView s L Tch.

Module Type Learner.
    Parameter mttt : unit -> { m : V.ML.M.t nat | V.ML.minimal m }.
End Learner.

Module MImpl : Learner := TTT_Moore_Binary s BoolOutput V.ML V.MT.

Definition ttt (_ : unit) : { d : D.t nat | minimal d } :=
    let (m, pf) := MImpl.mttt tt in
    exist _ (V.ML.to_dfa m) (V.minimal_to_dfa m pf).

End TTT.
