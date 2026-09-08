(** Rivest-Schapire-style automata learning
    https://www.tifr.res.in/~shibashis.guha/courses/diwali2021/L-starMalharManagoli.pdf *)

From lstar Require Import automata.DFA Teacher MooreDFA Lstar_Moore.

Module Lstar (s : Symbol) (L : RegularLanguage s) (T : DFATeacher s L).
Import s L.

(** The Moore view of [L] and [T] *)
Module V := MooreView s L T.

Module Type Learner.
    Parameter mlstar : unit -> { m : V.ML.M.t nat | V.ML.minimal m }.
End Learner.

Module MImpl : Learner := MooreLstar s BoolOutput V.ML V.MT.

Definition lstar (_ : unit) : { d : D.t nat | minimal d } :=
    let (m, pf) := MImpl.mlstar tt in
    exist _ (V.ML.to_dfa m) (V.minimal_to_dfa m pf).

End Lstar.
