From lstar Require Export Language.

Module DFA (s : Symbol) (L : L s).
    Import s L.

    Record t : Type := {
        state : Type;
        transition : state -> s.t -> state;
        initial : state;
        accept : state -> bool
    }.

    Definition accept_string (dfa : t) (s : string) : bool :=
        dfa.(accept) (fold_left dfa.(transition) s dfa.(initial)).

    Definition encodes (dfa : t) : Prop :=
        forall (s : string),
            member s = true <-> accept_string dfa s = true.
End DFA.
