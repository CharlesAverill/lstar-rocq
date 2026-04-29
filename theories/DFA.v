From lstar Require Export Language.

(** Deterministic Finite Automaton *)
Module DFA (s : Symbol) (L : L s).
    Import s L.

    (** DFA type *)
    Record t : Type := {
        state : Type;
        transition : state -> s.t -> state;
        initial : state;
        accept : state -> bool
    }.

    (** Run a DFA on a string and get the resulting state *)
    Definition run (dfa : t) (s : string) : dfa.(state) :=
        fold_left dfa.(transition) s dfa.(initial).

    (** Check whether a DFA reaches an accepting state after processing a string *)
    Definition accept_string (dfa : t) (s : string) : bool :=
        dfa.(accept) (run dfa s).

    (** Whether a DFA encodes the language L *)
    Definition encodes (dfa : t) : Prop :=
        forall (s : string),
            member s = true <-> accept_string dfa s = true.
End DFA.
