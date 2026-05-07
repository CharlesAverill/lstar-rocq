From lstar Require Export Language.

(** Deterministic Finite Automaton *)
Module DFA (s : Symbol) (L : L s).
    Import s L.

    (** DFA type *)
    Record t (state : Type) : Type := {
        transition : state -> s.t -> state;
        initial : state;
        accept : state -> bool
    }.

    (** Run a DFA on a string and get the resulting state *)
    Definition run {state : Type} (dfa : t state) (s : string) : state :=
        fold_left dfa.(transition state) s dfa.(initial state).

    (** Check whether a DFA reaches an accepting state after processing a string *)
    Definition accept_string {state : Type} (dfa : t state) (s : string) : bool :=
        dfa.(accept state) (run dfa s).

    (** Whether a DFA encodes the language L *)
    Definition encodes {state : Type} (dfa : t state) : Prop :=
        forall (s : string),
            member s = true <-> accept_string dfa s = true.
End DFA.
