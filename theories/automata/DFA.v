From Stdlib Require Export String List.
From lstar Require Export Alphabet.
Export ListNotations.

(** Deterministic Finite Automaton *)
Module DFA (s : Symbol).
    Import s.

    (** DFA type *)
    Record t (state : Type) : Type := {
        transition : state -> s.t -> state;
        initial : state;
        accept : state -> bool;
        states : list state;
        states_complete : forall w, In (fold_left transition w initial) (states)
    }.

    (** Run a DFA on a string and get the resulting state *)
    Definition run {state : Type} (dfa : t state) (s : str) : state :=
        fold_left dfa.(transition state) s dfa.(initial state).

    (** Check whether a DFA reaches an accepting state after processing a string *)
    Definition accept_string {state : Type} (dfa : t state) (s : str) : bool :=
        dfa.(accept state) (run dfa s).
    
    (** Every reachable state is listed in [states] *)
    Lemma run_in_states : forall {state : Type} (d : t state) (w : str),
        In (run d w) (states state d).
    Proof.
        intros state d w. unfold run. apply (states_complete state d).
    Qed.

    (** String equality is decidable*)
    Fixpoint str_eq (x y : str) {struct x} : {x = y} + {x <> y}.
        destruct x, y.
            now left.
            now right.
            now right.
        destruct (eq_dec t0 t1), (str_eq x y); subst; clear str_eq.
            now left.
        all: right; intro H; inversion H; subst; intuition.
    Defined.
End DFA.

(** Regular Language *)
Module Type RegularLanguage (s : Symbol).
    Import s.
    Module D := DFA s.
    Include Language s.

    (** Whether a DFA encodes the language L *)
    Definition encodes {state : Type} (dfa : D.t state) : Prop :=
        forall (s : str),
            member s = true <-> D.accept_string dfa s = true.

    (** DFA state minimality *)
    Definition minimal {state : Type} (dfa : D.t state) : Prop :=
        encodes dfa /\
        forall (state' : Type) (dfa' : D.t state'),
            encodes dfa' -> 
            List.length (D.states state dfa) <= List.length (D.states state' dfa').

    (** There exists a minimal DFA with number of states [num_states_in_minimal] *)
    Parameter num_states_in_minimal : nat.
    Parameter exists_dfa : exists state (d: D.t state), 
        minimal d /\ List.length (D.states state d) <= num_states_in_minimal.
End RegularLanguage.
