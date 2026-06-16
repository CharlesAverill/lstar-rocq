From Stdlib Require Export List String.
Export ListNotations.

(** Symbol type *)
Module Type Symbol.
    (** Alphabet *)
    Parameter t : Type.

    (** Symbol equality is decidable *)
    Parameter eq_dec :
        forall (x y : t), {x = y} + {x <> y}.

    (** Alphabet is finite *)
    Parameter enum : list t.
    Parameter t_enumerable : forall (x : t), In x enum.

    (** List of symbols *)
    Definition string := list t.

    (** String equality is decidable*)
    Fixpoint str_eq (x y : string) {struct x} : {x = y} + {x <> y}.
        destruct x.
        - destruct y. now left.
          now right.
        - destruct y. now right.
          destruct (eq_dec t0 t1).
            + destruct (str_eq x y).
                left. rewrite e, e0. reflexivity.
                right. intro. injection H. intros.
                contradiction.
            + right. intro. injection H. intros.
                contradiction.
    Defined.

    (** For debugging *)
    Parameter string_of_t : t -> String.string.
End Symbol.

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
    Definition run {state : Type} (dfa : t state) (s : string) : state :=
        fold_left dfa.(transition state) s dfa.(initial state).

    (** Check whether a DFA reaches an accepting state after processing a string *)
    Definition accept_string {state : Type} (dfa : t state) (s : string) : bool :=
        dfa.(accept state) (run dfa s).
    
    (** Every reachable state is listed in [states] *)
    Lemma run_in_states : forall {state : Type} (d : t state) (w : string),
        In (run d w) (states state d).
    Proof.
        intros state d w. unfold run. apply (states_complete state d).
    Qed.
End DFA.

(** Language *)
Module Type RegularLanguage (s : Symbol).
    Import s.
    Module D := DFA s.
    
    (** Language membership *)
    Parameter member : string -> bool.

    (** Whether a DFA encodes the language L *)
    Definition encodes {state : Type} (dfa : D.t state) : Prop :=
        forall (s : string),
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
