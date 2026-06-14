From Stdlib Require Export List.
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
End Symbol.

(** Deterministic Finite Automaton *)
Module DFA (s : Symbol).
    Import s.

    (** DFA type *)
    Record t (state : Type) : Type := {
        transition : state -> s.t -> state;
        initial : state;
        accept : state -> bool;
        states : list state
    }.

    (** Run a DFA on a string and get the resulting state *)
    Definition run {state : Type} (dfa : t state) (s : string) : state :=
        fold_left dfa.(transition state) s dfa.(initial state).

    (** Check whether a DFA reaches an accepting state after processing a string *)
    Definition accept_string {state : Type} (dfa : t state) (s : string) : bool :=
        dfa.(accept state) (run dfa s).
End DFA.

(** Language *)
Module Type RegularLanguage (s : Symbol).
    Import s.
    Module D := DFA s.
    Parameter member : string -> bool.
    (** Whether a DFA encodes the language L *)
    Definition encodes {state : Type} (dfa : D.t state) : Prop :=
        forall (s : string),
            member s = true <-> D.accept_string dfa s = true.
    Parameter exists_dfa : exists state (d: D.t state), encodes d.
End RegularLanguage.