From Stdlib Require Export String List.
From lstar Require Export Alphabet.
Export ListNotations.

(** Moore machine over symbol alphabet [s] and output alphabet [O]. *)
Module Moore (s : Symbol) (O : Output).
    Import s.

    (** Moore machine type: like [DFA.t] but with [output : state -> O.t]. *)
    Record t (state : Type) : Type := {
        transition : state -> s.t -> state;
        initial : state;
        output : state -> O.t;
        states : list state;
        states_complete : forall w, In (fold_left transition w initial) states
    }.

    (** Run a Moore machine on a string and get the resulting state *)
    Definition run {state : Type} (m : t state) (w : str) : state :=
        fold_left m.(transition state) w m.(initial state).

    (** The output the machine produces after processing a string *)
    Definition output_string {state : Type} (m : t state) (w : str) : O.t :=
        m.(output state) (run m w).

    (** Every reachable state is listed in [states] *)
    Lemma run_in_states : forall {state : Type} (m : t state) (w : str),
        In (run m w) (states state m).
    Proof.
        intros state m w. unfold run. apply (states_complete state m).
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
End Moore.

(** Moore language: the target is a total function [output_lang : str -> O]. *)
Module Type MooreLanguage (s : Symbol) (O : Output).
    Import s.
    Module M := Moore s O.

    (** The target output function: the value the learned machine must
        reproduce on every input word. *)
    Parameter output_lang : str -> O.t.

    (** Whether a Moore machine encodes the target output function *)
    Definition encodes {state : Type} (m : M.t state) : Prop :=
        forall (w : str), M.output_string m w = output_lang w.

    (** Moore-machine state minimality *)
    Definition minimal {state : Type} (m : M.t state) : Prop :=
        encodes m /\
        forall (state' : Type) (m' : M.t state'),
            encodes m' ->
            List.length (M.states state m) <= List.length (M.states state' m').

    (** There exists a minimal Moore machine with [num_states_in_minimal]
        states *)
    Parameter num_states_in_minimal : nat.
    Parameter exists_moore : exists state (m : M.t state),
        minimal m /\ List.length (M.states state m) <= num_states_in_minimal.
End MooreLanguage.
