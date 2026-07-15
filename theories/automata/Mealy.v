From Stdlib Require Export String List.
From lstar Require Export Alphabet.
Export ListNotations.

(** Mealy machine over symbol alphabet [s] and output alphabet [O]. *)
Module Mealy (s : Symbol) (O : Output).
    Import s.

    (** Mealy machine type *)
    Record t (state : Type) : Type := {
        transition : state -> s.t -> state;
        initial : state;
        output : state -> s.t -> O.t;
        states : list state;
        states_complete : forall w, In (fold_left transition w initial) states
    }.

    (** Run a Mealy machine on a string and get the resulting state *)
    Definition run {state : Type} (m : t state) (w : str) : state :=
        fold_left m.(transition state) w m.(initial state).

    (** The full output word produced by processing [w] *)
    Fixpoint output_word_from {state : Type} (m : t state)
        (q : state) (w : str) : list O.t :=
        match w with
        | [] => []
        | a :: w' =>
            m.(output state) q a :: output_word_from m (m.(transition state) q a) w'
        end.

    Definition output_word {state : Type} (m : t state) (w : str) : list O.t :=
        output_word_from m m.(initial state) w.

    Lemma output_word_from_app : forall {state : Type} (m : t state) q u v,
        output_word_from m q (u ++ v) =
        output_word_from m q u ++ output_word_from m (fold_left m.(transition state) u q) v.
    Proof.
        intros state m q u. revert q.
        induction u as [| a u IH]; intros q v; simpl.
            reflexivity.
        now rewrite IH.
    Qed.

    Lemma output_word_app : forall {state : Type} (m : t state) u v,
        output_word m (u ++ v) =
        output_word m u ++ output_word_from m (run m u) v.
    Proof.
        intros state m u v.
        unfold output_word, run.
        now rewrite output_word_from_app.
    Qed.

    (** The last output emitted while reading a non-empty word starting from state [q] *)
    Fixpoint last_output_from {state : Type} (m : t state)
        (q : state) (a : s.t) (w : str) : O.t :=
        match w with
        | [] => m.(output state) q a
        | b :: w' =>
            last_output_from m (m.(transition state) q a) b w'
        end.

    (** The last output of a non-empty word read from the machine's initial state. *)
    Definition last_output {state : Type} (m : t state) (a : s.t) (w : str)
        : O.t :=
        last_output_from m m.(initial state) a w.

    Lemma last_output_from_prefix :
        forall {state : Type} (m : t state) tl q c a w,
        last_output_from m q c (tl ++ a :: w)
          = last_output_from m (fold_left m.(transition state) (c :: tl) q) a w.
    Proof.
        intros state m tl. induction tl as [| d tl IH]; intros q c a w; simpl.
        - reflexivity.
        - now rewrite IH.
    Qed.

    (** The last output a *target* transition-output function [ol] emits
        while reading a non-empty word after having consumed [p] *)
    Fixpoint tgt_last (ol : str -> s.t -> O.t) (p : str) (a : s.t) (w : str) : O.t :=
        match w with
        | [] => ol p a
        | b :: w' => tgt_last ol (p ++ [a]) b w'
        end.

    (** Target observation on a possibly-empty suffix *)
    Definition tobs (ol : str -> s.t -> O.t) (q : str) (t : str) : option O.t :=
        match t with
        | [] => None
        | a :: w => Some (tgt_last ol q a w)
        end.

    (** Machine observation on a suffix *)
    Definition mobs {state : Type} (m : t state) (q : state) (t : str) : option O.t :=
        match t with
        | [] => None
        | a :: w => Some (last_output_from m q a w)
        end.

    Lemma mobs_prefix : forall {state : Type} (m : t state) u a w,
        mobs m m.(initial state) (u ++ a :: w) = mobs m (run m u) (a :: w).
    Proof.
        intros state m u a w. unfold mobs.
        destruct (u ++ a :: w) eqn:E.
        - now apply app_eq_nil in E as (_ & Hcontra).
        - f_equal.
          destruct u as [| c u'].
          + simpl in E. now inversion E.
          + simpl in E. inversion E; subst.
            unfold run. now rewrite last_output_from_prefix.
    Qed.

    Lemma mobs_snoc : forall {state : Type} (m : t state) u a,
        mobs m m.(initial state) (u ++ [a])
          = Some (m.(output state) (run m u) a).
    Proof.
        intros state m u a.
        rewrite (mobs_prefix m u a []).
        unfold mobs. reflexivity.
    Qed.

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
End Mealy.

(** Mealy language: the target is a transition-output function
    [output_lang : str -> s.t -> O.t], read as "having consumed the
    prefix [w], reading symbol [a] emits [output_lang w a]". *)
Module Type MealyLanguage (s : Symbol) (O : Output).
    Import s.
    Module M := Mealy s O.

    (** The target transition-output function *)
    Parameter output_lang : str -> s.t -> O.t.

    (** Whether a Mealy machine encodes the target *)
    Definition encodes {state : Type} (m : M.t state) : Prop :=
        forall (a : s.t) (w : str),
            M.last_output m a w = M.tgt_last output_lang [] a w.

    (** Mealy-machine state minimality *)
    Definition minimal {state : Type} (m : M.t state) : Prop :=
        encodes m /\
        forall (state' : Type) (m' : M.t state'),
            encodes m' ->
            List.length (M.states state m) <= List.length (M.states state' m').

    (** There exists a minimal Mealy machine with [num_states_in_minimal]
        states *)
    Parameter num_states_in_minimal : nat.
    Parameter exists_mealy : exists state (m : M.t state),
        minimal m /\ List.length (M.states state m) <= num_states_in_minimal.
End MealyLanguage.
