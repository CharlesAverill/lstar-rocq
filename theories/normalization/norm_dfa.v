(** Normalization of DFAs *)

From Stdlib Require Import List Lia PeanoNat.
From lstar Require Import Alphabet ListLemmas automata.DFA
     normalization.norm_lemmas.
Import ListNotations.

Module Type DFAType (s : Symbol).
  Include (DFA s).
End DFAType.

Module NormalizeDFA (s : Symbol) (D : DFAType s).
Import s D.
Module ND := NormDet s.

Section Normalize.
  Context {state : Type}.
  Variable eq_dec : forall (x y : state), {x = y} + {x <> y}.
  Variable d : D.t state.

  Definition TransClosed :=
    forall q a, In q (D.states state d) ->
                In (D.transition state d q a) (D.states state d).

  Hypothesis trans_closed : TransClosed.

  Definition sys : ND.DetSys state :=
    {| ND.ds_states := D.states state d;
       ND.ds_transition := D.transition state d;
       ND.ds_initial := D.initial state d;
       ND.ds_complete := D.states_complete state d;
       ND.ds_closed := trans_closed |}.

  Let Q := ND.Q eq_dec sys.
  Let ix := ND.ix eq_dec sys.
  Let sym_ix := ND.sym_ix.
  Let tix := ND.tix eq_dec sys.
  Let trans_table := ND.trans_table eq_dec sys.
  Let n_initial := ND.n_initial eq_dec sys.
  Let n_transition := ND.n_transition eq_dec sys.
  Let n_states := ND.n_states eq_dec sys.
  Let corr := ND.corr eq_dec sys.

  (** Acceptance table *)
  Definition acc_table : list bool := map (D.accept state d) Q.

  Definition n_accept (i : nat) : bool := nth i acc_table false.

  Lemma n_accept_spec : forall i q, nth_error Q i = Some q ->
      n_accept i = D.accept state d q.
  Proof.
    intros i q Hn. unfold n_accept, acc_table.
    exact (nth_error_nth _ _ false (map_nth_error _ _ _ Hn)).
  Qed.

  Lemma corr_accept : forall i q, corr i q ->
      n_accept i = D.accept state d q.
  Proof.
    intros i q (_ & Hix). exact (n_accept_spec i q (ND.nth_ix eq_dec sys q i Hix)).
  Qed.

  (** The normalized DFA *)

  Definition build (at_ : list bool) (tt_ : list (list nat)) (init : nat)
      (sc : forall w, In (fold_left
                 (fun i a => nth (sym_ix a) (nth i tt_ []) 0) w init)
                 n_states)
      : D.t nat :=
    {| D.transition := fun i a => nth (sym_ix a) (nth i tt_ []) 0;
       D.initial := init;
       D.accept := fun i => nth i at_ false;
       D.states := n_states;
       D.states_complete := sc |}.

  Lemma build_states_complete : forall w,
      In (fold_left
            (fun i a => nth (sym_ix a) (nth i trans_table []) 0) w n_initial)
         n_states.
  Proof. exact (ND.normalize_states_complete eq_dec sys). Qed.

  Definition normalize : D.t nat :=
    build acc_table trans_table n_initial build_states_complete.

  (** [normalize] accepts exactly the same strings as [d] *)

  Theorem normalize_accept_string : forall w,
      D.accept_string normalize w = D.accept_string d w.
  Proof.
    intro w. unfold D.accept_string, normalize, build, D.run. simpl.
    change (fun i a => nth (sym_ix a) (nth i trans_table []) 0)
      with n_transition.
    change (fun i => nth i acc_table false) with n_accept.
    apply corr_accept.
    apply (ND.corr_fold eq_dec sys). exact (ND.corr_initial eq_dec sys).
  Qed.

  (** Per-state version *)
  Theorem normalize_accept_from : forall i q,
      nth_error Q i = Some q ->
      forall w,
        D.accept nat normalize (fold_left n_transition w i) =
        D.accept state d (fold_left (D.transition state d) w q).
  Proof.
    intros i q Hn w.
    unfold normalize, build. cbn [D.accept].
    change (fun i0 => nth i0 acc_table false) with n_accept.
    apply corr_accept, (ND.corr_fold eq_dec sys). split.
    - apply (proj1 (ND.in_Q eq_dec sys q)). exact (nth_error_In _ _ Hn).
    - now apply (ND.ix_nth eq_dec sys).
  Qed.

End Normalize.
End NormalizeDFA.
