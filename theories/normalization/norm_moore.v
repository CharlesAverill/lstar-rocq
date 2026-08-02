(** Normalization of Moore machines. *)

From Stdlib Require Import List Lia PeanoNat.
From lstar Require Import Alphabet ListLemmas automata.Moore
     normalization.norm_lemmas.
Import ListNotations.

Module Type MooreType (s : Symbol) (O : Output).
  Include (Moore s O).
End MooreType.

Module NormalizeMoore (s : Symbol) (O : Output) (M : MooreType s O).
Import s O M.
Module ND := NormDet s.

Section Normalize.
  Context {state : Type}.
  Variable eq_dec : forall (x y : state), {x = y} + {x <> y}.
  Variable m : M.t state.

  Definition TransClosed :=
    forall q a, In q (M.states state m) ->
                In (M.transition state m q a) (M.states state m).

  Hypothesis trans_closed : TransClosed.

  Definition sys : ND.DetSys state :=
    {| ND.ds_states := M.states state m;
       ND.ds_transition := M.transition state m;
       ND.ds_initial := M.initial state m;
       ND.ds_complete := M.states_complete state m;
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

  Variable odefault : O.t.

  Definition out_table : list O.t := map (M.output state m) Q.

  Definition n_output (i : nat) : O.t := nth i out_table odefault.

  Lemma n_output_spec : forall i q, nth_error Q i = Some q ->
      n_output i = M.output state m q.
  Proof.
    intros i q Hn. unfold n_output, out_table.
    exact (nth_error_nth _ _ odefault (map_nth_error _ _ _ Hn)).
  Qed.

  Lemma corr_output : forall i q, corr i q ->
      n_output i = M.output state m q.
  Proof.
    intros i q (_ & Hix). exact (n_output_spec i q (ND.nth_ix eq_dec sys q i Hix)).
  Qed.

  (** The normalized Moore machine. *)

  Definition build (ot_ : list O.t) (tt_ : list (list nat)) (init : nat)
      (sc : forall w, In (fold_left
                 (fun i a => nth (sym_ix a) (nth i tt_ []) 0) w init)
                 n_states)
      : M.t nat :=
    {| M.transition := fun i a => nth (sym_ix a) (nth i tt_ []) 0;
       M.initial := init;
       M.output := fun i => nth i ot_ odefault;
       M.states := n_states;
       M.states_complete := sc |}.

  Lemma build_states_complete : forall w,
      In (fold_left
            (fun i a => nth (sym_ix a) (nth i trans_table []) 0) w n_initial)
         n_states.
  Proof. exact (ND.normalize_states_complete eq_dec sys). Qed.

  Definition normalize : M.t nat :=
    build out_table trans_table n_initial build_states_complete.

  (** [normalize] produces the same output on every string as [m] *)

  Theorem normalize_output_string : forall w,
      M.output_string normalize w = M.output_string m w.
  Proof.
    intro w. unfold M.output_string, normalize, build, M.run. simpl.
    change (fun i a => nth (sym_ix a) (nth i trans_table []) 0)
      with n_transition.
    change (fun i => nth i out_table odefault) with n_output.
    apply corr_output.
    apply (ND.corr_fold eq_dec sys). exact (ND.corr_initial eq_dec sys).
  Qed.

  (** Per-state version *)
  Theorem normalize_output_from : forall i q,
      nth_error Q i = Some q ->
      forall w,
        M.output nat normalize (fold_left n_transition w i) =
        M.output state m (fold_left (M.transition state m) w q).
  Proof.
    intros i q Hn w.
    unfold normalize, build. cbn [M.output].
    change (fun i0 => nth i0 out_table odefault) with n_output.
    apply corr_output, (ND.corr_fold eq_dec sys). split.
    - apply (proj1 (ND.in_Q eq_dec sys q)). exact (nth_error_In _ _ Hn).
    - now apply (ND.ix_nth eq_dec sys).
  Qed.

End Normalize.
End NormalizeMoore.
