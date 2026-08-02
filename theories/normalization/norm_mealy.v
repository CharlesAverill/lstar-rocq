(** Normalization of Mealy machines. *)

From Stdlib Require Import List Lia PeanoNat.
From lstar Require Import Alphabet ListLemmas automata.Mealy
     normalization.norm_lemmas.
Import ListNotations.

Module Type MealyType (s : Symbol) (O : Output).
  Include (Mealy s O).
End MealyType.

Module NormalizeMealy (s : Symbol) (O : Output) (M : MealyType s O).
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

  Definition out_table : list (list O.t) :=
    map (fun q => map (fun a => M.output state m q a) s.enum) Q.

  Definition sym_default (a : s.t) : O.t :=
    match s.enum as e return (In a e -> O.t) with
    | b :: _ => fun _ => M.output state m (M.initial state m) b
    | [] => fun Hin => match Hin with end
    end (s.t_enumerable a).

  Definition n_output (i : nat) (a : s.t) : O.t :=
    nth (sym_ix a) (nth i out_table []) (sym_default a).

  Lemma n_output_spec : forall i q a, nth_error Q i = Some q ->
      n_output i a = M.output state m q a.
  Proof.
    intros i q a Hn. unfold n_output, out_table.
    rewrite (nth_error_nth _ _ [] (map_nth_error _ _ _ Hn)).
    unfold sym_ix, ND.sym_ix.
    exact (nth_error_nth _ _ (sym_default a)
             (map_nth_error _ _ _ (spos_nth _ a s.enum (s.t_enumerable a)))).
  Qed.

  Lemma corr_output : forall i q a, corr i q ->
      n_output i a = M.output state m q a.
  Proof.
    intros i q a (_ & Hix).
    exact (n_output_spec i q a (ND.nth_ix eq_dec sys q i Hix)).
  Qed.

  (** The normalized Mealy machine. *)

  Definition build (ot_ : list (list O.t)) (tt_ : list (list nat)) (init : nat)
      (sc : forall w, In (fold_left
                 (fun i a => nth (sym_ix a) (nth i tt_ []) 0) w init)
                 n_states)
      : M.t nat :=
    {| M.transition := fun i a => nth (sym_ix a) (nth i tt_ []) 0;
       M.initial := init;
       M.output := fun i a => nth (sym_ix a) (nth i ot_ []) (sym_default a);
       M.states := n_states;
       M.states_complete := sc |}.

  Lemma build_states_complete : forall w,
      In (fold_left
            (fun i a => nth (sym_ix a) (nth i trans_table []) 0) w n_initial)
         n_states.
  Proof. exact (ND.normalize_states_complete eq_dec sys). Qed.

  Definition normalize : M.t nat :=
    build out_table trans_table n_initial build_states_complete.

  Lemma corr_output_word_from : forall w i q, corr i q ->
      M.output_word_from normalize i w = M.output_word_from m q w.
  Proof.
    induction w as [| a w IH]; intros i q Hc; simpl; [reflexivity |].
    unfold normalize, build.
    change (nth (sym_ix a) (nth i trans_table []) 0) with (n_transition i a).
    change (nth (sym_ix a) (nth i out_table []) (sym_default a)) with
      (n_output i a).
    rewrite (corr_output i q a Hc). f_equal.
    apply IH. now apply (ND.corr_step eq_dec sys).
  Qed.

  (** [normalize] emits the same output word on every input as [m] *)

  Theorem normalize_output_word : forall w,
      M.output_word normalize w = M.output_word m w.
  Proof.
    intro w. unfold M.output_word.
    change (M.initial nat normalize) with n_initial.
    apply corr_output_word_from. exact (ND.corr_initial eq_dec sys).
  Qed.

  (** [last_output_from] agrees from corresponding states. *)
  Lemma corr_last_output_from : forall w i q, corr i q -> forall a,
      M.last_output_from normalize i a w = M.last_output_from m q a w.
  Proof.
    induction w as [| b w IH]; intros i q Hc a; simpl.
    - exact (corr_output i q a Hc).
    - unfold normalize, build. cbn [M.output M.transition].
      change (fun i0 a0 => nth (sym_ix a0) (nth i0 trans_table []) 0)
        with n_transition.
      change (fun i0 a0 => nth (sym_ix a0) (nth i0 out_table []) (sym_default a0))
        with n_output.
      apply IH. now apply (ND.corr_step eq_dec sys).
  Qed.

  (** [normalize] agrees on last outputs *)
  Theorem normalize_last_output : forall a w,
      M.last_output normalize a w = M.last_output m a w.
  Proof.
    intros a w. unfold M.last_output.
    change (M.initial nat normalize) with n_initial.
    apply corr_last_output_from. exact (ND.corr_initial eq_dec sys).
  Qed.

End Normalize.
End NormalizeMealy.
