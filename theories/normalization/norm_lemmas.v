(** Common normalization infrastructure for deterministic machines. *)

From Stdlib Require Import List Lia PeanoNat.
From lstar Require Import Alphabet ListLemmas.
Import ListNotations.

Module NormDet (s : Symbol).
Import s.

(** A deterministic transition system *)
Record DetSys (state : Type) : Type := {
  ds_states : list state;
  ds_transition : state -> s.t -> state;
  ds_initial : state;
  ds_complete :
    forall w, In (fold_left ds_transition w ds_initial) ds_states;
  ds_closed :
    forall q a, In q ds_states -> In (ds_transition q a) ds_states
}.

Arguments ds_states {state} d.
Arguments ds_transition {state} d.
Arguments ds_initial {state} d.
Arguments ds_complete {state} d.
Arguments ds_closed {state} d.

Section Core.
  Context {state : Type}.
  Variable eq_dec : forall (x y : state), {x = y} + {x <> y}.
  Variable A : DetSys state.

  Let states := ds_states A.
  Let transition := ds_transition A.
  Let initial := ds_initial A.

  Definition Q : list state := dedup eq_dec states.

  Definition ix (q : state) : option nat := pos eq_dec q Q.

  Definition sym_ix (a : s.t) : nat := spos s.eq_dec a s.enum.

  Definition tix (q : state) : nat :=
    match ix q with Some i => i | None => 0 end.

  Definition trans_table : list (list nat) :=
    map (fun q => map (fun a => tix (transition q a)) s.enum) Q.

  (** The normalized transition system over [nat] states. *)

  Definition n_initial : nat := tix initial.

  Definition n_transition (i : nat) (a : s.t) : nat :=
    nth (sym_ix a) (nth i trans_table []) 0.

  Definition n_states : list nat := seq 0 (length Q).

  Lemma in_Q : forall q, In q Q <-> In q states.
  Proof. intro q. unfold Q. now apply dedup_In. Qed.

  Lemma ix_nth : forall i q, nth_error Q i = Some q -> ix q = Some i.
  Proof.
    intros i q Hn. unfold ix.
    apply pos_nth_error; [now apply dedup_NoDup | exact Hn].
  Qed.

  Lemma nth_ix : forall q i, ix q = Some i -> nth_error Q i = Some q.
  Proof.
    intros q i. unfold ix. generalize Q as l.
    intro l. revert i. induction l as [| h t IH]; simpl; intros i Hp.
      discriminate.
    destruct eq_dec eqn:E.
      subst h. inversion Hp. reflexivity.
    destruct (pos eq_dec q t) as [k |] eqn:Ek; simpl in Hp; inversion Hp; subst.
    simpl. now apply IH.
  Qed.

  Lemma ix_total : forall q, In q states -> exists i, ix q = Some i.
  Proof.
    intros q Hq. apply (proj2 (in_Q q)) in Hq. unfold ix. revert Hq.
    generalize Q as l. intro l. induction l as [| h t IH]; simpl.
      intros [].
    intros [<- | Hq].
      destruct eq_dec. now exists 0. contradiction.
    destruct eq_dec. now exists 0.
    destruct (IH Hq) as (k & Hk). rewrite Hk. simpl. now exists (S k).
  Qed.

  Lemma tix_lt : forall q, In q states -> tix q < length Q.
  Proof.
    intros q Hq. unfold tix.
    destruct (ix_total q Hq) as (i & Hi). rewrite Hi.
    unfold ix in Hi. exact (pos_lt _ _ _ _ Hi).
  Qed.

  (** Table lookups agree with the original machine. *)

  Lemma n_transition_spec : forall i q a, nth_error Q i = Some q ->
      n_transition i a = tix (transition q a).
  Proof.
    intros i q a Hn. unfold n_transition, trans_table.
    rewrite (nth_error_nth _ _ [] (map_nth_error _ _ _ Hn)).
    unfold sym_ix.
    exact (nth_error_nth _ _ 0
             (map_nth_error _ _ _ (spos_nth _ a s.enum (s.t_enumerable a)))).
  Qed.

  (** Bisimulation between original and normalized states. *)

  Definition corr (i : nat) (q : state) : Prop :=
    In q states /\ ix q = Some i.

  Lemma corr_initial : corr n_initial initial.
  Proof.
    unfold corr, n_initial, tix.
    assert (Hin : In initial states) by exact (ds_complete A []).
    destruct (ix_total _ Hin) as (i & Hi). rewrite Hi.
    now split.
  Qed.

  Lemma corr_step : forall i q a, corr i q ->
      corr (n_transition i a) (transition q a).
  Proof.
    intros i q a (Hin & Hix). unfold corr.
    rewrite (n_transition_spec i q a (nth_ix q i Hix)).
    assert (Htin : In (transition q a) states) by exact (ds_closed A q a Hin).
    destruct (ix_total _ Htin) as (j & Hj).
    unfold tix. rewrite Hj. now split.
  Qed.

  Lemma corr_fold : forall w i q, corr i q ->
      corr (fold_left n_transition w i) (fold_left transition w q).
  Proof.
    intro w. induction w as [| a w IH]; intros i q Hc; simpl; [exact Hc |].
    apply IH. now apply corr_step.
  Qed.

  Lemma normalize_states_complete : forall w,
      In (fold_left n_transition w n_initial) n_states.
  Proof.
    intro w.
    pose proof (corr_fold w n_initial initial corr_initial) as (Hin & Hix).
    unfold n_states. apply in_seq. split; [lia |]. rewrite Nat.add_0_l.
    unfold ix in Hix. exact (pos_lt _ _ _ _ Hix).
  Qed.
End Core.

Arguments Q {state} eq_dec A.
Arguments ix {state} eq_dec A q.
Arguments tix {state} eq_dec A q.
Arguments trans_table {state} eq_dec A.
Arguments n_initial {state} eq_dec A.
Arguments n_transition {state} eq_dec A i a.
Arguments n_states {state} eq_dec A.
Arguments corr {state} eq_dec A i q.

End NormDet.
