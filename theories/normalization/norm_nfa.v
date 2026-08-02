(** Normalization of NFAs. *)

From lstar Require Import automata.NFA ListLemmas SetLemmas.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

Module Type NFAType (s : Symbol).
  Include (NFA s).
End NFAType.

Module NormalizeNFA (s : Symbol) (N : NFAType s).
Import s N.

Section Normalize.
  Context {state : Type}.
  Variable eqb : state -> state -> bool.
  Variable m : N.t state.

  Fixpoint dedup (l : list state) : list state :=
    match l with
    | [] => []
    | h :: t =>
        let d := dedup t in
        if existsb (fun x => eqb h x) d then d else h :: d
    end.

  Definition Q : list state := dedup (N.states state m).

  (* First position of [q] in [l]. *)
  Fixpoint pos (q : state) (l : list state) : option nat :=
    match l with
    | [] => None
    | h :: t => if eqb q h then Some 0 else option_map S (pos q t)
    end.

  Definition ix (q : state) : option nat := pos q Q.

  (*  Positions of a list of states, without repetitions *)
  Definition raw_idxs (qs : list state) : list nat :=
    fold_right
      (fun q acc => match ix q with Some i => i :: acc | None => acc end)
      [] qs.

  Definition idxs (qs : list state) : list nat := nodup Nat.eq_dec (raw_idxs qs).

  (* Position of a symbol in [enum]; shared with the deterministic
     normalizers via [ListLemmas.spos]. *)
  Definition sym_ix (a : s.t) : nat := spos eq_dec a enum.

  (* The precomputed tables *)

  Definition acc_table : list bool := map (N.accept state m) Q.

  Definition trans_table : list (list (list nat)) :=
    map (fun q => map (fun a => idxs (N.transition state m q a)) enum) Q.

  (* The normalized automaton. *)

  Definition n_states : list nat := seq 0 (length Q).
  Definition n_initial : list nat := idxs (N.initial state m).
  Definition n_accept (acc : list bool) (i : nat) : bool := nth i acc false.
  Definition n_transition (tbl : list (list (list nat))) (i : nat) (a : s.t)
    : list nat := nth (sym_ix a) (nth i tbl []) [].

  (* Positions *)

  Lemma pos_lt : forall q l i, pos q l = Some i -> i < length l.
  Proof.
    intros q l. induction l as [| h t IH]; simpl; intros i Hp.
      discriminate.
    destruct (eqb q h).
      inversion Hp. lia.
    destruct (pos q t) as [k |] eqn:E; simpl in Hp; inversion Hp; subst.
    apply -> Nat.succ_lt_mono. now apply IH.
  Qed.

  Lemma in_idxs_lt : forall qs i, In i (idxs qs) -> i < length Q.
  Proof.
    intros qs i Hi. unfold idxs in Hi. apply nodup_In in Hi.
    revert Hi. unfold raw_idxs. induction qs as [| q qs IH]; simpl; intro Hi.
      destruct Hi.
    destruct (ix q) as [k |] eqn:E; [| now apply IH].
    destruct Hi as [<- | Hi]; [| now apply IH].
    unfold ix in E. exact (pos_lt _ _ _ E).
  Qed.

  Lemma in_raw_idxs : forall qs i,
      In i (raw_idxs qs) <-> exists q, In q qs /\ ix q = Some i.
  Proof.
    intros qs i. unfold raw_idxs.
    induction qs as [| q qs IH]; simpl.
      split; [intros [] | intros (x & [] & _)].
    destruct (ix q) as [k |] eqn:E.
    - simpl. split.
      + intros [<- | Hi].
          exists q. split; [now left | exact E].
        destruct (proj1 IH Hi) as (x & Hx & Hxe).
        exists x. split; [now right | exact Hxe].
      + intros (x & [<- | Hx] & Hxe).
          left. rewrite E in Hxe. now inversion Hxe.
        right. apply IH. now exists x.
    - split.
      + intro Hi. destruct (proj1 IH Hi) as (x & Hx & Hxe).
        exists x. split; [now right | exact Hxe].
      + intros (x & [<- | Hx] & Hxe).
          rewrite E in Hxe. discriminate.
        apply IH. now exists x.
  Qed.

  Lemma in_idxs : forall qs i,
      In i (idxs qs) <-> exists q, In q qs /\ ix q = Some i.
  Proof.
    intros qs i. unfold idxs. rewrite nodup_In. apply in_raw_idxs.
  Qed.

  Lemma n_transition_lt : forall i a j,
      In j (n_transition trans_table i a) -> j < length Q.
  Proof.
    intros i a j Hj. unfold n_transition in Hj.
    destruct (nth_error trans_table i) as [row |] eqn:Erow.
    - rewrite (nth_error_nth _ _ [] Erow) in Hj.
      unfold trans_table in Erow.
      destruct (nth_error Q i) as [q |] eqn:Eq.
      + rewrite (map_nth_error _ _ _ Eq) in Erow. inversion Erow. subst row.
        destruct (nth_error enum (sym_ix a)) as [b |] eqn:Eb.
        * rewrite (nth_error_nth _ _ [] (map_nth_error _ _ _ Eb)) in Hj.
          exact (in_idxs_lt _ _ Hj).
        * rewrite nth_overflow in Hj; [destruct Hj |].
          rewrite length_map. apply nth_error_None. exact Eb.
      + apply nth_error_None in Eq.
        assert (Hlen : length (map (fun q => map (fun a => idxs
                  (N.transition state m q a)) enum) Q) <= i)
          by (rewrite length_map; exact Eq).
        apply nth_error_None in Hlen. rewrite Hlen in Erow. discriminate.
    - rewrite (nth_overflow trans_table [] (proj1 (nth_error_None _ _) Erow)) in Hj.
      destruct (sym_ix a); destruct Hj.
  Qed.

  Lemma normalize_states_complete : forall w i,
      In i (fold_left (N.step (n_transition trans_table)) w n_initial) ->
      In i n_states.
  Proof.
    assert (Hstep : forall qs a j,
              In j (N.step (n_transition trans_table) qs a) -> j < length Q). {
      intros qs a j Hj. unfold N.step in Hj. apply in_flat_map in Hj.
      destruct Hj as (i & _ & Hj). exact (n_transition_lt _ _ _ Hj). }
    intro w. induction w as [| a w IH] using rev_ind; intros i Hi.
    - unfold n_states. apply in_seq. split; [lia |].
      simpl. simpl in Hi. exact (in_idxs_lt _ _ Hi).
    - rewrite fold_left_app in Hi. simpl in Hi.
      unfold n_states. apply in_seq. split; [lia |].
      rewrite Nat.add_0_l. exact (Hstep _ _ _ Hi).
  Qed.

  Definition normalize : N.t nat :=
    {| N.transition := n_transition trans_table;
       N.initial := n_initial;
       N.accept := n_accept acc_table;
       N.states := n_states;
       N.states_complete := normalize_states_complete |}.

  Definition Spec : Prop := forall x y, eqb x y = true <-> x = y.
  Definition TransClosed : Prop := forall q a,
      In q (N.states state m) -> incl (N.transition state m q a) (N.states state m).
  Definition InitClosed : Prop := incl (N.initial state m) (N.states state m).

  Lemma dedup_In : Spec -> forall l q, In q (dedup l) <-> In q l.
  Proof.
    intros eqb_spec l. induction l as [| h t IH]; intro q; simpl.
      reflexivity.
    destruct (existsb (fun x => eqb h x) (dedup t)) eqn:E.
    - apply existsb_exists in E. destruct E as (y & Hy & Hxy).
      apply eqb_spec in Hxy. subst y. split.
        intro Hq. right. now apply IH.
      intros [<- | Hq]. assumption. now apply IH.
    - simpl. split; (intros [<- | Hq]; [now left | right; now apply IH]).
  Qed.

  Lemma dedup_NoDup : Spec -> forall l, NoDup (dedup l).
  Proof.
    intros eqb_spec l. induction l as [| h t IH]; simpl.
      constructor.
    destruct (existsb (fun x => eqb h x) (dedup t)) eqn:E; [exact IH |].
    constructor; [| exact IH].
    intro Hin.
    assert (Hc : existsb (fun x => eqb h x) (dedup t) = true).
      { apply existsb_exists. exists h. split; [exact Hin | now apply eqb_spec]. }
    congruence.
  Qed.

  Lemma in_Q : Spec -> forall q, In q Q <-> In q (N.states state m).
  Proof. intros eqb_spec q. unfold Q. now apply dedup_In. Qed.

  Lemma pos_nth_error : Spec -> forall l i q,
      NoDup l -> nth_error l i = Some q -> pos q l = Some i.
  Proof.
    intros eqb_spec l. induction l as [| h t IH]; intros i q Hnd Hn.
      destruct i; discriminate.
    destruct i as [| k]; simpl in Hn.
    - inversion Hn. subst q. simpl.
      now destruct (eqb h h) eqn:E; [| rewrite (proj2 (eqb_spec h h) eq_refl) in E].
    - inversion Hnd as [| ? ? Hnh Hnt]. subst.
      simpl. destruct (eqb q h) eqn:E.
      + apply eqb_spec in E. subst h. exfalso. apply Hnh.
        exact (nth_error_In _ _ Hn).
      + rewrite (IH k q Hnt Hn). reflexivity.
  Qed.

  Lemma ix_nth : Spec -> forall i q, nth_error Q i = Some q -> ix q = Some i.
  Proof.
    intros eqb_spec i q Hn. unfold ix.
    apply pos_nth_error; [exact eqb_spec | now apply dedup_NoDup | exact Hn].
  Qed.

  Lemma nth_ix : Spec -> forall q i, ix q = Some i -> nth_error Q i = Some q.
  Proof.
    intros eqb_spec q i. unfold ix. generalize Q as l. clear - eqb_spec.
    intro l. revert i. induction l as [| h t IH]; simpl; intros i Hp.
      discriminate.
    destruct (eqb q h) eqn:E.
      apply eqb_spec in E. subst h. inversion Hp. reflexivity.
    destruct (pos q t) as [k |] eqn:Ek; simpl in Hp; inversion Hp; subst.
    simpl. now apply IH.
  Qed.

  Lemma ix_total : Spec -> forall q, In q (N.states state m) -> exists i, ix q = Some i.
  Proof.
    intros eqb_spec q Hq. apply (proj2 (in_Q eqb_spec q)) in Hq. unfold ix. revert Hq.
    generalize Q as l. clear - eqb_spec. intro l. induction l as [| h t IH]; simpl.
      intros [].
    intros [<- | Hq].
      rewrite (proj2 (eqb_spec h h) eq_refl). now exists 0.
    destruct (eqb q h); [now exists 0 |].
    destruct (IH Hq) as (k & Hk). rewrite Hk. simpl. now exists (S k).
  Qed.

  (** Table lookups agree with the original automaton. *)

  Lemma n_accept_spec : forall i q, nth_error Q i = Some q ->
      n_accept acc_table i = N.accept state m q.
  Proof.
    intros i q Hn. unfold n_accept, acc_table.
    exact (nth_error_nth _ _ false (map_nth_error _ _ _ Hn)).
  Qed.

  Lemma n_transition_spec : forall i q a, nth_error Q i = Some q ->
      n_transition trans_table i a = idxs (N.transition state m q a).
  Proof.
    intros i q a Hn. unfold n_transition, trans_table.
    rewrite (nth_error_nth _ _ [] (map_nth_error _ _ _ Hn)).
    unfold sym_ix.
    exact (nth_error_nth _ _ []
             (map_nth_error _ _ _ (spos_nth eq_dec a enum (t_enumerable a)))).
  Qed.

  (** Bisimulation *)

  Definition corr (is : list nat) (qs : list state) : Prop :=
    incl qs (N.states state m)
    /\ forall i, In i is <-> exists q, In q qs /\ ix q = Some i.

  Lemma corr_initial : Spec -> TransClosed -> InitClosed ->
      corr n_initial (N.initial state m).
  Proof.
    intros eqb_spec trans_closed init_closed.
    split; [exact init_closed |].
    intro i. unfold n_initial. apply in_idxs.
  Qed.

  Lemma corr_step : Spec -> TransClosed -> InitClosed ->
      forall is qs a, corr is qs ->
      corr (N.step (n_transition trans_table) is a)
           (N.step (N.transition state m) qs a).
  Proof.
    intros eqb_spec trans_closed init_closed is qs a (Hincl & Hcorr). split.
    - intros x Hx. unfold N.step in Hx. apply in_flat_map in Hx.
      destruct Hx as (q & Hq & Hx). exact (trans_closed q a (Hincl q Hq) x Hx).
    - intro j. unfold N.step. split.
      + intro Hj. apply in_flat_map in Hj. destruct Hj as (i & Hi & Hj).
        destruct (proj1 (Hcorr i) Hi) as (q & Hq & Hqi).
        rewrite (n_transition_spec i q a (nth_ix eqb_spec q i Hqi)) in Hj.
        destruct (proj1 (in_idxs _ _) Hj) as (q' & Hq' & Hq'j).
        exists q'. split; [| exact Hq'j].
        apply in_flat_map. now exists q.
      + intros (q' & Hq' & Hq'j). apply in_flat_map in Hq'.
        destruct Hq' as (q & Hq & Hq').
        destruct (ix_total eqb_spec q (Hincl q Hq)) as (i & Hi).
        apply in_flat_map. exists i. split.
          apply Hcorr. now exists q.
        rewrite (n_transition_spec i q a (nth_ix eqb_spec q i Hi)).
        apply in_idxs. now exists q'.
  Qed.

  Lemma corr_fold : Spec -> TransClosed -> InitClosed ->
      forall w is qs, corr is qs ->
      corr (fold_left (N.step (n_transition trans_table)) w is)
           (fold_left (N.step (N.transition state m)) w qs).
  Proof.
    intros eqb_spec trans_closed init_closed w.
    induction w as [| a w IH]; intros is qs Hc; simpl; [exact Hc |].
    apply IH. now apply corr_step.
  Qed.

  Lemma corr_existsb : Spec -> TransClosed -> InitClosed ->
      forall is qs, corr is qs ->
      existsb (n_accept acc_table) is = existsb (N.accept state m) qs.
  Proof.
    intros eqb_spec trans_closed init_closed is qs (Hincl & Hcorr).
    apply Bool.eq_true_iff_eq. split; intro Hex.
    - apply existsb_exists in Hex. destruct Hex as (i & Hi & Hai).
      destruct (proj1 (Hcorr i) Hi) as (q & Hq & Hqi).
      rewrite (n_accept_spec i q (nth_ix eqb_spec q i Hqi)) in Hai.
      apply existsb_exists. now exists q.
    - apply existsb_exists in Hex. destruct Hex as (q & Hq & Haq).
      destruct (ix_total eqb_spec q (Hincl q Hq)) as (i & Hi).
      apply existsb_exists. exists i. split.
        apply Hcorr. now exists q.
      rewrite (n_accept_spec i q (nth_ix eqb_spec q i Hi)). exact Haq.
  Qed.

  Lemma normalize_accept_string : Spec -> TransClosed -> InitClosed -> forall w,
      N.accept_string normalize w = N.accept_string m w.
  Proof.
    intros eqb_spec trans_closed init_closed w. unfold N.accept_string, N.run.
    apply corr_existsb; try assumption. apply corr_fold; try assumption.
    now apply corr_initial.
  Qed.

  Lemma normalize_L_state : Spec -> TransClosed -> InitClosed -> forall i q,
      nth_error Q i = Some q ->
      forall w, N.L_state normalize i w = N.L_state m q w.
  Proof.
    intros eqb_spec trans_closed init_closed i q Hn w. unfold N.L_state, N.run_from.
    apply corr_existsb; try assumption. apply corr_fold; try assumption. split.
    - intros x [<- | []]. apply in_Q; [exact eqb_spec |].
      exact (nth_error_In _ _ Hn).
    - intro j. split.
      + intros [<- | []]. exists q. split; [now left | now apply ix_nth].
      + intros (x & [<- | []] & Hx). rewrite (ix_nth eqb_spec i q Hn) in Hx.
        inversion Hx. now left.
  Qed.

  Lemma normalize_state_source : Spec -> TransClosed -> InitClosed ->
      forall i, In i n_states ->
      exists q, nth_error Q i = Some q /\ In q (N.states state m).
  Proof.
    intros eqb_spec trans_closed init_closed i Hi. unfold n_states in Hi. apply in_seq in Hi.
    destruct (nth_error Q i) as [q |] eqn:E.
    - exists q. split; [reflexivity |]. apply in_Q; [exact eqb_spec |].
      exact (nth_error_In _ _ E).
    - apply nth_error_None in E. lia.
  Qed.
End Normalize.
End NormalizeNFA.
