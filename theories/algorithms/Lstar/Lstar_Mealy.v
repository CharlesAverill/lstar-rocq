(** L* for Mealy machines *)

From lstar Require Import automata.Mealy ListLemmas SetLemmas Teacher.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.

Module MealyLstar (s : Symbol) (O : Output) (L : MealyLanguage s O)
                  (Tch : MealyTeacher s O L).
Import s O L Tch M.

(** Observations derived from the target *)

Definition obs : str -> str -> option O.t := M.tobs output_lang.
Definition mealy_output : str -> s.t -> str -> O.t := M.tgt_last output_lang.

Lemma obs_cons : forall q a w, obs q (a :: w) = Some (mealy_output q a w).
Proof. reflexivity. Qed.

Lemma obs_nil : forall q, obs q nil = None.
Proof. reflexivity. Qed.

Lemma obs_single : forall q a, obs q [a] = Some (output_lang q a).
Proof. reflexivity. Qed.

Lemma tgt_last_prefix : forall tl q c a w,
    mealy_output q c (tl ++ a :: w) = mealy_output (q ++ (c :: tl)) a w.
Proof.
    unfold mealy_output.
    intros tl. induction tl as [| d tl IH]; intros q c a w; simpl.
    - reflexivity.
    - rewrite IH. now rewrite <- app_assoc.
Qed.

Lemma obs_prefix : forall u a w, obs u (a :: w) = obs nil (u ++ a :: w).
Proof.
  intros. unfold obs, tobs.
  destruct (u ++ a :: w) eqn:E.
    now apply app_eq_nil in E.
  f_equal.
  destruct u as [| c u']; simpl in *; inversion E; subst.
    reflexivity.
  change (tgt_last _) with mealy_output. now rewrite tgt_last_prefix.
Qed.

Lemma obs_shift : forall u a t,
    t <> nil ->
    obs u (a :: t) = obs (u ++ [a]) t.
Proof.
    intros u a t Ht. destruct t as [| b t']; [contradiction|].
    unfold obs, M.tobs. reflexivity.
Qed.

Lemma obs_shift_app : forall t u a,
    obs u (t ++ [a]) = obs (u ++ t) [a].
Proof.
    intros t. induction t as [| c t IH]; intros u a; simpl.
    - now rewrite app_nil_r.
    - pose proof (obs_shift u c (t ++ [a])
                   (fun C => ltac:(now apply app_eq_nil in C))).
      unfold obs, tobs in *.
      rewrite H, IH. now rewrite <- app_assoc.
Qed.

Lemma obs_app_single : forall u t a,
    obs u (t ++ [a]) = Some (output_lang (u ++ t) a).
Proof. intros. now rewrite obs_shift_app, obs_single. Qed.

Lemma encodes_obs : forall {state} (m : M.t state),
    encodes m <-> (forall t, M.mobs m m.(M.initial _) t = obs nil t).
Proof.
    intros state m. unfold encodes, obs, M.tobs, M.mobs. split.
    - intros Henc t. destruct t as [| a w]; [reflexivity|].
      unfold last_output in Henc. now rewrite Henc.
    - intros Hobs a w. specialize (Hobs (a :: w)).
      now inversion Hobs.
Qed.

(** T-equivalent: u ≡T v iff ∀t ∈ T, obs u t = obs v t.  The empty
    suffix is inert ([obs _ nil = None] on both sides), so only non-empty
    suffixes can distinguish. *)
Definition T_equiv (T : str -> bool) (u v : str) : Prop :=
    forall (t : str),
        T t = true ->
        obs u t = obs v t.

Notation "T '[' u '==' v ']'" := (T_equiv T u v).

(** ≡T is an equivalence relation. *)
Definition Teq_refl : forall T u,
    T [u == u].
Proof.
    intros T u t Tt. reflexivity.
Qed.

Definition Teq_sym : forall T u v,
    T [u == v] -> T [v == u].
Proof.
    intros T u v Tuv t Tt.
    specialize (Tuv t Tt).
    now symmetry.
Qed.

Definition Teq_trans : forall T u v w,
    T [u == v] ->
    T [v == w] ->
    T [u == w].
Proof.
    intros T u v w Tuv Tvw t Tt.
    specialize (Tuv t Tt). specialize (Tvw t Tt).
    now rewrite Tuv, Tvw.
Qed.

Instance Teq_relation : forall T, Equivalence (T_equiv T).
Proof.
  constructor.
    unfold Reflexive. apply Teq_refl.
    unfold Symmetric. apply Teq_sym.
    unfold Transitive. apply Teq_trans.
Qed.

Add Parametric Relation T : str (T_equiv T)
  reflexivity proved by (Teq_refl T)
  symmetry proved by (Teq_sym T)
  transitivity proved by (Teq_trans T)
  as Teq_setoid.

(** For every T1 ⊆ T2, ≡T2 refines ≡T1. *)
Theorem refined_distinguish : forall T1 T2
    (Subset: forall s : str,
        T1 s = true -> T2 s = true),
    forall u v,
        T2 [u == v] -> T1 [u == v].
Proof.
    intros. intros t T1t.
    specialize (Subset t T1t).
    specialize (H _ Subset).
    assumption.
Qed.

Lemma total_refinement : forall T u v,
    (fun _ => true) [u == v] -> T [u == v].
Proof.
    intros. intros t Tt.
    specialize (H t eq_refl).
    assumption.
Qed.

Definition finite := SetLemmas.finite str.
Notation update := (SetLemmas.update str str_eq).
Notation "s [ k := v ]" := (update s k v).

(** Decidable equality for the [option O.t]-valued observable. *)
Definition obs_eq_dec : forall (x y : option O.t), {x = y} + {x <> y}.
Proof.
    intros [x|] [y|].
    - destruct (O.eq_dec x y); [left; now subst | right; congruence].
    - right; congruence.
    - right; congruence.
    - left; reflexivity.
Defined.

(** T-equivalence is decidable for finite sets. *)
Definition T_equiv_dec : forall T (u v : str),
    finite T ->
    {T [u == v]} + {~ T [u == v]}.
Proof.
    intros. destruct X as (x & _ & i).
    destruct (forallb (fun t =>
        if obs_eq_dec (obs u t) (obs v t)
        then true else false) x) eqn:Hfb.
    - left. intros t Ht.
        rewrite forallb_forall in Hfb.
        specialize (Hfb t ltac:(now apply i)).
        destruct obs_eq_dec eqn:E; [assumption | discriminate].
    - right. intro HTeq.
        apply Bool.not_true_iff_false in Hfb.
        apply Hfb. rewrite forallb_forall.
        intros t' HIn'.
        destruct obs_eq_dec eqn:E; [reflexivity|].
        exfalso. apply n.
        now apply HTeq, i.
Defined.

(** Q is separable wrt T when elements are pairwise T-distinguishable. *)
Definition separable (Q T : str -> bool) : Type :=
    forall (u v : str), Q u = true -> Q v = true ->
        u <> v ->
        ~ T [u == v].

(** Q is closed wrt T when every q·a has a T-equivalent representative. *)
Definition closed (Q T : str -> bool) :=
    forall q a,
        Q q = true ->
        {q' : str | Q q' = true /\ T [(q ++ [a]) == q']}.

Definition closed_dec_witness : forall Q T,
  finite Q ->
  finite T ->
  closed Q T +
  { q : str & { a : s.t &
      Q q = true /\
      forall q', Q q' = true -> ~ T [q ++ [a] == q'] }}.
Proof.
  intros Q T finQ finT.
  destruct finQ as (Ql & Qfin).
  destruct (List.find (fun '(q, a) =>
      negb (existsb (fun q' =>
          if T_equiv_dec T (q ++ [a]) q' finT then true else false
      ) Ql)) (list_prod Ql s.enum)) eqn:Hfind.
  - destruct p as (q, a).
    apply List.find_some in Hfind.
    destruct Hfind as (HIn & Hcheck).
    apply in_prod_iff in HIn. destruct HIn as (HIn_q & HIn_a).
    right. exists q, a. split.
        now apply Qfin.
    intros q' Hq' Contra.
    apply Bool.negb_true_iff, Bool.not_true_iff_false in Hcheck.
    apply Hcheck. rewrite existsb_exists.
    exists q'. split.
        now apply Qfin.
    destruct (T_equiv_dec T (q ++ [a]) q' finT); auto.
  - left. intros q a Hq.
    apply List.find_none with (x := (q, a)) in Hfind.
    + apply Bool.negb_false_iff, existsb_exists_set in Hfind.
      destruct Hfind as (q' & Hq' & Hcheck).
      exists q'. split.
        now apply Qfin.
        now destruct (T_equiv_dec T (q ++ [a]) q' finT).
    + apply in_prod.
        now apply Qfin.
        apply s.t_enumerable.
Qed.

Definition closed_dec : forall Q T,
    finite Q ->
    finite T ->
    closed Q T + (closed Q T -> Empty_set).
Proof.
    intros. destruct (closed_dec_witness Q T X X0).
        now left.
    right. intros Contra.
    destruct s as (q & a & Qq & Tdist).
    specialize (Contra q a Qq).
    destruct Contra as (q' & Qq' & Teq).
    destruct (Tdist q' Qq' Teq).
Defined.

(** Lemma 1: the transition function is well defined. *)
Definition delta Q T (c : closed Q T) (q : str) (a : s.t) (Qq : Q q = true) :
        {q' : str | Q q' = true /\ T [q' == (q ++ [a])]}.
    destruct (c q a Qq) as [q' [Hq' Heq]].
    now exists q'.
Defined.

(** A hypothesis (observation table) for Mealy learning. *)
Record HypothesisMealy : Type := {
  Q    : str -> bool;
  T    : str -> bool;
  sep  : separable Q T;
  clos : closed Q T;
  eps_in_Q : Q nil = true;
  fin_Q : finite Q;
  fin_T : finite T;
}.

(** The concrete Mealy machine extracted from a HypothesisMealy *)
Definition make_mealy (H : HypothesisMealy) : M.t {q | H.(Q) q = true}.
    set (state := {q | H.(Q) q = true}).
    assert (initial : state). {
        exists nil. apply H.(eps_in_Q). }
    assert (transition : state -> s.t -> state). {
        intros q a.
        set (r := delta H.(Q) H.(T) H.(clos) (proj1_sig q) a (proj2_sig q)).
        destruct r as (q' & Qq' & Teq). exists q'. apply Qq'. }
    set (out := fun (q : state) (a : s.t) => output_lang (proj1_sig q) a).
    destruct H.(fin_Q) as (l & ND & InQ).
    assert (InQpf : forall x, In x l -> H.(Q) x = true). {
        intros x Hin. now apply (proj2 (InQ x)). }
    set (ls := list_with_proof l (fun q => H.(Q) q = true) InQpf).
    refine {| initial    := initial;
              transition := transition;
              output     := out;
              states     := ls;
              states_complete := _ |}.
    intro w.
    set (qst := fold_left transition w initial).
    assert (Hin : In (proj1_sig qst) l) by
        apply (proj1 (InQ _)), (proj2_sig qst).
    assert (Heq : qst = exist _ (proj1_sig qst) (InQpf (proj1_sig qst) Hin)). {
        destruct qst as (q & Hq); simpl.
        f_equal. apply (UIP_dec Bool.bool_dec). }
    rewrite Heq.
    eapply (list_with_proof_complete l (fun q => H.(Q) q = true)).
    intros. apply UIP_dec, Bool.bool_dec.
Defined.

(** Shahbaz-Groz Counterexample analysis
    https://doi.org/10.1007/978-3-642-05089-3_14 *)

Lemma eps_in_H : forall (H : HypothesisMealy),
    proj1_sig (make_mealy H).(initial _) = nil.
Proof.
  intro H. unfold make_mealy, initial, fin_Q. simpl.
  now destruct H, fin_Q0, a.
Qed.

Lemma out_correct : forall (H : HypothesisMealy) q a,
    output _ (make_mealy H) q a = output_lang (proj1_sig q) a.
Proof.
  intros H q a. unfold make_mealy, output.
  now destruct fin_Q, a0.
Qed.

(** [pi H w i] is the access string of the state the hypothesis reaches
    after reading the length-[i] prefix of [w]. *)
Definition pi (H : HypothesisMealy) (w : str) (i : nat) : str :=
    proj1_sig (run (make_mealy H) (firstn i w)).

Lemma pi_0 : forall H w, pi H w 0 = nil.
Proof.
  intros H w. unfold pi.
  change (firstn 0 w) with (@nil s.t).
  unfold run. simpl (fold_left _ nil _).
  apply eps_in_H.
Qed.

Lemma pi_in_Q : forall H w i, H.(Q) (pi H w i) = true.
Proof.
  intros. unfold pi. exact (proj2_sig (run (make_mealy H) (firstn i w))).
Qed.

(** The hypothesis's own prediction for [w' ++ [a]] is the target's
    transition output at the access string reached after [w']. *)
Lemma prediction_is_obs_at_access : forall H w' a,
    mobs (make_mealy H) (make_mealy H).(initial _) (w' ++ a :: nil)
      = obs (proj1_sig (run (make_mealy H) w')) (a :: nil).
Proof.
  intros H w' a.
  rewrite M.mobs_snoc, out_correct, obs_single. reflexivity.
Qed.

Section SG.
Context (H : HypothesisMealy) (w' : str) (a : s.t).

Definition sg (i : nat) : option O.t :=
    obs (pi H w' i) (skipn i w' ++ [a]).

(** Index [i] is _correct_ when the reconstructed observation still agrees
    with the target's value on the whole counterexample. *)
Definition correct (i : nat) : Prop := sg i = obs nil (w' ++ [a]).

Lemma correct_dec : forall i, {correct i} + {~ correct i}.
Proof.
  intro i. unfold correct.
  destruct (sg i) as [x|] eqn:E1, (obs nil (w' ++ [a])) as [y|] eqn:E2.
  - destruct (O.eq_dec x y); [left; now subst | right; congruence].
  - right; congruence.
  - right; congruence.
  - left; reflexivity.
Defined.

Lemma sg_0 : correct 0.
Proof.
  unfold correct, sg. rewrite pi_0.
  change (skipn 0 w') with w'. reflexivity.
Qed.

Lemma sg_last :
    sg (List.length w')
      = mobs (make_mealy H) (make_mealy H).(initial _) (w' ++ [a]).
Proof.
  unfold sg, pi.
  rewrite firstn_all, skipn_all. simpl ((nil : str) ++ [a]).
  now rewrite prediction_is_obs_at_access.
Qed.

Lemma last_not_correct :
    mobs (make_mealy H) (make_mealy H).(initial _) (w' ++ [a])
      <> obs nil (w' ++ [a]) ->
    ~ correct (List.length w').
Proof.
  intros Hce Contra. unfold correct in Contra.
  rewrite sg_last in Contra. contradiction.
Qed.

(** Linear search for an adjacent correctness flip *)
Theorem sg_partition_linear :
    mobs (make_mealy H) (make_mealy H).(initial _) (w' ++ [a])
      <> obs nil (w' ++ [a]) ->
    {k | correct k /\ ~ correct (S k) /\ k < List.length w'}.
Proof.
  intro Hce.
  pose proof sg_0 as C0.
  pose proof (last_not_correct Hce) as Cm.
  (* Walk down from |w'| looking for the last correct index. *)
  assert (search : forall n, n <= List.length w' ->
            ~ correct n ->
            {k | correct k /\ ~ correct (S k) /\ k < List.length w'}). {
    induction n as [| n IH]; intros Hn Hnc.
    - contradiction.
    - destruct (correct_dec n) as [Cn | NCn].
      + exists n. split; [assumption | split; [assumption | lia]].
      + destruct (IH ltac:(lia) NCn) as (k & Ck & NCk & Hk).
        exists k. split; [assumption | split; [assumption | lia]].
  }
  apply (search (List.length w')); [lia | assumption].
Defined.

Theorem sg_partition_binary :
    mobs (make_mealy H) (make_mealy H).(initial _) (w' ++ [a])
      <> obs nil (w' ++ [a]) ->
    {k | correct k /\ ~ correct (S k) /\ k < List.length w'}.
Proof.
    intro Hce.
    pose proof sg_0 as C0.
    pose proof (last_not_correct Hce) as Cm.
    (* Search [lo, hi] with correct lo, ~correct hi, lo < hi, by strong
       induction on the gap (hi - lo). *)
    assert (search : forall gap lo hi,
        hi - lo <= gap ->
        lo < hi <= List.length w' ->
        correct lo ->
        ~ correct hi ->
        {k | correct k /\ ~ correct (S k) /\ k < List.length w'}). {
      induction gap as [| gap IHgap]; intros lo hi Hgap Hlt Clo Chi.
        lia.
      (* if hi = S lo, the flip is at lo.
         Otherwise, look for the midpoint *)
        destruct (Nat.eqb hi (S lo)) eqn:E.
        - exists lo. split; [assumption|].
          apply Nat.eqb_eq in E. rewrite <- E. split. assumption. lia.
        - (* lo + 1 < hi, so there is a midpoint strictly between *)
          set (mid := Nat.div2 (lo + hi)).
          assert (Hmid_lo : lo < mid). {
            unfold mid.
            apply Nat.div2_le_lower_bound.
            apply Nat.eqb_neq in E. lia. }
          assert (Hmid_hi : mid < hi). {
            unfold mid. rewrite Nat.div2_div.
            apply Nat.Div0.div_lt_upper_bound. lia. }
          destruct (correct_dec mid).
          (* correct at mid: recurse on [mid, hi] *)
            apply (IHgap mid hi); now try lia.
          (* incorrect at mid: recurse on [lo, mid] *)
            apply (IHgap lo mid); now try lia.
    }
    (* search(length w, 0 length w) *)
    destruct (Nat.eqb (List.length w') 0) eqn:E.
    - destruct Cm. apply Nat.eqb_eq in E. now rewrite E.
    - apply Nat.eqb_neq in E.
      apply (search (List.length w') 0 (List.length w')); now try lia.
Defined.

End SG.

(** Analyze a counterexample [w] to extract a new access string and a new
    distinguishing suffix that strictly refine the table. *)
Theorem find_separable :
  forall (H : HypothesisMealy)
         (w : str)
         (Hce : mobs (make_mealy H) (make_mealy H).(initial _) w <> obs nil w),
  { q_new : str &
  { t     : str &
      (H.(Q) q_new = false) *
      let Q' := H.(Q) [q_new := true] in
      let T' := H.(T) [t := true] in
      separable Q' T' *
      finite Q' *
      finite T' }}.
Proof.
    intros H w Hce.
    (* The counterexample is non-empty: peel its last symbol. *)
    assert (Hne : w <> nil). {
      intro Hw. subst w. apply Hce. reflexivity. }
    destruct (exists_last Hne) as (w' & a & Hw). subst w.
    (* Shahbaz-Groz search: a flip strictly inside w'. *)
    destruct (sg_partition_binary H w' a Hce) as (k & KCorrect & SKIncorrect & Hlt).
    (* The two adjacent reconstructions differ. *)
    assert (Dist : sg H w' a k <> sg H w' a (S k)). {
      unfold correct in KCorrect, SKIncorrect.
      rewrite KCorrect. intro Hbad. apply SKIncorrect. now rewrite <- Hbad.
    }
    (* Name the k-th symbol of w' and split skipn k w'. *)
    assert {wk | nth_error w' k = Some wk} as (wk & Hwk). {
      destruct (nth_error w' k) eqn:E.
        now exists t0.
      rewrite nth_error_None in E. lia.
    }
    pose proof (skipn_S_wk _ w' k wk Hwk) as Hskipn.
    (* The suffix we will add: always non-empty, since it ends in [a]. *)
    set (t := skipn (S k) w' ++ [a]).
    assert (Htne : t <> nil). {
      unfold t. intro Hbad.
      now apply app_eq_nil in Hbad as (_ & Hcontra). }
    (* Access-string facts, as in the Moore development. *)
    destruct (nth_error_split_sig _ _ _ Hwk) as (l1 & l2 & Hw' & Hlen).
    assert (Hfirstn : firstn (S k) w' = firstn k w' ++ [wk]). {
      now rewrite Hw', firstn_app, Nat.sub_succ_l,
                  firstn_all2, firstn_cons, Hlen, Nat.sub_diag,
                  firstn_0, firstn_app, Hlen, Nat.sub_diag, firstn_0,
                  <- Hlen, firstn_all2, app_nil_r by lia.
    }
    assert (run_step : forall i b,
        run (make_mealy H) (firstn i w' ++ [b]) =
        (make_mealy H).(transition _) (run (make_mealy H) (firstn i w')) b). {
      intros. unfold run. now rewrite fold_left_app.
    }
    assert (HTeq : H.(T) [pi H w' k ++ [wk] == pi H w' (S k)]). {
      unfold pi. rewrite Hfirstn, run_step.
      set (q := run (make_mealy H) (firstn k w')).
      destruct (delta H.(Q) H.(T) H.(clos) (proj1_sig q)
                    wk (proj2_sig q)) as [q' [Hq' Heq]].
      unfold transition, make_mealy, delta.
      now destruct H, fin_Q, a0, clos, a0.
    }
    assert (HQSk : H.(Q) (pi H w' (S k)) = true) by apply pi_in_Q.
    (* Reshape Dist into a statement about q_new and t. *)
    assert (DistQ : obs (pi H w' k ++ [wk]) t <> obs (pi H w' (S k)) t). {
      intro Hbad. apply Dist. unfold sg.
      rewrite Hskipn. fold t.
      (* obs (pi k) (wk :: t) = obs (pi k ++ [wk]) t  by obs_shift *)
      change ((wk :: skipn (S k) w') ++ [a]) with (wk :: t).
      rewrite (obs_shift (pi H w' k) wk t Htne).
      fold t. exact Hbad.
    }
    exists (pi H w' k ++ [wk]), t.
    repeat split.
    - (* q_new is genuinely new *)
      destruct (H.(Q) (pi H w' k ++ [wk])) eqn:HQ; [exfalso | reflexivity].
      destruct (str_eq (pi H w' k ++ [wk]) (pi H w' (S k))) as [Heq | Hneq].
      + apply DistQ. now rewrite Heq.
      + now destruct (H.(sep) _ _ HQ HQSk Hneq HTeq).
    - (* separability is preserved *)
      intros u v Qu Qv Neq Contra.
      unfold update, SetLemmas.update in Qu, Qv.
      destruct (str_eq u (pi H w' k ++ [wk])),
               (str_eq v (pi H w' k ++ [wk])); try subst u; try subst v; auto.
      + apply (H.(sep) (pi H w' (S k)) v HQSk Qv).
          intro Contra'. subst v. apply DistQ.
          specialize (Contra t (update_eq _ _ _ _ _)). now rewrite Contra.
        transitivity (pi H w' k ++ [wk]).
          now symmetry.
        eapply refined_distinguish; [| apply Contra].
        intros. unfold update, SetLemmas.update. now destruct str_eq.
      + apply (H.(sep) (pi H w' (S k)) u HQSk Qu).
          intro Contra'. subst u. apply DistQ.
          specialize (Contra t (update_eq _ _ _ _ _)). now rewrite <- Contra.
        transitivity (pi H w' k ++ [wk]).
          now symmetry.
        eapply refined_distinguish; [| symmetry; apply Contra].
        intros. unfold update, SetLemmas.update. now destruct str_eq.
      + apply (H.(sep) u v Qu Qv Neq).
        eapply refined_distinguish; [|apply Contra].
        intros t0 Ht0. unfold update, SetLemmas.update.
        now destruct (str_eq t0 t).
    - (* Q stays finite *)
      unfold finite. destruct H.(fin_Q) as (l & ND & X).
      eexists. split.
        apply NoDup_cons; eauto.
        + intro Contra. rewrite <- X in Contra.
          destruct (str_eq (pi H w' k ++ [wk]) (pi H w' (S k)))
            as [Heq | Hneq].
            apply DistQ. now rewrite Heq.
          now destruct (H.(sep) _ _ Contra HQSk Hneq HTeq).
        + split; intros.
          * destruct (str_eq s ((pi H w' k) ++ [wk])).
              subst. now constructor.
            apply in_cons, X. now rewrite (update_neq _ _) in H0.
          * destruct H0. subst.
              apply update_eq.
            destruct (str_eq s (pi H w' k ++ [wk])). subst.
              apply update_eq.
            rewrite update_neq. now apply X. now symmetry.
    - (* T stays finite *)
      unfold finite. destruct H.(fin_T) as (l & ND & X).
      eexists. split.
        apply NoDup_cons; eauto. intro Contra.
        rewrite <- X in Contra.
        apply DistQ. apply HTeq. eassumption.
      split; intros.
      + destruct (str_eq s t).
           subst. now constructor.
         apply in_cons, X. now rewrite update_neq in H0.
      + simpl in H0. destruct H0. subst.
           apply update_eq.
        destruct (str_eq s t). subst.
           apply update_eq.
        rewrite update_neq. now apply X. now symmetry.
Defined.

(** Lemma 3 *)
Lemma find_representative : forall Q T
    (finQ : finite Q)
    (finT : finite T)
    (u : str),
    { r | Q r = true /\ T [u == r] } +
    { forall r, Q r = true -> ~ T [u == r] }.
Proof with try easy.
    intros Q T finQ finT u.
    destruct finQ as (Ql & HQl),
    (List.find (fun q =>
        if Bool.eqb (Q q) true then
            if T_equiv_dec T u q finT then true else false
        else false) Ql) eqn:Hfind.
    - left. apply List.find_some in Hfind.
      destruct Hfind as (HIn & Hcheck).
      exists s.
      destruct (Bool.eqb (Q s) true) eqn:E...
        destruct (T_equiv_dec T u s finT)...
        split...
        apply Bool.eqb_prop in E...
    - right. intros r Hr Contra.
      apply List.find_none with (x := r) in Hfind.
      + destruct (Bool.eqb (Q r) true) eqn:E.
            destruct (T_equiv_dec T u r finT)...
        rewrite Hr in E...
      + apply HQl...
Defined.

Lemma close_step : forall Q T q (a : s.t)
    (sep : separable Q T)
    (finQ : finite Q)
    (finT : finite T),
    { Q' : str -> bool &
        ((Q' = Q [q ++ [a] := true]) + (Q' = Q)) *
        separable Q' T *
        finite Q' *
        (forall s, Q s = true -> Q' s = true) *
        { r | Q' r = true /\ T [(q ++ [a]) == r] } }.
Proof with try easy.
    intros Q T q a sep finQ finT.
    destruct (find_representative Q T finQ finT (q ++ [a])) as [rep | norep].
    - exists Q. repeat split; auto.
    - exists (update Q (q ++ [a]) true). repeat split; eauto.
      + intros u v Qu Qv Neq.
        unfold update, SetLemmas.update in *.
        destruct (str_eq u (q ++ [a])) eqn:Hu,
                 (str_eq v (q ++ [a])) eqn:Hv; subst; auto.
        intro Contra. symmetry in Contra. now apply norep in Contra.
      + destruct finQ as (Ql & NDQ & HQl).
        eexists. split.
            apply NoDup_cons; eauto. intro Contra.
            apply HQl in Contra.
            eapply norep; eauto. reflexivity.
        intro s. split.
        * intro Hs. unfold update, SetLemmas.update in Hs.
          destruct (str_eq s (q ++ [a])); subst.
            now left.
          right. now apply HQl.
        * intro HIn. unfold update, SetLemmas.update.
          destruct (str_eq s (q ++ [a]))...
          apply HQl. destruct HIn; subst...
      + intros s Hs. unfold update, SetLemmas.update.
        now destruct (str_eq s (q ++ [a])).
      + exists (q ++ [a]). split...
        apply update_eq.
Defined.

Lemma not_closed_impl_distinguishable :
    forall Q T,
        (closed Q T -> False) ->
        finite Q -> finite T ->
        {q : str & {a : s.t | Q q = true /\
            forall q', Q q' = true -> ~ T [q ++ [a] == q'] }}.
Proof.
    intros Q T QNC Qfin Tfin.
    destruct (closed_dec_witness Q T Qfin Tfin).
        contradiction.
    destruct s as (q & a & Qq & Tdist); eauto.
Defined.

Definition union_closed_loop :
    forall (n : nat) Q Q' T
        (sep' : separable Q' T)
        (finT : finite T)
        (finQ' : finite Q')
        (sub' : forall s, Q s = true -> Q' s = true),
        option { Q'' : str -> bool &
            closed Q'' T *
            separable Q'' T *
            finite Q'' *
            (forall s, Q' s = true -> Q'' s = true) }.
    intro n.
    induction n as [| n' IH]; intros Q Q' T; intros.
        exact None.
    pose proof finT as finT_copy. destruct finT as (Tl & HTl).
    destruct (closed_dec_witness Q' T finQ' (exist _ Tl HTl))
        as [clos | (q & a & Hq & norep)].
        apply Some. exists Q'. repeat split; auto.
    destruct (close_step Q' T q a sep' finQ' (exist _ Tl HTl))
            as (Q'' & (((Eq & sep'') & finQ'') & sub'') & _).
    destruct (IH Q Q'' T sep'' finT_copy finQ'' (fun s Hs => sub'' s (sub' s Hs)))
            as [result |].
        destruct result as (Q''' & ((clos''' & sep''') & finQ''') & sub''').
        apply Some. exists Q'''. repeat split; auto.
    exact None.
Defined.

(** union_closed_loop always returns Some with enough fuel *)
Lemma loop_terminates : forall n Q Q' T
    (sep' : separable Q' T)
    (finQ' : finite Q')
    (Tl : list str)
    (NDT : NoDup Tl)
    (HTl : forall s : str, T s = true <-> In s Tl)
    (sub' : forall s, Q s = true -> Q' s = true),
    Nat.pow (S (length O.enum)) (length Tl) - length (proj1_sig finQ') < n ->
    {x | union_closed_loop n Q Q' T sep' (exist _ Tl (conj NDT HTl)) finQ' sub' = Some x}.
Proof.
    intros n Q Q' T. intros.
    destruct finQ' as (Q'l & NDQ'l & finQ'). simpl in *.
    revert Q Q' sep' Q'l NDQ'l finQ' sub' H.
    induction n as [| n' IH]; intros. lia.
    rewrite Nat.lt_succ_r in H. simpl.
    destruct (closed_dec_witness Q' T
            (exist _ Q'l (conj NDQ'l finQ'))
            (exist _ Tl (conj NDT HTl))) as [clos | noclos].
        eexists. reflexivity.
    destruct noclos as (q & a & Hq & norep).
      destruct (close_step Q' T q a sep'
              (exist _ Q'l (conj NDQ'l finQ'))
              (exist _ Tl (conj NDT HTl)))
          as (Q'' & (((Eq & sep'') & finQ'') & sub'') & (r & Q''r & Teqr)).
      destruct finQ'' as (Q''l & NDQ'' & HQ''l).
      assert (Hnotin : ~ In (q ++ [a]) Q'l). {
          intro HIn.
          apply (norep (q ++ [a])).
            now apply finQ'.
          reflexivity. }
      assert (HinQ'' : In (q ++ [a]) Q''l). {
        apply HQ''l.
        destruct Eq; subst.
            apply update_eq.
        destruct (norep r); auto.
      }
      assert (Hsubset : forall s, In s Q'l -> In s Q''l). {
          intros s HIn. now apply HQ''l, sub'', finQ'. }
      destruct (IH _ Q'' sep'' Q''l NDQ'' HQ''l
              (fun s Hs => sub'' s (sub' s Hs))) as
              ((Q''' & (((clos''' & sep''') & fin''') & sub''')) & Eq').
      enough (Hlt : length Q'l < length Q''l <= Nat.pow (S (length O.enum)) (length Tl)) by lia. {
        assert (Hlt : length Q'l < length Q''l). {
            enough (H1 : length Q'l <= length Q''l). {
            enough (H2 : length Q'l <> length Q''l) by lia.
            intro Heq.
            apply Hnotin.
            assert (forall s, In s Q''l -> In s Q'l). {
                intros s Hs.
                destruct (in_dec str_eq s Q'l) as [? | Hout]; [assumption |].
                exfalso.
                assert (Hle : length Q'l <= length (remove str_eq s Q''l)). {
                  apply NoDup_incl_length. assumption.
                  intros x Hx.
                  apply in_in_remove.
                    intro Hxs. subst. contradiction.
                  now apply Hsubset. }
                assert (Hrm : length (remove str_eq s Q''l) < length Q''l) by
                    (apply remove_length_lt; auto).
                lia. } now apply H0.
            }
            now apply NoDup_incl_length.
        } split. assumption.
        set (vec := fun u => map (fun t => obs u t) Tl).
        (* vec is injective on Q''l *)
        assert (Hvec_inj : forall u v,
            In u Q''l -> In v Q''l -> vec u = vec v -> u = v). {
            intros u v Hu Hv Heqvec.
            destruct (str_eq u v) as [-> | Huv]; [reflexivity |].
            destruct (sep'' u v); auto;
                try now apply HQ''l.
            intros t Ht.
            apply HTl, In_nth with (d := t) in Ht.
            destruct Ht as (i & Hi & Hnth).
            assert (Hmu : nth_error (vec u) i = Some (obs u t)). {
                unfold vec. rewrite nth_error_map, nth_error_nth' with (d := t); [|lia].
                now rewrite Hnth. }
            assert (Hmv : nth_error (vec v) i = Some (obs v t)). {
                unfold vec. rewrite nth_error_map, nth_error_nth' with (d := t); [|lia].
                now rewrite Hnth. }
            rewrite Heqvec in Hmu. congruence. }
        assert (HND : NoDup (map vec Q''l)). {
            clear - NDQ'' Hvec_inj.
            induction Q''l as [| x xs IHxs].
            - constructor.
            - apply NoDup_cons_iff in NDQ''. destruct NDQ'' as [Hni NDxs].
                constructor.
                + intro HIn. apply in_map_iff in HIn.
                  destruct HIn as (y & Heq & Hyin).
                  replace y with x in * by (apply Hvec_inj; [left; auto | right; auto | auto]).
                  subst. contradiction.
                + apply IHxs; auto.
                  intros u v Hu Hv. apply Hvec_inj; right; auto. }
        rewrite <- length_map with (f := vec).
        (* The observation vectors live in [option O.t], enumerated by
           [None :: map Some O.enum], of length [S (length O.enum)]. *)
        set (oenum := None :: map Some O.enum).
        assert (Hoenum_len : length oenum = S (length O.enum)). {
          unfold oenum. simpl. now rewrite length_map. }
        rewrite <- Hoenum_len.
        apply NoDup_finlist_length.
        - exact HND.
        - intros v Hv. apply in_map_iff in Hv.
          destruct Hv as (u & <- & _). unfold vec. apply length_map.
        - intros v x Hv Hx.
          apply in_map_iff in Hv. destruct Hv as (u & <- & _).
          unfold vec in Hx. apply in_map_iff in Hx.
          destruct Hx as (t & <- & _).
          (* obs u t : option O.t is [None] (head of oenum) or [Some y]
             with [y ∈ O.enum] (hence in [map Some O.enum]). *)
          unfold oenum. destruct (obs u t) as [y|] eqn:Eo.
          + right. apply in_map. apply O.t_enumerable.
          + now left. }
      eexists. now rewrite Eq'.
Defined.

Lemma union_closed :
    forall Q T
    (sep : separable Q T)
    (finQ : finite Q)
    (finT : finite T),
    { Q' : str -> bool &
        closed Q' T *
        separable Q' T *
        finite Q' *
        (forall s, Q s = true -> Q' s = true) }.
Proof.
    intros Q T sep finQ finT.
    pose proof finT as finT_copy.
    destruct finT as (Tl & NDT & HTl).
    set (fuel := S (Nat.pow (S (length O.enum)) (length Tl))).
    destruct (loop_terminates fuel Q Q T sep finQ Tl NDT HTl ltac:(auto) ltac:(lia)).
    destruct x as (Q' & ((clos' & sep') & finQ') & sub').
    exists Q'. repeat split; auto.
Defined.

Definition num_states (H : HypothesisMealy) : nat :=
    num_states_of_fin _ H.(fin_Q).

(** A hypothesis is no bigger than the minimal Mealy machine *)
Lemma num_states_le_min : forall (H : HypothesisMealy),
    num_states H <= L.num_states_in_minimal.
Proof.
  intro H.
  destruct L.exists_mealy as (state_m & Mm & (Menc0 & Minimal) & Len).
  rewrite encodes_obs in Menc0. rename Menc0 into Menc.
  enough (Hle : num_states H <= Datatypes.length (M.states state_m Mm)) by lia.
  unfold num_states, num_states_of_fin.
  destruct H as [Q0 T0 sep0 clos0 eps0 finQ0 finT0].
  destruct finQ0 as (Ql & NDQl & InQl). simpl.
  set (f := fun q => M.run Mm q).
  assert (Hinj : forall u v, In u Ql -> In v Ql -> u <> v -> f u <> f v). {
    intros u v Hu Hv Huv Hf.
    apply (sep0 u v); try (now apply InQl); try assumption.
    intros t Ht.
    (* obs u t = obs nil (u++t) = mobs Mm init (u++t) = mobs Mm (run u) t,
       and likewise for v; since run u = run v (=f), the two agree.
       The empty suffix is handled uniformly by mobs_prefix' [None] case. *)
    destruct t as [| a w].
    - reflexivity.
    - rewrite (obs_prefix u a w), (obs_prefix v a w).
      rewrite <- (Menc (u ++ a :: w)), <- (Menc (v ++ a :: w)).
      rewrite (M.mobs_prefix Mm u a w), (M.mobs_prefix Mm v a w).
      unfold f in Hf. now rewrite Hf.
  }
  rewrite <- (length_map f Ql). apply NoDup_incl_length.
  - clear - NDQl Hinj.
    induction Ql; [constructor|].
    apply NoDup_cons_iff in NDQl. destruct NDQl. constructor.
    + intro HIn. apply in_map_iff in HIn. destruct HIn as (y & Hfy & Hyin).
      replace y with a in *. contradiction.
      destruct (str_eq a y). assumption.
        exfalso. apply (Hinj a y); [now left|now right|assumption|now symmetry].
    + apply IHQl; auto. intros u v Hu Hv. apply Hinj; now right.
  - intros st Hst. apply in_map_iff in Hst.
    destruct Hst as (q & <- & _). apply M.run_in_states.
Qed.

Lemma make_mealy_minimal : forall (H : HypothesisMealy),
    equiv_query (make_mealy H) = None ->
    minimal (make_mealy H).
Proof.
  intros H Heq.
  unfold minimal. split.
    now apply equiv_query_correct in Heq.
  intros state' m' H_encodes0.
  pose proof (proj1 (encodes_obs m') H_encodes0) as H_encodes.
  assert (H_LHS : Datatypes.length (M.states _ (make_mealy H)) = num_states H). {
    unfold num_states, num_states_of_fin, make_mealy.
    destruct H, fin_Q0, a. simpl. apply list_with_proof_preserves_len. }
  rewrite H_LHS.
  unfold num_states, num_states_of_fin.
  destruct H as [Q0 T0 sep0 clos0 eps0 finQ0 finT0].
  destruct finQ0 as (Ql & NDQl & InQl). simpl.
  set (f := fun q => M.run m' q).
  assert (Hinj : forall u v, In u Ql -> In v Ql -> u <> v -> f u <> f v). {
    intros u v Hu Hv Huv Hf.
    apply (sep0 u v); try (now apply InQl); try assumption.
    intros t Ht.
    destruct t as [| a w].
    - reflexivity.
    - rewrite (obs_prefix u a w), (obs_prefix v a w).
      rewrite <- (H_encodes (u ++ a :: w)), <- (H_encodes (v ++ a :: w)).
      rewrite (M.mobs_prefix m' u a w), (M.mobs_prefix m' v a w).
      unfold f in Hf. now rewrite Hf.
  }
  rewrite <- (length_map f Ql). apply NoDup_incl_length.
    clear - NDQl Hinj.
    induction Ql as [| x xs IH].
      constructor.
    apply NoDup_cons_iff in NDQl. destruct NDQl. constructor.
      intro HIn. apply in_map_iff in HIn. destruct HIn as (y & Hfy & Hyin).
        replace x with y in *. contradiction. symmetry.
        destruct (str_eq x y) as [e | n]; [assumption|].
        exfalso. now apply (Hinj x y); [now left | now right | exact n |].
      apply IH; auto. intros. apply Hinj; now (easy || right).
  intros st Hst. apply in_map_iff in Hst.
    destruct Hst as (q & <- & _). apply M.run_in_states.
Qed.

Lemma full_states_no_ce : forall (H : HypothesisMealy),
    L.num_states_in_minimal <= num_states H ->
    equiv_query (make_mealy H) = None.
Proof.
  intros H Hge.
  destruct (equiv_query (make_mealy H)) eqn:Heq; [exfalso | reflexivity].
  assert (Hce : mobs (make_mealy H) (make_mealy H).(initial _) s <> obs nil s)
    by (unfold obs; now apply equiv_query_ce).
  destruct (find_separable H s Hce) as
    (q_new & t & HQnew & (sep' & finQ') & finT').
  set (Q' := H.(Q) [q_new := true]).
  set (T' := H.(T) [t := true]).
  destruct (union_closed Q' T' sep' finQ' finT') as
    (Q'' & ((clos'' & sep'') & finQ'') & sub'').
  assert (eps_in_Q'' : Q'' nil = true). {
    apply sub''. unfold Q'. rewrite update_neq.
    - apply H.(eps_in_Q).
    - intro Heq'. subst q_new. now rewrite H.(eps_in_Q) in HQnew. }
  set (H'' := {|
      Q        := Q'';
      T        := T';
      sep      := sep'';
      clos     := clos'';
      eps_in_Q := eps_in_Q'';
      fin_Q    := finQ'';
      fin_T    := finT' |}).
  pose proof (num_states_le_min H'') as Hcap.
  pose proof (finite_subset_is_smaller _ _ _ finQ' finQ'' sub'') as Hmono.
  assert (H_step : S (num_states H) <= num_states_of_fin _ finQ'). {
      unfold num_states, num_states_of_fin.
      destruct (fin_Q H) as (fl & NDF & InF),
               finQ' as (fl' & NDF' & InF'),
               H, fin_Q0, a. simpl in *.
      change (S (Datatypes.length fl)) with (Datatypes.length (q_new :: fl)).
      apply NoDup_incl_length. constructor; [|assumption].
          intro C. apply (proj2 (InF q_new)) in C. now rewrite C in HQnew.
      unfold incl. intros y Hy.
      apply (proj1 (InF' y)).
      unfold update, SetLemmas.update. destruct Hy.
          subst y. now destruct (str_eq q_new q_new).
      apply (proj2 (InF y)) in H.
      now destruct (str_eq y q_new). }
  assert (HH'' : num_states H'' = num_states_of_fin _ finQ''). {
    now unfold H'', num_states. }
  unfold num_states in Hge, Hcap.
  destruct H''.
  unfold num_states in *. simpl in *.
  rewrite HH'' in *. lia.
Qed.

Fixpoint mlstar_fuel (H : HypothesisMealy) (fuel : nat)
    (LE : L.num_states_in_minimal - num_states H <= fuel)
    : { T : Type & {m : M.t T | minimal m} }.
  destruct (equiv_query (make_mealy H)) eqn:Heq.
  - destruct fuel as [| n].
    + exfalso.
      assert (Hge : L.num_states_in_minimal <= num_states H) by lia.
      now rewrite (full_states_no_ce H Hge) in Heq.
    + assert (Hce : mobs (make_mealy H) (make_mealy H).(initial _) s <> obs nil s)
        by (unfold obs; now apply equiv_query_ce).
      destruct (find_separable H s Hce) as
        (q_new & t & HQnew & (sep' & finQ') & finT').
      set (Q' := H.(Q) [q_new := true]).
      set (T' := H.(T) [t := true]).
      destruct (union_closed Q' T' sep' finQ' finT') as
        (Q'' & ((clos'' & sep'') & finQ'') & sub'').
      assert (eps_in_Q'' : Q'' nil = true). {
        apply sub''. unfold Q'. rewrite update_neq.
        - apply H.(eps_in_Q).
        - intro Heq'. subst q_new. now rewrite H.(eps_in_Q) in HQnew. }
      eapply (mlstar_fuel {|
          Q        := Q'';
          T        := T';
          sep      := sep'';
          clos     := clos'';
          eps_in_Q := eps_in_Q'';
          fin_Q    := finQ'';
          fin_T    := finT' |} n).
      match goal with
      | [|- context[_ - num_states ?Dh]] =>
          enough (H_strict : S (num_states H) <= num_states Dh)
      end. lia.
      pose proof (finite_subset_is_smaller _ _ _ finQ' finQ'' sub'').
      assert (H_step : S (num_states H) <= num_states_of_fin _ finQ'). {
          unfold num_states, num_states_of_fin.
          destruct (fin_Q H) as (fl & NDF & InF).
          destruct finQ' as (fl' & NDF' & InF').
          simpl. destruct H, fin_Q0. simpl in *.
          destruct a.
          change (S (Datatypes.length fl)) with (Datatypes.length (q_new :: fl)).
          apply NoDup_incl_length. constructor; [|assumption].
              intro C. apply (proj2 (InF q_new)) in C. now rewrite C in HQnew.
          unfold incl. intros y Hy.
          apply (proj1 (InF' y)).
          unfold update, SetLemmas.update. destruct Hy as [Eq | Iny].
              subst y. now destruct (str_eq q_new q_new) as [e|n'].
          apply (proj2 (InF y)) in Iny.
          now destruct (str_eq y q_new) as [e|n']. }
      unfold num_states at 2.
      etransitivity; eassumption.
  - exists {q : str | H.(Q) q = true}.
    exists (make_mealy H).
    exact (make_mealy_minimal H Heq).
Defined.

(** The total L* implementation for Mealy machines. *)
Definition mlstar (_ : unit) : { T : Type & {m : M.t T | minimal m} }.
    eapply mlstar_fuel with (fuel := num_states_in_minimal).
        lia.
    Unshelve.
    set (Q := fun s => if str_eq s nil then true else false).
    set (T := fun (_ : str) => false).
    eapply (Build_HypothesisMealy Q T); auto;
        unfold T, Q in *.
    - unfold separable, T_equiv. intros. intro Contra.
      now destruct (str_eq u nil), (str_eq v nil); subst.
    - unfold closed, T_equiv. intros. destruct (str_eq q nil); try discriminate.
      subst. exists nil. now split.
    - unfold finite. exists (nil :: nil). split. constructor.
        intro. now inversion H0.
        constructor.
      intros. destruct (str_eq s nil). subst.
        split; auto. intros. now constructor.
      split; intro. discriminate. inversion H0; subst.
      contradiction. inversion H1.
    - unfold finite. exists nil. split. constructor.
      intros. destruct (str_eq s nil). subst.
        split; auto. now intros.
      split; intro. discriminate. inversion H0.
Defined.

End MealyLstar.
