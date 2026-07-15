(** TTT automata learning
    https://doi.org/10.1007/978-3-319-11164-3 *)

From Stdlib Require Import Lia PeanoNat Bool.
From Stdlib Require Import Eqdep_dec.
From lstar Require Import automata.DFA Teacher ListLemmas RS.
Import ListNotations.

Module TTT (s : Symbol) (L : RegularLanguage s) (Tch : DFATeacher s L).
Import s L Tch D.

(** Trees are now tagged with whether their discriminators are
    _final_ or _temporary_ *)
Inductive disc : Type :=
| Final (e : str)
| Temp  (e : str).

Definition disc_str (d : disc) : str :=
    match d with Final e => e | Temp e => e end.

Inductive ttree : Type :=
| Leaf (access : str)
| Node (d : disc) (lt rt : ttree).

(** Sifting, as in KV *)
Fixpoint sift (t : ttree) (u : str) : str :=
    match t with
    | Leaf q => q
    | Node d lt rt =>
        if member (u ++ disc_str d) then sift lt u else sift rt u
    end.

Fixpoint leaves (t : ttree) : list str :=
    match t with
    | Leaf q => [q]
    | Node _ lt rt => leaves lt ++ leaves rt
    end.

Fixpoint discriminators (t : ttree) : list disc :=
    match t with
    | Leaf _ => []
    | Node d lt rt => d :: discriminators lt ++ discriminators rt
    end.

Lemma sift_in_leaves : forall t u, In (sift t u) (leaves t).
Proof.
    induction t0; intro u; simpl.
        now left.
    destruct (member (u ++ disc_str d)); auto using in_or_app.
Qed.

(** Tree invariants, as in KV *)
Definition consistent (t : ttree) : Prop :=
    forall q, In q (leaves t) -> sift t q = q.

Definition separated (t : ttree) : Prop :=
    forall u v,
        In u (leaves t) -> In v (leaves t) -> u <> v ->
        exists d, In d (discriminators t)
                /\ member (u ++ disc_str d) <> member (v ++ disc_str d).

Fixpoint wf' (t : ttree) : Prop :=
    match t with
    | Leaf _ => True
    | Node d lt rt =>
        (forall q, In q (leaves lt) -> member (q ++ disc_str d) = true) /\
        (forall q, In q (leaves rt) -> member (q ++ disc_str d) = false) /\
        wf' lt /\ wf' rt
    end.
Definition wf t := wf' t /\ In nil (leaves t).

(** A discrimination tree is _finalized_ if all of its
    internal nodes are final *)
Fixpoint finalized (t : ttree) : Prop :=
    match t with
    | Leaf _ => True
    | Node (Final _) lt rt => finalized lt /\ finalized rt
    | _ => False
    end.

Definition mem := mem str_eq.

Lemma sift_mem : forall t u, mem (sift t u) (leaves t) = true.
Proof. intros. apply mem_In, sift_in_leaves. Qed.

(** Hypothesis construction, as in KV *)
Definition make_dfa (t : ttree) : D.t { q | mem q (leaves t) = true }.
    set (state := { q | mem q (leaves t) = true }).
    assert (initial : state). {
        exists (sift t nil). apply sift_mem. }
    assert (transition : state -> s.t -> state). {
        intros q a. exists (sift t (proj1_sig q ++ [a])). apply sift_mem. }
    set (accept := fun (q : state) => member (proj1_sig q)).
    assert (mempf : forall x, In x (leaves t) -> mem x (leaves t) = true)
        by (intros x Hx; now apply mem_In).
    set (ls := list_with_proof (leaves t) (fun q => mem q (leaves t) = true) mempf).
    refine {| initial    := initial;
              transition := transition;
              accept     := accept;
              states     := ls;
              states_complete := _ |}.
    intro w.
    set (qst := fold_left transition w initial).
    assert (Hin : In (proj1_sig qst) (leaves t))
        by apply (mem_In str_eq), (proj2_sig qst).
    assert (Heq : qst = exist _ (proj1_sig qst) (mempf (proj1_sig qst) Hin)). {
        destruct qst as (q & Hq); simpl.
        f_equal. apply (UIP_dec Bool.bool_dec). }
    rewrite Heq.
    apply (list_with_proof_complete (leaves t) (fun q => mem q (leaves t) = true)).
    intros. apply UIP_dec, Bool.bool_dec.
Defined.

Lemma wf_NoDup : forall t, wf t -> NoDup (leaves t).
Proof.
    intros. destruct H as (Hwf & _).
    induction t0 as [q | e lt IHlt rt IHrt].
        simpl. constructor; [intuition | constructor].
    simpl in Hwf. destruct Hwf as (Hl & Hr & Wl & Wr). simpl.
    apply NoDup_app_intro; [now apply IHlt | now apply IHrt |].
    intros x Hx Hxr. pose proof (Hl x Hx). pose proof (Hr x Hxr). congruence.
Qed.

Lemma wf_consistent : forall t, wf t -> consistent t.
Proof.
    intros. destruct H as (Hwf & _).
    induction t0 as [q | e lt IHlt rt IHrt]; intros q0 Hin.
        simpl in Hin. destruct Hin as [H | []]. simpl. assumption.
    simpl in Hwf. destruct Hwf as (Hl & Hr & Wl & Wr).
    simpl in Hin. apply in_app_or in Hin. simpl. destruct Hin.
        rewrite (Hl q0 H). now apply IHlt.
    rewrite (Hr q0 H). now apply IHrt.
Qed.

Lemma wf_separated : forall t, wf t -> separated t.
Proof.
    intros. destruct H as (Hwf & _).
    induction t0 as [q | e lt IHlt rt IHrt]; intros u v Hu Hv Huv.
        simpl in Hu, Hv. destruct Hu as [-> | []], Hv as [-> | []]. now elim Huv.
    simpl in Hwf. destruct Hwf as (Hl & Hr & Wl & Wr).
    simpl in Hu, Hv. apply in_app_or in Hu. apply in_app_or in Hv.
    destruct Hu as [Hu | Hu], Hv as [Hv | Hv].
    - destruct (IHlt Wl u v Hu Hv Huv) as (d & Hd & Hdiff).
      exists d. split; [simpl; right; apply in_or_app; now left | assumption].
    - exists e. split; [simpl; now left |].
      rewrite (Hl u Hu), (Hr v Hv). discriminate.
    - exists e. split; [simpl; now left |].
      rewrite (Hr u Hu), (Hl v Hv). discriminate.
    - destruct (IHrt Wr u v Hu Hv Huv) as (d & Hd & Hdiff).
      exists d. split; [simpl; right; apply in_or_app; now right | assumption].
Qed.

(** Set up Rivest-Schapire counterexample analysis *)
Module RSS <: RS_Setup s L.
  Definition obt := { o : ttree | wf o }.
  Definition P (o : obt) (q : str) : Prop := mem q (leaves (proj1_sig o)) = true.
  Definition make_dfa (o : obt) : D.t { q | P o q } := make_dfa (proj1_sig o).

  Lemma eps_in_H : forall (o : obt),
      proj1_sig (make_dfa o).(initial _) = [].
  Proof.
    intros (t & Hwf). unfold make_dfa, TTT.make_dfa. simpl.
    apply (wf_consistent t Hwf). now destruct Hwf.
  Qed.

  Lemma acc_correct : forall (o : obt) q,
      accept _ (make_dfa o) q = member (proj1_sig q).
  Proof.
    intros (t & Hwf) q. unfold make_dfa, TTT.make_dfa. reflexivity.
  Qed.
End RSS.

Module RSan := RS s L RSS.
Import RSan.

Fixpoint split_leaf (t : ttree) (target e q_new : str) : ttree :=
    match t with
    | Leaf q =>
        if str_eq q target
        then if member (q ++ e)
             then Node (Temp e) (Leaf q)     (Leaf q_new)
             else Node (Temp e) (Leaf q_new) (Leaf q)
        else Leaf q
    | Node d lt rt =>
        Node d (split_leaf lt target e q_new) (split_leaf rt target e q_new)
    end.

Lemma split_leaves_fwd : forall t target e q_new x,
    In x (leaves (split_leaf t target e q_new)) ->
    x = q_new \/ In x (leaves t).
Proof.
    induction t0 as [q | e' lt IHlt rt IHrt]; intros target e q_new x H.
    - simpl in H. destruct (str_eq q target) as [Heq | Hneq]; simpl in H.
      + destruct (member (q ++ e)); simpl in H;
        destruct H; subst; auto.
            right. now left.
        destruct H; [|contradiction]; auto.
      + destruct H; [|contradiction]. right. now left.
    - simpl in H. apply in_app_or in H. destruct H;
      [destruct (IHlt target e q_new x H) as [Hqn | Hin]|
       destruct (IHrt target e q_new x H) as [Hqn | Hin]]; auto;
       right; apply in_or_app; auto.
Qed.

Lemma split_leaf_id : forall t target e q_new,
    ~ In target (leaves t) ->
    split_leaf t target e q_new = t.
Proof.
    induction t0 as [q | e' lt IHlt rt IHrt]; intros target e q_new Hni; simpl in *.
    - destruct (str_eq q target); auto.
      destruct Hni; auto.
    - f_equal; [apply IHlt|apply IHrt]; intro; eauto using in_or_app.
Qed.

Lemma split_leaves_pres : forall t target e q_new x,
    In x (leaves t) -> In x (leaves (split_leaf t target e q_new)).
Proof.
    induction t0 as [q | e' lt IHlt rt IHrt]; intros target e q_new x H.
    - simpl in H. destruct H; [|contradiction].
      simpl. destruct (str_eq q target); subst; [|now left].
      now destruct (member (target ++ e)); simpl; [left | right; left].
    - apply in_app_or in H. apply in_or_app.
      destruct H; auto.
Qed.

Lemma split_q_new_in : forall t target e q_new,
    In target (leaves t) -> In q_new (leaves (split_leaf t target e q_new)).
Proof.
    induction t0 as [q | e' lt IHlt rt IHrt]; intros target e q_new H.
    - simpl in H. destruct H; [|contradiction]; subst.
      simpl. destruct (str_eq target target); [|contradiction].
      now destruct (member (target ++ e)); simpl; [right; left | left].
    - simpl in H. apply in_app_or in H. simpl. apply in_or_app.
      destruct H; auto.
Qed.

Lemma split_leaves_bwd : forall t target e q_new x,
    In target (leaves t) ->
    (x = q_new \/ In x (leaves t)) ->
    In x (leaves (split_leaf t target e q_new)).
Proof.
    intros. destruct H0.
        subst. now apply split_q_new_in.
    now apply split_leaves_pres.
Qed.

(** A well-oriented split preserves distinctness of leaves: [target] occurs once
    and [q_new] is fresh, so replacing the former by the pair adds no
    duplicates *)
Lemma split_NoDup : forall t target e q_new,
    NoDup (leaves t) -> In target (leaves t) -> ~ In q_new (leaves t) ->
    NoDup (leaves (split_leaf t target e q_new)).
Proof.
    induction t0 as [q | e' lt IHlt rt IHrt]; intros target e q_new HND HinT Hfresh.
    - simpl in HinT. destruct HinT as [Hq | []]. simpl in Hfresh.
      assert (Hqn : q_new <> q) by (intro Heq; apply Hfresh; left; congruence).
      simpl. destruct (str_eq q target) as [_ | Hneq]; [| contradiction].
      destruct (member (q ++ e)); simpl; (constructor;
              [ intros x; destruct x; easy || congruence
              | constructor; [intros x; destruct x | constructor] ]).
    - simpl in HND, HinT, Hfresh. simpl.
      pose proof (NoDup_app_l _ _ HND) as NDl.
      pose proof (NoDup_app_r _ _ HND) as NDr.
      assert (Hfl : ~ In q_new (leaves lt))
          by (intro; apply Hfresh, in_or_app; now left).
      assert (Hfr : ~ In q_new (leaves rt))
          by (intro; apply Hfresh, in_or_app; now right).
      apply in_app_or in HinT. destruct HinT as [Hin | Hin].
      + assert (Hnr : ~ In target (leaves rt))
            by now apply (NoDup_app_disj _ _ HND).
        rewrite (split_leaf_id rt target e q_new Hnr).
        apply NoDup_app_intro; [now apply IHlt | assumption |].
        intros x Hx Hxr. apply split_leaves_fwd in Hx. destruct Hx as [-> | Hx].
            now apply Hfr.
        now apply (NoDup_app_disj _ _ HND x Hx).
      + assert (Hnl : ~ In target (leaves lt))
            by (intro Hl; apply (NoDup_app_disj _ _ HND target Hl Hin)).
        rewrite (split_leaf_id lt target e q_new Hnl).
        apply NoDup_app_intro; [assumption | now apply IHrt |].
        intros x Hx Hxr. apply split_leaves_fwd in Hxr. destruct Hxr as [-> | Hxr].
            now apply Hfl.
        now apply (NoDup_app_disj _ _ HND x Hx).
Qed.


Lemma consistent_NoDup_wf' : forall t,
    NoDup (leaves t) -> consistent t -> wf' t.
Proof.
    induction t0 as [q | d lt IHlt rt IHrt]; intros HND Hcons; [exact I |].
    simpl in HND.
    pose proof (NoDup_app_l _ _ HND) as NDl.
    pose proof (NoDup_app_r _ _ HND) as NDr.
    assert (Hdisj : forall x, In x (leaves lt) -> ~ In x (leaves rt))
        by now apply NoDup_app_disj.
    assert (Hl : forall q, In q (leaves lt) -> member (q ++ disc_str d) = true). {
        intros q Hq. destruct (member (q ++ disc_str d)) eqn:E; [reflexivity |].
        exfalso.
        assert (Hsc : sift (Node d lt rt) q = q)
            by (apply Hcons; simpl; apply in_or_app; now left).
        simpl in Hsc. rewrite E in Hsc.
        apply (Hdisj q Hq). rewrite <- Hsc. apply sift_in_leaves. }
    assert (Hr : forall q, In q (leaves rt) -> member (q ++ disc_str d) = false). {
        intros q Hq. destruct (member (q ++ disc_str d)) eqn:E; [| reflexivity].
        exfalso.
        assert (Hsc : sift (Node d lt rt) q = q)
            by (apply Hcons; simpl; apply in_or_app; now right).
        simpl in Hsc. rewrite E in Hsc.
        apply (Hdisj q); [rewrite <- Hsc; apply sift_in_leaves | assumption]. }
    assert (Cl : consistent lt). {
        intros q Hq.
        assert (Hsc : sift (Node d lt rt) q = q)
            by (apply Hcons; simpl; apply in_or_app; now left).
        simpl in Hsc. now rewrite (Hl q Hq) in Hsc. }
    assert (Cr : consistent rt). {
        intros q Hq.
        assert (Hsc : sift (Node d lt rt) q = q)
            by (apply Hcons; simpl; apply in_or_app; now right).
        simpl in Hsc. now rewrite (Hr q Hq) in Hsc. }
    simpl. repeat split; auto.
Qed.

(** [split_leaf] preserves the invariant *)
Lemma split_preserves_wf' : forall t target e q_new,
    wf' t ->
    In target (leaves t) ->
    ~ In q_new (leaves t) ->
    sift t q_new = target ->
    member (target ++ e) <> member (q_new ++ e) ->
    wf' (split_leaf t target e q_new).
Proof.
    induction t0 as [q | e' lt IHlt rt IHrt];
        intros target e q_new Hwf HinT Hfresh Hsift Hdiff.
    - simpl in HinT. destruct HinT as [Hq | []]. subst target.
      simpl. destruct (str_eq q q) as [_ | Hneq]; [| now destruct (Hneq eq_refl)].
      (* the new node's two singleton leaves witness orientation *)
      destruct (member (q ++ e)) eqn:Em; repeat split; auto;
      intros x Hx; destruct Hx as [Hx|[]]; subst x; subst; easy ||
      (simpl; now destruct (member (q_new ++ e))).
    - simpl in Hwf. destruct Hwf as (Hl & Hr & Wl & Wr).
      simpl in HinT, Hfresh. apply in_app_or in HinT. simpl.
      assert (Hfl : ~ In q_new (leaves lt))
          by (intro; apply Hfresh, in_or_app; now left).
      assert (Hfr : ~ In q_new (leaves rt))
          by (intro; apply Hfresh, in_or_app; now right).
      destruct HinT as [Hin | Hin].
      + (* target is in the left subtree, so the right subtree is untouched *)
        assert (Hnr : ~ In target (leaves rt))
            by (intro H; pose proof (Hl target Hin); pose proof (Hr target H);
                congruence).
        (* q_new sifts toward the left subtree as well *)
        assert (Hqe' : member (q_new ++ disc_str e') = true). {
            destruct (member (q_new ++ disc_str e')) eqn:E; [reflexivity |].
            destruct Hnr.
            assert (sift rt q_new = target) by (simpl in Hsift; now rewrite E in Hsift).
            rewrite <- H. apply sift_in_leaves. }
        assert (Hsl : sift lt q_new = target)
            by (simpl in Hsift; now rewrite Hqe' in Hsift).
        rewrite (split_leaf_id rt target e q_new Hnr).
        repeat split; auto.
        intros x Hx. apply split_leaves_fwd in Hx. destruct Hx as [-> | Hx]; auto.
      + (* symmetric: target is in the right subtree *)
        assert (Hnl : ~ In target (leaves lt))
            by (intro H; pose proof (Hl target H); pose proof (Hr target Hin);
                congruence).
        assert (Hqe' : member (q_new ++ disc_str e') = false). {
            destruct (member (q_new ++ disc_str e')) eqn:E; [| reflexivity].
            destruct Hnl.
            assert (sift lt q_new = target) by (simpl in Hsift; now rewrite E in Hsift).
            rewrite <- H. apply sift_in_leaves. }
        assert (Hsr : sift rt q_new = target)
            by (simpl in Hsift; now rewrite Hqe' in Hsift).
        rewrite (split_leaf_id lt target e q_new Hnl).
        repeat split; auto.
        intros x Hx. apply split_leaves_fwd in Hx. destruct Hx as [-> | Hx]; auto.
Qed.


Theorem find_split :
    forall (t : ttree) (w : str)
           (Heps : In nil (leaves t))
           (Hcons : consistent t)
           (HND : NoDup (leaves t))
           (Hce : accept_string (make_dfa t) w <> member w),
    { target : str &
    { e : str &
    { q_new : str |
        In target (leaves t) /\
        ~ In q_new (leaves t) /\
        member (target ++ e) <> member (q_new ++ e) /\
        let t' := split_leaf t target e q_new in
        wf t' }}}.
Proof.
    intros t. intros.
    assert (Hwf : wf t) by (split; [ now apply consistent_NoDup_wf' | easy ]).
    destruct (partition_binary (exist _ t Hwf) w Hce)
      as (k & Kcorrect & SKincorrect).
    assert (Hlt : k < List.length w). {
        destruct (Nat.le_gt_cases (List.length w) k) as [Hle |]; [| assumption].
        destruct SKincorrect. unfold correct, pi in *.
        rewrite firstn_all2, skipn_all2, app_nil_r by lia.
        now rewrite firstn_all2, skipn_all2, app_nil_r in Kcorrect by lia.
    }
    assert {wk | nth_error w k = Some wk}. {
        destruct (nth_error w k) eqn:E.
            now exists t0.
        rewrite nth_error_None in E. lia.
    } destruct X as (wk & Hwk).
    destruct (nth_error_split_sig _ _ _ Hwk) as (l1 & l2 & Hw & Hlen).
    assert (Hfirstn : firstn (S k) w = firstn k w ++ [wk]). {
        subst.
        now rewrite firstn_app, Nat.sub_succ_l, firstn_all2, firstn_cons,
                    Nat.sub_diag, firstn_0, firstn_len_app by lia.
    }
    set (o := exist wf t Hwf : RSS.obt).
    set (qk1 := pi o w k ++ [wk]).
    exists (sift t qk1), (skipn (S k) w), qk1.
    assert (HSk : pi o w (S k) = sift t qk1). {
        unfold pi, qk1, run, make_dfa. rewrite Hfirstn, fold_left_app.
        reflexivity.
    }
    assert (Hgk : member (qk1 ++ skipn (S k) w) = member w). {
        unfold correct in Kcorrect.
        rewrite (skipn_S_wk _ _ _ _ Hwk) in Kcorrect.
        unfold qk1. now rewrite <- app_assoc.
    }
    assert (Hgk1 : member (sift t qk1 ++ skipn (S k) w) <> member w). {
        rewrite <- HSk. now unfold correct in SKincorrect.
    }
    pose proof (sift_in_leaves t qk1) as HinT.
    assert (Hfresh : ~ In qk1 (leaves t)). {
        intro Hin. apply Hgk1. now rewrite (Hcons qk1 Hin).
    }
    assert (Hdiff : member (sift t qk1 ++ skipn (S k) w)
                  <> member (qk1 ++ skipn (S k) w)) by now rewrite Hgk.
    assert (Hwf' : wf' t) by (now apply consistent_NoDup_wf').
    assert (Hwf'' : wf' (split_leaf t (sift t qk1) (skipn (S k) w) qk1))
        by (now apply split_preserves_wf').
    repeat split; auto using split_leaves_pres.
Defined.

Lemma split_leaf_count : forall t target e q_new,
    NoDup (leaves t) -> In target (leaves t) -> ~ In q_new (leaves t) ->
    List.length (leaves (split_leaf t target e q_new)) = S (List.length (leaves t)).
Proof.
    intros t target e q_new HND HinT Hfresh.
    assert (ND' : NoDup (leaves (split_leaf t target e q_new)))
        by now apply split_NoDup.
    assert (NDc : NoDup (q_new :: leaves t)) by now constructor.
    assert (I1 : incl (leaves (split_leaf t target e q_new)) (q_new :: leaves t)). {
        intros x Hx. apply split_leaves_fwd in Hx. destruct Hx as [-> | Hx]; now constructor.
    }
    assert (I2 : incl (q_new :: leaves t) (leaves (split_leaf t target e q_new))). {
        intros x [-> | Hx];
            [now apply split_q_new_in | now apply split_leaves_pres].
    }
    pose proof (NoDup_incl_length ND' I1) as Ln1.
    pose proof (NoDup_incl_length NDc I2) as Ln2.
    simpl in Ln1, Ln2. lia.
Qed.

Lemma make_dfa_minimal : forall t,
    wf t ->
    equiv_query (make_dfa t) = None ->
    minimal (make_dfa t).
Proof.
  intros t Hwf Heq.
  unfold minimal. split.
    now apply equiv_query_correct in Heq.
  intros state' dfa' H_encodes.
  assert (H_LHS : List.length (states _ (make_dfa t)) = List.length (leaves t)). {
    unfold make_dfa. simpl. apply list_with_proof_preserves_len. }
  rewrite H_LHS.
  pose proof (wf_separated _ Hwf) as Hsep.
  pose proof (wf_consistent _ Hwf) as Hcons.
  pose proof (wf_NoDup _ Hwf) as HND.
  set (f := fun q => D.run dfa' q).
  assert (Hinj : forall u v, In u (leaves t) -> In v (leaves t) ->
                 u <> v -> f u <> f v). {
    intros u v Hu Hv Huv Hf.
    destruct (Hsep u v Hu Hv Huv) as (d & Hd & Hdiff).
    apply Hdiff.
    assert (Hsplit : forall x,
              D.accept_string dfa' (x ++ disc_str d)
              = dfa'.(D.accept _) (fold_left dfa'.(D.transition _) (disc_str d) (f x)))
      by (intro x; unfold D.accept_string, D.run, f; now rewrite fold_left_app).
    assert (Hacc : D.accept_string dfa' (u ++ disc_str d)
                 = D.accept_string dfa' (v ++ disc_str d))
      by (rewrite !Hsplit; unfold f in *; now rewrite Hf).
    destruct (member (u ++ disc_str d)) eqn:Mu, (member (v ++ disc_str d)) eqn:Mv;
      try reflexivity; exfalso.
    - assert (D.accept_string dfa' (u ++ disc_str d) = true) by (now apply H_encodes).
      assert (D.accept_string dfa' (v ++ disc_str d) = true) by (now rewrite <- Hacc).
      assert (member (v ++ disc_str d) = true) by (now apply H_encodes). congruence.
    - assert (D.accept_string dfa' (v ++ disc_str d) = true) by (now apply H_encodes).
      assert (D.accept_string dfa' (u ++ disc_str d) = true) by (now rewrite Hacc).
      assert (member (u ++ disc_str d) = true) by (now apply H_encodes). congruence. }
  rewrite <- (length_map f (leaves t)).
  apply NoDup_incl_length.
  - clear - HND Hinj.
    induction (leaves t) as [| x xs IH]; [constructor|].
    apply NoDup_cons_iff in HND. destruct HND as [Hnin NDxs]. constructor.
    + intro HIn. apply in_map_iff in HIn. destruct HIn as (y & Hfy & Hyin).
      replace x with y in *. contradiction.
      destruct (str_eq x y) as [e0|n0]; [now symmetry|].
      exfalso. apply (Hinj x y); [now left | now right | assumption | now symmetry].
    + apply IH; auto. intros u v Hu Hv. apply Hinj; now right.
  - intros st Hst. apply in_map_iff in Hst.
    destruct Hst as (q & <- & _). unfold f. apply D.run_in_states.
Qed.

Lemma le_min : forall t,
    wf t ->
    List.length (leaves t) <= num_states_in_minimal.
Proof.
  intro t. intro Hwf.
  destruct L.exists_dfa as (state_m & Dm & [Denc Minimal] & Len).
  enough (Hle : List.length (leaves t) <= List.length (D.states state_m Dm)) by lia.
  pose proof (wf_separated _ Hwf) as Hsep.
  pose proof (wf_NoDup _ Hwf) as HND.
  set (f := fun q => D.run Dm q).
  assert (Hinj : forall u v, In u (leaves t) -> In v (leaves t) ->
                 u <> v -> f u <> f v). {
    intros u v Hu Hv Huv Hf.
    destruct (Hsep u v Hu Hv Huv) as (d & Hd & Hdiff).
    apply Hdiff.
    assert (Hsplit : forall x,
              D.accept_string Dm (x ++ disc_str d)
              = Dm.(D.accept _) (fold_left Dm.(D.transition _) (disc_str d) (f x))). {
      intro x. unfold D.accept_string, D.run, f. now rewrite fold_left_app. }
    assert (Hacc : D.accept_string Dm (u ++ disc_str d)
                 = D.accept_string Dm (v ++ disc_str d)). {
      rewrite Hsplit. unfold f in *. now rewrite Hf. }
    destruct (member (u ++ disc_str d)) eqn:Mu, (member (v ++ disc_str d)) eqn:Mv;
      try reflexivity; exfalso.
    - assert (D.accept_string Dm (u ++ disc_str d) = true) by (now apply Denc).
      assert (D.accept_string Dm (v ++ disc_str d) = true) by (now rewrite <- Hacc).
      assert (member (v ++ disc_str d) = true) by (now apply Denc). congruence.
    - assert (D.accept_string Dm (v ++ disc_str d) = true) by (now apply Denc).
      assert (D.accept_string Dm (u ++ disc_str d) = true) by (now rewrite Hacc).
      assert (member (u ++ disc_str d) = true) by (now apply Denc). congruence.
  }
  rewrite <- (length_map f (leaves t)).
  apply NoDup_incl_length.
  - clear - HND Hinj.
    induction (leaves t) as [| x xs IH]; [constructor|].
    apply NoDup_cons_iff in HND. destruct HND as [Hnin NDxs]. constructor.
    + intro HIn. apply in_map_iff in HIn. destruct HIn as (y & Hfy & Hyin).
      assert (x = y). { destruct (str_eq x y) as [e|n]; [exact e|].
        exfalso. apply (Hinj x y); [now left | now right | exact n | now symmetry]. }
      subst y; contradiction.
    + apply IH; auto. intros u v Hu Hv. apply Hinj; now right.
  - intros st Hst. apply in_map_iff in Hst.
    destruct Hst as (q & <- & _). unfold f. apply D.run_in_states.
Qed.

Lemma full_states_no_ce : forall (t : ttree),
    wf t ->
    L.num_states_in_minimal <= List.length (leaves t) ->
    equiv_query (make_dfa t) = None.
Proof.
    intros t Hwf Contra.
    destruct (equiv_query (make_dfa t)) eqn:Heq; [exfalso | reflexivity].
    assert (Hce : accept_string (make_dfa t) s <> member s)
        by now apply equiv_query_ce.
    pose proof (wf_separated _ Hwf) as Hsep.
    pose proof (wf_consistent _ Hwf) as Hcons.
    pose proof (wf_NoDup _ Hwf) as HND. destruct Hwf as (Hwf & Heps).
    destruct (find_split _ s Heps Hcons HND Hce) as
        (target & e & q_new & In_target & NIn_qnew & Membership & X).
    cbv zeta in X. destruct X as (Wft' & Heps').
    pose proof (split_leaf_count t target e q_new HND In_target NIn_qnew) as Hcount.
    assert (wf (split_leaf t target e q_new)) by now split.
    pose proof (le_min _ H) as Hcap.
    rewrite Hcount in Hcap.
    lia.
Qed.

Section Finalize.
  Definition bisects e l r : bool :=
    (forallb (fun q => member (q ++ e)) (leaves l)) &&
    (forallb (fun q => negb (member (q ++ e))) (leaves r)).

  (* All suffixes of a string [e] *)
  Fixpoint suffixes (e : str) : list str :=
    e :: match e with
         | [] => []
         | _ :: e' => suffixes e'
         end.

  (** Among the suffixes of [e], pick the SHORTEST that bisects [l]/[r].
      If none does, fall back to [e]. *)
  Definition choose (e : str) (l r : ttree) : str :=
    match find (fun e' => bisects e' l r) (rev (suffixes e)) with
    | Some e' => e'
    | None    => e
    end.

  Fixpoint finalize (t : ttree) : ttree :=
    match t with
    | Leaf q => Leaf q
    | Node (Final e) lt rt => Node (Final e) (finalize lt) (finalize rt)
    | Node (Temp e) lt rt =>
        let lt' := finalize lt in
        let rt' := finalize rt in
        Node (Final (choose e lt' rt')) lt' rt'
    end.

  (** Finalization preserves the leaf set *)
  Lemma finalize_leaves : forall t, leaves (finalize t) = leaves t.
  Proof.
    induction t0 as [q | d lt IHlt rt IHrt]; simpl.
        reflexivity.
    destruct d; simpl; now rewrite IHlt, IHrt.
  Qed.

  (** [finalize] finalizes *)
  Lemma finalize_finalized : forall t, finalized (finalize t).
  Proof.
    induction t0 as [q | d lt IHlt rt IHrt]; simpl.
        exact I.
    destruct d; simpl; repeat split; auto.
  Qed.

  Lemma in_bigger_leaves_impl_in_smaller_leaves :
    forall s d l r,
    In s (leaves (Node d l r)) -> In s (leaves l) \/ In s (leaves r).
  Proof.
    intros. simpl in H. now apply in_app_or in H.
  Qed.

  Lemma wf_bisects_impl_bisects :
    forall e lt rt,
        (forall q : str, In q (leaves lt) -> member (q ++ e) = true) ->
        (forall q : str, In q (leaves rt) -> member (q ++ e) = false) ->
        bisects e lt rt = true.
  Proof.
    intros.
    unfold bisects. apply andb_true_iff. split;
        apply forallb_forall; intros; eauto.
    specialize (H0 _ H1). now rewrite H0.
  Qed.

  (** Conversely, a [bisects] flag gives back the two block-classification
      facts. Used to turn [choose]'s output into routing information. *)
  Lemma bisects_impl_clauses :
    forall e lt rt,
      bisects e lt rt = true ->
      (forall q, In q (leaves lt) -> member (q ++ e) = true) /\
      (forall q, In q (leaves rt) -> member (q ++ e) = false).
  Proof.
    unfold bisects. intros e lt rt H. apply andb_true_iff in H as [HL HR].
    rewrite forallb_forall in HL, HR. split.
    - intros q Hq. now apply HL.
    - intros q Hq. specialize (HR q Hq). now apply negb_true_iff in HR.
  Qed.

  (** Every suffix in [suffixes e] is no longer than [e]. *)
  Lemma suffixes_length : forall e e',
    In e' (suffixes e) -> List.length e' <= List.length e.
  Proof.
    induction e as [| a e IH]; intros e' Hin; simpl in Hin.
    - destruct Hin as [<- | []]. reflexivity.
    - destruct Hin as [<- | Hin].
      + reflexivity.
      + simpl. apply le_S. now apply IH.
  Qed.

  (** Bisecting input gives a bisecting, no-longer output *)
  Lemma choose_correct : forall e l r,
    bisects e l r = true ->
    bisects (choose e l r) l r = true /\
    List.length (choose e l r) <= List.length e.
  Proof.
    intros e l r He. unfold choose.
    destruct (find (fun e' => bisects e' l r) (rev (suffixes e))) eqn:F.
    - apply find_some in F as [Hin Hbis].
      apply in_rev in Hin. auto using suffixes_length.
    - now split.
  Qed.

  (** If some suffix strictly shorter than [e] bisects, the chosen
      discriminator is strictly shorter *)
  Theorem choose_shortens : forall e l r e0,
    In e0 (suffixes e) ->
    bisects e0 l r = true ->
    List.length (choose e l r) <= List.length e0.
  Proof.
    induction e as [| a e IH]; intros l r e0 Hin Hbis.
    - simpl in Hin. destruct Hin as [<- | []].
      unfold choose. simpl. now rewrite Hbis.
    - unfold choose.
      simpl (suffixes (a :: e)). simpl.
      rewrite list_find.
      destruct (find (fun e' => bisects e' l r) (rev (suffixes e))) eqn:F.
      + assert (Hs_in : In l0 (suffixes e))
          by (apply find_some in F as [Hi _]; now apply in_rev in Hi).
        assert (Hs_len : List.length l0 <= List.length e)
          by now apply suffixes_length.
        destruct Hin as [<- | Hin0].
            simpl. lia.
        assert (Hchoose_e : choose e l r = l0) by
            (unfold choose; now rewrite F).
        pose proof (IH l r e0 Hin0 Hbis) as Hle.
        now rewrite Hchoose_e in Hle.
      + simpl in *. destruct Hin as [<- | Hin0].
            now destruct (bisects _ _ _).
        exfalso.
        assert (Hin_rev : In e0 (rev (suffixes e))) by
            now rewrite <- in_rev.
        pose proof (find_none _ _ F e0 Hin_rev) as Hf.
        simpl in Hf. congruence.
  Qed.

  (** Finalization preserves well-formedness *)
  Lemma finalize_preserves_wf :
    forall t, wf t -> wf (finalize t).
  Proof.
    intros t H. destruct H as [H Heps]. unfold wf. split;
        [clear Heps | now rewrite finalize_leaves].
    induction t as [q | d lt IHlt rt IHrt]; simpl in *.
        exact I.
    destruct H as (DL & DR & Hwfl & Hwfr).
    rewrite <- (finalize_leaves lt) in DL.
    rewrite <- (finalize_leaves rt) in DR.
    destruct d; simpl. repeat split; auto.
    assert (Hbis : bisects e (finalize lt) (finalize rt) = true)
        by now apply wf_bisects_impl_bisects.
    destruct (choose_correct e (finalize lt) (finalize rt) Hbis) as [Hchb _].
    apply bisects_impl_clauses in Hchb as [HL HR].
    repeat split; auto.
  Qed.

  Lemma choose_routes_agree_leaves : forall e l r u,
    bisects e l r = true ->
    In u (leaves l) \/ In u (leaves r) ->
    member (u ++ choose e l r) = member (u ++ e).
  Proof.
    intros e l r u He Hu.
    destruct (choose_correct e l r He) as [Hchb _].
    apply bisects_impl_clauses in He as [HLe HRe].
    apply bisects_impl_clauses in Hchb as [HLc HRc].
    destruct Hu as [Hu | Hu].
    - now rewrite (HLe u Hu), (HLc u Hu).
    - now rewrite (HRe u Hu), (HRc u Hu).
  Qed.

  Lemma choose_routes_agree :
    forall e l r u,
        bisects e l r = true ->
        In u (leaves l) \/ In u (leaves r) ->
        member (u ++ choose e l r) = member (u ++ e).
  Proof.
    intros e l r u Hbis Hin.
    unfold choose.
    destruct (find (fun e' => bisects e' l r)
                    (rev (suffixes e))) eqn:F.
    - apply find_some in F as [Hin_rev Hbis_l0].
      apply in_rev, suffixes_length in Hin_rev.
      apply bisects_impl_clauses in Hbis_l0 as [Hl Hr].
      assert (Hrell :
        forall q, In q (leaves l) ->
            member (q ++ e) = member (q ++ l0)). {
        intros q Hq.
        rewrite Hl by assumption;
            apply bisects_impl_clauses in Hbis as [HLe _];
            now rewrite HLe.
      }
      assert (Hrelr :
        forall q, In q (leaves r) ->
            member (q ++ e) = member (q ++ l0)). {
        intros q Hq.
        rewrite Hr by assumption;
            apply bisects_impl_clauses in Hbis as [_ HRe];
            now rewrite HRe.
      }
      destruct Hin as [HinL | HinR].
        now rewrite <- (Hrell u HinL).
        now rewrite <- (Hrelr u HinR).
    - destruct Hin as [HinL | HinR];
        apply bisects_impl_clauses in Hbis as [Hl _]; auto.
    Qed.

  Lemma finalize_sift_agree_leaves :
    forall t u, wf t -> In u (leaves t) -> sift (finalize t) u = sift t u.
  Proof.
    intros t u H. destruct H as [H _].
    induction t as [q | d lt IHlt rt IHrt]; intro Hu; simpl in *.
        reflexivity.
    destruct H as (DL & DR & Hwfl & Hwfr).
    apply in_app_or in Hu.
    assert (Hbis : bisects (disc_str d) (finalize lt) (finalize rt) = true). {
        apply wf_bisects_impl_bisects;
        intros q Hq; rewrite finalize_leaves in Hq; auto. }
    destruct d; simpl in *.
    - destruct (member (u ++ e)) eqn:M; destruct Hu as [Hu | Hu]; auto.
        specialize (DR u Hu). congruence.
        specialize (DL u Hu). congruence.
    - assert (Hroute : member (u ++ choose e (finalize lt) (finalize rt))
                       = member (u ++ e)). {
        apply choose_routes_agree_leaves with (l := finalize lt) (r := finalize rt).
            assumption.
        now repeat rewrite !finalize_leaves. }
      rewrite Hroute.
      destruct (member (u ++ e)) eqn:M; destruct Hu as [Hu | Hu]; auto.
        specialize (DR u Hu). congruence.
        specialize (DL u Hu). congruence.
  Qed.

  (** Every finalized discriminator is no longer than its origin *)
  Lemma choose_length : forall e l r,
    List.length (choose e l r) <= List.length e.
  Proof.
    intros e l r. unfold choose.
    destruct (find (fun e' => bisects e' l r) (rev (suffixes e))) eqn:F;
        [|reflexivity].
    apply find_some in F as [Hin _]. apply in_rev in Hin.
    now apply suffixes_length.
  Qed.

  Lemma finalize_length_bound :
  forall t,
    Forall (fun d' => exists d, In d (discriminators t) /\
                          List.length (disc_str d') <= List.length (disc_str d))
           (discriminators (finalize t)).
  Proof.
    intros t.
    induction t as [q | d lt IHlt rt IHrt]; simpl in *.
        constructor.
    destruct d; simpl.
    - constructor.
        eexists. split; auto.
      apply Forall_app. split.
      -- eapply Forall_impl; [| eassumption].
         intros d' (d & Hin & Hle). exists d. split; [| assumption].
         right. apply in_or_app. now left.
      -- eapply Forall_impl; [| eassumption].
         intros d' (d & Hin & Hle). exists d. split; [| assumption].
         right. apply in_or_app. now right.
    - constructor.
        eexists. split; [now left |]. simpl.
        apply choose_length.
      apply Forall_app. split.
      -- eapply Forall_impl; [| eassumption].
         intros d' (d & Hin & Hle). exists d. split; [| assumption].
         right. apply in_or_app. now left.
      -- eapply Forall_impl; [| eassumption].
         intros d' (d & Hin & Hle). exists d. split; [| assumption].
         right. apply in_or_app. now right.
  Qed.

End Finalize.

Section Learner.
  Definition ttt_step (t : ttree) (target e q_new : str) : ttree :=
    finalize (split_leaf t target e q_new).

  Fixpoint ttt_learn (fuel : nat) (t : ttree)
                   (LE : L.num_states_in_minimal - List.length (leaves t) <= fuel)
                   (Hwf : wf t)
  : { St : Type & {d : D.t St | minimal d} }.
  Proof.
    destruct (equiv_query (make_dfa t)) eqn:Heq.
    - destruct fuel as [| n].
        + assert (forall x y, x - y <= 0 -> x - y = 0) by lia.
          apply H in LE. clear H.
          apply Nat.sub_0_le, full_states_no_ce in LE; auto.
          now rewrite Heq in LE.
        + assert (Hce : accept_string (make_dfa t) s <> member s)
            by now apply equiv_query_ce.
          pose proof Hwf as Hwf'.
          destruct Hwf' as (Hwf' & Heps).
          destruct (find_split t s Heps
                      (wf_consistent t Hwf)
                      (wf_NoDup t Hwf)
                      Hce)
              as (target & e & q_new &
                  HinT & Hfresh & Hdiff &
                  Hwf'' & Heps').
          enough (L.num_states_in_minimal - 
                  List.length (leaves (ttt_step t target e q_new)) <= n).
          eapply (ttt_learn n (ttt_step t target e q_new) H),
            finalize_preserves_wf. now split.
          unfold ttt_step.
          pose proof
            (split_leaf_count t target e q_new
                (wf_NoDup t Hwf) HinT Hfresh) as Hcount.
          rewrite finalize_leaves, Hcount. lia.
    - eexists. exists (make_dfa t). now apply make_dfa_minimal.
  Defined.

  Definition ttt (_ : unit) : { St : Type & {d : D.t St | minimal d} } :=
    ttt_learn num_states_in_minimal (Leaf nil) ltac:(lia) (conj I (or_introl eq_refl)).

End Learner.

End TTT.
