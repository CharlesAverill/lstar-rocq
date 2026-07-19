(** Kearns-Vazirani automata learning
    https://doi.org/10.7551/mitpress%2F3897.001.0001 *)

From lstar Require Import automata.DFA ListLemmas Teacher RS.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.

Module KV (s : Symbol) (L : RegularLanguage s) (Tch : DFATeacher s L).
Import s L Tch D.

(** A discrimination tree is a binary tree whose internal nodes hold a
    discriminator suffix and whose leaves hold an access string *)
Inductive dtree : Type :=
| Leaf (access : str)
| Node (discrim : str) (lt rt : dtree).

(** Sifting classifies a string u by descending the tree until it reaches
    the appropriate access node *)
Fixpoint sift (t : dtree) (u : str) : str :=
    match t with
    | Leaf q => q
    | Node e lt rt =>
        if member (u ++ e) then sift lt u else sift rt u
    end.

Fixpoint leaves (t : dtree) : list str :=
    match t with
    | Leaf q => [q]
    | Node _ lt rt => leaves lt ++ leaves rt
    end.

Fixpoint discriminators (t : dtree) : list str :=
    match t with
    | Leaf _ => []
    | Node e lt rt => e :: discriminators lt ++ discriminators rt
    end.

(** Sifting always lands on a leaf of the tree *)
Lemma sift_in_leaves : forall t u, In (sift t u) (leaves t).
Proof.
    induction t0 as [q | e lt IHlt rt IHrt]; intro u; simpl.
        now left.
    destruct (member (u ++ e)); auto using in_or_app.
Qed.

(** Tree invariants *)

(** A tree is _consistent_ when every access string sifts to its own leaf *)
Definition consistent (t : dtree) : Prop :=
    forall q, In q (leaves t) -> sift t q = q.

(** A tree is _separated_ when any two distinct leaves are told apart by some
    discriminator of the tree *)
Definition separated (t : dtree) : Prop :=
    forall u v,
        In u (leaves t) -> In v (leaves t) -> u <> v ->
        exists e, In e (discriminators t) /\ member (u ++ e) <> member (v ++ e).

(** A tree is _well-formed_ when each node's discriminator bisects the behavior
    of its two subtrees. Or, every leaf below the [true] branch agrees with the
    discriminator, every leaf below the [false] branch disagrees *)
Fixpoint wf' (t : dtree) : Prop :=
    match t with
    | Leaf _ => True
    | Node e lt rt =>
        (forall q, In q (leaves lt) -> member (q ++ e) = true) /\
        (forall q, In q (leaves rt) -> member (q ++ e) = false) /\
        wf' lt /\ wf' rt
    end.
Definition wf t := wf' t /\ In nil (leaves t).

Definition mem := mem str_eq.

Lemma sift_mem : forall t u, mem (sift t u) (leaves t) = true.
Proof. intros. apply mem_In, sift_in_leaves. Qed.

Definition make_dfa (t : dtree) : D.t { q | mem q (leaves t) = true }.
    set (state := { q | mem q (leaves t) = true }).
    assert (initial : state). {
        exists (sift t nil). apply sift_mem. }
    assert (transition : state -> s.t -> state). {
        intros q a. exists (sift t (proj1_sig q ++ [a])). apply sift_mem. }
    set (accept := fun (q : state) => member (proj1_sig q)).
    (* enumerate the leaves as the carrier list, via mem-proofs *)
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
  Definition obt := { o : dtree | wf o }.
  Definition P (o : obt) (q : str) : Prop := mem q (leaves (proj1_sig o)) = true.
  Definition make_dfa (o : obt) : D.t { q | P o q } := make_dfa (proj1_sig o).

  Lemma eps_in_H : forall (o : obt),
      proj1_sig (make_dfa o).(initial _) = [].
  Proof.
    intros (t & Hwf). unfold make_dfa, KV.make_dfa. simpl.
    apply (wf_consistent t Hwf). now destruct Hwf.
  Qed.

  Lemma acc_correct : forall (o : obt) q,
      accept _ (make_dfa o) q = member (proj1_sig q).
  Proof.
    intros (t & Hwf) q. unfold make_dfa, KV.make_dfa. reflexivity.
  Qed.
End RSS.

Module RSan := RS s L RSS.
Import RSan.

(** Replace the leaf whose access string is [target] by an internal node discriminating
    on e *)
Fixpoint split_leaf (t : dtree) (target e q_new : str) : dtree :=
    match t with
    | Leaf q =>
        if str_eq q target
        then if member (q ++ e)
             then Node e (Leaf q)     (Leaf q_new)
             else Node e (Leaf q_new) (Leaf q)
        else Leaf q
    | Node e' lt rt =>
        Node e' (split_leaf lt target e q_new) (split_leaf rt target e q_new)
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

Lemma split_discriminators_incl : forall t target e q_new,
    incl (discriminators t) (discriminators (split_leaf t target e q_new)).
Proof.
    induction t0 as [q | e' lt IHlt rt IHrt]; intros; simpl.
    - destruct (str_eq q target); [destruct (member (q ++ e)); simpl |];
        intros x Hx; inversion Hx.
    - intros x Hx. simpl in Hx. destruct Hx as [-> | Hx].
          now left.
      right. apply in_or_app. apply in_app_or in Hx. destruct Hx.
        left. now apply IHlt.
        right. now apply IHrt.
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
    induction t0 as [q | e lt IHlt rt IHrt]; intros HND Hcons; [exact I |].
    simpl in HND.
    pose proof (NoDup_app_l _ _ HND) as NDl.
    pose proof (NoDup_app_r _ _ HND) as NDr.
    assert (Hdisj : forall x, In x (leaves lt) -> ~ In x (leaves rt))
        by now apply NoDup_app_disj.
    (* the left subtree's leaves agree with the discriminator *)
    assert (Hl : forall q, In q (leaves lt) -> member (q ++ e) = true). {
        intros q Hq. destruct (member (q ++ e)) eqn:E; [reflexivity |]. exfalso.
        assert (Hsc : sift (Node e lt rt) q = q)
            by (apply Hcons; simpl; apply in_or_app; now left).
        simpl in Hsc. rewrite E in Hsc.
        apply (Hdisj q Hq). rewrite <- Hsc. apply sift_in_leaves. }
    (* the right subtree's leaves disagree with it *)
    assert (Hr : forall q, In q (leaves rt) -> member (q ++ e) = false). {
        intros q Hq. destruct (member (q ++ e)) eqn:E; [| reflexivity]. exfalso.
        assert (Hsc : sift (Node e lt rt) q = q)
            by (apply Hcons; simpl; apply in_or_app; now right).
        simpl in Hsc. rewrite E in Hsc.
        apply (Hdisj q); [rewrite <- Hsc; apply sift_in_leaves | assumption]. }
    (* and the subtrees are themselves consistent *)
    assert (Cl : consistent lt). {
        intros q Hq.
        assert (Hsc : sift (Node e lt rt) q = q)
            by (apply Hcons; simpl; apply in_or_app; now left).
        simpl in Hsc. now rewrite (Hl q Hq) in Hsc. }
    assert (Cr : consistent rt). {
        intros q Hq.
        assert (Hsc : sift (Node e lt rt) q = q)
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
      now destruct (member (q_new ++ e)).
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
        assert (Hqe' : member (q_new ++ e') = true). {
            destruct (member (q_new ++ e')) eqn:E; [reflexivity |].
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
        assert (Hqe' : member (q_new ++ e') = false). {
            destruct (member (q_new ++ e')) eqn:E; [| reflexivity].
            destruct Hnl.
            assert (sift lt q_new = target) by (simpl in Hsift; now rewrite E in Hsift).
            rewrite <- H. apply sift_in_leaves. }
        assert (Hsr : sift rt q_new = target)
            by (simpl in Hsift; now rewrite Hqe' in Hsift).
        rewrite (split_leaf_id lt target e q_new Hnl).
        repeat split; auto.
        intros x Hx. apply split_leaves_fwd in Hx. destruct Hx as [-> | Hx]; auto.
Qed.

(** Given a tree whose hypothesis mispredicts on a counterexample w, we can find
    a leaf [target] and a fresh discriminator e such that splitting [target] on
    e yields a still well-formed tree *)
Theorem find_split :
    forall (t : dtree) (w : str)
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
    (* The breakpoint lies strictly inside w, since beyond [length w] both
       prefixes coincide with all of w *)
    assert (Hlt : k < length w). {
        destruct (Nat.le_gt_cases (length w) k) as [Hle |]; [| assumption].
        destruct SKincorrect. unfold correct, pi in *.
        rewrite firstn_all2, skipn_all2, app_nil_r by lia.
        now rewrite firstn_all2, skipn_all2, app_nil_r in Kcorrect by lia.
    }
    (* Retrieve w[k] *)
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
    (* One step of the hypothesis advances from p_k to the leaf [qk1] sifts to *)
    assert (HSk : pi o w (S k) = sift t qk1). {
        unfold pi, qk1, run, make_dfa. rewrite Hfirstn, fold_left_app.
        reflexivity.
    }
    (* From correctness at k and incorrectness at (S k), the extension and the
       leaf it sifts to are told apart by the suffix e *)
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

(** Each counterexample adds exactly one state *)
Lemma split_leaf_count : forall t target e q_new,
    NoDup (leaves t) -> In target (leaves t) -> ~ In q_new (leaves t) ->
    length (leaves (split_leaf t target e q_new)) = S (length (leaves t)).
Proof.
    intros t target e q_new HND HinT Hfresh.
    assert (ND' : NoDup (leaves (split_leaf t target e q_new)))
        by now apply split_NoDup.
    assert (NDc : NoDup (q_new :: leaves t)) by now constructor.
    (* the split tree and [q_new :: leaves t] have the same elements *)
    assert (I1 : incl (leaves (split_leaf t target e q_new)) (q_new :: leaves t)). {
        intros x Hx. apply split_leaves_fwd in Hx. destruct Hx as [-> | Hx]; now constructor.
    }
    assert (I2 : incl (q_new :: leaves t) (leaves (split_leaf t target e q_new))). {
        intros x [-> | Hx];
            [now apply split_q_new_in | now apply split_leaves_pres].
    }
    pose proof (NoDup_incl_length ND' I1) as L1.
    pose proof (NoDup_incl_length NDc I2) as L2.
    simpl in L1, L2. lia.
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
    destruct (Hsep u v Hu Hv Huv) as (e & He & Hdiff).
    apply Hdiff.
    assert (Hsplit : forall x,
              D.accept_string dfa' (x ++ e)
              = dfa'.(D.accept _) (fold_left dfa'.(D.transition _) e (f x)))
      by (intro x; unfold D.accept_string, D.run, f; now rewrite fold_left_app).
    assert (Hacc : D.accept_string dfa' (u ++ e) = D.accept_string dfa' (v ++ e))
      by (rewrite !Hsplit; unfold f in *; now rewrite Hf).
    destruct (member (u ++ e)) eqn:Mu, (member (v ++ e)) eqn:Mv;
      try reflexivity; exfalso.
    - assert (D.accept_string dfa' (u ++ e) = true) by (now apply H_encodes).
      assert (D.accept_string dfa' (v ++ e) = true) by (now rewrite <- Hacc).
      assert (member (v ++ e) = true) by (now apply H_encodes). congruence.
    - assert (D.accept_string dfa' (v ++ e) = true) by (now apply H_encodes).
      assert (D.accept_string dfa' (u ++ e) = true) by (now rewrite Hacc).
      assert (member (u ++ e) = true) by (now apply H_encodes). congruence. }
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
  - (* every mapped state is a real state of dfa' *)
    intros st Hst. apply in_map_iff in Hst.
    destruct Hst as (q & <- & _). unfold f. apply D.run_in_states.
Qed.

Lemma le_min : forall t,
    wf t ->
    length (leaves t) <= num_states_in_minimal.
Proof.
  intro t. intro Hwf.
  destruct L.exists_dfa as (state_m & D & [Denc Minimal] & Len).
  (* It suffices to bound leaves by D's state count *)
  enough (Hle : List.length (leaves t) <= List.length (D.states state_m D)) by lia.
  pose proof (wf_separated _ Hwf) as Hsep.
  pose proof (wf_NoDup _ Hwf) as HND.
  set (f := fun q => D.run D q).
  (* f is injective on the leaves *)
  assert (Hinj : forall u v, In u (leaves t) -> In v (leaves t) ->
                 u <> v -> f u <> f v). {
    intros u v Hu Hv Huv Hf.
    (* Some discriminator e of t tells u and v apart *)
    destruct (Hsep u v Hu Hv Huv) as (e & He & Hdiff).
    (* But equal runs make u and v agree on every suffix, including e *)
    apply Hdiff.
    assert (Hsplit : forall x,
              D.accept_string D (x ++ e)
              = D.(D.accept _) (fold_left D.(D.transition _) e (f x))). {
      intro x. unfold D.accept_string, D.run, f. now rewrite fold_left_app. }
    assert (Hacc : D.accept_string D (u ++ e) = D.accept_string D (v ++ e)). {
      rewrite Hsplit. unfold f in *. now rewrite Hf. }
    (* Transport the acceptance equality back to membership via Denc *)
    destruct (member (u ++ e)) eqn:Mu, (member (v ++ e)) eqn:Mv;
      try reflexivity; exfalso.
    - assert (D.accept_string D (u ++ e) = true) by (now apply Denc).
      assert (D.accept_string D (v ++ e) = true) by (now rewrite <- Hacc).
      assert (member (v ++ e) = true) by (now apply Denc). congruence.
    - assert (D.accept_string D (v ++ e) = true) by (now apply Denc).
      assert (D.accept_string D (u ++ e) = true) by (now rewrite Hacc).
      assert (member (u ++ e) = true) by (now apply Denc). congruence.
  }
  (* An injection from leaves into D's states bounds the lengths *)
  rewrite <- (length_map f (leaves t)).
  apply NoDup_incl_length.
  - (* map f (leaves t) is duplicate-free, by injectivity of f on the leaves *)
    clear - HND Hinj.
    induction (leaves t) as [| x xs IH]; [constructor|].
    apply NoDup_cons_iff in HND. destruct HND as [Hnin NDxs]. constructor.
    + intro HIn. apply in_map_iff in HIn. destruct HIn as (y & Hfy & Hyin).
      assert (x = y). { destruct (str_eq x y) as [e|n]; [exact e|].
        exfalso. apply (Hinj x y); [now left | now right | exact n | now symmetry]. }
      subst y; contradiction.
    + apply IH; auto. intros u v Hu Hv. apply Hinj; now right.
  - (* every mapped state is an actual state of D *)
    intros st Hst. apply in_map_iff in Hst.
    destruct Hst as (q & <- & _). unfold f. apply D.run_in_states.
Qed.

Lemma full_states_no_ce : forall (t : dtree),
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
    (* Hcap : length (leaves (split_leaf t target e q_new)) <= num_states_in_minimal *)
    rewrite Hcount in Hcap.
    (* Hcap : S (length (leaves t)) <= num_states_in_minimal *)
    lia.
Qed.

(** The main KV implementation. Adds one state per counterexample *)
Fixpoint kv_learn (fuel : nat) (t : dtree)
                  (LE : L.num_states_in_minimal - List.length (leaves t) <= fuel)
                  (Hwf : wf t)
    : { St : Type & {d : D.t St | minimal d} }.
    destruct (equiv_query (make_dfa t)) eqn:Heq.
    - (* counterexample *)
        destruct fuel as [| n].
        -- assert (forall x y, x - y <= 0 -> x - y = 0) by lia. apply H in LE. clear H.
           apply Nat.sub_0_le, full_states_no_ce in LE; auto.
           rewrite Heq in LE. discriminate.
        -- assert (Hce : accept_string (make_dfa t) s <> member s)
                by now apply equiv_query_ce.
            pose proof Hwf as Hwf'.
            destruct Hwf' as (Hwf' & Heps).
            destruct (find_split t s Heps (wf_consistent t Hwf) (wf_NoDup t Hwf) Hce)
                as (target & e & q_new & HinT & Hfresh & Hdiff & Hwf'' & Heps').
            enough (num_states_in_minimal - List.length (leaves (split_leaf t target e q_new)) <= n).
            eapply (kv_learn n (split_leaf t target e q_new) H (conj Hwf'' Heps')).
            pose proof (split_leaf_count t target e q_new
                          (wf_NoDup t Hwf) HinT Hfresh) as Hcount.
            rewrite Hcount. lia.
    - eexists. exists (make_dfa t). apply (make_dfa_minimal t Hwf Heq).
Defined.

(** The learner is seeded with a trivially well-formed tree *)
Definition kv (_ : unit) : { St : Type & {d : D.t St | minimal d} } :=
    kv_learn num_states_in_minimal (Leaf nil) ltac:(lia) (conj I (or_introl eq_refl)).

End KV.
