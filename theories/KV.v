(** The Kearns-Vazirani active learner (discrimination-tree variant)

    Where #L<sup>*</sup># maintains a flat set of representatives Q and a flat
    set of distinguishing suffixes T, the Kearns-Vazirani learner stores its
    knowledge in a binary _discrimination tree_: internal nodes carry a
    _discriminator_ (a distinguishing suffix), and leaves carry an _access
    string_ (a state representative).

    A string is classified by _sifting_ it down the tree: at each internal node
    with discriminator e, we ask the membership query [member (u ++ e)] and
    descend left when it holds and right otherwise; the leaf reached names the
    state of u. *)

From lstar Require Import DFA ListLemmas Teacher.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Setoids.Setoid.
Import ListNotations.

Module KV (s : Symbol) (L : RegularLanguage s) (Tch : Teacher s L).
Import s L Tch D.

(** A discrimination tree is a binary tree whose internal nodes hold a
    discriminator suffix and whose leaves hold an access string. *)
Inductive dtree : Type :=
| Leaf (access : string)
| Node (discrim : string) (lt rt : dtree).

(** Sifting classifies a string u by descending the tree until it reaches
    the appropriate access node. *)
Fixpoint sift (t : dtree) (u : string) : string :=
    match t with
    | Leaf q => q
    | Node e lt rt =>
        if member (u ++ e) then sift lt u else sift rt u
    end.

Fixpoint leaves (t : dtree) : list string :=
    match t with
    | Leaf q => [q]
    | Node _ lt rt => leaves lt ++ leaves rt
    end.

Fixpoint discriminators (t : dtree) : list string :=
    match t with
    | Leaf _ => []
    | Node e lt rt => e :: discriminators lt ++ discriminators rt
    end.

(** Sifting always lands on a leaf of the tree. *)
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
    discriminator, every leaf below the [false] branch disagrees. *)
Fixpoint wf (t : dtree) : Prop :=
    match t with
    | Leaf _ => True
    | Node e lt rt =>
        (forall q, In q (leaves lt) -> member (q ++ e) = true) /\
        (forall q, In q (leaves rt) -> member (q ++ e) = false) /\
        wf lt /\ wf rt
    end.

Definition make_dfa (t : dtree) : D.t { q | In q (leaves t) }.
    set (state := { q | In q (leaves t) }).
    assert (initial : state). {
        exists (sift t nil). apply sift_in_leaves.
    }
    assert (transition : state -> s.t -> state). {
        intros q a. exists (sift t (proj1_sig q ++ [a])). apply sift_in_leaves.
    }
    set (accept := fun (q : state) => member (proj1_sig q)).
    assert (ls : list state). {
        eapply list_with_proof. intros x Hin. apply Hin.
    }
    apply {| initial    := initial;
             transition := transition;
             accept     := accept;
             states     := ls |}.
Defined.

(** [kv_p t w i] is the access string of the state that the hypothesis induced
    by t reaches after reading the length-i prefix of w. *)
Definition kv_p (t : dtree) (w : string) (i : nat) : string :=
    proj1_sig (run (make_dfa t) (firstn i w)).

(** A prefix of length i is _correct_ when its continuation classifies as in
    the language exactly when w does. *)
Definition kv_correct (t : dtree) (w : string) (i : nat) : Prop :=
    member (kv_p t w i ++ skipn i w) = member w.

Lemma kv_correct_dec : forall t w i, {kv_correct t w i} + {~ kv_correct t w i}.
Proof.
    intros. unfold kv_correct. destruct member, member; decide equality.
Qed.

Lemma kv_eps_correct : forall t w,
    In nil (leaves t) -> consistent t -> kv_correct t w 0.
Proof.
    intros t w Heps Hcons.
    unfold kv_correct, kv_p, run; simpl.
    now rewrite (Hcons nil Heps).
Qed.

Lemma kv_full_not_correct : forall t w,
    accept_string (make_dfa t) w <> member w ->
    ~ kv_correct t w (length w).
Proof.
    intros t w Hce Contra.
    unfold kv_correct, kv_p in Contra.
    rewrite firstn_all, skipn_all, app_nil_r in Contra.
    apply Hce. unfold accept_string, accept, make_dfa; simpl.
    assumption.
Qed.

(** Replace the leaf whose access string is [target] by an internal node discriminating
    on e *)
Fixpoint split_leaf (t : dtree) (target e q_new : string) : dtree :=
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
      + destruct (member (q ++ e)); simpl in H.
        * destruct H as [Hq | [Hqn | []]].
              right. simpl. now left.
          left. now symmetry.
        * destruct H as [Hqn | [Hq | []]].
              left. now symmetry.
          right. simpl. now left.
      + destruct H as [Hq | []]. right. simpl. now left.
    - simpl in H. apply in_app_or in H. destruct H as [H | H].
      + destruct (IHlt target e q_new x H) as [Hqn | Hin].
            now left.
        right. simpl. apply in_or_app. now left.
      + destruct (IHrt target e q_new x H) as [Hqn | Hin].
            now left.
        right. simpl. apply in_or_app. now right.
Qed.

Lemma split_leaf_id : forall t target e q_new,
    ~ In target (leaves t) ->
    split_leaf t target e q_new = t.
Proof.
    induction t0 as [q | e' lt IHlt rt IHrt]; intros target e q_new Hni; simpl in *.
    - destruct (str_eq q target) as [Heq | Hneq].
          exfalso. apply Hni. now left.
      reflexivity.
    - f_equal; [apply IHlt|apply IHrt]; intro; eauto using in_or_app.
Qed.

Lemma split_leaves_pres : forall t target e q_new x,
    In x (leaves t) -> In x (leaves (split_leaf t target e q_new)).
Proof.
    induction t0 as [q | e' lt IHlt rt IHrt]; intros target e q_new x H.
    - simpl in H. destruct H as [Hq | []].
      simpl. destruct (str_eq q target) as [_ | _].
          destruct (member (q ++ e)); simpl; [left | right; left]; assumption.
      simpl. now left.
    - simpl in H. apply in_app_or in H. simpl. apply in_or_app.
      destruct H as [H | H]; [left|right]; auto.
Qed.

Lemma split_q_new_in : forall t target e q_new,
    In target (leaves t) -> In q_new (leaves (split_leaf t target e q_new)).
Proof.
    induction t0 as [q | e' lt IHlt rt IHrt]; intros target e q_new H.
    - simpl in H. destruct H as [Hq | []].
      simpl. destruct (str_eq q target) as [_ | Hneq]; [| destruct (Hneq Hq)].
      destruct (member (q ++ e)); simpl; [right; left | left]; reflexivity.
    - simpl in H. apply in_app_or in H. simpl. apply in_or_app.
      destruct H as [H | H]; [left|right]; auto.
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
      right. apply in_or_app. apply in_app_or in Hx as [Hx | Hx].
        left. now apply IHlt.
        right. now apply IHrt.
Qed.

(** A well-oriented split preserves distinctness of leaves: [target] occurs once
    and [q_new] is fresh, so replacing the former by the pair adds no
    duplicates. *)
Lemma split_NoDup : forall t target e q_new,
    NoDup (leaves t) -> In target (leaves t) -> ~ In q_new (leaves t) ->
    NoDup (leaves (split_leaf t target e q_new)).
Proof.
    induction t0 as [q | e' lt IHlt rt IHrt]; intros target e q_new HND HinT Hfresh.
    - simpl in HinT. destruct HinT as [Hq | []]. simpl in Hfresh.
      assert (Hqn : q_new <> q) by (intro Heq; apply Hfresh; left; congruence).
      simpl. destruct (str_eq q target) as [_ | Hneq]; [| destruct (Hneq Hq)].
      destruct (member (q ++ e)); simpl;
          constructor; solve
              [ intros [H | []]; congruence
              | constructor; [intros [] | constructor] ].
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

Lemma wf_NoDup : forall t, wf t -> NoDup (leaves t).
Proof.
    induction t0 as [q | e lt IHlt rt IHrt]; intro Hwf.
        simpl. constructor; [intros [] | constructor].
    simpl in Hwf. destruct Hwf as (Hl & Hr & Wl & Wr). simpl.
    apply NoDup_app_intro; [now apply IHlt | now apply IHrt |].
    intros x Hx Hxr. pose proof (Hl x Hx). pose proof (Hr x Hxr). congruence.
Qed.

Lemma wf_consistent : forall t, wf t -> consistent t.
Proof.
    induction t0 as [q | e lt IHlt rt IHrt]; intros Hwf q0 Hin.
        simpl in Hin. destruct Hin as [H | []]. simpl. assumption.
    simpl in Hwf. destruct Hwf as (Hl & Hr & Wl & Wr).
    simpl in Hin. apply in_app_or in Hin. simpl. destruct Hin as [Hin | Hin].
        rewrite (Hl q0 Hin). now apply IHlt.
    rewrite (Hr q0 Hin). now apply IHrt.
Qed.

Lemma wf_separated : forall t, wf t -> separated t.
Proof.
    induction t0 as [q | e lt IHlt rt IHrt]; intros Hwf u v Hu Hv Huv.
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

Lemma consistent_NoDup_wf : forall t,
    NoDup (leaves t) -> consistent t -> wf t.
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
    simpl. repeat split;
        [assumption | assumption | now apply IHlt | now apply IHrt].
Qed.

(** [split_leaf] preserves the invariant *)
Lemma split_preserves_wf : forall t target e q_new,
    wf t ->
    In target (leaves t) ->
    ~ In q_new (leaves t) ->
    sift t q_new = target ->
    member (target ++ e) <> member (q_new ++ e) ->
    wf (split_leaf t target e q_new).
Proof.
    induction t0 as [q | e' lt IHlt rt IHrt];
        intros target e q_new Hwf HinT Hfresh Hsift Hdiff.
    - simpl in HinT. destruct HinT as [Hq | []]. subst target.
      simpl. destruct (str_eq q q) as [_ | Hneq]; [| now destruct (Hneq eq_refl)].
      (* the new node's two singleton leaves witness orientation; the
         disagreement hypothesis [Hdiff] fixes [q_new]'s side *)
      destruct (member (q ++ e)) eqn:Em; simpl; (split; [| split; [| split]]); auto.
      + intros x Hx; destruct Hx as [Hx | []]; subst x. assumption.
      + intros x Hx; destruct Hx as [Hx | []]; subst x.
        destruct (member (q_new ++ e)) eqn:En; [| reflexivity].
        exfalso. now apply Hdiff.
      + intros x Hx; destruct Hx as [Hx | []]; subst x.
        destruct (member (q_new ++ e)) eqn:En; [reflexivity |].
        exfalso. now apply Hdiff.
      + intros x Hx; destruct Hx as [Hx | []]; subst x. assumption.
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
            exfalso. apply Hnr.
            assert (sift rt q_new = target) by (simpl in Hsift; now rewrite E in Hsift).
            rewrite <- H. apply sift_in_leaves. }
        assert (Hsl : sift lt q_new = target)
            by (simpl in Hsift; now rewrite Hqe' in Hsift).
        rewrite (split_leaf_id rt target e q_new Hnr).
        split; [| split; [| split]].
        * intros x Hx. apply split_leaves_fwd in Hx. destruct Hx as [-> | Hx].
              assumption.
          now apply Hl.
        * assumption.
        * now apply IHlt.
        * assumption.
      + (* symmetric: target is in the right subtree *)
        assert (Hnl : ~ In target (leaves lt))
            by (intro H; pose proof (Hl target H); pose proof (Hr target Hin);
                congruence).
        assert (Hqe' : member (q_new ++ e') = false). {
            destruct (member (q_new ++ e')) eqn:E; [| reflexivity].
            exfalso. apply Hnl.
            assert (sift lt q_new = target) by (simpl in Hsift; now rewrite E in Hsift).
            rewrite <- H. apply sift_in_leaves. }
        assert (Hsr : sift rt q_new = target)
            by (simpl in Hsift; now rewrite Hqe' in Hsift).
        rewrite (split_leaf_id lt target e q_new Hnl).
        split; [| split; [| split]].
        * assumption.
        * intros x Hx. apply split_leaves_fwd in Hx. destruct Hx as [-> | Hx].
              assumption.
          now apply Hr.
        * assumption.
        * now apply IHrt.
Qed.

(** Given a tree whose hypothesis mispredicts on a counterexample w, we can find
    a leaf [target] and a fresh discriminator e such that splitting [target] on
    e yields a still well-formed tree. *)
Theorem find_split :
    forall (t : dtree) (w : string)
           (Heps : In nil (leaves t))
           (Hcons : consistent t)
           (HND : NoDup (leaves t))
           (Hce : accept_string (make_dfa t) w <> member w),
    { target : string &
    { e : string &
    { q_new : string |
        In target (leaves t) /\
        ~ In q_new (leaves t) /\
        member (target ++ e) <> member (q_new ++ e) /\
        let t' := split_leaf t target e q_new in
        wf t' /\ In nil (leaves t') }}}.
Proof.
    intros t. intros.
    (* There is some k such that the prefix of length k is correct but the one
       of length (S k) is not, found by scanning [0 .. length w]. *)
    assert (ExK : { k | kv_correct t w k /\ ~ kv_correct t w (S k) }). {
        pose proof (kv_eps_correct t w Heps Hcons).
        pose proof (kv_full_not_correct t w Hce).
        induction (length w) as [| n IH].
            contradiction.
        destruct (kv_correct_dec t w n) as [Hn | Hn].
            now exists n.
        destruct (IH Hn) as [k [Hk HSk]]. now exists k.
    } destruct ExK as (k & Kcorrect & SKincorrect).
    (* The breakpoint lies strictly inside w, since beyond [length w] both
       prefixes coincide with all of w. *)
    assert (Hlt : k < length w). {
        destruct (Nat.le_gt_cases (length w) k) as [Hle |]; [| assumption].
        exfalso. apply SKincorrect. unfold kv_correct, kv_p in *.
        rewrite firstn_all2, skipn_all2, app_nil_r by lia.
        now rewrite firstn_all2, skipn_all2, app_nil_r in Kcorrect by lia.
    }
    (* Retrieve w[k]. *)
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
    set (qk1 := kv_p t w k ++ [wk]).
    exists (sift t qk1), (skipn (S k) w), qk1.
    (* One step of the hypothesis advances from p_k to the leaf [qk1] sifts to. *)
    assert (HSk : kv_p t w (S k) = sift t qk1). {
        unfold kv_p, qk1. rewrite Hfirstn. unfold run.
        rewrite fold_left_app. unfold make_dfa; simpl. reflexivity.
    }
    (* From correctness at k and incorrectness at (S k), the extension and the
       leaf it sifts to are told apart by the suffix e. *)
    assert (Hgk : member (qk1 ++ skipn (S k) w) = member w). {
        unfold kv_correct in Kcorrect.
        rewrite (skipn_S_wk _ _ _ _ Hwk) in Kcorrect.
        unfold qk1. now rewrite <- app_assoc.
    }
    assert (Hgk1 : member (sift t qk1 ++ skipn (S k) w) <> member w). {
        rewrite <- HSk. now unfold kv_correct in SKincorrect.
    }
    assert (HinT : In (sift t qk1) (leaves t)) by apply sift_in_leaves.
    assert (Hfresh : ~ In qk1 (leaves t)). {
        intro Hin. apply Hgk1. rewrite (Hcons qk1 Hin). assumption.
    }
    assert (Hdiff : member (sift t qk1 ++ skipn (S k) w)
                  <> member (qk1 ++ skipn (S k) w)). {
        now rewrite Hgk.
    }
    (* Recover [wf] of the current tree, then push it through the split. *)
    assert (Hwf : wf t) by (apply consistent_NoDup_wf; assumption).
    assert (Hwf' : wf (split_leaf t (sift t qk1) (skipn (S k) w) qk1))
        by (apply split_preserves_wf; trivial).
    repeat split; auto using split_leaves_pres.
Qed.

(** Each counterexample adds exactly one state *)
Lemma split_leaf_count : forall t target e q_new,
    NoDup (leaves t) -> In target (leaves t) -> ~ In q_new (leaves t) ->
    length (leaves (split_leaf t target e q_new)) = S (length (leaves t)).
Proof.
    intros t target e q_new HND HinT Hfresh.
    assert (ND' : NoDup (leaves (split_leaf t target e q_new)))
        by now apply split_NoDup.
    assert (NDc : NoDup (q_new :: leaves t)) by (constructor; assumption).
    (* the split tree and [q_new :: leaves t] have the same elements *)
    assert (I1 : incl (leaves (split_leaf t target e q_new)) (q_new :: leaves t)). {
        intros x Hx. apply split_leaves_fwd in Hx. destruct Hx as [-> | Hx];
            [now left | now right].
    }
    assert (I2 : incl (q_new :: leaves t) (leaves (split_leaf t target e q_new))). {
        intros x [-> | Hx];
            [now apply split_q_new_in | now apply split_leaves_pres].
    }
    pose proof (NoDup_incl_length ND' I1) as L1.
    pose proof (NoDup_incl_length NDc I2) as L2.
    simpl in L1, L2. lia.
Qed.

(** The main KV implementation. Adds one state per counterexample *)
Fixpoint kv_learn (fuel : nat) (t : dtree)
                  (Hwf : wf t) (Heps : In nil (leaves t))
    : result { St : Type & {d : D.t St | encodes d} }
             { St : Type & {d : D.t St | True} }.
    destruct fuel as [| n].
    - (* out of fuel: return the in-progress hypothesis *)
      apply Error. eexists. now exists (make_dfa t).
    - destruct (equiv_query _ (make_dfa t)) as [w |] eqn:Heq.
      + (* counterexample w: split one leaf and recurse *)
        assert (Hce : accept_string (make_dfa t) w <> member w)
            by now apply equiv_query_ce.
        destruct (find_split t w Heps (wf_consistent t Hwf) (wf_NoDup t Hwf) Hce)
            as (target & e & q_new & HinT & Hfresh & Hdiff & Hwf' & Heps').
        apply (kv_learn n (split_leaf t target e q_new) Hwf' Heps').
      + (* no counterexample, make_dfa t encodes L *)
        apply Ok. eexists. exists (make_dfa t).
        now apply equiv_query_correct in Heq.
Defined.

(** The learner is seeded with a trivially well-formed tree *)
Definition kv_run (fuel : nat)
    : result { St : Type & {d : D.t St | encodes d} }
             { St : Type & {d : D.t St | True} } :=
    kv_learn fuel (Leaf nil) I (or_introl eq_refl).

End KV.
