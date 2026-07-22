(** Kearns-Vazirani for Moore machines using binary equality-test discrimination trees.
    Each internal node tests whether sifting a suffix [e] yields a specific output [o].
    Distinguishing more than two outputs on one suffix is achieved by chaining such tests down the [no] spine. *)

From lstar Require Import automata.Moore ListLemmas Teacher RS.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.

Module KV_Moore_Binary (s : Symbol) (O : Output) (L : MooreLanguage s O) (Tch : MooreTeacher s O L).
Import s L Tch M.

(** A discrimination tree is a binary tree whose internal nodes hold a
    discriminator suffix [e] and an output value [o], branching on whether
    [output_lang (u ++ e)] equals [o]; leaves hold an access string. *)
Inductive dtree : Type :=
| Leaf (access : str)
| Node (discrim : str) (o : O.t) (yes no : dtree).

(** Test performed at an internal node: does [u] produce output [o] on [e]? *)
Definition node_test (u e : str) (o : O.t) : bool :=
    if O.eq_dec (output_lang (u ++ e)) o then true else false.

Lemma node_test_true : forall u e o,
    node_test u e o = true <-> output_lang (u ++ e) = o.
Proof.
    intros u e o. unfold node_test. destruct (O.eq_dec (output_lang (u ++ e)) o).
    - split; auto.
    - split; [discriminate | intro; contradiction].
Qed.

Lemma node_test_false : forall u e o,
    node_test u e o = false <-> output_lang (u ++ e) <> o.
Proof.
    intros u e o. unfold node_test. destruct (O.eq_dec (output_lang (u ++ e)) o).
    - split; [discriminate | intro C; contradiction].
    - split; auto.
Qed.

(** Sifting classifies a string [u] by descending the tree until it reaches
    the appropriate access node *)
Fixpoint sift (t : dtree) (u : str) : str :=
    match t with
    | Leaf q => q
    | Node e o yes no =>
        if node_test u e o then sift yes u else sift no u
    end.

Fixpoint leaves (t : dtree) : list str :=
    match t with
    | Leaf q => [q]
    | Node _ _ yes no => leaves yes ++ leaves no
    end.

Fixpoint discriminators (t : dtree) : list str :=
    match t with
    | Leaf _ => []
    | Node e _ yes no => e :: discriminators yes ++ discriminators no
    end.

(** Sifting always lands on a leaf of the tree *)
Lemma sift_in_leaves : forall t u, In (sift t u) (leaves t).
Proof.
    induction t0 as [q | e o yes IHyes no IHno]; intro u; simpl.
        now left.
    destruct (node_test u e o); auto using in_or_app.
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
        exists e, In e (discriminators t)
               /\ output_lang (u ++ e) <> output_lang (v ++ e).

(** A tree is _well-formed_ when each node's discriminator classifies the leaves
    of its two subtrees. Or, every leaf below the [yes] branch produces [o] on [e],
    and every leaf below the [no] branch does not. *)
Fixpoint wf' (t : dtree) : Prop :=
    match t with
    | Leaf _ => True
    | Node e o yes no =>
        (forall q, In q (leaves yes) -> output_lang (q ++ e) = o) /\
        (forall q, In q (leaves no)  -> output_lang (q ++ e) <> o) /\
        wf' yes /\ wf' no
    end.
Definition wf t := wf' t /\ In nil (leaves t).

Definition mem := mem str_eq.

Lemma sift_mem : forall t u, mem (sift t u) (leaves t) = true.
Proof. intros. apply mem_In, sift_in_leaves. Qed.

Definition make_moore (t : dtree) : M.t { q | mem q (leaves t) = true }.
    set (state := { q | mem q (leaves t) = true }).
    assert (initial : state). {
        exists (sift t nil). apply sift_mem. }
    assert (transition : state -> s.t -> state). {
        intros q a. exists (sift t (proj1_sig q ++ [a])). apply sift_mem. }
    set (output := fun (q : state) => output_lang (proj1_sig q)).
    (* enumerate the leaves as the carrier list, via mem-proofs *)
    assert (mempf : forall x, In x (leaves t) -> mem x (leaves t) = true)
        by (intros x Hx; now apply mem_In).
    set (ls := list_with_proof (leaves t) (fun q => mem q (leaves t) = true) mempf).
    refine {| initial    := initial;
              transition := transition;
              output     := output;
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
    induction t0 as [q | e o yes IHyes no IHno].
        simpl. constructor; [intuition | constructor].
    simpl in Hwf. destruct Hwf as (Hy & Hn & Wy & Wn). simpl.
    apply NoDup_app_intro; [now apply IHyes | now apply IHno |].
    intros x Hx Hxn. pose proof (Hy x Hx). pose proof (Hn x Hxn). congruence.
Qed.

Lemma wf_consistent : forall t, wf t -> consistent t.
Proof.
    intros. destruct H as (Hwf & _).
    induction t0 as [q | e o yes IHyes no IHno]; intros q0 Hin.
        simpl in Hin. destruct Hin as [H | []]. simpl. assumption.
    simpl in Hwf. destruct Hwf as (Hy & Hn & Wy & Wn).
    simpl in Hin. apply in_app_or in Hin. simpl. destruct Hin.
        rewrite (proj2 (node_test_true q0 e o) (Hy q0 H)). now apply IHyes.
    rewrite (proj2 (node_test_false q0 e o) (Hn q0 H)). now apply IHno.
Qed.

Lemma wf_separated : forall t, wf t -> separated t.
Proof.
    intros. destruct H as (Hwf & _).
    induction t0 as [q | e o yes IHyes no IHno]; intros u v Hu Hv Huv.
        simpl in Hu, Hv. destruct Hu as [-> | []], Hv as [-> | []]. now elim Huv.
    simpl in Hwf. destruct Hwf as (Hy & Hn & Wy & Wn).
    simpl in Hu, Hv. apply in_app_or in Hu. apply in_app_or in Hv.
    destruct Hu as [Hu | Hu], Hv as [Hv | Hv].
    - destruct (IHyes Wy u v Hu Hv Huv) as (d & Hd & Hdiff).
      exists d. split; [simpl; right; apply in_or_app; now left | assumption].
    - exists e. split; [simpl; now left |].
      rewrite (Hy u Hu). intro C. symmetry in C. now apply (Hn v Hv).
    - exists e. split; [simpl; now left |].
      rewrite (Hy v Hv). intro C. now apply (Hn u Hu).
    - destruct (IHno Wn u v Hu Hv Huv) as (d & Hd & Hdiff).
      exists d. split; [simpl; right; apply in_or_app; now right | assumption].
Qed.

(** Set up Rivest-Schapire counterexample analysis *)
Module RSS <: MooreRS_Setup s O L.
  Definition obt := { t : dtree | wf t }.
  Definition P (o : obt) (q : str) : Prop := mem q (leaves (proj1_sig o)) = true.
  Definition make_moore (o : obt) : M.t { q | P o q } := make_moore (proj1_sig o).

  Lemma eps_in_H : forall (o : obt),
      proj1_sig (make_moore o).(initial _) = [].
  Proof.
    intros (t & Hwf). unfold make_moore, KV_Moore_Binary.make_moore. simpl.
    apply (wf_consistent t Hwf). now destruct Hwf.
  Qed.

  Lemma out_correct : forall (o : obt) q,
      output _ (make_moore o) q = output_lang (proj1_sig q).
  Proof.
    intros (t & Hwf) q. unfold make_moore, KV_Moore_Binary.make_moore. reflexivity.
  Qed.
End RSS.

Module RSan := MooreRS s O L RSS.
Import RSan.

(** Replace the leaf whose access string is [target] by an internal node discriminating
    on [e].  *)
Fixpoint split_leaf (t : dtree) (target e q_new : str) : dtree :=
    match t with
    | Leaf q =>
        if str_eq q target
        then Node e (output_lang (q ++ e)) (Leaf q) (Leaf q_new)
        else Leaf q
    | Node e' o' yes no =>
        Node e' o' (split_leaf yes target e q_new) (split_leaf no target e q_new)
    end.

Lemma split_leaves_fwd : forall t target e q_new x,
    In x (leaves (split_leaf t target e q_new)) ->
    x = q_new \/ In x (leaves t).
Proof.
    induction t0 as [q | e' o' yes IHyes no IHno]; intros target e q_new x H.
    - simpl in H. destruct (str_eq q target) as [Heq | Hneq]; simpl in H.
      + destruct H as [-> | [-> | []]]; auto. now right; left.
      + destruct H as [-> | []]. right; now left.
    - simpl in H. apply in_app_or in H. destruct H;
      [destruct (IHyes target e q_new x H) as [Hqn | Hin]|
       destruct (IHno target e q_new x H) as [Hqn | Hin]]; auto;
       right; apply in_or_app; auto.
Qed.

Lemma split_leaf_id : forall t target e q_new,
    ~ In target (leaves t) ->
    split_leaf t target e q_new = t.
Proof.
    induction t0 as [q | e' o' yes IHyes no IHno]; intros target e q_new Hni; simpl in *.
    - destruct (str_eq q target); auto.
      destruct Hni; auto.
    - f_equal; [apply IHyes | apply IHno]; intro; eauto using in_or_app.
Qed.

Lemma split_leaves_pres : forall t target e q_new x,
    In x (leaves t) -> In x (leaves (split_leaf t target e q_new)).
Proof.
    induction t0 as [q | e' o' yes IHyes no IHno]; intros target e q_new x H.
    - simpl in H. destruct H; [|contradiction].
      simpl. destruct (str_eq q target); subst; [|now left].
      simpl. now left.
    - apply in_app_or in H. apply in_or_app.
      destruct H; auto.
Qed.

Lemma split_q_new_in : forall t target e q_new,
    In target (leaves t) -> In q_new (leaves (split_leaf t target e q_new)).
Proof.
    induction t0 as [q | e' o' yes IHyes no IHno]; intros target e q_new H.
    - simpl in H. destruct H; [|contradiction]; subst.
      simpl. destruct (str_eq target target); [|contradiction].
      simpl. right; now left.
    - simpl in H. apply in_app_or in H. simpl. apply in_or_app.
      destruct H; auto.
Qed.

(** A well-oriented split preserves distinctness of leaves: [target] occurs once
    and [q_new] is fresh, so replacing the former by the pair adds no
    duplicates *)
Lemma split_NoDup : forall t target e q_new,
    NoDup (leaves t) -> In target (leaves t) -> ~ In q_new (leaves t) ->
    NoDup (leaves (split_leaf t target e q_new)).
Proof.
    induction t0 as [q | e' o' yes IHyes no IHno]; intros target e q_new HND HinT Hfresh.
    - simpl in HinT. destruct HinT as [Hq | []]. simpl in Hfresh.
      assert (Hqn : q_new <> q) by (intro Heq; apply Hfresh; left; congruence).
      simpl. destruct (str_eq q target) as [_ | Hneq]; [| congruence].
      simpl. constructor;
        [ intros [C | []]; congruence
        | constructor; [intros [] | constructor] ].
    - simpl in HND, HinT, Hfresh. simpl.
      pose proof (NoDup_app_l _ _ HND) as NDy.
      pose proof (NoDup_app_r _ _ HND) as NDn.
      assert (Hfy : ~ In q_new (leaves yes))
          by (intro; apply Hfresh, in_or_app; now left).
      assert (Hfn : ~ In q_new (leaves no))
          by (intro; apply Hfresh, in_or_app; now right).
      apply in_app_or in HinT. destruct HinT as [Hin | Hin].
      + assert (Hnn : ~ In target (leaves no))
            by now apply (NoDup_app_disj _ _ HND).
        rewrite (split_leaf_id no target e q_new Hnn).
        apply NoDup_app_intro; [now apply IHyes | assumption |].
        intros x Hx Hxn. apply split_leaves_fwd in Hx. destruct Hx as [-> | Hx].
            now apply Hfn.
        now apply (NoDup_app_disj _ _ HND x Hx).
      + assert (Hny : ~ In target (leaves yes))
            by (intro Hy; apply (NoDup_app_disj _ _ HND target Hy Hin)).
        rewrite (split_leaf_id yes target e q_new Hny).
        apply NoDup_app_intro; [assumption | now apply IHno |].
        intros x Hx Hxn. apply split_leaves_fwd in Hxn. destruct Hxn as [-> | Hxn].
            now apply Hfy.
        now apply (NoDup_app_disj _ _ HND x Hx).
Qed.

Lemma consistent_NoDup_wf' : forall t,
    NoDup (leaves t) -> consistent t -> wf' t.
Proof.
    induction t0 as [q | e o yes IHyes no IHno]; intros HND Hcons. exact I.
    simpl in HND.
    pose proof (NoDup_app_l _ _ HND) as NDy.
    pose proof (NoDup_app_r _ _ HND) as NDn.
    assert (Hdisj : forall x, In x (leaves yes) -> ~ In x (leaves no))
        by now apply NoDup_app_disj.
    (* the yes subtree's leaves produce o on e *)
    assert (Hy : forall q, In q (leaves yes) -> output_lang (q ++ e) = o). {
        intros q Hq. destruct (node_test q e o) eqn:E.
          now apply node_test_true.
        exfalso.
        assert (Hsc : sift (Node e o yes no) q = q)
            by (apply Hcons; simpl; apply in_or_app; now left).
        simpl in Hsc. rewrite E in Hsc.
        apply (Hdisj q Hq). rewrite <- Hsc. apply sift_in_leaves. }
    (* the no subtree's leaves do not produce o on e *)
    assert (Hn : forall q, In q (leaves no) -> output_lang (q ++ e) <> o). {
        intros q Hq. destruct (node_test q e o) eqn:E.
          exfalso.
          assert (Hsc : sift (Node e o yes no) q = q)
              by (apply Hcons; simpl; apply in_or_app; now right).
          simpl in Hsc. rewrite E in Hsc.
          apply (Hdisj q); [rewrite <- Hsc; apply sift_in_leaves | assumption].
        now apply node_test_false. }
    (* and the subtrees are themselves consistent *)
    assert (Cy : consistent yes). {
        intros q Hq.
        assert (Hsc : sift (Node e o yes no) q = q)
            by (apply Hcons; simpl; apply in_or_app; now left).
        simpl in Hsc.
        now rewrite (proj2 (node_test_true q e o) (Hy q Hq)) in Hsc. }
    assert (Cn : consistent no). {
        intros q Hq.
        assert (Hsc : sift (Node e o yes no) q = q)
            by (apply Hcons; simpl; apply in_or_app; now right).
        simpl in Hsc.
        now rewrite (proj2 (node_test_false q e o) (Hn q Hq)) in Hsc. }
    simpl. repeat split; auto.
Qed.

(** [split_leaf] preserves the invariant *)
Lemma split_preserves_wf' : forall t target e q_new,
    wf' t ->
    In target (leaves t) ->
    ~ In q_new (leaves t) ->
    sift t q_new = target ->
    output_lang (target ++ e) <> output_lang (q_new ++ e) ->
    wf' (split_leaf t target e q_new).
Proof.
    induction t0 as [q | e' o' yes IHyes no IHno];
        intros target e q_new Hwf HinT Hfresh Hsift Hdiff.
    - simpl in HinT. destruct HinT as [Hq | []]. subst target.
      simpl. destruct (str_eq q q) as [_ | Hneq]; [| now destruct (Hneq eq_refl)].
      (* the new node tests output_lang (q ++ e): q lands yes, q_new lands no *)
      simpl. repeat split.
      + intros x [Hx | []]. subst x. reflexivity.
      + intros x [Hx | []]. subst x. intro C. apply Hdiff. now rewrite C.
    - simpl in Hwf. destruct Hwf as (Hy & Hn & Wy & Wn).
      simpl in HinT, Hfresh. apply in_app_or in HinT. simpl.
      assert (Hfy : ~ In q_new (leaves yes))
          by (intro; apply Hfresh, in_or_app; now left).
      assert (Hfn : ~ In q_new (leaves no))
          by (intro; apply Hfresh, in_or_app; now right).
      destruct HinT as [Hin | Hin].
      + (* target is in the yes subtree, so the no subtree is untouched *)
        assert (Hnn : ~ In target (leaves no))
            by (intro H; pose proof (Hy target Hin); pose proof (Hn target H);
                congruence).
        (* q_new sifts toward the yes subtree as well *)
        assert (Hqe' : node_test q_new e' o' = true). {
            destruct (node_test q_new e' o') eqn:E; [reflexivity |].
            destruct Hnn.
            assert (sift no q_new = target) by (simpl in Hsift; now rewrite E in Hsift).
            rewrite <- H. apply sift_in_leaves. }
        assert (Hsy : sift yes q_new = target)
            by (simpl in Hsift; now rewrite Hqe' in Hsift).
        rewrite (split_leaf_id no target e q_new Hnn).
        repeat split; auto.
        * intros x Hx. apply split_leaves_fwd in Hx. destruct Hx as [-> | Hx].
            (* x = q_new : its e'-output equals o', since q_new sifts yes *)
            now apply node_test_true.
          now apply Hy.
      + (* symmetric: target is in the no subtree *)
        assert (Hny : ~ In target (leaves yes))
            by (intro H; pose proof (Hy target H); pose proof (Hn target Hin);
                congruence).
        assert (Hqe' : node_test q_new e' o' = false). {
            destruct (node_test q_new e' o') eqn:E; [| reflexivity].
            destruct Hny.
            assert (sift yes q_new = target) by (simpl in Hsift; now rewrite E in Hsift).
            rewrite <- H. apply sift_in_leaves. }
        assert (Hsn : sift no q_new = target)
            by (simpl in Hsift; now rewrite Hqe' in Hsift).
        rewrite (split_leaf_id yes target e q_new Hny).
        repeat split; auto.
        * intros x Hx. apply split_leaves_fwd in Hx. destruct Hx as [-> | Hx].
            now apply node_test_false.
          now apply Hn.
Qed.

(** Given a tree whose hypothesis mispredicts on a counterexample w, we can find
    a leaf [target] and a fresh discriminator e such that splitting [target] on
    e yields a still well-formed tree *)
Theorem find_split :
    forall (t : dtree) (w : str)
           (Heps : In nil (leaves t))
           (Hcons : consistent t)
           (HND : NoDup (leaves t))
           (Hce : output_string (make_moore t) w <> output_lang w),
    { target : str &
    { e : str &
    { q_new : str |
        In target (leaves t) /\
        ~ In q_new (leaves t) /\
        output_lang (target ++ e) <> output_lang (q_new ++ e) /\
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
        unfold pi, qk1, run, make_moore. rewrite Hfirstn, fold_left_app.
        reflexivity.
    }
    (* From correctness at k and incorrectness at (S k), the extension and the
       leaf it sifts to are told apart by the suffix e *)
    assert (Hgk : output_lang (qk1 ++ skipn (S k) w) = output_lang w). {
        unfold correct in Kcorrect.
        rewrite (skipn_S_wk _ _ _ _ Hwk) in Kcorrect.
        unfold qk1. now rewrite <- app_assoc.
    }
    assert (Hgk1 : output_lang (sift t qk1 ++ skipn (S k) w) <> output_lang w). {
        rewrite <- HSk. now unfold correct in SKincorrect.
    }
    pose proof (sift_in_leaves t qk1) as HinT.
    assert (Hfresh : ~ In qk1 (leaves t)). {
        intro Hin. apply Hgk1. now rewrite (Hcons qk1 Hin).
    }
    assert (Hdiff : output_lang (sift t qk1 ++ skipn (S k) w)
                  <> output_lang (qk1 ++ skipn (S k) w)) by now rewrite Hgk.
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

Lemma make_moore_minimal : forall t,
    wf t ->
    equiv_query (make_moore t) = None ->
    minimal (make_moore t).
Proof.
  intros t Hwf Heq.
  unfold minimal. split.
    now apply equiv_query_correct in Heq.
  intros state' m' H_encodes.
  assert (H_LHS : List.length (states _ (make_moore t)) = List.length (leaves t)). {
    unfold make_moore. simpl. apply list_with_proof_preserves_len. }
  rewrite H_LHS.
  pose proof (wf_separated _ Hwf) as Hsep.
  pose proof (wf_consistent _ Hwf) as Hcons.
  pose proof (wf_NoDup _ Hwf) as HND.
  set (f := fun q => M.run m' q).
  assert (Hinj : forall u v, In u (leaves t) -> In v (leaves t) ->
                 u <> v -> f u <> f v). {
    intros u v Hu Hv Huv Hf.
    destruct (Hsep u v Hu Hv Huv) as (e & He & Hdiff).
    apply Hdiff.
    assert (Hsplit : forall x,
              M.output_string m' (x ++ e)
              = m'.(M.output _) (fold_left m'.(M.transition _) e (f x)))
      by (intro x; unfold M.output_string, M.run, f; now rewrite fold_left_app).
    assert (Hout : M.output_string m' (u ++ e) = M.output_string m' (v ++ e))
      by (rewrite !Hsplit; unfold f in *; now rewrite Hf).
    (* m' encodes output_lang, so its outputs equal the target outputs *)
    rewrite <- (H_encodes (u ++ e)), <- (H_encodes (v ++ e)). assumption. }
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
  - (* every mapped state is a real state of m' *)
    intros st Hst. apply in_map_iff in Hst.
    destruct Hst as (q & <- & _). unfold f. apply M.run_in_states.
Qed.

Lemma le_min : forall t,
    wf t ->
    length (leaves t) <= num_states_in_minimal.
Proof.
  intro t. intro Hwf.
  destruct L.exists_moore as (state_m & Mm & [Menc Minimal] & Len).
  (* It suffices to bound leaves by Mm's state count *)
  enough (Hle : List.length (leaves t) <= List.length (M.states state_m Mm)) by lia.
  pose proof (wf_separated _ Hwf) as Hsep.
  pose proof (wf_NoDup _ Hwf) as HND.
  set (f := fun q => M.run Mm q).
  (* f is injective on the leaves *)
  assert (Hinj : forall u v, In u (leaves t) -> In v (leaves t) ->
                 u <> v -> f u <> f v). {
    intros u v Hu Hv Huv Hf.
    destruct (Hsep u v Hu Hv Huv) as (e & He & Hdiff).
    apply Hdiff.
    assert (Hsplit : forall x,
              M.output_string Mm (x ++ e)
              = Mm.(M.output _) (fold_left Mm.(M.transition _) e (f x)))
      by (intro x; unfold M.output_string, M.run, f; now rewrite fold_left_app).
    assert (Hout : M.output_string Mm (u ++ e) = M.output_string Mm (v ++ e))
      by (rewrite !Hsplit; unfold f in *; now rewrite Hf).
    rewrite <- (Menc (u ++ e)), <- (Menc (v ++ e)). assumption. }
  rewrite <- (length_map f (leaves t)).
  apply NoDup_incl_length.
  - clear - HND Hinj.
    induction (leaves t) as [| x xs IH]; [constructor|].
    apply NoDup_cons_iff in HND. destruct HND as [Hnin NDxs]. constructor.
    + intro HIn. apply in_map_iff in HIn. destruct HIn as (y & Hfy & Hyin).
      assert (x = y). { destruct (str_eq x y) as [e|n]. assumption.
        exfalso. apply (Hinj x y); [now left | now right | assumption | now symmetry]. }
      subst y; contradiction.
    + apply IH; auto. intros u v Hu Hv. apply Hinj; now right.
  - intros st Hst. apply in_map_iff in Hst.
    destruct Hst as (q & <- & _). unfold f. apply M.run_in_states.
Qed.

Lemma full_states_no_ce : forall (t : dtree),
    wf t ->
    L.num_states_in_minimal <= List.length (leaves t) ->
    equiv_query (make_moore t) = None.
Proof.
    intros t Hwf Contra.
    destruct (equiv_query (make_moore t)) eqn:Heq; [exfalso | reflexivity].
    assert (Hce : output_string (make_moore t) s <> output_lang s)
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

(** The main KV implementation. Adds one state per counterexample *)
Fixpoint kv_learn (fuel : nat) (t : dtree)
                  (LE : L.num_states_in_minimal - List.length (leaves t) <= fuel)
                  (Hwf : wf t)
    : { St : Type & {m : M.t St | minimal m} }.
    destruct (equiv_query (make_moore t)) eqn:Heq.
    - (* counterexample *)
        destruct fuel as [| n].
        -- assert (forall x y, x - y <= 0 -> x - y = 0) by lia. apply H in LE. clear H.
           apply Nat.sub_0_le, full_states_no_ce in LE; auto.
           rewrite Heq in LE. discriminate.
        -- assert (Hce : output_string (make_moore t) s <> output_lang s)
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
    - eexists. exists (make_moore t). apply (make_moore_minimal t Hwf Heq).
Defined.

(** The learner is seeded with a trivially well-formed tree *)
Definition mkv (_ : unit) : { St : Type & {m : M.t St | minimal m} } :=
    kv_learn num_states_in_minimal (Leaf nil) ltac:(lia) (conj I (or_introl eq_refl)).

End KV_Moore_Binary.
