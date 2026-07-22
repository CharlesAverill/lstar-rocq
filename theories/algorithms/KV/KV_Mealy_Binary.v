(** Kearns-Vazirani for Mealy machines using binary equality-test discrimination
    trees.
    Each internal node tests whether the target observation of a suffix
    [e] (an [option O.t], via [obs = M.tobs output_lang]) equals a stored value
    [o]. *)

From lstar Require Import automata.Mealy ListLemmas Teacher RS.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.

Module KV_Mealy_Binary (s : Symbol) (O : Output) (L : MealyLanguage s O) (Tch : MealyTeacher s O L).
Import s O L Tch M.

(** Observations derived from the target: [obs q t] is the last output emitted
    while reading [t] after having consumed [q], or [None] if [t] is empty. *)
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

Definition obs_eq_dec : forall (x y : option O.t), {x = y} + {x <> y}.
Proof.
    intros [x|] [y|].
    - destruct (O.eq_dec x y); [left; now subst | right; congruence].
    - right; congruence.
    - right; congruence.
    - left; reflexivity.
Defined.

(** A discrimination tree is a binary tree whose internal nodes hold a
    discriminator suffix [e] and a target observation [o : option O.t],
    branching on whether [obs u e] equals [o]; leaves hold an access string. *)
Inductive dtree : Type :=
| Leaf (access : str)
| Node (discrim : str) (o : option O.t) (yes no : dtree).

(** Test performed at an internal node: does [u] observe [o] on [e]? *)
Definition node_test (u e : str) (o : option O.t) : bool :=
    if obs_eq_dec (obs u e) o then true else false.

Lemma node_test_true : forall u e o,
    node_test u e o = true <-> obs u e = o.
Proof.
    intros u e o. unfold node_test. destruct (obs_eq_dec (obs u e) o).
    - split; auto.
    - split; [discriminate | intro; contradiction].
Qed.

Lemma node_test_false : forall u e o,
    node_test u e o = false <-> obs u e <> o.
Proof.
    intros u e o. unfold node_test. destruct (obs_eq_dec (obs u e) o).
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
               /\ obs u e <> obs v e.

(** A tree is _well-formed_ when each node's discriminator classifies the leaves
    of its two subtrees: every leaf below the [yes] branch observes [o] on [e],
    and every leaf below the [no] branch does not. *)
Fixpoint wf' (t : dtree) : Prop :=
    match t with
    | Leaf _ => True
    | Node e o yes no =>
        (forall q, In q (leaves yes) -> obs q e = o) /\
        (forall q, In q (leaves no)  -> obs q e <> o) /\
        wf' yes /\ wf' no
    end.
Definition wf t := wf' t /\ In nil (leaves t).

Definition mem := mem str_eq.

Lemma sift_mem : forall t u, mem (sift t u) (leaves t) = true.
Proof. intros. apply mem_In, sift_in_leaves. Qed.

Definition make_mealy (t : dtree) : M.t { q | mem q (leaves t) = true }.
    set (state := { q | mem q (leaves t) = true }).
    assert (initial : state). {
        exists (sift t nil). apply sift_mem. }
    assert (transition : state -> s.t -> state). {
        intros q a. exists (sift t (proj1_sig q ++ [a])). apply sift_mem. }
    set (output := fun (q : state) (a : s.t) => output_lang (proj1_sig q) a).
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

(** Set up Shahbaz-Groz counterexample analysis *)
Module RSS <: MealySG_Setup s O L.
  Definition obt := { t : dtree | wf t }.
  Definition P (o : obt) (q : str) : Prop := mem q (leaves (proj1_sig o)) = true.
  Definition make_mealy (o : obt) : M.t { q | P o q } := make_mealy (proj1_sig o).

  Lemma eps_in_H : forall (o : obt),
      proj1_sig (make_mealy o).(initial _) = [].
  Proof.
    intros (t & Hwf). unfold make_mealy, KV_Mealy_Binary.make_mealy. simpl.
    apply (wf_consistent t Hwf). now destruct Hwf.
  Qed.

  Lemma out_correct : forall (o : obt) q a,
      output _ (make_mealy o) q a = output_lang (proj1_sig q) a.
  Proof.
    intros (t & Hwf) q a. unfold make_mealy, KV_Mealy_Binary.make_mealy. reflexivity.
  Qed.

  Definition obs : str -> str -> option O.t := obs.

  Lemma prediction_is_obs_at_access : forall H w' a,
      mobs (make_mealy H) (make_mealy H).(initial _) (w' ++ a :: nil)
        = obs (proj1_sig (run (make_mealy H) w')) (a :: nil).
  Proof.
    intros H w' a. rewrite M.mobs_snoc.
    rewrite out_correct. unfold obs, KV_Mealy_Binary.obs. rewrite obs_single. reflexivity.
  Qed.
End RSS.

Module SG := MealySG s O L RSS.
Import SG.

Fixpoint split_leaf (t : dtree) (target e q_new : str) : dtree :=
    match t with
    | Leaf q =>
        if str_eq q target
        then Node e (obs q e) (Leaf q) (Leaf q_new)
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
    induction t0 as [q | e o yes IHyes no IHno]; intros HND Hcons; [exact I |].
    simpl in HND.
    pose proof (NoDup_app_l _ _ HND) as NDy.
    pose proof (NoDup_app_r _ _ HND) as NDn.
    assert (Hdisj : forall x, In x (leaves yes) -> ~ In x (leaves no))
        by now apply NoDup_app_disj.
    (* the yes subtree's leaves observe o on e *)
    assert (Hy : forall q, In q (leaves yes) -> obs q e = o). {
        intros q Hq. destruct (node_test q e o) eqn:E.
          now apply node_test_true.
        exfalso.
        assert (Hsc : sift (Node e o yes no) q = q)
            by (apply Hcons; simpl; apply in_or_app; now left).
        simpl in Hsc. rewrite E in Hsc.
        apply (Hdisj q Hq). rewrite <- Hsc. apply sift_in_leaves. }
    (* the no subtree's leaves do not observe o on e *)
    assert (Hn : forall q, In q (leaves no) -> obs q e <> o). {
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
    obs target e <> obs q_new e ->
    wf' (split_leaf t target e q_new).
Proof.
    induction t0 as [q | e' o' yes IHyes no IHno];
        intros target e q_new Hwf HinT Hfresh Hsift Hdiff.
    - simpl in HinT. destruct HinT as [Hq | []]. subst target.
      simpl. destruct (str_eq q q) as [_ | Hneq]; [| now destruct (Hneq eq_refl)].
      (* the new node tests obs q e: q lands yes, q_new lands no *)
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
            (* x = q_new : its observation on e' equals o', since q_new sifts yes *)
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
            (* x = q_new : its observation on e' differs from o', since q_new sifts no *)
            now apply node_test_false.
          now apply Hn.
Qed.

(** Given a tree whose hypothesis mispredicts on a counterexample [w], find a
    leaf [target] and a fresh non-empty discriminator [e] such that splitting
    [target] on [e] yields a still well-formed tree. *)
Theorem find_split :
    forall (t : dtree) (w : str)
           (Heps : In nil (leaves t))
           (Hcons : consistent t)
           (HND : NoDup (leaves t))
           (Hce : mobs (make_mealy t) (make_mealy t).(initial _) w <> obs nil w),
    { target : str &
    { e : str &
    { q_new : str |
        In target (leaves t) /\
        ~ In q_new (leaves t) /\
        obs target e <> obs q_new e /\
        let t' := split_leaf t target e q_new in
        wf t' }}}.
Proof.
    intros t. intros.
    assert (Hwf : wf t) by (split; [ now apply consistent_NoDup_wf' | easy ]).
    set (o := exist wf t Hwf : RSS.obt).
    assert (Hce' : mobs (RSS.make_mealy o) (RSS.make_mealy o).(initial _) w
                   <> obs nil w) by exact Hce.
    (* The counterexample is non-empty: peel its last symbol. *)
    assert (Hne : w <> nil). {
      intro Hw. subst w. apply Hce. reflexivity. }
    destruct (exists_last Hne) as (w' & a & Hw). subst w.
    (* Shahbaz-Groz search: a flip strictly inside w'. *)
    destruct (sg_partition_binary o w' a Hce')
        as (k & KCorrect & SKincorrect & Hlt).
    (* The two adjacent reconstructions differ. *)
    assert (Dist : sg o w' a k <> sg o w' a (S k)). {
      unfold correct in KCorrect, SKincorrect.
      rewrite KCorrect. intro Hbad. apply SKincorrect. now rewrite <- Hbad.
    }
    (* Name the k-th symbol of w' and split skipn k w'. *)
    assert {wk | nth_error w' k = Some wk} as (wk & Hwk). {
      destruct (nth_error w' k) eqn:E.
        now exists t0.
      rewrite nth_error_None in E. lia.
    }
    pose proof (skipn_S_wk _ w' k wk Hwk) as Hskipn.
    set (e := skipn (S k) w' ++ [a]).
    assert (Htne : e <> nil). {
      unfold e. intro Hbad.
      now apply app_eq_nil in Hbad as (_ & Hcontra). }
    destruct (nth_error_split_sig _ _ _ Hwk) as (l1 & l2 & Hw' & Hlen).
    assert (Hfirstn : firstn (S k) w' = firstn k w' ++ [wk]). {
        subst.
        now rewrite firstn_app, Nat.sub_succ_l, firstn_all2, firstn_cons,
                    Nat.sub_diag, firstn_0, firstn_len_app by lia.
    }
    set (qk1 := pi o w' k ++ [wk]).
    (* One step of the hypothesis advances from p_k to the leaf [qk1] sifts to *)
    assert (HSk : pi o w' (S k) = sift t qk1). {
        unfold pi, qk1, run, RSS.make_mealy, make_mealy. rewrite Hfirstn, fold_left_app.
        reflexivity.
    }
    (* From correctness at k and incorrectness at (S k), the extension and the
       leaf it sifts to are told apart by the suffix e *)
    assert (DistQ : obs qk1 e <> obs (sift t qk1) e). {
      rewrite <- HSk. intro Hbad. apply Dist. unfold sg.
      rewrite Hskipn. fold e.
      change ((wk :: skipn (S k) w') ++ [a]) with (wk :: e).
      unfold RSS.obs. rewrite (obs_shift (pi o w' k) wk e Htne).
      fold qk1. exact Hbad.
    }
    exists (sift t qk1), e, qk1.
    pose proof (sift_in_leaves t qk1) as HinT.
    assert (Hfresh : ~ In qk1 (leaves t)). {
        intro Hin. rewrite (Hcons qk1 Hin) in DistQ. now apply DistQ.
    }
    assert (Hdiff : obs (sift t qk1) e <> obs qk1 e) by (intro C; apply DistQ; now rewrite C).
    assert (Hwf' : wf' t) by (now apply consistent_NoDup_wf').
    assert (Hwf'' : wf' (split_leaf t (sift t qk1) e qk1))
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

Lemma make_mealy_minimal : forall t,
    wf t ->
    equiv_query (make_mealy t) = None ->
    minimal (make_mealy t).
Proof.
  intros t Hwf Heq.
  unfold minimal. split.
    now apply equiv_query_correct in Heq.
  intros state' m' H_encodes0.
  pose proof (proj1 (encodes_obs m') H_encodes0) as H_encodes.
  assert (H_LHS : List.length (states _ (make_mealy t)) = List.length (leaves t)). {
    unfold make_mealy. simpl. apply list_with_proof_preserves_len. }
  rewrite H_LHS.
  pose proof (wf_separated _ Hwf) as Hsep.
  pose proof (wf_NoDup _ Hwf) as HND.
  set (f := fun q => M.run m' q).
  assert (Hinj : forall u v, In u (leaves t) -> In v (leaves t) ->
                 u <> v -> f u <> f v). {
    intros u v Hu Hv Huv Hf.
    destruct (Hsep u v Hu Hv Huv) as (e & He & Hdiff).
    apply Hdiff.
    destruct e as [| a w]; [now rewrite !obs_nil |].
    rewrite (obs_prefix u a w), (obs_prefix v a w).
    rewrite <- (H_encodes (u ++ a :: w)), <- (H_encodes (v ++ a :: w)).
    rewrite (M.mobs_prefix m' u a w), (M.mobs_prefix m' v a w).
    unfold f in Hf. now rewrite Hf. }
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
    destruct Hst as (q & <- & _). unfold f. apply M.run_in_states.
Qed.

Lemma le_min : forall t,
    wf t ->
    length (leaves t) <= num_states_in_minimal.
Proof.
  intro t. intro Hwf.
  destruct L.exists_mealy as (state_m & Mm & (Menc0 & Minimal) & Len).
  rewrite encodes_obs in Menc0. rename Menc0 into Menc.
  enough (Hle : List.length (leaves t) <= List.length (M.states state_m Mm)) by lia.
  pose proof (wf_separated _ Hwf) as Hsep.
  pose proof (wf_NoDup _ Hwf) as HND.
  set (f := fun q => M.run Mm q).
  assert (Hinj : forall u v, In u (leaves t) -> In v (leaves t) ->
                 u <> v -> f u <> f v). {
    intros u v Hu Hv Huv Hf.
    destruct (Hsep u v Hu Hv Huv) as (e & He & Hdiff).
    apply Hdiff.
    destruct e as [| a w]; [now rewrite !obs_nil |].
    rewrite (obs_prefix u a w), (obs_prefix v a w).
    rewrite <- (Menc (u ++ a :: w)), <- (Menc (v ++ a :: w)).
    rewrite (M.mobs_prefix Mm u a w), (M.mobs_prefix Mm v a w).
    unfold f in Hf. now rewrite Hf. }
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
    destruct Hst as (q & <- & _). unfold f. apply M.run_in_states.
Qed.

Lemma full_states_no_ce : forall (t : dtree),
    wf t ->
    L.num_states_in_minimal <= List.length (leaves t) ->
    equiv_query (make_mealy t) = None.
Proof.
    intros t Hwf Contra.
    destruct (equiv_query (make_mealy t)) eqn:Heq; [exfalso | reflexivity].
    assert (Hce : mobs (make_mealy t) (make_mealy t).(initial _) s <> obs nil s)
        by (unfold obs; now apply equiv_query_ce).
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
    destruct (equiv_query (make_mealy t)) eqn:Heq.
    - (* counterexample *)
        destruct fuel as [| n].
        -- assert (forall x y, x - y <= 0 -> x - y = 0) by lia. apply H in LE. clear H.
           apply Nat.sub_0_le, full_states_no_ce in LE; auto.
           rewrite Heq in LE. discriminate.
        -- assert (Hce : mobs (make_mealy t) (make_mealy t).(initial _) s <> obs nil s)
                by (unfold obs; now apply equiv_query_ce).
            pose proof Hwf as Hwf'.
            destruct Hwf' as (Hwf' & Heps).
            destruct (find_split t s Heps (wf_consistent t Hwf) (wf_NoDup t Hwf) Hce)
                as (target & e & q_new & HinT & Hfresh & Hdiff & Hwf'' & Heps').
            enough (num_states_in_minimal - List.length (leaves (split_leaf t target e q_new)) <= n).
            eapply (kv_learn n (split_leaf t target e q_new) H (conj Hwf'' Heps')).
            pose proof (split_leaf_count t target e q_new
                          (wf_NoDup t Hwf) HinT Hfresh) as Hcount.
            rewrite Hcount. lia.
    - eexists. exists (make_mealy t). apply (make_mealy_minimal t Hwf Heq).
Defined.

(** The learner is seeded with a trivially well-formed tree *)
Definition mkv (_ : unit) : { St : Type & {m : M.t St | minimal m} } :=
    kv_learn num_states_in_minimal (Leaf nil) ltac:(lia) (conj I (or_introl eq_refl)).

End KV_Mealy_Binary.
