(** Kearns-Vazirani for Moore machines using n-ary trees (incomplete) *)

From lstar Require Import automata.Moore ListLemmas Teacher RS.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.

Module KV (s : Symbol) (O : Output) (L : MooreLanguage s O) (Tch : MooreTeacher s O L).
Import s L Tch M.

(** A discrimination tree is an n-ary tree whose internal nodes hold a
    discriminator suffix and whose leaves hold an access string *)
Inductive dtree : Type :=
| Leaf (access : str)
| Node (discrim : str) (trees : list (O.t * dtree)).

Theorem dtree_ind_l : forall (P : dtree -> Prop)
    (Base: forall access, P (Leaf access))
    (Ind: forall discrim trees, Forall P (map snd trees) -> P (Node discrim trees)),
    forall (t : dtree), P t.
Proof.
    intros P Base Ind.
    fix IH 1. destruct t0.
        apply Base.
    apply Ind. induction trees.
        constructor.
    simpl. constructor.
        apply IH.
        apply IHtrees.
Qed.

Ltac tind :=
    let a := fresh "access" in
    let e := fresh "e" in
    let trees := fresh "trees" in
    let IH := fresh "IH" in
    lazymatch goal with
    | [|- forall (x : dtree), _] =>
        let x' := fresh x in
        intro x';
        induction x' as [a | e trees IH] using dtree_ind_l
    | [x : dtree |- _] => induction x as [a | e trees IH] using dtree_ind_l
    end.

Inductive dtree_children_wf : dtree -> Prop :=
| DCWLeaf a : dtree_children_wf (Leaf a)
| DCWNode d trees :
    length trees <= length O.enum ->
    (forall o, In o (map fst trees)) ->
    Forall dtree_children_wf (map snd trees) ->
    NoDup (map fst trees) ->
    dtree_children_wf (Node d trees).

Definition matching_subtree (trees : list (O.t * dtree)) (o : O.t) : option dtree :=
    match List.find (fun '(x, _) => if O.eq_dec o x then true else false) trees with
    | None => None
    | Some (_, t) => Some t
    end.

(** Sifting classifies a string u by descending the tree until it reaches
    the appropriate access node *)
Fixpoint sift (t : dtree) (u : str) (n : nat) : option str :=
    match n with
    | O => None
    | S n' =>
        match t with
        | Leaf q => Some q
        | Node e trees =>
            match matching_subtree trees (output_lang (u ++ e)) with
            | None => None
            | Some t' => sift t' u n'
            end
        end
    end.

Fixpoint height (t : dtree) : nat :=
    match t with
    | Leaf _ => 1
    | Node _ trees => S (List.fold_left (fun a i => if a <=? i then i else a) (List.map (fun '(_, t) => height t) trees) 0)
    end.

Lemma sift_monotone : forall n t u m s,
    n <= m ->
    sift t u n = Some s ->
    sift t u m = Some s.
Proof.
    induction n as [|n' IHn]; intros t u m s Hle Hmp.
    - inversion Hmp.
    - destruct m as [|m']; [lia|].
      destruct t; simpl in *; [exact Hmp|].
      destruct matching_subtree; [|inversion Hmp].
      eapply IHn. lia. assumption.
Qed.

Lemma fold_max_le : forall l x,
    In x l ->
    x <= fold_left (fun a i => if a <=? i then i else a) l 0.
Proof.
    intros l.
    assert (Hgen : forall x acc, In x l \/ x <= acc -> 
        x <= fold_left (fun a i => if a <=? i then i else a) l acc).
    { induction l as [|h t IH]; intros x acc H; simpl in *.
      - destruct H; [contradiction | exact H].
      - apply IH. destruct (acc <=? h) eqn:E.
        + apply Nat.leb_le in E. destruct H as [[Heq | Hin] | Hle].
          * subst. right. lia.
          * left. exact Hin.
          * right. lia.
        + apply Nat.leb_gt in E. destruct H as [[Heq | Hin] | Hle].
          * subst. right. lia.
          * left. exact Hin.
          * right. lia. }
    intros x Hin. apply Hgen. now left.
Qed.

Lemma matching_subtree_In : forall trees o d,
    matching_subtree trees o = Some d ->
    In d (map snd trees).
Proof.
    unfold matching_subtree; intros trees o d.
    induction trees as [| [x t] ts IH]; simpl; [discriminate|].
    destruct (O.eq_dec o x); intros H.
    - inversion H; subst; now left.
    - right. exact (IH H).
Qed.

Lemma map_snd_height_eq : forall (trees : list (O.t * dtree)),
  map height (map snd trees) = map (fun '(_, t0) => height t0) trees.
Proof.
  induction trees as [| [o t'] ts IHts]; simpl; [reflexivity | now rewrite IHts].
Qed.

(** When the sought output labels a child, [matching_subtree] finds one. *)
Lemma matching_subtree_Some : forall trees o,
    In o (map fst trees) ->
    exists d, matching_subtree trees o = Some d.
Proof.
    unfold matching_subtree; intros trees o.
    induction trees as [| [x t] ts IH]; simpl; [contradiction|].
    destruct (O.eq_dec o x) as [Heq | Hne]; intros Hin.
    - now exists t.
    - destruct Hin as [Heq | Hin]; [now subst x; contradiction|].
      destruct (IH Hin) as (d & Hd).
      destruct (List.find (fun '(x0, _) =>
          if O.eq_dec o x0 then true else false) ts) as [[x' t']|] eqn:Ef.
      + inversion Hd; subst. now exists d.
      + discriminate Hd.
Qed.

(** Informative version: when the sought output labels a child, we can compute
    the subtree it points to. Used to build the witness in the [sig]-valued
    [sift_fuel]. *)
Lemma matching_subtree_sig : forall trees o,
    In o (map fst trees) ->
    {d | matching_subtree trees o = Some d}.
Proof.
    intros trees o Hin.
    destruct (matching_subtree trees o) as [d|] eqn:E.
    - exact (exist _ d eq_refl).
    - exfalso. destruct (matching_subtree_Some trees o Hin) as (d & Hd).
      rewrite E in Hd. discriminate.
Defined.

(** [Prop]-valued projections of [dtree_children_wf] at a node, so [sift_fuel]
    can consult them without [inversion] (whose sort-elimination is blocked in a
    [sig] goal). *)
Lemma dcw_cover : forall d trees,
    dtree_children_wf (Node d trees) -> forall o, In o (map fst trees).
Proof. intros d trees H. now inversion H. Qed.

Lemma dcw_forall : forall d trees,
    dtree_children_wf (Node d trees) -> Forall dtree_children_wf (map snd trees).
Proof. intros d trees H. now inversion H. Qed.

Lemma dcw_child : forall d trees o t',
    dtree_children_wf (Node d trees) -> In (o, t') trees -> dtree_children_wf t'.
Proof.
    intros d trees o t' H Hin. apply dcw_forall in H.
    rewrite Forall_forall in H. apply H, (in_map snd _ _ Hin).
Qed.

(** With enough fuel ([height t]), sifting a coverage-complete tree reaches a
    leaf. *)
Lemma sift_fuel_ex :
    forall t u,
    dtree_children_wf t ->
    exists s, sift t u (height t) = Some s.
Proof.
    tind; intros u Hwf; simpl in *.
        now exists access.
    inversion Hwf as [| d0 trees0 Hlen Hcov Hforall Hnodup]; subst.
    destruct (matching_subtree_Some trees (output_lang (u ++ e))
                (Hcov (output_lang (u ++ e)))) as (d & E).
    rewrite E.
    assert (Hin : In d (map snd trees)) by (eauto using matching_subtree_In).
    assert (Hd_wf : dtree_children_wf d)
        by (rewrite Forall_forall in Hforall; now apply Hforall).
    rewrite Forall_forall in IH.
    destruct (IH d Hin u Hd_wf) as (s & Hs).
    exists s.
    eapply sift_monotone; [| exact Hs].
    apply fold_max_le.
    rewrite <- map_snd_height_eq. apply in_map. exact Hin.
Qed.

(** Informative extractor: since [sift t u (height t)] is a concrete [option],
    we produce the [sig] by matching on it, discharging the [None] case with
    [sift_fuel_ex]. No custom [Type]-valued eliminator is needed. *)
Lemma sift_fuel :
    forall t u,
    dtree_children_wf t ->
    {s | sift t u (height t) = Some s}.
Proof.
    intros t u Hwf.
    destruct (sift t u (height t)) as [s|] eqn:E.
    - exact (exist _ s eq_refl).
    - exfalso. destruct (sift_fuel_ex t u Hwf) as (s & Hs).
      rewrite E in Hs. discriminate.
Defined.

(** The access strings held at a tree's leaves *)
Fixpoint leaves (t : dtree) : list str :=
    match t with
    | Leaf q => [q]
    | Node _ trees =>
        (fix leaves_list (l : list (O.t * dtree)) : list str :=
           match l with
           | nil => nil
           | (_, t') :: tl => leaves t' ++ leaves_list tl
           end) trees
    end.

(** The discriminator suffixes appearing at a tree's internal nodes *)
Fixpoint discriminators (t : dtree) : list str :=
    match t with
    | Leaf _ => nil
    | Node e trees =>
        e :: (fix d_list (l : list (O.t * dtree)) : list str :=
                match l with
                | nil => nil
                | (_, t') :: tl => discriminators t' ++ d_list tl
                end) trees
    end.

(** Normal forms: leaves and discriminators as [flat_map]s over the children,
    convenient for reasoning without unfolding the internal fixpoints. *)
Lemma leaves_node : forall e trees,
    leaves (Node e trees) = flat_map (fun p => leaves (snd p)) trees.
Proof.
    intros e trees. simpl.
    induction trees as [| (a, ta) tl IH]; simpl; [reflexivity | now rewrite IH].
Qed.

Lemma discriminators_node : forall e trees,
    discriminators (Node e trees)
    = e :: flat_map (fun p => discriminators (snd p)) trees.
Proof.
    intros e trees. simpl. f_equal.
    induction trees as [| (a, ta) tl IH]; simpl; [reflexivity | now rewrite IH].
Qed.

(** Membership in a node's leaves factors through some child. *)
Lemma in_leaves_node : forall e trees x,
    In x (leaves (Node e trees)) <->
    exists o t', In (o, t') trees /\ In x (leaves t').
Proof.
    intros e trees x. rewrite leaves_node. split.
    - intro Hx. apply in_flat_map in Hx.
      destruct Hx as ((o, t') & Hin & Hxt'). exists o, t'. split; assumption.
    - intros (o & t' & Hin & Hxt'). apply in_flat_map.
      exists (o, t'). split; assumption.
Qed.

(** Whatever [sift] returns is a leaf of the tree. *)
Lemma sift_in_leaves : forall n t u q,
    sift t u n = Some q -> In q (leaves t).
Proof.
    induction n as [| n' IHn]; intros t u q Hs; [discriminate |].
    destruct t as [a | e trees]; simpl in Hs.
    - injection Hs as <-. now left.
    - destruct (matching_subtree trees (output_lang (u ++ e))) as [t'|] eqn:E;
        [| discriminate].
      apply matching_subtree_In in E.
      apply in_map_iff in E. destruct E as ((o, td) & Heq & Hin). simpl in Heq. subst td.
      apply in_leaves_node. exists o, t'. split; [exact Hin | eapply IHn; exact Hs].
Qed.

(** Tree invariants *)

(** A tree is _consistent_ when every access string sifts to its own leaf.
    Fuel is fixed at [height t], which [sift_fuel] shows always suffices. *)
Definition consistent (t : dtree) : Prop :=
    forall q, In q (leaves t) -> sift t q (height t) = Some q.

(** A tree is _separated_ when any two distinct leaves are told apart by some
    discriminator of the tree: they produce different outputs on it. *)
Definition separated (t : dtree) : Prop :=
    forall u v,
        In u (leaves t) -> In v (leaves t) -> u <> v ->
        exists e, In e (discriminators t)
               /\ output_lang (u ++ e) <> output_lang (v ++ e).

(** A tree is _well-formed_ when each internal node's discriminator [e] labels
    its children: a leaf [q] under the child keyed by output [o] satisfies
    [output_lang (q ++ e) = o]. Coverage in [dtree_children_wf] guarantees every
    output has a child, so no default branch is needed. Each subtree is itself
    well-formed. *)
Fixpoint wf' (t : dtree) : Prop :=
    match t with
    | Leaf _ => True
    | Node e trees =>
        (fix wf_list (l : list (O.t * dtree)) : Prop :=
           match l with
           | nil => True
           | (o, t') :: tl =>
               (forall q, In q (leaves t') -> output_lang (q ++ e) = o)
               /\ wf' t' /\ wf_list tl
           end) trees
    end.
(** A tree is well-formed when it is semantically well-formed ([wf']), its
    children cover all outputs and are structurally sound ([dtree_children_wf],
    which makes [sift] total), and it contains the empty access string. *)
Definition wf t := wf' t /\ dtree_children_wf t /\ In nil (leaves t).

(** The nested fixpoint in [wf'] is equivalent to quantifying over the children:
    every child labels its leaves correctly and is itself well-formed. This is
    the form downstream proofs use, so they never unfold the internal fix. *)
Lemma wf'_node : forall e trees,
    wf' (Node e trees) <->
    (forall o t', In (o, t') trees ->
        (forall q, In q (leaves t') -> output_lang (q ++ e) = o) /\ wf' t').
Proof.
    intros e trees. simpl. split.
    - induction trees as [| (a, ta) tl IH]; simpl; [contradiction |].
      intros (Hlab & Hwfa & Htl) o t' [Heq | Hin].
      + inversion Heq; subst. split; assumption.
      + apply IH; assumption.
    - induction trees as [| (a, ta) tl IH]; simpl; [trivial |].
      intro Hall. split; [| split].
      + intros q Hq. now apply (Hall a ta (or_introl eq_refl)).
      + now apply (Hall a ta (or_introl eq_refl)).
      + apply IH. intros o t' Hin. apply Hall. now right.
Qed.

Definition mem := mem str_eq.

(** With enough fuel, sifting reaches a leaf that is a member of [leaves t]. *)
Lemma sift_mem : forall t u, dtree_children_wf t ->
    exists q, sift t u (height t) = Some q /\ mem q (leaves t) = true.
Proof.
    intros t u Hwf. destruct (sift_fuel t u Hwf) as (q & Hq).
    exists q. split; [assumption |]. apply mem_In. eapply sift_in_leaves; exact Hq.
Qed.

(** A single sift step at a node: descend into the child selected by
    [output_lang (u ++ e)], with monotone fuel. *)
Lemma sift_step_child : forall e trees u t' q n,
    matching_subtree trees (output_lang (u ++ e)) = Some t' ->
    sift t' u n = Some q ->
    sift (Node e trees) u (S n) = Some q.
Proof.
    intros e trees u t' q n Hmatch Hs. simpl. rewrite Hmatch. exact Hs.
Qed.

(** A transparent extractor for the sifted leaf, carrying the defining equation
    so downstream proofs (e.g. [eps_in_H]) can reason about the access string. *)
Definition sift_val (t : dtree) (u : str) (Ht : dtree_children_wf t)
    : { q | sift t u (height t) = Some q } :=
    let (q, Hq) := sift_fuel t u Ht in exist _ q Hq.

Lemma sift_val_in_leaves : forall t u Ht,
    In (proj1_sig (sift_val t u Ht)) (leaves t).
Proof.
    intros t u Ht. destruct (sift_val t u Ht) as (q & Hq); simpl.
    eapply sift_in_leaves; exact Hq.
Qed.

(** Build a Moore machine from a discrimination tree. States are the tree's
    leaves; the machine outputs each leaf's target output and transitions by
    sifting the extended access string. [dtree_children_wf] guarantees sifting
    always reaches a leaf. *)
Definition make_moore (t : dtree) (Ht : dtree_children_wf t)
    : M.t { q | mem q (leaves t) = true }.
    set (state := { q | mem q (leaves t) = true }).
    set (siftpkg := fun u =>
        exist (fun q => mem q (leaves t) = true)
              (proj1_sig (sift_val t u Ht))
              (proj2 (mem_In str_eq _ _) (sift_val_in_leaves t u Ht)) : state).
    set (initial := siftpkg nil).
    set (transition := fun (q : state) (a : s.t) => siftpkg (proj1_sig q ++ [a])).
    set (output := fun (q : state) => output_lang (proj1_sig q)).
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

(** Explicit-branch leaves are pairwise disjoint: each leaf's [e]-output equals
    its own child key, and keys are distinct. *)
Lemma children_leaves_NoDup : forall e trees,
    NoDup (map fst trees) ->
    (forall o t', In (o, t') trees ->
        (forall q, In q (leaves t') -> output_lang (q ++ e) = o)) ->
    (forall o t', In (o, t') trees -> NoDup (leaves t')) ->
    NoDup (flat_map (fun p => leaves (snd p)) trees).
Proof.
    intros e trees.
    induction trees as [| (b, tb) tl IH]; intros Hkeys Hlab Hsub; simpl; [constructor |].
    apply NoDup_app_intro.
    - apply (Hsub b tb (or_introl eq_refl)).
    - apply IH.
      + now inversion Hkeys.
      + intros o t' Hin; apply (Hlab o t' (or_intror Hin)).
      + intros o t' Hin; apply (Hsub o t' (or_intror Hin)).
    - intros x Hx Hxrest.
      apply in_flat_map in Hxrest. destruct Hxrest as ((o, t') & Hin' & Hxt'). simpl in Hxt'.
      pose proof (Hlab b tb (or_introl eq_refl) x Hx) as Hb.
      pose proof (Hlab o t' (or_intror Hin') x Hxt') as Ho.
      assert (b = o) by (rewrite <- Hb, <- Ho; reflexivity). subst o.
      inversion Hkeys as [| ? ? Hnin ?]. apply Hnin.
      apply in_map_iff. exists (b, t'). split. reflexivity.
      subst. assumption.
Qed.

Lemma wf_NoDup : forall t, wf t -> NoDup (leaves t).
Proof.
    intros t (Hwf & Hchild & _). revert Hwf Hchild.
    tind; intros.
        simpl. constructor; [intuition | constructor].
    rewrite leaves_node.
    pose proof (proj1 (wf'_node e trees) Hwf).
    inversion Hchild as [| d0 trees0 Hlen Hcov Hforall Hkeys]; subst.
    apply (children_leaves_NoDup e trees).
    - exact Hkeys.
    - intros. specialize (H _ _ H0). destruct H. now apply H.
    - intros o t' Hin.
      rewrite Forall_forall in IH, Hforall.
      apply (IH t' (in_map snd _ _ Hin)).
        now apply (H o t' Hin).
      apply Hforall. change t' with (snd (o, t')). now apply in_map.
Qed.

(** In a well-formed, well-childed tree, sifting a leaf returns that same leaf:
    the descent follows the leaf's own labelled child at every level. *)
Lemma sift_leaf_unique : forall t,
    wf' t -> dtree_children_wf t ->
    forall q0, In q0 (leaves t) ->
    forall q n, sift t q0 n = Some q -> q = q0.
Proof.
    intro t. tind;
        intros Hwf Hchild q0 Hin q n Hq.
    - simpl in Hin. destruct Hin as [-> | []].
      destruct n; simpl in Hq; [discriminate | injection Hq as <-; reflexivity].
    - pose proof (proj1 (wf'_node e trees) Hwf).
      inversion Hchild as [| d0 trees0 Hlen Hcov Hforall Hkeys]; subst.
      rewrite leaves_node in Hin. apply in_flat_map in Hin.
      destruct Hin as ((o0, t0) & Hbin & Hq0t0). simpl in Hq0t0.
      pose proof (H o0 t0 Hbin) as (Hlab0 & Hwf0).
      pose proof (Hlab0 q0 Hq0t0) as Hsel.
      assert (Hms : matching_subtree trees (output_lang (q0 ++ e)) = Some t0). {
        rewrite Hsel. clear -Hkeys Hbin.
        unfold matching_subtree.
        induction trees as [| (b, tb) tl IHl]; simpl in *; [contradiction |].
        inversion Hkeys as [| ? ? Hnin NDtl]; subst.
        destruct Hbin as [Heq | Hbin].
          inversion Heq; subst. now destruct (O.eq_dec o0 o0); [| contradiction].
        destruct (O.eq_dec o0 b) as [-> | Hne].
          exfalso. apply Hnin. apply in_map_iff. exists (b, t0); auto.
        now apply IHl. }
      destruct n as [| n']; simpl in Hq; [discriminate |].
      rewrite Hms in Hq.
      rewrite Forall_forall in IH, Hforall.
      apply (IH t0 (in_map snd _ _ Hbin) Hwf0 (Hforall _ (in_map snd _ _ Hbin))
                 q0 Hq0t0 q n' Hq).
Qed.

Lemma wf_consistent : forall t, wf t -> consistent t.
Proof.
    intros t (Hwf & Hchild & _) q0 Hin.
    destruct (sift_fuel t q0 Hchild) as (q & Hq).
    rewrite (sift_leaf_unique t Hwf Hchild q0 Hin q (height t) Hq) in Hq. exact Hq.
Qed.

Lemma wf_separated : forall t, wf t -> separated t.
Proof.
    intros t (Hwf & Hchild & _). revert Hwf Hchild.
    tind; intros Hwf Hchild u v Hu Hv Huv.
        simpl in Hu, Hv. destruct Hu as [-> | []], Hv as [-> | []]. now elim Huv.
    pose proof (proj1 (wf'_node e trees) Hwf).
    inversion Hchild as [| d0 trees0 Hlen Hcov Hforall Hkeys]; subst.
    rewrite leaves_node in Hu, Hv.
    apply in_flat_map in Hu. destruct Hu as ((ou, tu) & Hbu & Hutu). simpl in Hutu.
    apply in_flat_map in Hv. destruct Hv as ((ov, tv) & Hbv & Hvtv). simpl in Hvtv.
    pose proof (H ou tu Hbu) as (Hlabu & Hwfu).
    pose proof (H ov tv Hbv) as (Hlabv & Hwfv).
    pose proof (Hlabu u Hutu) as Hou.
    pose proof (Hlabv v Hvtv) as Hov.
    destruct (O.eq_dec ou ov) as [Hkeq | Hkne].
    - subst ov.
      assert (tu = tv). {
        clear - Hkeq Hkeys Hbu Hbv.
        induction trees as [| (b, tb) tl IHl]; simpl in *; [contradiction |].
        inversion Hkeys as [| ? ? Hnin NDtl]; subst.
        destruct Hbu as [Heu | Hbu], Hbv as [Hev | Hbv].
        - inversion Heu; inversion Hev; congruence.
        - inversion Heu; subst. exfalso. apply Hnin. apply in_map_iff.
          exists (output_lang (v ++ e), tv); auto.
        - inversion Hev; subst. exfalso. apply Hnin. apply in_map_iff.
          exists (output_lang (v ++ e), tu); auto.
        - now apply IHl. }
      subst tv.
      rewrite Forall_forall in IH, Hforall.
      destruct (IH tu (in_map snd _ _ Hbu) Hwfu (Hforall _ (in_map snd _ _ Hbu))
                   u v Hutu Hvtv Huv) as (d & Hd & Hdiff).
      exists d. split; [| assumption].
      rewrite discriminators_node. right. apply in_flat_map. exists (ou, tu); auto.
    - exists e. split; [rewrite discriminators_node; now left |].
      rewrite Hou, Hov. assumption.
Qed.

(** Set up Rivest-Schapire counterexample analysis for Moore machines *)
Module RSS <: MooreRS_Setup s O L.
  Definition obt := { t : dtree | wf t }.
  Definition P (o : obt) (q : str) : Prop := mem q (leaves (proj1_sig o)) = true.
  Definition make_moore (o : obt) : M.t { q | P o q } :=
    make_moore (proj1_sig o) (proj1 (proj2 (proj2_sig o))).

  Lemma eps_in_H : forall (o : obt),
      proj1_sig (make_moore o).(initial _) = [].
  Proof.
    intros (t & Hwf). unfold make_moore, KV.make_moore. simpl.
    destruct Hwf as (Hwf' & Hchild & Heps).
    set (Ht := proj1 (proj2 (conj Hwf' (conj Hchild Heps)))).
    eapply sift_leaf_unique with (q0 := []); eauto.
      apply (proj2_sig (sift_val t [] Ht)).
  Qed.

  Lemma out_correct : forall (o : obt) q,
      output _ (make_moore o) q = output_lang (proj1_sig q).
  Proof.
    intros (t & Hwf) q. unfold make_moore, KV.make_moore. reflexivity.
  Qed.
End RSS.

Module RSan := MooreRS s O L RSS.
Import RSan.

End KV.
