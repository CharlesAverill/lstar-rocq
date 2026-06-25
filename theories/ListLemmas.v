From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Lemma firstn_len_app : forall X (l1 l2 : list X),
    firstn (length l1) (l1 ++ l2) = l1.
Proof.
    induction l1; intros; simpl in *.
        reflexivity.
    now rewrite IHl1.
Qed.

Lemma skipn_len_app : forall X (l1 l2 : list X),
    skipn (length l1) (l1 ++ l2) = l2.
Proof.
    induction l1; intros; simpl in *.
        reflexivity.
    now rewrite IHl1.
Qed.

Lemma skipn_Slen_cons_app : forall X (l1 l2 : list X) x,
    skipn (S (length l1)) (l1 ++ x :: l2) = l2.
Proof.
    induction l1; intros; simpl in *.
        reflexivity.
    now rewrite IHl1.
Qed.

Lemma skipn_S_wk : forall (X : Type) (w : list X) k wk,
    nth_error w k = Some wk ->
    skipn k w = wk :: skipn (S k) w.
Proof.
    intros X w. induction w; intros.
    - destruct k; discriminate.
    - destruct k.
      + simpl in H. injection H. intro. subst. reflexivity.
      + simpl in *. apply IHw. assumption.
Qed.

Lemma nth_error_split_sig :
    forall {A : Type} (l : list A) (n : nat) (a : A),
    nth_error l n = Some a ->
    {l1 : list A & {l2 : list A | l = l1 ++ a :: l2 /\ length l1 = n}}.
Proof.
  intros. generalize dependent l.
  induction n as [|n IH]; intros [|x l] H; [easy| |easy|].
  - exists nil; exists l. now injection H as [= ->].
  - destruct (IH _ H) as (l1 & l2 & H1 & H2).
    exists (x::l1); exists l2; simpl; split; now f_equal.
Defined.

Definition existsb_exists_set :
    forall (A : Type) (f : A -> bool) (l : list A),
    existsb f l = true -> {x : A | In x l /\ f x = true}.
Proof.
    induction l; intros.
        discriminate.
    simpl in *. destruct (f a) eqn:E; simpl in *.
    - exists a. split. now left. assumption.
    - specialize (IHl H). destruct IHl as (x & InX & Fx).
      exists x. split. now right. assumption.
Defined.


(** Given a list of bool lists that contains no duplicates, where
    all of the lists have length [n], the length of the outer list
    is bounded by #2<sup>n</sup>#. *)
Lemma NoDup_boollist_length : forall (vecs : list (list bool)) (n : nat),
    NoDup vecs ->
    (forall v, In v vecs -> length v = n) ->
    length vecs <= Nat.pow 2 n.
Proof.
  intros vecs n. revert vecs.
  induction n as [| n' IHn]; intros vecs HND Hlen.
  - destruct vecs as [| v [| v' ?]]; simpl; try lia.
    exfalso.
      replace v with (@nil bool) in * by
        (symmetry; apply length_zero_iff_nil; apply Hlen; now left).
      replace v' with (@nil bool) in * by
        (symmetry; apply length_zero_iff_nil; apply Hlen; right; now left).
      subst. apply NoDup_cons_iff in HND. destruct HND. apply H. now left.
  - simpl. rewrite Nat.add_0_r.
    set (vt := filter (fun v => match v with true  :: _ => true | _ => false end) vecs).
    set (vf := filter (fun v => match v with false :: _ => true | _ => false end) vecs).
    assert (Hpart : length vecs = length vt + length vf). {
      unfold vt, vf. clear HND IHn.
      induction vecs as [| v vs IHvs].
        reflexivity.
      assert (Hvl : length v = S n') by (apply Hlen; now left).
        destruct v; simpl in Hvl; try discriminate; destruct b;
        simpl; rewrite IHvs; try lia;
        intros u Hu; apply Hlen; now right. }
    assert (HltT : length (map (@tl bool) vt) <= Nat.pow 2 n'). {
        apply IHn.
        - (* tl is injective on vt since all heads are true *)
            unfold vt. clear - HND Hlen.
            induction vecs.
                constructor.
            simpl. destruct a eqn:Hv.
            (* v = [] : length 0 = S n', contradiction *)
                exfalso. specialize (Hlen nil ltac:(now left)). simpl in Hlen. lia.
            destruct b.
            + (* v = true :: _ : goes into vt *)
                apply NoDup_cons_iff in HND. destruct HND as [Hni NDvs].
                simpl. constructor.
                * intro HIn. apply in_map_iff in HIn.
                  destruct HIn as (w & Htl & HwIn).
                  apply filter_In in HwIn. destruct HwIn as [HwVs Hwh].
                  destruct w. discriminate. destruct b;
                    simpl in Htl; subst.
                  now apply Hni. discriminate.
                * apply IHvecs; auto.
                  intros. apply Hlen. now right.
            + (* v = false :: _ : filtered out *)
                apply NoDup_cons_iff in HND. destruct HND as [Hni NDvs].
                apply IHvecs; auto.
                intros. apply Hlen. now right.
        - intros v Hv. apply in_map_iff in Hv.
            destruct Hv as (u & <- & HuIn).
            apply filter_In in HuIn. destruct HuIn as [HuV Huh].
            assert (length u = S n') by (apply Hlen; exact HuV).
            destruct u; simpl in *; lia. }
    assert (HltF : length (map (@tl bool) vf) <= Nat.pow 2 n'). {
        apply IHn.
        - (* tl is injective on vf since all heads are true *)
            unfold vf. clear - HND Hlen.
            induction vecs.
                constructor.
            simpl. destruct a eqn:Hv.
            (* v = [] : length 0 = S n', contradiction *)
                exfalso. specialize (Hlen nil ltac:(now left)). simpl in Hlen. lia.
            destruct b.
            + (* v = true :: _ : filtered out *)
                apply NoDup_cons_iff in HND. destruct HND as [Hni NDvs].
                    apply IHvecs; auto. intros. apply Hlen.
                    now right.
            + (* v = false :: _ : goes into vf *)
                apply NoDup_cons_iff in HND. destruct HND as [Hni NDvs].
                simpl. constructor.
                    intro HIn. apply in_map_iff in HIn.
                    destruct HIn as (w & Htl & HwIn).
                    apply filter_In in HwIn. destruct HwIn as [HwVs Hwh].
                    destruct w; try discriminate. destruct b. discriminate.
                    simpl in Htl. subst. now apply Hni.
                apply IHvecs; auto.
                  intros. apply Hlen. now right.
        - intros v Hv. apply in_map_iff in Hv.
            destruct Hv as (u & <- & HuIn).
            apply filter_In in HuIn. destruct HuIn as [HuV Huh].
            assert (length u = S n') by auto.
            destruct u; simpl in *; lia. }
        rewrite length_map in HltT, HltF. lia.
Qed.

Lemma NoDup_app_intro : forall {X} (l1 l2 : list X),
    NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
    induction l1 as [| a l1 IH]; intros l2 N1 N2 D; simpl; [assumption |].
    apply NoDup_cons_iff in N1 as [Hni N1]. constructor.
    - intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
          now apply Hni.
      apply (D a); [now left | assumption].
    - apply IH; [assumption.. |]. intros x Hx. apply D. now right.
Qed.

Lemma NoDup_app_l : forall {A} (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l1.
Proof.
    induction l1 as [| a l1 IH]; intros l2 H; simpl in H; [constructor |].
    apply NoDup_cons_iff in H as [Hni H]. constructor.
        intro Hin. apply Hni, in_or_app. now left.
    now apply IH with l2.
Qed.

Lemma NoDup_app_r : forall {A} (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l2.
Proof.
    induction l1 as [| a l1 IH]; intros l2 H; simpl in H; [assumption |].
    apply NoDup_cons_iff in H as [_ H]. now apply IH.
Qed.

Lemma NoDup_app_disj : forall {A} (l1 l2 : list A),
    NoDup (l1 ++ l2) -> forall x, In x l1 -> ~ In x l2.
Proof.
    induction l1 as [| a l1 IH]; intros l2 H x Hx; simpl in *; [contradiction |].
    apply NoDup_cons_iff in H as [Hni H]. destruct Hx as [-> | Hx].
        intro. apply Hni, in_or_app. now right.
    now apply IH.
Qed.

Lemma list_with_proof : forall {A : Type}
    (l : list A) (P : A -> Prop)
    (pf : forall s, In s l -> P s),
    list {s | P s}.
Proof.
    induction l; intros.
        exact nil.
    apply cons.
        exists a. apply pf. now left.
    apply IHl. intros s Hin. apply pf. now right.
Defined.

Lemma list_with_proof_preserves_len : forall {X} (l : list X) P In,
    List.length (list_with_proof l P In) = List.length l.
Proof.
    induction l; intros.
        reflexivity.
    simpl. f_equal. apply IHl.
Qed.

Lemma list_with_proof_complete :
    forall {X} (l : list X) (P : X -> Prop)
           (Pirr : forall x (p q : P x), p = q)
           (In_proof : forall x, In x l -> P x)
           (x : X) (Hx : In x l),
    In (exist P x (In_proof x Hx)) (list_with_proof l P In_proof).
Proof.
    induction l as [| a l IH]; intros P Pirr In_proof x Hx.
    - inversion Hx.
    - simpl. destruct Hx as [Heq | Hin].
      + subst a. now left.
      + right.
        specialize (IH P Pirr (fun s H => In_proof s (or_intror H)) x Hin).
        now rewrite (Pirr x (In_proof x (or_intror Hin))
                       ((fun s H => In_proof s (or_intror H)) x Hin)).
Qed.

Lemma in_list_with_proof : forall {A} (l : list A) (P : A -> Prop) pf r,
    In r (list_with_proof l P pf) -> In (proj1_sig r) l.
Proof.
    induction l; intros P pf r Hin.
        destruct Hin.
    simpl in Hin. destruct Hin.
        subst. now left.
    right. eauto.
Qed.

Fixpoint InS {A : Type} (a : A) (l : list A) : Type :=
    match l with
    | nil => Empty_set
    | b :: l' => (b = a) + InS a l'
    end.

Lemma In_to_InS : forall A a (l : list A)
    (dec : forall (x y : A), {x = y} + {x <> y}),
    In a l -> InS a l.
Proof.
    induction l; intros.
        contradiction.
    simpl in *. specialize (IHl dec).
    destruct (dec a0 a); subst.
        now left.
    assert (In a l) by now destruct H.
    right. now apply IHl.
Defined.

Lemma InS_to_In : forall A a (l : list A),
    InS a l -> In a l.
Proof.
    intros. induction l.
        contradiction.
    destruct X; subst.
        now left.
    right. auto.
Qed.

Definition mem {A} (eqdec : forall (x y : A), {x=y}+{x<>y})
        (q : A) (l : list A) : bool :=
    existsb (fun y => if eqdec y q then true else false) l.

Lemma mem_In : forall {A} eqdec q (l : list A),
    mem eqdec q l = true <-> In q l.
Proof.
    intros A eqdec q l. unfold mem. rewrite existsb_exists. split.
    - intros (y & Hy & Heq). destruct (eqdec y q); now subst.
    - intro Hin. exists q. split; now destruct (eqdec q q).
Qed.

Lemma list_find : forall {A} (l1 l2 : list A) (f : A -> bool),
    find f (l1 ++ l2) =
        match find f l1 with
        | None => find f l2
        | Some x => Some x
        end.
Proof.
    induction l1; intros; simpl.
        reflexivity.
    destruct (f a) eqn:E.
        reflexivity.
    apply IHl1.
Qed.

Fixpoint list_eqb {X} (eqb : X -> X -> bool) (l1 l2 : list X) : bool :=
    match l1, l2 with
    | h1 :: t1, h2 :: t2 => eqb h1 h2 && list_eqb eqb t1 t2
    | nil, nil => true
    | _, _ => false
    end.
