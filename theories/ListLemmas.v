From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
Import ListNotations.

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

(** All length-[n] vectors over the alphabet [alpha]. *)
Fixpoint all_vectors {A} (alpha : list A) (n : nat) : list (list A) :=
    match n with
    | 0 => [[]]
    | S n' => flat_map (fun x => map (cons x) (all_vectors alpha n')) alpha
    end.

Lemma length_all_vectors : forall {A} n (alpha : list A),
    length (all_vectors alpha n) = Nat.pow (length alpha) n.
Proof.
    induction n; intros; simpl in *.
        reflexivity.
    rewrite flat_map_constant_length with (c := length (all_vectors alpha n)).
        now rewrite IHn.
    intros. now rewrite length_map.
Qed.

Lemma in_all_vectors : forall {A} n (alpha : list A) v,
    length v = n ->
    (forall x, In x v -> In x alpha) ->
    In v (all_vectors alpha n).
Proof.
    induction n; intros; simpl in *.
        destruct v; simpl in *. now left. discriminate.
    destruct v; simpl in *. discriminate.
    inversion H; subst; clear H. apply in_flat_map.
    exists a. split.
        apply H0. now left.
    apply in_map_iff. eexists. split. reflexivity.
    apply IHn. reflexivity.
    intros. apply H0. now right.
Qed.

Lemma NoDup_finlist_length : forall {A} (alpha : list A) (vecs : list (list A)) (n : nat),
    NoDup vecs ->
    (forall v, In v vecs -> length v = n) ->
    (forall v x, In v vecs -> In x v -> In x alpha) ->
    length vecs <= Nat.pow (length alpha) n.
Proof.
    intros. rewrite <- length_all_vectors.
    apply NoDup_incl_length. assumption.
    repeat intro. apply in_all_vectors.
        now apply H0. eauto.
Qed.

Fixpoint suffixes {A : Type} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: xs => l :: suffixes xs
  end.

Lemma l_neq_cons_l : forall {A} (l : list A) a,
    l <> a :: l.
Proof.
    induction l; intros.
        discriminate.
    intro Contra. inversion Contra; subst; clear Contra.
    eapply IHl, H1.
Qed.

Lemma in_cons_suffixes_impl_in_suffixes : forall {A} (l l' : list A) (x : A),
    In (x :: l) (suffixes l') ->
    In l (suffixes l').
Proof.
    induction l'; intros; simpl in *.
        intuition. inversion H0.
    right. destruct H.
        inversion H; subst; clear H.
        destruct l; now left.
    eauto.
Qed.

Lemma NoDup_suffixes : forall {A} (l : list A),
    NoDup (suffixes l).
Proof.
    induction l.
        simpl. constructor. now intro. constructor.
    simpl. constructor; [|assumption]. clear.
    revert a. induction l; intros; simpl in *.
        intro. intuition. inversion H0.
    intro Contra. destruct Contra.
        inversion H; subst; clear H.
        now apply l_neq_cons_l in H2.
    eapply IHl.
    apply in_cons_suffixes_impl_in_suffixes in H. eassumption.
Qed.

Lemma app_in_suffixes : forall {A} (w0 w' : list A) w,
    In (w0 ++ w') (suffixes w) ->
    In w' (suffixes w).
Proof.
    induction w0; intros; simpl in *.
        assumption.
    apply IHw0. eauto using in_cons_suffixes_impl_in_suffixes.
Qed.

Lemma suffixes_refl : forall {A} (l : list A), In l (suffixes l).
Proof. intros A l. destruct l; simpl; now left. Qed.

(* A generic constructive search, used to decide the two progress conditions. *)
Lemma list_search : forall {A} (P : A -> Prop) (l : list A),
    (forall x, {P x} + {~ P x}) ->
    {x : A | In x l /\ P x} + {forall x, In x l -> ~ P x}.
Proof.
    intros A P l Pdec. induction l as [| x l IH].
        right. intros y [].
    destruct (Pdec x) as [Hx | Hx].
        left. exists x. split; [now left | apply Hx].
    destruct IH as [(y & Hy & HPy) | Hno].
        left. exists y. split; [now right | apply HPy].
    right. intros y [<- | Hy]; [apply Hx | now apply Hno].
Defined.

Lemma filter_len_le : forall {A} (f : A -> bool) l, length (filter f l) <= length l.
Proof.
  intros A f l. induction l as [| x l IH]; simpl; [lia |].
  destruct (f x); simpl; lia.
Qed.

(* Filters ordered pointwise are ordered in length. *)
Lemma filter_le_pointwise : forall {A} (f g : A -> bool) l,
    (forall x, In x l -> f x = true -> g x = true) ->
    length (filter f l) <= length (filter g l).
Proof.
    intros A f g l. induction l as [| x l IH]; intro Himp; simpl.
        lia.
    assert (Htail : forall y, In y l -> f y = true -> g y = true)
        by (intros y Hy; apply Himp; now right).
    specialize (IH Htail).
    destruct (f x) eqn:Ef.
    - rewrite (Himp x (or_introl eq_refl) Ef). simpl. lia.
    - destruct (g x); simpl; lia.
Qed.

Lemma filter_lt_pointwise : forall {A} (f g : A -> bool) l x,
    (forall y, In y l -> f y = true -> g y = true) ->
    In x l -> g x = true -> f x = false ->
    length (filter f l) < length (filter g l).
Proof.
    intros A f g l. induction l as [| y l IH]; intros x Himp Hin Hgx Hfx.
        destruct Hin.
    assert (Htail : forall z, In z l -> f z = true -> g z = true)
        by (intros z Hz; apply Himp; now right).
    simpl. destruct Hin as [<- | Hin].
    - rewrite Hfx, Hgx. simpl.
      pose proof (filter_le_pointwise f g l Htail). lia.
    - specialize (IH x Htail Hin Hgx Hfx).
      destruct (f y) eqn:Efy.
      + rewrite (Himp y (or_introl eq_refl) Efy). simpl. lia.
      + destruct (g y); simpl; lia.
Qed.

(* If two pointwise-ordered filters have the same length, they agree. *)
Lemma filter_eq_len_ext : forall {A} (f g : A -> bool) l,
    (forall x, In x l -> f x = true -> g x = true) ->
    length (filter f l) = length (filter g l) ->
    forall x, In x l -> g x = true -> f x = true.
Proof.
    intros A f g l Himp Hlen x Hx Hgx.
    destruct (f x) eqn:Efx; [reflexivity |].
    exfalso. pose proof (filter_lt_pointwise f g l x Himp Hx Hgx Efx). lia.
Qed.

Lemma existsb_map : forall {X Y} (l : list X) f (g : X -> Y),
    existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof.
    induction l; intros; simpl in *.
        reflexivity.
    f_equal. apply IHl.
Qed.

(* Remove the first occurrence of [x] from [l] *)
Fixpoint remove_one {X : Type} (eqX : forall a b : X, {a = b} + {a <> b})
    (x : X) (l : list X) : list X :=
    match l with
    | [] => []
    | y :: ys => if eqX x y then ys else y :: remove_one eqX x ys
    end.

Lemma remove_one_length_in : forall {X} eqX (x : X) l,
    In x l -> length l = S (length (remove_one eqX x l)).
Proof.
    induction l as [| y ys IH]; intros Hin.
        now destruct Hin.
    simpl. destruct (eqX x y) as [-> | Hneq].
        reflexivity.
    destruct Hin as [-> | Hin]; [now destruct Hneq |].
    simpl. now rewrite (IH Hin).
Qed.

Lemma remove_one_in_neq : forall {X} eqX (x b : X) l,
    In x l -> x <> b -> In x (remove_one eqX b l).
Proof.
    induction l as [| y ys IH]; intros Hin Hneq.
        now destruct Hin.
    simpl. destruct (eqX b y) as [-> | Hby].
        destruct Hin as [-> | Hin]; [now destruct Hneq | assumption].
    destruct Hin as [-> | Hin].
        now left.
    right. now apply IH.
Qed.

(* Finite conjunction of double negations is the double negation of the finite
   conjunction.  Intuitionistically valid for concrete lists. *)
Lemma nn_forall_list : forall {X} (l : list X) (Q : X -> Prop),
    (forall x, In x l -> ~ ~ Q x) ->
    ~ ~ (forall x, In x l -> Q x).
Proof.
    induction l as [| a l' IH]; intros Q Hall Hcon.
        apply Hcon. intros x [].
    apply (Hall a (or_introl eq_refl)). intro Qa.
    apply (IH Q (fun x Hx => Hall x (or_intror Hx))). intro Qtail.
    apply Hcon. intros x [<- | Hx]; [apply Qa | now apply Qtail].
Qed.

Lemma relational_pigeonhole :
    forall {A B : Type}
           (eqA : forall x y : A, {x = y} + {x <> y})
           (eqB : forall x y : B, {x = y} + {x <> y})
           (R : A -> B -> Prop) (la : list A) (lb : list B),
    NoDup la ->
    (forall a, In a la -> exists b, In b lb /\ R a b) ->
    (forall a1 a2 b, In a1 la -> In a2 la -> R a1 b -> R a2 b -> a1 = a2) ->
    length la <= length lb.
Proof.
    intros A B eqA eqB R la lb NDa.
    revert lb.
    induction la as [| a la' IH]; intros lb Htot Hinj.
        simpl. lia.
    apply NoDup_cons_iff in NDa as (Hnin & NDa').
    destruct (Htot a (or_introl eq_refl)) as (b & Hb & Rab).
    (* remove b from lb and recurse on la' *)
    assert (Hlen : length lb = S (length (remove_one eqB b lb)))
        by now apply remove_one_length_in.
    rewrite Hlen. apply le_n_S.
    apply (IH NDa' (remove_one eqB b lb)).
    - intros a' Ha'. destruct (Htot a' (or_intror Ha')) as (b' & Hb' & Rab').
      exists b'. split; [| assumption].
      apply remove_one_in_neq; [assumption |].
      intro Heqb. subst b'.
      assert (a = a') by (apply (Hinj a a' b); [now left | now right | assumption | assumption]).
      subst a'. contradiction.
    - intros a1 a2 c H1 H2. apply (Hinj a1 a2 c); now right.
Qed.
