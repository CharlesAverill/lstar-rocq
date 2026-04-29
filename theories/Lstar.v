(** https://www.tifr.res.in/~shibashis.guha/courses/diwali2021/L-starMalharManagoli.pdf *)

From lstar Require Import Language DFA.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Module Lstar (s : Symbol) (L : L s).
Import s L.

Module DFA := DFA s L.
Import DFA.

(** T-equivalent

    Given any two strings u, v ∈ Σ∗ and a set T ⊆ Σ∗, we say that u, v are
    T-equivalent, and write u ≡T v, if ∀t ∈ T, u · t ∈ L ⇐⇒ v · t ∈ L.
    Otherwise, we say that they are T-distinguishable*)
Definition T_equiv (T : string -> bool) (u v : string) : Prop :=
    forall (t : string),
        T t = true ->
        member (u ++ t) = member (v ++ t).

Notation "T '[' u '==' v ']'" := (T_equiv T u v).

(** Note that ≡T is an equivalence relation *)

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

Add Parametric Relation T : string (T_equiv T)
  reflexivity proved by (Teq_refl T)
  symmetry proved by (Teq_sym T)
  transitivity proved by (Teq_trans T)
  as Teq_setoid.

(** Also, for every T1 ⊆ T2 ⊆ Σ∗, ≡T2 is a refinement of ≡T1.
    As T2 has more strings in it, it has a better chance of
    distinguishing any given pair of strings *)

Theorem refined_distinguish : forall T1 T2
    (Subset: forall s : string,
        T1 s = true -> T2 s = true),
    forall u v,
        T2 [u == v] -> T1 [u == v].
Proof.
    intros. intros t T1t.
    specialize (Subset t T1t).
    specialize (H _ Subset).
    assumption.
Qed.

(** But Σ∗ is a superset of all the T's, so IL refines every ≡T. *)

Lemma total_refinement : forall T u v,
    (fun _ => true) [u == v] -> T [u == v].
Proof.
    intros. intros t Tt.
    specialize (H t eq_refl).
    assumption.
Qed.

(** The states Q and T that we maintain will be finite *)

Definition finite (f : string -> bool) :=
    {l : list string |
        forall (s : string), f s = true <-> In s l}.

(** Separable: A set Q ⊆ Σ∗ is said to be separable with respect to T,
    if the elements of Q are pairwise T-distinguishable. *)

Definition separable (Q T : string -> bool) : Type :=
    forall (u v : string), Q u = true -> Q v = true ->
        u <> v ->
        ~ T [u == v].

(** Closed: A set Q is said to be closed with respect to T, if
    ∀q ∈ Q ∀a ∈ Σ, ∃q′ ∈ Q such that q · a ≡T q'. *)

Definition closed (Q T : string -> bool) :=
    forall q a,
        Q q = true ->
        {q' : string | Q q' = true /\ T [(q ++ a) == q']}.

(** Lemma 1. If Q is closed and separable with respect to T,
    the transition function δ : (q, a) → q′ ∈ Q such that
    q′ ≡T q · a, is well defined. *)

Definition delta Q T (c : closed Q T) (q a : string) (Qq : Q q = true) :
        {q' : string | Q q' = true /\ T [q' == (q ++ a)]}.
    destruct (c q a Qq) as [q' [Hq' Heq]].
    now exists q'.
Defined.

(** Lemma 2. Given a hypothesis DFA H = (Q, Σ, δ, ε, F ) where
    Q is closed and separable with respect to T, and a
    counterexample w = w1, w2 · · · wm, we can find strings qn+1
    and t such that Q′ = Q ∪ {qn+1} is separable with respect to
    T′ = T ∪ {t}. *)

(** A hypothesis DFA is one whose states are exactly the
    string representatives in Q, with the transition function
    given by delta. *)
Record HypothesisDFA : Type := {
  Q    : string -> bool;
  T    : string -> bool;
  sep  : separable Q T;
  clos : closed Q T;
  (** ε must be in Q as the initial state *)
  eps_in_Q : Q nil = true;
  (** Q and T must be finite *)
  fin_Q : finite Q;
  fin_T : finite T;
}.

(** The concrete DFA extracted from a HypothesisDFA *)
Definition make_dfa (H : HypothesisDFA) : DFA.t.
    set (state := {q | H.(Q) q = true}).
    assert (initial : state). {
        unfold state. exists nil.
        apply H.(eps_in_Q).
    }
    assert (transition : state -> s.t -> state). {
        intros q a.
        set (r := delta H.(Q) H.(T) H.(clos) (proj1_sig q)
                  (a :: nil) (proj2_sig q)).
        unfold state. destruct r as (q' & Qq' & Teq).
        exists q'. apply Qq'.
    }
    set (accept := fun (q : state) => member (proj1_sig q)).
    exact {|state      := state;
            initial    := initial;
            transition := transition;
            accept     := accept|}.
Defined.

Definition str_upd (S : string -> bool) k b :=
    fun s => if str_eq s k then b else S s.

Lemma update_neq : forall S x y k,
    x <> y ->
    str_upd S x k y = S y.
Proof.
    intros. unfold str_upd.
    destruct str_eq; now subst.
Qed.

Lemma update_eq : forall S x k,
    str_upd S x k x = k.
Proof.
    intros. unfold str_upd.
    destruct str_eq; now subst.
Qed.

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
Qed.

Lemma find_separable :
  forall (H : HypothesisDFA)
         (w : string)
         (Hce : accept_string (make_dfa H) w <> member w),
  { q_new : string &
  { t     : string &
      (H.(Q) q_new = false) *
      let Q' := str_upd H.(Q) q_new true in
      let T' := str_upd H.(T) t true in
      separable Q' T' *
      finite Q' *
      finite T' }}.
    intros.
    (* Define p_i = δ∗(ε, w1w2 · · · wi) *)
    set (p := fun i => run (make_dfa H) (firstn i w)).
    (* We say a state p_i is correct if p_i w_(i+1) · · · w_m ∈ L ⇐⇒ w ∈ L. *)
    set (correct (i : nat) :=
            L.member (proj1_sig (p i) ++ skipn i w) =
            L.member w).
    (* Now, ε is correct trivially, and p_m is not correct since w is a counterexample. *)
    assert (ExEps: correct 0) by reflexivity.
    assert (ExFull: ~ correct (length w)). {
        intro Contra. unfold correct, p in Contra.
        rewrite firstn_all, skipn_all, app_nil_r in Contra.
        apply Hce. unfold accept_string, accept.
        cbn [make_dfa]. assumption.
    }
    (* Thus, there is some k such that p_(k−1) is correct but p_k is not *)
    assert (ExK: {k : nat | correct k /\ ~ correct (S k)}). {
        assert (correct_dec : forall i, {correct i} + {~ correct i}). {
            intros. unfold correct. destruct member, member;
                decide equality.
        }
        induction (length w) as [| n IH].
          contradiction.
          destruct (correct_dec n) as [Hn | Hn].
            now exists n.
            destruct (IH Hn) as [k [Hk HSk]]. now exists k.
    } destruct ExK as (k & KCorrect & SKIncorrect).
    (* Then t = w_(k+1) · · · w_m distinguishes p_k and p_(k−1)w_k. *)
    assert (Dist: member (proj1_sig (p k) ++ skipn k w) <>
                  member (proj1_sig (p (S k)) ++ skipn (S k) w)). {
        unfold correct in KCorrect, SKIncorrect.
        rewrite KCorrect. now symmetry.
    }
    (* Since p_(k−1)w_k ≡T p_k and p_k ∈ Q, by separability of Q,
       p_(k−1)w_k is T-distinguishable from every element of Q\p_k. *)
    assert (Hlt : k < length w). {
        destruct (PeanoNat.Nat.le_gt_cases (length w) k) as [Hle | Hlt].
        - exfalso. apply SKIncorrect.
          unfold correct, p in *.
          rewrite firstn_all2 in * by lia.
          rewrite skipn_all2 in * by lia.
          rewrite app_nil_r in *. assumption.
        - assumption.
    }
    assert {wk | nth_error w k = Some wk}. {
        destruct (nth_error w k) eqn:He.
        - now exists t0.
        - rewrite nth_error_None in He. lia.
    } destruct X as (wk & ?).
    exists (proj1_sig (p k) ++ [wk]), (skipn (S k) w).
    destruct (nth_error_split_sig _ _ _ e) as (l1 & l2 & Hw & Hlen).
    assert (Hfirstn : firstn (S k) w = firstn k w ++ [wk]). {
        subst w.
        rewrite firstn_app, Hlen, PeanoNat.Nat.sub_succ_l by lia.
        subst.
        rewrite firstn_all2 by lia.
        rewrite firstn_cons. rewrite PeanoNat.Nat.sub_diag.
        rewrite firstn_0. now rewrite firstn_len_app.
    }
    assert (run_step : forall i a, 
          run (make_dfa H) (firstn i w ++ [a]) = 
          (make_dfa H).(transition) (run (make_dfa H) (firstn i w)) a). {
      intros. unfold run.
      rewrite fold_left_app. reflexivity.
    }
    assert (HTeq : H.(T) [proj1_sig (p k) ++ [wk] == proj1_sig (p (S k))]). {
        unfold p. rewrite Hfirstn, run_step. simpl.
        set (q := run (make_dfa H) (firstn k w)).
        destruct (delta H.(Q) H.(T) H.(clos)
            (proj1_sig q) (wk :: nil) (proj2_sig q)) as [q' [Hq' Heq]].
        now symmetry.
    }
    repeat split.
    - unfold p. pose proof H.(sep). unfold separable in X.
      destruct (H.(Q) (proj1_sig (p k) ++ [wk])) eqn:HQ; auto.
      exfalso. apply Dist.
      assert (proj1_sig (p k) ++ [wk] = proj1_sig (p (S k))). {
          destruct (str_eq (proj1_sig (p k) ++ [wk]) (proj1_sig (p (S k)))) as [|Hneq].
          - assumption.
          - destruct (H.(sep) _ _ HQ (proj2_sig (p (S k))) Hneq HTeq).
      } subst.
      rewrite <- H0.
      rewrite skipn_len_app, skipn_Slen_cons_app.
      now rewrite <- app_assoc.
    - intros u v Qu Qv Neq Contra.
      unfold str_upd in Qu, Qv.
      destruct (str_eq u (proj1_sig (p k) ++ [wk])),
               (str_eq v (proj1_sig (p k) ++ [wk])); try subst u; try subst v.
      + now apply Neq.
      + apply (H.(sep) (proj1_sig (p (S k))) v (proj2_sig (p (S k))) Qv).
          intro Contra'. subst v. unfold T_equiv in Contra.
          apply Dist.
          specialize (Contra (skipn (S k) w) (update_eq _ _ _)).
          rewrite <- app_assoc in Contra. rewrite <- Contra.
          now erewrite skipn_S_wk.
        transitivity (proj1_sig (p k) ++ [wk]).
          now symmetry.
        eapply refined_distinguish; [| apply Contra].
        intros. unfold str_upd. now destruct str_eq.
      + apply (H.(sep) (proj1_sig (p (S k))) u (proj2_sig (p (S k))) Qu).
          intro Contra'. subst u. unfold T_equiv in Contra.
          apply Dist.
          specialize (Contra (skipn (S k) w) (update_eq _ _ _)).
          rewrite <- app_assoc in Contra. rewrite Contra.
          now erewrite skipn_S_wk.
        transitivity (proj1_sig (p k) ++ [wk]).
          now symmetry.
        eapply refined_distinguish; [| symmetry; apply Contra].
        intros. unfold str_upd. now destruct str_eq.
      + apply (H.(sep) u v Qu Qv Neq).
        eapply refined_distinguish. 2: exact Contra.
        intros t Ht. unfold str_upd.
        now destruct (str_eq t (skipn (S k) w)).
    - unfold finite. destruct H.(fin_Q) as (l & X).
      exists ((proj1_sig (p k) ++ [wk]) :: l). intros.
      split; intro.
      -- destruct (str_eq s (proj1_sig (p k) ++ [wk])).
            subst. now constructor.
            apply in_cons, X. now rewrite update_neq in H0.
      -- simpl in H0. destruct H0. subst.
            apply update_eq.
         destruct (str_eq s (proj1_sig (p k) ++ [wk])). subst.
            apply update_eq.
         rewrite update_neq. now apply X. now symmetry.
    - unfold finite. destruct H.(fin_T) as (l & X).
      exists ((skipn (S k) w) :: l). intros.
      split; intro.
      -- destruct (str_eq s (skipn (S k) w)).
            subst. now constructor.
            apply in_cons, X. now rewrite update_neq in H0.
      -- simpl in H0. destruct H0. subst.
            apply update_eq.
         destruct (str_eq s (skipn (S k) w)). subst.
            apply update_eq.
         rewrite update_neq. now apply X. now symmetry.
Qed.

(** Lemma 3. If Q is separable with respect to T, it is possible to
    add finitely many strings to Q resulting in a set Q′ which is
    closed and separable with respect to T. *)

Definition T_equiv_dec : forall T (u v : string),
    finite T ->
    {T [u == v]} + {~ T [u == v]}.
Proof.
    intros. destruct X.
    destruct (forallb (fun t =>
        if Bool.eqb (member (u ++ t)) (member (v ++ t))
        then true else false) x) eqn:Hfb.
    - left. intros t Ht.
        rewrite forallb_forall in Hfb.
        assert (In t x) by now apply i.
        specialize (Hfb t H).
        destruct Bool.eqb eqn:E.
            now rewrite Bool.eqb_true_iff in E.
            discriminate.
    - right. intro HTeq.
        apply Bool.not_true_iff_false in Hfb.
        apply Hfb. rewrite forallb_forall.
        intros t' HIn'.
        destruct Bool.eqb eqn:E; [reflexivity |].
        exfalso. apply Bool.eqb_false_iff in E.
        apply E. apply HTeq. apply i. assumption.
Qed.

Lemma union_closed :
    forall Q T
    (sep : separable Q T)
    (finQ : finite Q)
    (finT : finite T)
    (nclos : closed Q T -> False),
    { Q' : string -> bool &
        closed Q' T *
        separable Q' T *
        finite Q' *
        (forall s, Q s = true -> Q' s = true) }.
Proof.
    intros. unfold closed in nclos.
    (* If Q is not closed, we can find a string q ∈ Q
       and a letter a ∈ Σ such that q · a is T -distinguishable
       from every element of Q. *)
    assert {q : string & {a : s.t |
        forall q', Q0 q = true -> Q0 q' = true ->
        ~ T0 [q ++ [a] == q']}}. admit.
    destruct X as (q & a & H).
    exists (str_upd Q0 (q ++ [a]) true). repeat split.
Abort.
End Lstar.
