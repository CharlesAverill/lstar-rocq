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

Definition finite (f : string -> bool) : Prop :=
    exists (l : list string),
        forall (s : string), f s = true ->
        In s l.

(** Separable: A set Q ⊆ Σ∗ is said to be separable with respect to T,
    if the elements of Q are pairwise T-distinguishable. *)

Definition separable (Q T : string -> bool) : Prop :=
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

Lemma find_separable :
  forall (H : HypothesisDFA)
         (w : string)
         (Hce : accept_string (make_dfa H) w <> member w),
  { q_new : string &
  { t     : string &
      H.(Q) q_new = false /\
      let Q' := str_upd H.(Q) q_new true in
      let T' := str_upd H.(T) t true in
      separable Q' T' /\
      finite Q' /\
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
          unfold correct, p.
          rewrite firstn_all2 by lia.
          rewrite skipn_all2 by lia.
          rewrite app_nil_r. admit.
        - assumption.
    }
    assert {wk | nth_error w k = Some wk}. {
        eexists. apply nth_error_nth'. assumption.
    } destruct X as (wk & ?).
    set (Q_pk := str_upd H.(Q) (proj1_sig (p k)) false).
    assert (H.(T) [proj1_sig (p k) ++ [wk] == proj1_sig (p (S k))]). {
        intros t Tt.
    assert (forall x, Q_pk x = true -> ~ H.(T) [proj1_sig (p k) ++ [wk] == x]). {
        intros.
}
Admitted.

(** Lemma 3. If Q is separable with respect to T, it is possible to
    add finitely many strings to Q resulting in a set Q′ which is
    closed and separable with respect to T. *)

Lemma union_closed :
    forall Q T l
    (sep: separable Q T),
    let Q' := List.fold_left
        (fun a i => (fun i' => if str_eq i i' then true else a i'))
        l Q in
    closed Q' T.
Proof.
    induction l;
        unfold closed; intros; unfold separable in sep0.
    - simpl in *. exists (q ++ a).
Admitted.

End Lstar.
