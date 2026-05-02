(** https://www.tifr.res.in/~shibashis.guha/courses/diwali2021/L-starMalharManagoli.pdf *)

From lstar Require Import Language DFA ListLemmas.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Recdef.
Import ListNotations.

Module Type Teacher (s : Symbol) (L : L s).
    Import s L.
    Module DFA := DFA s L.
    Export DFA.

    (** The teacher answers equivalence queries *)
    Parameter equiv_query : DFA.t -> option string.
    Parameter equiv_query_correct : forall d,
        equiv_query d = None <-> encodes d.
    Parameter equiv_query_ce : forall d w,
        equiv_query d = Some w ->
        accept_string d w <> member w.
End Teacher.

Module Lstar (s : Symbol) (L : L s) (T : Teacher s L).
Import s L T.

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

Fixpoint InS {A : Type} (a : A) (l : list A) : Type :=
    match l with
    | [] => Empty_set
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
Qed.

Lemma InS_to_In : forall A a (l : list A),
    InS a l -> In a l.
Proof.
    intros. induction l.
        contradiction.
    destruct X; subst.
        now left.
    right. auto.
Qed.

Definition finite (f : string -> bool) :=
    {l : list string |
        forall (s : string), f s = true <-> In s l}.

(** T-equivalence is decidable for finite sets *)
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
        {q' : string | Q q' = true /\ T [(q ++ [a]) == q']}.

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
Qed.   

(** Closedness is decidable for finite sets *)
Definition closed_dec_witness : forall Q T,
  finite Q ->
  finite T ->
  closed Q T + 
  { q : string & { a : s.t &
      Q q = true /\
      forall q', Q q' = true -> ~ T [q ++ [a] == q'] }}.
Proof.
  intros Q T finQ finT.
  destruct finQ as (Ql & Qfin).
  destruct (List.find (fun '(q, a) =>
      negb (existsb (fun q' =>
          if T_equiv_dec T (q ++ [a]) q' finT then true else false
      ) Ql)) (list_prod Ql enum)) eqn:Hfind.
  - destruct p as (q, a).
    apply List.find_some in Hfind.
    destruct Hfind as [HIn Hcheck].
    apply in_prod_iff in HIn. destruct HIn as [HIn_q HIn_a].
    right. exists q, a. split.
    + now apply Qfin.
    + intros q' Hq' Contra.
      apply Bool.negb_true_iff in Hcheck.
      apply Bool.not_true_iff_false in Hcheck.
      apply Hcheck. rewrite existsb_exists.
      exists q'. split.
      * now apply Qfin.
      * destruct (T_equiv_dec T (q ++ [a]) q' finT).
        { reflexivity. }
        { exfalso. now apply n. }
  - left. intros q a Hq.
    apply List.find_none with (x := (q, a)) in Hfind.
    + apply Bool.negb_false_iff in Hfind.
      apply existsb_exists_set in Hfind.
      destruct Hfind as (q' & Hq' & Hcheck).
      exists q'. split.
      * now apply Qfin.
      * destruct (T_equiv_dec T (q ++ [a]) q' finT).
        { assumption. }
        { discriminate. }
    + apply in_prod.
      * now apply Qfin.
      * apply t_enumerable.
Qed.

Definition closed_dec : forall Q T,
    finite Q ->
    finite T ->
    closed Q T + (closed Q T -> False).
Proof.
    intros. destruct (closed_dec_witness Q T X X0).
        now left.
    right. intros Contra.
    destruct s as (q & a & Qq & Tdistinguishable).
    specialize (Contra q a Qq).
    destruct Contra as (q' & Qq' & Teq).
    destruct (Tdistinguishable q' Qq' Teq).
Qed.

(** Lemma 1. If Q is closed and separable with respect to T,
    the transition function δ : (q, a) → q′ ∈ Q such that
    q′ ≡T q · a, is well defined. *)

Definition delta Q T (c : closed Q T) (q : string) (a : s.t) (Qq : Q q = true) :
        {q' : string | Q q' = true /\ T [q' == (q ++ [a])]}.
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
        set (r := delta H.(Q) H.(T) H.(clos) (proj1_sig q) a (proj2_sig q)).
        unfold state. destruct r as (q' & Qq' & Teq).
        exists q'. apply Qq'.
    }
    set (accept := fun (q : state) => member (proj1_sig q)).
    exact {|state      := state;
            initial    := initial;
            transition := transition;
            accept     := accept|}.
Defined.

(** Updating sets of strings *)
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

Lemma find_separable :
  forall (H : HypothesisDFA) (* Q is closed and separable wrt T *)
         (w : string)
         (* w is a counterexample *)
         (Hce : accept_string (make_dfa H) w <> member w),
  (* We can find q_new and t to add to Q, T s.t. Q' and T' are finite and
     Q' is separable wrt T' *)
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
    (* Retrieve w[k] *)
    assert {wk | nth_error w k = Some wk}. {
        destruct (nth_error w k) eqn:He.
        - now exists t0.
        - rewrite nth_error_None in He. lia.
    } destruct X as (wk & ?).
    (* q_new := p_k w_k *)
    (* t := w[S k:] *)
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
    (* Perform a single step of the current DFA *)
    assert (run_step : forall i a, 
          run (make_dfa H) (firstn i w ++ [a]) = 
          (make_dfa H).(transition) (run (make_dfa H) (firstn i w)) a). {
      intros. unfold run.
      rewrite fold_left_app. reflexivity.
    }
    assert (HTeq : H.(T) [proj1_sig (p k) ++ [wk] == proj1_sig (p (S k))]). {
        unfold p. rewrite Hfirstn, run_step. simpl.
        set (q := run (make_dfa H) (firstn k w)).
        destruct (delta H.(Q) H.(T) H.(clos) (proj1_sig q)
                  wk (proj2_sig q)) as [q' [Hq' Heq]].
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

(** For any finite sets Q and T and string u, either we can find a
    'representative' string r in Q such that u and r are
    T-equivalent, or all elements in Q are T-distinguishable from u *)
Lemma find_representative : forall Q T
    (finQ : finite Q)
    (finT : finite T)
    (u : string),
    { r | Q r = true /\ T [u == r] } +
    { forall r, Q r = true -> ~ T [u == r] }.
Proof.
    intros Q T finQ finT u.
    destruct finQ as (Ql & HQl).
    destruct (List.find (fun q =>
        match Bool.bool_dec (Q q) true with
        | left _ =>
            match T_equiv_dec T u q finT with
            | left _ => true
            | right _ => false
            end
        | right _ => false
        end) Ql) eqn:Hfind.
    - apply List.find_some in Hfind.
      destruct Hfind as [HIn Hcheck].
      left. exists s.
      destruct (Bool.bool_dec (Q s) true) as [Hq | Hq].
        now destruct (T_equiv_dec T u s finT) as [Heq | Hneq].
      discriminate.
    - right. intros r Hr Contra.
      apply List.find_none with (x := r) in Hfind.
      + destruct (Bool.bool_dec (Q r) true) as [Hq | Hq].
            now destruct (T_equiv_dec T u r finT) as [Heq | Hneq].
        now rewrite Hr in Hq.
      + now apply HQl.
Qed.

(** We can add a representative of q to Q to get a new
    set Q' that is still separable and finite and is a
    superset of Q *)
Lemma close_step : forall Q T q (a : s.t)
    (sep : separable Q T)
    (finQ : finite Q)
    (finT : finite T),
    { Q' : string -> bool &
        separable Q' T *
        finite Q' *
        (forall s, Q s = true -> Q' s = true) *
        { r | Q' r = true /\ T [(q ++ [a]) == r] } }.
Proof.
    intros Q T q a sep finQ finT.
    destruct (find_representative Q T finQ finT (q ++ [a])) as [rep | norep].
    - now exists Q.
    - exists (str_upd Q (q ++ [a]) true). repeat split.
      + intros u v Qu Qv Neq.
        unfold str_upd in *.
        destruct (str_eq u (q ++ [a])) eqn:Hu,
                 (str_eq v (q ++ [a])) eqn:Hv; subst; auto.
        intro Contra. symmetry in Contra. now apply norep in Contra.
      + destruct finQ as (Ql & HQl).
        exists ((q ++ [a]) :: Ql). intro s. split.
        * intro Hs. unfold str_upd in Hs.
          destruct (str_eq s (q ++ [a])); subst.
            now left.
          right. now apply HQl.
        * intro HIn. unfold str_upd.
          destruct (str_eq s (q ++ [a])).
            reflexivity.
          apply HQl. destruct HIn; subst.
            now destruct n.
            assumption.
      + intros s Hs. unfold str_upd.
        now destruct (str_eq s (q ++ [a])).
      + exists (q ++ [a]). split.
            apply update_eq.
        reflexivity.
Qed.

(** If Q is not closed wrt T, we can find a q in Q such that
    all q' in Q are T-distinguishable from q ++ [a] for all 
    symbols in the alphabet *)
Lemma not_closed_impl_distinguishable :
    forall Q T,
        (closed Q T -> False) ->
        finite Q -> finite T ->
        {q : string & {a : s.t | Q q = true /\
            forall q', Q q' = true -> ~ T [q ++ [a] == q'] }}.
Proof.
    intros Q T QNC Qfin Tfin.
    destruct (closed_dec_witness Q T Qfin Tfin).
        contradiction.
    destruct s as (q & a & Qq & Tdist).
    now exists q, a.
Qed.

(** Adds a finite number of strings to Q to make it closed wrt T *)
Definition union_closed_loop :
    forall (n : nat) Q Q' T
        (sep' : separable Q' T)
        (finT : finite T)
        (finQ' : finite Q')
        (sub' : forall s, Q s = true -> Q' s = true),
        option { Q'' : string -> bool &
            closed Q'' T *
            separable Q'' T *
            finite Q'' *
            (forall s, Q' s = true -> Q'' s = true) }.
    intro n.
    induction n as [| n' IH]; intros Q Q' T; intros.
        exact None.
    pose proof finT as finT_copy. destruct finT as (Tl & HTl).
    destruct (closed_dec_witness Q' T finQ' (exist _ Tl HTl))
        as [clos | (q & a & Hq & norep)].
        apply Some. exists Q'. repeat split; auto.
    destruct (close_step Q' T q a sep' finQ' (exist _ Tl HTl))
            as (Q'' & ((sep'' & finQ'') & sub'') & _).
    destruct (IH Q Q'' T sep'' finT_copy finQ'' (fun s Hs => sub'' s (sub' s Hs)))
            as [result |].
        destruct result as (Q''' & ((clos''' & sep''') & finQ''') & sub''').
        apply Some. exists Q'''. repeat split; auto.
    apply None.
Defined.

(* union_closed_loop always returns Some with enough fuel *)
Lemma loop_terminates : forall n Q Q' T
    (sep' : separable Q' T)
    (finQ' : finite Q')
    (Tl : list string)
    (HTl : forall s : string, T s = true <-> In s Tl)
    (sub' : forall s, Q s = true -> Q' s = true),
    Nat.pow 2 (length Tl) - length (proj1_sig finQ') < n ->
    {x | union_closed_loop n Q Q' T sep' (exist _ Tl HTl) finQ' sub' = Some x}.
Proof.
    intros n Q Q' T. intros.
    destruct finQ' as (Q'l & finQ'). simpl in *.
    revert Q Q' sep' Q'l finQ' sub' H.
    induction n as [| n' IH]; intros. lia.
    rewrite PeanoNat.Nat.lt_succ_r in H.
    simpl.
    destruct (closed_dec_witness Q' T
        (exist _ Q'l finQ') (exist _ Tl HTl)) as [clos | noclos].
        eexists. reflexivity.
    destruct noclos as (q & a & Hq & norep).
    destruct (close_step Q' T q a sep'
        (exist _ Q'l finQ') (exist _ Tl HTl))
        as (Q'' & ((sep'' & finQ'') & sub'') & _).
    destruct finQ'' as (Q''l & HQ''l).
    destruct (IH Q0 Q'' sep'' Q''l HQ''l (fun s Hs => sub'' s (sub' s Hs))) as
        ((Q''' & (((clos''' & sep''') & fin''') & sub''')) & Eq). {
        admit.
    }
    simpl in *. eexists. rewrite Eq. reflexivity.
Admitted.

(** Lemma 3 *)
Lemma union_closed :
    forall Q T
    (sep : separable Q T)
    (finQ : finite Q)
    (finT : finite T),
    { Q' : string -> bool &
        closed Q' T *
        separable Q' T *
        finite Q' *
        (forall s, Q s = true -> Q' s = true) }.
Proof.
    intros Q T sep finQ finT.
    pose proof finT as finT_copy.
    destruct finT as (Tl & HTl).
    (* fuel = 2^|Tl| bounds the number of T-equivalence classes *)
    set (fuel := S (Nat.pow 2 (length Tl))).
    destruct (loop_terminates fuel Q Q T sep finQ Tl HTl ltac:(auto) ltac:(lia)).
    destruct x as (Q' & ((clos' & sep') & finQ') & sub').
    exists Q'. repeat split; auto.
Qed.

Fixpoint lstar (fuel : nat) (H : HypothesisDFA)
    : option { d : DFA.t | encodes d }.
    destruct fuel as [| n].
    - exact None.
    - destruct (equiv_query (make_dfa H)) eqn:Heq.
      + (* counterexample s *)
        assert (Hce : accept_string (make_dfa H) s <> member s)
            by now apply equiv_query_ce.
        destruct (find_separable H s Hce) as
            (q_new & t & HQnew & (sep' & finQ') & finT').
        set (Q' := str_upd H.(Q) q_new true).
        set (T' := str_upd H.(T) t true).
        destruct (union_closed Q' T' sep' finQ' finT') as
            (Q'' & ((clos'' & sep'') & finQ'') & sub'').
        assert (eps_in_Q'' : Q'' nil = true). {
            apply sub''. unfold Q'. 
            rewrite update_neq.
            - apply H.(eps_in_Q).
            - (* nil <> q_new *)
              intro Heq'. subst q_new.
              rewrite H.(eps_in_Q) in HQnew.
              discriminate. }
        exact (lstar n {|
            Q        := Q'';
            T        := T';
            sep      := sep'';
            clos     := clos'';
            eps_in_Q := eps_in_Q'';
            fin_Q    := finQ'';
            fin_T    := finT' |}).
      + (* no counterexample, make_dfa H encodes L *)
        apply Some. exists (make_dfa H).
        now apply equiv_query_correct in Heq.
Defined.

End Lstar.
