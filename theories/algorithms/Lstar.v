(** Rivest-Schapire-style automata learning
    https://www.tifr.res.in/~shibashis.guha/courses/diwali2021/L-starMalharManagoli.pdf *)

From lstar Require Import Automata ListLemmas SetLemmas RS.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.
From lstar Require Import Teacher.

Module Lstar (s : Symbol) (L : RegularLanguage s) (T : DFATeacher s L).
Import s L T D.

(** T-equivalent

    Given any two strings u, v ∈ Σ∗ and a set T ⊆ Σ∗, we say that u, v are
    T-equivalent, and write u ≡T v, if ∀t ∈ T, u · t ∈ L ⇐⇒ v · t ∈ L.
    Otherwise, we say that they are T-distinguishable*)
Definition T_equiv (T : str -> bool) (u v : str) : Prop :=
    forall (t : str),
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

Add Parametric Relation T : str (T_equiv T)
  reflexivity proved by (Teq_refl T)
  symmetry proved by (Teq_sym T)
  transitivity proved by (Teq_trans T)
  as Teq_setoid.

(** Also, for every T1 ⊆ T2 ⊆ Σ∗, ≡T2 is a refinement of ≡T1.

    As T2 has more strings in it, it has a better chance of
    distinguishing any given pair of strings *)

Theorem refined_distinguish : forall T1 T2
    (Subset: forall s : str,
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
Definition finite := SetLemmas.finite str.
Notation update := (SetLemmas.update str str_eq).
Notation "s [ k := v ]" := (update s k v).

(** T-equivalence is decidable for finite sets *)
Definition T_equiv_dec : forall T (u v : str),
    finite T ->
    {T [u == v]} + {~ T [u == v]}.
Proof.
    intros. destruct X as (x & _ & i).
    destruct (forallb (fun t =>
        if Bool.eqb (member (u ++ t)) (member (v ++ t))
        then true else false) x) eqn:Hfb.
    - left. intros t Ht.
        rewrite forallb_forall in Hfb.
        specialize (Hfb t ltac:(now apply i)).
        destruct Bool.eqb eqn:E; [|discriminate].
        now rewrite Bool.eqb_true_iff in E.
    - right. intro HTeq.
        apply Bool.not_true_iff_false in Hfb.
        apply Hfb. rewrite forallb_forall.
        intros t' HIn'.
        destruct Bool.eqb eqn:E; [reflexivity|].
        exfalso. apply Bool.eqb_false_iff in E.
        now apply E, HTeq, i.
Defined.

(** A set Q ⊆ Σ∗ is said to be separable with respect to T,
    if the elements of Q are pairwise T-distinguishable. *)
Definition separable (Q T : str -> bool) : Type :=
    forall (u v : str), Q u = true -> Q v = true ->
        u <> v ->
        ~ T [u == v].

(** A set Q is said to be closed with respect to T, if
    ∀q ∈ Q ∀a ∈ Σ, ∃q′ ∈ Q such that q · a ≡T q'. *)
Definition closed (Q T : str -> bool) :=
    forall q a,
        Q q = true ->
        {q' : str | Q q' = true /\ T [(q ++ [a]) == q']}.

(** Closedness is decidable for finite sets:
    - Q is not closed wrt T if one can traverse the list of elements
      in Q without finding a q' such that q · a ≡T q' for all a
    - Q is closed wrt T otherwise *)
Definition closed_dec_witness : forall Q T,
  finite Q ->
  finite T ->
  closed Q T + 
  { q : str & { a : s.t &
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
    destruct Hfind as (HIn & Hcheck).
    apply in_prod_iff in HIn. destruct HIn as (HIn_q & HIn_a).
    right. exists q, a. split.
        now apply Qfin.
    intros q' Hq' Contra.
    apply Bool.negb_true_iff, Bool.not_true_iff_false in Hcheck.
    apply Hcheck. rewrite existsb_exists.
    exists q'. split.
        now apply Qfin.
    destruct (T_equiv_dec T (q ++ [a]) q' finT); auto.
  - left. intros q a Hq.
    apply List.find_none with (x := (q, a)) in Hfind.
    + apply Bool.negb_false_iff, existsb_exists_set in Hfind.
      destruct Hfind as (q' & Hq' & Hcheck).
      exists q'. split.
        now apply Qfin.
        now destruct (T_equiv_dec T (q ++ [a]) q' finT).
    + apply in_prod.
        now apply Qfin.
        apply t_enumerable.
Qed.

Definition closed_dec : forall Q T,
    finite Q ->
    finite T ->
    closed Q T + (closed Q T -> Empty_set).
Proof.
    intros. destruct (closed_dec_witness Q T X X0).
        now left.
    right. intros Contra.
    destruct s as (q & a & Qq & Tdist).
    specialize (Contra q a Qq).
    destruct Contra as (q' & Qq' & Teq).
    destruct (Tdist q' Qq' Teq).
Defined.

(** Lemma 1. If Q is closed and separable with respect to T,
    the transition function δ : (q, a) → q′ ∈ Q such that
    q′ ≡T q · a, is well defined. *)

Definition delta Q T (c : closed Q T) (q : str) (a : s.t) (Qq : Q q = true) :
        {q' : str | Q q' = true /\ T [q' == (q ++ [a])]}.
    destruct (c q a Qq) as [q' [Hq' Heq]].
    now exists q'.
Defined.

(** Lemma 2. Given a hypothesis DFA H = (Q, Σ, δ, ε, F) where
    Q is closed and separable with respect to T, and a
    counterexample w = w1, w2 ... wm, we can find strings qn+1
    and t such that Q′ = Q ∪ {qn+1} is separable with respect to
    T′ = T ∪ {t}. *)

(** A hypothesis DFA is one whose states are the
    string representatives in Q, with the transition function
    given by delta. *)
Record HypothesisDFA : Type := {
  Q    : str -> bool;
  T    : str -> bool;
  sep  : separable Q T;
  clos : closed Q T;
  (** ε must be in Q as the initial state *)
  eps_in_Q : Q nil = true;
  (** Q and T must be finite *)
  fin_Q : finite Q;
  fin_T : finite T;
}.

(** The concrete DFA extracted from a HypothesisDFA *)
Definition make_dfa (H : HypothesisDFA) : D.t {q | H.(Q) q = true}.
    set (state := {q | H.(Q) q = true}).
    assert (initial : state). {
        exists nil. apply H.(eps_in_Q). }
    assert (transition : state -> s.t -> state). {
        intros q a.
        set (r := delta H.(Q) H.(T) H.(clos) (proj1_sig q) a (proj2_sig q)).
        destruct r as (q' & Qq' & Teq). exists q'. apply Qq'. }
    set (accept := fun (q : state) => member (proj1_sig q)).
    destruct H.(fin_Q) as (l & ND & InQ).
    assert (InQpf : forall x, In x l -> H.(Q) x = true). {
        intros x Hin. now apply (proj2 (InQ x)). }
    set (ls := list_with_proof l (fun q => H.(Q) q = true) InQpf).
    refine {| initial    := initial;
              transition := transition;
              accept     := accept;
              states     := ls;
              states_complete := _ |}.
    intro w.
    set (qst := fold_left transition w initial).
    assert (Hin : In (proj1_sig qst) l) by
        apply (proj1 (InQ _)), (proj2_sig qst).
    assert (Heq : qst = exist _ (proj1_sig qst) (InQpf (proj1_sig qst) Hin)). {
        destruct qst as (q & Hq); simpl.
        f_equal. apply (UIP_dec Bool.bool_dec). }
    rewrite Heq.
    eapply (list_with_proof_complete l (fun q => H.(Q) q = true)).
    intros. apply UIP_dec, Bool.bool_dec.
Defined.

(** Given a counter-example, we can always find q_new and t
    to add to Q, T such that Q' and T' are finite and Q' is
    separable wrt T' (see RS.v for linear and binary searches) *)

Module RSS <: RS_Setup s L T.
  Definition obt := HypothesisDFA.
  Definition P (o : obt) (q : str) : Prop := o.(Q) q = true.
  Definition make_dfa (o : obt) : D.t { q | P o q } := make_dfa o.

  Lemma eps_in_H : forall (o : obt),
      proj1_sig (make_dfa o).(initial _) = [].
  Proof.
    intro H. unfold make_dfa, Lstar.make_dfa, initial, fin_Q. simpl.
    now destruct H, fin_Q0, a.
  Qed.

  Lemma acc_correct : forall (o : obt) q,
      accept _ (make_dfa o) q = member (proj1_sig q).
  Proof.
    intros H q. unfold make_dfa, Lstar.make_dfa, accept.
    now destruct fin_Q, a.
  Qed.
End RSS.

Module RSan := RS s L T RSS.
Import RSan.

Theorem find_separable :
  forall (H : HypothesisDFA) (* Q is closed and separable wrt T *)
         (w : str)
         (* w is a counterexample *)
         (Hce : accept_string (make_dfa H) w <> member w),
  { q_new : str &
  { t     : str &
      (H.(Q) q_new = false) *
      let Q' := H.(Q) [q_new := true] in
      let T' := H.(T) [t := true] in
      separable Q' T' *
      finite Q' *
      finite T' }}.
    intros.
    (* There is some k such that p_(k−1) is correct but p_k is not *)
    destruct (RSan.partition_binary H w Hce) as
        (k & KCorrect & SKIncorrect).
    (* Then t = w_(k+1) ... w_m distinguishes p_k and p_(k−1)w_k. *)
    assert (Dist: member (pi H w k ++ skipn k w) <>
                  member (pi H w (S k) ++ skipn (S k) w)). {
        unfold correct, pi in *.
        now rewrite KCorrect.
    }
    (* Since p_(k−1)w_k ≡T p_k and p_k ∈ Q, by separability of Q,
       p_(k−1)w_k is T-distinguishable from every element of Q\p_k. *)
    assert (Hlt : k < length w). {
        destruct (Nat.le_gt_cases (length w) k) as [Hle |]; [|assumption].
        destruct SKIncorrect.
        unfold correct, pi in *.
        now rewrite firstn_all2, skipn_all2, app_nil_r in * by lia.
    }
    (* Retrieve w[k] *)
    assert {wk | nth_error w k = Some wk}. {
        destruct (nth_error w k) eqn:E.
            now exists t0.
        rewrite nth_error_None in E. lia.
    } destruct X as (wk & Hwk).
    (* q_new := p_k w_k *)
    (* t := w[S k:] *)
    exists (pi H w k ++ [wk]), (skipn (S k) w).
    destruct (nth_error_split_sig _ _ _ Hwk) as (l1 & l2 & Hw & Hlen).
    assert (Hfirstn : firstn (S k) w = firstn k w ++ [wk]). {
        subst.
        now rewrite firstn_app, Nat.sub_succ_l,
                    firstn_all2, firstn_cons, Nat.sub_diag,
                    firstn_0, firstn_len_app by lia.
    }
    (* Perform a single step of the current DFA *)
    assert (run_step : forall i a, 
          run (make_dfa H) (firstn i w ++ [a]) = 
          (make_dfa H).(transition _) (run (make_dfa H) (firstn i w)) a). {
      intros. unfold run. now rewrite fold_left_app.
    }
    assert (HTeq : H.(T) [pi H w k ++ [wk] == pi H w (S k)]). {
        unfold pi. rewrite Hfirstn, run_step.
        set (q := run (make_dfa H) (firstn k w)).
        destruct (delta H.(Q) H.(T) H.(clos) (proj1_sig q)
                      wk (proj2_sig q)) as [q' [Hq' Heq]].
        unfold transition, make_dfa, delta.
        now destruct H, fin_Q, a, clos, a.
    }
    assert (H.(Q) (pi H w (S k)) = true) by
        exact (proj2_sig (run (make_dfa H) (firstn (S k) w))).
    repeat split.
    - pose proof H.(sep). unfold separable in X.
      destruct (H.(Q) (pi H w k ++ [wk])) eqn:HQ; auto.
      destruct Dist.
      assert (pi H w k ++ [wk] = pi H w (S k)). {
          destruct (str_eq (pi H w k ++ [wk]) (pi H w (S k))) as [|Hneq].
            easy.
          destruct (H.(sep) _ _ HQ H0 Hneq HTeq).
      } subst.
      now rewrite <- H1, skipn_len_app, skipn_Slen_cons_app, <- app_assoc.
    - intros u v Qu Qv Neq Contra.
      unfold update, SetLemmas.update in Qu, Qv.
      destruct (str_eq u (pi H w k ++ [wk])),
               (str_eq v (pi H w k ++ [wk])); try subst u; try subst v; auto.
      + apply (H.(sep) (pi H w (S k)) v H0 Qv).
          intro Contra'. subst v. unfold T_equiv in Contra.
          apply Dist.
          specialize (Contra (skipn (S k) w) (update_eq _ _ _ _ _)).
          now erewrite <- Contra, <- app_assoc, skipn_S_wk.
        transitivity (pi H w k ++ [wk]).
          now symmetry.
        eapply refined_distinguish; [| apply Contra].
        intros. unfold update, SetLemmas.update. now destruct str_eq.
      + apply (H.(sep) (pi H w (S k)) u H0 Qu).
          intro Contra'. subst u. unfold T_equiv in Contra.
          apply Dist.
          specialize (Contra (skipn (S k) w) (update_eq _ _ _ _ _)).
          now erewrite Contra, <- app_assoc, skipn_S_wk.
        transitivity (pi H w k ++ [wk]).
          now symmetry.
        eapply refined_distinguish; [| symmetry; apply Contra].
        intros. unfold update, SetLemmas.update. now destruct str_eq.
      + apply (H.(sep) u v Qu Qv Neq).
        eapply refined_distinguish; [|apply Contra].
        intros t Ht. unfold update, SetLemmas.update.
        now destruct (str_eq t (skipn (S k) w)).
    - unfold finite. destruct H.(fin_Q) as (l & ND & X).
      eexists. split.
        apply NoDup_cons; eauto.
        + intro Contra.
          rewrite <- X in Contra.
          destruct (str_eq (pi H w k ++ [wk]) (pi H w (S k)))
            as [Heq | Hneq].
            apply Dist. rewrite <- Heq, <- app_assoc.
            unfold app. now rewrite <- skipn_S_wk.
          apply (H.(sep) _ _ Contra H0); eauto.
        + split; intros.
        -- destruct (str_eq s ((pi H w k) ++ [wk])).
            subst. now constructor.
            apply in_cons, X. now rewrite (update_neq _ _) in H1.
        -- destruct H1. subst.
            apply update_eq.
            destruct (str_eq s (pi H w k ++ [wk])). subst.
            apply update_eq.
            rewrite update_neq. now apply X. now symmetry.
    - unfold finite. destruct H.(fin_T) as (l & ND & X).
      eexists. split.
        apply NoDup_cons; eauto. intro Contra.
        rewrite <- X in Contra.
        destruct (str_eq (pi H w k ++ [wk]) (pi H w (S k)))
            as [Heq | Hneq].
            apply Dist. rewrite <- Heq, <- app_assoc.
            unfold app. now rewrite <- skipn_S_wk.
        apply Dist.
        specialize (HTeq (skipn (S k) w) Contra).
        rewrite <- HTeq, <- app_assoc.
        unfold app.
        now rewrite <- skipn_S_wk.
      split; intros.
      + destruct (str_eq s (skipn (S k) w)).
           subst. now constructor.
           apply in_cons, X. now rewrite update_neq in H1.
      + simpl in H1. destruct H1. subst.
           apply update_eq.
        destruct (str_eq s (skipn (S k) w)). subst.
           apply update_eq.
        rewrite update_neq. now apply X. now symmetry.
Defined.

(** Lemma 3. If Q is separable with respect to T, it is possible to
    add finitely many strings to Q resulting in a set Q′ which is
    closed and separable with respect to T. *)

(** For any finite sets Q and T and string u, either we can find a
    'representative' string r in Q such that u and r are
    T-equivalent, or all elements in Q are T-distinguishable from u *)
Lemma find_representative : forall Q T
    (finQ : finite Q)
    (finT : finite T)
    (u : str),
    { r | Q r = true /\ T [u == r] } +
    { forall r, Q r = true -> ~ T [u == r] }.
Proof with try easy.
    intros Q T finQ finT u.
    destruct finQ as (Ql & HQl),
    (List.find (fun q =>
        if Bool.eqb (Q q) true then
            if T_equiv_dec T u q finT then true else false
        else false) Ql) eqn:Hfind.
    - left. apply List.find_some in Hfind.
      destruct Hfind as (HIn & Hcheck).
      exists s.
      destruct (Bool.eqb (Q s) true) eqn:E...
        destruct (T_equiv_dec T u s finT)...
        split...
        apply Bool.eqb_prop in E...
    - right. intros r Hr Contra.
      apply List.find_none with (x := r) in Hfind.
      + destruct (Bool.eqb (Q r) true) eqn:E.
            destruct (T_equiv_dec T u r finT)...
        rewrite Hr in E...
      + apply HQl...
Defined.

(** We can add a representative of q to Q to get a new
    set Q' that is still separable and finite and is a
    superset of Q *)
Lemma close_step : forall Q T q (a : s.t)
    (sep : separable Q T)
    (finQ : finite Q)
    (finT : finite T),
    { Q' : str -> bool &
        ((Q' = Q [q ++ [a] := true]) + (Q' = Q)) *
        separable Q' T *
        finite Q' *
        (forall s, Q s = true -> Q' s = true) *
        { r | Q' r = true /\ T [(q ++ [a]) == r] } }.
Proof with try easy.
    intros Q T q a sep finQ finT.
    destruct (find_representative Q T finQ finT (q ++ [a])) as [rep | norep].
    - exists Q. repeat split; auto.
    - exists (update Q (q ++ [a]) true). repeat split; eauto.
      + intros u v Qu Qv Neq.
        unfold update, SetLemmas.update in *.
        destruct (str_eq u (q ++ [a])) eqn:Hu,
                 (str_eq v (q ++ [a])) eqn:Hv; subst; auto.
        intro Contra. symmetry in Contra. now apply norep in Contra.
      + destruct finQ as (Ql & NDQ & HQl).
        eexists. split.
            apply NoDup_cons; eauto. intro Contra.
            apply HQl in Contra.
            eapply norep; eauto. reflexivity.
        intro s. split.
        * intro Hs. unfold update, SetLemmas.update in Hs.
          destruct (str_eq s (q ++ [a])); subst.
            now left.
          right. now apply HQl.
        * intro HIn. unfold update, SetLemmas.update.
          destruct (str_eq s (q ++ [a]))...
          apply HQl. destruct HIn; subst...
      + intros s Hs. unfold update, SetLemmas.update.
        now destruct (str_eq s (q ++ [a])).
      + exists (q ++ [a]). split...
        apply update_eq.
Defined.

(** If Q is not closed wrt T, we can find a q in Q such that
    all q' in Q are T-distinguishable from q ++ [a] for all 
    symbols in the alphabet *)
Lemma not_closed_impl_distinguishable :
    forall Q T,
        (closed Q T -> False) ->
        finite Q -> finite T ->
        {q : str & {a : s.t | Q q = true /\
            forall q', Q q' = true -> ~ T [q ++ [a] == q'] }}.
Proof.
    intros Q T QNC Qfin Tfin.
    destruct (closed_dec_witness Q T Qfin Tfin).
        contradiction.
    destruct s as (q & a & Qq & Tdist); eauto.
Defined.

(** Adds a finite number of strings to Q to make it closed wrt T *)
Definition union_closed_loop :
    forall (n : nat) Q Q' T
        (sep' : separable Q' T)
        (finT : finite T)
        (finQ' : finite Q')
        (sub' : forall s, Q s = true -> Q' s = true),
        option { Q'' : str -> bool &
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
            as (Q'' & (((Eq & sep'') & finQ'') & sub'') & _).
    destruct (IH Q Q'' T sep'' finT_copy finQ'' (fun s Hs => sub'' s (sub' s Hs)))
            as [result |].
        destruct result as (Q''' & ((clos''' & sep''') & finQ''') & sub''').
        apply Some. exists Q'''. repeat split; auto.
    exact None.
Defined.

(** union_closed_loop always returns Some with enough fuel *)
Lemma loop_terminates : forall n Q Q' T
    (sep' : separable Q' T)
    (finQ' : finite Q')
    (Tl : list str)
    (NDT : NoDup Tl)
    (HTl : forall s : str, T s = true <-> In s Tl)
    (sub' : forall s, Q s = true -> Q' s = true),
    Nat.pow 2 (length Tl) - length (proj1_sig finQ') < n ->
    {x | union_closed_loop n Q Q' T sep' (exist _ Tl (conj NDT HTl)) finQ' sub' = Some x}.
Proof.
    intros n Q Q' T. intros.
    destruct finQ' as (Q'l & NDQ'l & finQ'). simpl in *.
    revert Q Q' sep' Q'l NDQ'l finQ' sub' H.
    induction n as [| n' IH]; intros. lia.
    rewrite Nat.lt_succ_r in H. simpl.
    destruct (closed_dec_witness Q' T
            (exist _ Q'l (conj NDQ'l finQ'))
            (exist _ Tl (conj NDT HTl))) as [clos | noclos].
        eexists. reflexivity.
    destruct noclos as (q & a & Hq & norep).
      destruct (close_step Q' T q a sep'
              (exist _ Q'l (conj NDQ'l finQ'))
              (exist _ Tl (conj NDT HTl)))
          as (Q'' & (((Eq & sep'') & finQ'') & sub'') & (r & Q''r & Teqr)).
      destruct finQ'' as (Q''l & NDQ'' & HQ''l).
      assert (Hnotin : ~ In (q ++ [a]) Q'l). {
          intro HIn.
          apply (norep (q ++ [a])).
            now apply finQ'.
          reflexivity. }
      assert (HinQ'' : In (q ++ [a]) Q''l). {
        apply HQ''l.
        destruct Eq; subst.
            apply update_eq.
        destruct (norep r); auto.
      }
      assert (Hsubset : forall s, In s Q'l -> In s Q''l). {
          intros s HIn. now apply HQ''l, sub'', finQ'. }
      destruct (IH _ Q'' sep'' Q''l NDQ'' HQ''l
              (fun s Hs => sub'' s (sub' s Hs))) as
              ((Q''' & (((clos''' & sep''') & fin''') & sub''')) & Eq').
      enough (Hlt : length Q'l < length Q''l <= Nat.pow 2 (length Tl)) by lia. {
        assert (Hlt : length Q'l < length Q''l). {
            enough (H1 : length Q'l <= length Q''l). {
            enough (H2 : length Q'l <> length Q''l) by lia.
            intro Heq.
            apply Hnotin.
            assert (forall s, In s Q''l -> In s Q'l). {
                intros s Hs.
                destruct (in_dec str_eq s Q'l) as [? | Hout]; [assumption |].
                exfalso.
                assert (Hle : length Q'l <= length (remove str_eq s Q''l)). {
                  apply NoDup_incl_length. assumption.
                  intros x Hx.
                  apply in_in_remove.
                    intro Hxs. subst. contradiction.
                  now apply Hsubset. }
                assert (Hrm : length (remove str_eq s Q''l) < length Q''l) by
                    (apply remove_length_lt; auto).
                lia. } now apply H0.
            }
            now apply NoDup_incl_length.
        } split. assumption.
        set (vec := fun u => map (fun t => member (u ++ t)) Tl).
        (* vec is injective on Q''l *)
        assert (Hvec_inj : forall u v,
            In u Q''l -> In v Q''l -> vec u = vec v -> u = v). {
            intros u v Hu Hv Heqvec.
            destruct (str_eq u v) as [-> | Huv]; [reflexivity |].
            destruct (sep'' u v); auto;
                try now apply HQ''l.
            intros t Ht.
            apply HTl, In_nth with (d := t) in Ht.
            destruct Ht as (i & Hi & Hnth).
            assert (Hmu : nth_error (vec u) i = Some (member (u ++ t))). {
                unfold vec. rewrite nth_error_map, nth_error_nth' with (d := t); [|lia].
                now rewrite Hnth. }
            assert (Hmv : nth_error (vec v) i = Some (member (v ++ t))). {
                unfold vec. rewrite nth_error_map, nth_error_nth' with (d := t); [|lia].
                now rewrite Hnth. }
            rewrite Heqvec in Hmu. congruence. }
        assert (HND : NoDup (map vec Q''l)). {
            clear - NDQ'' Hvec_inj.
            induction Q''l as [| x xs IHxs].
            - constructor.
            - apply NoDup_cons_iff in NDQ''. destruct NDQ'' as [Hni NDxs].
                constructor.
                + intro HIn. apply in_map_iff in HIn.
                  destruct HIn as (y & Heq & Hyin).
                  replace y with x in * by (apply Hvec_inj; [left; auto | right; auto | auto]).
                  subst. contradiction.
                + apply IHxs; auto.
                  intros u v Hu Hv. apply Hvec_inj; right; auto. }
        rewrite <- length_map with (f := vec).
        apply NoDup_boollist_length. assumption.
        intros v Hv.
        apply in_map_iff in Hv.
        destruct Hv as (u & <- & _).
        unfold vec. apply length_map. }
      eexists. now rewrite Eq'.
Defined.

(** Lemma 3 *)
Lemma union_closed :
    forall Q T
    (sep : separable Q T)
    (finQ : finite Q)
    (finT : finite T),
    { Q' : str -> bool &
        closed Q' T *
        separable Q' T *
        finite Q' *
        (forall s, Q s = true -> Q' s = true) }.
Proof.
    intros Q T sep finQ finT.
    pose proof finT as finT_copy.
    destruct finT as (Tl & NDT & HTl).
    (* fuel = 2^|Tl| bounds the number of T-equivalence classes *)
    set (fuel := S (Nat.pow 2 (length Tl))).
    destruct (loop_terminates fuel Q Q T sep finQ Tl NDT HTl ltac:(auto) ltac:(lia)).
    destruct x as (Q' & ((clos' & sep') & finQ') & sub').
    exists Q'. repeat split; auto.
Defined.

(** The main #L<sup>*</sup># implementation that uses Lemmas 2 and 3 to iteratively
    expand Q and T until the DFA they form encodes L (or fuel runs out).

    If fuel runs out, we return the in-progress DFA *)

Definition num_states (H : HypothesisDFA) : nat :=
    num_states_of_fin _ H.(fin_Q).

(** A hypothesis DFA must be smaller than the number of states in the
    minimal DFA. This follows from separability of Q *)
Lemma num_states_le_min : forall (H : HypothesisDFA),
    num_states H <= L.num_states_in_minimal.
Proof.
  intro H.
  destruct L.exists_dfa as (state_m & D & (Denc & Minimal) & Len).
  (* num_states H <= |states D| by the same injection as the minimality branch *)
  enough (Hle : num_states H <= Datatypes.length (D.states state_m D)) by lia.
  unfold num_states, num_states_of_fin.
  destruct H as [Q0 T0 sep0 clos0 eps0 finQ0 finT0].
  destruct finQ0 as (Ql & NDQl & InQl). simpl.
  set (f := fun q => D.run D q).
  assert (Hinj : forall u v, In u Ql -> In v Ql -> u <> v -> f u <> f v). {
    intros u v Hu Hv Huv Hf.
    apply (sep0 u v); try (now apply InQl); try assumption.
    intros t Ht.
    assert (Hsplit : forall x,
              D.accept_string D (x ++ t)
              = D.(D.accept _) (fold_left D.(D.transition _) t (f x))). {
      intro x. unfold D.accept_string, D.run, f. now rewrite fold_left_app. }
    assert (Hacc : D.accept_string D (u ++ t) = D.accept_string D (v ++ t)). {
      rewrite !Hsplit. unfold f in *. now rewrite Hf. }
    destruct (member (u ++ t)) eqn:Mu, (member (v ++ t)) eqn:Mv;
      try reflexivity; exfalso.
    - assert (D.accept_string D (u ++ t) = true) by (apply Denc; exact Mu).
      assert (D.accept_string D (v ++ t) = true) by (rewrite <- Hacc; assumption).
      assert (member (v ++ t) = true) by (apply Denc; assumption). congruence.
    - assert (D.accept_string D (v ++ t) = true) by (apply Denc; exact Mv).
      assert (D.accept_string D (u ++ t) = true) by (rewrite Hacc; assumption).
      assert (member (u ++ t) = true) by (apply Denc; assumption). congruence.
  }
  rewrite <- (length_map f Ql). apply NoDup_incl_length.
  - clear - NDQl Hinj.
    induction Ql; [constructor|].
    apply NoDup_cons_iff in NDQl. destruct NDQl. constructor.
    + intro HIn. apply in_map_iff in HIn. destruct HIn as (y & Hfy & Hyin).
      replace y with a in *. contradiction.
      destruct (str_eq a y). assumption.
        exfalso. apply (Hinj a y); [now left|now right|assumption|now symmetry].
    + apply IHQl; auto. intros u v Hu Hv. apply Hinj; now right.
  - intros st Hst. apply in_map_iff in Hst.
    destruct Hst as (q & <- & _). apply run_in_states.
Qed.

(** If [make_dfa] has no counterexample then it is minimal. By separability,
    all q : Q reach distinct states in any encoding DFA, so none can have fewer states *)
Lemma make_dfa_minimal : forall (H : HypothesisDFA),
    equiv_query (make_dfa H) = None ->
    minimal (make_dfa H).
Proof.
  intros H Heq.
  unfold minimal. split.
    now apply equiv_query_correct in Heq.
  intros state' dfa' H_encodes.
  assert (H_LHS : Datatypes.length (states _ (make_dfa H)) = num_states H). {
    unfold num_states, num_states_of_fin, make_dfa.
    destruct H, fin_Q0, a. simpl. apply list_with_proof_preserves_len. }
  rewrite H_LHS.
  unfold num_states, num_states_of_fin.
  destruct H as [Q0 T0 sep0 clos0 eps0 finQ0 finT0].
  destruct finQ0 as (Ql & NDQl & InQl). simpl.
  set (f := fun q => D.run dfa' q).
  assert (Hinj : forall u v, In u Ql -> In v Ql -> u <> v -> f u <> f v). {
    intros u v Hu Hv Huv Hf.
    apply (sep0 u v); try (now apply InQl); try assumption.
    intros t Ht.
    assert (Hsplit : forall x,
              D.accept_string dfa' (x ++ t)
              = dfa'.(D.accept _) (fold_left dfa'.(D.transition _) t (f x))). {
      intro x. unfold D.accept_string, D.run, f. now rewrite fold_left_app. }
    assert (Hacc : D.accept_string dfa' (u ++ t) = D.accept_string dfa' (v ++ t)). {
      rewrite Hsplit. unfold f in *. now rewrite Hf. }
    destruct (member (u ++ t)) eqn:Mu, (member (v ++ t)) eqn:Mv;
      try reflexivity; exfalso.
    - assert (D.accept_string dfa' (u ++ t) = true) by (apply H_encodes; exact Mu).
      assert (D.accept_string dfa' (v ++ t) = true) by (rewrite <- Hacc; assumption).
      assert (member (v ++ t) = true) by (apply H_encodes; assumption). congruence.
    - assert (D.accept_string dfa' (v ++ t) = true) by (apply H_encodes; exact Mv).
      assert (D.accept_string dfa' (u ++ t) = true) by (rewrite Hacc; assumption).
      assert (member (u ++ t) = true) by (apply H_encodes; assumption). congruence.
  }
  rewrite <- (length_map f Ql). apply NoDup_incl_length.
    clear - NDQl Hinj.
    induction Ql as [| x xs IH].
      constructor.
    apply NoDup_cons_iff in NDQl. destruct NDQl. constructor.
      intro HIn. apply in_map_iff in HIn. destruct HIn as (y & Hfy & Hyin).
        replace x with y in *. contradiction. symmetry.
        destruct (str_eq x y) as [e | n]; [assumption|].
        exfalso. now apply (Hinj x y); [now left | now right | exact n |].
      apply IH; auto. intros. apply Hinj; now (easy || right).
  intros st Hst. apply in_map_iff in Hst.
    destruct Hst as (q & <- & _). apply run_in_states.
Qed.

(** Once Q has the full minimal state count there is no counterexample left *)
Lemma full_states_no_ce : forall (H : HypothesisDFA),
    L.num_states_in_minimal <= num_states H ->
    equiv_query (make_dfa H) = None.
Proof.
  intros H Hge.
  destruct (equiv_query (make_dfa H)) eqn:Heq; [exfalso | reflexivity].
  assert (Hce : accept_string (make_dfa H) s <> member s)
    by now apply equiv_query_ce.
  destruct (find_separable H s Hce) as
    (q_new & t & HQnew & (sep' & finQ') & finT').
  set (Q' := H.(Q) [q_new := true]).
  set (T' := H.(T) [t := true]).
  destruct (union_closed Q' T' sep' finQ' finT') as
    (Q'' & ((clos'' & sep'') & finQ'') & sub'').
  assert (eps_in_Q'' : Q'' nil = true). {
    apply sub''. unfold Q'. rewrite update_neq.
    - apply H.(eps_in_Q).
    - intro Heq'. subst q_new. now rewrite H.(eps_in_Q) in HQnew. }
  set (H'' := {|
      Q        := Q'';
      T        := T';
      sep      := sep'';
      clos     := clos'';
      eps_in_Q := eps_in_Q'';
      fin_Q    := finQ'';
      fin_T    := finT' |}).
  (* num_states_le_min caps the extended DFA *)
  pose proof (num_states_le_min H'') as Hcap.
  (* The extension has strictly more states than H *)
  pose proof (finite_subset_is_smaller _ _ _ finQ' finQ'' sub'') as Hmono.
  assert (H_step : S (num_states H) <= num_states_of_fin _ finQ'). {
      unfold num_states, num_states_of_fin.
      destruct (fin_Q H) as (fl & NDF & InF),
               finQ' as (fl' & NDF' & InF'),
               H, fin_Q0, a. simpl in *.
      change (S (Datatypes.length fl)) with (Datatypes.length (q_new :: fl)).
      apply NoDup_incl_length. constructor; [|assumption].
          intro C. apply (proj2 (InF q_new)) in C. now rewrite C in HQnew.
      unfold incl. intros y Hy.
      apply (proj1 (InF' y)).
      unfold update, SetLemmas.update. destruct Hy.
          subst y. now destruct (str_eq q_new q_new).
      apply (proj2 (InF y)) in H.
      now destruct (str_eq y q_new). }
  assert (HH'' : num_states H'' = num_states_of_fin _ finQ''). {
    now unfold H'', num_states. }
  unfold num_states in Hge, Hcap.
  destruct H''.
  (* num_states_of_fin finQ' <= num_states_of_fin finQ'' *)
  unfold num_states in *. simpl in *.
  rewrite HH'' in *. lia.
Qed.

(** The main L* implementation *)
Fixpoint lstar_fuel (H : HypothesisDFA) (fuel : nat)
    (LE : L.num_states_in_minimal - num_states H <= fuel)
    : { T : Type & {d : D.t T | minimal d} }.
  destruct (equiv_query (make_dfa H)) eqn:Heq.
  - (* counterexample s - only reachable with fuel = S n *)
    destruct fuel as [| n].
    + (* fuel = 0: impossible.
         LE : num_states_in_minimal - num_states H <= 0, so min <= num_states H,
         and full_states_no_ce then says there is NO counterexample. *)
      exfalso.
      assert (Hge : L.num_states_in_minimal <= num_states H) by lia.
      now rewrite (full_states_no_ce H Hge) in Heq.
    + (* fuel = S n: build a bigger hypothesis DFA and recurse on n *)
      assert (Hce : accept_string (make_dfa H) s <> member s)
        by now apply equiv_query_ce.
      destruct (find_separable H s Hce) as
        (q_new & t & HQnew & (sep' & finQ') & finT').
      set (Q' := H.(Q) [q_new := true]).
      set (T' := H.(T) [t := true]).
      destruct (union_closed Q' T' sep' finQ' finT') as
        (Q'' & ((clos'' & sep'') & finQ'') & sub'').
      assert (eps_in_Q'' : Q'' nil = true). {
        apply sub''. unfold Q'. rewrite update_neq.
        - apply H.(eps_in_Q).
        - intro Heq'. subst q_new. now rewrite H.(eps_in_Q) in HQnew. }
      eapply (lstar_fuel {|
          Q        := Q'';
          T        := T';
          sep      := sep'';
          clos     := clos'';
          eps_in_Q := eps_in_Q'';
          fin_Q    := finQ'';
          fin_T    := finT' |} n).
      match goal with
      | [|- context[_ - num_states ?Dh]] =>
          enough (H_strict : S (num_states H) <= num_states Dh)
      end. lia.
      pose proof (finite_subset_is_smaller _ _ _ finQ' finQ'' sub'').
      assert (H_step : S (num_states H) <= num_states_of_fin _ finQ'). {
          unfold num_states, num_states_of_fin.
          destruct (fin_Q H) as (fl & NDF & InF).
          destruct finQ' as (fl' & NDF' & InF').
          simpl. destruct H, fin_Q0. simpl in *.
          destruct a.
          change (S (Datatypes.length fl)) with (Datatypes.length (q_new :: fl)).
          apply NoDup_incl_length. constructor; [|assumption].
              intro C. apply (proj2 (InF q_new)) in C. now rewrite C in HQnew.
          unfold incl. intros y Hy.
          apply (proj1 (InF' y)).
          unfold update, SetLemmas.update. destruct Hy as [Eq | Iny].
              subst y. now destruct (str_eq q_new q_new) as [e|n'].
          apply (proj2 (InF y)) in Iny.
          now destruct (str_eq y q_new) as [e|n']. }
      unfold num_states at 2.
      etransitivity; eassumption.
  - (* no counterexample: make_dfa H is minimal *)
    exists {q : str | H.(Q) q = true}.
    exists (make_dfa H).
    exact (make_dfa_minimal H Heq).
Defined.

(** The total L* implementation *)
Definition lstar (_ : unit) : { T : Type & {d : D.t T | minimal d} }.
    eapply lstar_fuel with (fuel := num_states_in_minimal).
        lia.
    Unshelve.
    set (Q := fun s => if str_eq s nil then true else false).
    set (T := fun (_ : str) => false).
    eapply (Build_HypothesisDFA Q T); auto;
        unfold T, Q in *.
    - unfold separable, T_equiv. intros. intro Contra.
      now destruct (str_eq u nil), (str_eq v nil); subst.
    - unfold closed, T_equiv. intros. destruct (str_eq q nil); try discriminate.
      subst. exists nil. now split.
    - unfold finite. exists (nil :: nil). split. constructor.
        intro. now inversion H0.
        constructor.
      intros. destruct (str_eq s nil). subst.
        split; auto. intros. now constructor.
      split; intro. discriminate. inversion H0; subst.
      contradiction. inversion H1.
    - unfold finite. exists nil. split. constructor.
      intros. destruct (str_eq s nil). subst.
        split; auto. now intros.
      split; intro. discriminate. inversion H0.
Defined.

End Lstar.
