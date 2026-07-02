(** NL* RFSA learning
    https://lsv.ens-paris-saclay.fr/Publis/RAPPORTS_LSV/PDF/rr-lsv-2008-28.pdf *)
    
#[local] Set Warnings "-intuition-auto-with-star".

From lstar Require Import Automata ListLemmas SetLemmas.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.
From lstar Require Import Teacher.

Module NLstar (s : Symbol) (L : ResidualLanguage s) (Tch : RFSATeacher s L).
Import s L Tch N R.

Definition mem := mem str_eq.
Definition finite := SetLemmas.finite str.

(* row(u)(v) = T(uv) *)
Definition cell (T : str -> bool) (u v : str) : bool := T (u ++ v).

(* Access strings together with their one-letter extensions *)
Definition USigma (Ul : list str) : list str :=
    flat_map (fun u => map (fun a => u ++ [a]) enum) Ul.

Definition row_index (Ul : list str) : list str :=
    Ul ++ USigma Ul.

(* Rows are equal when they agree on every v \in V *)
Definition row_eq (T V : str -> bool) (u1 u2 : str) : Prop :=
    forall v, V v = true -> cell T u1 v = cell T u2 v.

(* Definition 5: the join of two rows at a column *)
Definition join (T : str -> bool) (u1 u2 v : str) : bool :=
    cell T u1 v || cell T u2 v.

(* Definition 7: r is covered by r', r \sqsubseteq r', if for all v \in V, r(v)= true implies r'(v)= true *)
Definition covered (T V : str -> bool) (u1 u2 : str) : Prop :=
    forall v, V v = true -> cell T u1 v = true -> cell T u2 v = true.

(* Definition 7: if, moreover, r \neq r', then r is strictly covered by r', r \sqsubset r' *)
Definition strictly_covered (T V : str -> bool) (u1 u2 : str) : Prop :=
    covered T V u1 u2 /\ ~ row_eq T V u1 u2.

Lemma strict_impl_covered : forall T V u1 u2,
    strictly_covered T V u1 u2 -> covered T V u1 u2.
Proof. intros. now destruct H. Qed.

(* Definition 6: r is composed if there are r1,...,rn \in Rows(T) \ {r} such that r = r1 \sqcup ... \sqcup rn *)
Definition composed (T V : str -> bool) (Ul : list str) (u : str) : Prop :=
    forall v, V v = true ->
        cell T u v = true <->
        exists u', In u' (row_index Ul) /\ strictly_covered T V u' u /\ cell T u' v = true.

(* Otherwise, r is called prime *)
Definition prime (T V : str -> bool) (Ul : list str) (u : str) : Prop :=
    In u (row_index Ul) /\ ~ composed T V Ul u.

(* Covering is decidable relative to an arbitrary column list *)
Lemma covered_on_dec : forall T u1 u2 (vl : list str),
    {forall v, In v vl -> cell T u1 v = true -> cell T u2 v = true}
  + {~ forall v, In v vl -> cell T u1 v = true -> cell T u2 v = true}.
Proof.
    intros. induction vl.
        left. intros. destruct H.
    destruct (Bool.bool_dec (cell T u1 a) true).
    - destruct (Bool.bool_dec (cell T u2 a) true).
      + destruct IHvl.
            left. intros. destruct H; subst; auto.
        right. intro. apply n. intros. apply H; auto. now right.
      + right. intro. apply n. apply H; [now left | assumption].
    - destruct IHvl.
        left. intros. destruct H; subst; [congruence | auto].
      right. intro. apply n0. intros. apply H; auto. now right.
Defined.

(* Covering is decidable for finite V *)
Lemma covered_dec : forall T V u1 u2,
    finite V -> {covered T V u1 u2} + {~ covered T V u1 u2}.
Proof.
    intros T V u1 u2 finV. unfold covered.
    destruct finV as (vl & _ & Hv).
    destruct (covered_on_dec T u1 u2 vl).
    - left. intros. apply e; auto. now apply Hv.
    - right. intro. apply n. intros. apply H; auto. now apply Hv.
Defined.

(* Row equality is decidable relative to an arbitrary column list *)
Lemma row_eq_on_dec : forall T u1 u2 (vl : list str),
    {forall v, In v vl -> cell T u1 v = cell T u2 v}
  + {~ forall v, In v vl -> cell T u1 v = cell T u2 v}.
Proof.
    intros. induction vl.
        left. intros. destruct H.
    destruct (Bool.bool_dec (cell T u1 a) (cell T u2 a)).
    - destruct IHvl.
        left. intros. destruct H; subst; auto.
      right. intro. apply n. intros. apply H. now right.
    - right. intro. apply n, H. now left.
Defined.

(* Row equality is decidable for finite V *)
Lemma row_eq_dec : forall T V u1 u2,
    finite V -> {row_eq T V u1 u2} + {~ row_eq T V u1 u2}.
Proof.
    intros T V u1 u2 finV. unfold row_eq.
    destruct finV as (vl & _ & Hv).
    destruct (row_eq_on_dec T u1 u2 vl).
    - left. intros. apply e. now apply Hv.
    - right. intro. apply n. intros. apply H. now apply Hv.
Defined.

(* Strict covering is decidable for finite V *)
Lemma strictly_covered_dec : forall T V u1 u2,
    finite V -> {strictly_covered T V u1 u2} + {~ strictly_covered T V u1 u2}.
Proof.
    intros T V u1 u2 finV. unfold strictly_covered.
    destruct (covered_dec T V u1 u2 finV).
    - destruct (row_eq_dec T V u1 u2 finV).
        right. now intros.
      now left.
    - right. now intros.
Defined.

(* Composedness is decidable over an arbitrary row list *)
Lemma composed_witness_dec : forall T V u v (rl : list str),
    finite V ->
    {u' | In u' rl /\ strictly_covered T V u' u /\ cell T u' v = true}
  + {~ exists u', In u' rl /\ strictly_covered T V u' u /\ cell T u' v = true}.
Proof.
    intros T V u v rl finV. induction rl.
        right. intro Contra. destruct Contra, H. inversion H.
    destruct (strictly_covered_dec T V a u finV).
    - destruct (Bool.bool_dec (cell T a v) true).
        left. exists a. split; [now left | now split].
      destruct IHrl.
        left. destruct s0. exists x. split; [now right | intuition].
      right. intro Contra. destruct Contra, H, H0. destruct H.
        subst. congruence.
      apply n0. exists x. auto.
    - destruct IHrl.
        left. destruct s. exists x. split; [now right | intuition].
      right. intro Contra. destruct Contra, H, H0. destruct H.
        now subst.
      apply n0. exists x. auto.
Defined.

(* Composedness is decidable on an arbitrary column list *)
Lemma composed_on_dec : forall T V Ul u (vl : list str),
    finite V ->
    {forall v, In v vl ->
        cell T u v = true <->
        exists u', In u' (row_index Ul) /\ strictly_covered T V u' u /\ cell T u' v = true}
  + {~ forall v, In v vl ->
        cell T u v = true <->
        exists u', In u' (row_index Ul) /\ strictly_covered T V u' u /\ cell T u' v = true}.
Proof.
    intros T V Ul u vl finV. induction vl.
        left. intros. destruct H.
    destruct (composed_witness_dec T V u a (row_index Ul) finV).
    - destruct (Bool.bool_dec (cell T u a) true).
      + destruct IHvl.
            destruct s, a0, H0.
            left. intros. destruct H2; [subst; split; eauto | auto].
        right. intro. apply n. intros. apply H. now right.
      + right. intro. apply n. exfalso. specialize (H a (or_introl eq_refl)).
        destruct s, a0, H1. apply n, H. eauto.
    - destruct (Bool.bool_dec (cell T u a) true).
        right. intro. apply n. exfalso. specialize (H a (or_introl eq_refl)). intuition.
      destruct IHvl.
        left. intros. destruct H.
            subst. intuition.
        now apply i.
      right. intro. apply n1. intros. apply H. now right.
Defined.

(* Composedness is decidable for finite V *)
Lemma composed_dec : forall T V Ul u,
    finite V -> {composed T V Ul u} + {~ composed T V Ul u}.
Proof.
    intros T V Ul u finV. unfold composed.
    destruct finV as (vl & ND & Hv).
    destruct (composed_on_dec T V Ul u vl (exist _ vl (conj ND Hv))).
    - left. intros. apply i. now apply Hv.
    - right. intro. apply n. intros. apply H. now apply Hv.
Defined.

(* Primeness is decidable for finite V *)
Lemma prime_dec : forall T V Ul u,
    finite V -> {prime T V Ul u} + {~ prime T V Ul u}.
Proof.
    intros T V Ul u finV. unfold prime.
    destruct (in_dec str_eq u (row_index Ul)).
    - destruct (composed_dec T V Ul u finV).
        right. now intros (_ & ?).
      left. now split.
    - right. now intros (? & _).
Defined.

(* Primes_upp(T) = Primes(T) \cap Rows_upp(T) *)
Definition prime_reps (T V : str -> bool) (Ul : list str) (finV : finite V) : list str :=
    filter (fun u => if prime_dec T V Ul u finV then true else false) Ul.

(* Prime representatives lie in the upper part U *)
Lemma prime_reps_upper : forall T V Ul finV u,
    In u (prime_reps T V Ul finV) -> In u Ul.
Proof.
    intros. apply filter_In in H. now destruct H.
Qed.

(* Prime representatives are prime rows *)
Lemma prime_reps_prime : forall T V Ul finV u,
    In u (prime_reps T V Ul finV) -> prime T V Ul u.
Proof.
    intros. apply filter_In in H. destruct H. now destruct (prime_dec T V Ul u finV).
Qed.

(* Prime representatives are row indices *)
Lemma prime_reps_index : forall T V Ul finV u,
    In u (prime_reps T V Ul finV) -> In u (row_index Ul).
Proof.
    intros T V Ul finV u H. unfold prime_reps in H.
    apply filter_In in H. destruct H.
    unfold row_index. apply in_or_app. now left.
Qed.

(* Definition 10: \delta(row(u),a) = {r \in Q | r \sqsubseteq row(ua)} *)
Definition cover_set (T V : str -> bool) (Ul : list str) (finV : finite V) (u : str)
    : list str :=
    filter (fun p => if covered_dec T V p u finV then true else false)
           (prime_reps T V Ul finV).

(* Members of a cover set are prime representatives *)
Lemma cover_set_prime_reps : forall T V Ul finV u p,
    In p (cover_set T V Ul finV u) -> In p (prime_reps T V Ul finV).
Proof.
    intros. apply filter_In in H. now destruct H.
Qed.

(* Definition 8: r = \sqcup {r' \in Primes_upp(T) | r' \sqsubseteq r} *)
Definition closed_row (T V : str -> bool) (Ul : list str) (u : str) : Prop :=
    forall v, V v = true ->
        cell T u v = true <->
        exists u', In u' Ul /\ prime T V Ul u' /\ covered T V u' u /\ cell T u' v = true.

(* Closedness at a column is decidable over an arbitrary upper list *)
Lemma closed_witness_dec : forall T V Ul u v (ul : list str),
    finite V ->
    {u' | In u' ul /\ prime T V Ul u' /\ covered T V u' u /\ cell T u' v = true}
  + {~ exists u', In u' ul /\ prime T V Ul u' /\ covered T V u' u /\ cell T u' v = true}.
Proof.
    intros T V Ul u v ul finV. induction ul.
        right. intro Contra. destruct Contra, H. inversion H.
    destruct (prime_dec T V Ul a finV).
    - destruct (covered_dec T V a u finV).
      + destruct (Bool.bool_dec (cell T a v) true).
          left. exists a. intuition.
        destruct IHul.
          left. destruct s. exists x. split; [now right | intuition].
        right. intro Contra. destruct Contra, H, H0, H1, H.
          now subst.
        apply n0. eauto.
      + destruct IHul.
          left. destruct s. exists x. split; [now right | intuition].
        right. intro Contra. destruct Contra, H, H0, H1, H.
          now subst.
        apply n0. eauto.
    - destruct IHul.
        left. destruct s. exists x. split; [now right | intuition].
      right. intro Contra. destruct Contra, H, H0, H.
        now subst.
      apply n0. eauto.
Defined.

(* Closedness of one row on an arbitrary column list is decidable *)
Lemma closed_row_on_dec : forall T V Ul u (vl : list str),
    finite V ->
    {forall v, In v vl ->
        cell T u v = true <->
        exists u', In u' Ul /\ prime T V Ul u' /\ covered T V u' u /\ cell T u' v = true}
  + {~ forall v, In v vl ->
        cell T u v = true <->
        exists u', In u' Ul /\ prime T V Ul u' /\ covered T V u' u /\ cell T u' v = true}.
Proof.
    intros T V Ul u vl finV. induction vl.
        left. intros. destruct H.
    destruct (closed_witness_dec T V Ul u a Ul finV).
    - destruct (Bool.bool_dec (cell T u a) true).
      + destruct IHvl.
            left. intros. destruct H; [subst; split; eauto | auto].
            destruct s, a, H0, H1. eauto.
        right. intro. apply n. intros. apply H. now right.
      + right. intro. apply n. exfalso. specialize (H a (or_introl eq_refl)).
        destruct s, a0, H1, H2. apply n, H. eauto.
    - destruct (Bool.bool_dec (cell T u a) true).
        right. intro. apply n. exfalso. specialize (H a (or_introl eq_refl)). intuition.
      destruct IHvl.
        left. intros. destruct H.
            subst. intuition.
        now apply i.
      right. intro. apply n1. intros. apply H. now right.
Defined.

(* Closedness of one row is decidable for finite V *)
Lemma closed_row_dec : forall T V Ul u,
    finite V -> {closed_row T V Ul u} + {~ closed_row T V Ul u}.
Proof.
    intros T V Ul u finV. unfold closed_row.
    destruct finV as (vl & ND & Hv).
    destruct (closed_row_on_dec T V Ul u vl (exist _ vl (conj ND Hv))).
    - left. intros. apply i. now apply Hv.
    - right. intro. apply n. intros. apply H. now apply Hv.
Defined.

(* Definition 8: T is RFSA-closed if, for each r \in Rows_low(T), r = \sqcup {r' \in Primes_upp(T) | r' \sqsubseteq r} *)
Definition closed (T V : str -> bool) {U} (Ul : finite U) : Prop :=
    forall u, In u (row_index (proj1_sig Ul)) -> closed_row T V (proj1_sig Ul) u.

(* RFSA-closedness is decidable, returning a witness row when it fails *)
Lemma closed_dec : forall T V U
    (fin_U : finite U),
    finite V ->
    closed T V fin_U + {u : str | In u (row_index (proj1_sig fin_U)) /\ ~ closed_row T V (proj1_sig fin_U) u}.
Proof.
    intros T V U fin_U finV. unfold closed.
    induction (row_index _).
        left. intros. destruct H.
    destruct (closed_row_dec T V (proj1_sig fin_U) a finV).
    - destruct IHl.
        left. intros. destruct H; auto; now subst.
      right. destruct s, a0. eexists. split. right. eassumption. assumption.
    - right. exists a. split; [now left | assumption].
Defined.

(* Definition 9: for all u,u' \in U and a \in \Sigma, row(u') \sqsubseteq row(u) implies row(u'a) \sqsubseteq row(ua) *)
Definition rfsa_consistent (T V : str -> bool) {U} (Ul : finite U) : Prop :=
    forall u u' a,
        In u (row_index (proj1_sig Ul)) -> In u' (row_index (proj1_sig Ul)) -> In a enum ->
        covered T V u u' -> covered T V (u ++ [a]) (u' ++ [a]).

(* One consistency triple is decidable *)
Lemma consistent_triple_dec : forall T V u u' a,
    finite V ->
    {covered T V u u' -> covered T V (u ++ [a]) (u' ++ [a])} +
    {~ (covered T V u u' -> covered T V (u ++ [a]) (u' ++ [a]))}.
Proof.
    intros T V u u' a finV. destruct (covered_dec T V u u' finV).
    - destruct (covered_dec T V (u ++ [a]) (u' ++ [a]) finV).
        left. now intros.
      right. intro Contra. auto.
    - left. now intros.
Defined.

(* Consistency is decidable for over an arbitrary list *)
Lemma consistent_row_a_dec : forall T V u a (us : list str),
    finite V ->
    (forall u', In u' us -> covered T V u u' -> covered T V (u ++ [a]) (u' ++ [a]))
    + {u' : str | In u' us /\ ~ (covered T V u u' -> covered T V (u ++ [a]) (u' ++ [a]))}.
Proof.
    intros T V u a us finV. induction us.
        left. intros. destruct H.
    destruct (consistent_triple_dec T V u a0 a finV).
    - destruct IHus.
        left. intros. destruct H; subst; auto.
      right. destruct s. exists x. intuition.
    - right. exists a0. intuition.
Defined.

(* Consistency is decidable for an arbitrary list and all letters *)
Lemma consistent_row_dec : forall T V u (us : list str),
    finite V ->
    (forall u' a, In u' us -> In a enum -> covered T V u u' -> covered T V (u ++ [a]) (u' ++ [a]))
    + {p : str * s.t | let '(u', a) := p in
        In u' us /\ In a enum /\ ~ (covered T V u u' -> covered T V (u ++ [a]) (u' ++ [a]))}.
Proof.
    intros T V u us finV. induction enum.
        left. intros. destruct H0.
    destruct (consistent_row_a_dec T V u a us finV).
    - destruct IHl.
        left. intros. destruct H0; subst; auto.
      right. destruct s, x. exists (s, t0). intuition.
    - right. destruct s, a0. exists (x, a). intuition.
Defined.

(* Consistency over an arbitrary list is decidable *)
Lemma consistent_outer_dec : forall T V Ul (us : list str),
    finite V ->
    (forall u u' a, In u us -> In u' Ul -> In a enum -> covered T V u u' -> covered T V (u ++ [a]) (u' ++ [a]))
    + {p : str * str * s.t | let '(u, u', a) := p in
        In u us /\ In u' Ul /\ In a enum /\ ~ (covered T V u u' -> covered T V (u ++ [a]) (u' ++ [a]))}.
Proof.
    intros T V Ul us finV. induction us.
        left. intros. destruct H.
    destruct (consistent_row_dec T V a Ul finV).
    - destruct IHus.
        left. intros. destruct H; subst; auto.
      right. destruct s, x, p. exists (s, s0, t0). intuition.
    - right. destruct s, x. exists (a, s, t0). intuition.
Defined.

(* RFSA-consistency is decidable, returning a violating triple when it fails *)
Lemma rfsa_consistent_dec : forall T V {U} (Ul : finite U),
    finite V ->
    rfsa_consistent T V Ul
    + {p : str * str * s.t | let '(u, u', a) := p in
        In u (row_index (proj1_sig Ul)) /\ In u' (row_index (proj1_sig Ul)) /\ In a enum
        /\ ~ (covered T V u u' -> covered T V (u ++ [a]) (u' ++ [a]))}.
Proof.
    intros T V U Ul finV. unfold rfsa_consistent.
    destruct (consistent_outer_dec T V (row_index (proj1_sig Ul)) (row_index (proj1_sig Ul)) finV); auto.
Defined.

(* Definition 10: a table T=(T,U,V) with prefix-closed U and suffix-closed V that is
   RFSA-closed and RFSA-consistent, after Lstar's HypothesisDFA *)
Record HypothesisRFSA : Type := {
  T    : str -> bool;
  U    : str -> bool;
  V    : str -> bool;
  fin_U : finite U;
  fin_V : finite V;
  clos : closed T V fin_U;
  cons : rfsa_consistent T V fin_U;
  (* "U prefix-closed" *)
  pref : forall w w', U (w ++ w') = true -> U w = true;
  (* "V is always suffix-closed" *)
  suff : forall w w', V (w ++ w') = true -> V w' = true;
  (* "U and V are both initialized to {\epsilon}" *)
  eps_U : U [] = true;
  eps_V : V [] = true;
}.

(* Upper access strings of the table *)
Definition Ul (H : HypothesisRFSA) : list str := proj1_sig H.(fin_U).

(* Q = Primes_upp(T) *)
Definition memr (H : HypothesisRFSA) (q : str) : bool :=
    mem q (prime_reps H.(T) H.(V) (Ul H) H.(fin_V)).

(* Cover-set elements are states *)
Lemma cover_set_memr : forall H u p,
    In p (cover_set H.(T) H.(V) (Ul H) H.(fin_V) u) -> memr H p = true.
Proof.
    intros. apply mem_In. now apply (cover_set_prime_reps _ _ _ _ u).
Qed.

Lemma bool_eq_proof_irrel : forall H q (H1 H2 : memr H q = true),
    H1 = H2.
Proof. intros. apply UIP_dec, Bool.bool_dec. Qed.

Lemma states_proof_irrel : forall H q' Hq1 Hq2,
    exist (fun q : str => memr H q = true) q' Hq1 = exist (fun q : str => memr H q = true) q' Hq2.
Proof. intros. f_equal. apply bool_eq_proof_irrel. Qed.

(* RT = (Q,Q0,F,\delta) with Q = Primes_upp(T), Q0 = {r \in Q | r \sqsubseteq row(\epsilon)},
   F = {r \in Q | r(\epsilon)= true}, \delta(row(u),a) = {r \in Q | r \sqsubseteq row(ua)} *)
Definition make_nfa (H : HypothesisRFSA) : N.t { q | memr H q = true }.
    set (state := { q | memr H q = true }).
    set (Pr := prime_reps H.(T) H.(V) (Ul H) H.(fin_V)).
    assert (initial : list state). {
        refine (list_with_proof (cover_set H.(T) H.(V) (Ul H) H.(fin_V) [])
                  (fun q => memr H q = true) _).
        intros x Hx. now apply (cover_set_memr H []). }
    assert (transition : state -> s.t -> list state). {
        intros q a.
        refine (list_with_proof (cover_set H.(T) H.(V) (Ul H) H.(fin_V) (proj1_sig q ++ [a]))
                  (fun q' => memr H q' = true) _).
        intros x Hx. now apply (cover_set_memr H (proj1_sig q ++ [a])). }
    set (accept := fun (q : state) => H.(T) (proj1_sig q)).
    assert (mempf : forall x, In x Pr -> memr H x = true)
        by (intros x Hx; now apply mem_In).
    set (ls := list_with_proof Pr (fun q => memr H q = true) mempf).
    refine {| initial    := initial;
              transition := transition;
              accept     := accept;
              states     := ls;
              states_complete := _ |}.
    intros w q Hq.
    assert (Hin : In (proj1_sig q) Pr)
        by apply (mem_In str_eq), (proj2_sig q).
    assert (Heq : q = exist _ (proj1_sig q) (mempf (proj1_sig q) Hin)). {
        destruct q as (q' & Hq'); simpl.
        apply states_proof_irrel. }
    rewrite Heq.
    apply (list_with_proof_complete Pr (fun q => memr H q = true) (bool_eq_proof_irrel H)).
Defined.

(* Covering is reflexive *)
Lemma covered_refl : forall T V u, covered T V u u.
Proof. unfold covered. auto. Qed.

(* Covering is transitive *)
Lemma covered_trans : forall T V a b c,
    covered T V a b -> covered T V b c -> covered T V a c.
Proof.
    unfold covered. intros. apply H0; auto.
Qed.

(* Access strings are row indices *)
Lemma state_row_index : forall H (q : { q | memr H q = true }),
    In (proj1_sig q) (row_index (Ul H)).
Proof.
    intros. eapply prime_reps_index, mem_In. destruct q. eauto.
Qed.

(* Lemma 1: "For all u \in U and r \in \delta(Q0,u), we have r \sqsubseteq row(u)" *)
Lemma run_covered : forall H u r,
    H.(U) u = true ->
    In r (run (make_nfa H) u) ->
    covered H.(T) H.(V) (proj1_sig r) u.
Proof.
    intros H u. induction u using rev_ind; intros r Hu Hr.
    - unfold run, run_from in Hr. simpl in Hr.
      unfold make_nfa in Hr. simpl in Hr.
      apply in_list_with_proof in Hr.
      apply filter_In in Hr. destruct Hr as (_ & Hcov).
      now destruct (covered_dec H.(T) H.(V) (proj1_sig r) [] H.(fin_V)).
    - unfold run in Hr. unfold run_from in Hr.
      rewrite fold_left_app in Hr. simpl in Hr.
      unfold step in Hr. apply in_flat_map in Hr.
      destruct Hr as (q & Hq & Hr).
      assert (HUu : H.(U) u = true) by (now apply (H.(pref) u [x])).
      assert (Hqu : covered H.(T) H.(V) (proj1_sig q) u) by auto.
      unfold make_nfa in Hr. simpl in Hr.
      apply in_list_with_proof in Hr.
      apply filter_In in Hr. destruct Hr as (_ & Hcovr).
      assert (Hrq : covered H.(T) H.(V) (proj1_sig r) (proj1_sig q ++ [x]))
        by now destruct (covered_dec H.(T) H.(V) (proj1_sig r) (proj1_sig q ++ [x]) H.(fin_V)).
      assert (Hqx : covered H.(T) H.(V) (proj1_sig q ++ [x]) (u ++ [x])). {
          apply (H.(cons)); auto.
            apply state_row_index.
            unfold row_index. apply in_or_app. left.
              now apply (proj1 (proj2 (proj2_sig H.(fin_U)) u)).
            apply t_enumerable. }
      now apply (covered_trans _ _ _ _ _ Hrq Hqx).
Qed.

(* Cell distributes over a leading column symbol *)
Lemma cell_app : forall T u a v,
    cell T u (a :: v) = cell T (u ++ [a]) v.
Proof. intros. unfold cell. now rewrite <- app_assoc. Qed.

(* F = {r \in Q | r(\epsilon)= true} *)
Lemma accept_cell : forall H q,
    accept _ (make_nfa H) q = cell H.(T) (proj1_sig q) [].
Proof. intros. unfold cell. now rewrite app_nil_r. Qed.

(* Pointwise closedness *)
Lemma cover_set_cell : forall H w v,
    In w (row_index (Ul H)) ->
    H.(V) v = true ->
    (exists p, In p (cover_set H.(T) H.(V) (Ul H) H.(fin_V) w) /\ cell H.(T) p v = true) <-> cell H.(T) w v = true.
Proof.
    intros H w v Hw Hv. split.
    - intros (p & Hp & Hpv).
      apply filter_In in Hp. destruct Hp as (_ & Hcov).
      destruct (covered_dec H.(T) H.(V) p w H.(fin_V)) as [Hc |]; [| discriminate].
      now apply (Hc v Hv).
    - intro Hwv. destruct (H.(clos) w Hw v Hv) as (Hfwd & _).
      destruct (Hfwd Hwv) as (u' & Hu' & Hprime & Hcovu' & Hu'v).
      exists u'. split; [| assumption].
      apply filter_In. split.
        unfold prime_reps. apply filter_In. split; [assumption |].
          now destruct (prime_dec H.(T) H.(V) (Ul H) u' H.(fin_V)).
        now destruct (covered_dec H.(T) H.(V) u' w H.(fin_V)).
Qed.

(* Access strings lie in the upper part *)
Lemma state_upper : forall H (q : { q | memr H q = true }),
    In (proj1_sig q) (Ul H).
Proof.
    intros. apply (prime_reps_upper H.(T) H.(V) (Ul H) H.(fin_V)).
    apply (mem_In str_eq). now destruct q.
Qed.

(* Access strings of states lie in U *)
Lemma state_U : forall H (q : { q | memr H q = true }),
    H.(U) (proj1_sig q) = true.
Proof.
    intros. destruct H, fin_U0, a. apply i, state_upper.
Qed.

(* Running v from a set accepts iff cell(q)(v) = true for some start state q *)
Lemma run_from_set_accept : forall H v qs,
    H.(V) v = true ->
    (forall q, In q qs -> In (proj1_sig q) (Ul H)) ->
    existsb (accept _ (make_nfa H)) (run_from (make_nfa H) qs v) = true
    <-> exists q, In q qs /\ cell H.(T) (proj1_sig q) v = true.
Proof.
    intros H v. induction v; intros qs Hv Hup.
    - simpl. rewrite existsb_exists. split.
      + intros (q & Hq & Ha). exists q. split; auto.
        now rewrite <- accept_cell.
      + intros (q & Hq & Hc). exists q. split; auto.
        unfold cell in Hc. now rewrite app_nil_r in Hc.
    - assert (Hv' : H.(V) v = true) by (now apply (H.(suff) [a] v)).
      unfold run_from in *. simpl.
      fold (run_from (make_nfa H) (step (transition _ (make_nfa H)) qs a) v).
      rewrite IHv; auto.
      + split.
        * intros (p & Hp & Hpv).
          unfold step in Hp. apply in_flat_map in Hp.
          destruct Hp as (q & Hq & Hp).
          exists q. split; auto.
          rewrite cell_app.
          apply (cover_set_cell H (proj1_sig q ++ [a]) v); auto.
            unfold row_index. apply in_or_app. right.
            unfold USigma. apply in_flat_map. exists (proj1_sig q). split.
                now apply Hup.
            change (proj1_sig q ++ [a]) with ((fun a0 => proj1_sig q ++ [a0]) a).
            apply in_map, t_enumerable.
          exists (proj1_sig p). split; [| assumption].
          now apply in_list_with_proof in Hp.
        * intros (q & Hq & Hqv).
          rewrite cell_app in Hqv.
          assert (Hwu : In (proj1_sig q ++ [a]) (USigma (Ul H))).
          { unfold USigma. apply in_flat_map. exists (proj1_sig q).
            split.
                now apply Hup.
                change (proj1_sig q ++ [a]) with ((fun a0 => proj1_sig q ++ [a0]) a).
                apply in_map, t_enumerable. }
          assert (Hwr : In (proj1_sig q ++ [a]) (row_index (Ul H)))
                by (unfold row_index; apply in_or_app; now right).
          apply (cover_set_cell H (proj1_sig q ++ [a]) v Hwr Hv') in Hqv.
          destruct Hqv as (p & Hp & Hpv).
          exists (exist _ p (cover_set_memr H (proj1_sig q ++ [a]) p Hp)). split; auto.
            unfold step. apply in_flat_map. exists q. split; [assumption|].
            apply (list_with_proof_complete _ _ (bool_eq_proof_irrel H)).
      + intros p Hp. unfold step in Hp. apply in_flat_map in Hp.
        destruct Hp as (q & Hq & Hp).
        apply in_list_with_proof in Hp.
        apply (prime_reps_upper H.(T) H.(V) (Ul H) H.(fin_V)).
        now apply (cover_set_prime_reps _ _ _ _ (proj1_sig q ++ [a])).
Qed.

(* Lemma 2: "(1) r(v)= true iff v \in Lr, and (2) row(\epsilon)(v)= true iff v \in L(RT)" *)
Lemma row_state_lang : forall H (r : { q | memr H q = true }) v,
    H.(V) v = true ->
    (cell H.(T) (proj1_sig r) v = true <-> N.L_state (make_nfa H) r v = true) /\
    (cell H.(T) [] v = true <-> N.L_aut (make_nfa H) v = true).
Proof.
    intros H r v Hv. split.
    - unfold N.L_state.
      rewrite (run_from_set_accept H v [r] Hv).
      + split.
          intro Hc. exists r. split. now left. assumption.
        now intros (q & [<- | []] & Hc).
      + intros q [<- | []]. apply state_upper.
    - unfold N.L_aut, N.accept_string, run.
      rewrite (run_from_set_accept H v (N.initial _ (make_nfa H)) Hv).
      + unfold make_nfa. simpl. rewrite <- cover_set_cell; auto.
        * split.
            intros (q & Hq & Hc).
              exists (exist _ q (cover_set_memr H [] q Hq)). split.
                apply (list_with_proof_complete _ _ (bool_eq_proof_irrel H)).
                assumption.
            intros (q & Hq & Hc).
              apply in_list_with_proof in Hq.
              now exists (proj1_sig q).
        * unfold row_index, Ul. apply in_or_app. left.
          destruct H, fin_U0, a; simpl in *. now apply i.
      + intros q Hq.
        unfold make_nfa in Hq. cbn [N.initial] in Hq.
        apply in_list_with_proof in Hq.
        apply (prime_reps_upper H.(T) H.(V) (Ul H) H.(fin_V)).
        now apply (cover_set_prime_reps _ _ _ _ []).
Qed.

(* Covering of start sets is preserved by running *)
Lemma run_from_mono : forall H w qs1 qs2,
    (forall q1, In q1 qs1 -> In (proj1_sig q1) (Ul H)) ->
    (forall q2, In q2 qs2 -> In (proj1_sig q2) (Ul H)) ->
    (forall q1, In q1 qs1 ->
        exists q2, In q2 qs2 /\ covered H.(T) H.(V) (proj1_sig q1) (proj1_sig q2)) ->
    existsb (accept _ (make_nfa H)) (run_from (make_nfa H) qs1 w) = true ->
    existsb (accept _ (make_nfa H)) (run_from (make_nfa H) qs2 w) = true.
Proof.
    intros H w. induction w; intros qs1 qs2 Hup1 Hup2 Hmono Hacc.
    - simpl in *. rewrite existsb_exists in *.
      destruct Hacc as (q1 & Hq1 & Ha1).
      destruct (Hmono q1 Hq1) as (q2 & Hq2 & Hcov).
      exists q2. split; [assumption |].
      unfold covered, cell in Hcov.
      specialize (Hcov [] H.(eps_V)). repeat rewrite app_nil_r in Hcov. auto.
    - unfold run_from in *. simpl in *.
      fold (run_from (make_nfa H) (step (transition _ (make_nfa H)) qs1 a) w) in Hacc.
      fold (run_from (make_nfa H) (step (transition _ (make_nfa H)) qs2 a) w).
      apply (IHw (step (transition _ (make_nfa H)) qs1 a)
                 (step (transition _ (make_nfa H)) qs2 a)); auto.
      + intros p Hp. unfold step in Hp. apply in_flat_map in Hp.
        destruct Hp as (q & Hq & Hp). apply in_list_with_proof in Hp.
        eapply prime_reps_upper, cover_set_prime_reps. eassumption.
      + intros p Hp. unfold step in Hp. apply in_flat_map in Hp.
        destruct Hp as (q & Hq & Hp). apply in_list_with_proof in Hp.
        eapply prime_reps_upper, cover_set_prime_reps. eassumption.
      + intros p1 Hp1. unfold step in Hp1. apply in_flat_map in Hp1.
        destruct Hp1 as (q1 & Hq1 & Hp1).
        apply in_list_with_proof in Hp1.
        apply filter_In in Hp1. destruct Hp1 as (Hp1pr & Hp1cov).
        destruct (covered_dec H.(T) H.(V) (proj1_sig p1) (proj1_sig q1 ++ [a]) H.(fin_V))
          as [Hcov1 |]; [| discriminate].
        destruct (Hmono q1 Hq1) as (q2 & Hq2 & Hcovq).
        assert (Hq1U : In (proj1_sig q1) (row_index (Ul H)))
          by (unfold row_index; apply in_or_app; left; now apply Hup1).
        assert (Hq2U : In (proj1_sig q2) (row_index (Ul H)))
          by (unfold row_index; apply in_or_app; left; now apply Hup2).
        assert (Hlift : covered H.(T) H.(V) (proj1_sig q1 ++ [a]) (proj1_sig q2 ++ [a]))
          by (apply (H.(cons)); auto using t_enumerable).
        assert (Hp1cov2 : covered H.(T) H.(V) (proj1_sig p1) (proj1_sig q2 ++ [a]))
          by (apply (covered_trans _ _ _ _ _ Hcov1 Hlift)).
        assert (Hp1mem : In (proj1_sig p1)
                  (cover_set H.(T) H.(V) (Ul H) H.(fin_V) (proj1_sig q2 ++ [a]))).
        { apply filter_In. split.
            assumption.
          now destruct (covered_dec H.(T) H.(V) (proj1_sig p1) (proj1_sig q2 ++ [a]) H.(fin_V)). }
        exists p1. split; [| apply covered_refl].
        unfold step. apply in_flat_map. exists q2. split; [assumption |].
        replace p1 with (exist (fun q => memr H q = true) (proj1_sig p1)
                           (cover_set_memr H (proj1_sig q2 ++ [a]) (proj1_sig p1) Hp1mem)).
        apply (list_with_proof_complete _ _ (bool_eq_proof_irrel H)).
        destruct p1 as (p1v & p1pf). simpl.
        apply states_proof_irrel.
Qed.

(* Lemma 3: "For every r1,r2 \in Q, r1 \sqsubseteq r2 iff Lr1 \subseteq Lr2" *)
Lemma covered_iff_lang_incl : forall H u1 u2
    (p1 : memr H u1 = true) (p2 : memr H u2 = true),
    covered H.(T) H.(V) u1 u2
    <-> (forall w, N.L_state (make_nfa H) (exist _ u1 p1) w = true ->
                   N.L_state (make_nfa H) (exist _ u2 p2) w = true).
Proof.
    intros. split.
    - intros Hcov w Hw. eapply run_from_mono; eauto;
        intros q [<- | []]; eauto using state_upper.
      exists (exist _ u2 p2). split. now left. assumption.
    - repeat intro.
      destruct (row_state_lang H (exist _ u1 p1) v H1) as ((Hf1 & _) & _).
      destruct (row_state_lang H (exist _ u2 p2) v H1) as ((_ & Hb2) & _). auto.
Qed.

(* Definition 11: "RT is consistent with T if, for all w \in (U \cup U\Sigma)V, T(w)= true iff w \in L(RT)" *)
Definition consistent (H : HypothesisRFSA) : Prop :=
    forall u v, In u (row_index (Ul H)) -> H.(V) v = true ->
        cell H.(T) u v = true <-> N.L_aut (make_nfa H) (u ++ v) = true.

(* running uv is running v from the states reached after u *)
Lemma run_from_app : forall H u v qs,
    run_from (make_nfa H) qs (u ++ v)
    = run_from (make_nfa H) (run_from (make_nfa H) qs u) v.
Proof. intros. unfold run_from. now rewrite fold_left_app. Qed.

(* If the composed condition fails on the finite column list, some column in the
   list witnesses the failure *)
Lemma composed_fail_column : forall H u (vl : list str),
    (forall v, In v vl -> H.(V) v = true) ->
    ~ (forall v, In v vl ->
        cell H.(T) u v = true <->
        exists u', In u' (row_index (Ul H)) /\ strictly_covered H.(T) H.(V) u' u /\ cell H.(T) u' v = true) ->
    exists v, In v vl /\ H.(V) v = true /\
        ~ (cell H.(T) u v = true <->
           exists u', In u' (row_index (Ul H)) /\ strictly_covered H.(T) H.(V) u' u /\ cell H.(T) u' v = true).
Proof.
    induction vl; intros.
        destruct H1. intros. inversion H1.
    destruct (Bool.bool_dec (cell H.(T) u a) true).
    - destruct (composed_witness_dec H.(T) H.(V) u a (row_index (Ul H)) H.(fin_V)).
      + destruct (IHvl ltac:(intuition)) as (v & Hv & HvV & Hfail).
          intro Hall. apply H1. intros w Hw. destruct Hw as [<- | Hw].
            split.
                intro. destruct s as (u' & Hu'). eauto.
              auto.
            now apply Hall.
        exists v. split.
            now right.
            easy.
      + exists a. split. now left. split.
            apply H0. now left.
        intro Hiff. now apply n, Hiff.
    - destruct (composed_witness_dec H.(T) H.(V) u a (row_index (Ul H)) H.(fin_V)).
      + exists a. split. now left. split. apply H0. now left.
        intro Hiff. apply n, Hiff. destruct s. eauto.
      + destruct IHvl as (v & Hv & HvV & Hfail).
            intros v Hv. apply H0. now right.
          intro Hall. apply H1. intros. destruct H2. subst. easy.
          now apply Hall.
        exists v. split.
            now right.
            easy.
Qed.

(* if u is prime, some column v in V has row(u)(v) = true that no strictly-covered
   row witnesses *)
Lemma prime_distinguishes : forall H u,
    prime H.(T) H.(V) (Ul H) u ->
    exists v, H.(V) v = true /\ cell H.(T) u v = true
           /\ forall u', In u' (row_index (Ul H)) ->
                strictly_covered H.(T) H.(V) u' u -> cell H.(T) u' v = false.
Proof.
    intros H u (Hidx & Hncomp).
    destruct H.(fin_V) as (vl & ND & Hvl) eqn:EfinV.
    assert (HvlV : forall v, In v vl -> H.(V) v = true)
        by (intros v Hv; apply Hvl; exact Hv).
    assert (Hnc : ~ (forall v, In v vl ->
        cell H.(T) u v = true <->
        exists u', In u' (row_index (Ul H)) /\ strictly_covered H.(T) H.(V) u' u /\ cell H.(T) u' v = true)).
    { intro Hall. apply Hncomp. intros v HvV. apply Hall, Hvl. exact HvV. }
    destruct (composed_fail_column H u vl HvlV Hnc) as (v & Hv & HvV & Hfail).
    exists v. split; [exact HvV |].
    destruct (Bool.bool_dec (cell H.(T) u v) true) as [Hcu | Hcu].
    - split; [exact Hcu |].
      intros u' Hu'idx Hu'sc.
      apply Bool.not_true_is_false. intro Hu'v.
      apply Hfail. split; eauto.
    - exfalso. apply Hfail. split.
        intro Hc. now rewrite Hc in Hcu.
      intros. destruct H0 as (u' & Hu'idx & Hu'sc & Hu'v).
      destruct Hu'sc. now apply H0.
Qed.

(* State equality is decidable *)
Lemma state_eq_dec : forall H (q1 q2 : { q | memr H q = true }),
    {q1 = q2} + {q1 <> q2}.
Proof.
    intros. destruct (list_eq_dec eq_dec (proj1_sig q1) (proj1_sig q2)).
    - left. destruct q1, q2. simpl in *. subst.
      apply states_proof_irrel.
    - right. intro Heq. apply n. now subst.
Qed.

(* Cover sets are closed under row-equal prime reps *)
Lemma cover_set_row_eq_closed : forall H w r,
    In r (cover_set H.(T) H.(V) (Ul H) H.(fin_V) w) ->
    forall u, memr H u = true ->
        row_eq H.(T) H.(V) u r ->
        In u (cover_set H.(T) H.(V) (Ul H) H.(fin_V) w).
Proof.
    intros. apply filter_In in H0. destruct H0.
    destruct (covered_dec H.(T) H.(V) r w H.(fin_V)); [|discriminate].
    apply filter_In. split.
        now apply (mem_In str_eq).
    destruct (covered_dec H.(T) H.(V) u w H.(fin_V)).
        reflexivity.
    exfalso. apply n. repeat intro. apply c.
        assumption.
    now rewrite <- H2.
Qed.

(* Reachability is closed under row-equal prime reps *)
Lemma run_row_eq_closed : forall H w r,
    In r (run (make_nfa H) w) ->
    forall u' (u'Row : memr H u' = true),
        row_eq H.(T) H.(V) u' (proj1_sig r) ->
        In (exist _ u' u'Row) (run (make_nfa H) w).
Proof.
    intros H w. unfold run, run_from.
    induction w using rev_ind; intros.
    - simpl in *.
      apply in_list_with_proof in H0.
      epose proof (cover_set_row_eq_closed H [] (proj1_sig r) H0 u' u'Row H1).
      replace (exist (fun q => memr H q = true) u' u'Row)
        with (exist (fun q => memr H q = true) u' (cover_set_memr H [] u' H2))
        by apply states_proof_irrel.
      apply (list_with_proof_complete _ _ (bool_eq_proof_irrel H)
               (fun x Hx => cover_set_memr H [] x Hx) u' H2).
    - rewrite fold_left_app in *. simpl in *.
      unfold step in *. apply in_flat_map in H0. destruct H0, H0.
      apply in_flat_map. exists x0. split. assumption.
      apply in_list_with_proof in H2.
      pose proof (cover_set_row_eq_closed _ _ _ H2 u' u'Row H1) as H3.
      replace (exist (fun q0 => memr H q0 = true) u' u'Row)
        with (exist (fun q0 => memr H q0 = true) u' (cover_set_memr H (proj1_sig x0 ++ [x]) u' H3))
        by apply states_proof_irrel.
      apply (list_with_proof_complete _ _ (bool_eq_proof_irrel H)).
Qed.

(* Lemma 4 *)
Lemma rows_are_transitions : forall H,
    consistent H ->
    forall u (uRow : memr H u = true), H.(U) u = true ->
    In (exist _ u uRow) (run (make_nfa H) u).
Proof.
    intros.
    (* Suppose row(u) \notin \delta(Q_0, u) *)
    epose proof (in_dec (state_eq_dec H) _ (run (make_nfa H) u)).
        destruct H2. apply i.
    (* row(u) is prime, since it is a prime representative state *)
    assert (Hprime : prime H.(T) H.(V) (Ul H) u).
        eapply prime_reps_prime, mem_In. apply uRow.
    (* As row(u) \in Q and row(u) \notin \delta(Q_0, u), there is v \in V such that
       row(u)(v) = true and, for all r \sqsubset row(u), r(v) = false *)
    destruct (prime_distinguishes H u Hprime) as (v & HvV & Hcuv & Hdist).
    (* With lemma 1, every reached row is strictly covered by row(u), so by the
       distinguishing column each reached state is false at v: uv is not accepted *)
    assert (Hnotacc : N.L_aut (make_nfa H) (u ++ v) = false). {
        apply Bool.not_true_is_false. intro.
        unfold N.L_aut, N.accept_string, run in H2.
        rewrite run_from_app in H2.
        rewrite run_from_set_accept in H2; auto.
            destruct H2, H2.
            assert (cell H.(T) (proj1_sig x) v = false). {
                apply Hdist. apply state_row_index.
                split. now apply (run_covered H u).
                intro. apply n. apply (run_row_eq_closed H u x H2 u uRow).
                repeat intro. now rewrite H4.
            } congruence.
        intros. now apply state_upper.
    }
    (* but RT is consistent with T, so row(u)(v) = true gives uv \in L(RT): contradiction *)
    assert (In u (row_index (Ul H))).
        unfold row_index. apply in_or_app. left.
        unfold Ul. destruct H.(fin_U), a. simpl. now apply i.
    specialize (H0 u v H2 HvV). destruct H0.
    specialize (H0 Hcuv). congruence.
Qed.

(* Each state's language is the residual by its access string *)
Lemma state_lang_residual : forall H (q : { q | memr H q = true }),
    consistent H ->
    forall w, N.L_state (make_nfa H) q w = N.L_aut (make_nfa H) (proj1_sig q ++ w).
Proof.
    intros. apply Bool.eq_true_iff_eq. split.
    - intros. unfold N.L_state in H1. unfold N.L_aut, N.accept_string, run.
      rewrite run_from_app.
      eapply run_from_mono; eauto.
        intros. destruct H2. subst. apply state_upper.
            inversion H2.
        intros. apply state_upper.
        intros. destruct H2. subst.
          exists q1. split.
            remember q1. destruct s. apply rows_are_transitions; auto.
            replace x with (proj1_sig q1). apply state_U. destruct q1. simpl in *.
            now inversion Heqs.
        apply covered_refl.
      inversion H2.
    - intros. unfold N.L_state. unfold N.L_aut, N.accept_string, run in H1.
      rewrite run_from_app in H1.
      eapply run_from_mono; eauto.
        intros. apply state_upper.
        intros. destruct H2. subst. apply state_upper.
            inversion H2.
        intros. exists q. split. now left.
          remember q1. destruct s. apply run_covered; auto.
          apply state_U.
Qed.

(* Theorem 1 *)
(* make_nfa constructs a canonical RFSA if it is consistent with T *)
Theorem make_nfa_canonical : forall H,
    consistent H ->
    R.t { q | memr H q = true }.
Proof.
    intros. apply Build_t with (nfa := make_nfa H).
    intros. exists (proj1_sig q).
    intro w. unfold Res.inverse.
    now apply state_lang_residual.
Defined.

End NLstar.
