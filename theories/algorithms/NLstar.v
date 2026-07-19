(** NL* RFSA learning
    https://lsv.ens-paris-saclay.fr/Publis/RAPPORTS_LSV/PDF/rr-lsv-2008-28.pdf *)
    
#[local] Set Warnings "-intuition-auto-with-star".

From lstar Require Import automata.NFA ListLemmas SetLemmas.
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

(* Definition 7: r is covered by r', r \sqsubseteq r', if for all v \in V, r(v)=+ implies r'(v)=+ *)
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
        In u (proj1_sig Ul) -> In u' (proj1_sig Ul) -> In a enum ->
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
        In u (proj1_sig Ul) /\ In u' (proj1_sig Ul) /\ In a enum
        /\ ~ (covered T V u u' -> covered T V (u ++ [a]) (u' ++ [a]))}.
Proof.
    intros T V U Ul finV. unfold rfsa_consistent.
    destruct (consistent_outer_dec T V (proj1_sig Ul) (proj1_sig Ul) finV); auto.
Defined.

(* Definition 10: a table T=(T,U,V) with prefix-closed U and suffix-closed V that is
   RFSA-closed and RFSA-consistent, after Lstar's HypothesisDFA *)
Record HypothesisRFSA : Type := {
  T    : str -> bool;
  U    : str -> bool;
  V    : str -> bool;
  fin_U : finite U;
  fin_V : finite V;
  (* "U prefix-closed" *)
  pref : forall w w', U (w ++ w') = true -> U w = true;
  (* "V is always suffix-closed" *)
  suff : forall w w', V (w ++ w') = true -> V w' = true;
  (* "U and V are both initialized to {\epsilon}" *)
  eps_U : U [] = true;
  eps_V : V [] = true;
  tbl : forall u v,
        In u (row_index (proj1_sig fin_U)) -> V v = true ->
        T (u ++ v) = member (u ++ v)
}.

(* Upper access strings of the table *)
Definition Ul (H : HypothesisRFSA) : list str := proj1_sig H.(fin_U).

Definition Vl (H : HypothesisRFSA) : list str := proj1_sig H.(fin_V).

(* RFSA-closedness and consistency of a table *)
Definition Hclosed (H : HypothesisRFSA) : Prop :=
    closed H.(T) H.(V) H.(fin_U).
Definition Hconsistent (H : HypothesisRFSA) : Prop :=
    rfsa_consistent H.(T) H.(V) H.(fin_U).

(* Every residual of L is realised by a prime row of the table *)
Definition Hrep (H : HypothesisRFSA) : Prop :=
    forall r, L.residual r ->
        exists u, In u (prime_reps H.(T) H.(V) (Ul H) H.(fin_V))
                  /\ Res.lang_eq r (Res.inverse member u).

Definition Hsep (H : HypothesisRFSA) : Prop :=
    forall u1 u2,
        In u1 (Ul H) ->
        In u2 (Ul H) ->
        row_eq H.(T) H.(V) u1 u2 -> u1 = u2.

Definition Hdense (H : HypothesisRFSA) : Prop :=
    forall u,
        In u (prime_reps H.(T) H.(V) (Ul H) H.(fin_V)) ->
        L.prime (Res.inverse member u).

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
   F = {r \in Q | r(\epsilon)=+}, \delta(row(u),a) = {r \in Q | r \sqsubseteq row(ua)} *)
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

Lemma row_eq_refl : forall T V u, row_eq T V u u.
Proof. now intros T V u v Hv. Qed.

Lemma row_eq_sym : forall T V u1 u2,
    row_eq T V u1 u2 -> row_eq T V u2 u1.
Proof. intros T V u1 u2 Hr v Hv. symmetry. now apply Hr. Qed.

Lemma row_eq_trans : forall T V a b c,
    row_eq T V a b -> row_eq T V b c -> row_eq T V a c.
Proof.
    intros T V a b c Hab Hbc v Hv. rewrite (Hab v Hv). now apply Hbc.
Qed.

Lemma covered_row_eq_r : forall T V u u1 u2,
    row_eq T V u1 u2 -> covered T V u u1 -> covered T V u u2.
Proof.
    intros T V u u1 u2 Hr Hcov v Hv Huv.
    rewrite <- (Hr v Hv). now apply Hcov.
Qed.

Lemma covered_row_eq_l : forall T V u u1 u2,
    row_eq T V u1 u2 -> covered T V u1 u -> covered T V u2 u.
Proof.
    intros T V u u1 u2 Hr Hcov v Hv Huv.
    apply Hcov; [assumption |]. now rewrite (Hr v Hv).
Qed.

Lemma strictly_covered_row_eq_r : forall T V u u1 u2,
    row_eq T V u1 u2 -> strictly_covered T V u u1 -> strictly_covered T V u u2.
Proof.
    intros T V u u1 u2 Hr (Hcov & Hne). split.
        apply (covered_row_eq_r T V u u1 u2 Hr Hcov).
    intro Heq. apply Hne.
    apply (row_eq_trans T V u u2 u1 Heq (row_eq_sym T V u1 u2 Hr)).
Qed.

(* Composedness only depends on the row, not on the access string. *)
Lemma composed_row_eq : forall T V Ul u1 u2,
    row_eq T V u1 u2 -> composed T V Ul u1 -> composed T V Ul u2.
Proof.
    intros T V Ul u1 u2 Hr Hc v Hv. rewrite <- (Hr v Hv). split.
    - intro Hcell. destruct (proj1 (Hc v Hv) Hcell) as (u' & Hu' & Hsc & Hu'v).
      exists u'. split. assumption. split; [|assumption].
      eauto using strictly_covered_row_eq_r.
    - intros (u' & Hu' & Hsc & Hu'v). apply (Hc v Hv).
      exists u'. split. assumption. split; [|assumption].
      eauto using strictly_covered_row_eq_r, row_eq_sym.
Qed.

(* Hence so does primality, for strings that index rows of the table. *)
Lemma prime_row_eq : forall T V Ul u1 u2,
    In u2 (row_index Ul) ->
    row_eq T V u1 u2 -> prime T V Ul u1 -> prime T V Ul u2.
Proof.
    intros T V Ul u1 u2 Hu2 Hr (_ & Hnc). split; [apply Hu2 |].
    intro Hc. apply Hnc.
    apply (composed_row_eq T V Ul u2 u1 (row_eq_sym T V u1 u2 Hr) Hc).
Qed.

(* The number of columns of [vl] at which the row of [u] is true. *)
Definition row_weight (T : str -> bool) (vl : list str) (u : str) : nat :=
    List.length (filter (fun v => cell T u v) vl).

Lemma row_weight_zero : forall T vl u v,
    In v vl -> row_weight T vl u = 0 -> cell T u v = false.
Proof.
    intros T vl u v. unfold row_weight.
    induction vl as [| x vl IH]; intros Hin Hz.
        destruct Hin.
    simpl in Hz. destruct (cell T u x) eqn:E.
        simpl in Hz. discriminate.
    destruct Hin as [<- | Hin]; [apply E | now apply IH].
Qed.

Lemma row_weight_le : forall T vl u1 u2,
    (forall v, In v vl -> cell T u1 v = true -> cell T u2 v = true) ->
    row_weight T vl u1 <= row_weight T vl u2.
Proof.
    intros T vl. unfold row_weight.
    induction vl as [| v vl IH]; intros u1 u2 Hcov.
        simpl. lia.
    assert (Htail : forall x, In x vl -> cell T u1 x = true -> cell T u2 x = true)
        by (intros x Hx; apply Hcov; now right).
    specialize (IH u1 u2 Htail). simpl.
    destruct (cell T u1 v) eqn:E1.
    - rewrite (Hcov v (or_introl eq_refl) E1). simpl. lia.
    - destruct (cell T u2 v); simpl; lia.
Qed.

Lemma row_weight_lt : forall T vl u1 u2,
    (forall v, In v vl -> cell T u1 v = true -> cell T u2 v = true) ->
    (exists v, In v vl /\ cell T u1 v = false /\ cell T u2 v = true) ->
    row_weight T vl u1 < row_weight T vl u2.
Proof.
    intros T vl. unfold row_weight.
    induction vl as [| v vl IH]; intros u1 u2 Hcov (w & Hw & Hw1 & Hw2).
        destruct Hw.
    assert (Htail : forall x, In x vl -> cell T u1 x = true -> cell T u2 x = true)
        by (intros x Hx; apply Hcov; now right).
    pose proof (row_weight_le T vl u1 u2 Htail) as Hle.
    unfold row_weight in Hle. simpl.
    destruct Hw as [<- | Hw].
    - rewrite Hw1, Hw2. simpl. lia.
    - specialize (IH u1 u2 Htail (ex_intro _ w (conj Hw (conj Hw1 Hw2)))).
      destruct (cell T u1 v) eqn:E1.
      + rewrite (Hcov v (or_introl eq_refl) E1). simpl. lia.
      + destruct (cell T u2 v); simpl; lia.
Qed.

(* A pair of rows that differ somewhere on a column list differ at a listed
   column.  The search is constructive because cells are booleans. *)
Lemma row_neq_witness : forall T u1 u2 (vl : list str),
    ~ (forall v, In v vl -> cell T u1 v = cell T u2 v) ->
    exists v, In v vl /\ cell T u1 v <> cell T u2 v.
Proof.
    intros T u1 u2 vl. induction vl as [| v vl IH]; intro Hne.
        exfalso. apply Hne. intros x [].
    destruct (Bool.bool_dec (cell T u1 v) (cell T u2 v)) as [Heq | Hneq].
    - destruct IH as (x & Hx & Hxne).
          intro Hall. apply Hne. intros y [<- | Hy]; [apply Heq | now apply Hall].
      exists x. split; [now right | apply Hxne].
    - exists v. split; [now left | apply Hneq].
Qed.

(* A strictly covered row is false at some column where the covering row is
   true, hence is strictly lighter. *)
(* A failure of covering is witnessed by a listed column. *)
Lemma covered_fail_on : forall T u1 u2 (vl : list str),
    ~ (forall v, In v vl -> cell T u1 v = true -> cell T u2 v = true) ->
    {v | In v vl /\ cell T u1 v = true /\ cell T u2 v = false}.
Proof.
    intros T u1 u2 vl. induction vl as [| v vl IH]; intro Hne.
        exfalso. apply Hne. intros x [].
    destruct (Bool.bool_dec (cell T u1 v) true) as [E1 | E1].
    - destruct (Bool.bool_dec (cell T u2 v) true) as [E2 | E2].
      + destruct IH as (x & Hx & Hx1 & Hx2).
            intro Hall. apply Hne. intros y [<- | Hy]; [now intros _ | now apply Hall].
        exists x. split; [now right | now split].
      + exists v. split; [now left | split].
          apply E1.
        now apply Bool.not_true_is_false.
    - destruct IH as (x & Hx & Hx1 & Hx2).
          intro Hall. apply Hne. intros y [<- | Hy]; [| now apply Hall].
          intro C. congruence.
      exists x. split; [now right | now split].
Qed.

Lemma covered_fail_witness : forall T V u1 u2 (finV : finite V),
    ~ covered T V u1 u2 ->
    {v | V v = true /\ cell T u1 v = true /\ cell T u2 v = false}.
Proof.
    intros T V u1 u2 finV Hnc.
    destruct finV as (vl & ND & Hvl). simpl in *.
    destruct (covered_fail_on T u1 u2 vl) as (v & Hv & H1 & H2).
        intro Hall. apply Hnc. intros x Hx. apply Hall. now apply Hvl.
    exists v. split; [now apply Hvl | now split].
Qed.

Lemma strictly_covered_witness : forall T V u1 u2 (finV : finite V),
    strictly_covered T V u1 u2 ->
    exists v, In v (proj1_sig finV) /\ cell T u1 v = false /\ cell T u2 v = true.
Proof.
    intros T V u1 u2 finV (Hcov & Hne).
    destruct finV as (vl & ND & Hvl). simpl in *.
    destruct (row_neq_witness T u1 u2 vl) as (v & Hv & Hvne).
        intro Hall. apply Hne. intros x Hx. apply Hall. now apply Hvl.
    assert (HvV : V v = true) by now apply Hvl.
    exists v. split; [apply Hv |].
    destruct (cell T u1 v) eqn:E1.
    - exfalso. apply Hvne. symmetry. now apply (Hcov v HvV).
    - destruct (cell T u2 v) eqn:E2.
        now split.
      exfalso. now apply Hvne.
Qed.

Lemma strictly_covered_weight_lt : forall T V u1 u2 (finV : finite V),
    strictly_covered T V u1 u2 ->
    row_weight T (proj1_sig finV) u1 < row_weight T (proj1_sig finV) u2.
Proof.
    intros T V u1 u2 finV Hsc.
    destruct (strictly_covered_witness T V u1 u2 finV Hsc) as (x & Hx & Hx1 & Hx2).
    apply row_weight_lt; [| now exists x].
    intros y Hy Hy1. destruct Hsc as (Hcov & _). apply (Hcov y); [| apply Hy1].
    destruct finV as (vl & ND & Hvl). simpl in Hy. now apply Hvl.
Qed.

Lemma row_prime_witness : forall T V Ul (finV : finite V) k u v,
    row_weight T (proj1_sig finV) u <= k ->
    In u (row_index Ul) -> V v = true -> cell T u v = true ->
    exists p, In p (row_index Ul) /\ prime T V Ul p
              /\ covered T V p u /\ cell T p v = true.
Proof.
    intros T V Ul finV k. induction k as [| k IH]; intros u v Hw Hu Hv Hcell.
    - exfalso.
      assert (Hin : In v (proj1_sig finV)). {
          destruct finV as (vl & ND & Hvl). simpl. now apply Hvl. }
      assert (Hz : row_weight T (proj1_sig finV) u = 0) by lia.
      rewrite (row_weight_zero T (proj1_sig finV) u v Hin Hz) in Hcell.
      discriminate.
    - destruct (prime_dec T V Ul u finV) as [Hp | Hnp].
      + exists u.
        apply (conj Hu (conj Hp (conj (covered_refl T V u) Hcell))).
      + assert (Hcomp : composed T V Ul u). {
            destruct (composed_dec T V Ul u finV) as [Hc | Hnc]; [apply Hc |].
            exfalso. apply Hnp. now split. }
        destruct (proj1 (Hcomp v Hv) Hcell) as (u' & Hu' & Hsc & Hu'v).
        pose proof (strictly_covered_weight_lt T V u' u finV Hsc) as Hlt.
        destruct (IH u' v ltac:(lia) Hu' Hv Hu'v) as (p & Hp1 & Hp2 & Hp3 & Hp4).
        destruct Hsc as (Hcov & _).
        exists p.
        apply (conj Hp1 (conj Hp2
                 (conj (covered_trans T V p u' u Hp3 Hcov) Hp4))).
Qed.

Definition closed_violation (T V : str -> bool) (Ul : list str)
    (finV : finite V) (u : str) : Prop :=
    In u (USigma Ul) /\ prime T V Ul u
    /\ forall p, In p (prime_reps T V Ul finV) -> ~ row_eq T V p u.

(* A violating row is not an upper row: it is prime, so if it were in [Ul] it
   would be one of the prime representatives, and it is row-equal to itself. *)
Lemma closed_violation_not_upper : forall T V Ul finV u,
    closed_violation T V Ul finV u -> ~ In u Ul.
Proof.
    intros T V Ul finV u (Hin & Hp & Hno) HuUl.
    apply (Hno u); [| apply row_eq_refl].
    unfold prime_reps. apply filter_In. split; [apply HuUl |].
    now destruct (prime_dec T V Ul u finV).
Qed.

(* No upper row has the same row as a violating row. *)
Lemma closed_violation_row_new : forall T V Ul finV u w,
    closed_violation T V Ul finV u -> In w Ul -> ~ row_eq T V w u.
Proof.
    intros T V Ul finV u w (Hin & Hp & Hno) HwUl Hrow.
    apply (Hno w); [| apply Hrow].
    unfold prime_reps. apply filter_In. split; [apply HwUl |].
    assert (Hwidx : In w (row_index Ul))
        by (unfold row_index; apply in_or_app; now left).
    assert (Hwp : prime T V Ul w). {
        apply (prime_row_eq T V Ul u w Hwidx); [| apply Hp].
        apply (row_eq_sym T V w u Hrow). }
    now destruct (prime_dec T V Ul w finV).
Qed.

Lemma no_upper_prime_dec : forall T V Ul finV u,
    (forall p, In p (prime_reps T V Ul finV) -> ~ row_eq T V p u)
  + {p | In p (prime_reps T V Ul finV) /\ row_eq T V p u}.
Proof.
    intros T V Ul finV u.
    assert (Hgen : forall l,
        (forall p, In p l -> ~ row_eq T V p u)
      + {p | In p l /\ row_eq T V p u}). {
        intro l. induction l as [| p ps IH].
            left. intros q [].
        destruct (row_eq_dec T V p u finV) as [Heq | Hne].
            right. exists p. split; [now left | apply Heq].
        destruct IH.
        - left. intros q [<- | Hq]; eauto.
        - right. destruct s, a. exists x. split. now right. assumption. }
    apply Hgen.
Defined.

Lemma closed_violation_search : forall T V Ul finV (l : list str),
    (forall u, In u l -> In u (USigma Ul)) ->
    {u : str | closed_violation T V Ul finV u}
  + {forall u, In u l -> ~ closed_violation T V Ul finV u}.
Proof.
    intros T V Ul finV l. induction l as [| u l IH]; intro Hsub.
        right. intros x [].
    assert (Hsub' : forall x, In x l -> In x (USigma Ul))
        by (intros x Hx; apply Hsub; now right).
    destruct (prime_dec T V Ul u finV) as [Hp | Hnp].
    - destruct (no_upper_prime_dec T V Ul finV u) as [Hno | (p & Hp' & Hpe)].
      + left. exists u.
        apply (conj (Hsub u (or_introl eq_refl)) (conj Hp Hno)).
      + destruct (IH Hsub') as [Hyes | Hno].
            left. apply Hyes.
        right. intros x [<- | Hx]; [| now apply Hno].
        intros (_ & _ & Hall). apply (Hall p Hp' Hpe).
    - destruct (IH Hsub') as [Hyes | Hno].
          left. apply Hyes.
      right. intros x [<- | Hx]; [| now apply Hno].
      now intros (_ & Hpx & _).
Defined.

Lemma closed_violation_dec : forall T V Ul finV,
    {u : str | closed_violation T V Ul finV u}
  + {forall u, In u (USigma Ul) -> ~ closed_violation T V Ul finV u}.
Proof.
    intros T V Ul finV.
    apply (closed_violation_search T V Ul finV (USigma Ul) (fun u H => H)).
Defined.

(* Adequacy of the repair rule: if the lower part hides no prime row, the table
   is RFSA-closed in the sense of Definition 8.  Every true cell is witnessed by
   a prime row of the table ([row_prime_witness]); that prime row is either
   already an upper row, or a lower one, in which case the absence of a
   violation hands back an upper prime representative with the same row. *)
Lemma no_violation_closed : forall T V U (finU : finite U) (finV : finite V),
    (forall u, In u (USigma (proj1_sig finU)) ->
        ~ closed_violation T V (proj1_sig finU) finV u) ->
    closed T V finU.
Proof.
    intros T V U finU finV Hno u Hu v Hv. split.
    - intro Hcell.
      destruct (row_prime_witness T V (proj1_sig finU) finV
                  (row_weight T (proj1_sig finV) u) u v (le_n _) Hu Hv Hcell)
        as (p & Hpidx & Hpp & Hpcov & Hpv).
      unfold row_index in Hpidx. apply in_app_or in Hpidx.
      destruct Hpidx as [HpU | HpLow].
      + exists p. apply (conj HpU (conj Hpp (conj Hpcov Hpv))).
      + (* p is a lower prime row, so some upper prime representative has the
           same row *)
        destruct (no_upper_prime_dec T V (proj1_sig finU) finV p)
          as [Hnone | (q & Hq & Hqe)].
            exfalso. apply (Hno p HpLow).
            apply (conj HpLow (conj Hpp Hnone)).
        assert (Hqv : cell T q v = true) by (rewrite (Hqe v Hv); apply Hpv).
        exists q.
        apply (conj (prime_reps_upper T V (proj1_sig finU) finV q Hq)
                 (conj (prime_reps_prime T V (proj1_sig finU) finV q Hq)
                   (conj (covered_row_eq_l T V u p q
                            (row_eq_sym T V q p Hqe) Hpcov) Hqv))).
    - intros (u' & Hu' & Hpu' & Hcov & Hu'v). apply (Hcov v Hv Hu'v).
Qed.

(* Access strings are row indices *)
Lemma state_row_index : forall H (q : { q | memr H q = true }),
    In (proj1_sig q) (row_index (Ul H)).
Proof.
    intros. eapply prime_reps_index, mem_In. destruct q. eauto.
Qed.

(* Lemma 1: "For all u \in U and r \in \delta(Q0,u), we have r \sqsubseteq row(u)" *)
(* Access strings lie in the upper part *)
Lemma state_upper : forall H (q : { q | memr H q = true }),
    In (proj1_sig q) (Ul H).
Proof.
    intros. apply (prime_reps_upper H.(T) H.(V) (Ul H) H.(fin_V)).
    apply (mem_In str_eq). now destruct q.
Qed.

Lemma run_covered : forall H (Hco : Hconsistent H) u r,
    H.(U) u = true ->
    In r (run (make_nfa H) u) ->
    covered H.(T) H.(V) (proj1_sig r) u.
Proof.
    intros H Hco u. induction u using rev_ind; intros r Hu Hr.
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
          apply Hco; auto.
            apply state_upper.
            now apply (proj1 (proj2 (proj2_sig H.(fin_U)) u)).
            apply t_enumerable. }
      now apply (covered_trans _ _ _ _ _ Hrq Hqx).
Qed.

(* Cell distributes over a leading column symbol *)
Lemma cell_app : forall T u a v,
    cell T u (a :: v) = cell T (u ++ [a]) v.
Proof. intros. unfold cell. now rewrite <- app_assoc. Qed.

(* F = {r \in Q | r(\epsilon)=+} *)
Lemma accept_cell : forall H q,
    accept _ (make_nfa H) q = cell H.(T) (proj1_sig q) [].
Proof. intros. unfold cell. now rewrite app_nil_r. Qed.

(* Pointwise closedness *)
Lemma cover_set_cell : forall H (Hcl : Hclosed H) w v,
    In w (row_index (Ul H)) ->
    H.(V) v = true ->
    (exists p, In p (cover_set H.(T) H.(V) (Ul H) H.(fin_V) w) /\ cell H.(T) p v = true) <-> cell H.(T) w v = true.
Proof.
    intros H Hcl w v Hw Hv. split.
    - intros (p & Hp & Hpv).
      apply filter_In in Hp. destruct Hp as (_ & Hcov).
      destruct (covered_dec H.(T) H.(V) p w H.(fin_V)) as [Hc |]; [| discriminate].
      now apply (Hc v Hv).
    - intro Hwv. destruct (Hcl w Hw v Hv) as (Hfwd & _).
      destruct (Hfwd Hwv) as (u' & Hu' & Hprime & Hcovu' & Hu'v).
      exists u'. split; [| assumption].
      apply filter_In. split.
        unfold prime_reps. apply filter_In. split; [assumption |].
          now destruct (prime_dec H.(T) H.(V) (Ul H) u' H.(fin_V)).
        now destruct (covered_dec H.(T) H.(V) u' w H.(fin_V)).
Qed.

(* Access strings of states lie in U *)
Lemma state_U : forall H (q : { q | memr H q = true }),
    H.(U) (proj1_sig q) = true.
Proof.
    intros. destruct H, fin_U0, a. apply i, state_upper.
Qed.

(* Running v from a set accepts iff cell(q)(v) = true for some start state q *)
Lemma run_from_set_accept : forall H (Hcl : Hclosed H) v qs,
    H.(V) v = true ->
    (forall q, In q qs -> In (proj1_sig q) (Ul H)) ->
    existsb (accept _ (make_nfa H)) (run_from (make_nfa H) qs v) = true
    <-> exists q, In q qs /\ cell H.(T) (proj1_sig q) v = true.
Proof.
    intros H Hcl v. induction v; intros qs Hv Hup.
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
          apply (cover_set_cell H Hcl (proj1_sig q ++ [a]) v); auto.
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
          apply (cover_set_cell H Hcl (proj1_sig q ++ [a]) v Hwr Hv') in Hqv.
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

(* Lemma 2: "(1) r(v)=+ iff v \in Lr, and (2) row(\epsilon)(v)=+ iff v \in L(RT)" *)
Lemma row_state_lang : forall H (Hcl : Hclosed H) (r : { q | memr H q = true }) v,
    H.(V) v = true ->
    (cell H.(T) (proj1_sig r) v = true <-> N.L_state (make_nfa H) r v = true) /\
    (cell H.(T) [] v = true <-> N.L_aut (make_nfa H) v = true).
Proof.
    intros H Hcl r v Hv. split.
    - unfold N.L_state.
      rewrite (run_from_set_accept H Hcl v [r] Hv).
      + split.
          intro Hc. exists r. split. now left. assumption.
        now intros (q & [<- | []] & Hc).
      + intros q [<- | []]. apply state_upper.
    - unfold N.L_aut, N.accept_string, run.
      rewrite (run_from_set_accept H Hcl v (N.initial _ (make_nfa H)) Hv).
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

Lemma eps_cell_L_aut : forall H (Hcl : Hclosed H) v,
    H.(V) v = true ->
    (cell H.(T) [] v = true <-> N.L_aut (make_nfa H) v = true).
Proof.
    intros H Hcl v Hv.
    unfold N.L_aut, N.accept_string, run.
    rewrite (run_from_set_accept H Hcl v (N.initial _ (make_nfa H)) Hv).
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
Lemma run_from_mono : forall H (Hcl : Hclosed H) (Hco : Hconsistent H) w qs1 qs2,
    (forall q1, In q1 qs1 -> In (proj1_sig q1) (Ul H)) ->
    (forall q2, In q2 qs2 -> In (proj1_sig q2) (Ul H)) ->
    (forall q1, In q1 qs1 ->
        exists q2, In q2 qs2 /\ covered H.(T) H.(V) (proj1_sig q1) (proj1_sig q2)) ->
    existsb (accept _ (make_nfa H)) (run_from (make_nfa H) qs1 w) = true ->
    existsb (accept _ (make_nfa H)) (run_from (make_nfa H) qs2 w) = true.
Proof.
    intros H Hcl Hco w. induction w; intros qs1 qs2 Hup1 Hup2 Hmono Hacc.
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
        assert (Hq1U : In (proj1_sig q1) (Ul H)) by (now apply Hup1).
        assert (Hq2U : In (proj1_sig q2) (Ul H)) by (now apply Hup2).
        assert (Hlift : covered H.(T) H.(V) (proj1_sig q1 ++ [a]) (proj1_sig q2 ++ [a]))
          by (apply Hco; auto using t_enumerable).
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
Lemma covered_iff_lang_incl : forall H (Hcl : Hclosed H) (Hco : Hconsistent H) u1 u2
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
      destruct (row_state_lang H Hcl (exist _ u1 p1) v H1) as ((Hf1 & _) & _).
      destruct (row_state_lang H Hcl (exist _ u2 p2) v H1) as ((_ & Hb2) & _). auto.
Qed.

(* Definition 11: "RT is consistent with T if, for all w \in (U \cup U\Sigma)V, T(w)=+ iff w \in L(RT)" *)
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
        by (intros v Hv; apply Hvl; apply Hv).
    assert (Hnc : ~ (forall v, In v vl ->
        cell H.(T) u v = true <->
        exists u', In u' (row_index (Ul H)) /\ strictly_covered H.(T) H.(V) u' u /\ cell H.(T) u' v = true)).
    { intro Hall. apply Hncomp. intros v HvV. apply Hall, Hvl. apply HvV. }
    destruct (composed_fail_column H u vl HvlV Hnc) as (v & Hv & HvV & Hfail).
    exists v. split; [apply HvV |].
    destruct (Bool.bool_dec (cell H.(T) u v) true) as [Hcu | Hcu].
    - split; [apply Hcu |].
      intros u' Hu'idx Hu'sc.
      apply Bool.not_true_is_false. intro Hu'v.
      apply Hfail. split; eauto.
    - exfalso. apply Hfail. split.
        intro Hc. now rewrite Hc in Hcu.
      intros (u' & Hu'idx & Hu'sc & Hu'v).
      destruct Hu'sc. now apply (H0 v HvV).
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
Lemma rows_are_transitions : forall H (Hcl : Hclosed H) (Hco : Hconsistent H),
    consistent H ->
    forall u (uRow : memr H u = true), H.(U) u = true ->
    In (exist _ u uRow) (run (make_nfa H) u).
Proof.
    intros H Hcl Hco. intros.
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
    assert (Hnotacc : N.L_aut (make_nfa H) (u ++ v) = false).
        apply Bool.not_true_is_false. intro.
        unfold N.L_aut, N.accept_string, run in H2.
        rewrite run_from_app in H2.
        rewrite run_from_set_accept in H2; auto.
            destruct H2. destruct H2.
            assert (cell H.(T) (proj1_sig x) v = false).
                apply Hdist. apply state_row_index.
                split. now apply (run_covered H Hco u).
                intro. apply n. apply (run_row_eq_closed H u x H2 u uRow).
                repeat intro. now rewrite H4.
            congruence.
        intros. now apply state_upper.
    (* but RT is consistent with T, so row(u)(v) = true gives uv \in L(RT): contradiction *)
    assert (In u (row_index (Ul H))).
        unfold row_index. apply in_or_app. left.
        now apply (proj1 (proj2 (proj2_sig H.(fin_U)) u)).
    pose proof (proj1 (H0 u v H2 HvV) Hcuv). congruence.
Qed.

(* Each state's language is the residual by its access string *)
Lemma state_lang_residual : forall H (Hcl : Hclosed H) (Hco : Hconsistent H)
      (q : { q | memr H q = true }),
    consistent H ->
    forall w, N.L_state (make_nfa H) q w = true
              <-> N.L_aut (make_nfa H) (proj1_sig q ++ w) = true.
Proof.
    intros H Hcl Hco. intros. split.
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
Definition make_nfa_canonical : forall H (Hcl : Hclosed H) (Hco : Hconsistent H),
    consistent H ->
    R.t { q | memr H q = true }.
Proof.
    intros H HCl Hco H0. apply Build_t with (nfa := make_nfa H).
    intros. exists (proj1_sig q).
    intro w. unfold Res.inverse.
    now apply Bool.eq_true_iff_eq, state_lang_residual.
Defined.

(* T(w) = true iff w in L(RT) *)
Lemma nfa_encodes_consistent : forall H,
    encodes (make_nfa H) ->
    consistent H.
Proof.
    intros H Henc u v Hu Hv. unfold cell.
    rewrite (H.(tbl) u v Hu Hv). unfold N.L_aut. unfold encodes in Henc. now rewrite Henc.
Qed.

(* Under encoding, L_state q is exactly the residual inverse member (proj1_sig q) *)
Lemma state_lang_member : forall H (Hcl : Hclosed H) (Hco : Hconsistent H) q,
    encodes (make_nfa H) ->
    Res.lang_eq (N.L_state (make_nfa H) q) (Res.inverse member (proj1_sig q)).
Proof.
    intros H Hcl Hco. intros. unfold Res.inverse, Res.lang_eq. intros.
    apply Bool.eq_true_iff_eq. rewrite state_lang_residual; auto using nfa_encodes_consistent.
    unfold N.L_aut. destruct (N.accept_string _ _) eqn:E.
        apply H0 in E. now rewrite E.
    destruct (member _) eqn:E0.
        apply H0 in E0. congruence.
    reflexivity.
Qed.

(* A state's per-state language is a residual of member *)
Lemma state_residual : forall H (Hcl : Hclosed H) (Hco : Hconsistent H) q,
    encodes (make_nfa H) ->
    residual (N.L_state (make_nfa H) q).
Proof.
    intros. exists (proj1_sig q). now apply state_lang_member.
Qed.

(* A residual represented by row u agrees with the row of u on every column
   of the table *)
Lemma residual_cell : forall H u v,
    In u (row_index (Ul H)) -> H.(V) v = true ->
    Res.inverse member u v = cell H.(T) u v.
Proof.
    intros H u v Hu Hv. unfold Res.inverse, cell. now rewrite (H.(tbl) u v Hu Hv).
Qed.

Lemma residual_cell_rep : forall H u v,
    In u (prime_reps H.(T) H.(V) (Ul H) H.(fin_V)) -> H.(V) v = true ->
    Res.inverse member u v = cell H.(T) u v.
Proof.
    intros H u v Hu Hv. apply residual_cell; [| apply Hv].
    apply (prime_reps_index H.(T) H.(V) (Ul H) H.(fin_V)). apply Hu.
Qed.

(* Under encoding, L_state q agrees with the row of q on columns of V *)
Lemma state_lang_cell : forall H (Hcl : Hclosed H) q v,
    H.(V) v = true ->
    N.L_state (make_nfa H) q v = cell H.(T) (proj1_sig q) v.
Proof.
    intros. symmetry. pose proof (row_state_lang H Hcl q v H0). destruct H1.
    destruct cell.
        symmetry. now apply H1.
    destruct N.L_state. now apply H1.
    reflexivity.
Qed.

Lemma row_eq_lang_eq : forall H (Hcl : Hclosed H) (Hco : Hconsistent H)
      (q1 q2 : { q | memr H q = true }),
    row_eq H.(T) H.(V) (proj1_sig q1) (proj1_sig q2) ->
    Res.lang_eq (N.L_state (make_nfa H) q1) (N.L_state (make_nfa H) q2).
Proof.
    intros H Hcl Hco. intros. unfold Res.lang_eq. intros. apply Bool.eq_true_iff_eq. split; intro;
        destruct q1, q2; (eapply covered_iff_lang_incl; eauto);
        unfold covered; intros; simpl in *.
    now rewrite <- H0.
    now rewrite H0.
Qed.

(* Language inclusion between two states is
   covering between the rows of their access strings. *)
Lemma state_lang_incl_covered : forall H (Hcl : Hclosed H) (Hco : Hconsistent H)
      (q1 q2 : { q | memr H q = true }),
    (forall w, N.L_state (make_nfa H) q1 w = true ->
               N.L_state (make_nfa H) q2 w = true) ->
    covered H.(T) H.(V) (proj1_sig q1) (proj1_sig q2).
Proof.
    intros H Hcl Hco q1 q2 Hincl.
    destruct q1 as (u1 & p1), q2 as (u2 & p2); simpl in *.
    now apply (covered_iff_lang_incl H Hcl Hco u1 u2 p1 p2).
Qed.

(* Running a word from a set of start states accepts iff some start state
   accepts it on its own. *)
Lemma existsb_accept_run_from : forall {state} (n : N.t state) qs v,
    existsb (N.accept _ n) (N.run_from n qs v)
    = existsb (fun q => N.L_state n q v) qs.
Proof.
    intros state n qs v. revert qs.
    unfold N.run_from, N.L_state, N.run_from.
    induction v; intros qs.
    - simpl. induction qs; simpl. reflexivity.
      now rewrite IHqs, Bool.orb_false_r.
    - simpl. rewrite IHv.
      unfold N.step. induction qs; simpl.
        reflexivity.
      rewrite existsb_app, IHqs. f_equal.
      rewrite <- IHv. now rewrite app_nil_r.
Qed.

Lemma existsb_map : forall {X Y} (l : list X) f (g : X -> Y),
    existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof.
    induction l; intros; simpl in *.
        reflexivity.
    f_equal. apply IHl.
Qed.

(* The residual of an NFA's language by [u] is the union of the languages of
   the states reachable after reading [u]. *)
Lemma inverse_L_aut_union : forall {state} (n : N.t state) u,
    Res.lang_eq (Res.inverse (N.L_aut n) u)
                (union (map (N.L_state n) (N.run n u))).
Proof.
    intros state n u v. unfold Res.inverse, N.L_aut, N.accept_string.
    unfold union. rewrite existsb_map.
    unfold N.run at 1. unfold N.run_from. rewrite fold_left_app.
    change (fold_left (N.step (N.transition state n)) u (N.initial state n)) with
        (N.run n u).
    change (fold_left _ _ _) with (N.run_from n (N.run n u) v).
    now rewrite existsb_accept_run_from.
Qed.

Lemma state_lang_prime : forall H (Hcl : Hclosed H) (Hco : Hconsistent H) q,
    encodes (make_nfa H) ->
    L.prime (N.L_state (make_nfa H) q).
Proof.
    intros H Hcl Hco q Henc.
    set (n := make_nfa H).
    split.
        now apply (state_residual H Hcl Hco).
    intros (_ & rs & Hrs & Hunion).
    (* the row of [q] is a prime row of the table *)
    assert (Hqpr : In (proj1_sig q) (prime_reps H.(T) H.(V) (Ul H) H.(fin_V)))
        by (apply (mem_In str_eq); apply (proj2_sig q)).
    destruct (prime_reps_prime H.(T) H.(V) (Ul H) H.(fin_V) (proj1_sig q) Hqpr)
      as (Hqidx & Hncomp).
    apply Hncomp. clear Hncomp.
    intros v HvV. split.
    - intro Hcell.
      (* move from the table to the language of [q] *)
      assert (HLq : N.L_state n q v = true) by
        (rewrite state_lang_cell; eauto).
      rewrite (Hunion v) in HLq. unfold union in HLq.
      apply existsb_exists in HLq. destruct HLq as (r' & Hr'in & Hr'v).
      destruct (Hrs r' Hr'in) as ((x & Hx) & Hr'neq).
      (* [r'] is a residual of L(n), hence the union of the languages of the
         states reached on [x] *)
      assert (Hr'union : Res.lang_eq r' (union (map (N.L_state n) (N.run n x)))). {
          intro w. rewrite (Hx w).
          rewrite <- (inverse_L_aut_union n x w).
          unfold Res.inverse, N.L_aut.
          apply Bool.eq_true_iff_eq. split; intro Hm.
              now apply Henc.
          now apply (proj2 (Henc (x ++ w))). }
      rewrite (Hr'union v) in Hr'v. unfold union in Hr'v.
      apply existsb_exists in Hr'v. destruct Hr'v as (g & Hg & Hgv).
      apply in_map_iff in Hg. destruct Hg as (q' & Hq'eq & Hq'run).
      subst g.
      (* L_state q' is included in r', which is included in L_state q *)
      assert (Hincl : forall w, N.L_state n q' w = true -> N.L_state n q w = true). {
          intros w Hw. rewrite (Hunion w). unfold union.
          apply existsb_exists. exists r'. split; [apply Hr'in |].
          rewrite (Hr'union w). unfold union. apply existsb_exists.
          exists (N.L_state n q'). split; [| apply Hw].
          apply in_map_iff. now exists q'. }
      (* the inclusion is strict: otherwise [r'] would equal L_state q *)
      assert (Hne : ~ Res.lang_eq (N.L_state n q') (N.L_state n q)). {
          intro Heq. apply Hr'neq. intro w. apply Bool.eq_true_iff_eq. split.
          - intro Hw. rewrite (Hunion w). unfold union.
            apply existsb_exists. now exists r'.
          - intro Hw. rewrite (Hr'union w). unfold union.
            apply existsb_exists. exists (N.L_state n q'). split.
                apply in_map_iff. now exists q'.
            rewrite (Heq w). apply Hw. }
      exists (proj1_sig q'). split.
          apply state_row_index.
      split.
      + split.
        * apply (state_lang_incl_covered H Hcl Hco q' q Hincl).
        * intro Hrow. apply Hne. now apply row_eq_lang_eq.
      + rewrite <- (state_lang_cell H Hcl q' v HvV). apply Hgv.
    - intros (u' & Hu'idx & (Hcov & _) & Hu'v).
      apply (Hcov v HvV Hu'v).
Qed.

Lemma make_nfa_canonical_of_encodes : forall H (Hcl : Hclosed H) (Hco : Hconsistent H),
    encodes (make_nfa H) ->
    { r : R.t { q | memr H q = true } | R.nfa _ r = make_nfa H /\ canonical r }.
Proof.
    intros. exists (make_nfa_canonical H Hcl Hco (nfa_encodes_consistent H H0)).
    unfold make_nfa_canonical. simpl.
    split.
        reflexivity.
    split.
        unfold encodes in *. intros. simpl. split; intro.
            now rewrite <- H0.
            now rewrite H0.
    intros. simpl in *. now apply (state_lang_prime H Hcl Hco).
Qed.

Definition num_states (H : HypothesisRFSA) : nat :=
    List.length (make_nfa H).(states _).

(* Deduplicate a list of access strings modulo [row_eq]: keep a string only if
   no earlier-kept string has the same row. *)
Fixpoint dedup_rows (T V : str -> bool) (finV : finite V) (l : list str) : list str :=
    match l with
    | [] => []
    | u :: us =>
        let ded := dedup_rows T V finV us in
        if existsb (fun u' => if row_eq_dec T V u u' finV then true else false) ded
        then ded
        else u :: ded
    end.

(* The rows kept by [dedup_rows] are pairwise row-distinct. *)
Lemma dedup_rows_distinct : forall T V finV l u1 u2,
    In u1 (dedup_rows T V finV l) ->
    In u2 (dedup_rows T V finV l) ->
    row_eq T V u1 u2 -> u1 = u2.
Proof.
    intros T V finV l. induction l as [| u us IH]; intros a b Ha Hb Hrow.
        destruct Ha.
    simpl in Ha, Hb.
    destruct (existsb (fun u' => if row_eq_dec T V u u' finV then true else false)
                      (dedup_rows T V finV us)) eqn:E.
    - now apply IH.
    - (* u :: dedup us; u is row-distinct from all of dedup us *)
      assert (Hnew : forall x, In x (dedup_rows T V finV us) -> ~ row_eq T V u x). {
          intros x Hx Hrx. 
          assert (existsb (fun u' => if row_eq_dec T V u u' finV then true else false)
                          (dedup_rows T V finV us) = true). {
              apply existsb_exists. exists x. split; [assumption |].
              destruct (row_eq_dec T V u x finV); [reflexivity | contradiction]. }
          rewrite E in H. discriminate. }
      destruct Ha as [<- | Ha], Hb as [<- | Hb].
      + reflexivity.
      + exfalso. apply (Hnew b Hb Hrow).
      + exfalso. apply (Hnew a Ha). intro v. intro Hv. symmetry. now apply Hrow.
      + now apply IH.
Qed.

Lemma dedup_rows_incl : forall T V finV l x,
    In x (dedup_rows T V finV l) -> In x l.
Proof.
    intros T V finV l. induction l as [| u us IH]; intros x Hx.
        destruct Hx.
    simpl in Hx. destruct existsb eqn:E.
    - right. now apply IH.
    - destruct Hx as [<- | Hx]; [now left | right; now apply IH].
Qed.

Lemma dedup_rows_NoDup : forall T V finV l,
    NoDup (dedup_rows T V finV l).
Proof.
    intros T V finV l. induction l as [| u us IH].
        constructor.
    simpl. destruct existsb eqn:E; [assumption |].
    constructor; [| assumption].
    intro Hin.
    assert (existsb (fun u' => if row_eq_dec T V u u' finV then true else false)
                    (dedup_rows T V finV us) = true). {
        apply existsb_exists. exists u. split; [assumption |].
        destruct (row_eq_dec T V u u finV) as [_ | Hne]; [reflexivity |].
        exfalso. apply Hne. intros v _. reflexivity. }
    rewrite E in H. discriminate.
Qed.

(* Adding a row whose row is new keeps it. *)
Lemma dedup_rows_cons_new : forall T V finV u l,
    (forall x, In x l -> ~ row_eq T V u x) ->
    dedup_rows T V finV (u :: l) = u :: dedup_rows T V finV l.
Proof.
    intros T V finV u l Hnew. simpl.
    destruct (existsb (fun u' => if row_eq_dec T V u u' finV then true else false)
                      (dedup_rows T V finV l)) eqn:E; [| reflexivity].
    exfalso. apply existsb_exists in E. destruct E as (x & Hx & Hxe).
    destruct (row_eq_dec T V u x finV) as [Heq |]; [| discriminate].
    apply (Hnew x (dedup_rows_incl T V finV l x Hx) Heq).
Qed.

(* Every element of the list is represented in the deduplicated list. *)
Lemma dedup_rows_complete : forall T V finV l x,
    In x l -> exists y, In y (dedup_rows T V finV l) /\ row_eq T V x y.
Proof.
    intros T V finV l. induction l as [| u us IH]; intros x Hx.
        destruct Hx.
    simpl. destruct (existsb (fun u' => if row_eq_dec T V u u' finV then true else false)
                             (dedup_rows T V finV us)) eqn:E.
    - destruct Hx as [<- | Hx].
      + apply existsb_exists in E. destruct E as (y & Hy & Hye).
        destruct (row_eq_dec T V u y finV) as [Heq |]; [| discriminate].
        now exists y.
      + now apply IH.
    - destruct Hx as [<- | Hx].
      + exists u. split; [now left | apply row_eq_refl].
      + destruct (IH x Hx) as (y & Hy & Hye). exists y. split; [now right | apply Hye].
Qed.

(* The table cells of a hypothesis agree with the target on every row of the
   table, so row equality may be computed with [member] throughout. *)
Lemma row_eq_member : forall H u1 u2,
    In u1 (row_index (Ul H)) -> In u2 (row_index (Ul H)) ->
    (row_eq H.(T) H.(V) u1 u2 <-> row_eq member H.(V) u1 u2).
Proof.
    intros H u1 u2 H1 H2. unfold row_eq, cell. split; intros Hr v Hv.
    - rewrite <- (H.(tbl) u1 v H1 Hv), <- (H.(tbl) u2 v H2 Hv). now apply Hr.
    - rewrite (H.(tbl) u1 v H1 Hv), (H.(tbl) u2 v H2 Hv). now apply Hr.
Qed.

Lemma covered_member : forall H u1 u2,
    In u1 (row_index (Ul H)) -> In u2 (row_index (Ul H)) ->
    (covered H.(T) H.(V) u1 u2 <-> covered member H.(V) u1 u2).
Proof.
    intros H u1 u2 H1 H2. unfold covered, cell. split; intros Hc v Hv Hcv.
    - rewrite <- (H.(tbl) u2 v H2 Hv). apply Hc; [apply Hv |].
      rewrite (H.(tbl) u1 v H1 Hv). apply Hcv.
    - rewrite (H.(tbl) u2 v H2 Hv). apply Hc; [apply Hv |].
      rewrite <- (H.(tbl) u1 v H1 Hv). apply Hcv.
Qed.

(* The number of distinct rows of the table (upper and lower). *)
Definition num_distinct_rows (H : HypothesisRFSA) : nat :=
    List.length (dedup_rows H.(T) H.(V) H.(fin_V) (row_index (Ul H))).

(* A map that is Leibniz-injective on a NoDup list produces a NoDup image. *)
Lemma NoDup_map_inj : forall {A B} (f : A -> B) (l : list A),
    NoDup l ->
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup (map f l).
Proof.
    intros A B f l. induction l as [| a l IH]; intros ND Hinj; simpl.
        constructor.
    apply NoDup_cons_iff in ND as (Hnin & ND').
    constructor.
    - intro Hin. apply in_map_iff in Hin. destruct Hin as (y & Hfy & Hy).
      assert (a = y) by (apply Hinj; [now left | now right | now rewrite Hfy]).
      subst y. contradiction.
    - apply IH; [assumption |].
      intros x y Hx Hy. apply Hinj; now right.
Qed.

(* Two access strings that are rows of the table and induce the same residual
   have equal rows over V (uses the truthfulness of in-scope cells). *)
Lemma residual_eq_row_eq : forall H u1 u2,
    In u1 (row_index (Ul H)) -> In u2 (row_index (Ul H)) ->
    Res.lang_eq (Res.inverse member u1) (Res.inverse member u2) ->
    row_eq H.(T) H.(V) u1 u2.
Proof.
    intros H u1 u2 Hu1 Hu2 Heq v Hv. unfold cell.
    rewrite (H.(tbl) u1 v Hu1 Hv), (H.(tbl) u2 v Hu2 Hv). apply (Heq v).
Qed.

Lemma map_lang_pos_distinct :
    forall {A} (f : A -> Res.lang) (l : list A) (dA : A),
    NoDup l ->
    (forall x y, In x l -> In y l -> Res.lang_eq (f x) (f y) -> x = y) ->
    forall i j, i < length (map f l) -> j < length (map f l) ->
      Res.lang_eq (nth i (map f l) (fun _ => false)) (nth j (map f l) (fun _ => false)) ->
      i = j.
Proof.
    intros A f l dA ND Hinj i j Hi Hj Heq.
    rewrite length_map in Hi, Hj.
    rewrite (nth_indep (map f l) (fun _ => false) (f dA)) in Heq by (rewrite length_map; apply Hi).
    rewrite (nth_indep (map f l) (fun _ => false) (f dA)) in Heq
      by (rewrite length_map; apply Hj).
    rewrite !(map_nth f l dA) in Heq.
    assert (Hxy : nth i l dA = nth j l dA)
      by (apply Hinj; [apply nth_In; apply Hi | apply nth_In; apply Hj | apply Heq]).
    apply (NoDup_nth l dA) in Hxy; assumption.
Qed.

Lemma num_distinct_rows_le : forall H,
    num_distinct_rows H <= L.num_residuals.
Proof.
    intros H. unfold num_distinct_rows.
    set (D := dedup_rows H.(T) H.(V) H.(fin_V) (row_index (Ul H))).
    assert (Hincl : forall x, In x D -> In x (row_index (Ul H)))
        by (intros x Hx; apply (dedup_rows_incl _ _ _ _ _ Hx)).
    assert (Hinj : forall u1 u2, In u1 D -> In u2 D ->
              Res.lang_eq (Res.inverse member u1) (Res.inverse member u2) -> u1 = u2). {
        intros u1 u2 H1 H2 Heq.
        apply (dedup_rows_distinct H.(T) H.(V) H.(fin_V) (row_index (Ul H)) u1 u2 H1 H2).
        apply residual_eq_row_eq; auto. }
    rewrite <- (length_map (Res.inverse member) D).
    apply L.residuals_bounded.
    - intros r Hr. apply in_map_iff in Hr. destruct Hr as (u & <- & Hu).
      exists u. intro w. reflexivity.
    - apply (map_lang_pos_distinct (Res.inverse member) D []).
      + apply (dedup_rows_NoDup H.(T) H.(V) H.(fin_V)).
      + apply Hinj.
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

(* [le] on [nat] is stable under double negation. *)
Lemma nn_le : forall m n : nat, ~ ~ (m <= n) -> m <= n.
Proof.
    intros m n Hnn. destruct (Compare_dec.le_dec m n) as [Hle | Hgt].
        apply Hle.
    exfalso. now apply Hnn.
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

(* In any RFSA that encodes L, every prime residual of L is realised by one of
   its states. *)
Lemma prime_residual_realized_nn :
    forall {state} (r : R.t state),
    encodes (R.nfa _ r) ->
    forall rho, L.prime rho ->
    ~ ~ (exists q, In q (N.states _ (R.nfa _ r))
                   /\ Res.lang_eq (N.L_state (R.nfa _ r) q) rho).
Proof.
    intros state r Henc rho (Hres & Hncomp).
    destruct Hres as (u & Hu).
    set (n := R.nfa _ r).
    assert (HeqL : Res.lang_eq (Res.inverse member u) (Res.inverse (N.L_aut n) u)). {
        intro w. unfold Res.inverse, N.L_aut, N.accept_string.
        apply Bool.eq_true_iff_eq. split; intro Hm.
            now apply Henc.
        now apply (proj2 (Henc (u ++ w))). }
    set (qs := N.run n u).
    assert (Hunion : Res.lang_eq rho (union (map (N.L_state n) qs))). {
        intro w. rewrite Hu, HeqL. apply (inverse_L_aut_union n u w). }
    assert (Hstates : forall q, In q qs -> In q (N.states _ n))
        by (intros q Hq; apply (N.states_complete _ n u q Hq)).
    assert (Hres_state : forall q, In q qs -> L.residual (N.L_state n q)). {
        intros q Hq.
        destruct (R.states_are_residuals _ r q (Hstates q Hq)) as (x & Hx).
        exists x. intro w. rewrite Hx. unfold Res.inverse, N.L_aut.
        apply Bool.eq_true_iff_eq. split; intro Hm.
            now apply (proj2 (Henc (x ++ w))).
        now apply Henc. }
    intro Hno.
    apply Hncomp. split; [now exists u |].
    exists (map (N.L_state n) qs). split.
    - intros r' Hr'. apply in_map_iff in Hr'. destruct Hr' as (q & <- & Hq).
      split; [now apply Hres_state |].
      intro Heq. apply Hno.
      exists q. split; [now apply Hstates | apply Heq].
    - apply Hunion.
Qed.

(* If two access strings induce the same residual of
   [member], their rows agree on every column of V. *)
Lemma lang_eq_residual_row_eq : forall H u1 u2,
    In u1 (row_index (Ul H)) -> In u2 (row_index (Ul H)) ->
    Res.lang_eq (Res.inverse member u1) (Res.inverse member u2) ->
    row_eq H.(T) H.(V) u1 u2.
Proof.
    intros H u1 u2 Hu1 Hu2 Heq v Hv. unfold cell.
    rewrite (H.(tbl) u1 v Hu1 Hv), (H.(tbl) u2 v Hu2 Hv). apply (Heq v).
Qed.

(* The number of states of a hypothesis is bounded by the number of prime
   residuals of L, hence by [num_states_in_canonical]. *)
Lemma num_states_le_canonical : forall H,
    Hclosed H -> Hconsistent H -> Hrep H -> Hsep H -> Hdense H ->
    num_states H <= L.num_states_in_canonical.
Proof.
    intros H Hcl Hco Hr Hsp Hdn.
    assert (Hns : num_states H = length (prime_reps H.(T) H.(V) (Ul H) H.(fin_V))). {
        unfold num_states, make_nfa. simpl. apply list_with_proof_preserves_len. }
    rewrite Hns. clear Hns.
    set (PR := prime_reps H.(T) H.(V) (Ul H) H.(fin_V)).
    assert (HNDpr : NoDup PR).
    { unfold PR, prime_reps. apply NoDup_filter.
      unfold Ul. destruct H.(fin_U) as (l & Hnd & ?). apply Hnd. }
    destruct L.exists_rfsa as (st & rc & (Henc & _) & _ & Hlen).
    set (n := R.nfa _ rc).
    set (Qs := N.states _ n).
    set (idx := seq 0 (length Qs)).
    set (Rel := fun (u : str) (i : nat) =>
        exists q, nth_error Qs i = Some q
                  /\ Res.lang_eq (N.L_state n q) (Res.inverse member u)).
    assert (seq_len : forall (k start : nat), length (seq start k) = k).
    { induction k as [| k IH]; intros start; [reflexivity |]. simpl. now rewrite IH. }
    assert (Hidxlen : length idx = length Qs) by (unfold idx; apply seq_len).
    enough (Hle : length PR <= length idx).
    { rewrite Hidxlen in Hle. unfold Qs, n in Hle. lia. }
    apply nn_le.
    assert (Htot_nn : forall u, In u PR -> ~ ~ (exists i, In i idx /\ Rel u i)). {
        intros u Hu.
        assert (Hprime : L.prime (Res.inverse member u)).
            apply Hdn. now unfold PR in Hu.
        pose proof (prime_residual_realized_nn rc Henc _ Hprime) as Hnn.
        intro Hcon. apply Hnn. intros (q & HqQ & Hlangeq).
        apply Hcon.
        destruct (In_nth_error _ _ HqQ) as (i & Hnth).
        exists i. split.
        - unfold idx. apply in_seq. split; [lia |].
          rewrite Nat.add_0_l.
          apply (proj1 (nth_error_Some Qs i)).
          unfold Qs, n. rewrite Hnth. discriminate.
        - exists q. split; [apply Hnth | apply Hlangeq]. }
    assert (Hinj : forall u1 u2 i, In u1 PR -> In u2 PR ->
                     Rel u1 i -> Rel u2 i -> u1 = u2). {
        intros u1 u2 i Hu1 Hu2 (q1 & Hnth1 & He1) (q2 & Hnth2 & He2).
        assert (q1 = q2) by (rewrite Hnth1 in Hnth2; now inversion Hnth2). subst q2.
        assert (Heqr : Res.lang_eq (Res.inverse member u1) (Res.inverse member u2)). {
            intro w. rewrite <- (He1 w), <- (He2 w). reflexivity. }
        apply (Hsp u1 u2
                 (prime_reps_upper H.(T) H.(V) (Ul H) H.(fin_V) u1 Hu1)
                 (prime_reps_upper H.(T) H.(V) (Ul H) H.(fin_V) u2 Hu2)).
        apply (lang_eq_residual_row_eq H u1 u2
                 (prime_reps_index H.(T) H.(V) (Ul H) H.(fin_V) u1 Hu1)
                 (prime_reps_index H.(T) H.(V) (Ul H) H.(fin_V) u2 Hu2)
                 Heqr). }
    pose proof (nn_forall_list PR (fun u => exists i, In i idx /\ Rel u i) Htot_nn) as Hnn_tot.
    intro Hcon. apply Hnn_tot. intro Htot.
    apply Hcon.
    apply (relational_pigeonhole (list_eq_dec eq_dec) Nat.eq_dec Rel PR idx HNDpr).
    - intros u Hu. destruct (Htot u Hu) as (i & Hi & HR). now exists i.
    - apply Hinj.
Qed.

(* The number of states is bounded by the number of residuals of L. *)
Lemma num_states_le_num_residuals : forall H,
    Hsep H -> num_states H <= L.num_residuals.
Proof.
    intros H Hsp.
    assert (Hns : num_states H = length (prime_reps H.(T) H.(V) (Ul H) H.(fin_V))). {
        unfold num_states, make_nfa. simpl. apply list_with_proof_preserves_len. }
    rewrite Hns. clear Hns.
    set (PR := prime_reps H.(T) H.(V) (Ul H) H.(fin_V)).
    assert (HNDpr : NoDup PR).
    { unfold PR, prime_reps. apply NoDup_filter.
      unfold Ul. destruct H.(fin_U) as (l & Hnd & ?). apply Hnd. }
    assert (Hidx : forall u, In u PR -> In u (row_index (Ul H)))
        by (intros u Hu; apply (prime_reps_index H.(T) H.(V) (Ul H) H.(fin_V) u Hu)).
    assert (Hupp : forall u, In u PR -> In u (Ul H))
        by (intros u Hu; apply (prime_reps_upper H.(T) H.(V) (Ul H) H.(fin_V) u Hu)).
    assert (Hinj : forall u1 u2, In u1 PR -> In u2 PR ->
              Res.lang_eq (Res.inverse member u1) (Res.inverse member u2) -> u1 = u2). {
        intros u1 u2 H1 H2 Heq.
        apply (Hsp u1 u2 (Hupp u1 H1) (Hupp u2 H2)).
        apply (residual_eq_row_eq H u1 u2 (Hidx u1 H1) (Hidx u2 H2)). apply Heq. }
    rewrite <- (length_map (Res.inverse member) PR).
    apply L.residuals_bounded.
    - intros r Hr. apply in_map_iff in Hr. destruct Hr as (u & <- & Hu).
      exists u. intro w. reflexivity.
    - apply (map_lang_pos_distinct (Res.inverse member) PR []); assumption.
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

Definition extend_table_ce : forall (H : HypothesisRFSA) (w : str),
    N.accept_string (make_nfa H) w <> member w -> HypothesisRFSA.
Proof.
    intros H w Hce.
    set (sufs := filter (fun s => negb (H.(V) s)) (suffixes w)).
    set (V' :=
        fun s =>
            match find (fun s' => if str_eq s s' then true else false) sufs with
            | None => H.(V) s
            | Some _ => true
            end
    ).
    destruct H; simpl in *. eapply Build_HypothesisRFSA with (T := member) (V := V'); eauto.
    - (* fin_V' : finite V' *)
      destruct fin_V0, a. exists (x ++ sufs). split.
        apply NoDup_app. assumption.
            apply NoDup_filter, NoDup_suffixes.
        intros. intro Contra.
        destruct (V' a) eqn:E; unfold V' in E.
            destruct find eqn:E0 in E.
                unfold sufs in E0. apply find_some in E0. destruct E0.
                destruct (str_eq a s); [|discriminate]. subst.
                apply filter_In in H0. destruct H0. apply Bool.negb_true_iff in H2.
                pose proof (i s). destruct (V0 s). discriminate. apply H3 in H. discriminate.
            eapply find_none in E0; eauto. now destruct (str_eq a a).
        destruct find eqn:E0 in E. discriminate.
            pose proof (i a). destruct (V0 a). discriminate. apply H0 in H. discriminate.
        intros. unfold V'. split; intro.
            apply in_or_app. destruct find eqn:E in H.
                apply find_some in E. destruct E. unfold sufs in H0.
                destruct (str_eq s s0). subst. now right.
                discriminate.
            apply i in H. now left.
        destruct find eqn:E. reflexivity.
        apply i. apply in_app_or in H. destruct H. assumption.
        eapply find_none in E; eauto. now destruct (str_eq s s).
    - (* suff for V' *)
      intros. unfold V' in *. destruct find eqn:E.
      + apply find_some in E. destruct E. unfold sufs in *.
        apply filter_In in H0. destruct H0, (str_eq (w0 ++ w') s); [|discriminate].
        subst s. destruct find eqn:E. reflexivity.
        destruct fin_V0, a.
        assert (Hw'suf : In w' (suffixes w)) by eauto using app_in_suffixes.
        destruct (V0 w') eqn:E0; [reflexivity|exfalso].
        assert (In w' sufs). {
            unfold sufs. apply filter_In. split. assumption.
            now rewrite E0. }
        eapply find_none in E; [|eassumption]. now destruct (str_eq w' w').
      + assert (HV0 : V0 (w0 ++ w') = true) by now destruct find in E.
        destruct find eqn:E0 in |- *; eauto.
    - (* eps_V for V' *)
      unfold V'. destruct find. reflexivity. apply eps_V0.
    Unshelve.
    apply fin_U0.
Defined.

Lemma filter_len_le : forall {A} (f : A -> bool) l, length (filter f l) <= length l.
Proof.
  intros A f l. induction l as [| x l IH]; simpl; [lia |].
  destruct (f x); simpl; lia.
Qed.

Definition sigma_size : nat := List.length s.enum.

(* An upper part of at most [num_residuals] strings contributes a row index of
   at most [row_bound] strings. *)
Definition row_bound : nat := L.num_residuals * (1 + sigma_size).

Lemma USigma_length : forall l, List.length (USigma l) = List.length l * sigma_size.
Proof.
    unfold USigma, sigma_size. induction l as [| u l IH]; simpl.
        reflexivity.
    now rewrite length_app, length_map, <- IH.
Qed.

Lemma row_index_length : forall l,
    List.length (row_index l) = List.length l + List.length l * sigma_size.
Proof.
    intros l. unfold row_index. rewrite length_app, USigma_length. reflexivity.
Qed.

Lemma in_Ul_row_index : forall (l : list str) u,
    In u l -> In u (row_index l).
Proof. intros l u Hu. unfold row_index. apply in_or_app. now left. Qed.

(* Separated upper parts are no bigger than the number of residuals. *)
Lemma Ul_le : forall H, Hsep H -> List.length (Ul H) <= L.num_residuals.
Proof.
    intros H Hsp.
    rewrite <- (length_map (Res.inverse member) (Ul H)).
    apply L.residuals_bounded.
    - intros r Hr. apply in_map_iff in Hr. destruct Hr as (u & <- & Hu).
      exists u. intro w. reflexivity.
    - apply (map_lang_pos_distinct (Res.inverse member) (Ul H) []).
      + apply (proj1 (proj2_sig H.(fin_U))).
      + intros u1 u2 H1 H2 Heq. apply (Hsp u1 u2 H1 H2).
        apply (residual_eq_row_eq H u1 u2); auto using in_Ul_row_index.
Qed.

Lemma row_index_le : forall H, Hsep H ->
    List.length (row_index (Ul H)) <= row_bound.
Proof.
    intros H Hsp. rewrite row_index_length. unfold row_bound.
    pose proof (Ul_le H Hsp). nia.
Qed.

Definition l_up (H : HypothesisRFSA) : nat :=
    List.length (dedup_rows member H.(V) H.(fin_V) (Ul H)).

Definition eqp (H : HypothesisRFSA) : nat :=
    List.length
      (filter (fun p => if row_eq_dec member H.(V) (fst p) (snd p) H.(fin_V)
                        then true else false)
              (list_prod (row_index (Ul H)) (row_index (Ul H)))).

Definition icov (H : HypothesisRFSA) : nat :=
    List.length
      (filter (fun p => if strictly_covered_dec member H.(V) (fst p) (snd p) H.(fin_V)
                        then true else false)
              (list_prod (row_index (Ul H)) (row_index (Ul H)))).

Lemma l_up_le : forall H, l_up H <= L.num_residuals.
Proof.
    intros H. unfold l_up.
    set (D := dedup_rows member H.(V) H.(fin_V) (Ul H)).
    rewrite <- (length_map (Res.inverse member) D).
    apply L.residuals_bounded.
    - intros r Hr. apply in_map_iff in Hr. destruct Hr as (u & <- & Hu).
      exists u. intro w. reflexivity.
    - apply (map_lang_pos_distinct (Res.inverse member) D []).
      + apply dedup_rows_NoDup.
      + intros u1 u2 H1 H2 Heq.
        apply (dedup_rows_distinct member H.(V) H.(fin_V) (Ul H) u1 u2 H1 H2).
        intros v _. apply (Heq v).
Qed.

Lemma eqp_le : forall H, Hsep H -> eqp H <= row_bound * row_bound.
Proof.
    intros H Hsp. unfold eqp.
    eapply Nat.le_trans; [apply filter_len_le |].
    rewrite length_prod.
    pose proof (row_index_le H Hsp). now apply Nat.mul_le_mono.
Qed.

Lemma icov_le : forall H, Hsep H -> icov H <= row_bound * row_bound.
Proof.
    intros H Hsp. unfold icov.
    eapply Nat.le_trans; [apply filter_len_le |].
    rewrite length_prod.
    pose proof (row_index_le H Hsp). now apply Nat.mul_le_mono.
Qed.

Definition nprime (H : HypothesisRFSA) : nat :=
    List.length
      (filter (fun x => if prime_dec member H.(V) (Ul H) x H.(fin_V)
                        then true else false)
              (row_index (Ul H))).

Lemma nprime_le : forall H, Hsep H -> nprime H <= row_bound.
Proof.
    intros H Hsp. unfold nprime.
    eapply Nat.le_trans; [apply filter_len_le | now apply row_index_le].
Qed.

Definition ce_K : nat := row_bound * row_bound + 1.
Definition ce_K2 : nat := (row_bound + 1) * ce_K.
Definition ce_K1 : nat := ce_K * ce_K2.

Definition ce_measure (H : HypothesisRFSA) : nat :=
    (L.num_residuals - l_up H) * ce_K1
  + eqp H * ce_K2
  + (row_bound - nprime H) * ce_K
  + icov H.

Lemma ce_tail3_lt : forall H, icov H <= row_bound * row_bound -> icov H < ce_K.
Proof. intros H Hi. unfold ce_K. lia. Qed.

Lemma ce_tail2_lt : forall H, icov H <= row_bound * row_bound ->
    (row_bound - nprime H) * ce_K + icov H < ce_K2.
Proof.
    intros H Hi.
    assert (Hle : (row_bound - nprime H) * ce_K <= row_bound * ce_K)
        by (apply Nat.mul_le_mono_r; lia).
    pose proof (ce_tail3_lt H Hi).
    unfold ce_K2. rewrite Nat.mul_add_distr_r, Nat.mul_1_l. lia.
Qed.

Lemma ce_tail1_lt : forall H,
    eqp H <= row_bound * row_bound -> icov H <= row_bound * row_bound ->
    eqp H * ce_K2 + (row_bound - nprime H) * ce_K + icov H < ce_K1.
Proof.
    intros H He Hi.
    assert (HeK : eqp H + 1 <= ce_K) by (unfold ce_K; lia).
    pose proof (Nat.mul_le_mono_r _ _ ce_K2 HeK) as H1.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l in H1.
    pose proof (ce_tail2_lt H Hi).
    unfold ce_K1. lia.
Qed.

(* Case (1): the number of distinct upper rows increases. *)
Lemma ce_measure_lt_up : forall A B,
    l_up A < l_up B -> l_up B <= L.num_residuals ->
    eqp B <= row_bound * row_bound -> icov B <= row_bound * row_bound ->
    ce_measure B < ce_measure A.
Proof.
    intros A B Hlt Hbnd He Hi. unfold ce_measure.
    assert (Hsub : S (L.num_residuals - l_up B) <= L.num_residuals - l_up A) by lia.
    pose proof (Nat.mul_le_mono_r _ _ ce_K1 Hsub) as Hmul.
    rewrite Nat.mul_succ_l in Hmul.
    pose proof (ce_tail1_lt B He Hi). nia.
Qed.

(* Case (2): the upper rows are unchanged and two rows have been separated. *)
Lemma ce_measure_lt_eqp : forall A B,
    l_up A = l_up B -> eqp B < eqp A ->
    icov B <= row_bound * row_bound ->
    ce_measure B < ce_measure A.
Proof.
    intros A B Hup Hlt Hi. unfold ce_measure. rewrite Hup.
    assert (Hsub : S (eqp B) <= eqp A) by lia.
    pose proof (Nat.mul_le_mono_r _ _ ce_K2 Hsub) as Hmul.
    rewrite Nat.mul_succ_l in Hmul.
    pose proof (ce_tail2_lt B Hi). nia.
Qed.

(* Case (3a): nothing was separated, but a row became prime. *)
Lemma ce_measure_lt_nprime : forall A B,
    l_up A = l_up B -> eqp A = eqp B ->
    nprime A < nprime B -> nprime B <= row_bound ->
    icov B <= row_bound * row_bound ->
    ce_measure B < ce_measure A.
Proof.
    intros A B Hup Heq Hlt Hbnd Hi. unfold ce_measure. rewrite Hup, Heq.
    assert (Hsub : S (row_bound - nprime B) <= row_bound - nprime A) by lia.
    pose proof (Nat.mul_le_mono_r _ _ ce_K Hsub) as Hmul.
    rewrite Nat.mul_succ_l in Hmul.
    pose proof (ce_tail3_lt B Hi). lia.
Qed.

(* Case (3b): nothing was separated and no row became prime, but a strict
   covering was destroyed. *)
Lemma ce_measure_lt_icov : forall A B,
    l_up A = l_up B -> eqp A = eqp B -> nprime A = nprime B ->
    icov B < icov A ->
    ce_measure B < ce_measure A.
Proof.
    intros A B H1 H2 H3 H4. unfold ce_measure. rewrite H1, H2, H3. lia.
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

(* Refining the columns can only increase the number of distinct rows. *)
Lemma dedup_rows_len_mono : forall T V1 V2 (f1 : finite V1) (f2 : finite V2) l,
    (forall v, V1 v = true -> V2 v = true) ->
    length (dedup_rows T V1 f1 l) <= length (dedup_rows T V2 f2 l).
Proof.
    intros T V1 V2 f1 f2 l Hsub.
    apply (relational_pigeonhole (list_eq_dec eq_dec) (list_eq_dec eq_dec)
             (fun x y => row_eq T V2 x y)
             (dedup_rows T V1 f1 l) (dedup_rows T V2 f2 l)).
    - apply dedup_rows_NoDup.
    - intros x Hx.
      destruct (dedup_rows_complete T V2 f2 l x
                  (dedup_rows_incl T V1 f1 l x Hx)) as (y & Hy & Hxy).
      now exists y.
    - intros x1 x2 y Hx1 Hx2 Hr1 Hr2.
      apply (dedup_rows_distinct T V1 f1 l x1 x2 Hx1 Hx2).
      intros w Hw. rewrite Hr1, Hr2; auto.
Qed.

Lemma ce_measure_add_column :
    forall (H H' : HypothesisRFSA),
      Hsep H' ->
      Ul H' = Ul H ->
      (forall x, H.(V) x = true -> H'.(V) x = true) ->
      ((exists u u', In u (row_index (Ul H)) /\ In u' (row_index (Ul H))
                     /\ covered member H.(V) u u'
                     /\ ~ covered member H'.(V) u u')
       \/ (exists x, In x (row_index (Ul H))
                     /\ ~ prime member H.(V) (Ul H) x
                     /\ prime member H'.(V) (Ul H) x)) ->
      ce_measure H' < ce_measure H.
Proof.
    intros H H' Hsp' HUl HVsub Hprog.
    assert (Hreq : forall x y, row_eq member H'.(V) x y -> row_eq member H.(V) x y)
        by (intros x y Hr w Hw; apply Hr, HVsub, Hw).
    assert (Hcovmono : forall x y,
              covered member H'.(V) x y -> covered member H.(V) x y)
        by (intros x y Hc w Hw; apply Hc, HVsub, Hw).
    assert (HRI : row_index (Ul H') = row_index (Ul H)) by (now rewrite HUl).
    (* the number of distinct upper rows can only grow *)
    assert (Hlup : l_up H <= l_up H'). {
        unfold l_up. rewrite HUl.
        apply (dedup_rows_len_mono member H.(V) H'.(V) H.(fin_V) H'.(fin_V)
                 (Ul H) HVsub). }
    destruct (Nat.eq_dec (l_up H) (l_up H')) as [Hlupeq | Hlupne].
    2: { apply ce_measure_lt_up.
         - lia.
         - apply l_up_le.
         - now apply eqp_le.
         - now apply icov_le. }
    (* the row-equal pairs can only disappear *)
    assert (Heqpimp : forall x,
              In x (list_prod (row_index (Ul H)) (row_index (Ul H))) ->
              (if row_eq_dec member H'.(V) (fst x) (snd x) H'.(fin_V)
               then true else false) = true ->
              (if row_eq_dec member H.(V) (fst x) (snd x) H.(fin_V)
               then true else false) = true). {
        intros x _ Hx.
        destruct (row_eq_dec member H'.(V) (fst x) (snd x) H'.(fin_V)) as [Hr |];
          [| discriminate].
        destruct (row_eq_dec member H.(V) (fst x) (snd x) H.(fin_V)) as [| Hn];
          [reflexivity |].
        exfalso. apply Hn. now apply Hreq. }
    assert (Heqpmono : eqp H' <= eqp H). {
        unfold eqp. rewrite HRI. now apply filter_le_pointwise. }
    destruct (Nat.eq_dec (eqp H) (eqp H')) as [Heqpeq | Heqpne].
    2: { apply ce_measure_lt_eqp; [apply Hlupeq | lia | now apply icov_le]. }
    (* no pair was separated, so the two row equalities agree on the index *)
    assert (Hback : forall x y, In x (row_index (Ul H)) -> In y (row_index (Ul H)) ->
              row_eq member H.(V) x y -> row_eq member H'.(V) x y). {
        intros x y Hx Hy Hr.
        assert (Hpair : In (x, y) (list_prod (row_index (Ul H)) (row_index (Ul H))))
            by (apply in_prod_iff; now split).
        assert (Hlen : length (filter (fun q =>
                   if row_eq_dec member H'.(V) (fst q) (snd q) H'.(fin_V)
                   then true else false)
                   (list_prod (row_index (Ul H)) (row_index (Ul H))))
                 = length (filter (fun q =>
                   if row_eq_dec member H.(V) (fst q) (snd q) H.(fin_V)
                   then true else false)
                   (list_prod (row_index (Ul H)) (row_index (Ul H))))). {
            unfold eqp in Heqpeq. rewrite HRI in Heqpeq. lia. }
        pose proof (filter_eq_len_ext _ _ _ Heqpimp Hlen (x, y) Hpair) as Hext.
        simpl in Hext.
        destruct (row_eq_dec member H.(V) x y H.(fin_V)) as [| Hn]; [| contradiction].
        specialize (Hext eq_refl).
        now destruct (row_eq_dec member H'.(V) x y H'.(fin_V)). }
    (* hence strict covering can only be lost ... *)
    assert (Hscsub : forall x y, In x (row_index (Ul H)) -> In y (row_index (Ul H)) ->
              strictly_covered member H'.(V) x y ->
              strictly_covered member H.(V) x y). {
        intros x y Hx Hy (Hc & Hn). split.
          now apply Hcovmono.
        intro Hr. apply Hn. now apply Hback. }
    (* ... and therefore a composed row can only become prime *)
    assert (Hprimemono : forall x, In x (row_index (Ul H)) ->
              prime member H.(V) (Ul H) x -> prime member H'.(V) (Ul H) x). {
        intros x Hx (Hxi & Hnc). split; [apply Hxi |].
        intro Hc. apply Hnc. intros v Hv. split.
        - intro Hcell.
          destruct (proj1 (Hc v (HVsub v Hv)) Hcell) as (y & Hy & Hsc & Hyv).
          exists y. apply (conj Hy (conj (Hscsub y x Hy Hxi Hsc) Hyv)).
        - intros (y & Hy & Hsc & Hyv). destruct Hsc as (Hcov' & _).
          apply (Hcov' v Hv Hyv). }
    assert (Hnpimp : forall x,
              In x (row_index (Ul H)) ->
              (if prime_dec member H.(V) (Ul H) x H.(fin_V) then true else false) = true ->
              (if prime_dec member H'.(V) (Ul H) x H'.(fin_V) then true else false) = true). {
        intros x Hx Hxt.
        destruct (prime_dec member H.(V) (Ul H) x H.(fin_V)) as [Hp |];
          [| discriminate].
        destruct (prime_dec member H'.(V) (Ul H) x H'.(fin_V)) as [| Hn];
          [reflexivity |].
        exfalso. apply Hn. now apply Hprimemono. }
    assert (Hnpmono : nprime H <= nprime H'). {
        unfold nprime. rewrite HUl. now apply filter_le_pointwise. }
    destruct (Nat.eq_dec (nprime H) (nprime H')) as [Hnpeq | Hnpne].
    2: { apply ce_measure_lt_nprime;
         [apply Hlupeq | apply Heqpeq | lia | now apply nprime_le
          | now apply icov_le]. }
    destruct Hprog as [(u & u' & Hu & Hu' & Hcov & Hncov) | (x & Hx & Hnp & Hp)].
    2: { exfalso.
         assert (Hlt : nprime H < nprime H'). {
             unfold nprime. rewrite HUl.
             apply (filter_lt_pointwise _ _ _ x Hnpimp Hx).
             - now destruct (prime_dec member H'.(V) (Ul H) x H'.(fin_V)).
             - destruct (prime_dec member H.(V) (Ul H) x H.(fin_V)) as [Hc |].
                 now contradiction Hnp.
               reflexivity. }
         lia. }
    assert (Hicovimp : forall q,
              In q (list_prod (row_index (Ul H)) (row_index (Ul H))) ->
              (if strictly_covered_dec member H'.(V) (fst q) (snd q) H'.(fin_V)
               then true else false) = true ->
              (if strictly_covered_dec member H.(V) (fst q) (snd q) H.(fin_V)
               then true else false) = true). {
        intros (y & z) Hq Hqt.
        apply in_prod_iff in Hq. destruct Hq as (Hq1 & Hq2). simpl in *.
        destruct (strictly_covered_dec member H'.(V) y z H'.(fin_V))
          as [Hsc |]; [| discriminate].
        destruct (strictly_covered_dec member H.(V) y z H.(fin_V))
          as [| Hns]; [reflexivity |].
        exfalso. apply Hns. now apply Hscsub. }
    assert (Hnruu' : ~ row_eq member H.(V) u u'). {
        intro Hr. apply Hncov. intros q Hq Hcq.
        rewrite <- (Hback u u' Hu Hu' Hr q Hq). apply Hcq. }
    apply ce_measure_lt_icov; [apply Hlupeq | apply Heqpeq | apply Hnpeq |].
    unfold icov. rewrite HRI.
    apply (filter_lt_pointwise _ _ _ (u, u') Hicovimp).
    - apply in_prod_iff. now split.
    - simpl. destruct (strictly_covered_dec member H.(V) u u' H.(fin_V)) as [| Hn].
        reflexivity.
      exfalso. now apply Hn.
    - simpl. destruct (strictly_covered_dec member H'.(V) u u' H'.(fin_V))
        as [(Hc & _) |].
        exfalso. now apply Hncov.
      reflexivity.
Qed.

Lemma resolve_closedness :
    forall (H : HypothesisRFSA),
      Hsep H ->
      ~ Hclosed H ->
      { H' : HypothesisRFSA | Hsep H' /\ ce_measure H' < ce_measure H }.
Proof.
    intros H Hsp Hncl.
    destruct (closed_violation_dec H.(T) H.(V) (Ul H) H.(fin_V))
      as [(u0 & Hviol) | Hnone].
    2: { exfalso. apply Hncl. unfold Hclosed.
         apply (no_violation_closed H.(T) H.(V) H.(U) H.(fin_U) H.(fin_V) Hnone). }
    assert (Hu0low : In u0 (USigma (Ul H))) by (now destruct Hviol).
    assert (Hu0idx : In u0 (row_index (Ul H)))
        by (unfold row_index; apply in_or_app; now right).
    assert (Hu0new : forall w, In w (Ul H) -> ~ row_eq H.(T) H.(V) w u0)
        by (intros w Hw; apply (closed_violation_row_new _ _ _ _ _ _ Hviol Hw)).
    set (U' := fun x => (H.(U) x || (if str_eq x u0 then true else false))%bool).
    assert (Hu0nUl : ~ In u0 (Ul H))
        by (apply (closed_violation_not_upper _ _ _ _ _ Hviol)).
    assert (HfinU' : NoDup (u0 :: Ul H)
                     /\ forall x, U' x = true <-> In x (u0 :: Ul H)). {
      split.
        constructor; [apply Hu0nUl | apply (proj1 (proj2_sig H.(fin_U)))].
      intro x. unfold U'. rewrite Bool.orb_true_iff. simpl. split.
      - intros [Hx | Hx].
          right. now apply (proj2 (proj2_sig H.(fin_U)) x).
        destruct (str_eq x u0) as [-> |]; [now left | discriminate].
      - intros [-> | Hx].
          right. now destruct (str_eq x x); [reflexivity | contradiction].
        left. now apply (proj2 (proj2_sig H.(fin_U)) x). }
    set (finU' := exist (fun l => NoDup l /\ forall x, U' x = true <-> In x l)
                    (u0 :: Ul H) HfinU' : finite U').
    (* prefix-closedness of U' *)
    assert (prefU' : forall w w', U' (w ++ w') = true -> U' w = true). {
      intros w w' Hw. unfold U' in *. rewrite Bool.orb_true_iff in *.
      destruct Hw as [Hw | Hw].
      - left. apply (H.(pref) w w' Hw).
      - (* w ++ w' = u0.  Then w is a prefix of u0; either w in U or w = u0. *)
        destruct (str_eq (w ++ w') u0) as [Heq |]; [| discriminate].
        (* u0 in row_index: u0 in Ul, or u0 = u1 ++ [a] for u1 in Ul *)
        unfold row_index in Hu0idx. apply in_app_or in Hu0idx.
        destruct Hu0idx as [Hu0Ul | Hu0Sig].
        + (* u0 in Ul ⊆ U: w is a prefix of u0, so w ++ w' = u0 in U, giving U w *)
          left. apply (H.(pref) w w'). rewrite Heq.
          apply (proj2 (proj2_sig H.(fin_U)) u0) in Hu0Ul.
          apply Hu0Ul.
        + (* u0 = u1 ++ [a] with u1 in Ul.  w ++ w' = u1 ++ [a]. *)
          unfold USigma in Hu0Sig. apply in_flat_map in Hu0Sig.
          destruct Hu0Sig as (u1 & Hu1 & Ha). apply in_map_iff in Ha.
          destruct Ha as (a & Hau & _). subst u0.
          destruct w' as [| c w''] using rev_ind.
          * (* w' = [] : w = u1++[a] = u0 *)
            rewrite app_nil_r in Heq. right.
            destruct (str_eq w (u1 ++ [a])) as [_ | Hne]; [reflexivity |].
            exfalso. apply Hne. apply Heq.
          * (* w' = _ ++ [c] nonempty : w is a prefix of u1 *)
            left.
            (* w ++ (w'0 ++ [c]) = u1 ++ [a]; strip last elements: w ++ w'0 = u1 *)
            assert (Hpre : w ++ w'' = u1). {
              apply (app_inj_tail (w ++ w'') u1 c a).
              rewrite <- app_assoc. apply Heq. }
            apply (H.(pref) w w''). rewrite Hpre.
            now apply (proj2 (proj2_sig H.(fin_U)) u1). }
    (* Build H' with T := member, U := U', V unchanged *)
    unshelve eexists (Build_HypothesisRFSA member U' H.(V) finU' H.(fin_V)
                        prefU' H.(suff) _ H.(eps_V) _).
    - (* eps_U for U' *)
      unfold U'. rewrite H.(eps_U). reflexivity.
    - (* tbl : trivial since T := member *)
      intros u v _ _. reflexivity.
    - (* the three postconditions *)
      simpl.
      match goal with |- Hsep ?Hr /\ _ => assert (HsepH' : Hsep Hr) end.
      { intros u1 u2 Hu1 Hu2 Hrow.
        assert (Hmem : forall x, In x (Ul H) \/ x = u0 -> In x (Ul H) \/ x = u0)
          by (intros x Hx; apply Hx).
        simpl in Hu1, Hu2.
        assert (Hmem1 : In u1 (Ul H) \/ u1 = u0)
          by (destruct Hu1 as [-> | Hu1]; [now right | now left]).
        assert (Hmem2 : In u2 (Ul H) \/ u2 = u0)
          by (destruct Hu2 as [-> | Hu2]; [now right | now left]).
        clear Hu1 Hu2. rename Hmem1 into Hu1. rename Hmem2 into Hu2.
        assert (Hrow' : forall a b, In a (row_index (Ul H)) ->
                   In b (row_index (Ul H)) ->
                   row_eq member H.(V) a b -> row_eq H.(T) H.(V) a b). {
          intros a b Ha Hb Hab v Hv. unfold cell.
          rewrite (H.(tbl) a v Ha Hv), (H.(tbl) b v Hb Hv).
          specialize (Hab v Hv). unfold cell in Hab. apply Hab. }
        assert (Hup : forall x, In x (Ul H) -> In x (row_index (Ul H)))
          by (intros x Hx; unfold row_index; apply in_or_app; now left).
        destruct Hu1 as [Hu1U | Hu1e], Hu2 as [Hu2U | Hu2e].
        * apply (Hsp u1 u2 Hu1U Hu2U). apply Hrow'; auto.
        * (* u2 = u0 : impossible, no upper row has the row of u0 *)
          subst u2. exfalso.
          apply (Hu0new u1 Hu1U). apply Hrow'; auto.
        * (* u1 = u0 : symmetric *)
          subst u1. exfalso.
          apply (Hu0new u2 Hu2U). apply Hrow'; auto.
          apply (row_eq_sym member H.(V) u0 u2 Hrow).
        * subst u1 u2. reflexivity. }
      split; [apply HsepH' |].
      apply ce_measure_lt_up.
      + (* l_up H < l_up H' *)
        assert (Hnew : forall x, In x (Ul H) -> ~ row_eq member H.(V) u0 x). {
          intros x Hx Hrx. apply (Hu0new x Hx).
          apply (proj2 (row_eq_member H x u0 (in_Ul_row_index _ x Hx) Hu0idx)).
          apply (row_eq_sym member H.(V) u0 x Hrx). }
        unfold l_up. simpl.
        match goal with
        | |- context [if ?b then _ else _] => destruct b eqn:Eex
        end.
        * exfalso. apply existsb_exists in Eex. destruct Eex as (x & Hx & Hxe).
          simpl in Hxe.
          destruct (row_eq_dec member H.(V) u0 x H.(fin_V)) as [Heq |];
            [| discriminate].
          apply (Hnew x (dedup_rows_incl member H.(V) H.(fin_V) (Ul H) x Hx) Heq).
        * simpl. lia.
      + apply (l_up_le _).
      + apply (eqp_le _ HsepH').
      + apply (icov_le _ HsepH').
Qed.

Lemma filter_eq_nil : forall {X} (l : list X) f,
    filter f l = [] ->
    Forall (fun x => f x = false) l.
Proof.
    induction l; intros; simpl in *.
        constructor.
    destruct (f a) eqn:E.
        discriminate.
    constructor; auto.
Qed.

Lemma filter_eq_cons : forall {X} (l : list X) f h t,
    filter f l = h :: t ->
    f h = true.
Proof.
    induction l; intros; simpl in *.
        discriminate.
    destruct (f a) eqn:E.
        inversion H; now subst.
    eauto.
Qed.

Lemma resolve_consistency :
    forall (H : HypothesisRFSA),
      Hsep H ->
      Hclosed H ->
      ~ Hconsistent H ->
      { H' : HypothesisRFSA | Hsep H' /\ ce_measure H' < ce_measure H }.
Proof.
    intros H Hsp Hcl Hncon.
    destruct (rfsa_consistent_dec H.(T) H.(V) H.(fin_U) H.(fin_V))
      as [Hcon | (q & Hq)].
        exfalso. now apply Hncon.
    destruct q as ((u & u') & a). simpl in Hq.
    destruct Hq as (Hu & Hu' & Ha & Hviol).
    assert (Hcov : covered H.(T) H.(V) u u'). {
        destruct (covered_dec H.(T) H.(V) u u' H.(fin_V)) as [Hc | Hnc].
          apply Hc.
        exfalso. apply Hviol. intro Hc. contradiction. }
    assert (Hncov : ~ covered H.(T) H.(V) (u ++ [a]) (u' ++ [a]))
        by (intro Hc; apply Hviol; intros _; apply Hc).
    destruct (covered_fail_witness H.(T) H.(V) (u ++ [a]) (u' ++ [a]) H.(fin_V) Hncov)
      as (v & HvV & Huav & Hu'av).
    assert (Hidx : forall x, In x (Ul H) -> In (x ++ [a]) (row_index (Ul H))). {
        intros x Hx. unfold row_index. apply in_or_app. right.
        unfold USigma. apply in_flat_map. exists x. split; [apply Hx |].
        apply in_map_iff. exists a. split; [reflexivity | apply Ha]. }
    assert (Huidx : In u (row_index (Ul H))) by (apply in_Ul_row_index; apply Hu).
    assert (Hu'idx : In u' (row_index (Ul H))) by (apply in_Ul_row_index; apply Hu').
    set (c := [a] ++ v).
    assert (Hucm : cell member u c = true). {
        unfold c. change ([a] ++ v) with (a :: v). rewrite cell_app. unfold cell.
        rewrite <- (H.(tbl) (u ++ [a]) v (Hidx u Hu) HvV). apply Huav. }
    assert (Hu'cm : cell member u' c = false). {
        unfold c. change ([a] ++ v) with (a :: v). rewrite cell_app. unfold cell.
        rewrite <- (H.(tbl) (u' ++ [a]) v (Hidx u' Hu') HvV). apply Hu'av. }
      set (V' := fun x => (H.(V) x || (if str_eq x c then true else false))%bool).
      assert (finV' : finite V'). {
        destruct H.(fin_V) as (lv & NDv & Hlv).
        destruct (in_dec str_eq c lv) as [Hin | Hnin].
        - exists lv. split; [apply NDv |].
          intro x. unfold V'. rewrite Bool.orb_true_iff. split.
          + intros [Hx | Hx]. now apply Hlv.
            destruct (str_eq x c) as [-> |]; [apply Hin | discriminate].
          + intro Hx. left. now apply Hlv.
        - exists (c :: lv). split.
            constructor; [apply Hnin | apply NDv].
          intro x. unfold V'. rewrite Bool.orb_true_iff. simpl. split.
          + intros [Hx | Hx]. right. now apply Hlv.
            destruct (str_eq x c) as [-> |]; [now left | discriminate].
          + intros [-> | Hx].
              right. now destruct (str_eq x x); [reflexivity | contradiction].
            left. now apply Hlv. }
      assert (suffV' : forall w w', V' (w ++ w') = true -> V' w' = true). {
        intros w w' Hw. unfold V' in *. rewrite Bool.orb_true_iff in *.
        destruct Hw as [Hw | Hw].
        - left. apply (H.(suff) w w' Hw).
        - destruct (str_eq (w ++ w') c) as [Heq |]; [| discriminate].
          (* w ++ w' = c = [a] ++ v.  Case on w. *)
          destruct w as [| x w0].
          + (* w = [] : w' = c *)
            simpl in Heq. subst w'. right.
            now destruct str_eq.
          + (* w = x :: w0 : [a]++v = x :: (w0 ++ w'), so v = w0 ++ w' *)
            left. unfold c in Heq. simpl in Heq.
            injection Heq as Hax Hv.
            apply (H.(suff) w0 w'). rewrite Hv. apply HvV. }
      unshelve eexists (Build_HypothesisRFSA member H.(U) V' H.(fin_U) finV'
                          H.(pref) suffV' H.(eps_U) _ _).
      + (* eps_V for V' *) unfold V'. rewrite H.(eps_V). reflexivity.
      + (* tbl trivial : T := member *) intros uu vv _ _. reflexivity.
      + simpl.
        match goal with |- Hsep ?Hr /\ _ => assert (HsepH' : Hsep Hr) end.
        {
          intros u1 u2 Hu1 Hu2 Hrow.
          apply (Hsp u1 u2 Hu1 Hu2).
          intros vv Hvv.
          assert (Hu1i : In u1 (row_index (Ul H))) by (apply in_or_app; now left).
          assert (Hu2i : In u2 (row_index (Ul H))) by (apply in_or_app; now left).
          unfold cell. rewrite (H.(tbl) u1 vv Hu1i Hvv), (H.(tbl) u2 vv Hu2i Hvv).
          specialize (Hrow vv). unfold cell in Hrow.
          assert (HvvV' : V' vv = true) by (unfold V'; rewrite Hvv; reflexivity).
          specialize (Hrow HvvV'). apply Hrow.
        }
        split; [apply HsepH' |].
        assert (HcV' : V' c = true). {
            unfold V'. destruct (str_eq c c) as [_ | Hne].
              apply Bool.orb_true_r.
            now contradiction Hne. }
        apply (ce_measure_add_column H _ HsepH').
        * reflexivity.
        * intros x Hx. unfold V'. simpl. now rewrite Hx.
        * left. exists u, u'.
          split; [apply Huidx |]. split; [apply Hu'idx |]. split.
            apply (proj1 (covered_member H u u' Huidx Hu'idx) Hcov).
          intro Hc. simpl in Hc.
          specialize (Hc c HcV' Hucm). rewrite Hu'cm in Hc. discriminate.
Qed.

Lemma extend_ce_Ul : forall H w (Hce : N.accept_string (make_nfa H) w <> member w),
    Ul (extend_table_ce H w Hce) = Ul H.
Proof.
    intros H w Hce. unfold extend_table_ce, Ul. destruct H; simpl. reflexivity.
Qed.

Lemma extend_ce_T : forall H w (Hce : N.accept_string (make_nfa H) w <> member w),
    (extend_table_ce H w Hce).(T) = member.
Proof.
    intros H w Hce. unfold extend_table_ce. destruct H; simpl. reflexivity.
Qed.

Lemma extend_ce_V_incl : forall H w (Hce : N.accept_string (make_nfa H) w <> member w) v,
    H.(V) v = true -> (extend_table_ce H w Hce).(V) v = true.
Proof.
    intros H w Hce v Hv. unfold extend_table_ce. destruct H; simpl in *.
    destruct (find (fun s' => if str_eq v s' then true else false)
                   (filter (fun s => negb (V0 s)) (suffixes w))) eqn:E.
        reflexivity.
    apply Hv.
Qed.

Lemma extend_ce_sep :
    forall (H : HypothesisRFSA) w (Hce : N.accept_string (make_nfa H) w <> member w),
      Hsep H -> Hsep (extend_table_ce H w Hce).
Proof.
    intros H w Hce Hsp u1 u2 Hu1 Hu2 Hrow.
    rewrite extend_ce_Ul in Hu1, Hu2.
    (* transport row equality over V' back to H's table over V *)
    apply (Hsp u1 u2 Hu1 Hu2).
    intros v Hv.
    assert (Hu1i : In u1 (row_index (Ul H)))
        by (unfold row_index; apply in_or_app; now left).
    assert (Hu2i : In u2 (row_index (Ul H)))
        by (unfold row_index; apply in_or_app; now left).
    unfold cell.
    rewrite (H.(tbl) u1 v Hu1i Hv), (H.(tbl) u2 v Hu2i Hv).
    specialize (Hrow v (extend_ce_V_incl H w Hce v Hv)).
    unfold cell in Hrow. rewrite !(extend_ce_T H w Hce) in Hrow. apply Hrow.
Qed.

(* A counterexample is never already a column of the table. *)
Lemma ce_column_new : forall H (Hcl : Hclosed H) w,
    N.accept_string (make_nfa H) w <> member w ->
    H.(V) w = false.
Proof.
    intros H Hcl w Hce.
    destruct (H.(V) w) eqn:Hw; [| reflexivity].
    exfalso.
    assert (Heps : In ([] : str) (row_index (Ul H))). {
        unfold row_index. apply in_or_app. left.
        apply (proj1 (proj2 (proj2_sig H.(fin_U)) [])). apply H.(eps_U). }
    pose proof (eps_cell_L_aut H Hcl w Hw) as Hiff.
    unfold cell in Hiff. rewrite (H.(tbl) [] w Heps Hw) in Hiff. simpl in Hiff.
    apply Hce. apply Bool.eq_true_iff_eq. split; intro Hx.
    - now apply (proj2 Hiff).
    - now apply (proj1 Hiff).
Qed.

Lemma row_eq_covered : forall T V a b, row_eq T V a b -> covered T V a b.
Proof. intros T V a b Hr v Hv Hc. now rewrite <- (Hr v Hv). Qed.

Lemma covered_both_row_eq : forall T V a b,
    covered T V a b -> covered T V b a -> row_eq T V a b.
Proof.
    intros T V a b H1 H2 v Hv.
    destruct (cell T a v) eqn:Ea, (cell T b v) eqn:Eb; try reflexivity.
    - apply H1 in Ea. congruence. assumption.
    - apply H2 in Eb. congruence. assumption.
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

Lemma cell_member : forall H u v,
    In u (row_index (Ul H)) -> H.(V) v = true ->
    cell H.(T) u v = cell member u v.
Proof. intros H u v Hu Hv. unfold cell. apply (H.(tbl) u v Hu Hv). Qed.

(* Composedness, and hence primality, of a row of the table does not depend on
   whether the cells are read off [T] or off [member]. *)
Lemma composed_member : forall H u,
    In u (row_index (Ul H)) ->
    (composed H.(T) H.(V) (Ul H) u <-> composed member H.(V) (Ul H) u).
Proof.
    intros H u Hu.
    assert (Hsc : forall x, In x (row_index (Ul H)) ->
              (strictly_covered H.(T) H.(V) x u <-> strictly_covered member H.(V) x u)). {
        intros x Hx. unfold strictly_covered. split; intros (Hc & Hn); split.
        - now apply (covered_member H x u Hx Hu).
        - intro Hr. apply Hn. now apply (row_eq_member H x u Hx Hu).
        - now apply (proj2 (covered_member H x u Hx Hu)).
        - intro Hr. apply Hn. now apply (proj1 (row_eq_member H x u Hx Hu)). }
    unfold composed. split; intros Hc v Hv.
    - rewrite <- (cell_member H u v Hu Hv). split.
      + intro Hcell. destruct (proj1 (Hc v Hv) Hcell) as (x & Hx & Hxsc & Hxv).
        exists x. split; [apply Hx | split].
          now apply (Hsc x Hx).
        rewrite <- (cell_member H x v Hx Hv). apply Hxv.
      + intros (x & Hx & Hxsc & Hxv). apply (Hc v Hv). exists x.
        split; [apply Hx | split].
          now apply (proj2 (Hsc x Hx)).
        rewrite (cell_member H x v Hx Hv). apply Hxv.
    - rewrite (cell_member H u v Hu Hv). split.
      + intro Hcell. destruct (proj1 (Hc v Hv) Hcell) as (x & Hx & Hxsc & Hxv).
        exists x. split; [apply Hx | split].
          now apply (proj2 (Hsc x Hx)).
        rewrite (cell_member H x v Hx Hv). apply Hxv.
      + intros (x & Hx & Hxsc & Hxv). apply (Hc v Hv). exists x.
        split; [apply Hx | split].
          now apply (Hsc x Hx).
        rewrite <- (cell_member H x v Hx Hv). apply Hxv.
Qed.

Lemma prime_member : forall H u,
    In u (row_index (Ul H)) ->
    (prime H.(T) H.(V) (Ul H) u <-> prime member H.(V) (Ul H) u).
Proof.
    intros H u Hu. unfold prime. split; intros (Hi & Hn); split;
      try apply Hi; intro Hc; apply Hn.
    - now apply (proj2 (composed_member H u Hu)).
    - now apply (composed_member H u Hu).
Qed.

(* In an RFSA-closed table, every prime row is realised by a prime
   representative of the upper part.  If it were not, the closedness
   decomposition of that row would consist entirely of strictly covered rows,
   which is exactly what it means for the row to be composed. *)
Lemma closed_prime_upper : forall T V U (finU : finite U) (finV : finite V) p,
    closed T V finU ->
    In p (row_index (proj1_sig finU)) ->
    prime T V (proj1_sig finU) p ->
    exists q, In q (prime_reps T V (proj1_sig finU) finV) /\ row_eq T V q p.
Proof.
    intros T V U finU finV p Hcl Hpidx (_ & Hnc).
    destruct (no_upper_prime_dec T V (proj1_sig finU) finV p)
      as [Hno | (q & Hq & Hqe)].
    2: { exists q. split; [apply Hq | apply Hqe]. }
    exfalso. apply Hnc. intros v Hv. split.
    - intro Hcell.
      destruct (proj1 (Hcl p Hpidx v Hv) Hcell) as (q & HqU & Hqp & Hqcov & Hqv).
      assert (Hqpr : In q (prime_reps T V (proj1_sig finU) finV)). {
          unfold prime_reps. apply filter_In. split; [apply HqU |].
          now destruct (prime_dec T V (proj1_sig finU) q finV). }
      exists q. split.
        unfold row_index. apply in_or_app. now left.
      split; [| apply Hqv].
      split; [apply Hqcov |]. apply (Hno q Hqpr).
    - intros (u' & Hu' & (Hcov & _) & Hu'v). apply (Hcov v Hv Hu'v).
Qed.

(* Every suffix of the counterexample is a column of the extended table. *)
Lemma extend_ce_V_suffix : forall H w (Hce : N.accept_string (make_nfa H) w <> member w) t,
    In t (suffixes w) -> (extend_table_ce H w Hce).(V) t = true.
Proof.
    intros H w Hce t Ht.
    destruct (H.(V) t) eqn:Hv.
        now apply extend_ce_V_incl.
    unfold extend_table_ce. destruct H; simpl in *.
    destruct (find (fun s' => if str_eq t s' then true else false)
                   (filter (fun s => negb (V0 s)) (suffixes w))) eqn:E.
        reflexivity.
    exfalso.
    assert (Hin : In t (filter (fun s => negb (V0 s)) (suffixes w))).
        { apply filter_In. split; [apply Ht |]. now rewrite Hv. }
    pose proof (find_none _ _ E t Hin) as Hnone.
    simpl in Hnone. now destruct str_eq.
Qed.

Lemma ce_progress :
    forall (H : HypothesisRFSA),
      Hclosed H -> Hconsistent H -> Hsep H ->
      forall w (Hce : N.accept_string (make_nfa H) w <> member w),
      (exists u u', In u (row_index (Ul H)) /\ In u' (row_index (Ul H))
                    /\ covered member H.(V) u u'
                    /\ ~ covered member (extend_table_ce H w Hce).(V) u u')
      \/ (exists x, In x (row_index (Ul H))
                    /\ ~ prime member H.(V) (Ul H) x
                    /\ prime member (extend_table_ce H w Hce).(V) (Ul H) x).
Proof.
    intros H Hcl Hco Hsp w Hce.
    set (H' := extend_table_ce H w Hce).
    set (n := make_nfa H).
    (* Both progress conditions are decidable, so we may argue by contradiction. *)
    destruct (list_search
        (fun q => covered member H.(V) (fst q) (snd q)
                  /\ ~ covered member H'.(V) (fst q) (snd q))
        (list_prod (row_index (Ul H)) (row_index (Ul H)))
        (fun q =>
           match covered_dec member H.(V) (fst q) (snd q) H.(fin_V) with
           | left Hc =>
               match covered_dec member H'.(V) (fst q) (snd q) H'.(fin_V) with
               | left Hc' => right (fun HH => proj2 HH Hc')
               | right Hn' => left (conj Hc Hn')
               end
           | right Hn => right (fun HH => Hn (proj1 HH))
           end))
      as [(qq & Hqq & Hc1 & Hc2) | Hno1].
    { left. destruct qq. apply in_prod_iff in Hqq. destruct Hqq as (Hq1 & Hq2).
      exists s, s0. now repeat split. }
    destruct (list_search
        (fun x => ~ prime member H.(V) (Ul H) x /\ prime member H'.(V) (Ul H) x)
        (row_index (Ul H))
        (fun x =>
           match prime_dec member H.(V) (Ul H) x H.(fin_V) with
           | left Hp => right (fun HH => proj1 HH Hp)
           | right Hnp =>
               match prime_dec member H'.(V) (Ul H) x H'.(fin_V) with
               | left Hp' => left (conj Hnp Hp')
               | right Hnp' => right (fun HH => Hnp' (proj2 HH))
               end
           end))
      as [(x & Hx & Hp1 & Hp2) | Hno2].
    { right. exists x. apply (conj Hx (conj Hp1 Hp2)). }
    exfalso.
    (* Usable forms of the two negative results. *)
    assert (Hlift : forall a b, In a (row_index (Ul H)) -> In b (row_index (Ul H)) ->
              covered member H.(V) a b -> covered member H'.(V) a b). {
        intros a b Ha Hb Hc.
        destruct (covered_dec member H'.(V) a b H'.(fin_V)) as [Hc' | Hnc'].
          apply Hc'.
        exfalso. apply (Hno1 (a, b)).
          apply in_prod_iff. now split.
        simpl. now split. }
    assert (Hprimeback : forall z, In z (row_index (Ul H)) ->
              prime member H'.(V) (Ul H) z -> prime member H.(V) (Ul H) z). {
        intros z Hz Hp'.
        destruct (prime_dec member H.(V) (Ul H) z H.(fin_V)) as [Hp | Hnp].
          apply Hp.
        exfalso. apply (Hno2 z Hz). now split. }
    (* Going up: a covering that holds over V still holds over V'. *)
    assert (Hup : forall r u v, In r (row_index (Ul H)) -> In u (row_index (Ul H)) ->
              covered H.(T) H.(V) r u -> H'.(V) v = true ->
              cell member r v = true -> cell member u v = true). {
        intros r u v Hr Hu Hc Hv Hcell.
        apply (Hlift r u Hr Hu (proj1 (covered_member H r u Hr Hu) Hc) v Hv Hcell). }
    (* Going down: a true cell at a new column is still witnessed by an upper
       prime row below it. *)
    assert (Hdescend : forall u v, In u (row_index (Ul H)) -> H'.(V) v = true ->
              cell member u v = true ->
              exists r, In r (cover_set H.(T) H.(V) (Ul H) H.(fin_V) u)
                        /\ cell member r v = true). {
        intros u v Hu Hv Hcell.
        destruct (row_prime_witness member H'.(V) (Ul H) H'.(fin_V)
                    (row_weight member (proj1_sig H'.(fin_V)) u) u v
                    (le_n _) Hu Hv Hcell)
          as (p & Hp & Hpp & Hpcov & Hpv).
        assert (HpV : prime member H.(V) (Ul H) p) by (now apply Hprimeback).
        assert (HpcovV : covered member H.(V) p u)
            by (intros z Hz; apply Hpcov; now apply extend_ce_V_incl).
        assert (HpT : prime H.(T) H.(V) (Ul H) p)
            by (now apply (proj2 (prime_member H p Hp))).
        destruct (closed_prime_upper H.(T) H.(V) H.(U) H.(fin_U) H.(fin_V) p
                    Hcl Hp HpT) as (r & Hr & Hre).
        assert (HrIdx : In r (row_index (Ul H))). {
            unfold row_index. apply in_or_app. left.
            now apply (prime_reps_upper H.(T) H.(V) (Ul H) H.(fin_V)). }
        assert (HreM : row_eq member H.(V) r p)
            by (now apply (row_eq_member H r p HrIdx Hp)).
        assert (HrcovT : covered H.(T) H.(V) r u). {
            apply (proj2 (covered_member H r u HrIdx Hu)).
            apply (covered_trans member H.(V) r p u);
              [now apply row_eq_covered | apply HpcovV]. }
        exists r. split.
        - unfold cover_set. apply filter_In. split; [apply Hr |].
          now destruct (covered_dec H.(T) H.(V) r u H.(fin_V)).
        - (* the row equality survives the new columns *)
          assert (Hre' : row_eq member H'.(V) r p). {
              apply covered_both_row_eq.
              - apply Hlift; [apply HrIdx | apply Hp | now apply row_eq_covered].
              - apply Hlift; [apply Hp | apply HrIdx |].
                apply row_eq_covered. now apply row_eq_sym. }
          rewrite (Hre' v Hv). apply Hpv. }
    (* The automaton agrees with the table on every suffix of [w]. *)
    assert (Hmain : forall y, (forall t, In t (suffixes y) -> H'.(V) t = true) ->
              forall S : list { q | memr H q = true },
              existsb (fun q => cell member (proj1_sig q) y) S
              = existsb (N.accept _ n) (N.run_from n S y)). {
        induction y as [| a y IH]; intros Hsuf.
        - intro S. unfold N.run_from. simpl.
          induction S as [| q S IHS]; simpl; [reflexivity |].
          rewrite IHS. f_equal.
          unfold cell. rewrite app_nil_r. symmetry.
          pose proof (H.(tbl) (proj1_sig q) [] (state_row_index H q) H.(eps_V)) as Ht.
          rewrite app_nil_r in Ht. apply Ht.
        - intro S.
          assert (Hsufy : forall t, In t (suffixes y) -> H'.(V) t = true)
              by (intros t Ht; apply Hsuf; simpl; now right).
          assert (HyV : H'.(V) y = true) by (apply Hsufy, suffixes_refl).
          change (N.run_from n S (a :: y))
            with (N.run_from n (N.step (N.transition _ n) S a) y).
          rewrite <- (IH Hsufy (N.step (N.transition _ n) S a)).
          apply Bool.eq_true_iff_eq. split; intro Hex.
          + (* down: some state of S is true at [a :: y] *)
            apply existsb_exists in Hex. destruct Hex as (q & HqS & Hq).
            rewrite cell_app in Hq.
            assert (Hqa : In (proj1_sig q ++ [a]) (row_index (Ul H))). {
                unfold row_index. apply in_or_app. right. unfold USigma.
                apply in_flat_map. exists (proj1_sig q). split.
                  apply state_upper.
                apply in_map_iff. exists a. split; [reflexivity | apply t_enumerable]. }
            destruct (Hdescend (proj1_sig q ++ [a]) y Hqa HyV Hq)
              as (r & Hrcs & Hrv).
            apply existsb_exists.
            exists (exist (fun z => memr H z = true) r
                      (cover_set_memr H (proj1_sig q ++ [a]) r Hrcs)).
            split; [| apply Hrv].
            unfold N.step. apply in_flat_map. exists q. split; [apply HqS |].
            unfold n, make_nfa. simpl.
            apply (list_with_proof_complete _ _ (bool_eq_proof_irrel H)).
          + (* up: some successor state is true at [y] *)
            apply existsb_exists in Hex. destruct Hex as (r & HrS & Hr).
            unfold N.step in HrS. apply in_flat_map in HrS.
            destruct HrS as (q & HqS & Hrq).
            unfold n, make_nfa in Hrq. simpl in Hrq.
            apply in_list_with_proof in Hrq.
            apply filter_In in Hrq. destruct Hrq as (Hrpr & Hrcov).
            destruct (covered_dec H.(T) H.(V) (proj1_sig r) (proj1_sig q ++ [a])
                        H.(fin_V)) as [Hc |]; [| discriminate].
            assert (Hqa : In (proj1_sig q ++ [a]) (row_index (Ul H))). {
                unfold row_index. apply in_or_app. right. unfold USigma.
                apply in_flat_map. exists (proj1_sig q). split.
                  apply state_upper.
                apply in_map_iff. exists a. split; [reflexivity | apply t_enumerable]. }
            apply existsb_exists. exists q. split; [apply HqS |].
            rewrite cell_app.
            apply (Hup (proj1_sig r) (proj1_sig q ++ [a]) y
                     (state_row_index H r) Hqa Hc HyV Hr). }
    (* The table side, at the initial states, is [member w]. *)
    assert (Hsufw : forall t, In t (suffixes w) -> H'.(V) t = true)
        by (intros t Ht; now apply extend_ce_V_suffix).
    assert (HwV : H'.(V) w = true) by (apply Hsufw, suffixes_refl).
    assert (Hepsidx : In ([] : str) (row_index (Ul H))). {
        unfold row_index. apply in_or_app. left.
        apply (proj1 (proj2 (proj2_sig H.(fin_U)) [])). apply H.(eps_U). }
    assert (Hleft : existsb (fun q => cell member (proj1_sig q) w)
                            (N.initial _ n) = member w). {
        apply Bool.eq_true_iff_eq. split; intro Hx.
        - apply existsb_exists in Hx. destruct Hx as (q & Hq & Hqw).
          unfold n, make_nfa in Hq. simpl in Hq.
          apply in_list_with_proof in Hq.
          apply filter_In in Hq. destruct Hq as (Hqpr & Hqcov).
          destruct (covered_dec H.(T) H.(V) (proj1_sig q) [] H.(fin_V))
            as [Hc |]; [| discriminate].
          apply (Hup (proj1_sig q) [] w (state_row_index H q) Hepsidx Hc HwV Hqw).
        - destruct (Hdescend [] w Hepsidx HwV Hx) as (r & Hrcs & Hrw).
          apply existsb_exists.
          exists (exist (fun z => memr H z = true) r (cover_set_memr H [] r Hrcs)).
          split; [| apply Hrw].
          unfold n, make_nfa. simpl.
          apply (list_with_proof_complete _ _ (bool_eq_proof_irrel H)). }
    apply Hce. unfold N.accept_string, N.run.
    now rewrite <- Hmain.
Qed.

(* The counterexample step strictly decreases the measure. *)
Lemma ce_measure_extend_lt :
    forall (H : HypothesisRFSA),
      Hclosed H -> Hconsistent H -> Hsep H ->
      forall w (Hce : N.accept_string (make_nfa H) w <> member w),
      ce_measure (extend_table_ce H w Hce) < ce_measure H.
Proof.
    intros H Hcl Hco Hsp w Hce.
    apply (ce_measure_add_column H (extend_table_ce H w Hce)
             (extend_ce_sep H w Hce Hsp)).
    - apply extend_ce_Ul.
    - apply extend_ce_V_incl.
    - apply (ce_progress H Hcl Hco Hsp w Hce).
Qed.

Definition complete :
    forall (H : HypothesisRFSA), Hsep H ->
      { H' : HypothesisRFSA
        | Hclosed H' /\ Hconsistent H' /\ Hsep H'
          /\ num_states H' <= L.num_residuals
          /\ ce_measure H' <= ce_measure H }.
Proof.
    intros H0 Hsep0.
    remember (S (ce_measure H0)) as fuel eqn:Hfuel.
    assert (Hlt : ce_measure H0 < fuel) by lia.
    clear Hfuel. revert H0 Hsep0 Hlt.
    induction fuel as [| fuel IH]; intros H Hsp Hlt; [lia |].
    destruct (closed_dec H.(T) H.(V) H.(U) H.(fin_U) H.(fin_V)) as [Hcl | Hncl].
    - destruct (rfsa_consistent_dec H.(T) H.(V) H.(fin_U) H.(fin_V)) as [Hco | Hnco].
      + exists H. repeat (split; [assumption|]). split.
            apply (num_states_le_num_residuals H Hsp).
        reflexivity.
      + pose proof (resolve_consistency H Hsp Hcl).
        destruct X as (H' & H'sep & Measure).
            intro Contra. unfold Hconsistent, rfsa_consistent in Contra.
            destruct Hnco as (((u & u') & a) & In1 & In2 & In3 & ?).
            now specialize (Contra _ _ _ In1 In2 In3).
        destruct (IH H' H'sep ltac:(lia))
          as (H'' & ? & ? & ? & ? & Hmono').
        exists H''. repeat (split; [assumption|]). lia.
    - pose proof (resolve_closedness H Hsp).
      destruct X as (H' & Hsp' & Hdec).
        intro Contra. unfold Hclosed, closed in Contra.
        destruct Hncl as (u & Inu & Ncl).
        now specialize (Contra _ Inu).
      destruct (IH H' Hsp' ltac:(lia))
        as (H'' & ? & ? & ? & ? & Hmono').
      exists H''. repeat (split; [assumption|]). lia.
Defined.

Definition saturate :
    forall (H : HypothesisRFSA),
      Hclosed H -> Hconsistent H -> Hsep H ->
      forall w, N.accept_string (make_nfa H) w <> member w ->
      { H' : HypothesisRFSA
        | Hclosed H' /\ Hconsistent H' /\ Hsep H'
          /\ num_states H' <= L.num_residuals }.
Proof.
    intros H Hcl Hco Hsp w Hwce.
    destruct (complete (extend_table_ce H w Hwce) (extend_ce_sep H w Hwce Hsp))
      as (H' & Hcl' & Hco' & Hsp' & Hbnd' & _).
    now exists H'.
Defined.

Definition step :
    forall (H : HypothesisRFSA),
      Hclosed H -> Hconsistent H -> Hsep H ->
      forall w, N.accept_string (make_nfa H) w <> member w ->
      { H' : HypothesisRFSA
        | Hclosed H' /\ Hconsistent H' /\ Hsep H'
          /\ ce_measure H' < ce_measure H
          /\ num_states H' <= L.num_residuals }.
Proof.
    intros H Hcl Hco Hsp w Hwce.
    destruct (complete (extend_table_ce H w Hwce) (extend_ce_sep H w Hwce Hsp))
      as (H' & Hcl' & Hco' & Hsp' & Hbnd' & Hmono).
    exists H'. repeat (split; [assumption|]). split; [| assumption].
    (* completion does not increase the measure, and the counterexample
       extension strictly decreases it *)
    pose proof (ce_measure_extend_lt H Hcl Hco Hsp w Hwce). lia.
Defined.

(** The main NL* implementation *)
Fixpoint nlstar_fuel (H : HypothesisRFSA)
    (Hcl : Hclosed H) (Hco : Hconsistent H) (Hsp : Hsep H) (fuel : nat)
    (LE : ce_measure H <= fuel)
    {struct fuel}
    : { T : Type & {r : R.t T | canonical r} }.
Proof.
    destruct (equiv_query (make_nfa H)) eqn:E.
    - pose proof (equiv_query_ce (make_nfa H) s E) as Hce.
      destruct (step H Hcl Hco Hsp s Hce)
        as (H' & Hcl' & Hco' & Hsp' & Hlt & Hbnd).
      destruct fuel as [| fuel']. lia.
      apply (nlstar_fuel H' Hcl' Hco' Hsp' fuel' ltac:(lia)).
    - pose proof (proj1 (equiv_query_correct (make_nfa H)) E) as Henc.
      pose proof (make_nfa_canonical_of_encodes H Hcl Hco Henc) as X.
      destruct X as (RFSA & Eq & Canonical).
      now exists _, RFSA.
Defined.

Definition init_T : str -> bool :=
    fun x => if in_dec str_eq x ([] :: map (fun a => [a]) enum)
             then member x else false.

Definition init_U : str -> bool :=
    fun x => if str_eq x [] then true else false.

Lemma init_finite_eps : finite init_U.
Proof.
    exists [[]]. split.
        constructor; [now intro | constructor].
    intros z. unfold init_U. split; intro Hz.
        destruct (str_eq z []) as [-> |]; [now left | discriminate].
    destruct Hz as [<- | []]. now destruct (str_eq (@nil s.t) []).
Qed.

Definition init_hyp : HypothesisRFSA.
Proof.
    eapply Build_HypothesisRFSA
      with (T := init_T) (U := init_U) (V := init_U)
           (fin_U := init_finite_eps).
    - apply init_finite_eps.
    - (* pref *)
      intros w w' Hw. unfold init_U in *.
      destruct (str_eq (w ++ w') []) as [Heq |]; [| discriminate].
      apply app_eq_nil in Heq. destruct Heq as (-> & _).
      now destruct (str_eq (@nil s.t) []).
    - (* suff *)
      intros w w' Hw. unfold init_U in *.
      destruct (str_eq (w ++ w') []) as [Heq |]; [| discriminate].
      apply app_eq_nil in Heq. destruct Heq as (_ & ->).
      now destruct (str_eq (@nil s.t) []).
    - (* eps_U *) unfold init_U. now destruct (str_eq (@nil s.t) []).
    - (* eps_V *) unfold init_U. now destruct (str_eq (@nil s.t) []).
    - (* tbl : on in-scope cells, init_T agrees with member *)
      intros u v Hu Hv. unfold init_U in Hv.
      destruct (str_eq v []) as [-> |]; [| discriminate].
      rewrite app_nil_r. unfold init_T.
      destruct (in_dec str_eq u ([] :: map (fun a => [a]) enum)) as [Hin | Hnin].
        reflexivity.
      exfalso. apply Hnin.
      unfold row_index, USigma in Hu. simpl in Hu.
      apply in_app_or in Hu. destruct Hu as [Hu | Hu].
      + destruct init_finite_eps, a. simpl in *.
        destruct (str_eq u []). now left. right.
        apply i in Hu. unfold init_U in Hu.
        now destruct str_eq.
      + right. apply in_flat_map in Hu. destruct Hu as (a & Heq & Ha).
        apply in_map_iff. destruct u. simpl in Hnin.
            destruct (Hnin (or_introl eq_refl)).
        destruct init_finite_eps, a0. simpl in *.
        apply in_map_iff in Ha. destruct Ha, H.
        destruct a.
            simpl in H. exists x0. now split.
        apply i in Heq. unfold init_U in Heq.
        now destruct str_eq in Heq.
Defined.

Lemma init_sep : Hsep init_hyp.
Proof.
    intros u1 u2 H1 H2 _.
    unfold init_hyp, Ul in H1, H2. simpl in H1, H2.
    destruct init_finite_eps as (l & ND & Hl). simpl in H1, H2.
    apply Hl in H1, H2. unfold init_U in H1, H2.
    destruct (str_eq u1 []) as [-> |]; [| discriminate].
    destruct (str_eq u2 []) as [-> |]; [| discriminate].
    reflexivity.
Qed.

(** The total NL* implementation. *)
Definition nlstar (_ : unit) : { T : Type & {r : R.t T | canonical r} }.
Proof.
    destruct (complete init_hyp init_sep)
      as (H0 & Hcl & Hco & Hsp & Hbnd & _).
    apply (nlstar_fuel H0 Hcl Hco Hsp (ce_measure H0) (le_n _)).
Defined.

End NLstar.
