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

(** The value of the row of u at column v *)
Definition cell (T : str -> bool) (u v : str) : bool := T (u ++ v).

(** The strings indexing rows: U together with its one-letter extensions *)
Definition USigma (Ul : list str) : list str :=
    flat_map (fun u => map (fun a => u ++ [a]) enum) Ul.

Definition row_index (Ul : list str) : list str :=
    Ul ++ USigma Ul.

(** Two rows are equal when they agree on every column of V *)
Definition row_eq (T V : str -> bool) (u1 u2 : str) : Prop :=
    forall v, V v = true -> cell T u1 v = cell T u2 v.

(* Definition 5 *)
(** The join of rows u1 u2 at column v *)
Definition join (T : str -> bool) (u1 u2 v : str) : bool :=
    cell T u1 v || cell T u2 v.

(* Definition 7 *)
(** Row u1 is covered by row u2 when, on every column, a + in u1 forces a + in u2 *)
Definition covered (T V : str -> bool) (u1 u2 : str) : Prop :=
    forall v, V v = true -> cell T u1 v = true -> cell T u2 v = true.

(** Row u1 is strictly covered by row u2 when it is covered and they differ *)
Definition strictly_covered (T V : str -> bool) (u1 u2 : str) : Prop :=
    covered T V u1 u2 /\ ~ row_eq T V u1 u2.

Lemma strict_impl_covered : forall T V u1 u2,
    strictly_covered T V u1 u2 -> covered T V u1 u2.
Proof. intros. now destruct H. Qed.

(* Definition 6 *)
(** A row r is composed when on every column its value is the join of rows
    distinct from r among the row indices *)
Definition composed (T V : str -> bool) (Ul : list str) (u : str) : Prop :=
    forall v, V v = true ->
        cell T u v = true <->
        exists u', In u' (row_index Ul) /\ ~ row_eq T V u' u /\ cell T u' v = true.

Definition prime (T V : str -> bool) (Ul : list str) (u : str) : Prop :=
    In u (row_index Ul) /\ ~ composed T V Ul u.

(** Covering decided relative to an arbitrary column list *)
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

Lemma covered_dec : forall T V u1 u2,
    finite V -> {covered T V u1 u2} + {~ covered T V u1 u2}.
Proof.
    intros T V u1 u2 finV. unfold covered.
    destruct finV as (vl & _ & Hv).
    destruct (covered_on_dec T u1 u2 vl).
    - left. intros. apply e; auto. now apply Hv.
    - right. intro. apply n. intros. apply H; auto. now apply Hv.
Defined.

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

Lemma row_eq_dec : forall T V u1 u2,
    finite V -> {row_eq T V u1 u2} + {~ row_eq T V u1 u2}.
Proof.
    intros T V u1 u2 finV. unfold row_eq.
    destruct finV as (vl & _ & Hv).
    destruct (row_eq_on_dec T u1 u2 vl).
    - left. intros. apply e. now apply Hv.
    - right. intro. apply n. intros. apply H. now apply Hv.
Defined.

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

Lemma composed_witness_dec : forall T V u v (rl : list str),
    finite V ->
    {exists u', In u' rl /\ ~ row_eq T V u' u /\ cell T u' v = true}
  + {~ exists u', In u' rl /\ ~ row_eq T V u' u /\ cell T u' v = true}.
Proof.
    intros T V u v rl finV. induction rl.
        right. intro Contra. destruct Contra, H. inversion H.
    destruct (row_eq_dec T V a u finV).
    - destruct IHrl.
        left. destruct e. exists x. intuition.
      right. intro Contra. destruct Contra, H, H0. destruct H.
        now subst.
      apply n. exists x. auto.
    - destruct (Bool.bool_dec (cell T a v) true).
        left. exists a. split; [now left | now split].
      destruct IHrl.
        left. destruct e. exists x. split; [now right | intuition].
      right. intro Contra. destruct Contra, H, H0. destruct H.
        now subst.
      apply n1. exists x. auto.
Defined.

Lemma composed_on_dec : forall T V Ul u (vl : list str),
    finite V ->
    {forall v, In v vl ->
        cell T u v = true <->
        exists u', In u' (row_index Ul) /\ ~ row_eq T V u' u /\ cell T u' v = true}
  + {~ forall v, In v vl ->
        cell T u v = true <->
        exists u', In u' (row_index Ul) /\ ~ row_eq T V u' u /\ cell T u' v = true}.
Proof.
    intros T V Ul u vl finV. induction vl.
        left. intros. destruct H.
    destruct (composed_witness_dec T V u a (row_index Ul) finV).
    - destruct (Bool.bool_dec (cell T u a) true).
      + destruct IHvl.
            left. intros. destruct H; [subst; now split | auto].
        right. intro. apply n. intros. apply H. now right.
      + right. intro. apply n. exfalso. specialize (H a (or_introl eq_refl)). intuition.
    - destruct (Bool.bool_dec (cell T u a) true).
        right. intro. apply n. exfalso. specialize (H a (or_introl eq_refl)). intuition.
      destruct IHvl.
        left. intros. destruct H.
            subst. intuition.
        now apply i.
      right. intro. apply n1. intros. apply H. now right.
Defined.

Lemma composed_dec : forall T V Ul u,
    finite V -> {composed T V Ul u} + {~ composed T V Ul u}.
Proof.
    intros T V Ul u finV. unfold composed.
    destruct finV as (vl & ND & Hv).
    destruct (composed_on_dec T V Ul u vl (exist _ vl (conj ND Hv))).
    - left. intros. apply i. now apply Hv.
    - right. intro. apply n. intros. apply H. now apply Hv.
Defined.

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

Definition prime_reps (T V : str -> bool) (Ul : list str) (finV : finite V) : list str :=
    filter (fun u => if prime_dec T V Ul u finV then true else false) (row_index Ul).

Lemma prime_reps_prime : forall T V Ul finV u,
    In u (prime_reps T V Ul finV) -> prime T V Ul u.
Proof.
    intros. apply filter_In in H. destruct H. now destruct (prime_dec T V Ul u finV).
Qed.

Lemma prime_reps_index : forall T V Ul finV u,
    In u (prime_reps T V Ul finV) -> In u (row_index Ul).
Proof.
    intros. apply filter_In in H. now destruct H.
Qed.

Definition cover_set (T V : str -> bool) (Ul : list str) (finV : finite V) (u : str)
    : list str :=
    filter (fun p => if covered_dec T V p u finV then true else false)
           (prime_reps T V Ul finV).

Lemma cover_set_prime_reps : forall T V Ul finV u p,
    In p (cover_set T V Ul finV u) -> In p (prime_reps T V Ul finV).
Proof.
    intros. apply filter_In in H. now destruct H.
Qed.

(* Definition 8 *)
(** The closedness condition for a single lower row u: on every column, u's
    value is the join of the prime upper rows covered by it *)
Definition closed_row (T V : str -> bool) (Ul : list str) (u : str) : Prop :=
    forall v, V v = true ->
        cell T u v = true <->
        exists u', In u' Ul /\ prime T V Ul u' /\ covered T V u' u /\ cell T u' v = true.

Lemma closed_witness_dec : forall T V Ul u v (ul : list str),
    finite V ->
    {exists u', In u' ul /\ prime T V Ul u' /\ covered T V u' u /\ cell T u' v = true}
  + {~ exists u', In u' ul /\ prime T V Ul u' /\ covered T V u' u /\ cell T u' v = true}.
Proof.
    intros T V Ul u v ul finV. induction ul.
        right. intro Contra. destruct Contra, H. inversion H.
    destruct (prime_dec T V Ul a finV).
    - destruct (covered_dec T V a u finV).
      + destruct (Bool.bool_dec (cell T a v) true).
          left. exists a. intuition.
        destruct IHul.
          left. destruct e. exists x. split; [now right | intuition].
        right. intro Contra. destruct Contra, H, H0, H1, H.
          now subst.
        apply n0. eauto.
      + destruct IHul.
          left. destruct e. exists x. split; [now right | intuition].
        right. intro Contra. destruct Contra, H, H0, H1, H.
          now subst.
        apply n0. eauto.
    - destruct IHul.
        left. destruct e. exists x. split; [now right | intuition].
      right. intro Contra. destruct Contra, H, H0, H.
        now subst.
      apply n0. eauto.
Defined.

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
            left. intros. destruct H; [subst; now split | auto].
        right. intro. apply n. intros. apply H. now right.
      + right. intro. apply n. exfalso. specialize (H a (or_introl eq_refl)). intuition.
    - destruct (Bool.bool_dec (cell T u a) true).
        right. intro. apply n. exfalso. specialize (H a (or_introl eq_refl)). intuition.
      destruct IHvl.
        left. intros. destruct H.
            subst. intuition.
        now apply i.
      right. intro. apply n1. intros. apply H. now right.
Defined.

Lemma closed_row_dec : forall T V Ul u,
    finite V -> {closed_row T V Ul u} + {~ closed_row T V Ul u}.
Proof.
    intros T V Ul u finV. unfold closed_row.
    destruct finV as (vl & ND & Hv).
    destruct (closed_row_on_dec T V Ul u vl (exist _ vl (conj ND Hv))).
    - left. intros. apply i. now apply Hv.
    - right. intro. apply n. intros. apply H. now apply Hv.
Defined.

Definition closed (T V : str -> bool) (Ul : list str) : Prop :=
    forall u, In u (USigma Ul) -> closed_row T V Ul u.

Lemma closed_dec : forall T V Ul,
    finite V ->
    closed T V Ul + {u : str | In u (USigma Ul) /\ ~ closed_row T V Ul u}.
Proof.
    intros T V Ul finV. unfold closed.
    induction (USigma Ul).
        left. intros. destruct H.
    destruct (closed_row_dec T V Ul a finV).
    - destruct IHl.
        left. intros. destruct H; auto; now subst.
      right. destruct s. exists x. split; [now right | intuition].
    - right. exists a. split; [now left | assumption].
Defined.

(* Definition 9 *)
(** A table is RFSA-consistent if covering is preserved by one-letter extension *)
Definition rfsa_consistent (T V : str -> bool) (Ul : list str) : Prop :=
    forall u u' a,
        In u Ul -> In u' Ul -> In a enum ->
        covered T V u u' -> covered T V (u ++ [a]) (u' ++ [a]).

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

Lemma rfsa_consistent_dec : forall T V Ul,
    finite V ->
    rfsa_consistent T V Ul
    + {p : str * str * s.t | let '(u, u', a) := p in
        In u Ul /\ In u' Ul /\ In a enum /\ ~ (covered T V u u' -> covered T V (u ++ [a]) (u' ++ [a]))}.
Proof.
    intros T V Ul finV. unfold rfsa_consistent.
    destruct (consistent_outer_dec T V Ul Ul finV); auto.
Defined.

(* Definition 10 *)
(** A hypothesis RFSA bundles the table with its finiteness, closedness, and
    consistency invariants, after Lstar's HypothesisDFA *)
Record HypothesisRFSA : Type := {
  T    : str -> bool;
  U    : str -> bool;
  V    : str -> bool;
  fin_U : finite U;
  fin_V : finite V;
  clos : closed T V (proj1_sig fin_U);
  cons : rfsa_consistent T V (proj1_sig fin_U)
}.

Definition Ul (H : HypothesisRFSA) : list str := proj1_sig H.(fin_U).

Definition memr (H : HypothesisRFSA) (q : str) : bool :=
    mem q (prime_reps H.(T) H.(V) (Ul H) H.(fin_V)).

Lemma cover_set_memr : forall H u p,
    In p (cover_set H.(T) H.(V) (Ul H) H.(fin_V) u) -> memr H p = true.
Proof.
    intros. apply mem_In. now apply (cover_set_prime_reps _ _ _ _ u).
Qed.

Definition make_rfsa (H : HypothesisRFSA) : N.t { q | memr H q = true }.
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
        f_equal. apply UIP_dec, Bool.bool_dec. }
    rewrite Heq.
    apply (list_with_proof_complete Pr (fun q => memr H q = true)).
    intros. apply UIP_dec, Bool.bool_dec.
Defined.

End NLstar.
