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

Record hypothesis : Type := {
  T  : str -> bool;
  U  : list str;
  V  : list str
}.

(** One-letter extensions of the access strings *)
Definition USigma (o : hypothesis) : list str :=
    flat_map (fun u => map (fun a => u ++ [a]) enum) o.(U).

(** The strings indexing rows of the hypothesis: U together with U.Sigma *)
Definition row_index (o : hypothesis) : list str :=
    o.(U) ++ USigma o.

(** The value of the row of u at column v *)
Definition cell (o : hypothesis) (u v : str) : bool := o.(T) (u ++ v).

(** Two rows are equal when they agree on every column *)
Definition row_eq (o : hypothesis) (u1 u2 : str) : Prop :=
    forall v, In v o.(V) -> cell o u1 v = cell o u2 v.

(* Definition 5 *)
(** The join of rows u1 u2 at column v *)
Definition join (o : hypothesis) (u1 u2 v : str) : bool :=
    cell o u1 v || cell o u2 v.

(* Definition 6 *)
(** A row r is composed when on every column its value is the join of rows
    distinct from r among the row indices *)
Definition composed (o : hypothesis) (u : str) : Prop :=
    forall v, In v o.(V) ->
        cell o u v = true <->
        exists u', In u' (row_index o) /\ ~ row_eq o u' u /\ cell o u' v = true.

(** If a row is not composed, it is prime *)
Definition prime (o : hypothesis) (u : str) : Prop :=
    In u (row_index o) /\ ~ composed o u.

(* Definition 7 *)
(** Row u1 is covered by row u2 when, on every column, a + in u1 forces a + in u2 *)
Definition covered (o : hypothesis) (u1 u2 : str) : Prop :=
    forall v, In v o.(V) -> cell o u1 v = true -> cell o u2 v = true.

(** Row u1 is strictly covered by row u2 when it is covered and they differ
    on some column *)
Definition strictly_covered (o : hypothesis) (u1 u2 : str) : Prop :=
    covered o u1 u2 /\ ~ row_eq o u1 u2.

Lemma strict_impl_covered : forall o u1 u2,
    strictly_covered o u1 u2 -> covered o u1 u2.
Proof. intros. now destruct H. Qed.

Lemma covered_dec : forall o u1 u2, {covered o u1 u2} + {~ covered o u1 u2}.
Proof.
    intros. unfold covered.
    induction (V o).
        left. intros. destruct H.
    destruct (Bool.bool_dec (cell o u1 a) true).
    - destruct (Bool.bool_dec (cell o u2 a) true).
      + destruct IHl.
            left. intros. destruct H; subst; auto.
        right. intro. apply n. intros. apply H; auto. now right.
      + right. intro. apply n. apply H; [now left | assumption].
    - destruct IHl.
        left. intros. destruct H; subst; [congruence | auto].
      right. intro. apply n0. intros. apply H; auto. now right.
Defined.

Lemma row_eq_dec : forall o u1 u2, {row_eq o u1 u2} + {~ row_eq o u1 u2}.
Proof.
    intros. unfold row_eq.
    induction (V o).
        left. intros. destruct H.
    destruct (Bool.bool_dec (cell o u1 a) (cell o u2 a)).
    - destruct IHl.
        left. intros. destruct H; subst; auto.
      right. intro. apply n. intros. apply H. now right.
    - right. intro. apply n, H. now left.
Defined.

Lemma strictly_covered_dec : forall o u1 u2,
    {strictly_covered o u1 u2} + {~ strictly_covered o u1 u2}.
Proof.
    intros. unfold strictly_covered.
    destruct (covered_dec o u1 u2).
    - destruct (row_eq_dec o u1 u2).
        right. now intros.
      now left.
    - right. now intros.
Defined.

Lemma composed_dec : forall o u, {composed o u} + {~ composed o u}.
Proof.
    intros. unfold composed.
    induction (V o).
        left. intros. destruct H.
    assert (Pdec : {exists u', In u' (row_index o) /\ ~ row_eq o u' u /\ cell o u' a = true}
                 + {~ exists u', In u' (row_index o) /\ ~ row_eq o u' u /\ cell o u' a = true}).
    { clear IHl.
        induction (row_index o).
            right. intro Contra. destruct Contra, H. inversion H.
        destruct (row_eq_dec o a0 u).
        - destruct IHl0.
            left. destruct e. exists x. intuition.
          right. intro Contra. destruct Contra, H, H0. destruct H.
            now subst.
          apply n. exists x. auto.
        - destruct (Bool.bool_dec (cell o a0 a) true).
            left. exists a0. split; [now left | now split].
          destruct IHl0.
            left. destruct e. exists x. split; [now right | intuition].
          right. intro Contra. destruct Contra, H, H0. destruct H.
            now subst.
          apply n1. exists x. auto.
    }
    destruct (Bool.bool_dec (cell o u a) true).
    - destruct Pdec.
      + destruct IHl.
            left. intros. destruct H; [subst; now split | auto].
        right. intro. apply n. intros. apply H. now right.
      + right. intro. apply n. now apply (proj1 (H a (or_introl eq_refl))).
    - destruct Pdec.
        right. intro. apply n. now apply (proj2 (H a (or_introl eq_refl))).
      destruct IHl.
        left. intros. destruct H.
            subst. intuition.
        now apply i.
      right. intro. apply n1. intros. apply H. now right.
Defined.

Lemma prime_dec : forall o u, {prime o u} + {~ prime o u}.
Proof.
    intros. unfold prime.
    destruct (in_dec str_eq u (row_index o)).
    - destruct (composed_dec o u).
        right. now intros (_ & ?).
      left. now split.
    - right. now intros (? & _).
Defined.

Lemma composed_prime_dec : forall o u,
    In u (row_index o) -> {composed o u} + {prime o u}.
Proof.
    intros. destruct (composed_dec o u).
        now left.
    right. now split.
Defined.

Definition prime_reps (o : hypothesis) : list str :=
    filter (fun u => if prime_dec o u then true else false) (row_index o).

Lemma prime_reps_prime : forall o u, In u (prime_reps o) -> prime o u.
Proof.
    intros. apply filter_In in H. destruct H. now destruct (prime_dec o u).
Qed.

Lemma prime_reps_index : forall o u, In u (prime_reps o) -> In u (row_index o).
Proof.
    intros. apply filter_In in H. now destruct H.
Qed.

Definition memr (o : hypothesis) (q : str) : bool := mem q (prime_reps o).

Definition cover_set (o : hypothesis) (u : str) : list str :=
    filter (fun p => if covered_dec o p u then true else false) (prime_reps o).

Lemma cover_set_prime_reps : forall o u p,
    In p (cover_set o u) -> In p (prime_reps o).
Proof.
    intros. apply filter_In in H. now destruct H.
Qed.

Lemma cover_set_memr : forall o u p,
    In p (cover_set o u) -> memr o p = true.
Proof.
    intros. now apply mem_In, (cover_set_prime_reps o u).
Qed.

(* Definition 8 *)
(** A table is RFSA-closed if, for each r \in Rows_low(T),
    r = fold Union {r' \in Primes_upper(T) | r' covered by r} *)

(** The closedness condition for a single lower row u: on every column, u's
    value is the join of the prime upper rows covered by it *)
Definition closed_row (o : hypothesis) (u : str) : Prop :=
    forall v, In v o.(V) ->
        cell o u v = true <->
        exists u', In u' o.(U) /\ prime o u' /\ covered o u' u /\ cell o u' v = true.

Lemma closed_row_dec : forall o u, {closed_row o u} + {~ closed_row o u}.
Proof.
    intros. unfold closed_row.
    induction (V o).
        left. intros. destruct H.
    assert (Pdec : {exists u', In u' o.(U) /\ prime o u' /\ covered o u' u /\ cell o u' a = true}
                 + {~ exists u', In u' o.(U) /\ prime o u' /\ covered o u' u /\ cell o u' a = true}).
    { clear IHl.
        induction (U o).
            right. intro Contra. destruct Contra, H. inversion H.
        destruct (prime_dec o a0).
        - destruct (covered_dec o a0 u).
          + destruct (Bool.bool_dec (cell o a0 a) true).
              left. exists a0. intuition.
            destruct IHl0.
              left. destruct e. exists x. split; [now right | intuition].
            right. intro Contra. destruct Contra, H, H0, H1, H.
              now subst.
            apply n0. eauto.
          + destruct IHl0.
              left. destruct e. exists x. split; [now right | intuition].
            right. intro Contra. destruct Contra, H, H0, H1, H.
              now subst.
            apply n0. eauto.
        - destruct IHl0.
            left. destruct e. exists x. split; [now right | intuition].
          right. intro Contra. destruct Contra, H, H0, H.
            now subst.
          apply n0. eauto.
    }
    destruct (Bool.bool_dec (cell o u a) true).
    - destruct Pdec.
      + destruct IHl.
            left. intros. destruct H; [subst; now split | auto].
        right. intro. apply n. intros. apply H. now right.
      + right. intro. apply n. now apply (proj1 (H a (or_introl eq_refl))).
    - destruct Pdec.
        right. intro. apply n. now apply (proj2 (H a (or_introl eq_refl))).
      destruct IHl.
        left. intros. destruct H.
            subst. intuition.
        now apply i.
      right. intro. apply n1. intros. apply H. now right.
Defined.

Definition closed (o : hypothesis) : Prop :=
    forall u, In u (USigma o) -> closed_row o u.

Lemma closed_dec : forall o,
    closed o + {u : str | In u (USigma o) /\ ~ closed_row o u}.
Proof.
    intros. unfold closed.
    induction (USigma o).
        left. intros. destruct H.
    destruct (closed_row_dec o a).
    - destruct IHl.
        left. intros. destruct H; auto; now subst.
      right. destruct s. exists x. split; [now right | intuition].
    - right. exists a. split; [now left | assumption].
Defined.

(* Definition 9 *)
(** A table is RFSA-consistent if for all u, u' \in U, a \in S,
    row(u') covered by row(u) -> row(u'a) covered by row(ua). *)
Definition rfsa_consistent (o : hypothesis) : Prop :=
    forall u u' a,
        In u o.(U) -> In u' o.(U) -> In a enum ->
        covered o u u' -> covered o (u ++ [a]) (u' ++ [a]).

Lemma consistent_triple_dec : forall o u u' a,
    {covered o u u' -> covered o (u ++ [a]) (u' ++ [a])} +
    {~ (covered o u u' -> covered o (u ++ [a]) (u' ++ [a]))}.
Proof.
    intros. destruct (covered_dec o u u').
    - destruct (covered_dec o (u ++ [a]) (u' ++ [a])).
        left. now intros.
      right. intro Contra. auto.
    - left. now intros.
Defined.

Lemma consistent_row_a_dec : forall o u a (us : list str),
    (forall u', In u' us -> covered o u u' -> covered o (u ++ [a]) (u' ++ [a]))
    + {u' : str | In u' us /\ ~ (covered o u u' -> covered o (u ++ [a]) (u' ++ [a]))}.
Proof.
    intros. induction us.
        left. intros. destruct H.
    destruct (consistent_triple_dec o u a0 a).
    - destruct IHus.
        left. intros. destruct H; subst; auto.
      right. destruct s. exists x. intuition.
    - right. exists a0. intuition.
Defined.

Lemma consistent_row_dec : forall o u (us : list str),
    (forall u' a, In u' us -> In a enum -> covered o u u' -> covered o (u ++ [a]) (u' ++ [a]))
    + {p : str * s.t | let '(u', a) := p in
        In u' us /\ In a enum /\ ~ (covered o u u' -> covered o (u ++ [a]) (u' ++ [a]))}.
Proof.
    intros. induction enum.
        left. intros. destruct H0.
    destruct (consistent_row_a_dec o u a us).
    - destruct IHl.
        left. intros. destruct H0; subst; auto.
      right. destruct s, x. exists (s, t0). intuition.
    - right. destruct s, a0. exists (x, a). intuition.
Defined.

Lemma consistent_outer_dec : forall o (us : list str),
    (forall u u' a, In u us -> In u' o.(U) -> In a enum -> covered o u u' -> covered o (u ++ [a]) (u' ++ [a]))
    + {p : str * str * s.t | let '(u, u', a) := p in
        In u us /\ In u' o.(U) /\ In a enum /\ ~ (covered o u u' -> covered o (u ++ [a]) (u' ++ [a]))}.
Proof.
    intros. induction us.
        left. intros. destruct H.
    destruct (consistent_row_dec o a (U o)).
    - destruct IHus.
        left. intros. destruct H; subst; auto.
      right. destruct s, x, p. exists (s, s0, t0). intuition.
    - right. destruct s, x. exists (a, s, t0). intuition.
Defined.

Lemma rfsa_consistent_dec : forall o,
    rfsa_consistent o
    + {p : str * str * s.t | let '(u, u', a) := p in
        In u o.(U) /\ In u' o.(U) /\ In a enum /\ ~ (covered o u u' -> covered o (u ++ [a]) (u' ++ [a]))}.
Proof.
    intros. unfold rfsa_consistent.
    destruct (consistent_outer_dec o (U o)); auto.
Defined.

(* Definition 10 *)
Definition make_rfsa (o : hypothesis) : N.t { q | memr o q = true }.
    set (state := { q | memr o q = true }).
    assert (initial : list state). {
        refine (list_with_proof (cover_set o []) (fun q => memr o q = true) _).
        intros x Hx. now apply (cover_set_memr o []). }
    assert (transition : state -> s.t -> list state). {
        intros q a.
        refine (list_with_proof (cover_set o (proj1_sig q ++ [a]))
                  (fun q' => memr o q' = true) _).
        intros x Hx. now apply (cover_set_memr o (proj1_sig q ++ [a])). }
    set (accept := fun (q : state) => o.(T) (proj1_sig q)).
    assert (mempf : forall x, In x (prime_reps o) -> memr o x = true)
        by (intros x Hx; now apply mem_In).
    set (ls := list_with_proof (prime_reps o) (fun q => memr o q = true) mempf).
    refine {| initial    := initial;
              transition := transition;
              accept     := accept;
              states     := ls;
              states_complete := _ |}.
    intros w q Hq.
    assert (Hin : In (proj1_sig q) (prime_reps o))
        by apply (mem_In str_eq), (proj2_sig q).
    assert (Heq : q = exist _ (proj1_sig q) (mempf (proj1_sig q) Hin)). {
        destruct q as (q' & Hq'); simpl.
        f_equal. apply (UIP_dec Bool.bool_dec). }
    rewrite Heq.
    apply (list_with_proof_complete (prime_reps o) (fun q => memr o q = true)).
    intros. apply UIP_dec, Bool.bool_dec.
Defined.

End NLstar.
