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
    filter (fun u => if prime_dec T V Ul u finV then true else false) Ul.

Lemma prime_reps_upper : forall T V Ul finV u,
    In u (prime_reps T V Ul finV) -> In u Ul.
Proof.
    intros. apply filter_In in H. now destruct H.
Qed.

Lemma prime_reps_prime : forall T V Ul finV u,
    In u (prime_reps T V Ul finV) -> prime T V Ul u.
Proof.
    intros. apply filter_In in H. destruct H. now destruct (prime_dec T V Ul u finV).
Qed.

Lemma prime_reps_index : forall T V Ul finV u,
    In u (prime_reps T V Ul finV) -> In u (row_index Ul).
Proof.
    intros T V Ul finV u H. unfold prime_reps in H.
    apply filter_In in H. destruct H.
    unfold row_index. apply in_or_app. now left.
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

Definition closed (T V : str -> bool) {U} (Ul : finite U) : Prop :=
    forall u, In u (row_index (proj1_sig Ul)) -> closed_row T V (proj1_sig Ul) u.

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

(* Definition 9 *)
(** A table is RFSA-consistent if covering is preserved by one-letter extension *)
Definition rfsa_consistent (T V : str -> bool) {U} (Ul : finite U) : Prop :=
    forall u u' a,
        In u (row_index (proj1_sig Ul)) -> In u' (row_index (proj1_sig Ul)) -> In a enum ->
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

(* Definition 10 *)
(** A hypothesis RFSA bundles the table with its finiteness, closedness, and
    consistency invariants, after Lstar's HypothesisDFA *)
Record HypothesisRFSA : Type := {
  T    : str -> bool;
  U    : str -> bool;
  V    : str -> bool;
  fin_U : finite U;
  fin_V : finite V;
  clos : closed T V fin_U;
  cons : rfsa_consistent T V fin_U;
  (* U is prefix-closed *)
  pref : forall w w', U (w ++ w') = true -> U w = true;
  (* V is suffix-closed *)
  suff : forall w w', V (w ++ w') = true -> V w' = true;
  (* epsilon is in U and V *)
  eps_U : U [] = true;
  eps_V : V [] = true;
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

Lemma covered_trans : forall T V a b c,
    covered T V a b -> covered T V b c -> covered T V a c.
Proof.
    unfold covered. intros. apply H0; auto.
Qed.

Lemma state_row_index : forall H (q : { q | memr H q = true }),
    In (proj1_sig q) (row_index (Ul H)).
Proof.
    intros. eapply prime_reps_index, mem_In. destruct q. eauto.
Qed.

(* Lemma 1 *)
Lemma run_covered : forall H u r,
    H.(U) u = true ->
    In r (run (make_rfsa H) u) ->
    covered H.(T) H.(V) (proj1_sig r) u.
Proof.
    intros H u. induction u using rev_ind; intros r Hu Hr.
    - unfold run, run_from in Hr. simpl in Hr.
      unfold make_rfsa in Hr. simpl in Hr.
      apply in_list_with_proof in Hr.
      apply filter_In in Hr. destruct Hr as (_ & Hcov).
      now destruct (covered_dec H.(T) H.(V) (proj1_sig r) [] H.(fin_V)).
    - unfold run in Hr. unfold run_from in Hr.
      rewrite fold_left_app in Hr. simpl in Hr.
      unfold step in Hr. apply in_flat_map in Hr.
      destruct Hr as (q & Hq & Hr).
      assert (HUu : H.(U) u = true) by (now apply (H.(pref) u [x])).
      assert (Hqu : covered H.(T) H.(V) (proj1_sig q) u) by auto.
      unfold make_rfsa in Hr. simpl in Hr.
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

Lemma cell_app : forall T u a v,
    cell T u (a :: v) = cell T (u ++ [a]) v.
Proof. intros. unfold cell. now rewrite <- app_assoc. Qed.

Lemma accept_cell : forall H q,
    accept _ (make_rfsa H) q = cell H.(T) (proj1_sig q) [].
Proof. intros. unfold cell. now rewrite app_nil_r. Qed.

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

Lemma state_upper : forall H (q : { q | memr H q = true }),
    In (proj1_sig q) (Ul H).
Proof.
    intros. apply (prime_reps_upper H.(T) H.(V) (Ul H) H.(fin_V)).
    apply (mem_In str_eq). now destruct q.
Qed.

Lemma run_from_set_accept : forall H v qs,
    H.(V) v = true ->
    (forall q, In q qs -> In (proj1_sig q) (Ul H)) ->
    existsb (accept _ (make_rfsa H)) (run_from (make_rfsa H) qs v) = true
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
      fold (run_from (make_rfsa H) (step (transition _ (make_rfsa H)) qs a) v).
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
            apply list_with_proof_complete. intros. apply UIP_dec, Bool.bool_dec.
      + intros p Hp. unfold step in Hp. apply in_flat_map in Hp.
        destruct Hp as (q & Hq & Hp).
        apply in_list_with_proof in Hp.
        apply (prime_reps_upper H.(T) H.(V) (Ul H) H.(fin_V)).
        now apply (cover_set_prime_reps _ _ _ _ (proj1_sig q ++ [a])).
Qed.

(* Lemma 2 *)
Lemma row_state_lang : forall H (r : { q | memr H q = true }) v,
    H.(V) v = true ->
    (cell H.(T) (proj1_sig r) v = true <-> N.L_state (make_rfsa H) r v = true) /\
    (cell H.(T) [] v = true <-> N.L_aut (make_rfsa H) v = true).
Proof.
    intros H r v Hv. split.
    - unfold N.L_state.
      rewrite (run_from_set_accept H v [r] Hv).
      + split.
          intro Hc. exists r. split. now left. assumption.
        now intros (q & [<- | []] & Hc).
      + intros q [<- | []]. apply state_upper.
    - unfold N.L_aut, N.accept_string, run.
      rewrite (run_from_set_accept H v (N.initial _ (make_rfsa H)) Hv).
      + unfold make_rfsa. simpl. rewrite <- cover_set_cell; auto.
        * split.
            intros (q & Hq & Hc).
              exists (exist _ q (cover_set_memr H [] q Hq)). split.
                apply list_with_proof_complete.
                    intros. apply UIP_dec, Bool.bool_dec.
                assumption.
            intros (q & Hq & Hc).
              apply in_list_with_proof in Hq.
              now exists (proj1_sig q).
        * unfold row_index, Ul. apply in_or_app. left.
          destruct H, fin_U0, a; simpl in *. now apply i.
      + intros q Hq.
        unfold make_rfsa in Hq. cbn [N.initial] in Hq.
        apply in_list_with_proof in Hq.
        apply (prime_reps_upper H.(T) H.(V) (Ul H) H.(fin_V)).
        now apply (cover_set_prime_reps _ _ _ _ []).
Qed.

End NLstar.
