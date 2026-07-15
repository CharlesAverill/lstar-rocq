(** Rivest-Schapire counterexample analysis: https://doi.org/10.1006/inco.1993.1021*)

From Stdlib Require Import Lia PeanoNat.
From lstar Require Import automata.DFA automata.Moore.

Module Type RS_Setup (s : Symbol) (L : RegularLanguage s).
Import s L D.

(* An algorithm's internal representation of an observation table *)
Parameter obt : Type.

(* An algorithm's function to construct a DFA from an observation table *)
Parameter P : obt -> str -> Prop.
Parameter make_dfa : forall (o : obt), D.t {s : str | P o s}.

(* Epsilon is the start state of H *)
Parameter eps_in_H : forall (o : obt),
    proj1_sig (make_dfa o).(initial _) = [].

(* DFA acceptance is equivalent to membership *)
Parameter acc_correct : forall (o : obt),
    forall q, accept _ (make_dfa o) q = member (proj1_sig q).
End RS_Setup.

Module RS (s : Symbol) (L : RegularLanguage s) (Setup : RS_Setup s L).
Import s L D Setup.

(** [pi t w i] is the access string of the state that the hypothesis reaches
    after reading the length-i prefix of w *)
Definition pi (o : obt) (w : str) (i : nat) : str :=
    proj1_sig (run (make_dfa o) (firstn i w)).

(** A prefix of length i is _correct_ when its continuation classifies as in
    the language exactly when w does *)
Definition correct (o : obt) (w : str) (i : nat) : Prop :=
    member (pi o w i ++ skipn i w) = member w.

Lemma correct_dec : forall o w i, {correct o w i} + {~ correct o w i}.
Proof.
    intros. unfold correct. destruct member, member; decide equality.
Defined.

Lemma eps_correct : forall o w,
    correct o w 0.
Proof.
    intros. pose proof (eps_in_H o).
    unfold correct, pi, run; simpl in *.
    destruct (make_dfa o), initial0.
    now rewrite H.
Qed.

Lemma full_not_correct : forall o w,
    (* w is a counterexample *)
    accept_string (make_dfa o) w <> member w ->
    ~ correct o w (List.length w).
Proof.
    intros o w Hce Contra.
    pose proof (acc_correct o).
    unfold correct, pi in Contra.
    rewrite firstn_all, skipn_all, app_nil_r in Contra.
    unfold accept_string, accept, run, transition, initial in *.
    destruct Hce, (make_dfa o).
    now rewrite H.
Qed.

(** Linear search for an adjacent correctness flip *)
Theorem partition_linear : forall o w,
    (* w is a counterexample *)
    accept_string (make_dfa o) w <> member w ->
    {k | correct o w k /\ ~ correct o w (S k) }.
Proof.
    intros o w Hce. pose proof (acc_correct o).
    pose proof (eps_correct o w) as C0.
    pose proof (full_not_correct o w Hce) as ICm.
    induction (List.length w) as [| n IH].
        contradiction.
    destruct (correct_dec o w n).
        now exists n.
    destruct (IH n0) as (k & ck & ncSk).
    now exists k.
Defined.

(* Binary search for an adjacent correctness flip

   Given disagreeing endpoints, find an adjacent flip inside [lo, hi].
   Structural decreasing measure is [hi - lo] *)
Theorem partition_binary : forall o w,
    (* w is a counterexample *)
    accept_string (make_dfa o) w <> member w ->
    {k | correct o w k /\ ~ correct o w (S k) }.
Proof.
    intros o w Hce.
    pose proof (eps_correct o w) as C0.
    pose proof (full_not_correct o w Hce) as Cm.
    (* Search [lo, hi] with correct lo, ~correct hi, lo < hi, by strong
       induction on the gap (hi - lo). *)
    assert (search : forall gap lo hi,
        hi - lo <= gap ->
        lo < hi ->
        correct o w lo ->
        ~ correct o w hi ->
        {k | correct o w k /\ ~ correct o w (S k)}). {
      induction gap as [| gap IHgap]; intros lo hi Hgap Hlt Clo Chi.
        lia.
      (* if hi = S lo, the flip is at lo.
         Otherwise, look for the midpoint *)
        destruct (Nat.eqb hi (S lo)) eqn:E.
        - exists lo. split; [assumption|].
          apply Nat.eqb_eq in E. now rewrite <- E.
        - (* lo + 1 < hi, so there is a midpoint strictly between *)
          set (mid := Nat.div2 (lo + hi)).
          assert (Hmid_lo : lo < mid). {
            unfold mid.
            apply Nat.div2_le_lower_bound.
            apply Nat.eqb_neq in E. lia. }
          assert (Hmid_hi : mid < hi). {
            unfold mid. rewrite Nat.div2_div.
            apply Nat.Div0.div_lt_upper_bound. lia. }
          destruct (correct_dec o w mid).
          (* correct at mid: recurse on [mid, hi] *)
            apply (IHgap mid hi); now try lia.
          (* incorrect at mid: recurse on [lo, mid] *)
            apply (IHgap lo mid); now try lia.
    }
    (* search(length w, 0 length w) *)
    destruct (Nat.eqb (List.length w) 0) eqn:E.
    - destruct Cm. apply Nat.eqb_eq in E. now rewrite E.
    - apply Nat.eqb_neq in E.
      apply (search (List.length w) 0 (List.length w)); now try lia.
Defined.

End RS.

(** Rivest-Schapire counterexample analysis for Moore machines *)

Module Type MooreRS_Setup (s : Symbol) (O : Output) (L : MooreLanguage s O).
Import s O L M.

(* An algorithm's internal representation of an observation table *)
Parameter obt : Type.

(* An algorithm's function to construct a Moore machine from a table *)
Parameter P : obt -> str -> Prop.
Parameter make_moore : forall (o : obt), M.t {s : str | P o s}.

(* Epsilon is the start state of H *)
Parameter eps_in_H : forall (o : obt),
    proj1_sig (make_moore o).(initial _) = [].

(* Machine output at a state is the target output of its access string *)
Parameter out_correct : forall (o : obt),
    forall q, output _ (make_moore o) q = output_lang (proj1_sig q).
End MooreRS_Setup.

Module MooreRS (s : Symbol) (O : Output) (L : MooreLanguage s O) (Setup : MooreRS_Setup s O L).
Import s O L M Setup.

(** [pi o w i] is the access string of the state that the hypothesis
    reaches after reading the length-i prefix of w *)
Definition pi (o : obt) (w : str) (i : nat) : str :=
    proj1_sig (run (make_moore o) (firstn i w)).

(** A prefix of length i is _correct_ when its continuation produces the
    same output as w does. *)
Definition correct (o : obt) (w : str) (i : nat) : Prop :=
    output_lang (pi o w i ++ skipn i w) = output_lang w.

Lemma correct_dec : forall o w i, {correct o w i} + {~ correct o w i}.
Proof.
    intros. unfold correct. apply O.eq_dec.
Defined.

Lemma eps_correct : forall o w,
    correct o w 0.
Proof.
    intros. pose proof (eps_in_H o).
    unfold correct, pi, run; simpl in *.
    destruct (make_moore o), initial0.
    now rewrite H.
Qed.

Lemma full_not_correct : forall o w,
    (* w is a counterexample *)
    output_string (make_moore o) w <> output_lang w ->
    ~ correct o w (List.length w).
Proof.
    intros o w Hce Contra.
    pose proof (out_correct o).
    unfold correct, pi in Contra.
    rewrite firstn_all, skipn_all, app_nil_r in Contra.
    unfold output_string, output, run, transition, initial in *.
    destruct Hce, (make_moore o).
    now rewrite H.
Qed.

(** Linear search for an adjacent correctness flip *)
Theorem partition_linear : forall o w,
    output_string (make_moore o) w <> output_lang w ->
    {k | correct o w k /\ ~ correct o w (S k) }.
Proof.
    intros o w Hce. pose proof (out_correct o).
    pose proof (eps_correct o w) as C0.
    pose proof (full_not_correct o w Hce) as ICm.
    induction (List.length w) as [| n IH].
        contradiction.
    destruct (correct_dec o w n).
        now exists n.
    destruct (IH n0) as (k & ck & ncSk).
    now exists k.
Defined.

(** Binary search for an adjacent correctness flip *)
Theorem partition_binary : forall o w,
    output_string (make_moore o) w <> output_lang w ->
    {k | correct o w k /\ ~ correct o w (S k) }.
Proof.
    intros o w Hce.
    pose proof (eps_correct o w) as C0.
    pose proof (full_not_correct o w Hce) as Cm.
    assert (search : forall gap lo hi,
        hi - lo <= gap ->
        lo < hi ->
        correct o w lo ->
        ~ correct o w hi ->
        {k | correct o w k /\ ~ correct o w (S k)}). {
      induction gap as [| gap IHgap]; intros lo hi Hgap Hlt Clo Chi.
        lia.
        destruct (Nat.eqb hi (S lo)) eqn:E.
        - exists lo. split; [assumption|].
          apply Nat.eqb_eq in E. now rewrite <- E.
        - set (mid := Nat.div2 (lo + hi)).
          assert (Hmid_lo : lo < mid). {
            unfold mid.
            apply Nat.div2_le_lower_bound.
            apply Nat.eqb_neq in E. lia. }
          assert (Hmid_hi : mid < hi). {
            unfold mid. rewrite Nat.div2_div.
            apply Nat.Div0.div_lt_upper_bound. lia. }
          destruct (correct_dec o w mid).
            apply (IHgap mid hi); now try lia.
            apply (IHgap lo mid); now try lia.
    }
    destruct (Nat.eqb (List.length w) 0) eqn:E.
    - destruct Cm. apply Nat.eqb_eq in E. now rewrite E.
    - apply Nat.eqb_neq in E.
      apply (search (List.length w) 0 (List.length w)); now try lia.
Defined.

End MooreRS.
