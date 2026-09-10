(** L* for Moore machines *)

From lstar Require Import automata.Moore ListLemmas SetLemmas RS Teacher Cache.
From lstar Require Import normalization.norm_moore.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.

Module MooreLstar (s : Symbol) (O : Output) (L : MooreLanguage s O)
                  (Tch : MooreTeacher s O L).
Import s O L Tch M.

(** T-equivalent: u ≡T v iff ∀t ∈ T, output_lang (u·t) = output_lang (v·t). *)
Definition T_equiv (T : str -> bool) (u v : str) : Prop :=
    forall (t : str),
        T t = true ->
        output_lang (u ++ t) = output_lang (v ++ t).

Notation "T '[' u '==' v ']'" := (T_equiv T u v).

(** ≡T is an equivalence relation. *)
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

(** For every T1 ⊆ T2, ≡T2 refines ≡T1. *)
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

Definition finite := SetLemmas.finite str.
Notation update := (SetLemmas.update str str_eq).
Notation "s [ k := v ]" := (update s k v).

(** T-equivalence is decidable for finite sets. *)
Definition T_equiv_dec : forall T (u v : str),
    finite T ->
    {T [u == v]} + {~ T [u == v]}.
Proof.
    intros. destruct X as (x & _ & i).
    destruct (forallb (fun t =>
        if O.eq_dec (output_lang (u ++ t)) (output_lang (v ++ t))
        then true else false) x) eqn:Hfb.
    - left. intros t Ht.
        rewrite forallb_forall in Hfb.
        specialize (Hfb t ltac:(now apply i)).
        destruct O.eq_dec eqn:E; [assumption | discriminate].
    - right. intro HTeq.
        apply Bool.not_true_iff_false in Hfb.
        apply Hfb. rewrite forallb_forall.
        intros t' HIn'.
        destruct O.eq_dec eqn:E; [reflexivity|].
        exfalso. apply n.
        now apply HTeq, i.
Defined.

(* Cache-passing T-equivalence *)

Definition row (T : str -> bool) (finT : finite T) (u : str) : list O.t :=
    List.map (fun t => output_lang (u ++ t)) (proj1_sig finT).

Lemma map_eq_pointwise : forall (A B : Type) (f g : A -> B) (l : list A),
    List.map f l = List.map g l <-> (forall x, In x l -> f x = g x).
Proof.
    intros A B f g l. induction l as [| a l IH]; simpl.
    - split.
      + intros _ x [].
      + reflexivity.
    - split.
      + intros Heq x Hx. injection Heq as Ha Htl.
        destruct Hx as [Hx | Hx].
        * subst x. exact Ha.
        * apply IH; assumption.
      + intros H. f_equal.
        * apply H. now left.
        * apply IH. intros x Hx. apply H. now right.
Qed.

Lemma row_iff : forall T (finT : finite T) (u v : str),
    row T finT u = row T finT v <-> T [u == v].
Proof.
    intros T finT u v. unfold row.
    destruct finT as (l & Hnd & Hiff). simpl.
    rewrite map_eq_pointwise. split.
    - intros H t Ht. apply H. exact (proj1 (Hiff t) Ht).
    - intros H x Hx. apply H. exact (proj2 (Hiff x) Hx).
Qed.

(** Cache-threading counterparts of [List.find] and [existsb] *)
Section Threaded.

Variables A St : Type.

Fixpoint find_c (f : St -> A -> bool * St) (c : St) (l : list A)
    : option A * St :=
    match l with
    | nil => (None, c)
    | x :: tl =>
        let (b, c') := f c x in
        if b then (Some x, c') else find_c f c' tl
    end.

Fixpoint existsb_c (f : St -> A -> bool * St) (c : St) (l : list A)
    : bool * St :=
    match l with
    | nil => (false, c)
    | x :: tl =>
        let (b, c') := f c x in
        if b then (true, c') else existsb_c f c' tl
    end.

Lemma find_c_spec : forall (f : St -> A -> bool * St) (g : A -> bool) l c,
    (forall c' x, fst (f c' x) = g x) ->
    fst (find_c f c l) = List.find g l.
Proof.
    intros f g l. induction l as [| a l IH]; intros c H; simpl.
    - reflexivity.
    - assert (Hb := H c a). destruct (f c a) as (b, c') eqn:Hf.
      simpl in Hb. subst b.
      destruct (g a); simpl.
      + reflexivity.
      + now apply IH.
Qed.

Lemma existsb_c_spec : forall (f : St -> A -> bool * St) (g : A -> bool) l c,
    (forall c' x, fst (f c' x) = g x) ->
    fst (existsb_c f c l) = existsb g l.
Proof.
    intros f g l. induction l as [| a l IH]; intros c H; simpl.
    - reflexivity.
    - assert (Hb := H c a). destruct (f c a) as (b, c') eqn:Hf.
      simpl in Hb. subst b.
      destruct (g a); simpl.
      + reflexivity.
      + now apply IH.
Qed.

End Threaded.

Arguments find_c {A St}.
Arguments existsb_c {A St}.

Lemma dec_agree : forall (P : Prop) (d1 d2 : {P} + {~ P}),
    (if d1 then true else false) = (if d2 then true else false).
Proof.
    intros P d1 d2. destruct d1, d2; try reflexivity; contradiction.
Qed.

Section RowCache.

Variable T : str -> bool.
Variable finT : finite T.

Definition rowfact : Type :=
    { p : str * list O.t | snd p = row T finT (fst p) }.

Definition rcache : Type := Cache.trie s.t rowfact.

Definition empty_rcache : rcache := Cache.empty.

Definition fact_of (u : str) : rowfact :=
    exist _ (u, row T finT u) eq_refl.

Definition cached_row (c : rcache) (u : str) :
    { r : list O.t | r = row T finT u } * rcache.
Proof.
    destruct (Cache.lookup s.eq_dec c u) as [p |].
    - destruct (str_eq (fst (proj1_sig p)) u) as [Hk | _].
      + refine (exist _ (snd (proj1_sig p)) _, c).
        rewrite <- Hk. exact (proj2_sig p).
      + exact (exist _ (row T finT u) eq_refl, Cache.insert s.eq_dec c u (fact_of u)).
    - exact (exist _ (row T finT u) eq_refl, Cache.insert s.eq_dec c u (fact_of u)).
Defined.

(* Cache-passing T-equivalence *)
Definition T_equiv_dec_c (u v : str) (c : rcache) :
    ({T [u == v]} + {~ T [u == v]}) * rcache.
Proof.
    destruct (cached_row c u) as ((ru & Hu) & c1).
    destruct (cached_row c1 v) as ((rv & Hv) & c2).
    destruct (list_eq_dec O.eq_dec ru rv) as [Heq | Hne].
    - refine (left _, c2).
      apply (proj1 (row_iff T finT u v)).
      rewrite <- Hu, <- Hv. exact Heq.
    - refine (right _, c2).
      intro Hc. apply Hne.
      rewrite Hu, Hv. exact (proj2 (row_iff T finT u v) Hc).
Defined.

End RowCache.

(** Q is separable wrt T when elements are pairwise T-distinguishable. *)
Definition separable (Q T : str -> bool) : Set :=
    forall (u v : str), Q u = true -> Q v = true ->
        u <> v ->
        ~ T [u == v].

(** Q is closed wrt T when every q·a has a T-equivalent representative. *)
Definition closed (Q T : str -> bool) : Set :=
    forall q a,
        Q q = true ->
        {q' : str | Q q' = true /\ T [(q ++ [a]) == q']}.

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
  pose (gq := fun (q : str) (a : s.t) (q' : str) =>
        if T_equiv_dec T (q ++ [a]) q' finT then true else false).
  pose (fq := fun (q : str) (a : s.t) (c : rcache T finT) (q' : str) =>
        let (d, c') := T_equiv_dec_c T finT (q ++ [a]) q' c in
        ((if d then true else false), c')).
  assert (Hq_agree : forall q a c q', fst (fq q a c q') = gq q a q').
  { intros q a c q'. unfold fq, gq.
    destruct (T_equiv_dec_c T finT (q ++ [a]) q' c) as (d, c') eqn:E.
    replace d with (fst (T_equiv_dec_c T finT (q ++ [a]) q' c)) by now rewrite E.
    simpl. apply dec_agree. }
  pose (g := fun (pat : str * s.t) =>
        let (q, a) := pat in negb (existsb (gq q a) Ql)).
  pose (fc := fun (c : rcache T finT) (pat : str * s.t) =>
        let (q, a) := pat in
        let (b, c') := existsb_c (fq q a) c Ql in (negb b, c')).
  assert (Hagree : forall c pat, fst (fc c pat) = g pat).
  { intros c (q, a). unfold fc, g.
    destruct (existsb_c (fq q a) c Ql) as (b, c') eqn:E. simpl.
    replace b with (fst (existsb_c (fq q a) c Ql)) by now rewrite E.
    f_equal. apply existsb_c_spec. intros. apply Hq_agree. }
  destruct (find_c fc (empty_rcache T finT) (list_prod Ql s.enum))
      as (o, cfin) eqn:Hfc.
  assert (Hfind : List.find g (list_prod Ql s.enum) = o).
  { rewrite <- (find_c_spec _ _ fc g (list_prod Ql s.enum)
                  (empty_rcache T finT) Hagree).
    now rewrite Hfc. }
  destruct o as [p |].
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
    unfold gq. destruct (T_equiv_dec T (q ++ [a]) q' finT); auto.
  - left. intros q a Hq.
    assert (Hex : existsb (gq q a) Ql = true).
    { apply List.find_none with (x := (q, a)) in Hfind.
      - now apply Bool.negb_false_iff in Hfind.
      - apply in_prod.
          now apply Qfin.
          apply s.t_enumerable. }
    (* Reuse the cache from the search above to locate the representative. *)
    destruct (find_c (fq q a) cfin Ql) as (o2, c2) eqn:H2.
    assert (Hfind2 : List.find (gq q a) Ql = o2).
    { rewrite <- (find_c_spec _ _ (fq q a) (gq q a) Ql cfin
                    (fun c' x => Hq_agree q a c' x)).
      now rewrite H2. }
    destruct o2 as [q' |].
    + apply List.find_some in Hfind2. destruct Hfind2 as (HIn' & Hchk').
      exists q'. split.
        now apply Qfin.
        unfold gq in Hchk'. now destruct (T_equiv_dec T (q ++ [a]) q' finT).
    + exfalso.
      rewrite existsb_exists in Hex. destruct Hex as (x & HInx & Hgx).
      apply List.find_none with (x := x) in Hfind2; [| exact HInx].
      rewrite Hfind2 in Hgx. discriminate.
Qed.

(** Lemma 1: the transition function is well defined. *)
Definition delta Q T (c : closed Q T) (q : str) (a : s.t) (Qq : Q q = true) :
        {q' : str | Q q' = true /\ T [q' == (q ++ [a])]}.
    destruct (c q a Qq) as [q' [Hq' Heq]].
    now exists q'.
Defined.

(** A hypothesis Moore machine. *)
Record HypothesisMoore : Type := {
  Q    : str -> bool;
  T    : str -> bool;
  sep  : separable Q T;
  clos : closed Q T;
  eps_in_Q : Q nil = true;
  fin_Q : finite Q;
  fin_T : finite T;
}.

(** The concrete Moore machine extracted from a HypothesisMoore.  The
    output of a state is the target output of its access string. *)
Definition make_moore (H : HypothesisMoore) : M.t {q | H.(Q) q = true}.
    set (state := {q | H.(Q) q = true}).
    assert (initial : state). {
        exists nil. apply H.(eps_in_Q). }
    assert (transition : state -> s.t -> state). {
        intros q a.
        set (r := delta H.(Q) H.(T) H.(clos) (proj1_sig q) a (proj2_sig q)).
        destruct r as (q' & Qq' & Teq). exists q'. apply Qq'. }
    set (out := fun (q : state) => output_lang (proj1_sig q)).
    destruct H.(fin_Q) as (l & ND & InQ).
    assert (InQpf : forall x, In x l -> H.(Q) x = true). {
        intros x Hin. now apply (proj2 (InQ x)). }
    set (ls := list_with_proof l (fun q => H.(Q) q = true) InQpf).
    refine {| initial    := initial;
              transition := transition;
              output     := out;
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

(** RS instance for Moore machines. *)
Module RSS <: MooreRS_Setup s O L.
  Definition obt := HypothesisMoore.
  Definition P (o : obt) (q : str) : Prop := o.(Q) q = true.
  Definition make_moore (o : obt) : M.t { q | P o q } := make_moore o.

  Lemma eps_in_H : forall (o : obt),
      proj1_sig (make_moore o).(initial _) = [].
  Proof.
    intro H. unfold make_moore, MooreLstar.make_moore, initial, fin_Q. simpl.
    now destruct H, fin_Q0, a.
  Qed.

  Lemma out_correct : forall (o : obt) q,
      output _ (make_moore o) q = output_lang (proj1_sig q).
  Proof.
    intros H q. unfold make_moore, MooreLstar.make_moore, output.
    now destruct fin_Q, a.
  Qed.
End RSS.

Module RSan := MooreRS s O L RSS.
Import RSan.

Theorem find_separable :
  forall (H : HypothesisMoore)
         (w : str)
         (Hce : output_string (make_moore H) w <> output_lang w),
  { q_new : str &
  { t     : str &
      (H.(Q) q_new = false) *
      let Q' := H.(Q) [q_new := true] in
      let T' := H.(T) [t := true] in
      separable Q' T' *
      finite Q' *
      finite T' }}.
    intros.
    destruct (RSan.partition_binary H w Hce) as
        (k & KCorrect & SKIncorrect).
    assert (Dist: output_lang (pi H w k ++ skipn k w) <>
                  output_lang (pi H w (S k) ++ skipn (S k) w)). {
        unfold correct, pi in *.
        now rewrite KCorrect.
    }
    assert (Hlt : k < length w). {
        destruct (Nat.le_gt_cases (length w) k) as [Hle |]; [|assumption].
        destruct SKIncorrect.
        unfold correct, pi in *.
        now rewrite firstn_all2, skipn_all2, app_nil_r in * by lia.
    }
    assert {wk | nth_error w k = Some wk}. {
        destruct (nth_error w k) eqn:E.
            now exists t0.
        rewrite nth_error_None in E. lia.
    } destruct H0 as (wk & Hwk).
    exists (pi H w k ++ [wk]), (skipn (S k) w).
    destruct (nth_error_split_sig _ _ _ Hwk) as (l1 & l2 & Hw & Hlen).
    assert (Hfirstn : firstn (S k) w = firstn k w ++ [wk]). {
        subst.
        now rewrite firstn_app, Nat.sub_succ_l,
                    firstn_all2, firstn_cons, Nat.sub_diag,
                    firstn_0, firstn_len_app by lia.
    }
    assert (run_step : forall i a,
          run (make_moore H) (firstn i w ++ [a]) =
          (make_moore H).(transition _) (run (make_moore H) (firstn i w)) a). {
      intros. unfold run. now rewrite fold_left_app.
    }
    assert (HTeq : H.(T) [pi H w k ++ [wk] == pi H w (S k)]). {
        unfold pi. rewrite Hfirstn, run_step.
        set (q := run (make_moore H) (firstn k w)).
        destruct (delta H.(Q) H.(T) H.(clos) (proj1_sig q)
                      wk (proj2_sig q)) as [q' [Hq' Heq]].
        unfold transition, make_moore, delta.
        now destruct H, fin_Q, a, clos, a.
    }
    assert (H.(Q) (pi H w (S k)) = true) by
        exact (proj2_sig (run (make_moore H) (firstn (S k) w))).
    repeat split.
    - pose proof H.(sep). unfold separable in H1.
      destruct (H.(Q) (pi H w k ++ [wk])) eqn:HQ; auto.
      destruct Dist.
      assert (pi H w k ++ [wk] = pi H w (S k)). {
          destruct (str_eq (pi H w k ++ [wk]) (pi H w (S k))) as [|Hneq].
            easy.
          destruct (H.(sep) _ _ HQ H0 Hneq HTeq).
      } subst.
      now rewrite <- H2, skipn_len_app, skipn_Slen_cons_app, <- app_assoc.
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

(** Lemma 3 *)
Lemma find_representative : forall Q T
    (finQ : finite Q)
    (finT : finite T)
    (u : str),
    { r | Q r = true /\ T [u == r] } +
    { forall r, Q r = true -> ~ T [u == r] }.
Proof with try easy.
    intros Q T finQ finT u.
    destruct finQ as (Ql & HQl).
    pose (gr := fun (q : str) => if T_equiv_dec T u q finT then true else false).
    pose (fr := fun (c : rcache T finT) (q : str) =>
          let (d, c') := T_equiv_dec_c T finT u q c in
          ((if d then true else false), c')).
    assert (Hr_agree : forall c q, fst (fr c q) = gr q).
    { intros c q. unfold fr, gr.
      destruct (T_equiv_dec_c T finT u q c) as (d, c') eqn:E.
      replace d with (fst (T_equiv_dec_c T finT u q c)) by now rewrite E.
      simpl. apply dec_agree. }
    destruct (find_c fr (empty_rcache T finT) Ql) as (o, cfin) eqn:Hfc.
    assert (Hfind : List.find gr Ql = o).
    { rewrite <- (find_c_spec _ _ fr gr Ql (empty_rcache T finT) Hr_agree).
      now rewrite Hfc. }
    destruct o as [r0 |].
    - left. apply List.find_some in Hfind.
      destruct Hfind as (HIn & Hcheck).
      exists r0. split.
        apply HQl...
      unfold gr in Hcheck. destruct (T_equiv_dec T u r0 finT)...
    - right. intros r Hr Contra.
      apply List.find_none with (x := r) in Hfind.
      + unfold gr in Hfind. destruct (T_equiv_dec T u r finT)...
      + apply HQl...
Defined.

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
    Nat.pow (length O.enum) (length Tl) - length (proj1_sig finQ') < n ->
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
      enough (Hlt : length Q'l < length Q''l <= Nat.pow (length O.enum) (length Tl)) by lia. {
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
        set (vec := fun u => map (fun t => output_lang (u ++ t)) Tl).
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
            assert (Hmu : nth_error (vec u) i = Some (output_lang (u ++ t))). {
                unfold vec. rewrite nth_error_map, nth_error_nth' with (d := t); [|lia].
                now rewrite Hnth. }
            assert (Hmv : nth_error (vec v) i = Some (output_lang (v ++ t))). {
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
        (* |O|^{|Tl|} bound on distinct output-vectors *)
        apply NoDup_finlist_length. assumption.
        - intros v Hv.
          apply in_map_iff in Hv.
          destruct Hv as (u & <- & _).
          unfold vec. apply length_map.
        - intros v x Hv Hx.
          apply in_map_iff in Hv. destruct Hv as (u & <- & _).
          unfold vec in Hx. apply in_map_iff in Hx.
          destruct Hx as (t & <- & _). apply O.t_enumerable. }
      eexists. now rewrite Eq'.
Defined.

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
    set (fuel := S (Init.Nat.pow (length O.enum) (length Tl))).
    destruct (loop_terminates fuel Q Q T sep finQ Tl NDT HTl ltac:(auto) ltac:(lia)).
    destruct x as (Q' & ((clos' & sep') & finQ') & sub').
    exists Q'. repeat split; auto.
Defined.

Definition num_states (H : HypothesisMoore) : nat :=
    num_states_of_fin _ H.(fin_Q).

(** A hypothesis is no bigger than the minimal Moore machine (separability). *)
Lemma num_states_le_min : forall (H : HypothesisMoore),
    num_states H <= L.num_states_in_minimal.
Proof.
  intro H.
  destruct L.exists_moore as (state_m & Mm & (Menc & Minimal) & Len).
  enough (Hle : num_states H <= Datatypes.length (M.states state_m Mm)) by lia.
  unfold num_states, num_states_of_fin.
  destruct H as [Q0 T0 sep0 clos0 eps0 finQ0 finT0].
  destruct finQ0 as (Ql & NDQl & InQl). simpl.
  set (f := fun q => M.run Mm q).
  assert (Hinj : forall u v, In u Ql -> In v Ql -> u <> v -> f u <> f v). {
    intros u v Hu Hv Huv Hf.
    apply (sep0 u v); try (now apply InQl); try assumption.
    intros t Ht.
    assert (Hsplit : forall x,
              M.output_string Mm (x ++ t)
              = Mm.(M.output _) (fold_left Mm.(M.transition _) t (f x))). {
      intro x. unfold M.output_string, M.run, f. now rewrite fold_left_app. }
    assert (Hout : M.output_string Mm (u ++ t) = M.output_string Mm (v ++ t)). {
      rewrite !Hsplit. unfold f in *. now rewrite Hf. }
    rewrite <- (Menc (u ++ t)), <- (Menc (v ++ t)). exact Hout.
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
    destruct Hst as (q & <- & _). apply M.run_in_states.
Qed.

Lemma make_moore_minimal : forall (H : HypothesisMoore),
    equiv_query (make_moore H) = None ->
    minimal (make_moore H).
Proof.
  intros H Heq.
  unfold minimal. split.
    now apply equiv_query_correct in Heq.
  intros state' m' H_encodes.
  assert (H_LHS : Datatypes.length (M.states _ (make_moore H)) = num_states H). {
    unfold num_states, num_states_of_fin, make_moore.
    destruct H, fin_Q0, a. simpl. apply list_with_proof_preserves_len. }
  rewrite H_LHS.
  unfold num_states, num_states_of_fin.
  destruct H as [Q0 T0 sep0 clos0 eps0 finQ0 finT0].
  destruct finQ0 as (Ql & NDQl & InQl). simpl.
  set (f := fun q => M.run m' q).
  assert (Hinj : forall u v, In u Ql -> In v Ql -> u <> v -> f u <> f v). {
    intros u v Hu Hv Huv Hf.
    apply (sep0 u v); try (now apply InQl); try assumption.
    intros t Ht.
    assert (Hsplit : forall x,
              M.output_string m' (x ++ t)
              = m'.(M.output _) (fold_left m'.(M.transition _) t (f x))). {
      intro x. unfold M.output_string, M.run, f. now rewrite fold_left_app. }
    assert (Hout : M.output_string m' (u ++ t) = M.output_string m' (v ++ t)). {
      rewrite !Hsplit. unfold f in *. now rewrite Hf. }
    rewrite <- (H_encodes (u ++ t)), <- (H_encodes (v ++ t)). exact Hout.
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
    destruct Hst as (q & <- & _). apply M.run_in_states.
Qed.

Lemma full_states_no_ce : forall (H : HypothesisMoore),
    L.num_states_in_minimal <= num_states H ->
    equiv_query (make_moore H) = None.
Proof.
  intros H Hge.
  destruct (equiv_query (make_moore H)) eqn:Heq; [exfalso | reflexivity].
  assert (Hce : output_string (make_moore H) s <> output_lang s)
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
  pose proof (num_states_le_min H'') as Hcap.
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
  unfold num_states in *. simpl in *.
  rewrite HH'' in *. lia.
Qed.

Module Norm := NormalizeMoore s O M.

Definition state_eq_dec (H : HypothesisMoore) :
    forall (x y : {q | H.(Q) q = true}), {x = y} + {x <> y}.
Proof.
  intros [x Hx] [y Hy].
  destruct (str_eq x y) as [Heq | Hne].
  - left. subst y. f_equal. apply UIP_dec, Bool.bool_dec.
  - right. intro C. inversion C. contradiction.
Defined.

Lemma make_moore_trans_closed (H : HypothesisMoore) :
    Norm.TransClosed (make_moore H).
Proof.
  unfold Norm.TransClosed. intros [q Hq] a _.
  set (tgt := M.transition _ (make_moore H) (exist _ q Hq) a).
  unfold M.states, make_moore. cbn.
  destruct H.(fin_Q) as (l & ND & InQ) eqn:HF.
  assert (Hmem : In (proj1_sig tgt) l)
    by (apply (proj1 (InQ (proj1_sig tgt))); exact (proj2_sig tgt)).
  replace tgt
    with (exist (fun q0 => Q H q0 = true) (proj1_sig tgt)
                (proj2 (InQ (proj1_sig tgt)) Hmem)); cycle 1.
    destruct tgt as [v pf]. cbn. f_equal. apply UIP_dec, Bool.bool_dec.
  apply (list_with_proof_complete l (fun q0 => Q H q0 = true)
           (fun x0 p0 q0 => UIP_dec Bool.bool_dec p0 q0)
           (fun x0 Hin => proj2 (InQ x0) Hin)
           (proj1_sig tgt) Hmem).
Qed.

Definition odefault (H : HypothesisMoore) : O.t :=
  M.output _ (make_moore H) (make_moore H).(initial _).

Fixpoint mlstar_fuel (H : HypothesisMoore) (fuel : nat)
    (LE : L.num_states_in_minimal - num_states H <= fuel)
    : { m : M.t nat | minimal m }.
  destruct (equiv_query (make_moore H)) eqn:Heq.
  - destruct fuel as [| n].
    + exfalso.
      assert (Hge : L.num_states_in_minimal <= num_states H) by lia.
      now rewrite (full_states_no_ce H Hge) in Heq.
    + assert (Hce : output_string (make_moore H) s <> output_lang s)
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
      eapply (mlstar_fuel {|
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
  - pose (m0   := make_moore H).
    pose (edec := state_eq_dec H).
    pose (tc   := make_moore_trans_closed H).
    exists (Norm.normalize edec m0 tc (odefault H)).
    pose proof (make_moore_minimal H Heq) as [Henc0 Hmin0].
    split.
    + intro w. unfold m0 in *.
      rewrite (Norm.normalize_output_string edec _ tc (odefault H) w).
      exact (Henc0 w).
    + intros state' dfa' Henc'.
      unfold Norm.normalize, Norm.build, M.states, Norm.ND.n_states. cbn.
      rewrite length_seq.
      etransitivity; eauto using dedup_length_le.
Defined.

(** The total L* implementation for Moore machines. *)
Definition mlstar (_ : unit) : { m : M.t nat | minimal m }.
    eapply mlstar_fuel with (fuel := num_states_in_minimal).
        lia.
    Unshelve.
    set (Q := fun s => if str_eq s nil then true else false).
    set (T := fun (_ : str) => false).
    eapply (Build_HypothesisMoore Q T); auto;
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

End MooreLstar.
