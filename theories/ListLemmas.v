From Stdlib Require Import List.

Lemma firstn_len_app : forall X (l1 l2 : list X),
    firstn (length l1) (l1 ++ l2) = l1.
Proof.
    induction l1; intros; simpl in *.
        reflexivity.
    now rewrite IHl1.
Qed.

Lemma skipn_len_app : forall X (l1 l2 : list X),
    skipn (length l1) (l1 ++ l2) = l2.
Proof.
    induction l1; intros; simpl in *.
        reflexivity.
    now rewrite IHl1.
Qed.

Lemma skipn_Slen_cons_app : forall X (l1 l2 : list X) x,
    skipn (S (length l1)) (l1 ++ x :: l2) = l2.
Proof.
    induction l1; intros; simpl in *.
        reflexivity.
    now rewrite IHl1.
Qed.

Lemma skipn_S_wk : forall (X : Type) (w : list X) k wk,
    nth_error w k = Some wk ->
    skipn k w = wk :: skipn (S k) w.
Proof.
    intros X w. induction w; intros.
    - destruct k; discriminate.
    - destruct k.
      + simpl in H. injection H. intro. subst. reflexivity.
      + simpl in *. apply IHw. assumption.
Qed.

Lemma nth_error_split_sig :
    forall {A : Type} (l : list A) (n : nat) (a : A),
    nth_error l n = Some a ->
    {l1 : list A & {l2 : list A | l = l1 ++ a :: l2 /\ length l1 = n}}.
Proof.
  intros. generalize dependent l.
  induction n as [|n IH]; intros [|x l] H; [easy| |easy|].
  - exists nil; exists l. now injection H as [= ->].
  - destruct (IH _ H) as (l1 & l2 & H1 & H2).
    exists (x::l1); exists l2; simpl; split; now f_equal.
Qed.
