From Stdlib Require Import List.

Section SL.

Variable X : Type.
Variable eq_dec : forall (x y : X), {x = y} + {x <> y}.

Definition finite (f : X -> bool) :=
    {l : list X | NoDup l /\
        forall (s : X), f s = true <-> In s l}.

Definition num_states_of_fin {f : X -> bool} (H : finite f) : nat :=
    match H with
    | exist _ x _ => List.length x
    end.

(** Updating sets *)
Definition update (S : X -> bool) k b :=
    fun s => if eq_dec s k then b else S s.

Notation "s [ k := v ]" := (update s k v).

Lemma update_neq : forall S x y k,
    x <> y ->
    S[x := k] y = S y.
Proof.
    intros. unfold update.
    destruct eq_dec; now subst.
Qed.

Lemma update_eq : forall S x k,
    S[x := k] x = k.
Proof.
    intros. unfold update.
    destruct eq_dec; now subst.
Qed.

Lemma finite_subset_is_smaller : forall
    (f g : X -> bool)
    (FinF : finite f)
    (FinG : finite g)
    (FsubG : forall (x : X), f x = true -> g x = true),
    num_states_of_fin FinF <= num_states_of_fin FinG.
Proof.
    intros. destruct FinF as (fl & NDF & InF),
                     FinG as (gl & NDG & InG).
    simpl.
    apply NoDup_incl_length.
        assumption.
    unfold incl. intros x Hx.
    now apply (proj1 (InG x)), FsubG, (proj2 (InF x)).
Qed.

Lemma finite_update_impl_finite : forall
    (f : X -> bool) k v
    (FinUpdF : finite f[k := v]),
    finite f.
Proof.
    intros. destruct FinUpdF as (fl' & NDfl' & Infl).
    unfold finite, update in *.
    destruct v, (f k) eqn:Hfk.
    - exists fl'. split. assumption.
        intro s. specialize (Infl s). destruct (eq_dec s k).
            subst. now rewrite Hfk.
        assumption.
    - exists (filter f fl'). split.
        + clear Infl. induction fl' as [| h t IH].
            constructor.
          inversion NDfl'; subst. simpl. destruct (f h) eqn:Hfh.
            constructor.
                intro C. apply filter_In in C.
                now destruct C.
            now apply IH.
          now apply IH.
        + intro s. specialize (Infl s). rewrite filter_In. 
            destruct (eq_dec s k) as [e|n].
                subst. rewrite Hfk. now split; intro H.
            split; intro H.
                split; [now apply Infl | assumption].
            now destruct H.
    - exists (k :: fl'). split.
        + constructor; auto.
          intro C. specialize (Infl k). destruct (eq_dec k k).
            now rewrite <- Infl in C.
          contradiction.
        + intro s. specialize (Infl s). simpl. destruct (eq_dec s k).
            subst. rewrite Hfk. split; auto.
            split; intro H.
                right. now apply Infl.
            destruct H as [e2 | Hfl]; intuition.
    - exists fl'. split; auto.
        intro s. specialize (Infl s). destruct (eq_dec s k).
            subst. now rewrite Hfk.
            assumption.
Defined.

End SL.

