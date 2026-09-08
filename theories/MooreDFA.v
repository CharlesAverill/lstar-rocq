(** DFAs as Moore machines over [bool] *)

From Stdlib Require Import Bool List.
From lstar Require Import automata.DFA automata.Moore Teacher.
Import ListNotations.

(* Bool output alphabet *)
Module BoolOutput <: Output.
    Definition t := bool.
    Definition eq_dec := Bool.bool_dec.
    Definition enum := [true; false].
    Lemma t_enumerable : forall (x : t), In x enum.
    Proof. intros [|]; cbn; auto. Qed.
End BoolOutput.

Lemma bool_iff_eq : forall (b c : bool), (b = true <-> c = true) -> c = b.
Proof. intros [] [] [H1 H2]; auto; symmetry; auto. Qed.

Lemma eq_bool_iff : forall (b c : bool), c = b -> (b = true <-> c = true).
Proof. intros b c H; subst; split; auto. Qed.

(* The Moore view of a regular language *)
Module MooreView (s : Symbol) (L : RegularLanguage s) (T : DFATeacher s L).

    (** [L] as a Moore language over [bool] *)
    Module ML <: MooreLanguage s BoolOutput.
        Module M := Moore s BoolOutput.

        Definition of_dfa {state : Type} (d : L.D.t state) : M.t state :=
            {| M.transition := L.D.transition state d;
               M.initial := L.D.initial state d;
               M.output := L.D.accept state d;
               M.states := L.D.states state d;
               M.states_complete := L.D.states_complete state d |}.

        Definition to_dfa {state : Type} (m : M.t state) : L.D.t state :=
            {| L.D.transition := M.transition state m;
               L.D.initial := M.initial state m;
               L.D.accept := M.output state m;
               L.D.states := M.states state m;
               L.D.states_complete := M.states_complete state m |}.

        Definition output_lang : s.str -> BoolOutput.t := L.member.

        Definition encodes {state : Type} (m : M.t state) : Prop :=
            forall (w : s.str), M.output_string m w = output_lang w.

        Definition minimal {state : Type} (m : M.t state) : Prop :=
            encodes m /\
            forall (state' : Type) (m' : M.t state'),
                encodes m' ->
                List.length (M.states state m) <= List.length (M.states state' m').

        Definition num_states_in_minimal : nat := L.num_states_in_minimal.

        (** The two views agree on every string *)
        Lemma of_dfa_output : forall {state : Type} (d : L.D.t state) (w : s.str),
            M.output_string (of_dfa d) w = L.D.accept_string d w.
        Proof. reflexivity. Qed.

        Lemma to_dfa_accept : forall {state : Type} (m : M.t state) (w : s.str),
            L.D.accept_string (to_dfa m) w = M.output_string m w.
        Proof. reflexivity. Qed.

        Lemma encodes_of_dfa : forall {state : Type} (d : L.D.t state),
            L.encodes d <-> encodes (of_dfa d).
        Proof.
            intros state d. split; intros H w.
            - rewrite of_dfa_output. apply bool_iff_eq, H.
            - apply eq_bool_iff. rewrite <- of_dfa_output. apply H.
        Qed.

        Lemma encodes_to_dfa : forall {state : Type} (m : M.t state),
            encodes m <-> L.encodes (to_dfa m).
        Proof.
            intros state m. split; intros H w.
            - apply eq_bool_iff. rewrite to_dfa_accept. apply H.
            - rewrite <- to_dfa_accept. apply bool_iff_eq, H.
        Qed.

        Lemma exists_moore : exists state (m : M.t state),
            minimal m /\ List.length (M.states state m) <= num_states_in_minimal.
        Proof.
            destruct L.exists_dfa as (state & d & (Henc & Hmin) & Hlen).
            exists state, (of_dfa d). repeat split.
            - now apply encodes_of_dfa.
            - intros state' m' Henc'.
              apply (Hmin state' (to_dfa m') (proj1 (encodes_to_dfa m') Henc')).
            - apply Hlen.
        Qed.
    End ML.

    (* [T] as a Moore teacher *)
    Module MT <: MooreTeacher s BoolOutput ML.
        Definition equiv_query {state : Type} (m : ML.M.t state) : option s.str :=
            T.equiv_query (ML.to_dfa m).

        Lemma equiv_query_correct : forall {state : Type} (m : ML.M.t state),
            equiv_query m = None <-> ML.encodes m.
        Proof.
            intros state m. unfold equiv_query.
            rewrite (T.equiv_query_correct (ML.to_dfa m)).
            symmetry. apply ML.encodes_to_dfa.
        Qed.

        Lemma equiv_query_ce : forall {state : Type} (m : ML.M.t state) w,
            equiv_query m = Some w ->
            ML.M.output_string m w <> ML.output_lang w.
        Proof.
            intros state m w Hq. apply (T.equiv_query_ce (ML.to_dfa m) w Hq).
        Qed.
    End MT.

    (* Minimality is inherited *)
    Lemma minimal_to_dfa : forall {state : Type} (m : ML.M.t state),
        ML.minimal m -> L.minimal (ML.to_dfa m).
    Proof.
        intros state m (Henc & Hmin). split.
        - now apply ML.encodes_to_dfa.
        - intros state' d' Henc'.
          apply (Hmin state' (ML.of_dfa d') (proj1 (ML.encodes_of_dfa d') Henc')).
    Qed.
End MooreView.
