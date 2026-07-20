From Stdlib Require Export String List.
From lstar Require Export Alphabet.
Export ListNotations.

(** Residuals of an arbitrary language *)
Module Residuals (s : Symbol).
    Import s.

    (** Language membership predicate *)
    Definition lang := str -> bool.

    (** u^{-1}M : the residual of language [M] by word [u] *)
    Definition inverse (M : lang) (u : str) : lang :=
        fun v => M (u ++ v).

    (** Extensional equality of languages *)
    Definition lang_eq (M N : lang) : Prop := forall v, M v = N v.

    (** [r] is a residual of [M] when some word induces it.
        Res(M) = { u^{-1}M | u \in S } *)
    Definition Res (M : lang) (r : lang) : Prop :=
        exists u, lang_eq r (inverse M u).

    (** Every language is its own residual (by the empty word) *)
    Lemma Res_self : forall M, Res M M.
    Proof. intros M. exists []. intro. reflexivity. Qed.
End Residuals.

(** Nondeterministic Finite Automaton *)
Module NFA (s : Symbol).
    Import s.

    Definition step {state : Type}
        (transition : state -> s.t -> list state) (qs : list state) (a : s.t)
        : list state :=
        flat_map (fun q => transition q a) qs.

    Record t (state : Type) : Type := {
        transition : state -> s.t -> list state;
        initial : list state;
        accept : state -> bool;
        states : list state;
        states_complete : forall w q,
            In q (fold_left (step transition) w initial) -> 
            In q states
    }.

    (** Set of states reachable from a given set [qs] after reading [w] *)
    Definition run_from {state : Type} (n : t state) (qs : list state) (w : str)
        : list state :=
        fold_left (step n.(transition state)) w qs.

    Definition run {state : Type} (n : t state) (w : str) : list state :=
        run_from n n.(initial state) w.

    Definition accept_string {state : Type} (n : t state) (w : str) : bool :=
        existsb n.(accept state) (run n w).

    (** Language recognized starting from a single state [q] *)
    Definition L_state {state : Type} (n : t state) (q : state) : str -> bool :=
        fun w => existsb n.(accept state) (run_from n [q] w).

    (** Language recognized by the whole automaton *)
    Definition L_aut {state : Type} := @accept_string state.

    Section Dedup.
        Context {state : Type}.
        Variable eq_dec : forall x y : state, {x = y} + {x <> y}.

        Definition step_dedup (transition : state -> s.t -> list state)
            (qs : list state) (a : s.t) : list state :=
            nodup eq_dec (step transition qs a).

        Definition run_from_dedup (n : t state) (qs : list state) (w : str)
            : list state :=
            fold_left (step_dedup n.(transition state)) w qs.

        Definition run_dedup (n : t state) (w : str) : list state :=
            run_from_dedup n (n.(initial state)) w.

        Definition accept_string_dedup (n : t state) (w : str) : bool :=
            existsb n.(accept state) (run_dedup n w).

        (* Deduplication changes only the multiplicity of the states reached,
           never the set, so [run_from_dedup] and [run_from] agree on
           membership at every step -- given only that their starting frontiers
           agree on membership, not that they are the same list. *)
        Lemma run_from_dedup_set : forall (n : t state) w qs qs',
            (forall q, In q qs <-> In q qs') ->
            forall q, In q (run_from_dedup n qs w) <-> In q (run_from n qs' w).
        Proof.
            intros n w. induction w as [| a w IH]; intros qs qs' Hqs q; simpl.
                exact (Hqs q).
            apply IH. intro x. unfold step_dedup, step. rewrite nodup_In.
            split; intro Hx; apply in_flat_map in Hx; destruct Hx as (y & Hy & Hxy);
              apply in_flat_map; exists y; split; try exact Hxy; now apply Hqs.
        Qed.

        Lemma accept_string_dedup_correct : forall (n : t state) w,
            accept_string_dedup n w = accept_string n w.
        Proof.
            intros n w. unfold accept_string_dedup, accept_string, run_dedup, run.
            apply Bool.eq_true_iff_eq. split; intro Hex;
              apply existsb_exists in Hex; destruct Hex as (q & Hq & Hacc);
              apply existsb_exists; exists q; split; try exact Hacc.
            - exact (proj1 (run_from_dedup_set n w _ _
                              (fun x => conj (fun H => H) (fun H => H)) q) Hq).
            - exact (proj2 (run_from_dedup_set n w _ _
                              (fun x => conj (fun H => H) (fun H => H)) q) Hq).
        Qed.
    End Dedup.

    (** String equality is decidable*)
    Fixpoint str_eq (x y : str) {struct x} : {x = y} + {x <> y}.
        destruct x, y.
            now left.
            now right.
            now right.
        destruct (eq_dec t0 t1), (str_eq x y); subst; clear str_eq.
            now left.
        all: right; intro H; inversion H; subst; intuition.
    Defined.
End NFA.

(** Residual Finite-State Automaton *)
Module RFSA (s : Symbol).
    Module N := NFA s.
    Module Res := Residuals s.

    Record t (state : Type) : Type := {
        nfa : N.t state;
        (** Every state's per-state language is a residual of L(R) *)
        states_are_residuals : forall q,
            In q (N.states state nfa) ->
            Res.Res (N.L_aut nfa) (N.L_state nfa q)
    }.
End RFSA.

(* Union of sets *)
Definition union {T} (rs : list (T -> bool)) : T -> bool :=
    fun v => existsb (fun r => r v) rs.

(** Residual Language *)
Module Type ResidualLanguage (s : Symbol).
    Import s.
    Module R := RFSA s.
    Module Res := R.Res.
    Module N := R.N.
    Include Language s.

    (** The residuals of the target language are residuals of [member] *)
    Definition residual (r : Res.lang) : Prop := Res.Res member r.

    (** A residual is _composed_ when it is a union of residuals *)
    Definition composed (r : Res.lang) : Prop :=
        residual r /\
        exists rs,
            (forall r', In r' rs -> residual r' /\ ~ Res.lang_eq r' r) /\
            Res.lang_eq r (union rs).

    (** Otherwise it is _prime_ *)
    Definition prime (r : Res.lang) : Prop :=
        residual r /\ ~ composed r.

    (** Whether an NFA encodes the target language L *)
    Definition encodes {state : Type} (nfa : N.t state) : Prop :=
        forall (w : str),
            member w = true <-> N.accept_string nfa w = true.

    (** An RFSA is _canonical_ when it encodes L and its states denote exactly
        the prime residuals of L *)
    Definition canonical {state : Type} (rfsa : R.t state) : Prop :=
        encodes rfsa.(R.nfa _) /\
        forall q, In q (N.states state (R.nfa state rfsa)) ->
            prime (N.L_state (R.nfa state rfsa) q).

    (** RFSA state minimality *)
    Definition minimal {state : Type} (rfsa : R.t state) : Prop :=
        encodes rfsa.(R.nfa _) /\
        forall (state' : Type) (rfsa' : R.t state'),
            encodes rfsa'.(R.nfa _) -> 
            List.length (N.states state rfsa.(R.nfa _)) <= List.length (N.states state' rfsa'.(R.nfa _)).

    (** For every regular language there is a unique minimal canonical RFSA *)
    Parameter num_states_in_canonical : nat.
    Parameter exists_rfsa : exists state (r : R.t state),
        canonical r /\ minimal r /\
        List.length (N.states state (R.nfa state r)) <= num_states_in_canonical.

    (** The target language is regular, so it has finitely many residual languages.*)
    Parameter num_residuals : nat.
    Parameter residuals_bounded : forall (rs : list Res.lang),
        (forall r, In r rs -> residual r) ->
        (forall i j, i < List.length rs -> j < List.length rs ->
            Res.lang_eq (List.nth i rs (fun _ => false)) (List.nth j rs (fun _ => false)) ->
            i = j) ->
        List.length rs <= num_residuals.
End ResidualLanguage.
