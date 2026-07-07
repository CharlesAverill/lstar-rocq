From Stdlib Require Export List String.
Export ListNotations.

(** Symbol type *)
Module Type Symbol.
    (** Alphabet *)
    Parameter t : Type.

    (** Symbol equality is decidable *)
    Parameter eq_dec :
        forall (x y : t), {x = y} + {x <> y}.

    (** Alphabet is finite *)
    Parameter enum : list t.
    Parameter t_enumerable : forall (x : t), In x enum.

    (** List of symbols *)
    Definition str := list t.

    (** For debugging *)
    Parameter string_of_t : t -> String.string.
End Symbol.

(** Deterministic Finite Automaton *)
Module DFA (s : Symbol).
    Import s.

    (** DFA type *)
    Record t (state : Type) : Type := {
        transition : state -> s.t -> state;
        initial : state;
        accept : state -> bool;
        states : list state;
        states_complete : forall w, In (fold_left transition w initial) (states)
    }.

    (** Run a DFA on a string and get the resulting state *)
    Definition run {state : Type} (dfa : t state) (s : str) : state :=
        fold_left dfa.(transition state) s dfa.(initial state).

    (** Check whether a DFA reaches an accepting state after processing a string *)
    Definition accept_string {state : Type} (dfa : t state) (s : str) : bool :=
        dfa.(accept state) (run dfa s).
    
    (** Every reachable state is listed in [states] *)
    Lemma run_in_states : forall {state : Type} (d : t state) (w : str),
        In (run d w) (states state d).
    Proof.
        intros state d w. unfold run. apply (states_complete state d).
    Qed.

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
End DFA.

(** Arbitrary Language *)
Module Type Language (s : Symbol).
    Import s.

    (** Language membership *)
    Parameter member : str -> bool.
End Language.

(** Regular Language *)
Module Type RegularLanguage (s : Symbol).
    Import s.
    Module D := DFA s.
    Include Language s.

    (** Whether a DFA encodes the language L *)
    Definition encodes {state : Type} (dfa : D.t state) : Prop :=
        forall (s : str),
            member s = true <-> D.accept_string dfa s = true.

    (** DFA state minimality *)
    Definition minimal {state : Type} (dfa : D.t state) : Prop :=
        encodes dfa /\
        forall (state' : Type) (dfa' : D.t state'),
            encodes dfa' -> 
            List.length (D.states state dfa) <= List.length (D.states state' dfa').

    (** There exists a minimal DFA with number of states [num_states_in_minimal] *)
    Parameter num_states_in_minimal : nat.
    Parameter exists_dfa : exists state (d: D.t state), 
        minimal d /\ List.length (D.states state d) <= num_states_in_minimal.
End RegularLanguage.

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
            In q (fold_left (step transition) w initial) -> In q states
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

(** Residual Language *)
Module Type ResidualLanguage (s : Symbol).
    Import s.
    Module R := RFSA s.
    Module Res := R.Res.
    Module N := R.N.
    Include Language s.

    (** The residuals of the target language are residuals of [member] *)
    Definition residual (r : Res.lang) : Prop := Res.Res member r.

    (** Union of a list of residuals, pointwise *)
    Definition union (rs : list Res.lang) : Res.lang :=
        fun v => existsb (fun r => r v) rs.

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
End ResidualLanguage.
