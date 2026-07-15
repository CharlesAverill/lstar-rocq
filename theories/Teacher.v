From lstar Require Import automata.DFA automata.NFA automata.Moore automata.Mealy.

Module Type DFATeacher (s : Symbol) (L : RegularLanguage s).
    Import s L.

    (** The teacher answers equivalence queries: whether the given
        DFA encodes L or not *)
    Parameter equiv_query : 
        forall {state},
        D.t state -> option str.
    (** If the equivalence query returns [None], the DFA encodes L *)
    Parameter equiv_query_correct : forall {state} (d : D.t state),
        equiv_query d = None <-> encodes d.
    (** If the equivalence query returns [Some x], the DFA does not
        encode L, and [x] is a counter-example on which the DFA
        mis-predicts *)
    Parameter equiv_query_ce : forall {state} (d : D.t state) w,
        equiv_query d = Some w ->
        D.accept_string d w <> member w.
End DFATeacher.

Module Type RFSATeacher (s : Symbol) (L : ResidualLanguage s).
    Import s L.

    (** The teacher answers equivalence queries: whether the given
        RFSA encodes L or not *)
    Parameter equiv_query : 
        forall {state},
        N.t state -> option str.
    (** If the equivalence query returns [None], the RFSA encodes L *)
    Parameter equiv_query_correct : forall {state : Type} (n : N.t state),
        equiv_query n = None <-> encodes n.
    (** If the equivalence query returns [Some x], the RFSA does not
        encode L, and [x] is a counter-example on which the RFSA
        mis-predicts *)
    Parameter equiv_query_ce : forall {state : Type} (nfa : N.t state) w,
        equiv_query nfa = Some w ->
        N.accept_string nfa w <> member w.
End RFSATeacher.

(** Teacher for Moore-machine learning. *)
Module Type MooreTeacher (s : Symbol) (O : Output) (L : MooreLanguage s O).
    Import s O L.

    (** The teacher answers equivalence queries: whether the given Moore
        machine encodes the target output function or not. *)
    Parameter equiv_query :
        forall {state}, M.t state -> option str.
    (** If [equiv_query] returns [None], the machine encodes L. *)
    Parameter equiv_query_correct : forall {state} (m : M.t state),
        equiv_query m = None <-> encodes m.
    (** If [equiv_query] returns [Some w], the machine mis-predicts on [w]. *)
    Parameter equiv_query_ce : forall {state} (m : M.t state) w,
        equiv_query m = Some w ->
        M.output_string m w <> output_lang w.
End MooreTeacher.

(** Teacher for Mealy-machine learning. *)
Module Type MealyTeacher (s : Symbol) (O : Output) (L : MealyLanguage s O).
    Import s O L.

    (** The teacher answers equivalence queries: whether the given Mealy
        machine reproduces the target's observations on every suffix. *)
    Parameter equiv_query :
        forall {state}, M.t state -> option str.
    (** If [equiv_query] returns [None], the machine encodes L. *)
    Parameter equiv_query_correct : forall {state} (m : M.t state),
        equiv_query m = None <-> encodes m.
    (** If [equiv_query] returns [Some t], the machine mis-predicts on the
        suffix [t]: its observation from the initial state differs from
        the target's. *)
    Parameter equiv_query_ce : forall {state} (m : M.t state) t,
        equiv_query m = Some t ->
        M.mobs m m.(M.initial _) t <> M.tobs output_lang [] t.
End MealyTeacher.
