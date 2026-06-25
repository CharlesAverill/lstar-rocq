From lstar Require Import Automata.

Module Type DFATeacher (s : Symbol) (L : RegularLanguage s).
    Import s L.

    (** The teacher answers equivalence queries: whether the given
        DFA encodes L or not *)
    Parameter equiv_query : 
        forall (state : Type),
        D.t state -> option str.
    (** If the equivalence query returns [None], the DFA encodes L *)
    Parameter equiv_query_correct : forall (state : Type) d,
        equiv_query state d = None <-> encodes d.
    (** If the equivalence query returns [Some x], the DFA does not
        encode L, and [x] is a counter-example on which the DFA
        mis-predicts *)
    Parameter equiv_query_ce : forall (state : Type) d w,
        equiv_query state d = Some w ->
        D.accept_string d w <> member w.
End DFATeacher.

Module Type RFSATeacher (s : Symbol) (L : ResidualLanguage s).
    Import s L.

    (** The teacher answers equivalence queries: whether the given
        RFSA encodes L or not *)
    Parameter equiv_query : 
        forall (state : Type),
        R.t state -> option str.
    (** If the equivalence query returns [None], the RFSA encodes L *)
    Parameter equiv_query_correct : forall (state : Type) r,
        equiv_query state r = None <-> encodes r.
    (** If the equivalence query returns [Some x], the RFSA does not
        encode L, and [x] is a counter-example on which the RFSA
        mis-predicts *)
    Parameter equiv_query_ce : forall (state : Type) (r : R.t state) w,
        equiv_query state r = Some w ->
        N.accept_string r.(R.nfa state) w <> member w.
End RFSATeacher.
