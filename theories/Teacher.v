From lstar Require Import DFA.

Module Type Teacher (s : Symbol) (L : RegularLanguage s).
    Import s L.

    (** The teacher answers equivalence queries: whether the given
        DFA encodes L or not *)
    Parameter equiv_query : 
        forall (state : Type),
        D.t state -> option string.
    (** If the equivalence query returns [None], the DFA encodes L *)
    Parameter equiv_query_correct : forall (state : Type) d,
        equiv_query state d = None <-> encodes d.
    (** If the equivalence query returns [Some x], the DFA does not
        encode L, and [x] is a counter-example on which the DFA
        mis-predicts *)
    Parameter equiv_query_ce : forall (state : Type) d w,
        equiv_query state d = Some w ->
        D.accept_string d w <> member w.
End Teacher.
