From Stdlib Require Export List.
Export ListNotations.

Module Type Symbol.
    Parameter t : Type.
    Parameter eq_dec :
        forall (x y : t), {x = y} + {x <> y}.
    Parameter enum : list t.
    Parameter t_enumerable : forall (x : t), In x enum.
    Definition string := list t.
    Fixpoint str_eq (x y : string) {struct x} : {x = y} + {x <> y}.
        destruct x.
        - destruct y. now left.
          now right.
        - destruct y. now right.
          destruct (eq_dec t0 t1).
            + destruct (str_eq x y).
                left. rewrite e, e0. reflexivity.
                right. intro. injection H. intros.
                contradiction.
            + right. intro. injection H. intros.
                contradiction.
    Defined.
End Symbol.

Module Type L (s : Symbol).
    Import s.
    Parameter member : string -> bool.
End L.
