From Stdlib Require Export List.
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
    Definition string := list t.

    (** String equality is decidable*)
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

(** Language *)
Module Type L (s : Symbol).
    Import s.
    Parameter member : string -> bool.
End L.
