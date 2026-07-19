From Stdlib Require Export List.
From Stdlib Require Import String.
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

    (** Serialization *)
    Parameter string_of_t : t -> String.string.
    Parameter t_of_string : String.string -> result t string.
End Symbol.

(** A finite output alphabet *)
Module Type Output.
    Parameter t : Type.
    Parameter eq_dec : forall (x y : t), {x = y} + {x <> y}.
    Parameter enum : list t.
    Parameter t_enumerable : forall (x : t), In x enum.
    (* Parameter enum_nodup : NoDup enum. *)
End Output.

(** Arbitrary Language *)
Module Type Language (s : Symbol).
    Import s.

    (** Language membership *)
    Parameter member : str -> bool.
End Language.
