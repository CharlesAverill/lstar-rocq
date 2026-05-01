open Datatypes

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Coq_nil -> Coq_nil
| Coq_cons (a, l0) -> Coq_cons ((f a), (map f l0))

(** val firstn : nat -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  match n with
  | O -> Coq_nil
  | S n0 ->
    (match l with
     | Coq_nil -> Coq_nil
     | Coq_cons (a, l0) -> Coq_cons (a, (firstn n0 l0)))

(** val skipn : nat -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  match n with
  | O -> l
  | S n0 ->
    (match l with
     | Coq_nil -> Coq_nil
     | Coq_cons (_, l0) -> skipn n0 l0)
