open Datatypes
open ListDef

(** val nth_error : 'a1 list -> nat -> 'a1 option **)

let rec nth_error l = function
| O -> (match l with
        | Coq_nil -> None
        | Coq_cons (x, _) -> Some x)
| S n0 -> (match l with
           | Coq_nil -> None
           | Coq_cons (_, l') -> nth_error l' n0)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| Coq_nil -> Coq_false
| Coq_cons (a, l0) ->
  (match f a with
   | Coq_true -> Coq_true
   | Coq_false -> existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| Coq_nil -> Coq_true
| Coq_cons (a, l0) ->
  (match f a with
   | Coq_true -> forallb f l0
   | Coq_false -> Coq_false)

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| Coq_nil -> None
| Coq_cons (x, tl) ->
  (match f x with
   | Coq_true -> Some x
   | Coq_false -> find f tl)

(** val list_prod : 'a1 list -> 'a2 list -> ('a1, 'a2) prod list **)

let rec list_prod l l' =
  match l with
  | Coq_nil -> Coq_nil
  | Coq_cons (x, t) ->
    app (map (fun y -> Coq_pair (x, y)) l') (list_prod t l')
