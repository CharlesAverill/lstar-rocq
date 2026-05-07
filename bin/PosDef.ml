open BinNums
open Datatypes

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | Coq_xI p -> Coq_xO (succ p)
  | Coq_xO p -> Coq_xI p
  | Coq_xH -> Coq_xO Coq_xH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> Coq_xO (add_carry p q)
       | Coq_xO q -> Coq_xI (add p q)
       | Coq_xH -> Coq_xO (succ p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> Coq_xI (add p q)
       | Coq_xO q -> Coq_xO (add p q)
       | Coq_xH -> Coq_xI p)
    | Coq_xH ->
      (match y with
       | Coq_xI q -> Coq_xO (succ q)
       | Coq_xO q -> Coq_xI q
       | Coq_xH -> Coq_xO Coq_xH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> Coq_xI (add_carry p q)
       | Coq_xO q -> Coq_xO (add_carry p q)
       | Coq_xH -> Coq_xI (succ p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> Coq_xO (add_carry p q)
       | Coq_xO q -> Coq_xI (add p q)
       | Coq_xH -> Coq_xO (succ p))
    | Coq_xH ->
      (match y with
       | Coq_xI q -> Coq_xI (succ q)
       | Coq_xO q -> Coq_xO (succ q)
       | Coq_xH -> Coq_xI Coq_xH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | Coq_xI p -> Coq_xI (Coq_xO p)
  | Coq_xO p -> Coq_xI (pred_double p)
  | Coq_xH -> Coq_xH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> compare_cont r p q
       | Coq_xO q -> compare_cont Gt p q
       | Coq_xH -> Gt)
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> compare_cont Lt p q
       | Coq_xO q -> compare_cont r p q
       | Coq_xH -> Gt)
    | Coq_xH -> (match y with
                 | Coq_xH -> r
                 | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> Coq_xH
  | S x -> succ (of_succ_nat x)
 end
