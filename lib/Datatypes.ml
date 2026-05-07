
type coq_Empty_set = |

type ('a, 'b) sum =
| Coq_inl of 'a
| Coq_inr of 'b

type comparison =
| Eq
| Lt
| Gt

(** val coq_CompOpp : comparison -> comparison **)

let coq_CompOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt
