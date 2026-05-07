
(** val existsb_exists_set : ('a1 -> bool) -> 'a1 list -> 'a1 **)

let rec existsb_exists_set f = function
| [] -> assert false (* absurd case *)
| y::l0 -> let b = f y in if b then y else existsb_exists_set f l0
