(** val list_prod : 'a1 list -> 'a2 list -> ('a1*'a2) list **)

let rec list_prod l l' =
  match l with
  | [] ->
      []
  | x :: t ->
      Stdlib.List.map (fun y -> (x, y)) l' @ list_prod t l'
