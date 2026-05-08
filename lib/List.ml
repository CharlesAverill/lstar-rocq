
(** val list_prod : 'a1 list -> 'a2 list -> ('a1*'a2) list **)

let list_prod l =
  let rec list_prod0 l0 l' =
    match l0 with
    | [] -> []
    | x::t -> (@) (Stdlib.List.map (fun y -> x,y) l') (list_prod0 t l')
  in list_prod0 l
