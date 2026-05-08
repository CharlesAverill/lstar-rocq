open Specif

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val nth_error_split_sig :
    'a1 list -> int -> 'a1 -> ('a1 list, 'a1 list) sigT **)

let nth_error_split_sig l n _ =
  let rec f n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ l0 ->
      match l0 with
      | [] -> (fun _ -> assert false (* absurd case *))
      | _::l1 -> (fun _ -> Coq_existT ([], l1)))
      (fun n1 l0 ->
      match l0 with
      | [] -> (fun _ -> assert false (* absurd case *))
      | a::l1 ->
        (fun _ ->
          let Coq_existT (x, s) = f n1 l1 __ in Coq_existT ((a::x), s)))
      n0
  in f n l __

(** val existsb_exists_set : ('a1 -> bool) -> 'a1 list -> 'a1 **)

let existsb_exists_set f l =
  let rec f0 = function
  | [] -> (fun _ -> assert false (* absurd case *))
  | y::l1 ->
    (fun _ -> (if f y then (fun _ _ -> y) else (fun _ _ -> f0 l1 __)) __ __)
  in f0 l __
