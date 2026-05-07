open Lstar
open Language
open Specif
open Stdlib

module S = struct
  type t = Zero | One

  let string_of_t = function Zero -> "0" | One -> "1"

  let eq_dec x y =
    if x = y then
      Coq_left
    else
      Coq_right

  let enum = [Zero; One]

  type string = t list

  let string_of_string s = String.concat "" (List.map string_of_t s)

  let str_eq (l1 : string) (l2 : string) =
    if
      List.length l1 = List.length l2
      && List.for_all (fun (x, y) -> x = y) (List.combine l1 l2)
    then
      Coq_left
    else
      Coq_right
end

module L = struct
  let member (s : S.string) : bool =
    match s with
    | [] ->
        true
    | h :: t ->
        snd
          (List.fold_left
             (fun (last, mem) i -> (i, mem && last <> i))
             (h, true) t )
end

module AlternatingTeacher = struct
  module DFA = struct
    type 'state t =
      { transition: 'state -> S.t -> 'state
      ; initial: 'state
      ; accept: 'state -> bool }

    let transition d = d.transition

    let initial d = d.initial

    let accept d = d.accept

    let run d str = List.fold_left d.transition d.initial str

    let accept_string d str = d.accept (run d str)
  end

  let is_alternating (s : S.t list) : bool =
    match s with
    | [] ->
        true
    | h :: t ->
        snd
          (List.fold_left
             (fun (last, ok) curr -> (curr, ok && last <> curr))
             (h, true) t )

  let equiv_query (dfa : 'a DFA.t) : S.string option =
    let rec find_counter_example depth current_strings =
      if depth > 10 then
        None
      else
        match current_strings with
        | [] ->
            None
        | s :: rest ->
            let dfa_acc = DFA.accept_string dfa s in
            let spec_acc = is_alternating s in
            if dfa_acc <> spec_acc then
              Some s
            else
              let next_gen = List.map (fun c -> s @ [c]) [S.Zero; S.One] in
              find_counter_example (depth + 1) (rest @ next_gen)
    in
    find_counter_example 0 [[]]
end

module Lstar = Lstar (S) (L) (AlternatingTeacher)

(** Generate all bit strings of length [n] *)
let rec enumerate (n : int) : S.string list =
  if n <= 0 then [[]]
  else
    let prev = enumerate (n - 1) in
    let prepend c l = List.map (fun s -> [c] @ s) l in
    (prepend S.Zero prev) @ (prepend S.One prev)

let () =
  match
    Lstar.lstar_opt Int.max_int
      { coq_Q=
          (fun x ->
            if x = [] then
              true
            else
              false )
      ; coq_T=
          (fun x ->
            if x = [] then
              true
            else
              false )
      ; clos= (fun _ _ _ -> [])
      ; fin_Q= [[]]
      ; fin_T= [[]] }
  with
  | None ->
      print_endline "No DFA found"
  | Some (Coq_existT (_, d)) ->
      let open S in
      print_endline "DFA found" ;
      print_endline "Test case | Expected | Computed | Correct" ;
      List.iter
        (fun c ->
          let exp, comp = (L.member c, AlternatingTeacher.DFA.accept d c) in
          Printf.printf "[%s]     | %B       %b     %b\n" (S.string_of_string c) exp comp
            (exp = comp) )
        (enumerate 3)
