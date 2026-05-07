open Lstar
open Language
open Specif
open Stdlib

module S = struct
  type t = Zero | One

  let eq_dec x y =
    if x = y then
      Coq_left
    else
      Coq_right

  let enum = [Zero; One]

  type string = t list

  let str_eq (l1 : string) (l2 : string) =
    if List.for_all (fun (x, y) -> x = y) (List.combine l1 l2) then
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
    type 'state t = {
      transition : 'state -> S.t -> 'state;
      initial : 'state;
      accept : 'state -> bool;
    }

    let transition d = d.transition
    let initial d = d.initial
    let accept d = d.accept

    let run d str =
      List.fold_left d.transition d.initial str

    let accept_string d str =
      d.accept (run d str)
  end

  let is_alternating (s : S.t list) : bool =
    match s with
    | [] -> true
    | h :: t ->
        snd
          (List.fold_left
             (fun (last, ok) curr -> (curr, ok && last <> curr))
             (h, true)
             t)

  let equiv_query (dfa : 'a DFA.t) : S.string option =
    let rec find_counter_example depth current_strings =
      if depth > 10 then None
      else
        match current_strings with
        | [] -> None
        | s :: rest ->
            let dfa_acc = DFA.accept_string dfa s in
            let spec_acc = is_alternating s in
            if dfa_acc <> spec_acc then Some s
            else
              let next_gen =
                List.map (fun c -> s @ [c]) [S.Zero; S.One]
              in
              find_counter_example (depth + 1) (rest @ next_gen)
    in
    find_counter_example 0 [[]]
end

module Lstar = Lstar(S)(L)(AlternatingTeacher)
