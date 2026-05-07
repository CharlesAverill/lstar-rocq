open Lstar
open Language
open Specif
open Stdlib

module S = struct
  type t = Zero | One
  let string_of_t = function Zero -> "0" | One -> "1"
  let eq_dec x y = if x = y then Coq_left else Coq_right
  let enum = [Zero; One]
  type string = t list
  let string_of_string s = String.concat "" (List.map string_of_t s)
  let str_eq (l1 : string) (l2 : string) =
    if List.length l1 = List.length l2
       && List.for_all (fun (x, y) -> x = y) (List.combine l1 l2)
    then Coq_left else Coq_right
end

(** Language: strings over {0,1} where the number of 1s is divisible by 3.
    The minimal DFA has exactly 3 states (one per residue class mod 3),
    so L* must discover a nontrivial 3-state machine. *)
module L = struct
  let member (s : S.string) : bool =
    let count = List.fold_left (fun acc c -> if c = S.One then acc + 1 else acc) 0 s in
    count mod 3 = 0
end

module Mod3Teacher = struct
  module DFA = struct
    type 'state t =
      { transition : 'state -> S.t -> 'state
      ; initial    : 'state
      ; accept     : 'state -> bool }
    let transition d = d.transition
    let initial    d = d.initial
    let accept     d = d.accept
    let run d str         = List.fold_left d.transition d.initial str
    let accept_string d s = d.accept (run d s)
  end

  let equiv_query (dfa : 'a DFA.t) : S.string option =
    let rec bfs depth queue =
      if depth >= 4096 then None
      else match queue with
        | [] -> None
        | s :: rest ->
          if DFA.accept_string dfa s <> L.member s then Some s
          else bfs (depth + 1) (rest @ List.map (fun c -> s @ [c]) [S.Zero; S.One])
    in
    bfs 0 [[]]
end

module Lstar = Lstar (S) (L) (Mod3Teacher)

let rec enumerate n =
  if n <= 0 then [[]]
  else
    let prev = enumerate (n - 1) in
    List.map (fun s -> S.Zero :: s) prev @
    List.map (fun s -> S.One  :: s) prev

let print_results dfa n =
  let strings = enumerate n in
  let col_w = max 10 (n + 2) in
  let header = Printf.sprintf "%-*s  %-8s  %-8s  %-8s"
    col_w "Input" "Expected" "Got" "Correct" in
  print_endline header;
  List.iter (fun c ->
    let exp  = L.member c in
    let comp = Mod3Teacher.DFA.accept_string dfa c in
    Printf.printf "%-*s  %-8b  %-8b  %s\n"
      col_w (Printf.sprintf "[%s]" (S.string_of_string c))
      exp comp (if exp = comp then "Y" else "N")
  ) strings;
  let correct = List.length (List.filter
    (fun c -> L.member c = Mod3Teacher.DFA.accept_string dfa c) strings) in
  Printf.printf "Accuracy: %d/%d\n" correct (List.length strings)

let () =
  match
    Lstar.lstar_opt Int.max_int
      { coq_Q  = (fun x -> x = [])
      ; coq_T  = (fun x -> x = [])
      ; clos   = (fun _ _ _ -> [])
      ; fin_Q  = [[]]
      ; fin_T  = [[]] }
  with
  | None -> print_endline "No DFA found"
  | Some (Coq_existT (_, d)) ->
    print_endline "DFA found";
    print_results d 4
