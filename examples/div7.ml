open Lstar
open Language
open Specif
open Stdlib

(** Alphabet: decimal digits *)
module S = struct
  type t = D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8 | D9

  let all = [D0; D1; D2; D3; D4; D5; D6; D7; D8; D9]

  let to_int = function
    | D0 ->
        0
    | D1 ->
        1
    | D2 ->
        2
    | D3 ->
        3
    | D4 ->
        4
    | D5 ->
        5
    | D6 ->
        6
    | D7 ->
        7
    | D8 ->
        8
    | D9 ->
        9

  let string_of_t = function
    | D0 ->
        "0"
    | D1 ->
        "1"
    | D2 ->
        "2"
    | D3 ->
        "3"
    | D4 ->
        "4"
    | D5 ->
        "5"
    | D6 ->
        "6"
    | D7 ->
        "7"
    | D8 ->
        "8"
    | D9 ->
        "9"

  let eq_dec x y =
    if x = y then
      Coq_left
    else
      Coq_right

  let enum = all

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

(** Language: decimal strings (with leading zeros) whose numeric value is
    divisible by 7. The minimal DFA has exactly 7 states - one per residue
    class mod 7. The transition on reading digit d from state r is:
        r' = (r * 10 + d) mod 7
    which is the standard streaming divisibility DFA. *)
module L = struct
  let member (s : S.string) : bool =
    match s with
    | [] ->
        false
    | _ ->
        let value = List.fold_left (fun acc d -> (acc * 10) + S.to_int d) 0 s in
        value mod 7 = 0
end

module Mod7Teacher = struct
  module DFA = struct
    type 'state t =
      { transition: 'state -> S.t -> 'state
      ; initial: 'state
      ; accept: 'state -> bool }

    let transition d = d.transition

    let initial d = d.initial

    let accept d = d.accept

    let run d str = List.fold_left d.transition d.initial str

    let accept_string d s = d.accept (run d s)
  end

  let equiv_query (dfa : 'a DFA.t) : S.string option =
    let rec bfs depth queue =
      if depth >= 8192 then
        None
      else
        match queue with
        | [] ->
            None
        | s :: rest ->
            if DFA.accept_string dfa s <> L.member s then
              Some s
            else
              let children = List.map (fun c -> s @ [c]) S.enum in
              bfs (depth + 1) (rest @ children)
    in
    bfs 0 [[]]
end

module Lstar = Lstar (S) (L) (Mod7Teacher)

(** All digit strings of exactly length [n] *)
let rec enumerate_exact n =
  if n = 0 then
    [[]]
  else
    let prev = enumerate_exact (n - 1) in
    List.concat_map (fun d -> List.map (fun s -> d :: s) prev) S.enum

(** Collect all multiples of 7 up to 3 digits for display *)
let interesting_cases =
  (* hand-pick: 0, 7, 14, 21, 42, 49, 77, 98, 105, 119, 126 *)
  let nums = [0; 7; 14; 21; 35; 42; 49; 56; 63; 70; 77; 84; 91; 98] in
  List.map
    (fun n ->
      let s = string_of_int n in
      String.to_seq s
      |> Seq.map (fun c ->
          match c with
          | '0' ->
              S.D0
          | '1' ->
              S.D1
          | '2' ->
              S.D2
          | '3' ->
              S.D3
          | '4' ->
              S.D4
          | '5' ->
              S.D5
          | '6' ->
              S.D6
          | '7' ->
              S.D7
          | '8' ->
              S.D8
          | _ ->
              S.D9 )
      |> List.of_seq )
    nums

let print_results dfa =
  let multiples = interesting_cases @ [[D0; D7]] in
  let non_multiples =
    List.filteri
      (fun i _ -> i < 8)
      (List.filter (fun s -> not (L.member s)) (enumerate_exact 2))
  in
  let cases = multiples @ non_multiples in
  let col_w = 12 in
  let header =
    Printf.sprintf "%-*s  %-8s  %-8s  %-8s" col_w "Input" "Expected" "Got"
      "Correct"
  in
  print_endline header ;
  List.iter
    (fun c ->
      let exp = L.member c in
      let comp = Mod7Teacher.DFA.accept_string dfa c in
      Printf.printf "%-*s  %-8b  %-8b  %s\n" col_w (S.string_of_string c) exp
        comp
        ( if exp = comp then
            "Y"
          else
            "N" ) )
    cases ;
  let correct =
    List.length
      (List.filter
         (fun c -> L.member c = Mod7Teacher.DFA.accept_string dfa c)
         cases )
  in
  Printf.printf "Accuracy: %d/%d\n" correct (List.length cases)

let () =
  match
    Lstar.lstar_opt Int.max_int
      { coq_Q= (fun x -> x = [])
      ; coq_T= (fun x -> x = [])
      ; clos= (fun _ _ _ -> [])
      ; fin_Q= [[]]
      ; fin_T= [[]] }
  with
  | None ->
      print_endline "No DFA found"
  | Some (Coq_existT (_, d)) ->
      print_endline "DFA found" ; print_results d
