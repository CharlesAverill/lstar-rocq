open Lstar
open DFA
open Specif
open Teacher
open Stdlib

module S = struct
  type t = Zero | One

  let string_of_t = function Zero -> "0" | One -> "1"

  let eq_dec x y = x = y

  let enum = [Zero; One]

  type str = t list

  let string_of_str s = String.concat "" (List.map string_of_t s)

  let str_eq (l1 : str) (l2 : str) =
    List.length l1 = List.length l2
    && List.for_all (fun (x, y) -> x = y) (List.combine l1 l2)
end

(** Language: strings over {0,1} where the number of 1s is divisible by 3.
    The minimal DFA has exactly 3 states (one per residue class mod 3),
    so L* must discover a nontrivial 3-state machine. *)
module Teacher : TEACHER with module S = S = struct
  module S = S
  module D = DFA (S)

  let member (s : S.str) : bool =
    let count =
      List.fold_left
        (fun acc c ->
          if c = S.One then
            acc + 1
          else
            acc )
        0 s
    in
    count mod 3 = 0

  let equiv_query (dfa : 'a D.t) : S.str option =
    let rec bfs depth queue =
      if depth >= 4096 then
        None
      else
        match queue with
        | [] ->
            None
        | s :: rest ->
            if D.accept_string dfa s <> member s then
              Some s
            else
              bfs (depth + 1)
                (rest @ List.map (fun c -> s @ [c]) [S.Zero; S.One])
    in
    bfs 0 [[]]

  let fuel : int = Int.max_int
end

module Lstar = LstarLearner (Teacher)

(** Kearns-Vazirani (discrimination-tree) implementation *)
module KV = KVLearner (Teacher)

let rec enumerate n =
  if n <= 0 then
    [[]]
  else
    let prev = enumerate (n - 1) in
    List.map (fun s -> S.Zero :: s) prev @ List.map (fun s -> S.One :: s) prev

let print_results name dfa n =
  Printf.printf "\n=== %s ===\n" name ;
  Lstar.print_dfa dfa ;
  print_endline "DFA found" ;
  let strings = enumerate n in
  let col_w = max 10 (n + 2) in
  let header =
    Printf.sprintf "%-*s  %-8s  %-8s  %-8s" col_w "Input" "Expected" "Got"
      "Correct"
  in
  print_endline header ;
  List.iter
    (fun (c : S.str) ->
      let exp = Teacher.member c in
      let comp = Teacher.D.accept_string dfa c in
      Printf.printf "%-*s  %-8b  %-8b  %s\n" col_w
        (Printf.sprintf "[%s]" (S.string_of_str c))
        exp comp
        ( if exp = comp then
            "Y"
          else
            "N" ) )
    strings ;
  let correct =
    List.length
      (List.filter
         (fun (c : S.str) -> Teacher.member c = Teacher.D.accept_string dfa c)
         strings )
  in
  Printf.printf "Accuracy: %d/%d\n" correct (List.length strings)

let () =
  (match Lstar.lstar () with Coq_existT (_, d) -> print_results "L*" d 4) ;
  match KV.kv () with Coq_existT (_, d) -> print_results "KV" d 4
