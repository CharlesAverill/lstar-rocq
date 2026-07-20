open Lstar
open DFA
open NFA
open Specif
open Teacher
open Stdlib

(** L_n = Sigma* a Sigma^n over Sigma = {a, b}: the words carrying an [a] in the
    (n+1)-th position from the right. *)

let n = 2

(** Alphabet *)
module S = struct
  type t = A | B

  let string_of_t = function A -> "a" | B -> "b"

  let t_of_string : string -> (t, string) Datatypes.result = function
    | "a" ->
        Ok A
    | "b" ->
        Ok B
    | _ ->
        Error "t_of_string"

  let eq_dec x y = x = y

  let enum = [A; B]

  type str = t list

  let string_of_str s = String.concat "" (List.map string_of_t s)
end

(** Language membership: the (n+1)-th symbol from the right is [a]. Words
    shorter than n+1 have no such position and are rejected. *)
let member (s : S.str) : bool =
  match List.nth_opt (List.rev s) n with Some S.A -> true | _ -> false

let counterexample (accepts : S.str -> bool) : S.str option =
  let rec bfs depth queue =
    if depth >= 256 then
      None
    else
      match queue with
      | [] ->
          None
      | s :: rest ->
          if accepts s <> member s then
            Some s
          else
            bfs (depth + 1) (rest @ List.map (fun c -> s @ [c]) S.enum)
  in
  bfs 0 [[]]

(** Teacher for the deterministic learners *)
module DTeacher : DFATEACHER with module S = S = struct
  module S = S
  module D = DFA (S)

  let member = member

  let equiv_query (dfa : 'a D.t) : S.str option =
    counterexample (D.accept_string dfa)

  let fuel : int = Int.max_int
end

(** Teacher for the nondeterministic learner *)
module NTeacher : NFATEACHER with module S = S = struct
  module S = S
  module R = RFSA (S)

  let member = member

  let equiv_query (nfa : 'a R.N.t) : S.str option =
    counterexample (R.N.accept_string nfa)

  let fuel : int = Int.max_int
end

(** L* implementation *)
module Lstar = LstarLearner (DTeacher)

(** NL* implementation *)
module NLstar = NLstarLearner (NTeacher)

module DP = DFAPrinter (DTeacher)
module NP = NFAPrinter (NTeacher)

(** Generate all strings of length [k] *)
let rec enumerate (k : int) : S.str list =
  if k <= 0 then
    [[]]
  else
    let prev = enumerate (k - 1) in
    List.concat_map (fun c -> List.map (fun s -> c :: s) prev) S.enum

(** Run a hypothesis on test cases and pretty-print the results *)
let print_table (accepts : S.str -> bool) (k : int) =
  let strings = enumerate k in
  let col_w = max 10 (k + 2) in
  let header =
    Printf.sprintf "%-*s  %-8s  %-8s  %-8s" col_w "Input" "Expected" "Got"
      "Correct"
  in
  print_endline header ;
  List.iter
    (fun (c : S.str) ->
      let exp = member c in
      let comp = accepts c in
      Printf.printf "%-*s  %-8b  %-8b  %s\n" col_w
        (Printf.sprintf "[%s]" (S.string_of_str c))
        exp comp
        ( if exp = comp then
            "Y"
          else
            "N" ) )
    strings ;
  let correct =
    List.length (List.filter (fun c -> member c = accepts c) strings)
  in
  Printf.printf "Accuracy: %d/%d\n" correct (List.length strings)

let report_dfa name dfa k =
  Printf.printf "\n=== %s ===\n" name ;
  print_endline "DFA found" ;
  DP.print_dfa dfa ;
  Printf.printf "DOT file at %s\n" (DP.to_dot ~name:(name ^ "_suffix") dfa) ;
  print_table (DTeacher.D.accept_string dfa) k

let report_nfa name nfa k =
  Printf.printf "\n=== %s ===\n" name ;
  print_endline "RFSA found" ;
  NP.print_nfa nfa ;
  Printf.printf "DOT file at %s\n" (NP.to_dot ~name:(name ^ "_suffix") nfa) ;
  print_table (NTeacher.R.N.accept_string nfa) (3 * k)

let () =
  let dfa = Lstar.lstar () in
  let nfa = NLstar.nfa () in
  report_dfa "L*" dfa (n + 2) ;
  report_nfa "NL*" nfa (n + 2) ;
  let dfa_states, _ = DP.discover dfa in
  let nfa_states, _ = NP.discover nfa in
  Printf.printf "\n=== succinctness ===\n" ;
  Printf.printf "L_%d = Sigma* a Sigma^%d over {a, b}\n" n n ;
  Printf.printf "  minimal DFA     %d states (2^%d = %d)\n"
    (List.length dfa_states) (n + 1)
    (1 lsl (n + 1)) ;
  Printf.printf "  canonical RFSA  %d states (%d + 2 = %d)\n"
    (List.length nfa_states) n (n + 2)
