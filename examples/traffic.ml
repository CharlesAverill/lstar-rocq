(* European-style 4-phase traffic light *)

open Lstar
open Moore
open Specif
open Teacher
open Stdlib

(** Input alphabet: a clock [Tick] and a [Reset] line *)
module S = struct
  type t = Tick | Reset

  let string_of_t = function Tick -> "t" | Reset -> "r"

  let t_of_string : string -> (t, string) Datatypes.result = function
    | "t" ->
        Ok Tick
    | "r" ->
        Ok Reset
    | _ ->
        Error "t_of_string"

  let eq_dec x y = x = y

  let enum = [Tick; Reset]

  type str = t list

  let string_of_str s = String.concat "" (List.map string_of_t s)
end

(** Output alphabet: the light state *)
module O = struct
  type t = Red | Green | Yellow | RedYellow

  let string_of_t = function
    | Red ->
        "RED"
    | Green ->
        "GREEN"
    | Yellow ->
        "YELLOW"
    | RedYellow ->
        "RED+YELLOW"

  let t_of_string : string -> (t, string) Datatypes.result = function
    | "RED" ->
        Ok Red
    | "GREEN" ->
        Ok Green
    | "YELLOW" ->
        Ok Yellow
    | "RED+YELLOW" ->
        Ok RedYellow
    | _ ->
        Error "t_of_string"

  let eq_dec x y = x = y

  type str = t list

  let enum = [Red; Green; Yellow; RedYellow]
end

module Teacher : MOORETEACHER with module S = S and module O = O = struct
  module S = S
  module O = O
  module M = Moore (S) (O)

  (** Phases cycle on [Tick]:
        Red -> Red+Yellow -> Green -> Yellow -> Red -> ...
      [Reset] forces the lamp back to Red *)
  let output_lang (s : S.str) : O.t =
    let phase =
      List.fold_left
        (fun p -> function S.Reset -> 0 | S.Tick -> (p + 1) mod 4)
        0 s
    in
    [|O.Red; O.RedYellow; O.Green; O.Yellow|].(phase)

  let equiv_query (m : 'a M.t) : S.str option =
    let rec find_counter_example depth current_strings =
      if depth >= int_of_float (2. ** 12.) then
        None
      else
        match current_strings with
        | [] ->
            None
        | s :: rest ->
            let moore_out = M.output_string m s in
            let spec_out = output_lang s in
            if moore_out <> spec_out then
              Some s
            else
              let next_gen = List.map (fun c -> s @ [c]) [S.Tick; S.Reset] in
              find_counter_example (depth + 1) (rest @ next_gen)
    in
    find_counter_example 0 [[]]

  let fuel : int = Int.max_int
end

(** Moore L* implementation *)
module Learner = MooreLstarLearner (Teacher)

module MP = MoorePrinter (Teacher)

(** Generate all input sequences of length up to [n] *)
let rec enumerate (n : int) : S.str list =
  if n <= 0 then
    [[]]
  else
    let prev = enumerate (n - 1) in
    let prepend c l = List.map (fun s -> [c] @ s) l in
    [[]] @ prepend S.Tick prev @ prepend S.Reset prev

let dedup l =
  List.fold_left
    (fun acc x ->
      if List.mem x acc then
        acc
      else
        x :: acc )
    [] l
  |> List.rev

(** Run the learned controller on test cases and pretty-print results *)
let print_results name m n =
  Printf.printf "\n=== %s ===\n" name ;
  print_endline "Moore machine found" ;
  MP.print_moore m ;
  Printf.printf "DOT file at %s\n" (MP.to_dot ~name:(name ^ "_traffic") m) ;
  let strings = dedup (enumerate n) in
  let col_w = max 12 (n + 2) in
  let header =
    Printf.sprintf "%-*s  %-11s  %-11s  %-8s" col_w "Input" "Expected" "Got"
      "Correct"
  in
  print_endline header ;
  List.iter
    (fun (c : S.str) ->
      let exp = Teacher.output_lang c in
      let comp = Teacher.M.output_string m c in
      Printf.printf "%-*s  %-11s  %-11s  %s\n" col_w
        (Printf.sprintf "[%s]" (S.string_of_str c))
        (O.string_of_t exp) (O.string_of_t comp)
        ( if exp = comp then
            "Y"
          else
            "N" ) )
    strings ;
  let correct =
    List.length
      (List.filter
         (fun (c : S.str) -> Teacher.output_lang c = Teacher.M.output_string m c)
         strings )
  in
  Printf.printf "Accuracy: %d/%d\n" correct (List.length strings)

let () = print_results "Moore-L*" (Learner.mlstar ()) 4
