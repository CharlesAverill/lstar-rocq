(* Coin-operated vending machine: a 30c item, coins of 5/10/25, and a
   refund lever *)

open Mealy
open Specif
open Teacher
open Stdlib

(** Input alphabet *)
module S = struct
  type t = Nickel | Dime | Quarter | Refund

  let string_of_t = function
    | Nickel ->
        "n"
    | Dime ->
        "d"
    | Quarter ->
        "q"
    | Refund ->
        "r"

  let t_of_string : string -> (t, string) Datatypes.result = function
    | "n" ->
        Ok Nickel
    | "d" ->
        Ok Dime
    | "q" ->
        Ok Quarter
    | "r" ->
        Ok Refund
    | _ ->
        Error "t_of_string"

  let eq_dec x y = x = y

  let enum = [Nickel; Dime; Quarter; Refund]

  type str = t list

  let string_of_str s = String.concat "" (List.map string_of_t s)
end

(** Output alphabet

    [Vend c] dispenses the item and returns [c] cents of change
    [Coins c] is the refund lever handing back [c] cents. *)
module O = struct
  type t = Nothing | Vend of int | Coins of int

  let string_of_t = function
    | Nothing ->
        "-"
    | Vend 0 ->
        "VEND"
    | Vend c ->
        Printf.sprintf "VEND+%d" c
    | Coins c ->
        Printf.sprintf "BACK %d" c

  let t_of_string : string -> (t, string) Datatypes.result = function
    | "-" ->
        Ok Nothing
    | "VEND" ->
        Ok (Vend 0)
    | s when String.length s > 5 && String.sub s 0 5 = "VEND+" ->
        Ok (Vend (int_of_string (String.sub s 5 (String.length s - 5))))
    | s when String.length s > 5 && String.sub s 0 5 = "BACK " ->
        Ok (Coins (int_of_string (String.sub s 5 (String.length s - 5))))
    | _ ->
        Error "t_of_string"

  let eq_dec x y = x = y

  type str = t list

  let enum =
    [Nothing]
    @ List.map (fun c -> Vend c) [0; 5; 10; 15; 20]
    @ List.map (fun c -> Coins c) [5; 10; 15; 20; 25]
end

module Teacher : MEALYTEACHER with module S = S and module O = O = struct
  module S = S
  module O = O
  module M = Mealy (S) (O)

  let price = 30

  let value = function
    | S.Nickel ->
        5
    | S.Dime ->
        10
    | S.Quarter ->
        25
    | S.Refund ->
        0

  (** Credit accumulated after consuming [s], starting from an empty
      machine. Inserting a coin that reaches the price vends and clears
      the credit. *)
  let credit (s : S.str) : int =
    List.fold_left
      (fun c -> function
        | S.Refund ->
            0
        | i ->
            let c' = c + value i in
            if c' >= price then
              0
            else
              c' )
      0 s

  (** Having already consumed [s], what does reading [a]
      emit? *)
  let output_lang (s : S.str) (a : S.t) : O.t =
    let c = credit s in
    match a with
    | S.Refund ->
        if c > 0 then
          O.Coins c
        else
          O.Nothing
    | i ->
        let c' = c + value i in
        if c' >= price then
          O.Vend (c' - price)
        else
          O.Nothing

  (** Breadth-first search for a word on which the hypothesis mispredicts. *)
  let equiv_query (m : 'a M.t) : S.str option =
    let rec find_counter_example depth current_strings =
      if depth >= int_of_float (2. ** 12.) then
        None
      else
        match current_strings with
        | [] ->
            None
        | s :: rest -> (
          match (s, List.rev s) with
          | [], _ | _, [] ->
              find_counter_example (depth + 1) rest
          | hd :: tl, a :: rprefix ->
              let prefix = List.rev rprefix in
              let mealy_out = M.last_output m hd tl in
              let spec_out = output_lang prefix a in
              if mealy_out <> spec_out then
                Some s
              else
                let next_gen = List.map (fun c -> s @ [c]) S.enum in
                find_counter_example (depth + 1) (rest @ next_gen) )
    in
    find_counter_example 0 (List.map (fun c -> [c]) S.enum)

  let fuel : int = Int.max_int
end

(** Mealy L* implementation *)
module LstarLearner = MealyLstarLearner (Teacher)

(** Mealy KV implementation *)
module KVLearner = MealyKVLearner (Teacher)

(** Mealy TTT implementation *)
module TTTLearner = MealyTTTLearner (Teacher)

module MP = MealyPrinter (Teacher)

(** Generate all input sequences of length up to [n] *)
let rec enumerate (n : int) : S.str list =
  if n <= 0 then
    [[]]
  else
    let prev = enumerate (n - 1) in
    let prepend c l = List.map (fun s -> [c] @ s) l in
    [[]] @ List.concat_map (fun c -> prepend c prev) S.enum

let dedup l =
  List.fold_left
    (fun acc x ->
      if List.mem x acc then
        acc
      else
        x :: acc )
    [] l
  |> List.rev

(** Split a non-empty word into its prefix and final symbol *)
let unsnoc (s : S.str) : (S.str * S.t) option =
  match List.rev s with [] -> None | a :: rprefix -> Some (List.rev rprefix, a)

(** Run the learned machine on test cases and pretty-print results *)
let print_results name m n =
  Printf.printf "\n=== %s ===\n" name ;
  print_endline "Mealy machine found" ;
  MP.print_mealy m ;
  Printf.printf "DOT file at %s\n" (MP.to_dot ~name:(name ^ "_vending") m) ;
  let strings =
    dedup (enumerate n) |> List.filter (fun (s : S.str) -> s <> [])
  in
  let col_w = max 12 (n + 2) in
  let header =
    Printf.sprintf "%-*s  %-11s  %-11s  %-8s" col_w "Input" "Expected" "Got"
      "Correct"
  in
  print_endline header ;
  List.iter
    (fun (c : S.str) ->
      match unsnoc c with
      | None ->
          ()
      | Some (prefix, a) ->
          let exp = Teacher.output_lang prefix a in
          let comp =
            match c with
            | [] ->
                exp (* unreachable: empty inputs are filtered out *)
            | hd :: tl ->
                Teacher.M.last_output m hd tl
          in
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
         (fun (c : S.str) ->
           match unsnoc c with
           | None ->
               true
           | Some (prefix, a) -> (
             match c with
             | [] ->
                 true
             | hd :: tl ->
                 Teacher.output_lang prefix a = Teacher.M.last_output m hd tl ) )
         strings )
  in
  Printf.printf "Accuracy: %d/%d\n" correct (List.length strings)

let () =
  print_results "Mealy-L*" (LstarLearner.mlstar ()) 3 ;
  print_results "Mealy-KV" (KVLearner.mkv ()) 3 ;
  print_results "Mealy-TTT" (TTTLearner.mttt ()) 3
