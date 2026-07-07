(* alternating bit string example over a socket *)

open Specif
open Teacher
open SocketTeacher
open Unix

(** Two-symbol alphabet. *)
module S = struct
  type t = Zero | One

  let string_of_t = function Zero -> "0" | One -> "1"

  let t_of_string : string -> (t, string) Datatypes.result = function
    | "0" -> Ok Zero
    | "1" -> Ok One
    | _ -> Error "t_of_string"

  let eq_dec x y = x = y

  let enum = [Zero; One]

  type str = t list

  let string_of_str s = String.concat "" (Stdlib.List.map string_of_t s)
end

(* Target language: words whose symbols strictly alternate (no two adjacent
   symbols equal). The empty word is accepted. *)
let language_member (s : S.str) : bool =
  let rec alternating = function
    | [] | [_] -> true
    | a :: (b :: _ as rest) -> a <> b && alternating rest
  in
  alternating s

(* --- Mock oracle: answers membership and equivalence queries --------------- *)

(* Breadth-first search for the shortest word on which the submitted DFA and the
   target language disagree; None if they agree up to [max_len]. *)
let find_counterexample ~max_len (initial_state : int)
    (transitions : (int * string * int) list) (accepting_states : int list) :
    string option =
  let transition state symbol =
    let sym = S.string_of_t symbol in
    match Stdlib.List.find_opt (fun (f, s, _) -> f = state && s = sym) transitions with
    | Some (_, _, dst) -> dst
    | None -> state
  in
  let accepts word =
    let final = Stdlib.List.fold_left transition initial_state word in
    Stdlib.List.mem final accepting_states
  in
  let rec bfs = function
    | [] -> None
    | word :: rest ->
        if Stdlib.List.length word > max_len then None
        else if accepts word <> language_member word then
          Some (String.concat "," (Stdlib.List.map S.string_of_t word))
        else
          bfs (rest @ Stdlib.List.map (fun c -> word @ [c]) S.enum)
  in
  bfs [[]]

(* --- JSON parsing for the serialized DFA ----------------------------------- *)

let extract_int_field field json =
  let re = Str.regexp (Printf.sprintf {|"%s"[ \t]*:[ \t]*\([0-9]+\)|} field) in
  try
    ignore (Str.search_forward re json 0) ;
    int_of_string (Str.matched_group 1 json)
  with Not_found -> 0

let parse_transitions json =
  let re =
    Str.regexp
      {|{"from":[ \t]*\([0-9]+\),[ \t]*"input":[ \t]*"\([^"]+\)",[ \t]*"to":[ \t]*\([0-9]+\)}|}
  in
  let rec find pos acc =
    match Str.search_forward re json pos with
    | _ ->
        let from_id = int_of_string (Str.matched_group 1 json) in
        let input = Str.matched_group 2 json in
        let to_id = int_of_string (Str.matched_group 3 json) in
        find (Str.match_end ()) ((from_id, input, to_id) :: acc)
    | exception Not_found -> acc
  in
  find 0 []

let parse_accepting_states json =
  let re = Str.regexp {|{"id":[ \t]*\([0-9]+\),[ \t]*"accept":[ \t]*true}|} in
  let rec find pos acc =
    match Str.search_forward re json pos with
    | _ -> find (Str.match_end ()) (int_of_string (Str.matched_group 1 json) :: acc)
    | exception Not_found -> acc
  in
  find 0 []

let is_membership_query line =
  match Str.search_forward (Str.regexp {|"type"[ \t]*:[ \t]*"mq"|}) line 0 with
  | _ -> true
  | exception Not_found -> false

let word_of_json line =
  let re = Str.regexp {|"word"[ \t]*:[ \t]*"\([^"]*\)"|} in
  let raw =
    match Str.search_forward re line 0 with
    | _ -> Str.matched_group 1 line
    | exception Not_found -> ""
  in
  if raw = "" then []
  else
    Stdlib.List.filter_map
      (function "0" -> Some S.Zero | "1" -> Some S.One | _ -> None)
      (String.split_on_char ',' raw)

(* --- Mock server ----------------------------------------------------------- *)

let start_mock_server () =
  let server = socket PF_INET SOCK_STREAM 0 in
  setsockopt server SO_REUSEADDR true ;
  bind server (ADDR_INET (inet_addr_loopback, 8888)) ;
  listen server 1 ;
  let client, _ = accept server in
  let ic = in_channel_of_descr client in
  let oc = out_channel_of_descr client in
  let reply s = output_string oc (s ^ "\n") ; flush oc in
  try
    while true do
      let line = input_line ic in
      if String.trim line <> "" then
        if is_membership_query line then
          reply (string_of_bool (language_member (word_of_json line)))
        else
          let initial = extract_int_field "initial_state" line in
          let transitions = parse_transitions line in
          let accepting = parse_accepting_states line in
          match find_counterexample ~max_len:12 initial transitions accepting with
          | None -> reply "NONE"
          | Some ce -> reply ce
    done
  with End_of_file ->
    close_in ic ; close_out oc ; Unix.close server

(* --- Runtime: start the oracle, run L*, report accuracy -------------------- *)

let () =
  print_endline "Starting mock oracle on port 8888..." ;
  ignore (Thread.create start_mock_server ()) ;
  Thread.delay 0.2

module ST = MakeSocketTeacher (S)
module NetworkLstar = LstarLearner (ST)
module DP = DFAPrinter (ST)

let rec enumerate n : S.str list =
  if n <= 0 then [[]]
  else
    let prev = enumerate (n - 1) in
    Stdlib.List.concat_map (fun s -> Stdlib.List.map (fun c -> c :: s) S.enum) prev

let print_results name dfa n =
  Printf.printf "\n=== %s ===\n" name ;
  DP.print_dfa dfa ;
  let strings = enumerate n in
  let col_w = max 10 (n + 2) in
  Printf.printf "%-*s  %-8s  %-8s  %-8s\n" col_w "Input" "Expected" "Got" "Correct" ;
  let correct = ref 0 in
  Stdlib.List.iter
    (fun (c : S.str) ->
      let exp = ST.member c and got = ST.D.accept_string dfa c in
      if exp = got then incr correct ;
      Printf.printf "%-*s  %-8b  %-8b  %s\n" col_w
        (Printf.sprintf "[%s]" (S.string_of_str c))
        exp got (if exp = got then "Y" else "N") )
    strings ;
  Printf.printf "Accuracy: %d/%d\n" !correct (Stdlib.List.length strings)

let () =
  let (Coq_existT (_, dfa)) = NetworkLstar.lstar () in
  print_results "Isolated Network Test L*" dfa 3
