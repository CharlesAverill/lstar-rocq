open Lstar
open KV
open DFA
open Stdlib

module type TEACHER = sig
  module S : Symbol

  module D : module type of DFA (S)

  val member : S.string -> bool

  val equiv_query : 'a D.t -> S.string option

  val fuel : int
end

module DFAPrinter (Teacher : TEACHER) = struct
  module S = Teacher.S

  (** Print the reachable states and transitions of a learned DFA for
    inspection. Discovers states by BFS from the initial state, numbering
    them in discovery order (0 = initial). *)
  let print_dfa (d : 'st Teacher.D.t) : unit =
    let module H = Hashtbl in
    let ids : ('st, int) H.t = H.create 16 in
    let order = ref [] in
    let next = ref 0 in
    let id_of s =
      match H.find_opt ids s with
      | Some i ->
          i
      | None ->
          let i = !next in
          incr next ;
          H.add ids s i ;
          order := s :: !order ;
          i
    in
    (* BFS over reachable states *)
    let rec explore = function
      | [] ->
          ()
      | s :: rest ->
          if H.mem ids s then
            explore rest
          else begin
            ignore (id_of s) ;
            let succs = List.map (fun c -> Teacher.D.transition d s c) S.enum in
            explore (rest @ succs)
          end
    in
    explore [Teacher.D.initial d] ;
    let states = List.rev !order in
    let init_id = id_of (Teacher.D.initial d) in
    (* States section *)
    Printf.printf "States (%d):\n" (List.length states) ;
    List.iter
      (fun s ->
        let i = id_of s in
        let acc =
          if Teacher.D.accept d s then
            "accept"
          else
            "reject"
        in
        let mark =
          if i = init_id then
            " <- initial"
          else
            ""
        in
        Printf.printf "  q%-3d  %s%s\n" i acc mark )
      states ;
    (* Transitions section *)
    Printf.printf "Transitions:\n" ;
    List.iter
      (fun s ->
        let i = id_of s in
        List.iter
          (fun c ->
            let dst = Teacher.D.transition d s c in
            Printf.printf "  q%-3d --%s--> q%d\n" i (S.string_of_t c)
              (id_of dst) )
          S.enum )
      states
end

module LstarLearner (T : TEACHER) = struct
  module Impl =
    Lstar
      (T.S)
      (struct
        module D = T.D

        let member = T.member

        let num_states_in_minimal = T.fuel
      end)
      (struct
        let equiv_query = T.equiv_query
      end)

  include Impl
  include DFAPrinter (T)
end

module KVLearner (T : TEACHER) = struct
  module Impl =
    KV
      (T.S)
      (struct
        module D = T.D

        let member = T.member

        let num_states_in_minimal = T.fuel
      end)
      (struct
        let equiv_query = T.equiv_query
      end)

  include Impl
  include DFAPrinter (T)
end
