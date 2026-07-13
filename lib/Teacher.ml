open Lstar
open Lstar_Moore
open KV
open TTT
open NLstar
open Automata
open Stdlib

(** Minimally Adequate Teachers *)

(* Teacher for DFAs *)
module type DFATEACHER = sig
  (** Language alphabet *)
  module S : Symbol

  (** DFA *)
  module D : module type of DFA (S)

  val member : S.str -> bool
  (** Membership query *)

  val equiv_query : 'a D.t -> S.str option
  (** Equivalence query *)

  val fuel : int
  (** Maximum number of iterations to take
      
      Set to [Int.max_int] unless you know what you're doing *)
end

(* Teacher for NFAs *)
module type NFATEACHER = sig
  (** Language alphabet *)
  module S : Symbol

  (** RFSA *)
  module R : module type of RFSA (S)

  val member : S.str -> bool
  (** Membership query *)

  val equiv_query : 'a R.N.t -> S.str option
  (** Equivalence query *)

  val fuel : int
  (** Maximum number of iterations to take
      
      Set to [Int.max_int] unless you know what you're doing *)
end

(* Teacher for Moore machines *)
module type MOORETEACHER = sig
  (** Symbol alphabet *)
  module S : Symbol

  (** Output alphabet *)
  module O : Symbol

  (** DFA *)
  module M : module type of Moore (S) (O)

  val output_lang : S.str -> O.t
  (** Membership query *)

  val equiv_query : 'a M.t -> S.str option
  (** Equivalence query *)

  val fuel : int
  (** Maximum number of iterations to take
      
      Set to [Int.max_int] unless you know what you're doing *)
end

module DFAPrinter (Teacher : DFATEACHER) = struct
  module S = Teacher.S

  (* Returns states in discovery order plus an id lookup *)
  let discover (d : 'st Teacher.D.t) =
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
    (List.rev !order, id_of)

  let print_dfa (d : 'st Teacher.D.t) : unit =
    let states, id_of = discover d in
    let init_id = id_of (Teacher.D.initial d) in
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

  (** Render the DFA in Graphviz DOT format to a fresh temporary file and
      print the file's path to stdout. Accept states are drawn as double
      circles, the initial state has an incoming arrow from an invisible
      node, and every edge is labeled with its input symbol. The returned
      string is the path, e.g. to feed to [dot -Tpng <path> -o dfa.png]. *)
  let to_dot ?(name = "DFA") (d : 'st Teacher.D.t) : string =
    let states, id_of = discover d in
    let init_id = id_of (Teacher.D.initial d) in
    let path = Filename.temp_file name ".dot" in
    let out = open_out path in
    Fun.protect
      ~finally:(fun () -> close_out out)
      (fun () ->
        let p fmt = Printf.fprintf out fmt in
        let escape s =
          let buf = Buffer.create (String.length s + 2) in
          String.iter
            (fun ch ->
              match ch with
              | '"' ->
                  Buffer.add_string buf "\\\""
              | '\\' ->
                  Buffer.add_string buf "\\\\"
              | '\n' ->
                  Buffer.add_string buf "\\n"
              | '_' ->
                  Buffer.add_string buf " - "
              | c ->
                  Buffer.add_char buf c )
            s ;
          Buffer.contents buf
        in
        p "digraph \"%s\" {\n" (escape name) ;
        (* ---- graph-level styling ---- *)
        p "  bgcolor=\"#fbfbfd\";\n" ;
        p "  rankdir=LR;\n" ;
        p "  nodesep=0.5;\n" ;
        p "  dpi=300;\n" ;
        p "  ranksep=0.6;\n" ;
        p "  pad=0.3;\n" ;
        p "  label=\"%s\";\n" (escape name) ;
        p "  labelloc=\"t\";\n" ;
        p "  fontsize=22;\n" ;
        p "  fontname=\"Helvetica Neue, Helvetica, Arial, sans-serif\";\n" ;
        p "  fontcolor=\"#1d1d1f\";\n" ;
        (* ---- shared node + edge defaults ---- *)
        p
          "  node [fontname=\"Helvetica Neue, Helvetica, Arial, sans-serif\", \
           fontsize=13, penwidth=1.4, style=filled];\n" ;
        p
          "  edge [fontname=\"Menlo, Consolas, monospace\", fontsize=11, \
           color=\"#8a8a8e\", fontcolor=\"#3a3a3c\", arrowsize=0.8, \
           penwidth=1.1];\n" ;
        (* ---- start marker ---- *)
        p "  __start [shape=point, width=0.12, color=\"#1d1d1f\"];\n" ;
        (* ---- states ---- *)
        List.iter
          (fun s ->
            let i = id_of s in
            let shape, fill, line =
              if Teacher.D.accept d s then
                ("doublecircle", "#d6f0dd", "#349a57")
              (* accept: green *)
              else
                ("circle", "#eef1f6", "#9aa0aa")
              (* reject: grey-blue *)
            in
            p
              "  q%d [shape=%s, label=\"q%d\", fillcolor=\"%s\", color=\"%s\"];\n"
              i shape i fill line )
          states ;
        (* ---- start arrow ---- *)
        p "  __start -> q%d [color=\"#1d1d1f\", penwidth=1.4];\n" init_id ;
        (* ---- transitions (collapse parallel edges, omit universal label) ---- *)
        let alphabet_size = List.length S.enum in
        List.iter
          (fun s ->
            let i = id_of s in
            let tbl : (int, Buffer.t * int ref) Hashtbl.t = Hashtbl.create 8 in
            let dst_order = ref [] in
            List.iter
              (fun c ->
                let dst = id_of (Teacher.D.transition d s c) in
                let buf, cnt =
                  match Hashtbl.find_opt tbl dst with
                  | Some bc ->
                      bc
                  | None ->
                      let bc = (Buffer.create 16, ref 0) in
                      Hashtbl.add tbl dst bc ;
                      dst_order := dst :: !dst_order ;
                      bc
                in
                if Buffer.length buf > 0 then Buffer.add_string buf ", " ;
                Buffer.add_string buf (escape (S.string_of_t c)) ;
                incr cnt )
              S.enum ;
            List.iter
              (fun dst ->
                let buf, cnt = Hashtbl.find tbl dst in
                let self =
                  if i = dst then
                    " dir=back"
                  else
                    ""
                in
                if !cnt = alphabet_size then
                  p "  q%d -> q%d [color=\"#c6c6cc\"%s];\n" i dst self
                else
                  p "  q%d -> q%d [label=\" %s \"%s];\n" i dst
                    (Buffer.contents buf) self )
              (List.rev !dst_order) )
          states ;
        p "}\n" ) ;
    path
end

(** Pretty-printer / DOT exporter for learned Moore machines. *)
module MoorePrinter (Teacher : MOORETEACHER) = struct
  module S = Teacher.S
  module O = Teacher.O

  (* States in discovery order plus an id lookup, exactly as DFAPrinter. *)
  let discover (m : 'st Teacher.M.t) =
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
    let rec explore = function
      | [] ->
          ()
      | s :: rest ->
          if H.mem ids s then
            explore rest
          else begin
            ignore (id_of s) ;
            let succs = List.map (fun c -> Teacher.M.transition m s c) S.enum in
            explore (rest @ succs)
          end
    in
    explore [Teacher.M.initial m] ;
    (List.rev !order, id_of)

  let print_moore (m : 'st Teacher.M.t) : unit =
    let states, id_of = discover m in
    let init_id = id_of (Teacher.M.initial m) in
    Printf.printf "States (%d):\n" (List.length states) ;
    List.iter
      (fun s ->
        let i = id_of s in
        let out = O.string_of_t (Teacher.M.output m s) in
        let mark =
          if i = init_id then
            " <- initial"
          else
            ""
        in
        Printf.printf "  q%-3d  out=%s%s\n" i out mark )
      states ;
    Printf.printf "Transitions:\n" ;
    List.iter
      (fun s ->
        let i = id_of s in
        List.iter
          (fun c ->
            let dst = Teacher.M.transition m s c in
            Printf.printf "  q%-3d --%s--> q%d\n" i (S.string_of_t c)
              (id_of dst) )
          S.enum )
      states

  (** Render the Moore machine in Graphviz DOT format to a fresh temporary
      file and return its path.  Mirrors the DFA printer's styling; the
      accept/reject colouring is replaced by a per-output colour, and each
      node is labelled with its state id and emitted output. *)
  let to_dot ?(name = "Moore") (m : 'st Teacher.M.t) : string =
    let states, id_of = discover m in
    let init_id = id_of (Teacher.M.initial m) in
    let path = Filename.temp_file name ".dot" in
    let out = open_out path in
    Fun.protect
      ~finally:(fun () -> close_out out)
      (fun () ->
        let p fmt = Printf.fprintf out fmt in
        let escape s =
          let buf = Buffer.create (String.length s + 2) in
          String.iter
            (fun ch ->
              match ch with
              | '"' ->
                  Buffer.add_string buf "\\\""
              | '\\' ->
                  Buffer.add_string buf "\\\\"
              | '\n' ->
                  Buffer.add_string buf "\\n"
              | '_' ->
                  Buffer.add_string buf " - "
              | c ->
                  Buffer.add_char buf c )
            s ;
          Buffer.contents buf
        in
        (* A fixed palette; each distinct output value gets a (fill, line)
           colour pair, assigned by its position in [O.enum]. *)
        let palette =
          [| ("#fde2e1", "#d1584f") (* red *);
             ("#d6f0dd", "#349a57") (* green *);
             ("#fdf3d0", "#c9a227") (* yellow *);
             ("#ffe5cc", "#d97707") (* orange *);
             ("#dbe7fb", "#3a6fd8") (* blue *);
             ("#ece1f7", "#7a4fd1") (* purple *);
             ("#e6f0f0", "#3a9a9a") |] (* teal *);
        in
        let colour_of out =
          let rec idx i = function
            | [] ->
                0
            | x :: _ when Teacher.O.eq_dec x out ->
                i
            | _ :: r ->
                idx (i + 1) r
          in
          palette.(idx 0 O.enum mod Array.length palette)
        in
        p "digraph \"%s\" {\n" (escape name) ;
        (* ---- graph-level styling ---- *)
        p "  bgcolor=\"#fbfbfd\";\n" ;
        p "  rankdir=LR;\n" ;
        p "  nodesep=0.5;\n" ;
        p "  dpi=300;\n" ;
        p "  ranksep=0.6;\n" ;
        p "  pad=0.3;\n" ;
        p "  label=\"%s\";\n" (escape name) ;
        p "  labelloc=\"t\";\n" ;
        p "  fontsize=22;\n" ;
        p "  fontname=\"Helvetica Neue, Helvetica, Arial, sans-serif\";\n" ;
        p "  fontcolor=\"#1d1d1f\";\n" ;
        (* ---- shared node + edge defaults ---- *)
        p
          "  node [fontname=\"Helvetica Neue, Helvetica, Arial, sans-serif\", \
           fontsize=13, penwidth=1.4, style=filled];\n" ;
        p
          "  edge [fontname=\"Menlo, Consolas, monospace\", fontsize=11, \
           color=\"#8a8a8e\", fontcolor=\"#3a3a3c\", arrowsize=0.8, \
           penwidth=1.1];\n" ;
        (* ---- start marker ---- *)
        p "  __start [shape=point, width=0.12, color=\"#1d1d1f\"];\n" ;
        (* ---- states: labelled with id + output, coloured by output ---- *)
        List.iter
          (fun s ->
            let i = id_of s in
            let out = Teacher.M.output m s in
            let fill, line = colour_of out in
            p
              "  q%d [shape=circle, label=\"q%d\\n%s\", fillcolor=\"%s\", \
               color=\"%s\"];\n"
              i i
              (escape (O.string_of_t out))
              fill line )
          states ;
        (* ---- start arrow ---- *)
        p "  __start -> q%d [color=\"#1d1d1f\", penwidth=1.4];\n" init_id ;
        (* ---- transitions (collapse parallel edges, omit universal label) ---- *)
        let alphabet_size = List.length S.enum in
        List.iter
          (fun s ->
            let i = id_of s in
            let tbl : (int, Buffer.t * int ref) Hashtbl.t = Hashtbl.create 8 in
            let dst_order = ref [] in
            List.iter
              (fun c ->
                let dst = id_of (Teacher.M.transition m s c) in
                let buf, cnt =
                  match Hashtbl.find_opt tbl dst with
                  | Some bc ->
                      bc
                  | None ->
                      let bc = (Buffer.create 16, ref 0) in
                      Hashtbl.add tbl dst bc ;
                      dst_order := dst :: !dst_order ;
                      bc
                in
                if Buffer.length buf > 0 then Buffer.add_string buf ", " ;
                Buffer.add_string buf (escape (S.string_of_t c)) ;
                incr cnt )
              S.enum ;
            List.iter
              (fun dst ->
                let buf, cnt = Hashtbl.find tbl dst in
                let self = if i = dst then " dir=back" else "" in
                if !cnt = alphabet_size then
                  p "  q%d -> q%d [color=\"#c6c6cc\"%s];\n" i dst self
                else
                  p "  q%d -> q%d [label=\" %s \"%s];\n" i dst
                    (Buffer.contents buf) self )
              (List.rev !dst_order) )
          states ;
        p "}\n" ) ;
    path
end

module LstarLearner (T : DFATEACHER) = struct
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

  let lstar () : __ T.D.t = match Impl.lstar () with Coq_existT (_, d) -> d
end

module MooreLstarLearner (T : MOORETEACHER) = struct
  module Impl =
    MooreLstar (T.S) (T.O)
      (struct
        module M = T.M

        let output_lang = T.output_lang

        let num_states_in_minimal = T.fuel
      end)
      (struct
        let equiv_query = T.equiv_query
      end)

  include Impl

  let mlstar () : __ T.M.t = match Impl.mlstar () with Coq_existT (_, m) -> m
end

module KVLearner (T : DFATEACHER) = struct
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

  let kv () : __ T.D.t = match Impl.kv () with Coq_existT (_, d) -> d
end

module TTTLearner (T : DFATEACHER) = struct
  module Impl =
    TTT
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

  let ttt () : __ T.D.t = match Impl.ttt () with Coq_existT (_, d) -> d
end

module NLstarLearner (T : NFATEACHER) = struct
  module Impl =
    NLstar
      (T.S)
      (struct
        module N = T.R.N
        module R = T.R
        module Res = R.Res

        let member = T.member

        let num_states_in_canonical = T.fuel
      end)
      (struct
        let equiv_query r_aut = T.equiv_query (T.R.nfa r_aut)
      end)

  include Impl
end
