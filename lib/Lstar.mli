open Datatypes
open Language
open Specif

type __ = Obj.t

val __ : Obj.t

open Datatypes
open Language

module Lstar : functor
  (Coq_s : Symbol)
  -> functor
  (L : sig
     val member : Coq_s.string -> bool
   end)
  -> functor
  (T : sig
     module DFA : sig
       type 'state t =
         { transition: 'state -> Coq_s.t -> 'state
         ; initial: 'state
         ; accept: 'state -> bool }

       val transition : 'state t -> 'state -> Coq_s.t -> 'state

       val initial : 'state t -> 'state

       val accept : 'state t -> 'state -> bool

       val run : 'state t -> Coq_s.string -> 'state

       val accept_string : 'state t -> Coq_s.string -> bool
     end

     val equiv_query : 'a DFA.t -> Coq_s.string option
   end)
  -> sig
  type closed = Coq_s.string -> Coq_s.t -> __ -> Coq_s.string

  type finite = Coq_s.string list

  type coq_HypothesisDFA =
    { coq_Q: Coq_s.string -> bool
    ; coq_T: Coq_s.string -> bool
    ; clos: closed
    ; fin_Q: finite
    ; fin_T: finite }

  val lstar_opt :
       int
    -> coq_HypothesisDFA
    -> ((__, __ T.DFA.t) sigT, (__, __ T.DFA.t) sigT) result
end
