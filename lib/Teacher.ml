open Lstar
open Language

module type Teacher = functor
  (Coq_s : Symbol)
  (D : sig
     type 'state t =
       { transition: 'state -> Coq_s.t -> 'state
       ; initial: 'state
       ; accept: 'state -> bool }

     val transition : 'a t -> 'a -> Coq_s.t -> 'a

     val initial : 'a t -> 'a

     val accept : 'a t -> 'a -> bool

     val run : 'a t -> Coq_s.string -> 'a

     val accept_string : 'a t -> Coq_s.string -> bool
   end)
  -> sig
  val equiv_query : 'a D.t -> Coq_s.string option
end
