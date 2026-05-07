open Specif

module type Symbol = sig
  type t

  val eq_dec : t -> t -> sumbool

  val enum : t list

  type string = t list

  val str_eq : string -> string -> sumbool
end
