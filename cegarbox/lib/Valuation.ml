open List
open Lit

type t = Lit.t list

(** val forces_lit : t -> Lit.t -> bool **)

let forces_lit val0 l =
  existsb (eqb l) val0
