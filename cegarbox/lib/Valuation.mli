open List
open Lit

type t = Lit.t list

val forces_lit : t -> Lit.t -> bool
