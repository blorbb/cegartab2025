open Fml
open Lit
open PeanoNat

type t =
| Lit of Lit.t
| And of t * t
| Or of t * t
| Box of t
| Dia of t

val negate : t -> t

val from_fml : Fml.t -> t

val max_atm : t -> int
