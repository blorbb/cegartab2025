
type t =
| Pos of int
| Neg of int

val negate : t -> t

val atm : t -> int

val eqb : t -> t -> bool
