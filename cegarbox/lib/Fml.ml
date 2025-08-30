
type t =
| Var of int
| Neg of t
| And of t * t
| Or of t * t
| Impl of t * t
| Box of t
| Dia of t
