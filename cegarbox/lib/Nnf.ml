open Fml
open Lit
open PeanoNat

type t =
| Lit of Lit.t
| And of t * t
| Or of t * t
| Box of t
| Dia of t

(** val negate : t -> t **)

let rec negate = function
| Lit l -> Lit (Lit.negate l)
| And (a, b) -> Or ((negate a), (negate b))
| Or (a, b) -> And ((negate a), (negate b))
| Box a -> Dia (negate a)
| Dia a -> Box (negate a)

(** val from_fml : Fml.t -> t **)

let rec from_fml = function
| Var x -> Lit (Pos x)
| Fml.Neg a -> negate (from_fml a)
| Fml.And (a, b) -> And ((from_fml a), (from_fml b))
| Fml.Or (a, b) -> Or ((from_fml a), (from_fml b))
| Impl (a, b) -> Or ((negate (from_fml a)), (from_fml b))
| Fml.Box a -> Box (from_fml a)
| Fml.Dia a -> Dia (from_fml a)

(** val max_atm : t -> int **)

let rec max_atm = function
| Lit l -> (match l with
            | Pos x -> x
            | Neg x -> x)
| And (a, b) -> Nat.max (max_atm a) (max_atm b)
| Or (a, b) -> Nat.max (max_atm a) (max_atm b)
| Box a -> max_atm a
| Dia a -> max_atm a
