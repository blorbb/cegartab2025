
type t =
| Pos of int
| Neg of int

(** val negate : t -> t **)

let negate = function
| Pos n -> Neg n
| Neg n -> Pos n

(** val atm : t -> int **)

let atm = function
| Pos n -> n
| Neg n -> n

(** val eqb : t -> t -> bool **)

let eqb a b =
  match a with
  | Pos x -> (match b with
              | Pos y -> (=) x y
              | Neg _ -> false)
  | Neg x -> (match b with
              | Pos _ -> false
              | Neg y -> (=) x y)
