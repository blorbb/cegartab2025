
(** val coq_Fix_F_sub : ('a1 -> ('a1 -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let rec coq_Fix_F_sub f_sub x =
  f_sub x (fun x0 -> coq_Fix_F_sub f_sub x0)

(** val coq_Fix_sub : ('a1 -> ('a1 -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let coq_Fix_sub =
  coq_Fix_F_sub
