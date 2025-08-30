(** This needs to be a separate file for OCaml bindings to be able to import this. *)

From CegarTableaux Require Valuation Assumptions.

(** The return type of a classical SAT-solver. *)
Inductive t : Type :=
  (* Returns valuations that make the formula satisfied. *)
  | Sat (val : Valuation.t)
  (* Returns assumptions that maintain unsatisfiability. *)
  | Unsat (core : Assumptions.t).


Definition is_sat t : bool :=
  match t with
  | Sat _ => true
  | Unsat _ => false
  end.


Definition is_unsat t : bool :=
  match t with
  | Sat _ => false
  | Unsat _ => true
  end.
