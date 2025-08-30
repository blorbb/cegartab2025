open Assumptions
open Cnf
open CplClause
open List
open ListDef
open Lit
open Solution

type t = Bindings.t

(** val make : unit -> t **)

let make = Bindings.make

(** val add_clause : t -> CplClause.t -> t **)

let add_clause = Bindings.add_clause

(** val solve_with_assumptions : t -> Assumptions.t -> Solution.t **)

let solve_with_assumptions = Bindings.solve_with_assumptions

(** val make_with_clauses : Cnf.t -> t **)

let make_with_clauses clauses =
  fold_left add_clause clauses (make ())

(** val add_conflict_set : t -> Lit.t list -> t **)

let add_conflict_set solver conflict_set =
  add_clause solver (map negate conflict_set)
