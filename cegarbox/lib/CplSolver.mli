open Assumptions
open Cnf
open CplClause
open List
open ListDef
open Lit
open Solution

type t = Bindings.t

val make : unit -> t

val add_clause : t -> CplClause.t -> t

val solve_with_assumptions : t -> Assumptions.t -> Solution.t

val make_with_clauses : Cnf.t -> t

val add_conflict_set : t -> Lit.t list -> t
