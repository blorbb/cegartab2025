open Assumptions
open CplClause
open CplSolver
open Datatypes
open DiaClause
open Fml
open Lclauses
open List
open ListDef
open Lit
open Mchain
open Mcnf0
open Nnf
open Solution
open Specif
open Utils
open Valuation
open Wf

type __ = Obj.t

module Solution :
 sig
  type t =
  | Sat
  | Unsat of Assumptions.t
 end

val conflict_set_of : Lclauses.t -> t -> Lit.t -> Lit.t list -> Lit.t list

val first_cpls : Mchain.t -> CplClause.t list

module VA :
 sig
  type t = { val_attempt : Valuation.t; conflict_set : Lit.t list }
 end

val cegar_box_jumps_func :
  (Assumptions.t, (Lclauses.t, (Mchain.t, (CplSolver.t, (t, (DiaClause.t
  list, (VA.t list, (__, Assumptions.t -> Mchain.t -> CplSolver.t -> VA.t
  list -> __ -> __ -> Solution.t) sigT) sigT) sigT) sigT) sigT) sigT) sigT)
  sigT -> Solution.t

val cegar_box_jumps :
  Assumptions.t -> Lclauses.t -> Mchain.t -> CplSolver.t -> t -> DiaClause.t
  list -> VA.t list -> (Assumptions.t -> Mchain.t -> CplSolver.t -> VA.t list
  -> __ -> __ -> Solution.t) -> Solution.t

val cegar_box_func :
  (Assumptions.t, (Mchain.t, (CplSolver.t, VA.t list) sigT) sigT) sigT ->
  Solution.t

val cegar_box :
  Assumptions.t -> Mchain.t -> CplSolver.t -> VA.t list -> Solution.t

val solve_mchain : Mchain.t -> Solution.t

val solve_fml : Fml.t -> Solution.t
