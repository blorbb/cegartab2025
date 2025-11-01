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
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Solution =
 struct
  type t =
  | Sat
  | Unsat of Assumptions.t
 end

(** val conflict_set_of :
    Lclauses.t -> t -> Lit.t -> Lit.t list -> Lit.t list **)

let conflict_set_of w0 solver_val dia_antecedent core =
  let fired_box_clauses =
    apply w0.boxes (filter (fun box -> forces_lit solver_val (fst box)))
  in
  apply
    (apply
      (apply fired_box_clauses
        (filter (fun box -> existsb (eqb (snd box)) core)))
      (map fst))
    (fun x -> dia_antecedent :: x)

(** val first_cpls : Mchain.t -> CplClause.t list **)

let first_cpls = function
| [] -> []
| w0 :: _ -> w0.cpls

module HA =
 struct
  type t = { failed_val : Valuation.t; conflict_set : Lit.t list }
 end

(** val cegar_box_jumps :
    Assumptions.t -> Lclauses.t -> Mchain.t -> CplSolver.t -> t ->
    DiaClause.t list -> HA.t list -> (Assumptions.t -> Mchain.t ->
    CplSolver.t -> HA.t list -> __ -> __ -> Solution.t) -> Solution.t **)

let rec cegar_box_jumps assumptions w0 tail solver valuation dias0 hist cegar_box0 =
  match dias0 with
  | [] -> Solution.Sat
  | t0 :: dias' ->
    let (c, d) = t0 in
    let clause_is_fired = forces_lit valuation c in
    if clause_is_fired
    then let fired_box_clauses =
           apply w0.boxes (filter (fun box -> forces_lit valuation (fst box)))
         in
         let fired_box_lits = map snd fired_box_clauses in
         let next_cpls = first_cpls tail in
         let jump =
           cegar_box0 (d :: fired_box_lits) tail
             (make_with_clauses next_cpls) [] __ __
         in
         (match jump with
          | Solution.Sat ->
            cegar_box_jumps assumptions w0 tail solver valuation dias' hist
              cegar_box0
          | Solution.Unsat core ->
            let conflict_set0 = conflict_set_of w0 valuation c core in
            let solver0 = add_conflict_set solver conflict_set0 in
            cegar_box0 assumptions (w0 :: tail) solver0 ({ HA.failed_val =
              valuation; HA.conflict_set = conflict_set0 } :: hist) __ __)
    else cegar_box_jumps assumptions w0 tail solver valuation dias' hist
           cegar_box0

(** val cegar_box_func :
    (Assumptions.t, (Mchain.t, (CplSolver.t, HA.t list) sigT) sigT) sigT ->
    Solution.t **)

let cegar_box_func =
  coq_Fix_sub (fun recarg cegar_box' ->
    let assumptions = projT1 recarg in
    let phi = projT1 (projT2 recarg) in
    let solver = projT1 (projT2 (projT2 recarg)) in
    let hist = projT2 (projT2 (projT2 recarg)) in
    let cegar_box0 = fun assumptions0 phi0 solver0 hist0 ->
      cegar_box' (Coq_existT (assumptions0, (Coq_existT (phi0, (Coq_existT
        (solver0, hist0))))))
    in
    let filtered_var = solve_with_assumptions solver assumptions in
    (match filtered_var with
     | Sat valuation ->
       (match phi with
        | [] -> Solution.Sat
        | w0 :: tail ->
          cegar_box_jumps assumptions w0 tail solver valuation w0.dias hist
            (fun x x0 x1 x2 _ _ -> cegar_box0 x x0 x1 x2))
     | Unsat core -> Solution.Unsat core))

(** val cegar_box :
    Assumptions.t -> Mchain.t -> CplSolver.t -> HA.t list -> Solution.t **)

let cegar_box assumptions phi solver hist =
  cegar_box_func (Coq_existT (assumptions, (Coq_existT (phi, (Coq_existT
    (solver, hist))))))

(** val solve_mchain : Mchain.t -> Solution.t **)

let solve_mchain phi =
  let cpls0 = first_cpls phi in cegar_box [] phi (make_with_clauses cpls0) []

(** val solve_fml : Fml.t -> Solution.t **)

let solve_fml phi =
  apply (apply (apply (apply phi from_fml) from_nnf) from_mcnf) solve_mchain
