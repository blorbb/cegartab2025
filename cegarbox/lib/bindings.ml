module IntSet = Stdlib.Set.Make (Int)

(** The Minisat solver, and a set of atoms which are in the solver.
  The atoms are those from the Rocq program, i.e. they can start from 0.
*)
type t =
  { solver : Minisat.t
  ; atoms : IntSet.t
  }

let union_lits set vals = IntSet.union set (IntSet.of_list (Stdlib.List.map Lit.atm vals))

let rocq_lit_to_minisat l =
  match l with
  | Lit.Pos p -> Minisat.Lit.make (p + 1)
  | Lit.Neg p -> Minisat.Lit.make (p + 1) |> Minisat.Lit.neg
;;

let minisat_lit_to_rocq l =
  (* this atom is 1-indexed, return 0-indexed *)
  let p = Minisat.Lit.abs l |> Minisat.Lit.to_int in
  if Minisat.Lit.sign l then Lit.Pos (p - 1) else Lit.Neg (p - 1)
;;

let make () = { solver = Minisat.create (); atoms = IntSet.empty }

let add_clause s clause =
  ignore
    (try
       Minisat.add_clause_l s.solver (clause |> Stdlib.List.map rocq_lit_to_minisat)
     with
     | Minisat.Unsat -> ());
  { solver = s.solver; atoms = union_lits s.atoms clause }
;;

let solve_with_assumptions s (assumptions : Assumptions.t) : Solution.t =
  try
    Minisat.solve
      ~assumptions:
        (assumptions |> Stdlib.Array.of_list |> Stdlib.Array.map rocq_lit_to_minisat)
      s.solver;
    (* no exception means sat *)
    Solution.Sat
      (union_lits s.atoms assumptions
       |> IntSet.to_list
       (* p here is 0-indexed *)
       |> Stdlib.List.map (fun p ->
         (* check the 1-indexed atom, but return the 0-indexed one *)
         match Minisat.value s.solver (Minisat.Lit.make (p + 1)) with
         | Minisat.V_true -> Lit.Pos p
         | Minisat.V_false -> Lit.Neg p
         | Minisat.V_undef -> raise (Stdlib.Failure "unknown atom")))
  with
  | Minisat.Unsat ->
    Solution.Unsat
      (Minisat.unsat_core s.solver
       |> Stdlib.Array.to_list
       |> Stdlib.List.map minisat_lit_to_rocq)
;;
