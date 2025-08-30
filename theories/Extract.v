From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From CegarTableaux Require Mcnf Tree Solver CplSolver.

Extraction Language OCaml.
Set Extraction Output Directory "cegarbox/lib".

(** The axioms depend on a module named [Bindings] being accessible with
    the correct implementation. *)
Extract Constant CplSolver.t => "Bindings.t".
Extract Constant CplSolver.make => "Bindings.make".
Extract Constant CplSolver.add_clause => "Bindings.add_clause".
Extract Constant CplSolver.solve_with_assumptions => "Bindings.solve_with_assumptions".

(** [Lit.atm] is needed in the OCaml bindings but is not used by [solve_fml]. *)
Separate Extraction Solver.solve_fml Lit.atm.
