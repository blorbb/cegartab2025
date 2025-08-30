open Assumptions
open Valuation

type t =
| Sat of Valuation.t
| Unsat of Assumptions.t
