open BoxClause
open CplClause
open DiaClause

type t =
| Cpl of CplClause.t
| Box of BoxClause.t
| Dia of DiaClause.t
| Ctx of t
