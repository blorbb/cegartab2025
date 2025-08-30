type t

val make : unit -> t
val add_clause : t -> Lit.t list -> t
val solve_with_assumptions : t -> Assumptions.t -> Solution.t
