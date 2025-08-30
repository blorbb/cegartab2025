open Lclauses
open Mclause
open Mcnf0

type t = Lclauses.t list

val from_mclause : Mclause.t -> t

val zip_merge : t -> t -> t

val from_mcnf : Mcnf0.t -> t
