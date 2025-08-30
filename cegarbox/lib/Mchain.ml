open Lclauses
open Mclause
open Mcnf0

type t = Lclauses.t list

(** val from_mclause : Mclause.t -> t **)

let rec from_mclause = function
| Cpl cpl -> { cpls = (cpl :: []); boxes = []; dias = [] } :: []
| Box box -> { cpls = []; boxes = (box :: []); dias = [] } :: []
| Dia dia -> { cpls = []; boxes = []; dias = (dia :: []) } :: []
| Ctx phi0 -> empty :: (from_mclause phi0)

(** val zip_merge : t -> t -> t **)

let rec zip_merge a b =
  match a with
  | [] -> (match b with
           | [] -> a
           | _ :: _ -> b)
  | ha :: ta ->
    (match b with
     | [] -> a
     | hb :: tb -> (merge ha hb) :: (zip_merge ta tb))

(** val from_mcnf : Mcnf0.t -> t **)

let rec from_mcnf = function
| [] -> []
| head :: tail -> zip_merge (from_mclause head) (from_mcnf tail)
