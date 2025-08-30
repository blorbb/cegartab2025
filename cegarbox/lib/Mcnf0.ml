open Datatypes
open ListDef
open Lit
open Mclause
open Mcnf
open Nnf

type t = Mclause.t list

(** val from_n_nnf : int -> Nnf.t -> int -> Mcnf.t * int **)

let rec from_n_nnf n phi sur =
  match phi with
  | Lit l -> (((Cpl ((Neg n) :: (l :: []))) :: []), sur)
  | And (a, b) ->
    let sur0 = Stdlib.Int.succ sur in
    let sur1 = Stdlib.Int.succ sur0 in
    let (a_mcnf, sur2) = from_n_nnf sur a sur1 in
    let (b_mcnf, sur3) = from_n_nnf sur0 b sur2 in
    (((Cpl ((Neg n) :: ((Pos sur) :: []))) :: ((Cpl ((Neg n) :: ((Pos
    sur0) :: []))) :: (app a_mcnf b_mcnf))), sur3)
  | Or (a, b) ->
    let sur0 = Stdlib.Int.succ sur in
    let sur1 = Stdlib.Int.succ sur0 in
    let (a_mcnf, sur2) = from_n_nnf sur a sur1 in
    let (b_mcnf, sur3) = from_n_nnf sur0 b sur2 in
    (((Cpl ((Neg n) :: ((Pos sur) :: ((Pos
    sur0) :: [])))) :: (app a_mcnf b_mcnf)), sur3)
  | Box a ->
    let sur0 = Stdlib.Int.succ sur in
    let (a_mcnf, sur1) = from_n_nnf sur a sur0 in
    (((Mclause.Box ((Pos n), (Pos sur))) :: (map (fun x -> Ctx x) a_mcnf)),
    sur1)
  | Dia a ->
    let sur0 = Stdlib.Int.succ sur in
    let (a_mcnf, sur1) = from_n_nnf sur a sur0 in
    (((Mclause.Dia ((Pos n), (Pos sur))) :: (map (fun x -> Ctx x) a_mcnf)),
    sur1)

(** val from_nnf_with_sur : int -> Nnf.t -> int -> Mcnf.t **)

let from_nnf_with_sur name phi sur =
  (Cpl ((Pos name) :: [])) :: (fst (from_n_nnf name phi sur))

(** val from_nnf : Nnf.t -> Mcnf.t **)

let from_nnf phi =
  let n = Stdlib.Int.succ (max_atm phi) in
  from_nnf_with_sur n phi (Stdlib.Int.succ n)
