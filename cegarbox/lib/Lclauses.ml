open BoxClause
open CplClause
open Datatypes
open DiaClause

type t = { cpls : CplClause.t list; boxes : BoxClause.t list;
           dias : DiaClause.t list }

(** val empty : t **)

let empty =
  { cpls = []; boxes = []; dias = [] }

(** val merge : t -> t -> t **)

let merge a b =
  { cpls = (app a.cpls b.cpls); boxes = (app a.boxes b.boxes); dias =
    (app a.dias b.dias) }
