(** Equisatisfiable conversion from NNF to MCNF.

    We use the term 'surrogate' to mean an unused atom value. *)

From Stdlib Require List.

From CegarTableaux Require Lit Nnf Kripke Mclause Mcnf.Mcnf.
From CegarTableaux Require Import Utils.

Import List.ListNotations.
Open Scope list_scope.

(** Converts [n -> phi] to MCNF, with a given surrogate value.

    Returns a pair of the MCNF formula, and the next free surrogate.

    Corresponds to [mcnf(n -> phi, k)] in the paper. *)
Fixpoint from_n_nnf (n : nat) (phi : Nnf.t) (sur : nat) : (Mcnf.t * nat) :=
  match phi with
  (* n -> l  =>  ~n \/ l *)
  | Nnf.Lit l =>
    (
      [Mclause.Cpl [Lit.Neg n ; l]],
      sur
    )
  (* n -> A /\ B  =>  n -> nA ; n -> nB ; nA -> A ; nB -> B *)
  | Nnf.And A B =>
    let (nA, sur) := (sur, S sur) in
    let (nB, sur) := (sur, S sur) in
    let (A_mcnf, sur) := from_n_nnf nA A sur in
    let (B_mcnf, sur) := from_n_nnf nB B sur in
    (
      Mclause.Cpl [Lit.Neg n ; Lit.Pos nA] ::
      Mclause.Cpl [Lit.Neg n ; Lit.Pos nB] ::
      A_mcnf ++ B_mcnf,
      sur
    )
  (* n -> A \/ B  =>  n -> nA \/ nB ; nA -> A ; nB -> B *)
  | Nnf.Or A B =>
    let (nA, sur) := (sur, S sur) in
    let (nB, sur) := (sur, S sur) in
    let (A_mcnf, sur) := from_n_nnf nA A sur in
    let (B_mcnf, sur) := from_n_nnf nB B sur in
    (
      Mclause.Cpl [Lit.Neg n ; Lit.Pos nA ; Lit.Pos nB] ::
      A_mcnf ++ B_mcnf,
      sur
    )
  (* n -> []A  =>  n -> []nA ; [](nA -> A) *)
  | Nnf.Box A =>
    let (nA, sur) := (sur, S sur) in
    let (A_mcnf, sur) := from_n_nnf nA A sur in
    (
      Mclause.Box ((Lit.Pos n), (Lit.Pos nA)) ::
      (* wrap in new context *)
      List.map Mclause.Ctx A_mcnf,
      sur
    )
  (* n -> <>A  =>  n -> <>nA ; [](nA -> A) *)
  | Nnf.Dia A =>
    let (nA, sur) := (sur, S sur) in
    let (A_mcnf, sur) := from_n_nnf nA A sur in
    (
      Mclause.Dia ((Lit.Pos n), (Lit.Pos nA)) ::
      (* wrap the clauses in A new context *)
      List.map Mclause.Ctx A_mcnf,
      sur
    )
  end.


(** Converts [phi] with a name and surrogate to [n /\ mcnf(n -> phi, k)]. *)
Definition from_nnf_with_sur (name : nat) (phi : Nnf.t) (sur : nat) : Mcnf.t :=
  Mclause.Cpl [Lit.Pos name] :: fst (from_n_nnf name phi sur).


(** Converts an NNF formula to MCNF. *)
Definition from_nnf (phi : Nnf.t) : Mcnf.t :=
  let n := S (Nnf.max_atm phi) in
  from_nnf_with_sur n phi (S n).
