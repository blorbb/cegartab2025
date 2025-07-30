From Stdlib Require Import PeanoNat Setoids.Setoid Classical Lia.
From Stdlib Require List.

From CegarTableaux Require Lit Nnf Kripke Mclause Mcnf.Mcnf.
From CegarTableaux Require Import Utils.

Import List.ListNotations.
Open Scope list_scope.


(** Equisatisfiable conversion from NNF to MCNF *)


(* returns the mcnf formula and the next free surrogate *)
(* given a name for the current formula (literal to 'fire' the current formula) *)
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
  (* []l = n -> []l *)
  (* | Nnf.Box (Nnf.Lit l) =>
    (
      [Mclause.Box (Lit.Pos n) l],
      sur
    ) *)
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
  (* <>l = n -> <>l *)
  (* | Nnf.Dia (Nnf.Lit l) =>
    (
      [Mclause.Dia (Lit.Pos n) l],
      sur
    ) *)
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


(* convert phi to (n /\ from_n_nnf n phi p) *)
(* (satisfiability preserving if n and p have the right bounds, used in proofs below) *)
Definition from_nnf_with_sur (name : nat) (phi : Nnf.t) (sur : nat) : Mcnf.t :=
  Mclause.Cpl [Lit.Pos name] :: fst (from_n_nnf name phi sur).


Definition from_nnf (phi : Nnf.t) : Mcnf.t :=
  let n := S (Nnf.max_atm phi) in
  from_nnf_with_sur n phi (S n).
