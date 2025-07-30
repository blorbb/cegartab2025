From Stdlib Require List SetoidList.
From CegarTableaux Require CplClause Assumptions Lit Cnf Valuation.
From CegarTableaux Require Import Utils.
From Stdlib Require Import Permutation.
Import List.ListNotations.
Open Scope list_scope.

Module Solution.
  (** The return type of a SAT-solver. *)
  Inductive t : Type :=
    (** Returns valuations that make the formula satisfied. *)
    | Sat (val : Valuation.t)
    (** Returns assumptions that maintain unsatisfiability. *)
    | Unsat (core : Assumptions.t).

  Definition is_sat t : bool :=
    match t with
    | Sat _ => true
    | Unsat _ => false
    end.

  Definition is_unsat t : bool :=
    match t with
    | Sat _ => false
    | Unsat _ => true
    end.
End Solution.

(** A SAT-solver oracle. *)
Parameter t : Type.

Parameter make : t.

(** Add a clause to the solver, returning the new solver.

  Note that on the extraction side, minisat will be slightly incorrect.
  Minisat will *mutate* the existing solver, which means that the input
  solver must *never* be used again for everything to be clash_free.

  I'm not sure if there is a way to enforce this in Coq (affine types?),
  but we can manually check that the CEGAR-tableaux algorithm will never
  use an 'old' SAT-solver.
*)
Parameter add_clause : t -> CplClause.t -> t.

Parameter solve_with_assumptions : t -> Assumptions.t -> Solution.t.

(* Shortcut to make a new SAT-solver with these clauses *)
Definition make_with_clauses (clauses : Cnf.t) : t :=
  List.fold_left add_clause clauses make.

(** * Correctness *)

(** All clauses which have been added to this solver

  Not needed by the algorithm, only by the proofs.
*)
Parameter clauses_of : t -> Cnf.t.

(** The assumptions and clauses of the solver combined. *)
Definition solved_clauses (solver : t) (assumptions : Assumptions.t) : Cnf.t :=
  Cnf.from_assumptions assumptions ++ clauses_of solver.

Definition atms_of (solver : t) (assumptions : Assumptions.t) : list nat :=
  Cnf.atms_of (solved_clauses solver assumptions).

Definition every_valuation (solver : t) (assumptions : Assumptions.t) : list Valuation.t :=
  Valuation.every_valuation_of_atms (atms_of solver assumptions).

Definition In (x : nat) (solver : t) (assumptions : Assumptions.t) : Prop :=
  Cnf.In x (solved_clauses solver assumptions).

Definition clause_atms_in (clause : CplClause.t) (solver : t) (assumptions : Assumptions.t) : Prop :=
  forall x, CplClause.In x clause -> In x solver assumptions.

(** Adding a clause to the solver adds it to the [clauses_of]. *)
(* Axiom add_clause_cons :
  forall (s : t) (clause : CplClause.t), clauses_of (add_clause s clause) = clause :: clauses_of s. *)

(* TODO: add axioms about the valuation and unsat core specifically. *)

Class solver_axioms (solver : t) :=
{
  add_clause_cons : forall (clause : CplClause.t),
    clauses_of (add_clause solver clause) = clause :: clauses_of solver;

  valuation_clash_free : forall assumptions val,
    Solution.Sat val = solve_with_assumptions solver assumptions ->
    Valuation.clash_free val;

  valuation_in_clauses : forall assumptions val,
    Solution.Sat val = solve_with_assumptions solver assumptions ->
    forall x, Valuation.In x val <-> In x solver assumptions;

  core_subset_assumptions : forall assumptions core,
    Solution.Unsat core = solve_with_assumptions solver assumptions ->
    List.incl core assumptions;

  solution_correctness : forall assumptions, match solve_with_assumptions solver assumptions with
    (* this valuation makes it true *)
    | Solution.Sat val =>
      forall W R (M : @Kripke.t W R) (w0 : W),
        Valuation.matches_kripke_valuation val M w0 ->
        Cnf.force M w0 (solved_clauses solver assumptions)

    (* solver clauses ++ *unsat core* is also unsat *)
    (* the fact that solver ++ *assumptions* is unsat follows from this. *)
    | Solution.Unsat core =>
      Cnf.unsatisfiable (solved_clauses solver core)
    end;
}.

(** The empty SAT-solver contains no clauses. *)
Axiom make_is_empty : clauses_of make = [].
Axiom axioms_make : solver_axioms make.
Axiom axioms_ind : forall solver clause,
  solver_axioms solver -> solver_axioms (add_clause solver clause).

(** make_with_clauses also satisfies solver axioms. *)
Local Lemma axioms_clauses' : forall (solver : t) (phi : Cnf.t),
  solver_axioms solver -> solver_axioms (List.fold_left add_clause phi solver).
Proof.
  intros solver phi. revert solver.
  induction phi as [|head tail IH]; intros solver Hsolver.
  - cbn. assumption.
  - cbn. apply IH. apply axioms_ind. assumption.
Qed.

Lemma axioms_clauses : forall (phi : Cnf.t), solver_axioms (make_with_clauses phi).
Proof.
  intro phi.
  unfold make_with_clauses.
  apply axioms_clauses'. apply axioms_make.
Qed.

(** A SAT valuation is in every valuation of the solver. *)
Lemma valuation_in_every_valuation_of :
  forall (solver : t) (assumptions : Assumptions.t) (valuation : Valuation.t),
  solver_axioms solver ->
  Solution.Sat valuation = solve_with_assumptions solver assumptions ->
  SetoidList.InA Valuation.eq
      valuation
      (every_valuation solver assumptions).
Proof.
  intros solver assumptions val Hsolver Hsat.
  unfold every_valuation, atms_of.
  set (atms := Cnf.atms_of _).
  pose proof (valuation_clash_free _ _ Hsat) as Hsound.
  apply Valuation.val_of_atms_in_every_valuation.
  (* atms is permutation of atms of val *)
  apply Permutation.NoDup_Permutation.
  - unfold atms, Cnf.atms_of. apply List.NoDup_nodup.
  - apply Valuation.atms_of_nodup. exact Hsound.
  - setoid_rewrite (valuation_in_clauses assumptions val Hsat).
    setoid_rewrite Cnf.in_atms_of. fold atms. reflexivity.
Qed.


(* A solver with an added clause that contains no new atoms has the same set of atoms *)
Lemma add_no_new_atms :
  forall (solver : t) (clause : CplClause.t) (assumptions : Assumptions.t),
  solver_axioms solver ->
  clause_atms_in clause solver assumptions ->
  Permutation (atms_of solver assumptions) (atms_of (add_clause solver clause) assumptions).
Proof with auto.
  intros solver new_clause assumptions Hsolver Hclause_incl.

  unfold atms_of, solved_clauses in *.
  rewrite add_clause_cons.

  apply NoDup_Permutation.
  - apply List.NoDup_nodup.
  - apply List.NoDup_nodup.
  - intro x. split.
    (* in assumptions ++ clauses -> in assumptions ++ new_clause :: clauses *)
    + intro Hx_in_solver.
      (* simplify nodup and flatmap *)
      apply List.nodup_In. apply List.nodup_In in Hx_in_solver.
      apply List.in_flat_map. apply List.in_flat_map in Hx_in_solver.
      destruct Hx_in_solver as [clause [Hclause_in_clauses Hx_in_clause]].
      exists clause. split...

      (* in a ++ b -> in a ++ c :: b *)
      rewrite List.in_app_iff in Hclause_in_clauses.
      destruct Hclause_in_clauses as [Hclause_in_assumps | Hclause_in_solver].
      * apply List.in_app_iff. now left.
      * apply List.in_app_iff. right. now apply List.in_cons.
    (* in assumptions ++ clauses <- in assumptions ++ new_clause :: clauses *)
    + intro Hx_in_solver'.
      (* simplify nodup and flatmap *)
      apply List.nodup_In in Hx_in_solver'.
      apply List.in_flat_map in Hx_in_solver'.
      destruct Hx_in_solver' as [clause [Hclause_in_clauses Hx_in_clause]].

      (* split into 3 cases, two are almost identical, so reorder to simplify *)
      rewrite List.in_app_iff in Hclause_in_clauses. cbn in Hclause_in_clauses.
      apply or_comm, or_assoc in Hclause_in_clauses.
      destruct Hclause_in_clauses as [Heq_new | Hin_existing].
      (* x in new clause *)
      * subst clause. unfold In in Hclause_incl.
        apply Cnf.in_atms_of. apply Hclause_incl.
        cbn. assumption.
      (* x in solver or assumptions *)
      * apply List.nodup_In. apply List.in_flat_map.
        exists clause. split... apply List.in_app_iff.
        intuition.
Qed.


(** If the core is unsatisfiable, then all assumptions are unsatisfiable. *)
Lemma unsat_core_unsat_assumptions : forall (phi : Cnf.t) (assumptions : Assumptions.t) (core : Assumptions.t),
  List.incl core assumptions ->
  Cnf.unsatisfiable (Cnf.from_assumptions core ++ phi) ->
  Cnf.unsatisfiable (Cnf.from_assumptions assumptions ++ phi).
Proof.
Admitted.


(** Checking that the axioms are reasonable. *)
Lemma solver_correctness : forall (phi : Cnf.t) (assumptions : Assumptions.t),
  Cnf.satisfiable (Cnf.from_assumptions assumptions ++ phi) <->
  Solution.is_sat (solve_with_assumptions (make_with_clauses phi) assumptions) = true.
Proof.
  intros phi.
  induction phi as [| head tail IHtail].
  - intros assumptions.
    cbn. split.
    + rewrite contrapositive.
      intro Hunsat.
      pose proof (@solution_correctness make axioms_make assumptions).
      set (s := solve_with_assumptions make assumptions) in *.
      (* solution must be unsat *)
      destruct s as [val | core].
      { cbn in Hunsat. contradiction. }
Admitted.

Lemma subset_unsat_unsat : forall (phi psi : Cnf.t),
  List.incl phi psi ->
  Cnf.unsatisfiable phi ->
  Cnf.unsatisfiable psi.
Proof.
Admitted.

(* if two solvers have the same set of atoms, they must have the same set of valuations *)
Lemma same_atms_valuation_set :
  forall (solvera solverb : t) (assumptions : Assumptions.t),
  solver_axioms solvera -> solver_axioms solverb ->
  Permutation.Permutation (atms_of solvera assumptions) (atms_of solverb assumptions) ->
  Permutation.Permutation (every_valuation solvera assumptions) (every_valuation solverb assumptions).
Proof.
Admitted.

(*

axioms:
- unsat core is a subset of the assumptions
- make a negate_all thingy
PROOF:
- if i give it negate_all(core), then the new unsat core cannot equal the old unsat core.
-
*)