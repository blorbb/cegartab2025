(** An assumed classical SAT-solver oracle.

    We define [Parameter] types and functions which must be filled in during
    program extraction. They must also satisfy the axioms as defined in
    [solver_axioms].

    See the Extract module for details about our Minisat implementation.

    * Caveats


    We allow the SAT-solver to have mutable state. Mutability is not easy
    to formalise in Rocq (though {{https://softwarefoundations.cis.upenn.edu/plf-current/References.html} possible}).
    Our functions are defined as though the SAT-solver is immutable
    (as we return a new solver on [make] / [add_clause]).

    For our implementation to be correct, we must _manually_ ensure that
    we never use a mutated solver, i.e. a solver that has been used
    as input to [add_clause]. We must also be careful with how the solver is
    used, as referential transparency is lost.

    Future work to resolve this issue: wrap the solver in a monad.
    Something similar to {{https://github.com/Lysxia/coq-simple-io} coq-simple-io}
    may help with extracting to use the [IO] monad. *)

From Stdlib Require List.
From CegarTableaux Require CplClause Assumptions Lit Cnf Valuation.
From CegarTableaux Require Import Utils.
From CegarTableaux.CplSolver Require Solution.
From Stdlib Require Import Permutation SetoidPermutation SetoidList.
Import List.ListNotations.
Open Scope list_scope.


(** A (possibly stateful) classical SAT-solver oracle. *)
Parameter t : Type.


(** Creates a new SAT-solver.

    This has a slightly odd type because the solver is technically mutable.
    This must be a function since we can create multiple distinct instances
    of a SAT solver; being a constant (e.g. just [t]) would not work as all
    solvers would then be the same instance. *)
Parameter make : unit -> t.


(** Add a clause to the solver, returning the new solver.

    See module documentation for caveats. *)
Parameter add_clause : t -> CplClause.t -> t.


(** Determines the satisfiability of the provided solver state under a set of
    unit assumptions.

    The solver state is unchanged by this function call. *)
Parameter solve_with_assumptions : t -> Assumptions.t -> Solution.t.


(** Create a new solver with the provided CNF clauses. *)
Definition make_with_clauses (clauses : Cnf.t) : t :=
  List.fold_left add_clause clauses (make tt).


(** * Axioms *)

(** All clauses which have been added to this solver.

    This parameter is not (and should not) be used by the algorithm
    implementation. It is only used to describe the axioms of the solver. *)
Parameter clauses_of : t -> Cnf.t.


(** The assumptions and clauses of the solver combined.

    Returns the equivalent CNF formula that the solver is determining the
    satisfiability for (including the unit assumptions). *)
Definition solved_clauses (solver : t) (assumptions : Assumptions.t) : Cnf.t :=
  Cnf.from_assumptions assumptions ++ clauses_of solver.


(** Set of atoms that are in the solver or assumptions. *)
Definition atms_of (solver : t) (assumptions : Assumptions.t) : list nat :=
  Cnf.atms_of (solved_clauses solver assumptions).


(** Returns every possible valuation that can be created by the atoms of the
    solver and assumptions. *)
Definition every_valuation (solver : t) (assumptions : Assumptions.t) : list Valuation.t :=
  Valuation.every_valuation_of_atms (atms_of solver assumptions).


Definition In (x : nat) (solver : t) (assumptions : Assumptions.t) : Prop :=
  Cnf.In x (solved_clauses solver assumptions).


(** Whether a clause does not introduce new atoms to the solver. *)
Definition clause_atms_incl (clause : CplClause.t) (solver : t) (assumptions : Assumptions.t) : Prop :=
  forall x, CplClause.In x clause -> In x solver assumptions.

Arguments clause_atms_incl clause solver assumptions /.


(** The correctness assumptions we make about the SAT solver. *)
Class solver_axioms (solver : t) :=
{
  (** [add_clause solver clause] correctly adds [clause] to the
      clauses of [solver]. *)
  add_clause_cons : forall (clause : CplClause.t),
    clauses_of (add_clause solver clause) = clause :: clauses_of solver;

  (** The valuation returned by a satisfiable result is [clash_free]. *)
  valuation_clash_free : forall assumptions val,
    Solution.Sat val = solve_with_assumptions solver assumptions ->
    Valuation.clash_free val;

  (** Every atom in the valuation is an atom in the solver or assumptions. *)
  valuation_in_clauses : forall assumptions val,
    Solution.Sat val = solve_with_assumptions solver assumptions ->
    forall x, Valuation.In x val <-> In x solver assumptions;

  (** The valuation is a superset of the assumptions *)
  valuation_supset_assumptions : forall assumptions val,
    Solution.Sat val = solve_with_assumptions solver assumptions ->
    List.incl assumptions val;

  (** The unsatisfiable core is a subset of the unit assumptions. *)
  core_subset_assumptions : forall assumptions core,
    Solution.Unsat core = solve_with_assumptions solver assumptions ->
    List.incl core assumptions;

  (** The valuation satisfies the solver clauses. *)
  solution_soundness : forall assumptions val,
    Solution.Sat val = solve_with_assumptions solver assumptions ->
    exists W R (M : @Kripke.t W R) (w0 : W),
      Valuation.matches_kripke_valuation val M w0 /\
      Cnf.force M w0 (clauses_of solver);

  (** The solver + unsatisfiable core is still unsatisfiable. *)
  solution_completeness : forall assumptions core,
    Solution.Unsat core = solve_with_assumptions solver assumptions ->
    Cnf.unsatisfiable (solved_clauses solver core)
}.


(** The empty SAT-solver contains no clauses. *)
Axiom make_is_empty : clauses_of (make tt) = [].


(** [axioms_make] and [axioms_ind] define which solvers satisfy the axioms.

    This isn't strictly necessary as [make] and [add_clause] is the only way
    you can create a solver instance. These axioms enforce that only solvers
    created by [make] and [add_clause] satisfy the solvers, to ensure that
    we can't accidentally make a solver through some other means. *)
Axiom axioms_make : solver_axioms (make tt).

Axiom axioms_ind : forall solver clause,
  solver_axioms solver -> solver_axioms (add_clause solver clause).


(** Applying [List.fold_left] on a solver also satisfies axioms. *)
Lemma axioms_fold_left : forall (solver : t) (phi : Cnf.t),
  solver_axioms solver -> solver_axioms (List.fold_left add_clause phi solver).
Proof.
  intros solver phi. revert solver.
  induction phi as [|head tail IH]; intros solver Hsolver.
  - cbn. assumption.
  - cbn. apply IH. apply axioms_ind. assumption.
Qed.


(** [make_with_clauses] also satisfies solver axioms. *)
Lemma axioms_clauses : forall (phi : Cnf.t), solver_axioms (make_with_clauses phi).
Proof.
  intro phi.
  unfold make_with_clauses.
  apply axioms_fold_left. apply axioms_make.
Qed.


(** The clauses that the solver will hold from a [List.fold_left] of clauses. *)
Lemma clauses_of_fold_left : forall solver clauses,
  solver_axioms solver ->
  clauses_of (List.fold_left add_clause clauses solver) = (List.rev clauses) ++ clauses_of solver.
Proof with try easy.
  intros solver clauses. revert solver.
  induction clauses as [|h t IH]; intros solver Hsolver.
  { reflexivity. }
  cbn.
  specialize (IH (add_clause solver h)).
  forward IH by apply axioms_ind...
  rewrite add_clause_cons in IH.
  rewrite <- List.app_assoc. cbn. exact IH.
Qed.


Lemma atms_of_nodup : forall solver assumptions, List.NoDup (atms_of solver assumptions).
Proof.
  intros. unfold atms_of, Cnf.atms_of. apply List.NoDup_nodup.
Qed.


Lemma every_valuation_nodup : forall solver assumptions, NoDupA Valuation.eq (every_valuation solver assumptions).
Proof.
  intros. apply Valuation.every_valuation_unique, atms_of_nodup.
Qed.


(** A satisfiable valuation is in [every_valuation] of the solver. *)
Lemma valuation_in_every_valuation_of :
  forall (solver : t) (assumptions : Assumptions.t) (valuation : Valuation.t),
  solver_axioms solver ->
  Solution.Sat valuation = solve_with_assumptions solver assumptions ->
  InA Valuation.eq
      valuation
      (every_valuation solver assumptions).
Proof.
  intros solver assumptions val Hsolver Hsat.
  unfold every_valuation, atms_of.
  set (atms := Cnf.atms_of _).
  pose proof (valuation_clash_free _ _ Hsat) as Hsound.
  apply Valuation.val_with_atms_in_every_val.
  (* atms is permutation of atms of val *)
  apply NoDup_Permutation.
  - unfold atms, Cnf.atms_of. apply List.NoDup_nodup.
  - apply Valuation.atms_of_nodup. exact Hsound.
  - setoid_rewrite (valuation_in_clauses assumptions val Hsat).
    setoid_rewrite Cnf.in_atms_of. fold atms. reflexivity.
Qed.


(** A solver with an added clause that contains no new atoms has the same set of atoms *)
Lemma add_no_new_atms :
  forall (solver : t) (clause : CplClause.t) (assumptions : Assumptions.t),
  solver_axioms solver ->
  clause_atms_incl clause solver assumptions ->
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


(** Adds a list of literals interpreted as a conflict set.

    [conflict_set] should be a subset of a previous valuation.
    [add_conflict_set] will add a clause requiring that at least one of these
    literals must be different if the next solution is also satisfiable. *)
Definition add_conflict_set solver conflict_set := add_clause solver (List.map Lit.negate conflict_set).


(** If [val] = solution of [solver] and [val'] = solution of [solver']
    where [solver'] contains the conflict set as one of it's clauses,
    then [val] and [val'] cannot be equal. *)
Lemma refined_solver_diff_val : forall solver assumptions val conflict_set solver' val',
  solver_axioms solver ->
  solver_axioms solver' ->
  Solution.Sat val = solve_with_assumptions solver assumptions ->
  List.incl conflict_set val ->
  conflict_set <> [] ->
  List.In (List.map Lit.negate conflict_set) (clauses_of solver') ->
  Solution.Sat val' = solve_with_assumptions solver' assumptions ->
  ~ Valuation.eq val val'.
Proof with auto; try easy.
  intros solver assumptions val conflict_set solver' val' Hsolver Hsolver' Hval Hcs_val Hcs_nonempty Hcs_in_solver' Hval'.
  (* need to prove by contradiction *)
  intro Heq.
  pose proof (@solution_soundness solver' Hsolver' assumptions val' Hval') as Hsound.
  (* -> forces solved_clauses (added conflict set). *)
  (* but conflict set subset of val' so it cannot match the kripke valuation. *)

  destruct Hsound as [W [R [M [w0 [Hval_match Hforce]]]]].

  (* M w0 |= clauses_of solver' *)
  (* isolate just the conflict set *)
  cbn in Hforce.
  unfold Cnf.force in Hforce.
  rewrite List.Forall_forall in Hforce.
  specialize (Hforce (List.map Lit.negate conflict_set) Hcs_in_solver').

  (* forcing ~conflict set -> ~l in conflict set *)
  (* but +l in conflict set because conflict set subset of val. *)
  cbn in Hforce. destruct Hforce as [l [Hl_in_cs Hforce_l]].
  replace_hyp Hl_in_cs with (List.In (Lit.negate l) conflict_set).
  {
    apply List.in_map with (f:=Lit.negate) in Hl_in_cs.
    rewrite List.map_map in Hl_in_cs.
    setoid_rewrite Lit.negate_involution in Hl_in_cs.
    rewrite List.map_id in Hl_in_cs.
    assumption.
  }

  (* ~l in val' *)
  apply Hcs_val in Hl_in_cs.
  apply Permutation_in with (l' := val') in Hl_in_cs...
  rename Hl_in_cs into Hnl_in_val'.

  unfold Valuation.matches_kripke_valuation in Hval_match.

  (* Hnl_in_val' and Hforce_l form a contradiction. *)
  destruct l as [p|p]; cbn in Hforce_l, Hnl_in_val'.
  - apply (Valuation.clash_free_no_negation (Lit.Pos p) val')...
    + apply valuation_clash_free with assumptions...
    + apply Hval_match...
      apply (Valuation.lit_in_atm_in (Lit.Neg p))...
  - apply Hforce_l. apply Hval_match...
    apply (Valuation.lit_in_atm_in (Lit.Pos p))...
Qed.


(** If two solvers have the same set of atoms, they must have the same set
    of possible valuations. *)
Lemma same_atms_valuation_set :
  forall (solvera solverb : t) (assumptions : Assumptions.t),
  solver_axioms solvera -> solver_axioms solverb ->
  Permutation (atms_of solvera assumptions) (atms_of solverb assumptions) ->
  PermutationA Valuation.eq (every_valuation solvera assumptions) (every_valuation solverb assumptions).
Proof.
  intros solvera solverb assumptions Hsolvera Hsolverb Hatms_perm.
  unfold every_valuation. now apply Valuation.every_valuation_perm.
Qed.

