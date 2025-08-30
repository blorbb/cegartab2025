(** CEGARBox SAT-solver.

    We make heavy use of Program Fixpoint/Definition.

    Program Fixpoint allows us to prove that a fixpoint terminates with a custom
    well-founded measurement, and generates obligations to show that every
    recursive call is indeed a strict decrease of the measurement.

    Program also allows us to leave 'holes' in places where propositions are expected.
    We can then fill in these holes as obligations, so that we can actually
    use the proof language rather than trying to do some stuff with function application. *)

From Stdlib Require List SetoidList.
Import List.ListNotations.
Open Scope list_scope.
From Stdlib Require Import Relations Program Wellfounded Lia RelationClasses Permutation SetoidPermutation FunInd Recdef PeanoNat Nat.
From CegarTableaux Require CplSolver Lit Mchain Assumptions Valuation.
From CegarTableaux Require Import Utils ListExt.

(** A CEGARBox sat/unsat solution. *)
Module Solution.
  Inductive t : Type :=
    | Sat
    | Unsat (core : Assumptions.t).
End Solution.


(** * Conflict set lemmas *)

(** Creates a conflict set. *)
Definition conflict_set_of w0 solver_val dia_antecedent core :=
  let fired_box_clauses :=
    Lclauses.boxes w0
      |> List.filter (fun box => Valuation.forces_lit solver_val (fst box)) 
  in
    fired_box_clauses
      |> List.filter (fun box => List.existsb (Lit.eqb (snd box)) core)
      |> List.map fst
      |> cons dia_antecedent.


(** The learned clause that should be added. The negation of a conflict set. *)
Definition learned_clause_of w0 solver_val dia_antecedent core :=
  (* negate and interpret as CPL clause *)
  List.map Lit.negate (conflict_set_of w0 solver_val dia_antecedent core).


(** The conflict set is a subset of the valuation. *)
Lemma conflict_set_incl_val : forall w0 val dia_antecedent core solver assumptions,
  CplSolver.solver_axioms solver ->
  CplSolver.Solution.Sat val = CplSolver.solve_with_assumptions solver assumptions ->
  Valuation.forces_lit val dia_antecedent = true ->
  let conflict_set := conflict_set_of w0 val dia_antecedent core in
  List.incl conflict_set val.
Proof.
  intros w0 val dia_antecedent core solver assumptions Hsolver Hval Hforce_ante conflict_set.
  unfold conflict_set, conflict_set_of, "|>". intros x Hx_in_cs.
  cbn in Hx_in_cs. destruct Hx_in_cs as [Hante | Hin].
  - subst x.
    unfold Valuation.forces_lit in Hforce_ante.
    apply List.existsb_exists in Hforce_ante as [l [Hl_in_val Heq_ante]].
    apply Lit.eqb_eq in Heq_ante. subst l. assumption.
  - setoid_rewrite List.in_map_iff in Hin.
    destruct Hin as [pair [Hfst_x Hpair_in]].

    (* remove the two filters *)
    (* first filter doesn't matter, second filter shows that (fst box) is in solver val *)
    apply List.incl_filter in Hpair_in.
    apply List.filter_In in Hpair_in.
    destruct Hpair_in as [_ Hin].

    unfold Valuation.forces_lit in Hin.
    apply List.existsb_exists in Hin as [l [Hl_in_val Heq_ante]].
    apply Lit.eqb_eq in Heq_ante. subst l x. assumption.
Qed.


(** Adding a subset of a CPL solver valuation adds no new atoms to the solver state. *)
Lemma val_subset_no_new_atms : forall solver assumptions val subset,
  CplSolver.solver_axioms solver ->
  CplSolver.Solution.Sat val = CplSolver.solve_with_assumptions solver assumptions ->
  List.incl subset val ->
  CplSolver.clause_atms_incl (List.map Lit.negate subset) solver assumptions.
Proof with auto.
  intros solver assumptions val subset Hsolver Hval Hsubset.
  unfold List.incl in Hsubset.
  cbn. intros x Hx_in_subset. 
  rewrite <- CplSolver.valuation_in_clauses with (val:=val)... cbn.

  rewrite List.map_map in Hx_in_subset. setoid_rewrite Lit.negate_eq_atm in Hx_in_subset.
  rewrite List.in_map_iff in *.
  destruct Hx_in_subset as [l [Hlx Hl_in_subset]]. subst x.
  exists l. auto.
Qed.


(** Adding the learned clause adds no new atoms to the solver state. *)
Corollary learned_clause_no_new_atms : forall w0 solver assumptions val c core,
  CplSolver.solver_axioms solver ->
  CplSolver.Solution.Sat val = CplSolver.solve_with_assumptions solver assumptions ->
  Valuation.forces_lit val c = true ->
  let learned_clause := learned_clause_of w0 val c core in
  CplSolver.clause_atms_incl learned_clause solver assumptions.
Proof with auto.
  intros w0 solver assumptions val c core Hsolver Hval Hc learned_clause.

  subst learned_clause. unfold learned_clause_of.
  apply val_subset_no_new_atms with val...
  apply conflict_set_incl_val with solver assumptions...
Qed.


(** An old valuation is in the learned solver's set of possible valuations. *)
Lemma failed_val_in_solver'_vals : forall val solver assumptions conflict_set,
  CplSolver.solver_axioms solver ->
  CplSolver.Solution.Sat val = CplSolver.solve_with_assumptions solver assumptions ->
  List.incl conflict_set val ->
  let solver' := CplSolver.add_conflict_set solver conflict_set in
  SetoidList.InA Valuation.eq val (CplSolver.every_valuation solver' assumptions).
Proof with try easy; auto.
  intros val solver assumptions conflict_set Hsolver Hval Hcs_incl solver'.
  apply PermutationA_inA with (l:=CplSolver.every_valuation solver assumptions).
  - exact Valuation.eq_equivalence.
  - apply Valuation.every_valuation_perm.
    subst solver'.
    apply CplSolver.add_no_new_atms...
    apply val_subset_no_new_atms with (val:=val)...
  - apply CplSolver.valuation_in_every_valuation_of...
Qed.


(** * Conditions maintained through recursions *)

(** Get the CPL clauses of the first modal context. *)
Definition first_cpls (chain : Mchain.t) := match chain with
  | [] => []
  | w0 :: _ => Lclauses.cpls w0
  end.


(** A valuation attempt. *)
Module VA.
  Record t := make {
    (* The valuation that was attempted. *)
    val_attempt : Valuation.t;
    (* The conflict set generated from the attempted valuation. *)
    conflict_set : list Lit.t;
    Hcs_ne : conflict_set <> [];
    Hcs_incl : List.incl conflict_set val_attempt;
  }.

  (** Make a CPL solver from the valuation history.

      Making this custom instead of using [List.fold_right] as it makes
      the [cbn]s more useful *)
  Fixpoint make_solver (phi : Cnf.t) (hist : list t) : CplSolver.t :=
    match hist with
    | [] => CplSolver.make_with_clauses phi
    | h :: t => CplSolver.add_conflict_set (make_solver phi t) (VA.conflict_set h)
    end.

  Lemma make_solver_axioms : forall phi hist,
    CplSolver.solver_axioms (make_solver phi hist).
  Proof.
    intros phi hist. induction hist as [|h t IH].
    - cbn. apply CplSolver.axioms_clauses.
    - cbn. now apply CplSolver.axioms_ind.
  Qed.

  (** A proposition requiring that every valuation attempt was created 
      by the valuation history of all other attempts. *)
  Fixpoint attempts_from_solutions (assumptions : Assumptions.t) (phi : Cnf.t) (hist : list t) : Prop :=
    match hist with
    | [] => True
    | h :: t =>
      CplSolver.Solution.Sat (val_attempt h) = CplSolver.solve_with_assumptions (make_solver phi t) assumptions /\
      attempts_from_solutions assumptions phi t
    end.
End VA.


(** Conditions for [cegar_box_jumps]. *)
Module JumpConds.
  Record t assumptions w0  solver val  (val_hist : list VA.t) := {
    solver_from_val_hist :
      solver = VA.make_solver (Lclauses.cpls w0) val_hist;

    solver_sat_val :
      CplSolver.Solution.Sat val = CplSolver.solve_with_assumptions solver assumptions;

    attempts_from_solutions :
      VA.attempts_from_solutions assumptions (Lclauses.cpls w0) val_hist;

    val_hist_nodup :
      SetoidList.NoDupA Valuation.eq (List.map VA.val_attempt val_hist);

    val_hist_incl_solver :
      SetoidList.inclA Valuation.eq
        (ListDef.map VA.val_attempt val_hist)
        (CplSolver.every_valuation solver assumptions);

    val_not_in_hist :
      ~ SetoidList.InA Valuation.eq val (List.map VA.val_attempt val_hist);
  }.
End JumpConds.


(** Conditions for [cegar_box]. *)
Module LocalConds.
  Record t assumptions phi solver val_hist := {
    solver_from_val_hist :
      solver = VA.make_solver (first_cpls phi) val_hist;

    attempts_from_solutions :
      VA.attempts_from_solutions assumptions (first_cpls phi) val_hist;

    val_hist_nodup :
      SetoidList.NoDupA Valuation.eq (List.map VA.val_attempt val_hist);

    val_hist_incl_solver :
      SetoidList.inclA Valuation.eq
        (ListDef.map VA.val_attempt val_hist)
        (CplSolver.every_valuation solver assumptions);
  }.
End LocalConds.


(** The valuation history is a subset of every possible valuation. *)
Lemma val_hist_incl_solver' : forall solver assumptions val_hist val conflict_set,
  CplSolver.solver_axioms solver ->
  CplSolver.Solution.Sat val = CplSolver.solve_with_assumptions solver assumptions ->
  List.incl conflict_set val ->
  SetoidList.inclA Valuation.eq
    (List.map VA.val_attempt val_hist)
    (CplSolver.every_valuation solver assumptions) ->
  let solver' := CplSolver.add_conflict_set solver conflict_set in
  SetoidList.inclA Valuation.eq
    (List.map VA.val_attempt val_hist)
    (CplSolver.every_valuation solver' assumptions).
Proof with auto.
  intros solver assumptions val_hist val conflict_set Hsolver Hval Hcs_incl Hincla solver'.

  apply PermutationA_inclA with (l:=CplSolver.every_valuation solver assumptions).
  - exact Valuation.eq_equivalence.
  - apply Valuation.every_valuation_perm.
    unfold solver'. apply CplSolver.add_no_new_atms...
    apply val_subset_no_new_atms with (val:=val)...
  - assumption.
Qed.


(** A new valuation is not equal to any other valuation in the valuation history.

    [extra_constraints] is required to strengthen the IH, creating a [solver']
    that is over-abstracted. *)
Lemma new_val_not_in_hist : forall assumptions val_hist w0 val extra_constraints,
  let solver := VA.make_solver (Lclauses.cpls w0) val_hist in
  let solver' := List.fold_left CplSolver.add_clause extra_constraints solver in
  VA.attempts_from_solutions assumptions (Lclauses.cpls w0) val_hist ->
  SetoidList.NoDupA Valuation.eq (ListDef.map VA.val_attempt val_hist) ->
  SetoidList.inclA Valuation.eq (ListDef.map VA.val_attempt val_hist) (CplSolver.every_valuation solver assumptions) ->
  CplSolver.Solution.Sat val = CplSolver.solve_with_assumptions solver' assumptions ->
  ~ SetoidList.InA Valuation.eq val (List.map VA.val_attempt val_hist).
Proof with try easy; auto using Valuation.eq_equivalence.
  intros assumptions val_hist. revert assumptions.
  induction val_hist as [|hd tl IH];
    intros assumptions w0 val extra_constraints solver solver' Hatts_from_sols Hnodup Hincl Hval.
  { cbn. now rewrite SetoidList.InA_nil. }
  (* split the solver into solver of tl then solver := solvertl + clause *)
  cbn in solver.
  set (solvertl := VA.make_solver _ _) in solver.
  assert (CplSolver.solver_axioms solvertl) as Hsolvertl by apply VA.make_solver_axioms.
  assert (CplSolver.solver_axioms solver) as Hsolver. { unfold solver. apply CplSolver.axioms_ind... }
  assert (CplSolver.solver_axioms solver') as Hsolver'. { unfold solver'. apply CplSolver.axioms_fold_left... }

  intro Hval_in. rewrite List.map_cons in Hval_in.
  apply SetoidList.InA_cons in Hval_in as [Hhd | Htl].
  (* head cannot equal new valuation *)
  - apply (CplSolver.refined_solver_diff_val solvertl assumptions (VA.val_attempt hd) (VA.conflict_set hd) solver' val).
    + exact Hsolvertl.
    + exact Hsolver'.
    + destruct hd; cbn in *.
      apply (proj1 Hatts_from_sols).
    + destruct hd; cbn in *. assumption.
    + destruct hd; cbn in *.
      intro Hva_empty. subst conflict_set. contradiction.
    + subst solver' solver.
      unfold CplSolver.add_conflict_set.
      induction extra_constraints.
      * cbn. rewrite CplSolver.add_clause_cons. cbn. now left.
      * rewrite CplSolver.clauses_of_fold_left.
        2: { apply CplSolver.axioms_ind... }
        apply List.in_app_iff. right.
        rewrite CplSolver.add_clause_cons. cbn. now left.
    + fold solver solver'. assumption.
    + symmetry. assumption.

  - rewrite List.map_cons in *.
    (* with extra constraint of the new clause. *)
    specialize (IH assumptions w0 val ((List.map Lit.negate (VA.conflict_set hd)) :: extra_constraints)).

    apply IH.
    + cbn in Hatts_from_sols. apply (proj2 Hatts_from_sols).
    + apply cons_NoDupA in Hnodup. assumption.
    + apply inclA_cons in Hincl... apply proj2 in Hincl.
      fold solvertl.
      apply PermutationA_inclA with (l := CplSolver.every_valuation solver assumptions)...
      apply Valuation.every_valuation_perm.
      subst solver'. symmetry. apply CplSolver.add_no_new_atms...
      apply val_subset_no_new_atms with (val:=(VA.val_attempt hd))...
      * cbn in Hatts_from_sols.
        apply (proj1 Hatts_from_sols).
      * destruct hd; cbn in *. assumption.
    + clear -Hval. rewrite Hval.
      fold solvertl. subst solver' solver.
      cbn. unfold CplSolver.add_conflict_set. reflexivity.
    + assumption.
Qed.


(** * Measurement *)

(** Lexicographic ordering of a pair of naturals. *)
Definition lexnat2_lt : nat * nat -> nat * nat -> Prop :=
  slexprod _ _ lt lt.

(** [lexnat2_lt] is well-founded. *)
Lemma lexnat2_lt_wf : well_founded lexnat2_lt.
Proof.
  unfold lexnat2_lt.
  apply wf_slexprod; apply Wf_nat.lt_wf.
Qed.


(** Default auto-solver simplifies a bit too much. *)
Local Obligation Tactic := intros; try solve [ cbn; auto ].


(** * CEGARBox implementation and proof *)

Program Fixpoint cegar_box_jumps
  (assumptions : Assumptions.t)
  (w0 : Lclauses.t)
  (tail : Mchain.t)
  (solver : CplSolver.t)
  (valuation : Valuation.t)
  (dias : list DiaClause.t)
  (val_hist : list VA.t)
  (conds : JumpConds.t assumptions w0 solver valuation val_hist)
  (cegar_box :
    forall inp_assumps inp_phi inp_solver inp_val_hist (inp_ctconds : LocalConds.t inp_assumps inp_phi inp_solver inp_val_hist),
    lexnat2_lt
      (length inp_phi,    length (CplSolver.every_valuation inp_solver inp_assumps) - length inp_val_hist)
      (length (w0::tail), length (CplSolver.every_valuation solver assumptions)     - length val_hist)
    -> Solution.t
  )
  {measure (
    List.length tail,
    List.length dias
  ) lexnat2_lt}
  : Solution.t
  :=
  match dias with
  (* no more dia-clauses: every diamond has been fulfilled, SAT base case. *)
  | [] => Solution.Sat
  (* extra clauses and extra dias *)
  | (c, d) :: dias' =>
    let clause_is_fired := Valuation.forces_lit valuation c in
    match clause_is_fired with  (* if statements are more complicated when proving obligations *)
    (* unfired dia clause: just go to next dia clause *)
    (* recursion: NEXT UNFIRED *)
    | false =>
      cegar_box_jumps assumptions w0 tail solver valuation dias' val_hist _ cegar_box

    | true =>
      (* this clause has been fired. *)

      (* TODO: make this an input to the function? *)
      let fired_box_clauses :=
        (* for each box clause a -> []b, *)
        Lclauses.boxes w0
        (* filter for [a] (fst box) in the valuation *)
        |> List.filter (fun box => Valuation.forces_lit valuation (fst box)) in
      let fired_box_lits := List.map snd fired_box_clauses in

      let next_cpls := first_cpls tail in

      (* recursion: JUMP *)
      let jump := cegar_box
        (d :: fired_box_lits)
        tail
        (CplSolver.make_with_clauses next_cpls)
        [] _ _
        in

      match jump with
        (* JUMP success: continue with next dia *)
        (* recursion: NEXT FIRED *)
        | Solution.Sat =>
          cegar_box_jumps assumptions w0 tail solver valuation dias' val_hist _ cegar_box

        (* JUMP fail: RESTART *)
        | Solution.Unsat core =>
          (* get the conflict set: all names that fired some literal in the core *)
          let conflict_set := conflict_set_of w0 valuation c core in
          (* conflict_set is interpreted as a conjunction *)
          (* negate the whole thing to become a cpl clause, interpreted as a disjunction *)
          let solver := CplSolver.add_conflict_set solver conflict_set in
          (* recursion: RESTART *)
          cegar_box assumptions (w0::tail) solver ((VA.make valuation conflict_set _ _)::val_hist) _ _
        end
      end
  end.
(** Recursion NEXT UNFIRED: tail equal, dias decreasing *)
Next Obligation.
  right. subst dias. cbn. lia.
Qed.
(** Conditions met for above recursion. *)
Next Obligation.
  constructor.
  - cbn. now subst next_cpls.
  - cbn. apply I.
  - apply SetoidList.NoDupA_nil.
  - apply inclA_nil.
Qed.
(** Recursion JUMP: tail decreasing *)
Next Obligation.
  left. cbn. lia.
Qed.
(** Recursion NEXT FIRED: tail equal, dias decreasing *)
Next Obligation.
  right. subst dias. cbn. lia.
Qed.
(** Recursion RESTART: valid valuation attempt: conflict set non-empty *)
Next Obligation.
  subst conflict_set. symmetry. apply List.nil_cons.
Qed.
(** valid valuation attempt: conflict set subset of valuation *)
Next Obligation with auto.
  apply conflict_set_incl_val with (solver:=solver0) (assumptions:=assumptions).
  - destruct conds. subst solver0. apply VA.make_solver_axioms.
  - destruct conds. apply solver_sat_val.
  - easy.
Qed.
(** Conditions met for RESTART. *)
Next Obligation with try easy; auto.
  cbn. destruct conds.
  assert (CplSolver.solver_axioms solver0) as Hsolver. { subst solver0. apply VA.make_solver_axioms. }

  constructor; cbn.
  - subst solver solver0. unfold CplSolver.make_with_clauses. reflexivity.
  - subst solver0. split...
  - cbn. apply SetoidList.NoDupA_cons...
  - cbn. apply inclA_cons; [|split].
    + exact Valuation.eq_equivalence.
    + apply failed_val_in_solver'_vals...
      apply (conflict_set_incl_val w0 valuation c core solver0 assumptions)...
    + unfold solver.
      apply val_hist_incl_solver' with (val:=valuation)...
      apply (conflict_set_incl_val w0 valuation c core solver0 assumptions)...
Qed.
(** RESTART decreasing: tail equal, possible valuations decreasing *)
Next Obligation with try easy; auto.
  (* the actually hard part *)
  right. cbn.
  destruct conds.

  assert (CplSolver.solver_axioms solver0) as Hsolver0.
  { subst solver0. apply VA.make_solver_axioms. }

  assert (forall (n m r : nat), n = m -> r < n -> n - S r < m - r) as sub_S_lt by (intros; lia).
  apply sub_S_lt; clear sub_S_lt.

  (* Every possible valuation of solver and solver0 are equal. *)
  - subst solver. apply PermutationA_length with (eqA := Valuation.eq).
    apply CplSolver.same_atms_valuation_set...
    + apply CplSolver.axioms_ind...
    + symmetry. apply CplSolver.add_no_new_atms...
      apply learned_clause_no_new_atms...

  (* Valuation history must be strictly less than every possible valuation.

      [<=] is easy. Prove [<>] by contradiction. *)
  - apply Nat.le_neq. split.
    + rewrite <- List.length_map with (f:=VA.val_attempt).
      apply NoDupA_incl_length with (eqA := Valuation.eq).
      * exact Valuation.eq_equivalence.
      * exact val_hist_nodup.
      * apply val_hist_incl_solver' with (val:=valuation)...
        apply (conflict_set_incl_val w0 valuation c core solver0 assumptions)...

    (* length val hist [<>] length every valuation *)
    + rewrite <- List.length_map with (f:=VA.val_attempt).
      (* assume length val hist = length every valuation *)
      intro Hlength.
      (* then val hist is a permutation of every valuation *)
      assert (PermutationA Valuation.eq (List.map VA.val_attempt val_hist) (CplSolver.every_valuation solver assumptions)) as H.
      {
        apply NoDup_PermutationA_bis.
        - exact Valuation.eq_equivalence.
        - apply val_hist_nodup.
        - apply CplSolver.every_valuation_nodup.
        - apply Nat.eq_le_incl. now rewrite Hlength.
        - apply val_hist_incl_solver' with (val:=valuation)...
          apply (conflict_set_incl_val w0 valuation c core solver0 assumptions)...
      }
      (* contradiction by showing that valuation must be in val hist, but we assumed it isn't *)
      apply val_not_in_hist.
      apply PermutationA_inA with (l:=CplSolver.every_valuation solver assumptions)...
      { exact Valuation.eq_equivalence. }
      apply failed_val_in_solver'_vals...
      apply (conflict_set_incl_val w0 valuation c core solver0 assumptions)...
Qed.
(** lexnat2_lt is well founded *)
Next Obligation.
  unfold MR. apply wf_inverse_image. exact lexnat2_lt_wf.
Qed.


Program Fixpoint cegar_box
  (assumptions : Assumptions.t)
  (phi : Mchain.t)
  (solver : CplSolver.t)
  (val_hist : list VA.t)
  (conds : LocalConds.t assumptions phi solver val_hist)
  {measure (
    List.length phi,
    (* remaining number of possible valuations *)
    List.length (CplSolver.every_valuation solver assumptions) - List.length val_hist
  ) lexnat2_lt}

  : Solution.t
  :=
  match CplSolver.solve_with_assumptions solver assumptions with
  (* UNSAT base case: a subset is unsat -> whole thing must be unsat. *)
  | CplSolver.Solution.Unsat core => Solution.Unsat core
  | CplSolver.Solution.Sat valuation =>
    match phi with
    (* no more dia clauses, don't need to recurse to the next world. *)
    (* any fired box clauses would be trivially satisfiable by non-existence of next world. *)
    | [] => Solution.Sat
    | w0 :: tail =>
      cegar_box_jumps assumptions w0 tail solver valuation (Lclauses.dias w0) (val_hist) _ cegar_box
    end
  end.
(** Recursion conditions met *)
Next Obligation
  with try easy; auto using Valuation.eq_equivalence.
  subst phi filtered_var.
  destruct conds.
  constructor.
  - now subst solver.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  (* New valuation not in val hist. *)
  - clear cegar_box.
    rename Heq_anonymous into Hval.
    cbn [first_cpls] in *.
    set (extra_constraints := @nil CplClause.t).
    apply new_val_not_in_hist with assumptions w0 extra_constraints...
    + subst solver. assumption.
    + subst extra_constraints. cbn. subst solver. assumption.
Qed.
(** Definition of cegar_box matches the type def in cegar_box_jumps *)
Next Obligation.
  subst phi. reflexivity.
Qed.
(** lexnat2_lt is well founded *)
Next Obligation.
  unfold MR. apply wf_inverse_image. exact lexnat2_lt_wf.
Qed.


(** Solve a formula by applying [cegar_box] with the correct arguments. *)
Program Definition solve_mchain (phi : Mchain.t) : Solution.t :=
  let cpls := first_cpls phi in
  cegar_box [] phi (CplSolver.make_with_clauses cpls) [] _.
(** Base cases hold. *)
Next Obligation.
  constructor.
  - cbn. subst cpls. reflexivity.
  - cbn. apply I.
  - apply SetoidList.NoDupA_nil.
  - apply inclA_nil.
Qed.


(** Solve a [Fml.t] formula by converting first. *)
Definition solve_fml (phi : Fml.t) : Solution.t :=
  phi |> Nnf.from_fml |> Mcnf.from_nnf |> Mchain.from_mcnf |> solve_mchain.


(** Show the assumptions we made with [Print Assumptions solve_fml.]. This outputs:

    [[
Axioms:
  CplSolver.t :
    Type
  CplSolver.solve_with_assumptions :
    CplSolver.t -> Assumptions.t -> CplSolver.Solution.t
  CplSolver.make :
    () -> CplSolver.t
  CplSolver.clauses_of :
    CplSolver.t -> Cnf.t
  Classical_Prop.classic :
    forall P : Prop, P \/ ~ P
  CplSolver.axioms_make :
    CplSolver.solver_axioms (CplSolver.make ())
  CplSolver.axioms_ind :
    forall (solver : CplSolver.t) (clause : CplClause.t),
    CplSolver.solver_axioms solver -> CplSolver.solver_axioms (CplSolver.add_clause solver clause)
  CplSolver.add_clause :
    CplSolver.t -> CplClause.t -> CplSolver.t
    ]]

    * Future Work

    Soundness and completeness are unfinished. These theorems would look like:

    [[
Theorem soundness :
  forall (phi : Mchain.t), cegarbox phi = Solution.Sat -> Mchain.satisfiable phi.

Theorem completeness :
  forall (phi : Mchain.t), Mchain.satisfiable phi -> cegarbox phi = Solution.Sat.
    ]]

    The type of [Solution.t] would likely need to change though. *)
