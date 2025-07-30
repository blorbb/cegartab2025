(**
CEGAR-BOX SAT solver.

We make heavy use of Program Fixpoint/Definition.

Program Fixpoint allows us to prove that a fixpoint terminates with a custom
well-founded measurement, and generates obligations to show that every
recursive call is indeed a strict decrease of the measurement.

We use a Notation for the mutually recursive [cegar_box_rec]. This is because
we need to be able to see 'through' this function to the actual [process_dias]
recursive call. This way, we can actually prove that this recursive call
is decreasing. A let statement or Definition might work, but requires writing
some really big types which is annoying.

Program also allows us to leave 'holes' in places where propositions are expected.
We can then fill in these holes as obligations, so that we can actually
use the proof language rather than trying to do some stuff with function application.
*)

From Stdlib Require List SetoidList SetoidPermutation.
Import List.ListNotations.
Open Scope list_scope.
From Stdlib Require Import Relations Program Wellfounded Lia RelationClasses Permutation FunInd Recdef PeanoNat Nat.
From CegarTableaux Require SatSolver Lit Mchain Assumptions Valuation.
From CegarTableaux Require Import Utils ListExt.

Module Solution.
  Inductive t : Type :=
    | Sat
    | Unsat (core : Assumptions.t).
End Solution.

(** Function pipeline operator *)
Local Definition apply {A B} (x : A) (f : A -> B) := f x.
Local Infix "|>" := apply (at level 51, left associativity).

(** Lexicographic ordering of a triple. *)
Definition lexnat3_lt : nat * nat * nat -> nat * nat * nat -> Prop :=
  slexprod _ _ (slexprod _ _ lt lt) lt.

Lemma lexnat3_lt_wf : well_founded lexnat3_lt.
Proof.
  unfold lexnat3_lt.
  repeat apply wf_slexprod; apply Wf_nat.lt_wf.
Qed.

Lemma sub_S_lt : forall (n m r : nat), n = m -> r < n -> n - S r < m - r.
Proof.
  intros. lia.
Qed.

Lemma InA_eqA {A} {eqA} : forall (x y : A) (l : list A),
  eqA x y ->
  Equivalence eqA ->
  SetoidList.InA eqA x l <-> SetoidList.InA eqA y l.
Proof with auto.
  intros x y l HeqA_xy HeqA_trans.
  setoid_rewrite SetoidList.InA_alt.
  split.
  - intros [z [HeqA_xz Hin]].
    exists z. split...
    symmetry in HeqA_xy.
    transitivity x...
  - intros [z [HeqA_yz Hin]].
    exists z. split...
    transitivity y...
Qed.

(* TODO: Definition conflict_set_of *)


Lemma conflict_set_no_new_atms : forall w0 solver assumptions solver_val c core,
  SatSolver.solver_axioms solver ->
  SatSolver.Solution.Sat solver_val = SatSolver.solve_with_assumptions solver assumptions ->
  Valuation.forces_lit solver_val c = true ->
  let fired_box_clauses :=
    Lclauses.boxes w0
      |> List.filter (fun box => Valuation.forces_lit solver_val (fst box)) in
  let conflict_set :=
    fired_box_clauses
      |> List.filter (fun box => List.existsb (Lit.eqb (snd box)) core)
      |> List.map fst
      |> cons c in
  let new_clause := List.map Lit.negate conflict_set in
  SatSolver.clause_atms_in new_clause solver assumptions.
Proof with auto.
  intros w0 solver assumptions solver_val c core Hsolver Hsolver_val Hc fired_box_clauses conflict_set new_clause.
  unfold SatSolver.clause_atms_in, CplClause.In.
  intros x Hx.
  subst new_clause conflict_set fired_box_clauses.
  unfold "|>" in Hx. cbn in Hx.
  destruct Hx as [Hxc | Hxin].
  (* x = c *)
  - subst x.
    apply (SatSolver.valuation_in_clauses assumptions solver_val)...
    rewrite Lit.negate_eq_atm.
    apply Valuation.forces_in...
  (* x in conflict set *)
  - (* simplify the long chain of maps *)
    repeat setoid_rewrite List.in_map_iff in Hxin.
    destruct Hxin as [lx [Hlx [nlx [Hnlx [box [Hboxfst Hbox]]]]]].
    subst x lx nlx.

    (* remove the two filters *)
    (* first filter doesn't matter, second filter shows that (fst box) is in solver val *)
    apply List.incl_filter in Hbox.
    apply List.filter_In in Hbox.
    destruct Hbox as [_ Hbox].

    apply (SatSolver.valuation_in_clauses assumptions solver_val)...
    rewrite Lit.negate_eq_atm.
    apply Valuation.forces_in...
Qed.


Lemma incl_length_le : forall {A} (eqA : relation A) (l l' : list A),
  SetoidList.inclA eqA l l' ->
  SetoidList.NoDupA eqA l ->
  List.length l <= List.length l'.
Proof.
Admitted.



Local Obligation Tactic := intros; try solve [ cbn; auto ].

(* RA = Restart Attempt *)
Module RA.
  (* the valuation at a specfic restart attempt *)
  Record t := make {
    solver : SatSolver.t;
    val : Valuation.t;
  }.
End RA.

(* all restart attempts for a single world *)
Module RAs.
  Record t := {
    w0 : Lclauses.t;
    assumptions : Assumptions.t;
    (* might need dia_firer, conflict_set, unsat_core? *)
    hist : list RA.t;
  }.

  Definition cons (head : RA.t) (tail : t) := {| 
    w0 := w0 tail;
    assumptions := assumptions tail;
    hist := head :: hist tail;
  |}.

  Infix ":$:" := cons (at level 60, right associativity).

(* 
  Class Correct (ras : t) :=
  {
    nodup : SetoidList.NoDupA Valuation.eq (List.map RA.val (hist ras))
  }. *)
(* 
  Program Instance correct_init : forall w0 assumptions val,
    let solver := SatSolver.make_with_clauses (Lclauses.cpls w0) in
    SatSolver.Solution.Sat val = SatSolver.solve_with_assumptions solver assumptions ->
    Correct {|
      w0 := w0;
      assumptions := assumptions;
      hist := [{|
        RA.solver := solver;
        RA.val := val;
      |}];
    |} := {}.
  Next Obligation.
    apply SetoidList.NoDupA_singleton.
  Qed.

  Program Instance correct_ind : forall w0 assumptions ras next,
    Correct ras ->
    _ ->
    Correct (cons next ras). *)

  Inductive ok : t -> Prop :=
    | ok_fst :
      forall w0 assumptions val,
        let solver := SatSolver.make_with_clauses (Lclauses.cpls w0) in
        SatSolver.Solution.Sat val = SatSolver.solve_with_assumptions solver assumptions ->
        ok {|
          w0 := w0;
          assumptions := assumptions;
          hist := [RA.make solver val]
        |}

    (* need to define the conflict set somewhere. but how to avoid an option? *)
    | ok_cons : forall a b rest,
        ok (b :$: rest) ->
        a = a ->
        ok (a :$: b :$: rest).

End RAs.



(*
  INVARIANT: solver contains all CPL clauses of w0
*)
Notation cegar_box_rec
  assumptions (* Assumptions.t *)
  phi (* Mchain.t *)
  solver (* SatSolver.t *)
  val_hist (* list Valuation.t *)
  process_dias (* function below *)
  Hsolver Hvaluation Hval_hist_incl Hval_hist_nodup Hmeasure
  (* : Solution.t *)
  :=
  match SatSolver.solve_with_assumptions solver assumptions with
  (* UNSAT base case: a subset is unsat -> whole thing must be unsat. *)
  | SatSolver.Solution.Unsat core => Solution.Unsat core
  | SatSolver.Solution.Sat valuation =>
    match phi with
    (* no more dia clauses, don't need to recurse to the next world. *)
    (* any fired box clauses would be trivially satisfiable by non-existence of next world. *)
    | [] => Solution.Sat
    | w0 :: tail =>
      process_dias assumptions w0 tail solver valuation (Lclauses.dias w0) (valuation :: val_hist)
        Hsolver Hvaluation Hval_hist_incl Hval_hist_nodup Hmeasure
    end
  end.

Program Fixpoint process_dias
  (assumptions : Assumptions.t)
  (w0 : Lclauses.t)
  (tail : Mchain.t)
  (solver : SatSolver.t)
  (valuation : list Lit.t)
  (dias : list DiaClause.t)
  (val_hist : list Valuation.t)
  (Hsolver : SatSolver.solver_axioms solver)
  (Hvaluation : SatSolver.Solution.Sat valuation = SatSolver.solve_with_assumptions solver assumptions)
  (* val_hist must be in the set of all valuations *)
  (Hval_hist_incl : SetoidList.inclA Valuation.eq val_hist (SatSolver.every_valuation solver assumptions))
  (Hval_hist_nodup : SetoidList.NoDupA Valuation.eq val_hist)
  {measure (
    List.length tail,
    (* remaining number of possible valuations *)
    List.length (SatSolver.every_valuation solver assumptions) - List.length val_hist,
    List.length dias
  ) lexnat3_lt}
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
    (* at this recursion (1), tail equal, remaining valuations equal, dias decreasing *)
    | false =>
      process_dias assumptions w0 tail solver valuation dias' val_hist _ _ _ _

    | true =>
      (* this clause has been fired. *)

      (* TODO: make this an input to the function? *)
      let fired_box_clauses :=
        (* for each box clause a -> []b, *)
        Lclauses.boxes w0
        (* filter for [a] (fst box) in the valuation *)
        |> List.filter (fun box => Valuation.forces_lit valuation (fst box)) in
      let fired_box_lits := List.map snd fired_box_clauses in

      let next_cpls := match tail with
        | [] => []
        | w1 :: _ => Lclauses.cpls w1
      end in

      (* try a JUMP *)
      (* at this recursion (2), tail is decreasing, others don't matter. *)
      let jump := cegar_box_rec
        (d :: fired_box_lits)
        tail
        (SatSolver.make_with_clauses next_cpls)
        []
        process_dias _ _ _ _ _ in

      match jump with
        (* JUMP success: continue with next dia *)
        (* at this recursion (3), tail equal, remaining valuations equal, dias decreasing *)
        | Solution.Sat =>
          process_dias assumptions w0 tail solver valuation dias' val_hist _ _ _ _

        (* JUMP fail: RESTART *)
        | Solution.Unsat core =>
          (* get the conflict set: all names that fired some literal in the core *)
          let conflict_set :=
            fired_box_clauses
            |> List.filter (fun box => List.existsb (Lit.eqb (snd box)) core)
            |> List.map fst
          in
          (* add c as well *)
          let conflict_set := c :: conflict_set in
          (* conflict_set is interpreted as a conjunction *)
          (* negate the whole thing to become a cpl clause, interpreted as a disjunction *)
          let new_clause := List.map Lit.negate conflict_set in
          let solver := SatSolver.add_clause solver new_clause in
          (* RESTART with new solver state *)
          (* at this recursion (4), tail equal, remaining valuations decreasing, ... *)
          cegar_box_rec assumptions (w0::tail) solver val_hist process_dias _ _ _ _ _
        end
      end
  end.

(* There are multiple different proofs we are doing here: *)
(* solver always satisfies solver axioms *)
(* valuation history is always a subset of the valuations, *)
(* and the decreasing argument. *)
Next Obligation. (* (1): dias decreasing *)
  unfold lexnat3_lt. right. subst dias. cbn. lia.
Qed.
Next Obligation. (* solver with clauses satisfies axioms *)
  apply SatSolver.axioms_clauses.
Qed.
Next Obligation with auto. (* inclusion of a single valuation *)
  rename valuation into val.
  unfold SetoidList.inclA.
  intros v Hv_val.
  apply SetoidList.InA_singleton in Hv_val.

  rewrite (InA_eqA v val).
  - apply SatSolver.valuation_in_every_valuation_of with (valuation:=val)...
    apply SatSolver.axioms_clauses.
  - assumption.
  - apply Valuation.eq_equivalence.
Qed.
Next Obligation. (* valuation no dup *)
  apply SetoidList.NoDupA_singleton.
Qed.
Next Obligation. (* (2): tail decreasing *)
  unfold lexnat3_lt. left. left. subst tail. cbn. lia.
Qed.
Next Obligation. (* (3): dias decreasing *)
  unfold lexnat3_lt. right. subst dias. cbn. lia.
Qed.
Next Obligation. (* solver with extra clause satsifies axioms *)
  apply SatSolver.axioms_ind. exact Hsolver.
Qed.
Next Obligation with try easy; auto. (* inclusion with solver with added conflict set *)
  (* clear valuation0 Heq_anonymous0. *)
  rename
    solver into solver',
    solver0 into solver,
    valuation into solver'_val,
    valuation0 into solver_val.

  apply PermutationA_inclA with (l:=SatSolver.every_valuation solver assumptions)...
  - apply Valuation.eq_equivalence.
  - unfold SatSolver.every_valuation. apply Valuation.every_valuation_perm.
    unfold solver'. apply SatSolver.add_no_new_atms...
    apply conflict_set_no_new_atms...
  - apply inclA_cons. { exact Valuation.eq_equivalence. }
    split.
    (* solver'_val in every valuation *)
    + apply PermutationA_inA with (l:=SatSolver.every_valuation solver' assumptions).
      * exact Valuation.eq_equivalence.
      * apply Valuation.every_valuation_perm.
        symmetry. unfold solver'. apply SatSolver.add_no_new_atms...
        apply conflict_set_no_new_atms...
      * apply SatSolver.valuation_in_every_valuation_of... apply SatSolver.axioms_ind...
    + exact Hval_hist_incl.
Qed.
Next Obligation. (* valuations have no dup *)
  subst filtered_var. inversion Heq_anonymous. subst w1 tail0. clear Heq_anonymous.
  rename solver into solver', solver0 into solver.
Admitted.
Next Obligation with try easy; auto. (* (4) remaining valuations decreasing *)
  (* neaten up state a bit *)
  subst filtered_var. inversion Heq_anonymous. subst w1 tail0. clear Heq_anonymous.
  rename solver into solver', solver0 into solver.
  unfold lexnat3_lt. left. right.

  apply sub_S_lt.

  (* number of possible valuations is equal *)
  - apply Permutation_length.
    unfold solver'. symmetry.
    apply SatSolver.same_atms_valuation_set...
    + apply SatSolver.axioms_ind...
    + apply SatSolver.add_no_new_atms...
      apply conflict_set_no_new_atms...

  (* valuation history < every valuation *)
  - (* first show <= *)
    apply Nat.le_neq. split.
    {
      apply incl_length_le with (eqA := Valuation.eq).
      (* need to use above obligation. extract the core into a lemma? *)
      - admit. - admit.
    }
    (* setoid_rewrite Nat.le_lteq in H. *)
    (* then show <> because it is not possible for solver' to return sat.
      this is because the new valuation must be in every valuation AND
      the new valuation is not in val hist. *)
Admitted.
Next Obligation. (* lexnat3_lt is well-founded. *)
  unfold MR. apply wf_inverse_image. exact lexnat3_lt_wf.
Qed.

Program Definition cegar_box
  (assumptions : Assumptions.t)
  (phi : Mchain.t)
  (solver : SatSolver.t)
  (val_hist : list Valuation.t)
  (Hsolver : SatSolver.solver_axioms solver)
  (Hval_hist_incl : SetoidList.inclA Valuation.eq val_hist (SatSolver.every_valuation solver assumptions))
  (Hval_hist_nodup : SetoidList.NoDupA Valuation.eq val_hist)
  : Solution.t
  :=
  match SatSolver.solve_with_assumptions solver assumptions with
  (* UNSAT base case: a subset is unsat -> whole thing must be unsat. *)
  | SatSolver.Solution.Unsat core => Solution.Unsat core
  | SatSolver.Solution.Sat val =>
    match phi with
    (* no more dia clauses, don't need to recurse to the next world. *)
    (* any fired box clauses would be trivially satisfiable by non-existence of next world. *)
    | [] => Solution.Sat
    | w0 :: tail =>
      process_dias assumptions w0 tail solver val (Lclauses.dias w0) (val :: val_hist) _ _ _ _
    end
  end.
Next Obligation with auto.
  (* val :: val_hist satisfies Hval_hist_incl *)
  unfold SetoidList.inclA.
  intros v Hv_in_val_val_hist.
  rewrite SetoidList.InA_cons in Hv_in_val_val_hist.

  (* second case is trivial *)
  destruct Hv_in_val_val_hist as [Heq_v_val | Hin_v_val_hist]...

  rewrite (InA_eqA v val).
  - apply SatSolver.valuation_in_every_valuation_of with (valuation:=val)...
  - assumption.
  - apply Valuation.eq_equivalence.
Qed.
Next Obligation with auto.
Admitted.


Program Definition cegartab (phi : Mchain.t) : Solution.t :=
  let cpls := match phi with
  | [] => []
  | w0 :: tail => Lclauses.cpls w0
  end in
  cegar_box [] phi (SatSolver.make_with_clauses cpls) [] _ _ _.
Next Obligation. apply SatSolver.axioms_clauses. Qed.
Next Obligation. apply SetoidList.incl_nil. Qed.


Theorem soundness :
  forall (phi : Mchain.t), cegartab phi = Solution.Sat -> Mchain.satisfiable phi.
Proof.
Admitted.

Theorem completeness :
  forall (phi : Mchain.t), Mchain.satisfiable phi -> cegartab phi = Solution.Sat.
Proof.
  (* we prove the contrapositive. *)
  intro phi. apply contrapositive.

  intros Hsolve_unsat Hsatisfiable.

Admitted.

Theorem correctness :
  forall (phi : Mchain.t),
    Mchain.satisfiable phi <-> cegartab phi = Solution.Sat.
Proof.
  intros phi. split.
  - apply completeness.
  - apply soundness.
Qed.
