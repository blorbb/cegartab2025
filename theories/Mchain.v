From Stdlib Require List.
From CegarTableaux Require Lclauses Mcnf Cnf.
From CegarTableaux Require Import Utils.
Import List.ListNotations.
Open Scope list_scope.

(** TODO: change MCNF procedures to use this type directly instead of MCNF. *)


(** An alternative equivalent representation of an MCNF formula.

    A linked list of clauses, where the local clauses at the head represent
    clauses that need to be satisfied at the "current" world, and the tail
    is one modal context away. *)
Definition t : Type := list Lclauses.t.


Fixpoint force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  match phi with
  | [] => True
  | head :: tail => Lclauses.force M w0 head /\
    forall nbr, R w0 nbr -> force M nbr tail
  end.


Definition satisfiable (phi : t) : Prop :=
  exists W R (M : @Kripke.t W R) (w0 : W), force M w0 phi.


Definition unsatisfiable (phi : t) : Prop :=
  ~ satisfiable phi.


Definition In (x : nat) (phi : t) : Prop := List.Exists (Lclauses.In x) phi.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w : W) (x : nat), In x phi -> (Kripke.valuation M w x <-> Kripke.valuation M' w x).


Section Conversion.
  Fixpoint from_mclause (phi : Mclause.t) : t :=
    match phi with
    | Mclause.Cpl cpl => [Lclauses.make [cpl] [] []]
    | Mclause.Box box => [Lclauses.make [] [box] []]
    | Mclause.Dia dia => [Lclauses.make [] [] [dia]]
    | Mclause.Ctx ctx => Lclauses.empty :: from_mclause ctx
    end.

  (** Merge two [Mchain.t]'s together.

      This will retain all elements, and output a list the length of
      the longer list. *)
  Local Fixpoint zip_merge (a b : t) : t :=
    match a, b with
    | ha::ta, hb::tb => Lclauses.merge ha hb :: zip_merge ta tb
    | a, [] => a
    | [], b => b
    end.


  Fixpoint from_mcnf (phi : Mcnf.t) : t :=
    match phi with
    | [] => []
    | head :: tail => zip_merge (from_mclause head) (from_mcnf tail)
    end.
End Conversion.


(** Logical equivalence of the [from_mcnf] conversion. *)
Section Correctness.
  Lemma mclause_equivalent : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : Mclause.t),
    Mclause.force M w0 phi <-> force M w0 (from_mclause phi).
  Proof with auto; try tauto.
    intros W R M w0 phi. revert w0.

    induction phi as
      [ cpl
      | boxes
      | dias
      | mclause IHmclause]; intro w0.

    (* cpl *)
    - cbn. split.
      + intro Hforce_lclause. split...
      + intros [[Hforce_chain _] _].
        rewrite List.Forall_cons_iff in Hforce_chain...

    (* box *)
    - cbn. split.
      + intro Hforce_lclause. split...
      + intros [[_ [Hforce_chain _]] _].
        rewrite List.Forall_cons_iff in Hforce_chain...

    (* dia *)
    - cbn. split.
      + intro Hforce_lclause. split...
      + intros [[_ [_ Hforce_chain]] _].
        rewrite List.Forall_cons_iff in Hforce_chain...

    (* (Mclause.Ctx ctx) case *)
    - split.
      + intro Hforce_mclause.
        cbn. split...
        intros nbr Hrel_nbr.

        apply IHmclause.
        cbn in Hforce_mclause.
        apply Hforce_mclause.
        assumption.

      + intro Hforce_chain.
        cbn.
        intros nbr Hrel_nbr.

        apply IHmclause.
        cbn in Hforce_chain.
        apply proj2 in Hforce_chain.
        apply Hforce_chain.
        assumption.
  Qed.


  Lemma force_zip_and : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (A B : t),
    force M w0 (zip_merge A B) <-> force M w0 A /\ force M w0 B.
  Proof.
    intros W R M w0 A. revert w0.

    (* induction on A, case-by-case on arbitrary B *)
    induction A as [|ha ta IHta]; intros w0 B; destruct B as [| hb tb].
    (* trivial empty cases *)
    - cbn. intuition.
    - cbn. intuition.
    - cbn. intuition.
    (* merge (ha::ta) (hb::tb) <-> (ha::ta) and (hb::tb) *)
    - cbn [zip_merge force].
      rewrite Lclauses.force_merge_and.
      setoid_rewrite IHta.
      intuition.
      + now apply H1.
      + now apply H1.
  Qed.


  Theorem mcnf_equivalent : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : Mcnf.t),
    Mcnf.force M w0 phi <-> force M w0 (from_mcnf phi).
  Proof with auto; try tauto.
    intros W R M w0 phi. revert w0.

    induction phi as [| head tail IHtail].
    - cbn. tauto.
    - intro w0. cbn.
      rewrite force_zip_and, mclause_equivalent, IHtail.
      tauto.
  Qed.
End Correctness.
