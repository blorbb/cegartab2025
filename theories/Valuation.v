From Stdlib Require List SetoidList Permutation.
From Stdlib Require Import Relations RelationClasses Permutation SetoidPermutation.
From CegarTableaux Require Lit.
From CegarTableaux Require Import ListExt.
Import List.ListNotations.
Open Scope list_scope.


(** Valuation represented as a list of literals. *)
Definition t := list Lit.t.

(** Every atom must appear at most once. *)
Definition clash_free (val : t) := SetoidList.NoDupA Lit.eq_atm val.

Definition atms_of (val : t) := List.map Lit.atm val.

Definition In (x : nat) (val : t) :=
  List.In x (atms_of val).

Arguments atms_of val /.
Arguments In x val /.

Definition forces_lit (val : t) (x : Lit.t) : bool := List.existsb (Lit.eqb x) val.

Definition matches_kripke_valuation (val : t) {W} {R} (M : @Kripke.t W R) (w0 : W) :=
  forall x, In x val -> Kripke.valuation M w0 x <-> List.In (Lit.Pos x) val.

Lemma forces_in : forall (val : t) (lit : Lit.t), forces_lit val lit = true -> In (Lit.atm lit) val.
Proof.
  intros val lit Hforce_lit.
  cbn. apply List.in_map.
  unfold forces_lit in Hforce_lit.
  apply List.existsb_exists in Hforce_lit.
  destruct Hforce_lit as [lit' [Hlit_in_val Heq_lit]].
  apply Lit.eqb_eq in Heq_lit.
  subst lit'. exact Hlit_in_val.
Qed.


Lemma clash_free_nil : clash_free [].
Proof. unfold clash_free. apply SetoidList.NoDupA_nil. Qed.


(* Set-equality of valuations *)
Definition eq (a b : t) : Prop :=
  Permutation.Permutation a b.

(* coq can auto solve these *)
Global Instance eq_equivalence : Equivalence eq := {}.

Section AllValuations.
  Fixpoint every_valuation_of_atms (atms : list nat) : list t :=
    match atms with
    | [] => [[]]
    | atm :: atms' =>
      let rec := every_valuation_of_atms atms' in
      List.flat_map
        (fun val => [ Lit.Pos atm :: val ; Lit.Neg atm :: val ])
        rec
    end.

  Definition val_in_vals (val : t) (vals : list t) : Prop :=
    SetoidList.InA eq val vals.

  (** Atoms of every valuation is exactly the input atms. *)
  Lemma every_valuation_exact_atms : forall (atms : list nat),
    List.Forall (fun val => atms = atms_of val) (every_valuation_of_atms atms).
  Proof with try easy; auto.
    setoid_rewrite List.Forall_forall.
    intros atms. unfold atms_of.

    induction atms as [|head tail IHtail].
    - intros val Hval_in.
      cbn in Hval_in. destruct Hval_in as [Hval_nil | F]...
      subst val. reflexivity.
    - intros val Hval_in_vals.

      cbn in *. apply List.in_flat_map in Hval_in_vals.
      destruct Hval_in_vals as [val' [Hval'_in_tail Hval_in_cons]].

      (* val = +atm :: val' or -atm :: val' *)
      destruct Hval_in_cons as [Hval_pos_val' | [Hval_neg_val' | F]]...
      + subst val. cbn. rewrite <- (IHtail val')...
      + subst val. cbn. rewrite <- (IHtail val')...
  Qed.


  Lemma every_valuation_clash_free : forall (atms : list nat),
    List.NoDup atms ->
    List.Forall clash_free (every_valuation_of_atms atms).
  Proof with try easy; auto.
    intros atms Hnodup.
    induction Hnodup as [| atm atms Hatm_notin Hnodup' IH].
    - cbn. apply List.Forall_forall.
      intros val Hval_nil.
      cbn in Hval_nil. destruct Hval_nil as [Hval_nil | F]...
      subst val. apply clash_free_nil.
    - rewrite List.Forall_forall in *.
      intros val Hval_in.
      (* extract the flat map into the inner and outer parts. *)
      cbn in Hval_in. apply List.in_flat_map in Hval_in.
      destruct Hval_in as [val' [Hval'_in_atms Hval_in_cons]].

      (* val' is clash_free *)
      specialize (IH val' Hval'_in_atms) as Hval'_sound.

      (* val = +atm :: val' or -atm :: val' *)
      destruct Hval_in_cons as [Hval_pos_val' | [Hval_neg_val' | F]]...
      + subst val. unfold clash_free in *.
        apply SetoidList.NoDupA_cons...
        (* atm not in val' *)
        intro H.
        rewrite SetoidList.InA_alt in H.
        destruct H as [l [Hl_eq_atm Hl_in_val']].
        cbn in Hl_eq_atm.
        (* show that atm in atms *)
        apply Hatm_notin.

        pose proof (every_valuation_exact_atms atms) as Hatms_of_val.
        rewrite List.Forall_forall in Hatms_of_val.
        specialize (Hatms_of_val val' Hval'_in_atms).
        rewrite Hl_eq_atm. rewrite Hatms_of_val. unfold atms_of.
        now apply List.in_map.

      + subst val. unfold clash_free in *.
        apply SetoidList.NoDupA_cons...
        (* atm not in val' *)
        intro H.
        rewrite SetoidList.InA_alt in H.
        destruct H as [l [Hl_eq_atm Hl_in_val']].
        unfold Lit.eq_atm in Hl_eq_atm. cbn in Hl_eq_atm.
        (* show that atm in atms *)
        apply Hatm_notin.

        pose proof (every_valuation_exact_atms atms) as Hatms_of_val.
        rewrite List.Forall_forall in Hatms_of_val.
        specialize (Hatms_of_val val' Hval'_in_atms).
        rewrite Hl_eq_atm. rewrite Hatms_of_val. unfold atms_of.
        now apply List.in_map.
  Qed.

  Lemma lits_in_every_of_lits : forall (ls : list Lit.t),
    List.In ls (every_valuation_of_atms (atms_of ls)).
  Proof.
    intro ls. induction ls as [| l ls IH].
    - cbn. now left.
    - cbn. apply List.in_flat_map. cbn.
      exists ls. split.
      + exact IH.
      + destruct l as [x|x]; cbn; intuition.
  Qed.

  Lemma val_of_atms_in_every_valuation :
    forall atms val,
      Permutation atms (atms_of val) ->
      val_in_vals val (every_valuation_of_atms atms).
  Proof with auto.
    intros atms.
    induction atms as [| atm atms' IH].
    - intros val Hperm.
      cbn in *.
      apply SetoidList.InA_singleton.
      unfold eq.
      apply Permutation_nil in Hperm.
      apply List.map_eq_nil in Hperm.
      subst val. apply perm_nil.
    (* split the inA *)
    - intros val Hperm. unfold val_in_vals in *.
      cbn.

      apply inA_flat_map.

      (* destruct val into a permutation of l::ls *)
      apply Permutation_map_inv in Hperm.
      destruct Hperm as [val' [Hval'_eq Hperm_val']].
      symmetry in Hval'_eq.
      apply List.map_eq_cons in Hval'_eq.
      destruct Hval'_eq as [l [ls [Hval'_eq [Hl_atm Hls_atms']]]].
      subst atm atms' val'.

      exists ls. split.
      + apply lits_in_every_of_lits.
      + apply SetoidList.InA_alt.
        destruct l as [x|x].
        * cbn. exists (Lit.Pos x :: ls)...
        * cbn. exists (Lit.Neg x :: ls)...
  Qed.

  Lemma every_valuation_perm : forall (atms atms' : list nat),
    Permutation atms atms' ->
    PermutationA eq (every_valuation_of_atms atms) (every_valuation_of_atms atms').
  Proof.
    intros atms atms' Hperm.
  Admitted.

  Lemma every_valuation_unique : forall (atms : list nat),
    List.NoDup atms ->
    SetoidList.NoDupA eq (every_valuation_of_atms atms).
  Proof.
  Admitted.
End AllValuations.

(* TODO: probably don't need the lemmas below. just for practice with NoDupA. *)

Lemma atms_of_nodup : forall (val : t), clash_free val -> List.NoDup (atms_of val).
Proof.
  intros val Hnodup.
  induction Hnodup as [| l val' Hl_notin Hnodup' IH].
  - cbn. apply List.NoDup_nil.
  - cbn. apply List.NoDup_cons.
    (* show l not in val' *)
    + intros H.
      apply List.in_map_iff in H.
      destruct H as [x [Hxl Hx_in_val']].
      apply Hl_notin.
      unfold Lit.eq_atm.
      apply SetoidList.InA_alt. exists x. easy.
    + exact IH.
Qed.

Lemma lit_nodup : forall (val : t), clash_free val -> List.NoDup val.
Proof.
  intros val Hnodup.
  induction Hnodup as [| l val' Hl_notin Hnodup' IH].
  - apply List.NoDup_nil.
  - apply List.NoDup_cons.
    (* l not in val' *)
    + intro H.
      apply Hl_notin.
      unfold Lit.eq_atm.
      apply SetoidList.InA_alt. exists l. easy.
    + exact IH.
Qed.
