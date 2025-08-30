From Stdlib Require List SetoidList Permutation.
From Stdlib Require Import Relations RelationClasses Permutation SetoidPermutation.
From CegarTableaux Require Lit.
From CegarTableaux Require Import ListExt Utils.
Import List.ListNotations.
Open Scope list_scope.


(** Valuation represented as a list of literals. *)
Definition t := list Lit.t.


(** Every atom must appear at most once. *)
Definition clash_free (val : t) := SetoidList.NoDupA Lit.eq_atm val.


Definition atms_of (val : t) := List.map Lit.atm val.

Arguments atms_of val /.


Definition In (x : nat) (val : t) :=
  List.In x (atms_of val).

Arguments In x val /.


Lemma clash_free_nil : clash_free [].
Proof. unfold clash_free. apply SetoidList.NoDupA_nil. Qed.


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


Lemma clash_free_no_negation : forall l val,
  clash_free val -> List.In l val -> ~ List.In (Lit.negate l) val.
Proof with try easy; auto.
  intros l val Hcf Hl_in Hnl_in.
  unfold clash_free in Hcf.
  apply SetoidList.NoDupA_altdef in Hcf.
  apply List.ForallOrdPairs_In with (x:=l) (y:=Lit.negate l) in Hcf...
  destruct Hcf as [Hl_nl | [Hne | Hne]].
  - destruct l as [x|x]...
  - unfold complement in Hne. apply Hne.
    cbn. symmetry. apply Lit.negate_eq_atm.
  - unfold complement in Hne. apply Hne.
    cbn. apply Lit.negate_eq_atm.
Qed.


Lemma lit_in_atm_in : forall (l : Lit.t) (val : t),
  List.In l val -> In (Lit.atm l) val.
Proof.
  intros l val Hin.
  unfold In, atms_of.
  now apply List.in_map.
Qed.


Definition forces_lit (val : t) (l : Lit.t) : bool := List.existsb (Lit.eqb l) val.


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


(** Set-equality of valuations *)
Definition eq (a b : t) : Prop :=
  Permutation.Permutation a b.

(* coq can auto solve these *)
Global Instance eq_equivalence : Equivalence eq := {}.


(** These 3 are unused but might be helpful later. *)
Lemma atm_in_lit_in : forall (p : nat) (val : t),
  In p val -> List.In (Lit.Pos p) val \/ List.In (Lit.Neg p) val.
Proof.
  intros p val Hp_in.
  cbn in Hp_in.
  apply List.in_map_iff in Hp_in as [l [Hlp Hl_in]].
  destruct l as [q | q].
  - cbn in Hlp. subst p. now left.
  - cbn in Hlp. subst p. now right.
Qed.

Lemma eq_clash_free : forall (val val' : t), eq val val' -> clash_free val -> clash_free val'.
Proof with auto using Lit.eq_atm_equivalence.
  intros val val' Heq Hcf.
  unfold clash_free, eq in *.
  apply PermutationA_preserves_NoDupA with (l₁ := val)...
  apply Permutation_PermutationA...
Qed.

Lemma eq_in : forall (p : nat) (val val' : t), eq val val' -> In p val <-> In p val'.
Proof with auto.
  intros p val val' Heq.
  cbn.
  repeat rewrite List.in_map_iff in *.
  split.
  - intros [l [Hl_eq Hl_in]].
    exists l. split...
    apply Permutation_in with (l:=val)...
  - intros [l [Hl_eq Hl_in]].
    exists l. split...
    apply Permutation_in with (l:=val')...
    now symmetry.
Qed.


(** Generate every valuation from a set of atoms. *)
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
  Proof with try easy; auto using Valuation.eq_equivalence.
    intros atms atms' Hperm.
    induction Hperm.
    - cbn. constructor...
    - cbn. apply PermutationA_flat_map with (eqA := eq)...
      intros a a' Heq_aa'. repeat constructor...
    - cbn.
      set (vals := (every_valuation_of_atms l)).
      induction vals as [|v vals IHvals]...
      cbn.
      (* show that these are a permutation: *)
      (* +x::+y, +x::-y, -x::+y, -x::-y *)
      (* +x::+y, -x::+y, +x::-y, -x::-y *)
      (* just need to swap the middle two. *)
      apply PermutationA_cons. { apply perm_swap. }
      apply PermutationA_swap_heads. apply PermutationA_cons. { apply perm_swap. }
      apply PermutationA_cons. { apply perm_swap. }
      apply PermutationA_cons. { apply perm_swap. }
      exact IHvals.

    - apply (
        @permA_trans
          (list Lit.t)
          eq
          (every_valuation_of_atms l)
          (every_valuation_of_atms l')
          (every_valuation_of_atms l'')
      )...
  Qed.


  Lemma every_valuation_unique : forall (atms : list nat),
    List.NoDup atms ->
    SetoidList.NoDupA eq (every_valuation_of_atms atms).
  Proof with try easy; auto using eq_equivalence.
    intros atms Hnd.

    induction Hnd as [|atm atms Hatm_nin Hatms_nd IHatms]; cbn.
    { apply SetoidList.NoDupA_singleton. }

    set (vals := every_valuation_of_atms atms) in *.

    (* Need to perform induction on vals with enough information for the IH to be usable. *)
    assert (forall v, List.In v vals -> ~ In atm v) as Hnin.
    {
      intros v Hv_in_vals Hatm_in_v.
      apply Hatm_nin.
      assert (atms = atms_of v) as Hatms.
      { pose proof (every_valuation_exact_atms atms) as H. rewrite List.Forall_forall in H. apply H... }
      unfold In in Hatm_in_v.
      rewrite Hatms. assumption.
    }
    revert Hnin.

    induction vals as [|v vals IHvals]...

    intros Hatm_nin_vals.
    cbn. repeat constructor.
    - intro H. apply SetoidList.InA_cons in H as [Heq_atm | Hin_atms].
      + apply Permutation_in with (x := Lit.Pos atm) in Heq_atm.
        2: { apply List.in_eq. }
        cbn in Heq_atm. destruct Heq_atm...
        apply (Hatm_nin_vals v).
        * apply List.in_eq.
        * now apply (lit_in_atm_in (Lit.Pos atm)).
      + inversion_clear IHatms. rename H into Hv_nin_vals, H0 into Hvals_nd.
        apply inA_flat_map in Hin_atms as [v' [Hv'_in_vals Hin]].
        apply InA_length_2 in Hin as [Heq | Heq].
        * apply Hv_nin_vals.
          unfold eq in Heq. apply Permutation_cons_inv in Heq.
          apply SetoidList.InA_eqA with (x:=v') (y:=v)...
          apply SetoidList.In_InA...
        * unfold eq in Heq.
          symmetry in Heq.
          apply Permutation_heads_ne in Heq...
          apply (Hatm_nin_vals v). { apply List.in_eq. }
          apply (lit_in_atm_in (Lit.Neg atm))...

    (* Almost the same as the second case of the above. *)
    - intro Hin_atms.
      inversion_clear IHatms. rename H into Hv_nin_vals, H0 into Hvals_nd.
        apply inA_flat_map in Hin_atms as [v' [Hv'_in_vals Hin]].
        apply InA_length_2 in Hin as [Heq | Heq].
        + unfold eq in Heq.
          symmetry in Heq.
          apply Permutation_heads_ne in Heq...
          apply (Hatm_nin_vals v). { apply List.in_eq. }
          apply (lit_in_atm_in (Lit.Pos atm))...
        + apply Hv_nin_vals.
          unfold eq in Heq. apply Permutation_cons_inv in Heq.
          apply SetoidList.InA_eqA with (x:=v') (y:=v)...
          apply SetoidList.In_InA...

    - apply IHvals.
      + now apply cons_NoDupA in IHatms.
      + intros v' Hv'_in_vals.
        apply Hatm_nin_vals.
        cbn. now right.
  Qed.
End AllValuations.
