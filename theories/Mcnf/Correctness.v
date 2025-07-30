From Stdlib Require Import PeanoNat Setoids.Setoid Classical Lia.
From Stdlib Require List.

From CegarTableaux Require Lit Nnf Kripke Mclause.
From CegarTableaux.Mcnf Require Mcnf Conversion.
From CegarTableaux Require Import Utils.

Import List.ListNotations.
Open Scope list_scope.


(** Shorter alias for conversion functions *)
Module Mcnfc := Conversion.



Lemma sur_input_le_return :
  forall (name : nat) (phi : Nnf.t) (sur : nat),
    sur <= snd (Mcnfc.from_n_nnf name phi sur).
Proof.
  intros name phi sur.
  revert name sur.
  induction phi as
    [ l
    | A IHA B IHB
    | A IHA B IHB
    | A IHA
    | A IHA
    ].
  - simpl. reflexivity.
  - simpl. intros name sur.
    destruct_pair (Mcnfc.from_n_nnf sur A (S (S sur))) as [A_mcnf sur_A].
    destruct_pair (Mcnfc.from_n_nnf (S sur) B sur_A) as [B_mcnf sur_B].
    (* transitivity *)
    simpl.
    specialize (IHA sur (S (S sur))).
    specialize (IHB (S sur) sur_A).
    lia.
  - simpl. intros name sur.
    destruct_pair (Mcnfc.from_n_nnf sur A (S (S sur))) as [A_mcnf sur_A].
    destruct_pair (Mcnfc.from_n_nnf (S sur) B sur_A) as [B_mcnf sur_B].
    (* transitivity *)
    simpl.
    specialize (IHB (S sur) sur_A).
    specialize (IHA sur (S (S sur))).
    lia.
  - simpl. intros name sur.
    destruct_pair (Mcnfc.from_n_nnf sur A (S sur)) as [A_mcnf sur_A].
    (* transitivity *)
    simpl. specialize (IHA sur (S sur)). lia.
  - simpl. intros name sur.
    destruct_pair (Mcnfc.from_n_nnf sur A (S sur)) as [A_mcnf sur_A].
    (* transitivity *)
    simpl. specialize (IHA sur (S sur)). lia.
Qed.


(*
  an extra tactic [autolia] that is equivalent to [lia] but applies some
  known inequalities from the above theorems.
*)
Local Ltac add_ineq_from_sym_in_nnf :=
  match goal with
  | [ H: Nnf.In ?x ?phi |- _ ] =>
      let T := constr:(x <= Nnf.max_atm phi) in
      (* assertion already known: fail *)
      tryif assert T by assumption then
        fail 1
      else
        let Hle := fresh "Hsym_le" in
        assert (T) as Hle by (apply Nnf.atm_le_max; exact H);
        clear H
  end.

Local Ltac add_ineq_from_n_impl :=
  match goal with
  | [ q := snd (Mcnfc.from_n_nnf ?name ?phi ?sur) |- _ ] =>
      let T := constr:(sur <= q) in
      tryif assert T by assumption then
        fail 1
      else
        let Hle := fresh "Hsur_le" in
        assert (T) as Hle by (unfold q; apply sur_input_le_return);
        (* since we clear it, lia can't solve if we have an unfolded version of q *)
        fold_all q;
        clearbody q
  end.

Local Ltac add_ineqs := repeat (add_ineq_from_sym_in_nnf; [] || add_ineq_from_n_impl; []).

Local Ltac autolia :=
  add_ineqs;
  lia.

(**
  Solve the current goal with a variety of autosolvers which are likely
  to solve goals relating to the current context.

  This fails if the goal cannot be completely solved.

  Should be used like [Proof with try finish.].
*)
Local Ltac finish := simpl; solve [auto | autolia | tauto | ifauto].










Theorem conv_atm_range :
  forall
    (phi : Nnf.t)
    (n p : nat)
    (Hmnp_lt : Nnf.max_atm phi < n < p)
    (x : nat),
  let (phi_mcnf, q) := Mcnfc.from_n_nnf n phi p in
  Mcnf.In x phi_mcnf
  -> Nnf.In x phi
    \/ x = n
    \/ p <= x < q.
Proof.
  intros phi n p Hmnp_lt x.
  revert n p Hmnp_lt.

  induction phi as
    [ l
    | A IHA B IHB
    | A IHA B IHB
    | A IHA
    | A IHA
    ]; intros n p Hmnp_lt.
  (* literal: x in phi or x = n *)
  - destruct_pair (Mcnfc.from_n_nnf n (Nnf.Lit l) p) as [phi_mcnf q].
    intro Hxmcnf.

    unfold phi_mcnf in Hxmcnf. simpl in Hxmcnf.
    destruct Hxmcnf as [[Hn_eq_x | [Hl_eq_x | F]] | F]; try contradiction.
    (* n = x *)
    + rewrite Hn_eq_x. tauto.
    (* l = x *)
    + destruct l; simpl in Hl_eq_x; simpl; lia.

  (* and *)
  - (* destruct let-in statements to fst and last equalities *)
    simpl.
    set (nA := p). set (nB := S nA).
    destruct_pair (Mcnfc.from_n_nnf nA A (S (S p))) as [A_mcnf q].
    destruct_pair (Mcnfc.from_n_nnf nB B q) as [B_mcnf r].

    intro Hx_in_mcnf.
    simpl in *.

    (* apply IH to the specific surrogate/name values used by this branch *)
    specialize (IHA nA (S (S p))).
    specialize (IHB nB q).


    (* prove all LHS of implications in IH *)
    forward IHA by lia.
    forward IHB by autolia.

    (* simplify IH again. *)
    inline_pair in IHA.
    inline_pair in IHB.
    fold A_mcnf in IHA.
    fold B_mcnf in IHB.

    (* to apply to IH's *)
    assert (x = n \/ x = nA \/ x = nB \/ Mcnf.In x A_mcnf \/ Mcnf.In x B_mcnf) as Hin_split.
    {
      destruct Hx_in_mcnf as [[Hnx | [HnAx | F]] | [[Hnx | [HnBx | F]] | Hx_in_mcnf]]; try lia.
      right. right. right. apply Mcnf.in_mcnf_or. exact Hx_in_mcnf.
    }

    destruct Hin_split as
      [Hxn | [Hxp | [HxSp | [Hx_in_A | Hx_in_b]]]]; try autolia.
    + (* in A_mcnf *)
      forward IHA by assumption.
      destruct IHA; try tauto; autolia.

    + (* in B_mcnf *)
      forward IHB by assumption.
      destruct IHB; try tauto; autolia.

  (* or *)
  - (* destruct let-in statements to fst and last equalities *)
    simpl.
    destruct_pair (Mcnfc.from_n_nnf p A (S (S p))) as [A_mcnf q].
    destruct_pair (Mcnfc.from_n_nnf (S p) B q) as [B_mcnf r].
    intro Hx_in_mcnf.
    cbn in *.

    (* apply IH to the specific surrogate/name values used by this branch *)
    specialize (IHA p (S (S p))).
    specialize (IHB (S p) q).

    (* prove all LHS of implications in IH *)
    forward IHA by lia.
    forward IHB by autolia.

    (* simplify IH again. *)
    inline_pair in IHA.
    inline_pair in IHB.
    fold A_mcnf in IHA.
    fold B_mcnf in IHB.

    (* to apply to IH's *)
    assert (x = n \/ x = p \/ x = (S p) \/ Mcnf.In x A_mcnf \/ Mcnf.In x B_mcnf) as Hin_split.
    {
      destruct Hx_in_mcnf as [[Hnx | [Hpx | [HSpx | F]]] | Habx]; try lia.
      apply Mcnf.in_mcnf_or in Habx. tauto.
    }

    destruct Hin_split as
      [Hxn | [Hxp | [HxSp | [Hx_in_A | Hx_in_b]]]]; try autolia.
    + (* in A_mcnf *)
      forward IHA by assumption. 
      destruct IHA; try tauto; autolia.
    + (* in B_mcnf *)
      forward IHB by assumption.
      destruct IHB; try tauto; autolia.

  (* box *)
  - (* destruct let-in statements to fst and last equalities *)
    simpl.
    destruct_pair (Mcnfc.from_n_nnf p A (S p)) as [A_mcnf q].
    intro Hx_in_mcnf.
    simpl in *.

    (* apply IH to the specific surrogate/name values used by this branch *)
    specialize (IHA p (S p)).

    (* prove all LHS of implications in IH *)
    forward IHA by lia.

    (* simplify IH again. *)
    inline_pair in IHA. fold A_mcnf in IHA.

    (* to apply to IH's *)
    assert (x = n \/ x = p \/ Mcnf.In x A_mcnf) as Hin_split.
    {
      unfold A_mcnf in Hx_in_mcnf.
      simpl in Hx_in_mcnf.
      destruct Hx_in_mcnf as [[Hxn | Hxp] | Hctx_a_x]; try lia.
      rewrite Mcnf.in_ctx_iff_in_mcnf in Hctx_a_x. tauto.
    }

    (* adding these allow lia to auto-prove most cases. *)
    assert (S p <= q) as HSp_le_q.
    { unfold q. apply sur_input_le_return. }

    destruct Hin_split as
      [Hxn | [Hxp | Hx_in_A]]; try lia.
    (* in A_mcnf *)
    forward IHA by assumption. 
    destruct IHA; try tauto; lia.

  (* dia *)
  (* this is identical to the box case except for the first destruct_pair. *)
  - (* destruct let-in statements to fst and last equalities *)
    simpl.
    destruct_pair (Mcnfc.from_n_nnf p A (S p)) as [A_mcnf q].
    intro Hx_in_mcnf.
    simpl in *.

    (* apply IH to the specific surrogate/name values used by this branch *)
    specialize (IHA p (S p)).

    (* prove all LHS of implications in IH *)
    forward IHA by lia.

    (* simplify IH again. *)
    (* makes A bunch of redundant equalities, remove them *)
    inline_pair in IHA. fold A_mcnf in IHA.

    (* to apply to IH's *)
    assert (x = n \/ x = p \/ Mcnf.In x A_mcnf) as Hin_split.
    {
      simpl in Hx_in_mcnf.
      destruct Hx_in_mcnf as [[Hxn | Hxp] | Hctx_a_x]; try lia.
      rewrite Mcnf.in_ctx_iff_in_mcnf in Hctx_a_x. tauto.
    }

    (* adding these allow lia to auto-prove most cases. *)
    assert (S p <= q) as HSp_le_q.
    { unfold q. apply sur_input_le_return. }

    destruct Hin_split as
      [Hxn | [Hxp | Hx_in_A]]; try lia.
    (* in A_mcnf *)
    forward IHA by assumption.
    destruct IHA; try tauto; lia.
Qed.




Section EquisatModel.
  Definition set_kripke_at_n_iff_force
    {W} {R}
    (* the model to change at n *)
    (Mmcnf : @Kripke.t W R) (n : nat)
    (* at n, set valuation to Nnf.force Mnnf w phi *)
    (Mnnf : @Kripke.t W R) (phi : Nnf.t)
    : @Kripke.t W R :=
    Kripke.make W R (fun w x => if x =? n then Nnf.force Mnnf w phi else Kripke.valuation Mmcnf w x).


  (**
  Transforms M so that M forces (n -> phi) iff M' forces (n -> phi_mcnf)
  Requires that [Nnf.max_atm phi < n < sur]
  *)
  Fixpoint named_model {W} {R} (M : @Kripke.t W R) (n : nat) (phi : Nnf.t) (sur : nat) : @Kripke.t W R :=
    match phi with
    (* n -> l  =>  ~n \/ l *)
    | Nnf.Lit l =>
        set_kripke_at_n_iff_force M n M phi

    (* n -> A /\ B  =>  n -> nA ; n -> nB ; nA -> A ; nB -> B *)
    | Nnf.And A B =>
      let (nA, sur) := (sur, S sur) in
      let (nB, sur) := (sur, S sur) in
      let M' := named_model M nA A sur in
      let sur := snd (Mcnfc.from_n_nnf nA A sur) in
      let M' := named_model M' nB B sur in
        set_kripke_at_n_iff_force M' n M phi

    (* n -> A \/ B  =>  n -> nA \/ nB ; nA -> A ; nB -> B *)
    | Nnf.Or A B =>
      let (nA, sur) := (sur, S sur) in
      let (nB, sur) := (sur, S sur) in
      let M' := named_model M nA A sur in
      let sur := snd (Mcnfc.from_n_nnf nA A sur) in
      let M' := named_model M' nB B sur in
        set_kripke_at_n_iff_force M' n M phi

    (* n -> []A  =>  n -> []nA ; [](nA -> A) *)
    | Nnf.Box A =>
      let (nA, sur) := (sur, S sur) in
      let M' := named_model M nA A sur in
        set_kripke_at_n_iff_force M' n M phi

    (* n -> <>A  =>  n -> <>nA ; [](nA -> A) *)
    | Nnf.Dia A =>
      let (nA, sur) := (sur, S sur) in
      let M' := named_model M nA A sur in
        set_kripke_at_n_iff_force M' n M phi
    end.
End EquisatModel.



Section EquisatModelRange.
  Theorem named_model_changes_sur_only :
    forall {W} {R} (M : @Kripke.t W R) (w : W) (phi : Nnf.t) (n p x : nat) (Hmnp_lt : Nnf.max_atm phi < n < p),
      let s := snd (Mcnfc.from_n_nnf n phi p) in
      ~ (x = n \/ p <= x < s) ->
      Kripke.valuation M w x <-> Kripke.valuation (named_model M n phi p) w x.
  Proof with simpl; auto; try autolia.
    intros W R M w phi.
    revert w. generalize dependent M.
    induction phi as
      [ l
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ];
      intros M w n p x Hmnp_lt s Hx_range; apply not_or_and in Hx_range.
    (* literal *)
    - simpl. ifauto. reflexivity.

    (* and *)
    - set (MA := named_model M p A (S (S p))).
      set (q := snd (Mcnfc.from_n_nnf p A (S (S p)))).
      set (MB := named_model MA (S p) B q).
      set (r := snd (Mcnfc.from_n_nnf (S p) B q)).

      simpl in Hmnp_lt.
      assert (q <= s) as Hqs.
      {
        unfold s. simpl.
        repeat inline_pair. simpl.
        fold q. apply sur_input_le_return.
      }
      assert (r = s) as Hrs.
      {
        unfold s. simpl.
        repeat inline_pair. simpl.
        fold q. fold r. reflexivity.
      }

      assert (Kripke.valuation M w x <-> Kripke.valuation MA w x) as Hval_M_MA.
      {
        unfold MA. apply IHA...
        fold q. autolia.
      }
      assert (Kripke.valuation MA w x <-> Kripke.valuation MB w x) as Hval_MA_MB.
      {
        unfold MB. apply IHB...
        fold r. autolia.
      }

      simpl. ifauto. fold MA q MB. tauto.

    (* or *)
    - set (MA := named_model M p A (S (S p))).
      set (q := snd (Mcnfc.from_n_nnf p A (S (S p)))).
      set (MB := named_model MA (S p) B q).
      set (r := snd (Mcnfc.from_n_nnf (S p) B q)).

      simpl in Hmnp_lt.
      assert (q <= s) as Hqs.
      {
        unfold s. simpl.
        repeat inline_pair. simpl.
        fold q. apply sur_input_le_return.
      }
      assert (r = s) as Hrs.
      {
        unfold s. simpl.
        repeat inline_pair. simpl.
        fold q. fold r. reflexivity.
      }

      assert (Kripke.valuation M w x <-> Kripke.valuation MA w x) as Hval_M_MA.
      {
        unfold MA. apply IHA...
        fold q. autolia.
      }
      assert (Kripke.valuation MA w x <-> Kripke.valuation MB w x) as Hval_MA_MB.
      {
        unfold MB. apply IHB...
        fold r. autolia.
      }

      simpl. ifauto. fold MA q MB. tauto.

    (* box *)
    - simpl. simpl in Hmnp_lt. ifauto.

      set (q := snd (Mcnfc.from_n_nnf p A (S p))).
      assert (q = s).
      { unfold s. simpl. inline_pair. simpl. reflexivity. }

      apply IHA... fold q. autolia.

    (* dia *)
    - simpl. simpl in Hmnp_lt. ifauto.

      set (q := snd (Mcnfc.from_n_nnf p A (S p))).
      assert (q = s).
      { unfold s. simpl. inline_pair. simpl. reflexivity. }

      apply IHA... fold q. autolia.
  Qed.


  Theorem named_model_vals_name_iff_force :
    forall {W} {R} (M : @Kripke.t W R) (w : W) (phi : Nnf.t) (n p : nat),
      Kripke.valuation (named_model M n phi p) w n <-> Nnf.force M w phi.
  Proof.
    intros W R M w phi. revert w.
      induction phi as
      [ l
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ];
    intros w n p; simpl; ifauto; reflexivity.
  Qed.


  Theorem named_model_overrides_all_sur :
    forall {W} {R} (M M' : @Kripke.t W R) (w : W) (phi : Nnf.t) (n p x : nat) (Hmnp_lt : Nnf.max_atm phi < n < p),
      let q := snd (Mcnfc.from_n_nnf n phi p) in
      p <= x < q ->
      Nnf.agree phi M M' ->
      Kripke.valuation (named_model M n phi p) w x <->
      Kripke.valuation (named_model M' n phi p) w x.
  Proof with simpl; auto; try autolia.
    intros W R M M' w phi.
    revert w. generalize dependent M. generalize dependent M'.

    induction phi as
      [ l
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ];
    intros M M' w n p x Hmnp_lt s Hx_range Hmodels_agree.
    (* holds because s = p, the range is empty *)
    - simpl in s. simpl. ifauto. lia.

    - set (MA := named_model M p A (S (S p))).
      set (q := snd (Mcnfc.from_n_nnf p A (S (S p)))).
      set (MB := named_model MA (S p) B q).
      set (r := snd (Mcnfc.from_n_nnf (S p) B q)).

      set (M'A := named_model M' p A (S (S p))).
      set (M'B := named_model M'A (S p) B q).


      simpl in Hmnp_lt.
      assert (q <= s) as Hqs.
      {
        unfold s. simpl.
        repeat inline_pair. simpl.
        fold q. apply sur_input_le_return.
      }
      assert (r = s) as Hrs.
      {
        unfold s. simpl.
        repeat inline_pair. simpl.
        fold q. fold r. reflexivity.
      }

      simpl. ifauto. fold MA M'A q MB M'B.
      assert (x = p \/ x = S p \/ (S (S p)) <= x < q \/ q <= x < s) as [Hxp | [HxSp | [Hpxq | Hqxs]]] by lia.
      (* x = p *)
      + unfold MB, M'B.
        rewrite <- (named_model_changes_sur_only M'A)...
        rewrite <- (named_model_changes_sur_only MA)...
        unfold MA, M'A.
        rewrite Hxp.
        repeat rewrite named_model_vals_name_iff_force.
        apply Nnf.meaningful_valuations.
        apply (Nnf.agree_l A B). assumption.

      (* x = S p *)
      + unfold MB, M'B.
        rewrite HxSp.
        repeat rewrite named_model_vals_name_iff_force.
        apply Nnf.meaningful_valuations.
        unfold Nnf.agree.
        (* MA and M'A agree *)
        intros w' x' Hx'_in_B.
        unfold MA, M'A.
        rewrite <- (named_model_changes_sur_only M')...
        rewrite <- (named_model_changes_sur_only M)...
        apply (Nnf.agree_r A B)...

      (* S (S p) <= x < q *)
      + assert (Kripke.valuation MA w x <-> Kripke.valuation MB w x) as Hval_MA_MB.
        { unfold MB. apply named_model_changes_sur_only... }
        assert (Kripke.valuation M'A w x <-> Kripke.valuation M'B w x) as Hval_M'A_M'B.
        { unfold MB. apply named_model_changes_sur_only... }
        rewrite <- Hval_MA_MB.
        rewrite <- Hval_M'A_M'B.
        apply IHA...
        apply (Nnf.agree_l A B). assumption.

      (* q <= x < s *)
      + unfold MB, M'B.
        apply IHB...
        * fold r. lia.
        * intros w' x' Hx'_in_B.
          unfold MA, M'A.
          rewrite <- (named_model_changes_sur_only M')...
          rewrite <- (named_model_changes_sur_only M)...
          apply (Nnf.agree_r A B)...

    - set (MA := named_model M p A (S (S p))).
      set (q := snd (Mcnfc.from_n_nnf p A (S (S p)))).
      set (MB := named_model MA (S p) B q).
      set (r := snd (Mcnfc.from_n_nnf (S p) B q)).

      set (M'A := named_model M' p A (S (S p))).
      set (M'B := named_model M'A (S p) B q).


      simpl in Hmnp_lt.
      assert (q <= s) as Hqs.
      {
        unfold s. simpl.
        repeat inline_pair. simpl.
        fold q. apply sur_input_le_return.
      }
      assert (r = s) as Hrs.
      {
        unfold s. simpl.
        repeat inline_pair. simpl.
        fold q. fold r. reflexivity.
      }

      simpl. ifauto. fold MA M'A q MB M'B.
      assert (x = p \/ x = S p \/ (S (S p)) <= x < q \/ q <= x < s) as [Hxp | [HxSp | [Hpxq | Hqxs]]] by lia.
      (* x = p *)
      + unfold MB, M'B.
        rewrite <- (named_model_changes_sur_only M'A)...
        rewrite <- (named_model_changes_sur_only MA)...
        unfold MA, M'A.
        rewrite Hxp.
        repeat rewrite named_model_vals_name_iff_force.
        apply Nnf.meaningful_valuations.
        apply (Nnf.agree_l A B). assumption.

      (* x = S p *)
      + unfold MB, M'B.
        rewrite HxSp.
        repeat rewrite named_model_vals_name_iff_force.
        apply Nnf.meaningful_valuations.
        unfold Nnf.agree.
        (* MA and M'A agree *)
        intros w' x' Hx'_in_B.
        unfold MA, M'A.
        rewrite <- (named_model_changes_sur_only M')...
        rewrite <- (named_model_changes_sur_only M)...
        apply (Nnf.agree_r A B)...

      (* S (S p) <= x < q *)
      + assert (Kripke.valuation MA w x <-> Kripke.valuation MB w x) as Hval_MA_MB.
        { unfold MB. apply named_model_changes_sur_only... }
        assert (Kripke.valuation M'A w x <-> Kripke.valuation M'B w x) as Hval_M'A_M'B.
        { unfold MB. apply named_model_changes_sur_only... }
        rewrite <- Hval_MA_MB.
        rewrite <- Hval_M'A_M'B.
        apply IHA...
        apply (Nnf.agree_l A B)...

      (* q <= x < s *)
      + unfold MB, M'B.
        apply IHB...
        * fold r. lia.
        * intros w' x' Hx'_in_B.
          unfold MA, M'A.
          rewrite <- (named_model_changes_sur_only M')...
          rewrite <- (named_model_changes_sur_only M)...
          apply (Nnf.agree_r A B)...

    - simpl. simpl in Hmnp_lt. ifauto.
      set (q := snd (Mcnfc.from_n_nnf p A (S p))).
      assert (q = s) as Hqs.
      { unfold s. simpl. inline_pair. simpl. reflexivity. }

      assert (x = p \/ S p <= x < s) as [Hxp | HSpxs] by lia.
      + rewrite Hxp.
        repeat rewrite named_model_vals_name_iff_force.
        apply Nnf.meaningful_valuations. assumption.
      + apply IHA... fold q. lia.

    - simpl. simpl in Hmnp_lt. ifauto.
      set (q := snd (Mcnfc.from_n_nnf p A (S p))).
      assert (q = s) as Hqs.
      { unfold s. simpl. inline_pair. simpl. reflexivity. }

      assert (x = p \/ S p <= x < s) as [Hxp | HSpxs] by lia.
      + rewrite Hxp.
        repeat rewrite named_model_vals_name_iff_force.
        apply Nnf.meaningful_valuations. assumption.
      + apply IHA... fold q. lia.
  Qed.
End EquisatModelRange.



Section NnfToMcnf.
  Variable W : Type.
  Variable R : relation W.
  Variable M : @Kripke.t W R.

  Definition IH phi :=
    forall w0 n p, Nnf.max_atm phi < n < p ->
    let M' := named_model M n phi p in
    Mcnf.force M' w0 (fst (Mcnfc.from_n_nnf n phi p)).


  Lemma lit_sat : forall (l : Lit.t), IH (Nnf.Lit l).
  Proof with simpl; auto; try autolia.
    intros l w0 n p Hmnp_lt.
    simpl. split...
    pose proof (classic (Nnf.force M w0 (Nnf.Lit l))) as [HM_force_l | HM_nforce_l].
    (* forces l *)
    + exists l. simpl in *. split...
      destruct l as [x|x]; simpl in *; ifauto.
    (* does not force l *)
    + exists (Lit.Neg n). simpl in *. split... ifauto...
  Qed.


  Lemma and_sat : forall (A B : Nnf.t) (IHA : IH A) (IHB : IH B), IH (Nnf.And A B).
  Proof with try finish.
    intros A B IHA IHB w0 n p Hmnp_lt M'.
    simpl.
    destruct_pair (Mcnfc.from_n_nnf p A (S (S p))) as [A_mcnf q].
    destruct_pair (Mcnfc.from_n_nnf (S p) B q) as [B_mcnf r].
    simpl in *.

    set (MA := named_model M p A (S (S p))).
    set (MB := named_model MA (S p) B q).
    (* assert (S (S p) <= q) as Hpq. { unfold q. apply sur_input_le_return. }
    assert (q <= r) as Hqr. { unfold r. apply sur_input_le_return. } *)

    fold MA q MB in M'.

    specialize (IHA w0 p (S (S p))). forward IHA by lia.
    fold MA A_mcnf in IHA. simpl in IHA.
    specialize (IHB w0 (S p) q). forward IHB by autolia.
    set (MBIH := named_model M (S p) B q).
    fold MBIH B_mcnf in IHB. simpl in IHB.

    rewrite Mcnf.mcnf_force_and.
    repeat split.
    (* forces ~n or p *)
    {
      pose proof (classic (Nnf.force M w0 (Nnf.And A B))) as [HM_force_AB | HM_nforce_AB].
      (* M |= A /\ B *)
      (* then M |= A *)
      (* so M' values p *)
      - unfold M', set_kripke_at_n_iff_force.
        exists (Lit.Pos p). split...
        simpl. ifauto.
        unfold MB. rewrite <- named_model_changes_sur_only...
        unfold MA. apply named_model_vals_name_iff_force...
        simpl in HM_force_AB. tauto.
      (* M |/= A /\ B *)
      (* then M' values ~n *)
      - unfold M', set_kripke_at_n_iff_force.
        exists (Lit.Neg n). split...
    }
    (* forces ~n or S p *)
    {
      pose proof (classic (Nnf.force M w0 (Nnf.And A B))) as [HM_force_AB | HM_nforce_AB].
      (* M |= A /\ B *)
      (* then M |= A *)
      (* so M' values S p *)
      - unfold M'.
        exists (Lit.Pos (S p)).
        (* coq is simplifying too far, need to prevent it from simplifying (S p) =? n *)
        remember (S p) as nB. simpl.
        split; try tauto.
        ifauto.
        apply named_model_vals_name_iff_force...

        (* MA force B <-> M force B *)
        apply (Nnf.meaningful_valuations M MA).
        + unfold Nnf.agree.
          intros w x Hx_in_B.
          unfold MA. rewrite <- named_model_changes_sur_only; try tauto...
        + simpl in HM_force_AB. tauto.

      (* M |/= A /\ B *)
      (* then M' values ~n *)
      - unfold M', set_kripke_at_n_iff_force.
        exists (Lit.Neg n). split...
    }
    (* forces A_mcnf *)
    {
      apply (Mcnf.meaningful_valuations M' MA).
      (* valuations equal for x in mcnf *)
      - intros w x Hx_in_A_mcnf.

        (* x range *)
        pose proof (conv_atm_range A p (S (S p))) as Hx_range.
        forward Hx_range by lia. specialize (Hx_range x).
        inline_pair in Hx_range. forward Hx_range by assumption.

        assert (x <> n). { destruct Hx_range... }

        simpl. ifauto. unfold MB.
        symmetry. apply named_model_changes_sur_only.
        + autolia.
        + apply and_not_or. fold r. split...
          * destruct Hx_range...
          * destruct Hx_range...
      (* M' and MA force p at w0 *)
      - apply IHA.
    }
    (* forces B_mcnf *)
    {
      apply (Mcnf.meaningful_valuations M' MB).
      (* valuations equal for x in mcnf *)
      - intros w x Hx_in_A_mcnf.

        (* x range *)
        pose proof (conv_atm_range B (S p) q) as Hx_range.
        forward Hx_range by autolia. specialize (Hx_range x).
        inline_pair in Hx_range. forward Hx_range by assumption.

        assert (x <> n). { destruct Hx_range... }

        simpl. ifauto. reflexivity.
      (* MB forces B_mcnf *)
      - apply (Mcnf.meaningful_valuations MB MBIH)...
        (* show that valuation of MB and MBIH are equal *)
        intros w x Hx_in_B_mcnf.

        pose proof (conv_atm_range B (S p) q) as Hx_range.
        forward Hx_range by autolia. specialize (Hx_range x).
        inline_pair in Hx_range. forward Hx_range by assumption.
        fold r in Hx_range.

        destruct Hx_range as [Hx_in_B | [HxSp | Hqxr]]...
        + assert (Kripke.valuation M w x <-> Kripke.valuation MA w x) as Heqval_M_MA.
          { unfold MA. apply named_model_changes_sur_only... }
          assert (Kripke.valuation MA w x <-> Kripke.valuation MB w x) as Heqval_MA_MB.
          { unfold MB. apply named_model_changes_sur_only...  }
          unfold MBIH.
          rewrite <- Heqval_MA_MB. rewrite <- Heqval_M_MA.
          apply named_model_changes_sur_only...

        + unfold MB, MBIH.
          subst x.
          repeat rewrite named_model_vals_name_iff_force...

          apply Nnf.meaningful_valuations.
          unfold Nnf.agree. intros w' x Hx_in_B.

          assert (x <= Nnf.max_atm B). { apply Nnf.atm_le_max... }
          unfold MA.
          rewrite <- named_model_changes_sur_only...
        + unfold MBIH. unfold MB.
          apply named_model_overrides_all_sur with (phi := B) (n:=(S p)) (p:=q)...
          (* models agree on phi *)
          unfold Nnf.agree.
          intros w' x' Hx'_in_B.
          unfold MA. symmetry. apply named_model_changes_sur_only...
    }
  Qed.


  Lemma or_sat : forall (A B : Nnf.t) (IHA : IH A) (IHB : IH B), IH (Nnf.Or A B).
  Proof with simpl; auto; try autolia.
    intros A B IHA IHB w0 n p Hmnp_lt M'.
    simpl.
    destruct_pair (Mcnfc.from_n_nnf p A (S (S p))) as [A_mcnf q].
    destruct_pair (Mcnfc.from_n_nnf (S p) B q) as [B_mcnf r].
    simpl in *.

    set (MA := named_model M p A (S (S p))).
    set (MB := named_model MA (S p) B q).

    fold MA q MB in M'.

    specialize (IHA w0 p (S (S p))). forward IHA by lia.
    fold MA A_mcnf in IHA. simpl in IHA.
    specialize (IHB w0 (S p) q). forward IHB by autolia.
    set (MBIH := named_model M (S p) B q).
    fold MBIH B_mcnf in IHB. simpl in IHB.

    rewrite Mcnf.mcnf_force_and.
    repeat split.
    (* forces ~n or p or S p *)
    {
      pose proof (classic (Nnf.force M w0 (Nnf.Or A B))) as [[HM_force_A | HM_force_B] | HM_nforce_AB].
      (* M |= A *)
      - unfold M', set_kripke_at_n_iff_force.
        exists (Lit.Pos p). split... ifauto.
        unfold MB. rewrite <- named_model_changes_sur_only...
        unfold MA. apply named_model_vals_name_iff_force...
      (* M |= B *)
      - unfold M', set_kripke_at_n_iff_force.
        exists (Lit.Pos (S p)).
        (* simpl goes too far with S p, makes it hard to resolve. *)
        (* remember to avoid simplifying too far. *)
        remember (S p) as nB. split... ifauto.

        (* forces B <-> nB valued *)
        unfold MB. apply named_model_vals_name_iff_force...

        (* but MB is applied on top of. show that M and MA agree on A *)
        apply (Nnf.meaningful_valuations M MA)...
        unfold Nnf.agree.
        intros w x Hx_in_B.
        apply named_model_changes_sur_only...

      (* M |/= A /\ B *)
      (* then M' values ~n *)
      - unfold M', set_kripke_at_n_iff_force.
        exists (Lit.Neg n). split... ifauto.
    }
    (* forces A_mcnf *)
    {
      apply (Mcnf.meaningful_valuations M' MA).
      (* valuations equal for x in mcnf *)
      - intros w x Hx_in_A_mcnf.

        (* x range *)
        pose proof (conv_atm_range A p (S (S p))) as Hx_range.
        forward Hx_range by lia. specialize (Hx_range x).
        inline_pair in Hx_range. forward Hx_range by assumption.

        assert (x <> n). { destruct Hx_range... }

        simpl. ifauto. unfold MB.
        symmetry. apply named_model_changes_sur_only.
        + autolia.
        + apply and_not_or. fold r. split...
          * destruct Hx_range...
          * destruct Hx_range...
      - apply IHA.
    }
    (* forces B_mcnf *)
    {
      apply (Mcnf.meaningful_valuations M' MB).
      (* valuations equal for x in mcnf *)
      - intros w x Hx_in_A_mcnf.

        (* x range *)
        pose proof (conv_atm_range B (S p) q) as Hx_range.
        forward Hx_range by autolia. specialize (Hx_range x).
        inline_pair in Hx_range. forward Hx_range by assumption.

        assert (x <> n). { destruct Hx_range... }

        simpl. ifauto. reflexivity.
      (* MB forces B_mcnf *)
      - apply (Mcnf.meaningful_valuations MB MBIH)...
        (* show that valuation of MB and MBIH are equal *)
        intros w x Hx_in_B_mcnf. fold B_mcnf in Hx_in_B_mcnf |-.

        pose proof (conv_atm_range B (S p) q) as Hx_range.
        forward Hx_range by autolia. specialize (Hx_range x).
        inline_pair in Hx_range. forward Hx_range by assumption.
        fold r in Hx_range.

        destruct Hx_range as [Hx_in_B | [HxSp | Hqxr]]...
        + assert (Kripke.valuation M w x <-> Kripke.valuation MA w x) as Heqval_M_MA.
          { unfold MA. apply named_model_changes_sur_only... }
          assert (Kripke.valuation MA w x <-> Kripke.valuation MB w x) as Heqval_MA_MB.
          { unfold MB. apply named_model_changes_sur_only...  }
          unfold MBIH.
          rewrite <- Heqval_MA_MB. rewrite <- Heqval_M_MA.
          apply named_model_changes_sur_only...
        + unfold MB, MBIH. subst x.
          repeat rewrite named_model_vals_name_iff_force...

          apply Nnf.meaningful_valuations.
          unfold Nnf.agree. intros w' x Hx_in_B.

          assert (x <= Nnf.max_atm B). { apply Nnf.atm_le_max... }
          unfold MA.
          rewrite <- named_model_changes_sur_only... reflexivity.

        + unfold MBIH. unfold MB.
          apply named_model_overrides_all_sur with (phi := B) (n:=(S p)) (p:=q)...
          (* models agree on phi *)
          unfold Nnf.agree.
          intros w' x' Hx'_in_B.
          unfold MA. symmetry. apply named_model_changes_sur_only...
    }
  Qed.


  Lemma box_sat : forall (A : Nnf.t) (IHA : IH A), IH (Nnf.Box A).
  Proof with simpl; auto; try autolia.
    intros A IHA w0 n p Hmnp_lt M'.
    simpl.
    destruct_pair (Mcnfc.from_n_nnf p A (S p)) as [A_mcnf q].

    simpl in *. split.
    (* all neighbours force *)
    {
      intro Hnbr. ifauto in Hnbr.
      (* destruct Hnbr as [dnbr [Hrel_dnbr HM_force_nbr]]. *)

      intros nbr Hrel_nbr.
      ifauto.
      apply named_model_vals_name_iff_force...
    }

    (* M' forces []A_mcnf *)
    {
      (* M' forces A_mcnf at every neighbour *)
      rewrite Mcnf.w0_force_ctx_iff_nbr_force_phi.
      intros nbr Hrel_nbr.

      (* apply IH on the neighbour *)
      unfold IH in IHA.
      specialize (IHA nbr p (S p)). forward IHA by lia.

      fold A_mcnf in IHA.
      set (M'IH := named_model M p A (S p)) in IHA.

      apply (Mcnf.meaningful_valuations M' M'IH)...
        (* valuations equal for x <> p *)
      intros w x Hx_in_A_mcnf. fold A_mcnf in Hx_in_A_mcnf.

      (* x range *)
      pose proof (conv_atm_range A p (S p)) as Hx_range.
      forward Hx_range by lia. specialize (Hx_range x).
      inline_pair in Hx_range. forward Hx_range by assumption.

      assert (x <> n) as Hx_ne_n. { destruct Hx_range... }
      unfold M'IH, M'. simpl. ifauto. reflexivity.
    }
  Qed.


  Lemma dia_sat : forall (A : Nnf.t) (IHA : IH A), IH (Nnf.Dia A).
  Proof with simpl; auto; try autolia.
    intros A IHA w0 n p Hmnp_lt M'.
    simpl.
    destruct_pair (Mcnfc.from_n_nnf p A (S p)) as [A_mcnf q].

    simpl in *. split.
    (* exists a neighbour that forces *)
    {
      intro Hnbr. ifauto in Hnbr.
      destruct Hnbr as [dnbr [Hrel_dnbr HM_force_nbr]].

      exists dnbr. split...
      ifauto.
      apply named_model_vals_name_iff_force...
    }

    (* M' forces []A_mcnf *)
    {
      (* M' forces A_mcnf at every neighbour *)
      rewrite Mcnf.w0_force_ctx_iff_nbr_force_phi.
      intros nbr Hrel_nbr.

      (* apply IH on the neighbour *)
      unfold IH in IHA.
      specialize (IHA nbr p (S p)). forward IHA by lia.

      fold A_mcnf in IHA.
      set (M'IH := named_model M p A (S p)) in IHA.

      apply (Mcnf.meaningful_valuations M' M'IH)...
        (* valuations equal for x <> p *)
      intros w x Hx_in_A_mcnf. fold A_mcnf in Hx_in_A_mcnf.

      (* x range *)
      pose proof (conv_atm_range A p (S p)) as Hx_range.
      forward Hx_range by lia. specialize (Hx_range x).
      inline_pair in Hx_range. forward Hx_range by assumption.

      assert (x <> n) as Hx_ne_n. { destruct Hx_range... }
      unfold M'IH, M'. simpl. ifauto. reflexivity.
    }
  Qed.


  Theorem M'_force_n_impl_phi :
    forall (w0 : W) (phi : Nnf.t) (n p : nat) (Hmnp_lt : Nnf.max_atm phi < n < p),
    let M' := (named_model M n phi p) in
      Mcnf.force M' w0 (fst (Mcnfc.from_n_nnf n phi p)).
  Proof with simpl; auto; try autolia.
    intros w0 phi. revert w0.

    induction phi as
      [ l
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ]; intros w0 n p Hmnp_lt M'.

    - apply lit_sat...
    - apply and_sat...
    - apply or_sat...
    - apply box_sat...
    - apply dia_sat...
  Qed.


  Theorem nnf_to_mcnf_forces :
    forall (w0 : W) (phi : Nnf.t) (n p : nat),
    Nnf.max_atm phi < n < p ->
    Nnf.force M w0 phi ->
    Mcnf.force
      (named_model M n phi p)
      w0
      (Mcnfc.from_nnf_with_sur n phi p).
  Proof with simpl; try lia; auto.
    intros w0 phi n p Hmnp_lt HMforce_phi.
    unfold Mcnfc.from_nnf_with_sur. simpl.
    split.
    - exists (Lit.Pos n). split...
      apply named_model_vals_name_iff_force...
    - apply M'_force_n_impl_phi...
  Qed.
End NnfToMcnf.



Theorem sat_nnf_to_mcnf :
  forall (phi : Nnf.t), Nnf.satisfiable phi -> Mcnf.satisfiable (Mcnfc.from_nnf phi).
Proof with simpl; try lia; auto.
  intros phi Hphi_sat.
  unfold Nnf.satisfiable in Hphi_sat.
  destruct Hphi_sat as [W [R [M [w0 HM_force_phi]]]].

  unfold Mcnf.satisfiable.
  set (n := S (Nnf.max_atm phi)).
  exists W, R, (named_model M n phi (S n)), w0.
  apply nnf_to_mcnf_forces...
Qed.


Theorem mcnf_to_nnf_forces :
  forall {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : Nnf.t) (n p : nat) (Hmnp_lt : Nnf.max_atm phi < n < p),
  Mcnf.force M w0 (Mcnfc.from_nnf_with_sur n phi p) -> Nnf.force M w0 phi.
Proof with try finish.
  intros W R M w0 phi.
  revert w0.

  induction phi as
    [ l
    | A IHA B IHB
    | A IHA B IHB
    | phi IHphi
    | phi IHphi
    ]; intros w0 n p Hmnp_lt Hforce_mcnf; simpl in Hforce_mcnf.

  - simpl.
    destruct Hforce_mcnf as [HM_val_n HM_force_nn_l].

    destruct HM_val_n as [x [[Hxn | F] Hforce_n]]... subst x.
    simpl in Hforce_n.

    destruct HM_force_nn_l as [[x [Hx Hforce_x]] _]. cbn in Hx.
    destruct Hx as [Hxnn | [Hlx | F]]...
    (* x is ~n: contradiction *)
    + rewrite <- Hxnn in Hforce_x. simpl in Hforce_x. contradiction.
    + rewrite <- Hlx in Hforce_x. assumption.

  (* and *)
  - simpl in Hmnp_lt.
    destruct_pair (Mcnfc.from_n_nnf p A (S (S p))) as [A_mcnf q] in Hforce_mcnf.
    destruct_pair (Mcnfc.from_n_nnf (S p) B q) as [B_mcnf r] in Hforce_mcnf.
    simpl in Hforce_mcnf.

    (* show that forces n, p and S p *)
    destruct Hforce_mcnf as [Hforce_n [Hforce_nn_p [Hforce_nn_Sp Hforce_mcnf]]].
    (* forces n *)
    destruct Hforce_n as [x [[Hnx | F] Hforce_n]]...
    rewrite <- Hnx in Hforce_n. clear x Hnx. simpl in Hforce_n.
    (* forces p *)
    destruct Hforce_nn_p as [x [[Hnnx | [Hpx | F]] Hforce_p]]...
    { rewrite <- Hnnx in Hforce_p. simpl in Hforce_p. contradiction. }
    rewrite <- Hpx in Hforce_p. clear x Hpx. simpl in Hforce_p.
    (* forces S p *)
    destruct Hforce_nn_Sp as [x [[Hnnx | [HSpx | F]] Hforce_Sp]]...
    { rewrite <- Hnnx in Hforce_Sp. simpl in Hforce_Sp. contradiction. }
    rewrite <- HSpx in Hforce_Sp. clear x HSpx. simpl in Hforce_Sp.

    rewrite Mcnf.mcnf_force_and in Hforce_mcnf.
    destruct Hforce_mcnf as [Hforce_A_mcnf Hforce_B_mcnf].

    split.
    (* forces A *)
    + apply (IHA w0 p (S (S p)))... split...
      exists (Lit.Pos p)...
    (* forces B *)
    + apply (IHB w0 (S p) q)... split...
      exists (Lit.Pos (S p))...

  (* or *)
  - simpl in Hmnp_lt.
    destruct_pair (Mcnfc.from_n_nnf p A (S (S p))) as [A_mcnf q] in Hforce_mcnf.
    destruct_pair (Mcnfc.from_n_nnf (S p) B q) as [B_mcnf r] in Hforce_mcnf.
    simpl in Hforce_mcnf.

    (* show that forces n, p and S p *)
    destruct Hforce_mcnf as [Hforce_n [Hforce_nn_p_Sp Hforce_mcnf]].

    rewrite Mcnf.mcnf_force_and in Hforce_mcnf.
    destruct Hforce_mcnf as [Hforce_A_mcnf Hforce_B_mcnf].

    (* forces n *)
    destruct Hforce_n as [x [[Hnx | F] Hforce_n]]...
    rewrite <- Hnx in Hforce_n. clear x Hnx. simpl in Hforce_n.
    (* forces p OR S p *)
    destruct Hforce_nn_p_Sp as [x [[Hnnx | [Hpx | [HSpx | F]]] Hforce_x]]...
    { rewrite <- Hnnx in Hforce_x. simpl in Hforce_x. contradiction. }

    (* forces p: left branch *)
    + rewrite <- Hpx in Hforce_x. clear x Hpx.
      left.
      apply (IHA w0 p (S (S p)))... split...
      exists (Lit.Pos p)...
    (* forces S p: right branch *)
    + rewrite <- HSpx in Hforce_x. clear x HSpx.
      right.
      apply (IHB w0 (S p) q)... split...
      exists (Lit.Pos (S p))...

  (* box *)
  - simpl in Hmnp_lt.
    destruct_pair (Mcnfc.from_n_nnf p phi (S p)) as [A_mcnf q] in Hforce_mcnf.
    simpl in Hforce_mcnf.

    destruct Hforce_mcnf as [Hforce_n [Hforce_nbrs Hforce_ctx]].

    (* simplify Hforce_n *)
    destruct Hforce_n as [x [[Hnx | F] Hforce_n]]...
    rewrite <- Hnx in Hforce_n. clear x Hnx. simpl in Hforce_n.

    forward Hforce_nbrs by assumption.

    rewrite Mcnf.w0_force_ctx_iff_nbr_force_phi in Hforce_ctx.

    intros nbr Hrel_nbr.

    apply (IHphi nbr p (S p))... split...
    exists (Lit.Pos p)...
  
  - simpl in Hmnp_lt.
    destruct_pair (Mcnfc.from_n_nnf p phi (S p)) as [A_mcnf q] in Hforce_mcnf.
    simpl in Hforce_mcnf.

    destruct Hforce_mcnf as [Hforce_n [Hforce_dnbr Hforce_ctx]].

    (* simplify Hforce_n *)
    destruct Hforce_n as [x [[Hnx | F] Hforce_n]]...
    rewrite <- Hnx in Hforce_n. clear x Hnx. simpl in Hforce_n.

    forward Hforce_dnbr by assumption.
    destruct Hforce_dnbr as [dnbr [Hrel_dnbr Hval_p]].

    rewrite Mcnf.w0_force_ctx_iff_nbr_force_phi in Hforce_ctx.

    exists dnbr. split...

    apply (IHphi dnbr p (S p))... split...
    exists (Lit.Pos p)...
Qed.



Lemma sat_mcnf_to_nnf :
  forall (phi : Nnf.t), Mcnf.satisfiable (Mcnfc.from_nnf phi) -> Nnf.satisfiable phi.
Proof with simpl; try autolia; auto.
  intros phi Hmcnf_sat.

  unfold Mcnf.satisfiable in Hmcnf_sat.
  destruct Hmcnf_sat as [W [R [M [w0 Hforce_mcnf]]]].

  unfold Nnf.satisfiable.
  exists W, R, M, w0.

  set (n := S (Nnf.max_atm phi)).

  apply mcnf_to_nnf_forces with (n:=n) (p:=S n)...
Qed.


Theorem nnf_mcnf_equisat :
  forall (phi : Nnf.t), Nnf.satisfiable phi <-> Mcnf.satisfiable (Mcnfc.from_nnf phi).
Proof.
  intro phi. split.
  - apply (sat_nnf_to_mcnf phi).
  - apply (sat_mcnf_to_nnf phi).
Qed.
