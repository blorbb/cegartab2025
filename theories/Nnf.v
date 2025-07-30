From Stdlib Require List.
From Stdlib Require Import Classical Lia PeanoNat.

From CegarTableaux Require Lit Kripke Fml.
From CegarTableaux Require Import Utils.


Inductive t : Type :=
  | Lit (p : Lit.t)
  | And (phi psi : t)
  | Or  (phi psi : t)
  | Box (phi : t)
  | Dia (phi : t).

(* TODO: create nnf_simplify function *)


Section Satisfiability.
  Fixpoint force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
    match phi with
    | Lit l   => Lit.force M w0 l
    | And A B => force M w0 A /\ force M w0 B
    | Or  A B => force M w0 A \/ force M w0 B
    | Box A   => forall nbr, R w0 nbr -> force M nbr A
    | Dia A   => exists nbr, R w0 nbr /\ force M nbr A
    end.


  Definition nnfs_force {W} {R} (M : @Kripke.t W R) (w0 : W) (phis : list t) : Prop :=
    forall (phi : t), List.In phi phis -> force M w0 phi.


  Definition satisfiable (phi : t) : Prop :=
    exists W R (M : @Kripke.t W R) (w0 : W), force M w0 phi.


  Definition unsatisfiable (phi : t) : Prop :=
    forall W R (M : @Kripke.t W R) (w0 : W), ~ force M w0 phi.
End Satisfiability.



Section Conversion.
  Fixpoint negate (phi : t) : t :=
    match phi with
    | Lit l   => Lit (Lit.negate l)
    | And A B => Or  (negate A) (negate B)
    | Or  A B => And (negate A) (negate B)
    | Box A   => Dia (negate A)
    | Dia A   => Box (negate A)
    end.


  Fixpoint from_fml (phi : Fml.t) : t :=
    match phi with
    | Fml.Var  x   => Lit (Lit.Pos x)
    | Fml.Neg  A   => negate (from_fml A)
    | Fml.And  A B => And (from_fml A) (from_fml B)
    | Fml.Or   A B => Or  (from_fml A) (from_fml B)
    | Fml.Impl A B => Or  (negate (from_fml A)) (from_fml B)
    | Fml.Box  A   => Box (from_fml A)
    | Fml.Dia  A   => Dia (from_fml A)
    end.
End Conversion.



(* correctness of the from_fml conversion *)
Section Correctness.
  Theorem force_negate_iff_not_force {W} {R} (M : @Kripke.t W R) :
    forall w0 phi, force M w0 (negate phi) <-> ~ force M w0 phi.
  Proof.
    intros w0 phi.
    revert w0. (* make the induction hypothesis on 'forall w0' *)
    induction phi as
      [ x
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ]; intro w0; simpl.
    (* literals *)
    - destruct x.
      + reflexivity.
      + simpl. tauto.
    (* And, Or *)
    - rewrite IHA. rewrite IHB. tauto.
    - rewrite IHA. rewrite IHB. tauto.
    (* Box *)
    - split.
      (* exists neighbour : not A sat -> not all neighbours force *)
      + intros Hexists Hforall.
        destruct Hexists as [neighbour [Hrelated Hforces]].
        specialize (Hforall neighbour Hrelated). (* remove the forall *)
        apply IHA in Hforces.
        contradiction.
      (* not all neighbours force -> exists neighbour : not A sat *)
      + intros Hforall.
        apply not_all_ex_not in Hforall.
        destruct Hforall as [neighbour Himpl].
        apply not_imply_elim in Himpl as Hrelated.
        apply not_imply_elim2 in Himpl as Hforces.
        exists neighbour.
        split.
        * apply Hrelated.
        * apply IHA. apply Hforces.
    (* Dia *)
    - split.
      (* all neighbours force not A -> doesn't exist neighbour : force A *)
      + intros Hforall Hexists.
        destruct Hexists as [neighbour [Hrelated Hforces]].
        specialize (Hforall neighbour Hrelated).
        apply IHA in Hforall.
        contradiction.
      + intros Hexists neighbour Hrelated.
        apply not_ex_all_not with (n := neighbour) in Hexists.
        apply not_and_or in Hexists.
        destruct Hexists as [contra | not_nnf].
        * contradiction.
        * apply IHA. exact not_nnf.
  Qed.


  Theorem force_fml_iff_force_nnf :
    forall {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : Fml.t),
    Fml.force M w0 phi <-> force M w0 (from_fml phi).
  Proof.
    intros W R M w0 phi. revert w0.
    induction phi as
      [ x
      | A IHA
      | A IHA B IHB
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ]; intro w0; simpl.
    (* Var x *)
    - tauto.
    (* Neg fml *)
    - rewrite force_negate_iff_not_force. rewrite IHA. reflexivity.
    (* A /\ B *)
    - rewrite IHA. rewrite IHB. reflexivity.
    (* A \/ B *)
    - rewrite IHA. rewrite IHB. reflexivity.
    (* A -> B *)
    - rewrite IHA. rewrite IHB. rewrite force_negate_iff_not_force. tauto.
    (* []A *)
    - setoid_rewrite IHA. reflexivity.
    (* <>A *)
    - setoid_rewrite IHA. reflexivity.
  Qed.


  Theorem force_fmls_iff_force_nnfs :
    forall {W} {R} (M : @Kripke.t W R) (w0 : W) (fmls : list Fml.t),
    Fml.fmls_force M w0 fmls <-> nnfs_force M w0 (List.map from_fml fmls).
  Proof.
    intros W R M w0 fmls.
    induction fmls as [|first rest IHrest].
    (* base case *)
    - simpl.
      unfold Fml.fmls_force. unfold nnfs_force.
      simpl. tauto.
    (* induction on (first :: rest) *)
    - split.
      (* fml sat -> nnf sat *)
      + intros Hfml_force phi_nnf Hin.
        destruct Hin as [Hfirst | Hrest].
        * rewrite <- Hfirst. 
          apply force_fml_iff_force_nnf.
          apply Hfml_force. now left.
        * apply IHrest; try assumption.
          intros phi Hphi_in_rest.
          apply Hfml_force. now right.
      (* nnf sat -> fml sat *)
      + intros Hnnf_force phi Hphi_in.
        specialize (Hnnf_force (from_fml phi)).
        rewrite force_fml_iff_force_nnf. apply Hnnf_force.
        rewrite List.in_map_iff.
        exists phi. tauto.
  Qed.
End Correctness.



(* Definitions And theorems relating to the structure of an NNF formula. *)
Section Range.
  Fixpoint max_atm (phi : t) : nat :=
    match phi with
    | Lit (Lit.Pos x) => x
    | Lit (Lit.Neg x) => x
    | And A B => Nat.max (max_atm A) (max_atm B)
    | Or  A B => Nat.max (max_atm A) (max_atm B)
    | Box A   => max_atm A
    | Dia A   => max_atm A
    end.

  Fixpoint In (x : nat) (phi : t) : Prop :=
    match phi with
    | Lit (Lit.Pos y) => x = y
    | Lit (Lit.Neg y) => x = y
    | And A B => In x A \/ In x B
    | Or  A B => In x A \/ In x B
    | Box A   => In x A
    | Dia A   => In x A
    end.


  Corollary atm_in_nnf_atm :
    forall (l : Lit.t), In (Lit.atm l) (Lit l).
  Proof.
    intros l. destruct l; reflexivity.
  Qed.


  Theorem atm_le_max : forall (phi : t) (x : nat),
    In x phi -> x <= (max_atm phi).
  Proof.
    intros phi x Hx_in_nnf.

    induction phi as
      [ l
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ].
    - simpl in *. destruct l; lia.
    - simpl in *. destruct Hx_in_nnf.
      + forward IHA by assumption. lia.
      + forward IHB by assumption. lia.
    - simpl in *. destruct Hx_in_nnf.
      + forward IHA by assumption. lia.
      + forward IHB by assumption. lia.
    - simpl in *. forward IHA by assumption. lia.
    - simpl in *. forward IHA by assumption. lia.
  Qed.


  Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
    forall (w : W) (x : nat), In x phi -> (Kripke.valuation M w x <-> Kripke.valuation M' w x).


  (* some proofs in mcnf a bit easier -- agree on phi -> agree on subformulas of phi *)
  Corollary agree_l {W} {R} {M M' : @Kripke.t W R} (left right : t) :
    agree (And left right) M M' -> agree left M M'.
  Proof.
    intro Hagree.
    unfold agree in *.
    intros w p Hp_in_left.
    apply Hagree. simpl. now left.
  Qed.


  Corollary agree_r {W} {R} {M M' : @Kripke.t W R} (left right : t) :
    agree (And left right) M M' -> agree right M M'.
  Proof.
    intro Hagree.
    unfold agree in *.
    intros w p Hp_in_right.
    apply Hagree. simpl. now right.
  Qed.


  Theorem meaningful_valuations :
    forall {W} {R} (M M' : @Kripke.t W R) (w : W) (phi : t),
      agree phi M M' -> (force M w phi <-> force M' w phi).
  Proof with simpl; auto.
    intros W R M M' w phi Hagree. revert w Hagree.
    induction phi as
      [ l
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ]; intros w Hagree.
    (* literal base case *)
    - split.
      + intro HMforce.
        set (x := Lit.atm l).
        assert (Hin : In x (Lit l)) by apply atm_in_nnf_atm.
        specialize (Hagree w x Hin).
        simpl in *.
        unfold Lit.force in *.
        (* (~) valuation M' w p0 = (~) valuation m w p *)
        destruct l; subst x; rewrite <- Hagree; exact HMforce.
      + intro HMforce.
        set (x := Lit.atm l).
        assert (Hin : In x (Lit l)) by apply atm_in_nnf_atm.
        specialize (Hagree w x Hin).
        simpl in *.
        unfold Lit.force in *.
        (* (~) valuation M' w p0 = (~) valuation m w p *)
        destruct l; subst x; rewrite -> Hagree; exact HMforce.
    (* And case *)
    - split.
      (* M forces -> M' forces *)
      + intro HMforce.
        simpl. split.
        { (* forces A *)
          apply IHA.
          - intros w0 p Hin.
            apply Hagree. simpl. now left.
          - apply HMforce.
        }
        { (* forces B *)
          apply IHB.
          - intros w0 p Hin.
            apply Hagree. simpl. now right.
          - apply HMforce.
        }
      (* M' forces -> M forces *)
      + intro HM'force.
        simpl. split.
        { (* forces A *)
          apply IHA.
          - intros w0 p Hin.
            apply Hagree. simpl. now left.
          - apply HM'force.
        }
        { (* forces B *)
          apply IHB.
          - intros w0 p Hin.
            apply Hagree. simpl. now right.
          - apply HM'force.
        }
    (* Or case *)
    - split.
      (* M forces -> M' forces *)
      + intro HMforce.
        simpl. simpl in HMforce. destruct HMforce as [Hforce_a|Hforce_b].
        { (* forces A *)
          left. apply IHA.
          - intros w0 p Hin.
            apply Hagree. simpl. now left.
          - exact Hforce_a.
        }
        { (* forces B *)
          right. apply IHB.
          - intros w0 p Hin.
            apply Hagree. simpl. now right.
          - exact Hforce_b.
        }
      (* M' forces -> M forces *)
      + intro HM'force.
        simpl. simpl in HM'force. destruct HM'force as [Hforce_a|Hforce_b].
        { (* forces A *)
          left. apply IHA...
          intros w0 p Hin.
          apply Hagree. simpl. now left.
        }
        { (* forces B *)
          right. apply IHB...
          intros w0 p Hin.
          apply Hagree. simpl. now right.
        }
    (* Box case *)
    - simpl. split.
      + intros HMforce neighbour HM'rel.
        apply IHA...
      + intros HM'force neighbour HMrel.
        apply IHA...
    - simpl. split.
      + intros HMforce.
        destruct HMforce as [neighbour [Hn_rel Hn_force]].
        exists neighbour.
        split...
        apply IHA...

      + intros HM'force.
        destruct HM'force as [neighbour [Hn_rel Hn_force]].
        exists neighbour.
        split...
        apply IHA...
  Qed.
End Range.
