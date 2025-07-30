From Stdlib Require Import PeanoNat Setoids.Setoid Classical Lia.
From Stdlib Require List.

From CegarTableaux Require Lit Nnf Kripke Mclause.
From CegarTableaux Require Import Utils.

Import List.ListNotations.
Open Scope list_scope.


(** MCNF type with basic lemmas and definitions *)

Definition t := list Mclause.t.


Fixpoint force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  match phi with
  | [] => True
  | head :: tail => Mclause.force M w0 head /\ force M w0 tail
  end.


Definition satisfiable (phi : t) : Prop :=
  exists W R (M : @Kripke.t W R) (w0 : W), force M w0 phi.


Fixpoint In (x : nat) (phi : t) : Prop :=
  match phi with
  | [] => False
  | head :: tail => Mclause.In x head \/ In x tail
  end.

Section Simplify.
  (* mini lemmas useful for simplifications *)
  Lemma in_mcnf_or :
    forall (L R : t) (x : nat),
    In x (L ++ R) <-> In x L \/ In x R .
  Proof.
    intros L R x.
    induction L as [| head tail IHl]; simpl in *; tauto.
  Qed.


  Lemma in_ctx_iff_in_mcnf :
    forall (phi : t) (x : nat),
    In x (List.map Mclause.Ctx phi) <-> In x phi.
  Proof.
    intros phi x.
    induction phi as [| head tail IHphi]; simpl in *; tauto.
  Qed.


  Lemma mcnf_force_and :
    forall {W} {R} (M : @Kripke.t W R) (w : W) (l r : t),
    force M w (l ++ r) <-> force M w l /\ force M w r.
  Proof.
    intros W R M w l r.
    split.
    - intro Hforce_lr.
      induction l as [| head tail IHl]; simpl in *; tauto.
    - intros [Hforce_l Hforce_r].
      induction l as [| head tail IHl]; simpl in *; tauto.
  Qed.


  Lemma w0_force_ctx_iff_nbr_force_phi :
    forall {W} {R} (M : @Kripke.t W R) (w : W) (phi : t),
      force M w (List.map Mclause.Ctx phi) <->
      (forall (neighbour : W), R w neighbour -> force M neighbour phi).
  Proof with simpl; auto.
    intros W R M w phi.
    induction phi as [| head tail IHphi].
    - simpl. tauto.
    - simpl in *. split.
      + intros [Hforce_nbr Hforce_ctx_tail] nbr Hrel_nbr.
        split... apply IHphi...
      + intros Hnbr_forces_head_tail.
        split.
        * intros nbr Hrel_nbr.
          now apply Hnbr_forces_head_tail.
        * apply IHphi. apply Hnbr_forces_head_tail.
  Qed.
End Simplify.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w : W) (x : nat), In x phi -> (Kripke.valuation M w x <-> Kripke.valuation M' w x).


Lemma meaningful_valuations :
  forall {W} {R} (M M' : @Kripke.t W R) (phi : t) (w : W),
  agree phi M M' -> (force M w phi <-> force M' w phi).
Proof with simpl; auto.
  intros W R M M' phi w0 Hval.

  induction phi as [|head tail IHphi].
  - tauto.
  - assert (forall w' x, In x tail -> Kripke.valuation M w' x <-> Kripke.valuation M' w' x) as Hval_tail.
    {
      intros w' x Hx_tail.
      apply Hval...
    }
    assert (forall w' x, Mclause.In x head -> Kripke.valuation M w' x <-> Kripke.valuation M' w' x) as Hval_head.
    {
      intros w' x Hx_head.
      apply Hval...
    }

    rewrite (mcnf_force_and M w0 [head] tail).
    rewrite (mcnf_force_and M' w0 [head] tail).
    split.
    + intros [Hhead Htail].
      split.
      (* force head *)
      * simpl in *. split... destruct Hhead as [Hhead _].
        rewrite <- (Mclause.meaningful_valuations M M')...
      (* force tail by IH *)
      * apply IHphi...
    + intros [Hhead Htail].
      split.
      * simpl in *. split... destruct Hhead as [Hhead _].
        rewrite (Mclause.meaningful_valuations M M')...
      * apply IHphi...
Qed.
