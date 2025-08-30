From Stdlib Require List.
From Stdlib Require Import Lia.
From CegarTableaux Require Lit.
From CegarTableaux Require Import Utils.

(** An MCNF box-clause [a -> []b]. *)
Definition t : Type := Lit.t * Lit.t.


Definition force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  Lit.force M w0 (fst phi) -> (forall nbr, R w0 nbr -> Lit.force M nbr (snd phi)).

Arguments force {W R} M w0 phi /.


Definition In (x : nat) (phi : t) : Prop :=
  (x = Lit.atm (fst phi)) \/ (x = Lit.atm (snd phi)).

Arguments In x phi /.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w : W) (x : nat), In x phi -> (Kripke.valuation M w x <-> Kripke.valuation M' w x).


Lemma meaningful_valuations :
  forall {W} {R} (M M' : @Kripke.t W R) (phi : t) (w0 : W),
  agree phi M M' -> (force M w0 phi <-> force M' w0 phi).
Proof with simpl; auto.
  intros W R M M' phi w0 Hagree. revert w0.

  assert (
    forall w x, In (Lit.atm x) phi ->
    Lit.force M w x <-> Lit.force M' w x
  ) as Heq_lit.
  {
    intros w' x Hxin.
    unfold agree in Hagree.
    destruct x as [x | x]; simpl; rewrite Hagree; tauto.
  }

  unfold force in *. split.
  - intros HM_force_a HM'_force_a nbr HM'_rel_nbr.
    rewrite <- (Heq_lit w0 (fst phi)) in HM'_force_a.
    rewrite <- (Heq_lit nbr (snd phi)).
    + forward HM_force_a by assumption.
      apply HM_force_a...
    + unfold In. now right.
    + unfold In. now left.
  - intros HM'_force_a HM_force_a nbr HM_rel_nbr.
    rewrite <- (Heq_lit w0 (fst phi)) in HM'_force_a.
    rewrite (Heq_lit nbr (snd phi)).
    + forward HM'_force_a by assumption.
      apply HM'_force_a...
    + simpl. now right.
    + simpl. now left.
Qed.
