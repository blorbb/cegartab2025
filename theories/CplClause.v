From Stdlib Require List.
From CegarTableaux Require Lit.
Import List.ListNotations.
Open Scope list_scope.

(** A CPL-clause, a _disjunction_ of literals. *)
Definition t : Type := list Lit.t.


Definition force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  exists x, List.In x phi /\ Lit.force M w0 x.

Arguments force {W R} M w0 phi /.


Definition In (x : nat) (phi : t) : Prop :=
  List.In x (List.map Lit.atm phi).

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

  simpl. split.
  - intros [x [Hx_in Hforce_x]].
    exists x. split...
    apply Heq_lit...
    simpl. now apply List.in_map.
  - intros [x [Hx_in Hforce_x]].
    exists x. split...
    apply Heq_lit...
    simpl. now apply List.in_map.
Qed.


(** Creates a CPL clause from a single literal. *)
Definition from_lit (l : Lit.t) : t := [l].

Arguments from_lit l /.
