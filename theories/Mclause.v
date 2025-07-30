From Stdlib Require List.
From Stdlib Require Import Lia.
From CegarTableaux Require Lit Kripke CplClause BoxClause DiaClause.
From CegarTableaux Require Import Utils.

(** A modal clause: MCNF clause with an arbitrary number of boxes. *)
Inductive t : Type :=
  | Cpl (cpl : CplClause.t)
  | Box (box : BoxClause.t)
  | Dia (dia : DiaClause.t)
  (* new modal context: []phi *)
  | Ctx (phi : t).


Fixpoint force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  match phi with
  | Cpl A => CplClause.force M w0 A
  | Box A => BoxClause.force M w0 A
  | Dia A => DiaClause.force M w0 A
  | Ctx A => forall nbr, R w0 nbr -> force M nbr A
  end.


Fixpoint In (x : nat) (phi : t) : Prop :=
  match phi with
  | Cpl A => CplClause.In x A
  | Box A => BoxClause.In x A
  | Dia A => DiaClause.In x A
  | Ctx ctx => In x ctx
  end.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w : W) (x : nat), In x phi -> (Kripke.valuation M w x <-> Kripke.valuation M' w x).


Lemma meaningful_valuations :
  forall {W} {R} (M M' : @Kripke.t W R) (phi : t) (w0 : W),
  agree phi M M' -> (force M w0 phi <-> force M' w0 phi).
Proof with simpl; auto.
  intros W R M M' phi w0 Hagree.
  revert w0.

  induction phi as
    [ A
    | A
    | A
    | A IHA
    ]; intro w0.

  - apply CplClause.meaningful_valuations...
  - apply BoxClause.meaningful_valuations...
  - apply DiaClause.meaningful_valuations...

  (* context *)
  - simpl. split.
    + intros HM_force nbr Hrel_nbr.
      specialize (HM_force nbr Hrel_nbr).
      destruct IHA with (w0 := nbr)...

    + intros HM'_force nbr Hrel_nbr.
      specialize (HM'_force nbr Hrel_nbr).
      destruct IHA with (w0 := nbr)...
Qed.
