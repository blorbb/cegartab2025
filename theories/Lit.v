From Stdlib Require Import Setoid PeanoNat.
From CegarTableaux Require Kripke.

(** A positive or negative literal. *)
Inductive t : Type :=
  | Pos (x : nat)
  | Neg (x : nat).


Definition negate (l : t) : t :=
  match l with
  | Pos n => Neg n
  | Neg n => Pos n
  end.


Definition atm (l : t) : nat :=
  match l with
  | Pos n => n
  | Neg n => n
  end.


Definition eqb (a b : t) : bool :=
  match a, b with
  | Pos x, Pos y => x =? y
  | Neg x, Neg y => x =? y
  | _, _ => false
  end.


(** * Equality lemmas *)

Lemma eqb_eq (a b : t) : eqb a b = true <-> a = b.
Proof.
  destruct a, b; cbn.
  - rewrite Nat.eqb_eq. split; congruence.
  - split; discriminate.
  - split; discriminate.
  - rewrite Nat.eqb_eq. split; congruence.
Qed.


Lemma eq_dec (a b : t) : {a = b} + {a <> b}.
Proof.
  decide equality; apply Nat.eq_dec.
Qed.


Lemma negate_eq_atm (l : t) : atm (negate l) = atm l.
Proof.
  destruct l; reflexivity.
Qed.


Lemma negate_involution : forall l, Lit.negate (Lit.negate l) = l.
Proof.
  intro l. destruct l as [x|x]; auto.
Qed.


(** Whether the atom within the literal is the same. *)
Definition eq_atm (a b : t) : Prop :=
  atm a = atm b.

Arguments eq_atm a b /.


Lemma eq_atm_refl : Reflexive eq_atm.
Proof.
  intro atm. reflexivity.
Qed.

Lemma eq_atm_sym : Symmetric eq_atm.
Proof.
  intros p q Heq.
  cbn in *. now symmetry.
Qed.

Lemma eq_atm_trans : Transitive eq_atm.
Proof.
  intros p q r Hpq Hqr.
  cbn in *. now rewrite Hpq.
Qed.

Global Instance eq_atm_equivalence : Equivalence eq_atm := {
  Equivalence_Reflexive := eq_atm_refl;
  Equivalence_Symmetric := eq_atm_sym;
  Equivalence_Transitive := eq_atm_trans;
}.


(** * Forcing *)

Definition force {W} {R} (M : @Kripke.t W R) (w0 : W) (l : t) : Prop :=
  match l with
  | Pos n =>   Kripke.valuation M w0 n
  | Neg n => ~ Kripke.valuation M w0 n
  end.


Definition In (x : nat) (phi : t) : Prop :=
  x = atm phi.

Arguments In x phi /.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w : W) (x : nat), In x phi -> (Kripke.valuation M w x <-> Kripke.valuation M' w x).


Lemma meaningful_valuations :
  forall {W} {R} (M M' : @Kripke.t W R) (phi : t) (w0 : W),
  agree phi M M' -> (force M w0 phi <-> force M' w0 phi).
Proof with simpl; easy.
  intros W R M M' phi w0 Hagree.
  unfold agree in Hagree.

  destruct phi as [x | x].
  - simpl. rewrite Hagree...
  - simpl. rewrite Hagree...
Qed.
