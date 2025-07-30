From Stdlib Require List SetoidList.
From Stdlib Require Import Relations SetoidPermutation Permutation RelationClasses.

Lemma ex_eqA_iff_inA : forall {A} (eqA : relation A) (x : A) (l : list A),
  List.Exists (eqA x) l <-> SetoidList.InA eqA x l.
Proof.
  intros.
  induction l as [| head tail IH].
  - rewrite List.Exists_nil, SetoidList.InA_nil. reflexivity.
  - rewrite List.Exists_cons, SetoidList.InA_cons, IH.
    reflexivity.
Qed.

Lemma inA_flat_map : forall {A B} (eqB : relation B) (f : A -> list B) (l : list A) (y : B),
  SetoidList.InA eqB y (List.flat_map f l) <-> (exists x : A, List.In x l /\ SetoidList.InA eqB y (f x)).
Proof.
  intros.
  rewrite SetoidList.InA_altdef, List.Exists_flat_map, List.Exists_exists.
  setoid_rewrite ex_eqA_iff_inA.
  reflexivity.
Qed.


Lemma PermutationA_inA : forall {A} (eqA : relation A) (l l' : list A) (x : A),
  Equivalence eqA ->
  PermutationA eqA l l' ->
  SetoidList.InA eqA x l ->
  SetoidList.InA eqA x l'.
Proof with try easy.
  intros A eqA l l' x Hequiv Hperm Hx_in_l.
  apply PermutationA_equivlistA in Hperm...
  unfold SetoidList.equivlistA in Hperm.
  apply Hperm. assumption.
Qed.


Lemma PermutationA_inclA : forall {A} (eqA : relation A) (subset l l' : list A),
  Equivalence eqA ->
  PermutationA eqA l l' ->
  SetoidList.inclA eqA subset l ->
  SetoidList.inclA eqA subset l'.
Proof with try easy.
  intros A eqA subset l l' Hequiv Hperm_ab Hs_incl_a.
  unfold SetoidList.inclA in *.
  intros x Hx_in_subset.
  apply PermutationA_inA with (l:=l)...
  apply Hs_incl_a. assumption.
Qed.

Lemma inclA_cons : forall {A} (eqA : relation A) (h : A) (t l : list A),
  Equivalence eqA ->
  SetoidList.InA eqA h l /\ SetoidList.inclA eqA t l <-> SetoidList.inclA eqA (h :: t) l.
Proof with auto.
  intros A eqA h t l. unfold SetoidList.inclA. split.
  - intros [Hhin Htincl] x Hx_ht.
    apply SetoidList.InA_cons in Hx_ht.
    destruct Hx_ht as [Hxh | Hxt].
    + apply SetoidList.InA_eqA with (x:=h)... now symmetry.
    + now apply Htincl.
  - intros Hincl. split.
    + apply Hincl. now apply SetoidList.InA_cons_hd.
    + intros x Hxt.
      apply Hincl. now apply SetoidList.InA_cons_tl.
Qed.
