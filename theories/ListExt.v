(** Extra lemmas regarding lists. *)

From Stdlib Require List.
Import List.ListNotations.
Open Scope list_scope.
From Stdlib Require Import Relations SetoidPermutation Permutation RelationClasses SetoidList PeanoNat Lia Classical.
From CegarTableaux Require Import Utils.

Lemma ex_eqA_iff_inA : forall {A} (eqA : relation A) (x : A) (l : list A),
  List.Exists (eqA x) l <-> InA eqA x l.
Proof.
  intros.
  induction l as [| head tail IH].
  - rewrite List.Exists_nil, InA_nil. reflexivity.
  - rewrite List.Exists_cons, InA_cons, IH.
    reflexivity.
Qed.


Lemma inA_flat_map : forall {A B} (eqB : relation B) (f : A -> list B) (l : list A) (y : B),
  InA eqB y (List.flat_map f l) <-> (exists x : A, List.In x l /\ InA eqB y (f x)).
Proof.
  intros.
  rewrite InA_altdef, List.Exists_flat_map, List.Exists_exists.
  setoid_rewrite ex_eqA_iff_inA. reflexivity.
Qed.


Lemma InA_concat : forall {A} (eqA : relation A) (l : list (list A)) (y : A),
  InA eqA y (List.concat l) <-> (exists x, List.In x l /\ InA eqA y x).
Proof.
  intros A eqA l y.
  rewrite InA_altdef, List.Exists_concat, List.Exists_exists.
  setoid_rewrite ex_eqA_iff_inA. reflexivity.
Qed.


Lemma PermutationA_inA : forall {A} (eqA : relation A) (l l' : list A) (x : A),
  Equivalence eqA ->
  PermutationA eqA l l' ->
  InA eqA x l ->
  InA eqA x l'.
Proof with try easy.
  intros A eqA l l' x Hequiv Hperm Hx_in_l.
  apply PermutationA_equivlistA in Hperm...
  unfold equivlistA in Hperm.
  apply Hperm. assumption.
Qed.


Lemma PermutationA_inclA : forall {A} (eqA : relation A) (subset l l' : list A),
  Equivalence eqA ->
  PermutationA eqA l l' ->
  inclA eqA subset l ->
  inclA eqA subset l'.
Proof with try easy.
  intros A eqA subset l l' Hequiv Hperm_ab Hs_incl_a.
  unfold inclA in *.
  intros x Hx_in_subset.
  apply PermutationA_inA with (l:=l)...
  apply Hs_incl_a. assumption.
Qed.


Lemma inclA_cons : forall {A} (eqA : relation A) (h : A) (t l : list A),
  Equivalence eqA ->
  InA eqA h l /\ inclA eqA t l <-> inclA eqA (h :: t) l.
Proof with auto.
  intros A eqA h t l. unfold inclA. split.
  - intros [Hhin Htincl] x Hx_ht.
    apply InA_cons in Hx_ht.
    destruct Hx_ht as [Hxh | Hxt].
    + apply InA_eqA with (x:=h)... now symmetry.
    + now apply Htincl.
  - intros Hincl. split.
    + apply Hincl. now apply InA_cons_hd.
    + intros x Hxt.
      apply Hincl. now apply InA_cons_tl.
Qed.


Lemma inclA_nil : forall {A} (eqA : relation A) (l : list A),
  inclA eqA [] l.
Proof.
  intros A eqA l x Hxin.
  apply InA_nil in Hxin. contradiction.
Qed.


Lemma cons_NoDupA : forall {A} (eqA : relation A) a l,
  NoDupA eqA (a :: l) -> NoDupA eqA l.
Proof.
  intros A eqA a l Hnd.
  inversion Hnd. assumption.
Qed.


Lemma NoDupA_incl_length : forall {A} (eqA : relation A) l l',
  Equivalence eqA ->
  NoDupA eqA l -> inclA eqA l l' -> List.length l <= List.length l'.
Proof with try easy.
  intros A eqA l l' Hequiv Hnodup. revert l'.
  induction Hnodup as [|a l Hal Hnd IH]; cbn.
  - lia.
  - intros l' Hincl.
    (* a in l' but not in l *)
    apply inclA_cons in Hincl as [Hal' Hincl_ll']...
    apply InA_split in Hal' as [l1 [b [l2 [Hab ->]]]].
    (* remove a and b from the goal *)
    enough (length l <= length (l1 ++ l2)). { rewrite length_app in *. cbn. lia. }
    apply IH.
    intros x Hxin.
    specialize (Hincl_ll' x Hxin).
    apply InA_app in Hincl_ll'. rewrite InA_cons in Hincl_ll'.
    destruct Hincl_ll' as [Hxl1 | [Hxb | Hxl2]].
    + apply InA_app_iff. now left.
    (* contradiction *)
    + apply InA_eqA with (y:=a) in Hxin...
      transitivity b...
    + apply InA_app_iff. now right.
Qed.


(* TODO: classic should not be required. *)
Lemma NoDupA_length_incl : forall {A} (eqA : relation A) (l l' : list A),
  Equivalence eqA ->
  NoDupA eqA l ->
  List.length l' <= List.length l ->
  inclA eqA l l' ->
  inclA eqA l' l.
Proof with try easy; auto.
  intros A eqA l l' Hequiv Hnodup Hlen Hincl x Hxin.

  (* destruct (InA_dec eqA_dec x l) as [Hin | Hnin]... *)
  destruct (classic (InA eqA x l)) as [Hin | Hnin]...
  (* contradiction with bound on the length *)
  assert (List.length l < List.length l').
  {
    apply Nat.succ_lt_mono, PeanoNat.le_lt_n_Sm.
    pose proof (NoDupA_incl_length eqA (x::l) (l')) as Hl.
    forward Hl by assumption.
    forward Hl. { apply NoDupA_cons... }
    forward Hl. { apply inclA_cons... }
    now cbn in Hl.
  }
  lia.
Qed.


(** PermutationA counterpart to NoDup_Permutation_bis.
  Has an extra [NoDupA eqA l'] requirement that isn't strictly necessary,
  but proving that the other preconditions imply this is hard. *)
Lemma NoDup_PermutationA_bis : forall {A} (eqA : relation A) (l l' : list A), 
  Equivalence eqA ->
  NoDupA eqA l ->
  NoDupA eqA l' ->
  List.length l' <= List.length l ->
  inclA eqA l l' ->
  PermutationA eqA l l'.
Proof with auto.
  intros A eqA l l' Hequiv Hnodupl Hnodupl' Hlen Hincl.
  apply NoDupA_equivlistA_PermutationA...
  split...
  apply NoDupA_length_incl...
Qed.


(** If for setoid-equal inputs, f is a setoid-permutation, then flat mapping will also be a permutation. *)
Lemma PermutationA_flat_map : forall {A} (eqA : relation A) (f : A -> list A) (l l' : list A),
  Equivalence eqA ->
  (forall a a', eqA a a' -> PermutationA eqA (f a) (f a')) ->
  PermutationA eqA l l' -> PermutationA eqA (List.flat_map f l) (List.flat_map f l').
Proof with auto.
  intros A eqA f l l' Hequiv Hf Hperm.
  induction Hperm as
    [
    | a a' l l' Haa' Hperm IHperm
    | a b c
    | a b c Hab Hbc IHab IHbc
    ].
  - constructor.
  - cbn. apply PermutationA_app.
    + exact Hequiv.
    + now apply Hf.
    + exact IHperm.
  - cbn. repeat rewrite List.app_assoc.
    apply PermutationA_app_tail... apply PermutationA_app_comm...
  - apply permA_trans with (l₂ := List.flat_map f b)...
Qed.


Lemma PermutationA_swap_heads : forall {A} (eqA : relation A) l x y tl,
  PermutationA eqA l (x :: y :: tl) ->
  PermutationA eqA l (y :: x :: tl).
Proof with auto.
  intros.
  apply permA_trans with (l₂ := x::y::tl).
  - exact H.
  - apply permA_swap.
Qed.


(** Equivalent of [NoDup_concat] for setoid equality. *)
Lemma NoDupA_concat : forall {A} (eqA : relation A) (l : list (list A)),
  Equivalence eqA ->
  List.Forall (SetoidList.NoDupA eqA) l ->
  List.ForallOrdPairs (fun l1 l2 => forall a, SetoidList.InA eqA a l1 -> ~ SetoidList.InA eqA a l2) l ->
  SetoidList.NoDupA eqA (List.concat l).
Proof.
  intros A eqA l Hequiv Hforall Hfop.
  induction l as [|h t IH].
  { constructor. }
  cbn. apply SetoidList.NoDupA_app.
  - exact Hequiv.
  - now apply List.Forall_inv in Hforall.
  - apply IH.
    + now apply List.Forall_inv_tail in Hforall.
    + inversion Hfop. assumption.
  - intros a Ha_in_h Ha_in_t%InA_concat.
    destruct Ha_in_t as [l' [Hl'_in_t Ha_in_l']].
    inversion Hfop. rewrite List.Forall_forall in H1.
    apply (H1 _ Hl'_in_t _ Ha_in_h). assumption.
Qed.


Lemma NoDupA_length_2 : forall {A} (eqA : relation A) (x y : A),
  ~ eqA x y ->
  SetoidList.NoDupA eqA [x ; y].
Proof.
  intros A eqA x y Hneq.
  repeat constructor.
  - rewrite SetoidList.InA_singleton. assumption.
  - intro H. apply SetoidList.InA_nil in H. contradiction.
Qed.


Lemma InA_length_2 : forall {A} (eqA : relation A) (a x y : A),
  InA eqA a [x ; y] -> eqA a x \/ eqA a y.
Proof.
  intros A eqA a x y Hin.
  apply InA_cons in Hin. rewrite InA_singleton in Hin. assumption.
Qed.


Lemma Permutation_heads_ne : forall {A} (a b : A) (l l' : list A),
  a <> b ->
  Permutation (a :: l) (b :: l') ->
  List.In a l'.
Proof.
  intros A a b l l' Hne Hperm.
  apply Permutation_in with (x:=a) in Hperm.
  - cbn in Hperm. destruct Hperm; auto.
    symmetry in H. contradiction.
  - apply List.in_eq.
Qed.


Lemma PermutationA_length : forall {A} (eqA : relation A) (l l' : list A),
  PermutationA eqA l l' -> length l = length l'.
Proof.
  intros A eqA l l' Hperm.
  induction Hperm; cbn; auto.
  now transitivity (length l₂).
Qed.
