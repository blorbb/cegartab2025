From Stdlib Require List.
From Stdlib Require Import Lia.
From CegarTableaux Require Lit Kripke CplClause BoxClause DiaClause.
From CegarTableaux Require Import Utils.
Import List.ListNotations.
Open Scope list_scope.

(** Set of clauses at the current world. *)
Record t : Type := make {
  cpls : list CplClause.t;
  boxes : list BoxClause.t;
  dias : list DiaClause.t;
}.

Definition empty := make [] [] [].


(** Merge two sets of local clauses into one. *)
Definition merge A B := make (cpls A ++ cpls B) (boxes A ++ boxes B) (dias A ++ dias B).


Definition force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  List.Forall (CplClause.force M w0) phi.(cpls) /\
  List.Forall (BoxClause.force M w0) phi.(boxes) /\
  List.Forall (DiaClause.force M w0) phi.(dias).

Arguments force {W R} M w0 phi /.


Lemma force_merge_and : forall {W} {R} {M : @Kripke.t W R} {w0 : W} (A B : t),
  force M w0 (merge A B) <-> force M w0 A /\ force M w0 B.
Proof.
  intros W R M w0 A B.
  destruct A as [cpls boxes dias].

  unfold force, merge; cbn.
  repeat rewrite List.Forall_app.
  intuition.
Qed.


Definition In (x : nat) (phi : t) : Prop :=
  List.Exists (CplClause.In x) phi.(cpls) \/
  List.Exists (BoxClause.In x) phi.(boxes) \/
  List.Exists (DiaClause.In x) phi.(dias).

Arguments In x phi /.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w : W) (x : nat), In x phi -> (Kripke.valuation M w x <-> Kripke.valuation M' w x).


Lemma meaningful_valuations :
  forall {W} {R} (M M' : @Kripke.t W R) (phi : t) (w0 : W),
  agree phi M M' -> (force M w0 phi <-> force M' w0 phi).
Proof with try solve [simpl; auto; tauto].
  intros W R M M' phi w0 Hagree.
  destruct phi as [cpls boxes dias].

  unfold agree in Hagree.
  cbn in Hagree.

  cbn. split.
  - intros [Hc [Hb Hd]].
    repeat split.

    (* cpl *)
    + apply List.Forall_forall.
      intros cpl Hin.
      apply (CplClause.meaningful_valuations M M').
      * unfold CplClause.agree.
        intros w x Hx_in_cpl.
        apply Hagree. left.
        apply List.Exists_exists. exists cpl...
      * rewrite List.Forall_forall in Hc. apply Hc...

      (* box *)
    + apply List.Forall_forall.
      intros box Hin.
      apply (BoxClause.meaningful_valuations M M').
      * unfold BoxClause.agree.
        intros w x Hx_in_box.
        apply Hagree. right. left.
        apply List.Exists_exists. exists box...
      * rewrite List.Forall_forall in Hb. apply Hb...

    (* dia *)
    + apply List.Forall_forall.
      intros dia Hin.
      apply (DiaClause.meaningful_valuations M M').
      * unfold DiaClause.agree.
        intros w x Hx_in_dia.
        apply Hagree. right. right.
        apply List.Exists_exists. exists dia...
      * rewrite List.Forall_forall in Hd. apply Hd...

  - intros [Hc [Hb Hd]].
    repeat split.

    (* cpl *)
    + apply List.Forall_forall.
      intros cpl Hin.
      apply (CplClause.meaningful_valuations M M').
      * unfold CplClause.agree.
        intros w x Hx_in_cpl.
        apply Hagree. left.
        apply List.Exists_exists. exists cpl...
      * rewrite List.Forall_forall in Hc. apply Hc...

      (* box *)
    + apply List.Forall_forall.
      intros box Hin.
      apply (BoxClause.meaningful_valuations M M').
      * unfold BoxClause.agree.
        intros w x Hx_in_box.
        apply Hagree. right. left.
        apply List.Exists_exists. exists box...
      * rewrite List.Forall_forall in Hb. apply Hb...

    (* dia *)
    + apply List.Forall_forall.
      intros dia Hin.
      apply (DiaClause.meaningful_valuations M M').
      * unfold DiaClause.agree.
        intros w x Hx_in_dia.
        apply Hagree. right. right.
        apply List.Exists_exists. exists dia...
      * rewrite List.Forall_forall in Hd. apply Hd...
Qed.
