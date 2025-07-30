From Stdlib Require List.
Import List.ListNotations.
Open Scope list_scope.
From Stdlib Require Import Arith.
From CegarTableaux Require CplClause.

(** A classical formula in CNF. *)
Definition t := list CplClause.t.

Definition force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  List.Forall (CplClause.force M w0) phi.

Definition In (x : nat) (phi : t) : Prop :=
  List.Exists (CplClause.In x) phi.

Arguments In x phi /.
Arguments force {W R} M w0 phi /.

Definition from_assumptions (assumptions : list Lit.t) : t := List.map CplClause.from_lit assumptions.

Definition satisfiable (phi : t) : Prop :=
  exists W R (M : @Kripke.t W R) (w0 : W), force M w0 phi.

Definition unsatisfiable (phi : t) : Prop := ~ satisfiable phi.

(** NoDup list of atoms of a CNF formula. *)
Definition atms_of (phi : t) : list nat :=
  List.nodup (Nat.eq_dec) (List.flat_map (fun cpl => List.map Lit.atm cpl) phi).


Lemma in_atms_of : forall (phi : t) (x : nat), In x phi <-> List.In x (atms_of phi).
Proof.
  intros phi x.
  destruct phi as [| head tail].
  - cbn. apply List.Exists_nil.
  - cbn. rewrite List.nodup_In, List.Exists_cons, List.in_app_iff, List.Exists_exists.
    split.
    + intro Hxin.
      destruct Hxin as [Hxhead | [clause [Hclause_in_tail Hx_in_clause]]].
      * left. cbn in Hxhead. exact Hxhead.
      * right. apply List.in_flat_map.
        exists clause. cbn in Hx_in_clause. split; assumption.
    + intros [Hxhead | Hxtail].
      * left. cbn. exact Hxhead.
      * right. apply List.in_flat_map in Hxtail.
        destruct Hxtail as [clause [Hclause_in_tail Hx_in_clause]].
        exists clause. cbn. split; assumption.
Qed.
