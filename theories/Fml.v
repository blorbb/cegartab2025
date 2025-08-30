From Stdlib Require List.
From CegarTableaux Require Kripke Lit.


(** An arbitrary modal formula [Fml.t]. *)
Inductive t : Type :=
  | Var  (x : nat)
  | Neg  (A : t)
  | And  (A B : t)
  | Or   (A B : t)
  | Impl (A B : t)
  | Box  (A : t)
  | Dia  (A : t).


Fixpoint force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  match phi with
  | Var  x   => Kripke.valuation M w0 x
  | Neg  A   => ~ force M w0 A
  | And  A B => force M w0 A /\ force M w0 B
  | Or   A B => force M w0 A \/ force M w0 B
  | Impl A B => force M w0 A -> force M w0 B
  | Box  A   => forall nbr, R w0 nbr -> force M nbr A
  | Dia  A   => exists nbr, R w0 nbr /\ force M nbr A
  end.


Definition satisfiable (phi : t) : Prop :=
  exists W R (M : @Kripke.t W R) (w0 : W), force M w0 phi.
