From Stdlib Require List.
From CegarTableaux Require Kripke.

(** A Kripke model with a tree structure. *)

Inductive t :=
  | cons
      (* A list of atoms which are true at the current world. *)
      (atms : list nat)
      (* A list of sub-trees reachable from here. *)
      (children : list t).


Definition valuation (tree : t) (atm : nat) : Prop :=
  match tree with
  | cons atms _ => List.In atm atms
  end.


Definition relation (w0 w1 : t) : Prop :=
  match w0 with
  | cons _ children => List.In w1 children
  end.


Definition as_kripke : @Kripke.t t relation := Kripke.make t relation valuation.
