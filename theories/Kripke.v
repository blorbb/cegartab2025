
(**
  A binary relation [T * T].
*)
Definition relation T := T -> T -> Prop.

Record t {W : Type} {R : relation W} : Type := {
  valuation : W -> nat -> Prop;
}.

Definition make W R (valuation : W -> nat -> Prop) : @t W R :=
  {| valuation := valuation  |}.
