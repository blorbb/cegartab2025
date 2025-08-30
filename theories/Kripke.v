From Stdlib Require Import Relations.

(** A Kripke model with a parameterised Kripke frame [W, R] and [valuation].

    - [W : Type] is a (possibly infinite) set of worlds.
    - [R : relation W] is the successor relation between worlds.
      For worlds [u] and [v], the mathematical relation notation [uRv] is
      instead a binary function [R u v] that returns whether or not [u] and
      [v] are related.
    - [valuation : W -> nat -> Prop] is the valuation function; given a
      particular world and atom (represented by a natural), returns whether or
      not the atom is true at the particular world.

    We chose to parameterise the frame [W, R] so that we can easily describe
    multiple models with the same frame without requiring additional
    propositions.

    The relation and valuation functions could return a [bool] instead of a
    [Prop]. It doesn't matter much since we assume the law of excluded middle. *)
Record t {W : Type} {R : relation W} : Type := {
  valuation : W -> nat -> Prop;
}.

(** [make W R val] constructs a Kripke model. *)
Definition make W R (valuation : W -> nat -> Prop) : @t W R :=
  {| valuation := valuation  |}.
