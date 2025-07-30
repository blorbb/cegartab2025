From Stdlib Require Import PeanoNat Arith Lia Classical Permutation Relations RelationClasses SetoidPermutation.
From Stdlib Require SetoidList.
Import List.ListNotations.
Open Scope list_scope.


(* https://stackoverflow.com/a/60817708 *)
Ltac forward_gen H tac :=
  match type of H with
  | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.


(* Simplify if statements by asserting that the next condition is true/false. *)
Ltac assert_cond b :=
  lazymatch goal with
  | |- context [ if ?G then ?Then else ?Else ] =>
    let H := fresh "H" in
    (* make the assertion that the condition is true/false *)
    assert (H: G = b) ;
      [
        (* simplify boolean to proposition *)
        lazymatch G with
        | ?X =? ?Y =>
          lazymatch b with
          | true  => apply Nat.eqb_eq
          | false => apply Nat.eqb_neq
          end
        | ?X <=? ?Y =>
          lazymatch b with
          | true  => apply Nat.leb_le
          | false => apply Nat.leb_gt
          end
        | ?X <? ?Y =>
          lazymatch b with
          | true  => apply Nat.ltb_lt
          | false => apply Nat.ltb_ge
          end
        | _ => fail "cannot find a reflection lemma for" G
        end
      |
        (* remove the if in the old goal *)
        rewrite H; clear H; simpl 
      ]
  end.

Ltac assert_cond_in b H :=
  lazymatch type of H with
  | context [ if ?G then ?Then else ?Else ] =>
    let H := fresh "H" in
    (* make the assertion that the condition is true/false *)
    assert (H: G = b) ;
      [
        (* simplify boolean to proposition *)
        lazymatch G with
        | ?X =? ?Y =>
          lazymatch b with
          | true  => apply Nat.eqb_eq
          | false => apply Nat.eqb_neq
          end
        | ?X <=? ?Y =>
          lazymatch b with
          | true  => apply Nat.leb_le
          | false => apply Nat.leb_gt
          end
        | ?X <? ?Y =>
          lazymatch b with
          | true  => apply Nat.ltb_lt
          | false => apply Nat.ltb_ge
          end
        | _ => fail "cannot find a reflection lemma for" G
        end
      |
        (* remove the if in the old goal *)
        rewrite H in H; clear H; simpl in H
      ]
  end.


(* apply a tactic that's usually on the goal, in any hypothesis *)
Ltac in_hyp H T :=
  let H0 := fresh H "_old" in
  rename H into H0 ;
  generalize dependent H0 ;
  T ;
  try match goal with
    | H0: _ |- _ => intro H
  end.

Tactic Notation "assert_cond" constr(b) :=
  assert_cond b.

Tactic Notation "assert_cond" constr(b) "by" tactic(tac) :=
  assert_cond b; [tac|].

Tactic Notation "assert_cond" constr(b) "in" hyp(H) :=
  assert_cond_in b H.

Tactic Notation "assert_cond" constr(b) "in" hyp(H) "by" tactic(tac) :=
  assert_cond_in b H; [tac|].

Tactic Notation "ifauto" "by" tactic(tac) :=
  (repeat assert_cond false by tac);
  (try assert_cond true by tac).

Tactic Notation "ifauto" :=
  (ifauto by simpl; lia); auto.

Tactic Notation "ifauto" "in" hyp(H) :=
  in_hyp H ltac:(ifauto).

Tactic Notation "ifauto" "in" hyp(H) "by" tactic(tac) :=
  in_hyp H ltac:(ifauto by tac).


(* 
simplifies `let (a, b) := p in ...`
Replaces instances of `a` with `fst p`, and `b` with `snd p`.
*)
Local Lemma inline_pair_lemma
      {A B C : Type} (p : A * B) (f : A -> B -> C) :
  (let (a,b) := p in f a b)
    = f (fst p) (snd p).
Proof. destruct p. auto. Qed.

Tactic Notation "inline_pair" := rewrite inline_pair_lemma.
Tactic Notation "inline_pair" "in" hyp(H) := rewrite inline_pair_lemma in H.
Tactic Notation "inline_pair" "in" "*" := rewrite inline_pair_lemma in *.


Tactic Notation "destruct_pair" constr(p) "as" "[" ident(x) ident(y) "]" :=
    rewrite (inline_pair_lemma p);
    set (x := fst p);
    set (y := snd p).

Tactic Notation "destruct_pair" constr(p) "as" "[" ident(x) ident(y) "]" "in" hyp(H) :=
    rewrite (inline_pair_lemma p) in H;
    set (x := fst p);
    set (y := snd p);
    fold x in H; fold y in H.


(*
fold a definition in all hypotheses.

slightly different from [fold i in *] as this fails if [i] is one of the
things in the context. 
*)
Ltac fold_all ident := repeat match goal with
  | [ H: _ |- _ ] => progress fold ident in H
end.

Lemma contrapositive (P Q : Prop) : (P -> Q) <-> (~Q -> ~P).
Proof.
  split; tauto.
Qed.
