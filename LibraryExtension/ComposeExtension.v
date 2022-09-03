From mathcomp Require Import ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Arith.Plus.

Fixpoint repeat_compose (T : Type) (f : T -> T) (n : nat) : T -> T := match n with
  | O => Datatypes.id
  | S m => compose f (repeat_compose T f m)
end.

Lemma repeat_compose_add : forall (T : Type) (f : T -> T) (n m : nat), repeat_compose T f (n + m) = compose (repeat_compose T f n) (repeat_compose T f m).
Proof.
move=> T f.
elim.
move=> m.
reflexivity.
move=> n H1 m.
simpl.
rewrite H1.
reflexivity.
Qed.

Lemma repeat_compose_def2 : forall (T : Type) (f : T -> T), repeat_compose T f = fix rep (n : nat) : T -> T := match n with
  | O => Datatypes.id
  | S m => compose (rep m) f
end.
Proof.
move=> T f.
apply functional_extensionality.
elim.
reflexivity.
move=> n H1.
simpl.
rewrite - H1.
rewrite - {1} (compose_id_right T T f).
rewrite - {4} (compose_id_right T T f).
suff: (compose (compose f Datatypes.id) (repeat_compose T f n) = repeat_compose T f (n + 1)).
move=> H2.
rewrite H2.
apply (repeat_compose_add T f n 1).
rewrite (plus_comm n 1).
reflexivity.
Qed.