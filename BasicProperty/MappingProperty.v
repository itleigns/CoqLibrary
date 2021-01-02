From mathcomp
Require Import ssreflect.
Require Import Classical.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.FinFun.

Lemma InjSurjBij : forall (A B : Type) (f : A -> B), Injective f -> Surjective f -> Bijective f.
Proof.
move=> A B f H1 H2.
suff: (forall (b : B), {a : A | f a = b}).
move=> H3.
exists (fun (b : B) => proj1_sig (H3 b)).
apply conj.
move=> x.
apply (H1 (proj1_sig (H3 (f x))) x).
apply (proj2_sig (H3 (f x))).
move=> y.
apply (proj2_sig (H3 y)).
move=> b.
apply (constructive_definite_description (fun (a : A) => f a = b)).
apply (proj1 (unique_existence (fun (a : A) => f a = b))).
apply conj.
apply (H2 b).
move=> a1 a2 H3 H4.
apply (H1 a1 a2).
rewrite H4.
apply H3.
Qed.

Lemma BijInj : forall (A B : Type) (f : A -> B), Bijective f -> Injective f.
Proof.
move=> A B f.
elim.
move=> g H1 a1 a2 H2.
rewrite - (proj1 H1 a1).
rewrite - (proj1 H1 a2).
rewrite H2.
reflexivity.
Qed.

Lemma BijSurj : forall (A B : Type) (f : A -> B), Bijective f -> Surjective f.
Proof.
move=> A B f.
elim. 
move=> g H1 b.
exists (g b).
apply (proj2 H1 b).
Qed.
