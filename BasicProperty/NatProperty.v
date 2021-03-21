From mathcomp Require Import ssreflect.
Require Import Classical.
Require Import Coq.Logic.Description.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.

Definition is_max_nat := fun (E : (Ensemble nat)) (m : nat) => (In nat E m) /\ forall x : nat, (In nat E x) -> (x <= m)%nat.

Definition is_min_nat := fun (E : (Ensemble nat)) (m : nat) => (In nat E m) /\ forall x : nat, (In nat E x) -> (x >= m)%nat.

Lemma is_max_nat_unique : forall (E : (Ensemble nat)) (m1 m2 : nat), is_max_nat E m1 -> is_max_nat E m2 -> m1 = m2.
Proof.
move=> E m1 m2 H1 H2.
apply (le_antisym m1 m2).
apply (proj2 H2 m1 (proj1 H1)).
apply (proj2 H1 m2 (proj1 H2)).
Qed.

Lemma is_min_nat_unique : forall (E : (Ensemble nat)) (m1 m2 : nat), is_min_nat E m1 -> is_min_nat E m2 -> m1 = m2.
Proof.
move=> E m1 m2 H1 H2.
apply (le_antisym m1 m2).
apply (proj2 H1 m2 (proj1 H2)).
apply (proj2 H2 m1 (proj1 H1)).
Qed.

Lemma nat_cardinal : forall (n : nat) , cardinal nat (fun x : nat => (x < n)%nat) n.
Proof.
move=> n.
elim n.
suff: (fun x : nat => (x < 0)%nat) = (Empty_set nat).
move=> H1.
rewrite H1.
apply (card_empty nat).
apply (Extensionality_Ensembles nat (fun x : nat => (x < 0)%nat) (Empty_set nat)).
apply conj.
move=> m H1.
apply False_ind.
apply (le_not_lt 0 m).
apply (le_O_n m).
apply H1.
move=> m.
elim.
move=> n0 H1.
suff: (Add nat (fun x : nat => (x < n0)%nat) n0) = (fun x : nat => (x < S n0)%nat).
move=> H2.
rewrite - H2.
apply (card_add nat (fun x : nat => (x < n0)%nat) n0 H1 n0).
move=> H3.
apply (le_Sn_n n0 H3).
apply (Extensionality_Ensembles nat (Add nat (fun x : nat => (x < n0)%nat) n0) (fun x : nat => (x < S n0)%nat)).
apply conj.
move=> x.
elim.
move=> x0 H2.
apply (lt_trans x0 n0 (S n0)).
apply H2.
by [].
move=> x0 H2.
rewrite H2.
by [].
move=> x H2.
elim (le_lt_or_eq (S x) (S n0)).
move=> H3.
apply (Union_introl nat (fun x0 : nat => (x0 < n0)%nat) (Singleton nat n0) x).
apply (lt_S_n x n0 H3).
move=> H3.
apply (Union_intror nat (fun x0 : nat => (x0 < n0)%nat) (Singleton nat n0) x).
rewrite - (Nat.pred_succ n0).
rewrite - (Nat.pred_succ x).
rewrite H3.
by [].
apply H2.
Qed.

Lemma Finite_max_nat_exist : forall (U : Ensemble nat), (Finite nat U) -> (Inhabited nat U) -> exists m : nat, (is_max_nat U m).
Proof.
move=> U H1.
elim H1.
move=> H2.
apply False_ind.
elim H2.
move=> x H3.
elim H3.
move=> A H2 H3 x H4 H5.
move: H3.
elim H2.
exists x.
apply conj.
apply (Union_intror nat (Empty_set nat) (Singleton nat x) x).
apply (In_singleton nat x).
move=> x0.
elim.
move=> x1.
elim.
move=> x1.
elim.
by [].
move=> A0 H6 H7 x0 H8.
elim.
move=> x1.
move=> H9.
exists (max x x1).
apply conj.
apply (Nat.max_case_strong x x1).
move=> H10.
apply (Union_intror nat (Add nat A0 x0) (Singleton nat x) x).
apply (In_singleton nat x).
move=> H10.
apply (Union_introl nat (Add nat A0 x0) (Singleton nat x) x1).
apply (proj1 H9).
move=> x2.
elim.
move=> x3 H10.
apply (le_trans x3 x1 (Init.Nat.max x x1)).
apply (proj2 H9 x3 H10).
apply (Nat.le_max_r x x1).
move=> x3.
elim.
apply (Nat.le_max_l x x1).
exists x0.
apply (Union_intror nat A0 (Singleton nat x0) x0).
apply (In_singleton nat x0).
Qed.

Lemma min_nat_exist : forall (U : Ensemble nat), (Inhabited nat U) -> exists m : nat, (is_min_nat U m).
Proof.
suff: (forall (U : Ensemble nat), (Finite nat U) -> (Inhabited nat U) -> exists m : nat, (is_min_nat U m)).
move=> H1 U.
elim.
move=> n H2.
elim (classic (Inhabited nat (Intersection nat U (fun x:nat => (x < n)%nat)))).
move=> H3.
elim (H1 (Intersection nat U (fun x : nat => (x < n)%nat))).
move=> x H4.
exists x.
apply conj.
elim (proj1 H4).
move=> y H5 H6.
apply H5.
move=> y.
elim (le_or_lt n y).
move=> H5 H6.
apply (le_trans x n y).
apply (le_trans x (S x) n).
apply (le_S x).
apply (le_n x).
elim (proj1 H4).
move=> y0 H7.
apply.
apply H5.
move=> H5 H6.
apply ((proj2 H4) y).
apply (Intersection_intro nat U (fun x0 : nat => (x0 < n)%nat) y H6).
apply H5.
suff: (Finite nat (fun x : nat => (x < n)%nat)).
move=> H4.
apply (Intersection_preserves_finite nat (fun x : nat => (x < n)%nat) H4 U).
apply (cardinal_finite nat (fun x : nat => (x < n)%nat) n (nat_cardinal n)).
apply H3.
move=> H3.
exists n.
apply conj.
apply H2.
move=> x H4.
elim (le_or_lt n x).
apply.
move=> H5.
apply False_ind.
apply H3.
apply (Inhabited_intro nat (Intersection nat U (fun x0 : nat => (x0 < n)%nat)) x).
apply (Intersection_intro nat U (fun x0 : nat => (x0 < n)%nat) x H4 H5).
move=> U H1.
elim H1.
move=> H2.
apply False_ind.
elim H2.
move=> x H3.
elim H3.
move=> A H2 H3 x H4 H5.
suff: (Inhabited nat A -> exists m : nat, is_min_nat A m).
elim H2.
move=> H6.
exists x.
apply conj.
apply (Union_intror nat (Empty_set nat) (Singleton nat x) x).
apply (In_singleton nat x).
move=> x0.
elim.
move=> x1.
elim.
move=> x1.
elim.
by [].
move=> A0 H6 H7 x0 H8.
elim.
move=> x1 H9.
exists (min x x1).
apply conj.
apply (Nat.min_case_strong x x1).
move=> H10.
apply (Union_intror nat (Add nat A0 x0) (Singleton nat x) x).
apply (In_singleton nat x).
move=> H10.
apply (Union_introl nat (Add nat A0 x0) (Singleton nat x) x1).
apply (proj1 H9).
move=> x2.
elim.
move=> x3 H10.
apply (le_trans (min x x1) x1 x3).
apply (Nat.le_min_r x x1).
apply (proj2 H9 x3 H10).
move=> x3.
elim.
apply (Nat.le_min_l x x1).
exists x0.
apply (Union_intror nat A0 (Singleton nat x0) x0).
apply (In_singleton nat x0).
apply H3.
Qed.

Lemma min_nat_get : forall (U : Ensemble nat), (Inhabited nat U) -> {m : nat | is_min_nat U m}.
Proof.
move=> U H1.
apply (constructive_definite_description (fun (m : nat) => is_min_nat U m)).
apply (proj1 (unique_existence (fun (m : nat) => is_min_nat U m))).
apply conj.
elim (min_nat_exist U H1).
move=> n H2.
exists n.
apply H2.
unfold uniqueness.
apply (is_min_nat_unique U).
Qed.
