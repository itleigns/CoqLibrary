From mathcomp Require Import ssreflect.
Require Import Classical.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Image.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.Mult.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Le.

Definition Injective {A B : Type} (f : A -> B) := forall x y, f x = f y -> x = y.

Definition Surjective {A B : Type} (f : A -> B) := forall y, exists x, f x = y.

Definition Bijective {A B : Type} (f : A -> B) := exists (g : B -> A), (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

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

Lemma BijChain : forall (A B C : Type) (f : A -> B) (g : B -> C), Bijective f -> Bijective g -> Bijective (compose g f).
Proof.
move=> A B C f g.
elim.
move=> fi H1.
elim.
move=> gi H2.
exists (fun (c : C) => fi (gi c)).
apply conj.
move=> a.
rewrite (proj1 H2 (f a)).
apply (proj1 H1 a).
move=> c.
unfold compose.
rewrite (proj2 H1 (gi c)).
apply (proj2 H2 c).
Qed.

Lemma SurjChain : forall (A B C : Type) (f : A -> B) (g : B -> C), Surjective f -> Surjective g -> Surjective (compose g f).
Proof.
move=> A B C f g H1 H2 c.
elim (H2 c).
move=> b H3.
elim (H1 b).
move=> a H4.
exists a.
unfold compose.
rewrite H4.
apply H3.
Qed.

Lemma InjChain : forall (A B C : Type) (f : A -> B) (g : B -> C), Injective f -> Injective g -> Injective (compose g f).
Proof.
move=> A B C f g H1 H2 a1 a2 H3.
apply (H1 a1 a2).
apply (H2 (f a1) (f a2) H3).
Qed.

Lemma ChainSurj : forall (A B C : Type) (f : A -> B) (g : B -> C), Surjective (compose g f) -> Surjective g.
Proof.
move=> A B C f g H1 c.
elim (H1 c).
move=> a H2.
exists (f a).
apply H2.
Qed.

Lemma ChainInj : forall (A B C : Type) (f : A -> B) (g : B -> C), Injective (compose g f) -> Injective f.
Proof.
move=> A B C f g H1 a1 a2 H2.
apply (H1 a1 a2).
unfold compose.
rewrite H2.
reflexivity.
Qed.

Lemma InvUnique : forall (A B : Type) (f : A -> B) (g1 g2 : B -> A), ((forall x, g1 (f x) = x) /\ (forall y, f (g1 y) = y)) -> ((forall x, g2 (f x) = x) /\ (forall y, f (g2 y) = y)) -> g1 = g2.
Proof.
move=> A B f g1 g2 H1 H2.
apply functional_extensionality.
move=> x.
apply (BijInj A B f).
exists g1.
apply H1.
rewrite (proj2 H2 x).
apply (proj2 H1 x).
Qed.

Lemma BijectiveInvExist : forall (A B : Type) (f : A -> B), Bijective f -> {g : B -> A | (forall x, g (f x) = x) /\ (forall y, f (g y) = y)}.
Proof.
move=> A B f H1.
apply constructive_definite_description.
apply (proj1 (unique_existence (fun (g : B -> A) => (forall x, g (f x) = x) /\ (forall y, f (g y) = y)))).
apply conj.
elim H1.
move=> g H2.
exists g.
apply H2.
move=> g1 g2 H2 H3.
apply (InvUnique A B f g1 g2 H2 H3).
Qed.

Lemma sig_map : forall {T : Type} (P : T -> Prop) (x : {x : T | P x}) (y : {x : T | P x}), proj1_sig x = proj1_sig y -> x = y.
Proof.
move=> A P x y.
case x.
move=> xv xp.
case y.
move=> yv yp .
simpl.
move=> H1.
subst xv.
rewrite (proof_irrelevance (P yv) yp xp).
by [].
Qed.

Lemma CardinalSigSame : forall (T : Type) (A : Ensemble T) (n : nat), (cardinal T A n) <-> (cardinal {t : T | A t} (Full_set {t : T | A t}) n).
Proof.
suff: (forall (n : nat) (T : Type) (A : Ensemble T) (B : Ensemble T), cardinal T (Intersection T A B) n <-> cardinal {t : T | A t} (fun (x : {t : T | A t}) => B (proj1_sig x)) n).
move=> H1 T A n.
suff: (A = Intersection T A (Full_set T)).
move=> H2.
rewrite {1} H2.
suff: ((Full_set {t : T | A t}) = (fun x : {t : T | A t} => (Full_set T) (proj1_sig x))).
move=> H3.
rewrite H3.
apply (H1 n T A (Full_set T)).
apply Extensionality_Ensembles.
apply conj.
move=> a H3.
apply (Full_intro T (proj1_sig a)).
move=> t H3.
apply (Full_intro {t0 : T | A t0} t).
apply Extensionality_Ensembles.
apply conj.
move=> a H2.
apply (Intersection_intro T A (Full_set T) a H2 (Full_intro T a)).
move=> a.
elim.
move=> a0 H2 H3.
apply H2.
elim.
move=> T A B.
apply conj.
move=> H1.
suff: ((fun x : {t : T | A t} => B (proj1_sig x)) = Empty_set {t : T | A t}).
move=> H2.
rewrite H2.
apply (card_empty {t : T | A t}).
apply Extensionality_Ensembles.
apply conj.
move=> t H2.
apply False_ind.
suff: (In T (Empty_set T) (proj1_sig t)).
elim.
rewrite - (cardinal_invert T (Intersection T A B) 0 H1).
apply (Intersection_intro T A B (proj1_sig t)).
apply (proj2_sig t).
apply H2.
move=> x.
elim.
move=> H1.
suff: (Intersection T A B = Empty_set T).
move=> H2.
rewrite H2.
apply (card_empty T).
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0 H2 H3.
apply False_ind.
suff: (In {t : T | A t} (Empty_set {t : T | A t}) (exist A t0 H2)).
elim.
rewrite - (cardinal_elim {t : T | A t} (fun x : {t : T | A t} => B (proj1_sig x)) 0 H1).
apply H3.
move=> t.
elim.
move=> n H1 T A B.
apply conj.
move=> H2.
elim (cardinal_invert T (Intersection T A B) (S n) H2).
move=> B0.
elim.
move=> b H3.
suff: (In T A b).
move=> H4.
suff: ((fun x : {t : T | A t} => B (proj1_sig x)) = Add {t : T | A t} (fun x : {t : T | A t} => (fun t : T => B t /\ t <> b) (proj1_sig x)) (exist A b H4)).
move=> H5.
rewrite H5.
suff: (cardinal {t : T | A t} (fun x : {t : T | A t} => B (proj1_sig x) /\ proj1_sig x <> b) n).
move=> H6.
apply (card_add {t : T | A t} (fun x : {t : T | A t} => B (proj1_sig x) /\ proj1_sig x <> b) n H6 (exist A b H4)).
move=> H7.
apply (proj2 H7).
reflexivity.
apply (proj1 (H1 T A (fun t : T => B t /\ t <> b))).
suff: (Intersection T A (fun t : T => B t /\ t <> b) = B0).
move=> H6.
rewrite H6.
apply (proj2 (proj2 H3)).
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0 H6 H7.
suff: (In T (Intersection T A B) t0).
rewrite (proj1 H3).
move=> H8.
suff: (t0 <> b).
elim H8.
move=> t1 H9 H10.
apply H9.
move=> t1.
elim.
move=> H9.
apply False_ind.
apply H9.
reflexivity.
apply (proj2 H7).
apply (Intersection_intro T A B t0 H6 (proj1 H7)).
move=> t H6.
apply (Intersection_intro T A (fun t : T => B t /\ t <> b) t).
suff: (In T (Intersection T A B) t).
elim.
move=> t0 H7 H8.
apply H7.
rewrite (proj1 H3).
left.
apply H6.
apply conj.
suff: (In T (Intersection T A B) t).
elim.
move=> t0 H7 H8.
apply H8.
rewrite (proj1 H3).
left.
apply H6.
move=> H7.
apply (proj1 (proj2 H3)).
rewrite - H7.
apply H6.
apply Extensionality_Ensembles.
apply conj.
move=> t H5.
elim (classic (proj1_sig t = b)).
move=> H6.
right.
suff: (t = exist A b H4).
move=> H7.
rewrite H7.
apply (In_singleton {t0 : T | A t0} (exist A b H4)).
apply sig_map.
apply H6.
move=> H6.
left.
apply conj.
apply H5.
apply H6.
move=> t.
elim.
move=> t0 H5.
apply (proj1 H5).
move=> t0 H5.
unfold In.
suff: (In T (Intersection T A B) (proj1_sig t0)).
elim.
move=> t1 H6 H7.
apply H7.
rewrite (proj1 H3).
elim H5.
right.
apply (In_singleton T b).
suff: (In T (Intersection T A B) b).
elim.
move=> t H4 H5.
apply H4.
rewrite (proj1 H3).
right.
apply (In_singleton T b).
move=> H2.
elim (cardinal_invert {t : T | A t} (fun x : {t : T | A t} => B (proj1_sig x)) (S n) H2).
move=> B0.
elim.
move=> b H3.
suff: (Intersection T A B = Add T (Intersection T A (fun (t : T) => exists (H : A t), B0 (exist A t H))) (proj1_sig b)).
move=> H4.
rewrite H4.
suff: (cardinal T (Intersection T A (fun t : T => exists H : A t, B0 (exist A t H))) n).
move=> H5.
apply (card_add T (Intersection T A (fun t : T => exists H : A t, B0 (exist A t H))) n H5 (proj1_sig b)).
move=> H6.
suff: (forall (H : A (proj1_sig b)), ~ B0 (exist A (proj1_sig b) H)).
elim H6.
move=> t H7 H8 H9.
elim H8.
move=> H10 H11.
apply (H9 H10 H11).
move=> H7 H8.
apply (proj1 (proj2 H3)).
suff: (b = (exist A (proj1_sig b) H7)).
move=> H9.
rewrite H9.
apply H8.
apply sig_map.
reflexivity.
apply (proj2 (H1 T A (fun t : T => exists H : A t, B0 (exist A t H)))).
suff: ((fun x : {t : T | A t} => exists H : A (proj1_sig x), B0 (exist A (proj1_sig x) H)) = B0).
move=> H5.
rewrite H5.
apply (proj2 (proj2 H3)).
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> H5 H6.
suff: (t = (exist A (proj1_sig t) H5)).
move=> H7.
rewrite H7.
apply H6.
apply sig_map.
reflexivity.
move=> t H5.
exists (proj2_sig t).
suff: ((exist A (proj1_sig t) (proj2_sig t)) = t).
move=> H6.
rewrite H6.
apply H5.
apply sig_map.
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> t H4.
elim (classic (t = proj1_sig b)).
move=> H5.
right.
rewrite H5.
apply (In_singleton T (proj1_sig b)).
move=> H5.
left.
suff: (t <> proj1_sig b).
elim H4.
move=> t0 H6 H7 H8.
apply (Intersection_intro T A (fun t1 : T => exists H : A t1, B0 (exist A t1 H)) t0 H6).
exists H6.
suff: (~ In {t : T | A t} (Singleton {t : T | A t} b) (exist A t0 H6)).
suff: (In {t : T | A t} (fun x : {t : T | A t} => B (proj1_sig x)) (exist A t0 H6)).
rewrite (proj1 H3).
elim.
move=> t1 H9 H10.
apply H9.
move=> t1 H9 H10.
apply False_ind.
apply (H10 H9).
apply H7.
move=> H9.
apply H8.
suff: (exist A t0 H6 = b).
move=> H10.
rewrite - H10.
reflexivity.
elim H9.
reflexivity.
apply H5.
move=> t.
elim.
move=> t0.
elim.
move=> t1 H4 H5.
apply (Intersection_intro T A B t1 H4).
elim H5.
move=> H6 H7.
suff: (In {t : T | A t} (fun x : {t : T | A t} => B (proj1_sig x)) (exist A t1 H6)).
apply.
rewrite (proj1 H3).
left.
apply H7.
move=> t0.
elim.
apply (Intersection_intro T A B (proj1_sig b)).
apply (proj2_sig b).
suff: (In {t : T | A t} (fun x : {t : T | A t} => B (proj1_sig x)) b).
apply.
rewrite (proj1 H3).
right.
apply (In_singleton {t : T | A t} b).
Qed.

Lemma FiniteSigSame : forall (T : Type) (A : Ensemble T), (Finite T A) <-> (Finite {t : T | A t} (Full_set {t : T | A t})).
Proof.
move=> T A.
apply conj.
move=> H1.
elim (finite_cardinal T A H1).
move=> n H2.
apply (cardinal_finite {t : T | A t} (Full_set {t : T | A t}) n).
apply (proj1 (CardinalSigSame T A n) H2).
move=> H1.
elim (finite_cardinal {t : T | A t} (Full_set {t : T | A t}) H1).
move=> n H2.
apply (cardinal_finite T A n).
apply (proj2 (CardinalSigSame T A n) H2).
Qed.

Lemma CountCardinalBijective : forall (T : Type) (N : nat), (exists (f : {n : nat | n < N} -> T), Bijective f) <-> cardinal T (Full_set T) N.
Proof.
move=> T N.
apply conj.
elim.
move=> f H1.
suff: (forall (k : nat), (k <= N) -> cardinal T (fun (t : T) => exists (m : {n : nat | n < N}), proj1_sig m < k /\ t = f m) k).
move=> H2.
suff: (Full_set T = (fun t : T => exists m : {n : nat | n < N}, proj1_sig m < N /\ t = f m)).
move=> H3.
rewrite H3.
apply (H2 N (le_n N)).
apply Extensionality_Ensembles.
apply conj.
move=> t H3.
elim (BijSurj {n : nat | n < N} T f H1 t).
move=> m H4.
exists m.
apply conj.
apply (proj2_sig m).
rewrite H4.
reflexivity.
move=> t H3.
apply (Full_intro T t).
elim.
move=> H2.
suff: ((fun t : T => exists m : {n : nat | n < N}, proj1_sig m < 0 /\ t = f m) = Empty_set T).
move=> H3.
rewrite H3.
apply (card_empty T).
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> m H3.
apply False_ind.
apply (le_not_lt O (proj1_sig m)).
apply (le_0_n (proj1_sig m)).
apply (proj1 H3).
move=> t.
elim.
move=> k H2 H3.
suff: ((fun t : T => exists m : {n : nat | n < N}, proj1_sig m < S k /\ t = f m) = Add T (fun t : T => exists m : {n : nat | n < N}, proj1_sig m < k /\ t = f m) (f (exist (fun n : nat => n < N) k H3))).
move=> H4.
rewrite H4.
suff: (k <= N).
move=> H5.
apply (card_add T (fun t : T => exists m : {n : nat | n < N}, proj1_sig m < k /\ t = f m) k (H2 H5) (f (exist (fun n : nat => n < N) k H3))).
elim.
move=> m H6.
apply (le_not_lt k k (le_n k)).
suff: (k = proj1_sig (exist (fun n : nat => n < N) k H3)).
move=> H7.
rewrite {1} H7.
suff: ((exist (fun n : nat => n < N) k H3) = m).
move=> H8.
rewrite H8.
apply (proj1 H6).
apply (BijInj {n : nat | n < N} T f H1 (exist (fun n : nat => n < N) k H3) m).
apply (proj2 H6).
reflexivity.
apply (le_trans k (S k) N (le_S k k (le_n k)) H3).
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> m H4.
elim (le_lt_or_eq (proj1_sig m) k).
move=> H5.
left.
exists m.
apply conj.
apply H5.
apply (proj2 H4).
move=> H5.
right.
suff: ((exist (fun n : nat => n < N) k H3) = m).
move=> H6.
rewrite H6.
rewrite (proj2 H4).
apply (In_singleton T (f m)).
apply sig_map.
rewrite H5.
reflexivity.
apply (le_S_n (proj1_sig m) k (proj1 H4)).
move=> t.
elim.
move=> t0.
elim.
move=> m H4.
exists m.
apply conj.
apply (le_S (S (proj1_sig m)) k (proj1 H4)).
apply (proj2 H4).
move=> t0.
elim.
exists (exist (fun n : nat => n < N) k H3).
apply conj.
apply (le_n (S k)).
reflexivity.
move=> H1.
suff: (forall (m : nat) (A : Ensemble T), cardinal T A m -> exists f : {n : nat | n < m} -> {t : T | A t}, Bijective f).
move=> H2.
elim (H2 N (Full_set T) H1).
move=> f H3.
exists (fun m : {n : nat | n < N} => proj1_sig (f m)).
apply (BijChain {n : nat | n < N} {t : T | Full_set T t} T f).
apply H3.
exists (fun t : T => (exist (Full_set T) t (Full_intro T t))).
apply conj.
move=> t0.
apply sig_map.
reflexivity.
move=> y.
reflexivity.
elim.
move=> A H2.
rewrite (cardinal_elim T A 0 H2).
suff: (forall (n : nat), n < 0 -> False).
move=> H3.
exists (fun m : {n : nat | n < 0} => match (H3 (proj1_sig m) (proj2_sig m)) with
end).
exists (fun t0 : {t : T | Empty_set T t} => match (proj2_sig t0) with
end).
apply conj.
move=> m.
apply False_ind.
apply (H3 (proj1_sig m) (proj2_sig m)).
move=> t0.
elim (proj2_sig t0).
move=> n.
apply (le_not_lt 0 n (le_0_n n)).
move=> k H2 A H3.
elim (cardinal_invert T A (S k) H3).
move=> A0.
elim.
move=> a H4.
elim (H2 A0 (proj2 (proj2 H4))).
move=> f H5.
suff: (In T A a).
move=> H6.
suff: (forall (a0 : T), In T A0 a0 -> In T A a0).
move=> H7.
exists (fun m : {n : nat | n < S k} => match excluded_middle_informative (proj1_sig m < k) with
  | left H => exist A (proj1_sig (f (exist (fun n : nat => n < k) (proj1_sig m) H))) (H7 (proj1_sig (f (exist (fun n : nat => n < k) (proj1_sig m) H))) (proj2_sig (f (exist (fun n : nat => n < k) (proj1_sig m) H))))
  | right _ => exist A a H6
end).
apply InjSurjBij.
move=> m1 m2.
elim (excluded_middle_informative (proj1_sig m1 < k)).
move=> H8.
elim (excluded_middle_informative (proj1_sig m2 < k)).
move=> H9 H10.
apply sig_map.
suff: ((exist (fun n : nat => n < k) (proj1_sig m1) H8) = (exist (fun n : nat => n < k) (proj1_sig m2) H9)).
move=> H11.
suff: (proj1_sig m1 = proj1_sig (exist (fun n : nat => n < k) (proj1_sig m1) H8)).
move=> H12.
rewrite H12.
rewrite H11.
reflexivity.
reflexivity.
suff: (f (exist (fun n : nat => n < k) (proj1_sig m1) H8) = f (exist (fun n : nat => n < k) (proj1_sig m2) H9)).
move=> H11.
elim H5.
move=> g H12.
rewrite - (proj1 H12 (exist (fun n : nat => n < k) (proj1_sig m1) H8)).
rewrite H11.
apply (proj1 H12 (exist (fun n : nat => n < k) (proj1_sig m2) H9)).
apply sig_map.
suff: (proj1_sig (f (exist (fun n : nat => n < k) (proj1_sig m1) H8)) = proj1_sig (exist A (proj1_sig (f (exist (fun n : nat => n < k) (proj1_sig m1) H8))) (H7 (proj1_sig (f (exist (fun n : nat => n < k) (proj1_sig m1) H8))) (proj2_sig (f (exist (fun n : nat => n < k) (proj1_sig m1) H8)))))).
move=> H11.
rewrite H11.
rewrite H10.
reflexivity.
reflexivity.
move=> H9 H10.
apply False_ind.
apply (proj1 (proj2 H4)).
suff: (In T A0 (proj1_sig (exist A a H6))).
apply.
rewrite - H10.
simpl.
apply (proj2_sig (f (exist (fun n : nat => n < k) (proj1_sig m1) H8))).
move=> H8.
elim (excluded_middle_informative (proj1_sig m2 < k)).
move=> H9 H10.
apply False_ind.
apply (proj1 (proj2 H4)).
suff: (In T A0 (proj1_sig (exist A a H6))).
apply.
rewrite H10.
simpl.
apply (proj2_sig (f (exist (fun n : nat => n < k) (proj1_sig m2) H9))).
move=> H9 H10.
apply sig_map.
elim (le_lt_or_eq (proj1_sig m1) k).
move=> H11.
elim (H8 H11).
move=> H11.
elim (le_lt_or_eq (proj1_sig m2) k).
move=> H12.
elim (H9 H12).
move=> H12.
rewrite H12.
apply H11.
apply (le_S_n (proj1_sig m2) k (proj2_sig m2)).
apply (le_S_n (proj1_sig m1) k (proj2_sig m1)).
move=> a0.
suff: (In T (Add T A0 a) (proj1_sig a0)).
move=> H8.
suff: (exists m : {n : nat | n < S k}, proj1_sig match excluded_middle_informative (proj1_sig m < k) with
  | left H => exist A (proj1_sig (f (exist (fun n : nat => n < k) (proj1_sig m) H))) (H7 (proj1_sig (f (exist (fun n : nat => n < k) (proj1_sig m) H))) (proj2_sig (f (exist (fun n : nat => n < k) (proj1_sig m) H))))
  | right _ => exist A a H6
end = proj1_sig a0).
elim.
move=> m H9.
exists m.
apply sig_map.
apply H9.
elim H8.
move=> t H9.
elim H5.
move=> g H10.
suff: (forall (n : nat), n < k -> n < S k).
move=> H11.
exists (exist (fun n : nat => n < S k) (proj1_sig (g (exist A0 t H9))) (H11 (proj1_sig (g (exist A0 t H9))) (proj2_sig (g (exist A0 t H9))))).
elim (excluded_middle_informative (proj1_sig (exist (fun n : nat => n < S k) (proj1_sig (g (exist A0 t H9))) (H11 (proj1_sig (g (exist A0 t H9))) (proj2_sig (g (exist A0 t H9))))) < k)).
simpl.
move=> H12.
suff: ((exist (fun n : nat => n < k) (proj1_sig (g (exist A0 t H9))) H12) = (g (exist A0 t H9))).
move=> H13.
rewrite H13.
rewrite (proj2 H10 (exist A0 t H9)).
reflexivity.
apply sig_map.
reflexivity.
move=> H12.
apply False_ind.
apply H12.
simpl.
apply (proj2_sig (g (exist A0 t H9))).
move=> n H11.
apply (le_S (S n) k H11).
move=> t.
elim.
exists (exist (fun m : nat => m < S k) k (le_n (S k))).
elim (excluded_middle_informative (proj1_sig (exist (fun m : nat => m < S k) k (le_n (S k))) < k)).
simpl.
move=> H9.
apply False_ind.
apply (le_not_lt k k (le_n k) H9).
move=> H9.
reflexivity.
rewrite - (proj1 H4).
apply (proj2_sig a0).
move=> a0 H7.
rewrite (proj1 H4).
left.
apply H7.
rewrite (proj1 H4).
right.
apply (In_singleton T a).
Qed.

Lemma CountFiniteBijective : forall (T : Type), (exists (N : nat) (f : {n : nat | n < N} -> T), Bijective f) <-> Finite T (Full_set T).
Proof.
move=> T.
apply conj.
elim.
move=> N.
elim.
move=> f H1.
apply (cardinal_finite T (Full_set T) N).
apply (proj1 (CountCardinalBijective T N)).
exists f.
apply H1.
move=> H1.
elim (finite_cardinal T (Full_set T) H1).
move=> N H2.
exists N.
apply (proj2 (CountCardinalBijective T N) H2).
Qed.

Lemma CountCardinalSurjective : forall (T : Type) (N : nat) (f : {n : nat | n < N} -> T), Surjective f -> exists (M : nat), M <= N /\ cardinal T (Full_set T) M.
Proof.
move=> T N f H1.
suff: (forall (k : nat), k <= N -> exists (M : nat), M <= k /\ cardinal T (Im {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < k) f) M).
move=> H2.
suff: (Full_set T = Im {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < N) f).
move=> H3.
rewrite H3.
apply (H2 N (le_n N)).
apply Extensionality_Ensembles.
apply conj.
move=> t H3.
elim (H1 t).
move=> m0 H4.
apply (Im_intro {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < N) f m0).
apply (proj2_sig m0).
rewrite H4.
reflexivity.
move=> t H3.
apply (Full_intro T t).
elim.
move=> H2.
exists O.
apply conj.
apply (le_n O).
suff: (Im {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < 0) f = Empty_set T).
move=> H3.
rewrite H3.
apply (card_empty T).
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> m H3.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H3).
move=> t.
elim.
move=> k H2 H3.
elim (H2 (le_trans k (S k) N (le_S k k (le_n k)) H3)).
move=> M H4.
elim (classic (In T (Im {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < k) f) (f (exist (fun n : nat => n < N) k H3)))).
move=> H5.
exists M.
apply conj.
apply (le_S M k (proj1 H4)).
suff: (Im {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < S k) f = (Im {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < k) f)).
move=> H6.
rewrite H6.
apply (proj2 H4).
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> m H6 y H7.
rewrite H7.
elim (le_lt_or_eq (S (proj1_sig m)) (S k) H6).
move=> H8.
apply (Im_intro {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < k) f m).
apply (lt_S_n (proj1_sig m) k H8).
reflexivity.
move=> H8.
suff: (m = (exist (fun n : nat => n < N) k H3)).
move=> H9.
rewrite H9.
apply H5.
apply sig_map.
apply (eq_add_S (proj1_sig m) k H8).
move=> t.
elim.
move=> m H6 y H7.
apply (Im_intro {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < S k) f m).
apply (le_S (S (proj1_sig m)) k H6).
apply H7.
move=> H5.
exists (S M).
apply conj.
apply (le_n_S M k (proj1 H4)).
suff: (Im {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < S k) f = Add T (Im {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < k) f) (f (exist (fun n : nat => n < N) k H3))).
move=> H6.
rewrite H6.
apply (card_add T (Im {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < k) f) M (proj2 H4) (f (exist (fun n : nat => n < N) k H3))).
apply H5.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> m H6 y H7.
elim (le_lt_or_eq (S (proj1_sig m)) (S k) H6).
move=> H8.
left.
apply (Im_intro {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < k) f m).
apply (lt_S_n (proj1_sig m) k H8).
apply H7.
move=> H8.
right.
rewrite H7.
suff: ((exist (fun n : nat => n < N) k H3) = m).
move=> H9.
rewrite H9.
apply (In_singleton T (f m)).
apply sig_map.
apply (eq_add_S k (proj1_sig m)).
rewrite H8.
reflexivity.
move=> t.
elim.
move=> t0.
elim.
move=> m H6 y H7.
apply (Im_intro {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < S k) f m).
apply (le_S (S (proj1_sig m)) k H6).
apply H7.
move=> t0.
elim.
apply (Im_intro {n : nat | n < N} T (fun m : {n : nat | n < N} => proj1_sig m < S k) f (exist (fun n : nat => n < N) k H3)).
apply (le_n (S k)).
reflexivity.
Qed.

Lemma CountFiniteSurjective : forall (T : Type) (N : nat) (f : {n : nat | n < N} -> T), Surjective f -> Finite T (Full_set T).
Proof.
move=> T N f H1.
elim (CountCardinalSurjective T N f H1).
move=> n H2.
apply (cardinal_finite T (Full_set T) n (proj2 H2)).
Qed.

Lemma CountCardinalInjective : forall (T : Type) (N : nat) (f : T -> {n : nat | n < N}), Injective f -> exists (M : nat), M <= N /\ cardinal T (Full_set T) M.
Proof.
move=> T N f H1.
suff: (forall (k : nat), k <= N -> exists (M : nat), M <= k /\ cardinal T (fun t : T => proj1_sig (f t) < k) M).
move=> H2.
suff: (Full_set T = (fun t : T => proj1_sig (f t) < N)).
move=> H3.
rewrite H3.
apply (H2 N (le_n N)).
apply Extensionality_Ensembles.
apply conj.
move=> t H3.
apply (proj2_sig (f t)).
move=> t H3.
apply (Full_intro T t).
elim.
move=> H2.
exists O.
apply conj.
apply (le_n O).
suff: ((fun t : T => proj1_sig (f t) < 0) = Empty_set T).
move=> H3.
rewrite H3.
apply (card_empty T).
apply Extensionality_Ensembles.
apply conj.
move=> t H3.
apply False_ind.
apply (le_not_lt O (proj1_sig (f t)) (le_0_n (proj1_sig (f t))) H3).
move=> t.
elim.
move=> k H2 H3.
elim (H2 (le_trans k (S k) N (le_S k k (le_n k)) H3)).
move=> M H4.
elim (classic (Inhabited T (fun t : T => proj1_sig (f t) = k))).
elim.
move=> t H5.
exists (S M).
apply conj.
apply (le_n_S M k (proj1 H4)).
suff: ((fun t0 : T => proj1_sig (f t0) < S k) = Add T (fun t : T => proj1_sig (f t) < k) t).
move=> H6.
rewrite H6.
apply (card_add T (fun t : T => proj1_sig (f t) < k) M (proj2 H4) t).
move=> H7.
apply (lt_not_le (proj1_sig (f t)) k H7).
rewrite H5.
apply (le_n k).
apply Extensionality_Ensembles.
apply conj.
move=> t0 H6.
elim (le_lt_or_eq (S (proj1_sig (f t0))) (S k) H6).
move=> H7.
left.
apply (lt_S_n (proj1_sig (f t0)) k H7).
move=> H7.
right.
suff: (t0 = t).
move=> H8.
rewrite H8.
apply (In_singleton T t).
apply (H1 t0 t).
apply sig_map.
rewrite H5.
apply (eq_add_S (proj1_sig (f t0)) k H7).
move=> t0.
elim.
move=> t1 H6.
apply (le_S (S (proj1_sig (f t1))) k H6).
move=> t1.
elim.
unfold In.
rewrite H5.
apply (le_n (S k)).
move=> H5.
exists M.
apply conj.
apply (le_S M k (proj1 H4)).
suff: ((fun t : T => proj1_sig (f t) < S k) = (fun t : T => proj1_sig (f t) < k)).
move=> H6.
rewrite H6.
apply (proj2 H4).
apply Extensionality_Ensembles.
apply conj.
move=> t H6.
elim (le_lt_or_eq (S (proj1_sig (f t))) (S k) H6).
move=> H7.
apply (lt_S_n (proj1_sig (f t)) k H7).
move=> H7.
apply False_ind.
apply H5.
apply (Inhabited_intro T (fun t : T => proj1_sig (f t) = k) t).
apply (eq_add_S (proj1_sig (f t)) k H7).
move=> t.
apply (le_S (S (proj1_sig (f t))) k).
Qed.

Lemma CountFiniteInjective : forall (T : Type) (N : nat) (f : T -> {n : nat | n < N}), Injective f -> Finite T (Full_set T).
Proof.
move=> T N f H1.
elim (CountCardinalInjective T N f H1).
move=> n H2.
apply (cardinal_finite T (Full_set T) n (proj2 H2)).
Qed.

Lemma BijectiveSigFull : forall (T : Type) (A : Ensemble T), (forall (t : T), In T A t) -> {f : T -> {t : T | In T A t} | (forall (t : T), t = proj1_sig (f t)) /\ Bijective f}.
Proof.
move=> T A H1.
exists (fun (t : T) => exist A t (H1 t)).
apply conj.
move=> t.
reflexivity.
exists (fun (t0 : {t : T | In T A t}) => proj1_sig t0).
apply conj.
move=> x.
reflexivity.
move=> y.
apply sig_map.
reflexivity.
Qed.

Lemma BijectiveSigFullInv : forall (T : Type) (A : Ensemble T), (forall (t : T), In T A t) -> {f : {t : T | In T A t} -> T | (forall (t0 : {t : T | In T A t}), proj1_sig t0 = f t0) /\ Bijective f}.
Proof.
move=> T A H1.
exists (fun (t0 : {t : T | In T A t}) => proj1_sig t0).
apply conj.
move=> t0.
reflexivity.
exists (fun (t : T) => exist A t (H1 t)).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
reflexivity.
Qed.

Lemma BijectiveSameSig : forall (T : Type) (A B : Ensemble T), A = B -> {f : {t : T | In T A t} -> {t : T | In T B t} | (forall (t0 : {t : T | In T A t}), proj1_sig t0 = proj1_sig (f t0)) /\ Bijective f}.
Proof.
move=> T A B H1.
rewrite H1.
exists (fun (t0 : {t : T | In T B t}) => t0).
apply conj.
move=> t0.
reflexivity.
exists (fun (t0 : {t : T | In T B t}) => t0).
apply conj.
move=> x.
reflexivity.
move=> y.
reflexivity.
Qed.

Lemma BijectiveSigSig : forall (T : Type) (A B : Ensemble T), {f : {t : T | In T (Intersection T A B) t} -> {t0 : {t : T | In T A t} | In T B (proj1_sig t0)} | (forall (t0 : {t : T | In T (Intersection T A B) t}), proj1_sig t0 = proj1_sig (proj1_sig (f t0))) /\ Bijective f}.
Proof.
move=> T A B.
suff: (forall (t0 : {t : T | In T (Intersection T A B) t}), In T A (proj1_sig t0)).
move=> H1.
suff: (forall (t0 : {t : T | In T (Intersection T A B) t}), In T B (proj1_sig t0)).
move=> H2.
exists (fun (t0 : {t : T | In T (Intersection T A B) t}) => exist (fun (a : {t : T | In T A t}) => In T B (proj1_sig a)) (exist A (proj1_sig t0) (H1 t0)) (H2 t0)).
apply conj.
move=> t0.
reflexivity.
suff: (forall (x : {t0 : {t : T | In T A t} | In T B (proj1_sig t0)}),In T (Intersection T A B) (proj1_sig (proj1_sig x))).
move=> H3.
exists (fun (x : {t0 : {t : T | In T A t} | In T B (proj1_sig t0)}) => exist (Intersection T A B) (proj1_sig (proj1_sig x)) (H3 x)).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
reflexivity.
move=> x.
apply (Intersection_intro T A B (proj1_sig (proj1_sig x))).
apply (proj2_sig (proj1_sig x)).
apply (proj2_sig x).
move=> t0.
elim (proj2_sig t0).
move=> x H2 H3.
apply H3.
move=> t0.
elim (proj2_sig t0).
move=> x H2 H3.
apply H2.
Qed.

Lemma BijectiveSigSigInv : forall (T : Type) (A B : Ensemble T), {f : {t0 : {t : T | In T A t} | In T B (proj1_sig t0)} -> {t : T | In T (Intersection T A B) t} | (forall (x : {t0 : {t : T | In T A t} | In T B (proj1_sig t0)}), proj1_sig (proj1_sig x) = proj1_sig (f x)) /\ Bijective f}.
Proof.
move=> T A B.
suff: (forall (x : {t0 : {t : T | In T A t} | In T B (proj1_sig t0)}),In T (Intersection T A B) (proj1_sig (proj1_sig x))).
move=> H1.
exists (fun (x : {t0 : {t : T | In T A t} | In T B (proj1_sig t0)}) => exist (Intersection T A B) (proj1_sig (proj1_sig x)) (H1 x)).
apply conj.
move=> x.
reflexivity.
suff: (forall (t0 : {t : T | In T (Intersection T A B) t}), In T A (proj1_sig t0)).
move=> H2.
suff: (forall (t0 : {t : T | In T (Intersection T A B) t}), In T B (proj1_sig t0)).
move=> H3.
exists (fun (t0 : {t : T | In T (Intersection T A B) t}) => exist (fun (a : {t : T | In T A t}) => In T B (proj1_sig a)) (exist A (proj1_sig t0) (H2 t0)) (H3 t0)).
apply conj.
move=> x.
apply sig_map.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
reflexivity.
move=> t0.
elim (proj2_sig t0).
move=> x H3 H4.
apply H4.
move=> t0.
elim (proj2_sig t0).
move=> x H3 H4.
apply H3.
move=> x.
apply (Intersection_intro T A B (proj1_sig (proj1_sig x))).
apply (proj2_sig (proj1_sig x)).
apply (proj2_sig x).
Qed.

Lemma ForallSavesBijective_dep : forall (T : Type) (A : T -> Type) (B : T -> Type) (F : forall (t : T), (A t) -> (B t)), (forall (t : T), Bijective (F t)) -> Bijective (fun (x : forall (t : T), (A t)) (t0 : T) => (F t0 (x t0))).
Proof.
move=> T A B F H1.
suff: (forall (t : T), {g : (B t) -> (A t) | (forall (x : A t), g ((F t) x) = x) /\ (forall (y : B t), (F t) (g y) = y)}).
move=> H2.
exists (fun (y : forall (t : T), B t) (t0 : T) => proj1_sig (H2 t0) (y t0)).
apply conj.
move=> x.
apply functional_extensionality_dep.
move=> t.
apply (proj1 (proj2_sig (H2 t)) (x t)).
move=> y.
apply functional_extensionality_dep.
move=> t.
apply (proj2 (proj2_sig (H2 t)) (y t)).
move=> t.
apply constructive_definite_description.
apply (proj1 (unique_existence (fun (g : B t -> A t) => (forall (x : A t), g (F t x) = x) /\ (forall y : B t, F t (g y) = y)))).
apply conj.
elim (H1 t).
move=> g H2.
exists g.
apply H2.
move=> g1 g2 H2 H3.
apply functional_extensionality_dep.
move=> y.
rewrite - {1} (proj2 H3 y).
apply (proj1 H2 (g2 y)).
Qed.

Lemma ForallSavesBijective : forall (T A B: Type) (F : T -> A -> B), (forall (t : T), Bijective (F t)) -> Bijective (fun (x : T -> A) (t0 : T) => (F t0 (x t0))).
Proof.
move=> T A B F.
apply (ForallSavesBijective_dep T (fun (t : T) => A) (fun (t : T) => B) F).
Qed.

Lemma ForallSavesInjective_dep : forall (T : Type) (A : T -> Type) (B : T -> Type) (F : forall (t : T), (A t) -> (B t)), (forall (t : T), Injective (F t)) -> Injective (fun (x : forall (t : T), (A t)) (t0 : T) => (F t0 (x t0))).
Proof.
move=> T A B F H1 x1 x2 H2.
apply functional_extensionality_dep.
move=> t.
apply (H1 t (x1 t) (x2 t)).
suff: (F t (x1 t) = let temp := (fun t0 : T => F t0 (x1 t0)) in temp t).
move=> H3.
rewrite H3.
rewrite H2.
reflexivity.
reflexivity.
Qed.

Lemma ForallSavesInjective : forall (T A B: Type) (F : T -> A -> B), (forall (t : T), Injective (F t)) -> Injective (fun (x : T -> A) (t0 : T) => (F t0 (x t0))).
Proof.
move=> T A B F.
apply (ForallSavesInjective_dep T (fun (t : T) => A) (fun (t : T) => B) F).
Qed.

Lemma AddConnectSig : forall (N M : nat), {f : {n : nat | n < N} + {n : nat | n < M} -> {n : nat | n < N + M} | (forall (m : {n : nat | n < N}), proj1_sig m = proj1_sig (f (inl m))) /\ (forall (m : {n : nat | n < M}), N + proj1_sig m = proj1_sig (f (inr m)))}.
Proof.
move=> N M.
suff: (forall (m : {n : nat | n < N}), proj1_sig m < N + M).
move=> H1.
suff: (forall (m : {n : nat | n < M}), N + proj1_sig m < N + M).
move=> H2.
exists (fun (m : {n : nat | n < N} + {n : nat | n < M}) => match m with
  | inl k => exist (fun (l : nat) => l < N + M) (proj1_sig k) (H1 k)
  | inr k => exist (fun (l : nat) => l < N + M) (N + proj1_sig k) (H2 k)
end).
apply conj.
move=> m.
reflexivity.
move=> m.
reflexivity.
move=> m.
apply (plus_lt_compat_l (proj1_sig m) M N (proj2_sig m)).
move=> m.
apply (le_trans (S (proj1_sig m)) N (N + M) (proj2_sig m) (le_plus_l N M)).
Qed.

Definition AddConnect (N M : nat) := proj1_sig (AddConnectSig N M).

Definition AddConnectNature (N M : nat) : (forall (m : {n : nat | n < N}), proj1_sig m = proj1_sig (AddConnect N M (inl m))) /\ (forall (m : {n : nat | n < M}), N + proj1_sig m = proj1_sig (AddConnect N M (inr m))) := proj2_sig (AddConnectSig N M).

Lemma AddConnectInvSig : forall (N M : nat), {f : {n : nat | n < N + M} -> {n : nat | n < N} + {n : nat | n < M} | (forall (m : {n : nat | n < N + M}), (proj1_sig m < N) -> match (f m) with
  | inl k => proj1_sig m = proj1_sig k
  | inr _ => False
end) /\ (forall (m : {n : nat | n < N + M}), (N <= proj1_sig m) -> match (f m) with
  | inl _ => False
  | inr k => proj1_sig m = N + proj1_sig k
end)}.
Proof.
move=> N M.
suff: (forall (m : {n : nat | n < N + M}), ~ proj1_sig m < N -> proj1_sig m - N < M).
move=> H1.
exists (fun (m : {n : nat | n < N + M}) => match excluded_middle_informative (proj1_sig m < N) with
  | left H => inl (exist (fun (k : nat) => k < N) (proj1_sig m) H)
  | right H => inr (exist (fun (k : nat) => k < M) (proj1_sig m - N) (H1 m H))
end).
apply conj.
move=> m H2.
elim (excluded_middle_informative (proj1_sig m < N)).
move=> H3.
reflexivity.
move=> H3.
apply (H3 H2).
move=> m H2.
elim (excluded_middle_informative (proj1_sig m < N)).
move=> H3.
apply (le_not_lt N (proj1_sig m) H2 H3).
move=> H3.
apply (le_plus_minus N (proj1_sig m) H2).
move=> m H1.
apply (plus_lt_reg_l (proj1_sig m - N) M N).
rewrite (le_plus_minus_r N (proj1_sig m)).
apply (proj2_sig m).
elim (le_or_lt N (proj1_sig m)).
apply.
move=> H2.
apply False_ind.
apply (H1 H2).
Qed.

Definition AddConnectInv (N M : nat) := proj1_sig (AddConnectInvSig N M).

Definition AddConnectInvNature (N M : nat) : (forall (m : {n : nat | n < N + M}), proj1_sig m < N -> match AddConnectInv N M m with
  | inl k => proj1_sig m = proj1_sig k
  | inr _ => False
end) /\ (forall (m : {n : nat | n < N + M}), N <= proj1_sig m -> match AddConnectInv N M m with
  | inl _ => False
  | inr k => proj1_sig m = N + proj1_sig k
end) := proj2_sig (AddConnectInvSig N M).

Lemma AddConnectInvRelation : forall (N M : nat), (forall (m : {n : nat | n < N} + {n : nat | n < M}), AddConnectInv N M (AddConnect N M m) = m) /\ (forall (m : {n : nat | n < N + M}), AddConnect N M (AddConnectInv N M m) = m).
Proof.
move=> N M.
apply conj.
elim.
move=> m.
suff: (match AddConnectInv N M (AddConnect N M (inl m)) return Prop with
  | inl k => proj1_sig (AddConnect N M (inl m)) = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv N M (AddConnect N M (inl m))).
move=> k H1.
suff: (k = m).
move=> H2.
rewrite H2.
reflexivity.
apply sig_map.
rewrite - H1.
rewrite (proj1 (AddConnectNature N M) m).
reflexivity.
move=> k.
elim.
apply (proj1 (AddConnectInvNature N M) (AddConnect N M (inl m))).
rewrite - (proj1 (AddConnectNature N M) m).
apply (proj2_sig m).
move=> m.
suff: (match AddConnectInv N M (AddConnect N M (inr m)) return Prop with
  | inl _ => False
  | inr k => proj1_sig (AddConnect N M (inr m)) = N + proj1_sig k
end).
elim (AddConnectInv N M (AddConnect N M (inr m))).
move=> k.
elim.
move=> k H1.
suff: (m = k).
move=> H2.
rewrite H2.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig m) (proj1_sig k) N).
rewrite (proj2 (AddConnectNature N M) m).
apply H1.
apply (proj2 (AddConnectInvNature N M) (AddConnect N M (inr m))).
rewrite - (proj2 (AddConnectNature N M) m).
apply (le_plus_l N (proj1_sig m)).
move=> m.
elim (le_or_lt N (proj1_sig m)).
move=> H1.
suff: (match AddConnectInv N M m return Prop with
  | inl _ => False
  | inr k => proj1_sig m = N + proj1_sig k
end).
elim (AddConnectInv N M m).
move=> k.
elim.
move=> k H2.
apply sig_map.
rewrite H2.
rewrite (proj2 (AddConnectNature N M) k).
reflexivity.
apply (proj2 (AddConnectInvNature N M) m).
apply H1.
move=> H1.
suff: (match AddConnectInv N M m return Prop with
  | inl k => proj1_sig m = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv N M m).
move=> k H2.
apply sig_map.
rewrite H2.
rewrite (proj1 (AddConnectNature N M) k).
reflexivity.
move=> k.
elim.
apply (proj1 (AddConnectInvNature N M) m).
apply H1.
Qed.

Lemma CountAdd : forall (N M : nat), {f : {n : nat | n < N} + {n : nat | n < M} -> {n : nat | n < N + M} | Bijective f}.
Proof.
move=> N M.
exists (AddConnect N M).
exists (AddConnectInv N M).
apply (AddConnectInvRelation N M).
Qed.

Lemma CountMult : forall (N M : nat), {f : {n : nat | n < N} * {n : nat | n < M} -> {n : nat | n < N * M} | Bijective f}.
Proof.
move=> N M.
elim N.
exists (fun (xy : {n : nat | n < 0} * {n : nat | n < M}) => match (PeanoNat.Nat.nlt_0_r (proj1_sig (fst xy)) (proj2_sig (fst xy))) with
end).
suff: (forall (k : {n : nat | n < 0 * N}), False).
move=> H1.
exists (fun (k : {n : nat | n < 0 * N}) => match (H1 k) with
end).
apply conj.
move=> x.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig (fst x)) (proj2_sig (fst x))).
move=> y.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig y)).
rewrite - {2} (mult_0_l N).
apply (proj2_sig y).
rewrite (mult_0_l N).
apply (fun (k : {n : nat | n < 0}) => (PeanoNat.Nat.nlt_0_r (proj1_sig k) (proj2_sig k))).
simpl.
move=> K H1.
suff: {f : {n : nat | n < S K} * {n : nat | n < M} -> {n : nat | n < M} + {n : nat | n < K * M} | Bijective f}.
move=> H2.
exists (compose (proj1_sig (CountAdd M (K * M))) (proj1_sig H2)).
apply BijChain.
apply (proj2_sig H2).
apply (proj2_sig (CountAdd M (K * M))).
exists (fun (xy : {n : nat | n < S K} * {n : nat | n < M}) => match excluded_middle_informative (proj1_sig (fst xy) < K) with
  | left H => inr (proj1_sig H1 (exist (fun (k : nat) => k < K) (proj1_sig (fst xy)) H, snd xy))
  | right _ => inl (snd xy)
end).
elim (proj2_sig H1).
move=> g H2.
exists (fun (x : {n : nat | n < M} + {n : nat | n < K * M}) => match x with
  | inl k => (exist (fun (n : nat) => n < S K) K (le_n (S K)), k)
  | inr k => (exist (fun (n : nat) => n < S K) (proj1_sig (fst (g k))) (le_trans (S (proj1_sig (fst (g k)))) K (S K) (proj2_sig (fst (g k))) (le_S K K (le_n K))), snd (g k))
end).
apply conj.
move=> x.
elim (excluded_middle_informative (proj1_sig (fst x) < K)).
move=> H3.
apply injective_projections.
apply sig_map.
simpl.
rewrite (proj1 H2 (exist (fun k : nat => k < K) (proj1_sig (fst x)) H3, snd x)).
reflexivity.
simpl.
rewrite (proj1 H2 (exist (fun k : nat => k < K) (proj1_sig (fst x)) H3, snd x)).
reflexivity.
move=> H3.
apply injective_projections.
apply sig_map.
simpl.
elim (le_lt_or_eq (proj1_sig (fst x)) K).
move=> H4.
apply False_ind.
apply (H3 H4).
move=> H4.
rewrite H4.
reflexivity.
apply (le_S_n (proj1_sig (fst x)) K (proj2_sig (fst x))).
reflexivity.
elim.
simpl.
elim (excluded_middle_informative (K < K)).
move=> H3.
apply False_ind.
apply (lt_irrefl K H3).
move=> H3 H4.
reflexivity.
simpl.
move=> k.
elim (excluded_middle_informative (proj1_sig (fst (g k)) < K)).
move=> H4.
suff: ((proj1_sig H1 (exist (fun n : nat => n < K) (proj1_sig (fst (g k))) H4, snd (g k))) = k).
move=> H5.
rewrite H5.
reflexivity.
suff: ((exist (fun n : nat => n < K) (proj1_sig (fst (g k))) H4, snd (g k)) = g k).
move=> H5.
rewrite H5.
apply (proj2 H2 k).
apply injective_projections.
suff: (exist (fun n : nat => n < K) (proj1_sig (fst (g k))) H4 = fst (g k)).
move=> H5.
rewrite H5.
reflexivity.
apply sig_map.
reflexivity.
reflexivity.
move=> H3.
apply False_ind.
apply (H3 (proj2_sig (fst (g k)))).
Qed.

Lemma CountPow : forall (N M : nat), {f : ({n : nat | n < N} -> {n : nat | n < M}) -> {n : nat | n < M ^ N} | Bijective f}.
Proof.
move=> N M.
elim N.
simpl.
exists (fun (_ : {n : nat | n < 0} -> {n : nat | n < M}) => exist (fun (n : nat) => n < S O) O (le_n (S O))).
exists (fun (m : {n : nat | n < S O}) (k : {n : nat | n < O}) => match (PeanoNat.Nat.nlt_0_r (proj1_sig k) (proj2_sig k)) with
end).
apply conj.
move=> x.
apply functional_extensionality.
move=> k.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig k) (proj2_sig k)).
move=> y.
apply sig_map.
simpl.
elim (le_lt_or_eq (proj1_sig y) O).
move=> H1.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig y) H1).
move=> H1.
rewrite H1.
reflexivity.
apply (le_S_n (proj1_sig y) O (proj2_sig y)).
move=> K.
elim.
move=> f1 H1.
simpl.
suff: ({f : ({n : nat | n < S K} -> {n : nat | n < M}) -> ({n : nat | n < M} * {n : nat | n < M ^ K}) | Bijective f}).
elim.
move=> f2 H2.
exists (compose (proj1_sig (CountMult M (M ^ K))) f2).
apply BijChain.
apply H2.
apply (proj2_sig (CountMult M (M ^ K))).
exists (fun (x : {n : nat | n < S K} -> {n : nat | n < M}) => (x (exist (fun (n : nat) => n < S K) K (le_n (S K))), f1 (fun (m : {n : nat | n < K}) => x (exist (fun (n : nat) => n < S K) (proj1_sig m) (le_trans (S (proj1_sig m)) K (S K) (proj2_sig m) (le_S K K (le_n K))))))).
elim H1.
move=> g1 H2.
exists (fun (x : {n : nat | n < M} * {n : nat | n < M ^ K}) (k : {n : nat | n < S K}) => match excluded_middle_informative (proj1_sig k < K) with
  | left H => g1 (snd x) (exist (fun (n : nat) => n < K) (proj1_sig k) H)
  | right H => fst x
end).
apply conj.
move=> x.
apply functional_extensionality.
move=> k.
elim (excluded_middle_informative (proj1_sig k < K)).
move=> H3.
simpl.
rewrite (proj1 H2 (fun m : {n : nat | n < K} => x (exist (fun n : nat => n < S K) (proj1_sig m) (Nat.le_trans (S (proj1_sig m)) K (S K) (proj2_sig m) (le_S K K (le_n K)))))).
suff: ((exist (fun n : nat => n < S K) (proj1_sig (exist (fun n : nat => n < K) (proj1_sig k) H3)) (Nat.le_trans (S (proj1_sig (exist (fun n : nat => n < K) (proj1_sig k) H3))) K (S K) (proj2_sig (exist (fun n : nat => n < K) (proj1_sig k) H3)) (le_S K K (le_n K)))) = k).
move=> H4.
rewrite H4.
reflexivity.
apply sig_map.
reflexivity.
move=> H3.
suff: ((exist (fun n : nat => n < S K) K (le_n (S K))) = k).
move=> H4.
rewrite H4.
reflexivity.
apply sig_map.
elim (le_lt_or_eq (proj1_sig k) K (le_S_n (proj1_sig k) K (proj2_sig k))).
move=> H4.
apply False_ind.
apply (H3 H4).
move=> H4.
rewrite H4.
reflexivity.
move=> y.
simpl.
elim (excluded_middle_informative (K < K)).
move=> H3.
apply False_ind.
apply (lt_irrefl K H3).
move=> H3.
apply injective_projections.
reflexivity.
apply (BijInj {n : nat | n < M ^ K} ({n : nat | n < K} -> {n : nat | n < M}) g1).
exists f1.
apply conj.
apply (proj2 H2).
apply (proj1 H2).
simpl.
rewrite (proj1 H2 (fun m : {n : nat | n < K} => match excluded_middle_informative (proj1_sig m < K) with
  | left H => g1 (snd y) (exist (fun n : nat => n < K) (proj1_sig m) H)
  | right _ => fst y
end)).
apply functional_extensionality.
move=> k.
elim (excluded_middle_informative (proj1_sig k < K)).
move=> H4.
suff: ((exist (fun n : nat => n < K) (proj1_sig k) H4) = k).
move=> H5.
rewrite H5.
reflexivity.
apply sig_map.
reflexivity.
move=> H4.
apply False_ind.
apply (H4 (proj2_sig k)).
Qed.

Lemma CountPowFinite : forall (N M : nat), Finite ({n : nat | (n < N)%nat} -> {n : nat | (n < M)%nat}) (Full_set ({n : nat | (n < N)%nat} -> {n : nat | (n < M)%nat})).
Proof.
move=> N M.
apply (cardinal_finite ({n : nat | (n < N)%nat} -> {n : nat | (n < M)%nat}) (Full_set ({n : nat | (n < N)%nat} -> {n : nat | (n < M)%nat})) (M ^ N)).
apply (proj1 (CountCardinalBijective ({n : nat | (n < N)%nat} -> {n : nat | (n < M)%nat}) (M ^ N))).
elim (proj2_sig (CountPow N M)).
move=> g H1.
exists g.
exists (proj1_sig (CountPow N M)).
apply conj.
apply (proj2 H1).
apply (proj1 H1).
Qed.

Lemma CountInjBij : forall (N : nat) (f : {n : nat | (n < N)%nat} -> {n : nat | (n < N)%nat}), Injective f -> Bijective f.
Proof.
move=> N f H1.
apply InjSurjBij.
apply H1.
suff: (Im {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (Full_set {n : nat | (n < N)%nat}) f = (Full_set {n : nat | (n < N)%nat})).
move=> H2 k.
suff: (In {n : nat | (n < N)%nat} (Im {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (Full_set {n : nat | (n < N)%nat}) f) k).
elim.
move=> x H3 y H4.
exists x.
rewrite H4.
reflexivity.
rewrite H2.
apply (Full_intro {n : nat | (n < N)%nat} k).
suff: (cardinal {n : nat | (n < N)%nat} (Im {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (Full_set {n : nat | (n < N)%nat}) f) N).
move=> H2.
apply Extensionality_Ensembles.
apply conj.
move=> k H3.
apply (Full_intro {n : nat | (n < N)%nat} k).
move=> k H3.
apply NNPP.
move=> H4.
apply (lt_irrefl N).
apply (incl_card_le {n : nat | (n < N)%nat} (Add {n : nat | (n < N)%nat} (Im {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (Full_set {n : nat | (n < N)%nat}) f) k) (Full_set {n : nat | (n < N)%nat}) (S N) N).
apply (card_add {n : nat | (n < N)%nat}).
apply H2.
apply H4.
apply CountCardinalBijective.
exists (fun (k : {n : nat | (n < N)%nat}) => k).
exists (fun (k : {n : nat | (n < N)%nat}) => k).
apply conj.
move=> l.
reflexivity.
move=> l.
reflexivity.
move=> l H5.
apply (Full_intro {n : nat | (n < N)%nat} l).
suff: (forall (m : nat), (m <= N)%nat -> cardinal {n : nat | (n < N)%nat} (Im {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (fun (k : {n : nat | (n < N)%nat}) => (proj1_sig k < m)%nat) f) m).
move=> H2.
suff: ((Full_set {n : nat | (n < N)%nat}) = (fun (k : {n : nat | (n < N)%nat}) => (proj1_sig k < N)%nat)).
move=> H3.
rewrite H3.
apply (H2 N).
apply (le_n N).
apply Extensionality_Ensembles.
apply conj.
move=> k H3.
apply (proj2_sig k).
move=> k H3.
apply (Full_intro {n : nat | (n < N)%nat} k).
elim.
move=> H2.
suff: ((Im {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (fun (k : {n : nat | (n < N)%nat}) => (proj1_sig k < O)%nat) f) = Empty_set {n : nat | (n < N)%nat}).
move=> H3.
rewrite H3.
apply card_empty.
apply Extensionality_Ensembles.
apply conj.
move=> k.
elim.
move=> x H3.
apply False_ind.
apply (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) H3).
move=> k.
elim.
move=> m H2 H3.
suff: ((Im {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (fun k : {n : nat | (n < N)%nat} => (proj1_sig k < S m)%nat) f) = Add {n : nat | (n < N)%nat} (Im {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (fun k : {n : nat | (n < N)%nat} => (proj1_sig k < m)%nat) f) (f (exist (fun (n : nat) => (n < N)%nat) m H3))).
move=> H4.
rewrite H4.
apply card_add.
apply (H2 (le_trans m (S m) N (le_S m m (le_n m)) H3)).
move=> H5.
suff: (forall (k : {n : nat | (n < N)%nat}), (proj1_sig k < m)%nat -> f k <> f (exist (fun n : nat => (n < N)%nat) m H3)).
elim H5.
move=> x H6 y H7 H8.
apply (H8 x H6).
rewrite H7.
reflexivity.
move=> k H6 H7.
apply (lt_irrefl (proj1_sig k)).
suff: (k = (exist (fun n : nat => (n < N)%nat) m H3)).
move=> H8.
rewrite {2} H8.
apply H6.
apply H1.
apply H7.
apply Extensionality_Ensembles.
apply conj.
move=> k.
elim.
move=> x H4 y H5.
rewrite H5.
elim (le_lt_or_eq (proj1_sig x) m).
move=> H6.
left.
apply (Im_intro {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (fun (k : {n : nat | (n < N)%nat}) => (proj1_sig k < m)%nat) f x H6).
reflexivity.
move=> H6.
right.
suff: (x = (exist (fun n : nat => (n < N)%nat) m H3)).
move=> H7.
rewrite H7.
apply In_singleton.
apply sig_map.
apply H6.
apply le_S_n.
apply H4.
move=> k.
elim.
move=> k0.
elim.
move=> x H4 y H5.
apply (Im_intro {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (fun (k : {n : nat | (n < N)%nat}) => (proj1_sig k < S m)%nat) f x).
apply (le_trans (S (proj1_sig x)) m (S m) H4 (le_S m m (le_n m))).
apply H5.
move=> x.
elim.
apply (Im_intro {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (fun (k : {n : nat | (n < N)%nat}) => (proj1_sig k < S m)%nat) f (exist (fun n : nat => (n < N)%nat) m H3)).
apply (le_n (S m)).
reflexivity.
Qed.

Lemma SkipOneSig : forall (N : nat) (m : {n : nat | n < N}), {f : {n : nat | n < pred N} -> {n : nat | n < N} | forall (k : {n : nat | n < pred N}), (proj1_sig k < proj1_sig m -> proj1_sig (f k) = proj1_sig k) /\ (proj1_sig k >= proj1_sig m -> proj1_sig (f k) = S (proj1_sig k))}.
Proof.
elim.
move=> m.
apply constructive_definite_description.
apply False_ind.
apply (le_not_lt 0 (proj1_sig m) (le_0_n (proj1_sig m)) (proj2_sig m)).
move=> k H1 m.
simpl.
suff: (forall (l : {n : nat | n < k}), proj1_sig l < S k).
move=> H2.
suff: (forall (l : {n : nat | n < k}), S (proj1_sig l) < S k).
move=> H3.
exists (fun (l : {n : nat | n < k}) => match excluded_middle_informative (proj1_sig l < proj1_sig m) with
  | left _ => exist (fun (n : nat) => n < S k) (proj1_sig l) (H2 l)
  | right _ => exist (fun (n : nat) => n < S k) (S (proj1_sig l)) (H3 l)
end).
move=> l.
apply conj.
move=> H4.
elim (excluded_middle_informative (proj1_sig l < proj1_sig m)).
move=> H5.
reflexivity.
move=> H5.
apply False_ind.
apply (H5 H4).
move=> H4.
elim (excluded_middle_informative (proj1_sig l < proj1_sig m)).
move=> H5.
apply False_ind.
apply (le_not_lt (proj1_sig m) (proj1_sig l) H4 H5).
move=> H5.
reflexivity.
move=> l.
apply (lt_n_S (proj1_sig l) k (proj2_sig l)).
move=> l.
apply (le_S (S (proj1_sig l)) k (proj2_sig l)).
Qed.

Definition SkipOne (N : nat) (m : {n : nat | n < N}) := proj1_sig (SkipOneSig N m).

Definition SkipOneNature (N : nat) (m : {n : nat | n < N}) : forall (k : {n : nat | n < pred N}), (proj1_sig k < proj1_sig m -> proj1_sig ((SkipOne N m) k) = proj1_sig k) /\ (proj1_sig k >= proj1_sig m -> proj1_sig ((SkipOne N m) k) = S (proj1_sig k)) := proj2_sig (SkipOneSig N m).

Lemma SkipOneInj : forall (N : nat) (m : {n : nat | n < N}), Injective (SkipOne N m).
Proof.
elim.
move=> m.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) (proj2_sig m)).
move=> N H1 m k1 k2 H2.
elim (le_or_lt (proj1_sig m) (proj1_sig k1)).
move=> H3.
elim (le_or_lt (proj1_sig m) (proj1_sig k2)).
move=> H4.
apply sig_map.
apply (Nat.succ_inj (proj1_sig k1) (proj1_sig k2)).
rewrite - (proj2 (SkipOneNature (S N) m k1) H3).
rewrite - (proj2 (SkipOneNature (S N) m k2) H4).
rewrite H2.
reflexivity.
move=> H4.
apply False_ind.
apply (le_not_lt (proj1_sig (SkipOne (S N) m k1)) (proj1_sig (SkipOne (S N) m k2))).
rewrite H2.
apply (le_n (proj1_sig (SkipOne (S N) m k2))).
rewrite (proj1 (SkipOneNature (S N) m k2) H4).
rewrite (proj2 (SkipOneNature (S N) m k1) H3).
apply (lt_trans (proj1_sig k2) (proj1_sig m) (S (proj1_sig k1)) H4).
apply (le_n_S (proj1_sig m) (proj1_sig k1) H3).
move=> H3.
elim (le_or_lt (proj1_sig m) (proj1_sig k2)).
move=> H4.
apply False_ind.
apply (le_not_lt (proj1_sig (SkipOne (S N) m k2)) (proj1_sig (SkipOne (S N) m k1))).
rewrite H2.
apply (le_n (proj1_sig (SkipOne (S N) m k2))).
rewrite (proj1 (SkipOneNature (S N) m k1) H3).
rewrite (proj2 (SkipOneNature (S N) m k2) H4).
apply (lt_trans (proj1_sig k1) (proj1_sig m) (S (proj1_sig k2)) H3).
apply (le_n_S (proj1_sig m) (proj1_sig k2) H4).
move=> H4.
apply sig_map.
rewrite - (proj1 (SkipOneNature (S N) m k1) H3).
rewrite - (proj1 (SkipOneNature (S N) m k2) H4).
rewrite H2.
reflexivity.
Qed.

Lemma SkipOneMonotonicallyIncreasing : forall (N : nat) (m : {n : nat | n < N}) (k1 k2 : {n : nat | n < pred N}), proj1_sig k1 < proj1_sig k2 -> proj1_sig (SkipOne N m k1) < proj1_sig (SkipOne N m k2).
Proof.
elim.
move=> m.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) (proj2_sig m)).
move=> N H1 m k1 k2 H2.
elim (le_or_lt (proj1_sig m) (proj1_sig k1)).
move=> H3.
rewrite (proj2 (SkipOneNature (S N) m k1) H3).
rewrite (proj2 (SkipOneNature (S N) m k2) (le_trans (proj1_sig m) (proj1_sig k1) (proj1_sig k2) H3 (lt_le_weak (proj1_sig k1) (proj1_sig k2) H2))).
apply (le_n_S (S (proj1_sig k1)) (proj1_sig k2) H2).
move=> H3.
rewrite (proj1 (SkipOneNature (S N) m k1) H3).
elim (le_or_lt (proj1_sig m) (proj1_sig k2)).
move=> H4.
rewrite (proj2 (SkipOneNature (S N) m k2) H4).
apply (le_S (S (proj1_sig k1)) (proj1_sig k2) H2).
move=> H4.
rewrite (proj1 (SkipOneNature (S N) m k2) H4).
apply H2.
Qed.
