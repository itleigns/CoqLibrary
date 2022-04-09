Add LoadPath "Analysis/KaisekiNyuumonn" as Analysis.KaisekiNyuumonn.
Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "Tools" as Tools.
Add LoadPath "BasicProperty" as BasicProperty.
Add LoadPath "LibraryExtension" as LibraryExtension.
Add LoadPath "Topology/ShuugouIsouNyuumonn" as Topology.ShuugouIsouNyuumonn.
Add LoadPath "LibraryExtension" as LibraryExtension.

From mathcomp Require Import ssreflect.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Image.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Mult.
Require Import Coq.Arith.Even.
Require Import Tools.MySum.
Require Import Tools.BasicTools.
Require Import Reals.
Require Export Rdefinitions.
Require Import BasicProperty.MappingProperty.
Require Import LibraryExtension.EnsemblesExtension.
Require Import Topology.ShuugouIsouNyuumonn.ShuugouIsouNyuumonn1.
Require Import LibraryExtension.DatatypesExtension.
Require Import Analysis.KaisekiNyuumonn.KaisekiNyuumonn1_1.
Require Import BasicProperty.NatProperty.
Local Open Scope nat_scope.

Definition SameCard (A B : Type) := exists (f : A -> B), Bijective f.

Lemma SameCardSig : forall (A : Type), SameCard A {a : A | In A (Full_set A) a}.
Proof.
move=> A.
exists (fun (a : A) => exist (Full_set A) a (Full_intro A a)).
exists (fun (a : {a0 : A | In A (Full_set A) a0}) => proj1_sig a).
apply conj.
move=> a.
reflexivity.
move=> a.
apply sig_map.
reflexivity.
Qed.

Lemma Formula_1_1 : forall (A : Type), SameCard A A.
Proof.
move=> A.
exists (fun (a : A) => a).
exists (fun (a : A) => a).
apply conj.
move=> x.
reflexivity.
move=> y.
reflexivity.
Qed.

Lemma Formula_1_2 : forall (A B : Type), SameCard A B -> SameCard B A.
Proof.
move=> A B.
elim.
move=> f.
elim.
move=> g H1.
exists g.
exists f.
apply conj.
apply (proj2 H1).
apply (proj1 H1).
Qed.

Lemma Formula_1_3 : forall (A B C : Type), SameCard A B -> SameCard B C -> SameCard A C.
Proof.
move=> A B C H1 H2.
elim H1.
move=> f H3.
elim H2.
move=> g H4.
exists (Basics.compose g f).
apply (BijChain A B C f g H3 H4).
Qed.

Lemma Formula_61 : forall (T1 : Type), ~ Inhabited T1 (Full_set T1) -> forall (T2 : Type), (~ Inhabited T2 (Full_set T2) <-> SameCard T1 T2).
Proof.
move=> T1 H1 T2.
apply conj.
move=> H2.
exists (fun (t : T1) => match H1 (Inhabited_intro T1 (Full_set T1) t (Full_intro T1 t)) with
end).
exists (fun (t : T2) => match H2 (Inhabited_intro T2 (Full_set T2) t (Full_intro T2 t)) with
end).
apply conj.
move=> t.
elim (H1 (Inhabited_intro T1 (Full_set T1) t (Full_intro T1 t))).
move=> t.
elim (H2 (Inhabited_intro T2 (Full_set T2) t (Full_intro T2 t))).
elim.
move=> f.
elim.
move=> g H2 H3.
apply H1.
elim H3.
move=> t H4.
apply (Inhabited_intro T1 (Full_set T1) (g t) (Full_intro T1 (g t))).
Qed.

Lemma Example_1_1 : forall (A : Type) (n : nat), cardinal A (Full_set A) n -> forall (B : Type), SameCard A B <-> cardinal B (Full_set B) n.
Proof.
move=> A n H1 B.
apply conj.
move=> H2.
apply (proj1 (CountCardinalBijective B n)).
elim (proj2 (CountCardinalBijective A n) H1).
move=> g H3.
elim H2.
move=> f H4.
exists (Basics.compose f g).
apply (BijChain (Count n) A B g f H3 H4).
move=> H2.
elim (proj2 (CountCardinalBijective A n) H1).
move=> f H3.
elim (proj2 (CountCardinalBijective B n) H2).
move=> g H4.
elim H3.
move=> fi H5.
exists (Basics.compose g fi).
apply (BijChain A (Count n) B fi g).
exists f.
apply conj.
apply (proj2 H5).
apply (proj1 H5).
apply H4.
Qed.

Lemma Example_1_2_set : forall (T : Type) (A : Ensemble T) (n : nat), cardinal T A n -> forall (B : Ensemble T), Strict_Included T B A -> ~ SameCard {t : T | In T A t} {t : T | In T B t}.
Proof.
move=> T A n H1 B H2 H3.
apply (lt_irrefl n).
suff: (exists (t : T), ~ In T B t /\ In T A t).
elim.
move=> t H4.
apply (incl_card_le T (Add T B t) A (S n) n).
apply (card_add T B n).
apply (proj2 (CardinalSigSame T B n)).
apply (proj1 (Example_1_1 {t : T | In T A t} n (proj1 (CardinalSigSame T A n) H1) {t : T | In T B t}) H3).
apply (proj1 H4).
apply H1.
move=> t0.
elim.
apply (proj1 H2).
move=> t1.
elim.
apply (proj2 H4).
apply NNPP.
move=> H4.
apply (proj2 H2).
apply Extensionality_Ensembles.
apply conj.
apply (proj1 H2).
move=> t H5.
apply NNPP.
move=> H6.
apply H4.
exists t.
apply conj.
apply H6.
apply H5.
Qed.

Lemma Example_1_2 : forall (T : Type) (n : nat), cardinal T (Full_set T) n -> forall (A : Ensemble T), Strict_Included T A (Full_set T) -> ~ SameCard T {t : T | In T A t}.
Proof.
move=> T n H1 A H2 H3.
apply (Example_1_2_set T (Full_set T) n H1 A H2).
apply (Formula_1_3 {t : T | In T (Full_set T) t} T {t : T | In T A t} (Formula_1_2 T {t : T | In T (Full_set T) t} (SameCardSig T)) H3).
Qed.

Lemma Example_2 : SameCard nat {n : nat | In nat even n}.
Proof.
suff: (forall (n : nat), even (n + n)).
move=> H1.
exists (fun (n : nat) => exist even (n + n) (H1 n)).
apply InjSurjBij.
move=> n1 n2 H2.
elim (le_or_lt n1 n2).
move=> H3.
elim (le_lt_or_eq n1 n2 H3).
move=> H4.
elim (lt_irrefl (n1 + n1)).
suff: (n1 + n1 = proj1_sig (exist even (n1 + n1) (H1 n1))).
move=> H5.
rewrite {2} H5.
rewrite H2.
simpl.
apply (plus_lt_compat n1 n2 n1 n2 H4 H4).
reflexivity.
apply.
move=> H3.
elim (lt_irrefl (n1 + n1)).
suff: (n1 + n1 = proj1_sig (exist even (n1 + n1) (H1 n1))).
move=> H4.
rewrite {1} H4.
rewrite H2.
simpl.
apply (plus_lt_compat n2 n1 n2 n1 H3 H3).
reflexivity.
move=> n.
suff: (forall (m k : nat), even m -> m = S (S k) -> even k).
move=> H2.
suff: (forall (m : nat), (even m -> exists (k : nat), m = k + k) /\ (even (S m) -> exists (k : nat), S m = k + k)).
move=> H3.
elim (proj1 (H3 (proj1_sig n)) (proj2_sig n)).
move=> m H4.
exists m.
apply sig_map.
rewrite H4.
reflexivity.
elim.
apply conj.
move=> H3.
exists O.
reflexivity.
suff: (forall (m : nat), even m -> m = 1 -> False).
move=> H3 H4.
elim (H3 1 H4).
reflexivity.
move=> m.
elim.
move=> H3.
suff: (let t := O in match t with
  | O => True
  | S _ => False
end).
rewrite H3.
elim.
apply I.
move=> k.
elim.
move=> l H3 H4.
suff: (let t := S (S l) in match t with
  | O => True
  | S p => match p with
    | O => False
    | S _ => True
  end
end).
rewrite H4.
apply.
apply I.
move=> m H3.
apply conj.
apply (proj2 H3).
move=> H4.
elim (proj1 H3).
move=> k H5.
rewrite H5.
exists (S k).
simpl.
rewrite (plus_comm k (S k)).
reflexivity.
apply (H2 (S (S m)) m H4).
reflexivity.
move=> m k.
elim.
move=> H2.
suff: (let t := O in match t with
  | O => True
  | S _ => False
end).
rewrite H2.
elim.
apply I.
move=> l.
elim.
move=> p H2 H3.
suff: (pred (pred (S (S k))) = k).
move=> H4.
rewrite - H4.
rewrite - H3.
apply H2.
reflexivity.
elim.
apply even_O.
move=> n H1.
simpl.
rewrite (plus_comm n (S n)).
apply (even_S (S n + n) (odd_S (n + n) H1)).
Qed.

Lemma Example_3 : SameCard nat (nat * nat).
Proof.
apply (Formula_1_2 (nat * nat) nat).
exists (fun (m : nat * nat) => pred (2 ^ (fst m) * (2 * (snd m) + 1))).
suff: (forall (n : nat), 2 * n = n + n).
move=> H1.
suff: (forall (m : nat), exists ! (n : nat), exists (k : nat), S m = 2 ^ n * (2 * k + 1)).
move=> H2.
suff: (forall (n k : nat), 2 ^ n * (2 * k + 1) <> O).
move=> H3.
suff: (0 < 2).
move=> H4.
apply InjSurjBij.
move=> m1 m2 H5.
suff: (fst m1 = fst m2).
move=> H6.
apply injective_projections.
apply H6.
suff: (forall (n k : nat), 2 ^ n * (2 * k + 1) = S (pred (2 ^ n * (2 * k + 1)))).
move=> H7.
elim (le_or_lt (snd m1) (snd m2)).
move=> H8.
elim (le_lt_or_eq (snd m1) (snd m2) H8).
move=> H9.
elim (lt_irrefl (2 ^ fst m1 * (2 * snd m1 + 1))).
rewrite {2} (H7 (fst m1) (snd m1)).
rewrite H5.
rewrite - (H7 (fst m2) (snd m2)).
rewrite H6.
apply (mult_lt_compat_l (2 * snd m1 + 1) (2 * snd m2 + 1) (2 ^ fst m2)).
apply (plus_lt_compat_r (2 * snd m1) (2 * snd m2) 1).
apply (mult_lt_compat_l (snd m1) (snd m2) 2 H9 H4).
elim (fst m2).
apply (le_n 1).
move=> n H10.
rewrite - {1} (mult_0_r 2).
apply (mult_lt_compat_l 0 (2 ^ n) 2 H10 H4).
apply.
move=> H8.
elim (lt_irrefl (2 ^ fst m1 * (2 * snd m1 + 1))).
rewrite {1} (H7 (fst m1) (snd m1)).
rewrite H5.
rewrite - (H7 (fst m2) (snd m2)).
rewrite H6.
apply (mult_lt_compat_l (2 * snd m2 + 1) (2 * snd m1 + 1) (2 ^ fst m2)).
apply (plus_lt_compat_r (2 * snd m2) (2 * snd m1) 1).
apply (mult_lt_compat_l (snd m2) (snd m1) 2 H8 H4).
elim (fst m2).
apply (le_n 1).
move=> n H9.
rewrite - {1} (mult_0_r 2).
apply (mult_lt_compat_l 0 (2 ^ n) 2 H9 H4).
move=> n k.
suff: (2 ^ n * (2 * k + 1) <> O).
elim (2 ^ n * (2 * k + 1)).
elim.
reflexivity.
move=> l H7 H8.
reflexivity.
apply (H3 n k).
apply (proj2 (proj2 (unique_existence (fun (n : nat) => exists (k : nat), S (pred (2 ^ fst m1 * (2 * snd m1 + 1))) = 2 ^ n * (2 * k + 1))) (H2 (pred (2 ^ fst m1 * (2 * snd m1 + 1)))))).
exists (snd m1).
suff: (2 ^ fst m1 * (2 * snd m1 + 1) <> O).
elim (2 ^ fst m1 * (2 * snd m1 + 1)).
elim.
reflexivity.
move=> n H6 H7.
reflexivity.
apply (H3 (fst m1) (snd m1)).
rewrite H5.
exists (snd m2).
suff: (2 ^ fst m2 * (2 * snd m2 + 1) <> O).
elim (2 ^ fst m2 * (2 * snd m2 + 1)).
elim.
reflexivity.
move=> n H8 H7.
reflexivity.
apply (H3 (fst m2) (snd m2)).
move=> m.
elim (proj1 (proj2 (unique_existence (fun (n : nat) => exists (k : nat), S m = 2 ^ n * (2 * k + 1))) (H2 m))).
move=> n.
elim.
move=> k H5.
exists (n, k).
simpl.
rewrite - H5.
reflexivity.
apply (plus_lt_compat 0 1 0 1 (le_n 1) (le_n 1)).
move=> n k.
rewrite - {4} (mult_0_l (2 * k + 1)).
move=> H3.
elim (lt_irrefl (2 ^ n * (2 * k + 1))).
rewrite {1} H3.
apply (mult_lt_compat_r 0 (2 ^ n) (2 * k + 1)).
elim n.
apply (le_n 1).
move=> m H4.
rewrite - {1} (mult_0_r 2).
apply (mult_lt_compat_l 0 (2 ^ m) 2 H4).
apply (plus_lt_compat 0 1 0 1 (le_n 1) (le_n 1)).
apply (plus_le_compat_r O (2 * k) 1 (le_0_n (2 * k))).
suff: (forall (n : nat), (exists (m : nat), 2 * m + 1 = n) \/ (exists (m : nat), 2 * m = n)).
move=> H2.
suff: (forall (m : nat) (l : nat), l < m -> exists ! (n : nat), exists (k : nat), S l = 2 ^ n * (2 * k + 1)).
move=> H3 m.
apply (H3 (S m) m (le_n (S m))).
elim.
move=> l H3.
elim (le_not_lt O l (le_0_n l) H3).
move=> n H3 l H4.
elim (le_lt_or_eq l n (le_S_n l n H4)).
move=> H5.
apply (H3 l H5).
move=> H5.
elim (H2 l).
elim.
move=> k H6.
elim (H3 k).
move=> m H7.
exists (S m).
apply conj.
elim (proj1 H7).
move=> p H8.
rewrite - H6.
exists p.
suff: (S (2 * k + 1) = 2 * (S k)).
move=> H9.
rewrite H9.
rewrite H8.
apply (mult_assoc 2 (2 ^ m) (2 * p + 1)).
suff: (S (S (2 * k)) = 2 * (S k)).
rewrite (plus_comm (2 * k) 1).
apply.
elim k.
reflexivity.
move=> q H9.
simpl.
rewrite (plus_comm q (S (q + 0))).
rewrite (plus_comm q (S (S (q + 0)))).
reflexivity.
move=> y H8.
suff: (exists (p : nat), y = S p).
elim.
move=> p H9.
rewrite H9.
apply (f_equal (fun (x : nat) => S x)).
apply (proj2 H7 p).
elim H8.
move=> q H10.
exists q.
suff: (2 * (S k) = 2 * (2 ^ p * (2 * q + 1))).
move=> H11.
suff: (2 > 0).
move=> H12.
elim (le_or_lt (S k) (2 ^ p * (2 * q + 1))).
move=> H13.
elim (le_lt_or_eq (S k) (2 ^ p * (2 * q + 1)) H13).
move=> H14.
elim (le_not_lt (2 * (2 ^ p * (2 * q + 1))) (2 * (S k))).
rewrite H11.
apply (le_n (2 * (2 ^ p * (2 * q + 1)))).
apply (mult_lt_compat_l (S k) (2 ^ p * (2 * q + 1)) 2 H14 H12).
apply.
move=> H13.
elim (le_not_lt (2 * (S k)) (2 * (2 ^ p * (2 * q + 1)))).
rewrite H11.
apply (le_n (2 * (2 ^ p * (2 * q + 1)))).
apply (mult_lt_compat_l (2 ^ p * (2 * q + 1)) (S k) 2 H13 H12).
apply (le_S 1 1 (le_n 1)).
suff: (2 * S k = S l).
move=> H11.
rewrite H11.
rewrite H10.
rewrite H9.
rewrite (mult_assoc 2 (2 ^ p) (2 * q + 1)).
reflexivity.
rewrite - H6.
rewrite (plus_comm (2 * k) 1).
simpl.
rewrite (plus_comm k (S (k + 0))).
rewrite (plus_comm k 0).
reflexivity.
suff: (y <> O).
elim y.
elim.
reflexivity.
move=> p H9 H10.
exists p.
reflexivity.
move=> H9.
elim H8.
move=> p H10.
elim (le_or_lt p k).
move=> H11.
elim (lt_irrefl (S l)).
rewrite {1} H10.
rewrite - H6.
rewrite H9.
simpl.
rewrite (plus_comm (2 * p + 1) O).
apply (le_n_S (2 * p + 1) (2 * k + 1)).
apply (plus_le_compat_r (2 * p) (2 * k) 1 (mult_le_compat_l p k 2 H11)).
move=> H11.
elim (lt_irrefl (S l)).
rewrite {2} H10.
rewrite - H6.
rewrite H9.
simpl.
rewrite (plus_comm k 0).
rewrite (plus_comm p 0).
rewrite (plus_comm (p + (0 + p) + 1) 0).
simpl.
unfold lt.
suff: (S (S (k + k + 1)) = S k + S k + 1).
move=> H12.
rewrite H12.
apply (plus_le_compat_r (S k + S k) (p + p) 1 (plus_le_compat (S k) p (S k) p H11 H11)).
rewrite (plus_comm (k + k) 1).
rewrite (plus_comm (S k + S k) 1).
simpl.
rewrite (plus_comm k (S k)).
reflexivity.
rewrite - H5.
rewrite - H6.
rewrite (plus_comm (2 * k) 1).
rewrite (H1 k).
apply (le_n_S k (k + k) (plus_le_compat_r 0 k k (le_0_n k))).
elim.
move=> m H6.
exists O.
apply conj.
exists m.
rewrite - H6.
simpl.
rewrite (plus_comm (2 * m + 1) 0).
apply (plus_comm 1 (2 * m)).
move=> p.
elim.
move=> k H7.
suff: (forall (q : nat), S l <> q + q).
move=> H8.
apply NNPP.
move=> H9.
suff: (exists (r : nat), p = S r).
elim.
move=> r H10.
apply (H8 (2 ^ r * (2 * k + 1))).
rewrite H7.
rewrite H10.
rewrite - (mult_assoc 2 (2 ^ r) (2 * k + 1)).
apply (H1 (2 ^ r * (2 * k + 1))).
suff: (0 <> p).
elim p.
elim.
reflexivity.
move=> q H10 H11.
exists q.
reflexivity.
apply H9.
move=> q.
rewrite - H6.
rewrite (H1 m).
move=> H8.
elim (le_or_lt q m).
move=> H9.
elim (lt_irrefl (m + m)).
unfold lt.
rewrite H8.
apply (plus_le_compat q m q m H9 H9).
move=> H9.
elim (lt_irrefl (q + q)).
rewrite - {1} H8.
unfold lt.
suff: (S (m + m) = m + S m).
move=> H10.
rewrite H10.
apply (plus_le_compat (S m) q (S m) q H9 H9).
apply (plus_comm (S m) m).
elim.
right.
exists O.
apply (mult_0_r 2).
move=> n.
elim.
elim.
move=> m H2.
right.
exists (S m).
rewrite - H2.
simpl.
rewrite (plus_comm m 0).
rewrite - (plus_assoc m (0 + m) 1).
rewrite (plus_comm (0 + m) 1).
reflexivity.
elim.
move=> m H2.
left.
exists m.
rewrite - H2.
apply (plus_comm (2 * m) 1).
move=> n.
simpl.
rewrite (plus_comm n 0).
reflexivity.
Qed.

Lemma Example_4_1 : forall (a b c d : R), (a < b)%R -> (c < d)%R -> SameCard {x : R | (a <= x <= b)%R} {x : R | (c <= x <= d)%R}.
Proof.
move=> a b c d H1 H2.
suff: (d - c > 0)%R.
move=> H3.
suff: (b - a > 0)%R.
move=> H4.
suff: (forall (r : {x : R | (a <= x <= b)%R}), c <= (d - c) / (b - a) * (proj1_sig r - a) + c <= d)%R.
move=> H5.
exists (fun (r : {x : R | (a <= x <= b)%R}) => exist (fun (x : R) => c <= x <= d) ((d - c) / (b - a) * (proj1_sig r - a) + c) (H5 r))%R.
suff: (forall (r : {x : R | (c <= x <= d)%R}), a <= (b - a) / (d - c) * (proj1_sig r - c) + a <= b)%R.
move=> H6.
exists (fun (r : {x : R | (c <= x <= d)%R}) => exist (fun (x : R) => a <= x <= b) ((b - a) / (d - c) * (proj1_sig r - c) + a) (H6 r))%R.
apply conj.
move=> r.
apply sig_map.
simpl.
unfold Rminus.
rewrite Rplus_assoc.
rewrite (Rplus_opp_r c).
rewrite Rplus_0_r.
rewrite - Rmult_assoc.
unfold Rdiv.
rewrite (Rmult_assoc (b + - a) (/ (d + - c)) ((d + - c) * / (b + - a))).
rewrite - (Rmult_assoc (/ (d + - c)) (d + - c) (/ (b + - a))).
rewrite (Rinv_l (d + - c)).
rewrite (Rmult_1_l (/ (b + - a))).
rewrite (Rinv_r (b + - a)).
rewrite (Rmult_1_l (proj1_sig r + - a)).
rewrite (Rplus_assoc (proj1_sig r) (- a) a).
rewrite (Rplus_opp_l a).
apply (Rplus_0_r (proj1_sig r)).
apply (Rgt_not_eq (b - a) 0 H4).
apply (Rgt_not_eq (d - c) 0 H3).
move=> r.
apply sig_map.
simpl.
unfold Rminus.
rewrite Rplus_assoc.
rewrite (Rplus_opp_r a).
rewrite Rplus_0_r.
rewrite - Rmult_assoc.
unfold Rdiv.
rewrite (Rmult_assoc (d + - c) (/ (b + - a)) ((b + - a) * / (d + - c))).
rewrite - (Rmult_assoc (/ (b + - a)) (b + - a) (/ (d + - c))).
rewrite (Rinv_l (b + - a)).
rewrite (Rmult_1_l (/ (d + - c))).
rewrite (Rinv_r (d + - c)).
rewrite (Rmult_1_l (proj1_sig r + - c)).
rewrite (Rplus_assoc (proj1_sig r) (- c) c).
rewrite (Rplus_opp_l c).
apply (Rplus_0_r (proj1_sig r)).
apply (Rgt_not_eq (d - c) 0 H3).
apply (Rgt_not_eq (b - a) 0 H4).
move=> r.
apply conj.
rewrite - {1} (Rplus_0_l a).
apply (Rplus_le_compat_r a 0 ((b - a) / (d - c) * (proj1_sig r - c))).
rewrite - {1} (Rmult_0_l 0).
apply (Rmult_le_compat 0 ((b - a) / (d - c)) 0 (proj1_sig r - c)).
right.
reflexivity.
right.
reflexivity.
left.
apply (Rmult_gt_0_compat (b - a) (/ (d - c)) H4 (Rinv_0_lt_compat (d - c) H3)).
rewrite - (Rplus_opp_r c).
apply (Rplus_le_compat_r (- c) c (proj1_sig r) (proj1 (proj2_sig r))).
apply (Rplus_le_reg_r (- a)).
rewrite Rplus_assoc.
rewrite (Rplus_opp_r a).
rewrite Rplus_0_r.
rewrite - (Rmult_1_r (b + - a)).
unfold Rdiv.
rewrite Rmult_assoc.
apply (Rmult_le_compat_l (b - a)).
left.
apply H4.
rewrite - (Rinv_l (d - c)).
apply (Rmult_le_compat_l (/ (d - c))).
left.
apply (Rinv_0_lt_compat (d - c) H3).
apply (Rplus_le_compat_r (- c) (proj1_sig r) d (proj2 (proj2_sig r))).
apply (Rgt_not_eq (d - c) 0 H3).
move=> r.
apply conj.
rewrite - {1} (Rplus_0_l c).
apply (Rplus_le_compat_r c 0 ((d - c) / (b - a) * (proj1_sig r - a))).
rewrite - {1} (Rmult_0_l 0).
apply (Rmult_le_compat 0 ((d - c) / (b - a)) 0 (proj1_sig r - a)).
right.
reflexivity.
right.
reflexivity.
left.
apply (Rmult_gt_0_compat (d - c) (/ (b - a)) H3 (Rinv_0_lt_compat (b - a) H4)).
rewrite - (Rplus_opp_r a).
apply (Rplus_le_compat_r (- a) a (proj1_sig r) (proj1 (proj2_sig r))).
apply (Rplus_le_reg_r (- c)).
rewrite Rplus_assoc.
rewrite (Rplus_opp_r c).
rewrite Rplus_0_r.
rewrite - (Rmult_1_r (d + - c)).
unfold Rdiv.
rewrite Rmult_assoc.
apply (Rmult_le_compat_l (d - c)).
left.
apply H3.
rewrite - (Rinv_l (b - a)).
apply (Rmult_le_compat_l (/ (b - a))).
left.
apply (Rinv_0_lt_compat (b - a) H4).
apply (Rplus_le_compat_r (- a) (proj1_sig r) b (proj2 (proj2_sig r))).
apply (Rgt_not_eq (b - a) 0 H4).
apply (Rgt_minus b a H1).
apply (Rgt_minus d c H2).
Qed.

Lemma Example_4_2 : forall (a b c d : R), (a < b)%R -> (c < d)%R -> SameCard {x : R | (a < x < b)%R} {x : R | (c < x < d)%R}.
Proof.
move=> a b c d H1 H2.
suff: (d - c > 0)%R.
move=> H3.
suff: (b - a > 0)%R.
move=> H4.
suff: (forall (r : {x : R | (a < x < b)%R}), c < (d - c) / (b - a) * (proj1_sig r - a) + c < d)%R.
move=> H5.
exists (fun (r : {x : R | (a < x < b)%R}) => exist (fun (x : R) => c < x < d) ((d - c) / (b - a) * (proj1_sig r - a) + c) (H5 r))%R.
suff: (forall (r : {x : R | (c < x < d)%R}), a < (b - a) / (d - c) * (proj1_sig r - c) + a < b)%R.
move=> H6.
exists (fun (r : {x : R | (c < x < d)%R}) => exist (fun (x : R) => a < x < b) ((b - a) / (d - c) * (proj1_sig r - c) + a) (H6 r))%R.
apply conj.
move=> r.
apply sig_map.
simpl.
unfold Rminus.
rewrite Rplus_assoc.
rewrite (Rplus_opp_r c).
rewrite Rplus_0_r.
rewrite - Rmult_assoc.
unfold Rdiv.
rewrite (Rmult_assoc (b + - a) (/ (d + - c)) ((d + - c) * / (b + - a))).
rewrite - (Rmult_assoc (/ (d + - c)) (d + - c) (/ (b + - a))).
rewrite (Rinv_l (d + - c)).
rewrite (Rmult_1_l (/ (b + - a))).
rewrite (Rinv_r (b + - a)).
rewrite (Rmult_1_l (proj1_sig r + - a)).
rewrite (Rplus_assoc (proj1_sig r) (- a) a).
rewrite (Rplus_opp_l a).
apply (Rplus_0_r (proj1_sig r)).
apply (Rgt_not_eq (b - a) 0 H4).
apply (Rgt_not_eq (d - c) 0 H3).
move=> r.
apply sig_map.
simpl.
unfold Rminus.
rewrite Rplus_assoc.
rewrite (Rplus_opp_r a).
rewrite Rplus_0_r.
rewrite - Rmult_assoc.
unfold Rdiv.
rewrite (Rmult_assoc (d + - c) (/ (b + - a)) ((b + - a) * / (d + - c))).
rewrite - (Rmult_assoc (/ (b + - a)) (b + - a) (/ (d + - c))).
rewrite (Rinv_l (b + - a)).
rewrite (Rmult_1_l (/ (d + - c))).
rewrite (Rinv_r (d + - c)).
rewrite (Rmult_1_l (proj1_sig r + - c)).
rewrite (Rplus_assoc (proj1_sig r) (- c) c).
rewrite (Rplus_opp_l c).
apply (Rplus_0_r (proj1_sig r)).
apply (Rgt_not_eq (d - c) 0 H3).
apply (Rgt_not_eq (b - a) 0 H4).
move=> r.
apply conj.
rewrite - {1} (Rplus_0_l a).
apply (Rplus_lt_compat_r a 0 ((b - a) / (d - c) * (proj1_sig r - c))).
apply (Rmult_lt_0_compat ((b - a) / (d - c)) (proj1_sig r - c)).
apply (Rmult_gt_0_compat (b - a) (/ (d - c)) H4 (Rinv_0_lt_compat (d - c) H3)).
rewrite - (Rplus_opp_r c).
apply (Rplus_lt_compat_r (- c) c (proj1_sig r) (proj1 (proj2_sig r))).
apply (Rplus_lt_reg_r (- a)).
rewrite Rplus_assoc.
rewrite (Rplus_opp_r a).
rewrite Rplus_0_r.
rewrite - (Rmult_1_r (b + - a)).
unfold Rdiv.
rewrite Rmult_assoc.
apply (Rmult_lt_compat_l (b - a)).
apply H4.
rewrite - (Rinv_l (d - c)).
apply (Rmult_lt_compat_l (/ (d - c))).
apply (Rinv_0_lt_compat (d - c) H3).
apply (Rplus_lt_compat_r (- c) (proj1_sig r) d (proj2 (proj2_sig r))).
apply (Rgt_not_eq (d - c) 0 H3).
move=> r.
apply conj.
rewrite - {1} (Rplus_0_l c).
apply (Rplus_lt_compat_r c 0 ((d - c) / (b - a) * (proj1_sig r - a))).
apply (Rmult_lt_0_compat ((d - c) / (b - a)) (proj1_sig r - a)).
apply (Rmult_gt_0_compat (d - c) (/ (b - a)) H3 (Rinv_0_lt_compat (b - a) H4)).
rewrite - (Rplus_opp_r a).
apply (Rplus_lt_compat_r (- a) a (proj1_sig r) (proj1 (proj2_sig r))).
apply (Rplus_lt_reg_r (- c)).
rewrite Rplus_assoc.
rewrite (Rplus_opp_r c).
rewrite Rplus_0_r.
rewrite - (Rmult_1_r (d + - c)).
unfold Rdiv.
rewrite Rmult_assoc.
apply (Rmult_lt_compat_l (d - c)).
apply H3.
rewrite - (Rinv_l (b - a)).
apply (Rmult_lt_compat_l (/ (b - a))).
apply (Rinv_0_lt_compat (b - a) H4).
apply (Rplus_lt_compat_r (- a) (proj1_sig r) b (proj2 (proj2_sig r))).
apply (Rgt_not_eq (b - a) 0 H4).
apply (Rgt_minus b a H1).
apply (Rgt_minus d c H2).
Qed.

Lemma Example_5 : forall (a b : R), (a < b)%R -> SameCard {x : R | (a < x < b)%R} R.
Proof.
suff: (SameCard R {x : R | (-1 < x < 1)%R}).
move=> H1 a b H2.
apply (Formula_1_3 {x : R | (a < x < b)%R} {x : R | (- 1 < x < 1)%R} R).
apply (Example_4_2 a b (- 1) 1 H2).
apply (Rplus_lt_reg_l 1 (- 1) 1).
rewrite (Rplus_opp_r 1).
apply (Rlt_trans 0 1 (1 + 1) Rlt_0_1 (Rlt_plus_1 1)).
apply (Formula_1_2 R {x : R | (-1 < x < 1)%R}).
apply H1.
suff: (exists (f : R -> R), (forall (x : R), - (1) < f x < 1) /\ (forall (x y : R), (x < y) -> (f x < f y)) /\ (forall (x : R), - (1) < x < 1 -> exists (y : R), f y = x))%R.
elim.
move=> f H1.
exists (fun (r : R) => exist (fun (x : R) => (- (1) < x < 1)%R) (f r) (proj1 H1 r)).
apply InjSurjBij.
move=> x y H2.
elim (Rle_or_lt x y).
elim.
move=> H3.
elim (Rlt_irrefl (proj1_sig (exist (fun (x : R) => (- (1) < x < 1)%R) (f x) (proj1 H1 x)))).
rewrite {2} H2.
apply (proj1 (proj2 H1) x y H3).
apply.
move=> H3.
elim (Rlt_irrefl (proj1_sig (exist (fun (x : R) => (- (1) < x < 1)%R) (f x) (proj1 H1 x)))).
rewrite {1} H2.
apply (proj1 (proj2 H1) y x H3).
move=> y.
elim (proj2 (proj2 H1) (proj1_sig y) (proj2_sig y)).
move=> x H2.
exists x.
apply sig_map.
apply H2.
exists (fun (r : R) => match (Rlt_le_dec 0 r) with
  | left _ => 1 - / (r + 1)
  | right _ => - (1) - / (r - 1)
end)%R.
apply conj.
move=> x.
elim (Rlt_le_dec 0 x).
move=> H1.
apply conj.
suff: (/ (x + 1) < 1)%R.
move=> H2.
apply (Rlt_trans (- (1)) (- (/ (x + 1))) (1 - / (x + 1))).
apply (Ropp_lt_contravar 1 (/ (x + 1)) H2).
rewrite - {1} (Rplus_0_l (- (/ (x + 1)))).
apply (Rplus_lt_compat_r (- (/ (x + 1))) 0 1 Rlt_0_1).
rewrite - {2} Rinv_1.
apply (Rinv_1_lt_contravar 1 (x + 1)).
apply (Req_le 1 1).
reflexivity.
rewrite - {1} (Rplus_0_l 1).
apply (Rplus_lt_compat_r 1 0 x H1).
rewrite - {3} (Rplus_0_r 1).
apply (Rplus_lt_compat_l 1 (- / (x + 1)) 0).
apply (Ropp_lt_gt_0_contravar (/ (x + 1))).
apply (Rinv_0_lt_compat (x + 1)).
apply (Rlt_trans 0 x (x + 1) H1).
rewrite - {1} (Rplus_0_r x).
apply (Rplus_lt_compat_l x 0 1 Rlt_0_1).
move=> H1.
apply conj.
rewrite - {1} (Rplus_0_r (- (1))).
apply (Rplus_lt_compat_l (- (1)) 0 (- / (x - 1))).
apply (Ropp_0_gt_lt_contravar (/ (x - 1))).
apply (Rinv_lt_0_compat (x - 1)).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
apply (Rplus_lt_compat_l x (- (1)) 0).
apply (Ropp_0_lt_gt_contravar 1 Rlt_0_1).
apply H1.
suff: (/ (x - 1) >= - (1))%R.
move=> H2.
apply (Rle_lt_trans (- (1) - / (x - 1)) 0 1).
rewrite - (Rplus_opp_l 1).
apply (Rplus_le_compat_l (- (1)) (- / (x - 1)) 1).
rewrite - {2} (Ropp_involutive 1).
apply (Ropp_ge_le_contravar (/ (x - 1)) (- (1)) H2).
apply Rlt_0_1.
rewrite - (Rmult_1_r (/ (x - 1))).
rewrite - {3} (Rinv_l (x - 1)).
rewrite (Ropp_mult_distr_r (/ (x - 1)) (x - 1)).
apply (Rmult_le_ge_compat_neg_l (/ (x - 1)) 1 (- (x - 1))).
apply (Rlt_le (/ (x - 1)) 0).
apply (Rinv_lt_0_compat (x - 1)).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
apply (Rplus_lt_compat_l x (- (1)) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply H1.
rewrite - {1} (Ropp_involutive 1).
apply (Ropp_le_contravar (- (1)) (x - 1)).
rewrite - (Rplus_0_l (- (1))).
apply (Rplus_le_compat_r (- (1)) x 0 H1).
apply (Rlt_not_eq (x - 1) 0).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
apply (Rplus_lt_compat_l x (- (1)) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply H1.
apply conj.
move=> x y H1.
elim (Rlt_le_dec 0 x).
move=> H2.
elim (Rlt_le_dec 0 y).
move=> H3.
apply (Rplus_lt_compat_l 1 (- / (x + 1)) (- / (y + 1))).
apply (Ropp_lt_contravar (/ (x + 1)) (/ (y + 1))).
apply (Rinv_1_lt_contravar (x + 1) (y + 1)).
rewrite - {1} (Rplus_0_l 1).
apply (Rplus_le_compat_r 1 0 x).
apply (Rlt_le 0 x H2).
apply (Rplus_lt_compat_r 1 x y H1).
move=> H3.
apply False_ind.
apply (Rle_not_lt y x).
apply (Rlt_le x y H1).
apply (Rle_lt_trans y 0 x H3 H2).
move=> H2.
elim (Rlt_le_dec 0 y).
move=> H3.
apply (Rle_lt_trans (- (1) - / (x - 1)) 0 (1 - / (y + 1))).
rewrite - (Rplus_opp_l 1).
apply (Rplus_le_compat_l (- (1)) (- / (x - 1)) 1).
rewrite - (Rmult_1_r (/ (x - 1))).
rewrite (Ropp_mult_distr_r (/ (x - 1)) 1).
rewrite - {3} (Rinv_l (x - 1)).
apply (Rmult_le_compat_neg_l (/ (x - 1)) (x - 1) (- (1))).
apply (Rlt_le (/ (x - 1)) 0).
apply (Rinv_lt_0_compat (x - 1)).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
apply (Rplus_lt_compat_l x (- (1)) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply H2.
rewrite - (Rplus_0_l (- (1))).
apply (Rplus_le_compat_r (- (1)) x 0 H2).
apply (Rlt_not_eq (x - 1) 0).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
apply (Rplus_lt_compat_l x (- (1)) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply H2.
rewrite - (Rplus_opp_r 1).
apply (Rplus_lt_compat_l 1 (- (1)) (- / (y + 1))).
apply (Ropp_lt_contravar 1 (/ (y + 1))).
rewrite - {2} Rinv_1.
apply (Rinv_1_lt_contravar 1 (y + 1)).
apply (Rle_refl 1).
rewrite - {1} (Rplus_0_l 1).
apply (Rplus_lt_compat_r 1 0 y H3).
move=> H3.
apply (Rplus_lt_compat_l (- (1)) (- / (x - 1)) (- / (y - 1))).
apply (Ropp_lt_contravar (/ (x - 1)) (/ (y - 1))).
apply (Rinv_lt_contravar (x - 1) (y - 1)).
rewrite - (Rmult_opp_opp (x - 1) (y - 1)).
apply (Rmult_lt_0_compat (- (x - 1)) (- (y - 1))).
apply (Ropp_0_gt_lt_contravar (x - 1)).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
apply (Rplus_lt_compat_l x (- (1)) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply H2.
apply (Ropp_0_gt_lt_contravar (y - 1)).
apply (Rlt_le_trans (y - 1) y 0).
rewrite - {2} (Rplus_0_r y).
apply (Rplus_lt_compat_l y (- (1)) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply H3.
apply (Rplus_lt_compat_r (- (1)) x y H1).
move=> x H1.
elim (Rtotal_order 0 x).
move=> H2.
exists (/ - (x - 1) - 1)%R.
elim (Rlt_le_dec 0 (/ - (x - 1) - 1)).
move=> H3.
rewrite (Rplus_assoc (/ - (x - 1)) (- (1)) 1).
rewrite (Rplus_opp_l 1).
rewrite (Rplus_0_r (/ - (x - 1))).
rewrite (Rinv_involutive (- (x - 1))).
unfold Rminus.
rewrite (Ropp_involutive (x - 1)).
rewrite (Rplus_comm 1 (x - 1)).
rewrite (Rplus_assoc x (- (1)) 1).
rewrite (Rplus_opp_l 1).
apply (Rplus_0_r x).
apply (Ropp_neq_0_compat (x - 1)).
apply (Rlt_not_eq (x - 1) 0).
apply (Rlt_minus x 1).
apply (proj2 H1).
move=> H3.
apply False_ind.
apply (Rle_not_lt 0 (/ - (x - 1) - 1) H3).
apply (Rgt_minus (/ - (x - 1)) 1).
rewrite - {2} (Rinv_1).
apply (Rinv_lt_contravar (- (x - 1)) 1).
rewrite (Rmult_1_r (- (x - 1))).
apply (Ropp_0_gt_lt_contravar (x - 1)).
apply (Rlt_minus x 1 (proj2 H1)).
rewrite - {2} (Ropp_involutive 1).
apply (Ropp_lt_contravar (x - 1) (- (1))).
rewrite - (Rplus_0_l (- (1))).
apply (Rplus_lt_compat_r (- (1)) 0 x H2).
elim.
move=> H2.
exists 0%R.
elim (Rlt_le_dec 0 0).
move=> H3.
apply False_ind.
apply (Rlt_irrefl 0 H3).
move=> H3.
unfold Rminus.
rewrite (Rplus_0_l (- (1))).
rewrite - (Ropp_inv_permute 1).
rewrite Rinv_1.
rewrite (Rplus_opp_r (- (1))).
apply H2.
apply (Rgt_not_eq 1 0 Rlt_0_1).
move=> H2.
exists (/ - (x + 1) + 1)%R.
elim (Rlt_le_dec 0 (/ - (x + 1) + 1)).
move=> H3.
apply False_ind.
apply (Rlt_not_le (/ - (x + 1) + 1) 0 H3).
left.
rewrite - {2} (Ropp_involutive 1).
apply (Rlt_minus (/ - (x + 1)) (- (1))).
rewrite - (Ropp_inv_permute (x + 1)).
apply (Ropp_lt_contravar (/ (x + 1)) 1).
rewrite - {1} Rinv_1.
apply (Rinv_lt_contravar (x + 1) 1).
rewrite (Rmult_1_r (x + 1)).
rewrite - (Rplus_opp_l 1).
apply (Rplus_lt_compat_r 1 (- (1)) x (proj1 H1)).
rewrite - {2} (Rplus_0_l 1).
apply (Rplus_lt_compat_r 1 x 0 H2).
apply (Rgt_not_eq (x + 1) 0).
rewrite - (Rplus_opp_l 1).
apply (Rplus_lt_compat_r 1 (- (1)) x (proj1 H1)).
move=> H3.
unfold Rminus.
rewrite (Rplus_assoc (/ - (x + 1)) 1 (- (1))).
rewrite (Rplus_opp_r 1).
rewrite (Rplus_0_r (/ - (x + 1))).
rewrite (Rinv_involutive (- (x + 1))).
rewrite (Ropp_involutive (x + 1)).
rewrite (Rplus_comm x 1).
rewrite - (Rplus_assoc (- (1)) 1 x).
rewrite (Rplus_opp_l 1).
apply (Rplus_0_l x).
apply (Ropp_neq_0_compat (x + 1)).
apply (Rgt_not_eq (x + 1) 0).
rewrite - (Rplus_opp_l 1).
apply (Rplus_lt_compat_r 1 (- (1)) x (proj1 H1)).
Qed.

Lemma Theorem_2 : forall (A B : Type), (exists (f : A -> B), Injective f) -> (exists (g : B -> A), Injective g) -> SameCard A B.
Proof.
move=> A B.
elim.
move=> f H1.
elim.
move=> g H2.
suff: (let C := Setminus B (Full_set B) (Im A B (Full_set A) f) in SameCard A B).
apply.
move=> C.
suff: (let Cn := fix Cn (n : nat) : Ensemble B := match n with
  | O => C
  | S n0 => Im B B (Cn n0) (Basics.compose f g)
end in SameCard A B).
apply.
move=> Cn.
suff: (let Dn := fix Dn (n : nat) : Ensemble A := match n with
  | O => Im B A C g
  | S n0 => Im A A (Dn n0) (Basics.compose g f)
end in SameCard A B).
apply.
move=> Dn.
suff: (forall (a : A), (exists (n : nat), In B (Cn n) (f a)) <-> (exists (n : nat), In A (Dn n) a)).
move=> H3.
suff: (SameCard {a : A | exists (n : nat), In A (Dn n) a} {b : B | exists (n : nat), In B (Cn n) b}).
elim.
move=> ginv H4.
exists (fun (a : A) => match excluded_middle_informative (exists (n : nat), In A (Dn n) a) with
  | left H => proj1_sig (ginv (exist (fun (a0 : A) => exists (n : nat), In A (Dn n) a0) a H))
  | right _ => f a
end).
apply InjSurjBij.
move=> a1 a2.
elim (excluded_middle_informative (exists (n : nat), In A (Dn n) a1)).
move=> H5.
elim (excluded_middle_informative (exists (n : nat), In A (Dn n) a2)).
move=> H6 H7.
suff: ((exist (fun (a0 : A) => exists (n : nat), In A (Dn n) a0) a1 H5) = (exist (fun (a0 : A) => exists (n : nat), In A (Dn n) a0) a2 H6)).
move=> H8.
suff: (a1 = proj1_sig (exist (fun (a0 : A) => exists (n : nat), In A (Dn n) a0) a1 H5)).
move=> H9.
rewrite H9.
rewrite H8.
reflexivity.
reflexivity.
apply (BijInj {a : A | exists (n : nat), In A (Dn n) a} {b : B | exists (n : nat), In B (Cn n) b} ginv H4).
apply sig_map.
apply H7.
move=> H6 H7.
elim H6.
apply (proj1 (H3 a2)).
rewrite - H7.
apply (proj2_sig (ginv (exist (fun (a0 : A) => exists (n : nat), In A (Dn n) a0) a1 H5))).
move=> H5.
elim (excluded_middle_informative (exists (n : nat), In A (Dn n) a2)).
move=> H6 H7.
elim H5.
apply (proj1 (H3 a1)).
rewrite H7.
apply (proj2_sig (ginv (exist (fun (a0 : A) => exists (n : nat), In A (Dn n) a0) a2 H6))).
move=> H6.
apply (H1 a1 a2).
move=> b.
elim (classic (exists (n : nat), In B (Cn n) b)).
move=> H5.
elim (BijSurj {a : A | exists n : nat, In A (Dn n) a} {b : B | exists n : nat, In B (Cn n) b} ginv H4 (exist (fun (b0 : B) => exists (n : nat), In B (Cn n) b0) b H5)).
move=> a H6.
exists (proj1_sig a).
elim (excluded_middle_informative (exists (n : nat), In A (Dn n) (proj1_sig a))).
move=> H7.
suff: (b = proj1_sig (ginv a)).
move=> H8.
rewrite H8.
apply (f_equal (fun (x : {a : A | exists n : nat, In A (Dn n) a}) => proj1_sig (ginv x))).
apply sig_map.
reflexivity.
rewrite H6.
reflexivity.
move=> H7.
elim (H7 (proj2_sig a)).
move=> H5.
suff: (~ (exists n : nat, In B (Cn n) b)).
suff: (In B (Im A B (Full_set A) f) b).
elim.
move=> x H6 y H7 H8.
exists x.
elim (excluded_middle_informative (exists n : nat, In A (Dn n) x)).
move=> H9.
elim H8.
rewrite H7.
apply (proj2 (H3 x) H9).
move=> H9.
rewrite H7.
reflexivity.
apply NNPP.
move=> H6.
apply H5.
exists O.
apply conj.
apply (Full_intro B b).
apply H6.
apply H5.
apply (Formula_1_2 {b : B | exists (n : nat), In B (Cn n) b} {a : A | exists (n : nat), In A (Dn n) a}).
suff: (forall (b : B), (exists (n : nat), In B (Cn n) b) -> (exists (n : nat), In A (Dn n) (g b))).
move=> H4.
exists (fun (x : {b : B | exists (n : nat), In B (Cn n) b}) => exist (fun (a : A) => exists (n : nat), In A (Dn n) a) (g (proj1_sig x)) (H4 (proj1_sig x) (proj2_sig x))).
apply InjSurjBij.
move=> a1 a2 H5.
apply sig_map.
apply (H2 (proj1_sig a1) (proj1_sig a2)).
suff: (g (proj1_sig a1) = proj1_sig (exist (fun (a : A) => exists (n : nat), In A (Dn n) a) (g (proj1_sig a1)) (H4 (proj1_sig a1) (proj2_sig a1)))).
move=> H6.
rewrite H6.
rewrite H5.
reflexivity.
reflexivity.
suff: (forall (n : nat) (a : A), In A (Dn n) a -> exists (b : B), (In B (Cn n) b /\ g b = a)).
move=> H5 a.
elim (proj2_sig a).
move=> n H6.
elim (H5 n (proj1_sig a) H6).
move=> b H7.
exists (exist (fun (b0 : B) => exists (m : nat), In B (Cn m) b0) b (ex_intro (fun (m : nat) => In B (Cn m) b) n (proj1 H7))).
apply sig_map.
apply (proj2 H7).
elim.
move=> a.
elim.
move=> x H5 y H6.
exists x.
apply conj.
apply H5.
rewrite H6.
reflexivity.
simpl.
move=> n H5 a.
elim.
move=> x H6 y H7.
exists (f x).
apply conj.
elim (H5 x H6).
move=> z H8.
rewrite - (proj2 H8).
apply (Im_intro B B (Cn n) (Basics.compose f g) z (proj1 H8)).
reflexivity.
rewrite H7.
reflexivity.
suff: (forall (n : nat) (b : B), In B (Cn n) b -> In A (Dn n) (g b)).
move=> H4 b.
elim.
move=> n H5.
exists n.
apply (H4 n b H5).
elim.
move=> b H4.
apply (Im_intro B A C g b H4).
reflexivity.
simpl.
move=> n H4 b.
elim.
move=> x H5 y H6.
rewrite H6.
apply (Im_intro A A (Dn n) (Basics.compose g f) (g x) (H4 x H5)).
reflexivity.
suff: (forall (n : nat) (a : A), In B (Cn (S n)) (f a) <-> In A (Dn n) a).
move=> H3 a.
apply conj.
elim.
elim.
move=> H4.
elim (proj2 H4).
apply (Im_intro A B (Full_set A) f a (Full_intro A a)).
reflexivity.
move=> n H4 H5.
exists n.
apply (proj1 (H3 n a) H5).
elim.
move=> n H4.
exists (S n).
apply (proj2 (H3 n a) H4).
elim.
move=> a.
simpl.
apply conj.
move=> H3.
suff: (exists (b : B), In B C b /\ f a = f (g b)).
elim.
move=> b H4.
rewrite (H1 a (g b) (proj2 H4)).
apply (Im_intro B A C g b (proj1 H4)).
reflexivity.
elim H3.
move=> x H4 y H5.
exists x.
apply conj.
apply H4.
apply H5.
elim.
move=> x H3 y H4.
rewrite H4.
apply (Im_intro B B C (Basics.compose f g) x H3).
reflexivity.
move=> n H3 a.
apply conj.
move=> H4.
simpl.
suff: (exists (b : B), In B (Cn (S n)) b /\ f (g b) = f a).
elim.
move=> b H5.
suff: (exists (a0 : A), b = f a0).
elim.
move=> a0 H6.
apply (Im_intro A A (Dn n) (Basics.compose g f) a0).
apply (proj1 (H3 a0)).
rewrite - H6.
apply (proj1 H5).
simpl.
unfold Basics.compose.
rewrite - H6.
rewrite (H1 (g b) a (proj2 H5)).
reflexivity.
elim (proj1 H5).
move=> x H6 y H7.
exists (g x).
apply H7.
elim H4.
move=> x H5 y H6.
exists x.
apply conj.
apply H5.
rewrite H6.
reflexivity.
simpl.
elim.
move=> x H4 y H5.
rewrite H5.
apply (Im_intro B B (Cn (S n)) (Basics.compose f g) (f x)).
apply (proj2 (H3 x) H4).
reflexivity.
Qed.

Lemma Theorem_2_dash_dash_dash : forall (A B : Type), (exists (B1 : Ensemble B) (f : A -> {b : B | In B B1 b}), Bijective f) -> (exists (A1 : Ensemble A) (g : B -> {a : A | In A A1 a}), Bijective g) -> SameCard A B.
Proof.
move=> A B.
elim.
move=> B1.
elim.
move=> f H1.
elim.
move=> A1.
elim.
move=> g H2.
apply (Theorem_2 A B).
exists (fun (a : A) => proj1_sig (f a)).
move=> a1 a2 H3.
apply (BijInj A {b : B | In B B1 b} f H1 a1 a2).
apply sig_map.
apply H3.
exists (fun (b : B) => proj1_sig (g b)).
move=> b1 b2 H3.
apply (BijInj B {a : A | In A A1 a} g H2 b1 b2).
apply sig_map.
apply H3.
Qed.

Lemma Formula_65 : forall (a b : R), (a < b)%R -> SameCard {x : R | (a <= x <= b)%R} R.
Proof.
move=> a b H1.
apply (Theorem_2_dash_dash_dash {x : R | (a <= x <= b)%R} R).
exists (fun (r : R) => a <= r <= b)%R.
exists (fun (r : {x : R | (a <= x <= b)%R}) => r).
exists (fun (r : {x : R | (a <= x <= b)%R}) => r).
apply conj.
move=> x.
reflexivity.
move=> y.
reflexivity.
exists (fun (r : {x : R | (a <= x <= b)%R}) => (a < proj1_sig r < b)%R).
elim (Example_5 a b H1).
move=> f.
elim.
move=> g H2.
suff: (forall (r : R), (a < r < b)%R -> (a <= r <= b)%R).
move=> H3.
exists (fun (r : R) => exist (fun (y : {x : R | (a <= x <= b)%R}) => (a < proj1_sig y < b)%R) (exist (fun (x : R) => (a <= x <= b)%R) (proj1_sig (g r)) (H3 (proj1_sig (g r)) (proj2_sig (g r)))) (proj2_sig (g r))).
exists (fun (r : {y : {x : R | (a <= x <= b)%R} | In {x : R | (a <= x <= b)%R} (fun (r : {x : R | (a <= x <= b)%R}) => (a < proj1_sig r < b)%R) y}) => f (exist (fun (x : R) => (a < x < b)%R) (proj1_sig (proj1_sig r)) (proj2_sig r))).
apply conj.
move=> x.
simpl.
rewrite - {3} (proj2 H2 x).
apply (f_equal f).
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
simpl.
rewrite (proj1 H2).
reflexivity.
move=> r H3.
apply conj.
left.
apply (proj1 H3).
left.
apply (proj2 H3).
Qed.

Definition CardEquivalence := mkEquivalenceRelation Type SameCard Formula_1_1 Formula_1_2 Formula_1_3.

Definition CardT := EquivalenceRelationQuotient Type CardEquivalence.

Definition Card : Type -> CardT := EquivalenceRelationQuotientFunction Type CardEquivalence.

Lemma Formula_66_1 : forall (A B : Type), SameCard A B <-> Card A = Card B.
Proof.
move=> A B.
apply conj.
move=> H1.
apply sig_map.
apply (proj1 (Formula_6_2 Type CardEquivalence A B) H1).
move=> H1.
apply (proj2 (Formula_6_2 Type CardEquivalence A B)).
suff: (EquivalenceRelationClass Type CardEquivalence A = proj1_sig (Card A)).
move=> H2.
rewrite H2.
rewrite H1.
reflexivity.
reflexivity.
Qed.

Definition CardN : nat -> CardT := fun (n : nat) => Card (Count n).

Definition Formula_66_2 : forall (T : Type) (n : nat), proj1_sig (CardN n) T <-> cardinal T (Full_set T) n := CountCardinalBijective.

Lemma Formula_66_3 : forall (T : Type), proj1_sig (CardN O) T <-> ~ Inhabited T (Full_set T).
Proof.
move=> T.
apply conj.
elim.
move=> f.
elim.
move=> g H1.
elim.
move=> t H2.
elim (le_not_lt O (proj1_sig (g t)) (le_0_n (proj1_sig (g t))) (proj2_sig (g t))).
move=> H1.
exists (fun (m : Count O) => match (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) (proj2_sig m)) with
end).
exists (fun (t : T) => match H1 (Inhabited_intro T (Full_set T) t (Full_intro T t)) with
end).
apply conj.
move=> m.
elim (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) (proj2_sig m)).
move=> t.
elim (H1 (Inhabited_intro T (Full_set T) t (Full_intro T t))).
Qed.

Definition InfiniteCard : CardT -> Prop := fun (c : CardT) => ~ exists (n : nat), c = CardN n.

Definition cardLe (A B : Type) := exists (f : A -> B), Injective f.

Lemma CardLeWellDefined : forall (A1 A2 B1 B2 : Type), SameCard A1 A2 -> SameCard B1 B2 -> cardLe A1 B1 = cardLe A2 B2.
Proof.
suff: (forall (A1 A2 B1 B2 : Type), SameCard A1 A2 -> SameCard B1 B2 -> cardLe A1 B1 -> cardLe A2 B2).
move=> H1 A1 A2 B1 B2 H2 H3.
apply propositional_extensionality.
apply conj.
apply (H1 A1 A2 B1 B2 H2 H3).
apply (H1 A2 A1 B2 B1 (Formula_1_2 A1 A2 H2) (Formula_1_2 B1 B2 H3)).
move=> A1 A2 B1 B2.
elim.
move=> f.
elim.
move=> finv H1.
elim.
move=> g.
elim.
move=> ginv H2.
elim.
move=> h H3.
exists (Basics.compose (Basics.compose g h) finv).
move=> a1 a2 H4.
apply (BijInj A2 A1 finv).
exists f.
apply conj.
apply (proj2 H1).
apply (proj1 H1).
apply H3.
apply (BijInj B1 B2 g).
exists ginv.
apply H2.
apply H4.
Qed.

Definition CardLe : CardT -> CardT -> Prop := EquivalenceRelationFunctionTwo Type Type Prop CardEquivalence CardEquivalence cardLe CardLeWellDefined.

Definition CardLeNature : forall (T1 T2 : Type) (C1 C2 : CardT), proj1_sig C1 T1 -> proj1_sig C2 T2 -> cardLe T1 T2 = CardLe C1 C2 := EquivalenceRelationFunctionTwoNature Type Type Prop CardEquivalence CardEquivalence cardLe CardLeWellDefined.

Lemma cardLeDef2 : forall (A B: Type), cardLe A B <-> exists (B1 : Ensemble B), SameCard A {b : B | In B B1 b}.
Proof.
move=> A B.
apply conj.
elim.
move=> f H1.
exists (Im A B (Full_set A) f).
exists (fun (a : A) => exist (Im A B (Full_set A) f) (f a) (Im_intro A B (Full_set A) f a (Full_intro A a) (f a) eq_refl)).
apply InjSurjBij.
move=> a1 a2 H2.
apply H1.
suff: (f a1 = proj1_sig (exist (Im A B (Full_set A) f) (f a1) (Im_intro A B (Full_set A) f a1 (Full_intro A a1) (f a1) eq_refl))).
move=> H3.
rewrite H3.
rewrite H2.
reflexivity.
reflexivity.
move=> b.
suff: (let temp := b in proj1_sig b = proj1_sig temp).
elim (proj2_sig b).
move=> x H2 y H3 H4.
simpl.
exists x.
apply sig_map.
rewrite - H4.
rewrite H3.
reflexivity.
reflexivity.
elim.
move=> B1.
elim.
move=> f H1.
exists (fun (a : A) => proj1_sig (f a)).
move=> a1 a2 H2.
apply (BijInj A {b : B | In B B1 b} f H1 a1 a2).
apply sig_map.
apply H2.
Qed.

Lemma Formula_69 : forall (N M : nat), N <= M <-> CardLe (CardN N) (CardN M).
Proof.
move=> N M.
apply conj.
move=> H1.
rewrite - (CardLeNature (Count N) (Count M) (CardN N) (CardN M)).
apply (proj2 (cardLeDef2 (Count N) (Count M))).
exists (fun (k : Count M) => proj1_sig k < N).
exists (fun (n : Count N) => exist (fun (k : Count M) => proj1_sig k < N) (exist (fun (k : nat) => k < M) (proj1_sig n) (le_trans (S (proj1_sig n)) N M (proj2_sig n) H1)) (proj2_sig n)).
exists (fun (n : {m : Count M | In (Count M) (fun (k : Count M) => proj1_sig k < N) m}) => exist (fun (k : nat) => k < N) (proj1_sig (proj1_sig n)) (proj2_sig n)).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
reflexivity.
apply (ERref Type CardEquivalence (Count N)).
apply (ERref Type CardEquivalence (Count M)).
rewrite - (CardLeNature (Count N) (Count M) (CardN N) (CardN M)).
elim.
move=> f H1.
apply (CountInjectiveLe N M f H1).
apply (ERref Type CardEquivalence (Count N)).
apply (ERref Type CardEquivalence (Count M)).
Qed.

Lemma Formula_1_6 : forall (C : CardT), CardLe C C.
Proof.
move=> C.
suff: (exists (t : Type), proj1_sig C t).
elim.
move=> t H1.
rewrite - (CardLeNature t t C C H1 H1).
exists (fun (x : t) => x).
move=> x1 x2.
apply.
elim (proj2_sig C).
move=> x H1.
exists x.
rewrite H1.
apply (ERref Type CardEquivalence x).
Qed.

Lemma Formula_1_7 : forall (C1 C2 : CardT), CardLe C1 C2 -> CardLe C2 C1 -> C1 = C2.
Proof.
move=> C1 C2.
suff: (exists (t1 : Type), proj1_sig C1 t1 /\ C1 = Card t1).
elim.
move=> t1 H1.
suff: (exists (t2 : Type), proj1_sig C2 t2 /\ C2 = Card t2).
elim.
move=> t2 H2.
rewrite - (CardLeNature t1 t2 C1 C2 (proj1 H1) (proj1 H2)).
rewrite - (CardLeNature t2 t1 C2 C1 (proj1 H2) (proj1 H1)).
move=> H3 H4.
rewrite (proj2 H1).
rewrite (proj2 H2).
apply (proj1 (Formula_66_1 t1 t2)).
apply (Theorem_2 t1 t2 H3 H4).
elim (proj2_sig C2).
move=> x H2.
exists x.
apply conj.
rewrite H2.
apply (ERref Type CardEquivalence x).
apply sig_map.
rewrite H2.
reflexivity.
elim (proj2_sig C1).
move=> x H1.
exists x.
apply conj.
rewrite H1.
apply (ERref Type CardEquivalence x).
apply sig_map.
rewrite H1.
reflexivity.
Qed.

Lemma Formula_1_8 : forall (C1 C2 C3 : CardT), CardLe C1 C2 -> CardLe C2 C3 -> CardLe C1 C3.
Proof.
move=> C1 C2 C3.
suff: (exists (t1 : Type), proj1_sig C1 t1 /\ C1 = Card t1).
elim.
move=> t1 H1.
suff: (exists (t2 : Type), proj1_sig C2 t2 /\ C2 = Card t2).
elim.
move=> t2 H2.
suff: (exists (t3 : Type), proj1_sig C3 t3 /\ C3 = Card t3).
elim.
move=> t3 H3.
rewrite - (CardLeNature t1 t2 C1 C2 (proj1 H1) (proj1 H2)).
rewrite - (CardLeNature t2 t3 C2 C3 (proj1 H2) (proj1 H3)).
rewrite - (CardLeNature t1 t3 C1 C3 (proj1 H1) (proj1 H3)).
elim.
move=> f H4.
elim.
move=> g H5.
exists (Basics.compose g f).
apply (InjChain t1 t2 t3 f g H4 H5).
elim (proj2_sig C3).
move=> x H3.
exists x.
apply conj.
rewrite H3.
apply (ERref Type CardEquivalence x).
apply sig_map.
rewrite H3.
reflexivity.
elim (proj2_sig C2).
move=> x H2.
exists x.
apply conj.
rewrite H2.
apply (ERref Type CardEquivalence x).
apply sig_map.
rewrite H2.
reflexivity.
elim (proj2_sig C1).
move=> x H1.
exists x.
apply conj.
rewrite H1.
apply (ERref Type CardEquivalence x).
apply sig_map.
rewrite H1.
reflexivity.
Qed.

Lemma Theorem_5_1_1 : forall (A B : Type), cardLe A nat -> cardLe B nat -> cardLe (A * B) nat.
Proof.
move=> A B.
elim.
move=> f1 H1.
elim.
move=> f2 H2.
elim (Formula_1_2 nat (nat * nat) Example_3).
move=> g H3.
exists (fun (x : A * B) => g (f1 (fst x), f2 (snd x))).
move=> x1 x2 H4.
apply injective_projections.
apply H1.
suff: (f1 (fst x1) = fst (f1 (fst x1), f2 (snd x1))).
move=> H5.
rewrite H5.
rewrite (BijInj (nat * nat) nat g H3 (f1 (fst x1), f2 (snd x1)) (f1 (fst x2), f2 (snd x2)) H4).
reflexivity.
reflexivity.
apply H2.
suff: (f2 (snd x1) = snd (f1 (fst x1), f2 (snd x1))).
move=> H5.
rewrite H5.
rewrite (BijInj (nat * nat) nat g H3 (f1 (fst x1), f2 (snd x1)) (f1 (fst x2), f2 (snd x2)) H4).
reflexivity.
reflexivity.
Qed.

Lemma Theorem_5_1_2 : forall (A B : Type), cardLe A nat -> cardLe B nat -> Full_set A <> Empty_set A -> Full_set B <> Empty_set B -> (SameCard A nat \/ SameCard B nat) -> SameCard (A * B) nat.
Proof.
move=> A B H1 H2 H3 H4 H5.
apply (Theorem_2 (A * B) nat).
apply (Theorem_5_1_1 A B H1 H2).
elim H5.
move=> H6.
elim (Formula_1_2 A nat H6).
move=> f H7.
suff: (exists (b : B), True).
elim.
move=> b H8.
exists (fun (n : nat) => (f n, b)).
move=> n1 n2 H9.
apply (BijInj nat A f H7 n1 n2).
suff: (f n1 = fst (f n1, b)).
move=> H10.
rewrite H10.
rewrite H9.
reflexivity.
reflexivity.
apply NNPP.
move=> H8.
apply H4.
apply Extensionality_Ensembles.
apply conj.
move=> b.
elim H8.
exists b.
apply I.
move=> b H9.
apply (Full_intro B b).
move=> H6.
elim (Formula_1_2 B nat H6).
move=> f H7.
suff: (exists (a : A), True).
elim.
move=> a H8.
exists (fun (n : nat) => (a, f n)).
move=> n1 n2 H9.
apply (BijInj nat B f H7 n1 n2).
suff: (f n1 = snd (a, f n1)).
move=> H10.
rewrite H10.
rewrite H9.
reflexivity.
reflexivity.
apply NNPP.
move=> H8.
apply H3.
apply Extensionality_Ensembles.
apply conj.
move=> a.
elim H8.
exists a.
apply I.
move=> a H9.
apply (Full_intro A a).
Qed.

Lemma Theorem_5_corollary_1 : SameCard Z nat.
Proof.
apply (Theorem_2 Z nat).
elim (Formula_1_2 nat (nat * nat) Example_3).
move=> f H1.
exists (fun (m : Z) => f (match m with
  | Z0 => (O, O)
  | Zpos n => (1, Pos.to_nat n)
  | Zneg n => (2, Pos.to_nat n)
end)).
apply (InjChain Z (nat * nat) nat).
move=> m1 m2.
elim m1.
elim m2.
move=> H2.
reflexivity.
move=> p H2.
elim (lt_irrefl (fst (0, 0))).
rewrite {2} H2.
apply (le_n 1).
move=> p H2.
elim (lt_irrefl (fst (0, 0))).
rewrite {2} H2.
apply (le_S 1 1 (le_n 1)).
move=> p.
elim m2.
move=> H2.
elim (lt_irrefl (fst (1, Pos.to_nat p))).
rewrite {1} H2.
apply (le_n 1).
move=> q H2.
rewrite (Pos2Nat.inj p q).
reflexivity.
suff: (Pos.to_nat p = snd (1, Pos.to_nat p)).
move=> H3.
rewrite H3.
rewrite H2.
reflexivity.
reflexivity.
move=> q H2.
elim (lt_irrefl (fst (1, Pos.to_nat p))).
rewrite {2} H2.
apply (le_n 2).
move=> p.
elim m2.
move=> H2.
elim (lt_irrefl (fst (2, Pos.to_nat p))).
rewrite {1} H2.
apply (le_S 1 1 (le_n 1)).
move=> q H2.
elim (lt_irrefl (fst (2, Pos.to_nat p))).
rewrite {1} H2.
apply (le_n 2).
move=> q H2.
rewrite (Pos2Nat.inj p q).
reflexivity.
suff: (Pos.to_nat p = snd (2, Pos.to_nat p)).
move=> H3.
rewrite H3.
rewrite H2.
reflexivity.
reflexivity.
apply (BijInj (nat * nat) nat f H1).
exists (fun (n : nat) => Zpos (Pos.of_nat (S n))).
move=> n1 n2 H1.
apply (eq_add_S n1 n2).
apply (Nat2Pos.inj (S n1) (S n2)).
move=> H2.
suff: (let temp := S n1 in match temp with
  | O => True
  | S _ => False
end).
apply.
rewrite H2.
apply I.
move=> H2.
suff: (let temp := S n2 in match temp with
  | O => True
  | S _ => False
end).
apply.
rewrite H2.
apply I.
suff: (Pos.of_nat (S n1) = let temp := Z.pos (Pos.of_nat (S n1)) in match temp with
  | Z0 => Pos.of_nat (S n1)
  | Zpos n => n
  | Zneg _ => Pos.of_nat (S n1)
end).
move=> H2.
rewrite H2.
rewrite H1.
reflexivity.
reflexivity.
Qed.

Lemma Theorem_5_corollary_2_sub : SameCard QArith_base.Q nat.
Proof.
apply (Theorem_2 QArith_base.Q nat).
elim (Formula_1_2 nat (nat * nat) Example_3).
move=> f H1.
elim Theorem_5_corollary_1.
move=> g H2.
exists (fun (q : QArith_base.Q) => f (g (QArith_base.Qnum q), Pos.to_nat (QArith_base.Qden q))).
move=> q1 q2.
elim q1.
move=> Qnum1 Qden1.
elim q2.
move=> Qnum2 Qden2.
simpl.
move=> H3.
suff: (Qnum1 = Qnum2).
move=> H4.
rewrite H4.
suff: (Qden1 = Qden2).
move=> H5.
rewrite H5.
reflexivity.
apply (Pos2Nat.inj Qden1 Qden2).
suff: (Pos.to_nat Qden1 = snd (g Qnum1, Pos.to_nat Qden1)).
move=> H5.
rewrite H5.
rewrite (BijInj (nat * nat) nat f H1 (g Qnum1, Pos.to_nat Qden1) (g Qnum2, Pos.to_nat Qden2) H3).
reflexivity.
reflexivity.
apply (BijInj Z nat g H2 Qnum1 Qnum2).
suff: (g Qnum1 = fst (g Qnum1, Pos.to_nat Qden1)).
move=> H4.
rewrite H4.
rewrite (BijInj (nat * nat) nat f H1 (g Qnum1, Pos.to_nat Qden1) (g Qnum2, Pos.to_nat Qden2) H3).
reflexivity.
reflexivity.
exists (fun (n : nat) => QArith_base.inject_Z (Zpos (Pos.of_nat (S n)))).
move=> n1 n2 H1.
apply (eq_add_S n1 n2).
apply (Nat2Pos.inj (S n1) (S n2)).
move=> H2.
suff: (let temp := S n1 in match temp with
  | O => True
  | S _ => False
end).
apply.
rewrite H2.
apply I.
move=> H2.
suff: (let temp := S n2 in match temp with
  | O => True
  | S _ => False
end).
apply.
rewrite H2.
apply I.
suff: (Z.pos (Pos.of_nat (S n1)) = Z.pos (Pos.of_nat (S n2))).
move=> H2.
suff: (Pos.of_nat (S n1) = let temp := Z.pos (Pos.of_nat (S n1)) in match temp with
  | Z0 => Pos.of_nat (S n1)
  | Zpos p => p
  | Zneg _ => Pos.of_nat (S n1)
end).
move=> H3.
rewrite H3.
rewrite H2.
reflexivity.
reflexivity.
suff: (Z.pos (Pos.of_nat (S n1)) = QArith_base.Qnum (QArith_base.inject_Z (Z.pos (Pos.of_nat (S n1))))).
move=> H2.
rewrite H2.
rewrite H1.
reflexivity.
reflexivity.
Qed.

Definition QEquivalence := mkEquivalenceRelation QArith_base.Q QArith_base.Qeq QArith_base.Qeq_refl QArith_base.Qeq_sym QArith_base.Qeq_trans.

Definition MyQ := EquivalenceRelationQuotient QArith_base.Q QEquivalence.

Lemma Theorem_5_corollary_2 : SameCard MyQ nat.
Proof.
apply (Theorem_2 MyQ nat).
elim Theorem_5_corollary_2_sub.
move=> f H1.
suff: (forall (q : MyQ), {q0 : QArith_base.Q | In QArith_base.Q (proj1_sig q) q0 /\ forall (q1 : QArith_base.Q), (In QArith_base.Q (proj1_sig q) q1 -> (QArith_base.Qden q0 <= QArith_base.Qden q1)%positive)}).
move=> H2.
exists (fun (q : MyQ) => f (proj1_sig (H2 q))).
move=> q1 q2 H3.
apply (EquivalenceRelationQuotientSame QArith_base.Q QEquivalence q1 q2 (proj1_sig (H2 q1))).
apply (proj1 (proj2_sig (H2 q1))).
rewrite (BijInj QArith_base.Q nat f H1 (proj1_sig (H2 q1)) (proj1_sig (H2 q2)) H3).
apply (proj1 (proj2_sig (H2 q2))).
move=> q.
apply constructive_definite_description.
apply (unique_existence (fun (x : QArith_base.Q) => In QArith_base.Q (proj1_sig q) x /\ (forall (q1 : QArith_base.Q), In QArith_base.Q (proj1_sig q) q1 -> (QArith_base.Qden x <= QArith_base.Qden q1)%positive))).
apply conj.
suff: (exists (n : nat), is_min_nat (fun (k : nat) => exists (x : QArith_base.Q), In QArith_base.Q (proj1_sig q) x /\ QArith_base.Qden x = Pos.of_nat (S k)) n).
elim.
move=> n H2.
elim (proj1 H2).
move=> q0 H3.
exists q0.
apply conj.
apply (proj1 H3).
move=> q1 H4.
elim (le_or_lt (Pos.to_nat (QArith_base.Qden q0)) (Pos.to_nat (QArith_base.Qden q1))).
move=> H5.
apply (proj2 (Pos2Nat.inj_le (QArith_base.Qden q0) (QArith_base.Qden q1)) H5).
move=> H5.
elim (le_not_lt (Pos.to_nat (QArith_base.Qden q0)) (Pos.to_nat (QArith_base.Qden q1))).
rewrite (proj2 H3).
rewrite (Nat2Pos.id (S n)).
suff: (exists (m : nat), Pos.to_nat (QArith_base.Qden q1) = S m).
elim.
move=> m H6.
rewrite H6.
apply (le_n_S n m).
apply (proj2 H2 m).
exists q1.
apply conj.
apply H4.
rewrite - H6.
rewrite (Pos2Nat.id (QArith_base.Qden q1)).
reflexivity.
suff: (Pos.to_nat (QArith_base.Qden q1) > O).
elim (Pos.to_nat (QArith_base.Qden q1)).
move=> H6.
elim (lt_irrefl O H6).
move=> m H6 H7.
exists m.
reflexivity.
apply (Pos2Nat.is_pos (QArith_base.Qden q1)).
move=> H6.
suff: (let temp := S n in match temp with
  | O => True
  | S _ => False
end).
apply.
rewrite H6.
apply I.
apply H5.
apply (min_nat_exist (fun (k : nat) => exists (x : QArith_base.Q), In QArith_base.Q (proj1_sig q) x /\ QArith_base.Qden x = Pos.of_nat (S k))).
elim (proj2_sig q).
move=> x H2.
apply (Inhabited_intro nat (fun (k : nat) => exists (x : QArith_base.Q), In QArith_base.Q (proj1_sig q) x /\ QArith_base.Qden x = Pos.of_nat (S k)) (pred (Pos.to_nat (QArith_base.Qden x)))).
exists x.
apply conj.
rewrite H2.
apply (ERref QArith_base.Q QEquivalence x).
suff: (forall (n : nat), n > 0 -> S (pred n) = n).
move=> H3.
rewrite (H3 (Pos.to_nat (QArith_base.Qden x)) (Pos2Nat.is_pos (QArith_base.Qden x))).
rewrite (Pos2Nat.id (QArith_base.Qden x)).
reflexivity.
elim.
move=> H3.
elim (lt_irrefl O H3).
move=> n H3 H4.
reflexivity.
move=> q1 q2.
elim q1.
elim q2.
move=> Qnum1 Qden1 Qnum2 Qden2 H2 H3.
suff: (QArith_base.Qeq {| QArith_base.Qnum := Qnum2; QArith_base.Qden := Qden2 |} {| QArith_base.Qnum := Qnum1; QArith_base.Qden := Qden1 |}).
unfold QArith_base.Qeq.
simpl.
suff: (Qden2 = Qden1).
move=> H4.
rewrite H4.
move=> H5.
rewrite (Z.mul_reg_r Qnum2 Qnum1 (Z.pos Qden1)).
reflexivity.
move=> H6.
suff: (let temp := Z.pos Qden1 in match temp with
  | Z0 => False
  | Zpos _ => True
  | Zneg _ => True
end).
rewrite H6.
elim.
reflexivity.
apply H5.
apply (Pos.le_antisym Qden2 Qden1).
apply (proj2 H2 {| QArith_base.Qnum := Qnum1; QArith_base.Qden := Qden1 |} (proj1 H3)).
apply (proj2 H3 {| QArith_base.Qnum := Qnum2; QArith_base.Qden := Qden2 |} (proj1 H2)).
elim (EquivalenceRelationQuotientInhabited QArith_base.Q QEquivalence q).
move=> q0 H4.
apply (QArith_base.Qeq_trans {| QArith_base.Qnum := Qnum2; QArith_base.Qden := Qden2 |} q0 {| QArith_base.Qnum := Qnum1; QArith_base.Qden := Qden1 |}).
apply QArith_base.Qeq_sym.
suff: (In QArith_base.Q (proj1_sig q) {| QArith_base.Qnum := Qnum2; QArith_base.Qden := Qden2 |}).
rewrite H4.
apply.
apply (proj1 H2).
suff: (In QArith_base.Q (proj1_sig q) {| QArith_base.Qnum := Qnum1; QArith_base.Qden := Qden1 |}).
rewrite H4.
apply.
apply (proj1 H3).
exists (fun (n : nat) => EquivalenceRelationQuotientFunction QArith_base.Q QEquivalence (QArith_base.inject_Z (Zpos (Pos.of_nat (S n))))).
move=> n1 n2 H1.
suff: (QArith_base.Qeq (QArith_base.inject_Z (Z.pos (Pos.of_nat (S n1)))) (QArith_base.inject_Z (Z.pos (Pos.of_nat (S n2))))).
unfold QArith_base.Qeq.
unfold QArith_base.inject_Z.
unfold QArith_base.Qnum.
unfold QArith_base.Qden.
rewrite (Z.mul_1_r (Z.pos (Pos.of_nat (S n1)))).
rewrite (Z.mul_1_r (Z.pos (Pos.of_nat (S n2)))).
move=> H2.
apply (eq_add_S n1 n2).
apply (Nat2Pos.inj (S n1) (S n2)).
move=> H3.
suff: (let temp := S n1 in match temp with
  | O => True
  | S _ => False
end).
apply.
rewrite H3.
apply I.
move=> H3.
suff: (let temp := S n2 in match temp with
  | O => True
  | S _ => False
end).
apply.
rewrite H3.
apply I.
suff: (Pos.of_nat (S n1) = let temp := Z.pos (Pos.of_nat (S n1)) in match temp with
  | Z0 => Pos.of_nat (S n1)
  | Zpos n => n
  | Zneg _ => Pos.of_nat (S n1)
end).
move=> H3.
rewrite H3.
rewrite H2.
reflexivity.
reflexivity.
apply (proj2 (Formula_6_2 QArith_base.Q QEquivalence (QArith_base.inject_Z (Z.pos (Pos.of_nat (S n1)))) (QArith_base.inject_Z (Z.pos (Pos.of_nat (S n2)))))).
suff: (EquivalenceRelationClass QArith_base.Q QEquivalence (QArith_base.inject_Z (Z.pos (Pos.of_nat (S n1)))) = proj1_sig (EquivalenceRelationQuotientFunction QArith_base.Q QEquivalence (QArith_base.inject_Z (Z.pos (Pos.of_nat (S n1)))))).
move=> H2.
rewrite H2.
rewrite H1.
reflexivity.
reflexivity.
Qed.

Lemma Formula_85_3 : SameCard (nat -> Count 2) R.
Proof.
suff: (forall (an : nat -> R) (s : R) (k : nat), (Un_cv (sum_f_R0 an) s) <-> (Un_cv (sum_f_R0 (fun (n : nat) => an (n + (S k)))) (s - (sum_f_R0 an k))%R)).
move=> H0.
apply (Formula_1_3 (nat -> Count 2) {f : nat -> Count 2 | forall (n : nat), exists (m : nat), m >= n /\ f m = (exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))} R).
suff: (let sw := fun (m : Count 2) => match excluded_middle_informative (m = (exist (fun (k : nat) => k < 2) 1 (le_n 2))) with
  | left _ => (exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))
  | right _ => (exist (fun (k : nat) => k < 2) 1 (le_n 2))
end in SameCard (nat -> Count 2) {f : (nat -> Count 2) | forall (n : nat), exists (m : nat), m >= n /\ f m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))}).
apply.
move=> sw.
suff: (forall (f : nat -> Count 2), In (nat -> Count 2) (fun (g : nat -> Count 2) => forall (n : nat), exists (m : nat), m >= n /\ g m = (exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))) (match excluded_middle_informative (exists (n : nat), forall (m : nat), m >= n -> f m = (exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))) with
  | left _ => (fun (k : nat) => match k with
    | O => (exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))
    | S k0 => f k0
  end)
  | right _ => match excluded_middle_informative (exists (n : nat), forall (m : nat), m >= n -> f m = (exist (fun (k : nat) => k < 2) 1 (le_n 2))) with
    | left _ => (fun (k : nat) => match k with
      | O => (exist (fun (k : nat) => k < 2) 1 (le_n 2))
      | S k0 => sw (f k0)
    end)
    | right _ => f
  end
end)).
move=> H1.
exists (fun (f : nat -> Count 2) => exist (fun (g : nat -> Count 2) => forall (n : nat), exists (m : nat), m >= n /\ g m = (exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))) (match excluded_middle_informative (exists (n : nat), forall (m : nat), m >= n -> f m = (exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))) with
  | left _ => (fun (k : nat) => match k with
    | O => (exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))
    | S k0 => f k0
  end)
  | right _ => match excluded_middle_informative (exists (n : nat), forall (m : nat), m >= n -> f m = (exist (fun (k : nat) => k < 2) 1 (le_n 2))) with
    | left _ => (fun (k : nat) => match k with
      | O => (exist (fun (k : nat) => k < 2) 1 (le_n 2))
      | S k0 => sw (f k0)
    end)
    | right _ => f
  end
end) (H1 f)).
exists (fun (f : {g : nat -> Count 2 | forall (n : nat), exists (m : nat), m >= n /\ g m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))}) => match excluded_middle_informative (exists (n : nat), forall (m : nat), m >= n -> proj1_sig f m = (exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))) with
  | left _ => match excluded_middle_informative (proj1_sig f O = (exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))) with
    | left _ => (fun (k : nat) => proj1_sig f (S k))
    | right _ => (fun (k : nat) => sw (proj1_sig f (S k)))
  end
  | right _ => proj1_sig f
end).
simpl.
apply conj.
move=> x.
elim (excluded_middle_informative (exists (n : nat), forall (m : nat), m >= n -> x m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))).
move=> H2.
elim (excluded_middle_informative (@ex nat (fun n : nat => forall (m : nat) (_ : ge m n), @eq (Count (S (S O))) match m return (Count (S (S O))) with
  | O => @exist nat (fun k : nat => lt k (S (S O))) O (le_S (S O) (S O) (le_n (S O)))
  | S k0 => x k0
end (@exist nat (fun k : nat => lt k (S (S O))) O (le_S (S O) (S O) (le_n (S O))))))).
move=> H3.
elim (excluded_middle_informative (@eq (Count (S (S O))) (@exist nat (fun k : nat => lt k (S (S O))) O (le_S (S O) (S O) (le_n (S O)))) (@exist nat (fun k : nat => lt k (S (S O))) O (le_S (S O) (S O) (le_n (S O)))))).
move=> H4.
reflexivity.
elim.
reflexivity.
elim.
elim H2.
move=> n H3.
exists (S n).
move=> m H4.
suff: (exists (k : nat), m = S k).
elim.
move=> k H5.
rewrite H5.
apply (H3 k).
apply (le_S_n n k).
rewrite - H5.
apply H4.
suff: (m >= S n).
elim m.
move=> H5.
elim (le_not_lt 0 n (le_0_n n) H5).
move=> k H5 H6.
exists k.
reflexivity.
apply H4.
move=> H2.
elim (excluded_middle_informative (exists (n : nat), forall (m : nat), m >= n -> x m = exist (fun (k : nat) => k < 2) 1 (le_n 2))).
move=> H3.
elim (excluded_middle_informative (@ex nat (fun (n : nat) => forall (m : nat) (_ : ge m n), @eq (Count (S (S O))) match m return (Count (S (S O))) with
  | O => @exist nat (fun (k : nat) => lt k (S (S O))) (S O) (le_n (S (S O)))
  | S k0 => sw (x k0)
end (@exist nat (fun (k : nat) => lt k (S (S O))) O (le_S (S O) (S O) (le_n (S O))))))).
move=> H4.
elim (excluded_middle_informative (@eq (Count (S (S O))) (@exist nat (fun (k : nat) => lt k (S (S O))) (S O) (le_n (S (S O)))) (@exist nat (fun (k : nat) => lt k (S (S O))) O (le_S (S O) (S O) (le_n (S O)))))).
move=> H5.
elim (lt_irrefl (proj1_sig (exist (fun (k : nat) => k < 2) 1 (le_n 2)))).
rewrite {1} H5.
apply (le_n 1).
move=> H5.
apply functional_extensionality.
move=> n.
unfold sw.
elim (excluded_middle_informative (x n = exist (fun (k : nat) => k < 2) 1 (le_n 2))).
move=> H6.
elim (excluded_middle_informative (@eq (Count (S (S O))) (@exist nat (fun (k : nat) => lt k (S (S O))) O (le_S (S O) (S O) (le_n (S O)))) (@exist nat (fun (k : nat) => lt k (S (S O))) (S O) (le_n (S (S O)))))).
move=> H7.
elim (lt_irrefl (proj1_sig (exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))))).
rewrite {2} H7.
apply (le_n 1).
move=> H7.
rewrite H6.
reflexivity.
move=> H6.
elim (excluded_middle_informative (@eq (Count (S (S O))) (@exist nat (fun (k : nat) => lt k (S (S O))) (S O) (le_n (S (S O)))) (@exist nat (fun (k : nat) => lt k (S (S O))) (S O) (le_n (S (S O)))))).
move=> H7.
elim (le_lt_or_eq (proj1_sig (x n)) 1 (le_S_n (proj1_sig (x n)) 1 (proj2_sig (x n)))).
move=> H8.
apply sig_map.
elim (le_lt_or_eq (proj1_sig (x n)) O (le_S_n (proj1_sig (x n)) O H8)).
move=> H9.
elim (le_not_lt O (proj1_sig (x n)) (le_0_n (proj1_sig (x n))) H9).
move=> H9.
rewrite H9.
reflexivity.
move=> H8.
elim H6.
apply sig_map.
apply H8.
elim.
reflexivity.
elim.
elim H3.
move=> n H4.
exists (S n).
move=> m H5.
suff: (exists (k : nat), m = S k).
elim.
move=> k H6.
rewrite H6.
rewrite (H4 k).
unfold sw.
elim (excluded_middle_informative (@eq (Count (S (S O))) (@exist nat (fun (l : nat) => lt l (S (S O))) (S O) (le_n (S (S O)))) (@exist nat (fun (l : nat) => lt l (S (S O))) (S O) (le_n (S (S O)))))).
move=> H7.
reflexivity.
elim.
reflexivity.
apply (le_S_n n k).
rewrite - H6.
apply H5.
suff: (m >= S n).
elim m.
move=> H6.
elim (le_not_lt 0 n (le_0_n n) H6).
move=> k H6 H7.
exists k.
reflexivity.
apply H5.
move=> H3.
elim (excluded_middle_informative (exists n : nat, forall m : nat, m >= n -> x m = exist (fun k : nat => k < 2) 0 (le_S 1 1 (le_n 1)))).
move=> H4.
elim (H2 H4).
move=> H4.
reflexivity.
move=> y.
apply sig_map.
simpl.
elim (excluded_middle_informative (exists (n : nat), forall (m : nat), m >= n -> proj1_sig y m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))).
move=> H2.
elim (excluded_middle_informative (proj1_sig y 0 = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))).
move=> H3.
elim (excluded_middle_informative (exists (n : nat), forall (m : nat), m >= n -> proj1_sig y (S m) = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))).
move=> H4.
apply functional_extensionality.
elim.
rewrite H3.
reflexivity.
move=> n H5.
reflexivity.
elim.
elim H2.
move=> n H4.
exists n.
move=> m H5.
apply (H4 (S m) (le_S n m H5)).
move=> H3.
elim (excluded_middle_informative (exists (n : nat), forall (m : nat), m >= n -> sw (proj1_sig y (S m)) = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))).
elim.
move=> n1 H4.
elim H2.
move=> n2 H5.
elim (lt_irrefl (proj1_sig (proj1_sig y (S (max n1 n2))))).
suff: (sw (proj1_sig y (S (max n1 n2))) = exist (fun k : nat => k < 2) 0 (le_S 1 1 (le_n 1))).
unfold sw.
elim (excluded_middle_informative (proj1_sig y (S (max n1 n2)) = exist (fun (k : nat) => k < 2) 1 (le_n 2))).
move=> H6 H7.
rewrite {1} (H5 (S (max n1 n2))).
rewrite H6.
apply (le_n 1).
apply (le_S n2 (max n1 n2) (Nat.le_max_r n1 n2)).
move=> H6 H7.
elim (lt_irrefl (proj1_sig (exist (fun (k : nat) => k < 2) 1 (le_n 2)))).
rewrite {1} H7.
apply (le_n 1).
apply (H4 (max n1 n2) (Nat.le_max_l n1 n2)).
move=> H4.
elim (excluded_middle_informative (@ex nat (fun (n : nat) => forall (m : nat) (_ : ge m n), @eq (Count (S (S O))) (sw (@proj1_sig (forall _ : nat, Count (S (S O))) (fun g : forall _ : nat, Count (S (S O)) => forall n0 : nat, @ex nat (fun m0 : nat => and (ge m0 n0) (@eq (Count (S (S O))) (g m0) (@exist nat (fun k : nat => lt k (S (S O))) O (le_S (S O) (S O) (le_n (S O))))))) y (S m))) (@exist nat (fun k : nat => lt k (S (S O))) O (le_S (S O) (S O) (le_n (S O))))))).
move=> H5.
elim (H4 H5).
move=> H5.
elim (excluded_middle_informative (@ex nat (fun (n : nat) => forall (m : nat) (_ : ge m n), @eq (Count (S (S O))) (sw (@proj1_sig (forall _ : nat, Count (S (S O))) (fun (g : forall _ : nat, Count (S (S O))) => forall n0 : nat, @ex nat (fun (m0 : nat) => and (ge m0 n0) (@eq (Count (S (S O))) (g m0) (@exist nat (fun (k : nat) => lt k (S (S O))) O (le_S (S O) (S O) (le_n (S O))))))) y (S m))) (@exist nat (fun (k : nat) => lt k (S (S O))) (S O) (le_n (S (S O))))))).
move=> H6.
apply functional_extensionality.
elim.
elim (le_lt_or_eq (proj1_sig (proj1_sig y O)) 1 (le_S_n (proj1_sig (proj1_sig y O)) 1 (proj2_sig (proj1_sig y O)))).
move=> H7.
apply sig_map.
elim H3.
elim (le_lt_or_eq (proj1_sig (proj1_sig y O)) O (le_S_n (proj1_sig (proj1_sig y O)) O H7)).
move=> H8.
elim (le_not_lt O (proj1_sig (proj1_sig y O)) (le_0_n (proj1_sig (proj1_sig y O))) H8).
move=> H8.
apply sig_map.
apply H8.
move=> H7.
apply sig_map.
rewrite H7.
reflexivity.
move=> n H7.
unfold sw.
elim (excluded_middle_informative (proj1_sig y (S n) = exist (fun (k : nat) => k < 2) 1 (le_n 2))).
move=> H8.
elim (excluded_middle_informative (@eq (Count (S (S O))) (@exist nat (fun (k : nat) => lt k (S (S O))) O (le_S (S O) (S O) (le_n (S O)))) (@exist nat (fun (k : nat) => lt k (S (S O))) (S O) (le_n (S (S O)))))).
move=> H9.
elim (lt_irrefl (proj1_sig (exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))))).
rewrite {2} H9.
apply (le_n 1).
move=> H9.
rewrite H8.
reflexivity.
move=> H8.
elim (excluded_middle_informative (@eq (Count (S (S O))) (@exist nat (fun (k : nat) => lt k (S (S O))) (S O) (le_n (S (S O)))) (@exist nat (fun (k : nat) => lt k (S (S O))) (S O) (le_n (S (S O)))))).
move=> H9.
elim (le_lt_or_eq (proj1_sig (proj1_sig y (S n))) 1 (le_S_n (proj1_sig (proj1_sig y (S n))) 1 (proj2_sig (proj1_sig y (S n))))).
move=> H10.
apply sig_map.
elim (le_lt_or_eq (proj1_sig (proj1_sig y (S n))) O (le_S_n (proj1_sig (proj1_sig y (S n))) O H10)).
move=> H11.
elim (le_not_lt O (proj1_sig (proj1_sig y (S n))) (le_0_n (proj1_sig (proj1_sig y (S n)))) H11).
move=> H11.
rewrite H11.
reflexivity.
move=> H10.
elim H8.
apply sig_map.
apply H10.
elim.
reflexivity.
elim.
elim H2.
move=> n H6.
exists n.
move=> m H7.
unfold sw.
elim (excluded_middle_informative (proj1_sig y (S m) = exist (fun (k : nat) => k < 2) 1 (le_n 2))).
rewrite (H6 (S m) (le_S n m H7)).
apply.
move=> H8.
reflexivity.
elim (excluded_middle_informative (exists (n : nat), forall (m : nat), m >= n -> proj1_sig y m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))).
move=> H2 H3.
elim (H3 H2).
move=> H2 H3.
elim (excluded_middle_informative (exists (n : nat), forall (m : nat), m >= n -> proj1_sig y m = exist (fun (k : nat) => k < 2) 1 (le_n 2))).
elim.
move=> n H4.
elim (proj2_sig y n).
move=> m H5.
elim (lt_irrefl (proj1_sig (proj1_sig y m))).
rewrite {1} (proj2 H5).
rewrite (H4 m (proj1 H5)).
apply (le_n 1).
move=> H4.
reflexivity.
move=> f.
unfold In.
elim (excluded_middle_informative (exists (n : nat), forall (m : nat), m >= n -> f m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))).
elim.
move=> n H1 m.
exists (S (max n m)).
apply conj.
apply (le_S m (max n m) (Nat.le_max_r n m)).
apply (H1 (max n m) (Nat.le_max_l n m)).
move=> H1.
elim (excluded_middle_informative (exists (n : nat), forall (m : nat), m >= n -> f m = exist (fun (k : nat) => k < 2) 1 (le_n 2))).
elim.
move=> n H2 m.
exists (S (max n m)).
apply conj.
apply (le_S m (max n m) (Nat.le_max_r n m)).
rewrite (H2 (max n m) (Nat.le_max_l n m)).
unfold sw.
elim (excluded_middle_informative (@eq (Count (S (S O))) (@exist nat (fun k : nat => lt k (S (S O))) (S O) (le_n (S (S O)))) (@exist nat (fun k : nat => lt k (S (S O))) (S O) (le_n (S (S O)))))).
move=> H3.
reflexivity.
elim.
reflexivity.
move=> H2 n.
apply NNPP.
move=> H3.
apply H2.
exists n.
move=> m H4.
elim (le_lt_or_eq (proj1_sig (f m)) 1 (le_S_n (proj1_sig (f m)) 1 (proj2_sig (f m)))).
move=> H5.
elim H3.
exists m.
apply conj.
apply H4.
elim (le_lt_or_eq (proj1_sig (f m)) O (le_S_n (proj1_sig (f m)) O H5)).
move=> H6.
elim (le_not_lt O (proj1_sig (f m)) (le_0_n (proj1_sig (f m))) H6).
move=> H6.
apply sig_map.
apply H6.
move=> H5.
apply sig_map.
apply H5.
apply (Formula_1_3 {f : nat -> Count 2 | forall (n : nat), exists (m : nat), m >= n /\ f m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))} {r : R | (0 <= r < 1)%R} R).
suff: (forall (f : nat -> Count 2), (forall (n : nat), exists (m : nat), (m >= n /\ f m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))) -> exists (x : {r : R | (0 <= r < 1)%R}), Un_cv (sum_f_R0 (fun (n : nat) => INR (proj1_sig (f n)) / pow 2 (S n))%R) (proj1_sig x)).
move=> H1.
suff: (forall (f1 f2 : nat -> Count 2) (x : {r : R | (0 <= r < 1)%R}), (forall (n : nat), exists (m : nat), (m >= n /\ f1 m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))) -> (forall (n : nat), exists (m : nat), (m >= n /\ f2 m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))) -> Un_cv (sum_f_R0 (fun (n : nat) => INR (proj1_sig (f1 n)) / pow 2 (S n))%R) (proj1_sig x) -> Un_cv (sum_f_R0 (fun (n : nat) => INR (proj1_sig (f2 n)) / pow 2 (S n))%R) (proj1_sig x) -> f1 = f2).
move=> H2.
suff: (forall (f : nat -> Count 2), (forall (n : nat), exists (m : nat), (m >= n /\ f m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))) -> {x : {r : R | (0 <= r < 1)%R} | Un_cv (sum_f_R0 (fun (n : nat) => INR (proj1_sig (f n)) / pow 2 (S n))%R) (proj1_sig x)}).
move=> H3.
suff: (forall (x : {r : R | (0 <= r < 1)%R}), {g : {f : nat -> Count 2 | forall (n : nat), exists (m : nat), m >= n /\ f m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))} | Un_cv (sum_f_R0 (fun (n : nat) => INR (proj1_sig (proj1_sig g n)) / pow 2 (S n))%R) (proj1_sig x)}).
move=> H4.
exists (fun (g : {f : nat -> Count 2 | forall (n : nat), exists (m : nat), m >= n /\ f m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))}) => proj1_sig (H3 (proj1_sig g) (proj2_sig g))).
exists (fun (x : {r : R | (0 <= r < 1)%R}) => proj1_sig (H4 x)).
apply conj.
move=> x.
apply sig_map.
apply (H2 (proj1_sig (proj1_sig (H4 (proj1_sig (H3 (proj1_sig x) (proj2_sig x)))))) (proj1_sig x) (proj1_sig (H3 (proj1_sig x) (proj2_sig x))) (proj2_sig (proj1_sig (H4 (proj1_sig (H3 (proj1_sig x) (proj2_sig x)))))) (proj2_sig x) (proj2_sig (H4 (proj1_sig (H3 (proj1_sig x) (proj2_sig x))))) (proj2_sig (H3 (proj1_sig x) (proj2_sig x)))).
move=> y.
apply sig_map.
apply (Proposition_2_3 (sum_f_R0 (fun (n : nat) => (INR (proj1_sig (proj1_sig (proj1_sig (H4 y)) n)) / 2 ^ (S n))%R)) (proj1_sig (proj1_sig (H3 (proj1_sig (proj1_sig (H4 y))) (proj2_sig (proj1_sig (H4 y)))))) (proj1_sig y) (proj2_sig (H3 (proj1_sig (proj1_sig (H4 y))) (proj2_sig (proj1_sig (H4 y))))) (proj2_sig (H4 y))).
move=> x.
apply (constructive_definite_description (fun (g : {f : nat -> Count 2 | forall (n : nat), exists (m : nat), m >= n /\ f m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))}) => Un_cv (sum_f_R0 (fun (n : nat) => (INR (proj1_sig (proj1_sig g n)) / 2 ^ (S n))%R)) (proj1_sig x))).
apply (proj1 (unique_existence (fun (g : {f : nat -> Count 2 | forall (n : nat), exists (m : nat), m >= n /\ f m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))}) => Un_cv (sum_f_R0 (fun (n : nat) => (INR (proj1_sig (proj1_sig g n)) / 2 ^ (S n))%R)) (proj1_sig x)))).
apply conj.
elim (Theorem_3_9_sub 2 (le_n 2) (proj1_sig x)).
simpl.
move=> an H4.
elim (classic (forall (n : nat), exists (m : nat), m >= n /\ an m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))).
move=> H5.
exists (exist (fun (f : nat -> Count 2) => forall (n : nat), exists (m : nat), m >= n /\ f m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))) an H5).
simpl.
suff: (let An := fun (n : nat) => match n with
  | 0 => IZR (Floor (proj1_sig x))
  | S n1 => (INR (proj1_sig (an n1)) / INR 2 ^ S n1)%R
end in Un_cv (sum_f_R0 (fun n : nat => (INR (proj1_sig (an n)) / (2 * 2 ^ n))%R)) (proj1_sig x)).
apply.
move=> An.
suff: ((fun (n : nat) => (INR (proj1_sig (an n)) / (2 * 2 ^ n))%R) = (fun (n : nat) => An (n + S O))).
move=> H6.
rewrite H6.
suff: (proj1_sig x = proj1_sig x - (sum_f_R0 An O))%R.
move=> H7.
rewrite H7.
apply (proj1 (H0 An (proj1_sig x) O) H4).
simpl.
rewrite - (Floor_unique (proj1_sig x) 0).
rewrite (Rminus_0_r (proj1_sig x)).
reflexivity.
apply (proj2_sig x).
unfold An.
apply functional_extensionality.
move=> n.
rewrite (plus_comm n 1).
reflexivity.
move=> H5.
suff: (exists (n : nat), an n = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)) /\ (forall (m : nat), m > n -> proj1_sig (an m) = 1)).
elim.
move=> n H6.
suff: (In (nat -> Count 2) (fun (f : nat -> Count 2) => forall (n0 : nat), exists (m : nat), m >= n0 /\ f m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))) (fun (k : nat) => match excluded_middle_informative (k < n) with
  | left _ => an k
  | right _ => match excluded_middle_informative (k = n) with
    | left _ => exist (fun (k : nat) => k < 2) 1 (le_n 2)
    | right _ => exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))
  end
end)).
move=> H7.
exists (exist (fun (f : nat -> Count 2) => forall (n0 : nat), exists (m : nat), m >= n0 /\ f m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))) (fun (k : nat) => match excluded_middle_informative (k < n) with
  | left _ => an k
  | right _ => match excluded_middle_informative (k = n) with
    | left _ => exist (fun (k : nat) => k < 2) 1 (le_n 2)
    | right _ => exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))
  end
end) H7).
simpl.
suff: (Un_cv (sum_f_R0 (fun n : nat => (INR (proj1_sig (an n)) / (2 * 2 ^ n))%R)) (proj1_sig x)).
move=> H8.
suff: (forall (m : nat), (m >= n)%nat -> sum_f_R0 (fun (k : nat) => (INR (proj1_sig (match excluded_middle_informative (k < n) with
  | left _ => an k
  | right _ => match excluded_middle_informative (k = n) with
    | left _ => exist (fun (k : nat) => k < 2) 1 (le_n 2)
    | right _ => exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))
  end
end)%nat) / (2 * 2 ^ k))%R) m = sum_f_R0 (fun (n : nat) => (INR (proj1_sig (an n)) / (2 * 2 ^ n))) m + / (2 ^ (S m)))%R.
move=> H9 eps H10.
elim (H8 (eps * / 2)%R (eps2_Rgt_R0 eps H10)).
move=> N1 H11.
elim (Formula_3_9_2 (eps * / 2)%R (eps2_Rgt_R0 eps H10)).
move=> N2 H12.
exists (max n (max N1 N2)).
move=> k H13.
rewrite (H9 k (le_trans n (max n (max N1 N2)) k (Nat.le_max_l n (max N1 N2)) H13)).
unfold R_dist.
unfold Rminus.
rewrite Rplus_assoc.
rewrite (Rplus_comm (/ 2 ^ S k) (- proj1_sig x)).
rewrite - Rplus_assoc.
rewrite - (Rminus_0_r (/ 2 ^ S k)).
rewrite - (Rmult_1_l (/ 2 ^ S k)).
apply (Rle_lt_trans (Rabs (sum_f_R0 (fun (n0 : nat) => INR (proj1_sig (an n0)) / (2 * 2 ^ n0)) k + - proj1_sig x + (1 / 2 ^ S k - 0)))%R (R_dist (sum_f_R0 (fun (n0 : nat) => INR (proj1_sig (an n0)) / (2 * 2 ^ n0)) k) (proj1_sig x) + R_dist (1 / 2 ^ S k) 0)%R eps).
apply Rabs_triang.
rewrite - (eps2 eps).
apply Rplus_lt_compat.
apply (H11 k (le_trans N1 (max n (max N1 N2)) k (le_trans N1 (max N1 N2) (max n (max N1 N2)) (Nat.le_max_l N1 N2) (Nat.le_max_r n (max N1 N2))) H13)).
apply (H12 (S k) (le_S N2 k (le_trans N2 (max n (max N1 N2)) k (le_trans N2 (max N1 N2) (max n (max N1 N2)) (Nat.le_max_r N1 N2) (Nat.le_max_r n (max N1 N2))) H13))).
suff: (forall (m : nat), (m < n)%nat -> sum_f_R0 (fun (k : nat) => (INR (proj1_sig (match excluded_middle_informative (k < n) with
  | left _ => an k
  | right _ => match excluded_middle_informative (k = n) with
    | left _ => exist (fun (k : nat) => k < 2) 1 (le_n 2)
    | right _ => exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))
  end
end))%nat / (2 * 2 ^ k))) m = sum_f_R0 (fun (n0 : nat) => INR (proj1_sig (an n0)) / (2 * 2 ^ n0)) m)%R.
move=> H9.
elim.
move=> H10.
unfold sum_f_R0.
elim (excluded_middle_informative (0 < n)%nat).
move=> H11.
elim (le_not_lt n 0 H10 H11).
move=> H11.
elim (excluded_middle_informative (0%nat = n)).
move=> H12.
rewrite {7} H12.
rewrite (proj1 H6).
simpl.
unfold Rdiv.
rewrite (Rmult_0_l (/ (2 * 1))).
rewrite (Rplus_0_l (/ (2 * 1))).
apply (Rmult_1_l (/ (2 * 1))).
elim.
elim (le_lt_or_eq n 0 H10).
move=> H12.
elim (le_not_lt O n (le_0_n n) H12).
move=> H12.
rewrite H12.
reflexivity.
move=> k H10 H11.
simpl.
elim (le_lt_or_eq n (S k)).
move=> H12.
rewrite (H10 (le_S_n n k H12)).
elim (excluded_middle_informative (S k < n)%nat).
move=> H13.
elim (le_not_lt n (S k) H11 H13).
move=> H13.
elim (excluded_middle_informative (S k = n)%nat).
move=> H14.
elim H13.
rewrite H14.
rewrite - {2} H14.
apply H12.
move=> H14.
simpl.
rewrite (proj2 H6 (S k) H12).
unfold Rdiv.
rewrite (Rmult_0_l (/ (2 * (2 * 2 ^ k)))).
rewrite Rplus_0_r.
rewrite Rplus_assoc.
suff: (INR 1 * / (2 * (2 * 2 ^ k)) + / (2 * (2 * 2 ^ k)) = / (2 * 2 ^ k))%R.
move=> H15.
rewrite H15.
reflexivity.
unfold INR.
rewrite Rmult_1_l.
rewrite (Rinv_mult_distr 2 (2 * 2 ^ k) Two_Neq_Zero (Two_Pow_Neq_Zero (S k))).
rewrite - (Rmult_plus_distr_r (/ 2)).
rewrite - (Rmult_1_r (/ 2)).
rewrite - (Rmult_plus_distr_l (/ 2)).
rewrite (Rinv_l (1 + 1)).
apply (Rmult_1_l (/ (2 ^ (S k)))).
apply Two_Neq_Zero.
move=> H12.
rewrite (H9 k).
rewrite - H12.
rewrite (proj1 H6).
elim (excluded_middle_informative (n < n)).
move=> H13.
elim (lt_irrefl n H13).
move=> H13.
elim (excluded_middle_informative (n = n)).
move=> H14.
simpl.
unfold Rdiv.
rewrite (Rmult_0_l (/ (2 * (2 * 2 ^ k)))).
rewrite (Rmult_1_l (/ (2 * (2 * 2 ^ k)))).
rewrite Rplus_0_r.
reflexivity.
elim.
reflexivity.
rewrite H12.
apply (le_n (S k)).
apply H11.
elim.
simpl.
move=> H9.
elim (excluded_middle_informative (0 < n)).
move=> H10.
reflexivity.
move=> H10.
elim (H10 H9).
move=> k H9 H10.
simpl.
rewrite H9.
elim (excluded_middle_informative (S k < n)).
move=> H11.
reflexivity.
move=> H11.
elim (H11 H10).
apply (le_trans (S k) (S (S k)) n (le_S (S k) (S k) (le_n (S k))) H10).
suff: (let An := fun (n : nat) => match n with
  | 0 => IZR (Floor (proj1_sig x))
  | S n1 => (INR (proj1_sig (an n1)) / INR 2 ^ S n1)%R
end in Un_cv (sum_f_R0 (fun n : nat => (INR (proj1_sig (an n)) / (2 * 2 ^ n))%R)) (proj1_sig x)).
apply.
move=> An.
suff: ((fun (n : nat) => (INR (proj1_sig (an n)) / (2 * 2 ^ n))%R) = (fun (n : nat) => An (n + S O))).
move=> H8.
rewrite H8.
suff: (proj1_sig x = proj1_sig x - (sum_f_R0 An O))%R.
move=> H9.
rewrite H9.
apply (proj1 (H0 An (proj1_sig x) O) H4).
simpl.
rewrite - (Floor_unique (proj1_sig x) 0).
rewrite (Rminus_0_r (proj1_sig x)).
reflexivity.
apply (proj2_sig x).
unfold An.
apply functional_extensionality.
move=> k.
rewrite (plus_comm k 1).
reflexivity.
move=> k.
exists (max (S n) k).
apply conj.
apply (Nat.le_max_r (S n) k).
elim (excluded_middle_informative (max (S n) k < n)).
move=> H7.
elim (le_not_lt n (max (S n) k) (le_trans n (S n) (max (S n) k) (le_S n n (le_n n)) (Nat.le_max_l (S n) k)) H7).
move=> H7.
elim (excluded_middle_informative (max (S n) k = n)).
move=> H8.
elim (lt_irrefl n).
rewrite - {2} H8.
apply (Nat.le_max_l (S n) k).
move=> H8.
reflexivity.
suff: (exists (n : nat), an n = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))).
move=> H6.
apply NNPP.
move=> H7.
apply H5.
move=> n.
apply NNPP.
move=> H8.
apply H7.
elim (min_nat_exist (fun (l : nat) => forall (m : nat), m > l -> proj1_sig (an m) = 1)).
move=> k H9.
exists k.
apply conj.
elim (le_lt_or_eq O k (le_0_n k)).
move=> H10.
apply NNPP.
move=> H11.
suff: (exists (l : nat), S l = k).
elim.
move=> l H12.
apply (lt_irrefl l).
unfold lt.
rewrite H12.
apply (proj2 H9 l).
move=> p H13.
elim (le_lt_or_eq k p).
move=> H14.
apply (proj1 H9 p H14).
move=> H14.
elim (le_lt_or_eq (proj1_sig (an p)) 1).
move=> H15.
elim H11.
apply sig_map.
elim (le_lt_or_eq (proj1_sig (an p)) O (le_S_n (proj1_sig (an p)) O H15)).
move=> H16.
elim (le_not_lt O (proj1_sig (an p)) (le_0_n (proj1_sig (an p))) H16).
rewrite H14.
apply.
apply.
apply (le_S_n (proj1_sig (an p)) 1 (proj2_sig (an p))).
rewrite - H12.
apply H13.
suff: (O < k).
elim k.
move=> H12.
elim (lt_irrefl O H12).
move=> p H12 H13.
exists p.
reflexivity.
apply H10.
move=> H10.
elim H6.
move=> l H11.
elim (le_lt_or_eq O l (le_0_n l)).
move=> H12.
elim (lt_irrefl (proj1_sig (an l))).
rewrite {1} H11.
rewrite (proj1 H9 l).
apply (le_n 1).
rewrite - H10.
apply H12.
move=> H12.
rewrite - H10.
rewrite {2} H12.
apply H11.
apply (proj1 H9).
apply (Inhabited_intro nat (fun (l : nat) => forall (m : nat), m > l -> proj1_sig (an m) = 1) n).
move=> p H9.
apply NNPP.
move=> H10.
apply H8.
exists p.
apply conj.
apply (le_trans n (S n) p (le_S n n (le_n n)) H9).
elim (le_lt_or_eq (proj1_sig (an p)) 1 (le_S_n (proj1_sig (an p)) 1 (proj2_sig (an p)))).
move=> H11.
apply sig_map.
elim (le_lt_or_eq (proj1_sig (an p)) O (le_S_n (proj1_sig (an p)) O H11)).
move=> H12.
elim (le_not_lt O (proj1_sig (an p)) (le_0_n (proj1_sig (an p))) H12).
apply.
move=> H11.
elim H10.
apply H11.
apply NNPP.
move=> H6.
apply (Rlt_irrefl (proj1_sig x)).
rewrite {2} (Proposition_2_3 (sum_f_R0 (fun (n : nat) => match n with
  | 0 => IZR (Floor (proj1_sig x))
  | S n1 => (INR (proj1_sig (an n1)) / ((1 + 1) * (1 + 1) ^ n1))%R
end)) (proj1_sig x) 1 H4).
apply (proj2 (proj2_sig x)).
apply (proj2 (H0 (fun (n : nat) => match n with
  | 0 => IZR (Floor (proj1_sig x))
  | S n1 => (INR (proj1_sig (an n1)) / ((1 + 1) * (1 + 1) ^ n1))%R
end) 1%R O)).
simpl.
rewrite - (Floor_unique (proj1_sig x) 0).
rewrite (Rminus_0_r 1).
suff: (sum_f_R0 (fun (n : nat) => match n + 1 with
  | 0 => 0%R
  | S n1 => (INR (proj1_sig (an n1)) / ((1 + 1) * (1 + 1) ^ n1))%R
end) = (fun (n : nat) => 1 - / (pow 2 (S n)))%R).
move=> H7.
rewrite H7.
rewrite - {2} (Rminus_0_r 1).
apply (Theorem_2_5_1_minus (fun (n : nat) => 1%R) (fun (n : nat) => / (pow 2 (S n)))%R 1 0).
move=> eps H8.
exists O.
move=> n H9.
unfold R_dist.
unfold Rminus.
rewrite (Rplus_opp_r 1).
rewrite Rabs_R0.
apply H8.
move=> eps H8.
elim (Formula_3_9_2 eps H8).
move=> N H9.
exists N.
move=> n H10.
rewrite - (Rmult_1_l (/ 2 ^ S n)%R).
apply (H9 (S n) (le_trans N n (S n) H10 (le_S n n (le_n n)))).
suff: (forall (n : nat), proj1_sig (an n) = 1).
move=> H7.
apply functional_extensionality.
elim.
simpl.
rewrite (H7 O).
simpl.
unfold Rdiv.
rewrite (Rmult_1_l (/ ((1 + 1) * 1))).
rewrite (Rmult_1_r (1 + 1)).
rewrite - {3} (Rinv_r (1 + 1)).
rewrite (Rmult_plus_distr_r 1 1).
rewrite (Rmult_1_l (/ (1 + 1))).
unfold Rminus.
rewrite (Rplus_assoc (/ (1 + 1)) (/ (1 + 1)) (- / (1 + 1))).
rewrite (Rplus_opp_r (/ (1 + 1))).
rewrite (Rplus_0_r (/ (1 + 1))).
reflexivity.
apply Two_Neq_Zero.
move=> n H8.
simpl.
rewrite H8.
rewrite (H7 (n + 1)).
simpl.
rewrite - (Rmult_1_l (/ (2 * 2^ n))).
rewrite - {2} (Rinv_r 2 Two_Neq_Zero).
rewrite (Rmult_assoc 2 (/ 2) (/ (2 * 2 ^ n))).
rewrite - (Rinv_mult_distr 2 (2 * 2 ^ n) Two_Neq_Zero (Two_Pow_Neq_Zero (S n))).
unfold Rminus.
rewrite Ropp_mult_distr_l.
unfold Rdiv.
rewrite Rplus_assoc.
suff: (2 * (2 * 2 ^ n) = (1 + 1) * (1 + 1) ^ (n + 1))%R.
move=> H9.
rewrite H9.
rewrite - (Rmult_plus_distr_r (- (2)) 1).
unfold IZR.
unfold IPR.
unfold IPR_2.
rewrite (Ropp_plus_distr 1 1).
rewrite (Rplus_assoc (- (1)) (- (1)) 1).
rewrite (Rplus_opp_l 1).
rewrite (Rplus_0_r (- (1))).
rewrite Ropp_mult_distr_l_reverse.
rewrite Rmult_1_l.
reflexivity.
rewrite (plus_comm n 1).
reflexivity.
move=> n.
apply NNPP.
move=> H7.
apply H6.
exists n.
apply sig_map.
elim (le_lt_or_eq (proj1_sig (an n)) 1 (le_S_n (proj1_sig (an n)) 1 (proj2_sig (an n)))).
move=> H8.
elim (le_lt_or_eq (proj1_sig (an n)) O (le_S_n (proj1_sig (an n)) O H8)).
move=> H9.
elim (le_not_lt O (proj1_sig (an n)) (le_0_n (proj1_sig (an n))) H9).
apply.
move=> H8.
elim H7.
apply H8.
apply (proj2_sig x).
move=> g1 g2 H4 H5.
apply sig_map.
apply (H2 (proj1_sig g1) (proj1_sig g2) x (proj2_sig g1) (proj2_sig g2) H4 H5).
move=> f H3.
apply constructive_definite_description.
apply (proj1 (unique_existence (fun (x : {r : R | (0 <= r < 1)%R}) => Un_cv (sum_f_R0 (fun n : nat => (INR (proj1_sig (f n)) / 2 ^ S n)%R)) (proj1_sig x)))).
apply conj.
apply (H1 f H3).
move=> r1 r2 H4 H5.
apply sig_map.
apply (Proposition_2_3 (sum_f_R0 (fun (n : nat) => (INR (proj1_sig (f n)) / 2 ^ S n)%R)) (proj1_sig r1) (proj1_sig r2) H4 H5).
suff: (forall (g1 g2 : nat -> Count 2) (x : {r : R | (0 <= r < 1)%R}), (forall (n : nat), exists (m : nat), m >= n /\ g1 m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))) -> (forall (n : nat), exists (m : nat), m >= n /\ g2 m = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))) -> Un_cv (sum_f_R0 (fun (n : nat) => (INR (proj1_sig (g1 n)) / 2 ^ S n)%R)) (proj1_sig x) -> Un_cv (sum_f_R0 (fun (n : nat) => (INR (proj1_sig (g2 n)) / 2 ^ S n)%R)) (proj1_sig x) -> (exists (k : nat), is_min_nat (fun (n : nat) => g1 n <> g2 n) k /\ proj1_sig (g1 k) < proj1_sig (g2 k)) -> False).
move=> H2 g1 g2 x H3 H4 H5 H6.
apply functional_extensionality.
apply NNPP.
move=> H7.
elim (min_nat_exist (fun (n : nat) => g1 n <> g2 n)).
move=> n H8.
elim (le_or_lt (proj1_sig (g1 n)) (proj1_sig (g2 n))).
move=> H9.
elim (le_lt_or_eq (proj1_sig (g1 n)) (proj1_sig (g2 n)) H9).
move=> H10.
apply (H2 g1 g2 x H3 H4 H5 H6).
exists n.
apply conj.
apply H8.
apply H10.
move=> H10.
apply (proj1 H8).
apply sig_map.
apply H10.
move=> H9.
apply (H2 g2 g1 x H4 H3 H6 H5).
exists n.
apply conj.
suff: ((fun (k : nat) => g2 k <> g1 k) = (fun (k : nat) => g1 k <> g2 k)).
move=> H10.
rewrite H10.
apply H8.
apply Extensionality_Ensembles.
apply conj.
move=> k H10 H11.
apply H10.
rewrite H11.
reflexivity.
move=> k H10 H11.
apply H10.
rewrite H11.
reflexivity.
apply H9.
apply NNPP.
move=> H8.
apply H7.
move=> m.
apply NNPP.
move=> H9.
apply H8.
apply (Inhabited_intro nat (fun (n : nat) => g1 n <> g2 n) m H9).
move=> g1 g2 x H2 H3 H4 H5.
elim.
move=> N H6.
elim (H2 (S N)).
move=> M H7.
suff: (forall (k : nat), (k >= M)%nat -> sum_f_R0 (fun (n : nat) => (INR (proj1_sig (g2 n)) / 2 ^ S n)%R) k - sum_f_R0 (fun (n : nat) => (INR (proj1_sig (g1 n)) / 2 ^ S n)%R) k >= / (2 ^ (S M)))%R.
move=> H8.
elim (Rlt_irrefl 0).
apply (Rlt_le_trans 0 (/ 2 ^ S M) 0).
apply (Rinv_0_lt_compat (2 ^ S M) (Two_Pow_Gt_Zero (S M))).
apply (Theorem_2_6_2 (fun (k : nat) => / 2 ^ S M) (fun (k : nat) => (sum_f_R0 (fun (n : nat) => INR (proj1_sig (g2 n)) / 2 ^ S n) k - sum_f_R0 (fun (n : nat) => INR (proj1_sig (g1 n)) / 2 ^ S n) k)) (/ 2 ^ S M) 0)%R.
move=> eps H9.
exists O.
move=> n H10.
rewrite (proj2 (R_dist_refl (/ 2 ^ S M) (/ 2 ^ S M))).
apply H9.
reflexivity.
rewrite - (Rplus_opp_r (proj1_sig x)).
apply (Theorem_2_5_1_minus (sum_f_R0 (fun (n : nat) => INR (proj1_sig (g2 n)) / 2 ^ S n)) (sum_f_R0 (fun (n : nat) => INR (proj1_sig (g1 n)) / 2 ^ S n)) (proj1_sig x) (proj1_sig x) H5 H4)%R.
exists M.
move=> n H9.
apply Rge_le.
apply (H8 n H9).
suff: (forall (k : nat), k >= M -> (sum_f_R0 (fun (n : nat) => INR (proj1_sig (g2 n)) / 2 ^ S n) k >= sum_f_R0 (fun (n : nat) => INR (proj1_sig (g1 n)) / 2 ^ S n) k + / 2 ^ S M + / 2 ^ S k)%R).
move=> H8 k H9.
apply Rle_ge.
apply (Rplus_le_reg_r (sum_f_R0 (fun (n : nat) => INR (proj1_sig (g1 n)) / 2 ^ S n) k)%R).
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_l.
apply Rge_le.
rewrite Rplus_0_r.
rewrite (Rplus_comm (/ 2 ^ S M)).
apply (Rge_trans (sum_f_R0 (fun (n : nat) => INR (proj1_sig (g2 n)) / 2 ^ S n) k) (sum_f_R0 (fun (n : nat) => INR (proj1_sig (g1 n)) / 2 ^ S n) k + / 2 ^ S M + / 2 ^ S k) (sum_f_R0 (fun (n : nat) => INR (proj1_sig (g1 n)) / 2 ^ S n) k + / 2 ^ S M) (H8 k H9))%R.
rewrite - {2} (Rplus_0_r (sum_f_R0 (fun (n : nat) => INR (proj1_sig (g1 n)) / 2 ^ S n) k + / 2 ^ S M))%R.
apply Rplus_ge_compat_l.
left.
apply (Rinv_0_lt_compat (2 ^ S k) (Two_Pow_Gt_Zero (S k))).
suff: (forall (k : nat), k >= N -> (sum_f_R0 (fun n : nat => INR (proj1_sig (g2 n)) / 2 ^ S n) k >= sum_f_R0 (fun n : nat => INR (proj1_sig (g1 n)) / 2 ^ S n) k + / 2 ^ S k)%R).
move=> H8.
elim.
move=> H9.
elim (le_not_lt O N (le_0_n N) (le_trans (S N) M O (proj1 H7) H9)).
move=> n H9 H10.
elim (le_lt_or_eq M (S n) H10).
move=> H11.
apply (Rge_trans (sum_f_R0 (fun (k : nat) => INR (proj1_sig (g2 k)) / 2 ^ S k) (S n)) (sum_f_R0 (fun (k : nat) => INR (proj1_sig (g2 k)) / 2 ^ S k) n))%R.
rewrite - (Rplus_0_r (sum_f_R0 (fun (k : nat) => INR (proj1_sig (g2 k)) / 2 ^ S k) n)%R).
apply Rplus_ge_compat_l.
rewrite - (Rmult_0_l 0).
apply Rmult_ge_compat.
right.
reflexivity.
right.
reflexivity.
apply Rle_ge.
apply (pos_INR (proj1_sig (g2 (S n)))).
left.
apply (Rinv_0_lt_compat (2 ^ S (S n)) (Two_Pow_Gt_Zero (S (S n)))).
apply (Rge_trans (sum_f_R0 (fun (k : nat) => INR (proj1_sig (g2 k)) / 2 ^ S k) n) ((sum_f_R0 (fun (k : nat) => INR (proj1_sig (g1 k)) / 2 ^ S k) n + / 2 ^ S (S n)) + / 2 ^ S M + / 2 ^ S (S n)))%R.
rewrite Rplus_assoc.
rewrite Rplus_assoc.
rewrite (Rplus_comm (/ 2 ^ S (S n)) (/ 2 ^ S M + / 2 ^ S (S n))).
rewrite (Rplus_assoc (/ 2 ^ S M) (/ 2 ^ S (S n)) (/ 2 ^ S (S n))).
rewrite - Rplus_assoc.
suff: (/ 2 ^ S (S n) + / 2 ^ S (S n) = / 2 ^ S n)%R.
move=> H12.
rewrite H12.
apply (H9 (le_S_n M n H11)).
rewrite - (Rmult_1_l (/ 2 ^ S (S n))).
rewrite - (Rmult_plus_distr_r 1 1 (/ 2 ^ S (S n))).
rewrite (Rinv_mult_distr 2 (2 ^ S n) Two_Neq_Zero (Two_Pow_Neq_Zero (S n))).
rewrite - Rmult_assoc.
rewrite (Rinv_r 2 Two_Neq_Zero).
apply (Rmult_1_l (/ 2 ^ S n)).
apply Rplus_ge_compat_r.
apply Rplus_ge_compat_r.
apply Rplus_ge_compat_l.
rewrite - (Rmult_1_l (/ 2 ^ S (S n))).
apply Rmult_ge_compat_r.
left.
apply (Rinv_0_lt_compat (2 ^ S (S n)) (Two_Pow_Gt_Zero (S (S n)))).
apply Rle_ge.
apply (le_INR (proj1_sig (g1 (S n))) 1 (le_S_n (proj1_sig (g1 (S n))) 1 (proj2_sig (g1 (S n))))).
move=> H11.
rewrite - (Rplus_0_r (sum_f_R0 (fun (k : nat) => INR (proj1_sig (g1 k)) / 2 ^ S k) (S n) + / 2 ^ S M + / 2 ^ S (S n))%R).
simpl.
apply Rplus_ge_compat.
suff: (INR (proj1_sig (g1 (S n))) = 0%R).
move=> H12.
rewrite H12.
unfold Rdiv.
rewrite Rmult_0_l.
rewrite Rplus_0_r.
rewrite H11.
rewrite Rplus_assoc.
suff: (/ 2 ^ S (S n) + / 2 ^ S (S n) = / 2 ^ S n)%R.
move=> H13.
rewrite H13.
apply (H8 n).
apply (le_S_n N n).
rewrite - H11.
apply (proj1 H7).
rewrite - (Rmult_1_l (/ 2 ^ S (S n))).
rewrite - (Rmult_plus_distr_r 1 1 (/ 2 ^ S (S n))).
rewrite (Rinv_mult_distr 2 (2 ^ S n) Two_Neq_Zero (Two_Pow_Neq_Zero (S n))).
rewrite - Rmult_assoc.
rewrite (Rinv_r 2 Two_Neq_Zero).
apply (Rmult_1_l (/ 2 ^ S n)).
rewrite - H11.
rewrite (proj2 H7).
reflexivity.
rewrite - (Rmult_0_l 0).
apply Rmult_ge_compat.
right.
reflexivity.
right.
reflexivity.
apply Rle_ge.
apply (pos_INR (proj1_sig (g2 (S n)))).
left.
apply (Rinv_0_lt_compat (2 ^ S (S n)) (Two_Pow_Gt_Zero (S (S n)))).
suff: (forall (k : nat), k < N -> (sum_f_R0 (fun (n : nat) => INR (proj1_sig (g2 n)) / 2 ^ S n) k = sum_f_R0 (fun (n : nat) => INR (proj1_sig (g1 n)) / 2 ^ S n) k)%R).
move=> H8.
suff: (proj1_sig (g1 N) = O).
move=> H9.
suff: (proj1_sig (g2 N) = 1).
move=> H10.
elim.
move=> H11.
simpl.
elim (le_lt_or_eq N O H11).
move=> H12.
elim (le_not_lt O N (le_0_n N) H12).
move=> H12.
rewrite - {2} H12.
rewrite - {3} H12.
rewrite H9.
rewrite H10.
simpl.
unfold Rdiv.
rewrite Rmult_0_l.
rewrite Rplus_0_l.
right.
apply Rmult_1_l.
move=> n H11 H12.
elim (le_lt_or_eq N (S n) H12).
move=> H13.
apply (Rge_trans (sum_f_R0 (fun (k : nat) => INR (proj1_sig (g2 k)) / 2 ^ S k) (S n)) (sum_f_R0 (fun (k : nat) => INR (proj1_sig (g2 k)) / 2 ^ S k) n))%R.
rewrite - (Rplus_0_r (sum_f_R0 (fun (k : nat) => INR (proj1_sig (g2 k)) / 2 ^ S k) n)%R).
apply Rplus_ge_compat_l.
rewrite - (Rmult_0_r 0).
apply Rmult_ge_compat.
right.
reflexivity.
right.
reflexivity.
apply Rle_ge.
apply (pos_INR (proj1_sig (g2 (S n)))).
left.
apply (Rinv_0_lt_compat (2 ^ S (S n)) (Two_Pow_Gt_Zero (S (S n)))).
apply (Rge_trans (sum_f_R0 (fun (k : nat) => INR (proj1_sig (g2 k)) / 2 ^ S k) n) (sum_f_R0 (fun (k : nat) => INR (proj1_sig (g1 k)) / 2 ^ S k) n + / 2 ^ S n))%R.
apply (H11 (le_S_n N n H13)).
simpl.
rewrite Rplus_assoc.
apply Rplus_ge_compat_l.
suff: (/ (2 ^ (S n)) = / (2 ^ (S (S n))) + / (2 ^ (S (S n))))%R.
move=> H14.
rewrite H14.
apply Rplus_ge_compat_r.
rewrite - (Rmult_1_l (/ 2 ^ S (S n))).
apply Rmult_ge_compat_r.
left.
apply (Rinv_0_lt_compat (2 ^ S (S n)) (Two_Pow_Gt_Zero (S (S n)))).
apply Rle_ge.
apply (le_INR (proj1_sig (g1 (S n))) 1 (le_S_n (proj1_sig (g1 (S n))) 1 (proj2_sig (g1 (S n))))).
rewrite - (Rmult_1_l (/ 2 ^ S (S n))).
rewrite - (Rmult_plus_distr_r 1 1 (/ 2 ^ S (S n))).
rewrite (Rinv_mult_distr 2 (2 ^ S n) Two_Neq_Zero (Two_Pow_Neq_Zero (S n))).
rewrite - Rmult_assoc.
rewrite (Rinv_r 2 Two_Neq_Zero).
rewrite (Rmult_1_l (/ 2 ^ S n)).
reflexivity.
move=> H13.
simpl.
rewrite - H13.
rewrite H9.
rewrite H10.
unfold Rdiv.
rewrite Rmult_1_l.
rewrite Rmult_0_l.
rewrite Rplus_0_r.
rewrite (H8 n).
right.
reflexivity.
rewrite H13.
apply (le_n (S n)).
elim (le_lt_or_eq 1 (proj1_sig (g2 N))).
move=> H10.
elim (lt_irrefl 2 (le_trans 3 (S (proj1_sig (g2 N))) 2 (le_n_S 2 (proj1_sig (g2 N)) H10) (proj2_sig (g2 N)))).
move=> H10.
rewrite {2} H10.
reflexivity.
rewrite - {1} H9.
apply (proj2 H6).
elim (le_lt_or_eq O (proj1_sig (g1 N)) (le_0_n (proj1_sig (g1 N)))).
move=> H9.
elim (lt_irrefl 1).
apply (le_trans 2 (S (proj1_sig (g1 N))) 1).
apply (le_n_S 1 (proj1_sig (g1 N)) H9).
apply (le_trans (S (proj1_sig (g1 N))) (proj1_sig (g2 N)) 1 (proj2 H6) (le_S_n (proj1_sig (g2 N)) 1 (proj2_sig (g2 N)))).
move=> H9.
rewrite {2} H9.
reflexivity.
elim.
move=> H8.
apply NNPP.
move=> H9.
elim (lt_irrefl O).
apply (le_trans 1 N O H8).
apply (proj2 (proj1 H6) O).
move=> H10.
apply H9.
simpl.
rewrite H10.
reflexivity.
move=> n H8 H9.
simpl.
apply NNPP.
move=> H10.
elim (lt_irrefl (S n)).
apply (le_trans (S (S n)) N (S n) H9).
apply (proj2 (proj1 H6) (S n)).
move=> H11.
apply H10.
rewrite (H8 (le_trans (S n) (S (S n)) N (le_S (S n) (S n) (le_n (S n))) H9)).
rewrite H11.
reflexivity.
move=> f H1.
elim (H1 O).
move=> N H2.
suff: (forall (k : nat), sum_f_R0 (fun (n : nat) => (INR (proj1_sig (f n)) / 2 ^ S n)%R) k <= 1 - / 2 ^ (S N))%R.
move=> H3.
elim (Theorem_3_1_1 (sum_f_R0 (fun (n : nat) => (INR (proj1_sig (f n)) / 2 ^ S n)%R))).
move=> s H4.
suff: (0 <= s < 1)%R.
move=> H5.
exists (exist (fun (r : R) => (0 <= r < 1)%R) s H5).
apply (proj1 H4).
apply conj.
apply (Theorem_2_6_Collorary_2 (sum_f_R0 (fun (n : nat) => (INR (proj1_sig (f n)) / 2 ^ S n)%R)) s 0 (proj1 H4)).
elim.
rewrite - (Rmult_0_r 0).
apply Rmult_le_compat.
right.
reflexivity.
right.
reflexivity.
apply (pos_INR (proj1_sig (f 0%nat))).
left.
simpl.
rewrite (Rmult_1_r 2).
apply (Rinv_0_lt_compat 2 Two_Gt_Zero).
move=> n H5.
simpl.
apply Rplus_le_le_0_compat.
apply H5.
rewrite - (Rmult_0_r 0).
apply Rmult_le_compat.
right.
reflexivity.
right.
reflexivity.
apply (pos_INR (proj1_sig (f (S n)))).
left.
apply (Rinv_0_lt_compat (2 ^ S (S n)) (Two_Pow_Gt_Zero (S (S n)))).
apply (Rle_lt_trans s (1 - / 2 ^ S N) 1).
apply (Theorem_2_6_Collorary_1 (sum_f_R0 (fun (n : nat) => (INR (proj1_sig (f n)) / 2 ^ S n)%R)) s (1 - / 2 ^ S N) (proj1 H4) H3).
rewrite - {2} (Rplus_0_r 1).
apply (Rplus_lt_compat_l 1 (- (/ 2 ^ S N)) 0)%R.
apply Ropp_lt_gt_0_contravar.
apply (Rinv_0_lt_compat (2 ^ S N) (Two_Pow_Gt_Zero (S N))).
exists (1 - / 2 ^ S N)%R.
move=> r.
elim.
move=> x H4 y H5.
rewrite H5.
apply (H3 x).
move=> n.
rewrite - (Rplus_0_r (sum_f_R0 (fun (k : nat) => INR (proj1_sig (f k)) / 2 ^ S k) n))%R.
apply Rplus_le_compat_l.
rewrite - (Rmult_0_r 0).
apply Rmult_le_compat.
right.
reflexivity.
right.
reflexivity.
apply (pos_INR (proj1_sig (f (S n)))).
left.
apply (Rinv_0_lt_compat (2 ^ S (S n)) (Two_Pow_Gt_Zero (S (S n)))).
suff: (forall (k : nat), ((sum_f_R0 (fun (n : nat) => INR (proj1_sig (f n)) / 2 ^ S n) k <= 1 - / 2 ^ S k))%R).
move=> H3.
suff: (forall (k : nat), k >= N -> ((sum_f_R0 (fun (n : nat) => INR (proj1_sig (f n)) / 2 ^ S n) k <= 1 - / 2 ^ S N - / 2 ^ S k))%R).
move=> H4 k.
elim (le_or_lt N k).
move=> H5.
apply (Rle_trans (sum_f_R0 (fun (n : nat) => INR (proj1_sig (f n)) / 2 ^ S n) k) (1 - / 2 ^ S N - / 2 ^ S k))%R.
apply (H4 k H5).
rewrite - {2} (Rplus_0_r (1 - / 2 ^ S N)).
apply Rplus_le_compat_l.
left.
apply Ropp_lt_gt_0_contravar.
apply (Rinv_0_lt_compat (2 ^ S k) (Two_Pow_Gt_Zero (S k))).
move=> H5.
apply (Rle_trans (sum_f_R0 (fun (n : nat) => INR (proj1_sig (f n)) / 2 ^ S n) k) (1 - / 2 ^ S k) (1 - / 2 ^ S N) (H3 k))%R.
apply (Rplus_le_compat_l 1 (- (/ 2 ^ S k)) (- (/ 2 ^ S N))).
apply (Ropp_le_contravar (/ 2 ^ S k) (/ 2 ^ S N)).
suff: (2 ^ S k <= 2 ^ S N)%R.
elim.
move=> H6.
left.
apply Rinv_lt_contravar.
apply (Rmult_lt_0_compat (2 ^ S k) (2 ^ S N) (Two_Pow_Gt_Zero (S k)) (Two_Pow_Gt_Zero (S N))).
apply H6.
move=> H6.
rewrite H6.
right.
reflexivity.
elim (le_trans k (S k) N (le_S k k (le_n k)) H5).
right.
reflexivity.
move=> m H6 H7.
apply (Rle_trans (2 ^ S k) (2 ^ S m) (2 ^ S (S m)) H7).
rewrite - (Rplus_0_r (2 ^ S m)).
suff: (2 ^ S (S m) = 2 ^ S m + 2 ^ S m)%R.
move=> H8.
rewrite H8.
apply (Rplus_le_compat_l (2 ^ S m) 0 (2 ^ S m)).
left.
apply (Two_Pow_Gt_Zero (S m)).
rewrite - (Rmult_1_l (2 ^ S m)).
apply (Rmult_plus_distr_r 1 1 (2 ^ S m)).
elim.
move=> H4.
elim (le_lt_or_eq N O H4).
move=> H5.
elim (le_not_lt O N (le_0_n N) H5).
move=> H5.
rewrite H5.
simpl.
rewrite - {2} H5.
rewrite (proj2 H2).
rewrite (Rmult_1_r 2).
unfold Rdiv.
rewrite (Rmult_0_l (/ 2)).
right.
unfold Rminus.
rewrite (Rplus_assoc 1 (- / 2) (- / 2)).
rewrite - (Ropp_plus_distr (/ 2) (/ 2)).
rewrite - (Rmult_1_l (/ 2)).
rewrite - (Rmult_plus_distr_r 1 1 (/ 2)).
rewrite - {1} (Rinv_r 2 Two_Neq_Zero).
rewrite (Rplus_opp_r (2 * / 2)).
reflexivity.
move=> n H4 H5.
elim (le_lt_or_eq N (S n) H5).
move=> H6.
suff: (1 - / 2 ^ S N - / 2 ^ S (S n) = 1 - / 2 ^ S N - / 2 ^ S n + / 2 ^ S (S n))%R.
move=> H7.
rewrite H7.
apply (Rplus_le_compat (sum_f_R0 (fun (k : nat) => INR (proj1_sig (f k)) / 2 ^ S k) n) (1 - / 2 ^ S N - / 2 ^ S n) (INR (proj1_sig (f (S n))) / 2 ^ S (S n)) (/ 2 ^ S (S n)) (H4 (le_S_n N n H6)))%R.
rewrite - (Rmult_1_l (/ 2 ^ S (S n))).
apply (Rmult_le_compat_r (/ 2 ^ S (S n)) (INR (proj1_sig (f (S n)))) 1)%R.
left.
apply (Rinv_0_lt_compat (2 ^ S (S n)) (Two_Pow_Gt_Zero (S (S n)))).
apply (le_INR (proj1_sig (f (S n))) 1 (le_S_n (proj1_sig (f (S n))) 1 (proj2_sig (f (S n))))).
unfold Rminus.
rewrite (Rplus_assoc (1 - / 2 ^ S N) (- / 2 ^ S n) (/ 2 ^ S (S n))).
suff: (/ 2 ^ S n = / 2 ^ S (S n) + / 2 ^ S (S n))%R.
move=> H7.
rewrite H7.
rewrite (Ropp_plus_distr (/ 2 ^ S (S n)) (/ 2 ^ S (S n))).
rewrite (Rplus_assoc (- / 2 ^ S (S n)) (- / 2 ^ S (S n)) (/ 2 ^ S (S n))).
rewrite (Rplus_opp_l (/ 2 ^ S (S n))).
rewrite (Rplus_0_r (- / 2 ^ S (S n))).
reflexivity.
rewrite - (Rmult_1_l (/ 2 ^ S (S n))).
rewrite - (Rmult_plus_distr_r 1 1 (/ 2 ^ S (S n))).
rewrite (Rinv_mult_distr 2 (2 ^ S n) Two_Neq_Zero (Two_Pow_Neq_Zero (S n))).
rewrite - Rmult_assoc.
rewrite (Rinv_r 2 Two_Neq_Zero).
rewrite (Rmult_1_l (/ 2 ^ S n)).
reflexivity.
move=> H6.
unfold Rminus.
rewrite H6.
rewrite (Rplus_assoc 1 (- / 2 ^ S (S n)) (- / 2 ^ S (S n))).
rewrite - (Ropp_plus_distr (/ 2 ^ S (S n)) (/ 2 ^ S (S n))).
suff: (/ 2 ^ S n = / 2 ^ S (S n) + / 2 ^ S (S n))%R.
move=> H7.
rewrite - H7.
simpl.
rewrite - H6.
rewrite (proj2 H2).
unfold Rdiv.
rewrite Rmult_0_l.
rewrite Rplus_0_r.
apply (H3 n).
rewrite - (Rmult_1_l (/ 2 ^ S (S n))).
rewrite - (Rmult_plus_distr_r 1 1 (/ 2 ^ S (S n))).
rewrite (Rinv_mult_distr 2 (2 ^ S n) Two_Neq_Zero (Two_Pow_Neq_Zero (S n))).
rewrite - Rmult_assoc.
rewrite (Rinv_r 2 Two_Neq_Zero).
rewrite (Rmult_1_l (/ 2 ^ S n)).
reflexivity.
elim.
simpl.
rewrite (Rmult_1_r 2).
rewrite - (Rinv_r 2 Two_Neq_Zero).
rewrite (Rmult_plus_distr_r 1 1 (/ 2)).
rewrite (Rmult_1_l (/ 2)).
unfold Rminus.
rewrite (Rplus_assoc (/ 2) (/ 2) (- / 2)).
rewrite (Rplus_opp_r (/ 2)).
rewrite (Rplus_0_r (/ 2)).
rewrite - (Rmult_1_l (/ 2)).
apply (Rmult_le_compat_r (/ 2) (INR (proj1_sig (f 0%nat))) 1).
left.
apply (Rinv_0_lt_compat 2 Two_Gt_Zero).
apply (le_INR (proj1_sig (f O)) 1 (le_S_n (proj1_sig (f O)) 1 (proj2_sig (f O)))).
move=> n H3.
suff: (/ 2 ^ S n = / 2 ^ S (S n) + / 2 ^ S (S n))%R.
move=> H4.
suff: (1 - / 2 ^ S (S n) = 1 - / 2 ^ S n + / 2 ^ S (S n))%R.
move=> H5.
rewrite H5.
simpl.
apply Rplus_le_compat.
apply H3.
rewrite - (Rmult_1_l (/ 2 ^ S (S n))).
apply Rmult_le_compat_r.
left.
apply (Rinv_0_lt_compat (2 ^ S (S n)) (Two_Pow_Gt_Zero (S (S n)))).
apply (le_INR (proj1_sig (f (S n))) 1 (le_S_n (proj1_sig (f (S n))) 1 (proj2_sig (f (S n))))).
rewrite H4.
unfold Rminus.
rewrite (Ropp_plus_distr (/ 2 ^ S (S n)) (/ 2 ^ S (S n))).
rewrite (Rplus_assoc 1 (- / 2 ^ S (S n) + - / 2 ^ S (S n)) (/ 2 ^ S (S n))).
rewrite (Rplus_assoc (- / 2 ^ S (S n)) (- / 2 ^ S (S n)) (/ 2 ^ S (S n))).
rewrite (Rplus_opp_l (/ 2 ^ S (S n))).
rewrite (Rplus_0_r (- / 2 ^ S (S n))).
reflexivity.
rewrite - (Rmult_1_l (/ 2 ^ S (S n))).
rewrite - (Rmult_plus_distr_r 1 1 (/ 2 ^ S (S n))).
rewrite (Rinv_mult_distr 2 (2 ^ S n) Two_Neq_Zero (Two_Pow_Neq_Zero (S n))).
rewrite - Rmult_assoc.
rewrite (Rinv_r 2 Two_Neq_Zero).
rewrite (Rmult_1_l (/ 2 ^ S n)).
reflexivity.
apply (Theorem_2 {r : R | (0 <= r < 1)%R} R).
exists (fun (x : {r : R | (0 <= r < 1)%R}) => proj1_sig x).
move=> r1 r2.
apply sig_map.
elim (Formula_1_2 {r : R | (0 < r < 1)%R} R (Example_5 0 1 Rlt_0_1)).
move=> f H1.
suff: (forall (r : R), 0 <= proj1_sig (f r) < 1)%R.
move=> H2.
exists (fun (r : R) => exist (fun (x : R) => 0 <= x < 1) (proj1_sig (f r)) (H2 r))%R.
move=> r1 r2 H3.
apply (BijInj R {r : R | (0 < r < 1)%R} f H1 r1 r2).
apply sig_map.
suff: (proj1_sig (f r1) = proj1_sig (exist (fun (x : R) => (0 <= x < 1)%R) (proj1_sig (f r1)) (H2 r1))).
move=> H4.
rewrite H4.
rewrite H3.
reflexivity.
reflexivity.
move=> r.
apply conj.
left.
apply (proj1 (proj2_sig (f r))).
apply (proj2 (proj2_sig (f r))).
move=> an s k.
suff: (sum_f_R0 (fun (n : nat) => an (n + S k)) = (fun (n : nat) => sum_f_R0 an (n + S k) - sum_f_R0 an k)%R).
move=> H1.
rewrite H1.
apply conj.
move=> H2.
apply (Theorem_2_5_1_minus (fun (n : nat) => sum_f_R0 an (n + S k)) (fun (n : nat) => sum_f_R0 an k) s (sum_f_R0 an k)).
move=> eps H3.
elim (H2 eps H3).
move=> N H4.
exists N.
move=> n H5.
apply (H4 (n + S k)).
apply (le_trans N n (n + S k) H5 (le_plus_l n (S k))).
move=> eps H3.
exists O.
move=> n H4.
rewrite (proj2 (R_dist_refl (sum_f_R0 an k) (sum_f_R0 an k))).
apply H3.
reflexivity.
move=> H2.
suff: (sum_f_R0 an = (fun (n : nat) => (sum_f_R0 an n - sum_f_R0 an k + sum_f_R0 an k)%R)).
move=> H3.
rewrite H3.
rewrite - (Rplus_0_r s).
rewrite - (Rplus_opp_l (sum_f_R0 an k)).
rewrite - (Rplus_assoc s (- sum_f_R0 an k) (sum_f_R0 an k)).
apply (Theorem_2_5_1_plus (fun (n : nat) => sum_f_R0 an n - sum_f_R0 an k)%R (fun (n : nat) => sum_f_R0 an k) (s - sum_f_R0 an k) (sum_f_R0 an k)).
move=> eps H4.
elim (H2 eps H4).
move=> N H5.
exists (N + S k).
suff: (forall (n : nat), n >= N + S k -> exists (m : nat), m >= N /\ n = m + S k).
move=> H6 n H7.
elim (H6 n H7).
move=> m H8.
rewrite (proj2 H8).
apply (H5 m (proj1 H8)).
move=> n H6.
exists (n - S k).
apply conj.
apply (plus_le_reg_l N (n - S k) (S k)).
rewrite (plus_comm (S k) N).
rewrite (le_plus_minus_r (S k) n).
apply H6.
apply (le_trans (S k) (N + S k) n (le_plus_r N (S k)) H6).
rewrite (plus_comm (n - S k) (S k)).
apply (le_plus_minus (S k) n).
apply (le_trans (S k) (N + S k) n (le_plus_r N (S k)) H6).
move=> eps H4.
exists O.
move=> n H5.
rewrite (proj2 (R_dist_refl (sum_f_R0 an k) (sum_f_R0 an k))).
apply H4.
reflexivity.
apply functional_extensionality.
move=> n.
unfold Rminus.
rewrite (Rplus_assoc (sum_f_R0 an n) (- sum_f_R0 an k) (sum_f_R0 an k)).
rewrite (Rplus_opp_l (sum_f_R0 an k)).
rewrite (Rplus_0_r (sum_f_R0 an n)).
reflexivity.
apply functional_extensionality.
elim.
simpl.
unfold Rminus.
rewrite (Rplus_comm (sum_f_R0 an k + an (S k)) (- sum_f_R0 an k)).
rewrite - (Rplus_assoc (- sum_f_R0 an k) (sum_f_R0 an k) (an (S k))).
rewrite (Rplus_opp_l (sum_f_R0 an k)).
rewrite (Rplus_0_l (an (S k))).
reflexivity.
move=> n H1.
simpl.
rewrite H1.
unfold Rminus.
rewrite (Rplus_assoc (sum_f_R0 an (n + S k)) (- sum_f_R0 an k) (an (S (n + S k)))).
rewrite (Rplus_assoc (sum_f_R0 an (n + S k)) (an (S (n + S k))) (- sum_f_R0 an k)).
rewrite (Rplus_comm (an (S (n + S k))) (- sum_f_R0 an k)).
reflexivity.
Qed.

Definition cardLt (A B : Type) := cardLe A B /\ ~ SameCard A B.

Lemma CardLtWellDefined : forall (A1 A2 B1 B2 : Type), SameCard A1 A2 -> SameCard B1 B2 -> cardLt A1 B1 = cardLt A2 B2.
Proof.
move=> A1 A2 B1 B2 H1 H2.
unfold cardLt.
rewrite (CardLeWellDefined A1 A2 B1 B2 H1 H2).
suff: ((~ SameCard A1 B1) = (~ SameCard A2 B2)).
move=> H3.
rewrite H3.
reflexivity.
apply propositional_extensionality.
apply conj.
move=> H3 H4.
apply H3.
apply (Formula_1_3 A1 A2 B1 H1 (Formula_1_3 A2 B2 B1 H4 (Formula_1_2 B1 B2 H2))).
move=> H3 H4.
apply H3.
apply (Formula_1_3 A2 A1 B2 (Formula_1_2 A1 A2 H1) (Formula_1_3 A1 B1 B2 H4 H2)).
Qed.

Definition CardLt (A B : CardT) := CardLe A B /\ A <> B.

Lemma CardLtDef2 : CardLt = EquivalenceRelationFunctionTwo Type Type Prop CardEquivalence CardEquivalence cardLt CardLtWellDefined.
Proof.
apply functional_extensionality.
move=> A.
apply functional_extensionality.
move=> B.
elim (EquivalenceRelationQuotientInhabited Type CardEquivalence A).
move=> a H1.
elim (EquivalenceRelationQuotientInhabited Type CardEquivalence B).
move=> b H2.
unfold CardLt.
unfold CardLe.
rewrite - (EquivalenceRelationFunctionTwoNature Type Type Prop CardEquivalence CardEquivalence cardLt CardLtWellDefined a b A B).
rewrite - (EquivalenceRelationFunctionTwoNature Type Type Prop CardEquivalence CardEquivalence cardLe CardLeWellDefined a b A B).
apply propositional_extensionality.
apply conj.
move=> H3.
apply conj.
apply (proj1 H3).
move=> H4.
apply (proj2 H3).
rewrite H1.
rewrite H2.
apply (proj1 (Formula_66_1 a b) H4).
move=> H3.
apply conj.
apply (proj1 H3).
rewrite H1.
rewrite H2.
move=> H4.
apply (proj2 H3).
apply (proj2 (Formula_66_1 a b) H4).
rewrite H1.
apply (ERref Type CardEquivalence a).
rewrite H2.
apply (ERref Type CardEquivalence b).
rewrite H1.
apply (ERref Type CardEquivalence a).
rewrite H2.
apply (ERref Type CardEquivalence b).
Qed.

Lemma CardLtNature : forall (T1 T2 : Type) (C1 C2 : CardT), proj1_sig C1 T1 -> proj1_sig C2 T2 -> cardLt T1 T2 = CardLt C1 C2.
Proof.
rewrite CardLtDef2.
apply (EquivalenceRelationFunctionTwoNature Type Type Prop CardEquivalence CardEquivalence cardLt CardLtWellDefined).
Qed.

Lemma Formula_69_1 : forall (C1 C2 : CardT), (exists (n : nat), C1 = CardN n) -> InfiniteCard C2 -> CardLt C1 C2.
Proof.
suff: (forall (n : nat) (C1 C2 : CardT), C1 = CardN n -> InfiniteCard C2 -> CardLe C1 C2).
move=> H1 C1 C2.
elim.
move=> n H2 H3.
apply conj.
apply (H1 n C1 C2 H2 H3).
move=> H4.
apply H3.
exists n.
rewrite - H4.
apply H2.
elim.
move=> C1 C2 H1 H2.
elim (proj2_sig C2).
move=> T2 H3.
suff: (proj1_sig C2 T2).
move=> H4.
rewrite - (CardLeNature (Count O) T2 C1 C2).
exists (fun (m : Count O) => match (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) (proj2_sig m)) with
end).
move=> m1.
elim (le_not_lt O (proj1_sig m1) (le_0_n (proj1_sig m1)) (proj2_sig m1)).
rewrite H1.
apply (Formula_1_1 (Count O)).
apply H4.
rewrite H3.
apply (Formula_1_1 T2).
move=> n H1 C1 C2 H2 H3.
elim (EquivalenceRelationQuotientInhabited Type CardEquivalence C2).
move=> T2 H4.
suff: (proj1_sig C2 T2).
move=> H5.
suff: (cardLe (Count n) T2).
elim.
move=> f H6.
suff: (exists (t : T2), forall (m : Count n), f m <> t).
elim.
move=> t H7.
rewrite - (CardLeNature (Count (S n)) T2 C1 C2).
exists (fun (m : Count (S n)) => match excluded_middle_informative (proj1_sig m < n) with
  | left H => f (exist (fun (k : nat) => k < n) (proj1_sig m) H)
  | right _ => t
end).
move=> m1 m2.
elim (excluded_middle_informative (proj1_sig m1 < n)).
move=> H8.
elim (excluded_middle_informative (proj1_sig m2 < n)).
move=> H9 H10.
apply sig_map.
suff: (proj1_sig m1 = proj1_sig (exist (fun (k : nat) => k < n) (proj1_sig m1) H8)).
move=> H11.
rewrite H11.
rewrite (H6 (exist (fun (k : nat) => k < n) (proj1_sig m1) H8) (exist (fun (k : nat) => k < n) (proj1_sig m2) H9) H10).
reflexivity.
reflexivity.
move=> H9 H10.
elim (H7 (exist (fun (k : nat) => k < n) (proj1_sig m1) H8) H10).
move=> H8.
elim (excluded_middle_informative (proj1_sig m2 < n)).
move=> H9 H10.
elim (H7 (exist (fun (k : nat) => k < n) (proj1_sig m2) H9)).
rewrite H10.
reflexivity.
move=> H9 H10.
apply sig_map.
elim (le_or_lt (proj1_sig m1) n).
move=> H11.
elim (le_lt_or_eq (proj1_sig m1) n H11).
move=> H12.
elim (H8 H12).
move=> H12.
elim (le_or_lt (proj1_sig m2) n).
move=> H13.
elim (le_lt_or_eq (proj1_sig m2) n H13).
move=> H14.
elim (H9 H14).
move=> H14.
rewrite H14.
apply H12.
move=> H13.
elim (le_not_lt (S n) (proj1_sig m2) H13 (proj2_sig m2)).
move=> H11.
elim (le_not_lt (S n) (proj1_sig m1) H11 (proj2_sig m1)).
rewrite H2.
apply (Formula_1_1 (Count (S n))).
rewrite H4.
apply (Formula_1_1 T2).
apply NNPP.
move=> H7.
apply H3.
exists n.
rewrite H4.
apply (proj1 (Formula_66_1 T2 (Count n))).
apply (Formula_1_2 (Count n) T2).
exists f.
apply InjSurjBij.
apply H6.
move=> t.
apply NNPP.
move=> H8.
apply H7.
exists t.
move=> m H9.
apply H8.
exists m.
apply H9.
rewrite (CardLeNature (Count n) T2 (CardN n) C2 (Formula_1_1 (Count n)) H5).
apply (H1 (CardN n) C2).
reflexivity.
apply H3.
rewrite H4.
apply (Formula_1_1 T2).
Qed.

Lemma Formula_69_2_set : forall (T : Type) (A : Ensemble T) (n : nat), cardinal T A n -> forall (B : Ensemble T), Strict_Included T B A -> cardLt {t : T | In T B t} {t : T | In T A t}.
Proof.
move=> T A n H1 B H2.
apply conj.
exists (fun (m : {t : T | In T B t}) => exist A (proj1_sig m) (proj1 H2 (proj1_sig m) (proj2_sig m))).
move=> m1 m2 H3.
apply sig_map.
suff: (proj1_sig m1 = proj1_sig (exist A (proj1_sig m1) (proj1 H2 (proj1_sig m1) (proj2_sig m1)))).
move=> H4.
rewrite H4.
rewrite H3.
reflexivity.
reflexivity.
move=> H3.
apply (Example_1_2_set T A n H1 B H2).
apply (Formula_1_2 {t : T | In T B t} {t : T | In T A t} H3).
Qed.

Lemma Formula_69_2 : forall (T : Type) (n : nat), cardinal T (Full_set T) n -> forall (A : Ensemble T), Strict_Included T A (Full_set T) -> cardLt {t : T | In T A t} T.
Proof.
move=> T n H1 A H2.
apply conj.
exists (fun (m : {t : T | In T A t}) => proj1_sig m).
move=> m1 m2.
apply sig_map.
move=> H3.
apply (Example_1_2 T n H1 A H2).
apply (Formula_1_2 {t : T | In T A t} T H3).
Qed.

Lemma Count2PropSameCard : SameCard (Count 2) Prop.
Proof.
exists (fun (t : Count 2) => t = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))).
exists (fun (t : Prop) => match excluded_middle_informative t with
  | left _ => exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))
  | right _ => exist (fun (k : nat) => k < 2) 1 (le_n 2)
end).
apply conj.
move=> x.
elim (excluded_middle_informative (x = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))).
move=> H1.
rewrite H1.
reflexivity.
move=> H1.
elim (le_lt_or_eq O (proj1_sig x) (le_0_n (proj1_sig x))).
move=> H2.
elim (le_lt_or_eq 1 (proj1_sig x) H2).
move=> H3.
elim (lt_irrefl 2 (le_trans 3 (S (proj1_sig x)) 2 (le_n_S 2 (proj1_sig x) H3) (proj2_sig x))).
move=> H3.
apply sig_map.
apply H3.
move=> H2.
elim H1.
apply sig_map.
simpl.
rewrite {2} H2.
reflexivity.
move=> y.
elim (excluded_middle_informative y).
move=> H1.
apply propositional_extensionality.
apply conj.
move=> H2.
apply H1.
move=> H2.
reflexivity.
move=> H1.
apply propositional_extensionality.
apply conj.
move=> H2.
elim (lt_irrefl (proj1_sig (exist (fun (k : nat) => k < 2) 1 (le_n 2)))).
rewrite {1} H2.
apply (le_n 1).
move=> H2.
elim (H1 H2).
Qed.

Lemma Pow2EnsembleSameCard : forall (T : Type), SameCard (T -> Count 2) (Ensemble T).
Proof.
move=> T.
elim Count2PropSameCard.
move=> f.
elim.
move=> finv H1.
exists (fun (g : T -> Count 2) (t : T) => f (g t)).
exists (fun (A : Ensemble T) (t : T) => finv (A t)).
apply conj.
move=> x.
apply functional_extensionality.
move=> t.
apply (proj1 H1 (x t)).
move=> y.
apply functional_extensionality.
move=> t.
apply (proj2 H1 (y t)).
Qed.

Lemma Theorem_8 : forall (T : Type), cardLt T (Ensemble T).
Proof.
move=> T.
rewrite (CardLtWellDefined T T (Ensemble T) (T -> Count 2) (Formula_1_1 T) (Formula_1_2 (T -> Count 2) (Ensemble T) (Pow2EnsembleSameCard T))).
apply conj.
exists (fun (t1 t2 : T) => match excluded_middle_informative (t1 = t2) with
  | left _ => exist (fun (k : nat) => k < 2) 1 (le_n 2)
  | right _ => exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))
end).
move=> t1 t2 H1.
suff: (let f := fun (t0 : T) => match excluded_middle_informative (t1 = t0) with
  | left _ => exist (fun (k : nat) => k < 2) 1 (le_n 2)
  | right _ => exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))
end in f t1 = exist (fun (k : nat) => k < 2) 1 (le_n 2)).
rewrite H1.
simpl.
elim (excluded_middle_informative (t2 = t1)).
move=> H2 H3.
rewrite H2.
reflexivity.
move=> H2 H3.
elim (lt_irrefl (proj1_sig (exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))))).
rewrite {2} H3.
apply (le_n 1).
simpl.
elim (excluded_middle_informative (t1 = t1)).
move=> H2.
reflexivity.
elim.
reflexivity.
elim.
move=> f H1.
elim (BijSurj T (T -> Count 2) f H1 (fun (t : T) => match excluded_middle_informative (f t t = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))) with
  | left _ => exist (fun (k : nat) => k < 2) 1 (le_n 2)
  | right _ => exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1))
end)).
move=> t H2.
elim (le_lt_or_eq O (proj1_sig (f t t)) (le_0_n (proj1_sig (f t t)))).
move=> H3.
elim (le_lt_or_eq 1 (proj1_sig (f t t)) H3).
move=> H4.
elim (lt_irrefl 2 (le_trans 3 (S (proj1_sig (f t t))) 2 (le_n_S 2 (proj1_sig (f t t)) H4) (proj2_sig (f t t)))).
move=> H4.
suff: (1 = proj1_sig (f t t)).
rewrite H2.
elim (excluded_middle_informative (f t t = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))).
move=> H5.
elim (lt_irrefl (proj1_sig (f t t))).
rewrite - {2} H4.
rewrite H5.
apply (le_n 1).
move=> H5 H6.
elim (lt_irrefl 1).
rewrite {1} H6.
apply (le_n 1).
apply H4.
move=> H3.
suff: (0 = proj1_sig (f t t)).
rewrite H2.
elim (excluded_middle_informative (f t t = exist (fun (k : nat) => k < 2) 0 (le_S 1 1 (le_n 1)))).
move=> H4 H5.
elim (lt_irrefl 0).
rewrite {2} H5.
apply (le_n 1).
elim.
apply sig_map.
rewrite - H3.
reflexivity.
apply H3.
Qed.

Lemma Theorem_7 : CardLt (Card nat) (Card R).
Proof.
rewrite - (CardLtNature nat (Ensemble nat) (Card nat) (Card R)).
apply (Theorem_8 nat).
apply (Formula_1_1 nat).
apply (Formula_1_2 (Ensemble nat) R).
apply (Formula_1_3 (Ensemble nat) (nat -> Count 2) R (Formula_1_2 (nat -> Count 2) (Ensemble nat) (Pow2EnsembleSameCard nat)) Formula_85_3).
Qed.

Lemma CardPlusWellDefined : forall (A1 A2 B1 B2 : Type), SameCard A1 A2 -> SameCard B1 B2 -> Card (sum A1 B1) = Card (sum A2 B2).
Proof.
move=> A1 A2 B1 B2.
elim.
move=> f.
elim.
move=> finv H1.
elim.
move=> g.
elim.
move=> ginv H2.
apply (proj1 (Formula_66_1 (A1 + B1) (A2 + B2))).
exists (fun (x : A1 + B1) => match x with
  | inl x0 => inl (f x0)
  | inr x0 => inr (g x0)
end).
exists (fun (x : A2 + B2) => match x with
  | inl x0 => inl (finv x0)
  | inr x0 => inr (ginv x0)
end).
apply conj.
elim.
move=> a.
rewrite (proj1 H1 a).
reflexivity.
move=> b.
rewrite (proj1 H2 b).
reflexivity.
elim.
move=> a.
rewrite (proj2 H1 a).
reflexivity.
move=> b.
rewrite (proj2 H2 b).
reflexivity.
Qed.

Definition CardPlus : CardT -> CardT -> CardT := EquivalenceRelationFunctionTwo Type Type CardT CardEquivalence CardEquivalence (fun (A B : Type) => Card (sum A B)) CardPlusWellDefined.

Definition CardPlusNature : forall (T1 T2 : Type) (C1 C2 : CardT), proj1_sig C1 T1 -> proj1_sig C2 T2 -> Card (sum T1 T2) = CardPlus C1 C2 := EquivalenceRelationFunctionTwoNature Type Type CardT CardEquivalence CardEquivalence (fun (A B : Type) => Card (sum A B)) CardPlusWellDefined.

Lemma CardPlusCount : forall (n m : nat), CardPlus (CardN n) (CardN m) = CardN (n + m).
Proof.
move=> n m.
rewrite - (CardPlusNature (Count n) (Count m) (CardN n) (CardN m) (Formula_1_1 (Count n)) (Formula_1_1 (Count m))).
apply (proj1 (Formula_66_1 (Count n + Count m) (Count (n + m)))).
elim (CountAdd n m).
move=> f H1.
exists f.
apply H1.
Qed.

Lemma Formula_3_1 : forall (C1 C2 : CardT), CardPlus C1 C2 = CardPlus C2 C1.
Proof.
move=> C1 C2.
elim (proj2_sig C1).
move=> T1 H1.
suff: (proj1_sig C1 T1).
move=> H2.
elim (proj2_sig C2).
move=> T2 H3.
suff: (proj1_sig C2 T2).
move=> H4.
rewrite - (CardPlusNature T1 T2 C1 C2 H2 H4).
rewrite - (CardPlusNature T2 T1 C2 C1 H4 H2).
apply (proj1 (Formula_66_1 (T1 + T2) (T2 + T1))).
exists (fun (x : T1 + T2) => match x with
  | inl x0 => inr x0
  | inr x0 => inl x0
end).
exists (fun (x : T2 + T1) => match x with
  | inl x0 => inr x0
  | inr x0 => inl x0
end).
apply conj.
elim.
move=> x0.
reflexivity.
move=> x0.
reflexivity.
elim.
move=> x0.
reflexivity.
move=> x0.
reflexivity.
rewrite H3.
apply (Formula_1_1 T2).
rewrite H1.
apply (Formula_1_1 T1).
Qed.

Lemma Formula_3_2 : forall (C1 C2 C3 : CardT), CardPlus (CardPlus C1 C2) C3 = CardPlus C1 (CardPlus C2 C3).
Proof.
move=> C1 C2 C3.
elim (proj2_sig C1).
move=> T1 H1.
suff: (proj1_sig C1 T1).
move=> H2.
elim (proj2_sig C2).
move=> T2 H3.
suff: (proj1_sig C2 T2).
move=> H4.
elim (proj2_sig C3).
move=> T3 H5.
suff: (proj1_sig C3 T3).
move=> H6.
rewrite - (CardPlusNature (T1 + T2) T3 (CardPlus C1 C2) C3).
rewrite - (CardPlusNature T1 (T2 + T3) C1 (CardPlus C2 C3)).
apply (proj1 (Formula_66_1 (T1 + T2 + T3) (T1 + (T2 + T3)))).
exists (fun (x : T1 + T2 + T3) => match x with
  | inl x0 => match x0 with
    | inl x1 => inl x1
    | inr x1 => inr (inl x1)
  end
  | inr x0 => inr (inr x0)
end).
exists (fun (x : T1 + (T2 + T3)) => match x with
  | inl x0 => inl (inl x0)
  | inr x0 => match x0 with
    | inl x1 => inl (inr x1)
    | inr x1 => inr x1
  end
end).
apply conj.
elim.
elim.
move=> x.
reflexivity.
move=> x.
reflexivity.
move=> x.
reflexivity.
elim.
move=> y.
reflexivity.
elim.
move=> y.
reflexivity.
move=> y.
reflexivity.
apply H2.
rewrite - (CardPlusNature T2 T3 C2 C3 H4 H6).
apply (Formula_1_1 (T2 + T3)).
rewrite - (CardPlusNature T1 T2 C1 C2 H2 H4).
apply (Formula_1_1 (T1 + T2)).
apply H6.
rewrite H5.
apply (Formula_1_1 T3).
rewrite H3.
apply (Formula_1_1 T2).
rewrite H1.
apply (Formula_1_1 T1).
Qed.

Lemma Formula_3_3 : forall (C : CardT), CardPlus C (CardN O) = C.
Proof.
move=> C.
elim (EquivalenceRelationQuotientInhabited Type CardEquivalence C).
move=> T H1.
suff: (proj1_sig C T).
move=> H2.
rewrite - (CardPlusNature T (Count O) C (CardN O) H2 (Formula_1_1 (Count O))).
rewrite H1.
apply (proj1 (Formula_66_1 (T + Count O) T)).
exists (fun (x : T + Count O) => match x with
  | inl x => x
  | inr x => match (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) (proj2_sig x)) with
  end
end).
exists (fun (x : T) => inl x).
apply conj.
elim.
move=> t.
reflexivity.
move=> t.
elim (le_not_lt O (proj1_sig t) (le_0_n (proj1_sig t)) (proj2_sig t)).
move=> t.
reflexivity.
rewrite H1.
apply (Formula_1_1 T).
Qed.

Lemma Formula_3_4 : forall (C1 C2 D1 D2 : CardT), CardLe C1 C2 -> CardLe D1 D2 -> CardLe (CardPlus C1 D1) (CardPlus C2 D2).
Proof.
move=> C1 C2 C3 C4.
elim (proj2_sig C1).
move=> T1 H1.
suff: (proj1_sig C1 T1).
move=> H2.
elim (proj2_sig C2).
move=> T2 H3.
suff: (proj1_sig C2 T2).
move=> H4.
elim (proj2_sig C3).
move=> T3 H5.
suff: (proj1_sig C3 T3).
move=> H6.
elim (proj2_sig C4).
move=> T4 H7.
suff: (proj1_sig C4 T4).
move=> H8.
rewrite - (CardLeNature T1 T2 C1 C2 H2 H4).
rewrite - (CardLeNature T3 T4 C3 C4 H6 H8).
rewrite - (CardLeNature (T1 + T3) (T2 + T4) (CardPlus C1 C3) (CardPlus C2 C4)).
elim.
move=> f1 H9.
elim.
move=> f2 H10.
exists (fun (x : T1 + T3) => match x with
  | inl x0 => inl (f1 x0)
  | inr x0 => inr (f2 x0)
end).
elim.
move=> x1.
elim.
move=> x2 H11.
apply f_equal.
apply H9.
suff: (let temp := @inl T2 T4 (f1 x1) in match temp with
  | inl x => x
  | inr _ => f1 x1
end = f1 x2).
apply.
rewrite H11.
reflexivity.
move=> x2 H11.
suff: (let temp := @inl T2 T4 (f1 x1) in match temp with
  | inl x => True
  | inr _ => False
end).
rewrite H11.
elim.
apply I.
move=> x1.
elim.
move=> x2 H11.
suff: (let temp := @inr T2 T4 (f2 x1) in match temp with
  | inl x => True
  | inr _ => False
end).
elim.
rewrite H11.
apply I.
move=> x2 H11.
apply f_equal.
apply H10.
suff: (let temp := @inr T2 T4 (f2 x1) in match temp with
  | inl _ => f2 x1
  | inr x => x
end = f2 x2).
apply.
rewrite H11.
reflexivity.
rewrite - (CardPlusNature T1 T3 C1 C3 H2 H6).
apply (Formula_1_1 (T1 + T3)).
rewrite - (CardPlusNature T2 T4 C2 C4 H4 H8).
apply (Formula_1_1 (T2 + T4)).
rewrite H7.
apply (Formula_1_1 T4).
rewrite H5.
apply (Formula_1_1 T3).
rewrite H3.
apply (Formula_1_1 T2).
rewrite H1.
apply (Formula_1_1 T1).
Qed.

Lemma CardMultWellDefined : forall (A1 A2 B1 B2 : Type), SameCard A1 A2 -> SameCard B1 B2 -> Card (A1 * B1) = Card (A2 * B2).
Proof.
move=> A1 A2 B1 B2.
elim.
move=> f.
elim.
move=> finv H1.
elim.
move=> g.
elim.
move=> ginv H2.
apply (proj1 (Formula_66_1 (A1 * B1) (A2 * B2))).
exists (fun (x : A1 * B1) => (f (fst x), g (snd x))).
exists (fun (x : A2 * B2) => (finv (fst x), ginv (snd x))).
apply conj.
move=> x.
simpl.
rewrite (proj1 H1 (fst x)).
rewrite (proj1 H2 (snd x)).
elim x.
move=> a b.
reflexivity.
move=> y.
simpl.
rewrite (proj2 H1 (fst y)).
rewrite (proj2 H2 (snd y)).
elim y.
move=> a b.
reflexivity.
Qed.

Definition CardMult : CardT -> CardT -> CardT := EquivalenceRelationFunctionTwo Type Type CardT CardEquivalence CardEquivalence (fun (A B : Type) => Card (A * B)) CardMultWellDefined.

Definition CardMultNature : forall (T1 T2 : Type) (C1 C2 : CardT), proj1_sig C1 T1 -> proj1_sig C2 T2 -> Card (T1 * T2) = CardMult C1 C2 := EquivalenceRelationFunctionTwoNature Type Type CardT CardEquivalence CardEquivalence (fun (A B : Type) => Card (A * B)) CardMultWellDefined.

Lemma CardMultCount : forall (n m : nat), CardMult (CardN n) (CardN m) = CardN (n * m).
Proof.
move=> n m.
rewrite - (CardMultNature (Count n) (Count m) (CardN n) (CardN m) (Formula_1_1 (Count n)) (Formula_1_1 (Count m))).
apply (proj1 (Formula_66_1 (Count n * Count m) (Count (n * m)))).
elim (CountMult n m).
move=> f H1.
exists f.
apply H1.
Qed.

Lemma Formula_3_5 : forall (C1 C2 : CardT), CardMult C1 C2 = CardMult C2 C1.
Proof.
move=> C1 C2.
elim (proj2_sig C1).
move=> T1 H1.
suff: (proj1_sig C1 T1).
move=> H2.
elim (proj2_sig C2).
move=> T2 H3.
suff: (proj1_sig C2 T2).
move=> H4.
rewrite - (CardMultNature T1 T2 C1 C2 H2 H4).
rewrite - (CardMultNature T2 T1 C2 C1 H4 H2).
apply (proj1 (Formula_66_1 (T1 * T2) (T2 * T1))).
exists (fun (x : T1 * T2) => (snd x, fst x)).
exists (fun (x : T2 * T1) => (snd x, fst x)).
apply conj.
elim.
move=> a b.
reflexivity.
elim.
move=> a b.
reflexivity.
rewrite H3.
apply (Formula_1_1 T2).
rewrite H1.
apply (Formula_1_1 T1).
Qed.

Lemma Formula_3_6 : forall (C1 C2 C3 : CardT), CardMult (CardMult C1 C2) C3 = CardMult C1 (CardMult C2 C3).
Proof.
move=> C1 C2 C3.
elim (proj2_sig C1).
move=> T1 H1.
suff: (proj1_sig C1 T1).
move=> H2.
elim (proj2_sig C2).
move=> T2 H3.
suff: (proj1_sig C2 T2).
move=> H4.
elim (proj2_sig C3).
move=> T3 H5.
suff: (proj1_sig C3 T3).
move=> H6.
rewrite - (CardMultNature (T1 * T2) T3 (CardMult C1 C2) C3).
rewrite - (CardMultNature T1 (T2 * T3) C1 (CardMult C2 C3)).
apply (proj1 (Formula_66_1 (T1 * T2 * T3) (T1 * (T2 * T3)))).
exists (fun (x : T1 * T2 * T3) => (fst (fst x), (snd (fst x), snd x))).
exists (fun (x : T1 * (T2 * T3)) => ((fst x, fst (snd x)), snd (snd x))).
apply conj.
elim.
elim.
move=> a b c.
reflexivity.
elim.
move=> a.
elim.
move=> b c.
reflexivity.
apply H2.
rewrite - (CardMultNature T2 T3 C2 C3 H4 H6).
apply (Formula_1_1 (T2 * T3)).
rewrite - (CardMultNature T1 T2 C1 C2 H2 H4).
apply (Formula_1_1 (T1 * T2)).
apply H6.
rewrite H5.
apply (Formula_1_1 T3).
rewrite H3.
apply (Formula_1_1 T2).
rewrite H1.
apply (Formula_1_1 T1).
Qed.

Lemma Formula_3_7_1 : forall (C : CardT), CardMult C (CardN O) = CardN O.
Proof.
move=> C.
elim (proj2_sig C).
move=> T H1.
suff: (proj1_sig C T).
move=> H2.
rewrite - (CardMultNature T (Count O) C (CardN O) H2 (Formula_1_1 (Count O))).
apply (proj1 (Formula_66_1 (T * Count O) (Count O))).
exists (fun (x : T * Count O) => match (le_not_lt O (proj1_sig (snd x)) (le_0_n (proj1_sig (snd x))) (proj2_sig (snd x))) with
end).
exists (fun (x : Count O) => match (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) (proj2_sig x)) with
end).
apply conj.
move=> x.
elim (le_not_lt 0 (proj1_sig (snd x)) (le_0_n (proj1_sig (snd x))) (proj2_sig (snd x))).
move=> y.
elim (le_not_lt 0 (proj1_sig y) (le_0_n (proj1_sig y)) (proj2_sig y)).
rewrite H1.
apply (Formula_1_1 T).
Qed.

Lemma Formula_3_7_2 : forall (C : CardT), CardMult C (CardN 1) = C.
Proof.
move=> C.
elim (EquivalenceRelationQuotientInhabited Type CardEquivalence C).
move=> T H1.
suff: (proj1_sig C T).
move=> H2.
rewrite - (CardMultNature T (Count 1) C (CardN 1) H2 (Formula_1_1 (Count 1))).
rewrite H1.
apply (proj1 (Formula_66_1 (T * Count 1) T)).
exists (fun (x : T * Count 1) => fst x).
exists (fun (x : T) => (x, exist (fun (n : nat) => n < 1) O (le_n 1))).
apply conj.
elim.
move=> a b.
suff: (exist (fun (n : nat) => n < 1) O (le_n 1) = b).
move=> H3.
rewrite H3.
reflexivity.
apply sig_map.
elim (le_lt_or_eq (proj1_sig b) O (le_S_n (proj1_sig b) O (proj2_sig b))).
move=> H3.
elim (le_not_lt O (proj1_sig b) (le_0_n (proj1_sig b)) H3).
move=> H3.
rewrite H3.
reflexivity.
move=> y.
reflexivity.
rewrite H1.
apply (Formula_1_1 T).
Qed.

Lemma Formula_3_8 : forall (C1 C2 D1 D2 : CardT), CardLe C1 C2 -> CardLe D1 D2 -> CardLe (CardMult C1 D1) (CardMult C2 D2).
Proof.
move=> C1 C2 C3 C4.
elim (proj2_sig C1).
move=> T1 H1.
suff: (proj1_sig C1 T1).
move=> H2.
elim (proj2_sig C2).
move=> T2 H3.
suff: (proj1_sig C2 T2).
move=> H4.
elim (proj2_sig C3).
move=> T3 H5.
suff: (proj1_sig C3 T3).
move=> H6.
elim (proj2_sig C4).
move=> T4 H7.
suff: (proj1_sig C4 T4).
move=> H8.
rewrite - (CardLeNature T1 T2 C1 C2 H2 H4).
rewrite - (CardLeNature T3 T4 C3 C4 H6 H8).
rewrite - (CardLeNature (T1 * T3) (T2 * T4) (CardMult C1 C3) (CardMult C2 C4)).
elim.
move=> f1 H9.
elim.
move=> f2 H10.
exists (fun (x : T1 * T3) => (f1 (fst x), f2 (snd x))).
move=> x1 x2 H11.
apply injective_projections.
apply H9.
suff: (f1 (fst x1) = fst (f1 (fst x1), f2 (snd x1))).
move=> H12.
rewrite H12.
rewrite H11.
reflexivity.
reflexivity.
apply H10.
suff: (f2 (snd x1) = snd (f1 (fst x1), f2 (snd x1))).
move=> H12.
rewrite H12.
rewrite H11.
reflexivity.
reflexivity.
rewrite - (CardMultNature T1 T3 C1 C3 H2 H6).
apply (Formula_1_1 (T1 * T3)).
rewrite - (CardMultNature T2 T4 C2 C4 H4 H8).
apply (Formula_1_1 (T2 * T4)).
rewrite H7.
apply (Formula_1_1 T4).
rewrite H5.
apply (Formula_1_1 T3).
rewrite H3.
apply (Formula_1_1 T2).
rewrite H1.
apply (Formula_1_1 T1).
Qed.

Lemma Formula_3_9 : forall (C1 C2 C3 : CardT), CardMult (CardPlus C1 C2) C3 = CardPlus (CardMult C1 C3) (CardMult C2 C3).
Proof.
move=> C1 C2 C3.
elim (proj2_sig C1).
move=> T1 H1.
suff: (proj1_sig C1 T1).
move=> H2.
elim (proj2_sig C2).
move=> T2 H3.
suff: (proj1_sig C2 T2).
move=> H4.
elim (proj2_sig C3).
move=> T3 H5.
suff: (proj1_sig C3 T3).
move=> H6.
rewrite - (CardMultNature (T1 + T2) T3 (CardPlus C1 C2) C3).
rewrite - (CardPlusNature (T1 * T3) (T2 * T3) (CardMult C1 C3) (CardMult C2 C3)).
apply (proj1 (Formula_66_1 ((T1 + T2) * T3) (T1 * T3 + T2 * T3))).
exists (fun (x : (T1 + T2) * T3) => match fst x with
  | inl x0 => inl (x0, snd x)
  | inr x0 => inr (x0, snd x)
end).
exists (fun (x : T1 * T3 + T2 * T3) => match x with
  | inl x0 => (inl (fst x0), snd x0)
  | inr x0 => (inr (fst x0), snd x0)
end).
apply conj.
elim.
elim.
move=> a b.
reflexivity.
move=> a b.
reflexivity.
elim.
elim.
move=> a b.
reflexivity.
elim.
move=> a b.
reflexivity.
rewrite - (CardMultNature T1 T3 C1 C3 H2 H6).
apply (Formula_1_1 (T1 * T3)).
rewrite - (CardMultNature T2 T3 C2 C3 H4 H6).
apply (Formula_1_1 (T2 * T3)).
rewrite - (CardPlusNature T1 T2 C1 C2 H2 H4).
apply (Formula_1_1 (T1 + T2)).
apply H6.
rewrite H5.
apply (Formula_1_1 T3).
rewrite H3.
apply (Formula_1_1 T2).
rewrite H1.
apply (Formula_1_1 T1).
Qed.

Lemma CardPowWellDefined : forall (A1 A2 B1 B2 : Type), SameCard A1 A2 -> SameCard B1 B2 -> Card (B1 -> A1) = Card (B2 -> A2).
Proof.
move=> A1 A2 B1 B2.
elim.
move=> f.
elim.
move=> finv H1.
elim.
move=> g.
elim.
move=> ginv H2.
apply (proj1 (Formula_66_1 (B1 -> A1) (B2 -> A2))).
exists (fun (h : B1 -> A1) (a : B2) => f (h (ginv a))).
exists (fun (h : B2 -> A2) (a : B1) => finv (h (g a))).
apply conj.
move=> h.
apply functional_extensionality.
move=> a.
rewrite (proj1 H1 (h (ginv (g a)))).
rewrite (proj1 H2 a).
reflexivity.
move=> h.
apply functional_extensionality.
move=> b.
rewrite (proj2 H1 (h (g (ginv b)))).
rewrite (proj2 H2 b).
reflexivity.
Qed.

Definition CardPow : CardT -> CardT -> CardT := EquivalenceRelationFunctionTwo Type Type CardT CardEquivalence CardEquivalence (fun (A B : Type) => Card (B -> A)) CardPowWellDefined.

Definition CardPowNature : forall (T1 T2 : Type) (C1 C2 : CardT), proj1_sig C1 T1 -> proj1_sig C2 T2 -> Card (T2 -> T1) = CardPow C1 C2 := EquivalenceRelationFunctionTwoNature Type Type CardT CardEquivalence CardEquivalence (fun (A B : Type) => Card (B -> A)) CardPowWellDefined.

Lemma CardPowCount : forall (n m : nat), CardPow (CardN n) (CardN m) = CardN (n ^ m).
Proof.
move=> n m.
rewrite - (CardPowNature (Count n) (Count m) (CardN n) (CardN m) (Formula_1_1 (Count n)) (Formula_1_1 (Count m))).
apply (proj1 (Formula_66_1 (Count m -> Count n) (Count (n ^ m)))).
elim (CountPow m n).
move=> f H1.
exists f.
apply H1.
Qed.

Lemma CardEnsembleWellDefined : forall (A1 A2 : Type), SameCard A1 A2 -> Card (Ensemble A1) = Card (Ensemble A2).
Proof.
move=> A1 A2.
elim.
move=> f.
elim.
move=> finv H1.
apply (proj1 (Formula_66_1 (Ensemble A1) (Ensemble A2))).
exists (fun (X : Ensemble A1) (a : A2) => In A1 X (finv a)).
exists (fun (X : Ensemble A2) (a : A1) => In A2 X (f a)).
apply conj.
move=> X.
apply functional_extensionality.
move=> a.
unfold In.
rewrite (proj1 H1 a).
reflexivity.
move=> X.
apply functional_extensionality.
move=> a.
unfold In.
rewrite (proj2 H1 a).
reflexivity.
Qed.

Definition CardEnsemble : CardT -> CardT := EquivalenceRelationFunction Type CardT CardEquivalence (fun (A : Type) => Card (Ensemble A)) CardEnsembleWellDefined.

Definition CardEnsembleNature : forall (T : Type) (C : CardT), proj1_sig C T -> Card (Ensemble T) = CardEnsemble C := EquivalenceRelationFunctionNature Type CardT CardEquivalence (fun (A : Type) => Card (Ensemble A)) CardEnsembleWellDefined.

Lemma CardEnsembleCount : forall (n : nat), CardEnsemble (CardN n) = CardN (2 ^ n).
Proof.
move=> n.
rewrite - (CardEnsembleNature (Count n) (CardN n) (Formula_1_1 (Count n))).
apply (proj1 (Formula_66_1 (Ensemble (Count n)) (Count (2 ^ n)))).
elim (Formula_P18_2_sub n).
move=> f H1.
exists f.
apply H1.
Qed.

Lemma CardPowEnsembleRelation : forall (C : CardT), CardPow (CardN 2) C = CardEnsemble C.
Proof.
move=> C.
elim (proj2_sig C).
move=> T H1.
suff: (proj1_sig C T).
move=> H2.
rewrite - (CardPowNature (Count 2) T (CardN 2) C (Formula_1_1 (Count 2)) H2).
rewrite - (CardEnsembleNature T C H2).
apply (proj1 (Formula_66_1 (T -> Count 2) (Ensemble T))).
apply (Pow2EnsembleSameCard T).
rewrite H1.
apply (Formula_1_1 T).
Qed.

Lemma Formula_3_10_1 : forall (C : CardT), CardPow C (CardN 1) = C.
Proof.
move=> C.
elim (EquivalenceRelationQuotientInhabited Type CardEquivalence C).
move=> T H1.
suff: (proj1_sig C T).
move=> H2.
rewrite - (CardPowNature T (Count 1) C (CardN 1) H2 (Formula_1_1 (Count 1))).
rewrite H1.
apply (proj1 (Formula_66_1 (Count 1 -> T) T)).
exists (fun (f : Count 1 -> T) => f (exist (fun (n : nat) => n < 1) O (le_n 1))).
exists (fun (t : T) (n : Count 1) => t).
apply conj.
move=> x.
apply functional_extensionality.
move=> n.
apply (f_equal x).
elim (le_lt_or_eq O (proj1_sig n) (le_0_n (proj1_sig n))).
move=> H3.
elim (le_not_lt 1 (proj1_sig n) H3 (proj2_sig n)).
move=> H3.
apply sig_map.
apply H3.
move=> y.
reflexivity.
rewrite H1.
apply (Formula_1_1 T).
Qed.

Lemma Formula_3_10_2 : forall (C : CardT), CardPow (CardN 1) C = CardN 1.
Proof.
move=> C.
elim (proj2_sig C).
move=> T H1.
suff: (proj1_sig C T).
move=> H2.
rewrite - (CardPowNature (Count 1) T (CardN 1) C (Formula_1_1 (Count 1)) H2).
apply (proj1 (Formula_66_1 (T -> Count 1) (Count 1))).
exists (fun (f : T -> Count 1) => (exist (fun (n : nat) => n < 1) O (le_n 1))).
exists (fun (n : Count 1) (t : T) => (exist (fun (n : nat) => n < 1) O (le_n 1))).
apply conj.
move=> x.
apply functional_extensionality.
move=> t.
elim (le_lt_or_eq O (proj1_sig (x t)) (le_0_n (proj1_sig (x t)))).
move=> H3.
elim (le_not_lt 1 (proj1_sig (x t)) H3 (proj2_sig (x t))).
move=> H3.
apply sig_map.
apply H3.
move=> y.
elim (le_lt_or_eq O (proj1_sig y) (le_0_n (proj1_sig y))).
move=> H3.
elim (le_not_lt 1 (proj1_sig y) H3 (proj2_sig y)).
move=> H3.
apply sig_map.
apply H3.
rewrite H1.
apply (Formula_1_1 T).
Qed.

Lemma Formula_3_11_1 : forall (C D1 D2 : CardT), C <> CardN O -> CardLe D1 D2 -> CardLe (CardPow C D1) (CardPow C D2).
Proof.
move=> C1 C2 C3.
elim (EquivalenceRelationQuotientInhabited Type CardEquivalence C1).
move=> T1 H1.
suff: (proj1_sig C1 T1).
move=> H2.
elim (proj2_sig C2).
move=> T2 H3.
suff: (proj1_sig C2 T2).
move=> H4.
elim (proj2_sig C3).
move=> T3 H5.
suff: (proj1_sig C3 T3).
move=> H6 H7.
rewrite - (CardLeNature T2 T3 C2 C3 H4 H6).
rewrite - (CardLeNature (T2 -> T1) (T3 -> T1) (CardPow C1 C2) (CardPow C1 C3)).
elim.
move=> f H8.
suff: (Inhabited T1 (Full_set T1)).
elim.
move=> t1 H9.
suff: (forall (t3 : T3), (exists (t2 : T2), f t2 = t3) -> {t2 : T2 | f t2 = t3}).
move=> H10.
exists (fun (h : T2 -> T1) (t3 : T3) => match excluded_middle_informative (exists (t2 : T2), f t2 = t3) with
  | left H => h (proj1_sig (H10 t3 H))
  | right _ => t1
end).
move=> h1 h2 H11.
apply functional_extensionality.
move=> t2.
suff: (h1 t2 = let temp := (fun (t3 : T3) => match excluded_middle_informative (exists (t2 : T2), f t2 = t3) with
  | left H => h1 (proj1_sig (H10 t3 H))
  | right _ => t1
end) in temp (f t2)).
rewrite H11.
simpl.
elim (excluded_middle_informative (exists (t : T2), f t = f t2)).
move=> H12.
rewrite (H8 (proj1_sig (H10 (f t2) H12)) t2).
apply.
apply (proj2_sig (H10 (f t2) H12)).
elim.
exists t2.
reflexivity.
simpl.
elim (excluded_middle_informative (exists (t : T2), f t = f t2)).
move=> H12.
rewrite - (H8 t2 (proj1_sig (H10 (f t2) H12))).
reflexivity.
rewrite (proj2_sig (H10 (f t2) H12)).
reflexivity.
elim.
exists t2.
reflexivity.
move=> t3 H10.
apply (constructive_definite_description (fun (t2 : T2) => f t2 = t3)).
apply (proj1 (unique_existence (fun (t2 : T2) => f t2 = t3))).
apply conj.
apply H10.
move=> t21 t22 H11 H12.
apply H8.
rewrite H12.
apply H11.
apply NNPP.
move=> H9.
apply H7.
rewrite H1.
apply (proj1 (Formula_66_1 T1 (Count O))).
exists (fun (t1 : T1) => match H9 (Inhabited_intro T1 (Full_set T1) t1 (Full_intro T1 t1)) with
end).
exists (fun (n : Count O) => match le_not_lt O (proj1_sig n) (le_0_n (proj1_sig n)) (proj2_sig n) with
end).
apply conj.
move=> t1.
elim (H9 (Inhabited_intro T1 (Full_set T1) t1 (Full_intro T1 t1))).
move=> n.
elim (le_not_lt O (proj1_sig n) (le_0_n (proj1_sig n)) (proj2_sig n)).
rewrite - (CardPowNature T1 T2 C1 C2 H2 H4).
apply (Formula_1_1 (T2 -> T1)).
rewrite - (CardPowNature T1 T3 C1 C3 H2 H6).
apply (Formula_1_1 (T3 -> T1)).
rewrite H5.
apply (Formula_1_1 T3).
rewrite H3.
apply (Formula_1_1 T2).
rewrite H1.
apply (Formula_1_1 T1).
Qed.

Lemma Formula_3_11_2 : forall (C1 C2 D : CardT), CardLe C1 C2 -> CardLe (CardPow C1 D) (CardPow C2 D).
Proof.
move=> C1 C2 C3.
elim (proj2_sig C1).
move=> T1 H1.
suff: (proj1_sig C1 T1).
move=> H2.
elim (proj2_sig C2).
move=> T2 H3.
suff: (proj1_sig C2 T2).
move=> H4.
elim (proj2_sig C3).
move=> T3 H5.
suff: (proj1_sig C3 T3).
move=> H6.
rewrite - (CardLeNature T1 T2 C1 C2 H2 H4).
rewrite - (CardLeNature (T3 -> T1) (T3 -> T2) (CardPow C1 C3) (CardPow C2 C3)).
elim.
move=> f H7.
exists (fun (h : T3 -> T1) (t3 : T3) => f (h t3)).
move=> h1 h2 H8.
apply functional_extensionality.
move=> t3.
apply H7.
suff: (f (h1 t3) = let temp := (fun (t3 : T3) => f (h1 t3)) in temp t3).
rewrite H8.
apply.
reflexivity.
rewrite - (CardPowNature T1 T3 C1 C3 H2 H6).
apply (Formula_1_1 (T3 -> T1)).
rewrite - (CardPowNature T2 T3 C2 C3 H4 H6).
apply (Formula_1_1 (T3 -> T2)).
rewrite H5.
apply (Formula_1_1 T3).
rewrite H3.
apply (Formula_1_1 T2).
rewrite H1.
apply (Formula_1_1 T1).
Qed.

Lemma Formula_3_12 : forall (C D1 D2 : CardT), CardMult (CardPow C D1) (CardPow C D2) = CardPow C (CardPlus D1 D2).
Proof.
move=> C1 C2 C3.
elim (proj2_sig C1).
move=> T1 H1.
suff: (proj1_sig C1 T1).
move=> H2.
elim (proj2_sig C2).
move=> T2 H3.
suff: (proj1_sig C2 T2).
move=> H4.
elim (proj2_sig C3).
move=> T3 H5.
suff: (proj1_sig C3 T3).
move=> H6.
rewrite - (CardMultNature (T2 -> T1) (T3 -> T1) (CardPow C1 C2) (CardPow C1 C3)).
rewrite - (CardPowNature T1 (T2 + T3) C1 (CardPlus C2 C3)).
apply (proj1 (Formula_66_1 ((T2 -> T1) * (T3 -> T1)) (T2 + T3 -> T1))).
exists (fun (h : (T2 -> T1) * (T3 -> T1)) (t : T2 + T3) => match t with
  | inl t0 => fst h t0
  | inr t0 => snd h t0
end).
exists (fun (h : T2 + T3 -> T1) => (fun (t : T2) => h (inl t), fun (t : T3) => h (inr t))).
apply conj.
move=> h.
apply injective_projections.
reflexivity.
reflexivity.
move=> h.
apply functional_extensionality.
elim.
move=> t2.
reflexivity.
move=> t3.
reflexivity.
rewrite H1.
apply (Formula_1_1 T1).
rewrite - (CardPlusNature T2 T3 C2 C3 H4 H6).
apply (Formula_1_1 (T2 + T3)).
rewrite - (CardPowNature T1 T2 C1 C2 H2 H4).
apply (Formula_1_1 (T2 -> T1)).
rewrite - (CardPowNature T1 T3 C1 C3 H2 H6).
apply (Formula_1_1 (T3 -> T1)).
rewrite H5.
apply (Formula_1_1 T3).
rewrite H3.
apply (Formula_1_1 T2).
rewrite H1.
apply (Formula_1_1 T1).
Qed.

Lemma Formula_3_13 : forall (C1 C2 D : CardT), CardPow (CardMult C1 C2) D = CardMult (CardPow C1 D) (CardPow C2 D).
Proof.
move=> C1 C2 C3.
elim (proj2_sig C1).
move=> T1 H1.
suff: (proj1_sig C1 T1).
move=> H2.
elim (proj2_sig C2).
move=> T2 H3.
suff: (proj1_sig C2 T2).
move=> H4.
elim (proj2_sig C3).
move=> T3 H5.
suff: (proj1_sig C3 T3).
move=> H6.
rewrite - (CardPowNature (T1 * T2) T3 (CardMult C1 C2) C3).
rewrite - (CardMultNature (T3 -> T1) (T3 -> T2) (CardPow C1 C3) (CardPow C2 C3)).
apply (proj1 (Formula_66_1 (T3 -> T1 * T2) ((T3 -> T1) * (T3 -> T2)))).
exists (fun (h : T3 -> T1 * T2) => (fun (t : T3) => fst (h t), fun (t : T3) => snd (h t))).
exists (fun (h : (T3 -> T1) * (T3 -> T2)) (t : T3) => (fst h t, snd h t)).
apply conj.
move=> x.
apply functional_extensionality.
move=> t.
simpl.
elim (x t).
move=> a b.
reflexivity.
elim.
move=> y1 y2.
reflexivity.
rewrite - (CardPowNature T1 T3 C1 C3 H2 H6).
apply (Formula_1_1 (T3 -> T1)).
rewrite - (CardPowNature T2 T3 C2 C3 H4 H6).
apply (Formula_1_1 (T3 -> T2)).
rewrite - (CardMultNature T1 T2 C1 C2 H2 H4).
apply (Formula_1_1 (T1 * T2)).
apply H6.
rewrite H5.
apply (Formula_1_1 T3).
rewrite H3.
apply (Formula_1_1 T2).
rewrite H1.
apply (Formula_1_1 T1).
Qed.

Lemma Formula_3_14 : forall (C1 C2 C3 : CardT), CardPow (CardPow C1 C2) C3 = CardPow C1 (CardMult C2 C3).
Proof.
move=> C1 C2 C3.
elim (proj2_sig C1).
move=> T1 H1.
suff: (proj1_sig C1 T1).
move=> H2.
elim (proj2_sig C2).
move=> T2 H3.
suff: (proj1_sig C2 T2).
move=> H4.
elim (proj2_sig C3).
move=> T3 H5.
suff: (proj1_sig C3 T3).
move=> H6.
rewrite - (CardPowNature (T2 -> T1) T3 (CardPow C1 C2) C3).
rewrite - (CardPowNature T1 (T2 * T3) C1 (CardMult C2 C3)).
apply (proj1 (Formula_66_1 (T3 -> T2 -> T1) (T2 * T3 -> T1))).
exists (fun (h : T3 -> T2 -> T1) (t : T2 * T3) => h (snd t) (fst t)).
exists (fun (h : T2 * T3 -> T1) (t3 : T3) (t2 : T2) => h (t2, t3)).
apply conj.
move=> t.
reflexivity.
move=> t.
apply functional_extensionality.
elim.
move=> a b.
reflexivity.
apply H2.
rewrite - (CardMultNature T2 T3 C2 C3 H4 H6).
apply (Formula_1_1 (T2 * T3)).
rewrite - (CardPowNature T1 T2 C1 C2 H2 H4).
apply (Formula_1_1 (T2 -> T1)).
apply H6.
rewrite H5.
apply (Formula_1_1 T3).
rewrite H3.
apply (Formula_1_1 T2).
rewrite H1.
apply (Formula_1_1 T1).
Qed.

Lemma Formula_3_15 : forall (C : CardT), CardLt C (CardPow (CardN 2) C).
Proof.
move=> C.
elim (proj2_sig C).
move=> T H1.
suff: (proj1_sig C T).
move=> H2.
rewrite (CardPowEnsembleRelation C).
rewrite - (CardLtNature T (Ensemble T) C (CardEnsemble C) H2).
apply (Theorem_8 T).
rewrite - (CardEnsembleNature T C H2).
apply (Formula_1_1 (Ensemble T)).
rewrite H1.
apply (Formula_1_1 T).
Qed.

Lemma Formula_3_16_2 : CardPlus (Card nat) (Card nat) = Card nat.
Proof.
suff: (SameCard {n : nat | In nat even n} {n : nat | In nat odd n}).
move=> H1.
rewrite - (CardPlusNature {n : nat | In nat even n} {n : nat | In nat odd n} (Card nat) (Card nat)).
apply (proj1 (Formula_66_1 ({n : nat | In nat even n} + {n : nat | In nat odd n}) nat)).
exists (fun (m : {n : nat | In nat even n} + {n : nat | In nat odd n}) => match m with
  | inl m0 => proj1_sig m0
  | inr m0 => proj1_sig m0
end).
exists (fun (m : nat) => match even_odd_dec m with
  | left H => inl (exist even m H)
  | right H => inr (exist odd m H)
end).
apply conj.
elim.
move=> m.
elim (even_odd_dec (proj1_sig m)).
move=> H2.
apply (f_equal inl).
apply sig_map.
reflexivity.
move=> H2.
elim (not_even_and_odd (proj1_sig m) (proj2_sig m) H2).
move=> m.
elim (even_odd_dec (proj1_sig m)).
move=> H2.
elim (not_even_and_odd (proj1_sig m) H2 (proj2_sig m)).
move=> H2.
apply (f_equal inr).
apply sig_map.
reflexivity.
move=> y.
elim (even_odd_dec y).
move=> H2.
reflexivity.
move=> H2.
reflexivity.
apply Example_2.
apply (Formula_1_3 nat {n : nat | In nat even n} {n : nat | In nat odd n} Example_2 H1).
exists (fun (m : {n : nat | In nat even n}) => exist odd (S (proj1_sig m)) (odd_S (proj1_sig m) (proj2_sig m))).
apply InjSurjBij.
move=> m1 m2 H1.
apply sig_map.
apply (eq_add_S (proj1_sig m1) (proj1_sig m2)).
suff: (S (proj1_sig m1) = proj1_sig (exist odd (S (proj1_sig m1)) (odd_S (proj1_sig m1) (proj2_sig m1)))).
move=> H2.
rewrite H2.
rewrite H1.
reflexivity.
reflexivity.
elim.
move=> m H1.
suff: (exists (x : {n : nat | In nat even n}), S (proj1_sig x) = m).
elim.
move=> n H2.
exists n.
apply sig_map.
apply H2.
elim H1.
move=> n H2.
exists (exist even n H2).
reflexivity.
Qed.

Lemma Formula_3_16_1 : forall (C : CardT), CardLe C (Card nat) -> CardPlus C (Card nat) = Card nat.
Proof.
move=> C H1.
apply (Formula_1_7 (CardPlus C (Card nat)) (Card nat)).
rewrite - {2} Formula_3_16_2.
apply (Formula_3_4 C (Card nat) (Card nat) (Card nat)).
apply H1.
apply (Formula_1_6 (Card nat)).
elim (proj2_sig C).
move=> T H2.
suff: (proj1_sig C T).
move=> H3.
rewrite - (CardLeNature nat (T + nat) (Card nat) (CardPlus C (Card nat))).
exists (fun (m : nat) => inr m).
unfold Injective.
apply (injective_inr T nat).
apply (Formula_1_1 nat).
rewrite - (CardPlusNature T nat C (Card nat)).
apply (Formula_1_1 (T + nat)).
apply H3.
apply (Formula_1_1 nat).
rewrite H2.
apply (Formula_1_1 T).
Qed.

Lemma Formula_3_17_3 : CardPlus (Card R) (Card R) = Card R.
Proof.
suff: (forall (r1 r2 : R), (r1 < r2)%R -> SameCard {r : R | (r1 <= r < r2)%R} R).
move=> H1.
rewrite - (CardPlusNature {r : R | (0 <= r < 1)%R} {r : R | (1 <= r < 2)%R} (Card R) (Card R)).
apply (proj1 (Formula_66_1 ({r : R | (0 <= r < 1)%R} + {r : R | (1 <= r < 2)%R}) R)).
apply (Formula_1_3 ({r : R | (0 <= r < 1)%R} + {r : R | (1 <= r < 2)%R}) {r : R | (0 <= r < 2)%R} R).
suff: (0 <= 1)%R.
move=> H2.
suff: (1 < 2)%R.
move=> H3.
exists (fun (x : {r : R | (0 <= r < 1)%R} + {r : R | (1 <= r < 2)%R}) => match x with
  | inl x0 => exist (fun (r : R) => (0 <= r < 2)%R) (proj1_sig x0) (conj (proj1 (proj2_sig x0)) (Rlt_trans (proj1_sig x0) 1 2 (proj2 (proj2_sig x0)) H3))
  | inr x0 => exist (fun (r : R) => (0 <= r < 2)%R) (proj1_sig x0) (conj (Rle_trans 0 1 (proj1_sig x0) H2 (proj1 (proj2_sig x0))) (proj2 (proj2_sig x0)))
end).
exists (fun (x : {r : R | (0 <= r < 2)%R}) => match Rle_lt_dec 1 (proj1_sig x) with
  | left H => inr (exist (fun (r : R) => (1 <= r < 2)%R) (proj1_sig x) (conj H (proj2 (proj2_sig x))))
  | right H => inl (exist (fun (r : R) => (0 <= r < 1)%R) (proj1_sig x) (conj (proj1 (proj2_sig x)) H))
end).
apply conj.
elim.
move=> x.
simpl.
elim (Rle_lt_dec 1 (proj1_sig x)).
move=> H4.
elim (Rle_not_lt (proj1_sig x) 1 H4 (proj2 (proj2_sig x))).
move=> H4.
apply (f_equal inl).
apply sig_map.
reflexivity.
move=> x.
simpl.
elim (Rle_lt_dec 1 (proj1_sig x)).
move=> H4.
apply (f_equal inr).
apply sig_map.
reflexivity.
move=> H4.
elim (Rle_not_lt (proj1_sig x) 1 (proj1 (proj2_sig x)) H4).
move=> y.
elim (Rle_lt_dec 1 (proj1_sig y)).
move=> H4.
apply sig_map.
reflexivity.
move=> H4.
apply sig_map.
reflexivity.
apply (Rlt_plus_1 1).
left.
apply Rlt_0_1.
apply (H1 0 2 (Rlt_trans 0 1 2 Rlt_0_1 (Rlt_plus_1 1)))%R.
apply (Formula_1_2 {r : R | (0 <= r < 1)%R} R (H1 0 1 Rlt_0_1))%R.
apply (Formula_1_2 {r : R | (1 <= r < 2)%R} R (H1 1 2 (Rlt_plus_1 1)))%R.
move=> r1 r2 H1.
apply (Theorem_2 {r : R | (r1 <= r < r2)%R} R).
exists (fun (x : {r : R | (r1 <= r < r2)%R}) => proj1_sig x).
move=> x1 x2.
apply sig_map.
elim (Example_5 r1 r2 H1).
move=> f.
elim.
move=> g H2.
exists (fun (r : R) => exist (fun (r : R) => (r1 <= r < r2)%R) (proj1_sig (g r)) (conj (or_introl (proj1 (proj2_sig (g r)))) (proj2 (proj2_sig (g r))))).
move=> r3 r4 H3.
apply (BijInj R {x : R | (r1 < x < r2)%R} g).
exists f.
apply conj.
apply (proj2 H2).
apply (proj1 H2).
apply sig_map.
suff: (proj1_sig (g r3) = proj1_sig (exist (fun (r : R) => (r1 <= r < r2)%R) (proj1_sig (g r3)) (conj (or_introl (proj1 (proj2_sig (g r3)))) (proj2 (proj2_sig (g r3)))))).
move=> H4.
rewrite H4.
rewrite H3.
reflexivity.
reflexivity.
Qed.

Lemma Formula_3_17_1 : forall (C : CardT), CardLe C (Card R) -> CardPlus C (Card R) = Card R.
Proof.
move=> C H1.
apply (Formula_1_7 (CardPlus C (Card R)) (Card R)).
rewrite - {2} Formula_3_17_3.
apply (Formula_3_4 C (Card R) (Card R) (Card R)).
apply H1.
apply (Formula_1_6 (Card R)).
elim (proj2_sig C).
move=> T H2.
suff: (proj1_sig C T).
move=> H3.
rewrite - (CardLeNature R (T + R) (Card R) (CardPlus C (Card R))).
exists (fun (r : R) => inr r).
unfold Injective.
apply (injective_inr T R).
apply (Formula_1_1 R).
rewrite - (CardPlusNature T R C (Card R)).
apply (Formula_1_1 (T + R)).
apply H3.
apply (Formula_1_1 R).
rewrite H2.
apply (Formula_1_1 T).
Qed.

Lemma Formula_3_17_2 : CardPlus (Card nat) (Card R) = Card R.
Proof.
apply (Formula_3_17_1 (Card nat) (proj1 Theorem_7)).
Qed.

Lemma Formula_3_18_2 : CardMult (Card nat) (Card nat) = Card nat.
Proof.
rewrite - (CardMultNature nat nat (Card nat) (Card nat)).
apply (proj1 (Formula_66_1 (nat * nat) nat) (Formula_1_2 nat (nat * nat) Example_3)).
apply (Formula_1_1 nat).
apply (Formula_1_1 nat).
Qed.

Lemma Formula_3_18_1 : forall (C : CardT), CardLe (CardN 1) C -> CardLe C (Card nat) -> CardMult C (Card nat) = Card nat.
Proof.
move=> C.
elim (proj2_sig C).
move=> T H1.
suff: (proj1_sig C T).
move=> H2.
rewrite - (CardLeNature (Count 1) T (CardN 1) C).
elim.
move=> f H3 H4.
apply (Formula_1_7 (CardMult C (Card nat)) (Card nat)).
rewrite - {2} Formula_3_18_2.
apply (Formula_3_8 C (Card nat) (Card nat) (Card nat) H4 (Formula_1_6 (Card nat))).
rewrite - (CardMultNature T nat C (Card nat)).
rewrite - (CardLeNature nat (T * nat) (Card nat) (Card (T * nat)) (Formula_1_1 nat) (Formula_1_1 (T * nat))).
exists (fun (n : nat) => (f (exist (fun (m : nat) => m < 1) O (le_n 1)), n)).
move=> n1 n2 H5.
suff: (n1 = snd (f (exist (fun (m : nat) => m < 1) 0 (le_n 1)), n1)).
move=> H6.
rewrite H6.
rewrite H5.
reflexivity.
reflexivity.
apply H2.
apply (Formula_1_1 nat).
apply (Formula_1_1 (Count 1)).
apply H2.
rewrite H1.
apply (Formula_1_1 T).
Qed.

Lemma Formula_3_19_2 : CardPow (CardN 2) (Card nat) = Card R.
Proof.
rewrite - (CardPowNature (Count 2) nat (CardN 2) (Card nat) (Formula_1_1 (Count 2)) (Formula_1_1 nat)).
apply (proj1 (Formula_66_1 (nat -> Count 2) R)).
apply Formula_85_3.
Qed.

Lemma Formula_3_19_3 : CardPow (Card nat) (Card nat) = Card R.
Proof.
rewrite - Formula_3_19_2.
apply (Formula_1_7 (CardPow (Card nat) (Card nat)) (CardPow (CardN 2) (Card nat))).
rewrite - {3} Formula_3_18_2.
rewrite - (Formula_3_14 (CardN 2) (Card nat) (Card nat)).
apply (Formula_3_11_2 (Card nat) (CardPow (CardN 2) (Card nat)) (Card nat) (proj1 (Formula_3_15 (Card nat)))).
apply (Formula_3_11_2 (CardN 2) (Card nat) (Card nat)).
rewrite - (CardLeNature (Count 2) nat (CardN 2) (Card nat) (Formula_1_1 (Count 2)) (Formula_1_1 nat)).
exists (fun (m : Count 2) => proj1_sig m).
move=> m1 m2.
apply sig_map.
Qed.

Lemma Formula_3_19_1 : forall (C : CardT), CardLe (CardN 2) C -> CardLe C (Card nat) -> CardPow C (Card nat) = Card R.
Proof.
move=> C H1 H2.
apply (Formula_1_7 (CardPow C (Card nat)) (Card R)).
rewrite - Formula_3_19_3.
apply (Formula_3_11_2 C (Card nat) (Card nat) H2).
rewrite - Formula_3_19_2.
apply (Formula_3_11_2 (CardN 2) C (Card nat) H1).
Qed.

Lemma Formula_3_20_3 : CardMult (Card R) (Card R) = Card R.
Proof.
rewrite - Formula_3_19_2.
rewrite (Formula_3_12 (CardN 2) (Card nat) (Card nat)).
rewrite Formula_3_16_2.
reflexivity.
Qed.

Lemma Formula_3_20_1 : forall (C : CardT), CardLe (CardN 1) C -> CardLe C (Card R) -> CardMult C (Card R) = Card R.
Proof.
move=> C.
elim (proj2_sig C).
move=> T H1.
suff: (proj1_sig C T).
move=> H2.
rewrite - (CardLeNature (Count 1) T (CardN 1) C).
elim.
move=> f H3 H4.
apply (Formula_1_7 (CardMult C (Card R)) (Card R)).
rewrite - {2} Formula_3_20_3.
apply (Formula_3_8 C (Card R) (Card R) (Card R) H4 (Formula_1_6 (Card R))).
rewrite - (CardMultNature T R C (Card R)).
rewrite - (CardLeNature R (T * R) (Card R) (Card (T * R)) (Formula_1_1 R) (Formula_1_1 (T * R))).
exists (fun (r : R) => (f (exist (fun (m : nat) => m < 1) O (le_n 1)), r)).
move=> r1 r2 H5.
suff: (r1 = snd (f (exist (fun (m : nat) => m < 1) 0 (le_n 1)), r1)).
move=> H6.
rewrite H6.
rewrite H5.
reflexivity.
reflexivity.
apply H2.
apply (Formula_1_1 R).
apply (Formula_1_1 (Count 1)).
apply H2.
rewrite H1.
apply (Formula_1_1 T).
Qed.

Lemma Formula_3_20_2 : CardMult (Card nat) (Card R) = Card R.
Proof.
apply (Formula_3_20_1 (Card nat)).
rewrite - (CardLeNature (Count 1) nat (CardN 1) (Card nat) (Formula_1_1 (Count 1)) (Formula_1_1 nat)).
exists (fun (m : Count 1) => proj1_sig m).
move=> m1 m2.
apply sig_map.
apply (proj1 Theorem_7).
Qed.

Lemma Formula_3_21_3 : CardPow (CardN 2) (Card R) = CardPow (Card R) (Card R).
Proof.
apply (Formula_1_7 (CardPow (CardN 2) (Card R)) (CardPow (Card R) (Card R))).
apply (Formula_3_11_2 (CardN 2) (Card R) (Card R)).
rewrite - (CardLeNature (Count 2) R (CardN 2) (Card R) (Formula_1_1 (Count 2)) (Formula_1_1 R)).
exists (fun (m : Count 2) => INR (proj1_sig m)).
move=> m1 m2 H1.
apply sig_map.
apply (INR_eq (proj1_sig m1) (proj1_sig m2) H1).
rewrite - {3} Formula_3_20_3.
rewrite - (Formula_3_14 (CardN 2) (Card R) (Card R)).
apply (Formula_3_11_2 (Card R) (CardPow (CardN 2) (Card R)) (Card R) (proj1 (Formula_3_15 (Card R)))).
Qed.

Lemma Formula_3_21_1 : forall (C : CardT), CardLe (CardN 2) C -> CardLe C (Card R) -> CardPow (CardN 2) (Card R) = CardPow C (Card R).
Proof.
move=> C H1 H2.
apply (Formula_1_7 (CardPow (CardN 2) (Card R)) (CardPow C (Card R))).
apply (Formula_3_11_2 (CardN 2) C (Card R) H1).
rewrite Formula_3_21_3.
apply (Formula_3_11_2 C (Card R) (Card R) H2).
Qed.

Lemma Formula_3_21_2 : CardPow (CardN 2) (Card R) = CardPow (Card nat) (Card R).
Proof.
apply (Formula_3_21_1 (Card nat)).
rewrite - (CardLeNature (Count 2) nat (CardN 2) (Card nat) (Formula_1_1 (Count 2)) (Formula_1_1 nat)).
exists (fun (m : Count 2) => proj1_sig m).
move=> m1 m2.
apply sig_map.
apply (proj1 Theorem_7).
Qed.

Lemma Formula_85_1 : SameCard (nat * R) R.
Proof.
apply (proj2 (Formula_66_1 (nat * R) R)).
rewrite (CardMultNature nat R (Card nat) (Card R) (Formula_1_1 nat) (Formula_1_1 R)).
apply Formula_3_20_2.
Qed.

Lemma Formula_85_2 : SameCard (R * R) R.
Proof.
apply (proj2 (Formula_66_1 (R * R) R)).
rewrite (CardMultNature R R (Card R) (Card R) (Formula_1_1 R) (Formula_1_1 R)).
apply Formula_3_20_3.
Qed.

Lemma Formula_85_4 : SameCard (nat -> nat) R.
Proof.
apply (proj2 (Formula_66_1 (nat -> nat) R)).
rewrite (CardPowNature nat nat (Card nat) (Card nat) (Formula_1_1 nat) (Formula_1_1 nat)).
apply Formula_3_19_3.
Qed.

Definition Formula_85_5 : CardLt (Card R) (CardPow (CardN 2) (Card R)) := Formula_3_15 (Card R).

Lemma Formula_85_6 : proj1_sig (CardPow (CardN 2) (Card R)) (R -> R).
Proof.
rewrite Formula_3_21_3.
rewrite - (CardPowNature R R (Card R) (Card R) (Formula_1_1 R) (Formula_1_1 R)).
apply (Formula_1_1 (R -> R)).
Qed.
