Add LoadPath "Tools" as Tools.
Add LoadPath "BasicProperty" as BasicProperty.
Add LoadPath "LibraryExtension" as LibraryExtension.

From mathcomp Require Import ssreflect.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Image.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.
Require Import Tools.MySum.
Require Import BasicProperty.MappingProperty.
Require Import LibraryExtension.EnsemblesExtension.

Lemma Formula_1_4 : forall (T : Type) (A B C : Ensemble T), Included T A B -> Included T B C -> Included T A C.
Proof.
move=> T A B C H1 H2 t H3.
apply (H2 t (H1 t H3)).
Qed.

Lemma Formula_1_5 : forall (T : Type) (A : Ensemble T), Included T (Empty_set T) A.
Proof.
move=> T A t.
elim.
Qed.

Lemma Formula_2_2_1 : forall (T : Type) (A B : Ensemble T), Included T A (Union T A B).
Proof.
move=> T A B t H1.
left.
apply H1.
Qed.

Lemma Formula_2_2_2 : forall (T : Type) (A B : Ensemble T), Included T B (Union T A B).
Proof.
move=> T A B t H1.
right.
apply H1.
Qed.

Lemma Formula_2_3 : forall (T : Type) (A B C : Ensemble T), Included T A C -> Included T B C -> Included T (Union T A B) C.
Proof.
move=> T A B C H1 H2 t.
elim.
apply H1.
apply H2.
Qed.

Lemma Formula_2_4 : forall (T : Type) (A : Ensemble T), (Union T A A) = A.
Proof.
move=> T A.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0.
apply.
move=> t0.
apply.
apply (Formula_2_2_1 T A A).
Qed.

Lemma Formula_2_5 : forall (T : Type) (A B : Ensemble T), (Union T A B) = (Union T B A).
Proof.
move=> T.
suff: (forall (A B : Ensemble T), Included T (Union T A B) (Union T B A)).
move=> H1 A B.
apply Extensionality_Ensembles.
apply conj.
apply (H1 A B).
apply (H1 B A).
move=> A B t.
elim.
apply (Union_intror T B A).
apply (Union_introl T B A).
Qed.

Lemma Formula_2_6 : forall (T : Type) (A B C : Ensemble T), (Union T (Union T A B) C) = (Union T A (Union T B C)).
Proof.
move=> T A B C.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0.
elim.
apply (Union_introl T A (Union T B C)).
move=> t1 H1.
apply (Union_intror T A (Union T B C) t1 (Union_introl T B C t1 H1)).
move=> t0 H1.
apply (Union_intror T A (Union T B C) t0 (Union_intror T B C t0 H1)).
move=> t.
elim.
move=> t0 H1.
apply (Union_introl T (Union T A B) C t0 (Union_introl T A B t0 H1)).
move=> t0.
elim.
move=> t1 H1.
apply (Union_introl T (Union T A B) C t1 (Union_intror T A B t1 H1)).
apply (Union_intror T (Union T A B) C).
Qed.

Lemma Formula_2_7 : forall (T : Type) (A B : Ensemble T), Included T A B <-> (Union T A B) = B.
Proof.
move=> T A B.
apply conj.
move=> H1.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
apply H1.
move=> t0.
apply.
apply (Formula_2_2_2 T A B).
move=> H1.
rewrite - H1.
move=> t.
apply (Union_introl T A B).
Qed.

Lemma Formula_2_8 : forall (T : Type) (A B C : Ensemble T), Included T A B -> Included T (Union T A C) (Union T B C).
Proof.
move=> T A B C H1 t.
elim.
move=> t0 H2.
apply (Union_introl T B C t0 (H1 t0 H2)).
apply (Union_intror T B C).
Qed.

Lemma Formula_2_9 : forall (T : Type) (A : Ensemble T), (Union T (Empty_set T) A) = A.
Proof.
move=> T A.
apply (proj1 (Formula_2_7 T (Empty_set T) A) (Formula_1_5 T A)).
Qed.

Lemma Formula_2_9_rev : forall (T : Type) (A : Ensemble T), (Union T A (Empty_set T)) = A.
Proof.
move=> T A.
rewrite (Formula_2_5 T A (Empty_set T)).
apply (Formula_2_9 T A).
Qed.

Definition UnionCM (T : Type) : CommutativeMonoid := mkCommutativeMonoid (Ensemble T) (Empty_set T) (Union T) (Formula_2_5 T) (Formula_2_9_rev T) (Formula_2_6 T).

Definition Disjoint (T : Type) (A B : Ensemble T) := (Intersection T A B) = (Empty_set T).

Lemma Formula_2_2_1_dash : forall (T : Type) (A B : Ensemble T), Included T (Intersection T A B) A.
Proof.
move=> T A B t.
elim.
move=> t0 H1 H2.
apply H1.
Qed.

Lemma Formula_2_2_2_dash : forall (T : Type) (A B : Ensemble T), Included T (Intersection T A B) B.
Proof.
move=> T A B t.
elim.
move=> t0 H1 H2.
apply H2.
Qed.

Lemma Formula_2_3_dash : forall (T : Type) (A B C : Ensemble T), Included T C A -> Included T C B -> Included T C (Intersection T A B).
Proof.
move=> T A B C H1 H2 t H3.
apply (Intersection_intro T A B t (H1 t H3) (H2 t H3)).
Qed.

Lemma Formula_2_4_dash : forall (T : Type) (A : Ensemble T), (Intersection T A A) = A.
Proof.
move=> T A.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0 H1 H2.
apply H1.
move=> t H1.
apply (Intersection_intro T A A t H1 H1).
Qed.

Lemma Formula_2_5_dash : forall (T : Type) (A B : Ensemble T), (Intersection T A B) = (Intersection T B A).
Proof.
move=> T.
suff: (forall (A B : Ensemble T), Included T (Intersection T A B) (Intersection T B A)).
move=> H1 A B.
apply Extensionality_Ensembles.
apply conj.
apply (H1 A B).
apply (H1 B A).
move=> A B t.
elim.
move=> t0 H1 H2.
apply (Intersection_intro T B A t0 H2 H1).
Qed.

Lemma Formula_2_6_dash : forall (T : Type) (A B C : Ensemble T), (Intersection T (Intersection T A B) C) = (Intersection T A (Intersection T B C)).
Proof.
move=> T A B C.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0.
elim.
move=> t1 H1 H2 H3.
apply (Intersection_intro T A (Intersection T B C) t1 H1 (Intersection_intro T B C t1 H2 H3)).
move=> t.
elim.
move=> t0 H1 H2.
suff: (In T A t0).
elim H2.
move=> t1 H3 H4 H5.
apply (Intersection_intro T (Intersection T A B) C t1 (Intersection_intro T A B t1 H5 H3) H4).
apply H1.
Qed.

Lemma Formula_2_7_dash : forall (T : Type) (A B : Ensemble T), Included T A B <-> (Intersection T A B) = A.
Proof.
move=> T A B.
apply conj.
move=> H1.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0 H2 H3.
apply H2.
move=> t H2.
apply (Intersection_intro T A B t H2 (H1 t H2)).
move=> H1.
rewrite - H1.
move=> t.
elim.
move=> t0 H2 H3.
apply H3.
Qed.

Lemma Formula_2_8_dash : forall (T : Type) (A B C : Ensemble T), Included T A B -> Included T (Intersection T A C) (Intersection T B C).
Proof.
move=> T A B C H1 t.
elim.
move=> t0 H2 H3.
apply (Intersection_intro T B C t0 (H1 t0 H2) H3).
Qed.

Lemma Formula_2_9_dash : forall (T : Type) (A : Ensemble T), (Intersection T (Empty_set T) A) = (Empty_set T).
Proof.
move=> T A.
apply (proj1 (Formula_2_7_dash T (Empty_set T) A) (Formula_1_5 T A)).
Qed.

Lemma Intersection_O_r : forall (T : Type) (A : Ensemble T), (Intersection T A (Full_set T)) = A.
Proof.
move=> T A.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0 H1 H2.
apply H1.
move=> t H1.
apply (Intersection_intro T A (Full_set T) t H1 (Full_intro T t)).
Qed.

Definition IntersectionCM (T : Type) : CommutativeMonoid := mkCommutativeMonoid (Ensemble T) (Full_set T) (Intersection T) (Formula_2_5_dash T) (Intersection_O_r T) (Formula_2_6_dash T).

Lemma Formula_2_10 : forall (T : Type) (A B C : Ensemble T), Intersection T (Union T A B) C = Union T (Intersection T A C) (Intersection T B C).
Proof.
move=> T A B C.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0.
elim.
move=> t1 H1 H2.
apply (Union_introl T (Intersection T A C) (Intersection T B C) t1 (Intersection_intro T A C t1 H1 H2)).
move=> t1 H1 H2.
apply (Union_intror T (Intersection T A C) (Intersection T B C) t1 (Intersection_intro T B C t1 H1 H2)).
move=> t.
elim.
move=> t0.
elim.
move=> t1 H1 H2.
apply (Intersection_intro T (Union T A B) C t1 (Union_introl T A B t1 H1) H2).
move=> t0.
elim.
move=> t1 H1 H2.
apply (Intersection_intro T (Union T A B) C t1 (Union_intror T A B t1 H1) H2).
Qed.

Lemma Formula_2_10_dash : forall (T : Type) (A B C : Ensemble T), Union T (Intersection T A B) C = Intersection T (Union T A C) (Union T B C).
Proof.
move=> T A B C.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0.
elim.
move=> t1 H1 H2.
apply (Intersection_intro T (Union T A C) (Union T B C) t1 (Union_introl T A C t1 H1) (Union_introl T B C t1 H2)).
move=> t0 H1.
apply (Intersection_intro T (Union T A C) (Union T B C) t0 (Union_intror T A C t0 H1) (Union_intror T B C t0 H1)).
move=> t.
elim.
move=> t0.
elim.
move=> t1 H1 H2.
suff: (In T A t1).
elim H2.
move=> t2 H3 H4.
apply (Union_introl T (Intersection T A B) C t2 (Intersection_intro T A B t2 H4 H3)).
move=> t2 H3 H4.
apply (Union_intror T (Intersection T A B) C t2 H3).
apply H1.
move=> t1 H1 H2.
apply (Union_intror T (Intersection T A B) C t1 H1).
Qed.

Lemma Formula_2_11 : forall (T : Type) (A B : Ensemble T), Intersection T (Union T A B) A = A.
Proof.
move=> T A B.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0 H1 H2.
apply H2.
move=> t H1.
apply (Intersection_intro T (Union T A B) A t (Union_introl T A B t H1) H1).
Qed.

Lemma Formula_2_11_dash : forall (T : Type) (A B : Ensemble T), Union T (Intersection T A B) A = A.
Proof.
move=> T A B.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0.
elim.
move=> t1 H1 H2.
apply H1.
apply (fun (t : T) (H : In T A t) => H).
move=> t H1.
apply (Union_intror T (Intersection T A B) A t H1).
Qed.

Lemma ComplementSetminus : forall (T : Type) (A : Ensemble T), (Complement T A) = (Setminus T (Full_set T) A).
Proof.
move=> T A.
apply Extensionality_Ensembles.
apply conj.
move=> t H1.
apply conj.
apply (Full_intro T t).
apply H1.
move=> t.
elim.
move=> H1 H2.
apply H2.
Qed.

Lemma Formula_2_12_1 : forall (T : Type) (A : Ensemble T), Union T A (Complement T A) = Full_set T.
Proof.
move=> T A.
apply Extensionality_Ensembles.
apply conj.
move=> t H1.
apply (Full_intro T t).
move=> t H1.
elim (classic (In T A t)).
move=> H2.
left.
apply H2.
move=> H2.
right.
apply H2.
Qed.

Lemma Formula_2_12_2 : forall (T : Type) (A : Ensemble T), Intersection T A (Complement T A) = Empty_set T.
Proof.
move=> T A.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0 H1 H2.
apply False_ind.
apply (H2 H1).
move=> t.
elim.
Qed.

Lemma Formula_2_13 : forall (T : Type) (A : Ensemble T), (Complement T (Complement T A)) = A.
Proof.
move=> T A.
apply Extensionality_Ensembles.
apply conj.
move=> t H1.
apply NNPP.
apply H1.
move=> t H1 H2.
apply (H2 H1).
Qed.

Lemma Formula_2_14_1 : forall (T : Type), (Complement T (Empty_set T)) = (Full_set T).
Proof.
move=> T.
apply Extensionality_Ensembles.
apply conj.
move=> t H1.
apply (Full_intro T t).
move=> t H1.
elim.
Qed.

Lemma Formula_2_14_2 : forall (T : Type), (Complement T (Full_set T)) = (Empty_set T).
Proof.
move=> T.
apply Extensionality_Ensembles.
apply conj.
move=> t H1.
apply False_ind.
apply H1.
apply (Full_intro T t).
move=> t.
elim.
Qed.

Lemma Formula_2_15 : forall (T : Type) (A B : Ensemble T), (Included T A B) <-> (Included T (Complement T B) (Complement T A)).
Proof.
move=> T A B.
apply conj.
move=> H1 t H2 H3.
apply (H2 (H1 t H3)).
move=> H1 t H2.
apply NNPP.
move=> H3.
apply (H1 t H3 H2).
Qed.

Lemma Formula_2_16 : forall (T : Type) (A B : Ensemble T), (Complement T (Union T A B)) = (Intersection T (Complement T A) (Complement T B)).
Proof.
move=> T A B.
apply Extensionality_Ensembles.
apply conj.
move=> t H1.
apply (Intersection_intro T (Complement T A) (Complement T B) t).
move=> H2.
apply (H1 (Union_introl T A B t H2)).
move=> H2.
apply (H1 (Union_intror T A B t H2)).
move=> t.
elim.
move=> t0 H1 H2 H3.
suff: (In T (Complement T A) t0).
suff: (In T (Complement T B) t0).
elim H3.
move=> t1 H4 H5 H6.
apply (H6 H4).
move=> t1 H4 H5 H6.
apply (H5 H4).
apply H2.
apply H1.
Qed.

Lemma Formula_2_16_dash : forall (T : Type) (A B : Ensemble T), (Complement T (Intersection T A B)) = (Union T (Complement T A) (Complement T B)).
Proof.
move=> T A B.
apply Extensionality_Ensembles.
apply conj.
move=> t H1.
apply NNPP.
move=> H2.
apply H1.
apply (Intersection_intro T A B t).
apply NNPP.
move=> H3.
apply H2.
left.
apply H3.
apply NNPP.
move=> H3.
apply H2.
right.
apply H3.
move=> t H1.
elim H1.
move=> t0 H2 H3.
apply H2.
elim H3.
move=> t1 H4 H5.
apply H4.
move=> t0 H2 H3.
apply H2.
elim H3.
move=> t1 H4 H5.
apply H5.
Qed.

Lemma Formula_P18_1 : forall (T : Type), (Full_set T) = (Empty_set T) -> (Full_set (Ensemble T)) = (Singleton (Ensemble T) (Empty_set T)).
Proof.
move=> T H1.
apply Extensionality_Ensembles.
apply conj.
move=> t H2.
suff: (t = Empty_set T).
move=> H3.
rewrite H3.
apply (In_singleton (Ensemble T) (Empty_set T)).
apply Extensionality_Ensembles.
apply conj.
rewrite - H1.
move=> x H3.
apply (Full_intro T x).
move=> x.
elim.
move=> t H2.
apply (Full_intro (Ensemble T) t).
Qed.

Lemma Formula_P18_2_sub : forall (N : nat), {f : (Ensemble {n : nat | n < N}) -> {n : nat | n < 2 ^ N} | Bijective f}.
Proof.
move=> N.
elim (CountPow N 2).
move=> F H1.
suff: (O < 2).
move=> H2.
suff: (1 < 2).
move=> H3.
exists (compose F (fun (t : Ensemble {n : nat | n < N}) => (fun (k : {m : nat | m < N}) => match excluded_middle_informative (In {n : nat | n < N} t k) with
  | left _ => exist (fun (k : nat) => k < 2) O H2
  | right _ => exist (fun (k : nat) => k < 2) 1 H3
end))).
apply BijChain.
exists (fun (k : ({n : nat | n < N} -> {n : nat | n < 2})) (t : {n : nat | n < N}) => proj1_sig (k t) = O).
apply conj.
move=> l.
apply Extensionality_Ensembles.
apply conj.
move=> t.
unfold In.
elim (excluded_middle_informative (l t)).
move=> H4 H5.
apply H4.
move=> H4 H5.
apply False_ind.
apply (lt_irrefl O).
rewrite - {2} H5.
apply (le_n 1).
move=> t.
unfold In.
elim (excluded_middle_informative (l t)).
move=> H4 H5.
reflexivity.
move=> H4 H5.
apply False_ind.
apply (H4 H5).
move=> u.
apply functional_extensionality.
move=> k.
elim (excluded_middle_informative (In {n : nat | n < N} (fun (t : {n : nat | n < N}) => proj1_sig (u t) = 0) k)).
move=> H4.
apply sig_map.
rewrite H4.
reflexivity.
move=> H4.
apply sig_map.
elim (le_lt_or_eq (proj1_sig (u k)) 1).
move=> H5.
apply False_ind.
apply H4.
apply (le_antisym (proj1_sig (u k)) 0).
apply (le_S_n (proj1_sig (u k)) O H5).
apply (le_0_n (proj1_sig (u k))).
move=> H5.
rewrite H5.
reflexivity.
apply (le_S_n (proj1_sig (u k)) 1 (proj2_sig (u k))).
apply H1.
apply (le_n 2).
apply (le_S 1 1 (le_n 1)).
Qed.

Lemma Formula_P18_2 : forall (T : Type) (n : nat), cardinal T (Full_set T) n -> cardinal (Ensemble T) (Full_set (Ensemble T)) (2 ^ n).
Proof.
move=> T n H1.
apply CountCardinalBijective.
elim (proj2 (CountCardinalBijective T n) H1).
move=> F H2.
elim H2.
move=> FI H3.
elim (Formula_P18_2_sub n).
move=> G.
elim.
move=> GI H4.
exists (compose (fun (X : Ensemble {m : nat | m < n}) (t : T) => In {m : nat | m < n} X (FI t)) GI).
apply BijChain.
exists G.
apply conj.
apply (proj2 H4).
apply (proj1 H4).
exists (fun (Y : Ensemble T) (t : {m : nat | m < n}) => In T Y (F t)).
apply conj.
move=> X.
apply Extensionality_Ensembles.
apply conj.
move=> m.
unfold In.
rewrite (proj1 H3 m).
apply.
move=> m.
unfold In.
rewrite (proj1 H3 m).
apply.
move=> Y.
apply Extensionality_Ensembles.
apply conj.
move=> t.
unfold In.
rewrite (proj2 H3 t).
apply.
move=> t.
unfold In.
rewrite (proj2 H3 t).
apply.
Qed.

Lemma Formula_2_17 : forall (U T : Type) (X : U -> Ensemble T) (u : U), Included T (X u) (UnionT T U X).
Proof.
move=> U T X u t H1.
apply (UnionT_intro T U X t u H1).
Qed.

Lemma Formula_2_18 : forall (U T : Type) (X : U -> Ensemble T) (A : Ensemble T), (forall (u : U), Included T (X u) A) -> Included T (UnionT T U X) A.
Proof.
move=> U T X A H1 t.
elim.
move=> t0 u H2.
apply (H1 u t0 H2).
Qed.

Lemma Formula_2_17_dash : forall (U T : Type) (X : U -> Ensemble T) (u : U), Included T (IntersectionT T U X) (X u).
Proof.
move=> U T X u t.
elim.
move=> t0 H1.
apply (H1 u).
Qed.

Lemma Formula_2_18_dash : forall (U T : Type) (X : U -> Ensemble T) (A : Ensemble T), (forall (u : U), Included T A (X u)) -> Included T A (IntersectionT T U X).
Proof.
move=> U T X A H1 t H2.
apply (IntersectionT_intro T U X t (fun (u : U) => H1 u t H2)).
Qed.

Definition Correspondence (U T : Type) := U -> (Ensemble T).

Definition CorrespondenceGraph (U T : Type) (G : Correspondence U T) := fun (x : U * T) => In T (G (fst x)) (snd x).

Lemma Formula_3_1 : forall (U T : Type) (G : Correspondence U T) (u : U), G u = (fun (t : T) => In (U * T) (CorrespondenceGraph U T G) (u, t)).
Proof.
move=> U T G u.
reflexivity.
Qed.

Lemma Theorem_1 : forall (U T : Type) (X : Ensemble (U * T)), exists! (G : Correspondence U T), X = (CorrespondenceGraph U T G).
Proof.
move=> U T X.
apply (unique_existence (fun (G : Correspondence U T) => X = (fun (x : U * T) => In T (G (fst x)) (snd x)))).
apply conj.
exists (fun (u : U) (t : T) => In (U * T) X (u, t)).
apply Extensionality_Ensembles.
apply conj.
move=> x.
unfold In.
rewrite (surjective_pairing x).
apply.
move=> x.
unfold In.
rewrite (surjective_pairing x).
apply.
move=> g1 g2 H1 H2.
apply functional_extensionality.
move=> u.
apply Extensionality_Ensembles.
apply conj.
move=> t H3.
suff: (In (U * T) X (u, t)).
rewrite H2.
apply.
rewrite H1.
apply H3.
move=> t H3.
suff: (In (U * T) X (u, t)).
rewrite H1.
apply.
rewrite H2.
apply H3.
Qed.

Definition InverseCorrespondence (U T : Type) (G : Correspondence U T) : Correspondence T U := fun (t : T) (u : U) => In T (G u) t.

Definition CorrespondenceDomain (U T : Type) (G : Correspondence U T) := (fun (u : U) => exists (t : T), In (U * T) (CorrespondenceGraph U T G) (u, t)).

Definition CorrespondenceRange (U T : Type) (G : Correspondence U T) := (fun (t : T) => exists (u : U), In (U * T) (CorrespondenceGraph U T G) (u, t)).

Lemma Formula_3_2 : forall (U T : Type) (G : Correspondence U T) (u : U) (t : T), In T (G u) t <-> In U (InverseCorrespondence U T G t) u.
Proof.
move=> U T G u t.
apply conj.
apply.
apply.
Qed.

Lemma Formula_P27_1 : forall (U T : Type) (G : Correspondence U T), (CorrespondenceGraph T U (InverseCorrespondence U T G)) = fun (x : (T * U)) => In (U * T) (CorrespondenceGraph U T G) (snd x, fst x).
Proof.
move=> U T G.
reflexivity.
Qed.

Lemma Formula_3_3_1 : forall (U T : Type) (G : Correspondence U T), CorrespondenceDomain T U (InverseCorrespondence U T G) = CorrespondenceRange U T G.
Proof.
move=> U T G.
reflexivity.
Qed.

Lemma Formula_3_3_2 : forall (U T : Type) (G : Correspondence U T), CorrespondenceRange T U (InverseCorrespondence U T G) = CorrespondenceDomain U T G.
Proof.
move=> U T G.
reflexivity.
Qed.

Lemma Formula_3_4 : forall (U T : Type) (G : Correspondence U T), InverseCorrespondence T U (InverseCorrespondence U T G) = G.
Proof.
move=> U T G.
reflexivity.
Qed.

Lemma Formula_P27_2 : forall (U T : Type) (G : Correspondence U T) (t : T), (InverseCorrespondence U T G t <> Empty_set U) <-> In T (CorrespondenceRange U T G) t.
Proof.
move=> U T G t.
apply conj.
move=> H1.
apply NNPP.
move=> H2.
apply H1.
apply Extensionality_Ensembles.
apply conj.
move=> u H3.
apply False_ind.
apply H2.
exists u.
apply H3.
move=> u.
elim.
move=> H1 H2.
elim H1.
move=> u H3.
suff: (In U (InverseCorrespondence U T G t) u).
rewrite H2.
elim.
apply H3.
Qed.

Lemma Theorem_2 : forall (U T : Type) (X : Ensemble (U * T)), (exists (f : U -> T), X = (fun (x : U * T) => snd x = f (fst x))) <-> forall (u : U), exists! (t : T), In (U * T) X (u, t).
Proof.
move=> U T X.
apply conj.
elim.
move=> f H1 u.
apply (unique_existence (fun (t : T) => In (U * T) X (u, t))).
apply conj.
exists (f u).
rewrite H1.
reflexivity.
move=> t1 t2.
rewrite H1.
move=> H2 H3.
suff: (t1 = snd (u , t1)).
move=> H4.
rewrite H4.
suff: (t2 = snd (u , t2)).
move=> H5.
rewrite H5.
rewrite H2.
rewrite H3.
reflexivity.
reflexivity.
reflexivity.
move=> H1.
suff: (forall (u : U), {t : T | In (U * T) X (u, t)}).
move=> H2.
exists (fun (u : U) => proj1_sig (H2 u)).
apply Extensionality_Ensembles.
apply conj.
move=> x H3.
unfold In.
suff: (uniqueness (fun (t : T) => In (U * T) X (fst x, t))).
move=> H4.
apply H4.
rewrite - (surjective_pairing x).
apply H3.
apply (proj2_sig (H2 (fst x))).
apply unique_existence.
apply (H1 (fst x)).
move=> u H3.
rewrite (surjective_pairing u).
rewrite H3.
apply (proj2_sig (H2 (fst u))).
move=> u.
apply constructive_definite_description.
apply (H1 u).
Qed.

Inductive Inverse_Im (U V : Type) (Y : Ensemble V) (f : U -> V) : Ensemble U := Inverse_Im_intro : forall x : U, In V Y (f x) -> In U (Inverse_Im U V Y f) x.

Lemma Formula_P30 : forall (U T : Type) (X : Ensemble U) (f : U -> T), Im U T X f = Empty_set T <-> X = Empty_set U.
Proof.
move=> U T X f.
apply conj.
move=> H1.
apply Extensionality_Ensembles.
apply conj.
move=> u H2.
apply False_ind.
suff: (In T (Im U T X f) (f u)).
rewrite H1.
elim.
apply (Im_intro U T X f u).
apply H2.
reflexivity.
move=> u.
elim.
move=> H1.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> u.
rewrite H1.
elim.
move=> t.
elim.
Qed.

Lemma Formula_P31 : forall (U T : Type) (f : U -> T), Inverse_Im U T (Full_set T) f = Full_set U.
Proof.
move=> U T f.
apply Extensionality_Ensembles.
apply conj.
move=> u H1.
apply (Full_intro U u).
move=> u H1.
apply (Inverse_Im_intro U T (Full_set T) f u (Full_intro T (f u))).
Qed.

Lemma Formula_4_1 : forall (U T : Type) (f : U -> T) (X1 X2 : Ensemble U), Included U X1 X2 -> Included T (Im U T X1 f) (Im U T X2 f).
Proof.
move=> U T f X1 X2 H1 t.
elim.
move=> x H2 y H3.
apply (Im_intro U T X2 f x (H1 x H2) y H3).
Qed.

Lemma Formula_4_2 : forall (U T : Type) (f : U -> T) (X1 X2 : Ensemble U), (Im U T (Union U X1 X2) f) = (Union T (Im U T X1 f) (Im U T X2 f)).
Proof.
move=> U T f X1 X2.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> x.
elim.
move=> u H1 y H2.
left.
apply (Im_intro U T X1 f u H1 y H2).
move=> u H1 y H2.
right.
apply (Im_intro U T X2 f u H1 y H2).
move=> t.
elim.
move=> t0.
elim.
move=> x H2 y H3.
apply (Im_intro U T (Union U X1 X2) f x (Union_introl U X1 X2 x H2) y H3).
move=> t0.
elim.
move=> x H2 y H3.
apply (Im_intro U T (Union U X1 X2) f x (Union_intror U X1 X2 x H2) y H3).
Qed.

Lemma Formula_4_3 : forall (U T : Type) (f : U -> T) (X1 X2 : Ensemble U), Included T (Im U T (Intersection U X1 X2) f) (Intersection T (Im U T X1 f) (Im U T X2 f)).
Proof.
move=> U T f X1 X2 t.
elim.
move=> x H1 y H2.
apply (Intersection_intro T (Im U T X1 f) (Im U T X2 f) y).
apply (Im_intro U T X1 f x).
elim H1.
move=> u H3 H4.
apply H3.
apply H2.
apply (Im_intro U T X2 f x).
elim H1.
move=> u H3 H4.
apply H4.
apply H2.
Qed.

Lemma Formula_4_4_1 : forall (U T : Type) (f : U -> T) (X1 X2 : Ensemble U), Included T (Setminus T (Im U T X1 f) (Im U T X2 f)) (Im U T (Setminus U X1 X2) f).
Proof.
move=> U T f X1 X2 t H1.
suff: (~ In T (Im U T X2 f) t).
elim (proj1 H1).
move=> x H2 y H3 H4.
apply (Im_intro U T (Setminus U X1 X2) f x).
apply conj.
apply H2.
move=> H5.
apply H4.
apply (Im_intro U T X2 f x H5 y H3).
apply H3.
apply (proj2 H1).
Qed.

Lemma Formula_4_4_2 : forall (U T : Type) (f : U -> T) (X1 : Ensemble U), Included T (Setminus T (Im U T (Full_set U) f) (Im U T X1 f)) (Im U T (Complement U X1) f).
Proof.
move=> U T f X1 t H1.
suff: (~ In T (Im U T X1 f) t).
elim (proj1 H1).
move=> x H2 y H3 H4.
apply (Im_intro U T (Complement U X1) f x).
move=> H5.
apply H4.
apply (Im_intro U T X1 f x H5 y H3).
apply H3.
apply (proj2 H1).
Qed.

Lemma Formula_4_5 : forall (U T : Type) (f : U -> T) (X : Ensemble U), Included U X (Inverse_Im U T (Im U T X f) f).
Proof.
move=> U T f X u H1.
apply (Inverse_Im_intro U T (Im U T X f) f u).
apply (Im_intro U T X f u H1).
reflexivity.
Qed.

Lemma Formula_4_1_dash : forall (U T : Type) (f : U -> T) (Y1 Y2 : Ensemble T), Included T Y1 Y2 -> Included U (Inverse_Im U T Y1 f) (Inverse_Im U T Y2 f).
Proof.
move=> U T f X1 X2 H1 t.
elim.
move=> u H2.
apply (Inverse_Im_intro U T X2 f u (H1 (f u) H2)).
Qed.

Lemma Formula_4_2_dash : forall (U T : Type) (f : U -> T) (Y1 Y2 : Ensemble T), (Inverse_Im U T (Union T Y1 Y2) f) = (Union U (Inverse_Im U T Y1 f) (Inverse_Im U T Y2 f)).
Proof.
move=> U T f X1 X2.
apply Extensionality_Ensembles.
apply conj.
move=> x.
elim.
move=> u H1.
suff: (In T X1 (f u) \/ In T X2 (f u)).
elim.
move=> H2.
left.
apply (Inverse_Im_intro U T X1 f u H2).
move=> H2.
right.
apply (Inverse_Im_intro U T X2 f u H2).
elim H1.
move=> t H2.
left.
apply H2.
move=> t H2.
right.
apply H2.
move=> u.
elim.
move=> u0.
elim.
move=> u1 H1.
apply (Inverse_Im_intro U T (Union T X1 X2) f u1).
apply (Union_introl T X1 X2 (f u1) H1).
move=> u0.
elim.
move=> u1 H1.
apply (Inverse_Im_intro U T (Union T X1 X2) f u1).
apply (Union_intror T X1 X2 (f u1) H1).
Qed.

Lemma Formula_4_3_dash : forall (U T : Type) (f : U -> T) (Y1 Y2 : Ensemble T), (Inverse_Im U T (Intersection T Y1 Y2) f) = (Intersection U (Inverse_Im U T Y1 f) (Inverse_Im U T Y2 f)).
Proof.
move=> U T f X1 X2.
apply Extensionality_Ensembles.
apply conj.
move=> u.
elim.
move=> u0 H1.
suff: (In T X1 (f u0) /\ In T X2 (f u0)).
move=> H2.
apply (Intersection_intro U (Inverse_Im U T X1 f) (Inverse_Im U T X2 f) u0 (Inverse_Im_intro U T X1 f u0 (proj1 H2)) (Inverse_Im_intro U T X2 f u0 (proj2 H2))).
elim H1.
move=> t.
apply conj.
move=> u.
elim.
move=> u0 H1 H2.
apply (Inverse_Im_intro U T (Intersection T X1 X2) f u0).
apply (Intersection_intro T X1 X2 (f u0)).
elim H1.
move=> u1.
apply.
elim H2.
move=> u2.
apply.
Qed.

Lemma Formula_4_4_1_dash : forall (U T : Type) (f : U -> T) (Y1 Y2 : Ensemble T), (Setminus U (Inverse_Im U T Y1 f) (Inverse_Im U T Y2 f)) = (Inverse_Im U T (Setminus T Y1 Y2) f).
Proof.
move=> U T f X1 X2.
apply Extensionality_Ensembles.
apply conj.
move=> u H1.
apply (Inverse_Im_intro U T (Setminus T X1 X2) f u).
apply conj.
elim (proj1 H1).
move=> u0.
apply.
move=> H2.
apply (proj2 H1).
apply (Inverse_Im_intro U T X2 f u H2).
move=> u.
elim.
move=> u0 H1.
apply conj.
apply (Inverse_Im_intro U T X1 f u0 (proj1 H1)).
move=> H2.
apply (proj2 H1).
elim H2.
move=> u1.
apply.
Qed.

Lemma Formula_4_4_2_dash : forall (U T : Type) (f : U -> T) (Y : Ensemble T), (Complement U (Inverse_Im U T Y f)) = (Inverse_Im U T (Complement T Y) f).
Proof.
move=> U T f X.
apply Extensionality_Ensembles.
apply conj.
move=> u H1.
apply (Inverse_Im_intro U T (Complement T X) f u).
move=> H2.
apply H1.
apply (Inverse_Im_intro U T X f u H2).
move=> u.
elim.
move=> u0 H1 H2.
apply H1.
elim H2.
move=> u1.
apply.
Qed.

Lemma Formula_4_5_dash : forall (U T : Type) (f : U -> T) (Y : Ensemble T), Included T (Im U T (Inverse_Im U T Y f) f) Y.
Proof.
move=> U T f X u H1.
elim H1.
move=> u0 H2 y H3.
rewrite H3.
elim H2.
move=> u1.
apply.
Qed.

Lemma SurjectiveDef2 : forall (U T : Type) (f : U -> T), Surjective f <-> Im U T (Full_set U) f = (Full_set T).
Proof.
move=> U T f.
apply conj.
move=> H1.
apply Extensionality_Ensembles.
apply conj.
move=> t H2.
apply (Full_intro T t).
move=> t H2.
elim (H1 t).
move=> u H3.
apply (Im_intro U T (Full_set U) f u (Full_intro U u) t).
rewrite H3.
reflexivity.
move=> H1 t.
suff: (In T (Im U T (Full_set U) f) t).
elim.
move=> x H2 y H3.
exists x.
rewrite H3.
reflexivity.
rewrite H1.
apply (Full_intro T t).
Qed.

Lemma Formula_P33_1 : forall (U T : Type) (f : U -> T), Surjective f <-> forall (t : T), Inverse_Im U T (Singleton T t) f <> Empty_set U.
Proof.
move=> U T f.
apply conj.
move=> H1 t H2.
elim (H1 t).
move=> u H3.
suff: (In U (Inverse_Im U T (Singleton T t) f) u).
rewrite H2.
elim.
rewrite - H3.
apply (Inverse_Im_intro U T (Singleton T (f u)) f).
apply (In_singleton T (f u)).
move=> H1 t.
apply NNPP.
move=> H2.
apply (H1 t).
apply Extensionality_Ensembles.
apply conj.
move=> u H3.
apply False_ind.
apply H2.
elim H3.
move=> u0 H4.
exists u0.
elim H4.
reflexivity.
move=> u.
elim.
Qed.

Lemma Formula_P33_2 : forall (U T : Type) (f : U -> T), Injective f <-> forall (t : T), In T (Im U T (Full_set U) f) t -> cardinal U (Inverse_Im U T (Singleton T t) f) 1.
Proof.
move=> U T f.
apply conj.
move=> H1 t H2.
elim H2.
move=> u H3 y H4.
suff: ((Inverse_Im U T (Singleton T y) f) = Add U (Empty_set U) u).
move=> H5.
rewrite H5.
apply (card_add U (Empty_set U) O (card_empty U)).
elim.
apply Extensionality_Ensembles.
apply conj.
move=> u0 H5.
right.
suff: (u = u0).
move=> H6.
rewrite H6.
apply (In_singleton U u0).
apply H1.
elim H5.
move=> u1.
elim.
rewrite H4.
reflexivity.
move=> u0.
elim.
move=> u1.
elim.
move=> u1.
elim.
rewrite H4.
apply (Inverse_Im_intro U T).
apply (In_singleton T (f u)).
move=> H1 u1 u2 H2.
apply NNPP.
move=> H3.
apply (lt_irrefl 1).
apply (incl_card_le U (Add U (Add U (Empty_set U) u1) u2) (Inverse_Im U T (Singleton T (f u1)) f) 2 1).
apply (card_add U (Add U (Empty_set U) u1) 1).
apply (card_add U (Empty_set U) O (card_empty U)).
elim.
move=> H4.
apply H3.
elim H4.
move=> u0.
elim.
move=> u0.
elim.
reflexivity.
apply (H1 (f u1)).
apply (Im_intro U T (Full_set U) f u1 (Full_intro U u1)).
reflexivity.
move=> u.
elim.
move=> u0.
elim.
move=> u3.
elim.
move=> u3.
elim.
apply (Inverse_Im_intro U T).
apply (In_singleton T (f u1)).
rewrite H2.
move=> u0.
elim.
apply (Inverse_Im_intro U T).
apply (In_singleton T (f u2)).
Qed.

Lemma Theorem_4_1 : forall (U T : Type) (f : U -> T), (exists (g : T -> U), (fun (t : T) (u : U) => g t = u) = InverseCorrespondence U T (fun (u : U) (t : T) => f u = t)) <-> Bijective f.
Proof.
move=> U T f.
apply conj.
elim.
move=> g H1.
exists g.
apply conj.
move=> u.
suff: (In U (InverseCorrespondence U T (fun (u : U) (t : T) => f u = t) (f u)) u).
rewrite - H1.
apply.
reflexivity.
move=> t.
suff: (In U (InverseCorrespondence U T (fun (u : U) (t : T) => f u = t) t) (g t)).
apply.
rewrite - H1.
reflexivity.
elim.
move=> g H1.
exists g.
apply functional_extensionality.
move=> t.
apply Extensionality_Ensembles.
apply conj.
move=> u H2.
rewrite - (proj2 H1 t).
rewrite H2.
reflexivity.
move=> u H2.
rewrite - H2.
apply (proj1 H1 u).
Qed.

Lemma Theorem_4_2 : forall (U T : Type) (f : U -> T) (g : T -> U), (fun (t : T) (u : U) => g t = u) = InverseCorrespondence U T (fun (u : U) (t : T) => f u = t) -> Bijective g.
Proof.
move=> U T f g H1.
exists f.
apply conj.
move=> t.
suff: (In U (InverseCorrespondence U T (fun (u : U) (t : T) => f u = t) t) (g t)).
apply.
rewrite - H1.
reflexivity.
move=> u.
suff: (In U (InverseCorrespondence U T (fun (u : U) (t : T) => f u = t) (f u)) u).
rewrite - H1.
apply.
reflexivity.
Qed.

Definition InvFunction (U T : Type) (f : U -> T) (H : Bijective f) := proj1_sig (BijectiveInvExist U T f H).

Definition InvFunctionNature (U T : Type) (f : U -> T) (H : Bijective f) : (forall (u : U), InvFunction U T f H (f u) = u) /\ (forall (t : T), f (InvFunction U T f H t) = t) := proj2_sig (BijectiveInvExist U T f H).

Lemma Formula_P34 : forall (U T : Type) (f : U -> T) (H : Bijective f) (u : U) (t : T), InvFunction U T f H t = u <-> f u = t.
Proof.
move=> U T f H1 u t.
apply conj.
move=> H2.
rewrite - H2.
apply (proj2 (InvFunctionNature U T f H1) t).
move=> H2.
rewrite - H2.
apply (proj1 (InvFunctionNature U T f H1) u).
Qed.

Definition Theorem_5_1 : forall (U T V : Type) (f : U -> T) (g : T -> V), (Surjective f) -> (Surjective g) -> (Surjective (compose g f)) := SurjChain.

Definition Theorem_5_2 : forall (U T V : Type) (f : U -> T) (g : T -> V), (Injective f) -> (Injective g) -> (Injective (compose g f)) := InjChain.

Definition Theorem_5_3 : forall (U T V : Type) (f : U -> T) (g : T -> V), (Bijective f) -> (Bijective g) -> (Bijective (compose g f)) := BijChain.

Definition Theorem_6_1 : forall (U T V W : Type) (f : U -> T) (g : T -> V) (h : V -> W), (compose (compose h g) f) = (compose h (compose g f)) := compose_assoc.

Definition Theorem_6_2_1 : forall (U T : Type) (f : U -> T), (compose f (fun (u : U) => u)) = f := compose_id_right.

Definition Theorem_6_2_2 : forall (U T : Type) (f : U -> T), (compose (fun (t : T) => t) f) = f := compose_id_left.

Lemma Theorem_6_3_1 : forall (U T : Type) (f : U -> T) (H : Bijective f), (compose (InvFunction U T f H) f) = (fun (u : U) => u).
Proof.
move=> U T f H1.
apply functional_extensionality.
move=> u.
apply (proj1 (InvFunctionNature U T f H1) u).
Qed.

Lemma Theorem_6_3_2 : forall (U T : Type) (f : U -> T) (H : Bijective f), (compose f (InvFunction U T f H)) = (fun (t : T) => t).
Proof.
move=> U T f H1.
apply functional_extensionality.
move=> t.
apply (proj2 (InvFunctionNature U T f H1) t).
Qed.

Lemma Formula_P39_1 : forall (U T : Type) (m : nat) (n : nat), cardinal U (Full_set U) n -> cardinal T (Full_set T) m -> cardinal (U -> T) (Full_set (U -> T)) (m ^ n).
Proof.
move=> U T m n H1 H2.
apply CountCardinalBijective.
elim (proj2 (CountCardinalBijective U n) H1).
move=> g H3.
elim H3.
move=> ginv H4.
elim (proj2 (CountCardinalBijective T m) H2).
move=> h H5.
elim H5.
move=> hinv H6.
elim (CountPow n m).
move=> c H7.
elim H7.
move=> cinv H8.
exists (fun (k : {l : nat | l < m ^ n}) (u : U) => h (cinv k (ginv u))).
exists (fun (f : U -> T) => c (fun (k : {l : nat | l < n}) => hinv (f (g k)))).
apply conj.
move=> p.
rewrite - (proj2 H8 p).
suff: ((fun (k : {l : nat | l < n}) => hinv (h (cinv (c (cinv p)) (ginv (g k))))) = cinv p).
move=> H9.
rewrite H9.
reflexivity.
apply functional_extensionality.
move=> k.
rewrite (proj1 H6).
rewrite (proj1 H8).
rewrite (proj1 H4).
reflexivity.
move=> q.
apply functional_extensionality.
move=> u.
rewrite - (proj2 H6 (q u)).
rewrite (proj1 H8).
rewrite (proj2 H4).
reflexivity.
Qed.

Definition CharacteristicFunction (U : Type) (A : Ensemble U) := (fun (u : U) => match excluded_middle_informative (In U A u) with
  | left _ => exist (fun (n : nat) => n < 2) 1 (le_n 2)
  | right _ => exist (fun (n : nat) => n < 2) O (le_S 1 1 (le_n 1))
end).

Lemma Formula_P39_2 : forall (U : Type) (u : U), proj1_sig (CharacteristicFunction U (Full_set U) u) = 1.
Proof.
move=> U u.
unfold CharacteristicFunction.
elim (excluded_middle_informative (In U (Full_set U) u)).
move=> H1.
reflexivity.
move=> H1.
apply False_ind.
apply H1.
apply (Full_intro U u).
Qed.

Lemma Formula_P39_3 : forall (U : Type) (u : U), proj1_sig (CharacteristicFunction U (Empty_set U) u) = 0.
Proof.
move=> U u.
unfold CharacteristicFunction.
elim (excluded_middle_informative (In U (Empty_set U) u)).
elim.
move=> H1.
reflexivity.
Qed.

Lemma Formula_P39_4 : forall (U : Type), Injective (CharacteristicFunction U).
Proof.
unfold CharacteristicFunction.
move=> U u1 u2 H1.
apply Extensionality_Ensembles.
apply conj.
move=> u H2.
suff: (proj1_sig (let temp := (fun (u : U) => match excluded_middle_informative (In U u1 u) with
  | left _ => exist (fun n : nat => n < 2) 1 (le_n 2)
  | right _ => exist (fun n0 : nat => n0 < 2) 0 (le_S 1 1 (le_n 1))
end) in temp u) = 1).
rewrite H1.
simpl.
elim (excluded_middle_informative (In U u2 u)).
move=> H3 H4.
apply H3.
move=> H3 H4.
apply False_ind.
apply (lt_irrefl 1).
rewrite - {1} H4.
apply (le_n 1).
simpl.
elim (excluded_middle_informative (In U u1 u)).
move=> H3.
reflexivity.
move=> H3.
apply False_ind.
apply (H3 H2).
move=> u H2.
suff: (proj1_sig (let temp := (fun (u : U) => match excluded_middle_informative (In U u2 u) with
  | left _ => exist (fun n : nat => n < 2) 1 (le_n 2)
  | right _ => exist (fun n0 : nat => n0 < 2) 0 (le_S 1 1 (le_n 1))
end) in temp u) = 1).
rewrite - H1.
simpl.
elim (excluded_middle_informative (In U u1 u)).
move=> H3 H4.
apply H3.
move=> H3 H4.
apply False_ind.
apply (lt_irrefl 1).
rewrite - {1} H4.
apply (le_n 1).
simpl.
elim (excluded_middle_informative (In U u2 u)).
move=> H3.
reflexivity.
move=> H3.
apply False_ind.
apply (H3 H2).
Qed.

Lemma Formula_P39_5 : forall (U : Type) (f : U -> {n : nat | n < 2}), CharacteristicFunction U (Inverse_Im U {n : nat | n < 2} (fun (m : {n : nat | n < 2}) => proj1_sig m = 1) f) = f.
Proof.
move=> U f.
apply functional_extensionality.
move=> u.
unfold CharacteristicFunction.
elim (excluded_middle_informative (In U (Inverse_Im U {n : nat | n < 2} (fun (m : {n : nat | n < 2}) => proj1_sig m = 1) f) u)).
elim.
move=> u0 H1.
apply sig_map.
rewrite H1.
reflexivity.
move=> H1.
apply sig_map.
simpl.
elim (le_lt_or_eq (proj1_sig (f u)) 1).
move=> H2.
apply (le_antisym 0 (proj1_sig (f u))).
apply (le_0_n (proj1_sig (f u))).
apply (le_S_n (proj1_sig (f u)) 0 H2).
move=> H2.
apply False_ind.
apply H1.
apply (Inverse_Im_intro U {n : nat | n < 2} (fun (m : {n : nat | n < 2}) => proj1_sig m = 1) f u H2).
apply (le_S_n (proj1_sig (f u)) 1 (proj2_sig (f u))).
Qed.

Lemma Formula_P39_6 : forall (U : Type), {f : Ensemble U -> U -> {n : nat | n < 2} | Bijective f}.
Proof.
move=> U.
exists (CharacteristicFunction U).
apply InjSurjBij.
apply (Formula_P39_4 U).
move=> f.
exists (Inverse_Im U {n : nat | n < 2} (fun (m : {n : nat | n < 2}) => proj1_sig m = 1) f).
apply (Formula_P39_5 U f).
Qed.

Lemma Formula_P45_1 : forall (U T : Type) (A : T -> Ensemble U), (forall (t : T), Included U (A t) (UnionT U T A)) /\ forall (B : Ensemble U), (forall (t : T), Included U (A t) B) -> Included U (UnionT U T A) B.
Proof.
move=> U T A.
apply conj.
move=> t u H1.
apply (UnionT_intro U T A u t H1).
move=> B H1 u.
elim.
move=> u0 t H2.
apply (H1 t u0 H2).
Qed.

Lemma Formula_P45_2 : forall (U T : Type) (A : T -> Ensemble U), (forall (t : T), Included U (IntersectionT U T A) (A t)) /\ forall (B : Ensemble U), (forall (t : T), Included U B (A t)) -> Included U B (IntersectionT U T A).
Proof.
move=> U T A.
apply conj.
move=> t u.
elim.
move=> u0 H1.
apply (H1 t).
move=> B H1 u H2.
apply (IntersectionT_intro U T A u).
move=> t.
apply (H1 t u H2).
Qed.

Lemma Formula_5_1 : forall (U T : Type) (A : T -> Ensemble U) (B : Ensemble U), Intersection U (UnionT U T A) B = (UnionT U T (fun (t : T) => Intersection U (A t) B)).
Proof.
move=> U T A B.
apply Extensionality_Ensembles.
apply conj.
move=> u.
elim.
move=> u0 H1.
elim H1.
move=> u1 t H2 H3.
apply (UnionT_intro U T (fun (t0 : T) => Intersection U (A t0) B) u1 t).
apply (Intersection_intro U (A t) B u1 H2 H3).
move=> u.
elim.
move=> u0 t.
elim.
move=> u1 H1 H2.
apply (Intersection_intro U (UnionT U T A) B u1).
apply (UnionT_intro U T A u1 t H1).
apply H2.
Qed.

Lemma Formula_5_1_dash : forall (U T : Type) (A : T -> Ensemble U) (B : Ensemble U), Union U (IntersectionT U T A) B = (IntersectionT U T (fun (t : T) => Union U (A t) B)).
Proof.
move=> U T A B.
apply Extensionality_Ensembles.
apply conj.
move=> u.
elim.
move=> u0 H1.
apply (IntersectionT_intro U T).
move=> t.
apply (Union_introl U (A t) B).
elim H1.
move=> u1 H2.
apply (H2 t).
move=> u0 H1.
apply (IntersectionT_intro U T (fun (t : T) => Union U (A t) B) u0).
move=> t.
apply (Union_intror U (A t) B u0 H1).
move=> u.
elim.
move=> u0 H1.
elim (classic (In U B u0)).
move=> H2.
apply (Union_intror U (IntersectionT U T A) B u0 H2).
move=> H2.
apply (Union_introl U (IntersectionT U T A) B u0).
apply (IntersectionT_intro U T A u0).
move=> t.
suff: (~ In U B u0).
elim (H1 t).
move=> u1 H3 H4.
apply H3.
move=> u1 H3 H4.
apply False_ind.
apply (H4 H3).
apply H2.
Qed.

Lemma Formula_5_2 : forall (U T : Type) (A : T -> Ensemble U), Complement U (UnionT U T A) = IntersectionT U T (fun (t : T) => Complement U (A t)).
Proof.
move=> U T A.
apply Extensionality_Ensembles.
apply conj.
move=> u H1.
apply (IntersectionT_intro U T).
move=> t H2.
apply H1.
apply (UnionT_intro U T A u t H2).
move=> u.
elim.
move=> u0 H1 H2.
suff: (forall (t : T), In U (Complement U (A t)) u0).
elim H2.
move=> u1 t H3 H4.
apply (H4 t H3).
apply H1.
Qed.

Lemma Formula_5_2_dash : forall (U T : Type) (A : T -> Ensemble U), Complement U (IntersectionT U T A) = UnionT U T (fun (t : T) => Complement U (A t)).
Proof.
move=> U T A.
apply Extensionality_Ensembles.
apply conj.
move=> u H1.
apply NNPP.
move=> H2.
apply H1.
apply (IntersectionT_intro U T A u).
move=> t.
apply NNPP.
move=> H3.
apply H2.
apply (UnionT_intro U T (fun (t0 : T) => Complement U (A t0)) u t H3).
move=> u.
elim.
move=> u0 t H1 H2.
apply H1.
elim H2.
move=> u1 H3.
apply (H3 t).
Qed.

Lemma Formula_5_3 : forall (V U T : Type) (A : T -> Ensemble V) (f : V -> U), Im V U (UnionT V T A) f = UnionT U T (fun (t : T) => Im V U (A t) f).
Proof.
move=> V U T A f.
apply Extensionality_Ensembles.
apply conj.
move=> u.
elim.
move=> v H1 u0 H2.
rewrite H2.
elim H1.
move=> v0 t H3.
apply (UnionT_intro U T (fun (t0 : T) => Im V U (A t0) f) (f v0) t).
apply (Im_intro V U (A t) f v0 H3).
reflexivity.
move=> u.
elim.
move=> u0 t.
elim.
move=> v H1 u1 H2.
apply (Im_intro V U (UnionT V T A) f v).
apply (UnionT_intro V T A v t H1).
apply H2.
Qed.

Lemma Formula_5_4 : forall (V U T : Type) (A : T -> Ensemble V) (f : V -> U), Included U (Im V U (IntersectionT V T A) f) (IntersectionT U T (fun (t : T) => Im V U (A t) f)).
Proof.
move=> V U T A f u.
elim.
move=> v H1 u0 H2.
apply (IntersectionT_intro U T (fun (t : T) => Im V U (A t) f) u0).
move=> t.
rewrite H2.
apply (Im_intro V U (A t) f v).
elim H1.
move=> v0 H3.
apply (H3 t).
reflexivity.
Qed.

Lemma Formula_5_3_dash : forall (V U T : Type) (A : T -> Ensemble U) (f : V -> U), Inverse_Im V U (UnionT U T A) f = UnionT V T (fun (t : T) => Inverse_Im V U (A t) f).
Proof.
move=> V U T A f.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> v0 H1.
suff: (exists (t : T), In U (A t) (f v0)).
elim.
move=> t H2.
apply (UnionT_intro V T (fun (t0 : T) => Inverse_Im V U (A t0) f) v0 t).
apply (Inverse_Im_intro V U (A t) f v0 H2).
elim H1.
move=> u t H2.
exists t.
apply H2.
move=> v.
elim.
move=> v0 t.
elim.
move=> v1 H1.
apply (Inverse_Im_intro V U (UnionT U T A) f v1).
apply (UnionT_intro U T A (f v1) t H1).
Qed.

Lemma Formula_5_4_dash : forall (V U T : Type) (A : T -> Ensemble U) (f : V -> U), Inverse_Im V U (IntersectionT U T A) f = IntersectionT V T (fun (t : T) => Inverse_Im V U (A t) f).
Proof.
move=> V U T A f.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> v0 H1.
apply (IntersectionT_intro V T (fun (t : T) => Inverse_Im V U (A t) f) v0).
move=> t.
apply (Inverse_Im_intro V U (A t) f v0).
elim H1.
move=> u H2.
apply (H2 t).
move=> v.
elim.
move=> v0 H1.
apply (Inverse_Im_intro V U (IntersectionT U T A) f v0).
apply (IntersectionT_intro U T A (f v0)).
move=> t.
elim (H1 t).
move=> v1.
apply.
Qed.

Inductive ProductionEnsemble (U : Type) (T : U -> Type) (A : forall (u : U), Ensemble (T u)) : (Ensemble (forall (u : U), T u)) :=
  | ProductionEnsemble_intro : forall (t : forall (u : U), T u), (forall (u : U), In (T u) (A u) (t u)) -> In (forall (u : U), T u) (ProductionEnsemble U T A) t.

Lemma Formula_P47_1 : forall (U : Type) (T : U -> Type) (A : forall (u : U), Ensemble (T u)), (exists (u : U), A u = Empty_set (T u)) -> ProductionEnsemble U T A = Empty_set (forall (u : U), T u).
Proof.
move=> U T A H1.
apply Extensionality_Ensembles.
apply conj.
move=> X H2.
elim H1.
move=> u H3.
suff: (In (T u) (A u) (X u)).
rewrite H3.
elim.
elim H2.
move=> t H4.
apply (H4 u).
move=> t.
elim.
Qed.

Lemma Theorem_7_1_2 : forall (U T : Type) (f : U -> T), (exists (g : T -> U), compose f g = (fun (t : T) => t)) -> Surjective f.
Proof.
move=> U T f.
elim.
move=> g H1 t.
exists (g t).
suff: (f (g t) = compose f g t).
move=> H2.
rewrite H2.
rewrite H1.
reflexivity.
reflexivity.
Qed.

Lemma Theorem_7_2_1 : forall (U T : Type) (u : U) (f : U -> T), Injective f -> exists (g : T -> U), compose g f = (fun (u0 : U) => u0).
Proof.
move=> U T u f H1.
suff: (forall (t : T), (exists (u : U), t = f u) -> {u : U | t = f u}).
move=> H2.
exists (fun (t : T) => match excluded_middle_informative (exists (u : U), t = f u) with
  | left H => proj1_sig (H2 t H)
  | right _ => u
end).
apply functional_extensionality.
unfold compose.
move=> u0.
elim (excluded_middle_informative (exists (u1 : U), f u0 = f u1)).
move=> H3.
apply H1.
rewrite - (proj2_sig (H2 (f u0) H3)).
reflexivity.
move=> H3.
apply False_ind.
apply H3.
exists u0.
reflexivity.
move=> t H2.
apply constructive_definite_description.
apply (unique_existence (fun (u0 : U) => t = f u0)).
apply conj.
apply H2.
move=> u0 u1 H3 H4.
apply H1.
rewrite - H3.
apply H4.
Qed.

Lemma Theorem_7_2_2 : forall (U T : Type) (f : U -> T), (exists (g : T -> U), compose g f = (fun (u0 : U) => u0)) -> Injective f.
Proof.
move=> U T f.
elim.
move=> g H1 u0 u1 H2.
suff: (u0 = (compose g f u0)).
move=> H3.
suff: (u1 = (compose g f u1)).
move=> H4.
rewrite H3.
rewrite H4.
unfold compose.
rewrite H2.
reflexivity.
rewrite H1.
reflexivity.
rewrite H1.
reflexivity.
Qed.

Lemma Theorem_7_corollary_1 : forall (U T : Type) (u : U), (exists (f : U -> T), Injective f) -> (exists (g : T -> U), Surjective g).
Proof.
move=> U T u.
elim.
move=> f H1.
elim (Theorem_7_2_1 U T u f H1).
move=> g H2.
exists g.
apply (Theorem_7_1_2 T U g).
exists f.
apply H2.
Qed.

Record EquivalenceRelation (T : Type) : Type := mkEquivalenceRelation
{
ER : T -> T -> Prop;
ERref : forall (t : T), ER t t;
ERsym : forall (t1 t2 : T), ER t1 t2 -> ER t2 t1;
ERtrans : forall (t1 t2 t3 : T), ER t1 t2 -> ER t2 t3 -> ER t1 t3
}.

Definition FunctionER (A B : Type) (f : A -> B) (a1 a2 : A) := f a1 = f a2.

Lemma FunctionERref : forall (A B : Type) (f : A -> B) (a : A), FunctionER A B f a a.
Proof.
move=> A B f a.
reflexivity.
Qed.

Lemma FunctionERsym : forall (A B : Type) (f : A -> B) (a1 a2 : A), FunctionER A B f a1 a2 -> FunctionER A B f a2 a1.
Proof.
move=> A B f a1 a2 H1.
unfold FunctionER.
rewrite H1.
reflexivity.
Qed.

Lemma FunctionERtrans : forall (A B : Type) (f : A -> B) (a1 a2 a3 : A), FunctionER A B f a1 a2 -> FunctionER A B f a2 a3 -> FunctionER A B f a1 a3.
Proof.
move=> A B f a1 a2 a3 H1 H2.
unfold FunctionER.
rewrite H1.
rewrite H2.
reflexivity.
Qed.

Definition FunctionEquivalenceRelation (A B : Type) (f : A -> B) := mkEquivalenceRelation A (FunctionER A B f) (FunctionERref A B f) (FunctionERsym A B f) (FunctionERtrans A B f).

Definition DirectSumDivision (T : Type) (X : Ensemble (Ensemble T)) := (forall (t : T), exists (x : Ensemble T), (In (Ensemble T) X x) /\ (In T x t)) /\ forall (x1 x2 : Ensemble T), In (Ensemble T) X x1 -> In (Ensemble T) X x2 -> x1 <> x2 -> Intersection T x1 x2 = Empty_set T.

Lemma DirectSumDivisionGet : forall (T : Type) (X : Ensemble (Ensemble T)), DirectSumDivision T X -> forall (t : T), {x : Ensemble T | (In (Ensemble T) X x) /\ (In T x t)}.
Proof.
move=> T X H1 t.
apply constructive_definite_description.
apply (unique_existence (fun (x : Ensemble T) => In (Ensemble T) X x /\ In T x t)).
apply conj.
apply (proj1 H1 t).
move=> x1 x2 H2 H3.
apply NNPP.
move=> H4.
suff: (In T (Intersection T x1 x2) t).
rewrite (proj2 H1 x1 x2 (proj1 H2) (proj1 H3) H4).
elim.
apply (Intersection_intro T x1 x2 t (proj2 H2) (proj2 H3)).
Qed.

Definition DirectSumDivisionER (T : Type) (X : Ensemble (Ensemble T)) (t1 t2 : T) := exists (x : Ensemble T), In (Ensemble T) X x /\ In T x t1 /\ In T x t2.

Lemma DirectSumDivisionERref : forall (T : Type) (X : Ensemble (Ensemble T)), DirectSumDivision T X -> forall (t : T), DirectSumDivisionER T X t t.
Proof.
move=> T X H1 t.
elim (proj1 H1 t).
move=> x H2.
exists x.
apply conj.
apply (proj1 H2).
apply conj.
apply (proj2 H2).
apply (proj2 H2).
Qed.

Lemma DirectSumDivisionERsym : forall (T : Type) (X : Ensemble (Ensemble T)), DirectSumDivision T X -> forall (t1 t2 : T), DirectSumDivisionER T X t1 t2 -> DirectSumDivisionER T X t2 t1.
Proof.
move=> T X H1 t1 t2 H2.
elim H2.
move=> x H3.
exists x.
apply conj.
apply (proj1 H3).
apply conj.
apply (proj2 (proj2 H3)).
apply (proj1 (proj2 H3)).
Qed.

Lemma DirectSumDivisionERtrans : forall (T : Type) (X : Ensemble (Ensemble T)), DirectSumDivision T X -> forall (t1 t2 t3 : T), DirectSumDivisionER T X t1 t2 -> DirectSumDivisionER T X t2 t3 -> DirectSumDivisionER T X t1 t3.
Proof.
move=> T X H1 t1 t2 t3 H2 H3.
elim H2.
move=> x H4.
elim H3.
move=> y H5.
suff: (x = y).
move=> H6.
exists x.
apply conj.
apply (proj1 H4).
apply conj.
apply (proj1 (proj2 H4)).
rewrite H6.
apply (proj2 (proj2 H5)).
apply NNPP.
move=> H6.
suff: (In T (Intersection T x y) t2).
rewrite (proj2 H1 x y (proj1 H4) (proj1 H5) H6).
elim.
apply (Intersection_intro T x y t2 (proj2 (proj2 H4)) (proj1 (proj2 H5))).
Qed.

Definition DirectSumDivisionEquivalenceRelation (T : Type) (X : Ensemble (Ensemble T)) (H : DirectSumDivision T X) := mkEquivalenceRelation T (DirectSumDivisionER T X) (DirectSumDivisionERref T X H) (DirectSumDivisionERsym T X H) (DirectSumDivisionERtrans T X H).

Definition EquivalenceRelationClass (T : Type) (R : EquivalenceRelation T) (t : T) := fun (t0 : T) => ER T R t t0.

Definition EquivalenceRelationQuotient (T : Type) (R : EquivalenceRelation T) := {X : Ensemble T | Im T (Ensemble T) (Full_set T) (EquivalenceRelationClass T R) X}.

Lemma EquivalenceRelationQuotientSub : forall (T : Type) (R : EquivalenceRelation T) (t : T), In (Ensemble T) (Im T (Ensemble T) (Full_set T) (EquivalenceRelationClass T R)) (EquivalenceRelationClass T R t).
Proof.
move=> T R t.
apply (Im_intro T (Ensemble T) (Full_set T) (EquivalenceRelationClass T R) t (Full_intro T t)).
reflexivity.
Qed.

Definition EquivalenceRelationQuotientFunction (T : Type) (R : EquivalenceRelation T) (t : T) := exist (Im T (Ensemble T) (Full_set T) (EquivalenceRelationClass T R)) (EquivalenceRelationClass T R t) (EquivalenceRelationQuotientSub T R t).

Lemma Formula_6_1 : forall (T : Type) (R : EquivalenceRelation T) (t : T), In T (EquivalenceRelationClass T R t) t.
Proof.
move=> T R t.
apply (ERref T R t).
Qed.

Lemma Formula_6_2 : forall (T : Type) (R : EquivalenceRelation T) (t1 t2 : T), ER T R t1 t2 <-> EquivalenceRelationClass T R t1 = EquivalenceRelationClass T R t2.
Proof.
move=> T R t1 t2.
apply conj.
move=> H1.
apply Extensionality_Ensembles.
apply conj.
move=> t H2.
apply (ERtrans T R t2 t1 t (ERsym T R t1 t2 H1) H2).
move=> t H2.
apply (ERtrans T R t1 t2 t H1 H2).
move=> H1.
suff: (In T (EquivalenceRelationClass T R t1) t2).
apply.
rewrite H1.
apply (ERref T R t2).
Qed.

Lemma Formula_6_3 : forall (T : Type) (R : EquivalenceRelation T) (t1 t2 : T), EquivalenceRelationClass T R t1 <> EquivalenceRelationClass T R t2 -> Intersection T (EquivalenceRelationClass T R t1) (EquivalenceRelationClass T R t2) = Empty_set T.
Proof.
move=> T R t1 t2 H1.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0 H2 H3.
apply False_ind.
apply H1.
apply (Formula_6_2 T R t1 t2).
apply (ERtrans T R t1 t0 t2 H2 (ERsym T R t2 t0 H3)).
move=> t.
elim.
Qed.

Lemma EquivalenceRelationClassDirectSumDivision : forall (T : Type) (R : EquivalenceRelation T), DirectSumDivision T (Im T (Ensemble T) (Full_set T) (EquivalenceRelationClass T R)).
Proof.
move=> T R.
apply conj.
move=> t.
exists (EquivalenceRelationClass T R t).
apply conj.
apply (Im_intro T (Ensemble T) (Full_set T) (EquivalenceRelationClass T R) t (Full_intro T t)).
reflexivity.
apply (Formula_6_1 T R t).
move=> x1 x2.
elim.
move=> t1 H1 y1 H2.
elim.
move=> t2 H3 y2 H4.
rewrite H2.
rewrite H4.
apply (Formula_6_3 T R t1 t2).
Qed.

Lemma Theorem_8 : forall (T : Type) (R : EquivalenceRelation T), DirectSumDivisionEquivalenceRelation T (Im T (Ensemble T) (Full_set T) (EquivalenceRelationClass T R)) (EquivalenceRelationClassDirectSumDivision T R) = R.
Proof.
move=> T R.
suff: (forall (R1 R2 : EquivalenceRelation T), ER T R1 = ER T R2 -> R1 = R2).
move=> H1.
apply H1.
apply functional_extensionality.
move=> t1.
apply Extensionality_Ensembles.
apply conj.
move=> t2.
elim.
move=> X H2.
suff: (In T X t1 /\ In T X t2).
elim (proj1 H2).
move=> t H3 y H4.
rewrite H4.
move=> H5.
apply (ERtrans T R t1 t t2 (ERsym T R t t1 (proj1 H5)) (proj2 H5)).
apply (proj2 H2).
move=> t H2.
exists (EquivalenceRelationClass T R t1).
apply conj.
apply (Im_intro T (Ensemble T) (Full_set T) (EquivalenceRelationClass T R) t1 (Full_intro T t1)).
reflexivity.
apply conj.
apply (Formula_6_1 T R t1).
apply H2.
move=> R1 R2.
elim R1.
elim R2.
simpl.
suff: (forall (ER1 ER2 : T -> T -> Prop), ER1 = ER2 -> forall (ERref1 : forall (t : T), ER1 t t) (ERsym1 : forall (t1 t2 : T), ER1 t1 t2 -> ER1 t2 t1) (ERtrans1 : forall (t1 t2 t3 : T), ER1 t1 t2 -> ER1 t2 t3 -> ER1 t1 t3) (ERref2 : forall (t : T), ER2 t t) (ERsym2 : forall (t1 t2 : T), ER2 t1 t2 -> ER2 t2 t1) (ERtrans2 : forall (t1 t2 t3 : T), ER2 t1 t2 -> ER2 t2 t3 -> ER2 t1 t3), {| ER := ER1; ERref := ERref1; ERsym := ERsym1; ERtrans := ERtrans1 |} = {| ER := ER2; ERref := ERref2; ERsym := ERsym2; ERtrans := ERtrans2 |}).
move=> H1 ER2 ERref2 ERsym2 ERtrans2 ER1 ERref1 ERsym1 ERtrans1 H2.
apply (H1 ER1 ER2 H2 ERref1 ERsym1 ERtrans1 ERref2 ERsym2 ERtrans2).
move=> ER1 ER2 H1.
rewrite H1.
move=> ERref1 ERsym1 ERtrans1 ERref2 ERsym2 ERtrans2.
suff: (ERref1 = ERref2).
move=> H2.
suff: (ERsym1 = ERsym2).
move=> H3.
suff: (ERtrans1 = ERtrans2).
move=> H4.
rewrite H2.
rewrite H3.
rewrite H4.
reflexivity.
apply proof_irrelevance.
apply proof_irrelevance.
apply proof_irrelevance.
Qed.

Lemma Theorem_8_inv : forall (T : Type) (A : Ensemble (Ensemble T)) (H : DirectSumDivision T A), (forall (X : Ensemble T), In (Ensemble T) A X -> Inhabited T X) -> (Im T (Ensemble T) (Full_set T) (EquivalenceRelationClass T (DirectSumDivisionEquivalenceRelation T A H))) = A.
Proof.
move=> T A H1 H2.
apply Extensionality_Ensembles.
apply conj.
move=> X H3.
elim H3.
move=> t H4 Y H5.
rewrite H5.
elim (proj1 H1 t).
move=> Y2 H6.
suff: (EquivalenceRelationClass T (DirectSumDivisionEquivalenceRelation T A H1) t = Y2).
move=> H7.
rewrite H7.
apply (proj1 H6).
apply Extensionality_Ensembles.
apply conj.
move=> x.
elim.
move=> Y3 H7.
suff: (Y2 = Y3).
move=> H8.
rewrite H8.
apply (proj2 (proj2 H7)).
apply NNPP.
move=> H8.
suff: (Intersection T Y2 Y3 = Empty_set T).
move=> H9.
suff: (In T (Intersection T Y2 Y3) t).
rewrite H9.
elim.
apply (Intersection_intro T Y2 Y3 t (proj2 H6) (proj1 (proj2 H7))).
apply (proj2 H1 Y2 Y3 (proj1 H6) (proj1 H7) H8).
move=> x H7.
exists Y2.
apply conj.
apply (proj1 H6).
apply conj.
apply (proj2 H6).
apply H7.
move=> X H3.
elim (H2 X H3).
move=> x H4.
apply (Im_intro T (Ensemble T) (Full_set T) (EquivalenceRelationClass T (DirectSumDivisionEquivalenceRelation T A H1)) x (Full_intro T x)).
apply Extensionality_Ensembles.
apply conj.
move=> y H5.
exists X.
apply conj.
apply H3.
apply conj.
apply H4.
apply H5.
move=> t.
elim.
move=> Y H5.
suff: (X = Y).
move=> H6.
rewrite H6.
apply (proj2 (proj2 H5)).
apply NNPP.
move=> H6.
suff: (Intersection T X Y = Empty_set T).
move=> H7.
suff: (In T (Intersection T X Y) x).
rewrite H7.
elim.
apply (Intersection_intro T X Y x H4 (proj1 (proj2 H5))).
apply (proj2 H1 X Y H3 (proj1 H5) H6).
Qed.

Lemma Formula_59_1_1 : forall (A B : Type) (f : A -> B) (a1 a2 : A), EquivalenceRelationQuotientFunction A (FunctionEquivalenceRelation A B f) a1 = EquivalenceRelationQuotientFunction A (FunctionEquivalenceRelation A B f) a2 <-> ER A (FunctionEquivalenceRelation A B f) a1 a2.
Proof.
move=> A B f a1 a2.
apply conj.
move=> H1.
suff: (In A (proj1_sig (EquivalenceRelationQuotientFunction A (FunctionEquivalenceRelation A B f) a1)) a2).
apply.
rewrite H1.
apply (Formula_6_1 A (FunctionEquivalenceRelation A B f) a2).
move=> H1.
apply sig_map.
apply (proj1 (Formula_6_2 A (FunctionEquivalenceRelation A B f) a1 a2) H1).
Qed.

Lemma Formula_59_1_2 : forall (A B : Type) (f : A -> B) (a1 a2 : A), ER A (FunctionEquivalenceRelation A B f) a1 a2 <-> f a1 = f a2.
Proof.
move=> A B f a1 a2.
apply conj.
apply.
apply.
Qed.

Lemma Formula_59_2 : forall (A B : Type) (f : A -> B), {g : EquivalenceRelationQuotient A (FunctionEquivalenceRelation A B f) -> {b : B | Im A B (Full_set A) f b} | Bijective g /\ compose (compose (fun (x : {b : B | Im A B (Full_set A) f b}) => proj1_sig x) g) (EquivalenceRelationQuotientFunction A (FunctionEquivalenceRelation A B f)) = f}.
Proof.
move=> A B f.
suff: (forall (X : EquivalenceRelationQuotient A (FunctionEquivalenceRelation A B f)), {b : B | forall (a : A), In A (proj1_sig X) a -> f a = b}).
move=> H1.
suff: (forall (X : EquivalenceRelationQuotient A (FunctionEquivalenceRelation A B f)), In B (Im A B (Full_set A) f) (proj1_sig (H1 X))).
move=> H2.
exists (fun (X : EquivalenceRelationQuotient A (FunctionEquivalenceRelation A B f)) => exist (Im A B (Full_set A) f) (proj1_sig (H1 X)) (H2 X)).
apply conj.
apply InjSurjBij.
move=> X1 X2 H3.
apply sig_map.
suff: (forall (a1 a2 : A), In A (proj1_sig X1) a1 -> In A (proj1_sig X2) a2 -> f a1 = f a2).
elim (proj2_sig X1).
move=> a1 H4 Y1 H5.
elim (proj2_sig X2).
move=> a2 H6 Y2 H7 H8.
rewrite H5.
rewrite H7.
apply (proj1 (Formula_6_2 A (FunctionEquivalenceRelation A B f) a1 a2)).
apply (H8 a1 a2).
rewrite H5.
apply (Formula_6_1 A (FunctionEquivalenceRelation A B f) a1).
rewrite H7.
apply (Formula_6_1 A (FunctionEquivalenceRelation A B f) a2).
move=> a1 a2 H4 H5.
rewrite (proj2_sig (H1 X1) a1 H4).
suff: (proj1_sig (H1 X1) = proj1_sig (exist (Im A B (Full_set A) f) (proj1_sig (H1 X1)) (H2 X1))).
move=> H6.
rewrite H6.
rewrite H3.
rewrite (proj2_sig (H1 X2) a2 H5).
reflexivity.
reflexivity.
move=> b.
suff: (exists (x : EquivalenceRelationQuotient A (FunctionEquivalenceRelation A B f)), proj1_sig (H1 x) = proj1_sig b).
elim.
move=> x H3.
exists x.
apply sig_map.
apply H3.
elim (proj2_sig b).
move=> x H3 y H4.
exists (EquivalenceRelationQuotientFunction A (FunctionEquivalenceRelation A B f) x).
rewrite - (proj2_sig (H1 (EquivalenceRelationQuotientFunction A (FunctionEquivalenceRelation A B f) x)) x).
rewrite H4.
reflexivity.
apply (Formula_6_1 A (FunctionEquivalenceRelation A B f) x).
apply functional_extensionality.
move=> a.
rewrite (proj2_sig (H1 (EquivalenceRelationQuotientFunction A (FunctionEquivalenceRelation A B f) a)) a).
reflexivity.
apply (Formula_6_1 A (FunctionEquivalenceRelation A B f) a).
move=> X.
suff: (exists (a : A), In A (proj1_sig X) a).
elim.
move=> a H2.
rewrite - (proj2_sig (H1 X) a H2).
apply (Im_intro A B (Full_set A) f a (Full_intro A a)).
reflexivity.
elim (proj2_sig X).
move=> x H2 y H3.
rewrite H3.
exists x.
apply (Formula_6_1 A (FunctionEquivalenceRelation A B f) x).
move=> x.
apply constructive_definite_description.
suff: (exists (a : A), In A (proj1_sig x) a).
move=> H1.
apply (unique_existence (fun (b : B) => forall (a : A), In A (proj1_sig x) a -> f a = b)).
apply conj.
elim H1.
move=> a H2.
exists (f a).
move=> a0.
suff: (In A (proj1_sig x) a).
elim (proj2_sig x).
move=> a1 H3 y H4.
rewrite H4.
move=> H5 H6.
rewrite - H6.
apply H5.
apply H2.
move=> b1 b2 H2 H3.
elim H1.
move=> a H4.
rewrite - (H2 a H4).
apply (H3 a H4).
elim (proj2_sig x).
move=> a H1 Y H2.
rewrite H2.
exists a.
apply (Formula_6_1 A (FunctionEquivalenceRelation A B f) a).
Qed.
