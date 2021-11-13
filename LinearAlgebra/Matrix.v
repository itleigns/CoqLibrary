Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "Tools" as Tools.
Add LoadPath "BasicProperty" as BasicProperty.
Add LoadPath "BasicNotation" as BasicNotation.
Add LoadPath "LibraryExtension" as LibraryExtension.
Add LoadPath "LinearAlgebra/SenkeiDaisuunoSekai" as LinearAlgebra.SenkeiDaisuunoSekai.

From mathcomp Require Import ssreflect.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Minus.
Require Import Classical.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Image.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Arith.Compare_dec.
Require Import MyAlgebraicStructure.MyField.
Require Import MyAlgebraicStructure.MyVectorSpace.
Require Import Tools.MySum.
Require Import Tools.MyProd.
Require Import BasicProperty.MappingProperty.
Require Import BasicProperty.NatProperty.
Require Import BasicNotation.Parity.
Require Import BasicNotation.Permutation.
Require Import LibraryExtension.DatatypesExtension.
Require Import LinearAlgebra.SenkeiDaisuunoSekai.SenkeiDaisuunoSekai1.

Section Matrix.

Definition Matrix (f : Field) (M N : nat) := {n : nat| (n < M) } -> {n : nat| (n < N) } -> (FT f).

Definition Mplus (f : Field) (M N : nat) := fun (A B : Matrix f M N) (x : {n : nat| (n < M) }) (y : {n : nat| (n < N) }) => (Fadd f (A x y) (B x y)).

Definition Mmult (f : Field) (M N K : nat) := fun (A : Matrix f M N) (B : Matrix f N K) (x : {n : nat| (n < M) }) (y : {n : nat| (n < K) }) => MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat| (n < N) }) (CountFinite N)) (FPCM f) (fun (n : Count N) => Fmul f (A x n) (B n y)).

Definition Mopp (f : Field) (M N : nat) := fun (A : Matrix f M N) (x : {n : nat| (n < M) }) (y : {n : nat| (n < N) }) => (Fopp f (A x y)).

Definition MO (f : Field) (M N : nat) := fun (x : {n : nat| (n < M) }) (y : {n : nat| (n < N) }) => (FO f).

Definition MI (f : Field) (N : nat) := fun (x : {n : nat| (n < N) }) (y : {n : nat| (n < N) }) => match (Nat.eq_dec (proj1_sig x) (proj1_sig y)) with
  | left _ => (FI f)
  | right _ => (FO f)
end.

Lemma Mplus_comm : forall (f : Field) (M N : nat) (A B : Matrix f M N), (Mplus f M N A B) = (Mplus f M N B A).
Proof.
move=> f M N A B.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mplus.
apply (Fadd_comm f (A x y) (B x y)).
Qed.

Lemma Mplus_assoc : forall (f : Field) (M N : nat) (A B C : Matrix f M N), (Mplus f M N (Mplus f M N A B) C) = (Mplus f M N A (Mplus f M N B C)).
Proof.
move=> f M N A B C.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mplus.
apply (Fadd_assoc f (A x y) (B x y) (C x y)).
Qed.

Lemma Mplus_O_l : forall (f : Field) (M N : nat) (A : Matrix f M N), (Mplus f M N (MO f M N) A) = A.
Proof.
move=> f M N A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mplus.
apply (Fadd_O_l f (A x y)).
Qed.

Lemma Mplus_opp_r : forall (f : Field) (M N : nat) (A : Matrix f M N), (Mplus f M N A (Mopp f M N A)) = MO f M N.
Proof.
move=> f M N A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mplus.
apply (Fadd_opp_r f (A x y)).
Qed.

Lemma Mmult_I_r : forall (f : Field) (M N : nat) (A : Matrix f M N), (Mmult f M N N A (MI f N)) = A.
Proof.
move=> f M N A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
rewrite (MySumF2Excluded {n : nat | (n < N)} (FPCM f) (fun n : Count N => Fmul f (A x n) (MI f N n y)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (fun (m : {n : nat | (n < N)}) => proj1_sig m = proj1_sig y)).
suff: (FiniteIntersection {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (fun m : {n : nat | (n < N)} => proj1_sig m = proj1_sig y)) = FiniteSingleton {n : nat | (n < N)} y.
move=> H1.
rewrite H1.
rewrite MySumF2Singleton.
suff: (MySumF2 {n : nat | (n < N)} (FiniteIntersection {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (Complement {n : nat | (n < N)} (fun m : {n : nat | (n < N)} => proj1_sig m = proj1_sig y))) (FPCM f) (fun n : Count N => Fmul f (A x n) (MI f N n y)) = FO f).
move=> H2.
rewrite H2.
simpl.
rewrite (Fadd_O_r f (Fmul f (A x y) (MI f N y y))).
unfold MI.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig y)).
move=> H3.
apply (Fmul_I_r f (A x y)).
move=> H3.
apply False_ind.
apply H3.
reflexivity.
apply MySumF2Induction.
apply conj.
reflexivity.
move=> cm u.
unfold In.
unfold FiniteIntersection.
move=> H2 H3.
rewrite H3.
unfold MI.
elim H2.
move=> u0 H4 H5.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig y)).
move=> H6.
apply False_ind.
apply (H4 H6).
move=> H6.
rewrite (Fmul_O_r f (A x u0)).
apply (Fadd_O_l f (FO f)).
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> m H1.
apply Singleton_intro.
apply sig_map.
elim H1.
move=> m1 H2 H3.
rewrite H2.
reflexivity.
move=> m H1.
apply Intersection_intro.
rewrite H1.
reflexivity.
apply Full_intro.
Qed.

Lemma Mmult_I_l : forall (f : Field) (M N : nat) (A : Matrix f M N), (Mmult f M M N (MI f M) A) = A.
Proof.
move=> f M N A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
rewrite (MySumF2Excluded {n : nat | (n < M)} (FPCM f) (fun n : Count M => Fmul f (MI f M x n) (A n y)) (exist (Finite (Count M)) (Full_set {n : nat | (n < M)}) (CountFinite M)) (fun (m : {n : nat | (n < M)}) => proj1_sig m = proj1_sig x)).
suff: (FiniteIntersection {n : nat | (n < M)} (exist (Finite (Count M)) (Full_set {n : nat | (n < M)}) (CountFinite M)) (fun m : {n : nat | (n < M)} => proj1_sig m = proj1_sig x)) = FiniteSingleton {n : nat | (n < M)} x.
move=> H1.
rewrite H1.
rewrite MySumF2Singleton.
suff: (MySumF2 {n : nat | (n < M)} (FiniteIntersection {n : nat | (n < M)} (exist (Finite (Count M)) (Full_set {n : nat | (n < M)}) (CountFinite M)) (Complement {n : nat | (n < M)} (fun m : {n : nat | (n < M)} => proj1_sig m = proj1_sig x))) (FPCM f) (fun n : Count M => Fmul f (MI f M x n) (A n y)) = FO f).
move=> H2.
rewrite H2.
simpl.
rewrite (Fadd_O_r f (Fmul f (MI f M x x) (A x y))).
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig x)).
move=> H3.
apply (Fmul_I_l f (A x y)).
move=> H3.
apply False_ind.
apply H3.
reflexivity.
apply MySumF2Induction.
apply conj.
reflexivity.
move=> cm u.
unfold In.
unfold FiniteIntersection.
move=> H2 H3.
rewrite H3.
unfold MI.
elim H2.
move=> u0 H4 H5.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig u0)).
move=> H6.
apply False_ind.
apply H4.
rewrite H6.
reflexivity.
move=> H6.
rewrite (Fmul_O_l f (A u0 y)).
apply (Fadd_O_l f (FO f)).
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> m H1.
apply Singleton_intro.
apply sig_map.
elim H1.
move=> m1 H2 H3.
rewrite H2.
reflexivity.
move=> m H1.
apply Intersection_intro.
rewrite H1.
reflexivity.
apply Full_intro.
Qed.

Lemma Mmult_O_r : forall (f : Field) (M N K : nat) (A : Matrix f M N), (Mmult f M N K A (MO f N K)) = MO f M K.
Proof.
move=> f M N K A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply MySumF2O.
move=> u H1.
apply (Fmul_O_r f (A x u)).
Qed.

Lemma Mmult_O_l : forall (f : Field) (M N K : nat) (A : Matrix f N K), (Mmult f M N K (MO f M N) A) = MO f M K.
Proof.
move=> f M N K A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply MySumF2O.
move=> u H1.
apply (Fmul_O_l f (A u y)).
Qed.

Lemma Mmult_assoc : forall (f : Field) (M N K L : nat) (A : Matrix f M N) (B : Matrix f N K) (C : Matrix f K L), (Mmult f M K L (Mmult f M N K A B) C) = (Mmult f M N L A (Mmult f N K L B C)).
Proof.
move=> f M N K L A B C.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (Mmult f M K L (Mmult f M N K A B) C x y = MySumF2 ({n : nat | (n < N)} * {n : nat | (n < K)}) (FinitePair {n : nat | (n < N)} {n : nat | (n < K)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (exist (Finite (Count K)) (Full_set {n : nat | (n < K)}) (CountFinite K))) (FPCM f) (fun (nm : ({n : nat | (n < N)} * {n : nat | (n < K)})) => Fmul f (Fmul f (A x (fst nm)) (B (fst nm) (snd nm))) (C (snd nm) y))).
move=> H1.
rewrite H1.
suff: (Mmult f M N L A (Mmult f N K L B C) x y = MySumF2 ({n : nat | (n < N)} * {n : nat | (n < K)}) (FinitePair {n : nat | (n < N)} {n : nat | (n < K)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (exist (Finite (Count K)) (Full_set {n : nat | (n < K)}) (CountFinite K))) (FPCM f) (fun (nm : ({n : nat | (n < N)} * {n : nat | (n < K)})) => Fmul f (Fmul f (A x (fst nm)) (B (fst nm) (snd nm))) (C (snd nm) y))).
move=> H2.
rewrite H2.
reflexivity.
rewrite (MySumF2Pair {n : nat | (n < N)} {n : nat | (n < K)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (exist (Finite (Count K)) (Full_set {n : nat | (n < K)}) (CountFinite K)) (FPCM f) (fun (n0 : {n : nat | (n < N)}) (k0 : {n : nat | (n < K)}) => Fmul f (Fmul f (A x n0) (B n0 k0)) (C k0 y))).
unfold Mmult.
suff: ((fun n : Count N => Fmul f (A x n) (MySumF2 {n0 : nat | (n0 < K)} (exist (Finite (Count K)) (Full_set {n0 : nat | (n0 < K)}) (CountFinite K)) (FPCM f) (fun n0 : Count K => Fmul f (B n n0) (C n0 y)))) = (fun u : {n : nat | (n < N)} => MySumF2 {n : nat | (n < K)} (exist (Finite (Count K)) (Full_set {n : nat | (n < K)}) (CountFinite K)) (FPCM f) (fun k0 : {n : nat | (n < K)} => Fmul f (Fmul f (A x u) (B u k0)) (C k0 y)))).
move=> H2.
rewrite H2.
reflexivity.
apply functional_extensionality.
move=> k.
apply (FiniteSetInduction (Count K) (exist (Finite (Count K)) (Full_set {n0 : nat | (n0 < K)}) (CountFinite K))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Fmul_O_r f (A x k)).
move=> A1 a1 H2 H3 H4 H5.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite Fmul_add_distr_l.
rewrite H5.
rewrite (Fmul_assoc f (A x k) (B k a1) (C a1 y)).
reflexivity.
apply H4.
apply H4.
suff: (MySumF2 ({n : nat | (n < N)} * {n : nat | (n < K)}) (FinitePair {n : nat | (n < N)} {n : nat | (n < K)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (exist (Finite (Count K)) (Full_set {n : nat | (n < K)}) (CountFinite K))) (FPCM f) (fun nm : {n : nat | (n < N)} * {n : nat | (n < K)} => Fmul f (Fmul f (A x (fst nm)) (B (fst nm) (snd nm))) (C (snd nm) y)) = MySumF2 ({n : nat | (n < K)} * {n : nat | (n < N)}) (FinitePair {n : nat | (n < K)} {n : nat | (n < N)} (exist (Finite (Count K)) (Full_set {n : nat | (n < K)}) (CountFinite K)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))) (FPCM f) (fun nm : {n : nat | (n < K)} * {n : nat | (n < N)} => Fmul f (Fmul f (A x (snd nm)) (B (snd nm) (fst nm))) (C (fst nm) y))).
move=> H2.
rewrite H2.
unfold Mmult.
rewrite (MySumF2Pair {n : nat | (n < K)} {n : nat | (n < N)} (exist (Finite (Count K)) (Full_set {n : nat | (n < K)}) (CountFinite K)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FPCM f) (fun (n0 : {n : nat | (n < K)}) (k0 : {n : nat | (n < N)}) => Fmul f (Fmul f (A x k0) (B k0 n0)) (C n0 y))).
suff: ((fun n : Count K => Fmul f (MySumF2 {n0 : nat | (n0 < N)} (exist (Finite (Count N)) (Full_set {n0 : nat | (n0 < N)}) (CountFinite N)) (FPCM f) (fun n0 : Count N => Fmul f (A x n0) (B n0 n))) (C n y)) = (fun u : {n : nat | (n < K)} => MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FPCM f) (fun k0 : {n : nat | (n < N)} => Fmul f (Fmul f (A x k0) (B k0 u)) (C u y)))).
move=> H3.
rewrite H3.
reflexivity.
apply functional_extensionality.
move=> k.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (Full_set {n0 : nat | (n0 < N)}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Fmul_O_l f (C k y)).
move=> A1 a1 H3 H4 H5 H6.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite Fmul_add_distr_r.
rewrite H6.
reflexivity.
apply H5.
apply H5.
suff: (forall u : ({n : nat | (n < N)} * {n : nat | (n < K)}), proj1_sig (FinitePair {n : nat | (n < N)} {n : nat | (n < K)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (exist (Finite (Count K)) (Full_set {n : nat | (n < K)}) (CountFinite K))) u -> proj1_sig (FinitePair {n : nat | (n < K)} {n : nat | (n < N)} (exist (Finite (Count K)) (Full_set {n : nat | (n < K)}) (CountFinite K)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))) ((fun nm : {n : nat | (n < N)} * {n : nat | (n < K)} => (snd nm, fst nm)) u)).
move=> H1.
rewrite - (MySumF2BijectiveSame ({n : nat | (n < N)} * {n : nat | (n < K)}) (FinitePair {n : nat | (n < N)} {n : nat | (n < K)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (exist (Finite (Count K)) (Full_set {n : nat | (n < K)}) (CountFinite K))) ({n : nat | (n < K)} * {n : nat | (n < N)}) (FinitePair {n : nat | (n < K)} {n : nat | (n < N)} (exist (Finite (Count K)) (Full_set {n : nat | (n < K)}) (CountFinite K)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))) (FPCM f) (fun nm : {n : nat | (n < K)} * {n : nat | (n < N)} => Fmul f (Fmul f (A x (snd nm)) (B (snd nm) (fst nm))) (C (fst nm) y)) (fun (nm : {n : nat | (n < N)} * {n : nat | (n < K)}) => (snd nm, fst nm)) H1).
reflexivity.
simpl.
suff: (forall u : ({n : nat | (n < K)} * {n : nat | (n < N)}), proj1_sig (FinitePair {n : nat | (n < K)} {n : nat | (n < N)} (exist (Finite (Count K)) (Full_set {n : nat | (n < K)}) (CountFinite K)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))) u -> proj1_sig (FinitePair {n : nat | (n < N)} {n : nat | (n < K)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (exist (Finite (Count K)) (Full_set {n : nat | (n < K)}) (CountFinite K))) ((fun nm : {n : nat | (n < K)} * {n : nat | (n < N)} => (snd nm, fst nm)) u)).
move=> H2.
exists (fun u : {u : {n : nat | (n < K)} * {n : nat | (n < N)} | Full_set {n : nat | (n < K)} (fst u) /\ Full_set {n : nat | (n < N)} (snd u)} => exist (fun uv : {n : nat | (n < N)} * {n : nat | (n < K)} => Full_set {n : nat | (n < N)} (fst uv) /\ Full_set {n : nat | (n < K)} (snd uv)) (snd (proj1_sig u), fst (proj1_sig u)) (H2 (proj1_sig u) (proj2_sig u))).
apply conj.
move=> u.
apply sig_map.
simpl.
rewrite - (surjective_pairing (proj1_sig u)).
reflexivity.
move=> u.
apply sig_map.
simpl.
rewrite - (surjective_pairing (proj1_sig u)).
reflexivity.
move=> u H2.
simpl.
apply conj.
apply Full_intro.
apply Full_intro.
move=> u H1.
simpl.
apply conj.
apply Full_intro.
apply Full_intro.
Qed.

Lemma Mmult_plus_distr_l : forall (f : Field) (M N K : nat) (A : Matrix f M N) (B C : Matrix f N K), (Mmult f M N K A (Mplus f N K B C)) = (Mplus f M K (Mmult f M N K A B) (Mmult f M N K A C)).
Proof.
move=> f M N K A B C.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mplus.
unfold Mmult.
apply (FiniteSetInduction {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (Fadd_O_l f (CMe (FPCM f))).
reflexivity.
move=> B0 b0 H1 H2 H3 H4.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H4.
simpl.
rewrite - (Fadd_assoc f (Fadd f (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (B n y))) (Fmul f (A x b0) (B b0 y))) (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y))) (Fmul f (A x b0) (C b0 y))).
rewrite (Fadd_assoc f (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (B n y))) (Fmul f (A x b0) (B b0 y)) (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y)))).
rewrite (Fadd_comm f (Fmul f (A x b0) (B b0 y)) (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y)))).
rewrite - (Fadd_assoc f (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (B n y))) (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y))) (Fmul f (A x b0) (B b0 y))).
rewrite (Fadd_assoc f (Fadd f (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (B n y))) (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y)))) (Fmul f (A x b0) (B b0 y)) (Fmul f (A x b0) (C b0 y))).
rewrite (Fmul_add_distr_l f).
reflexivity.
apply H3.
apply H3.
apply H3.
Qed.

Lemma Mmult_plus_distr_r : forall (f : Field) (M N K : nat) (A B : Matrix f M N) (C : Matrix f N K), (Mmult f M N K (Mplus f M N A B) C) = (Mplus f M K (Mmult f M N K A C) (Mmult f M N K B C)).
Proof.
move=> f M N K A B C.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mplus.
unfold Mmult.
apply (FiniteSetInduction {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (Fadd_O_l f (CMe (FPCM f))).
reflexivity.
move=> B0 b0 H1 H2 H3 H4.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H4.
simpl.
rewrite - (Fadd_assoc f (Fadd f (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y))) (Fmul f (A x b0) (C b0 y))) (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (B x n) (C n y))) (Fmul f (B x b0) (C b0 y))).
rewrite (Fadd_assoc f (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y))) (Fmul f (A x b0) (C b0 y)) (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (B x n) (C n y)))).
rewrite (Fadd_comm f (Fmul f (A x b0) (C b0 y)) (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (B x n) (C n y)))).
rewrite - (Fadd_assoc f (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y))) (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (B x n) (C n y))) (Fmul f (A x b0) (C b0 y))).
rewrite (Fadd_assoc f (Fadd f (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y))) (MySumF2 {n : nat | (n < N)} B0 (FPCM f) (fun n : Count N => Fmul f (B x n) (C n y)))) (Fmul f (A x b0) (C b0 y)) (Fmul f (B x b0) (C b0 y))).
rewrite (Fmul_add_distr_r f).
reflexivity.
apply H3.
apply H3.
apply H3.
Qed.

Definition VMmult (f : Field) (M N : nat) := fun (c : FT f) (A : Matrix f M N) (x : {n : nat | (n < M)}) (y : {n : nat | (n < N)}) => (Fmul f c (A x y)).

Lemma VMmult_plus_distr_l : forall (f : Field) (M N : nat) (c : FT f) (A B : Matrix f M N), (VMmult f M N c (Mplus f M N A B)) = (Mplus f M N (VMmult f M N c A) (VMmult f M N c B)).
Proof.
move=> f M N c A B.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply Fmul_add_distr_l.
Qed.

Lemma VMmult_plus_distr_r : forall (f : Field) (M N : nat) (c d : FT f) (A : Matrix f M N), (VMmult f M N (Fadd f c d) A) = (Mplus f M N (VMmult f M N c A) (VMmult f M N d A)).
Proof.
move=> f M N c A B.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply Fmul_add_distr_r.
Qed.

Lemma VMmult_assoc : forall (f : Field) (M N : nat) (c d : FT f) (A : Matrix f M N), (VMmult f M N (Fmul f c d) A) = (VMmult f M N c (VMmult f M N d A)).
Proof.
move=> f M N c d A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply Fmul_assoc.
Qed.

Lemma VMmult_assoc_reverse : forall (f : Field) (M N : nat) (c d : FT f) (A : Matrix f M N), (VMmult f M N c (VMmult f M N d A)) = (VMmult f M N (Fmul f c d) A).
Proof.
move=> f M N c d A.
rewrite (VMmult_assoc f M N c d A).
reflexivity.
Qed.

Lemma VMmult_assoc_l : forall (f : Field) (M N K : nat) (c : FT f) (A : Matrix f M N) (B : Matrix f N K), (Mmult f M N K (VMmult f M N c A) B) = (VMmult f M K c (Mmult f M N K A B)).
Proof.
move=> f M N K c A B.
unfold Mmult.
unfold VMmult.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply (FiniteSetInduction {n : nat | n < N} (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (Fmul_O_r f c).
reflexivity.
move=> D d H1 H2 H3 H4.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H4.
rewrite (Fmul_add_distr_l f c (MySumF2 {n : nat | n < N} D (FPCM f) (fun (n : Count N) => Fmul f (A x n) (B n y))) (Fmul f (A x d) (B d y))).
rewrite (Fmul_assoc f c (A x d) (B d y)).
reflexivity.
apply H3.
apply H3.
Qed.

Lemma VMmult_assoc_r : forall (f : Field) (M N K : nat) (c : FT f) (A : Matrix f M N) (B : Matrix f N K), (Mmult f M N K A (VMmult f N K c B)) = (VMmult f M K c (Mmult f M N K A B)).
Proof.
move=> f M N K c A B.
unfold Mmult.
unfold VMmult.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply (FiniteSetInduction {n : nat | n < N} (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (Fmul_O_r f c).
reflexivity.
move=> D d H1 H2 H3 H4.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H4.
rewrite (Fmul_add_distr_l f c (MySumF2 {n : nat | n < N} D (FPCM f) (fun (n : Count N) => Fmul f (A x n) (B n y))) (Fmul f (A x d) (B d y))).
rewrite - (Fmul_assoc f c (A x d) (B d y)).
rewrite (Fmul_comm f c (A x d)).
rewrite (Fmul_assoc f (A x d) c (B d y)).
reflexivity.
apply H3.
apply H3.
Qed.

Lemma VMmult_I_l : forall (f : Field) (M N : nat) (A : Matrix f M N), (VMmult f M N (FI f) A) = A.
Proof.
move=> f M N A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply Fmul_I_l.
Qed.

Definition MVectorToMatrix (f : Field) (N : nat) (v : {n : nat | (n < N)%nat} -> FT f) := fun (x : {n : nat | (n < N)%nat}) (y : {n : nat | (n < 1)%nat}) => v x.

Definition MMatrixToVector (f : Field) (N : nat) (A : Matrix f N 1) := fun (x : {n : nat | (n < N)%nat}) => A x Single.

Lemma MVectorMatrixRelation : forall (f : Field) (N : nat), (forall (v : {n : nat | (n < N)%nat} -> FT f), MMatrixToVector f N (MVectorToMatrix f N v) = v) /\ forall (A : Matrix f N 1), MVectorToMatrix f N (MMatrixToVector f N A) = A.
Proof.
move=> f N.
apply conj.
move=> v.
reflexivity.
move=> A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MMatrixToVector.
unfold MVectorToMatrix.
rewrite (SingleSame y).
reflexivity.
Qed.

Definition MVmult (f : Field) (M N : nat) (A : Matrix f M N) (v : {n : nat | (n < N)%nat} -> FT f) := MMatrixToVector f M (Mmult f M N 1 A (MVectorToMatrix f N v)).

Definition MVS (f : Field) (M N : nat) := mkVectorSpace f (Matrix f M N) (MO f M N) (Mplus f M N) (VMmult f M N) (Mopp f M N) (Mplus_comm f M N) (Mplus_assoc f M N) (Mplus_O_l f M N) (Mplus_opp_r f M N) (VMmult_plus_distr_l f M N) (VMmult_plus_distr_r f M N) (VMmult_assoc_reverse f M N) (VMmult_I_l f M N).

Fixpoint PowM (f : Field) (N : nat) (A : Matrix f N N) (r : nat) : Matrix f N N := match r with
  | O => MI f N
  | S k => Mmult f N N N (PowM f N A k) A
end.

Definition MMM (f : Field) (N : nat) := mkMonoid (Matrix f N N) (MI f N) (Mmult f N N N) (Mmult_I_r f N N) (Mmult_I_l f N N) (Mmult_assoc f N N N N).

Lemma PowMMyProdFL : forall (f : Field) (N : nat) (A : Matrix f N N) (r : nat), PowM f N A r = MyProdFL (MMM f N) (repeat A r).
Proof.
move=> f N A.
suff: (forall (r : nat), rev (repeat A r) = repeat A r).
move=> H1 r.
rewrite (MyProdFLReverse (MMM f N) (repeat A r)).
elim r.
reflexivity.
move=> n H2.
rewrite (H1 (S n)).
simpl.
rewrite H2.
rewrite (H1 n).
reflexivity.
elim.
reflexivity.
move=> n H1.
simpl.
rewrite H1.
rewrite (repeat_cons n A).
reflexivity.
Qed.

Lemma PowMplus : forall (f : Field) (N : nat) (A : Matrix f N N) (r1 r2 : nat), PowM f N A (r1 + r2) = Mmult f N N N (PowM f N A r1) (PowM f N A r2).
Proof.
move=> f N A r1 r2.
rewrite (PowMMyProdFL f N A (r1 + r2)).
rewrite (PowMMyProdFL f N A r1).
rewrite (PowMMyProdFL f N A r2).
suff: (repeat A (r1 + r2) = repeat A r1 ++ repeat A r2).
move=> H1.
rewrite H1.
apply (MyProdFLApp (MMM f N) (repeat A r1) (repeat A r2)).
elim r1.
reflexivity.
move=> n H1.
simpl.
rewrite H1.
reflexivity.
Qed.

Definition MTranspose (f : Field) (M N : nat) := fun (A : Matrix f M N) (x : {n : nat | (n < N)}) (y : {n : nat | (n < M)}) => A y x.

Lemma MTransI : forall (f : Field) (N : nat), MTranspose f N N (MI f N) = MI f N.
Proof.
move=> f N.
unfold MTranspose.
unfold MI.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig x)).
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H2.
reflexivity.
move=> H2.
apply False_ind.
apply H2.
rewrite H1.
reflexivity.
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H2.
apply False_ind.
apply H1.
rewrite H2.
reflexivity.
move=> H2.
reflexivity.
Qed.

Lemma MTransO : forall (f : Field) (M N : nat), MTranspose f M N (MO f M N) = MO f N M.
Proof.
move=> f M N.
reflexivity.
Qed.

Lemma MTransPlus : forall (f : Field) (M N : nat) (A B : Matrix f M N), (MTranspose f M N (Mplus f M N A B)) = (Mplus f N M (MTranspose f M N A) (MTranspose f M N B)).
Proof.
move=> f M N A B.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
reflexivity.
Qed.

Lemma MTransOpp : forall (f : Field) (M N : nat) (A : Matrix f M N), (MTranspose f M N (Mopp f M N A)) = (Mopp f N M (MTranspose f M N A)).
Proof.
move=> f M N A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
reflexivity.
Qed.

Lemma MTransMult : forall (f : Field) (M N K : nat) (A : Matrix f M N) (B : Matrix f N K), (MTranspose f M K (Mmult f M N K A B)) = (Mmult f K N M (MTranspose f N K B) (MTranspose f M N A)).
Proof.
move=> f M N K A B.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MTranspose.
unfold Mmult.
suff: ((fun n : Count N => Fmul f (A y n) (B n x)) = (fun n : Count N => Fmul f (B n x) (A y n))).
move=> H1.
rewrite H1.
reflexivity.
apply functional_extensionality.
move=> n.
apply Fmul_comm.
Qed.

Lemma MTransVMult : forall (f : Field) (M N : nat) (c : FT f) (A : Matrix f M N), (MTranspose f M N (VMmult f M N c A)) = (VMmult f N M c (MTranspose f M N A)).
Proof.
move=> f M N c A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
reflexivity.
Qed.

Lemma MTransTrans : forall (f : Field) (M N : nat) (A : Matrix f M N), (MTranspose f N M (MTranspose f M N A)) = A.
Proof.
move=> f M N A.
reflexivity.
Qed.

Lemma MTransReg : forall (f : Field) (M N : nat) (A B : Matrix f M N), (MTranspose f M N A) = (MTranspose f M N B) -> A = B.
Proof.
move=> f M N A B H1.
rewrite - (MTransTrans f M N A).
rewrite - (MTransTrans f M N B).
rewrite H1.
reflexivity.
Qed.

Definition MDiag (f : Field) (N : nat) (a : {n : nat | (n < N)%nat} -> FT f) := fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig x) (proj1_sig y) with
  | left _ => a x
  | right _ => FO f
end.

Lemma MDiagMult : forall (f : Field) (N : nat) (a b : {n : nat | (n < N)%nat} -> FT f), Mmult f N N N (MDiag f N a) (MDiag f N b) = MDiag f N (fun (m : {n : nat | (n < N)%nat}) => Fmul f (a m) (b m)).
Proof.
move=> f N a b.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H1.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} x)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite H1.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig y)).
move=> H2.
apply (CM_O_r (FPCM f)).
elim.
reflexivity.
move=> u.
elim.
move=> u0 H2 H3.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig u0)).
move=> H4.
elim H2.
suff: (x = u0).
move=> H5.
rewrite H5.
apply (In_singleton {n : nat | (n < N)%nat} u0).
apply sig_map.
apply H4.
move=> H4.
apply (Fmul_O_l f).
move=> u H2.
apply (Full_intro {n : nat | (n < N)%nat} u).
move=> H1.
apply MySumF2O.
move=> u H2.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig u)).
move=> H3.
elim (Nat.eq_dec (proj1_sig u) (proj1_sig y)).
move=> H4.
elim H1.
rewrite H3.
apply H4.
move=> H4.
apply (Fmul_O_r f (a x)).
move=> H3.
apply (Fmul_O_l f).
Qed.

Lemma MDiagTrans : forall (f : Field) (N : nat) (a : {n : nat | (n < N)%nat} -> FT f), MTranspose f N N (MDiag f N a) = (MDiag f N a).
Proof.
move=> f N a.
unfold MTranspose.
unfold MDiag.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig x)).
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H2.
suff: (y = x).
move=> H3.
rewrite H3.
reflexivity.
apply sig_map.
apply H1.
elim.
rewrite H1.
reflexivity.
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H2.
elim H1.
rewrite H2.
reflexivity.
move=> H2.
reflexivity.
Qed.

Definition MSymmetric (f : Field) (N : nat) (A : Matrix f N N) := MTranspose f N N A = A.

Definition MBlockH := fun (f : Field) (M1 M2 N : nat) (A1 : Matrix f M1 N) (A2 : Matrix f M2 N) (x : {n : nat | (n < M1 + M2)}) (y : {n : nat | (n < N)}) => match (AddConnectInv M1 M2 x) with
  | inl x0 => A1 x0 y
  | inr x0 => A2 x0 y
end.

Definition MBlockW := fun (f : Field) (M N1 N2 : nat) (A1 : Matrix f M N1) (A2 : Matrix f M N2) (x : {n : nat | (n < M)}) (y : {n : nat | (n < N1 + N2)}) => match (AddConnectInv N1 N2 y) with
  | inl y0 => A1 x y0
  | inr y0 => A2 x y0
end.

Lemma MBlockHPlus : forall (f : Field) (M1 M2 N : nat) (A1 B1 : Matrix f M1 N) (A2 B2 : Matrix f M2 N), Mplus f (M1 + M2) N (MBlockH f M1 M2 N A1 A2) (MBlockH f M1 M2 N B1 B2) = MBlockH f M1 M2 N (Mplus f M1 N A1 B1) (Mplus f M2 N A2 B2).
Proof.
move=> f M1 M2 N A1 B1 A2 B2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mplus.
unfold MBlockH.
elim (AddConnectInv M1 M2 x).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockWPlus : forall (f : Field) (M N1 N2 : nat) (A1 B1 : Matrix f M N1) (A2 B2 : Matrix f M N2), Mplus f M (N1 + N2) (MBlockW f M N1 N2 A1 A2) (MBlockW f M N1 N2 B1 B2) = MBlockW f M N1 N2 (Mplus f M N1 A1 B1) (Mplus f M N2 A2 B2).
Proof.
move=> f M N1 N2 A1 B1 A2 B2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mplus.
unfold MBlockW.
elim (AddConnectInv N1 N2 y).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockHOpp : forall (f : Field) (M1 M2 N : nat) (A1 : Matrix f M1 N) (A2 : Matrix f M2 N), Mopp f (M1 + M2) N (MBlockH f M1 M2 N A1 A2) = MBlockH f M1 M2 N (Mopp f M1 N A1) (Mopp f M2 N A2).
Proof.
move=> f M1 M2 N A1 A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mopp.
unfold MBlockH.
elim (AddConnectInv M1 M2 x).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockWOpp : forall (f : Field) (M N1 N2 : nat) (A1 : Matrix f M N1) (A2 : Matrix f M N2), Mopp f M (N1 + N2) (MBlockW f M N1 N2 A1 A2) = MBlockW f M N1 N2 (Mopp f M N1 A1) (Mopp f M N2 A2).
Proof.
move=> f M N1 N2 A1 A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mopp.
unfold MBlockW.
elim (AddConnectInv N1 N2 y).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockHMult : forall (f : Field) (M1 M2 N K : nat) (A1 : Matrix f M1 N) (A2 : Matrix f M2 N) (B : Matrix f N K), Mmult f (M1 + M2) N K (MBlockH f M1 M2 N A1 A2) B = MBlockH f M1 M2 K (Mmult f M1 N K A1 B) (Mmult f M2 N K A2 B).
Proof.
move=> f M1 M2 N K A1 A2 B.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
unfold MBlockH.
elim (AddConnectInv M1 M2 x).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockWMult : forall (f : Field) (M N K1 K2 : nat) (A : Matrix f M N) (B1 : Matrix f N K1) (B2 : Matrix f N K2), Mmult f M N (K1 + K2) A (MBlockW f N K1 K2 B1 B2) = MBlockW f M K1 K2 (Mmult f M N K1 A B1) (Mmult f M N K2 A B2).
Proof.
move=> f M N K1 K2 A B1 B2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
unfold MBlockW.
elim (AddConnectInv K1 K2 y).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockHWMult : forall (f : Field) (M N1 N2 K : nat) (A1 : Matrix f M N1) (A2 : Matrix f M N2) (B1 : Matrix f N1 K) (B2 : Matrix f N2 K), Mmult f M (N1 + N2) K (MBlockW f M N1 N2 A1 A2) (MBlockH f N1 N2 K B1 B2) = Mplus f M K (Mmult f M N1 K A1 B1) (Mmult f M N2 K A2 B2).
Proof.
move=> f M N1 N2 K A1 A2 B1 B2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
unfold Mplus.
unfold MBlockH.
unfold MBlockW.
rewrite (MySumF2Excluded {n : nat | (n < N1 + N2)} (FPCM f) (fun n : Count (N1 + N2) => Fmul f match AddConnectInv N1 N2 n with
  | inl y0 => A1 x y0
  | inr y0 => A2 x y0
end match AddConnectInv N1 N2 n with
  | inl x0 => B1 x0 y
  | inr x0 => B2 x0 y
end) (exist (Finite (Count (N1 + N2))) (Full_set {n : nat | (n < N1 + N2)}) (CountFinite (N1 + N2))) (fun (m : {n : nat | (n < N1 + N2)}) => (proj1_sig m < N1))).
suff: ((MySumF2 {n : nat | (n < N1 + N2)} (FiniteIntersection {n : nat | (n < N1 + N2)} (exist (Finite (Count (N1 + N2))) (Full_set {n : nat | (n < N1 + N2)}) (CountFinite (N1 + N2))) (fun m : {n : nat | (n < N1 + N2)} => (proj1_sig m < N1))) (FPCM f) (fun n : Count (N1 + N2) => Fmul f match AddConnectInv N1 N2 n with
  | inl y0 => A1 x y0
  | inr y0 => A2 x y0
end match AddConnectInv N1 N2 n with
  | inl x0 => B1 x0 y
  | inr x0 => B2 x0 y
end)) = (MySumF2 {n : nat | (n < N1)} (exist (Finite (Count N1)) (Full_set {n : nat | (n < N1)}) (CountFinite N1)) (FPCM f) (fun n : Count N1 => Fmul f (A1 x n) (B1 n y)))).
move=> H1.
rewrite H1.
suff: ((MySumF2 {n : nat | (n < N1 + N2)} (FiniteIntersection {n : nat | (n < N1 + N2)} (exist (Finite (Count (N1 + N2))) (Full_set {n : nat | (n < N1 + N2)}) (CountFinite (N1 + N2))) (Complement {n : nat | (n < N1 + N2)} (fun m : {n : nat | (n < N1 + N2)} => (proj1_sig m < N1)))) (FPCM f) (fun n : Count (N1 + N2) => Fmul f match AddConnectInv N1 N2 n with
  | inl y0 => A1 x y0
  | inr y0 => A2 x y0
end match AddConnectInv N1 N2 n with
  | inl x0 => B1 x0 y
  | inr x0 => B2 x0 y
end)) = (MySumF2 {n : nat | (n < N2)} (exist (Finite (Count N2)) (Full_set {n : nat | (n < N2)}) (CountFinite N2)) (FPCM f) (fun n : Count N2 => Fmul f (A2 x n) (B2 n y)))).
move=> H2.
rewrite H2.
reflexivity.
rewrite - (MySumF2BijectiveSame {n : nat | (n < N2)} (exist (Finite (Count N2)) (Full_set {n : nat | (n < N2)}) (CountFinite N2)) {n : nat | (n < N1 + N2)} (FiniteIntersection {n : nat | (n < N1 + N2)} (exist (Finite (Count (N1 + N2))) (Full_set {n : nat | (n < N1 + N2)}) (CountFinite (N1 + N2))) (Complement {n : nat | (n < N1 + N2)} (fun m : {n : nat | (n < N1 + N2)} => (proj1_sig m < N1)))) (FPCM f) (fun n : Count (N1 + N2) => Fmul f match AddConnectInv N1 N2 n with
  | inl y0 => A1 x y0
  | inr y0 => A2 x y0
end match AddConnectInv N1 N2 n with
  | inl x0 => B1 x0 y
  | inr x0 => B2 x0 y
end) (fun (u1 : {n : nat | (n < N2)}) => AddConnect N1 N2 (inr u1))).
apply (MySumF2Same {n : nat | (n < N2)} (exist (Finite (Count N2)) (Full_set {n : nat | (n < N2)}) (CountFinite N2)) (FPCM f)).
move=> u H2.
suff: (match AddConnectInv N1 N2 (AddConnect N1 N2 (inr u)) return Prop with
  | inl _ => False
  | inr k => proj1_sig (AddConnect N1 N2 (inr u)) = N1 + proj1_sig k
end).
elim (AddConnectInv N1 N2 (AddConnect N1 N2 (inr u))).
move=> k.
elim.
move=> k H3.
suff: (k = u).
move=> H4.
rewrite H4.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig k) (proj1_sig u) N1).
rewrite - H3.
rewrite (proj2 (AddConnectNature N1 N2) u).
reflexivity.
apply (proj2 (AddConnectInvNature N1 N2) (AddConnect N1 N2 (inr u))).
rewrite - (proj2 (AddConnectNature N1 N2) u).
apply (le_plus_l N1 (proj1_sig u)).
move=> u H2.
apply (Intersection_intro {n : nat | (n < N1 + N2)}).
apply (le_not_lt N1 (proj1_sig (AddConnect N1 N2 (inr u)))).
rewrite - (proj2 (AddConnectNature N1 N2) u).
apply (le_plus_l N1 (proj1_sig u)).
apply (Full_intro {n : nat | (n < N1 + N2)}).
move=> H2.
simpl.
apply InjSurjBij.
move=> u1 u2 H3.
apply sig_map.
apply (injective_inr {n : nat | n < N1} {n : nat | n < N2}).
apply (BijInj ({n : nat | n < N1} + {n : nat | n < N2}) {n : nat | n < N1 + N2} (AddConnect N1 N2)).
exists (AddConnectInv N1 N2).
apply (AddConnectInvRelation N1 N2).
suff: (AddConnect N1 N2 (inr (proj1_sig u1)) = proj1_sig (exist (Intersection {n : nat | n < N1 + N2} (Complement {n : nat | n < N1 + N2} (fun m : {n : nat | n < N1 + N2} => proj1_sig m < N1)) (Full_set {n : nat | n < N1 + N2})) (AddConnect N1 N2 (inr (proj1_sig u1))) (H2 (proj1_sig u1) (proj2_sig u1)))).
move=> H4.
rewrite H4.
rewrite H3.
reflexivity.
reflexivity.
move=> u.
suff: (match AddConnectInv N1 N2 (proj1_sig u) return Prop with
  | inl _ => False
  | inr k => proj1_sig (proj1_sig u) = N1 + proj1_sig k
end).
elim (AddConnectInv N1 N2 (proj1_sig u)).
move=> H3.
elim.
move=> k H3.
exists (exist (Full_set {n : nat | n < N2}) k (Full_intro {n : nat | n < N2} k)).
apply sig_map.
apply sig_map.
simpl.
rewrite H3.
rewrite (proj2 (AddConnectNature N1 N2) k).
reflexivity.
apply (proj2 (AddConnectInvNature N1 N2) (proj1_sig u)).
elim (proj2_sig u).
move=> u0 H3 H4.
apply NNPP.
move=> H5.
apply H3.
elim (le_or_lt N1 (proj1_sig u0)).
move=> H6.
apply False_ind.
apply (H5 H6).
apply.
rewrite - (MySumF2BijectiveSame {n : nat | (n < N1)} (exist (Finite (Count N1)) (Full_set {n : nat | (n < N1)}) (CountFinite N1)) {n : nat | (n < N1 + N2)} (FiniteIntersection {n : nat | (n < N1 + N2)} (exist (Finite (Count (N1 + N2))) (Full_set {n : nat | (n < N1 + N2)}) (CountFinite (N1 + N2))) (fun m : {n : nat | (n < N1 + N2)} => (proj1_sig m < N1))) (FPCM f) (fun n : Count (N1 + N2) => Fmul f match AddConnectInv N1 N2 n with
  | inl y0 => A1 x y0
  | inr y0 => A2 x y0
end match AddConnectInv N1 N2 n with
  | inl x0 => B1 x0 y
  | inr x0 => B2 x0 y
end) (fun (u1 : {n : nat | (n < N1)}) => AddConnect N1 N2 (inl u1))).
apply (MySumF2Same {n : nat | (n < N1)} (exist (Finite (Count N1)) (Full_set {n : nat | (n < N1)}) (CountFinite N1)) (FPCM f)).
move=> u H1.
suff: (match AddConnectInv N1 N2 (AddConnect N1 N2 (inl u)) return Prop with
  | inl k => proj1_sig (AddConnect N1 N2 (inl u)) = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv N1 N2 (AddConnect N1 N2 (inl u))).
move=> k H2.
suff: (k = u).
move=> H3.
rewrite H3.
reflexivity.
apply sig_map.
rewrite - H2.
rewrite (proj1 (AddConnectNature N1 N2) u).
reflexivity.
move=> k.
elim.
apply (proj1 (AddConnectInvNature N1 N2) (AddConnect N1 N2 (inl u))).
rewrite - (proj1 (AddConnectNature N1 N2) u).
apply (proj2_sig u).
move=> u H1.
apply (Intersection_intro {n : nat | (n < N1 + N2)}).
unfold In.
rewrite - (proj1 (AddConnectNature N1 N2) u).
apply (proj2_sig u).
apply (Full_intro {n : nat | (n < N1 + N2)}).
move=> H1.
simpl.
apply InjSurjBij.
move=> u1 u2 H2.
apply sig_map.
apply (injective_inl {n : nat | n < N1} {n : nat | n < N2}).
apply (BijInj ({n : nat | n < N1} + {n : nat | n < N2}) {n : nat | n < N1 + N2} (AddConnect N1 N2)).
exists (AddConnectInv N1 N2).
apply (AddConnectInvRelation N1 N2).
suff: (AddConnect N1 N2 (inl (proj1_sig u1)) = proj1_sig (exist (Intersection {n : nat | n < N1 + N2} (fun m : {n : nat | n < N1 + N2} => proj1_sig m < N1) (Full_set {n : nat | n < N1 + N2})) (AddConnect N1 N2 (inl (proj1_sig u1))) (H1 (proj1_sig u1) (proj2_sig u1)))).
move=> H3.
rewrite H3.
rewrite H2.
reflexivity.
reflexivity.
move=> u.
suff: (match AddConnectInv N1 N2 (proj1_sig u) return Prop with
  | inl k => proj1_sig (proj1_sig u) = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv N1 N2 (proj1_sig u)).
move=> k H2.
exists (exist (Full_set {n : nat | n < N1}) k (Full_intro {n : nat | n < N1} k)).
apply sig_map.
apply sig_map.
simpl.
rewrite H2.
rewrite (proj1 (AddConnectNature N1 N2) k).
reflexivity.
move=> k.
elim.
apply (proj1 (AddConnectInvNature N1 N2) (proj1_sig u)).
elim (proj2_sig u).
move=> u0 H2 H3.
apply H2.
Qed.

Lemma MBlockHWWHSame : forall (f : Field) (M1 M2 N1 N2 : nat) (A : Matrix f M1 N1) (B : Matrix f M1 N2) (C : Matrix f M2 N1) (D : Matrix f M2 N2), MBlockH f M1 M2 (N1 + N2) (MBlockW f M1 N1 N2 A B) (MBlockW f M2 N1 N2 C D) = MBlockW f (M1 + M2) N1 N2 (MBlockH f M1 M2 N1 A C) (MBlockH f M1 M2 N2 B D).
Proof.
move=> f M1 M2 N1 N2 A B C D.
unfold MBlockH.
unfold MBlockW.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (AddConnectInv M1 M2 x).
move=> m.
reflexivity.
move=> m.
reflexivity.
Qed.

Lemma MBlockHVMult : forall (f : Field) (M1 M2 N : nat) (c : FT f) (A1 : Matrix f M1 N) (A2 : Matrix f M2 N), VMmult f (M1 + M2) N c (MBlockH f M1 M2 N A1 A2) = MBlockH f M1 M2 N (VMmult f M1 N c A1) (VMmult f M2 N c A2).
Proof.
move=> f M1 M2 N c A1 A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold VMmult.
unfold MBlockH.
elim (AddConnectInv M1 M2 x).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockWVMult : forall (f : Field) (M N1 N2 : nat) (c : FT f) (A1 : Matrix f M N1) (A2 : Matrix f M N2), VMmult f M (N1 + N2) c (MBlockW f M N1 N2 A1 A2) = MBlockW f M N1 N2 (VMmult f M N1 c A1) (VMmult f M N2 c A2).
Proof.
move=> f M N1 N2 c A1 A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold VMmult.
unfold MBlockW.
elim (AddConnectInv N1 N2 y).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockHTranspose : forall (f : Field) (M1 M2 N : nat) (A1 : Matrix f M1 N) (A2 : Matrix f M2 N), MTranspose f (M1 + M2) N (MBlockH f M1 M2 N A1 A2) = MBlockW f N M1 M2 (MTranspose f M1 N A1) (MTranspose f M2 N A2).
Proof.
move=> f M1 M2 N A1 A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
reflexivity.
Qed.

Lemma MBlockWTranspose : forall (f : Field) (M N1 N2 : nat) (A1 : Matrix f M N1) (A2 : Matrix f M N2), MTranspose f M (N1 + N2) (MBlockW f M N1 N2 A1 A2) = MBlockH f N1 N2 M (MTranspose f M N1 A1) (MTranspose f M N2 A2).
Proof.
move=> f M N1 N2 A1 A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
reflexivity.
Qed.

Definition ElementaryMatrixSwap (f : Field) (N : nat) (p q : {n : nat | n < N}) := (fun (x y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => match Nat.eq_dec (proj1_sig y) (proj1_sig q) with
    | left _ => FI f
    | right _ => FO f
  end
  | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
    | left _ => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
      | left _ => FI f
      | right _ => FO f
    end
    | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig y) with
      | left _ => FI f
      | right _ => FO f
    end
  end
end).

Definition ElementaryMatrixMultiply (f : Field) (N : nat) (p : {n : nat | n < N}) (c : FT f) := (fun (x y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig y) with
  | left _ => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
    | left _ => c
    | right _ => FI f
  end
  | right _ => FO f
end).

Definition ElementaryMatrixAdd (f : Field) (N : nat) (p q : {n : nat | n < N}) (c : FT f) := (fun (x y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig y) with
  | left _ => FI f
  | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig p), Nat.eq_dec (proj1_sig y) (proj1_sig q) with
    | left _, left _ => c
    | left _, right _ => FO f
    | right _, left _ => FO f
    | right _, right _ => FO f
  end
end).

Definition ReverseMatrix (f : Field) (N : nat) := fun (x y : {n : nat | n < N}) => MI f N x (CountReverse N y).

Inductive ElementaryMatrix (f : Field) (N : nat) : Ensemble (Matrix f N N) :=
  | ElementaryMatrixAdd_intro : forall (p q : {n : nat | n < N}) (c : FT f), proj1_sig p <> proj1_sig q -> c <> FO f -> ElementaryMatrix f N (ElementaryMatrixAdd f N p q c)
  | ElementaryMatrixMultiply_intro : forall (p : {n : nat | n < N}) (c : FT f), c <> FO f -> ElementaryMatrix f N (ElementaryMatrixMultiply f N p c)
  | ElementaryMatrixSwap_intro : forall (p q : {n : nat | n < N}), proj1_sig p <> proj1_sig q -> ElementaryMatrix f N (ElementaryMatrixSwap f N p q).

Definition ElementaryTransformable (f : Field) (N : nat) (A : Matrix f N N) := exists (AL : list (Matrix f N N)), (Forall (ElementaryMatrix f N) AL) /\ A = MyProdFL (MMM f N) AL.

Lemma ElementaryMatrixAddTrans : forall (f : Field) (N : nat) (p q : {n : nat | n < N}) (c : FT f), MTranspose f N N (ElementaryMatrixAdd f N p q c) = ElementaryMatrixAdd f N q p c.
Proof.
move=> f N p q c.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MTranspose.
unfold ElementaryMatrixAdd.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig x)).
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H2.
reflexivity.
move=> H2.
apply False_ind.
apply H2.
rewrite H1.
reflexivity.
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H2.
apply False_ind.
apply H1.
rewrite H2.
reflexivity.
move=> H2.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig p)).
move=> H3.
reflexivity.
move=> H3.
reflexivity.
Qed.

Lemma ElementaryMatrixMultiplyTrans : forall (f : Field) (N : nat) (p : {n : nat | n < N}) (c : FT f), MTranspose f N N (ElementaryMatrixMultiply f N p c) = ElementaryMatrixMultiply f N p c.
Proof.
move=> f N p c.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MTranspose.
unfold ElementaryMatrixMultiply.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig x)).
move=> H1.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig p)).
move=> H2.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H3.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
move=> H4.
reflexivity.
rewrite H3.
rewrite H2.
move=> H4.
apply False_ind.
apply H4.
reflexivity.
rewrite H1.
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> H2.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H3.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
rewrite H3.
move=> H4.
elim (H2 H4).
move=> H4.
reflexivity.
rewrite H1.
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H2.
apply False_ind.
apply H1.
rewrite H2.
reflexivity.
move=> H2.
reflexivity.
Qed.

Lemma ElementaryMatrixSwapTrans : forall (f : Field) (N : nat) (p q : {n : nat | n < N}), MTranspose f N N (ElementaryMatrixSwap f N p q) = ElementaryMatrixSwap f N p q.
Proof.
move=> f N p q.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MTranspose.
unfold ElementaryMatrixSwap.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig p)).
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig q)).
move=> H2.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
move=> H3.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig q)).
move=> H4.
reflexivity.
rewrite H1.
rewrite - H2.
move=> H4.
apply False_ind.
apply H4.
rewrite H3.
reflexivity.
move=> H3.
reflexivity.
move=> H2.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
move=> H3.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig q)).
rewrite H1.
move=> H4.
apply False_ind.
apply H2.
rewrite H3.
apply H4.
move=> H4.
reflexivity.
move=> H3.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
rewrite H1.
move=> H4.
elim (H3 H4).
move=> H4.
reflexivity.
move=> H1.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig q)).
move=> H2.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
move=> H3.
reflexivity.
move=> H3.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig q)).
move=> H4.
reflexivity.
move=> H4.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
rewrite H2.
move=> H5.
elim (H4 H5).
move=> H5.
reflexivity.
move=> H2.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig x)).
move=> H3.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
rewrite - H3.
move=> H4.
elim (H1 H4).
move=> H4.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig q)).
rewrite - H3.
move=> H5.
elim (H2 H5).
move=> H5.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H6.
reflexivity.
move=> H6.
apply False_ind.
apply H6.
rewrite H3.
reflexivity.
move=> H3.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
move=> H4.
reflexivity.
move=> H4.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig q)).
move=> H5.
reflexivity.
move=> H5.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H6.
apply False_ind.
apply H3.
rewrite H6.
reflexivity.
move=> H6.
reflexivity.
Qed.

Lemma ReverseMatrixTrans : forall (f : Field) (N : nat), MTranspose f N N (ReverseMatrix f N) = ReverseMatrix f N.
Proof.
move=> f N.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MTranspose.
unfold ReverseMatrix.
unfold MI.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (CountReverse N x))).
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (CountReverse N y))).
move=> H2.
reflexivity.
elim.
suff: (y = CountReverse N x).
move=> H2.
rewrite H2.
rewrite (CountReverseInvolutive N x).
reflexivity.
apply sig_map.
apply H1.
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (CountReverse N y))).
move=> H2.
elim H1.
suff: (x = CountReverse N y).
move=> H3.
rewrite H3.
rewrite (CountReverseInvolutive N y).
reflexivity.
apply sig_map.
apply H2.
move=> H2.
reflexivity.
Qed.

Lemma ElementaryTransformableConnect : forall (f : Field) (N : nat) (A B : Matrix f N N), ElementaryTransformable f N A -> ElementaryTransformable f N B -> ElementaryTransformable f N (Mmult f N N N A B).
Proof.
move=> f N A B H1 H2.
elim H1.
move=> AL H3.
elim H2.
move=> BL H4.
exists (app AL BL).
apply conj.
apply (Forall_app (fun (x : Matrix f N N) => ElementaryMatrix f N x) AL BL).
apply conj.
apply (proj1 H3).
apply (proj1 H4).
rewrite (MyProdFLApp (MMM f N) AL BL).
rewrite (proj2 H3).
rewrite (proj2 H4).
reflexivity.
Qed.

Lemma ElementaryTransformableTrans : forall (f : Field) (N : nat) (A : Matrix f N N), ElementaryTransformable f N A -> ElementaryTransformable f N (MTranspose f N N A).
Proof.
move=> f N A.
elim.
move=> AL H1.
exists (rev (map (MTranspose f N N) AL)).
apply conj.
suff: (Forall (fun x : Matrix f N N => ElementaryMatrix f N x) (map (MTranspose f N N) AL)).
move=> H2.
apply (Forall_rev H2).
apply (proj2 (Forall_forall (fun (x : Matrix f N N) => ElementaryMatrix f N x) (map (MTranspose f N N) AL))).
move=> B H2.
elim (proj1 (in_map_iff (MTranspose f N N) AL B)).
move=> BT H3.
rewrite - (proj1 H3).
elim (proj1 (Forall_forall (fun (x : Matrix f N N) => ElementaryMatrix f N x) AL) (proj1 H1) BT (proj2 H3)).
move=> p q c H4 H5.
suff: (proj1_sig q <> proj1_sig p).
move=> H6.
rewrite (ElementaryMatrixAddTrans f N p q c).
apply (ElementaryMatrixAdd_intro f N q p c H6 H5).
move=> H6.
apply H4.
rewrite H6.
reflexivity.
move=> p c H4.
rewrite (ElementaryMatrixMultiplyTrans f N p c).
apply (ElementaryMatrixMultiply_intro f N p c H4).
move=> p q H4.
rewrite (ElementaryMatrixSwapTrans f N p q).
apply (ElementaryMatrixSwap_intro f N p q H4).
apply H2.
rewrite (proj2 H1).
elim AL.
apply (MTransI f N).
move=> a l H2.
simpl.
rewrite (MyProdFLApp (MMM f N)).
rewrite (MTransMult f N N N).
rewrite H2.
simpl.
rewrite (Mmult_I_r f N N (MTranspose f N N a)).
reflexivity.
Qed.

Lemma ElementaryMatrixAddNatureL : forall (f : Field) (M N : nat) (A : Matrix f M N) (p q : {n : nat | n < M}) (c : FT f), proj1_sig p <> proj1_sig q -> Mmult f M M N (ElementaryMatrixAdd f M p q c) A = (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => Fadd f (A x y) (Fmul f c (A q y))
  | right _ => A x y
end).
Proof.
move=> f M N A p q c H1.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
unfold ElementaryMatrixAdd.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
move=> H2.
rewrite (MySumF2Included {n : nat | n < M} (FiniteSingleton {n : nat | n < M} x)).
rewrite MySumF2Singleton.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig x)).
move=> H3.
rewrite (MySumF2Included {n : nat | n < M} (FiniteSingleton {n : nat | n < M} q)).
rewrite MySumF2Singleton.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig q)).
move=> H4.
apply False_ind.
apply H1.
rewrite - H2.
apply H4.
move=> H4.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig q)).
move=> H5.
rewrite MySumF2O.
rewrite (Fmul_I_l f (A x y)).
rewrite (CM_O_r (FPCM f) (Fmul f c (A q y))).
reflexivity.
move=> u.
elim.
move=> u0 H6 H7.
suff: (In {n : nat | n < M} (Complement {n : nat | n < M} (proj1_sig (FiniteSingleton {n : nat | n < M} q))) u0).
elim H7.
move=> u1 H8 H9 H10.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig u1)).
move=> H11.
apply False_ind.
apply H8.
suff: (x = u1).
move=> H12.
rewrite H12.
apply (In_singleton {n : nat | n < M} u1).
apply sig_map.
apply H11.
move=> H11.
elim (Nat.eq_dec (proj1_sig u1) (proj1_sig q)).
move=> H12.
apply False_ind.
apply H10.
suff: (u1 = q).
move=> H13.
rewrite H13.
apply (In_singleton {n : nat | n < M} q).
apply sig_map.
apply H12.
move=> H12.
apply (Fmul_O_l f (A u1 y)).
apply H6.
move=> H5.
apply False_ind.
apply H5.
reflexivity.
move=> m H4.
apply (Intersection_intro {n : nat | n < M}).
move=> H5.
apply H1.
rewrite - H2.
suff: (q = m).
move=> H6.
rewrite H6.
elim H5.
reflexivity.
elim H4.
reflexivity.
apply (Full_intro {n : nat | n < M} m).
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> m H3.
apply (Full_intro {n : nat | n < M} m).
move=> H2.
rewrite (MySumF2Included {n : nat | n < M} (FiniteSingleton {n : nat | n < M} x)).
rewrite MySumF2Singleton.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig x)).
move=> H3.
rewrite MySumF2O.
rewrite (Fmul_I_l f (A x y)).
apply (Fadd_O_r f (A x y)).
move=> u.
elim.
move=> u0 H4 H5.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig u0)).
move=> H6.
apply False_ind.
apply H4.
suff: (x = u0).
move=> H7.
rewrite H7.
apply (In_singleton {n : nat | n < M} u0).
apply sig_map.
apply H6.
move=> H6.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig q)).
move=> H7.
apply (Fmul_O_l f (A u0 y)).
move=> H7.
apply (Fmul_O_l f (A u0 y)).
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> u H3.
apply (Full_intro {n : nat | n < M} u).
Qed.

Lemma ElementaryMatrixAddNatureR : forall (f : Field) (M N : nat) (A : Matrix f M N) (p q : {n : nat | n < N}) (c : FT f), proj1_sig p <> proj1_sig q -> Mmult f M N N A (ElementaryMatrixAdd f N p q c) = (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig y) (proj1_sig q) with
  | left _ => Fadd f (A x y) (Fmul f c (A x p))
  | right _ => A x y
end).
Proof.
move=> f M N A p q c H1.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
unfold ElementaryMatrixAdd.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig q)).
move=> H2.
rewrite (MySumF2Included {n : nat | n < N} (FiniteSingleton {n : nat | n < N} y)).
rewrite MySumF2Singleton.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig y)).
move=> H3.
rewrite (MySumF2Included {n : nat | n < N} (FiniteSingleton {n : nat | n < N} p)).
rewrite MySumF2Singleton.
elim (Nat.eq_dec (proj1_sig p) (proj1_sig y)).
move=> H4.
apply False_ind.
apply H1.
rewrite - H2.
apply H4.
move=> H4.
elim (Nat.eq_dec (proj1_sig p) (proj1_sig p)).
move=> H5.
rewrite MySumF2O.
rewrite (Fmul_I_r f (A x y)).
rewrite (CM_O_r (FPCM f) (Fmul f (A x p) c)).
rewrite (Fmul_comm f (A x p) c).
reflexivity.
move=> u.
elim.
move=> u0 H6 H7.
suff: (In {n : nat | n < N} (Complement {n : nat | n < N} (proj1_sig (FiniteSingleton {n : nat | n < N} p))) u0).
elim H7.
move=> u1 H8 H9 H10.
elim (Nat.eq_dec (proj1_sig u1) (proj1_sig y)).
move=> H11.
apply False_ind.
apply H8.
suff: (u1 = y).
move=> H12.
rewrite H12.
apply (In_singleton {n : nat | n < N} y).
apply sig_map.
apply H11.
move=> H11.
elim (Nat.eq_dec (proj1_sig u1) (proj1_sig p)).
move=> H12.
apply False_ind.
apply H10.
suff: (u1 = p).
move=> H13.
rewrite H13.
apply (In_singleton {n : nat | n < N} p).
apply sig_map.
apply H12.
move=> H12.
apply (Fmul_O_r f (A x u1)).
apply H6.
move=> H5.
apply False_ind.
apply H5.
reflexivity.
move=> m H4.
apply (Intersection_intro {n : nat | n < N}).
move=> H5.
apply H1.
rewrite - H2.
suff: (p = m).
move=> H6.
rewrite H6.
elim H5.
reflexivity.
elim H4.
reflexivity.
apply (Full_intro {n : nat | n < N} m).
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> m H3.
apply (Full_intro {n : nat | n < N} m).
move=> H2.
rewrite (MySumF2Included {n : nat | n < N} (FiniteSingleton {n : nat | n < N} y)).
rewrite MySumF2Singleton.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig y)).
move=> H3.
rewrite MySumF2O.
rewrite (Fmul_I_r f (A x y)).
apply (Fadd_O_r f (A x y)).
move=> u.
elim.
move=> u0 H4 H5.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig y)).
move=> H6.
apply False_ind.
apply H4.
suff: (u0 = y).
move=> H7.
rewrite H7.
apply (In_singleton {n : nat | n < N} y).
apply sig_map.
apply H6.
move=> H6.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig p)).
move=> H7.
apply (Fmul_O_r f (A x u0)).
move=> H7.
apply (Fmul_O_r f (A x u0)).
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> u H3.
apply (Full_intro {n : nat | n < N} u).
Qed.

Lemma ElementaryMatrixMultiplyNatureL : forall (f : Field) (M N : nat) (A : Matrix f M N) (p : {n : nat | n < M}) (c : FT f), Mmult f M M N (ElementaryMatrixMultiply f M p c) A = (fun (x : {n : nat | (n < M)}) (y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end).
Proof.
move=> f M N A p c.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
unfold ElementaryMatrixMultiply.
rewrite (MySumF2Included {n : nat | n < M} (FiniteSingleton {n : nat | n < M} x)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (CM_O_r (FPCM f)).
elim (Nat.eq_dec (proj1_sig x) (proj1_sig x)).
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
move=> H2.
reflexivity.
move=> H2.
apply (Fmul_I_l f (A x y)).
move=> H1.
apply False_ind.
apply H1.
reflexivity.
move=> u.
elim.
move=> u0 H1 H2.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig u0)).
move=> H3.
apply False_ind.
apply H1.
suff: (x = u0).
move=> H4.
rewrite H4.
apply (In_singleton {n : nat | n < M} u0).
apply sig_map.
apply H3.
move=> H3.
apply (Fmul_O_l f (A u0 y)).
move=> m H1.
apply (Full_intro {n : nat | n < M} m).
Qed.

Lemma ElementaryMatrixMultiplyNatureR : forall (f : Field) (M N : nat) (A : Matrix f M N) (p : {n : nat | n < N}) (c : FT f), Mmult f M N N A (ElementaryMatrixMultiply f N p c) = (fun (x : {n : nat | (n < M)}) (y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end).
Proof.
move=> f M N A p c.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
unfold ElementaryMatrixMultiply.
rewrite (MySumF2Included {n : nat | n < N} (FiniteSingleton {n : nat | n < N} y)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (CM_O_r (FPCM f)).
elim (Nat.eq_dec (proj1_sig y) (proj1_sig y)).
move=> H1.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig p)).
move=> H2.
apply (Fmul_comm f (A x y) c).
move=> H2.
apply (Fmul_I_r f (A x y)).
move=> H1.
apply False_ind.
apply H1.
reflexivity.
move=> u.
elim.
move=> u0 H1 H2.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig y)).
move=> H3.
apply False_ind.
apply H1.
suff: (u0 = y).
move=> H4.
rewrite H4.
apply (In_singleton {n : nat | n < N} y).
apply sig_map.
apply H3.
move=> H3.
apply (Fmul_O_r f (A x u0)).
move=> m H1.
apply (Full_intro {n : nat | n < N} m).
Qed.

Lemma ElementaryMatrixSwapNatureL : forall (f : Field) (M N : nat) (A : Matrix f M N) (p q : {n : nat | n < M}), Mmult f M M N (ElementaryMatrixSwap f M p q) A = (fun (x : {n : nat | (n < M)}) (y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => A q y
  | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
    | left _ => A p y
    | right _ => A x y
  end
end).
Proof.
move=> f M N A p q.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
unfold ElementaryMatrixSwap.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
move=> H1.
rewrite (MySumF2Included {n : nat | n < M} (FiniteSingleton {n : nat | n < M} q)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (CM_O_r (FPCM f)).
elim (Nat.eq_dec (proj1_sig q) (proj1_sig q)).
move=> H2.
apply (Fmul_I_l f (A q y)).
move=> H2.
apply False_ind.
apply H2.
reflexivity.
move=> u.
elim.
move=> u0 H2 H3.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig q)).
move=> H4.
apply False_ind.
apply H2.
suff: (u0 = q).
move=> H5.
rewrite H5.
apply (In_singleton {n : nat | n < M} q).
apply sig_map.
apply H4.
move=> H4.
apply (Fmul_O_l f (A u0 y)).
move=> m H2.
apply (Full_intro {n : nat | n < M} m).
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig q)).
move=> H2.
rewrite (MySumF2Included {n : nat | n < M} (FiniteSingleton {n : nat | n < M} p)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (CM_O_r (FPCM f)).
elim (Nat.eq_dec (proj1_sig p) (proj1_sig p)).
move=> H3.
apply (Fmul_I_l f (A p y)).
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> u.
elim.
move=> u0 H3 H4.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig p)).
move=> H5.
apply False_ind.
apply H3.
suff: (u0 = p).
move=> H6.
rewrite H6.
apply (In_singleton {n : nat | n < M} p).
apply sig_map.
apply H5.
move=> H5.
apply (Fmul_O_l f (A u0 y)).
move=> m H3.
apply (Full_intro {n : nat | n < M} m).
move=> H2.
rewrite (MySumF2Included {n : nat | n < M} (FiniteSingleton {n : nat | n < M} x)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (CM_O_r (FPCM f)).
elim (Nat.eq_dec (proj1_sig x) (proj1_sig x)).
move=> H3.
apply (Fmul_I_l f (A x y)).
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> u.
elim.
move=> u0 H3 H4.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig u0)).
move=> H5.
apply False_ind.
apply H3.
suff: (x = u0).
move=> H6.
rewrite H6.
apply (In_singleton {n : nat | n < M} u0).
apply sig_map.
apply H5.
move=> H5.
apply (Fmul_O_l f (A u0 y)).
move=> m H3.
apply (Full_intro {n : nat | n < M} m).
Qed.

Lemma ElementaryMatrixSwapNatureR : forall (f : Field) (M N : nat) (A : Matrix f M N) (p q : {n : nat | n < N}), Mmult f M N N A (ElementaryMatrixSwap f N p q) = (fun (x : {n : nat | (n < M)}) (y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => A x q
  | right _ => match Nat.eq_dec (proj1_sig y) (proj1_sig q) with
    | left _ => A x p
    | right _ => A x y
  end
end).
Proof.
move=> f M N A p q.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
unfold ElementaryMatrixSwap.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig p)).
move=> H1.
rewrite (MySumF2Included {n : nat | n < N} (FiniteSingleton {n : nat | n < N} q)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (CM_O_r (FPCM f)).
elim (Nat.eq_dec (proj1_sig q) (proj1_sig q)).
move=> H2.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig p)).
move=> H3.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig q)).
move=> H4.
apply (Fmul_I_r f (A x q)).
move=> H4.
apply False_ind.
apply H4.
rewrite H3.
apply H1.
move=> H3.
apply (Fmul_I_r f (A x q)).
move=> H2.
apply False_ind.
apply H2.
reflexivity.
move=> u.
elim.
move=> u0 H2 H3.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig q)).
move=> H4.
apply False_ind.
apply H2.
suff: (u0 = q).
move=> H5.
rewrite H5.
apply (In_singleton {n : nat | n < N} q).
apply sig_map.
apply H4.
move=> H4.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig p)).
move=> H5.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig q)).
move=> H6.
apply False_ind.
apply H4.
rewrite - H6.
rewrite H1.
apply H5.
move=> H6.
apply (Fmul_O_r f (A x u0)).
move=> H5.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig y)).
move=> H6.
apply False_ind.
apply H5.
rewrite - H1.
apply H6.
move=> H6.
apply (Fmul_O_r f (A x u0)).
move=> m H2.
apply (Full_intro {n : nat | n < N} m).
move=> H1.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig q)).
move=> H2.
rewrite (MySumF2Included {n : nat | n < N} (FiniteSingleton {n : nat | n < N} p)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (CM_O_r (FPCM f)).
elim (Nat.eq_dec (proj1_sig p) (proj1_sig p)).
move=> H3.
apply (Fmul_I_r f (A x p)).
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> u.
elim.
move=> u0 H3 H4.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig p)).
move=> H5.
apply False_ind.
apply H3.
suff: (u0 = p).
move=> H6.
rewrite H6.
apply (In_singleton {n : nat | n < N} p).
apply sig_map.
apply H5.
move=> H5.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig q)).
move=> H6.
apply (Fmul_O_r f (A x u0)).
move=> H6.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig y)).
move=> H7.
apply False_ind.
apply H6.
rewrite H7.
apply H2.
move=> H7.
apply (Fmul_O_r f (A x u0)).
move=> m H3.
apply (Full_intro {n : nat | n < N} m).
move=> H2.
rewrite (MySumF2Included {n : nat | n < N} (FiniteSingleton {n : nat | n < N} y)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (CM_O_r (FPCM f)).
elim (Nat.eq_dec (proj1_sig y) (proj1_sig y)).
move=> H3.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig p)).
move=> H4.
elim (H1 H4).
move=> H4.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig q)).
move=> H5.
elim (H2 H5).
move=> H5.
apply (Fmul_I_r f (A x y)).
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> u.
elim.
move=> u0 H3 H4.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig y)).
move=> H5.
apply False_ind.
apply H3.
suff: (u0 = y).
move=> H6.
rewrite H6.
apply (In_singleton {n : nat | n < N} y).
apply sig_map.
apply H5.
move=> H5.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig p)).
move=> H6.
apply (Fmul_O_r f (A x u0)).
move=> H6.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig q)).
move=> H7.
apply (Fmul_O_r f (A x u0)).
move=> H7.
apply (Fmul_O_r f (A x u0)).
move=> m H3.
apply (Full_intro {n : nat | n < N} m).
Qed.

Lemma ReverseMatrixNatureL : forall (f : Field) (M N : nat) (A : Matrix f M N), Mmult f M M N (ReverseMatrix f M) A = (fun (x : {n : nat | n < M}) => A (CountReverse M x)).
Proof.
move=> f M N A.
unfold Mmult.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite (MySumF2Included {n : nat | n < M} (FiniteSingleton {n : nat | n < M} (CountReverse M x))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
unfold ReverseMatrix.
rewrite (CountReverseInvolutive M x).
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig x)).
move=> H1.
apply (Fmul_I_l f (A (CountReverse M x) y)).
elim.
reflexivity.
move=> u.
elim.
move=> u0 H2 H3.
unfold ReverseMatrix.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (CountReverse M u0))).
move=> H4.
elim H2.
suff: (u0 = CountReverse M x).
move=> H5.
rewrite H5.
apply (In_singleton {n : nat | n < M}).
suff: (x = CountReverse M u0).
move=> H5.
rewrite H5.
rewrite (CountReverseInvolutive M u0).
reflexivity.
apply sig_map.
apply H4.
move=> H4.
apply (Fmul_O_l f (A u0 y)).
move=> u H2.
apply (Full_intro {n : nat | n < M} u).
Qed.

Lemma ReverseMatrixNatureR : forall (f : Field) (M N : nat) (A : Matrix f M N), Mmult f M N N A (ReverseMatrix f N) = (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => A x (CountReverse N y)).
Proof.
move=> f M N A.
unfold Mmult.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite (MySumF2Included {n : nat | n < N} (FiniteSingleton {n : nat | n < N} (CountReverse N y))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
unfold ReverseMatrix.
unfold MI.
elim (Nat.eq_dec (proj1_sig (CountReverse N y)) (proj1_sig (CountReverse N y))).
move=> H1.
apply (Fmul_I_r f).
elim.
reflexivity.
move=> u.
elim.
move=> u0 H1 H2.
unfold ReverseMatrix.
unfold MI.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig (CountReverse N y))).
move=> H3.
elim H1.
suff: (u0 = CountReverse N y).
move=> H4.
rewrite H4.
apply (In_singleton {n : nat | n < N}).
apply sig_map.
apply H3.
move=> H4.
apply (Fmul_O_r f (A x u0)).
move=> u H2.
apply (Full_intro {n : nat | n < N} u).
Qed.

Definition Determinant (f : Field) (N : nat) (A : Matrix f N N) := MySumF2 (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (FPCM f) (fun (P : Permutation N) => Fmul f (match PermutationParity N P with
  | OFF => (FI f)
  | ON => Fopp f (FI f)
end) (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat| (n < N) }) (CountFinite N)) (FMCM f) (fun (k : {n : nat | (n < N)}) => A k (proj1_sig P k)))).

Lemma DeterminantI : forall (f : Field) (N : nat), Determinant f N (MI f N) = FI f.
Proof.
move=> f N.
unfold Determinant.
rewrite (MySumF2Included (Permutation N) (FiniteSingleton (Permutation N) (PermutationID N)) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (FPCM f)).
rewrite MySumF2Singleton.
rewrite (PermutationIDParity N).
rewrite (MySumF2O (Permutation N)).
rewrite (CM_O_r (FPCM f)).
rewrite (Fmul_I_l f).
apply MySumF2Induction.
apply conj.
reflexivity.
move=> cm u H1 H2.
rewrite H2.
unfold PermutationID.
simpl.
unfold MI.
elim (Nat.eq_dec (proj1_sig u) (proj1_sig u)).
move=> H3.
apply (Fmul_I_l f (FI f)).
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> u H1.
suff: (exists (k : {n : nat | (n < N)}), k <> proj1_sig u k).
elim.
move=> k H2.
rewrite (MySumF2Included {n : nat | (n < N)} (FiniteSingleton {n : nat | (n < N)} k) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f)).
rewrite MySumF2Singleton.
unfold MI.
elim (Nat.eq_dec (proj1_sig k) (proj1_sig (proj1_sig u k))).
move=> H3.
apply False_ind.
apply H2.
apply sig_map.
apply H3.
move=> H3.
simpl.
rewrite (Fmul_O_l f).
apply (Fmul_O_r f).
move=> l H3.
apply (Full_intro {n : nat | (n < N)} l).
elim H1.
move=> p H2 H3.
apply NNPP.
move=> H4.
apply H2.
suff: (p = PermutationID N).
move=> H5.
rewrite H5.
apply In_singleton.
apply sig_map.
apply functional_extensionality.
move=> l.
apply NNPP.
move=> H5.
apply H4.
exists l.
move=> H6.
apply H5.
rewrite - H6.
reflexivity.
move=> p H1.
apply (Full_intro (Permutation N) p).
Qed.

Lemma DeterminantO : forall (f : Field) (N : nat), N <> O -> Determinant f N (MO f N N) = FO f.
Proof.
move=> f N H1.
unfold Determinant.
apply (MySumF2O (Permutation N)).
move=> u H2.
suff: ((N > O)).
move=> H3.
rewrite (MySumF2Included {n : nat | (n < N)} (FiniteSingleton {n : nat | (n < N)} (exist (fun (k : nat) => (k < N)) O H3))).
rewrite MySumF2Singleton.
unfold MO.
simpl.
rewrite (Fmul_O_l f).
apply (Fmul_O_r f).
move=> k H4.
apply (Full_intro {n : nat | (n < N)} k).
elim (le_lt_or_eq O N (le_0_n N)).
apply.
move=> H3.
apply False_ind.
apply H1.
rewrite H3.
reflexivity.
Qed.

Lemma DeterminantTrans : forall (f : Field) (N : nat) (A : Matrix f N N), Determinant f N (MTranspose f N N A) = Determinant f N A.
Proof.
move=> f N A.
unfold Determinant.
suff: ((exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) = FiniteIm (Permutation N) (Permutation N) (PermutationInv N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))).
move=> H1.
rewrite {1} H1.
rewrite - (MySumF2BijectiveSame2 (Permutation N) (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))).
unfold Basics.compose.
suff: ((fun P : Permutation N => Fmul f match PermutationParity N P with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => A k (proj1_sig P k)))) = (fun x : Permutation N => Fmul f match PermutationParity N (PermutationInv N x) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => MTranspose f N N A k (proj1_sig (PermutationInv N x) k))))).
move=> H2.
rewrite H2.
reflexivity.
apply functional_extensionality.
move=> k.
unfold MTranspose.
rewrite (PermutationInvParity N k).
suff: ((exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) = FiniteIm {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig (PermutationInv N k)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))).
move=> H2.
rewrite {1} H2.
rewrite - (MySumF2BijectiveSame2 {n : nat | (n < N)} {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (proj1_sig (PermutationInv N k))).
unfold Basics.compose.
suff: ((fun (l : {n : nat | (n < N)}) => A (proj1_sig (PermutationInv N k) l) (proj1_sig k (proj1_sig (PermutationInv N k) l))) = (fun (l : {n : nat | (n < N)}) => A (proj1_sig (PermutationInv N k) l) l)).
move=> H3.
rewrite H3.
reflexivity.
apply functional_extensionality.
move=> l.
unfold PermutationInv at 2.
simpl.
rewrite (proj2 (proj2_sig (BijectiveInvExist {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig k) (proj2_sig k))) l).
reflexivity.
move=> u1 u2 H3 H4.
apply (BijInj {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig (PermutationInv N k)) (proj2_sig (PermutationInv N k))).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> m H2.
apply (Im_intro {n : nat | (n < N)} {n : nat | (n < N)} (Full_set {n : nat | (n < N)}) (proj1_sig (PermutationInv N k)) (proj1_sig k m)).
apply (Full_intro {n : nat | (n < N)} (proj1_sig k m)).
unfold PermutationInv.
simpl.
rewrite (proj1 (proj2_sig (BijectiveInvExist {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig k) (proj2_sig k))) m).
reflexivity.
move=> m H2.
apply (Full_intro {n : nat | (n < N)} m).
unfold PermutationInv.
move=> u1 u2 H2 H3 H4.
apply sig_map.
apply functional_extensionality.
move=> l.
apply (BijInj {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig (BijectiveInvExist {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig u1) (proj2_sig u1)))).
apply (PermutationInvSub N u1).
rewrite (proj1 (proj2_sig (BijectiveInvExist {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig u1) (proj2_sig u1))) l).
suff: (proj1_sig (BijectiveInvExist {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig u1) (proj2_sig u1)) = proj1_sig (exist (fun f : {n : nat | (n < N)} -> {n : nat | (n < N)} => Bijective f) (proj1_sig (BijectiveInvExist {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig u1) (proj2_sig u1))) (PermutationInvSub N u1))).
move=> H5.
rewrite H5.
rewrite H4.
simpl.
rewrite (proj1 (proj2_sig (BijectiveInvExist {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig u2) (proj2_sig u2))) l).
reflexivity.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> p H1.
apply (Im_intro (Permutation N) (Permutation N) (Full_set (Permutation N)) (PermutationInv N) (PermutationInv N p)).
apply (Full_intro (Permutation N) (PermutationInv N p)).
apply sig_map.
apply (InvUnique {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig (PermutationInv N p))).
apply conj.
apply (proj2 (proj2_sig (BijectiveInvExist {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig p) (proj2_sig p)))).
apply (proj1 (proj2_sig (BijectiveInvExist {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig p) (proj2_sig p)))).
apply (proj2_sig (BijectiveInvExist {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig (exist (fun f0 : {n : nat | (n < N)} -> {n : nat | (n < N)} => Bijective f0) (proj1_sig (BijectiveInvExist {n : nat | (n < N)} {n : nat | (n < N)} (proj1_sig p) (proj2_sig p))) (PermutationInvSub N p))) (proj2_sig (PermutationInv N p)))).
move=> k H1.
apply (Full_intro (Permutation N) k).
Qed.

Lemma DeterminantMultiLinearityHPlus : forall (f : Field) (N : nat) (A : Matrix f N N) (p : {n : nat | (n < N)}) (b : {n : nat | (n < N)} -> FT f), Determinant f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => Fadd f (A x y) (b y)
  | right _ => A x y
end) = Fadd f (Determinant f N A) (Determinant f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => (b y)
  | right _ => A x y
end)).
Proof.
move=> f N A p b.
unfold Determinant.
apply (MySumF2Distr (Permutation N) (FPCM f)).
move=> u H1.
simpl.
suff: ((MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => Fadd f (A k (proj1_sig u k)) (b (proj1_sig u k))
  | right _ => A k (proj1_sig u k)
end)) = Fadd f (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => A k (proj1_sig u k))) (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => b (proj1_sig u k)
  | right _ => A k (proj1_sig u k)
end))).
move=> H2.
rewrite H2.
apply (Fmul_add_distr_l f).
rewrite (MySumF2Included {n : nat | (n < N)} (FiniteSingleton {n : nat | (n < N)} p) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))).
rewrite (MySumF2Included {n : nat | (n < N)} (FiniteSingleton {n : nat | (n < N)} p) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))).
rewrite (MySumF2Included {n : nat | (n < N)} (FiniteSingleton {n : nat | (n < N)} p) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))).
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
elim (Nat.eq_dec (proj1_sig p) (proj1_sig p)).
move=> H2.
simpl.
suff: ((MySumF2 {n : nat | (n < N)} (FiniteIntersection {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (Complement {n : nat | (n < N)} (Singleton {n : nat | (n < N)} p))) (FMCM f) (fun (k : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => Fadd f (A k (proj1_sig u k)) (b (proj1_sig u k))
  | right _ => A k (proj1_sig u k)
end)) = (MySumF2 {n : nat | (n < N)} (FiniteIntersection {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (Complement {n : nat | (n < N)} (Singleton {n : nat | (n < N)} p))) (FMCM f) (fun (k : {n : nat | (n < N)}) => A k (proj1_sig u k)))).
move=> H3.
rewrite H3.
suff: ((MySumF2 {n : nat | (n < N)} (FiniteIntersection {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (Complement {n : nat | (n < N)} (Singleton {n : nat | (n < N)} p))) (FMCM f) (fun (k : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => b (proj1_sig u k)
  | right _ => A k (proj1_sig u k)
end)) = (MySumF2 {n : nat | (n < N)} (FiniteIntersection {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (Complement {n : nat | (n < N)} (Singleton {n : nat | (n < N)} p))) (FMCM f) (fun (k : {n : nat | (n < N)}) => A k (proj1_sig u k)))).
move=> H4.
rewrite H4.
apply (Fmul_add_distr_r f).
apply MySumF2Same.
move=> u0 H4.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig p)).
elim H4.
move=> u1 H5 H6 H7.
apply False_ind.
apply H5.
suff: (u1 = p).
move=> H8.
rewrite H8.
apply In_singleton.
apply sig_map.
apply H7.
move=> H5.
reflexivity.
apply MySumF2Same.
move=> u0 H3.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig p)).
elim H3.
move=> u1 H4 H5 H6.
apply False_ind.
apply H4.
suff: (u1 = p).
move=> H7.
rewrite H7.
apply In_singleton.
apply sig_map.
apply H6.
move=> H4.
reflexivity.
move=> H2.
apply False_ind.
apply H2.
reflexivity.
move=> k H2.
apply (Full_intro {n : nat | (n < N)} k).
move=> k H2.
apply (Full_intro {n : nat | (n < N)} k).
move=> k H2.
apply (Full_intro {n : nat | (n < N)} k).
Qed.

Lemma DeterminantMultiLinearityWPlus : forall (f : Field) (N : nat) (A : Matrix f N N) (p : {n : nat | (n < N)}) (b : {n : nat | (n < N)} -> FT f), Determinant f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => Fadd f (A x y) (b x)
  | right _ => A x y
end) = Fadd f (Determinant f N A) (Determinant f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => b x
  | right _ => A x y
end)).
Proof.
move=> f N A p b.
rewrite - (DeterminantTrans f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => Fadd f (A x y) (b x)
  | right _ => A x y
end)).
rewrite - (DeterminantTrans f N A).
rewrite - (DeterminantTrans f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => b x
  | right _ => A x y
end)).
apply (DeterminantMultiLinearityHPlus f N (MTranspose f N N A) p b).
Qed.

Lemma DeterminantMultiLinearityHMult : forall (f : Field) (N : nat) (A : Matrix f N N) (p : {n : nat | (n < N)}) (c : FT f), Determinant f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end) = Fmul f c (Determinant f N A).
Proof.
move=> f N A p c.
unfold Determinant.
apply (FiniteSetInduction (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))).
suff: (forall (b : Permutation N), (Fmul f match PermutationParity N b with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => Fmul f c (A k (proj1_sig b k))
  | right _ => A k (proj1_sig b k)
end))) = Fmul f c (Fmul f match PermutationParity N b with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => A k (proj1_sig b k))))).
move=> H1.
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (Fmul_O_r f).
reflexivity.
move=> B b H2 H3 H4 H5.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H5.
rewrite H1.
rewrite (Fmul_add_distr_l f).
reflexivity.
apply H4.
apply H4.
move=> b.
rewrite (MySumF2Included {n : nat | (n < N)} (FiniteSingleton {n : nat | (n < N)} p) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))).
rewrite (MySumF2Included {n : nat | (n < N)} (FiniteSingleton {n : nat | (n < N)} p) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))).
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
elim (Nat.eq_dec (proj1_sig p) (proj1_sig p)).
move=> H1.
simpl.
rewrite (Fmul_assoc f c (A p (proj1_sig b p))).
rewrite - (Fmul_assoc f (match PermutationParity N b with
  | ON => Fopp f (FI f)
  | OFF => FI f
end) c).
rewrite - (Fmul_assoc f c (match PermutationParity N b with
  | ON => Fopp f (FI f)
  | OFF => FI f
end)).
rewrite (Fmul_comm f c (match PermutationParity N b with
  | ON => Fopp f (FI f)
  | OFF => FI f
end)).
rewrite (MySumF2Same {n : nat | (n < N)} (FiniteIntersection {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (Complement {n : nat | (n < N)} (Singleton {n : nat | (n < N)} p))) (FMCM f) (fun (k : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => Fmul f c (A k (proj1_sig b k))
  | right _ => A k (proj1_sig b k)
end) (fun (k : {n : nat | (n < N)}) => A k (proj1_sig b k))).
reflexivity.
move=> u H2.
elim (Nat.eq_dec (proj1_sig u) (proj1_sig p)).
elim H2.
move=> u0 H3 H4 H5.
apply False_ind.
apply H3.
suff: (u0 = p).
move=> H6.
rewrite H6.
apply In_singleton.
apply sig_map.
apply H5.
move=> H3.
reflexivity.
move=> H1.
apply False_ind.
apply H1.
reflexivity.
move=> k H1.
apply (Full_intro {n : nat | (n < N)} k).
move=> k H1.
apply (Full_intro {n : nat | (n < N)} k).
Qed.

Lemma DeterminantMultiLinearityWMult : forall (f : Field) (N : nat) (A : Matrix f N N) (p : {n : nat | (n < N)}) (c : FT f), Determinant f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end) = Fmul f c (Determinant f N A).
Proof.
move=> f N A p c.
rewrite - (DeterminantTrans f N (fun x y : {n : nat | (n < N)} => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end)).
rewrite - (DeterminantTrans f N A).
apply (DeterminantMultiLinearityHMult f N (MTranspose f N N A) p c).
Qed.

Lemma DeterminantSwapH : forall (f : Field) (N : nat) (A : Matrix f N N) (p q : {n : nat | (n < N)}), proj1_sig p <> proj1_sig q -> Determinant f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => A q y
  | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
    | left _ => A p y
    | right _ => A x y
  end
end) = Fopp f (Determinant f N A).
Proof.
move=> f N A p q H1.
unfold Determinant.
suff: ((exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) = FiniteIm (Permutation N) (Permutation N) (fun (r : Permutation N) => PermutationCompose N r (PermutationSwap N p q)) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))).
move=> H2.
rewrite {2} H2.
rewrite - (MySumF2BijectiveSame2 (Permutation N) (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))).
unfold Basics.compose.
apply (FiniteSetInduction (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (Fopp_O f).
reflexivity.
move=> B b H3 H4 H5 H6.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H6.
suff: ((Fmul f match PermutationParity N b with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => A q (proj1_sig b k)
  | right _ => match Nat.eq_dec (proj1_sig k) (proj1_sig q) with
    | left _ => A p (proj1_sig b k)
    | right _ => A k (proj1_sig b k)
  end
end))) = Fopp f (Fmul f match PermutationParity N (PermutationCompose N b (PermutationSwap N p q)) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => A k (proj1_sig (PermutationCompose N b (PermutationSwap N p q)) k))))).
move=> H7.
rewrite H7.
rewrite (Fopp_add_distr f).
reflexivity.
suff: ((MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => A q (proj1_sig b k)
  | right _ => match Nat.eq_dec (proj1_sig k) (proj1_sig q) with
    | left _ => A p (proj1_sig b k)
    | right _ => A k (proj1_sig b k)
  end
end)) = (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => A k (proj1_sig (PermutationCompose N b (PermutationSwap N p q)) k)))).
move=> H7.
rewrite H7.
rewrite (PermutationComposeParity N b (PermutationSwap N p q)).
rewrite (PermutationSwapParity N p q).
elim (PermutationParity N b).
simpl.
apply (Fopp_mul_distr_l_reverse f).
simpl.
rewrite (Fopp_mul_distr_l f).
rewrite (Fopp_involutive f (FI f)).
reflexivity.
move=> H8.
apply H1.
rewrite H8.
reflexivity.
unfold PermutationCompose.
unfold PermutationSwap.
simpl.
unfold Basics.compose.
rewrite (MySumF2Included {n : nat | (n < N)} (FiniteUnion {n : nat | (n < N)} (FiniteSingleton {n : nat | (n < N)} p) (FiniteSingleton {n : nat | (n < N)} q)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f)).
rewrite (MySumF2Included {n : nat | (n < N)} (FiniteUnion {n : nat | (n < N)} (FiniteSingleton {n : nat | (n < N)} p) (FiniteSingleton {n : nat | (n < N)} q)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f)).
rewrite (MySumF2Same {n : nat | (n < N)} (FiniteIntersection {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (Complement {n : nat | (n < N)} (proj1_sig (FiniteUnion {n : nat | (n < N)} (FiniteSingleton {n : nat | (n < N)} p) (FiniteSingleton {n : nat | (n < N)} q))))) (FMCM f) (fun k : {n : nat | (n < N)} => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => A q (proj1_sig b k)
  | right _ => match Nat.eq_dec (proj1_sig k) (proj1_sig q) with
    | left _ => A p (proj1_sig b k)
    | right _ => A k (proj1_sig b k)
  end
end) (fun k : {n : nat | (n < N)} => A k (proj1_sig b (match excluded_middle_informative (k = p) with
  | left _ => q
  | right _ => match excluded_middle_informative (k = q) with
    | left _ => p
    | right _ => k
  end
end)))).
apply (Fmul_eq_compat_r f).
rewrite MySumF2Union.
rewrite MySumF2Union.
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
elim (Nat.eq_dec (proj1_sig p) (proj1_sig p)).
elim (excluded_middle_informative (p = p)).
elim (Nat.eq_dec (proj1_sig q) (proj1_sig p)).
move=> H7.
apply False_ind.
apply H1.
rewrite H7.
reflexivity.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig q)).
elim (excluded_middle_informative (q = p)).
move=> H7.
apply False_ind.
apply H1.
rewrite H7.
reflexivity.
elim (excluded_middle_informative (q = q)).
move=> H7 H8 H9 H10 H11 H12.
apply (Fmul_comm f).
move=> H7.
apply False_ind.
apply H7.
reflexivity.
move=> H7.
apply False_ind.
apply H7.
reflexivity.
move=> H7.
apply False_ind.
apply H7.
reflexivity.
move=> H7.
apply False_ind.
apply H7.
reflexivity.
move=> u.
elim.
move=> H7.
apply H1.
elim H7.
reflexivity.
move=> u.
elim.
move=> H7.
apply H1.
elim H7.
reflexivity.
move=> u H7.
elim (Nat.eq_dec (proj1_sig u) (proj1_sig p)).
elim H7.
move=> u0 H8 H9 H10.
apply False_ind.
apply H8.
left.
suff: (u0 = p).
move=> H11.
rewrite H11.
apply In_singleton.
apply sig_map.
apply H10.
elim (Nat.eq_dec (proj1_sig u) (proj1_sig q)).
elim H7.
move=> u0 H8 H9 H10.
apply False_ind.
apply H8.
right.
suff: (u0 = q).
move=> H11.
rewrite H11.
apply In_singleton.
apply sig_map.
apply H10.
elim (excluded_middle_informative (u = p)).
elim H7.
move=> u0 H8 H9 H10.
apply False_ind.
apply H8.
left.
rewrite H10.
apply In_singleton.
elim (excluded_middle_informative (u = q)).
elim H7.
move=> u0 H8 H9 H10.
apply False_ind.
apply H8.
right.
rewrite H10.
apply In_singleton.
move=> H8 H9 H10 H11.
reflexivity.
move=> k H7.
apply (Full_intro {n : nat | (n < N)} k).
move=> k H7.
apply (Full_intro {n : nat | (n < N)} k).
apply H5.
apply H5.
move=> u1 u2 H3 H4 H5.
suff: (u1 = PermutationCompose N (PermutationCompose N u1 (PermutationSwap N p q)) (PermutationInv N (PermutationSwap N p q))).
move=> H6.
rewrite H6.
rewrite H5.
rewrite (PermutationCompose_assoc N).
rewrite (PermutationCompose_inv_r N).
apply (PermutationCompose_O_r N).
rewrite (PermutationCompose_assoc N).
rewrite (PermutationCompose_inv_r N).
rewrite (PermutationCompose_O_r N).
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> r H2.
apply (Im_intro (Permutation N) (Permutation N) (Full_set (Permutation N)) (fun (s : Permutation N) => PermutationCompose N s (PermutationSwap N p q)) (PermutationCompose N r (PermutationInv N (PermutationSwap N p q)))).
apply (Full_intro (Permutation N)).
rewrite PermutationCompose_assoc.
rewrite (PermutationCompose_inv_l N).
rewrite (PermutationCompose_O_r N).
reflexivity.
move=> r H2.
apply (Full_intro (Permutation N) r).
Qed.

Lemma DeterminantSwapW : forall (f : Field) (N : nat) (A : Matrix f N N) (p q : {n : nat | (n < N)}), proj1_sig p <> proj1_sig q -> Determinant f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => A x q
  | right _ => match Nat.eq_dec (proj1_sig y) (proj1_sig q) with
    | left _ => A x p
    | right _ => A x y
  end
end) = Fopp f (Determinant f N A).
Proof.
move=> f N A p q H1.
rewrite - (DeterminantTrans f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => A x q
  | right _ => match Nat.eq_dec (proj1_sig y) (proj1_sig q) with
    | left _ => A x p
    | right _ => A x y
  end
end)).
rewrite - (DeterminantTrans f N A).
apply (DeterminantSwapH f N (MTranspose f N N A) p q H1).
Qed.

Lemma DeterminantDuplicateH : forall (f : Field) (N : nat) (A : Matrix f N N) (p q : {n : nat | (n < N)}), proj1_sig p <> proj1_sig q -> A p = A q -> Determinant f N A = FO f.
Proof.
move=> f N A p q H1 H2.
unfold Determinant.
suff: ((exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) = (FiniteUnion (Permutation N) (FiniteIntersection (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (fun (r : Permutation N) => PermutationParity N r = OFF)) (FiniteIntersection (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (fun (r : Permutation N) => PermutationParity N r = ON)))).
move=> H3.
rewrite H3.
rewrite MySumF2Union.
suff: ((FiniteIntersection (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (fun r : Permutation N => PermutationParity N r = OFF)) = (FiniteIm (Permutation N) (Permutation N) (fun (r : Permutation N) => PermutationCompose N r (PermutationSwap N p q)) (FiniteIntersection (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (fun r : Permutation N => PermutationParity N r = ON)))).
move=> H4.
rewrite H4.
rewrite - (MySumF2BijectiveSame2 (Permutation N) (Permutation N)).
unfold Basics.compose.
apply (FiniteSetInduction (Permutation N) (FiniteIntersection (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (fun r : Permutation N => PermutationParity N r = ON))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Fadd_O_r f (FO f)).
move=> B b H5 H6 H7 H8.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (CM_comm_assoc (FPCM f)).
rewrite H8.
rewrite (PermutationComposeParity N).
rewrite (PermutationSwapParity N p q).
suff: ((MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => A k (proj1_sig (PermutationCompose N b (PermutationSwap N p q)) k))) = (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => A k (proj1_sig b k)))).
move=> H9.
rewrite H9.
elim (PermutationParity N b).
simpl.
rewrite - (Fmul_add_distr_r f).
rewrite (Fadd_opp_r f (FI f)).
rewrite (Fmul_O_l f).
apply (Fadd_O_r f).
simpl.
rewrite - (Fmul_add_distr_r f).
rewrite (Fadd_opp_l f (FI f)).
rewrite (Fmul_O_l f).
apply (Fadd_O_r f).
rewrite (MySumF2Included {n : nat | (n < N)} (FiniteUnion {n : nat | (n < N)} (FiniteSingleton {n : nat | (n < N)} p) (FiniteSingleton {n : nat | (n < N)} q)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))).
rewrite (MySumF2Included {n : nat | (n < N)} (FiniteUnion {n : nat | (n < N)} (FiniteSingleton {n : nat | (n < N)} p) (FiniteSingleton {n : nat | (n < N)} q)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))).
rewrite MySumF2Union.
rewrite MySumF2Union.
suff: ((MySumF2 {n : nat | (n < N)} (FiniteIntersection {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (Complement {n : nat | (n < N)} (proj1_sig (FiniteUnion {n : nat | (n < N)} (FiniteSingleton {n : nat | (n < N)} p) (FiniteSingleton {n : nat | (n < N)} q))))) (FMCM f) (fun (k : {n : nat | (n < N)}) => A k (proj1_sig (PermutationCompose N b (PermutationSwap N p q)) k))) = (MySumF2 {n : nat | (n < N)} (FiniteIntersection {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (Complement {n : nat | (n < N)} (proj1_sig (FiniteUnion {n : nat | (n < N)} (FiniteSingleton {n : nat | (n < N)} p) (FiniteSingleton {n : nat | (n < N)} q))))) (FMCM f) (fun (k : {n : nat | (n < N)}) => A k (proj1_sig b k)))).
move=> H9.
rewrite H9.
apply (Fmul_eq_compat_r f).
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
unfold PermutationSwap.
unfold PermutationCompose.
unfold Basics.compose.
simpl.
elim (excluded_middle_informative (p = p)).
move=> H10.
elim (excluded_middle_informative (q = p)).
move=> H11.
apply False_ind.
apply H1.
rewrite H11.
reflexivity.
elim (excluded_middle_informative (q = q)).
move=> H11 H12.
rewrite - {1} H2.
rewrite {1} H2.
apply (Fmul_comm f).
move=> H11.
apply False_ind.
apply H11.
reflexivity.
move=> H10.
apply False_ind.
apply H10.
reflexivity.
apply MySumF2Same.
move=> u H9.
unfold PermutationSwap.
unfold PermutationCompose.
unfold Basics.compose.
simpl.
elim (excluded_middle_informative (u = p)).
elim H9.
move=> u0 H10 H11 H12.
apply False_ind.
apply H10.
left.
rewrite H12.
apply In_singleton.
elim (excluded_middle_informative (u = q)).
elim H9.
move=> u0 H10 H11 H12.
apply False_ind.
apply H10.
right.
rewrite H12.
apply In_singleton.
move=> H10 H11.
reflexivity.
move=> u.
elim.
move=> H9.
apply H1.
elim H9.
reflexivity.
move=> u.
elim.
move=> H9.
apply H1.
elim H9.
reflexivity.
move=> k H9.
apply (Full_intro {n : nat | (n < N)}).
move=> k H9.
apply (Full_intro {n : nat | (n < N)}).
move=> H9.
apply H1.
rewrite H9.
reflexivity.
apply H7.
apply H7.
move=> u1 u2 H5 H6 H7.
rewrite - (PermutationCompose_O_r N u1).
rewrite - (PermutationCompose_inv_r N (PermutationSwap N p q)).
rewrite - (PermutationCompose_assoc N u1).
rewrite H7.
rewrite (PermutationCompose_assoc N u2).
rewrite (PermutationCompose_inv_r N (PermutationSwap N p q)).
apply (PermutationCompose_O_r N u2).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> r H4.
apply (Im_intro (Permutation N) (Permutation N) (Intersection (Permutation N) (fun (s : Permutation N) => PermutationParity N s = ON) (Full_set (Permutation N))) (fun (s : Permutation N) => PermutationCompose N s (PermutationSwap N p q)) (PermutationCompose N r (PermutationInv N (PermutationSwap N p q)))).
apply Intersection_intro.
unfold In.
rewrite (PermutationComposeParity N).
rewrite (PermutationInvParity N).
rewrite (PermutationSwapParity N p q).
elim H4.
move=> r0 H5 H6.
rewrite H5.
reflexivity.
move=> H5.
apply H1.
rewrite H5.
reflexivity.
apply (Full_intro (Permutation N)).
rewrite (PermutationCompose_assoc N r).
rewrite (PermutationCompose_inv_l N (PermutationSwap N p q)).
rewrite (PermutationCompose_O_r N r).
reflexivity.
move=> r.
elim.
move=> s H4 y H5.
rewrite H5.
apply Intersection_intro.
unfold In.
rewrite (PermutationComposeParity N).
rewrite (PermutationSwapParity N p q).
elim H4.
move=> s0 H6 H7.
rewrite H6.
reflexivity.
move=> H6.
apply H1.
rewrite H6.
reflexivity.
apply (Full_intro (Permutation N)).
move=> u H4 H5.
suff: (match PermutationParity N u with
  | OFF => False
  | ON => True
end).
elim H5.
move=> u0 H6 H7.
rewrite H6.
apply.
suff: (PermutationParity N u = ON).
move=> H6.
rewrite H6.
apply I.
elim H4.
move=> u0 H6 H7.
apply H6.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> r H3.
suff: (PermutationParity N r = ON \/ PermutationParity N r = OFF).
elim.
move=> H4.
right.
apply Intersection_intro.
apply H4.
apply (Full_intro (Permutation N)).
move=> H4.
left.
apply Intersection_intro.
apply H4.
apply (Full_intro (Permutation N)).
elim (PermutationParity N r).
left.
reflexivity.
right.
reflexivity.
move=> r H3.
apply (Full_intro (Permutation N) r).
Qed.

Lemma DeterminantDuplicateW : forall (f : Field) (N : nat) (A : Matrix f N N) (p q : {n : nat | (n < N)}), proj1_sig p <> proj1_sig q -> (forall (k : {n : nat | (n < N)}), A k p = A k q) -> Determinant f N A = FO f.
Proof.
move=> f N A p q H1 H2.
rewrite - (DeterminantTrans f N A).
apply (DeterminantDuplicateH f N (MTranspose f N N A) p q H1).
apply functional_extensionality.
move=> k.
apply (H2 k).
Qed.

Lemma DeterminantAddTransformH : forall (f : Field) (N : nat) (A : Matrix f N N) (p q : {n : nat | (n < N)}) (c : FT f), proj1_sig p <> proj1_sig q -> Determinant f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
  | left _ => Fadd f (A x y) (Fmul f c (A p y))
  | right _ => A x y
end) = Determinant f N A.
Proof.
move=> f N A p q c H1.
rewrite (DeterminantMultiLinearityHPlus f N A q (fun (k : {n : nat | (n < N)}) => Fmul f c (A p k))).
suff: ((fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
  | left _ => Fmul f c (A p y)
  | right _ => A x y
end) = (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
  | left _ => Fmul f c ((fun (x0 y0 : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
    | left _ => A p y0
    | right _ => A x0 y0
  end) x y)
  | right _ => (fun (x0 y0 : {n0 : nat | (n0 < N)}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
    | left _ => A p y0
    | right _ => A x0 y0
  end) x y
end)).
move=> H2.
rewrite H2.
rewrite (DeterminantMultiLinearityHMult f N (fun x y : {n : nat | (n < N)} => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
  | left _ => A p y
  | right _ => A x y
end) q c).
rewrite (DeterminantDuplicateH f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
  | left _ => A p y
  | right _ => A x y
end) p q).
rewrite (Fmul_O_r f c).
apply (Fadd_O_r f (Determinant f N A)).
apply H1.
apply functional_extensionality.
move=> x.
elim (Nat.eq_dec (proj1_sig p) (proj1_sig q)).
elim (Nat.eq_dec (proj1_sig q) (proj1_sig q)).
move=> H3 H4.
reflexivity.
move=> H3.
apply False_ind.
apply H3.
reflexivity.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig q)).
move=> H3 H4.
reflexivity.
move=> H3.
apply False_ind.
apply H3.
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig q)).
move=> H2.
reflexivity.
move=> H2.
reflexivity.
Qed.

Lemma DeterminantAddTransformW : forall (f : Field) (N : nat) (A : Matrix f N N) (p q : {n : nat | (n < N)}) (c : FT f), proj1_sig p <> proj1_sig q -> Determinant f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig y) (proj1_sig q) with
  | left _ => Fadd f (A x y) (Fmul f c (A x p))
  | right _ => A x y
end) = Determinant f N A.
Proof.
move=> f N A p q c H1.
rewrite - (DeterminantTrans f N (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig y) (proj1_sig q) with
  | left _ => Fadd f (A x y) (Fmul f c (A x p))
  | right _ => A x y
end)).
rewrite - (DeterminantTrans f N A).
apply (DeterminantAddTransformH f N (MTranspose f N N A) p q c H1).
Qed.

Lemma CauchyBinet : forall (f : Field) (N M : nat) (A : Matrix f N M) (B : Matrix f M N), Determinant f N (Mmult f N M N A B) = MySumF2 ({n : nat | (n < N)} -> {n : nat | (n < M)}) (FiniteIntersection ({n : nat | (n < N)} -> {n : nat | (n < M)}) (exist (Finite ({n : nat | (n < N)} -> {n : nat | (n < M)})) (Full_set ({n : nat | (n < N)} -> {n : nat | (n < M)})) (CountPowFinite N M)) (fun (r : ({n : nat | (n < N)} -> {n : nat | (n < M)})) => forall (p q : {n : nat | (n < N)}), (proj1_sig p < proj1_sig q) -> (proj1_sig (r p) < proj1_sig (r q)))) (FPCM f) (fun (r : ({n : nat | (n < N)} -> {n : nat | (n < M)})) => Fmul f (Determinant f N (fun (x y : {n : nat | (n < N)}) => A x (r y))) (Determinant f N (fun (x y : {n : nat | (n < N)}) => B (r x) y))).
Proof.
suff: (forall (m1 m2 : nat) (x : {n : nat | (n < m1 + m2)}), (m1 <= proj1_sig x) -> {y : {n : nat | (n < m2)} | (m1 + proj1_sig y = proj1_sig x)}).
move=> H37 f N M A B.
suff: (MBlockH = fun (f : Field) (M1 M2 N : nat) (A1 : Matrix f M1 N) (A2 : Matrix f M2 N) (x : {n : nat | (n < M1 + M2)}) (y : {n : nat | (n < N)}) => match (le_lt_dec M1 (proj1_sig x)) with
  | left a => A2 (proj1_sig (H37 M1 M2 x a)) y
  | right b => A1 (exist (fun (n : nat) => (n < M1)) (proj1_sig x) b) y
end).
move=> H35.
suff: (MBlockW = fun (f : Field) (M N1 N2 : nat) (A1 : Matrix f M N1) (A2 : Matrix f M N2) (x : {n : nat | (n < M)}) (y : {n : nat | (n < N1 + N2)}) => match (le_lt_dec N1 (proj1_sig y)) with
  | left a => A2 x (proj1_sig (H37 N1 N2 y a))
  | right b => A1 x (exist (fun (n : nat) => (n < N1)) (proj1_sig y) b)
end).
move=> H36.
suff: (Determinant f N (Mopp f N N (Mmult f N M N A B)) = Determinant f (M + N) (MBlockW f (M + N) M N (MBlockH f M N M (MI f M) A) (MBlockH f M N N B (MO f N N)))).
move=> H1.
suff: (Determinant f N (Mmult f N M N A B) = Fmul f (PowF f (Fopp f (FI f)) N) (Determinant f (M + N) (MBlockW f (M + N) M N (MBlockH f M N M (MI f M) A) (MBlockH f M N N B (MO f N N))))).
move=> H2.
rewrite H2.
unfold Determinant at 1.
suff: (forall (p : {n : nat | (n < N)} -> {n : nat | (n < M)}) (k : {n : nat | (n < M)}), Injective p -> (exists (l : {n : nat | (n < N)}), k = p l) -> {l : {n : nat | (n < N)} | k = p l}).
move=> H3.
suff: (forall (l : {n : nat | (n < M)}), (proj1_sig l < M + N)).
move=> H4.
suff: (forall (l : {n : nat | (n < N)}), (M + proj1_sig l < M + N)).
move=> H5.
suff: (forall (x : (({n : nat | (n < N)} -> {n : nat | (n < M)}) * ((Permutation N) * (Permutation N)))), Bijective ((fun (x : (({n : nat | (n < N)} -> {n : nat | (n < M)}) * ((Permutation N) * (Permutation N)))) => match excluded_middle_informative (Injective (fst x)) with
  | left a => (fun (k : {n : nat | (n < M + N)}) => match le_lt_dec M (proj1_sig k) with
    | left b => exist (fun (s : nat) => (s < M + N)) (proj1_sig (fst x (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k b))))) (H4 (fst x (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k b)))))
    | right b => match excluded_middle_informative (exists (l : {n : nat | (n < N)}), exist (fun (s : nat) => (s < M)) (proj1_sig k) b = fst x l) with
      | left c => exist (fun (s : nat) => (s < M + N)) (M + proj1_sig (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun (s : nat) => (s < M)) (proj1_sig k) b) a c)))) (H5 (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun (s : nat) => (s < M)) (proj1_sig k) b) a c))))
      | right _ => k
    end
  end)
  | right a => (fun (k : {n : nat | (n < M + N)}) => k)
end) x)).
move=> H6.
rewrite (MySumF2Included (Permutation (M + N)) (FiniteIm (({n : nat | (n < N)} -> {n : nat | (n < M)}) * ((Permutation N) * (Permutation N))) (Permutation (M + N)) (fun (x : (({n : nat | (n < N)} -> {n : nat | (n < M)}) * ((Permutation N) * (Permutation N)))) => exist Bijective (match excluded_middle_informative (Injective (fst x)) with
  | left a => (fun (k : {n : nat | (n < M + N)}) => match le_lt_dec M (proj1_sig k) with
    | left b => exist (fun (s : nat) => (s < M + N)) (proj1_sig (fst x (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k b))))) (H4 (fst x (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k b)))))
    | right b => match excluded_middle_informative (exists (l : {n : nat | (n < N)}), exist (fun (s : nat) => (s < M)) (proj1_sig k) b = fst x l) with
      | left c => exist (fun (s : nat) => (s < M + N)) (M + proj1_sig (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun (s : nat) => (s < M)) (proj1_sig k) b) a c)))) (H5 (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun (s : nat) => (s < M)) (proj1_sig k) b) a c))))
      | right _ => k
    end
  end)
  | right a => (fun (k : {n : nat | (n < M + N)}) => k)
end) (H6 x)) (FinitePair ({n : nat | (n < N)} -> {n : nat | (n < M)}) ((Permutation N) * (Permutation N)) (FiniteIntersection ({n : nat | (n < N)} -> {n : nat | (n < M)}) (exist (Finite ({n : nat | (n < N)} -> {n : nat | (n < M)})) (Full_set ({n : nat | (n < N)} -> {n : nat | (n < M)})) (CountPowFinite N M)) (fun r : {n : nat | (n < N)} -> {n : nat | (n < M)} => forall p q : {n : nat | (n < N)}, (proj1_sig p < proj1_sig q) -> (proj1_sig (r p) < proj1_sig (r q)))) (FinitePair (Permutation N) (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))))) (exist (Finite (Permutation (M + N))) (Full_set (Permutation (M + N))) (PermutationFinite (M + N)))).
rewrite (MySumF2O (Permutation (M + N)) (FiniteIntersection (Permutation (M + N)) (exist (Finite (Permutation (M + N))) (Full_set (Permutation (M + N))) (PermutationFinite (M + N))) (Complement (Permutation (M + N)) (proj1_sig (FiniteIm (({n : nat | (n < N)} -> {n : nat | (n < M)}) * (Permutation N * Permutation N)) (Permutation (M + N)) (fun x : ({n : nat | (n < N)} -> {n : nat | (n < M)}) * (Permutation N * Permutation N) => exist Bijective match excluded_middle_informative (Injective (fst x)) with
  | left a => fun k : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k) with
    | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (fst x (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k b))))) (H4 (fst x (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k b)))))
    | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = fst x l) with
      | left c => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig k) b) a c)))) (H5 (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun s : nat => (s < M)) (proj1_sig k) b) a c))))
      | right _ => k
    end
  end
  | right _ => fun k : {n : nat | (n < M + N)} => k
end (H6 x)) (FinitePair ({n : nat | (n < N)} -> {n : nat | (n < M)}) (Permutation N * Permutation N) (FiniteIntersection ({n : nat | (n < N)} -> {n : nat | (n < M)}) (exist (Finite ({n : nat | (n < N)} -> {n : nat | (n < M)})) (Full_set ({n : nat | (n < N)} -> {n : nat | (n < M)})) (CountPowFinite N M)) (fun r : {n : nat | (n < N)} -> {n : nat | (n < M)} => forall p q : {n : nat | (n < N)}, (proj1_sig p < proj1_sig q) -> (proj1_sig (r p) < proj1_sig (r q)))) (FinitePair (Permutation N) (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))))))))).
rewrite - (MySumF2BijectiveSame2 (({n : nat | (n < N)} -> {n : nat | (n < M)}) * (Permutation N * Permutation N)) (Permutation (M + N))).
unfold Basics.compose.
rewrite (MySumF2Pair ({n : nat | (n < N)} -> {n : nat | (n < M)}) ((Permutation N) * (Permutation N)) (FiniteIntersection ({n : nat | (n < N)} -> {n : nat | (n < M)}) (exist (Finite ({n : nat | (n < N)} -> {n : nat | (n < M)})) (Full_set ({n : nat | (n < N)} -> {n : nat | (n < M)})) (CountPowFinite N M)) (fun r : {n : nat | (n < N)} -> {n : nat | (n < M)} => forall p q : {n : nat | (n < N)}, (proj1_sig p < proj1_sig q) -> (proj1_sig (r p) < proj1_sig (r q)))) (FinitePair (Permutation N) (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))) (FPCM f) (fun (x : ({n : nat | (n < N)} -> {n : nat | (n < M)})) (y : (Permutation N * Permutation N)) => Fmul f match PermutationParity (M + N) (exist Bijective match excluded_middle_informative (Injective x) with
    | left a => fun k : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k) with
      | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (x (proj1_sig (fst y) (proj1_sig (H37 M N k b))))) (H4 (x (proj1_sig (fst y) (proj1_sig (H37 M N k b)))))
      | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = x l) with
        | left c => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd y) (proj1_sig (H3 x (exist (fun s : nat => s < M) (proj1_sig k) b) a c)))) (H5 (proj1_sig (snd y) (proj1_sig (H3 x (exist (fun s : nat => (s < M)) (proj1_sig k) b) a c))))
        | right _ => k
      end
    end
    | right _ => fun k : {n : nat | (n < M + N)} => k
  end (H6 (x, y))) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < M + N)} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N))) (FMCM f) (fun k : {n : nat | (n < M + N)} => MBlockW f (M + N) M N (MBlockH f M N M (MI f M) A) (MBlockH f M N N B (MO f N N)) k (proj1_sig (exist Bijective match excluded_middle_informative (Injective x) with
  | left a => fun k0 : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k0) with
    | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (x (proj1_sig (fst y) (proj1_sig (H37 M N k0 b))))) (H4 (x (proj1_sig (fst y) (proj1_sig (H37 M N k0 b)))))
    | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k0) b = x l) with
      | left c => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd y) (proj1_sig (H3 x (exist (fun s : nat => s < M) (proj1_sig k0) b) a c)))) (H5 (proj1_sig (snd y) (proj1_sig (H3 x (exist (fun s : nat => (s < M)) (proj1_sig k0) b) a c))))
      | right _ => k0
    end
  end
  | right _ => fun k0 : {n : nat | (n < M + N)} => k0
end (H6 (x,y))) k))))).
rewrite (CM_O_r (FPCM f)).
apply (FiniteSetInduction ({n : nat | (n < N)} -> {n : nat | (n < M)}) (FiniteIntersection ({n : nat | (n < N)} -> {n : nat | (n < M)}) (exist (Finite ({n : nat | (n < N)} -> {n : nat | (n < M)})) (Full_set ({n : nat | (n < N)} -> {n : nat | (n < M)})) (CountPowFinite N M)) (fun r : {n : nat | (n < N)} -> {n : nat | (n < M)} => forall p q : {n : nat | (n < N)}, (proj1_sig p < proj1_sig q) -> (proj1_sig (r p) < proj1_sig (r q))))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Fmul_O_r f).
move=> C c H7 H8 H9 H10.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Fmul_add_distr_l f).
rewrite H10.
apply (Fadd_eq_compat_l f).
suff: (Fmul f (Determinant f N (fun x y : {n : nat | (n < N)} => A x (c y))) (Determinant f N (fun x y : {n : nat | (n < N)} => B (c x) y)) = (MySumF2 ((Permutation N) * (Permutation N)) (FinitePair (Permutation N) (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))) (FPCM f) (fun PQ : ((Permutation N) * (Permutation N)) => Fmul f (Fmul f match PermutationParity N (fst PQ) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => A k (c (proj1_sig (fst PQ) k))))) (Fmul f match PermutationParity N (snd PQ) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => B (c k) (proj1_sig (snd PQ) k))))))).
move=> H11.
rewrite H11.
apply (FiniteSetInduction (Permutation N * Permutation N) (FinitePair (Permutation N) (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Fmul_O_r f).
move=> D d H12 H13 H14 H15.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Fmul_add_distr_l f).
rewrite H15.
apply (Fadd_eq_compat_l f).
rewrite - (Fmul_assoc f (Fmul f match PermutationParity N (fst d) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => A k (c (proj1_sig (fst d) k))))) (match PermutationParity N (snd d) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end) (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => B (c k) (proj1_sig (snd d) k)))).
rewrite (Fmul_comm f (Fmul f match PermutationParity N (fst d) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => A k (c (proj1_sig (fst d) k))))) (match PermutationParity N (snd d) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end)).
rewrite - (Fmul_assoc f (match PermutationParity N (snd d) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end) (match PermutationParity N (fst d) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end)).
rewrite (Fmul_assoc f (Fmul f match PermutationParity N (snd d) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end match PermutationParity N (fst d) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end)).
rewrite - (Fmul_assoc f (PowF f (Fopp f (FI f)) N)).
suff: ((Fmul f (PowF f (Fopp f (FI f)) N) match PermutationParity (M + N) (exist Bijective match excluded_middle_informative (Injective c) with
    | left a => fun k : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k) with
      | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (c (proj1_sig (fst d) (proj1_sig (H37 M N k b))))) (H4 (c (proj1_sig (fst d) (proj1_sig (H37 M N k b)))))
      | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = c l) with
        | left c0 => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd d) (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) b) a c0)))) (H5 (proj1_sig (snd d) (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) b) a c0))))
        | right _ => k
      end
    end
    | right _ => fun k : {n0 : nat | (n0 < M + N)} => k
  end (H6 (c, d))) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end) = (Fmul f match PermutationParity N (snd d) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end match PermutationParity N (fst d) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end)).
move=> H16.
rewrite H16.
apply (Fmul_eq_compat_l f).
rewrite (MySumF2Included {n : nat | (n < M + N)} (FiniteIntersection {n : nat | (n < M + N)} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N))) (fun (k : {n : nat | (n < M + N)}) => (M <= proj1_sig k)))).
rewrite (MySumF2Included {n : nat | (n < M + N)} (FiniteIntersection {n : nat | (n < M + N)} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N))) (fun (k : {n : nat | (n < M + N)}) => exists (l : {n : nat | (n < N)}), proj1_sig k = proj1_sig (c l))) (FiniteIntersection {n : nat | (n < M + N)} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N))) (Complement {n : nat | (n < M + N)} (proj1_sig (FiniteIntersection {n : nat | (n < M + N)} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N))) (fun k : {n : nat | (n < M + N)} => (M <= proj1_sig k))))))).
rewrite (MySumF2O {n : nat | (n < M + N)} (FiniteIntersection {n : nat | (n < M + N)} (FiniteIntersection {n : nat | (n < M + N)} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N))) (Complement {n : nat | (n < M + N)} (proj1_sig (FiniteIntersection {n : nat | (n < M + N)} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N))) (fun k : {n : nat | (n < M + N)} => (M <= proj1_sig k)))))) (Complement {n : nat | (n < M + N)} (proj1_sig (FiniteIntersection {n : nat | (n < M + N)} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N))) (fun k : {n : nat | (n < M + N)} => exists l : {n : nat | (n < N)}, proj1_sig k = proj1_sig (c l))))))).
rewrite (CM_O_r (FMCM f)).
suff: ((MySumF2 {n : nat | (n < M + N)} (FiniteIntersection {n : nat | (n < M + N)} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N))) (fun k : {n : nat | (n < M + N)} => (M <= proj1_sig k))) (FMCM f) (fun k : {n : nat | (n < M + N)} => MBlockW f (M + N) M N (MBlockH f M N M (MI f M) A) (MBlockH f M N N B (MO f N N)) k (proj1_sig (exist Bijective match excluded_middle_informative (Injective c) with
  | left a => fun k0 : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k0) with
    | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (c (proj1_sig (fst d) (proj1_sig (H37 M N k0 b))))) (H4 (c (proj1_sig (fst d) (proj1_sig (H37 M N k0 b)))))
    | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k0) b = c l) with
      | left c0 => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd d) (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k0) b) a c0)))) (H5 (proj1_sig (snd d) (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k0) b) a c0))))
      | right _ => k0
    end
  end
  | right _ => fun k0 : {n0 : nat | (n0 < M + N)} => k0
end (H6 (c, d))) k))) = (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => A k (c (proj1_sig (fst d) k))))).
move=> H17.
rewrite H17.
apply (Fmul_eq_compat_l f).
suff: ((FiniteIntersection {n : nat | (n < M + N)} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N))) (fun k : {n : nat | (n < M + N)} => exists l : {n : nat | (n < N)}, proj1_sig k = proj1_sig (c l))) = (FiniteIm {n : nat | (n < N)} {n : nat | (n < M + N)} (fun (l : {n : nat | (n < N)}) => exist (fun (s : nat) => (s < M + N)) (proj1_sig (c l)) (H4 (c l))) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)))).
move=> H18.
rewrite H18.
rewrite - (MySumF2BijectiveSame2 {n : nat | (n < N)} {n : nat | (n < M + N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))).
unfold Basics.compose.
apply (MySumF2Same {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f)).
move=> u H19.
simpl.
elim (excluded_middle_informative (Injective c)).
move=> H20.
simpl.
elim (le_lt_dec M (proj1_sig (c u))).
move=> H21.
apply False_ind.
apply (le_not_lt M (proj1_sig (c u)) H21 (proj2_sig (c u))).
move=> H21.
elim (excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig (c u)) H21 = c l)).
move=> H22.
rewrite H36.
rewrite H35.
simpl.
elim (le_lt_dec M (M + proj1_sig (proj1_sig (snd d) (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig (c u)) H21) H20 H22))))).
move=> H23.
elim (le_lt_dec M (proj1_sig (c u))).
move=> H24.
apply False_ind.
apply (le_not_lt M (proj1_sig (c u)) H24 (proj2_sig (c u))).
move=> H24.
suff: ((exist (fun n : nat => (n < M)) (proj1_sig (c u)) H24) = c u).
move=> H25.
rewrite H25.
suff: ((proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd d) (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig (c u)) H21) H20 H22)))) (H5 (proj1_sig (snd d) (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig (c u)) H21) H20 H22))))) H23)) = (proj1_sig (snd d) u)).
move=> H26.
rewrite H26.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd d) (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig (c u)) H21) H20 H22)))) (H5 (proj1_sig (snd d) (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig (c u)) H21) H20 H22))))) H23))) (proj1_sig (proj1_sig (snd d) u)) M).
rewrite ((proj2_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd d) (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig (c u)) H21) H20 H22)))) (H5 (proj1_sig (snd d) (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig (c u)) H21) H20 H22))))) H23))).
simpl.
suff: ((proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig (c u)) H21) H20 H22)) = u).
move=> H26.
rewrite H26.
reflexivity.
apply H20.
rewrite - (proj2_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig (c u)) H21) H20 H22)).
apply sig_map.
reflexivity.
apply sig_map.
reflexivity.
move=> H23.
apply False_ind.
apply (lt_not_le (M + proj1_sig (proj1_sig (snd d) (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig (c u)) H21) H20 H22)))) M H23).
apply (le_plus_l M).
move=> H22.
apply False_ind.
apply H22.
exists u.
apply sig_map.
reflexivity.
move=> H20.
apply False_ind.
apply H20.
elim H8.
move=> c0 H21 H22 k1 k2 H23.
apply sig_map.
elim (le_or_lt (proj1_sig k1) (proj1_sig k2)).
move=> H24.
elim (le_lt_or_eq (proj1_sig k1) (proj1_sig k2) H24).
move=> H25.
apply False_ind.
apply (lt_irrefl (proj1_sig (c0 k1))).
rewrite {2} H23.
apply (H21 k1 k2 H25).
apply.
move=> H24.
apply False_ind.
apply (lt_irrefl (proj1_sig (c0 k1))).
rewrite {1} H23.
apply (H21 k2 k1 H24).
elim H8.
move=> c0 H19 H20 u1 u2 H21 H22 H23.
elim (le_or_lt (proj1_sig u1) (proj1_sig u2)).
move=> H24.
elim (le_lt_or_eq (proj1_sig u1) (proj1_sig u2) H24).
move=> H25.
apply False_ind.
apply (lt_irrefl (proj1_sig (exist (fun s : nat => (s < M + N)) (proj1_sig (c0 u1)) (H4 (c0 u1))))).
rewrite {2} H23.
apply (H19 u1 u2 H25).
apply sig_map.
move=> H24.
apply False_ind.
apply (lt_irrefl (proj1_sig (exist (fun s : nat => (s < M + N)) (proj1_sig (c0 u1)) (H4 (c0 u1))))).
rewrite {1} H23.
apply (H19 u2 u1 H24).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> k.
elim.
move=> k0 H18 H19.
elim H18.
move=> l H20.
apply (Im_intro {n : nat | (n < N)} {n : nat | (n < M + N)} (Full_set {n : nat | (n < N)}) (fun l : {n : nat | (n < N)} => exist (fun s : nat => (s < M + N)) (proj1_sig (c l)) (H4 (c l))) l).
apply (Full_intro {n : nat | (n < N)} l).
apply sig_map.
apply H20.
move=> l.
elim.
move=> s H18 t H19.
apply Intersection_intro.
exists s.
rewrite H19.
reflexivity.
apply (Full_intro {n : nat | (n < M + N)} t).
suff: ((FiniteIntersection {n : nat | (n < M + N)} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N))) (fun k : {n : nat | (n < M + N)} => (M <= proj1_sig k))) = (FiniteIm {n : nat | (n < N)} {n : nat | (n < M + N)} (fun (k : {n : nat | (n < N)}) => exist (fun (l : nat) => (l < M + N)) (M + proj1_sig k) (H5 k)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)))).
move=> H17.
rewrite H17.
rewrite - (MySumF2BijectiveSame2 {n : nat | (n < N)} {n : nat | (n < M + N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))).
unfold Basics.compose.
apply MySumF2Same.
move=> u H18.
rewrite H36.
rewrite H35.
simpl.
elim (excluded_middle_informative (Injective c)).
move=> H19.
simpl.
elim (le_lt_dec M (M + proj1_sig u)).
move=> H20.
simpl.
elim (le_lt_dec M (@proj1_sig nat (fun n : nat => lt n M) (c (@proj1_sig (forall _ : @sig nat (fun n : nat => lt n N), @sig nat (fun n : nat => lt n N)) (fun f0 : forall _ : @sig nat (fun n : nat => lt n N), @sig nat (fun n : nat => lt n N) => @Bijective (@sig nat (fun n : nat => lt n N)) (@sig nat (fun n : nat => lt n N)) f0) (@fst (Permutation N) (Permutation N) d) (@proj1_sig (@sig nat (fun n : nat => lt n N)) (fun y : @sig nat (fun n : nat => lt n N) => @eq nat (Init.Nat.add M (@proj1_sig nat (fun n : nat => lt n N) y)) (Init.Nat.add M (@proj1_sig nat (fun n : nat => lt n N) u))) (H37 M N (@exist nat (fun l : nat => lt l (Init.Nat.add M N)) (Init.Nat.add M (@proj1_sig nat (fun n : nat => lt n N) u)) (H5 u)) H20)))))).
move=> H21.
apply False_ind.
apply (lt_not_le (proj1_sig (c (proj1_sig (fst d) (proj1_sig (H37 M N (exist (fun l : nat => (l < M + N)) (M + proj1_sig u) (H5 u)) H20))))) M (proj2_sig (c (proj1_sig (fst d) (proj1_sig (H37 M N (exist (fun l : nat => (l < M + N)) (M + proj1_sig u) (H5 u)) H20))))) H21).
move=> H21.
suff: ((proj1_sig (H37 M N (exist (fun l : nat => (l < M + N)) (M + proj1_sig u) (H5 u)) H20)) = u).
move=> H22.
suff: ((exist (fun n : nat => (n < M)) (proj1_sig (c (proj1_sig (fst d) (proj1_sig (H37 M N (exist (fun l : nat => (l < M + N)) (M + proj1_sig u) (H5 u)) H20))))) H21) = (c (proj1_sig (fst d) u))).
move=> H23.
rewrite H23.
rewrite H22.
reflexivity.
apply sig_map.
simpl.
rewrite H22.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun l : nat => (l < M + N)) (M + proj1_sig u) (H5 u)) H20))) (proj1_sig u) M).
apply (proj2_sig (H37 M N (exist (fun l : nat => (l < M + N)) (M + proj1_sig u) (H5 u)) H20)).
move=> H20.
apply False_ind.
apply (lt_not_le (M + proj1_sig u) M H20).
apply le_plus_l.
move=> H19.
apply False_ind.
apply H19.
elim H8.
move=> c0 H20 H21 k1 k2 H22.
apply sig_map.
elim (le_or_lt (proj1_sig k1) (proj1_sig k2)).
move=> H23.
elim (le_lt_or_eq (proj1_sig k1) (proj1_sig k2) H23).
move=> H24.
apply False_ind.
apply (lt_irrefl (proj1_sig (c0 k1))).
rewrite {2} H22.
apply (H20 k1 k2 H24).
apply.
move=> H23.
apply False_ind.
apply (lt_irrefl (proj1_sig (c0 k1))).
rewrite {1} H22.
apply (H20 k2 k1 H23).
move=> u1 u2 H18 H19 H20.
apply sig_map.
apply (plus_reg_l (proj1_sig u1) (proj1_sig u2) M).
suff: ((M + proj1_sig u1) = proj1_sig (exist (fun l : nat => (l < M + N)) (M + proj1_sig u1) (H5 u1))).
move=> H21.
rewrite H21.
rewrite H20.
reflexivity.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> k.
elim.
move=> k0 H17 H18.
suff: (proj1_sig k0 - M < N).
move=> H19.
apply (Im_intro {n : nat | (n < N)} {n : nat | (n < M + N)} (Full_set {n : nat | (n < N)}) (fun (k1 : {n : nat | (n < N)}) => exist (fun l : nat => (l < M + N)) (M + proj1_sig k1) (H5 k1)) (exist (fun (n : nat) => (n < N)) (proj1_sig k0 - M) H19)).
apply (Full_intro {n : nat | (n < N)}).
apply sig_map.
simpl.
rewrite (le_plus_minus_r M (proj1_sig k0) H17).
reflexivity.
apply (plus_lt_reg_l (proj1_sig k0 - M) N M).
rewrite (le_plus_minus_r M (proj1_sig k0) H17).
apply (proj2_sig k0).
move=> k.
elim.
move=> s H17 t H18.
rewrite H18.
apply Intersection_intro.
apply (le_plus_l M (proj1_sig s)).
apply (Full_intro {n : nat | (n < M + N)}).
move=> u H17.
rewrite H36.
rewrite H35.
simpl.
elim (excluded_middle_informative (Injective c)).
move=> H18.
elim (le_lt_dec M (proj1_sig u)).
elim H17.
move=> k0 H19 H20.
elim H20.
move=> k1 H21 H22 H23.
apply False_ind.
apply H21.
apply Intersection_intro.
apply H23.
apply (Full_intro {n : nat | (n < M + N)} k1).
move=> H19.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N)}), exist (fun s : nat => (s < M)) (proj1_sig u) H19 = c l)).
move=> H20.
suff: (~ exists (l : {n : nat | (n < N)}), (proj1_sig u) = proj1_sig (c l)).
move=> H21.
apply False_ind.
apply H21.
elim H20.
move=> l H22.
exists l.
rewrite - H22.
reflexivity.
elim H17.
move=> u0 H21 H22 H23.
apply H21.
apply Intersection_intro.
apply H23.
apply (Full_intro {n : nat | (n < M + N)} u0).
move=> H20.
elim (le_lt_dec M (proj1_sig u)).
move=> H21.
apply False_ind.
apply (lt_not_le (proj1_sig u) M H19 H21).
move=> H21.
unfold MI.
elim (Nat.eq_dec (proj1_sig (exist (fun n : nat => (n < M)) (proj1_sig u) H19)) (proj1_sig (exist (fun n : nat => (n < M)) (proj1_sig u) H21))).
move=> H22.
reflexivity.
move=> H22.
apply False_ind.
apply H22.
reflexivity.
move=> H18.
apply False_ind.
apply H18.
move=> u1 u2 H19.
apply sig_map.
elim (le_or_lt (proj1_sig u1) (proj1_sig u2)).
move=> H20.
elim (le_lt_or_eq (proj1_sig u1) (proj1_sig u2) H20).
move=> H21.
apply False_ind.
apply (lt_irrefl (proj1_sig (c u1))).
rewrite {2} H19.
elim H8.
move=> c0 H22 H23.
apply (H22 u1 u2 H21).
apply.
move=> H20.
apply False_ind.
apply (lt_irrefl (proj1_sig (c u1))).
rewrite {1} H19.
elim H8.
move=> c0 H21 H22.
apply (H21 u2 u1 H20).
move=> k.
elim.
move=> k0 H17 H18.
apply Intersection_intro.
move=> H19.
apply (le_not_lt M (proj1_sig k0)).
elim H19.
move=> k1 H20 H21.
apply H20.
elim H17.
move=> l H20.
rewrite H20.
apply (proj2_sig (c l)).
apply (Full_intro {n : nat | (n < M + N)} k0).
move=> k H17.
apply (Full_intro {n : nat | (n < M + N)} k).
suff: (forall (N1 N2 : nat) (p : {n : nat | (n < N1)} -> {n : nat | (n < N2)}) (k : {n : nat | (n < N2)}), Injective p -> (exists l : {n : nat | (n < N1)}, k = p l) -> {l : {n : nat | (n < N1)} | k = p l}).
move=> H16.
suff: (forall (N1 N2 : nat) (f : {n : nat | (n < N1)} -> {n : nat | (n < N2)}) (P : Permutation N1) (H : Injective f), Bijective (fun (k : {n : nat | (n < N2)}) => match excluded_middle_informative (exists l : {n : nat | (n < N1)}, k = f l) with
  | left H2 => f (proj1_sig P (proj1_sig (H16 N1 N2 f k H H2)))
  | right _ => k
end)).
move=> H17.
suff: (forall (N1 N2 : nat) (f : {n : nat | (n < N1)} -> {n : nat | (n < N2)}) (P : Permutation N1) (H : Injective f), (forall (p q : {n : nat | (n < N1)}), (proj1_sig p < proj1_sig q) -> (proj1_sig (f p) < proj1_sig (f q))) -> PermutationParity N1 P = PermutationParity N2 (exist Bijective (fun (k : {n : nat | (n < N2)}) => match excluded_middle_informative (exists l : {n : nat | (n < N1)}, k = f l) with
  | left H2 => f (proj1_sig P (proj1_sig (H16 N1 N2 f k H H2)))
  | right _ => k
end) (H17 N1 N2 f P H))).
move=> H18.
suff: (forall (N1 : nat) (co : nat) (P : Permutation N1), (forall (k : {n : nat | (n < N1)}), proj1_sig P (proj1_sig P k) = k) -> cardinal {n : nat | (n < N1)} (fun (k : {n : nat | (n < N1)}) => (proj1_sig (proj1_sig P k) < proj1_sig k)) co -> Fmul f (PowF f (Fopp f (FI f)) co) (match PermutationParity N1 P with
  | ON => Fopp f (FI f)
  | OFF => FI f
end) = FI f).
move=> H19.
suff: (Injective c).
move=> H20.
suff: (Bijective (fun (k : {n : nat | (n < M + N)}) => match le_lt_dec M (proj1_sig k) with
  | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (c (proj1_sig (H37 M N k b)))) (H4 (c (proj1_sig (H37 M N k b))))
  | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = c l) with
    | left c0 => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) b) H20 c0))) (H5 (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) b) H20 c0)))
    | right _ => k
  end
end)).
move=> H21.
suff: (Injective (fun (k : {n : nat | (n < N)}) => exist (fun (n : nat) => (n < M + N)) (M + proj1_sig k) (H5 k))).
move=> H22.
suff: (Injective (fun (k : {n : nat | (n < N)}) => exist (fun (n : nat) => (n < M + N)) (proj1_sig (c k)) (H4 (c k)))).
move=> H23.
suff: ((exist Bijective match excluded_middle_informative (Injective c) with
  | left a => fun k : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k) with
    | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (c (proj1_sig (fst d) (proj1_sig (H37 M N k b))))) (H4 (c (proj1_sig (fst d) (proj1_sig (H37 M N k b)))))
    | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = c l) with
      | left c0 => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd d) (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) b) a c0)))) (H5 (proj1_sig (snd d) (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) b) a c0))))
      | right _ => k
    end
  end
  | right _ => fun k : {n0 : nat | (n0 < M + N)} => k
end (H6 (c, d))) = PermutationCompose (M + N) (exist Bijective (fun (k : {n : nat | (n < M + N)}) => match le_lt_dec M (proj1_sig k) with
  | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (c (proj1_sig (H37 M N k b)))) (H4 (c (proj1_sig (H37 M N k b))))
  | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = c l) with
    | left c0 => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) b) H20 c0))) (H5 (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) b) H20 c0)))
    | right _ => k
  end
end) H21) (PermutationCompose (M + N) (exist Bijective (fun k : {n : nat | (n < M + N)} => match excluded_middle_informative (exists l : {n : nat | (n < N)}, k = (fun (k : {n : nat | (n < N)}) => exist (fun (n : nat) => (n < M + N)) (M + proj1_sig k) (H5 k)) l) with
  | left H2 => (fun (k : {n : nat | (n < N)}) => exist (fun (n : nat) => (n < M + N)) (M + proj1_sig k) (H5 k)) (proj1_sig (fst d) (proj1_sig (H16 N (M + N) (fun (k : {n : nat | (n < N)}) => exist (fun (n : nat) => (n < M + N)) (M + proj1_sig k) (H5 k)) k H22 H2)))
  | right _ => k
end) (H17 N (M + N) (fun (k : {n : nat | (n < N)}) => exist (fun (n : nat) => (n < M + N)) (M + proj1_sig k) (H5 k)) (fst d) H22)) (exist Bijective (fun k : {n : nat | (n < M + N)} => match excluded_middle_informative (exists l : {n : nat | (n < N)}, k = (fun (k : {n : nat | (n < N)}) => exist (fun (n : nat) => (n < M + N)) (proj1_sig (c k)) (H4 (c k))) l) with
  | left H2 => (fun (k : {n : nat | (n < N)}) => exist (fun (n : nat) => (n < M + N)) (proj1_sig (c k)) (H4 (c k))) (proj1_sig (snd d) (proj1_sig (H16 N (M + N) (fun (k : {n : nat | (n < N)}) => exist (fun (n : nat) => (n < M + N)) (proj1_sig (c k)) (H4 (c k))) k H23 H2)))
  | right _ => k
end) (H17 N (M + N) (fun (k : {n : nat | (n < N)}) => exist (fun (n : nat) => (n < M + N)) (proj1_sig (c k)) (H4 (c k))) (snd d) H23)))).
move=> H24.
rewrite H24.
rewrite (PermutationComposeParity (M + N)).
suff: (forall (X Y : Permutation (M + N)), match ParityXOR (PermutationParity (M + N) X) (PermutationParity (M + N) Y) with
  | OFF => FI f
  | ON => Fopp f (FI f)
end = Fmul f match PermutationParity (M + N) X with
  | OFF => FI f
  | ON => Fopp f (FI f)
end match PermutationParity (M + N) Y with
  | OFF => FI f
  | ON => Fopp f (FI f)
end).
move=> H25.
rewrite H25.
rewrite - (Fmul_assoc f).
rewrite (H19 (M + N) N).
rewrite (Fmul_I_l f).
rewrite (PermutationComposeParity (M + N)).
rewrite H25.
rewrite - (H18 N (M + N) (fun (k : {n : nat | (n < N)}) => exist (fun n : nat => (n < M + N)) (M + proj1_sig k) (H5 k)) (fst d) H22).
rewrite - (H18 N (M + N) (fun k : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (proj1_sig (c k)) (H4 (c k))) (snd d) H23).
apply (Fmul_comm f).
elim H8.
move=> c0 H26 H27.
apply H26.
move=> p q.
apply plus_lt_compat_l.
move=> k.
simpl.
elim (le_lt_dec M (proj1_sig k)).
move=> H26.
simpl.
elim (le_lt_dec M (proj1_sig (c (proj1_sig (H37 M N k H26))))).
move=> H27.
apply False_ind.
apply (le_not_lt M (proj1_sig (c (proj1_sig (H37 M N k H26)))) H27 (proj2_sig (c (proj1_sig (H37 M N k H26))))).
move=> H27.
elim (excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig (c (proj1_sig (H37 M N k H26)))) H27 = c l)).
move=> H28.
apply sig_map.
simpl.
suff: ((proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig (c (proj1_sig (H37 M N k H26)))) H27) H20 H28)) = (proj1_sig (H37 M N k H26))).
move=> H29.
rewrite H29.
apply (proj2_sig (H37 M N k H26)).
apply H20.
rewrite - (proj2_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig (c (proj1_sig (H37 M N k H26)))) H27) H20 H28)).
apply sig_map.
reflexivity.
move=> H28.
apply False_ind.
apply H28.
exists (proj1_sig (H37 M N k H26)).
apply sig_map.
reflexivity.
move=> H26.
elim (excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) H26 = c l)).
move=> H27.
simpl.
elim (le_lt_dec M (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) H26) H20 H27)))).
move=> H28.
apply sig_map.
simpl.
elim H27.
move=> l H29.
suff: (proj1_sig k = proj1_sig (c l)).
move=> H30.
rewrite {7} H30.
suff: ((proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) H26) H20 H27))) (H5 (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) H26) H20 H27)))) H28)) = l).
move=> H31.
rewrite H31.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) H26) H20 H27))) (H5 (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) H26) H20 H27)))) H28))) (proj1_sig l) M).
rewrite ((proj2_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) H26) H20 H27))) (H5 (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) H26) H20 H27)))) H28))).
simpl.
suff: ((proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) H26) H20 H27)) = l).
move=> H31.
rewrite H31.
reflexivity.
apply H20.
rewrite - (proj2_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) H26) H20 H27)).
apply sig_map.
simpl.
apply H30.
rewrite - H29.
reflexivity.
move=> H28.
apply False_ind.
apply (lt_not_le (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) H26) H20 H27))) M H28).
apply le_plus_l.
move=> H27.
elim (le_lt_dec M (proj1_sig k)).
move=> H28.
apply False_ind.
apply (le_not_lt M (proj1_sig k) H28 H26).
move=> H28.
elim (excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) H28 = c l)).
move=> H29.
apply False_ind.
apply H27.
elim H29.
move=> l H30.
exists l.
suff: (H26 = H28).
move=> H31.
rewrite H31.
apply H30.
apply proof_irrelevance.
move=> H29.
reflexivity.
simpl.
suff: ((fun (k : {n : nat | (n < M + N)}) => (proj1_sig match le_lt_dec M (proj1_sig k) with
  | left b => exist (fun s : nat => s < M + N) (proj1_sig (c (proj1_sig (H37 M N k b)))) (H4 (c (proj1_sig (H37 M N k b))))
  | right b => match excluded_middle_informative (exists l : {n : nat | n < N}, exist (fun s : nat => s < M) (proj1_sig k) b = c l) with
    | left c0 => exist (fun s : nat => s < M + N) (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) b) H20 c0))) (H5 (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) b) H20 c0)))
    | right _ => k
  end
end < proj1_sig k)) = (fun (k : {n : nat | (n < M + N)}) => (M <= proj1_sig k))).
move=> H26.
rewrite H26.
apply (CardinalSigSame {n : nat | (n < M + N)}).
apply (CountCardinalBijective {t : {n : nat | (n < M + N)} | (M <= proj1_sig t)}).
exists (fun (k : {n : nat | (n < N)}) => (exist (fun (t : {n : nat | (n < M + N)}) => (M <= proj1_sig t)) (exist (fun (l : nat) => (l < M + N)) (M + proj1_sig k) (H5 k)) (le_plus_l M (proj1_sig k)))).
exists (fun (k : {t : {n : nat | (n < M + N)} | (M <= proj1_sig t)}) => proj1_sig (H37 M N (proj1_sig k) (proj2_sig k))).
apply conj.
move=> k.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (proj1_sig (exist (fun t : {n : nat | (n < M + N)} => (M <= proj1_sig t)) (exist (fun l : nat => (l < M + N)) (M + proj1_sig k) (H5 k)) (le_plus_l M (proj1_sig k)))) (proj2_sig (exist (fun t : {n : nat | (n < M + N)} => (M <= proj1_sig t)) (exist (fun l : nat => (l < M + N)) (M + proj1_sig k) (H5 k)) (le_plus_l M (proj1_sig k))))))) (proj1_sig k) M).
rewrite (proj2_sig (H37 M N (proj1_sig (exist (fun t : {n : nat | (n < M + N)} => (M <= proj1_sig t)) (exist (fun l : nat => (l < M + N)) (M + proj1_sig k) (H5 k)) (le_plus_l M (proj1_sig k)))) (proj2_sig (exist (fun t : {n : nat | (n < M + N)} => (M <= proj1_sig t)) (exist (fun l : nat => (l < M + N)) (M + proj1_sig k) (H5 k)) (le_plus_l M (proj1_sig k)))))).
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
simpl.
apply (proj2_sig (H37 M N (proj1_sig y) (proj2_sig y))).
apply Extensionality_Ensembles.
apply conj.
move=> k.
unfold In.
elim (le_lt_dec M (proj1_sig k)).
move=> H26 H27.
apply H26.
move=> H26.
elim (excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) H26 = c l)).
simpl.
move=> H27 H28.
apply False_ind.
apply (lt_irrefl M).
apply (lt_trans M (proj1_sig k) M).
apply (le_trans (S M) (S (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) H26) H20 H27)))) (proj1_sig k)).
apply le_n_S.
apply le_plus_l.
apply H28.
apply H26.
move=> H27 H28.
apply False_ind.
apply (lt_irrefl (proj1_sig k) H28).
move=> k H26.
unfold In.
elim (le_lt_dec M (proj1_sig k)).
move=> H27.
apply (le_trans (S (proj1_sig (c (proj1_sig (H37 M N k H27))))) M (proj1_sig k) (proj2_sig (c (proj1_sig (H37 M N k H27)))) H27).
move=> H27.
apply False_ind.
apply (le_not_lt M (proj1_sig k) H26 H27).
move=> X Y.
elim (PermutationParity (M + N) X).
elim (PermutationParity (M + N) Y).
rewrite (Fmul_opp_opp f (FI f) (FI f)).
rewrite (Fmul_I_l f).
reflexivity.
rewrite (Fmul_I_r f).
reflexivity.
elim (PermutationParity (M + N) Y).
rewrite (Fmul_I_l f).
reflexivity.
rewrite (Fmul_I_l f).
reflexivity.
unfold PermutationCompose.
unfold Basics.compose.
apply sig_map.
simpl.
elim (excluded_middle_informative (Injective c)).
move=> H24.
apply functional_extensionality.
move=> k.
elim (le_lt_dec M (proj1_sig k)).
move=> H25.
elim (excluded_middle_informative (exists l0 : {n : nat | (n < N)}, k = exist (fun n : nat => (n < M + N)) (proj1_sig (c l0)) (H4 (c l0)))).
move=> H26.
apply False_ind.
apply (le_not_lt M (proj1_sig k) H25).
elim H26.
move=> s H27.
rewrite H27.
apply (proj2_sig (c s)).
move=> H26.
elim (excluded_middle_informative (exists l : {n : nat | (n < N)}, k = exist (fun n : nat => (n < M + N)) (M + proj1_sig l) (H5 l))).
move=> H27.
simpl.
elim (le_lt_dec M (M + proj1_sig (proj1_sig (fst d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (M + proj1_sig k0) (H5 k0)) k H22 H27))))).
move=> H28.
apply sig_map.
simpl.
suff: ((proj1_sig (fst d) (proj1_sig (H37 M N k H25))) = (proj1_sig (H37 M N (exist (fun n : nat => (n < M + N)) (M + proj1_sig (proj1_sig (fst d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | n < N} => exist (fun n : nat => n < M + N) (M + proj1_sig k0) (H5 k0)) k H22 H27)))) (H5 (proj1_sig (fst d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (M + proj1_sig k0) (H5 k0)) k H22 H27))))) H28))).
move=> H29.
rewrite H29.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (fst d) (proj1_sig (H37 M N k H25)))) (proj1_sig (proj1_sig (H37 M N (exist (fun n : nat => (n < M + N)) (M + proj1_sig (proj1_sig (fst d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | n < N} => exist (fun n : nat => n < M + N) (M + proj1_sig k0) (H5 k0)) k H22 H27)))) (H5 (proj1_sig (fst d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (M + proj1_sig k0) (H5 k0)) k H22 H27))))) H28))) M).
rewrite (proj2_sig (H37 M N (exist (fun n : nat => (n < M + N)) (M + proj1_sig (proj1_sig (fst d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | n < N} => exist (fun n : nat => n < M + N) (M + proj1_sig k0) (H5 k0)) k H22 H27)))) (H5 (proj1_sig (fst d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (M + proj1_sig k0) (H5 k0)) k H22 H27))))) H28)).
simpl.
suff: ((proj1_sig (H37 M N k H25)) = (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (M + proj1_sig k0) (H5 k0)) k H22 H27))).
move=> H29.
rewrite H29.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N k H25))) (proj1_sig (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (M + proj1_sig k0) (H5 k0)) k H22 H27))) M).
rewrite (proj2_sig (H37 M N k H25)).
rewrite {1} (proj2_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (M + proj1_sig k0) (H5 k0)) k H22 H27)).
reflexivity.
move=> H28.
apply False_ind.
apply (lt_not_le (M + proj1_sig (proj1_sig (fst d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | n < N} => exist (fun n : nat => n < M + N) (M + proj1_sig k0) (H5 k0)) k H22 H27)))) M H28).
apply le_plus_l.
move=> H27.
apply False_ind.
apply H27.
suff: (proj1_sig k - M < N).
move=> H28.
exists (exist (fun (n : nat) => (n < N)) (proj1_sig k - M) H28).
apply sig_map.
simpl.
rewrite (le_plus_minus_r M (proj1_sig k) H25).
reflexivity.
apply (plus_lt_reg_l (proj1_sig k - M) N M).
rewrite (le_plus_minus_r M (proj1_sig k) H25).
apply (proj2_sig k).
move=> H25.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N)}), exist (fun s : nat => (s < M)) (proj1_sig k) H25 = c l)).
move=> H26.
elim (excluded_middle_informative (exists (l0 : {n : nat | (n < N)}), k = exist (fun n : nat => (n < M + N)) (proj1_sig (c l0)) (H4 (c l0)))).
move=> H27.
elim (excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun n : nat => (n < M + N)) (proj1_sig (c (proj1_sig (snd d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (proj1_sig (c k0)) (H4 (c k0))) k H23 H27))))) (H4 (c (proj1_sig (snd d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (proj1_sig (c k0)) (H4 (c k0))) k H23 H27))))) = exist (fun n : nat => (n < M + N)) (M + proj1_sig l) (H5 l))).
move=> H28.
apply False_ind.
elim H28.
move=> l H29.
apply (lt_irrefl M).
apply (le_trans (S M) (S (M + proj1_sig l)) M).
apply le_n_S.
apply le_plus_l.
suff: ((M + proj1_sig l) = proj1_sig (exist (fun n : nat => (n < M + N)) (M + proj1_sig l) (H5 l))).
move=> H30.
rewrite H30.
rewrite - H29.
apply (proj2_sig (c (proj1_sig (snd d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (proj1_sig (c k0)) (H4 (c k0))) k H23 H27))))).
reflexivity.
move=> H28.
simpl.
elim (le_lt_dec M (proj1_sig (c (proj1_sig (snd d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (proj1_sig (c k0)) (H4 (c k0))) k H23 H27)))))).
move=> H29.
apply False_ind.
apply (le_not_lt M (proj1_sig (c (proj1_sig (snd d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | n < N} => exist (fun n : nat => n < M + N) (proj1_sig (c k0)) (H4 (c k0))) k H23 H27))))) H29 (proj2_sig (c (proj1_sig (snd d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | n < N} => exist (fun n : nat => n < M + N) (proj1_sig (c k0)) (H4 (c k0))) k H23 H27)))))).
move=> H29.
elim (excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig (c (proj1_sig (snd d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (proj1_sig (c k0)) (H4 (c k0))) k H23 H27))))) H29 = c l)).
move=> H30.
apply sig_map.
simpl.
suff: ((proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig (c (proj1_sig (snd d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | n < N} => exist (fun n : nat => n < M + N) (proj1_sig (c k0)) (H4 (c k0))) k H23 H27))))) H29) H20 H30)) = (proj1_sig (snd d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (proj1_sig (c k0)) (H4 (c k0))) k H23 H27)))).
move=> H31.
rewrite H31.
suff: ((proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) H25) H24 H26)) = (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | n < N} => exist (fun n : nat => n < M + N) (proj1_sig (c k0)) (H4 (c k0))) k H23 H27))).
move=> H32.
rewrite H32.
reflexivity.
apply H20.
rewrite - (proj2_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) H25) H24 H26)).
apply sig_map.
simpl.
rewrite {1} (proj2_sig (H16 N (M + N) (fun k0 : {n : nat | n < N} => exist (fun n : nat => n < M + N) (proj1_sig (c k0)) (H4 (c k0))) k H23 H27)).
reflexivity.
apply H20.
rewrite - (proj2_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig (c (proj1_sig (snd d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (proj1_sig (c k0)) (H4 (c k0))) k H23 H27))))) H29) H20 H30)).
apply sig_map.
reflexivity.
move=> H30.
apply False_ind.
apply H30.
exists (proj1_sig (snd d) (proj1_sig (H16 N (M + N) (fun k0 : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (proj1_sig (c k0)) (H4 (c k0))) k H23 H27))).
apply sig_map.
reflexivity.
move=> H27.
apply False_ind.
apply H27.
elim H26.
move=> l H28.
exists l.
rewrite - H28.
apply sig_map.
reflexivity.
move=> H26.
elim (excluded_middle_informative (exists l0 : {n : nat | (n < N)}, k = exist (fun n : nat => (n < M + N)) (proj1_sig (c l0)) (H4 (c l0)))).
move=> H27.
apply False_ind.
apply H26.
elim H27.
move=> l H28.
exists l.
apply sig_map.
simpl.
rewrite H28.
reflexivity.
move=> H27.
elim (excluded_middle_informative (exists l : {n : nat | (n < N)}, k = exist (fun n : nat => (n < M + N)) (M + proj1_sig l) (H5 l))).
move=> H28.
apply False_ind.
elim H28.
move=> l H29.
apply (lt_irrefl M).
apply (le_trans (S M) (S (proj1_sig k)) M).
apply le_n_S.
rewrite H29.
apply le_plus_l.
apply H25.
move=> H28.
elim (le_lt_dec M (proj1_sig k)).
move=> H29.
apply False_ind.
apply (le_not_lt M (proj1_sig k) H29 H25).
move=> H29.
elim (excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) H29 = c l)).
move=> H30.
apply False_ind.
apply H26.
elim H30.
move=> l H31.
exists l.
suff: (H25 = H29).
move=> H32.
rewrite H32.
apply H31.
apply proof_irrelevance.
move=> H30.
reflexivity.
move=> H24.
apply False_ind.
apply (H24 H20).
move=> k1 k2 H23.
apply H20.
apply sig_map.
suff: (proj1_sig (c k1) = proj1_sig (exist (fun n : nat => (n < M + N)) (proj1_sig (c k1)) (H4 (c k1)))).
move=> H24.
rewrite H24.
rewrite H23.
reflexivity.
reflexivity.
move=> k1 k2 H22.
apply sig_map.
apply (plus_reg_l (proj1_sig k1) (proj1_sig k2) M).
suff: ((M + proj1_sig k1) = proj1_sig (exist (fun n : nat => (n < M + N)) (M + proj1_sig k1) (H5 k1))).
move=> H23.
rewrite H23.
rewrite H22.
reflexivity.
reflexivity.
exists (fun k : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k) with
  | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (c (proj1_sig (H37 M N k b)))) (H4 (c (proj1_sig (H37 M N k b))))
  | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = c l) with
    | left c0 => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) b) H20 c0))) (H5 (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) b) H20 c0)))
    | right _ => k
  end
end).
suff: (forall (x : {n : nat | (n < M + N)}), Basics.compose (fun k : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k) with
  | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (c (proj1_sig (H37 M N k b)))) (H4 (c (proj1_sig (H37 M N k b))))
  | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = c l) with
    | left c0 => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) b) H20 c0))) (H5 (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) b) H20 c0)))
    | right _ => k
  end
end) (fun k : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k) with
  | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (c (proj1_sig (H37 M N k b)))) (H4 (c (proj1_sig (H37 M N k b))))
  | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = c l) with
    | left c0 => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) b) H20 c0))) (H5 (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) b) H20 c0)))
    | right _ => k
  end
end) x = x).
move=> H21.
apply conj.
apply H21.
apply H21.
move=> k.
unfold Basics.compose.
elim (le_lt_dec M (proj1_sig k)).
move=> H21.
simpl.
elim (le_lt_dec M (proj1_sig (c (proj1_sig (H37 M N k H21))))).
move=> H22.
apply False_ind.
apply (le_not_lt M (proj1_sig (c (proj1_sig (H37 M N k H21)))) H22 (proj2_sig (c (proj1_sig (H37 M N k H21))))).
move=> H22.
elim (excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig (c (proj1_sig (H37 M N k H21)))) H22 = c l)).
move=> H23.
apply sig_map.
simpl.
suff: ((proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig (c (proj1_sig (H37 M N k H21)))) H22) H20 H23)) = (proj1_sig (H37 M N k H21))).
move=> H24.
rewrite H24.
apply (proj2_sig (H37 M N k H21)).
apply H20.
rewrite - (proj2_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig (c (proj1_sig (H37 M N k H21)))) H22) H20 H23)).
apply sig_map.
reflexivity.
move=> H23.
apply False_ind.
apply H23.
exists (proj1_sig (H37 M N k H21)).
apply sig_map.
reflexivity.
move=> H21.
elim (excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) H21 = c l)).
move=> H22.
simpl.
elim (le_lt_dec M (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) H21) H20 H22)))).
move=> H23.
apply sig_map.
simpl.
suff: ((proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) H21) H20 H22))) (H5 (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) H21) H20 H22)))) H23)) = (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) H21) H20 H22))).
move=> H24.
rewrite H24.
rewrite - (proj2_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) H21) H20 H22)).
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) H21) H20 H22))) (H5 (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) H21) H20 H22)))) H23))) (proj1_sig (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) H21) H20 H22))) M).
apply (proj2_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) H21) H20 H22))) (H5 (proj1_sig (H3 c (exist (fun s : nat => (s < M)) (proj1_sig k) H21) H20 H22)))) H23)).
move=> H23.
apply False_ind.
apply (lt_irrefl M).
apply (le_trans (S M) (S (M + proj1_sig (proj1_sig (H3 c (exist (fun s : nat => s < M) (proj1_sig k) H21) H20 H22)))) M).
apply le_n_S.
apply le_plus_l.
apply H23.
move=> H22.
elim (le_lt_dec M (proj1_sig k)).
move=> H23.
apply False_ind.
apply (le_not_lt M (proj1_sig k) H23 H21).
move=> H23.
elim (excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) H23 = c l)).
move=> H24.
apply False_ind.
apply H22.
suff: (H21 = H23).
move=> H25.
rewrite H25.
apply H24.
apply proof_irrelevance.
move=> H24.
reflexivity.
elim H8.
move=> c0 H20 H21 k1 k2 H22.
apply sig_map.
elim (le_or_lt (proj1_sig k1) (proj1_sig k2)).
move=> H23.
elim (le_lt_or_eq (proj1_sig k1) (proj1_sig k2) H23).
move=> H24.
apply False_ind.
apply (lt_irrefl (proj1_sig (c0 k1))).
rewrite {2} H22.
apply (H20 k1 k2 H24).
apply.
move=> H23.
apply False_ind.
apply (lt_irrefl (proj1_sig (c0 k1))).
rewrite {1} H22.
apply (H20 k2 k1 H23).
move=> N1.
elim.
move=> P H19 H20.
suff: (P = PermutationID N1).
move=> H21.
rewrite H21.
rewrite (PermutationIDParity N1).
apply (Fmul_I_r f (FI f)).
apply sig_map.
apply functional_extensionality.
move=> k.
simpl.
apply sig_map.
elim (le_or_lt (proj1_sig (proj1_sig P k)) (proj1_sig k)).
move=> H21.
elim (le_lt_or_eq (proj1_sig (proj1_sig P k)) (proj1_sig k) H21).
move=> H22.
apply False_ind.
suff: (In {n : nat | (n < N1)} (fun (k : {n : nat | (n < N1)}) => (proj1_sig (proj1_sig P k) < proj1_sig k)) k).
rewrite (cardinal_elim {n : nat | (n < N1)} (fun (k : {n : nat | (n < N1)}) => (proj1_sig (proj1_sig P k) < proj1_sig k)) O H20).
elim.
apply H22.
apply.
move=> H21.
apply False_ind.
suff: (In {n : nat | (n < N1)} (fun (k : {n : nat | (n < N1)}) => (proj1_sig (proj1_sig P k) < proj1_sig k)) (proj1_sig P k)).
rewrite (cardinal_elim {n : nat | (n < N1)} (fun (k : {n : nat | (n < N1)}) => (proj1_sig (proj1_sig P k) < proj1_sig k)) O H20).
elim.
unfold In.
rewrite (H19 k).
apply H21.
move=> n H19 P H20 H21.
elim (cardinal_invert {n : nat | (n < N1)} (fun (k : {n : nat | (n < N1)}) => (proj1_sig (proj1_sig P k) < proj1_sig k)) (S n) H21).
move=> W.
elim.
move=> w H22.
rewrite - (PermutationCompose_O_l N1 P).
rewrite - (PermutationCompose_inv_l N1 (PermutationSwap N1 w (proj1_sig P w))).
rewrite (PermutationCompose_assoc N1).
rewrite (PermutationComposeParity N1).
rewrite (PermutationInvParity N1).
rewrite (PermutationSwapParity N1).
suff: (match ParityXOR ON (PermutationParity N1 (PermutationCompose N1 (PermutationSwap N1 w (proj1_sig P w)) P)) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end = Fmul f (Fopp f (FI f)) match (PermutationParity N1 (PermutationCompose N1 (PermutationSwap N1 w (proj1_sig P w)) P)) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end).
move=> H23.
rewrite H23.
simpl.
rewrite - (Fmul_assoc f (Fmul f (PowF f (Fopp f (FI f)) n) (Fopp f (FI f)))).
rewrite (Fmul_assoc f (PowF f (Fopp f (FI f)) n) (Fopp f (FI f))).
rewrite (Fmul_opp_opp f (FI f) (FI f)).
rewrite (Fmul_I_r f (FI f)).
rewrite (Fmul_I_r f).
apply H19.
move=> k.
unfold PermutationCompose.
unfold Basics.compose.
simpl.
elim (excluded_middle_informative (proj1_sig P k = w)).
move=> H24.
elim (excluded_middle_informative (proj1_sig P (proj1_sig P w) = w)).
move=> H25.
rewrite - H24.
apply (H20 k).
move=> H25.
apply False_ind.
apply H25.
apply (H20 w).
move=> H24.
elim (excluded_middle_informative (proj1_sig P k = proj1_sig P w)).
move=> H25.
elim (excluded_middle_informative (proj1_sig P w = w)).
move=> H26.
apply False_ind.
apply (lt_irrefl (proj1_sig (proj1_sig P w))).
rewrite {2} H26.
suff: (In {n : nat | (n < N1)} (fun (k : {n : nat | (n < N1)}) => (proj1_sig (proj1_sig P k) < proj1_sig k)) w).
apply.
rewrite (proj1 H22).
right.
apply (In_singleton {n : nat | (n < N1)} w).
move=> H26.
elim (excluded_middle_informative (proj1_sig P w = proj1_sig P w)).
move=> H27.
apply (BijInj {n : nat | (n < N1)} {n : nat | (n < N1)} (proj1_sig P) (proj2_sig P)).
rewrite H25.
reflexivity.
move=> H27.
apply False_ind.
apply H27.
reflexivity.
move=> H25.
elim (excluded_middle_informative (proj1_sig P (proj1_sig P k) = w)).
rewrite (H20 k).
move=> H26.
apply False_ind.
apply H25.
rewrite H26.
reflexivity.
move=> H26.
elim (excluded_middle_informative (proj1_sig P (proj1_sig P k) = proj1_sig P w)).
move=> H27.
apply False_ind.
apply (H24 (BijInj {n : nat | (n < N1)} {n : nat | (n < N1)} (proj1_sig P) (proj2_sig P) (proj1_sig P k) w H27)).
move=> H27.
apply (H20 k).
suff: ((fun (k : {n0 : nat | (n0 < N1)}) => (proj1_sig (proj1_sig (PermutationCompose N1 (PermutationSwap N1 w (proj1_sig P w)) P) k) < proj1_sig k)) = W).
move=> H24.
rewrite H24.
apply (proj2 (proj2 H22)).
apply Extensionality_Ensembles.
apply conj.
move=> u.
unfold In.
unfold PermutationCompose.
unfold Basics.compose.
unfold PermutationSwap.
simpl.
elim (excluded_middle_informative (proj1_sig P u = w)).
move=> H24.
rewrite - (H20 u).
rewrite H24.
move=> H25.
apply False_ind.
apply (lt_irrefl (proj1_sig (proj1_sig P w)) H25).
move=> H24.
elim (excluded_middle_informative (proj1_sig P u = proj1_sig P w)).
move=> H25 H26.
apply False_ind.
apply (lt_irrefl (proj1_sig u)).
suff: (u = w).
move=> H27.
rewrite {1} H27.
apply H26.
apply (BijInj {n : nat | (n < N1)} {n : nat | (n < N1)} (proj1_sig P) (proj2_sig P) u w H25).
move=> H25 H26.
suff: (proj1_sig P u <> proj1_sig P w).
suff: (In {n : nat | (n < N1)} (fun (k : {n : nat | (n < N1)}) => (proj1_sig (proj1_sig P k) < proj1_sig k)) u).
rewrite (proj1 H22).
elim.
move=> u0 H27 H28.
apply H27.
move=> u0.
elim.
move=> H27.
apply False_ind.
apply H27.
reflexivity.
apply H26.
apply H25.
move=> u H24.
unfold PermutationCompose.
unfold Basics.compose.
unfold PermutationSwap.
simpl.
unfold In.
elim (excluded_middle_informative (proj1_sig P u = w)).
move=> H25.
apply False_ind.
apply (lt_irrefl (proj1_sig w)).
apply (lt_trans (proj1_sig w) (proj1_sig (proj1_sig P w)) (proj1_sig w)).
rewrite - H25.
rewrite (H20 u).
suff: (In {n : nat | (n < N1)} (fun (k : {n : nat | (n < N1)}) => (proj1_sig (proj1_sig P k) < proj1_sig k)) u).
apply.
rewrite (proj1 H22).
left.
apply H24.
suff: (In {n : nat | (n < N1)} (fun (k : {n : nat | (n < N1)}) => (proj1_sig (proj1_sig P k) < proj1_sig k)) w).
apply.
rewrite (proj1 H22).
right.
apply (In_singleton {n : nat | (n < N1)} w).
move=> H25.
elim (excluded_middle_informative (proj1_sig P u = proj1_sig P w)).
move=> H26.
apply False_ind.
apply (proj1 (proj2 H22)).
suff: (u = w).
move=> H27.
rewrite - H27.
apply H24.
apply (BijInj {n : nat | (n < N1)} {n : nat | (n < N1)} (proj1_sig P) (proj2_sig P) u w H26).
move=> H26.
suff: (In {n : nat | (n < N1)} (fun (k : {n : nat | (n < N1)}) => (proj1_sig (proj1_sig P k) < proj1_sig k)) u).
apply.
rewrite (proj1 H22).
left.
apply H24.
elim (PermutationParity N1 (PermutationCompose N1 (PermutationSwap N1 w (proj1_sig P w)) P)).
rewrite (Fmul_opp_opp f (FI f) (FI f)).
rewrite (Fmul_I_r f (FI f)).
reflexivity.
rewrite (Fmul_I_r f (Fopp f (FI f))).
reflexivity.
move=> H23.
apply (lt_irrefl (proj1_sig w)).
rewrite {1} H23.
suff: (In {n : nat | (n < N1)} (fun (k : {n : nat | (n < N1)}) => (proj1_sig (proj1_sig P k) < proj1_sig k)) w).
apply.
rewrite (proj1 H22).
right.
apply (In_singleton {n : nat | (n < N1)} w).
suff: (forall (N1 N2 : nat) (f : {n : nat | (n < N1)} -> {n : nat | (n < N2)}) (H : Injective f), (forall (p q : {n : nat | (n < N1)}), (proj1_sig p < proj1_sig q) -> (proj1_sig (f p) < proj1_sig (f q))) -> forall (m : nat) (P : Permutation N1), (m <= N1) -> (forall (k : {n : nat | (n < N1)}), (proj1_sig k >= m) -> proj1_sig P k = k) -> PermutationParity N1 P = PermutationParity N2 (exist Bijective (fun (k : {n : nat | (n < N2)}) => match excluded_middle_informative (exists l : {n : nat | (n < N1)}, k = f l) with
  | left H0 => f (proj1_sig P (proj1_sig (H16 N1 N2 f k H H0)))
  | right _ => k
end) (H17 N1 N2 f P H))).
move=> H18 N1 N2 g P H19 H20.
apply (H18 N1 N2 g H19 H20 N1 P).
apply (le_n N1).
move=> k H21.
apply False_ind.
apply (le_not_lt N1 (proj1_sig k) H21 (proj2_sig k)).
move=> N1 N2 g H18 H19.
elim.
move=> P H20 H21.
suff: ((exist Bijective (fun (k : {n : nat | (n < N2)}) => match excluded_middle_informative (exists l : {n : nat | (n < N1)}, k = g l) with
  | left H0 => g (proj1_sig P (proj1_sig (H16 N1 N2 g k H18 H0)))
  | right _ => k
end) (H17 N1 N2 g P H18)) = PermutationID N2).
move=> H22.
rewrite H22.
suff: (P = PermutationID N1).
move=> H23.
rewrite H23.
rewrite (PermutationIDParity N2).
apply (PermutationIDParity N1).
apply sig_map.
apply functional_extensionality.
apply (fun (k : {n : nat | (n < N1)}) => H21 k (le_0_n (proj1_sig k))).
apply sig_map.
apply functional_extensionality.
move=> k.
simpl.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N1)}), k = g l)).
move=> H22.
rewrite (H21 (proj1_sig (H16 N1 N2 g k H18 H22)) (le_0_n (proj1_sig (proj1_sig (H16 N1 N2 g k H18 H22))))).
rewrite - (proj2_sig (H16 N1 N2 g k H18 H22)).
reflexivity.
move=> H22.
reflexivity.
move=> n H20 P H21 H22.
elim (classic (proj1_sig P (exist (fun (k : nat) => (k < N1)) n H21) = (exist (fun (k : nat) => (k < N1)) n H21))).
move=> H23.
apply (H20 P (le_trans n (S n) N1 (le_S n n (le_n n)) H21)).
move=> k H24.
elim (le_lt_or_eq n (proj1_sig k) H24).
move=> H25.
apply (H22 k H25).
move=> H25.
suff: (k = (exist (fun k : nat => (k < N1)) n H21)).
move=> H26.
rewrite H26.
apply H23.
apply sig_map.
rewrite - H25.
reflexivity.
move=> H23.
suff: (proj1_sig (proj1_sig P (exist (fun k : nat => (k < N1)) n H21)) < n).
move=> H24.
suff: (PermutationParity N1 (PermutationCompose N1 (PermutationSwap N1 (proj1_sig P (exist (fun (k : nat) => k < N1) n H21)) (exist (fun k : nat => k < N1) n H21)) P) = PermutationParity N2 (PermutationCompose N2 (PermutationSwap N2 (g (proj1_sig P (exist (fun (k : nat) => k < N1) n H21))) (g (exist (fun k : nat => k < N1) n H21))) (exist Bijective (fun k : {n0 : nat | (n0 < N2)} => match excluded_middle_informative (exists l : {n0 : nat | (n0 < N1)}, k = g l) with
  | left H0 => g (proj1_sig P (proj1_sig (H16 N1 N2 g k H18 H0)))
  | right _ => k
end) (H17 N1 N2 g P H18)))).
rewrite (PermutationComposeParity N1).
rewrite (PermutationComposeParity N2).
rewrite (PermutationSwapParity N1).
rewrite (PermutationSwapParity N2).
elim (PermutationParity N2 (exist Bijective (fun k : {n0 : nat | (n0 < N2)} => match excluded_middle_informative (exists l : {n0 : nat | (n0 < N1)}, k = g l) with
  | left H0 => g (proj1_sig P (proj1_sig (H16 N1 N2 g k H18 H0)))
  | right _ => k
end) (H17 N1 N2 g P H18))).
elim (PermutationParity N1 P).
move=> H25.
reflexivity.
simpl.
move=> H25.
rewrite H25.
reflexivity.
elim (PermutationParity N1 P).
simpl.
move=> H25.
rewrite H25.
reflexivity.
move=> H25.
reflexivity.
move=> H25.
apply H23.
apply H18.
apply H25.
apply H23.
suff: ((PermutationCompose N2 (PermutationSwap N2 (g (proj1_sig P (exist (fun k : nat => (k < N1)) n H21))) (g (exist (fun k : nat => (k < N1)) n H21))) (exist Bijective (fun k : {n0 : nat | (n0 < N2)} => match excluded_middle_informative (exists l : {n0 : nat | (n0 < N1)}, k = g l) with
  | left H0 => g (proj1_sig P (proj1_sig (H16 N1 N2 g k H18 H0)))
  | right _ => k
end) (H17 N1 N2 g P H18))) = (exist Bijective (fun k : {n : nat | (n < N2)} => match excluded_middle_informative (exists l : {n : nat | (n < N1)}, k = g l) with
  | left H0 => g (proj1_sig (PermutationCompose N1 (PermutationSwap N1 (proj1_sig P (exist (fun k0 : nat => (k0 < N1)) n H21)) (exist (fun k0 : nat => (k0 < N1)) n H21)) P) (proj1_sig (H16 N1 N2 g k H18 H0)))
  | right _ => k
end) (H17 N1 N2 g (PermutationCompose N1 (PermutationSwap N1 (proj1_sig P (exist (fun k : nat => (k < N1)) n H21)) (exist (fun k : nat => (k < N1)) n H21)) P) H18))).
move=> H25.
rewrite H25.
apply (H20 (PermutationCompose N1 (PermutationSwap N1 (proj1_sig P (exist (fun k : nat => (k < N1)) n H21)) (exist (fun k : nat => (k < N1)) n H21)) P)).
apply (le_trans n (S n) N1 (le_S n n (le_n n)) H21).
move=> k H26.
unfold PermutationCompose.
unfold PermutationSwap.
unfold Basics.compose.
simpl.
elim (excluded_middle_informative (proj1_sig P k = proj1_sig P (exist (fun (l : nat) => (l < N1)) n H21))).
move=> H27.
apply (BijInj {l : nat | (l < N1)} {l : nat | (l < N1)} (proj1_sig P) (proj2_sig P)).
rewrite H27.
reflexivity.
elim (le_lt_or_eq n (proj1_sig k)).
move=> H27 H28.
elim (excluded_middle_informative (proj1_sig P k = exist (fun k0 : nat => (k0 < N1)) n H21)).
move=> H29.
apply False_ind.
apply (lt_irrefl (proj1_sig (proj1_sig P k))).
rewrite {1} H29.
rewrite (H22 k H27).
apply H27.
move=> H29.
apply (H22 k H27).
move=> H27 H28.
apply False_ind.
apply H28.
suff: ((exist (fun (l : nat) => (l < N1)) n H21) = k).
move=> H29.
rewrite H29.
reflexivity.
apply sig_map.
apply H27.
apply H26.
apply sig_map.
unfold PermutationCompose.
unfold PermutationSwap.
unfold Basics.compose.
simpl.
apply functional_extensionality.
move=> k.
elim (excluded_middle_informative (exists (l : {n0 : nat | (n0 < N1)}), k = g l)).
move=> H25.
elim (excluded_middle_informative (proj1_sig P (proj1_sig (H16 N1 N2 g k H18 H25)) = proj1_sig P (exist (fun k0 : nat => (k0 < N1)) n H21))).
move=> H26.
elim (excluded_middle_informative (g (proj1_sig P (proj1_sig (H16 N1 N2 g k H18 H25))) = g (proj1_sig P (exist (fun k0 : nat => (k0 < N1)) n H21)))).
move=> H27.
reflexivity.
move=> H27.
apply False_ind.
apply H27.
rewrite H26.
reflexivity.
move=> H26.
elim (excluded_middle_informative (proj1_sig P (proj1_sig (H16 N1 N2 g k H18 H25)) = exist (fun k0 : nat => (k0 < N1)) n H21)).
move=> H27.
elim (excluded_middle_informative (g (proj1_sig P (proj1_sig (H16 N1 N2 g k H18 H25))) = g (proj1_sig P (exist (fun k0 : nat => (k0 < N1)) n H21)))).
move=> H28.
rewrite - H28.
rewrite H27.
reflexivity.
move=> H28.
elim (excluded_middle_informative (g (proj1_sig P (proj1_sig (H16 N1 N2 g k H18 H25))) = g (exist (fun k0 : nat => (k0 < N1)) n H21))).
move=> H29.
reflexivity.
move=> H29.
apply False_ind.
apply H29.
rewrite H27.
reflexivity.
move=> H27.
elim (excluded_middle_informative (g (proj1_sig P (proj1_sig (H16 N1 N2 g k H18 H25))) = g (proj1_sig P (exist (fun k0 : nat => (k0 < N1)) n H21)))).
move=> H28.
apply False_ind.
apply H26.
apply H18.
apply H28.
move=> H28.
elim (excluded_middle_informative (g (proj1_sig P (proj1_sig (H16 N1 N2 g k H18 H25))) = g (exist (fun k0 : nat => (k0 < N1)) n H21))).
move=> H29.
apply False_ind.
apply H27.
apply H18.
apply H29.
move=> H29.
reflexivity.
move=> H25.
elim (excluded_middle_informative (k = g (proj1_sig P (exist (fun k0 : nat => (k0 < N1)) n H21)))).
move=> H26.
apply False_ind.
apply H25.
exists (proj1_sig P (exist (fun k0 : nat => (k0 < N1)) n H21)).
apply H26.
move=> H26.
elim (excluded_middle_informative (k = g (exist (fun k0 : nat => (k0 < N1)) n H21))).
move=> H27.
apply False_ind.
apply H25.
exists (exist (fun k0 : nat => (k0 < N1)) n H21).
apply H27.
move=> H27.
reflexivity.
elim (nat_total_order (proj1_sig (proj1_sig P (exist (fun k : nat => (k < N1)) n H21))) n).
apply.
move=> H24.
apply False_ind.
apply H23.
apply (BijInj {n : nat | (n < N1)} {n : nat | (n < N1)} (proj1_sig P) (proj2_sig P)).
apply (H22 (proj1_sig P (exist (fun k : nat => (k < N1)) n H21)) H24).
move=> H24.
apply H23.
apply sig_map.
apply H24.
move=> N1 N2 g P H17.
elim (proj2_sig P).
move=> q H18.
exists (fun (k : {n : nat | (n < N2)}) => match excluded_middle_informative (exists l : {n : nat | (n < N1)}, k = g l) with
  | left H0 => g (q (proj1_sig (H16 N1 N2 g k H17 H0)))
  | right _ => k
end).
apply conj.
move=> k.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N1)}), k = g l)).
move=> H19.
elim (excluded_middle_informative (exists l : {n : nat | (n < N1)}, g (proj1_sig P (proj1_sig (H16 N1 N2 g k H17 H19))) = g l)).
move=> H20.
suff: ((proj1_sig (H16 N1 N2 g (g (proj1_sig P (proj1_sig (H16 N1 N2 g k H17 H19)))) H17 H20)) = (proj1_sig P (proj1_sig (H16 N1 N2 g k H17 H19)))).
move=> H21.
rewrite H21.
rewrite (proj1 H18 (proj1_sig (H16 N1 N2 g k H17 H19))).
rewrite - (proj2_sig (H16 N1 N2 g k H17 H19)).
reflexivity.
apply H17.
rewrite - (proj2_sig (H16 N1 N2 g (g (proj1_sig P (proj1_sig (H16 N1 N2 g k H17 H19)))) H17 H20)).
reflexivity.
move=> H20.
apply False_ind.
apply H20.
exists (proj1_sig P (proj1_sig (H16 N1 N2 g k H17 H19))).
reflexivity.
move=> H19.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N1)}), k = g l)).
move=> H20.
apply False_ind.
apply (H19 H20).
move=> H20.
reflexivity.
move=> k.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N1)}), k = g l)).
move=> H19.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N1)}), g (q (proj1_sig (H16 N1 N2 g k H17 H19))) = g l)).
move=> H20.
suff: ((proj1_sig (H16 N1 N2 g (g (q (proj1_sig (H16 N1 N2 g k H17 H19)))) H17 H20)) = (q (proj1_sig (H16 N1 N2 g k H17 H19)))).
move=> H21.
rewrite H21.
rewrite (proj2 H18 (proj1_sig (H16 N1 N2 g k H17 H19))).
rewrite - (proj2_sig (H16 N1 N2 g k H17 H19)).
reflexivity.
apply H17.
rewrite - (proj2_sig (H16 N1 N2 g (g (q (proj1_sig (H16 N1 N2 g k H17 H19)))) H17 H20)).
reflexivity.
move=> H20.
apply False_ind.
apply H20.
exists (q (proj1_sig (H16 N1 N2 g k H17 H19))).
reflexivity.
move=> H19.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N1)}), k = g l)).
move=> H20.
apply False_ind.
apply (H19 H20).
move=> H20.
reflexivity.
move=> N1 N2 p k H16 H17.
apply constructive_definite_description.
apply (unique_existence (fun (m : {n : nat | (n < N1)}) => k = p m)).
apply conj.
apply H17.
move=> k1 k2 H18 H19.
apply H16.
rewrite - H18.
apply H19.
apply H14.
apply H14.
rewrite (MySumF2Pair (Permutation N) (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (FPCM f) (fun (u v : Permutation N) => Fmul f (Fmul f match PermutationParity N u with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => A k (c (proj1_sig u k))))) (Fmul f match PermutationParity N v with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => B (c k) (proj1_sig v k)))))).
unfold Determinant at 1.
apply (FiniteSetInduction (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (fun (E : {X : Ensemble (Permutation N) | Finite (Permutation N) X}) => Fmul f (MySumF2 (Permutation N) E (FPCM f) (fun P : Permutation N => Fmul f match PermutationParity N P with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => A k (c (proj1_sig P k)))))) (Determinant f N (fun x y : {n : nat | (n < N)} => B (c x) y)) = MySumF2 (Permutation N) E (FPCM f) (fun u : Permutation N => MySumF2 (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (FPCM f) (fun v : Permutation N => Fmul f (Fmul f match PermutationParity N u with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => A k (c (proj1_sig u k))))) (Fmul f match PermutationParity N v with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)} => B (c k) (proj1_sig v k)))))))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Fmul_O_l f).
move=> D d H11 H12 H13 H14.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite (Fmul_add_distr_r f).
rewrite H14.
apply (Fadd_eq_compat_l f).
unfold Determinant.
apply (FiniteSetInduction (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Fmul_O_r f).
move=> E e H15 H16 H17 H18.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite (Fmul_add_distr_l f).
rewrite H18.
reflexivity.
apply H17.
apply H17.
apply H13.
apply H13.
apply H9.
apply H9.
suff: (forall (u : (({n : nat | (n < N)} -> {n : nat | (n < M)}) * (Permutation N * Permutation N))), In (({n : nat | (n < N)} -> {n : nat | (n < M)}) * (Permutation N * Permutation N)) (proj1_sig (FinitePair ({n : nat | (n < N)} -> {n : nat | (n < M)}) (Permutation N * Permutation N) (FiniteIntersection ({n : nat | (n < N)} -> {n : nat | (n < M)}) (exist (Finite ({n : nat | (n < N)} -> {n : nat | (n < M)})) (Full_set ({n : nat | (n < N)} -> {n : nat | (n < M)})) (CountPowFinite N M)) (fun r : {n : nat | (n < N)} -> {n : nat | (n < M)} => forall p q : {n : nat | (n < N)}, (proj1_sig p < proj1_sig q) -> (proj1_sig (r p) < proj1_sig (r q)))) (FinitePair (Permutation N) (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))))) u -> Injective (fst u)).
move=> H7 u1 u2 H8 H9 H10.
suff: (proj1_sig (exist Bijective match excluded_middle_informative (Injective (fst u1)) with
  | left a => fun k : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k) with
    | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (fst u1 (proj1_sig (fst (snd u1)) (proj1_sig (H37 M N k b))))) (H4 (fst u1 (proj1_sig (fst (snd u1)) (proj1_sig (H37 M N k b)))))
    | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = fst u1 l) with
      | left c => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd (snd u1)) (proj1_sig (H3 (fst u1) (exist (fun s : nat => s < M) (proj1_sig k) b) a c)))) (H5 (proj1_sig (snd (snd u1)) (proj1_sig (H3 (fst u1) (exist (fun s : nat => (s < M)) (proj1_sig k) b) a c))))
      | right _ => k
    end
  end
  | right _ => fun k : {n : nat | (n < M + N)} => k
end (H6 u1)) = proj1_sig (exist Bijective match excluded_middle_informative (Injective (fst u2)) with
  | left a => fun k : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k) with
    | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (fst u2 (proj1_sig (fst (snd u2)) (proj1_sig (H37 M N k b))))) (H4 (fst u2 (proj1_sig (fst (snd u2)) (proj1_sig (H37 M N k b)))))
    | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = fst u2 l) with
      | left c => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd (snd u2)) (proj1_sig (H3 (fst u2) (exist (fun s : nat => s < M) (proj1_sig k) b) a c)))) (H5 (proj1_sig (snd (snd u2)) (proj1_sig (H3 (fst u2) (exist (fun s : nat => (s < M)) (proj1_sig k) b) a c))))
      | right _ => k
    end
  end
  | right _ => fun k : {n : nat | (n < M + N)} => k
end (H6 u2))).
simpl.
elim (excluded_middle_informative (Injective (fst u1))).
move=> H11.
elim (excluded_middle_informative (Injective (fst u2))).
move=> H12 H13.
suff: (fst u1 = fst u2).
move=> H14.
apply injective_projections.
apply H14.
apply injective_projections.
apply sig_map.
apply functional_extensionality.
move=> k.
apply H11.
rewrite {2} H14.
apply sig_map.
suff: (proj1_sig (fst u1 (proj1_sig (fst (snd u1)) k)) = let temp := (fun k : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k) with
  | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (fst u1 (proj1_sig (fst (snd u1)) (proj1_sig (H37 M N k b))))) (H4 (fst u1 (proj1_sig (fst (snd u1)) (proj1_sig (H37 M N k b)))))
  | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = fst u1 l) with
    | left c => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd (snd u1)) (proj1_sig (H3 (fst u1) (exist (fun s : nat => s < M) (proj1_sig k) b) H11 c)))) (H5 (proj1_sig (snd (snd u1)) (proj1_sig (H3 (fst u1) (exist (fun s : nat => (s < M)) (proj1_sig k) b) H11 c))))
    | right _ => k
  end
end) in proj1_sig (temp (exist (fun (s : nat) => (s < M + N)) (M + proj1_sig k) (H5 k)))).
move=> H15.
rewrite H15.
rewrite H13.
simpl.
elim (le_lt_dec M (M + proj1_sig k)).
move=> H16.
simpl.
suff: ((proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig k) (H5 k)) H16)) = k).
move=> H17.
rewrite H17.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig k) (H5 k)) H16))) (proj1_sig k) M).
apply (proj2_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig k) (H5 k)) H16)).
move=> H16.
apply False_ind.
apply (lt_irrefl M).
apply (le_trans (S M) (S (M + proj1_sig k)) M).
apply le_n_S.
apply le_plus_l.
apply H16.
simpl.
elim (le_lt_dec M (M + proj1_sig k)).
move=> H15.
simpl.
suff: ((proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig k) (H5 k)) H15)) = k).
move=> H16.
rewrite H16.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig k) (H5 k)) H15))) (proj1_sig k) M).
apply (proj2_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig k) (H5 k)) H15)).
move=> H15.
apply False_ind.
apply (lt_irrefl M).
apply (le_trans (S M) (S (M + proj1_sig k)) M).
apply le_n_S.
apply le_plus_l.
apply H15.
apply sig_map.
apply functional_extensionality.
move=> k.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (snd (snd u1)) k)) (proj1_sig (proj1_sig (snd (snd u2)) k)) M).
suff: ((M + proj1_sig (proj1_sig (snd (snd u1)) k)) = let temp := (fun (k : {n : nat | (n < M + N)}) => match le_lt_dec M (proj1_sig k) with
  | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (fst u1 (proj1_sig (fst (snd u1)) (proj1_sig (H37 M N k b))))) (H4 (fst u1 (proj1_sig (fst (snd u1)) (proj1_sig (H37 M N k b)))))
  | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = fst u1 l) with
    | left c => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd (snd u1)) (proj1_sig (H3 (fst u1) (exist (fun s : nat => s < M) (proj1_sig k) b) H11 c)))) (H5 (proj1_sig (snd (snd u1)) (proj1_sig (H3 (fst u1) (exist (fun s : nat => (s < M)) (proj1_sig k) b) H11 c))))
    | right _ => k
  end
end) in proj1_sig (temp (exist (fun (s : nat) => (s < M + N)) (proj1_sig (fst u1 k)) (H4 (fst u1 k))))).
move=> H15.
rewrite H15.
rewrite H13.
rewrite H14.
simpl.
elim (le_lt_dec M (proj1_sig (fst u2 k))).
move=> H16.
apply False_ind.
apply (le_not_lt M (proj1_sig (fst u2 k)) H16 (proj2_sig (fst u2 k))).
move=> H16.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N)}), exist (fun (s : nat) => (s < M)) (proj1_sig (fst u2 k)) H16 = fst u2 l)).
move=> H17.
suff: (proj1_sig (H3 (fst u2) (exist (fun s : nat => (s < M)) (proj1_sig (fst u2 k)) H16) H12 H17) = k).
move=> H18.
rewrite H18.
reflexivity.
apply H12.
rewrite - (proj2_sig (H3 (fst u2) (exist (fun s : nat => (s < M)) (proj1_sig (fst u2 k)) H16) H12 H17)).
apply sig_map.
reflexivity.
move=> H17.
apply False_ind.
apply H17.
exists k.
apply sig_map.
reflexivity.
simpl.
elim (le_lt_dec M (proj1_sig (fst u1 k))).
move=> H15.
apply False_ind.
apply (le_not_lt M (proj1_sig (fst u1 k)) H15 (proj2_sig (fst u1 k))).
move=> H15.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N)}), exist (fun (s : nat) => (s < M)) (proj1_sig (fst u1 k)) H15 = fst u1 l)).
move=> H16.
suff: ((proj1_sig (H3 (fst u1) (exist (fun s : nat => (s < M)) (proj1_sig (fst u1 k)) H15) H11 H16)) = k).
move=> H17.
rewrite H17.
reflexivity.
apply H11.
rewrite - (proj2_sig (H3 (fst u1) (exist (fun s : nat => (s < M)) (proj1_sig (fst u1 k)) H15) H11 H16)).
apply sig_map.
reflexivity.
move=> H16.
apply False_ind.
apply H16.
exists k.
apply sig_map.
reflexivity.
suff: (forall (p q : {n : nat | (n < N)}), (proj1_sig p < proj1_sig q) -> (proj1_sig (fst u1 p) < proj1_sig (fst u1 q))).
move=> H14.
suff: (forall (p q : {n : nat | (n < N)}), (proj1_sig p < proj1_sig q) -> (proj1_sig (fst u2 p) < proj1_sig (fst u2 q))).
move=> H15.
suff: (Im {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (fun (k : {n : nat | (n < N)}) => proj1_sig (fst u1 k)) = Im {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (fun (k : {n : nat | (n < N)}) => proj1_sig (fst u2 k))).
move=> H16.
suff: (forall (m : nat), (m <= N) -> (forall (k : {n : nat | (n < N)}), (proj1_sig k < m) -> proj1_sig (fst u1 k) = proj1_sig (fst u2 k))).
move=> H17.
apply functional_extensionality.
move=> k.
apply sig_map.
apply (H17 N (le_n N) k (proj2_sig k)).
elim.
move=> H17 k H18.
apply False_ind.
apply (le_not_lt O (proj1_sig k) (le_0_n (proj1_sig k)) H18).
move=> m H17 H18 k H19.
elim (le_lt_or_eq (proj1_sig k) m).
move=> H20.
apply (H17 (le_trans m (S m) N (le_S m m (le_n m)) H18) k H20).
move=> H20.
suff: (Inhabited nat (Intersection nat (Im {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (fun (l : {n : nat | (n < N)}) => proj1_sig (fst u1 l))) (fun (l : nat) => forall (k : {n : nat | (n < N)}), (proj1_sig k < m) -> (proj1_sig (fst u1 k) < l)) )).
move=> H21.
suff: (proj1_sig (fst u1 k) = proj1_sig (min_nat_get (Intersection nat (Im {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (fun (l : {n : nat | (n < N)}) => proj1_sig (fst u1 l))) (fun (l : nat) => forall (k : {n : nat | (n < N)}), (proj1_sig k < m) -> (proj1_sig (fst u1 k) < l)) ) H21)).
move=> H22.
rewrite H22.
suff: (Inhabited nat (Intersection nat (Im {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (fun (l : {n : nat | (n < N)}) => proj1_sig (fst u2 l))) (fun (l : nat) => forall (k : {n : nat | (n < N)}), (proj1_sig k < m) -> (proj1_sig (fst u2 k) < l)) )).
move=> H23.
suff: (proj1_sig (fst u2 k) = proj1_sig (min_nat_get (Intersection nat (Im {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (fun (l : {n : nat | (n < N)}) => proj1_sig (fst u2 l))) (fun (l : nat) => forall (k : {n : nat | (n < N)}), (proj1_sig k < m) -> (proj1_sig (fst u2 k) < l)) ) H23)).
move=> H24.
rewrite H24.
suff: (forall (E1 E2 : Ensemble nat), E1 = E2 -> forall (H1 : Inhabited nat E1) (H2 : Inhabited nat E2), proj1_sig (min_nat_get E1 H1) = proj1_sig (min_nat_get E2 H2)).
apply.
rewrite H16.
suff: ((fun (l : nat) => forall (s : {n : nat | (n < N)}), (proj1_sig s < m) -> (proj1_sig (fst u1 s) < l)) = (fun (l : nat) => forall (s : {n : nat | (n < N)}), (proj1_sig s < m) -> (proj1_sig (fst u2 s) < l))).
move=> H25.
rewrite H25.
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> l H25 s H26.
rewrite - (H17 (le_trans m (S m) N (le_S m m (le_n m)) H18) s H26).
apply (H25 s H26).
move=> l H25 s H26.
rewrite (H17 (le_trans m (S m) N (le_S m m (le_n m)) H18) s H26).
apply (H25 s H26).
move=> E1 E2 H25.
rewrite H25.
move=> H26 H27.
suff: (H26 = H27).
move=> H28.
rewrite H28.
reflexivity.
apply proof_irrelevance.
apply le_antisym.
elim (proj1 (proj2_sig (min_nat_get (Intersection nat (Im {n : nat | n < N} nat (Full_set {n : nat | n < N}) (fun (l : {n : nat | n < N}) => proj1_sig (fst u2 l))) (fun (l : nat) => forall (s : {n : nat | n < N}), proj1_sig s < m -> proj1_sig (fst u2 s) < l)) H23))).
move=> m1.
elim.
move=> l1 H24 m2 H25 H26.
elim (le_or_lt (proj1_sig k) (proj1_sig l1)).
move=> H27.
elim (le_lt_or_eq (proj1_sig k) (proj1_sig l1) H27).
move=> H28.
apply lt_le_weak.
rewrite H25.
apply (H15 k l1 H28).
move=> H28.
suff: (k = l1).
move=> H29.
rewrite H29.
rewrite H25.
apply (le_n (proj1_sig (fst u2 l1))).
apply sig_map.
apply H28.
move=> H27.
apply False_ind.
apply (lt_irrefl m2).
rewrite {1} H25.
apply (H26 l1).
rewrite - H20.
apply H27.
apply (proj2 (proj2_sig (min_nat_get (Intersection nat (Im {n : nat | n < N} nat (Full_set {n : nat | n < N}) (fun l : {n : nat | n < N} => proj1_sig (fst u2 l))) (fun (l : nat) => forall (s : {n : nat | n < N}), proj1_sig s < m -> proj1_sig (fst u2 s) < l)) H23)) (proj1_sig (fst u2 k))).
apply Intersection_intro.
apply (Im_intro {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (fun (l : {n : nat | (n < N)}) => proj1_sig (fst u2 l)) k).
apply (Full_intro {n : nat | (n < N)} k).
reflexivity.
move=> l.
rewrite - H20.
apply (H15 l k).
apply (Inhabited_intro nat (Intersection nat (Im {n : nat | n < N} nat (Full_set {n : nat | n < N}) (fun l : {n : nat | n < N} => proj1_sig (fst u2 l))) (fun (l : nat) => forall (s : {n : nat | n < N}), proj1_sig s < m -> proj1_sig (fst u2 s) < l)) (proj1_sig (fst u2 k))).
apply Intersection_intro.
apply (Im_intro {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (fun (l : {n : nat | (n < N)}) => proj1_sig (fst u2 l)) k).
apply (Full_intro {n : nat | (n < N)} k).
reflexivity.
move=> l.
rewrite - H20.
apply (H15 l k).
apply le_antisym.
elim (proj1 (proj2_sig (min_nat_get (Intersection nat (Im {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (fun (l : {n : nat | (n < N)}) => proj1_sig (fst u1 l))) (fun (l : nat) => forall (s : {n : nat | (n < N)}), (proj1_sig s < m) -> (proj1_sig (fst u1 s) < l))) H21))).
move=> m1.
elim.
move=> l1 H22 m2 H23 H24.
elim (le_or_lt (proj1_sig k) (proj1_sig l1)).
move=> H25.
elim (le_lt_or_eq (proj1_sig k) (proj1_sig l1) H25).
move=> H26.
apply lt_le_weak.
rewrite H23.
apply (H14 k l1 H26).
move=> H26.
suff: (k = l1).
move=> H27.
rewrite H27.
rewrite H23.
apply (le_n (proj1_sig (fst u1 l1))).
apply sig_map.
apply H26.
move=> H25.
apply False_ind.
apply (lt_irrefl m2).
rewrite {1} H23.
apply (H24 l1).
rewrite - H20.
apply H25.
apply (proj2 (proj2_sig (min_nat_get (Intersection nat (Im {n : nat | n < N} nat (Full_set {n : nat | n < N}) (fun l : {n : nat | n < N} => proj1_sig (fst u1 l))) (fun (l : nat) => forall (s : {n : nat | n < N}), proj1_sig s < m -> proj1_sig (fst u1 s) < l)) H21)) (proj1_sig (fst u1 k))).
apply Intersection_intro.
apply (Im_intro {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (fun (l : {n : nat | (n < N)}) => proj1_sig (fst u1 l)) k).
apply (Full_intro {n : nat | (n < N)} k).
reflexivity.
move=> l.
rewrite - H20.
apply (H14 l k).
apply (Inhabited_intro nat (Intersection nat (Im {n : nat | n < N} nat (Full_set {n : nat | n < N}) (fun (l : {n : nat | n < N}) => proj1_sig (fst u1 l))) (fun (l : nat) => forall (s : {n : nat | n < N}), proj1_sig s < m -> proj1_sig (fst u1 s) < l)) (proj1_sig (fst u1 k))).
apply Intersection_intro.
apply (Im_intro {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (fun (l : {n : nat | (n < N)}) => proj1_sig (fst u1 l)) k).
apply (Full_intro {n : nat | (n < N)} k).
reflexivity.
move=> l.
rewrite - H20.
apply (H14 l k).
apply le_S_n.
apply H19.
suff: (Im {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (fun k : {n : nat | (n < N)} => proj1_sig (fst u1 k)) = Im {n : nat | (n < M + N)} nat (fun (k : {n : nat | (n < M + N)}) => (M <= proj1_sig k)) (Basics.compose (fun (k : {n : nat | (n < M + N)}) => proj1_sig k) (fun (k : {n : nat | (n < M + N)}) => match le_lt_dec M (proj1_sig k) with
  | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (fst u1 (proj1_sig (fst (snd u1)) (proj1_sig (H37 M N k b))))) (H4 (fst u1 (proj1_sig (fst (snd u1)) (proj1_sig (H37 M N k b)))))
  | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = fst u1 l) with
    | left c => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd (snd u1)) (proj1_sig (H3 (fst u1) (exist (fun s : nat => s < M) (proj1_sig k) b) H11 c)))) (H5 (proj1_sig (snd (snd u1)) (proj1_sig (H3 (fst u1) (exist (fun s : nat => (s < M)) (proj1_sig k) b) H11 c))))
    | right _ => k
  end
end))).
move=> H16.
rewrite H16.
rewrite H13.
apply Extensionality_Ensembles.
apply conj.
move=> m.
elim.
move=> x H17 y H18.
rewrite H18.
unfold Basics.compose.
unfold In.
apply (Im_intro {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (fun (k : {n : nat | (n < N)}) => proj1_sig (fst u2 k)) (proj1_sig (fst (snd u2)) (proj1_sig (H37 M N x H17)))).
apply (Full_intro {n : nat | (n < N)}).
elim (le_lt_dec M (proj1_sig x)).
move=> H19.
suff: (H19 = H17).
move=> H20.
rewrite H20.
reflexivity.
apply proof_irrelevance.
move=> H19.
apply False_ind.
apply (le_not_lt M (proj1_sig x) H17 H19).
move=> m.
elim.
move=> x H17 y H18.
rewrite H18.
elim (proj2_sig (fst (snd u2))).
move=> invg H19.
apply (Im_intro {n : nat | (n < M + N)} nat (fun (k : {n : nat | (n < M + N)}) => (M <= proj1_sig k)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (fun k : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k) with
  | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (fst u2 (proj1_sig (fst (snd u2)) (proj1_sig (H37 M N k b))))) (H4 (fst u2 (proj1_sig (fst (snd u2)) (proj1_sig (H37 M N k b)))))
  | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = fst u2 l) with
    | left c => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd (snd u2)) (proj1_sig (H3 (fst u2) (exist (fun s : nat => s < M) (proj1_sig k) b) H12 c)))) (H5 (proj1_sig (snd (snd u2)) (proj1_sig (H3 (fst u2) (exist (fun s : nat => (s < M)) (proj1_sig k) b) H12 c))))
    | right _ => k
  end
end)) (exist (fun (s : nat) => (s < M + N)) (M + (proj1_sig (invg x))) (H5 (invg x)))).
apply le_plus_l.
unfold Basics.compose.
simpl.
elim (le_lt_dec M (M + (proj1_sig (invg x)))).
move=> H20.
suff: ((proj1_sig (fst (snd u2)) (proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (invg x)) (H5 (invg x))) H20))) = x).
move=> H21.
rewrite H21.
reflexivity.
suff: ((proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (invg x)) (H5 (invg x))) H20)) = invg x).
move=> H21.
rewrite H21.
apply (proj2 H19 x).
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (invg x)) (H5 (invg x))) H20))) (proj1_sig (invg x)) M).
apply (proj2_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (invg x)) (H5 (invg x))) H20)).
move=> H20.
apply False_ind.
apply (lt_not_le (M + proj1_sig (invg x)) M H20).
apply le_plus_l.
apply Extensionality_Ensembles.
apply conj.
move=> m.
elim.
move=> x H16 y H17.
rewrite H17.
elim (proj2_sig (fst (snd u1))).
move=> invg H18.
apply (Im_intro {n : nat | (n < M + N)} nat (fun (k : {n : nat | (n < M + N)}) => (M <= proj1_sig k)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (fun k : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k) with
  | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (fst u1 (proj1_sig (fst (snd u1)) (proj1_sig (H37 M N k b))))) (H4 (fst u1 (proj1_sig (fst (snd u1)) (proj1_sig (H37 M N k b)))))
  | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = fst u1 l) with
    | left c => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd (snd u1)) (proj1_sig (H3 (fst u1) (exist (fun s : nat => s < M) (proj1_sig k) b) H11 c)))) (H5 (proj1_sig (snd (snd u1)) (proj1_sig (H3 (fst u1) (exist (fun s : nat => (s < M)) (proj1_sig k) b) H11 c))))
    | right _ => k
  end
end)) (exist (fun (s : nat) => (s < M + N)) (M + (proj1_sig (invg x))) (H5 (invg x)))).
apply le_plus_l.
unfold Basics.compose.
simpl.
elim (le_lt_dec M (M + (proj1_sig (invg x)))).
move=> H19.
suff: ((proj1_sig (fst (snd u1)) (proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (invg x)) (H5 (invg x))) H19))) = x).
move=> H20.
rewrite H20.
reflexivity.
suff: ((proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (invg x)) (H5 (invg x))) H19)) = invg x).
move=> H20.
rewrite H20.
apply (proj2 H18 x).
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (invg x)) (H5 (invg x))) H19))) (proj1_sig (invg x)) M).
apply (proj2_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (invg x)) (H5 (invg x))) H19)).
move=> H19.
apply False_ind.
apply (lt_not_le (M + proj1_sig (invg x)) M H19).
apply le_plus_l.
move=> m.
elim.
move=> x H16 y H17.
rewrite H17.
unfold Basics.compose.
unfold In.
apply (Im_intro {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (fun (k : {n : nat | (n < N)}) => proj1_sig (fst u1 k)) (proj1_sig (fst (snd u1)) (proj1_sig (H37 M N x H16)))).
apply (Full_intro {n : nat | (n < N)}).
elim (le_lt_dec M (proj1_sig x)).
move=> H18.
suff: (H18 = H16).
move=> H19.
rewrite H19.
reflexivity.
apply proof_irrelevance.
move=> H18.
apply False_ind.
apply (le_not_lt M (proj1_sig x) H16 H18).
elim (proj1 H9).
move=> u H15 H16.
apply H15.
elim (proj1 H8).
move=> u H14 H15.
apply H14.
move=> H12.
apply False_ind.
apply H12.
apply (H7 u2 H9).
move=> H11.
apply False_ind.
apply H11.
apply (H7 u1 H8).
rewrite H10.
reflexivity.
move=> u H7.
elim (proj1 H7).
move=> g H8 H9 k1 k2 H10.
apply sig_map.
elim (le_or_lt (proj1_sig k1) (proj1_sig k2)).
move=> H11.
elim (le_lt_or_eq (proj1_sig k1) (proj1_sig k2) H11).
move=> H12.
apply False_ind.
apply (lt_irrefl (proj1_sig (g k1))).
rewrite {2} H10.
apply (H8 k1 k2 H12).
apply.
move=> H11.
apply False_ind.
apply (lt_irrefl (proj1_sig (g k1))).
rewrite {1} H10.
apply (H8 k2 k1 H11).
move=> u.
elim.
move=> u0 H7 H8.
suff: (exists (k : {n : nat | (n < M + N)}), MBlockW f (M + N) M N (MBlockH f M N M (MI f M) A) (MBlockH f M N N B (MO f N N)) k (proj1_sig u0 k) = FO f).
elim.
move=> k H9.
rewrite (MySumF2Included {n : nat | (n < M + N)} (FiniteSingleton {n : nat | (n < M + N)} k) (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N)))).
rewrite MySumF2Singleton.
simpl.
rewrite H9.
rewrite (Fmul_O_l f).
apply (Fmul_O_r f).
move=> l H10.
apply (Full_intro {n : nat | (n < M + N)} l).
suff: (~ forall (k : {n : nat | (n < M + N)}), MBlockW f (M + N) M N (MBlockH f M N M (MI f M) A) (MBlockH f M N N B (MO f N N)) k (proj1_sig u0 k) <> FO f).
move=> H9.
apply NNPP.
move=> H10.
apply H9.
move=> k H11.
apply H10.
exists k.
apply H11.
move=> H9.
apply H7.
suff: (forall (m : {n : nat | (n < M + N)}), (proj1_sig m >= M) -> (proj1_sig (proj1_sig u0 m) < M)).
move=> H10.
suff: (exists (g : {n : nat | (n < N)} -> {n : nat | (n < M)}), Im {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (Basics.compose (fun (k : {n : nat | (n < M)}) => proj1_sig k) g) = Im {n : nat | (n < M + N)} nat (fun (k : {n : nat | (n < M + N)}) => (proj1_sig k >= M)) (Basics.compose (fun (k : {n : nat | (n < M + N)}) => proj1_sig k) (proj1_sig u0)) /\ forall (p q : {n : nat | (n < N)}), (proj1_sig p < proj1_sig q) -> (proj1_sig (g p) < proj1_sig (g q))).
elim.
move=> g H11.
suff: (exists (p1 : Permutation N), forall (m : {n : nat | (n < N)}), proj1_sig (g (proj1_sig p1 m)) = proj1_sig (proj1_sig u0 (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m) (H5 m)))).
elim.
move=> p1 H12.
suff: (forall (m : {n : nat | (n < N)}), (M <= proj1_sig (proj1_sig u0 (exist (fun (n : nat) => (n < M + N)) (proj1_sig (g m)) (H4 (g m)))))).
move=> H13.
suff: (exists (p2 : Permutation N), forall (m : {n : nat | (n < N)}), (M + proj1_sig (proj1_sig p2 m)) = proj1_sig (proj1_sig u0 (exist (fun (n : nat) => (n < M + N)) (proj1_sig (g m)) (H4 (g m))))).
elim.
move=> p2 H14.
apply (Im_intro (({n : nat | (n < N)} -> {n : nat | (n < M)}) * (Permutation N * Permutation N)) (Permutation (M + N)) (proj1_sig (FinitePair ({n : nat | (n < N)} -> {n : nat | (n < M)}) (Permutation N * Permutation N) (FiniteIntersection ({n : nat | (n < N)} -> {n : nat | (n < M)}) (exist (Finite ({n : nat | (n < N)} -> {n : nat | (n < M)})) (Full_set ({n : nat | (n < N)} -> {n : nat | (n < M)})) (CountPowFinite N M)) (fun r : {n : nat | (n < N)} -> {n : nat | (n < M)} => forall p q : {n : nat | (n < N)}, (proj1_sig p < proj1_sig q) -> (proj1_sig (r p) < proj1_sig (r q)))) (FinitePair (Permutation N) (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))))) (fun (x : ({n : nat | (n < N)} -> {n : nat | (n < M)}) * (Permutation N * Permutation N)) => exist Bijective match excluded_middle_informative (Injective (fst x)) with
  | left a => fun k : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig k) with
    | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (fst x (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k b))))) (H4 (fst x (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k b)))))
    | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = fst x l) with
      | left c => exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig k) b) a c)))) (H5 (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun s : nat => (s < M)) (proj1_sig k) b) a c))))
      | right _ => k
    end
  end
  | right _ => fun k : {n0 : nat | (n0 < M + N)} => k
end (H6 x)) (g, (p1, p2))).
apply conj.
apply Intersection_intro.
simpl.
move=> p q H15.
apply (proj2 H11 p q H15).
apply (Full_intro ({n : nat | (n < N)} -> {n : nat | (n < M)}) g).
apply conj.
apply (Full_intro (Permutation N) p1).
apply (Full_intro (Permutation N) p2).
apply sig_map.
apply functional_extensionality.
move=> k.
simpl.
elim (excluded_middle_informative (Injective g)).
move=> H15.
elim (le_lt_dec M (proj1_sig k)).
move=> H16.
apply sig_map.
simpl.
rewrite (H12 (proj1_sig (H37 M N k H16))).
suff: ((exist (fun n : nat => (n < M + N)) (M + proj1_sig (proj1_sig (H37 M N k H16))) (H5 (proj1_sig (H37 M N k H16)))) = k).
move=> H17.
rewrite H17.
reflexivity.
apply sig_map.
apply (proj2_sig (H37 M N k H16)).
move=> H16.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N)}), exist (fun s : nat => (s < M)) (proj1_sig k) H16 = g l)).
move=> H17.
apply sig_map.
simpl.
rewrite (H14 (proj1_sig (H3 g (exist (fun s : nat => (s < M)) (proj1_sig k) H16) H15 H17))).
rewrite - (proj2_sig (H3 g (exist (fun s : nat => (s < M)) (proj1_sig k) H16) H15 H17)).
suff: ((exist (fun n : nat => (n < M + N)) (proj1_sig (exist (fun s : nat => (s < M)) (proj1_sig k) H16)) (H4 (exist (fun s : nat => (s < M)) (proj1_sig k) H16))) = k).
move=> H18.
rewrite H18.
reflexivity.
apply sig_map.
reflexivity.
move=> H17.
suff: (proj1_sig (proj1_sig u0 k) < M).
move=> H18.
apply NNPP.
move=> H19.
apply (H9 k).
rewrite H36.
rewrite H35.
elim (le_lt_dec M (proj1_sig (proj1_sig u0 k))).
move=> H20.
apply False_ind.
apply (lt_not_le (proj1_sig (proj1_sig u0 k)) M H18 H20).
move=> H20.
elim (le_lt_dec M (proj1_sig k)).
move=> H21.
apply False_ind.
apply (lt_not_le (proj1_sig k) M H16 H21).
move=> H21.
unfold MI.
elim (Nat.eq_dec (proj1_sig (exist (fun n : nat => (n < M)) (proj1_sig k) H21)) (proj1_sig (exist (fun n : nat => (n < M)) (proj1_sig (proj1_sig u0 k)) H20))).
simpl.
move=> H22.
apply False_ind.
apply H19.
apply sig_map.
rewrite H22.
reflexivity.
move=> H22.
reflexivity.
elim (le_or_lt M (proj1_sig (proj1_sig u0 k))).
move=> H18.
apply False_ind.
apply (lt_irrefl N).
elim (proj2 (CountCardinalBijective {x : {n : nat | (n < M + N)} | (M <= proj1_sig x)} N)).
move=> h.
elim.
move=> hinv H20.
suff: (forall (m : {n : nat | (n < M + N)}), In {n : nat | (n < M + N)} (Add {n : nat | (n < M + N)} (fun (s : {n : nat | (n < M + N)}) => (exists (l : {n : nat | (n < N)}), (exist (fun (n : nat) => (n < M + N)) (proj1_sig (g l)) (H4 (g l))) = s)) k) m -> (M <= proj1_sig (proj1_sig u0 m))).
move=> H21.
elim (CountCardinalInjective {x : {n : nat | (n < M + N)} | In {n : nat | (n < M + N)} (Add {n : nat | (n < M + N)} (fun (s : {n : nat | (n < M + N)}) => (exists (l : {n : nat | (n < N)}), (exist (fun (n : nat) => (n < M + N)) (proj1_sig (g l)) (H4 (g l))) = s)) k) x} N (Basics.compose hinv (fun (y : {x : {n : nat | (n < M + N)} | In {n : nat | (n < M + N)} (Add {n : nat | (n < M + N)} (fun (s : {n : nat | (n < M + N)}) => (exists (l : {n : nat | (n < N)}), (exist (fun (n : nat) => (n < M + N)) (proj1_sig (g l)) (H4 (g l))) = s)) k) x}) => exist (fun (x : {n : nat | (n < M + N)}) => (M <= proj1_sig x)) (proj1_sig u0 (proj1_sig y)) (H21 (proj1_sig y) (proj2_sig y)) ))).
move=> m H22.
unfold lt.
suff: (S N = m).
move=> H23.
rewrite H23.
apply H22.
rewrite (cardinal_is_functional {x : {n : nat | (n < M + N)} | In {n : nat | (n < M + N)} (Add {n : nat | (n < M + N)} (fun (s : {n : nat | (n < M + N)}) => (exists (l : {n : nat | (n < N)}), (exist (fun (n : nat) => (n < M + N)) (proj1_sig (g l)) (H4 (g l))) = s)) k) x} (Full_set {x : {n : nat | (n < M + N)} | In {n : nat | (n < M + N)} (Add {n : nat | (n < M + N)} (fun (s : {n : nat | (n < M + N)}) => (exists (l : {n : nat | (n < N)}), (exist (fun (n : nat) => (n < M + N)) (proj1_sig (g l)) (H4 (g l))) = s)) k) x}) m (proj2 H22) (Full_set {x : {n : nat | (n < M + N)} | In {n : nat | (n < M + N)} (Add {n : nat | (n < M + N)} (fun (s : {n : nat | (n < M + N)}) => (exists (l : {n : nat | (n < N)}), (exist (fun (n : nat) => (n < M + N)) (proj1_sig (g l)) (H4 (g l))) = s)) k) x}) (S N)).
reflexivity.
apply (CardinalSigSame {n : nat | (n < M + N)}).
apply card_add.
suff: (forall (m : nat), (m <= N) -> cardinal {n : nat | (n < M + N)} (fun (s : {n : nat | (n < M + N)}) => exists (l : {n : nat | (n < N)}), (proj1_sig l < m) /\ exist (fun (n : nat) => (n < M + N)) (proj1_sig (g l)) (H4 (g l)) = s) m).
move=> H23.
suff: ((fun (s : {n : nat | (n < M + N)}) => exists (l : {n : nat | (n < N)}), exist (fun (n : nat) => (n < M + N)) (proj1_sig (g l)) (H4 (g l)) = s) = (fun (s : {n : nat | (n < M + N)}) => exists (l : {n : nat | (n < N)}), (proj1_sig l < N) /\ exist (fun (n : nat) => (n < M + N)) (proj1_sig (g l)) (H4 (g l)) = s)).
move=> H24.
rewrite H24.
apply (H23 N).
apply (le_n N).
apply Extensionality_Ensembles.
apply conj.
move=> s.
elim.
move=> l H24.
exists l.
apply conj.
apply (proj2_sig l).
apply H24.
move=> s.
elim.
move=> l H24.
exists l.
apply (proj2 H24).
elim.
move=> H23.
suff: ((fun (s : {n : nat | (n < M + N)}) => exists (l : {n : nat | (n < N)}), (proj1_sig l < 0) /\ exist (fun (n : nat) => (n < M + N)) (proj1_sig (g l)) (H4 (g l)) = s) = Empty_set {n : nat | (n < M + N)}).
move=> H24.
rewrite H24.
apply card_empty.
apply Extensionality_Ensembles.
apply conj.
move=> s.
elim.
move=> l H24.
apply False_ind.
apply (le_not_lt O (proj1_sig l) (le_0_n (proj1_sig l)) (proj1 H24)).
move=> s.
elim.
move=> t H23 H24.
suff: ((fun (s : {n : nat | (n < M + N)}) => exists (l : {n : nat | (n < N)}), (proj1_sig l < S t) /\ exist (fun (n : nat) => (n < M + N)) (proj1_sig (g l)) (H4 (g l)) = s) = Add {n : nat | (n < M + N)} (fun (s : {n : nat | (n < M + N)}) => exists (l : {n : nat | (n < N)}), (proj1_sig l < t) /\ exist (fun (n : nat) => (n < M + N)) (proj1_sig (g l)) (H4 (g l)) = s) (exist (fun (n : nat) => (n < M + N)) (proj1_sig (g (exist (fun (n : nat) => (n < N)) t H24))) (H4 (g (exist (fun (n : nat) => (n < N)) t H24))))).
move=> H25.
rewrite H25.
apply card_add.
apply (H23 (le_trans t (S t) N (le_S t t (le_n t)) H24)).
elim.
move=> r H26.
apply (lt_irrefl (proj1_sig r)).
suff: (r = (exist (fun n : nat => (n < N)) t H24)).
move=> H27.
rewrite {2} H27.
apply (proj1 H26).
apply H15.
apply sig_map.
suff: (proj1_sig (g r) = proj1_sig (exist (fun n : nat => (n < M + N)) (proj1_sig (g r)) (H4 (g r)))).
move=> H27.
rewrite H27.
rewrite (proj2 H26).
reflexivity.
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> s.
elim.
move=> z H25.
elim (le_lt_or_eq (proj1_sig z) t).
move=> H26.
left.
exists z.
apply conj.
apply H26.
apply (proj2 H25).
move=> H26.
right.
suff: ((exist (fun n : nat => (n < N)) t H24) = z).
move=> H27.
rewrite H27.
rewrite (proj2 H25).
apply In_singleton.
apply sig_map.
rewrite H26.
reflexivity.
apply le_S_n.
apply (proj1 H25).
move=> l.
elim.
move=> s.
elim.
move=> z H25.
exists z.
apply conj.
apply (lt_trans (proj1_sig z) t (S t) (proj1 H25) (le_n (S t))).
apply (proj2 H25).
move=> z.
elim.
exists (exist (fun n : nat => (n < N)) t H24).
apply conj.
apply (le_n (S t)).
reflexivity.
elim.
move=> z H23.
apply H17.
exists z.
apply sig_map.
simpl.
rewrite - H23.
reflexivity.
reflexivity.
apply InjChain.
move=> y1 y2 H22.
apply sig_map.
apply (BijInj {n : nat | (n < M + N)} {n : nat | (n < M + N)} (proj1_sig u0) (proj2_sig u0)).
suff: (proj1_sig u0 (proj1_sig y1) = proj1_sig (exist (fun x : {n : nat | (n < M + N)} => (M <= proj1_sig x)) (proj1_sig u0 (proj1_sig y1)) (H21 (proj1_sig y1) (proj2_sig y1)))).
move=> H23.
rewrite H23.
rewrite H22.
reflexivity.
reflexivity.
apply BijInj.
exists h.
apply conj.
apply (proj2 H20).
apply (proj1 H20).
move=> m.
elim.
move=> m0.
elim.
move=> l H21.
rewrite - H21.
apply (H13 l).
move=> l.
elim.
apply H18.
apply (CountCardinalBijective {x : {n : nat | (n < M + N)} | (M <= proj1_sig x)} N).
suff: (forall (l : {n : nat | (n < N)}), (M <= M + proj1_sig l)).
move=> H19.
exists (fun (l : {n : nat | (n < N)}) => exist (fun (x : {n : nat | (n < M + N)}) => (M <= proj1_sig x)) (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig l) (H5 l)) (H19 l)).
exists (fun (l : {x : {n : nat | (n < M + N)} | (M <= proj1_sig x)}) => proj1_sig (H37 M N (proj1_sig l) (proj2_sig l))).
apply conj.
move=> t.
apply sig_map.
simpl.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun n : nat => (n < M + N)) (M + proj1_sig t) (H5 t)) (H19 t)))) (proj1_sig t) M).
apply (proj2_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig t) (H5 t)) (H19 t))).
move=> t.
apply sig_map.
apply sig_map.
apply (proj2_sig (H37 M N (proj1_sig t) (proj2_sig t))).
move=> l.
apply le_plus_l.
apply.
move=> H15.
apply False_ind.
apply H15.
move=> k1 k2 H16.
elim (le_or_lt (proj1_sig k1) (proj1_sig k2)).
move=> H17.
elim (le_lt_or_eq (proj1_sig k1) (proj1_sig k2) H17).
move=> H18.
apply False_ind.
apply (lt_irrefl (proj1_sig (g k1))).
rewrite {2} H16.
apply (proj2 H11 k1 k2 H18).
apply sig_map.
move=> H17.
apply False_ind.
apply (lt_irrefl (proj1_sig (g k1))).
rewrite {1} H16.
apply (proj2 H11 k2 k1 H17).
suff: (Bijective (fun (m : {n : nat | (n < N)}) => (proj1_sig (H37 M N (proj1_sig u0 (exist (fun n : nat => (n < M + N)) (proj1_sig (g m)) (H4 (g m)))) (H13 m))))).
move=> H14.
exists (exist Bijective (fun (m : {n : nat | (n < N)}) => proj1_sig (H37 M N (proj1_sig u0 (exist (fun n : nat => (n < M + N)) (proj1_sig (g m)) (H4 (g m)))) (H13 m))) H14).
move=> m.
simpl.
apply (proj2_sig (H37 M N (proj1_sig u0 (exist (fun (n : nat) => n < M + N) (proj1_sig (g m)) (H4 (g m)))) (H13 m))).
apply CountInjBij.
move=> k1 k2 H14.
suff: ((proj1_sig (g k1)) = (proj1_sig (g k2))).
move=> H15.
elim (le_or_lt (proj1_sig k1) (proj1_sig k2)).
move=> H16.
elim (le_lt_or_eq (proj1_sig k1) (proj1_sig k2) H16).
move=> H17.
apply False_ind.
apply (lt_irrefl (proj1_sig (g k1))).
rewrite {2} H15.
apply (proj2 H11 k1 k2 H17).
apply sig_map.
move=> H16.
apply False_ind.
apply (lt_irrefl (proj1_sig (g k1))).
rewrite {1} H15.
apply (proj2 H11 k2 k1 H16).
suff: ((exist (fun (n : nat) => (n < M + N)) (proj1_sig (g k1)) (H4 (g k1))) = (exist (fun (n : nat) => (n < M + N)) (proj1_sig (g k2)) (H4 (g k2)))).
move=> H15.
suff: (proj1_sig (g k1) = proj1_sig (exist (fun n : nat => (n < M + N)) (proj1_sig (g k1)) (H4 (g k1)))).
move=> H16.
rewrite H16.
rewrite H15.
reflexivity.
reflexivity.
apply (BijInj {n : nat | (n < M + N)} {n : nat | (n < M + N)} (proj1_sig u0) (proj2_sig u0)).
apply sig_map.
rewrite - (proj2_sig (H37 M N (proj1_sig u0 (exist (fun n : nat => (n < M + N)) (proj1_sig (g k1)) (H4 (g k1)))) (H13 k1))).
rewrite H14.
apply (proj2_sig (H37 M N (proj1_sig u0 (exist (fun n : nat => (n < M + N)) (proj1_sig (g k2)) (H4 (g k2)))) (H13 k2))).
move=> m.
elim (le_or_lt M (proj1_sig (proj1_sig u0 (exist (fun (n : nat) => (n < M + N)) (proj1_sig (g m)) (H4 (g m)))))).
apply.
move=> H13.
apply False_ind.
apply (H9 (exist (fun (n : nat) => n < M + N) (proj1_sig (g m)) (H4 (g m)))).
rewrite H36.
rewrite H35.
simpl.
elim (le_lt_dec M (proj1_sig (g m))).
move=> H14.
apply False_ind.
apply (le_not_lt M (proj1_sig (g m)) H14 (proj2_sig (g m))).
move=> H14.
elim (le_lt_dec M (proj1_sig (proj1_sig u0 (exist (fun n : nat => (n < M + N)) (proj1_sig (g m)) (H4 (g m)))))).
move=> H15.
apply False_ind.
apply (le_not_lt M (proj1_sig (proj1_sig u0 (exist (fun (n : nat) => n < M + N) (proj1_sig (g m)) (H4 (g m))))) H15 H13).
move=> H15.
unfold MI.
simpl.
elim (Nat.eq_dec (proj1_sig (g m)) (proj1_sig (proj1_sig u0 (exist (fun n : nat => (n < M + N)) (proj1_sig (g m)) (H4 (g m)))))).
move=> H16.
apply False_ind.
suff: (exists (k : {n : nat | (n < M + N)}), (M <= proj1_sig k) /\ proj1_sig (g m) = proj1_sig (proj1_sig u0 k)).
elim.
move=> k H17.
apply (le_not_lt M (proj1_sig k) (proj1 H17)).
suff: (k = (exist (fun n : nat => (n < M + N)) (proj1_sig (g m)) (H4 (g m)))).
move=> H18.
rewrite H18.
apply (proj2_sig (g m)).
apply (BijInj {n : nat | (n < M + N)} {n : nat | (n < M + N)} (proj1_sig u0) (proj2_sig u0)).
apply sig_map.
rewrite - (proj2 H17).
apply H16.
suff: (In nat (Im {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (Basics.compose (fun k : {n : nat | (n < M)} => proj1_sig k) g)) (proj1_sig (g m))).
rewrite (proj1 H11).
elim.
move=> l H17 x H18.
exists l.
apply conj.
apply H17.
rewrite H18.
reflexivity.
apply (Im_intro {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (Basics.compose (fun k : {n : nat | (n < M)} => proj1_sig k) g) m).
apply (Full_intro {n : nat | (n < N)} m).
reflexivity.
move=> H16.
reflexivity.
suff: (forall (m : {n : nat | (n < N)}), {k : {n : nat | (n < N)} | proj1_sig (g k) = proj1_sig (proj1_sig u0 (exist (fun n : nat => (n < M + N)) (M + proj1_sig m) (H5 m)))}).
move=> H12.
suff: (Bijective (fun (m : {n : nat | (n < N)}) => proj1_sig (H12 m))).
move=> H13.
exists (exist Bijective (fun (m : {n : nat | (n < N)}) => proj1_sig (H12 m)) H13).
move=> m.
apply (proj2_sig (H12 m)).
apply CountInjBij.
move=> k1 k2 H13.
apply sig_map.
apply (plus_reg_l (proj1_sig k1) (proj1_sig k2) M).
suff: ((exist (fun (n : nat) => (n < M + N)) (M + proj1_sig k1) (H5 k1)) = (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig k2) (H5 k2))).
move=> H14.
suff: ((M + proj1_sig k1) = proj1_sig (exist (fun n : nat => (n < M + N)) (M + proj1_sig k1) (H5 k1))).
move=> H15.
rewrite H15.
rewrite H14.
reflexivity.
reflexivity.
apply (BijInj {n : nat | (n < M + N)} {n : nat | (n < M + N)} (proj1_sig u0) (proj2_sig u0)).
apply sig_map.
rewrite - (proj2_sig (H12 k1)).
rewrite H13.
apply (proj2_sig (H12 k2)).
move=> m.
apply constructive_definite_description.
apply (unique_existence (fun (x : {n : nat | (n < N)}) => proj1_sig (g x) = proj1_sig (proj1_sig u0 (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m) (H5 m))))).
apply conj.
suff: (In nat (Im {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (Basics.compose (fun k : {n : nat | (n < M)} => proj1_sig k) g)) (proj1_sig (proj1_sig u0 (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m) (H5 m))))).
elim.
move=> x H12 y H13.
exists x.
rewrite H13.
reflexivity.
rewrite (proj1 H11).
apply (Im_intro {n : nat | (n < M + N)} nat (fun (k : {n : nat | (n < M + N)}) => (proj1_sig k >= M)) (Basics.compose (fun (k : {n : nat | (n < M + N)}) => proj1_sig k) (proj1_sig u0)) (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m) (H5 m))).
apply le_plus_l.
reflexivity.
move=> k1 k2 H12 H13.
suff: (proj1_sig (g k1) = proj1_sig (g k2)).
move=> H14.
elim (le_or_lt (proj1_sig k1) (proj1_sig k2)).
move=> H15.
elim (le_lt_or_eq (proj1_sig k1) (proj1_sig k2) H15).
move=> H16.
apply False_ind.
apply (lt_irrefl (proj1_sig (g k1))).
rewrite {2} H14.
apply (proj2 H11 k1 k2 H16).
apply sig_map.
move=> H15.
apply False_ind.
apply (lt_irrefl (proj1_sig (g k1))).
rewrite {1} H14.
apply (proj2 H11 k2 k1 H15).
rewrite H13.
apply H12.
suff: (cardinal nat (Im {n : nat | (n < M + N)} nat (fun (k : {n : nat | (n < M + N)}) => (proj1_sig k >= M)) (Basics.compose (fun (k : {n : nat | (n < M + N)}) => proj1_sig k) (proj1_sig u0))) N).
move=> H11.
suff: (forall (m : nat), (m < N) -> {k : nat | cardinal nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun (l : nat) => (l < k))) m /\ In nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) k}).
move=> H12.
suff: (forall (m : nat) (H : m < N), proj1_sig (H12 m H) < M).
move=> H13.
exists (fun (k : {n : nat | (n < N)}) => exist (fun (l : nat) => (l < M)) (proj1_sig (H12 (proj1_sig k) (proj2_sig k))) (H13 (proj1_sig k) (proj2_sig k))).
apply conj.
apply Extensionality_Ensembles.
apply conj.
move=> m.
elim.
move=> x H14 y H15.
rewrite H15.
apply (proj2 (proj2_sig (H12 (proj1_sig x) (proj2_sig x)))).
move=> m.
elim.
move=> x H14 y H15.
suff: (exists (m : nat), (m < N) /\ cardinal nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun (k : {n : nat | (n < M + N)}) => (proj1_sig k >= M)) (Basics.compose (fun (k : {n : nat | (n < M + N)}) => proj1_sig k) (proj1_sig u0))) (fun (l : nat) => (l < y))) m).
elim.
move=> l H16.
apply (Im_intro {n : nat | (n < N)} nat (Full_set {n : nat | (n < N)}) (Basics.compose (fun k : {n : nat | (n < M)} => proj1_sig k) (fun k : {n : nat | (n < N)} => exist (fun (n : nat) => (n < M)) (proj1_sig (H12 (proj1_sig k) (proj2_sig k))) (H13 (proj1_sig k) (proj2_sig k)))) (exist (fun (n : nat) => (n < N)) l (proj1 H16))).
apply (Full_intro {n : nat | (n < N)}).
elim (le_or_lt y (Basics.compose (fun k : {n : nat | (n < M)} => proj1_sig k) (fun k : {n : nat | (n < N)} => exist (fun n : nat => (n < M)) (proj1_sig (H12 (proj1_sig k) (proj2_sig k))) (H13 (proj1_sig k) (proj2_sig k))) (exist (fun n : nat => (n < N)) l (proj1 H16)))).
move=> H17.
elim (le_lt_or_eq y (Basics.compose (fun k : {n : nat | (n < M)} => proj1_sig k) (fun k : {n : nat | (n < N)} => exist (fun n : nat => (n < M)) (proj1_sig (H12 (proj1_sig k) (proj2_sig k))) (H13 (proj1_sig k) (proj2_sig k))) (exist (fun n : nat => (n < N)) l (proj1 H16))) H17).
move=> H18.
apply False_ind.
apply (lt_irrefl l).
suff: (Included nat (Add nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l : nat => (l < y))) y) (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l0 : nat => (l0 < proj1_sig (H12 l (proj1 H16)))))).
apply (incl_card_le nat (Add nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l : nat => (l < y))) y) (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l0 : nat => (l0 < proj1_sig (H12 l (proj1 H16))))) (S l) l).
apply card_add.
apply (proj2 H16).
move=> H19.
apply (lt_irrefl y).
suff: (forall (z : nat), In nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l : nat => (l < y))) z -> z < y).
move=> H20.
apply (H20 y H19).
move=> z.
elim.
move=> z0 H20 H21.
apply H21.
apply (proj2_sig (H12 l (proj1 H16))).
move=> k.
elim.
move=> k0.
elim.
move=> k1 H19 H20.
apply Intersection_intro.
apply H19.
apply (lt_trans k1 y (proj1_sig (H12 l (proj1 H16))) H20 H18).
move=> k1.
elim.
apply Intersection_intro.
rewrite H15.
apply (Im_intro {n : nat | (n < M + N)} nat (fun (l : {n : nat | (n < M + N)}) => (proj1_sig l >= M)) (Basics.compose (fun (l : {n : nat | (n < M + N)}) => proj1_sig l) (proj1_sig u0)) x).
apply H14.
reflexivity.
apply H18.
apply.
move=> H17.
apply False_ind.
apply (lt_irrefl l).
apply (incl_card_le nat (Add nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l0 : nat => (l0 < proj1_sig (H12 l (proj1 H16))))) (Basics.compose (fun k : {n : nat | (n < M)} => proj1_sig k) (fun k : {n : nat | (n < N)} => exist (fun n : nat => (n < M)) (proj1_sig (H12 (proj1_sig k) (proj2_sig k))) (H13 (proj1_sig k) (proj2_sig k))) (exist (fun n : nat => (n < N)) l (proj1 H16)))) (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l0 : nat => (l0 < y))) (S l) l).
apply card_add.
apply (proj1 (proj2_sig (H12 (proj1_sig (exist (fun n : nat => n < N) l (proj1 H16))) (proj2_sig (exist (fun n : nat => n < N) l (proj1 H16)))))).
move=> H18.
apply (lt_irrefl (Basics.compose (fun k : {n : nat | (n < M)} => proj1_sig k) (fun k : {n : nat | (n < N)} => exist (fun n : nat => (n < M)) (proj1_sig (H12 (proj1_sig k) (proj2_sig k))) (H13 (proj1_sig k) (proj2_sig k))) (exist (fun n : nat => (n < N)) l (proj1 H16)))).
suff: (forall (z : nat), In nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l0 : nat => (l0 < proj1_sig (H12 l (proj1 H16))))) z -> z < (Basics.compose (fun k : {n : nat | n < M} => proj1_sig k) (fun k : {n : nat | n < N} => exist (fun n : nat => n < M) (proj1_sig (H12 (proj1_sig k) (proj2_sig k))) (H13 (proj1_sig k) (proj2_sig k))) (exist (fun n : nat => n < N) l (proj1 H16)))).
move=> H19.
apply (H19 (Basics.compose (fun k : {n : nat | n < M} => proj1_sig k) (fun k : {n : nat | n < N} => exist (fun n : nat => n < M) (proj1_sig (H12 (proj1_sig k) (proj2_sig k))) (H13 (proj1_sig k) (proj2_sig k))) (exist (fun n : nat => n < N) l (proj1 H16))) H18).
move=> z.
elim.
move=> z0 H19 H20.
apply H20.
apply (proj2 H16).
move=> k.
elim.
move=> k0.
elim.
move=> k1 H18 H19.
apply Intersection_intro.
apply H18.
apply (lt_trans k1 (proj1_sig (H12 l (proj1 H16))) y H19 H17).
move=> k1.
elim.
apply Intersection_intro.
unfold Basics.compose at 2.
simpl.
elim (proj2 (proj2_sig (H12 l (proj1 H16)))).
move=> z H18 w H19.
rewrite H19.
apply (Im_intro {n : nat | (n < M + N)} nat (fun (l : {n : nat | (n < M + N)}) => (proj1_sig l >= M)) (Basics.compose (fun (k : {n : nat | (n < M + N)}) => proj1_sig k) (proj1_sig u0)) z).
apply H18.
reflexivity.
apply H17.
simpl.
elim (finite_cardinal nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l : nat => (l < y)))).
move=> z H16.
exists z.
apply conj.
apply (incl_st_card_lt nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l : nat => (l < y))) z H16 (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) N H11).
apply conj.
move=> w.
elim.
move=> w0 H17 H18.
apply H17.
move=> H17.
apply (lt_irrefl y).
suff: (forall (w : nat), In nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l : nat => (l < y))) w -> w < y).
move=> H18.
apply (H18 y).
rewrite H17.
rewrite H15.
apply (Im_intro {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0)) x H14).
reflexivity.
move=> w.
elim.
move=> w0 H18 H19.
apply H19.
apply H16.
apply (Finite_downward_closed nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0)))).
apply (cardinal_finite nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) N H11).
move=> z.
elim.
move=> w H16 H17.
apply H16.
simpl.
move=> p q H14.
elim (le_or_lt (proj1_sig (H12 (proj1_sig q) (proj2_sig q))) (proj1_sig (H12 (proj1_sig p) (proj2_sig p)))).
move=> H15.
apply False_ind.
apply (lt_irrefl (proj1_sig p)).
apply (le_trans (S (proj1_sig p)) (proj1_sig q) (proj1_sig p) H14).
apply (incl_card_le nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l : nat => (l < proj1_sig (H12 (proj1_sig q) (proj2_sig q))))) (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l : nat => (l < proj1_sig (H12 (proj1_sig p) (proj2_sig p)))))).
apply (proj1 (proj2_sig (H12 (proj1_sig q) (proj2_sig q)))).
apply (proj1 (proj2_sig (H12 (proj1_sig p) (proj2_sig p)))).
move=> m.
elim.
move=> m0 H16 H17.
apply Intersection_intro.
apply H16.
apply (le_trans (S m0) (proj1_sig (H12 (proj1_sig q) (proj2_sig q))) (proj1_sig (H12 (proj1_sig p) (proj2_sig p))) H17 H15).
apply.
move=> m H13.
elim (proj2 (proj2_sig (H12 m H13))).
move=> x H14 y H15.
rewrite H15.
apply (H10 x H14).
elim.
move=> H12.
elim (min_nat_get (Im {n : nat | (n < M + N)} nat (fun (k : {n : nat | (n < M + N)}) => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0)))).
move=> l H13.
exists l.
apply conj.
suff: ((Intersection nat (Im {n : nat | (n < M + N)} nat (fun (k : {n : nat | (n < M + N)}) => (proj1_sig k >= M)) (Basics.compose (fun (k : {n : nat | (n < M + N)}) => proj1_sig k) (proj1_sig u0))) (fun (m : nat) => (m < l))) = Empty_set nat).
move=> H14.
rewrite H14.
apply card_empty.
apply Extensionality_Ensembles.
apply conj.
move=> k.
elim.
move=> m H14 H15.
apply False_ind.
apply (le_not_lt l m (proj2 H13 m H14) H15).
move=> k.
elim.
apply (proj1 H13).
suff: (exists (n : nat), S n = N).
elim.
move=> n H13.
apply (cardinal_elim nat (Im {n : nat | (n < M + N)} nat (fun (k : {n : nat | (n < M + N)}) => (proj1_sig k >= M)) (Basics.compose (fun (k : {n : nat | (n < M + N)}) => proj1_sig k) (proj1_sig u0))) (S n)).
rewrite H13.
apply H11.
suff: (0 < N).
elim N.
move=> H13.
apply False_ind.
apply (lt_irrefl O H13).
move=> n H13 H14.
exists n.
reflexivity.
apply H12.
move=> m H12 H13.
elim (H12 (le_trans (S m) (S (S m)) N (le_S (S m) (S m) (le_n (S m))) H13)).
move=> k H14.
elim (min_nat_get (Intersection nat (Im {n : nat | (n < M + N)} nat (fun (k : {n : nat | (n < M + N)}) => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun (l : nat) => (k < l)))).
move=> s H15.
exists s.
apply conj.
suff: ((Intersection nat (Im {n : nat | (n < M + N)} nat (fun (k0 : {n : nat | (n < M + N)}) => (proj1_sig k0 >= M)) (Basics.compose (fun (k0 : {n : nat | (n < M + N)}) => proj1_sig k0) (proj1_sig u0))) (fun (l : nat) => (l < s))) = Add nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l : nat => (l < k))) k).
move=> H16.
rewrite H16.
apply card_add.
apply (proj1 H14).
move=> H17.
suff: (forall (w : nat), In nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l : nat => (l < k))) w -> (w < k)).
move=> H18.
apply (lt_irrefl k).
apply (H18 k H17).
move=> w.
elim.
move=> w0 H18 H19.
apply H19.
apply Extensionality_Ensembles.
apply conj.
move=> z.
elim.
move=> w H16 H17.
elim (le_or_lt k w).
move=> H18.
right.
elim (le_lt_or_eq k w H18).
move=> H19.
apply False_ind.
apply (le_not_lt s w).
apply (proj2 H15 w).
apply Intersection_intro.
apply H16.
apply H19.
apply H17.
move=> H19.
rewrite H19.
apply (In_singleton nat w).
move=> H18.
left.
apply Intersection_intro.
apply H16.
apply H18.
move=> z.
elim.
move=> w.
elim.
move=> w0 H16 H17.
apply Intersection_intro.
apply H16.
apply (lt_trans w0 k s H17).
elim (proj1 H15).
move=> t H18 H19.
apply H19.
move=> w.
elim.
apply Intersection_intro.
apply (proj2 H14).
elim (proj1 H15).
move=> t H16 H17.
apply H17.
elim (proj1 H15).
move=> z H16 H17.
apply H16.
apply NNPP.
move=> H15.
apply (le_not_lt N (S m)).
apply (incl_card_le nat (Im {n : nat | (n < M + N)} nat (fun (k : {n : nat | (n < M + N)}) => (proj1_sig k >= M)) (Basics.compose (fun (k : {n : nat | (n < M + N)}) => proj1_sig k) (proj1_sig u0))) (Add nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (fun l : nat => (l < k))) k)).
apply H11.
apply card_add.
apply (proj1 H14).
move=> H16.
suff: (forall (w : nat), In nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun k0 : {n : nat | (n < M + N)} => (proj1_sig k0 >= M)) (Basics.compose (fun k0 : {n : nat | (n < M + N)} => proj1_sig k0) (proj1_sig u0))) (fun l : nat => (l < k))) w -> (w < k)).
move=> H17.
apply False_ind.
apply (lt_irrefl k).
apply (H17 k H16).
move=> w.
elim.
move=> z H17 H18.
apply H18.
move=> w H16.
elim (le_or_lt w k).
move=> H17.
elim (le_lt_or_eq w k H17).
move=> H18.
left.
apply Intersection_intro.
apply H16.
apply H18.
move=> H18.
rewrite H18.
right.
apply (In_singleton nat k).
move=> H17.
apply False_ind.
apply H15.
apply (Inhabited_intro nat (Intersection nat (Im {n : nat | (n < M + N)} nat (fun (k : {n : nat | (n < M + N)}) => (proj1_sig k >= M)) (Basics.compose (fun (k : {n : nat | (n < M + N)}) => proj1_sig k) (proj1_sig u0))) (fun l : nat => (k < l))) w).
apply Intersection_intro.
apply H16.
apply H17.
apply H13.
apply (CardinalSigSame nat).
apply CountCardinalBijective.
suff: (forall (m : {n : nat | (n < N)}), In nat (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (proj1_sig (proj1_sig u0 (exist (fun (s : nat) => (s < M + N)) (M + proj1_sig m) (H5 m))))).
move=> H11.
exists (fun (m : {n : nat | (n < N)}) => exist (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (proj1_sig (proj1_sig u0 (exist (fun (s : nat) => (s < M + N)) (M + proj1_sig m) (H5 m)))) (H11 m)).
apply InjSurjBij.
move=> m1 m2 H12.
apply sig_map.
apply (plus_reg_l (proj1_sig m1) (proj1_sig m2) M).
suff: ((exist (fun s : nat => (s < M + N)) (M + proj1_sig m1) (H5 m1)) = (exist (fun s : nat => (s < M + N)) (M + proj1_sig m2) (H5 m2))).
move=> H13.
suff: ((M + proj1_sig m1) = proj1_sig (exist (fun s : nat => (s < M + N)) (M + proj1_sig m1) (H5 m1))).
move=> H14.
rewrite H14.
rewrite H13.
reflexivity.
reflexivity.
apply (BijInj {n : nat | (n < M + N)} {n : nat | (n < M + N)} (proj1_sig u0) (proj2_sig u0)).
apply sig_map.
suff: (proj1_sig (proj1_sig u0 (exist (fun (s : nat) => (s < M + N)) (M + proj1_sig m1) (H5 m1))) = proj1_sig (exist (Im {n : nat | (n < M + N)} nat (fun k : {n : nat | (n < M + N)} => (proj1_sig k >= M)) (Basics.compose (fun k : {n : nat | (n < M + N)} => proj1_sig k) (proj1_sig u0))) (proj1_sig (proj1_sig u0 (exist (fun s : nat => (s < M + N)) (M + proj1_sig m1) (H5 m1)))) (H11 m1))).
move=> H13.
rewrite H13.
rewrite H12.
reflexivity.
reflexivity.
move=> k.
suff: (exists (x : {n : nat | (n < N)}), (proj1_sig (proj1_sig u0 (exist (fun s : nat => (s < M + N)) (M + proj1_sig x) (H5 x)))) = proj1_sig k).
elim.
move=> x H12.
exists x.
apply sig_map.
apply H12.
elim (proj2_sig k).
move=> x H12 y H13.
exists (proj1_sig (H37 M N x H12)).
rewrite H13.
suff: ((exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (H37 M N x H12))) (H5 (proj1_sig (H37 M N x H12)))) = x).
move=> H14.
rewrite H14.
reflexivity.
apply sig_map.
apply (proj2_sig (H37 M N x H12)).
move=> m.
apply (Im_intro {n : nat | (n < M + N)} nat (fun (k : {n : nat | (n < M + N)}) => (proj1_sig k >= M)) (Basics.compose (fun (k : {n : nat | (n < M + N)}) => proj1_sig k) (proj1_sig u0)) (exist (fun s : nat => (s < M + N)) (M + proj1_sig m) (H5 m))).
apply le_plus_l.
reflexivity.
move=> m H10.
elim (le_or_lt M (proj1_sig (proj1_sig u0 m))).
move=> H11.
apply False_ind.
apply (H9 m).
rewrite H36.
rewrite H35.
elim (le_lt_dec M (proj1_sig (proj1_sig u0 m))).
move=> H12.
elim (le_lt_dec M (proj1_sig m)).
move=> H13.
reflexivity.
move=> H13.
apply False_ind.
apply (le_not_lt M (proj1_sig m) H10 H13).
move=> H12.
apply False_ind.
apply (le_not_lt M (proj1_sig (proj1_sig u0 m)) H11 H12).
apply.
move=> P H7.
apply (Full_intro (Permutation (M + N)) P).
move=> x.
elim (excluded_middle_informative (Injective (fst x))).
move=> H6.
elim (proj2_sig (fst (snd x))).
move=> fsti H7.
elim (proj2_sig (snd (snd x))).
move=> sndi H8.
exists ((fun (k : {n : nat | (n < M + N)}) => match le_lt_dec M (proj1_sig k) with
  | left b => exist (fun s : nat => (s < M + N)) (proj1_sig (fst x (sndi (proj1_sig (H37 M N k b))))) (H4 (fst x (sndi (proj1_sig (H37 M N k b)))))
  | right b => match excluded_middle_informative (exists l : {n : nat | (n < N)}, exist (fun s : nat => (s < M)) (proj1_sig k) b = fst x l) with
    | left c => exist (fun s : nat => (s < M + N)) (M + proj1_sig (fsti (proj1_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig k) b) H6 c)))) (H5 (fsti (proj1_sig (H3 (fst x) (exist (fun s : nat => (s < M)) (proj1_sig k) b) H6 c))))
    | right _ => k
  end
end)).
apply conj.
move=> k.
elim (le_lt_dec M (proj1_sig k)).
move=> H9.
simpl.
elim (le_lt_dec M (proj1_sig (fst x (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k H9)))))).
move=> H10.
apply sig_map.
simpl.
apply False_ind.
apply (le_not_lt M (proj1_sig (fst x (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k H9))))) H10 (proj2_sig (fst x (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k H9)))))).
move=> H10.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N)}), exist (fun s : nat => (s < M)) (proj1_sig (fst x (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k H9))))) H10 = fst x l)).
move=> H11.
apply sig_map.
simpl.
suff: ((proj1_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig (fst x (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k H9))))) H10) H6 H11)) = (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k H9)))).
move=> H12.
rewrite H12.
rewrite (proj1 H7).
apply (proj2_sig (H37 M N k H9)).
apply H6.
rewrite - (proj2_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig (fst x (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k H9))))) H10) H6 H11)).
apply sig_map.
reflexivity.
move=> H11.
apply False_ind.
apply H11.
exists (proj1_sig (fst (snd x)) (proj1_sig (H37 M N k H9))).
apply sig_map.
reflexivity.
move=> H9.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N)}), exist (fun s : nat => (s < M)) (proj1_sig k) H9 = fst x l)).
move=> H10.
simpl.
elim (le_lt_dec M (M + proj1_sig (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun s : nat => (s < M)) (proj1_sig k) H9) H6 H10))))).
move=> H11.
apply sig_map.
simpl.
suff: ((proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig k) H9) H6 H10)))) (H5 (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun s : nat => (s < M)) (proj1_sig k) H9) H6 H10))))) H11)) = (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig k) H9) H6 H10)))).
move=> H12.
rewrite H12.
rewrite (proj1 H8).
rewrite - (proj2_sig (H3 (fst x) (exist (fun (s : nat) => (s < M)) (proj1_sig k) H9) H6 H10)).
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig k) H9) H6 H10)))) (H5 (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun s : nat => (s < M)) (proj1_sig k) H9) H6 H10))))) H11))) (proj1_sig (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun s : nat => (s < M)) (proj1_sig k) H9) H6 H10)))) M).
apply (proj2_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig k) H9) H6 H10)))) (H5 (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun s : nat => (s < M)) (proj1_sig k) H9) H6 H10))))) H11)).
move=> H11.
apply False_ind.
apply (le_not_lt M (M + proj1_sig (proj1_sig (snd (snd x)) (proj1_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig k) H9) H6 H10))))).
apply le_plus_l.
apply H11.
move=> H10.
elim (le_lt_dec M (proj1_sig k)).
move=> H11.
apply False_ind.
apply (le_not_lt M (proj1_sig k) H11 H9).
move=> H11.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N)}), exist (fun s : nat => (s < M)) (proj1_sig k) H11 = fst x l)).
move=> H12.
apply False_ind.
apply H10.
elim H12.
move=> l H13.
exists l.
suff: (H9 = H11).
move=> H14.
rewrite H14.
apply H13.
apply proof_irrelevance.
move=> H12.
reflexivity.
move=> y.
elim (le_lt_dec M (proj1_sig y)).
move=> H9.
simpl.
elim (le_lt_dec M (proj1_sig (fst x (sndi (proj1_sig (H37 M N y H9)))))).
move=> H10.
apply False_ind.
apply (le_not_lt M (proj1_sig (fst x (sndi (proj1_sig (H37 M N y H9))))) H10 (proj2_sig (fst x (sndi (proj1_sig (H37 M N y H9)))))).
move=> H10.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N)}), exist (fun s : nat => (s < M)) (proj1_sig (fst x (sndi (proj1_sig (H37 M N y H9))))) H10 = fst x l)).
move=> H11.
apply sig_map.
simpl.
suff: ((proj1_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig (fst x (sndi (proj1_sig (H37 M N y H9))))) H10) H6 H11)) = (sndi (proj1_sig (H37 M N y H9)))).
move=> H12.
rewrite H12.
rewrite (proj2 H8).
apply (proj2_sig (H37 M N y H9)).
apply H6.
rewrite - (proj2_sig (H3 (fst x) (exist (fun s : nat => (s < M)) (proj1_sig (fst x (sndi (proj1_sig (H37 M N y H9))))) H10) H6 H11)).
apply sig_map.
reflexivity.
move=> H11.
apply False_ind.
apply H11.
exists (sndi (proj1_sig (H37 M N y H9))).
apply sig_map.
reflexivity.
move=> H9.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N)}), exist (fun s : nat => (s < M)) (proj1_sig y) H9 = fst x l)).
move=> H10.
simpl.
elim (le_lt_dec M (M + proj1_sig (fsti (proj1_sig (H3 (fst x) (exist (fun s : nat => (s < M)) (proj1_sig y) H9) H6 H10))))).
move=> H11.
apply sig_map.
simpl.
suff: ((proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (fsti (proj1_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig y) H9) H6 H10)))) (H5 (fsti (proj1_sig (H3 (fst x) (exist (fun s : nat => (s < M)) (proj1_sig y) H9) H6 H10))))) H11)) = (fsti (proj1_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig y) H9) H6 H10)))).
move=> H12.
rewrite H12.
rewrite (proj2 H7).
rewrite - (proj2_sig (H3 (fst x) (exist (fun s : nat => (s < M)) (proj1_sig y) H9) H6 H10)).
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun s : nat => (s < M + N)) (M + proj1_sig (fsti (proj1_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig y) H9) H6 H10)))) (H5 (fsti (proj1_sig (H3 (fst x) (exist (fun s : nat => (s < M)) (proj1_sig y) H9) H6 H10))))) H11))) (proj1_sig (fsti (proj1_sig (H3 (fst x) (exist (fun s : nat => (s < M)) (proj1_sig y) H9) H6 H10)))) M).
apply (proj2_sig (H37 M N (exist (fun (s : nat) => (s < M + N)) (M + proj1_sig (fsti (proj1_sig (H3 (fst x) (exist (fun (s : nat) => s < M) (proj1_sig y) H9) H6 H10)))) (H5 (fsti (proj1_sig (H3 (fst x) (exist (fun (s : nat) => (s < M)) (proj1_sig y) H9) H6 H10))))) H11)).
move=> H11.
apply False_ind.
apply (le_not_lt M (M + proj1_sig (fsti (proj1_sig (H3 (fst x) (exist (fun s : nat => s < M) (proj1_sig y) H9) H6 H10))))).
apply le_plus_l.
apply H11.
move=> H10.
elim (le_lt_dec M (proj1_sig y)).
move=> H11.
apply False_ind.
apply (le_not_lt M (proj1_sig y) H11 H9).
move=> H11.
elim (excluded_middle_informative (exists (l : {n : nat | (n < N)}), exist (fun s : nat => (s < M)) (proj1_sig y) H11 = fst x l)).
move=> H12.
apply False_ind.
apply H10.
elim H12.
move=> l H13.
exists l.
suff: (H9 = H11).
move=> H14.
rewrite H14.
apply H13.
apply proof_irrelevance.
move=> H12.
reflexivity.
move=> H6.
exists (fun k : {n : nat | (n < M + N)} => k).
apply conj.
move=> y.
reflexivity.
move=> z.
reflexivity.
move=> l.
apply (plus_lt_compat_l (proj1_sig l) N M (proj2_sig l)).
move=> l.
apply (le_trans (S (proj1_sig l)) M (M + N) (proj2_sig l)).
apply le_plus_l.
move=> p k H3 H4.
apply constructive_definite_description.
apply (unique_existence (fun (l : {n : nat | (n < N)}) => k = p l)).
apply conj.
apply H4.
move=> l1 l2 H5 H6.
apply H3.
rewrite - H5.
apply H6.
rewrite - H1.
suff: (forall (m : nat), (m <= N) -> Determinant f N (Mmult f N M N A B) = Fmul f (PowF f (Fopp f (FI f)) m) (Determinant f N (fun (x y : {n : nat | (n < N)}) => match (le_lt_dec m (proj1_sig x)) with
  | left _ => Mmult f N M N A B x y
  | right _ => Fopp f (Mmult f N M N A B x y)
end))).
move=> H2.
suff: ((Mopp f N N (Mmult f N M N A B)) = (fun (x y : {n : nat | (n < N)}) => match (le_lt_dec N (proj1_sig x)) with
  | left _ => Mmult f N M N A B x y
  | right _ => Fopp f (Mmult f N M N A B x y)
end)).
move=> H3.
rewrite H3.
apply (H2 N (le_n N)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (le_lt_dec N (proj1_sig x)).
move=> H3.
apply False_ind.
apply (le_not_lt N (proj1_sig x) H3 (proj2_sig x)).
move=> H3.
reflexivity.
elim.
move=> H2.
suff: ((Mmult f N M N A B) = (fun (x y : {n : nat | (n < N)}) => match (le_lt_dec O (proj1_sig x)) with
  | left _ => Mmult f N M N A B x y
  | right _ => Fopp f (Mmult f N M N A B x y)
end)).
move=> H3.
rewrite {1} H3.
rewrite (Fmul_I_l f).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (le_lt_dec O (proj1_sig x)).
move=> H3.
reflexivity.
move=> H3.
apply False_ind.
apply (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) H3).
move=> m H2 H3.
suff: (Determinant f N (fun (x y : {n : nat | (n < N)}) => match le_lt_dec (S m) (proj1_sig x) with
  | left _ => Mmult f N M N A B x y
  | right _ => Fopp f (Mmult f N M N A B x y)
end) = Fmul f (Fopp f (FI f)) (Determinant f N (fun (x y : {n : nat | (n < N)}) => match le_lt_dec m (proj1_sig x) with
  | left _ => Mmult f N M N A B x y
  | right _ => Fopp f (Mmult f N M N A B x y)
end))).
move=> H4.
rewrite H4.
simpl.
rewrite - (Fmul_assoc f (Fmul f (PowF f (Fopp f (FI f)) m) (Fopp f (FI f)))).
rewrite (Fmul_assoc f (PowF f (Fopp f (FI f)) m)).
rewrite (Fmul_opp_opp f (FI f)).
rewrite (Fmul_I_r f).
rewrite (Fmul_I_r f).
apply (H2 (le_trans m (S m) N (le_S m m (le_n m)) H3)).
rewrite - (DeterminantMultiLinearityHMult f N (fun (x y : {n : nat | (n < N)}) => match (le_lt_dec m (proj1_sig x)) with
  | left _ => Mmult f N M N A B x y
  | right _ => Fopp f (Mmult f N M N A B x y)
end) (exist (fun (k : nat) => (k < N)) m H3) (Fopp f (FI f))).
suff: ((fun (x y : {n : nat | (n < N)}) => match le_lt_dec (S m) (proj1_sig x) with
  | left _ => Mmult f N M N A B x y
  | right _ => Fopp f (Mmult f N M N A B x y)
end) = (fun (x y : {n : nat | (n < N)}) => match Nat.eq_dec (proj1_sig x) (proj1_sig (exist (fun k : nat => (k < N)) m H3)) with
  | left _ => (Fmul f (Fopp f (FI f)) match le_lt_dec m (proj1_sig x) with
    | left _ => Mmult f N M N A B x y
    | right _ => Fopp f (Mmult f N M N A B x y)
  end)
  | right _ => (match le_lt_dec m (proj1_sig x) with
    | left _ => Mmult f N M N A B x y
    | right _ => Fopp f (Mmult f N M N A B x y)
  end)
end)).
move=> H4.
rewrite H4.
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (le_lt_dec (S m) (proj1_sig x)).
move=> H4.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (exist (fun k : nat => (k < N)) m H3))).
move=> H5.
apply False_ind.
apply (le_not_lt (proj1_sig x) m).
rewrite H5.
apply (le_n m).
apply H4.
move=> H5.
elim (le_lt_dec m (proj1_sig x)).
move=> H6.
reflexivity.
move=> H6.
apply False_ind.
apply (lt_irrefl m).
apply (lt_trans m (proj1_sig x) m H4 H6).
move=> H4.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (exist (fun k : nat => (k < N)) m H3))).
move=> H5.
elim (le_lt_dec m (proj1_sig x)).
move=> H6.
rewrite (Fopp_mul_distr_l_reverse f).
rewrite (Fmul_I_l f).
reflexivity.
move=> H6.
apply False_ind.
apply (lt_irrefl (proj1_sig x)).
rewrite {2} H5.
apply H6.
move=> H5.
elim (le_lt_dec m (proj1_sig x)).
move=> H6.
apply False_ind.
elim (le_lt_or_eq m (proj1_sig x) H6).
move=> H7.
apply (lt_irrefl (S m)).
apply (le_trans (S (S m)) (S (proj1_sig x)) (S m)).
apply le_n_S.
apply H7.
apply H4.
move=> H7.
apply H5.
rewrite - H7.
reflexivity.
move=> H6.
reflexivity.
suff: (Determinant f (M + N) (MBlockW f (M + N) M N (MBlockH f M N M (MI f M) A) (MBlockH f M N N B (MO f N N))) = Determinant f (M + N) (Mmult f (M + N) (M + N) (M + N) (MBlockW f (M + N) M N (MBlockH f M N M (MI f M) A) (MBlockH f M N N B (MO f N N))) (MBlockH f M N (M + N) (MBlockW f M M N (MI f M) (Mopp f M N B)) (MBlockW f N M N (MO f N M) (MI f N))))).
move=> H1.
rewrite H1.
rewrite (MBlockHWMult f (M + N) M N (M + N)).
rewrite (MBlockHMult f M N M).
rewrite (MBlockHMult f M N N).
rewrite (MBlockWMult f M M M).
rewrite (MBlockWMult f N M M).
rewrite (MBlockWMult f M N M).
rewrite (MBlockWMult f N N M).
rewrite (MBlockHPlus f M N (M + N)).
rewrite (MBlockWPlus f M M N).
rewrite (MBlockWPlus f N M N).
rewrite (Mmult_I_l f M M (MI f M)).
rewrite (Mmult_I_l f M N (Mopp f M N B)).
rewrite (Mmult_I_r f M N B).
rewrite (Mplus_comm f M N (Mopp f M N B) B).
rewrite (Mplus_opp_r f M N B).
rewrite (Mmult_I_r f N M A).
rewrite (Mmult_I_r f N N (MO f N N)).
rewrite (Mplus_comm f N N).
rewrite (Mplus_O_l f N N).
suff: ((Mmult f N M N A (Mopp f M N B)) = (Mopp f N N (Mmult f N M N A B))).
move=> H2.
rewrite H2.
suff: ((Mmult f N N M (MO f N N) (MO f N M)) = MO f N M).
move=> H3.
rewrite H3.
rewrite (Mplus_comm f N M A).
rewrite (Mplus_O_l f N M A).
suff: ((Mmult f M N M B (MO f N M)) = MO f M M).
move=> H4.
rewrite H4.
rewrite (Mplus_comm f M M).
rewrite (Mplus_O_l f M M).
unfold Determinant.
suff: (forall (m : {n : nat | (n < N)}), (M + proj1_sig m < M + N)).
move=> H5.
suff: (forall (P : Permutation N), Bijective (fun (m : {n : nat | (n < M + N)}) => match le_lt_dec M (proj1_sig m) with
  | left H => exist (fun (n : nat) => (n < M + N)) (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N m H)))) (H5 (proj1_sig P (proj1_sig (H37 M N m H))))
  | right _ => m
end)).
move=> H6.
rewrite (MySumF2Included (Permutation (M + N)) (FiniteIm (Permutation N) (Permutation (M + N)) (fun (P : (Permutation N)) => exist Bijective (fun (m : {n : nat | (n < M + N)}) => match le_lt_dec M (proj1_sig m) with
  | left H => exist (fun (n : nat) => (n < M + N)) (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N m H)))) (H5 (proj1_sig P (proj1_sig (H37 M N m H))))
  | right _ => m
end) (H6 P)) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))) (exist (Finite (Permutation (M + N))) (Full_set (Permutation (M + N))) (PermutationFinite (M + N)))).
rewrite (MySumF2O (Permutation (M + N)) (FiniteIntersection (Permutation (M + N)) (exist (Finite (Permutation (M + N))) (Full_set (Permutation (M + N))) (PermutationFinite (M + N))) (Complement (Permutation (M + N)) (proj1_sig (FiniteIm (Permutation N) (Permutation (M + N)) (fun P : Permutation N => exist Bijective (fun m : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig m) with
  | left H => exist (fun n : nat => (n < M + N)) (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N m H)))) (H5 (proj1_sig P (proj1_sig (H37 M N m H))))
  | right _ => m
end) (H6 P)) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))))))).
rewrite (CM_O_r (FPCM f)).
rewrite - (MySumF2BijectiveSame2 (Permutation N) (Permutation (M + N))).
unfold Basics.compose.
apply MySumF2Same.
move=> P H7.
suff: (PermutationParity N P = PermutationParity (M + N) (exist Bijective (fun m : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig m) with
  | left H => exist (fun n : nat => (n < M + N)) (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N m H)))) (H5 (proj1_sig P (proj1_sig (H37 M N m H))))
  | right _ => m
end) (H6 P))).
move=> H8.
rewrite H8.
apply (Fmul_eq_compat_l f).
rewrite (MySumF2Included {n : nat | (n < M + N)} (FiniteIm {n : nat | (n < N)} {n : nat | (n < M + N)} (fun (m : {n : nat | (n < N)}) => exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m) (H5 m)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))) (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N)))).
rewrite (MySumF2O {n : nat | (n < M + N)} (FiniteIntersection {n : nat | (n < M + N)} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N))) (Complement {n : nat | (n < M + N)} (proj1_sig (FiniteIm {n : nat | (n < N)} {n : nat | (n < M + N)} (fun m : {n : nat | (n < N)} => exist (fun n : nat => (n < M + N)) (M + proj1_sig m) (H5 m)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N))))))).
rewrite (CM_O_r (FMCM f)).
rewrite - (MySumF2BijectiveSame2 {n : nat | (n < N)} {n : nat | (n < M + N)}).
apply (MySumF2Same {n : nat | (n < N)} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)}) (CountFinite N)) (FMCM f)).
move=> x H9.
unfold Basics.compose.
simpl.
rewrite H35.
rewrite H36.
simpl.
elim (le_lt_dec M (M + proj1_sig x)).
move=> H10.
simpl.
elim (le_lt_dec M (Init.Nat.add M (@proj1_sig nat (fun n : nat => lt n N) (@proj1_sig (forall _ : @sig nat (fun n : nat => lt n N), @sig nat (fun n : nat => lt n N)) (fun f0 : forall _ : @sig nat (fun n : nat => lt n N), @sig nat (fun n : nat => lt n N) => @Bijective (@sig nat (fun n : nat => lt n N)) (@sig nat (fun n : nat => lt n N)) f0) P (@proj1_sig (@sig nat (fun n : nat => lt n N)) (fun y : @sig nat (fun n : nat => lt n N) => @eq nat (Init.Nat.add M (@proj1_sig nat (fun n : nat => lt n N) y)) (Init.Nat.add M (@proj1_sig nat (fun n : nat => lt n N) x))) (H37 M N (@exist nat (fun n : nat => lt n (Init.Nat.add M N)) (Init.Nat.add M (@proj1_sig nat (fun n : nat => lt n N) x)) (H5 x)) H10)))))).
move=> H11.
suff: ((proj1_sig (H37 M N (exist (fun n : nat => (n < M + N)) (M + proj1_sig x) (H5 x)) H10)) = x).
move=> H12.
suff: ((proj1_sig (H37 M N (exist (fun n : nat => (n < M + N)) (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig x) (H5 x)) H10)))) (H5 (proj1_sig P (proj1_sig (H37 M N (exist (fun n : nat => (n < M + N)) (M + proj1_sig x) (H5 x)) H10))))) H11)) = proj1_sig P x).
move=> H13.
rewrite H13.
rewrite H12.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun n : nat => (n < M + N)) (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig x) (H5 x)) H10)))) (H5 (proj1_sig P (proj1_sig (H37 M N (exist (fun n : nat => (n < M + N)) (M + proj1_sig x) (H5 x)) H10))))) H11))) (proj1_sig (proj1_sig P x)) M).
rewrite (proj2_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig x) (H5 x)) H10)))) (H5 (proj1_sig P (proj1_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig x) (H5 x)) H10))))) H11)).
rewrite H12.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun n : nat => (n < M + N)) (M + proj1_sig x) (H5 x)) H10))) (proj1_sig x) M).
apply (proj2_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig x) (H5 x)) H10)).
move=> H11.
apply False_ind.
apply (le_not_lt M (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig x) (H5 x)) H10))))).
apply le_plus_l.
apply H11.
move=> H10.
apply False_ind.
apply (le_not_lt M (M + proj1_sig x) (le_plus_l M (proj1_sig x)) H10).
move=> u1 u2 H9 H10 H11.
apply sig_map.
apply (plus_reg_l (proj1_sig u1) (proj1_sig u2) M).
suff: ((M + proj1_sig u1) = proj1_sig (exist (fun n : nat => (n < M + N)) (M + proj1_sig u1) (H5 u1))).
move=> H12.
rewrite H12.
rewrite H11.
reflexivity.
reflexivity.
move=> u H9.
rewrite H35.
rewrite H36.
simpl.
elim (le_lt_dec M (proj1_sig u)).
elim H9.
move=> u0 H10 H11 H12.
apply False_ind.
apply H10.
apply (Im_intro {n : nat | (n < N)} {n : nat | (n < M + N)} (Full_set {n : nat | (n < N)}) (fun (m : {n : nat | (n < N)}) => exist (fun n : nat => (n < M + N)) (M + proj1_sig m) (H5 m)) (proj1_sig (H37 M N u0 H12))).
apply (Full_intro {n : nat | (n < N)}).
apply sig_map.
simpl.
rewrite (proj2_sig (H37 M N u0 H12)).
reflexivity.
move=> H10.
elim (le_lt_dec M (proj1_sig u)).
move=> H11.
apply False_ind.
apply (le_not_lt M (proj1_sig u) H11 H10).
move=> H11.
unfold MI.
elim (Nat.eq_dec (proj1_sig (exist (fun n : nat => (n < M)) (proj1_sig u) H10)) (proj1_sig (exist (fun n : nat => (n < M)) (proj1_sig u) H11))).
move=> H12.
reflexivity.
move=> H12.
apply False_ind.
apply H12.
suff: (H10 = H11).
move=> H13.
rewrite H13.
reflexivity.
apply proof_irrelevance.
move=> m H9.
apply (Full_intro {n : nat | (n < M + N)} m).
unfold PermutationParity.
simpl.
rewrite (MySumF2Included ({n : nat | (n < M + N)} * {n : nat | (n < M + N)}) (FiniteIm ({n : nat | (n < N)} * {n : nat | (n < N)}) ({n : nat | (n < M + N)} * {n : nat | (n < M + N)}) (fun (m : ({n : nat | (n < N)} * {n : nat | (n < N)})) => (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig (fst m)) (H5 (fst m)),exist (fun (n : nat) => (n < M + N)) (M + proj1_sig (snd m)) (H5 (snd m)))) (exist (Finite ({n : nat | (n < N)} * {n : nat | (n < N)})) (fun xy : {n : nat | (n < N)} * {n : nat | (n < N)} => (proj1_sig (fst xy) < proj1_sig (snd xy))) (PermutationParitySub N)))).
rewrite (MySumF2O ({n : nat | (n < M + N)} * {n : nat | (n < M + N)}) (FiniteIntersection ({n : nat | (n < M + N)} * {n : nat | (n < M + N)}) (exist (Finite ({n : nat | (n < M + N)} * {n : nat | (n < M + N)})) (fun (xy : {n : nat | (n < M + N)} * {n : nat | (n < M + N)}) => (proj1_sig (fst xy) < proj1_sig (snd xy))) (PermutationParitySub (M + N))) (Complement ({n : nat | (n < M + N)} * {n : nat | (n < M + N)}) (proj1_sig (FiniteIm ({n : nat | (n < N)} * {n : nat | (n < N)}) ({n : nat | (n < M + N)} * {n : nat | (n < M + N)}) (fun m : {n : nat | (n < N)} * {n : nat | (n < N)} => (exist (fun n : nat => (n < M + N)) (M + proj1_sig (fst m)) (H5 (fst m)), exist (fun n : nat => (n < M + N)) (M + proj1_sig (snd m)) (H5 (snd m)))) (exist (Finite ({n : nat | (n < N)} * {n : nat | (n < N)})) (fun xy : {n : nat | (n < N)} * {n : nat | (n < N)} => (proj1_sig (fst xy) < proj1_sig (snd xy))) (PermutationParitySub N))))))).
rewrite CM_O_r.
rewrite - (MySumF2BijectiveSame2 ({n : nat | (n < N)} * {n : nat | (n < N)}) ({n : nat | (n < M + N)} * {n : nat | (n < M + N)})).
apply (MySumF2Same ({n : nat | (n < N)} * {n : nat | (n < N)}) (exist (Finite ({n : nat | (n < N)} * {n : nat | (n < N)})) (fun (xy : {n : nat | (n < N)} * {n : nat | (n < N)}) => (proj1_sig (fst xy) < proj1_sig (snd xy))) (PermutationParitySub N)) ParityXORCM).
move=> xy H8.
unfold Basics.compose.
simpl.
elim (le_lt_dec M (M + proj1_sig (fst xy))).
move=> H9.
elim (le_lt_dec M (M + proj1_sig (snd xy))).
move=> H10.
simpl.
suff: ((proj1_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig (fst xy)) (H5 (fst xy))) H9)) = fst xy).
move=> H11.
rewrite H11.
suff: ((proj1_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig (snd xy)) (H5 (snd xy))) H10)) = snd xy).
move=> H12.
rewrite H12.
elim (excluded_middle_informative (proj1_sig (proj1_sig P (fst xy)) < proj1_sig (proj1_sig P (snd xy)))).
move=> H13.
elim (excluded_middle_informative (M + proj1_sig (proj1_sig P (fst xy)) < M + proj1_sig (proj1_sig P (snd xy)))).
move=> H14.
reflexivity.
move=> H14.
apply False_ind.
apply H14.
apply plus_lt_compat_l.
apply H13.
move=> H13.
elim (excluded_middle_informative (M + proj1_sig (proj1_sig P (fst xy)) < M + proj1_sig (proj1_sig P (snd xy)))).
move=> H14.
apply False_ind.
apply H13.
apply (plus_lt_reg_l (proj1_sig (proj1_sig P (fst xy))) (proj1_sig (proj1_sig P (snd xy))) M H14).
move=> H14.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun n : nat => (n < M + N)) (M + proj1_sig (snd xy)) (H5 (snd xy))) H10))) (proj1_sig (snd xy)) M).
apply (proj2_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig (snd xy)) (H5 (snd xy))) H10)).
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun n : nat => (n < M + N)) (M + proj1_sig (fst xy)) (H5 (fst xy))) H9))) (proj1_sig (fst xy)) M).
apply (proj2_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig (fst xy)) (H5 (fst xy))) H9)).
move=> H10.
apply False_ind.
apply (le_not_lt M (M + proj1_sig (snd xy)) (le_plus_l M (proj1_sig (snd xy))) H10).
move=> H9.
apply False_ind.
apply (le_not_lt M (M + proj1_sig (fst xy)) (le_plus_l M (proj1_sig (fst xy))) H9).
move=> u1 u2 H8 H9 H10.
apply injective_projections.
apply sig_map.
apply (plus_reg_l (proj1_sig (fst u1)) (proj1_sig (fst u2)) M).
suff: ((M + proj1_sig (fst u1)) = proj1_sig (fst (exist (fun n : nat => (n < M + N)) (M + proj1_sig (fst u1)) (H5 (fst u1)), exist (fun n : nat => (n < M + N)) (M + proj1_sig (snd u1)) (H5 (snd u1))))).
move=> H11.
rewrite H11.
rewrite H10.
reflexivity.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (snd u1)) (proj1_sig (snd u2)) M).
suff: ((M + proj1_sig (snd u1)) = proj1_sig (snd (exist (fun n : nat => (n < M + N)) (M + proj1_sig (fst u1)) (H5 (fst u1)), exist (fun n : nat => (n < M + N)) (M + proj1_sig (snd u1)) (H5 (snd u1))))).
move=> H11.
rewrite H11.
rewrite H10.
reflexivity.
reflexivity.
move=> u H8.
elim (le_lt_dec M (proj1_sig (fst u))).
elim (le_lt_dec M (proj1_sig (snd u))).
elim H8.
move=> u0 H9 H10 H11 H12.
apply False_ind.
apply H9.
apply (Im_intro ({n : nat | (n < N)} * {n : nat | (n < N)}) ({n : nat | (n < M + N)} * {n : nat | (n < M + N)}) (fun (xy : {n : nat | (n < N)} * {n : nat | (n < N)}) => (proj1_sig (fst xy) < proj1_sig (snd xy))) (fun m : {n : nat | (n < N)} * {n : nat | (n < N)} => (exist (fun n : nat => (n < M + N)) (M + proj1_sig (fst m)) (H5 (fst m)), exist (fun n : nat => (n < M + N)) (M + proj1_sig (snd m)) (H5 (snd m)))) (proj1_sig (H37 M N (fst u0) H12), proj1_sig (H37 M N (snd u0) H11))).
apply (plus_lt_reg_l (proj1_sig (proj1_sig (H37 M N (fst u0) H12))) (proj1_sig (proj1_sig (H37 M N (snd u0) H11))) M).
rewrite (proj2_sig (H37 M N (fst u0) H12)).
rewrite (proj2_sig (H37 M N (snd u0) H11)).
apply H10.
apply injective_projections.
apply sig_map.
simpl.
rewrite (proj2_sig (H37 M N (fst u0) H12)).
reflexivity.
apply sig_map.
simpl.
rewrite (proj2_sig (H37 M N (snd u0) H11)).
reflexivity.
elim H8.
move=> u0 H9 H10 H11 H12.
apply False_ind.
apply (le_not_lt M (proj1_sig (fst u0)) H12 (lt_trans (proj1_sig (fst u0)) (proj1_sig (snd u0)) M H10 H11)).
elim (le_lt_dec M (proj1_sig (snd u))).
move=> H9 H10.
simpl.
elim (excluded_middle_informative (proj1_sig (fst u) < M + proj1_sig (proj1_sig P (proj1_sig (H37 M N (snd u) H9))))).
move=> H11.
reflexivity.
move=> H11.
apply False_ind.
apply H11.
apply (le_trans (S (proj1_sig (fst u))) M (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N (snd u) H9))))).
apply H10.
apply le_plus_l.
move=> H9 H10.
elim (excluded_middle_informative (proj1_sig (fst u) < proj1_sig (snd u))).
move=> H11.
reflexivity.
move=> H11.
apply False_ind.
apply H11.
elim H8.
move=> u0 H12 H13.
apply H13.
move=> m.
elim.
move=> x H8 y H9.
rewrite H9.
apply (plus_lt_compat_l (proj1_sig (fst x)) (proj1_sig (snd x)) M H8).
move=> u1 u2 H7 H8 H9.
apply sig_map.
apply functional_extensionality.
move=> m.
apply sig_map.
suff: (proj1_sig (proj1_sig u1 m) = proj1_sig (proj1_sig (exist Bijective (fun m : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig m) with
  | left H => exist (fun n : nat => (n < M + N)) (M + proj1_sig (proj1_sig u1 (proj1_sig (H37 M N m H)))) (H5 (proj1_sig u1 (proj1_sig (H37 M N m H))))
  | right _ => m
end) (H6 u1)) (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m) (H5 m))) - M).
move=> H10.
rewrite H10.
rewrite H9.
simpl.
elim (le_lt_dec M (M + proj1_sig m)).
move=> H11.
suff: ((proj1_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig m) (H5 m)) H11)) = m).
move=> H12.
rewrite H12.
apply minus_plus.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m) (H5 m)) H11))) (proj1_sig m) M).
apply (proj2_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig m) (H5 m)) H11)).
move=> H11.
apply False_ind.
apply (le_not_lt M (M + proj1_sig m)).
apply le_plus_l.
apply H11.
simpl.
elim (le_lt_dec M (M + proj1_sig m)).
move=> H10.
suff: ((proj1_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig m) (H5 m)) H10)) = m).
move=> H11.
rewrite H11.
simpl.
rewrite minus_plus.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m) (H5 m)) H10))) (proj1_sig m) M).
apply (proj2_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig m) (H5 m)) H10)).
move=> H10.
apply False_ind.
apply (le_not_lt M (M + proj1_sig m)).
apply le_plus_l.
apply H10.
move=> u H7.
suff: (exists (k : {n : nat | (n < M + N)}), MBlockH f M N (M + N) (MBlockW f M M N (MI f M) (MO f M N)) (MBlockW f N M N A (Mopp f N N (Mmult f N M N A B))) k (proj1_sig u k) = FO f).
elim.
move=> k H8.
rewrite (MySumF2Included {n : nat | (n < M + N)} (FiniteSingleton {n : nat | (n < M + N)} k)).
rewrite MySumF2Singleton.
rewrite H8.
simpl.
rewrite (Fmul_O_l f).
apply (Fmul_O_r f).
move=> l H9.
apply (Full_intro {n : nat | (n < M + N)} l).
elim H7.
move=> u0 H8 H9.
apply NNPP.
move=> H10.
apply H8.
suff: (forall (m : {n : nat | (n < M + N)}), (proj1_sig m < M) -> (proj1_sig u0 m) = m).
move=> H20.
suff: (forall (m : {n : nat | (n < M + N)}), (M <= proj1_sig m) -> (M <= proj1_sig (proj1_sig u0 m))).
move=> H11.
suff: (exists (P : Permutation N), forall (m : {n : nat | (n < N)}), proj1_sig (proj1_sig u0 (exist (fun n : nat => n < M + N) (M + proj1_sig m) (H5 m))) = M + proj1_sig (proj1_sig P m)).
elim.
move=> P H12.
apply (Im_intro (Permutation N) (Permutation (M + N)) (Full_set (Permutation N)) (fun (P : Permutation N) => exist Bijective (fun m : {n : nat | (n < M + N)} => match le_lt_dec M (proj1_sig m) with
  | left H => exist (fun n : nat => (n < M + N)) (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N m H)))) (H5 (proj1_sig P (proj1_sig (H37 M N m H))))
  | right _ => m
end) (H6 P)) P).
apply (Full_intro (Permutation N) P).
apply sig_map.
apply functional_extensionality.
move=> m.
simpl.
elim (le_lt_dec M (proj1_sig m)).
move=> H13.
apply sig_map.
suff: (m = (exist (fun n : nat => (n < M + N)) (M + proj1_sig (proj1_sig (H37 M N m H13))) (H5 (proj1_sig (H37 M N m H13))))).
move=> H14.
rewrite {1} H14.
apply (H12 (proj1_sig (H37 M N m H13))).
apply sig_map.
simpl.
rewrite (proj2_sig (H37 M N m H13)).
reflexivity.
move=> H13.
apply (H20 m H13).
suff: (forall (m : {n : nat | (n < N)}), M <= M + proj1_sig m).
move=> H12.
suff: (Bijective (fun (m : {n : nat | (n < N)}) => proj1_sig (H37 M N (proj1_sig u0 (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m) (H5 m))) (H11 (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m) (H5 m)) (H12 m))))).
move=> H13.
exists (exist Bijective (fun (m : {n : nat | (n < N)}) => proj1_sig (H37 M N (proj1_sig u0 (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m) (H5 m))) (H11 (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m) (H5 m)) (H12 m)))) H13).
simpl.
move=> m.
rewrite (proj2_sig (H37 M N (proj1_sig u0 (exist (fun n : nat => n < M + N) (M + proj1_sig m) (H5 m))) (H11 (exist (fun n : nat => n < M + N) (M + proj1_sig m) (H5 m)) (H12 m)))).
reflexivity.
apply CountInjBij.
move=> m1 m2 H13.
suff: ((exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m1) (H5 m1)) = (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m2) (H5 m2))).
move=> H14.
apply sig_map.
apply (plus_reg_l (proj1_sig m1) (proj1_sig m2) M).
suff: ((M + proj1_sig m1) = proj1_sig (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig m1) (H5 m1))).
move=> H15.
rewrite H15.
rewrite H14.
reflexivity.
reflexivity.
apply (BijInj {n : nat | (n < M + N)} {n : nat | (n < M + N)} (proj1_sig u0) (proj2_sig u0)).
apply sig_map.
rewrite - (proj2_sig (H37 M N (proj1_sig u0 (exist (fun n : nat => (n < M + N)) (M + proj1_sig m1) (H5 m1))) (H11 (exist (fun n : nat => (n < M + N)) (M + proj1_sig m1) (H5 m1)) (H12 m1)))).
rewrite H13.
rewrite (proj2_sig (H37 M N (proj1_sig u0 (exist (fun n : nat => (n < M + N)) (M + proj1_sig m2) (H5 m2))) (H11 (exist (fun n : nat => (n < M + N)) (M + proj1_sig m2) (H5 m2)) (H12 m2)))).
reflexivity.
move=> m.
apply le_plus_l.
move=> m H11.
elim (le_or_lt M (proj1_sig (proj1_sig u0 m))).
apply.
move=> H12.
apply False_ind.
apply (lt_irrefl (proj1_sig m)).
suff: (m = (proj1_sig u0 m)).
move=> H13.
rewrite {1} H13.
apply (le_trans (S (proj1_sig (proj1_sig u0 m))) M (proj1_sig m) H12 H11).
apply (BijInj {n : nat | (n < M + N)} {n : nat | (n < M + N)} (proj1_sig u0) (proj2_sig u0)).
rewrite (H20 (proj1_sig u0 m) H12).
reflexivity.
move=> m H11.
apply NNPP.
move=> H12.
apply H10.
exists m.
rewrite H35.
rewrite H36.
elim (le_lt_dec M (proj1_sig m)).
move=> H13.
apply False_ind.
apply (le_not_lt M (proj1_sig m) H13 H11).
move=> H13.
elim (le_lt_dec M (proj1_sig (proj1_sig u0 m))).
move=> H14.
reflexivity.
move=> H14.
unfold MI.
simpl.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig (proj1_sig u0 m))).
move=> H15.
apply False_ind.
apply H12.
apply sig_map.
rewrite H15.
reflexivity.
move=> H15.
reflexivity.
move=> P H7.
apply (Full_intro (Permutation (M + N)) P).
move=> P.
elim (proj2_sig P).
move=> Pinv H6.
exists (fun (m : {n : nat | (n < M + N)}) => match le_lt_dec M (proj1_sig m) with
  | left H => exist (fun n : nat => (n < M + N)) (M + proj1_sig (Pinv (proj1_sig (H37 M N m H)))) (H5 (Pinv (proj1_sig (H37 M N m H))))
  | right _ => m
end).
apply conj.
move=> m.
elim (le_lt_dec M (proj1_sig m)).
move=> H7.
simpl.
elim (le_lt_dec M (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N m H7))))).
move=> H8.
apply sig_map.
simpl.
suff: ((proj1_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N m H7)))) (H5 (proj1_sig P (proj1_sig (H37 M N m H7))))) H8)) = (proj1_sig P (proj1_sig (H37 M N m H7)))).
move=> H9.
rewrite H9.
rewrite (proj1 H6).
apply (proj2_sig (H37 M N m H7)).
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun n : nat => (n < M + N)) (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N m H7)))) (H5 (proj1_sig P (proj1_sig (H37 M N m H7))))) H8))) (proj1_sig (proj1_sig P (proj1_sig (H37 M N m H7)))) M).
apply (proj2_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N m H7)))) (H5 (proj1_sig P (proj1_sig (H37 M N m H7))))) H8)).
move=> H8.
apply False_ind.
apply (le_not_lt M (M + proj1_sig (proj1_sig P (proj1_sig (H37 M N m H7))))).
apply le_plus_l.
apply H8.
move=> H7.
elim (le_lt_dec M (proj1_sig m)).
move=> H8.
apply False_ind.
apply (le_not_lt M (proj1_sig m) H8 H7).
move=> H8.
reflexivity.
move=> m.
elim (le_lt_dec M (proj1_sig m)).
move=> H7.
simpl.
elim (le_lt_dec M (M + proj1_sig (Pinv (proj1_sig (H37 M N m H7))))).
move=> H8.
apply sig_map.
simpl.
suff: ((proj1_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig (Pinv (proj1_sig (H37 M N m H7)))) (H5 (Pinv (proj1_sig (H37 M N m H7))))) H8)) = (Pinv (proj1_sig (H37 M N m H7)))).
move=> H9.
rewrite H9.
rewrite (proj2 H6).
apply (proj2_sig (H37 M N m H7)).
apply sig_map.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N (exist (fun n : nat => (n < M + N)) (M + proj1_sig (Pinv (proj1_sig (H37 M N m H7)))) (H5 (Pinv (proj1_sig (H37 M N m H7))))) H8))) (proj1_sig (Pinv (proj1_sig (H37 M N m H7)))) M).
apply (proj2_sig (H37 M N (exist (fun n : nat => n < M + N) (M + proj1_sig (Pinv (proj1_sig (H37 M N m H7)))) (H5 (Pinv (proj1_sig (H37 M N m H7))))) H8)).
move=> H8.
apply False_ind.
apply (le_not_lt M (M + proj1_sig (Pinv (proj1_sig (H37 M N m H7))))).
apply le_plus_l.
apply H8.
move=> H7.
elim (le_lt_dec M (proj1_sig m)).
move=> H8.
apply False_ind.
apply (le_not_lt M (proj1_sig m) H8 H7).
move=> H8.
reflexivity.
move=> m.
apply (plus_lt_compat_l (proj1_sig m) N M (proj2_sig m)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
rewrite MySumF2O.
reflexivity.
move=> u H4.
apply (Fmul_O_r f (B x u)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
rewrite MySumF2O.
reflexivity.
move=> u H3.
apply (Fmul_O_r f (FO f)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
unfold Mopp.
apply (FiniteSetInduction {n : nat | (n < M)} (exist (Finite (Count M)) (Full_set {n : nat | (n < M)}) (CountFinite M))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite (Fopp_O f).
reflexivity.
move=> C c H2 H3 H4 H5.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite (Fopp_add_distr f).
rewrite H5.
rewrite (Fopp_mul_distr_r f).
reflexivity.
apply H4.
apply H4.
suff: (forall (k : nat) (C : Matrix f M N), cardinal ({n : nat | (n < M)} * {n : nat | (n < N)}) (fun (xy : ({n : nat | (n < M)} * {n : nat | (n < N)})) => C (fst xy) (snd xy) <> FO f) k -> Determinant f (M + N) (MBlockW f (M + N) M N (MBlockH f M N M (MI f M) A) (MBlockH f M N N B (MO f N N))) = Determinant f (M + N) (Mmult f (M + N) (M + N) (M + N) (MBlockW f (M + N) M N (MBlockH f M N M (MI f M) A) (MBlockH f M N N B (MO f N N))) (MBlockH f M N (M + N) (MBlockW f M M N (MI f M) C) (MBlockW f N M N (MO f N M) (MI f N))))).
move=> H5.
suff: (Finite ({n : nat | (n < M)} * {n : nat | (n < N)}) (fun (xy : {n : nat | (n < M)} * {n : nat | (n < N)}) => (Mopp f M N B) (fst xy) (snd xy) <> FO f)).
move=> H6.
elim (finite_cardinal ({n : nat | (n < M)} * {n : nat | (n < N)}) (fun (xy : {n : nat | (n < M)} * {n : nat | (n < N)}) => (Mopp f M N B) (fst xy) (snd xy) <> FO f) H6).
move=> n H7.
apply (H5 n (Mopp f M N B) H7).
apply (Finite_downward_closed ({n : nat | (n < M)} * {n : nat | (n < N)}) (Full_set ({n : nat | (n < M)} * {n : nat | (n < N)}))).
apply CountFiniteBijective.
exists (M * N).
elim (CountMult M N).
move=> g.
elim.
move=> h H7.
exists h.
exists g.
apply conj.
apply (proj2 H7).
apply (proj1 H7).
move=> xy H6.
apply (Full_intro ({n : nat | (n < M)} * {n : nat | (n < N)}) xy).
elim.
move=> C H1.
suff: ((MBlockH f M N (M + N) (MBlockW f M M N (MI f M) C) (MBlockW f N M N (MO f N M) (MI f N))) = (MI f (M + N))).
move=> H2.
rewrite H2.
rewrite (Mmult_I_r f (M + N) (M + N)).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite H35.
rewrite H36.
elim (le_lt_dec M (proj1_sig x)).
move=> H2.
elim (le_lt_dec M (proj1_sig y)).
move=> H3.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H4.
elim (Nat.eq_dec (proj1_sig (proj1_sig (H37 M N x H2))) (proj1_sig (proj1_sig (H37 M N y H3)))).
move=> H5.
reflexivity.
move=> H5.
apply False_ind.
apply H5.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N x H2))) (proj1_sig (proj1_sig (H37 M N y H3))) M).
rewrite (proj2_sig (H37 M N x H2)).
rewrite (proj2_sig (H37 M N y H3)).
apply H4.
move=> H4.
elim (Nat.eq_dec (proj1_sig (proj1_sig (H37 M N x H2))) (proj1_sig (proj1_sig (H37 M N y H3)))).
move=> H5.
apply False_ind.
apply H4.
rewrite - (proj2_sig (H37 M N x H2)).
rewrite H5.
apply (proj2_sig (H37 M N y H3)).
move=> H5.
reflexivity.
move=> H3.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H4.
apply False_ind.
apply (lt_irrefl (proj1_sig x)).
rewrite {1} H4.
apply (le_trans (S (proj1_sig y)) M (proj1_sig x) H3 H2).
move=> H4.
reflexivity.
move=> H2.
elim (le_lt_dec M (proj1_sig y)).
move=> H3.
suff: (~ In ({n : nat | (n < M)} * {n : nat | (n < N)}) (fun (xy : {n : nat | (n < M)} * {n : nat | (n < N)}) => C (fst xy) (snd xy) <> FO f) ((exist (fun n : nat => (n < M)) (proj1_sig x) H2), (proj1_sig (H37 M N y H3)))).
move=> H4.
apply NNPP.
move=> H5.
apply H4.
simpl.
move=> H6.
apply H5.
rewrite H6.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H7.
apply False_ind.
apply (lt_irrefl (proj1_sig x)).
rewrite {2} H7.
apply (le_trans (S (proj1_sig x)) M (proj1_sig y) H2 H3).
move=> H7.
reflexivity.
rewrite (cardinal_elim ({n : nat | (n < M)} * {n : nat | (n < N)}) (fun (xy : ({n : nat | (n < M)} * {n : nat | (n < N)})) => C (fst xy) (snd xy) <> FO f) O H1).
elim.
move=> H3.
reflexivity.
move=> n H1 C H2.
elim (cardinal_invert ({n : nat | (n < M)} * {n : nat | (n < N)}) (fun (xy : ({n : nat | (n < M)} * {n : nat | (n < N)})) => C (fst xy) (snd xy) <> FO f) (S n) H2).
move=> D.
elim.
move=> d H3.
suff: ((MBlockH f M N (M + N) (MBlockW f M M N (MI f M) C) (MBlockW f N M N (MO f N M) (MI f N))) = Mmult f (M + N) (M + N) (M + N) (MBlockH f M N (M + N) (MBlockW f M M N (MI f M) (fun (x : {n : nat | (n < M)}) (y : {n : nat | (n < N)}) => match excluded_middle_informative ((x, y) = d) with
  | left _ => FO f
  | right _ => C x y
end)) (MBlockW f N M N (MO f N M) (MI f N))) (Mplus f (M + N) (M + N) (MI f (M + N)) (fun (x y : {n : nat | (n < M + N)}) => match excluded_middle_informative (proj1_sig x = proj1_sig (fst d) /\ proj1_sig y = M + proj1_sig (snd d)) with
  | left _ => C (fst d) (snd d)
  | right _ => FO f
end))).
move=> H4.
rewrite H4.
rewrite - (Mmult_assoc f).
rewrite (H1 (fun (x : {n : nat | (n < M)}) (y : {n : nat | (n < N)}) => match excluded_middle_informative ((x, y) = d) with
  | left _ => FO f
  | right _ => C x y
end)).
suff: (proj1_sig (fst d) < M + N).
move=> H5.
suff: (M + proj1_sig (snd d) < M + N).
move=> H6.
rewrite - (DeterminantAddTransformW f (M + N) (Mmult f (M + N) (M + N) (M + N) (MBlockW f (M + N) M N (MBlockH f M N M (MI f M) A) (MBlockH f M N N B (MO f N N))) (MBlockH f M N (M + N) (MBlockW f M M N (MI f M) (fun (x : {n0 : nat | (n0 < M)}) (y : {n0 : nat | (n0 < N)}) => match excluded_middle_informative ((x, y) = d) with
  | left _ => FO f
  | right _ => C x y
end)) (MBlockW f N M N (MO f N M) (MI f N)))) (exist (fun (n : nat) => (n < M + N)) (proj1_sig (fst d)) H5) (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig (snd d)) H6) (C (fst d) (snd d))).
suff: (forall (X : Matrix f (M + N) (M + N)), (fun (x y : {n : nat | (n < M + N)}) => match Nat.eq_dec (proj1_sig y) (proj1_sig (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig (snd d)) H6)) with
  | left _ => Fadd f (X x y) (Fmul f (C (fst d) (snd d)) (X x (exist (fun (n : nat) => (n < M + N)) (proj1_sig (fst d)) H5)))
  | right _ => X x y
end) = (Mmult f (M + N) (M + N) (M + N) X (Mplus f (M + N) (M + N) (MI f (M + N)) (fun (x y : {n : nat | (n < M + N)}) => match excluded_middle_informative (proj1_sig x = proj1_sig (fst d) /\ proj1_sig y = (M + proj1_sig (snd d))) with
  | left _ => C (fst d) (snd d)
  | right _ => FO f
end)))).
move=> H7.
rewrite H7.
reflexivity.
move=> X.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite (Mmult_plus_distr_l f).
rewrite (Mmult_I_r f).
unfold Mmult.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (exist (fun (n : nat) => (n < M + N)) (M + proj1_sig (snd d)) H6))).
simpl.
move=> H7.
unfold Mplus.
rewrite (MySumF2Included {n : nat | (n < M + N)} (FiniteSingleton {n : nat | (n < M + N)} (exist (fun (n : nat) => (n < M + N)) (proj1_sig (fst d)) H5))).
rewrite (MySumF2O {n : nat | (n < M + N)} (FiniteIntersection {n : nat | (n < M + N)} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N))) (Complement {n : nat | (n < M + N)} (proj1_sig (FiniteSingleton {n : nat | (n < M + N)} (exist (fun (n : nat) => (n < M + N)) (proj1_sig (fst d)) H5)))))).
rewrite MySumF2Singleton.
rewrite (CM_O_r (FPCM f)).
elim (excluded_middle_informative (proj1_sig (exist (fun (n : nat) => (n < M + N)) (proj1_sig (fst d)) H5) = proj1_sig (fst d) /\ proj1_sig y = (M + proj1_sig (snd d)))).
move=> H8.
rewrite (Fmul_comm f).
reflexivity.
move=> H8.
apply False_ind.
apply H8.
apply conj.
reflexivity.
apply H7.
move=> u.
elim.
move=> u0 H8 H9.
elim (excluded_middle_informative (proj1_sig u0 = proj1_sig (fst d) /\ proj1_sig y = (M + proj1_sig (snd d)))).
move=> H10.
apply False_ind.
apply H8.
suff: (u0 = (exist (fun (n : nat) => (n < M + N)) (proj1_sig (fst d)) H5)).
move=> H11.
rewrite H11.
apply In_singleton.
apply sig_map.
apply (proj1 H10).
move=> H10.
apply (Fmul_O_r f).
move=> k H8.
apply (Full_intro {n : nat | (n < M + N)} k).
simpl.
move=> H7.
unfold Mplus.
rewrite MySumF2O.
rewrite (Fadd_O_r f).
reflexivity.
move=> u H8.
elim (excluded_middle_informative (proj1_sig u = proj1_sig (fst d) /\ proj1_sig y = (M + proj1_sig (snd d)))).
move=> H9.
apply False_ind.
apply H7.
apply (proj2 H9).
move=> H9.
apply (Fmul_O_r f).
simpl.
move=> H7.
apply (lt_irrefl (proj1_sig (fst d))).
rewrite {2} H7.
apply (le_trans (S (proj1_sig (fst d))) M (M + proj1_sig (snd d)) (proj2_sig (fst d))).
apply le_plus_l.
apply (plus_lt_compat_l (proj1_sig (snd d)) N M (proj2_sig (snd d))).
apply (le_trans (S (proj1_sig (fst d))) M (M + N) (proj2_sig (fst d))).
apply le_plus_l.
suff: ((fun (xy : {n : nat | (n < M)} * {n : nat | (n < N)}) => (match excluded_middle_informative ((fst xy, snd xy) = d) with
  | left _ => FO f
  | right _ => C (fst xy) (snd xy)
end) <> FO f) = D).
move=> H5.
rewrite H5.
apply (proj2 (proj2 H3)).
apply Extensionality_Ensembles.
apply conj.
move=> xy.
unfold In.
elim (excluded_middle_informative ((fst xy, snd xy) = d)).
move=> H5 H6.
apply False_ind.
apply H6.
reflexivity.
move=> H5 H6.
suff: (In ({n : nat | (n < M)} * {n : nat | (n < N)}) (fun (xy : {n : nat | (n < M)} * {n : nat | (n < N)}) => C (fst xy) (snd xy) <> FO f) xy).
rewrite (proj1 H3).
move=> H7.
suff: ((fst xy, snd xy) <> d).
elim H7.
move=> xy0 H8 H9.
apply H8.
move=> xy0 H8 H9.
apply False_ind.
apply H9.
elim H8.
apply injective_projections.
reflexivity.
reflexivity.
apply H5.
apply H6.
move=> xy H5.
unfold In.
elim (excluded_middle_informative ((fst xy, snd xy) = d)).
move=> H6.
apply False_ind.
apply (proj1 (proj2 H3)).
suff: (d = xy).
move=> H7.
rewrite H7.
apply H5.
rewrite - H6.
apply injective_projections.
reflexivity.
reflexivity.
move=> H6.
suff: (In ({n : nat | (n < M)} * {n : nat | (n < N)}) (fun (xy : {n : nat | (n < M)} * {n : nat | (n < N)}) => C (fst xy) (snd xy) <> FO f) xy).
apply.
rewrite (proj1 H3).
left.
apply H5.
rewrite (Mmult_plus_distr_l f).
rewrite (Mmult_I_r f).
unfold Mmult.
unfold Mplus.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (proj1_sig (fst d) < M + N).
move=> H4.
rewrite (MySumF2Included {n : nat | (n < M + N)} (FiniteSingleton {n : nat | (n < M + N)} (exist (fun (n : nat) => (n < M + N)) (proj1_sig (fst d)) H4))).
rewrite (MySumF2O {n : nat | (n < M + N)} (FiniteIntersection {n : nat | (n < M + N)} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)}) (CountFinite (M + N))) (Complement {n : nat | (n < M + N)} (proj1_sig (FiniteSingleton {n : nat | (n < M + N)} (exist (fun (n : nat) => (n < M + N)) (proj1_sig (fst d)) H4)))))).
rewrite (CM_O_r (FPCM f)).
rewrite MySumF2Singleton.
simpl.
elim (excluded_middle_informative (proj1_sig (fst d) = proj1_sig (fst d) /\ proj1_sig y = (M + proj1_sig (snd d)))).
move=> H5.
rewrite H35.
rewrite H36.
elim (le_lt_dec M (proj1_sig x)).
move=> H6.
elim (le_lt_dec M (proj1_sig y)).
move=> H7.
simpl.
elim (le_lt_dec M (proj1_sig (fst d))).
move=> H8.
apply False_ind.
apply (le_not_lt M (proj1_sig (fst d)) H8 (proj2_sig (fst d))).
move=> H8.
unfold MO.
rewrite (Fmul_O_l f).
rewrite (Fadd_O_r f).
reflexivity.
move=> H7.
apply False_ind.
apply (le_not_lt M (proj1_sig y)).
rewrite (proj2 H5).
apply le_plus_l.
apply H7.
move=> H6.
elim (le_lt_dec M (proj1_sig y)).
move=> H7.
simpl.
elim (le_lt_dec M (proj1_sig (fst d))).
move=> H8.
apply False_ind.
apply (le_not_lt M (proj1_sig (fst d)) H8 (proj2_sig (fst d))).
move=> H8.
elim (excluded_middle_informative ((exist (fun (n : nat) => (n < M)) (proj1_sig x) H6, proj1_sig (H37 M N y H7)) = d)).
move=> H9.
rewrite (Fadd_O_l f).
unfold MI.
elim (Nat.eq_dec (proj1_sig (exist (fun n0 : nat => (n0 < M)) (proj1_sig x) H6)) (proj1_sig (exist (fun n0 : nat => (n0 < M)) (proj1_sig (fst d)) H8))).
move=> H10.
rewrite (Fmul_I_l f).
rewrite - H9.
reflexivity.
move=> H10.
apply False_ind.
apply H10.
simpl.
rewrite - H9.
reflexivity.
move=> H9.
unfold MI.
elim (Nat.eq_dec (proj1_sig (exist (fun n0 : nat => (n0 < M)) (proj1_sig x) H6)) (proj1_sig (exist (fun n0 : nat => (n0 < M)) (proj1_sig (fst d)) H8))).
move=> H10.
apply False_ind.
apply H9.
apply injective_projections.
apply sig_map.
simpl.
apply H10.
apply sig_map.
simpl.
apply (plus_reg_l (proj1_sig (proj1_sig (H37 M N y H7))) (proj1_sig (snd d)) M).
rewrite (proj2_sig (H37 M N y H7)).
apply (proj2 H5).
move=> H10.
rewrite (Fmul_O_l f).
rewrite (Fadd_O_r f).
reflexivity.
move=> H7.
apply False_ind.
apply (le_not_lt M (proj1_sig y)).
rewrite (proj2 H5).
apply le_plus_l.
apply H7.
move=> H5.
rewrite (Fmul_O_r f).
rewrite (Fadd_O_r f).
rewrite H35.
rewrite H36.
elim (le_lt_dec M (proj1_sig x)).
move=> H6.
reflexivity.
move=> H6.
elim (le_lt_dec M (proj1_sig y)).
move=> H7.
elim (excluded_middle_informative ((exist (fun (n : nat) => (n < M)) (proj1_sig x) H6, proj1_sig (H37 M N y H7)) = d)).
move=> H8.
apply False_ind.
apply H5.
apply conj.
reflexivity.
rewrite - H8.
simpl.
rewrite (proj2_sig (H37 M N y H7)).
reflexivity.
move=> H8.
reflexivity.
move=> H7.
reflexivity.
move=> u.
elim.
move=> u0 H5 H6.
elim (excluded_middle_informative (proj1_sig u0 = proj1_sig (fst d) /\ proj1_sig y = (M + proj1_sig (snd d)))).
move=> H7.
apply False_ind.
apply H5.
suff: ((exist (fun n0 : nat => (n0 < M + N)) (proj1_sig (fst d)) H4) = u0).
move=> H8.
rewrite H8.
apply In_singleton.
apply sig_map.
rewrite (proj1 H7).
reflexivity.
move=> H7.
apply (Fmul_O_r f).
move=> k H5.
apply (Full_intro {n : nat | (n < M + N)} k).
apply (le_trans (S (proj1_sig (fst d))) M (M + N) (proj2_sig (fst d)) (le_plus_l M N)).
apply functional_extensionality_dep.
move=> f0.
apply functional_extensionality_dep.
move=> K.
apply functional_extensionality_dep.
move=> N1.
apply functional_extensionality_dep.
move=> N2.
apply functional_extensionality.
move=> A1.
apply functional_extensionality.
move=> A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockW.
elim (le_lt_dec N1 (proj1_sig y)).
move=> H1.
suff: (match AddConnectInv N1 N2 y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = N1 + proj1_sig k
end).
elim (AddConnectInv N1 N2 y).
move=> m.
elim.
move=> m H2.
suff: (m = (proj1_sig (H37 N1 N2 y H1))).
move=> H3.
rewrite H3.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig m) (proj1_sig (proj1_sig (H37 N1 N2 y H1))) N1).
rewrite (proj2_sig (H37 N1 N2 y H1)).
rewrite H2.
reflexivity.
apply (proj2 (AddConnectInvNature N1 N2) y H1).
move=> H1.
suff: (match AddConnectInv N1 N2 y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv N1 N2 y).
move=> m H2.
suff: (m = (exist (fun n : nat => n < N1) (proj1_sig y) H1)).
move=> H3.
rewrite H3.
reflexivity.
apply sig_map.
rewrite - H2.
reflexivity.
move=> m.
elim.
apply (proj1 (AddConnectInvNature N1 N2) y H1).
apply functional_extensionality_dep.
move=> f0.
apply functional_extensionality_dep.
move=> M1.
apply functional_extensionality_dep.
move=> M2.
apply functional_extensionality_dep.
move=> K.
apply functional_extensionality.
move=> A1.
apply functional_extensionality.
move=> A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
elim (le_lt_dec M1 (proj1_sig x)).
move=> H1.
suff: (match AddConnectInv M1 M2 x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = M1 + proj1_sig k
end).
elim (AddConnectInv M1 M2 x).
move=> m.
elim.
move=> m H2.
suff: (m = (proj1_sig (H37 M1 M2 x H1))).
move=> H3.
rewrite H3.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig m) (proj1_sig (proj1_sig (H37 M1 M2 x H1))) M1).
rewrite (proj2_sig (H37 M1 M2 x H1)).
rewrite H2.
reflexivity.
apply (proj2 (AddConnectInvNature M1 M2) x H1).
move=> H1.
suff: (match AddConnectInv M1 M2 x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv M1 M2 x).
move=> m H2.
suff: (m = (exist (fun n : nat => n < M1) (proj1_sig x) H1)).
move=> H3.
rewrite H3.
reflexivity.
apply sig_map.
rewrite - H2.
reflexivity.
move=> m.
elim.
apply (proj1 (AddConnectInvNature M1 M2) x H1).
move=> m1 m2 x H1.
suff: ((proj1_sig x - m1) < m2).
move=> H2.
exists (exist (fun n : nat => (n < m2)) (proj1_sig x - m1) H2).
unfold proj1_sig at 1.
apply (le_plus_minus_r m1 (proj1_sig x) H1).
apply (plus_lt_reg_l (proj1_sig x - m1) m2 m1).
rewrite (le_plus_minus_r m1 (proj1_sig x) H1).
apply (proj2_sig x).
Qed.

Lemma DeterminantMult : forall (f : Field) (N : nat) (A B : Matrix f N N), Determinant f N (Mmult f N N N A B) = Fmul f (Determinant f N A) (Determinant f N B).
Proof.
move=> f N A B.
rewrite (CauchyBinet f N N A B).
suff: ((FiniteIntersection ({n : nat | (n < N)} -> {n : nat | (n < N)}) (exist (Finite ({n : nat | (n < N)} -> {n : nat | (n < N)})) (Full_set ({n : nat | (n < N)} -> {n : nat | (n < N)})) (CountPowFinite N N)) (fun r : {n : nat | (n < N)} -> {n : nat | (n < N)} => forall p q : {n : nat | (n < N)}, (proj1_sig p < proj1_sig q) -> (proj1_sig (r p) < proj1_sig (r q)))) = FiniteSingleton ({n : nat | (n < N)} -> {n : nat | (n < N)}) (fun (m : {n : nat | (n < N)}) => m)).
move=> H1.
rewrite H1.
rewrite MySumF2Singleton.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> g.
elim.
move=> G H1 H2.
suff: (G = (fun (m : {n : nat | (n < N)}) => m)).
move=> H3.
rewrite H3.
apply In_singleton.
apply functional_extensionality.
suff: (forall (k : nat), k <= N -> forall (m : {n : nat | (n < N)}), proj1_sig m < k -> proj1_sig m <= proj1_sig (G m)).
move=> H3.
suff: (forall (k : nat), k <= N -> forall (m : {n : nat | (n < N)}), proj1_sig m + k >= N -> proj1_sig m >= proj1_sig (G m)).
move=> H4 m.
apply sig_map.
apply (le_antisym (proj1_sig (G m)) (proj1_sig m)).
apply (H4 N (le_n N) m).
apply (le_plus_r (proj1_sig m) N).
apply (H3 N (le_n N) m).
apply (proj2_sig m).
elim.
move=> H4 m.
rewrite (plus_0_r (proj1_sig m)).
move=> H5.
apply False_ind.
apply (le_not_lt N (proj1_sig m) H5 (proj2_sig m)).
move=> k H4 H5 m H6.
elim (le_lt_or_eq (S (proj1_sig m)) N).
move=> H7.
apply (le_S_n (proj1_sig (G m)) (proj1_sig m)).
apply (le_trans (S (proj1_sig (G m))) (proj1_sig (G (exist (fun (n : nat) => n < N) (S (proj1_sig m)) H7))) (S (proj1_sig m))).
apply (H1 m (exist (fun (n : nat) => n < N) (S (proj1_sig m)) H7)).
apply (le_n (S (proj1_sig m))).
apply (H4 (le_trans k (S k) N (le_S k k (le_n k)) H5) (exist (fun (n : nat) => n < N) (S (proj1_sig m)) H7)).
simpl.
suff: (S (proj1_sig m + k) = proj1_sig m + S k).
move=> H8.
rewrite H8.
apply H6.
apply (plus_Snm_nSm (proj1_sig m) k).
move=> H7.
apply (le_S_n (proj1_sig (G m)) (proj1_sig m)).
rewrite H7.
apply (proj2_sig (G m)).
apply (proj2_sig m).
elim.
move=> H3 m H4.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H4).
move=> n H3 H4 m H5.
elim (le_lt_or_eq O (proj1_sig m)).
move=> H6.
suff: (exists (k : nat), S k = proj1_sig m).
elim.
move=> k H7.
suff: (k < N).
move=> H8.
apply (le_trans (proj1_sig m) (S (proj1_sig (G (exist (fun (l : nat) => l < N) k H8)))) (proj1_sig (G m))).
rewrite - H7.
apply le_n_S.
apply (H3 (le_trans n (S n) N (le_S n n (le_n n)) H4) (exist (fun (l : nat) => l < N) k H8)).
apply (lt_S_n k n).
rewrite H7.
apply H5.
apply (H1 (exist (fun (l : nat) => l < N) k H8) m).
rewrite - H7.
apply (le_n (S k)).
unfold lt.
rewrite H7.
apply (le_trans (proj1_sig m) (S n) N).
apply (lt_le_weak (proj1_sig m) (S n) H5).
apply H4.
suff: (0 < proj1_sig m).
elim (proj1_sig m).
move=> H7.
apply False_ind.
apply (lt_irrefl O H7).
move=> l H7 H8.
exists l.
reflexivity.
apply H6.
move=> H6.
rewrite - H6.
apply (le_0_n (proj1_sig (G m))).
apply (le_0_n (proj1_sig m)).
move=> g H1.
apply Intersection_intro.
elim H1.
move=> p q.
apply.
apply (Full_intro ({n : nat | (n < N)} -> {n : nat | (n < N)}) g).
Qed.

Definition Cofactor (f : Field) (N : nat) (A : Matrix f N N) (p q : {n : nat | (n < N)}) := Fmul f (PowF f (Fopp f (FI f)) (proj1_sig p + proj1_sig q)) (Determinant f (pred N) (fun (x y : {n : nat | (n < pred N)}) => A (SkipOne N p x) (SkipOne N q y))).

Lemma DeterminantDivideW : forall (f : Field) (N : nat) (A : Matrix f N N) (p : {n : nat | (n < N)}), Determinant f N A = MySumF2 {n : nat | n < N} (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N)) (FPCM f) (fun (n : Count N) => Fmul f (A p n) (Cofactor f N A p n)).
Proof.
move=> f.
elim.
move=> A p.
apply False_ind.
apply (le_not_lt O (proj1_sig p) (le_0_n (proj1_sig p)) (proj2_sig p)).
move=> N H1 A p.
unfold Determinant.
rewrite (MySumF2ImageSum (Permutation (S N)) {n : nat | n < S N} (exist (Finite (Permutation (S N))) (Full_set (Permutation (S N))) (PermutationFinite (S N))) (FPCM f) (fun (P : Permutation (S N)) => Fmul f match PermutationParity (S N) P with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | n < S N} (exist (Finite (Count (S N))) (Full_set {n : nat | n < S N}) (CountFinite (S N))) (FMCM f) (fun k : {n : nat | n < S N} => A k (proj1_sig P k)))) (fun (P : Permutation (S N)) => proj1_sig P p)).
suff: ((FiniteIm (Permutation (S N)) {n : nat | n < S N} (fun P : (Permutation (S N)) => proj1_sig P p) (exist (Finite (Permutation (S N))) (Full_set (Permutation (S N))) (PermutationFinite (S N)))) = (exist (Finite (Count (S N))) (Full_set {n : nat | n < S N}) (CountFinite (S N)))).
move=> H2.
rewrite H2.
apply MySumF2Same.
move=> m H3.
suff: (forall (k : {n : nat | n < S N}), proj1_sig k < proj1_sig p -> proj1_sig k < N).
move=> H4.
suff: (forall (k : {n : nat | n < S N}), proj1_sig k > proj1_sig p -> pred (proj1_sig k) < N).
move=> H5.
suff: (forall (P : Permutation N), {Q : Permutation (S N) | (forall (k : {n : nat | n < S N}) (H : proj1_sig k < proj1_sig p), proj1_sig Q k = SkipOne (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H)))) /\ proj1_sig Q p = m /\ (forall (k : {n : nat | n < S N}) (H : proj1_sig k > proj1_sig p), proj1_sig Q k = SkipOne (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H))))}).
move=> H6.
unfold Cofactor.
unfold Determinant.
simpl.
suff: ((FiniteIntersection (Permutation (S N)) (exist (Finite (Permutation (S N))) (Full_set (Permutation (S N))) (PermutationFinite (S N))) (fun u1 : Permutation (S N) => proj1_sig u1 p = m)) = (FiniteIm (Permutation N) (Permutation (S N)) (fun P : Permutation N => proj1_sig (H6 P)) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)))).
move=> H7.
rewrite H7.
rewrite - (MySumF2BijectiveSame2 (Permutation N) (Permutation (S N)) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (fun (P : Permutation N) => proj1_sig (H6 P))).
apply (FiniteSetInduction (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (Fmul_O_r f).
rewrite (Fmul_O_r f).
reflexivity.
move=> B b H8 H9 H10 H11.
rewrite MySumF2Add.
rewrite MySumF2Add.
suff: ((Basics.compose (fun P : Permutation (S N) => Fmul f match PermutationParity (S N) P with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | n < S N} (exist (Finite (Count (S N))) (Full_set {n : nat | n < S N}) (CountFinite (S N))) (FMCM f) (fun k : {n : nat | n < S N} => A k (proj1_sig P k)))) (fun P : Permutation N => proj1_sig (H6 P)) b) = Fmul f (A p m) (Fmul f (PowF f (Fopp f (FI f)) (proj1_sig p + proj1_sig m)) (Fmul f match PermutationParity N b with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | n < N} (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N)) (FMCM f) (fun k : {n : nat | n < N} => A (SkipOne (S N) p k) (SkipOne (S N) m (proj1_sig b k))))))).
move=> H12.
rewrite H12.
rewrite H11.
simpl.
rewrite (Fmul_add_distr_l f (PowF f (Fopp f (FI f)) (proj1_sig p + proj1_sig m))).
rewrite (Fmul_add_distr_l f (A p m)).
reflexivity.
unfold Basics.compose.
suff: (match PermutationParity (S N) (proj1_sig (H6 b)) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end = Fmul f (PowF f (Fopp f (FI f)) (proj1_sig p + proj1_sig m)) (match PermutationParity N b with
  | ON => Fopp f (FI f)
  | OFF => FI f
end)).
move=> H12.
suff: (MySumF2 {n : nat | n < S N} (exist (Finite (Count (S N))) (Full_set {n : nat | n < S N}) (CountFinite (S N))) (FMCM f) (fun k : {n : nat | n < S N} => A k (proj1_sig (proj1_sig (H6 b)) k)) = Fmul f (A p m) (MySumF2 {n : nat | n < N} (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N)) (FMCM f) (fun k : {n : nat | n < N} => A (SkipOne (S N) p k) (SkipOne (S N) m (proj1_sig b k))))).
move=> H13.
rewrite H12.
rewrite H13.
rewrite (Fmul_comm f (Fmul f (PowF f (Fopp f (FI f)) (proj1_sig p + proj1_sig m)) match PermutationParity N b with
  | ON => Fopp f (FI f)
  | OFF => FI f
end)).
rewrite (Fmul_assoc f (A p m)).
rewrite (Fmul_comm f (MySumF2 {n : nat | n < N} (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N)) (FMCM f) (fun k : {n : nat | n < N} => A (SkipOne (S N) p k) (SkipOne (S N) m (proj1_sig b k))))).
rewrite (Fmul_assoc f (PowF f (Fopp f (FI f)) (proj1_sig p + proj1_sig m)) (match PermutationParity N b with
  | ON => Fopp f (FI f)
  | OFF => FI f
end)).
reflexivity.
rewrite (MySumF2Included {n : nat | n < S N} (FiniteSingleton {n : nat | n < S N} p) (exist (Finite (Count (S N))) (Full_set {n : nat | n < S N}) (CountFinite (S N))) (FMCM f)).
rewrite MySumF2Singleton.
simpl.
rewrite (proj1 (proj2 (proj2_sig (H6 b)))).
suff: (FiniteIntersection {n : nat | n < S N} (exist (Finite (Count (S N))) (Full_set {n : nat | n < S N}) (CountFinite (S N))) (Complement {n : nat | n < S N} (Singleton {n : nat | n < S N} p)) = (FiniteIm {n : nat | n < N} {n : nat | n < S N} (SkipOne (S N) p) (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N)))).
move=> H13.
rewrite H13.
rewrite - (MySumF2BijectiveSame2 {n : nat | n < N} {n : nat | n < S N} (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N)) (SkipOne (S N) p)).
unfold Basics.compose.
suff: ((fun (x : {n : nat | n < N}) => A (SkipOne (S N) p x) (proj1_sig (proj1_sig (H6 b)) (SkipOne (S N) p x))) = (fun (k : {n : nat | n < N}) => A (SkipOne (S N) p k) (SkipOne (S N) m (proj1_sig b k)))).
move=> H14.
rewrite H14.
reflexivity.
apply functional_extensionality.
move=> k.
elim (le_or_lt (proj1_sig p) (proj1_sig k)).
move=> H14.
suff: ((proj1_sig (proj1_sig (H6 b)) (SkipOne (S N) p k)) = (SkipOne (S N) m (proj1_sig b k))).
move=> H15.
rewrite H15.
reflexivity.
suff: (proj1_sig (SkipOne (S N) p k) > proj1_sig p).
move=> H15.
rewrite (proj2 (proj2 (proj2_sig (H6 b))) (SkipOne (S N) p k)).
suff: ((exist (fun n : nat => n < N) (pred (proj1_sig (SkipOne (S N) p k))) (H5 (SkipOne (S N) p k) H15)) = k).
move=> H16.
rewrite H16.
reflexivity.
apply sig_map.
simpl.
rewrite (proj2 (SkipOneNature (S N) p k)).
reflexivity.
apply H14.
rewrite (proj2 (SkipOneNature (S N) p k)).
apply (le_n_S (proj1_sig p) (proj1_sig k) H14).
apply H14.
move=> H14.
suff: (proj1_sig (proj1_sig (H6 b)) (SkipOne (S N) p k) = SkipOne (S N) m (proj1_sig b k)).
move=> H15.
rewrite H15.
reflexivity.
suff: (proj1_sig (SkipOne (S N) p k) < proj1_sig p).
move=> H15.
rewrite (proj1 (proj2_sig (H6 b)) (SkipOne (S N) p k) H15).
suff: (exist (fun n : nat => n < N) (proj1_sig (SkipOne (S N) p k)) (H4 (SkipOne (S N) p k) H15) = k).
move=> H16.
rewrite H16.
reflexivity.
apply sig_map.
apply (proj1 (SkipOneNature (S N) p k) H14).
rewrite (proj1 (SkipOneNature (S N) p k) H14).
apply H14.
move=> u1 u2 H14 H15 H16.
elim (le_or_lt (proj1_sig p) (proj1_sig u1)).
move=> H17.
elim (le_or_lt (proj1_sig p) (proj1_sig u2)).
move=> H18.
apply sig_map.
apply (Nat.succ_inj (proj1_sig u1) (proj1_sig u2)).
rewrite - (proj2 (SkipOneNature (S N) p u1) H17).
rewrite H16.
apply (proj2 (SkipOneNature (S N) p u2) H18).
move=> H18.
apply False_ind.
apply (lt_irrefl (proj1_sig (SkipOne (S N) p u1))).
apply (lt_trans (proj1_sig (SkipOne (S N) p u1)) (proj1_sig p) (proj1_sig (SkipOne (S N) p u1))).
rewrite H16.
rewrite (proj1 (SkipOneNature (S N) p u2) H18).
apply H18.
rewrite (proj2 (SkipOneNature (S N) p u1) H17).
apply (le_n_S (proj1_sig p) (proj1_sig u1) H17).
move=> H17.
elim (le_or_lt (proj1_sig p) (proj1_sig u2)).
move=> H18.
apply False_ind.
apply (lt_irrefl (proj1_sig (SkipOne (S N) p u1))).
apply (lt_trans (proj1_sig (SkipOne (S N) p u1)) (proj1_sig p) (proj1_sig (SkipOne (S N) p u1))).
rewrite (proj1 (SkipOneNature (S N) p u1) H17).
apply H17.
rewrite H16.
rewrite (proj2 (SkipOneNature (S N) p u2) H18).
apply (le_n_S (proj1_sig p) (proj1_sig u2) H18).
move=> H18.
apply sig_map.
rewrite - (proj1 (SkipOneNature (S N) p u1) H17).
rewrite H16.
apply (proj1 (SkipOneNature (S N) p u2) H18).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> k.
elim.
move=> l H13 H14.
elim (le_or_lt (proj1_sig l) (proj1_sig p)).
move=> H15.
elim (le_lt_or_eq (proj1_sig l) (proj1_sig p) H15).
move=> H16.
apply (Im_intro {n : nat | n < N} {n : nat | n < S N} (Full_set {n : nat | n < N}) (SkipOne (S N) p) (exist (fun (n : nat) => n < N) (proj1_sig l) (H4 l H16))).
apply (Full_intro {n : nat | n < N} (exist (fun n : nat => n < N) (proj1_sig l) (H4 l H16))).
apply sig_map.
rewrite (proj1 (SkipOneNature (S N) p (exist (fun (n : nat) => n < N) (proj1_sig l) (H4 l H16)))).
reflexivity.
apply H16.
move=> H16.
apply False_ind.
apply H13.
suff: (l = p).
move=> H17.
rewrite H17.
apply (In_singleton {n : nat | n < S N} p).
apply sig_map.
apply H16.
move=> H15.
apply (Im_intro {n : nat | n < N} {n : nat | n < S N} (Full_set {n : nat | n < N}) (SkipOne (S N) p) (exist (fun (n : nat) => n < N) (pred (proj1_sig l)) (H5 l H15))).
apply (Full_intro {n : nat | n < N} (exist (fun n : nat => n < N) (pred (proj1_sig l)) (H5 l H15))).
apply sig_map.
rewrite (proj2 (SkipOneNature (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig l)) (H5 l H15)))).
simpl.
suff: (proj1_sig l <> 0).
elim (proj1_sig l).
move=> H16.
apply False_ind.
apply H16.
reflexivity.
move=> n H16 H17.
reflexivity.
move=> H16.
apply (le_not_lt (proj1_sig l) (proj1_sig p)).
rewrite H16.
apply (le_0_n (proj1_sig p)).
apply H15.
simpl.
apply (le_S_n (proj1_sig p) (pred (proj1_sig l))).
apply (le_trans (S (proj1_sig p)) (proj1_sig l) (S (pred (proj1_sig l))) H15).
elim (proj1_sig l).
apply (le_S 0 0 (le_n 0)).
move=> n H16.
apply (le_n (S n)).
move=> k.
elim.
move=> l H13 y H14.
rewrite H14.
apply (Intersection_intro {n : nat | n < S N}).
elim (le_or_lt (proj1_sig p) (proj1_sig l)).
move=> H15 H16.
apply (lt_irrefl (proj1_sig p)).
apply (le_trans (S (proj1_sig p)) (S (proj1_sig l)) (proj1_sig p)).
apply (le_n_S (proj1_sig p) (proj1_sig l) H15).
suff: (p = SkipOne (S N) p l).
move=> H17.
rewrite H17.
rewrite (proj2 (SkipOneNature (S N) p l) H15).
apply (le_n (S (proj1_sig l))).
elim H16.
reflexivity.
move=> H15 H16.
apply (lt_irrefl (proj1_sig (SkipOne (S N) p l))).
apply (le_trans (S (proj1_sig (SkipOne (S N) p l))) (proj1_sig p) (proj1_sig (SkipOne (S N) p l))).
rewrite (proj1 (SkipOneNature (S N) p l) H15).
apply H15.
elim H16.
apply (le_n (proj1_sig p)).
apply (Full_intro {n : nat | n < S N} (SkipOne (S N) p l)).
move=> k H13.
apply (Full_intro {n : nat | n < S N} k).
suff: (forall (q k : {n : nat | n < S N}), proj1_sig k < proj1_sig q -> proj1_sig k < N).
move=> H12.
suff: (forall (q k : {n : nat | n < S N}), proj1_sig k > proj1_sig q -> pred (proj1_sig k) < N).
move=> H13.
suff: (forall (r : nat), r < S N -> forall (s : nat), s < S N -> forall (x y : {n : nat | n < S N}), proj1_sig x = r -> proj1_sig y = s -> forall (Q : Permutation (S N)), ((forall (k : {n : nat | n < S N}) (H : proj1_sig k < proj1_sig x), proj1_sig Q k = SkipOne (S N) y (proj1_sig b (exist (fun n : nat => n < N) (proj1_sig k) (H12 x k H)))) /\ proj1_sig Q x = y /\ (forall (k : {n : nat | n < S N}) (H : proj1_sig k > proj1_sig x), proj1_sig Q k = SkipOne (S N) y (proj1_sig b (exist (fun n : nat => n < N) (pred (proj1_sig k)) (H13 x k H))))) -> match PermutationParity (S N) Q with
  | ON => Fopp f (FI f)
  | OFF => FI f
end = Fmul f (PowF f (Fopp f (FI f)) (proj1_sig x + proj1_sig y)) match PermutationParity N b with
  | ON => Fopp f (FI f)
  | OFF => FI f
end).
move=> H14.
apply (H14 (proj1_sig p) (proj2_sig p) (proj1_sig m) (proj2_sig m) p m).
reflexivity.
reflexivity.
apply conj.
move=> k H15.
rewrite (proj1 (proj2_sig (H6 b)) k H15).
suff: (H4 k H15 = H12 p k H15).
move=> H16.
rewrite H16.
reflexivity.
apply proof_irrelevance.
apply conj.
apply (proj1 (proj2 (proj2_sig (H6 b)))).
move=> k H15.
rewrite (proj2 (proj2 (proj2_sig (H6 b))) k H15).
suff: (H5 k H15 = H13 p k H15).
move=> H16.
rewrite H16.
reflexivity.
apply proof_irrelevance.
elim.
move=> H14.
elim.
move=> H15 x y H16 H17 Q H18.
rewrite H16.
rewrite H17.
rewrite (Fmul_I_l f).
unfold PermutationParity.
suff: (forall (k : {n : nat | n < N}), S (proj1_sig k) < S N).
move=> H19.
rewrite (MySumF2Included ({n : nat | n < S N} * {n : nat | n < S N}) (FiniteIm ({n : nat | n < N} * {n : nat | n < N}) ({n : nat | n < S N} * {n : nat | n < S N}) (fun xy : {n : nat | n < N} * {n : nat | n < N} => (exist (fun n : nat => n < S N) (S (proj1_sig (fst xy))) (H19 (fst xy)), exist (fun n : nat => n < S N) (S (proj1_sig (snd xy))) (H19 (snd xy)))) (exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N)))).
rewrite - (MySumF2BijectiveSame2 ({n : nat | n < N} * {n : nat | n < N}) ({n : nat | n < S N} * {n : nat | n < S N}) (exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N)) (fun (xy : {n : nat | n < N} * {n : nat | n < N}) => (exist (fun (n : nat) => n < S N) (S (proj1_sig (fst xy))) (H19 (fst xy)), exist (fun (n : nat) => n < S N) (S (proj1_sig (snd xy))) (H19 (snd xy)))) ParityXORCM).
suff: (MySumF2 ({n : nat | n < S N} * {n : nat | n < S N}) (FiniteIntersection ({n : nat | n < S N} * {n : nat | n < S N}) (exist (Finite ({n : nat | n < S N} * {n : nat | n < S N})) (fun xy : {n : nat | n < S N} * {n : nat | n < S N} => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub (S N))) (Complement ({n : nat | n < S N} * {n : nat | n < S N}) (proj1_sig (FiniteIm ({n : nat | n < N} * {n : nat | n < N}) ({n : nat | n < S N} * {n : nat | n < S N}) (fun xy : {n : nat | n < N} * {n : nat | n < N} => (exist (fun n : nat => n < S N) (S (proj1_sig (fst xy))) (H19 (fst xy)), exist (fun n : nat => n < S N) (S (proj1_sig (snd xy))) (H19 (snd xy)))) (exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N)))))) ParityXORCM (fun xy : {n : nat | n < S N} * {n : nat | n < S N} => match excluded_middle_informative (proj1_sig (proj1_sig Q (fst xy)) < proj1_sig (proj1_sig Q (snd xy))) with
  | left _ => OFF
  | right _ => ON
end) = OFF).
move=> H20.
rewrite H20.
suff: (MySumF2 ({n : nat | n < N} * {n : nat | n < N}) (exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N)) ParityXORCM (Basics.compose (fun xy : {n : nat | n < S N} * {n : nat | n < S N} => match excluded_middle_informative (proj1_sig (proj1_sig Q (fst xy)) < proj1_sig (proj1_sig Q (snd xy))) with
  | left _ => OFF
  | right _ => ON
end) (fun xy : {n : nat | n < N} * {n : nat | n < N} => (exist (fun n : nat => n < S N) (S (proj1_sig (fst xy))) (H19 (fst xy)), exist (fun n : nat => n < S N) (S (proj1_sig (snd xy))) (H19 (snd xy))))) = MySumF2 ({n : nat | n < N} * {n : nat | n < N}) (exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N)) ParityXORCM (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig b (fst xy)) < proj1_sig (proj1_sig b (snd xy))) with
  | left _ => OFF
  | right _ => ON
end)).
move=> H21.
rewrite H21.
elim (MySumF2 ({n : nat | n < N} * {n : nat | n < N}) (exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N)) ParityXORCM (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig b (fst xy)) < proj1_sig (proj1_sig b (snd xy))) with
  | left _ => OFF
  | right _ => ON
end)).
reflexivity.
reflexivity.
unfold Basics.compose.
apply MySumF2Same.
move=> u H21.
suff: (proj1_sig (proj1_sig Q (fst (exist (fun n : nat => n < S N) (S (proj1_sig (fst u))) (H19 (fst u)), exist (fun n : nat => n < S N) (S (proj1_sig (snd u))) (H19 (snd u))))) = S (proj1_sig (proj1_sig b (fst u)))).
move=> H22.
suff: (proj1_sig (proj1_sig Q (snd (exist (fun n : nat => n < S N) (S (proj1_sig (fst u))) (H19 (fst u)), exist (fun n : nat => n < S N) (S (proj1_sig (snd u))) (H19 (snd u))))) = S (proj1_sig (proj1_sig b (snd u)))).
move=> H23.
rewrite H22.
rewrite H23.
elim (excluded_middle_informative (proj1_sig (proj1_sig b (fst u)) < proj1_sig (proj1_sig b (snd u)))).
move=> H24.
elim (excluded_middle_informative (S (proj1_sig (proj1_sig b (fst u))) < S (proj1_sig (proj1_sig b (snd u))))).
move=> H25.
reflexivity.
move=> H25.
apply False_ind.
apply (H25 (lt_n_S (proj1_sig (proj1_sig b (fst u))) (proj1_sig (proj1_sig b (snd u))) H24)).
move=> H24.
elim (excluded_middle_informative (S (proj1_sig (proj1_sig b (fst u))) < S (proj1_sig (proj1_sig b (snd u))))).
move=> H25.
apply False_ind.
apply (H24 (lt_S_n (proj1_sig (proj1_sig b (fst u))) (proj1_sig (proj1_sig b (snd u))) H25)).
move=> H25.
reflexivity.
suff: (proj1_sig x < S (proj1_sig (snd u))).
move=> H23.
rewrite (proj2 (proj2 H18) (exist (fun n : nat => n < S N) (S (proj1_sig (snd u))) (H19 (snd u))) H23).
simpl.
rewrite (proj2 (SkipOneNature (S N) y (proj1_sig b (exist (fun n : nat => n < N) (proj1_sig (snd u)) (H13 x (exist (fun n : nat => n < S N) (S (proj1_sig (snd u))) (H19 (snd u))) H23))))).
suff: (exist (fun n : nat => n < N) (proj1_sig (snd u)) (H13 x (exist (fun n : nat => n < S N) (S (proj1_sig (snd u))) (H19 (snd u))) H23) = (snd u)).
move=> H24.
rewrite H24.
reflexivity.
apply sig_map.
reflexivity.
rewrite H17.
apply le_0_n.
rewrite H16.
apply (le_n_S O (proj1_sig (snd u)) (le_0_n (proj1_sig (snd u)))).
suff: (proj1_sig x < S (proj1_sig (fst u))).
move=> H22.
rewrite (proj2 (proj2 H18) (exist (fun (n : nat) => n < S N) (S (proj1_sig (fst u))) (H19 (fst u))) H22).
simpl.
rewrite (proj2 (SkipOneNature (S N) y (proj1_sig b (exist (fun (n : nat) => n < N) (proj1_sig (fst u)) (H13 x (exist (fun (n : nat) => n < S N) (S (proj1_sig (fst u))) (H19 (fst u))) H22))))).
suff: (exist (fun n : nat => n < N) (proj1_sig (fst u)) (H13 x (exist (fun n : nat => n < S N) (S (proj1_sig (fst u))) (H19 (fst u))) H22) = (fst u)).
move=> H23.
rewrite H23.
reflexivity.
apply sig_map.
reflexivity.
rewrite H17.
apply le_0_n.
rewrite H16.
apply (le_n_S O (proj1_sig (fst u)) (le_0_n (proj1_sig (fst u)))).
apply MySumF2O.
move=> u.
elim.
move=> u0 H20 H21.
elim (excluded_middle_informative (proj1_sig (proj1_sig Q (fst u0)) < proj1_sig (proj1_sig Q (snd u0)))).
move=> H22.
reflexivity.
move=> H22.
apply False_ind.
suff: (proj1_sig (fst u0) <> O).
move=> H23.
suff: (proj1_sig (snd u0) <> O).
move=> H24.
apply H20.
suff: (pred (proj1_sig (fst u0)) < N).
move=> H25.
suff: (pred (proj1_sig (snd u0)) < N).
move=> H26.
apply (Im_intro ({n : nat | n < N} * {n : nat | n < N}) ({n : nat | n < S N} * {n : nat | n < S N}) (fun (xy : {n : nat | n < N} * {n : nat | n < N}) => proj1_sig (fst xy) < proj1_sig (snd xy)) (fun (xy : {n : nat | n < N} * {n : nat | n < N}) => (exist (fun n : nat => n < S N) (S (proj1_sig (fst xy))) (H19 (fst xy)), exist (fun n : nat => n < S N) (S (proj1_sig (snd xy))) (H19 (snd xy)))) (exist (fun (n : nat) => n < N) (pred (proj1_sig (fst u0))) H25, exist (fun (n : nat) => n < N) (pred (proj1_sig (snd u0))) H26)).
suff: (proj1_sig (fst u0) <> O).
suff: (proj1_sig (snd u0) <> O).
suff: (proj1_sig (fst u0) < proj1_sig (snd u0)).
unfold In.
simpl.
elim (proj1_sig (fst u0)).
move=> H27 H28 H29.
apply False_ind.
apply H29.
reflexivity.
move=> a H27.
elim (proj1_sig (snd u0)).
move=> H28 H29.
apply False_ind.
apply H29.
reflexivity.
move=> z H28 H29 H30 H31.
apply (lt_S_n a z H29).
apply H21.
apply H24.
apply H23.
apply injective_projections.
apply sig_map.
simpl.
suff: (proj1_sig (fst u0) <> 0).
elim (proj1_sig (fst u0)).
move=> H27.
apply False_ind.
apply H27.
reflexivity.
move=> n H27 H28.
reflexivity.
apply H23.
apply sig_map.
simpl.
suff: (proj1_sig (snd u0) <> 0).
elim (proj1_sig (snd u0)).
move=> H27.
apply False_ind.
apply H27.
reflexivity.
move=> n H27 H28.
reflexivity.
apply H24.
apply (lt_S_n (pred (proj1_sig (snd u0))) N).
suff: (proj1_sig (snd u0) <> 0).
suff: (proj1_sig (snd u0) < S N).
elim (proj1_sig (snd u0)).
move=> H26 H27.
apply False_ind.
apply H27.
reflexivity.
move=> n H26 H27 H28.
apply H27.
apply (proj2_sig (snd u0)).
apply H24.
apply (lt_S_n (pred (proj1_sig (fst u0))) N).
suff: (proj1_sig (fst u0) <> 0).
suff: (proj1_sig (fst u0) < S N).
elim (proj1_sig (fst u0)).
move=> H25 H26.
apply False_ind.
apply H26.
reflexivity.
move=> n H25 H26 H27.
apply H26.
apply (proj2_sig (fst u0)).
apply H23.
move=> H24.
apply (lt_irrefl (proj1_sig (snd u0))).
apply (le_trans (S (proj1_sig (snd u0))) (S (proj1_sig (fst u0))) (proj1_sig (snd u0))).
rewrite H24.
apply (le_n_S O (proj1_sig (fst u0)) (le_0_n (proj1_sig (fst u0)))).
apply H21.
move=> H23.
apply H22.
suff: (fst u0 = x).
move=> H24.
rewrite H24.
rewrite (proj1 (proj2 H18)).
rewrite H17.
suff: (proj1_sig (snd u0) > proj1_sig x).
move=> H25.
rewrite (proj2 (proj2 H18) (snd u0) H25).
rewrite (proj2 (SkipOneNature (S N) y (proj1_sig b (exist (fun n : nat => n < N) (pred (proj1_sig (snd u0))) (H13 x (snd u0) H25))))).
apply (le_n_S O (proj1_sig (proj1_sig b (exist (fun n : nat => n < N) (pred (proj1_sig (snd u0))) (H13 x (snd u0) H25))))).
apply le_0_n.
rewrite H17.
apply le_0_n.
rewrite H16.
apply (le_trans (S O) (S (proj1_sig (fst u0))) (proj1_sig (snd u0))).
apply (le_n_S O (proj1_sig (fst u0)) (le_0_n (proj1_sig (fst u0)))).
apply H21.
apply sig_map.
rewrite H16.
apply H23.
move=> u1 u2 H20 H21 H22.
apply injective_projections.
apply sig_map.
apply (Nat.succ_inj (proj1_sig (fst u1)) (proj1_sig (fst u2))).
suff: (S (proj1_sig (fst u1)) = proj1_sig (fst (exist (fun n : nat => n < S N) (S (proj1_sig (fst u1))) (H19 (fst u1)), exist (fun n : nat => n < S N) (S (proj1_sig (snd u1))) (H19 (snd u1))))).
move=> H23.
rewrite H23.
rewrite H22.
reflexivity.
reflexivity.
apply sig_map.
apply (Nat.succ_inj (proj1_sig (snd u1)) (proj1_sig (snd u2))).
suff: (S (proj1_sig (snd u1)) = proj1_sig (snd (exist (fun n : nat => n < S N) (S (proj1_sig (fst u1))) (H19 (fst u1)), exist (fun n : nat => n < S N) (S (proj1_sig (snd u1))) (H19 (snd u1))))).
move=> H23.
rewrite H23.
rewrite H22.
reflexivity.
reflexivity.
move=> xy.
elim.
move=> xy0 H20 y0 H21.
rewrite H21.
apply (lt_n_S (proj1_sig (fst xy0)) (proj1_sig (snd xy0)) H20).
move=> k.
apply (lt_n_S (proj1_sig k) N (proj2_sig k)).
move=> y0 H15 H16 x1 y1 H17 H18 Q H19.
rewrite H17.
rewrite (plus_0_l (proj1_sig y1)).
suff: (y0 < S N).
move=> H20.
suff: (Q = PermutationCompose (S N) (PermutationInv (S N) (PermutationSwap (S N) y1 (exist (fun (n : nat) => n < S N) y0 H20))) (PermutationCompose (S N) (PermutationSwap (S N) y1 (exist (fun (n : nat) => n < S N) y0 H20)) Q)).
move=> H21.
rewrite H21.
rewrite (PermutationComposeParity (S N)).
rewrite (PermutationInvParity (S N)).
rewrite (PermutationSwapParity (S N)).
suff: (match ParityXOR ON (PermutationParity (S N) (PermutationCompose (S N) (PermutationSwap (S N) y1 (exist (fun (n : nat) => n < S N) y0 H20)) Q)) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end = Fmul f (Fopp f (FI f)) match PermutationParity (S N) (PermutationCompose (S N) (PermutationSwap (S N) y1 (exist (fun (n : nat) => n < S N) y0 H20)) Q) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end).
move=> H22.
rewrite H22.
rewrite (H15 H20 x1 (exist (fun (n : nat) => n < S N) y0 H20) H17).
rewrite H18.
rewrite H17.
simpl.
rewrite - (Fmul_assoc f (Fopp f (FI f)) (PowF f (Fopp f (FI f)) y0)).
rewrite (Fmul_comm f (Fopp f (FI f)) (PowF f (Fopp f (FI f)) y0)).
reflexivity.
reflexivity.
apply conj.
move=> k H23.
apply False_ind.
apply (le_not_lt O (proj1_sig k) (le_0_n (proj1_sig k))).
rewrite - H17.
apply H23.
apply conj.
unfold PermutationSwap.
unfold PermutationCompose.
unfold Basics.compose.
apply sig_map.
simpl.
elim (excluded_middle_informative (proj1_sig Q x1 = y1)).
move=> H23.
reflexivity.
move=> H23.
apply False_ind.
apply H23.
apply (proj1 (proj2 H19)).
move=> k H23.
unfold PermutationSwap.
unfold PermutationCompose.
unfold Basics.compose.
simpl.
elim (excluded_middle_informative (proj1_sig Q k = y1)).
move=> H24.
apply False_ind.
suff: (x1 = k).
move=> H25.
apply (le_not_lt (proj1_sig k) (proj1_sig x1)).
rewrite H25.
apply (le_n (proj1_sig k)).
apply H23.
apply (BijInj {n : nat | n < S N} {n : nat | n < S N} (proj1_sig Q) (proj2_sig Q)).
rewrite H24.
apply (proj1 (proj2 H19)).
move=> H24.
elim (excluded_middle_informative (proj1_sig Q k = exist (fun n : nat => n < S N) y0 H20)).
move=> H25.
suff: (y0 < N).
move=> H26.
suff: (proj1_sig b (exist (fun n : nat => n < N) (Init.Nat.pred (proj1_sig k)) (H13 x1 k H23)) = exist (fun (n : nat) => n < N) y0 H26).
move=> H27.
rewrite H27.
apply sig_map.
rewrite (proj2 (SkipOneNature (S N) (exist (fun (n : nat) => n < S N) y0 H20) (exist (fun n : nat => n < N) y0 H26))).
apply H18.
apply (le_n y0).
suff: (proj1_sig (proj1_sig b (exist (fun n : nat => n < N) (pred (proj1_sig k)) (H13 x1 k H23))) = proj1_sig (proj1_sig Q k)).
move=> H27.
apply sig_map.
rewrite H27.
rewrite H25.
reflexivity.
rewrite (proj2 (proj2 H19) k H23).
rewrite (proj1 (SkipOneNature (S N) y1 (proj1_sig b (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H13 x1 k H23))))).
reflexivity.
apply (le_trans (S (proj1_sig (proj1_sig b (exist (fun n : nat => n < N) (Init.Nat.pred (proj1_sig k)) (H13 x1 k H23))))) (S (proj1_sig (proj1_sig Q k))) (proj1_sig y1)).
apply le_n_S.
rewrite (proj2 (proj2 H19) k H23).
elim (le_or_lt (proj1_sig y1) (proj1_sig (proj1_sig b (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H13 x1 k H23))))).
move=> H27.
rewrite (proj2 (SkipOneNature (S N) y1 (proj1_sig b (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H13 x1 k H23)))) H27).
apply le_S.
apply le_n.
move=> H27.
rewrite (proj1 (SkipOneNature (S N) y1 (proj1_sig b (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H13 x1 k H23)))) H27).
apply le_n.
rewrite H25.
rewrite H18.
apply (le_n (S y0)).
unfold lt.
rewrite - H18.
apply (le_S_n (proj1_sig y1) N (proj2_sig y1)).
move=> H25.
elim (le_or_lt y0 (proj1_sig (proj1_sig b (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H13 x1 k H23))))).
move=> H26.
apply sig_map.
rewrite (proj2 (SkipOneNature (S N) (exist (fun n : nat => n < S N) y0 H20) (proj1_sig b (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H13 x1 k H23)))) H26).
rewrite (proj2 (proj2 H19) k H23).
apply (proj2 (SkipOneNature (S N) y1 (proj1_sig b (exist (fun (n : nat) => n < N) (Init.Nat.pred (proj1_sig k)) (H13 x1 k H23))))).
elim (le_lt_or_eq y0 (proj1_sig (proj1_sig b (exist (fun (n : nat) => n < N) (Init.Nat.pred (proj1_sig k)) (H13 x1 k H23)))) H26).
rewrite H18.
apply.
move=> H27.
apply False_ind.
elim (le_or_lt (proj1_sig y1) (proj1_sig (proj1_sig b (exist (fun n : nat => n < N) (Init.Nat.pred (proj1_sig k)) (H13 x1 k H23))))).
move=> H28.
apply H24.
rewrite (proj2 (proj2 H19) k H23).
apply sig_map.
rewrite (proj2 (SkipOneNature (S N) y1 (proj1_sig b (exist (fun (n : nat) => n < N) (Init.Nat.pred (proj1_sig k)) (H13 x1 k H23))))).
rewrite - H27.
rewrite H18.
reflexivity.
apply H28.
move=> H28.
apply H25.
rewrite (proj2 (proj2 H19) k H23).
apply sig_map.
rewrite (proj1 (SkipOneNature (S N) y1 (proj1_sig b (exist (fun (n : nat) => n < N) (Init.Nat.pred (proj1_sig k)) (H13 x1 k H23))))).
simpl.
rewrite H27.
reflexivity.
apply H28.
move=> H26.
rewrite (proj2 (proj2 H19) k H23).
apply sig_map.
rewrite (proj1 (SkipOneNature (S N) (exist (fun n : nat => n < S N) y0 H20) (proj1_sig b (exist (fun (n : nat) => n < N) (Init.Nat.pred (proj1_sig k)) (H13 x1 k H23)))) H26).
apply (proj1 (SkipOneNature (S N) y1 (proj1_sig b (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H13 x1 k H23))))).
rewrite H18.
apply (lt_trans (proj1_sig (proj1_sig b (exist (fun (n : nat) => n < N) (Init.Nat.pred (proj1_sig k)) (H13 x1 k H23)))) y0 (S y0) H26 (le_n (S y0))).
elim (PermutationParity (S N) (PermutationCompose (S N) (PermutationSwap (S N) y1 (exist (fun n : nat => n < S N) y0 H20)) Q)).
rewrite (Fmul_opp_opp f (FI f) (FI f)).
rewrite (Fmul_I_r f (FI f)).
reflexivity.
rewrite (Fmul_I_r f (Fopp f (FI f))).
reflexivity.
move=> H22.
apply (lt_irrefl y0).
unfold lt.
rewrite - H18.
rewrite H22.
apply (le_n y0).
rewrite - (PermutationCompose_assoc (S N)).
rewrite (PermutationCompose_inv_l (S N)).
rewrite (PermutationCompose_O_l (S N) Q).
reflexivity.
apply (lt_trans y0 (S y0) (S N) (le_n (S y0)) H16).
move=> x0 H14 H15 y0 H16 x y H17 H18 Q H19.
suff: (x0 < S N).
move=> H20.
suff: (Q = PermutationCompose (S N) (PermutationCompose (S N) Q (PermutationSwap (S N) x (exist (fun (n : nat) => n < S N) x0 H20))) (PermutationInv (S N) (PermutationSwap (S N) x (exist (fun (n : nat) => n < S N) x0 H20)))).
move=> H21.
rewrite H21.
rewrite (PermutationComposeParity (S N)).
rewrite (PermutationInvParity (S N)).
rewrite (PermutationSwapParity (S N)).
suff: (match ParityXOR (PermutationParity (S N) (PermutationCompose (S N) Q (PermutationSwap (S N) x (exist (fun n : nat => n < S N) x0 H20)))) ON with
  | ON => Fopp f (FI f)
  | OFF => FI f
end = Fmul f (Fopp f (FI f)) match PermutationParity (S N) (PermutationCompose (S N) Q (PermutationSwap (S N) x (exist (fun n : nat => n < S N) x0 H20))) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end).
move=> H22.
rewrite H22.
rewrite (H14 H20 (proj1_sig y) (proj2_sig y) (exist (fun (n : nat) => n < S N) x0 H20) y).
rewrite - (Fmul_assoc f (Fopp f (FI f))).
rewrite (Fmul_comm f (Fopp f (FI f))).
rewrite H17.
reflexivity.
reflexivity.
reflexivity.
apply conj.
move=> k H23.
unfold PermutationSwap.
unfold PermutationCompose.
unfold Basics.compose.
apply sig_map.
simpl.
elim (excluded_middle_informative (k = x)).
move=> H24.
apply False_ind.
apply (le_not_lt x0 (proj1_sig k)).
rewrite H24.
rewrite H17.
apply (le_S x0 x0 (le_n x0)).
apply H23.
move=> H24.
elim (excluded_middle_informative (k = exist (fun (n : nat) => n < S N) x0 H20)).
move=> H25.
apply False_ind.
apply (le_not_lt x0 (proj1_sig k)).
rewrite H25.
apply (le_n x0).
apply H23.
move=> H25.
suff: (proj1_sig k < proj1_sig x).
move=> H26.
rewrite (proj1 H19 k H26).
suff: (H12 x k H26 = H12 (exist (fun (n : nat) => n < S N) x0 H20) k H23).
move=> H27.
rewrite H27.
reflexivity.
apply proof_irrelevance.
rewrite H17.
apply (lt_trans (proj1_sig k) x0 (S x0) H23 (le_n (S x0))).
apply conj.
unfold PermutationSwap.
unfold PermutationCompose.
unfold Basics.compose.
apply sig_map.
simpl.
elim (excluded_middle_informative (exist (fun (n : nat) => n < S N) x0 H20 = x)).
move=> H23.
apply False_ind.
apply (le_not_lt (S x0) x0).
rewrite - H17.
rewrite - H23.
apply (le_n x0).
apply (le_n (S x0)).
move=> H23.
elim (excluded_middle_informative (exist (fun (n : nat) => n < S N) x0 H20 = exist (fun (n : nat) => n < S N) x0 H20)).
move=> H24.
rewrite (proj1 (proj2 H19)).
reflexivity.
move=> H24.
apply False_ind.
apply H24.
reflexivity.
move=> k H23.
unfold PermutationSwap.
unfold PermutationCompose.
unfold Basics.compose.
simpl.
elim (excluded_middle_informative (k = x)).
move=> H24.
apply sig_map.
suff: (x0 < proj1_sig x).
move=> H25.
rewrite (proj1 H19 (exist (fun n : nat => n < S N) x0 H20) H25).
suff: (exist (fun (n : nat) => n < N) (proj1_sig (exist (fun (n : nat) => n < S N) x0 H20)) (H12 x (exist (fun (n : nat) => n < S N) x0 H20) H25) = exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H13 (exist (fun (n : nat) => n < S N) x0 H20) k H23)).
move=> H26.
rewrite H26.
reflexivity.
apply sig_map.
simpl.
rewrite H24.
rewrite H17.
reflexivity.
rewrite H17.
apply (le_n (S x0)).
move=> H24.
elim (excluded_middle_informative (k = exist (fun (n : nat) => n < S N) x0 H20)).
move=> H25.
apply False_ind.
apply (le_not_lt (proj1_sig k) x0).
rewrite H25.
apply (le_n x0).
apply H23.
move=> H25.
suff: (proj1_sig k > proj1_sig x).
move=> H26.
rewrite (proj2 (proj2 H19) k H26).
suff: (H13 x k H26 = H13 (exist (fun (n : nat) => n < S N) x0 H20) k H23).
move=> H27.
rewrite H27.
reflexivity.
apply proof_irrelevance.
elim (le_lt_or_eq (proj1_sig x) (proj1_sig k)).
apply.
move=> H26.
apply False_ind.
apply H24.
apply sig_map.
rewrite H26.
reflexivity.
rewrite H17.
apply H23.
elim (PermutationParity (S N) (PermutationCompose (S N) Q (PermutationSwap (S N) x (exist (fun (n : nat) => n < S N) x0 H20)))).
rewrite (Fmul_opp_opp f (FI f) (FI f)).
rewrite (Fmul_I_r f (FI f)).
reflexivity.
rewrite (Fmul_I_r f (Fopp f (FI f))).
reflexivity.
move=> H22.
apply (lt_irrefl x0).
unfold lt.
rewrite - H17.
rewrite H22.
apply (le_n x0).
rewrite (PermutationCompose_assoc (S N)).
rewrite (PermutationCompose_inv_r (S N)).
rewrite (PermutationCompose_O_r (S N) Q).
reflexivity.
apply (lt_trans x0 (S x0) (S N) (le_n (S x0)) H15).
move=> q k.
suff: (proj1_sig k < S N).
elim (proj1_sig k).
move=> H13 H14.
apply False_ind.
apply (le_not_lt O (proj1_sig q) (le_0_n (proj1_sig q)) H14).
move=> n H13 H14 H15.
apply (lt_S_n n N H14).
apply (proj2_sig k).
move=> q k H12.
apply (le_trans (S (proj1_sig k)) (proj1_sig q) N H12 (le_S_n (proj1_sig q) N (proj2_sig q))).
apply H10.
apply H10.
move=> u1 u2 H8 H9 H10.
apply sig_map.
apply functional_extensionality.
move=> k.
suff: (SkipOne (S N) m (proj1_sig u1 k) = SkipOne (S N) m (proj1_sig u2 k)).
move=> H11.
elim (le_or_lt (proj1_sig (SkipOne (S N) m (proj1_sig u1 k))) (proj1_sig m)).
move=> H12.
suff: (proj1_sig (proj1_sig u1 k) < proj1_sig m).
move=> H13.
apply sig_map.
rewrite - (proj1 (SkipOneNature (S N) m (proj1_sig u1 k)) H13).
rewrite H11.
apply (proj1 (SkipOneNature (S N) m (proj1_sig u2 k))).
elim (le_or_lt (proj1_sig m) (proj1_sig (proj1_sig u2 k))).
move=> H14.
apply False_ind.
apply (le_not_lt (proj1_sig (SkipOne (S N) m (proj1_sig u1 k))) (proj1_sig m) H12).
rewrite H11.
rewrite (proj2 (SkipOneNature (S N) m (proj1_sig u2 k)) H14).
apply (le_n_S (proj1_sig m) (proj1_sig (proj1_sig u2 k)) H14).
apply.
elim (le_or_lt (proj1_sig m) (proj1_sig (proj1_sig u1 k))).
move=> H13.
unfold lt.
rewrite - (proj2 (SkipOneNature (S N) m (proj1_sig u1 k)) H13).
apply H12.
apply.
move=> H12.
apply sig_map.
suff: (proj1_sig m <= proj1_sig (proj1_sig u1 k)).
move=> H13.
apply Nat.succ_inj.
rewrite - (proj2 (SkipOneNature (S N) m (proj1_sig u1 k)) H13).
rewrite H11.
apply (proj2 (SkipOneNature (S N) m (proj1_sig u2 k))).
apply (le_S_n (proj1_sig m) (proj1_sig (proj1_sig u2 k))).
rewrite - (proj2 (SkipOneNature (S N) m (proj1_sig u2 k))).
rewrite - H11.
apply H12.
elim (le_or_lt (proj1_sig m) (proj1_sig (proj1_sig u2 k))).
apply.
move=> H14.
rewrite - (proj1 (SkipOneNature (S N) m (proj1_sig u2 k)) H14).
rewrite - H11.
apply (lt_le_weak (proj1_sig m) (proj1_sig (SkipOne (S N) m (proj1_sig u1 k))) H12).
elim (le_or_lt (proj1_sig m) (proj1_sig (proj1_sig u1 k))).
apply.
move=> H13.
rewrite - (proj1 (SkipOneNature (S N) m (proj1_sig u1 k)) H13).
apply (lt_le_weak (proj1_sig m) (proj1_sig (SkipOne (S N) m (proj1_sig u1 k))) H12).
elim (le_or_lt (proj1_sig p) (proj1_sig k)).
move=> H11.
suff: (k = (exist (fun n : nat => n < N) (pred (S (proj1_sig k)) ) (H5 (exist (fun (n : nat) => n < S N) (S (proj1_sig k)) (le_n_S (S (proj1_sig k)) N (proj2_sig k))) (le_n_S (proj1_sig p) (proj1_sig k) H11)))).
move=> H12.
rewrite H12.
rewrite - (proj2 (proj2 (proj2_sig (H6 u1))) (exist (fun (n : nat) => n < S N) (S (proj1_sig k)) (le_n_S (S (proj1_sig k)) N (proj2_sig k))) (le_n_S (proj1_sig p) (proj1_sig k) H11)).
rewrite - (proj2 (proj2 (proj2_sig (H6 u2))) (exist (fun (n : nat) => n < S N) (S (proj1_sig k)) (le_n_S (S (proj1_sig k)) N (proj2_sig k))) (le_n_S (proj1_sig p) (proj1_sig k) H11)).
rewrite H10.
reflexivity.
apply sig_map.
reflexivity.
move=> H11.
suff: (k = (exist (fun (n : nat) => n < N) (proj1_sig (exist (fun (n : nat) => n < S N) (proj1_sig k) (le_S (S (proj1_sig k)) N (proj2_sig k)))) (H4 (exist (fun (n : nat) => n < S N) (proj1_sig k) (le_S (S (proj1_sig k)) N (proj2_sig k))) H11))).
move=> H12.
rewrite H12.
rewrite - (proj1 (proj2_sig (H6 u1)) (exist (fun (n : nat) => n < S N) (proj1_sig k) (le_S (S (proj1_sig k)) N (proj2_sig k))) H11).
rewrite - (proj1 (proj2_sig (H6 u2)) (exist (fun (n : nat) => n < S N) (proj1_sig k) (le_S (S (proj1_sig k)) N (proj2_sig k))) H11).
rewrite H10.
reflexivity.
apply sig_map.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> P.
elim.
move=> P0 H7 H8.
suff: (forall (k : {n : nat | n < S N}), proj1_sig k < proj1_sig m -> proj1_sig k < N).
move=> H9.
suff: (forall (k : {n : nat | n < S N}), proj1_sig k > proj1_sig m -> pred (proj1_sig k) < N).
move=> H10.
suff: (forall (k : {n : nat | n < N}), {proj1_sig (proj1_sig P0 (SkipOne (S N) p k)) < proj1_sig m} + {proj1_sig (proj1_sig P0 (SkipOne (S N) p k)) > proj1_sig m}).
move=> H11.
suff: (Bijective (fun (k : {n : nat | n < N}) => match H11 k with
  | left H => (exist (fun (n : nat) => n < N) (proj1_sig (proj1_sig P0 (SkipOne (S N) p k))) (H9 (proj1_sig P0 (SkipOne (S N) p k)) H))
  | right H => (exist (fun (n : nat) => n < N) (pred (proj1_sig (proj1_sig P0 (SkipOne (S N) p k)))) (H10 (proj1_sig P0 (SkipOne (S N) p k)) H))
end)).
move=> H12.
apply (Im_intro (Permutation N) (Permutation (S N)) (Full_set (Permutation N)) (fun (P1 : Permutation N) => proj1_sig (H6 P1)) (exist Bijective (fun (k : {n : nat | n < N}) => match H11 k with
  | left H => (exist (fun (n : nat) => n < N) (proj1_sig (proj1_sig P0 (SkipOne (S N) p k))) (H9 (proj1_sig P0 (SkipOne (S N) p k)) H))
  | right H => (exist (fun (n : nat) => n < N) (pred (proj1_sig (proj1_sig P0 (SkipOne (S N) p k)))) (H10 (proj1_sig P0 (SkipOne (S N) p k)) H))
end) H12)).
apply (Full_intro (Permutation N)).
apply sig_map.
apply functional_extensionality.
move=> k.
elim (le_or_lt (proj1_sig k) (proj1_sig p)).
move=> H13.
elim (le_lt_or_eq (proj1_sig k) (proj1_sig p) H13).
move=> H14.
rewrite (proj1 (proj2_sig (H6 (exist Bijective (fun (k0 : {n : nat | n < N}) => match H11 k0 with
  | left H => exist (fun (n : nat) => n < N) (proj1_sig (proj1_sig P0 (SkipOne (S N) p k0))) (H9 (proj1_sig P0 (SkipOne (S N) p k0)) H)
  | right H => exist (fun (n : nat) => n < N) (Init.Nat.pred (proj1_sig (proj1_sig P0 (SkipOne (S N) p k0)))) (H10 (proj1_sig P0 (SkipOne (S N) p k0)) H)
end) H12))) k H14).
simpl.
elim (H11 (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H14))).
move=> H15.
apply sig_map.
rewrite (proj1 (SkipOneNature (S N) m (exist (fun (n : nat) => n < N) (proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H14))))) (H9 (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H14)))) H15))) H15).
suff: (SkipOne (S N) p (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H14)) = k).
move=> H16.
simpl.
rewrite H16.
reflexivity.
apply sig_map.
apply (proj1 (SkipOneNature (S N) p (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H14))) H14).
move=> H15.
apply sig_map.
rewrite (proj2 (SkipOneNature (S N) m (exist (fun (n : nat) => n < N) (pred (proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H14)))))) (H10 (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H14)))) H15)))).
simpl.
suff: (S (pred (proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun n : nat => n < N) (proj1_sig k) (H4 k H14)))))) = proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun n : nat => n < N) (proj1_sig k) (H4 k H14))))).
move=> H16.
rewrite H16.
suff: (SkipOne (S N) p (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H14)) = k).
move=> H17.
rewrite H17.
reflexivity.
apply sig_map.
apply (proj1 (SkipOneNature (S N) p (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H14))) H14).
suff: (proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H14)))) > proj1_sig m).
elim (proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H14))))).
move=> H16.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H16).
move=> n H16 H17.
reflexivity.
apply H15.
apply (le_S_n (proj1_sig m)).
suff: (proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H14)))) > proj1_sig m).
simpl.
elim (proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H14))))).
move=> H16.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H16).
move=> n H16 H17.
apply H17.
apply H15.
move=> H14.
suff: (k = p).
move=> H15.
rewrite H15.
rewrite H7.
rewrite (proj1 (proj2 (proj2_sig (H6 (exist Bijective (fun (k0 : {n : nat | n < N}) => match H11 k0 with
  | left H => exist (fun (n : nat) => n < N) (proj1_sig (proj1_sig P0 (SkipOne (S N) p k0))) (H9 (proj1_sig P0 (SkipOne (S N) p k0)) H)
  | right H => exist (fun (n : nat) => n < N) (pred (proj1_sig (proj1_sig P0 (SkipOne (S N) p k0)))) (H10 (proj1_sig P0 (SkipOne (S N) p k0)) H)
end) H12))))).
reflexivity.
apply sig_map.
apply H14.
move=> H13.
apply sig_map.
rewrite (proj2 (proj2 (proj2_sig (H6 (exist Bijective (fun (k0 : {n : nat | n < N}) => match H11 k0 with
  | left H => exist (fun (n : nat) => n < N) (proj1_sig (proj1_sig P0 (SkipOne (S N) p k0))) (H9 (proj1_sig P0 (SkipOne (S N) p k0)) H)
  | right H => exist (fun (n : nat) => n < N) (Init.Nat.pred (proj1_sig (proj1_sig P0 (SkipOne (S N) p k0)))) (H10 (proj1_sig P0 (SkipOne (S N) p k0)) H)
end) H12))))).
simpl.
elim (H11 (exist (fun (n : nat) => n < N) (Init.Nat.pred (proj1_sig k)) (H5 k H13))).
move=> H14.
rewrite (proj1 (SkipOneNature (S N) m (exist (fun (n : nat) => n < N) (proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H13))))) (H9 (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H13)))) H14)))).
simpl.
suff: (SkipOne (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H13)) = k).
move=> H15.
rewrite H15.
reflexivity.
apply sig_map.
rewrite (proj2 (SkipOneNature (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H13)))).
simpl.
suff: (proj1_sig p < proj1_sig k).
elim (proj1_sig k).
move=> H15.
apply False_ind.
apply (le_not_lt O (proj1_sig p) (le_0_n (proj1_sig p)) H15).
move=> n H15 H16.
reflexivity.
apply H13.
apply (le_S_n (proj1_sig p) (pred (proj1_sig k))).
suff: (S (pred (proj1_sig k)) = proj1_sig k).
move=> H15.
rewrite H15.
apply H13.
suff: (proj1_sig p < proj1_sig k).
elim (proj1_sig k).
move=> H15.
apply False_ind.
apply (le_not_lt O (proj1_sig p) (le_0_n (proj1_sig p)) H15).
move=> H15 H16.
reflexivity.
apply H13.
apply H14.
move=> H14.
rewrite (proj2 (SkipOneNature (S N) m (exist (fun (n : nat) => n < N) (pred (proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H13)))))) (H10 (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H13)))) H14)))).
simpl.
suff: (SkipOne (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H13)) = k).
move=> H15.
rewrite - {1} H15.
suff: (proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H13)))) > proj1_sig m).
elim (proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H13))))).
move=> H16.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H16).
move=> n H16 H17.
reflexivity.
apply H14.
apply sig_map.
rewrite (proj2 (SkipOneNature (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H13)))).
simpl.
suff: (proj1_sig p < proj1_sig k).
elim (proj1_sig k).
move=> H15.
apply False_ind.
apply (le_not_lt O (proj1_sig p) (le_0_n (proj1_sig p)) H15).
move=> n H15 H16.
reflexivity.
apply H13.
apply (le_S_n (proj1_sig p) (pred (proj1_sig k))).
suff: (proj1_sig p < proj1_sig k).
elim (proj1_sig k).
move=> H15.
apply False_ind.
apply (le_not_lt O (proj1_sig p) (le_0_n (proj1_sig p)) H15).
move=> n H15 H16.
apply H16.
apply H13.
apply le_S_n.
simpl.
suff: (S (pred (proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H13)))))) = proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H13))))).
move=> H15.
rewrite H15.
apply H14.
suff: (proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H13)))) > proj1_sig m).
elim (proj1_sig (proj1_sig P0 (SkipOne (S N) p (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H13))))).
move=> H15.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H15).
move=> n H15 H16.
reflexivity.
apply H14.
apply CountInjBij.
move=> k1 k2.
elim (H11 k1).
move=> H12.
elim (H11 k2).
move=> H13 H14.
suff: (SkipOne (S N) p k1 = SkipOne (S N) p k2).
move=> H15.
elim (le_or_lt (proj1_sig p) (proj1_sig (SkipOne (S N) p k1))).
move=> H16.
apply sig_map.
apply (Nat.succ_inj (proj1_sig k1) (proj1_sig k2)).
rewrite - (proj2 (SkipOneNature (S N) p k1)).
rewrite - (proj2 (SkipOneNature (S N) p k2)).
rewrite H15.
reflexivity.
elim (le_or_lt (proj1_sig p) (proj1_sig k2)).
apply.
move=> H17.
rewrite - (proj1 (SkipOneNature (S N) p k2) H17).
rewrite - H15.
apply H16.
elim (le_or_lt (proj1_sig p) (proj1_sig k1)).
apply.
move=> H17.
rewrite - (proj1 (SkipOneNature (S N) p k1) H17).
apply H16.
move=> H16.
apply sig_map.
rewrite - (proj1 (SkipOneNature (S N) p k1)).
rewrite - (proj1 (SkipOneNature (S N) p k2)).
rewrite H15.
reflexivity.
elim (le_or_lt (proj1_sig p) (proj1_sig k2)).
move=> H17.
unfold lt.
rewrite - (proj2 (SkipOneNature (S N) p k2) H17).
rewrite - H15.
apply (lt_le_weak (proj1_sig (SkipOne (S N) p k1)) (proj1_sig p) H16).
apply.
elim (le_or_lt (proj1_sig p) (proj1_sig k1)).
move=> H17.
unfold lt.
rewrite - (proj2 (SkipOneNature (S N) p k1) H17).
apply (lt_le_weak (proj1_sig (SkipOne (S N) p k1)) (proj1_sig p) H16).
apply.
apply (BijInj {n : nat | n < S N} {n : nat | n < S N} (proj1_sig P0) (proj2_sig P0)).
apply sig_map.
suff: (proj1_sig (proj1_sig P0 (SkipOne (S N) p k1)) = proj1_sig (exist (fun (n : nat) => n < N) (proj1_sig (proj1_sig P0 (SkipOne (S N) p k1))) (H9 (proj1_sig P0 (SkipOne (S N) p k1)) H12))).
move=> H15.
rewrite H15.
rewrite H14.
reflexivity.
reflexivity.
move=> H13 H14.
apply False_ind.
apply (lt_irrefl (proj1_sig m)).
apply (le_trans (S (proj1_sig m)) (S (proj1_sig (proj1_sig P0 (SkipOne (S N) p k1)))) (proj1_sig m)).
suff: (proj1_sig (proj1_sig P0 (SkipOne (S N) p k1)) = proj1_sig (exist (fun (n : nat) => n < N) (proj1_sig (proj1_sig P0 (SkipOne (S N) p k1))) (H9 (proj1_sig P0 (SkipOne (S N) p k1)) H12))).
move=> H15.
rewrite H15.
rewrite H14.
simpl.
suff: (S (pred (proj1_sig (proj1_sig P0 (SkipOne (S N) p k2)))) = (proj1_sig (proj1_sig P0 (SkipOne (S N) p k2)))).
move=> H16.
rewrite H16.
apply H13.
suff: (proj1_sig (proj1_sig P0 (SkipOne (S N) p k2)) > proj1_sig m).
elim (proj1_sig (proj1_sig P0 (SkipOne (S N) p k2))).
move=> H16.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H16).
move=> n H16 H17.
reflexivity.
apply H13.
reflexivity.
apply H12.
move=> H12.
elim (H11 k2).
move=> H13 H14.
apply False_ind.
apply (lt_irrefl (proj1_sig m)).
apply (le_trans (S (proj1_sig m)) (S (proj1_sig (proj1_sig P0 (SkipOne (S N) p k2)))) (proj1_sig m)).
suff: (proj1_sig (proj1_sig P0 (SkipOne (S N) p k2)) = proj1_sig (exist (fun (n : nat) => n < N) (proj1_sig (proj1_sig P0 (SkipOne (S N) p k2))) (H9 (proj1_sig P0 (SkipOne (S N) p k2)) H13))).
move=> H15.
rewrite H15.
rewrite - H14.
simpl.
suff: (S (pred (proj1_sig (proj1_sig P0 (SkipOne (S N) p k1)))) = (proj1_sig (proj1_sig P0 (SkipOne (S N) p k1)))).
move=> H16.
rewrite H16.
apply H12.
suff: (proj1_sig (proj1_sig P0 (SkipOne (S N) p k1)) > proj1_sig m).
elim (proj1_sig (proj1_sig P0 (SkipOne (S N) p k1))).
move=> H16.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H16).
move=> n H16 H17.
reflexivity.
apply H12.
reflexivity.
apply H13.
move=> H13 H14.
suff: (SkipOne (S N) p k1 = SkipOne (S N) p k2).
move=> H15.
elim (le_or_lt (proj1_sig p) (proj1_sig (SkipOne (S N) p k1))).
move=> H16.
apply sig_map.
apply (Nat.succ_inj (proj1_sig k1) (proj1_sig k2)).
rewrite - (proj2 (SkipOneNature (S N) p k1)).
rewrite - (proj2 (SkipOneNature (S N) p k2)).
rewrite H15.
reflexivity.
elim (le_or_lt (proj1_sig p) (proj1_sig k2)).
apply.
move=> H17.
rewrite - (proj1 (SkipOneNature (S N) p k2) H17).
rewrite - H15.
apply H16.
elim (le_or_lt (proj1_sig p) (proj1_sig k1)).
apply.
move=> H17.
rewrite - (proj1 (SkipOneNature (S N) p k1) H17).
apply H16.
move=> H16.
apply sig_map.
rewrite - (proj1 (SkipOneNature (S N) p k1)).
rewrite - (proj1 (SkipOneNature (S N) p k2)).
rewrite H15.
reflexivity.
elim (le_or_lt (proj1_sig p) (proj1_sig k2)).
move=> H17.
unfold lt.
rewrite - (proj2 (SkipOneNature (S N) p k2) H17).
rewrite - H15.
apply (lt_le_weak (proj1_sig (SkipOne (S N) p k1)) (proj1_sig p) H16).
apply.
elim (le_or_lt (proj1_sig p) (proj1_sig k1)).
move=> H17.
unfold lt.
rewrite - (proj2 (SkipOneNature (S N) p k1) H17).
apply (lt_le_weak (proj1_sig (SkipOne (S N) p k1)) (proj1_sig p) H16).
apply.
apply (BijInj {n : nat | n < S N} {n : nat | n < S N} (proj1_sig P0) (proj2_sig P0)).
apply sig_map.
suff: (proj1_sig (proj1_sig P0 (SkipOne (S N) p k1)) = S (proj1_sig (exist (fun (n : nat) => n < N) (pred (proj1_sig (proj1_sig P0 (SkipOne (S N) p k1)))) (H10 (proj1_sig P0 (SkipOne (S N) p k1)) H12)))).
move=> H15.
rewrite H15.
rewrite H14.
simpl.
suff: (proj1_sig (proj1_sig P0 (SkipOne (S N) p k2)) > proj1_sig m).
elim (proj1_sig (proj1_sig P0 (SkipOne (S N) p k2))).
move=> H16.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H16).
move=> n H16 H17.
reflexivity.
apply H13.
simpl.
suff: (proj1_sig (proj1_sig P0 (SkipOne (S N) p k1)) > proj1_sig m).
elim (proj1_sig (proj1_sig P0 (SkipOne (S N) p k1))).
move=> H15.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H15).
move=> n H15 H16.
reflexivity.
apply H12.
move=> k.
elim (le_lt_dec (proj1_sig (proj1_sig P0 (SkipOne (S N) p k))) (proj1_sig m)).
move=> H11.
left.
elim (le_lt_or_eq (proj1_sig (proj1_sig P0 (SkipOne (S N) p k))) (proj1_sig m) H11).
apply.
move=> H12.
apply False_ind.
suff: (SkipOne (S N) p k = p).
move=> H13.
elim (le_or_lt (proj1_sig p) (proj1_sig k)).
move=> H14.
apply (lt_irrefl (proj1_sig (SkipOne (S N) p k))).
rewrite {2} (proj2 (SkipOneNature (S N) p k) H14).
rewrite H13.
apply (le_n_S (proj1_sig p) (proj1_sig k) H14).
move=> H14.
apply (lt_irrefl (proj1_sig (SkipOne (S N) p k))).
rewrite {1} (proj1 (SkipOneNature (S N) p k) H14).
rewrite H13.
apply H14.
apply (BijInj {n : nat | n < S N} {n : nat | n < S N} (proj1_sig P0) (proj2_sig P0)).
rewrite H7.
apply sig_map.
apply H12.
move=> H11.
right.
apply H11.
move=> k.
suff: (proj1_sig k < S N).
elim (proj1_sig k).
move=> H10 H11.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H11).
move=> n H10 H11 H12.
apply (le_S_n (S n) N H11).
apply (proj2_sig k).
move=> k H9.
apply (le_trans (S (proj1_sig k)) (proj1_sig m) N H9 (le_S_n (proj1_sig m) N (proj2_sig m))).
move=> k.
elim.
move=> q H7 y H8.
apply (Intersection_intro (Permutation (S N))).
rewrite H8.
apply (proj1 (proj2 (proj2_sig (H6 q)))).
apply (Full_intro (Permutation (S N)) y).
move=> P.
suff: (Bijective (fun (k : {n : nat | n < S N}) => match excluded_middle_informative (proj1_sig k < proj1_sig p) with
  | left H => SkipOne (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H)))
  | right _ => (match excluded_middle_informative (proj1_sig k > proj1_sig p) with
    | left H => SkipOne (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H)))
    | right _ => m
  end)
end)).
move=> H6.
exists (exist Bijective (fun (k : {n : nat | n < S N}) => match excluded_middle_informative (proj1_sig k < proj1_sig p) with
  | left H => SkipOne (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k) (H4 k H)))
  | right _ => (match excluded_middle_informative (proj1_sig k > proj1_sig p) with
    | left H => SkipOne (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k)) (H5 k H)))
    | right _ => m
  end)
end) H6).
simpl.
apply conj.
move=> k H7.
elim (excluded_middle_informative (proj1_sig k < proj1_sig p)).
move=> H8.
suff: (H7 = H8).
move=> H9.
rewrite H9.
reflexivity.
apply proof_irrelevance.
move=> H8.
apply False_ind.
apply (H8 H7).
apply conj.
elim (excluded_middle_informative (proj1_sig p < proj1_sig p)).
move=> H7.
apply False_ind.
apply (lt_irrefl (proj1_sig p) H7).
move=> H7.
elim (excluded_middle_informative (proj1_sig p > proj1_sig p)).
move=> H8.
apply False_ind.
apply (H7 H8).
move=> H8.
reflexivity.
move=> k H7.
elim (excluded_middle_informative (proj1_sig k < proj1_sig p)).
move=> H8.
apply False_ind.
apply (lt_irrefl (proj1_sig k) (lt_trans (proj1_sig k) (proj1_sig p) (proj1_sig k) H8 H7)).
move=> H8.
elim (excluded_middle_informative (proj1_sig k > proj1_sig p)).
move=> H9.
suff: (H7 = H9).
move=> H10.
rewrite H10.
reflexivity.
apply proof_irrelevance.
move=> H9.
apply False_ind.
apply (H9 H7).
apply (CountInjBij (S N)).
move=> k1 k2.
elim (excluded_middle_informative (proj1_sig k1 < proj1_sig p)).
move=> H6.
elim (excluded_middle_informative (proj1_sig k2 < proj1_sig p)).
move=> H7 H8.
apply sig_map.
suff: (exist (fun (n : nat) => n < N) (proj1_sig k1) (H4 k1 H6) = exist (fun (n : nat) => n < N) (proj1_sig k2) (H4 k2 H7)).
move=> H9.
suff: (proj1_sig k1 = proj1_sig (exist (fun (n : nat) => n < N) (proj1_sig k1) (H4 k1 H6))).
move=> H10.
rewrite H10.
rewrite H9.
reflexivity.
reflexivity.
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig P) (proj2_sig P) (exist (fun (n : nat) => n < N) (proj1_sig k1) (H4 k1 H6)) (exist (fun (n : nat) => n < N) (proj1_sig k2) (H4 k2 H7)) (SkipOneInj (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k1) (H4 k1 H6))) (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k2) (H4 k2 H7))) H8)).
move=> H7.
elim (excluded_middle_informative (proj1_sig k2 > proj1_sig p)).
move=> H8 H9.
apply False_ind.
suff: (proj1_sig k1 = pred (proj1_sig k2)).
move=> H10.
apply (le_not_lt (pred (proj1_sig k2)) (proj1_sig k1)).
rewrite H10.
apply (le_n (pred (proj1_sig k2))).
apply (le_trans (S (proj1_sig k1)) (proj1_sig p) (pred (proj1_sig k2)) H6).
suff: (proj1_sig k2 > proj1_sig p).
elim (proj1_sig k2).
move=> H11.
apply False_ind.
apply (le_not_lt O (proj1_sig p) (le_0_n (proj1_sig p)) H11).
move=> n H11 H12.
apply (le_S_n (proj1_sig p) (pred (S n)) H12).
apply H8.
suff: (exist (fun (n : nat) => n < N) (proj1_sig k1) (H4 k1 H6) = exist (fun (n : nat) => n < N) (Init.Nat.pred (proj1_sig k2)) (H5 k2 H8)).
move=> H10.
suff: (proj1_sig k1 = proj1_sig (exist (fun (n : nat) => n < N) (proj1_sig k1) (H4 k1 H6))).
move=> H11.
rewrite H11.
rewrite H10.
reflexivity.
reflexivity.
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig P) (proj2_sig P)).
apply (SkipOneInj (S N) m).
apply H9.
move=> H8 H9.
apply False_ind.
elim (le_or_lt (proj1_sig m) (proj1_sig (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k1) (H4 k1 H6))))).
move=> H10.
apply (lt_irrefl (proj1_sig m)).
rewrite - H9.
rewrite {2} (proj2 (SkipOneNature (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k1) (H4 k1 H6))))).
rewrite H9.
apply (le_n_S (proj1_sig m) (proj1_sig (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k1) (H4 k1 H6)))) H10).
apply H10.
move=> H10.
apply (le_not_lt (proj1_sig m) (proj1_sig (SkipOne (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k1) (H4 k1 H6)))))).
rewrite H9.
apply (le_n (proj1_sig m)).
rewrite (proj1 (SkipOneNature (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k1) (H4 k1 H6)))) H10).
apply H10.
move=> H6.
elim (excluded_middle_informative (proj1_sig k1 > proj1_sig p)).
move=> H7.
elim (excluded_middle_informative (proj1_sig k2 < proj1_sig p)).
move=> H8 H9.
apply False_ind.
apply (le_not_lt (pred (proj1_sig k1)) (proj1_sig k2)).
suff: (exist (fun (n : nat) => n < N) (pred (proj1_sig k1)) (H5 k1 H7) = exist (fun (n : nat) => n < N) (proj1_sig k2) (H4 k2 H8)).
move=> H10.
suff: (pred (proj1_sig k1) = proj1_sig (exist (fun (n : nat) => n < N) (pred (proj1_sig k1)) (H5 k1 H7))).
move=> H11.
rewrite H11.
rewrite H10.
apply (le_n (proj1_sig k2)).
reflexivity.
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig P) (proj2_sig P)).
apply (SkipOneInj (S N) m).
apply H9.
apply (le_trans (S (proj1_sig k2)) (proj1_sig p) (pred (proj1_sig k1)) H8).
apply (le_S_n (proj1_sig p) (pred (proj1_sig k1))).
suff: (proj1_sig k1 > proj1_sig p).
elim (proj1_sig k1).
move=> H10.
apply False_ind.
apply (le_not_lt O (proj1_sig p) (le_0_n (proj1_sig p)) H10).
move=> n H10 H11.
apply H11.
apply H7.
move=> H8.
elim (excluded_middle_informative (proj1_sig k2 > proj1_sig p)).
move=> H9 H10.
apply sig_map.
suff: (pred (proj1_sig k1) = pred (proj1_sig k2)).
suff: (proj1_sig k1 > proj1_sig p).
suff: (proj1_sig k2 > proj1_sig p).
elim (proj1_sig k2).
move=> H11.
apply False_ind.
apply (le_not_lt O (proj1_sig p) (le_0_n (proj1_sig p)) H11).
move=> n H11 H12.
elim (proj1_sig k1).
move=> H13.
apply False_ind.
apply (le_not_lt O (proj1_sig p) (le_0_n (proj1_sig p)) H13).
simpl.
move=> k H13 H14 H15.
rewrite H15.
reflexivity.
apply H9.
apply H7.
suff: (exist (fun (n : nat) => n < N) (pred (proj1_sig k1)) (H5 k1 H7) = exist (fun (n : nat) => n < N) (pred (proj1_sig k2)) (H5 k2 H9)).
move=> H11.
suff: (pred (proj1_sig k1) = proj1_sig (exist (fun (n : nat) => n < N) (pred (proj1_sig k1)) (H5 k1 H7))).
move=> H12.
rewrite H12.
rewrite H11.
reflexivity.
reflexivity.
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig P) (proj2_sig P)).
apply (SkipOneInj (S N) m).
apply H10.
move=> H9 H10.
apply False_ind.
elim (le_or_lt (proj1_sig m) (proj1_sig (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k1)) (H5 k1 H7))))).
move=> H11.
apply (le_not_lt (proj1_sig (SkipOne (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k1)) (H5 k1 H7))))) (proj1_sig m)).
rewrite H10.
apply (le_n (proj1_sig m)).
rewrite (proj2 (SkipOneNature (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k1)) (H5 k1 H7)))) H11).
apply (le_n_S (proj1_sig m) (proj1_sig (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k1)) (H5 k1 H7)))) H11).
move=> H11.
apply (le_not_lt (proj1_sig m) (proj1_sig (SkipOne (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k1)) (H5 k1 H7)))))).
rewrite H10.
apply (le_n (proj1_sig m)).
rewrite (proj1 (SkipOneNature (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k1)) (H5 k1 H7)))) H11).
apply H11.
move=> H7.
elim (excluded_middle_informative (proj1_sig k2 < proj1_sig p)).
move=> H8 H9.
apply False_ind.
elim (le_or_lt (proj1_sig m) (proj1_sig (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k2) (H4 k2 H8))))).
move=> H10.
apply (le_not_lt (proj1_sig (SkipOne (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k2) (H4 k2 H8))))) (proj1_sig m)).
rewrite - H9.
apply (le_n (proj1_sig m)).
rewrite (proj2 (SkipOneNature (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k2) (H4 k2 H8)))) H10).
apply (le_n_S (proj1_sig m) (proj1_sig (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k2) (H4 k2 H8)))) H10).
move=> H10.
apply (le_not_lt (proj1_sig m) (proj1_sig (SkipOne (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k2) (H4 k2 H8)))))).
rewrite - H9.
apply (le_n (proj1_sig m)).
rewrite (proj1 (SkipOneNature (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (proj1_sig k2) (H4 k2 H8)))) H10).
apply H10.
move=> H8.
elim (excluded_middle_informative (proj1_sig k2 > proj1_sig p)).
move=> H9 H10.
apply False_ind.
elim (le_or_lt (proj1_sig m) (proj1_sig (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k2)) (H5 k2 H9))))).
move=> H11.
apply (le_not_lt (proj1_sig (SkipOne (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k2)) (H5 k2 H9))))) (proj1_sig m)).
rewrite - H10.
apply (le_n (proj1_sig m)).
rewrite (proj2 (SkipOneNature (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k2)) (H5 k2 H9)))) H11).
apply (le_n_S (proj1_sig m) (proj1_sig (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k2)) (H5 k2 H9)))) H11).
move=> H11.
apply (le_not_lt (proj1_sig m) (proj1_sig (SkipOne (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k2)) (H5 k2 H9)))))).
rewrite - H10.
apply (le_n (proj1_sig m)).
rewrite (proj1 (SkipOneNature (S N) m (proj1_sig P (exist (fun (n : nat) => n < N) (pred (proj1_sig k2)) (H5 k2 H9)))) H11).
apply H11.
move=> H9 H10.
elim (le_or_lt (proj1_sig k1) (proj1_sig p)).
move=> H11.
elim (le_lt_or_eq (proj1_sig k1) (proj1_sig p) H11).
move=> H12.
apply False_ind.
apply (H6 H12).
move=> H12.
elim (le_or_lt (proj1_sig k2) (proj1_sig p)).
move=> H13.
elim (le_lt_or_eq (proj1_sig k2) (proj1_sig p) H13).
move=> H14.
apply False_ind.
apply (H8 H14).
move=> H14.
apply sig_map.
rewrite H14.
apply H12.
move=> H13.
apply False_ind.
apply (H9 H13).
move=> H11.
apply False_ind.
apply (H7 H11).
move=> k.
suff: (proj1_sig k < S N).
elim (proj1_sig k).
move=> H5 H6.
apply False_ind.
apply (le_not_lt O (proj1_sig p) (le_0_n (proj1_sig p)) H6).
move=> n H5 H6 H7.
apply (le_S_n (S n) N H6).
apply (proj2_sig k).
move=> k H4.
apply (le_trans (S (proj1_sig k)) (proj1_sig p) N H4).
apply (le_S_n (proj1_sig p) N (proj2_sig p)).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> k H2.
apply (Full_intro {n : nat| n < S N} k).
move=> m H2.
apply (Im_intro (Permutation (S N)) {n : nat | n < S N} (Full_set (Permutation (S N))) (fun (P : Permutation (S N)) => proj1_sig P p) (PermutationSwap (S N) p m)).
apply (Full_intro (Permutation (S N)) (PermutationSwap (S N) p m)).
unfold PermutationSwap.
simpl.
elim (excluded_middle_informative (p = p)).
move=> H3.
reflexivity.
move=> H3.
apply False_ind.
apply H3.
reflexivity.
Qed.

Lemma DeterminantDivideH : forall (f : Field) (N : nat) (A : Matrix f N N) (p : {n : nat | (n < N)}), Determinant f N A = MySumF2 {n : nat | n < N} (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N)) (FPCM f) (fun (n : Count N) => Fmul f (Cofactor f N A n p) (A n p)).
Proof.
move=> f N A p.
rewrite - (DeterminantTrans f N A).
rewrite (DeterminantDivideW f N (MTranspose f N N A) p).
apply (MySumF2Same {n : nat | n < N} (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N))).
move=> u H1.
rewrite (Fmul_comm f (Cofactor f N A u p) (A u p)).
unfold Cofactor.
rewrite (DeterminantTrans f (pred N) (fun (x y : {n : nat | n < pred N}) => A (SkipOne N u x) (SkipOne N p y))).
rewrite (plus_comm (proj1_sig u) (proj1_sig p)).
reflexivity.
Qed.

Definition CofactorMatrix (f : Field) (N : nat) (A : Matrix f N N) := MTranspose f N N (Cofactor f N A).

Lemma CofactorMultR : forall (f : Field) (N : nat) (A : Matrix f N N), Mmult f N N N A (CofactorMatrix f N A) = VMmult f N N (Determinant f N A) (MI f N).
Proof.
move=> f N A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MI.
unfold VMmult.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H1.
suff: (x = y).
move=> H2.
rewrite H2.
rewrite (Fmul_I_r f (Determinant f N A)).
rewrite (DeterminantDivideW f N A y).
reflexivity.
apply sig_map.
apply H1.
move=> H1.
rewrite (Fmul_O_r f (Determinant f N A)).
unfold Mmult.
suff: ((fun (n : Count N) => Fmul f (A x n) (CofactorMatrix f N A n y)) = (fun (n : Count N) => Fmul f ((fun (a : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig a) (proj1_sig y) with
  | left _ => A x
  | right _ => A a
end) y n) (Cofactor f N (fun (a : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig a) (proj1_sig y) with
  | left _ => A x
  | right _ => A a
end) y n))).
move=> H2.
rewrite H2.
rewrite - (DeterminantDivideW f N (fun (a : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig a) (proj1_sig y) with
  | left _ => A x
  | right _ => A a
end) y).
apply (DeterminantDuplicateH f N (fun (a : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig a) (proj1_sig y) with
  | left _ => A x
  | right _ => A a
end) x y H1).
elim (Nat.eq_dec (proj1_sig y) (proj1_sig y)).
move=> H3.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H4.
reflexivity.
move=> H4.
reflexivity.
move=> H3.
apply False_ind.
apply H3.
reflexivity.
apply functional_extensionality.
move=> n.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig y)).
move=> H2.
unfold CofactorMatrix.
unfold MTranspose.
unfold Cofactor.
suff: ((fun (x0 y0 : {n0 : nat | n0 < pred N}) => A (SkipOne N y x0) (SkipOne N n y0)) = (fun (x0 y0 : {n0 : nat | n0 < pred N}) => (match Nat.eq_dec (proj1_sig (SkipOne N y x0)) (proj1_sig y) with
  | left _ => A x
  | right _ => A (SkipOne N y x0)
end) (SkipOne N n y0))).
move=> H3.
rewrite H3.
reflexivity.
apply functional_extensionality.
move=> x0.
elim (Nat.eq_dec (proj1_sig (SkipOne N y x0)) (proj1_sig y)).
move=> H3.
apply False_ind.
elim (le_or_lt (proj1_sig y) (proj1_sig x0)).
move=> H4.
apply (le_not_lt (proj1_sig y) (proj1_sig x0) H4).
unfold lt.
rewrite - (proj2 (SkipOneNature N y x0) H4).
rewrite H3.
apply (le_n (proj1_sig y)).
move=> H4.
apply (le_not_lt (proj1_sig y) (proj1_sig x0)).
rewrite - (proj1 (SkipOneNature N y x0) H4).
rewrite H3.
apply (le_n (proj1_sig y)).
apply H4.
move=> H3.
reflexivity.
move=> H2.
apply False_ind.
apply H2.
reflexivity.
Qed.

Lemma CofactorMultL : forall (f : Field) (N : nat) (A : Matrix f N N), Mmult f N N N (CofactorMatrix f N A) A = VMmult f N N (Determinant f N A) (MI f N).
Proof.
move=> f N A.
apply (MTransReg f N N (Mmult f N N N (CofactorMatrix f N A) A) (VMmult f N N (Determinant f N A) (MI f N))).
rewrite (MTransMult f N N N (CofactorMatrix f N A) A).
rewrite (MTransVMult f N N (Determinant f N A) (MI f N)).
rewrite - (DeterminantTrans f N A).
rewrite (MTransI f N).
rewrite - (CofactorMultR f N (MTranspose f N N A)).
suff: (MTranspose f N N (CofactorMatrix f N A) = CofactorMatrix f N (MTranspose f N N A)).
move=> H1.
rewrite H1.
reflexivity.
unfold CofactorMatrix.
unfold Cofactor.
unfold MTranspose.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite - (DeterminantTrans f (pred N) (fun (x0 y0 : {n : nat | n < pred N}) => A (SkipOne N x y0) (SkipOne N y x0))).
rewrite (plus_comm (proj1_sig x) (proj1_sig y)).
reflexivity.
Qed.

Lemma CofactorMult : forall (f : Field) (N : nat) (A B : Matrix f N N), CofactorMatrix f N (Mmult f N N N A B) = Mmult f N N N (CofactorMatrix f N B) (CofactorMatrix f N A).
Proof.
move=> f.
elim.
move=> A B.
apply functional_extensionality.
move=> x.
apply False_ind.
apply (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) (proj2_sig x)).
move=> N H1 A B.
unfold CofactorMatrix.
rewrite - (MTransMult f (S N) (S N) (S N) (Cofactor f (S N) A) (Cofactor f (S N) B)).
unfold Mmult at 2.
unfold Cofactor.
suff: ((fun (p q : {n : nat | n < S N}) => Fmul f (PowF f (Fopp f (FI f)) (proj1_sig p + proj1_sig q)) (Determinant f (pred (S N)) (fun (x y : {n : nat | n < pred (S N)}) => Mmult f (S N) (S N) (S N) A B (SkipOne (S N) p x) (SkipOne (S N) q y)))) = (fun (x y : {n : nat | n < S N}) => MySumF2 {n : nat | n < S N} (exist (Finite (Count (S N))) (Full_set {n : nat | n < S N}) (CountFinite (S N))) (FPCM f) (fun n : Count (S N) => Fmul f (Fmul f (PowF f (Fopp f (FI f)) (proj1_sig x + proj1_sig n)) (Determinant f (pred (S N)) (fun (x0 y0 : {n0 : nat | n0 < pred (S N)}) => A (SkipOne (S N) x x0) (SkipOne (S N) n y0)))) (Fmul f (PowF f (Fopp f (FI f)) (proj1_sig n + proj1_sig y)) (Determinant f (pred (S N)) (fun (x0 y0 : {n0 : nat | n0 < pred (S N)}) => B (SkipOne (S N) n x0) (SkipOne (S N) y y0))))))).
move=> H2.
rewrite H2.
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
simpl.
suff: ((fun (x0 y0 : {n : nat | n < N}) => Mmult f (S N) (S N) (S N) A B (SkipOne (S N) x x0) (SkipOne (S N) y y0)) = Mmult f N (S N) N (fun (x0 : {n : nat | n < N}) (y0 : {n : nat | n < S N}) => A (SkipOne (S N) x x0) y0) (fun (x0 : {n : nat | n < S N}) (y0 : {n : nat | n < N}) => B x0 (SkipOne (S N) y y0))).
move=> H2.
rewrite H2.
rewrite (CauchyBinet f N (S N) (fun (x0 : {n : nat | n < N}) (y0 : {n : nat | n < S N}) => A (SkipOne (S N) x x0) y0) (fun (x0 : {n : nat | n < S N}) (y0 : {n : nat | n < N}) => B x0 (SkipOne (S N) y y0))).
suff: ((FiniteIntersection ({n : nat | n < N} -> {n : nat | n < S N}) (exist (Finite ({n : nat | n < N} -> {n : nat | n < S N})) (Full_set ({n : nat | n < N} -> {n : nat | n < S N})) (CountPowFinite N (S N))) (fun (r : {n : nat | n < N} -> {n : nat | n < S N}) => forall (p q : {n : nat | n < N}), proj1_sig p < proj1_sig q -> proj1_sig (r p) < proj1_sig (r q))) = FiniteIm {n : nat | n < S N} ({n : nat | n < N} -> {n : nat | n < S N}) (SkipOne (S N)) (exist (Finite (Count (S N))) (Full_set {n : nat | n < S N}) (CountFinite (S N)))).
move=> H3.
rewrite H3.
rewrite - (MySumF2BijectiveSame2 {n : nat | n < S N} ({n : nat | n < N} -> {n : nat | n < S N}) (exist (Finite (Count (S N))) (Full_set {n : nat | n < S N}) (CountFinite (S N)))).
unfold Basics.compose.
apply (FiniteSetInduction {n : nat | n < S N} (exist (Finite (Count (S N))) (Full_set {n : nat | n < S N}) (CountFinite (S N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Fmul_O_r f (PowF f (Fopp f (FI f)) (proj1_sig x + proj1_sig y))).
move=> C c H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Fmul_add_distr_l f (PowF f (Fopp f (FI f)) (proj1_sig x + proj1_sig y))).
rewrite H7.
apply (Fadd_eq_compat_l f).
rewrite (Fmul_assoc f (PowF f (Fopp f (FI f)) (proj1_sig x + proj1_sig c)) (Determinant f N (fun (x0 y0 : {n : nat | n < N}) => A (SkipOne (S N) x x0) (SkipOne (S N) c y0)))).
rewrite - (Fmul_assoc f (Determinant f N (fun (x0 y0 : {n : nat | n < N}) => A (SkipOne (S N) x x0) (SkipOne (S N) c y0))) (PowF f (Fopp f (FI f)) (proj1_sig c + proj1_sig y)) (Determinant f N (fun (x0 y0 : {n0 : nat | n0 < N}) => B (SkipOne (S N) c x0) (SkipOne (S N) y y0)))).
rewrite (Fmul_comm f (Determinant f N (fun (x0 y0 : {n : nat | n < N}) => A (SkipOne (S N) x x0) (SkipOne (S N) c y0))) (PowF f (Fopp f (FI f)) (proj1_sig c + proj1_sig y))).
rewrite - (Fmul_assoc f (PowF f (Fopp f (FI f)) (proj1_sig x + proj1_sig c))).
rewrite (Fmul_assoc f (PowF f (Fopp f (FI f)) (proj1_sig x + proj1_sig c))).
rewrite (Fmul_assoc f (PowF f (Fopp f (FI f)) (proj1_sig c + proj1_sig y))).
rewrite - (Fmul_assoc f (PowF f (Fopp f (FI f)) (proj1_sig x + proj1_sig c))).
apply (Fmul_eq_compat_r f).
rewrite (plus_comm (proj1_sig x) (proj1_sig c)).
elim (proj1_sig c).
elim (proj1_sig x).
simpl.
rewrite (Fmul_I_l f (PowF f (Fopp f (FI f)) (proj1_sig y))).
reflexivity.
simpl.
move=> n H8.
rewrite H8.
rewrite (Fmul_assoc f (PowF f (Fopp f (FI f)) n) (Fopp f (FI f))).
rewrite (Fmul_assoc f (PowF f (Fopp f (FI f)) n) (PowF f (Fopp f (FI f)) (proj1_sig y))).
rewrite (Fmul_comm f (Fopp f (FI f))).
reflexivity.
move=> n H8.
rewrite H8.
simpl.
rewrite (Fmul_comm f (PowF f (Fopp f (FI f)) (n + proj1_sig y)) (Fopp f (FI f))).
rewrite (Fmul_assoc f (PowF f (Fopp f (FI f)) (n + proj1_sig x)) (Fopp f (FI f))).
rewrite - (Fmul_assoc f (Fopp f (FI f)) (Fopp f (FI f))).
rewrite (Fmul_opp_opp f (FI f) (FI f)).
rewrite (Fmul_I_r f (FI f)).
rewrite (Fmul_I_l f (PowF f (Fopp f (FI f)) (n + proj1_sig y))).
reflexivity.
apply H6.
apply H6.
move=> u1 u2 H4 H5 H6.
elim (le_or_lt (proj1_sig u1) (proj1_sig u2)).
move=> H7.
elim (le_lt_or_eq (proj1_sig u1) (proj1_sig u2) H7).
move=> H8.
apply False_ind.
apply (lt_irrefl (proj1_sig (SkipOne (S N) u1 (exist (fun (n : nat) => n < N) (proj1_sig u1) (le_trans (S (proj1_sig u1)) (proj1_sig u2) N H8 (le_S_n (proj1_sig u2) N (proj2_sig u2))))))).
rewrite {1} H6.
rewrite (proj1 (SkipOneNature (S N) u2 (exist (fun (n : nat) => n < N) (proj1_sig u1) (le_trans (S (proj1_sig u1)) (proj1_sig u2) N H8 (le_S_n (proj1_sig u2) N (proj2_sig u2))))) H8).
rewrite (proj2 (SkipOneNature (S N) u1 (exist (fun (n : nat) => n < N) (proj1_sig u1) (le_trans (S (proj1_sig u1)) (proj1_sig u2) N H8 (le_S_n (proj1_sig u2) N (proj2_sig u2))))) (le_n (proj1_sig u1))).
apply (le_n (S (proj1_sig u1))).
apply sig_map.
move=> H7.
apply False_ind.
apply (lt_irrefl (proj1_sig (SkipOne (S N) u1 (exist (fun (n : nat) => n < N) (proj1_sig u2) (le_trans (S (proj1_sig u2)) (proj1_sig u1) N H7 (le_S_n (proj1_sig u1) N (proj2_sig u1))))))).
rewrite {2} H6.
rewrite (proj1 (SkipOneNature (S N) u1 (exist (fun (n : nat) => n < N) (proj1_sig u2) (le_trans (S (proj1_sig u2)) (proj1_sig u1) N H7 (le_S_n (proj1_sig u1) N (proj2_sig u1))))) H7).
rewrite (proj2 (SkipOneNature (S N) u2 (exist (fun (n : nat) => n < N) (proj1_sig u2) (le_trans (S (proj1_sig u2)) (proj1_sig u1) N H7 (le_S_n (proj1_sig u1) N (proj2_sig u1))))) (le_n (proj1_sig u2))).
apply (le_n (S (proj1_sig u2))).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> g.
elim.
move=> g0 H3 H4.
suff: (exists (m : {n : nat | n < S N}), forall (k : {n : nat | n < N}), g0 k <> m).
elim.
move=> m H5.
suff: (forall (p : {n : nat | n < S N}), (forall (k : {n : nat | n < N}), g0 k <> p) -> p = m).
move=> H6.
apply (Im_intro {n : nat | n < S N} ({n : nat | n < N} -> {n : nat | n < S N}) (Full_set {n : nat | n < S N}) (SkipOne (S N)) m (Full_intro {n : nat | n < S N} m)).
apply functional_extensionality.
suff: (forall (k : nat), k <= N -> forall (p : {n : nat | n < N}), proj1_sig p < k -> g0 p = SkipOne (S N) m p).
move=> H7 k.
apply (H7 N (le_n N) k (proj2_sig k)).
elim.
move=> H7 p H8.
apply False_ind.
apply (le_not_lt O (proj1_sig p) (le_0_n (proj1_sig p)) H8).
move=> n H7 H8 p H9.
elim (le_lt_or_eq (proj1_sig p) n (le_S_n (proj1_sig p) n H9)).
apply (H7 (le_trans n (S n) N (le_S n n (le_n n)) H8)).
move=> H10.
elim (le_or_lt (proj1_sig (g0 p)) (proj1_sig (SkipOne (S N) m p))).
move=> H11.
elim (le_lt_or_eq (proj1_sig (g0 p)) (proj1_sig (SkipOne (S N) m p)) H11).
move=> H12.
apply False_ind.
suff: (exists (q : {n : nat | n < N}), proj1_sig q < proj1_sig p /\ proj1_sig (g0 p) = proj1_sig (g0 q)).
elim.
move=> q H13.
apply (le_not_lt (proj1_sig (g0 p)) (proj1_sig (g0 q))).
rewrite (proj2 H13).
apply (le_n (proj1_sig (g0 q))).
apply (H3 q p (proj1 H13)).
suff: (exists (q : {n : nat | n < N}), proj1_sig (g0 p) = proj1_sig (SkipOne (S N) m q)).
elim.
move=> q H13.
exists q.
suff: (proj1_sig q < proj1_sig p).
move=> H14.
apply conj.
apply H14.
rewrite (H7 (le_trans n (S n) N (le_S n n (le_n n)) H8) q).
apply H13.
rewrite - H10.
apply H14.
elim (le_or_lt (proj1_sig p) (proj1_sig q)).
move=> H14.
apply False_ind.
apply (le_not_lt (proj1_sig (SkipOne (S N) m p)) (proj1_sig (g0 p))).
rewrite H13.
elim (le_lt_or_eq (proj1_sig p) (proj1_sig q) H14).
move=> H15.
apply (lt_le_weak (proj1_sig (SkipOne (S N) m p)) (proj1_sig (SkipOne (S N) m q)) (SkipOneMonotonicallyIncreasing (S N) m p q H15)).
move=> H15.
suff: (p = q).
move=> H16.
rewrite H16.
apply (le_n (proj1_sig (SkipOne (S N) m q))).
apply sig_map.
apply H15.
apply H12.
apply.
elim (le_or_lt (proj1_sig (g0 p)) (proj1_sig m)).
move=> H13.
elim (le_lt_or_eq (proj1_sig (g0 p)) (proj1_sig m) H13).
move=> H14.
exists (exist (fun (k : nat) => k < N) (proj1_sig (g0 p)) (le_trans (S (proj1_sig (g0 p))) (proj1_sig m) N H14 (le_S_n (proj1_sig m) N (proj2_sig m)))).
rewrite (proj1 (SkipOneNature (S N) m (exist (fun (k : nat) => k < N) (proj1_sig (g0 p)) (le_trans (S (proj1_sig (g0 p))) (proj1_sig m) N H14 (le_S_n (proj1_sig m) N (proj2_sig m))))) H14).
reflexivity.
move=> H14.
apply False_ind.
apply (H5 p).
apply sig_map.
apply H14.
move=> H13.
suff: (pred (proj1_sig (g0 p)) < N).
move=> H14.
exists (exist (fun (k : nat) => k < N) (pred (proj1_sig (g0 p))) H14).
rewrite (proj2 (SkipOneNature (S N) m (exist (fun k : nat => k < N) (pred (proj1_sig (g0 p))) H14))).
simpl.
suff: (proj1_sig m < proj1_sig (g0 p)).
elim (proj1_sig (g0 p)).
move=> H15.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H15).
move=> k H15 H16.
reflexivity.
apply H13.
simpl.
apply le_S_n.
suff: (S (pred (proj1_sig (g0 p))) = (proj1_sig (g0 p))).
move=> H15.
rewrite H15.
apply H13.
suff: (proj1_sig m < proj1_sig (g0 p)).
elim (proj1_sig (g0 p)).
move=> H15.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H15).
move=> k H15 H16.
reflexivity.
apply H13.
suff: (proj1_sig m < proj1_sig (g0 p)).
suff: (proj1_sig (g0 p) < S N).
elim (proj1_sig (g0 p)).
move=> H14 H15.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H15).
move=> k H14 H15 H16.
apply (le_S_n (S k) N H15).
apply (proj2_sig (g0 p)).
apply H13.
apply sig_map.
move=> H11.
apply False_ind.
suff: (SkipOne (S N) m p = m).
move=> H12.
elim (le_or_lt (proj1_sig m) (proj1_sig p)).
move=> H13.
apply (le_not_lt (proj1_sig (SkipOne (S N) m p)) (proj1_sig m)).
rewrite H12.
apply (le_n (proj1_sig m)).
rewrite (proj2 (SkipOneNature (S N) m p) H13).
apply (le_n_S (proj1_sig m) (proj1_sig p) H13).
move=> H13.
apply (le_not_lt (proj1_sig m) (proj1_sig p)).
rewrite - (proj1 (SkipOneNature (S N) m p) H13).
rewrite H12.
apply (le_n (proj1_sig m)).
apply H13.
apply (H6 (SkipOne (S N) m p)).
move=> k.
elim (le_or_lt (proj1_sig k) (proj1_sig p)).
move=> H12.
elim (le_lt_or_eq (proj1_sig k) (proj1_sig p) H12).
move=> H13 H14.
apply (lt_irrefl (proj1_sig (g0 k))).
rewrite {2} H14.
rewrite (H7 (le_trans n (S n) N (le_S n n (le_n n)) H8) k).
apply (SkipOneMonotonicallyIncreasing (S N) m k p H13).
rewrite - H10.
apply H13.
move=> H13.
suff: (k = p).
move=> H14.
rewrite H14.
move=> H15.
apply (le_not_lt (proj1_sig (g0 p)) (proj1_sig (SkipOne (S N) m p))).
rewrite H15.
apply (le_n (proj1_sig (SkipOne (S N) m p))).
apply H11.
apply sig_map.
apply H13.
move=> H12 H13.
apply (le_not_lt (proj1_sig (g0 k)) (proj1_sig (SkipOne (S N) m p))).
rewrite H13.
apply (le_n (proj1_sig (SkipOne (S N) m p))).
apply (lt_trans (proj1_sig (SkipOne (S N) m p)) (proj1_sig (g0 p)) (proj1_sig (g0 k)) H11).
apply (H3 p k H12).
move=> p H6.
apply NNPP.
move=> H7.
apply (lt_irrefl (S N)).
apply (incl_card_le {n : nat | n < S N} (Add {n : nat | n < S N} (Add {n : nat | n < S N} (Im {n : nat | n < N} {n : nat | n < S N} (Full_set {n : nat | n < N}) g0) p) m) (Full_set {n : nat | n < S N})).
apply (card_add {n : nat | n < S N}).
apply (card_add {n : nat | n < S N}).
suff: (forall (k : nat), k <= N -> cardinal {n : nat | n < S N} (Im {n : nat | n < N} {n : nat | n < S N} (fun (l : {n : nat | n < N}) => proj1_sig l < k) g0) k).
move=> H8.
suff: (Full_set {n : nat | n < N} = (fun (l : {n : nat | n < N}) => proj1_sig l < N)).
move=> H9.
rewrite H9.
apply (H8 N (le_n N)).
apply Extensionality_Ensembles.
apply conj.
move=> k H9.
apply (proj2_sig k).
move=> k H9.
apply (Full_intro {n : nat | n < N} k).
elim.
move=> H8.
suff: (Im {n : nat | n < N} {n : nat | n < S N} (fun (l : {n : nat | n < N}) => proj1_sig l < 0) g0 = Empty_set {n : nat | n < S N}).
move=> H9.
rewrite H9.
apply (card_empty {n : nat | n < S N}).
apply Extensionality_Ensembles.
apply conj.
move=> k.
elim.
move=> l H9.
apply False_ind.
apply (le_not_lt O (proj1_sig l) (le_0_n (proj1_sig l)) H9).
move=> k.
elim.
move=> k H8 H9.
suff: (Im {n : nat | n < N} {n : nat | n < S N} (fun (l : {n : nat | n < N}) => proj1_sig l < S k) g0 = Add {n : nat | n < S N} (Im {n : nat | n < N} {n : nat | n < S N} (fun (l : {n : nat | n < N}) => proj1_sig l < k) g0) (g0 (exist (fun (n : nat) => n < N) k H9))).
move=> H10.
rewrite H10.
apply (card_add {n : nat | n < S N}).
apply (H8 (le_trans k (S k) N (le_S k k (le_n k)) H9)).
move=> H11.
suff: (exists (l : {n : nat | n < N}), proj1_sig l < k /\ g0 l = g0 (exist (fun (n : nat) => n < N) k H9)).
elim.
move=> l H12.
apply (le_not_lt k (proj1_sig l)).
suff: (l = (exist (fun n : nat => n < N) k H9)).
move=> H13.
rewrite H13.
apply (le_n k).
apply sig_map.
elim (le_or_lt (proj1_sig l) k).
move=> H13.
elim (le_lt_or_eq (proj1_sig l) k H13).
move=> H14.
apply False_ind.
apply (le_not_lt (proj1_sig (g0 (exist (fun (n : nat) => n < N) k H9))) (proj1_sig (g0 l))).
rewrite (proj2 H12).
apply (le_n (proj1_sig (g0 (exist (fun (n : nat) => n < N) k H9)))).
apply (H3 l (exist (fun (n : nat) => n < N) k H9) H14).
apply.
move=> H13.
apply False_ind.
apply (le_not_lt (proj1_sig (g0 l)) (proj1_sig (g0 (exist (fun (n : nat) => n < N) k H9)))).
rewrite (proj2 H12).
apply (le_n (proj1_sig (g0 (exist (fun (n : nat) => n < N) k H9)))).
apply (H3 (exist (fun (n : nat) => n < N) k H9) l H13).
apply (proj1 H12).
elim H11.
move=> x0 H12 y0 H13.
rewrite H13.
exists x0.
apply conj.
apply H12.
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> l.
elim.
move=> x0 H10 y0 H11.
elim (le_lt_or_eq (proj1_sig x0) k (le_S_n (proj1_sig x0) k H10)).
move=> H12.
left.
apply (Im_intro {n : nat | n < N} {n : nat | n < S N} (fun (t : {n : nat | n < N}) => proj1_sig t < k) g0 x0 H12 y0 H11).
move=> H12.
right.
rewrite H11.
suff: (exist (fun (n : nat) => n < N) k H9 = x0).
move=> H13.
rewrite H13.
apply (In_singleton {n : nat | n < S N} (g0 x0)).
apply sig_map.
rewrite H12.
reflexivity.
move=> l.
elim.
move=> s.
elim.
move=> t H10 z H11.
apply (Im_intro {n : nat | n < N} {n : nat | n < S N} (fun (l : {n : nat | n < N}) => proj1_sig l < S k) g0 t (le_trans (S (proj1_sig t)) k (S k) H10 (le_S k k (le_n k))) z H11).
move=> s.
elim.
apply (Im_intro {n : nat | n < N} {n : nat | n < S N} (fun (l : {n : nat | n < N}) => proj1_sig l < S k) g0 (exist (fun (n : nat) => n < N) k H9)).
apply (le_n (S k)).
reflexivity.
move=> H8.
suff: (forall (k : {n : nat | n < N}), g0 k <> p).
elim H8.
move=> t H9 s H10 H11.
apply (H11 t).
rewrite H10.
reflexivity.
apply H6.
move=> H8.
suff: (forall (k : {n : nat | n < N}), g0 k <> m).
suff: (p <> m).
elim H8.
move=> t.
elim.
move=> s H9 z H10 H11 H12.
apply (H12 s).
rewrite H10.
reflexivity.
move=> z.
elim.
move=> H9.
apply False_ind.
apply H9.
reflexivity.
apply H7.
apply H5.
suff: (Full_set {n : nat | n < S N} = (fun (k : {n : nat | n < S N}) => proj1_sig k < S N)).
move=> H8.
rewrite H8.
suff: (forall (l : nat), l <= S N -> cardinal {n : nat | n < S N} (fun (k : {n : nat | n < S N}) => proj1_sig k < l) l).
move=> H9.
apply (H9 (S N) (le_n (S N))).
elim.
move=> H9.
suff: ((fun (k : {n : nat | n < S N}) => proj1_sig k < 0) = Empty_set {n : nat | n < S N}).
move=> H10.
rewrite H10.
apply (card_empty {n : nat | n < S N}).
apply Extensionality_Ensembles.
apply conj.
move=> k H10.
apply False_ind.
apply (le_not_lt O (proj1_sig k) (le_0_n (proj1_sig k)) H10).
move=> k.
elim.
move=> l H9 H10.
suff: ((fun (k : {n : nat | n < S N}) => proj1_sig k < S l) = Add {n : nat | n < S N} (fun (k : {n : nat | n < S N}) => proj1_sig k < l) (exist (fun (n : nat) => n < S N) l H10)).
move=> H11.
rewrite H11.
apply (card_add {n : nat | n < S N}).
apply (H9 (le_trans l (S l) (S N) (le_S l l (le_n l)) H10)).
apply (lt_irrefl l).
apply Extensionality_Ensembles.
apply conj.
move=> k H11.
elim (le_lt_or_eq (proj1_sig k) l (le_S_n (proj1_sig k) l H11)).
move=> H12.
left.
apply H12.
move=> H12.
right.
suff: (exist (fun (n : nat) => n < S N) l H10 = k).
move=> H13.
rewrite H13.
apply (In_singleton {n : nat | n < S N} k).
apply sig_map.
rewrite H12.
reflexivity.
move=> s.
elim.
move=> t H11.
apply (le_trans (S (proj1_sig t)) l (S l) H11 (le_S l l (le_n l))).
move=> t.
elim.
apply (le_n (S l)).
apply Extensionality_Ensembles.
apply conj.
move=> k H8.
apply (proj2_sig k).
move=> k H8.
apply (Full_intro {n : nat | n < S N} k).
move=> k H8.
apply (Full_intro {n : nat | n < S N} k).
apply NNPP.
move=> H5.
apply (lt_irrefl N).
apply (incl_card_le {n : nat | n < S N} (Full_set {n : nat | n < S N}) (fun (m : {n : nat | n < S N}) => ~ (forall k : {n : nat | n < N}, g0 k <> m))).
suff: (Full_set {n : nat | n < S N} = (fun (k : {n : nat | n < S N}) => proj1_sig k < S N)).
move=> H6.
rewrite H6.
suff: (forall (l : nat), l <= S N -> cardinal {n : nat | n < S N} (fun (k : {n : nat | n < S N}) => proj1_sig k < l) l).
move=> H7.
apply (H7 (S N) (le_n (S N))).
elim.
move=> H7.
suff: ((fun (k : {n : nat | n < S N}) => proj1_sig k < 0) = Empty_set {n : nat | n < S N}).
move=> H8.
rewrite H8.
apply (card_empty {n : nat | n < S N}).
apply Extensionality_Ensembles.
apply conj.
move=> k H8.
apply False_ind.
apply (le_not_lt O (proj1_sig k) (le_0_n (proj1_sig k)) H8).
move=> k.
elim.
move=> l H7 H8.
suff: ((fun (k : {n : nat | n < S N}) => proj1_sig k < S l) = Add {n : nat | n < S N} (fun (k : {n : nat | n < S N}) => proj1_sig k < l) (exist (fun (n : nat) => n < S N) l H8)).
move=> H9.
rewrite H9.
apply (card_add {n : nat | n < S N}).
apply (H7 (le_trans l (S l) (S N) (le_S l l (le_n l)) H8)).
apply (lt_irrefl l).
apply Extensionality_Ensembles.
apply conj.
move=> k H9.
elim (le_lt_or_eq (proj1_sig k) l (le_S_n (proj1_sig k) l H9)).
move=> H10.
left.
apply H10.
move=> H10.
right.
suff: (exist (fun (n : nat) => n < S N) l H8 = k).
move=> H11.
rewrite H11.
apply (In_singleton {n : nat | n < S N} k).
apply sig_map.
rewrite H10.
reflexivity.
move=> q.
elim.
move=> s H9.
apply (le_trans (S (proj1_sig s)) l (S l) H9 (le_S l l (le_n l))).
move=> s.
elim.
apply (le_n (S l)).
apply Extensionality_Ensembles.
apply conj.
move=> k H6.
apply (proj2_sig k).
move=> k H6.
apply (Full_intro {n : nat | n < S N} k).
suff: ((fun (m : {n : nat | n < S N}) => ~ (forall k : {n : nat | n < N}, g0 k <> m)) = Im {n : nat | n < N} {n : nat | n < S N} (fun (l : {n : nat | n < N}) => proj1_sig l < N) g0).
move=> H6.
rewrite H6.
suff: (forall (k : nat), k <= N -> cardinal {n : nat | n < S N} (Im {n : nat | n < N} {n : nat | n < S N} (fun (l : {n : nat | n < N}) => proj1_sig l < k) g0) k).
move=> H7.
apply (H7 N (le_n N)).
elim.
move=> H7.
suff: (Im {n : nat | n < N} {n : nat | n < S N} (fun (l : {n : nat | n < N}) => proj1_sig l < 0) g0 = Empty_set {n : nat | n < S N}).
move=> H8.
rewrite H8.
apply (card_empty {n : nat | n < S N}).
apply Extensionality_Ensembles.
apply conj.
move=> k.
elim.
move=> l H8.
apply False_ind.
apply (le_not_lt O (proj1_sig l) (le_0_n (proj1_sig l)) H8).
move=> k.
elim.
move=> k H7 H8.
suff: (Im {n : nat | n < N} {n : nat | n < S N} (fun (l : {n : nat | n < N}) => proj1_sig l < S k) g0 = Add {n : nat | n < S N} (Im {n : nat | n < N} {n : nat | n < S N} (fun (l : {n : nat | n < N}) => proj1_sig l < k) g0) (g0 (exist (fun (n : nat) => n < N) k H8))).
move=> H9.
rewrite H9.
apply (card_add {n : nat | n < S N}).
apply (H7 (le_trans k (S k) N (le_S k k (le_n k)) H8)).
move=> H10.
suff: (exists (l : {n : nat | n < N}), proj1_sig l < k /\ g0 l = g0 (exist (fun (n : nat) => n < N) k H8)).
elim.
move=> l H11.
apply (le_not_lt k (proj1_sig l)).
suff: (l = (exist (fun n : nat => n < N) k H8)).
move=> H12.
rewrite H12.
apply (le_n k).
apply sig_map.
elim (le_or_lt (proj1_sig l) k).
move=> H12.
elim (le_lt_or_eq (proj1_sig l) k H12).
move=> H13.
apply False_ind.
apply (le_not_lt (proj1_sig (g0 (exist (fun (n : nat) => n < N) k H8))) (proj1_sig (g0 l))).
rewrite (proj2 H11).
apply (le_n (proj1_sig (g0 (exist (fun (n : nat) => n < N) k H8)))).
apply (H3 l (exist (fun (n : nat) => n < N) k H8) H13).
apply.
move=> H12.
apply False_ind.
apply (le_not_lt (proj1_sig (g0 l)) (proj1_sig (g0 (exist (fun (n : nat) => n < N) k H8)))).
rewrite (proj2 H11).
apply (le_n (proj1_sig (g0 (exist (fun (n : nat) => n < N) k H8)))).
apply (H3 (exist (fun (n : nat) => n < N) k H8) l H12).
apply (proj1 H11).
elim H10.
move=> x0 H11 y0 H12.
rewrite H12.
exists x0.
apply conj.
apply H11.
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> l.
elim.
move=> x0 H9 y0 H10.
elim (le_lt_or_eq (proj1_sig x0) k (le_S_n (proj1_sig x0) k H9)).
move=> H11.
left.
apply (Im_intro {n : nat | n < N} {n : nat | n < S N} (fun (t : {n : nat | n < N}) => proj1_sig t < k) g0 x0 H11 y0 H10).
move=> H11.
right.
rewrite H10.
suff: (exist (fun (n : nat) => n < N) k H8 = x0).
move=> H12.
rewrite H12.
apply (In_singleton {n : nat | n < S N} (g0 x0)).
apply sig_map.
rewrite H11.
reflexivity.
move=> q.
elim.
move=> l.
elim.
move=> s H9 z H10.
apply (Im_intro {n : nat | n < N} {n : nat | n < S N} (fun (l : {n : nat | n < N}) => proj1_sig l < S k) g0 s (le_trans (S (proj1_sig s)) k (S k) H9 (le_S k k (le_n k))) z H10).
move=> s.
elim.
apply (Im_intro {n : nat | n < N} {n : nat | n < S N} (fun (l : {n : nat | n < N}) => proj1_sig l < S k) g0 (exist (fun (n : nat) => n < N) k H8)).
apply (le_n (S k)).
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> m H6.
suff: (exists (k : {n : nat | n < N}), g0 k = m).
elim.
move=> l H7.
apply (Im_intro {n : nat | n < N} {n : nat | n < S N} (fun (s : {n : nat | n < N}) => proj1_sig s < N) g0 l (proj2_sig l) m).
rewrite H7.
reflexivity.
apply NNPP.
move=> H7.
apply H6.
move=> k H8.
apply H7.
exists k.
apply H8.
move=> k.
elim.
move=> s H6 t H7 H8.
apply (H8 s).
rewrite H7.
reflexivity.
move=> t H6 H7.
apply H5.
exists t.
apply H7.
move=> g.
elim.
move=> m H3 z H4.
rewrite H4.
apply (Intersection_intro ({n : nat | n < N} -> {n : nat | n < S N})).
unfold In.
apply (SkipOneMonotonicallyIncreasing (S N) m).
apply (Full_intro ({n : nat | n < N} -> {n : nat | n < S N}) (SkipOne (S N) m)).
reflexivity.
Qed.

Definition RegularMatrix (f : Field) (N : nat) (A : Matrix f N N) := Determinant f N A <> FO f.

Lemma RegularMatrixChain : forall (f : Field) (N : nat) (A B : Matrix f N N), RegularMatrix f N A -> RegularMatrix f N B -> RegularMatrix f N (Mmult f N N N A B).
Proof.
move=> f N A B.
unfold RegularMatrix.
rewrite (DeterminantMult f N A B).
apply (Fmul_integral_contrapositive_currified f (Determinant f N A) (Determinant f N B)).
Qed.

Definition InvMatrix (f : Field) (N : nat) (A : Matrix f N N) := VMmult f N N (Finv f (Determinant f N A)) (CofactorMatrix f N A).

Lemma InvMatrixMultR : forall (f : Field) (N : nat) (A : Matrix f N N), RegularMatrix f N A -> Mmult f N N N A (InvMatrix f N A) = MI f N.
Proof.
move=> f N A H1.
unfold InvMatrix.
rewrite (VMmult_assoc_r f N N N (Finv f (Determinant f N A)) A (CofactorMatrix f N A)).
rewrite (CofactorMultR f N A).
rewrite - (VMmult_assoc f N N (Finv f (Determinant f N A)) (Determinant f N A) (MI f N)).
rewrite (Finv_l f (Determinant f N A) H1).
apply (VMmult_I_l f N N (MI f N)).
Qed.

Lemma InvMatrixMultL : forall (f : Field) (N : nat) (A : Matrix f N N), RegularMatrix f N A -> Mmult f N N N (InvMatrix f N A) A = MI f N.
Proof.
move=> f N A H1.
unfold InvMatrix.
rewrite (VMmult_assoc_l f N N N (Finv f (Determinant f N A)) (CofactorMatrix f N A) A).
rewrite (CofactorMultL f N A).
rewrite - (VMmult_assoc f N N (Finv f (Determinant f N A)) (Determinant f N A) (MI f N)).
rewrite (Finv_l f (Determinant f N A) H1).
apply (VMmult_I_l f N N (MI f N)).
Qed.

Lemma InvMatrixMultUniqueR : forall (f : Field) (N : nat) (A : Matrix f N N), RegularMatrix f N A -> forall (B : Matrix f N N), Mmult f N N N A B = MI f N -> B = InvMatrix f N A.
Proof.
move=> f N A H1 B H2.
rewrite - (Mmult_I_l f N N B).
rewrite - (InvMatrixMultL f N A H1).
rewrite (Mmult_assoc f N N N N (InvMatrix f N A) A B).
rewrite H2.
apply (Mmult_I_r f N N (InvMatrix f N A)).
Qed.

Lemma InvMatrixMultUniqueL : forall (f : Field) (N : nat) (A : Matrix f N N), RegularMatrix f N A -> forall (B : Matrix f N N), Mmult f N N N B A = MI f N -> B = InvMatrix f N A.
Proof.
move=> f N A H1 B H2.
rewrite - (Mmult_I_r f N N B).
rewrite - (InvMatrixMultR f N A H1).
rewrite - (Mmult_assoc f N N N N B A (InvMatrix f N A)).
rewrite H2.
apply (Mmult_I_l f N N (InvMatrix f N A)).
Qed.

Lemma InvMatrixMult : forall (f : Field) (N : nat) (A B : Matrix f N N), RegularMatrix f N A -> RegularMatrix f N B -> InvMatrix f N (Mmult f N N N A B) = Mmult f N N N (InvMatrix f N B) (InvMatrix f N A).
Proof.
move=> f N A B H1 H2.
suff: (Determinant f N (Mmult f N N N A B) <> FO f).
move=> H3.
rewrite (InvMatrixMultUniqueL f N (Mmult f N N N A B) H3 (Mmult f N N N (InvMatrix f N B) (InvMatrix f N A))).
reflexivity.
rewrite (Mmult_assoc f N N N N (InvMatrix f N B) (InvMatrix f N A) (Mmult f N N N A B)).
rewrite - (Mmult_assoc f N N N N (InvMatrix f N A) A B).
rewrite (InvMatrixMultL f N A H1).
rewrite (Mmult_I_l f N N B).
apply (InvMatrixMultL f N B H2).
apply (RegularMatrixChain f N A B H1 H2).
Qed.

Lemma RegularInvRExistRelation : forall (f : Field) (N : nat) (A : Matrix f N N), RegularMatrix f N A <-> exists (B : Matrix f N N), Mmult f N N N A B = MI f N.
Proof.
move=> f N A.
apply conj.
move=> H1.
exists (InvMatrix f N A).
apply (InvMatrixMultR f N A H1).
elim.
move=> B H1 H2.
apply (FI_neq_FO f).
rewrite - (DeterminantI f N).
rewrite - H1.
rewrite (DeterminantMult f N A B).
rewrite H2.
apply (Fmul_O_l f (Determinant f N B)).
Qed.

Lemma RegularInvLExistRelation : forall (f : Field) (N : nat) (A : Matrix f N N), RegularMatrix f N A <-> exists (B : Matrix f N N), Mmult f N N N B A = MI f N.
Proof.
move=> f N A.
apply conj.
move=> H1.
exists (InvMatrix f N A).
apply (InvMatrixMultL f N A H1).
elim.
move=> B H1 H2.
apply (FI_neq_FO f).
rewrite - (DeterminantI f N).
rewrite - H1.
rewrite (DeterminantMult f N B A).
rewrite H2.
apply (Fmul_O_r f (Determinant f N B)).
Qed.

Lemma RegularInvBothExistRelation : forall (f : Field) (N : nat) (A : Matrix f N N), RegularMatrix f N A <-> exists (B : Matrix f N N), Mmult f N N N A B = MI f N /\ Mmult f N N N B A = MI f N.
Proof.
move=> f N A.
apply conj.
move=> H1.
exists (InvMatrix f N A).
apply conj.
apply (InvMatrixMultR f N A H1).
apply (InvMatrixMultL f N A H1).
elim.
move=> B H1.
apply (proj2 (RegularInvLExistRelation f N A)).
exists B.
apply (proj2 H1).
Qed.

Lemma RegularZeroDivisorBothExistRelation : forall (f : Field) (N : nat) (A : Matrix f N N), (~ RegularMatrix f N A) <-> exists (B : Matrix f N N), B <> MO f N N /\ Mmult f N N N A B = MO f N N /\ Mmult f N N N B A = MO f N N.
Proof.
move=> f N A.
apply conj.
move=> H1.
elim (min_nat_get (fun (d : nat) => ~ LinearlyIndependentVS f (MVS f N N) (Count d) (fun (m : Count d) => PowM f N A (proj1_sig m)))).
move=> d H2.
suff: (exists (a : Count d -> FT f), MySumF2 (Count d) (exist (Finite (Count d)) (Full_set (Count d)) (CountFinite d)) (VSPCM f (MVS f N N)) (fun n : Count d => Vmul f (MVS f N N) (a n) (PowM f N A (proj1_sig n))) = VO f (MVS f N N) /\ exists (m : Count d), a m <> FO f).
elim.
simpl.
move=> a H3.
suff: (O < d).
move=> H4.
suff: (a (exist (fun (k : nat) => k < d) O H4) = FO f).
move=> H5.
suff: (forall (m : Count (pred d)), S (proj1_sig m) < d).
move=> H6.
suff: (forall (b : Count (pred d) -> FT f), Mmult f N N N A (MySumF2 (Count (pred d)) (exist (Finite (Count (pred d))) (Full_set (Count (pred d))) (CountFinite (pred d))) (VSPCM f (MVS f N N)) (fun (n : Count (pred d)) => Vmul f (MVS f N N) (b n) (PowM f N A (proj1_sig n)))) = Mmult f N N N (MySumF2 (Count (pred d)) (exist (Finite (Count (pred d))) (Full_set (Count (pred d))) (CountFinite (pred d))) (VSPCM f (MVS f N N)) (fun (n : Count (pred d)) => Vmul f (MVS f N N) (b n) (PowM f N A (proj1_sig n)))) A).
move=> H7.
exists (MySumF2 (Count (pred d)) (exist (Finite (Count (pred d))) (Full_set (Count (pred d))) (CountFinite (pred d))) (VSPCM f (MVS f N N)) (fun (n : Count (pred d)) => Vmul f (MVS f N N) (a (exist (fun (k : nat) => k < d) (S (proj1_sig n)) (H6 n))) (PowM f N A (proj1_sig n)))).
apply conj.
move=> H8.
suff: (LinearlyIndependentVS f (MVS f N N) (Count (pred d)) (fun (m : Count (pred d)) => PowM f N A (proj1_sig m))).
move=> H9.
elim (proj2 H3).
move=> m H10.
suff: (forall (k : nat), proj1_sig m = k -> a m = FO f).
move=> H11.
apply H10.
apply (H11 (proj1_sig m)).
reflexivity.
elim.
move=> H11.
rewrite - H5.
suff: (m = (exist (fun k : nat => k < d) 0 H4)).
move=> H12.
rewrite H12.
reflexivity.
apply sig_map.
apply H11.
move=> n H11 H12.
suff: (n < pred d).
move=> H13.
suff: (m = (exist (fun (k : nat) => k < d) (S (proj1_sig (exist (fun (k : nat) => k < pred d) n H13))) (H6 (exist (fun (k : nat) => k < pred d) n H13)))).
move=> H14.
rewrite H14.
apply (proj1 (FiniteLinearlyIndependentVS f (MVS f N N) (pred d) (fun (m : Count (pred d)) => PowM f N A (proj1_sig m))) H9 (fun (n : Count (pred d)) => (a (exist (fun k : nat => k < d) (S (proj1_sig n)) (H6 n)))) H8 (exist (fun (k : nat) => k < pred d) n H13)).
apply sig_map.
apply H12.
suff: (proj1_sig m < d).
rewrite H12.
suff: (0 < d).
elim d.
move=> H13.
apply False_ind.
apply (lt_irrefl O H13).
move=> l H13 H14.
apply (lt_S_n n l).
apply H4.
apply (proj2_sig m).
apply NNPP.
move=> H9.
apply (lt_irrefl (pred d)).
suff: (0 < d).
suff: (d <= pred d).
elim d.
move=> H10 H11.
apply False_ind.
apply (lt_irrefl O H11).
move=> n H10 H11 H12.
apply H11.
apply (proj2 H2 (pred d) H9).
apply H4.
suff: (Mmult f N N N (MySumF2 (Count (pred d)) (exist (Finite (Count (pred d))) (Full_set (Count (pred d))) (CountFinite (pred d))) (VSPCM f (MVS f N N)) (fun n : Count (pred d) => Vmul f (MVS f N N) (a (exist (fun k : nat => k < d) (S (proj1_sig n)) (H6 n))) (PowM f N A (proj1_sig n)))) A = MO f N N).
move=> H8.
apply conj.
rewrite H7.
apply H8.
apply H8.
rewrite - (proj1 H3).
rewrite (MySumF2Included (Count d) (FiniteSingleton (Count d) (exist (fun (k : nat) => k < d) 0 H4)) (exist (Finite (Count d)) (Full_set (Count d)) (CountFinite d)) ).
rewrite MySumF2Singleton.
rewrite H5.
simpl.
suff: (VMmult f N N (FO f) (MI f N) = MO f N N).
move=> H8.
rewrite H8.
rewrite (Mplus_O_l f N N).
suff: ((FiniteIntersection (Count d) (exist (Finite (Count d)) (Full_set (Count d)) (CountFinite d)) (Complement (Count d) (Singleton (Count d) (exist (fun (k : nat) => k < d) 0 H4)))) = (FiniteIm (Count (pred d)) (Count d) (fun (n : Count (pred d)) => exist (fun k : nat => k < d) (S (proj1_sig n)) (H6 n)) (exist (Finite (Count (pred d))) (Full_set (Count (pred d))) (CountFinite (pred d))))).
move=> H9.
rewrite H9.
rewrite - (MySumF2BijectiveSame2 (Count (pred d)) (Count d) (exist (Finite (Count (pred d))) (Full_set (Count (pred d))) (CountFinite (pred d))) (fun (n : Count (pred d)) => exist (fun (k : nat) => k < d) (S (proj1_sig n)) (H6 n)) (VSPCM f (MVS f N N))).
apply (FiniteSetInduction (Count (pred d)) (exist (Finite (Count (pred d))) (Full_set (Count (pred d))) (CountFinite (pred d)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
unfold MO.
apply MySumF2Induction.
apply conj.
reflexivity.
move=> cm u H10 H11.
rewrite H11.
rewrite (Fmul_O_l f (A u y)).
apply (Fadd_O_r f (FO f)).
move=> B b H10 H11 H12 H13.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite - H13.
rewrite (Mmult_plus_distr_r f N N N).
unfold Basics.compose.
simpl.
rewrite (VMmult_assoc_l f N N N (a (exist (fun k : nat => k < d) (S (proj1_sig b)) (H6 b)))).
reflexivity.
apply H12.
apply H12.
move=> u1 u2 H10 H11 H12.
apply sig_map.
apply (eq_add_S (proj1_sig u1) (proj1_sig u2)).
suff: (S (proj1_sig u1) = proj1_sig (exist (fun (k : nat) => k < d) (S (proj1_sig u1)) (H6 u1))).
move=> H13.
rewrite H13.
rewrite H12.
reflexivity.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> m.
elim.
move=> m0 H9 H10.
suff: (pred (proj1_sig m0) < pred d).
move=> H11.
apply (Im_intro (Count (pred d)) (Count d) (Full_set (Count (pred d))) (fun (n : Count (pred d)) => exist (fun (k : nat) => k < d) (S (proj1_sig n)) (H6 n)) (exist (fun (k : nat) => k < pred d) (pred (proj1_sig m0)) H11)).
apply (Full_intro (Count (pred d))).
apply sig_map.
simpl.
suff: (proj1_sig m0 <> O).
elim (proj1_sig m0).
move=> H12.
apply False_ind.
apply H12.
reflexivity.
move=> n H12 H13.
reflexivity.
move=> H12.
apply H9.
suff: (m0 = (exist (fun (k : nat) => k < d) 0 H4)).
move=> H13.
rewrite H13.
apply (In_singleton (Count d) (exist (fun (k : nat) => k < d) 0 H4)).
apply sig_map.
apply H12.
suff: (proj1_sig m0 < d).
suff: (proj1_sig m0 <> 0).
suff: (0 < d).
elim (proj1_sig m0).
move=> H11 H12.
apply False_ind.
apply H12.
reflexivity.
move=> n1 H11.
elim d.
move=> H12.
apply False_ind.
apply (lt_irrefl O H12).
move=> n2 H12 H13 H14.
apply (lt_S_n n1 n2).
apply H4.
move=> H11.
apply H9.
suff: (m0 = (exist (fun (k : nat) => k < d) 0 H4)).
move=> H12.
rewrite H12.
apply (In_singleton (Count d) (exist (fun (k : nat) => k < d) 0 H4)).
apply sig_map.
apply H11.
apply (proj2_sig m0).
move=> m.
elim.
move=> x H9 y H10.
apply Intersection_intro.
move=> H11.
suff: (match (proj1_sig y) with
  | O => True
  | S _ => False
end).
rewrite H10.
apply.
elim H11.
apply I.
apply (Full_intro (Count d)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply (Fmul_O_l f (MI f N x y)).
move=> v H8.
apply (Full_intro (Count d) v).
move=> b.
apply (FiniteSetInduction (Count (pred d)) (exist (Finite (Count (pred d))) (Full_set (Count (pred d))) (CountFinite (pred d)))).
apply conj.
rewrite MySumF2Empty.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
simpl.
apply (MySumF2Same {n : nat | n < N} (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N)) (FPCM f)).
move=> u H7.
rewrite (Fmul_O_l f (A u y)).
apply (Fmul_O_r f (A x u)).
move=> C c H7 H8 H9 H10.
rewrite MySumF2Add.
rewrite (Mmult_plus_distr_r f N N N).
rewrite (Mmult_plus_distr_l f N N N).
rewrite H10.
rewrite (VMmult_assoc_r f N N).
rewrite (VMmult_assoc_l f N N).
suff: (Mmult f N N N A (PowM f N A (proj1_sig c)) = Mmult f N N N (PowM f N A (proj1_sig c)) A).
move=> H11.
rewrite H11.
reflexivity.
suff: (Mmult f N N N (PowM f N A (S O)) (PowM f N A (proj1_sig c)) = Mmult f N N N (PowM f N A (proj1_sig c)) (PowM f N A (S O))).
simpl.
rewrite (Mmult_I_l f N N A).
apply.
rewrite - (PowMplus f N A (S O) (proj1_sig c)).
rewrite - (PowMplus f N A (proj1_sig c) (S O)).
rewrite (plus_comm (S O) (proj1_sig c)).
reflexivity.
apply H9.
move=> m.
suff: (proj1_sig m < pred d).
elim (proj1_sig m).
elim d.
move=> H6.
apply False_ind.
apply (lt_irrefl O H6).
move=> n H6.
apply (lt_n_S O n).
move=> n H6.
suff: (O < d).
elim d.
move=> H7.
apply False_ind.
apply (lt_irrefl O H7).
move=> k H7 H8.
apply (lt_n_S (S n) k).
apply H4.
apply (proj2_sig m).
apply NNPP.
move=> H5.
apply H1.
apply (proj2 (RegularInvLExistRelation f N A)).
suff: (exists (B : Matrix f N N), Mplus f N N (Mmult f N N N B A) (VMmult f N N (a (exist (fun (k : nat) => k < d) 0 H4)) (MI f N)) = MO f N N).
elim.
move=> B H6.
exists (VMmult f N N (Fopp f (Finv f (a (exist (fun (k : nat) => k < d) 0 H4)))) B).
rewrite (VMmult_assoc_l f N N N (Fopp f (Finv f (a (exist (fun (k : nat) => k < d) 0 H4)))) B).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold VMmult.
apply (Fmul_eq_reg_l f (a (exist (fun (k : nat) => k < d) 0 H4))).
rewrite - (Fmul_assoc f).
rewrite (Fopp_mul_distr_r_reverse f (a (exist (fun (k : nat) => k < d) 0 H4))).
rewrite (Finv_r f (a (exist (fun (k : nat) => k < d) 0 H4)) H5).
apply (Fminus_diag_uniq_sym f).
rewrite (Fopp_mul_distr_l_reverse f).
rewrite (Fmul_I_l f).
rewrite (Fopp_involutive f).
rewrite (Fadd_comm f).
suff: (Fadd f (Mmult f N N N B A x y) (Fmul f (a (exist (fun (k : nat) => k < d) 0 H4)) (MI f N x y)) = Mplus f N N (Mmult f N N N B A) (VMmult f N N (a (exist (fun (k : nat) => k < d) 0 H4)) (MI f N)) x y).
move=> H7.
rewrite H7.
rewrite H6.
reflexivity.
reflexivity.
apply H5.
exists (MySumF2 (Count d) (FiniteIntersection (Count d) (exist (Finite (Count d)) (Full_set (Count d)) (CountFinite d)) (Complement (Count d) (Singleton (Count d) (exist (fun (k : nat) => k < d) 0 H4)))) (VSPCM f (MVS f N N)) (fun (n : Count d) => VMmult f N N (a n) (PowM f N A (pred (proj1_sig n))))).
rewrite - (proj1 H3).
rewrite (MySumF2Included (Count d) (FiniteSingleton (Count d) (exist (fun (k : nat) => k < d) 0 H4)) (exist (Finite (Count d)) (Full_set (Count d)) (CountFinite d))).
rewrite (CM_comm (VSPCM f (MVS f N N))).
rewrite MySumF2Singleton.
suff: (Mmult f N N N (MySumF2 (Count d) (FiniteIntersection (Count d) (exist (Finite (Count d)) (Full_set (Count d)) (CountFinite d)) (Complement (Count d) (Singleton (Count d) (exist (fun (k : nat) => k < d) 0 H4)))) (VSPCM f (MVS f N N)) (fun (n : Count d) => VMmult f N N (a n) (PowM f N A (Init.Nat.pred (proj1_sig n))))) A = MySumF2 (Count d) (FiniteIntersection (Count d) (exist (Finite (Count d)) (Full_set (Count d)) (CountFinite d)) (Complement (Count d) (proj1_sig (FiniteSingleton (Count d) (exist (fun (k : nat) => k < d) 0 H4))))) (VSPCM f (MVS f N N)) (fun (n : Count d) => VMmult f N N (a n) (PowM f N A (proj1_sig n)))).
move=> H6.
rewrite H6.
reflexivity.
simpl.
apply (FiniteSetInduction (Count d) (FiniteIntersection (Count d) (exist (Finite (Count d)) (Full_set (Count d)) (CountFinite d)) (Complement (Count d) (Singleton (Count d) (exist (fun (k : nat) => k < d) 0 H4))))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
simpl.
apply MySumF2Induction.
apply conj.
reflexivity.
move=> cm u H6 H7.
rewrite H7.
rewrite (Fmul_O_l f (A u y)).
apply (Fadd_O_r f (FO f)).
move=> B b H6 H7 H8 H9.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Mmult_plus_distr_r f N N N).
rewrite H9.
rewrite (VMmult_assoc_l f N N N (a b)).
suff: (proj1_sig b = S (pred (proj1_sig b))).
move=> H10.
rewrite {2} H10.
reflexivity.
suff: (proj1_sig b <> O).
elim (proj1_sig b).
move=> H10.
apply False_ind.
apply H10.
reflexivity.
move=> n H10 H11.
reflexivity.
elim H7.
move=> c H10 H11 H12.
apply H10.
suff: (c = exist (fun (k : nat) => k < d) 0 H4).
move=> H13.
rewrite H13.
apply (In_singleton (Count d) (exist (fun (k : nat) => k < d) 0 H4)).
apply sig_map.
apply H12.
apply H8.
apply H8.
move=> m H6.
apply (Full_intro (Count d) m).
apply NNPP.
move=> H4.
suff: (0 = d).
move=> H5.
apply (proj1 H2).
apply (proj2 (FiniteLinearlyIndependentVS f (MVS f N N) d (fun (m : Count d) => PowM f N A (proj1_sig m)))).
move=> b H6 m.
apply False_ind.
apply (le_not_lt O (proj1_sig m) (le_O_n (proj1_sig m))).
rewrite H5.
apply (proj2_sig m).
elim (le_lt_or_eq O d (le_O_n d)).
move=> H5.
elim (H4 H5).
apply.
apply NNPP.
move=> H3.
apply (proj1 H2).
apply (proj2 (FiniteLinearlyIndependentVS f (MVS f N N) d (fun (m : Count d) => PowM f N A (proj1_sig m)))).
move=> a H4 m.
apply NNPP.
move=> H5.
apply H3.
exists a.
apply conj.
apply H4.
exists m.
apply H5.
suff: (FiniteDimensionVS f (MVS f N N)).
move=> H2.
apply (Inhabited_intro nat (fun (d : nat) => ~ LinearlyIndependentVS f (MVS f N N) (Count d) (fun m : Count d => PowM f N A (proj1_sig m))) (S (DimensionVS f (MVS f N N) H2))).
move=> H3.
apply (lt_irrefl (DimensionVS f (MVS f N N) H2)).
apply (Corollary_5_7_3 f (MVS f N N) (S (DimensionVS f (MVS f N N) H2)) (fun (m : Count (S (DimensionVS f (MVS f N N) H2))) => PowM f N A (proj1_sig m)) H2 H3).
elim (CountMult N N).
move=> F.
elim.
move=> G H2.
apply (Corollary_5_7_1 f (MVS f N N) (N * N) (fun (m : Count (N * N)) (x y : Count N) => match excluded_middle_informative (x = fst (G m)), excluded_middle_informative (y = snd (G m)) with
  | left _, left _ => FI f
  | left _, right _ => FO f
  | right _, left _ => FO f
  | right _, right _ => FO f
end)).
apply Extensionality_Ensembles.
apply conj.
move=> B H3.
rewrite (FiniteSpanVS f (MVS f N N) (N * N) (fun (m : Count (N * N)) (x y : Count N) => match excluded_middle_informative (x = fst (G m)), excluded_middle_informative (y = snd (G m)) with
  | left _, left _ => FI f
  | left _, right _ => FO f
  | right _, left _ => FO f
  | right _, right _ => FO f
end)).
exists (fun (m : Count (N * N)) => B (fst (G m)) (snd (G m))).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite (MySumF2Included (Count (N * N)) (FiniteSingleton (Count (N * N)) (F (x, y))) (exist (Finite (Count (N * N))) (Full_set (Count (N * N))) (CountFinite (N * N)))).
rewrite MySumF2Singleton.
simpl.
unfold Mplus.
unfold VMmult.
rewrite (proj1 H2 (x, y)).
simpl.
elim (excluded_middle_informative (@eq (Count N) x x)).
move=> H4.
elim (excluded_middle_informative (@eq (Count N) y y)).
move=> H5.
rewrite (Fmul_I_r f (B x y)).
rewrite - {1} (Fadd_O_r f (B x y)).
apply (Fadd_eq_compat_l f).
apply (FiniteSetInduction (Count (N * N)) (FiniteIntersection (Count (N * N)) (exist (Finite (Count (N * N))) (Full_set (Count (N * N))) (CountFinite (N * N))) (Complement (Count (N * N)) (Singleton (Count (N * N)) (F (x, y)))))).
apply conj.
rewrite MySumF2Empty.
reflexivity.
move=> C c H6 H7 H8 H9.
rewrite MySumF2Add.
simpl.
unfold Mplus.
rewrite - H9.
elim (excluded_middle_informative (@eq (Count N) x (@fst (@sig nat (fun (n : nat) => lt n N)) (@sig nat (fun (n : nat) => lt n N)) (G c)))).
move=> H10.
elim (excluded_middle_informative (@eq (Count N) y (@snd (@sig nat (fun (n : nat) => lt n N)) (@sig nat (fun (n : nat) => lt n N)) (G c)))).
move=> H11.
apply False_ind.
suff: (x = fst (G c)).
suff: (y = snd (G c)).
elim H7.
move=> d H12 H13 H14 H15.
apply H12.
suff: (d = F (x, y)).
move=> H16.
rewrite H16.
apply (In_singleton (Count (N * N)) (F (x, y))).
apply (BijInj {n : nat | n < N * N} ({n : nat | n < N} * {n : nat | n < N}) G).
exists F.
apply conj.
apply (proj2 H2).
apply (proj1 H2).
rewrite (proj1 H2 (x, y)).
apply injective_projections.
rewrite H15.
reflexivity.
rewrite H14.
reflexivity.
apply H11.
apply H10.
move=> H11.
rewrite (Fmul_O_r f (B (fst (G c)) (snd (G c)))).
rewrite (Fadd_O_r f (FO f)).
reflexivity.
move=> H10.
elim (excluded_middle_informative (@eq (Count N) y (@snd (@sig nat (fun (n : nat) => lt n N)) (@sig nat (fun (n : nat) => lt n N)) (G c)))).
move=> H11.
rewrite (Fmul_O_r f (B (fst (G c)) (snd (G c)))).
rewrite (Fadd_O_r f (FO f)).
reflexivity.
move=> H11.
rewrite (Fmul_O_r f (B (fst (G c)) (snd (G c)))).
rewrite (Fadd_O_r f (FO f)).
reflexivity.
apply H8.
move=> H5.
apply False_ind.
apply H5.
reflexivity.
move=> H4.
apply False_ind.
apply H4.
reflexivity.
move=> m H4.
apply (Full_intro (Count (N * N)) m).
move=> m H3.
apply (Full_intro (Matrix f N N) m).
elim.
move=> B H1 H2.
apply (proj1 H1).
rewrite - (Mmult_I_l f N N B).
rewrite - (InvMatrixMultL f N A H2).
rewrite (Mmult_assoc f N N N N (InvMatrix f N A) A B).
rewrite (proj1 (proj2 H1)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
apply MySumF2Induction.
apply conj.
reflexivity.
move=> cm u H3 H4.
rewrite H4.
rewrite (Fmul_O_r f (InvMatrix f N A x u)).
apply (CM_O_r (FPCM f) (MO f N N x y)).
Qed.

Lemma InvMatrixMultUniqueRStrong : forall (f : Field) (N : nat) (A : Matrix f N N) (B : Matrix f N N), Mmult f N N N A B = MI f N -> B = InvMatrix f N A.
Proof.
move=> f N A B H2.
apply (InvMatrixMultUniqueR f N A).
apply (proj2 (RegularInvRExistRelation f N A)).
exists B.
apply H2.
apply H2.
Qed.

Lemma InvMatrixMultUniqueLStrong : forall (f : Field) (N : nat) (A : Matrix f N N) (B : Matrix f N N), Mmult f N N N B A = MI f N -> B = InvMatrix f N A.
Proof.
move=> f N A B H2.
apply (InvMatrixMultUniqueL f N A).
apply (proj2 (RegularInvLExistRelation f N A)).
exists B.
apply H2.
apply H2.
Qed.

Lemma MmultILRSame : forall (f : Field) (N : nat) (A B : Matrix f N N), Mmult f N N N A B = MI f N <-> Mmult f N N N B A = MI f N .
Proof.
suff: (forall (f : Field) (N : nat) (A B : Matrix f N N), Mmult f N N N A B = MI f N -> Mmult f N N N B A = MI f N).
move=> H1 f N A B.
apply conj.
apply (H1 f N A B).
apply (H1 f N B A).
move=> f N A B H1.
suff: (B = InvMatrix f N A).
move=> H2.
rewrite H2.
apply (InvMatrixMultL f N A).
apply (proj2 (RegularInvRExistRelation f N A)).
exists B.
apply H1.
apply (InvMatrixMultUniqueRStrong f N A B H1).
Qed.

Lemma DeterminantElementaryMatrixAdd : forall (f : Field) (N : nat) (p q : {n : nat | n < N}) (c : FT f), proj1_sig p <> proj1_sig q -> Determinant f N (ElementaryMatrixAdd f N p q c) = FI f.
Proof.
move=> f N p q c H1.
rewrite - (Mmult_I_r f N N (ElementaryMatrixAdd f N p q c)).
rewrite (ElementaryMatrixAddNatureL f N N (MI f N) p q c H1).
rewrite (DeterminantAddTransformH f N (MI f N) q p c).
apply (DeterminantI f N).
move=> H2.
apply H1.
rewrite H2.
reflexivity.
Qed.

Lemma DeterminantElementaryMatrixMultiply : forall (f : Field) (N : nat) (p : {n : nat | n < N}) (c : FT f), Determinant f N (ElementaryMatrixMultiply f N p c) = c.
Proof.
move=> f N p c.
rewrite - (Mmult_I_r f N N (ElementaryMatrixMultiply f N p c)).
rewrite (ElementaryMatrixMultiplyNatureL f N N (MI f N) p c).
rewrite (DeterminantMultiLinearityHMult f N (MI f N) p c).
rewrite (DeterminantI f N).
apply (Fmul_I_r f c).
Qed.

Lemma DeterminantElementaryMatrixSwap : forall (f : Field) (N : nat) (p q : {n : nat | n < N}), proj1_sig p <> proj1_sig q -> Determinant f N (ElementaryMatrixSwap f N p q) = Fopp f (FI f).
Proof.
move=> f N p q H1.
rewrite - (Mmult_I_r f N N (ElementaryMatrixSwap f N p q)).
rewrite (ElementaryMatrixSwapNatureL f N N (MI f N) p q).
rewrite (DeterminantSwapH f N (MI f N) p q).
rewrite (DeterminantI f N).
reflexivity.
apply H1.
Qed.

Lemma ElementaryMatrixRegular : forall (f : Field) (N : nat) (A : Matrix f N N), ElementaryMatrix f N A -> RegularMatrix f N A.
Proof.
move=> f N A.
elim.
move=> p q c H1 H2.
unfold RegularMatrix.
rewrite (DeterminantElementaryMatrixAdd f N p q c H1).
apply (FI_neq_FO f).
move=> p c.
unfold RegularMatrix.
rewrite (DeterminantElementaryMatrixMultiply f N p c).
apply.
move=> p q H1.
unfold RegularMatrix.
rewrite (DeterminantElementaryMatrixSwap f N p q H1).
apply (Fopp_neq_O_compat f (FI f) (FI_neq_FO f)).
Qed.

Lemma InvMatrixElementaryMatrixAdd : forall (f : Field) (N : nat) (p q : {n : nat | n < N}) (c : FT f), proj1_sig p <> proj1_sig q -> InvMatrix f N (ElementaryMatrixAdd f N p q c) = ElementaryMatrixAdd f N p q (Fopp f c).
Proof.
move=> f N p q c H1.
rewrite (InvMatrixMultUniqueLStrong f N (ElementaryMatrixAdd f N p q c) (ElementaryMatrixAdd f N p q (Fopp f c))).
reflexivity.
rewrite (ElementaryMatrixAddNatureL f N N (ElementaryMatrixAdd f N p q c) p q (Fopp f c)).
unfold ElementaryMatrixAdd.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
move=> H2.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H3.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig y)).
move=> H4.
apply False_ind.
apply H1.
rewrite - H2.
rewrite H3.
rewrite H4.
reflexivity.
move=> H4.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig p)).
move=> H5.
apply False_ind.
apply H1.
rewrite H5.
reflexivity.
move=> H5.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig q)).
move=> H6.
rewrite (Fmul_O_r f (Fopp f c)).
apply (Fadd_O_r f (FI f)).
move=> H6.
rewrite (Fmul_O_r f (Fopp f c)).
apply (Fadd_O_r f (FI f)).
move=> H3.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig q)).
move=> H4.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig y)).
move=> H5.
rewrite (Fmul_I_r f (Fopp f c)).
apply (Fadd_opp_r f c).
move=> H5.
apply False_ind.
apply H5.
rewrite H4.
reflexivity.
move=> H4.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig y)).
move=> H5.
apply False_ind.
apply H4.
rewrite H5.
reflexivity.
move=> H5.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig p)).
move=> H6.
apply False_ind.
apply H1.
rewrite H6.
reflexivity.
move=> H6.
rewrite (Fmul_O_r f (Fopp f c)).
apply (Fadd_O_l f (FO f)).
move=> H2.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H3.
reflexivity.
move=> H3.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig q)).
move=> H4.
reflexivity.
move=> H4.
reflexivity.
apply H1.
Qed.

Lemma InvMatrixElementaryMatrixMultiply : forall (f : Field) (N : nat) (p : {n : nat | n < N}) (c : FT f), c <> FO f -> InvMatrix f N (ElementaryMatrixMultiply f N p c) = ElementaryMatrixMultiply f N p (Finv f c).
Proof.
move=> f N p c H1.
rewrite (InvMatrixMultUniqueLStrong f N (ElementaryMatrixMultiply f N p c) (ElementaryMatrixMultiply f N p (Finv f c))).
reflexivity.
rewrite (ElementaryMatrixMultiplyNatureL f N N (ElementaryMatrixMultiply f N p c) p (Finv f c)).
unfold ElementaryMatrixMultiply.
unfold MI.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H2.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
move=> H3.
apply (Finv_l f c H1).
move=> H3.
reflexivity.
move=> H2.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
move=> H3.
apply (Fmul_O_r f (Finv f c)).
move=> H3.
reflexivity.
Qed.

Lemma InvMatrixElementaryMatrixSwap : forall (f : Field) (N : nat) (p q : {n : nat | n < N}), InvMatrix f N (ElementaryMatrixSwap f N p q) = ElementaryMatrixSwap f N p q.
Proof.
move=> f N p q.
rewrite - (InvMatrixMultUniqueLStrong f N (ElementaryMatrixSwap f N p q) (ElementaryMatrixSwap f N p q)).
reflexivity.
rewrite (ElementaryMatrixSwapNatureL f N N (ElementaryMatrixSwap f N p q) p q).
unfold ElementaryMatrixSwap.
unfold MI.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H1.
rewrite H1.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig p)).
move=> H2.
rewrite H2.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig p)).
move=> H3.
reflexivity.
move=> H3.
reflexivity.
move=> H2.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig p)).
move=> H3.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig q)).
move=> H4.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig q)).
move=> H5.
reflexivity.
move=> H5.
apply False_ind.
apply H5.
reflexivity.
move=> H4.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig q)).
move=> H5.
reflexivity.
move=> H5.
apply False_ind.
apply H5.
reflexivity.
move=> H3.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig q)).
move=> H4.
elim (Nat.eq_dec (proj1_sig p) (proj1_sig p)).
move=> H5.
reflexivity.
move=> H5.
apply False_ind.
apply H5.
reflexivity.
move=> H4.
reflexivity.
move=> H1.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig p)).
move=> H2.
rewrite H2.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
move=> H3.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig p)).
move=> H4.
apply False_ind.
apply H1.
rewrite H4.
apply H3.
move=> H4.
reflexivity.
move=> H3.
reflexivity.
move=> H2.
elim (Nat.eq_dec (proj1_sig p) (proj1_sig q)).
move=> H3.
apply False_ind.
apply H2.
rewrite H3.
reflexivity.
move=> H3.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig p)).
move=> H4.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig q)).
move=> H5.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig p)).
move=> H6.
apply False_ind.
apply H1.
rewrite H6.
apply H4.
move=> H6.
reflexivity.
move=> H5.
apply False_ind.
apply H5.
reflexivity.
move=> H4.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig q)).
move=> H5.
elim (Nat.eq_dec (proj1_sig p) (proj1_sig p)).
move=> H6.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig q)).
move=> H7.
apply False_ind.
apply H1.
rewrite H7.
apply H5.
move=> H7.
reflexivity.
move=> H6.
apply False_ind.
apply H6.
reflexivity.
move=> H5.
reflexivity.
Qed.

Lemma ReverseMatrixInvolutive : forall (f : Field) (N : nat), Mmult f N N N (ReverseMatrix f N) (ReverseMatrix f N) = MI f N.
Proof.
move=> f N.
unfold Mmult.
unfold MI.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H1.
rewrite (MySumF2Included {n : nat | n < N} (FiniteSingleton {n : nat | n < N} (CountReverse N x))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
unfold ReverseMatrix.
rewrite (CountReverseInvolutive N x).
suff: (x = y).
move=> H2.
rewrite H2.
unfold MI.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig y)).
move=> H3.
elim (Nat.eq_dec (proj1_sig (CountReverse N y)) (proj1_sig (CountReverse N y))).
move=> H4.
rewrite (Fmul_I_l f (FI f)).
apply (CM_O_r (FPCM f) (FI f)).
elim.
reflexivity.
elim.
reflexivity.
apply sig_map.
apply H1.
move=> u.
elim.
move=> u0 H2 H3.
unfold ReverseMatrix.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (CountReverse N u0))).
move=> H4.
elim H2.
suff: (u0 = CountReverse N x).
move=> H5.
rewrite H5.
apply (In_singleton {n : nat | n < N} (CountReverse N x)).
suff: (x = CountReverse N u0).
move=> H5.
rewrite H5.
rewrite (CountReverseInvolutive N u0).
reflexivity.
apply sig_map.
apply H4.
move=> H4.
apply (Fmul_O_l f).
move=> u H2.
apply (Full_intro {n : nat | n < N} u).
move=> H1.
apply MySumF2O.
move=> u H2.
unfold ReverseMatrix.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (CountReverse N u))).
move=> H3.
elim (Nat.eq_dec (proj1_sig u) (proj1_sig (CountReverse N y))).
move=> H4.
elim H1.
rewrite H3.
suff: (u = CountReverse N y).
move=> H5.
rewrite H5.
rewrite (CountReverseInvolutive N y).
reflexivity.
apply sig_map.
apply H4.
move=> H4.
apply (Fmul_O_r f (FI f)).
move=> H3.
apply (Fmul_O_l f).
Qed.

Lemma InvMatrixReverseMatrix : forall (f : Field) (N : nat), InvMatrix f N (ReverseMatrix f N) = ReverseMatrix f N.
Proof.
move=> f N.
rewrite - (InvMatrixMultUniqueLStrong f N (ReverseMatrix f N) (ReverseMatrix f N)).
reflexivity.
apply (ReverseMatrixInvolutive f N).
Qed.

Lemma MDiagReverseRelation : forall (f : Field) (N : nat) (d : Count N -> FT f), Mmult f N N N (Mmult f N N N (ReverseMatrix f N) (MDiag f N d)) (ReverseMatrix f N) = MDiag f N (fun (m : Count N) => d (CountReverse N m)).
Proof.
move=> f N d.
rewrite (ReverseMatrixNatureL f N N (MDiag f N d)).
rewrite (ReverseMatrixNatureR f N N).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig (CountReverse N x)) (proj1_sig (CountReverse N y))).
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H2.
reflexivity.
elim.
rewrite - (CountReverseInvolutive N x).
suff: (CountReverse N x = CountReverse N y).
move=> H2.
rewrite H2.
rewrite (CountReverseInvolutive N y).
reflexivity.
apply sig_map.
apply H1.
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H2.
elim H1.
suff: (x = y).
move=> H3.
rewrite H3.
reflexivity.
apply sig_map.
apply H2.
move=> H2.
reflexivity.
Qed.

Definition Rank (f : Field) (M N : nat) (A : Matrix f M N) := DimensionSubspaceVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A) (Proposition_5_9_1_1 f (FnVS f N) (FnVSFiniteDimension f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)).

Lemma RankDef2 : forall (f : Field) (M N : nat) (A : Matrix f M N) (r : nat), Rank f M N A = r <-> is_max_nat (fun (k : nat) => exists (x : {n : nat | n < k} -> {n : nat | n < M}), LinearlyIndependentVS f (FnVS f N) {n : nat | n < k} (fun (m : {n : nat | n < k}) => A (x m))) r.
Proof.
move=> f M N A r.
apply conj.
move=> H1.
apply conj.
elim (proj2 (CountFiniteBijective {m : Count M | ~ In (VT f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A))) (SpanVS f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) {n : Count M | proj1_sig n < proj1_sig m} (fun k : {n : Count M | proj1_sig n < proj1_sig m} => exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A (proj1_sig k)) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A (proj1_sig k)))) (exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A m) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A m))})).
move=> s.
elim.
move=> g H2.
suff: (r = s).
move=> H3.
rewrite H3.
exists (fun (k : {n : nat | n < s}) => proj1_sig (g k)).
apply (SubspaceBasisLinearlyIndependentVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A) {n : nat | n < s} (fun (m : {n : nat | n < s}) => A (proj1_sig (g m)))).
exists (fun (m : {n : nat | n < s}) => SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A (proj1_sig (g m))).
apply (BijectiveSaveBasisVS f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) {n : nat | n < s} {m : Count M | ~ In (VT f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A))) (SpanVS f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) {n : Count M | proj1_sig n < proj1_sig m} (fun k : {n : Count M | proj1_sig n < proj1_sig m} => exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A (proj1_sig k)) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A (proj1_sig k)))) (exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A m) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A m))} g (fun (t : {m : Count M | ~ In (VT f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A))) (SpanVS f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) {n : Count M | proj1_sig n < proj1_sig m} (fun k : {n : Count M | proj1_sig n < proj1_sig m} => exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A (proj1_sig k)) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A (proj1_sig k)))) (exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A m) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A m))}) => exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A (proj1_sig t)) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A (proj1_sig t))) H2).
apply (Theorem_5_6_sub f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) M (fun (k : {n : nat | n < M}) => exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A k) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A k))).
apply Extensionality_Ensembles.
apply conj.
move=> v H4.
elim (proj2_sig v).
move=> x H5.
exists x.
apply sig_map.
rewrite H5.
unfold Count.
apply (FiniteSetInduction {n : nat | n < M} (exist (Finite {n : nat | n < M}) (fun (t : {n : nat | n < M}) => proj1_sig x t <> FO f) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H6 H7 H8 H9.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H9.
reflexivity.
apply H8.
apply H8.
move=> v H4.
apply Full_intro.
rewrite - H1.
apply (DimensionVSNature2 f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) (Proposition_5_9_1_1 f (FnVS f N) (FnVSFiniteDimension f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) s (fun (t : {n : nat | n < s}) => exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A (proj1_sig (g t))) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A (proj1_sig (g t))))).
apply (BijectiveSaveBasisVS f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) {n : nat | n < s} {m : Count M | ~ In (VT f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A))) (SpanVS f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) {n : Count M | proj1_sig n < proj1_sig m} (fun k : {n : Count M | proj1_sig n < proj1_sig m} => exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A (proj1_sig k)) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A (proj1_sig k)))) (exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A m) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A m))} g (fun (t : {m : Count M | ~ In (VT f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A))) (SpanVS f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) {n : Count M | proj1_sig n < proj1_sig m} (fun k : {n : Count M | proj1_sig n < proj1_sig m} => exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A (proj1_sig k)) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A (proj1_sig k)))) (exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A m) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A m))}) => exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A (proj1_sig t)) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A (proj1_sig t))) H2).
apply (Theorem_5_6_sub f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) M (fun (k : {n : nat | n < M}) => exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A k) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A k))).
apply Extensionality_Ensembles.
apply conj.
move=> v H4.
elim (proj2_sig v).
move=> x H5.
exists x.
apply sig_map.
rewrite H5.
unfold Count.
apply (FiniteSetInduction {n : nat | n < M} (exist (Finite {n : nat | n < M}) (fun (t : {n : nat | n < M}) => proj1_sig x t <> FO f) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H6 H7 H8 H9.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H9.
reflexivity.
apply H8.
apply H8.
move=> v H4.
apply Full_intro.
apply (FiniteSigSame (Count M)).
apply (Finite_downward_closed (Count M) (Full_set (Count M)) (CountFinite M)).
move=> m H2.
apply (Full_intro (Count M) m).
move=> s.
elim.
move=> g.
rewrite - H1.
move=> H2.
apply (Corollary_5_7_3 f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) s (fun (m : (Count s)) => exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A (g m)) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A (g m)))).
apply (FiniteLinearlyIndependentVS f).
move=> x H3.
apply (FiniteLinearlyIndependentVS f (FnVS f N) s (fun m : {n : nat | n < s} => A (g m))).
apply H2.
suff: (VO f (FnVS f N) = proj1_sig (VO f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)))).
move=> H4.
rewrite H4.
rewrite - H3.
apply (FiniteSetInduction (Count s) (exist (Finite (Count s)) (Full_set (Count s)) (CountFinite s))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H5 H6 H7 H8.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H8.
reflexivity.
apply H7.
apply H7.
reflexivity.
move=> H1.
elim (proj1 H1).
move=> g H2.
apply (DimensionVSNature2 f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) (Proposition_5_9_1_1 f (FnVS f N) (FnVSFiniteDimension f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) r (fun (t : {n : nat | n < r}) => exist (SpanVS f (FnVS f N) {n : nat | n < M} A) (A (g t)) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A (g t)))).
apply (BasisLIGeVS f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A))).
apply conj.
apply (FiniteLinearlyIndependentVS f).
move=> x H3.
apply (FiniteLinearlyIndependentVS f (FnVS f N) r (fun m : {n : nat | n < r} => A (g m))).
apply H2.
suff: (VO f (FnVS f N) = proj1_sig (VO f (SubspaceMakeVS f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)))).
move=> H4.
rewrite H4.
rewrite - H3.
apply (FiniteSetInduction (Count r) (exist (Finite (Count r)) (Full_set (Count r)) (CountFinite r))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H5 H6 H7 H8.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H8.
reflexivity.
apply H7.
apply H7.
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> v H3.
suff: (In (Fn f N) (SpanVS f (FnVS f N) {n : nat | n < r} (fun (t : {n : nat | n < r}) => A (g t))) (proj1_sig v)).
elim.
move=> x H4.
exists x.
apply sig_map.
rewrite H4.
unfold Count.
apply (FiniteSetInduction {n : nat | n < r} (exist (Finite {n : nat | n < r}) (fun (t : {n : nat | n < r}) => proj1_sig x t <> FO f) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H5 H6 H7 H8.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H8.
reflexivity.
apply H7.
apply H7.
elim (proj2_sig v).
move=> x H4.
rewrite H4.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < r} (fun (t : {n : nat | n < r}) => A (g t))))).
move=> cm t H5 H6.
apply (proj1 (SpanSubspaceVS f (FnVS f N) {n : nat | n < r} (fun (t : {n : nat | n < r}) => A (g t))) cm (Vmul f (FnVS f N) (proj1_sig x t) (A t)) H6).
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < r} (fun (t : {n : nat | n < r}) => A (g t)))) (proj1_sig x t) (A t)).
apply NNPP.
move=> H7.
apply (lt_irrefl r).
apply (proj2 H1 (S r)).
exists (fun (m : Count (S r)) => match excluded_middle_informative (proj1_sig m < r) with
  | left H => g (exist (fun (k : nat) => k < r) (proj1_sig m) H)
  | right _ => t
end).
elim (Proposition_5_2_exists f (FnVS f N) r).
move=> H8.
elim.
move=> H9 H10.
apply (proj2 (H10 (fun (m : {n : nat | n < S r}) => A match excluded_middle_informative (proj1_sig m < r) with
  | left H => g (exist (fun k : nat => k < r) (proj1_sig m) H)
  | right _ => t
end))).
simpl.
suff: ((fun (m : Count r) => A match excluded_middle_informative (proj1_sig m < r) with
  | left H => g (exist (fun k : nat => k < r) (proj1_sig m) H)
  | right _ => t
end) = (fun m : {n : nat | n < r} => A (g m))).
move=> H11.
rewrite H11.
apply conj.
apply H2.
elim (excluded_middle_informative (r < r)).
move=> H12.
apply False_ind.
apply (lt_irrefl r H12).
move=> H12.
apply H7.
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (proj1_sig m < r)).
move=> H11.
suff: (exist (fun (k : nat) => k < r) (proj1_sig m) H11 = m).
move=> H12.
rewrite H12.
reflexivity.
apply sig_map.
reflexivity.
move=> H11.
elim (H11 (proj2_sig m)).
move=> v H3.
apply Full_intro.
Qed.

Lemma RankLeH : forall (f : Field) (M N : nat) (A : Matrix f M N), Rank f M N A <= M.
Proof.
move=> f M N A.
suff: (Rank f M N A = Rank f M N A).
move=> H1.
elim (proj1 (proj1 (RankDef2 f M N A (Rank f M N A)) H1)).
move=> F H2.
apply (CountInjectiveLe (Rank f M N A) M F).
move=> m1 m2 H3.
apply (LinearlyIndependentInjectiveVS f (FnVS f N) {n : nat | n < Rank f M N A} (fun (m : {n : nat | n < Rank f M N A}) => A (F m)) H2).
rewrite H3.
reflexivity.
reflexivity.
Qed.

Lemma RankLeW : forall (f : Field) (M N : nat) (A : Matrix f M N), Rank f M N A <= N.
Proof.
move=> f M N A.
elim (FnVSDimension f N).
move=> H1 H2.
rewrite - {2} H2.
apply (Proposition_5_9_1_2 f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A) H1 (Proposition_5_9_1_1 f (FnVS f N) (FnVSFiniteDimension f N) (SpanVS f (FnVS f N) {n : nat | n < M} A) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A))).
Qed.

Lemma RankMinorDeterminant : forall (f : Field) (M N : nat) (A : Matrix f M N) (r : nat), Rank f M N A = r <-> is_max_nat (fun (k : nat) => exists (hi : {n : nat | n < k} -> {n : nat | n < M}) (wi : {n : nat | n < k} -> {n : nat | n < N}), Determinant f k (fun (x y : {n : nat | n < k}) => A (hi x) (wi y)) <> FO f) r.
Proof.
suff: (forall (f : Field) (M N : nat) (A : Matrix f M N) (k : nat), (exists (hi : {n : nat | n < k} -> {n : nat | n < M}) (wi : {n : nat | n < k} -> {n : nat | n < N}), Determinant f k (fun (x y : {n : nat | n < k}) => A (hi x) (wi y)) <> FO f) -> Rank f M N A >= k).
move=> H1.
suff: (forall (f : Field) (M N : nat) (A : Matrix f M N), exists (hi : {n : nat | n < Rank f M N A} -> {n : nat | n < M}) (wi : {n : nat | n < Rank f M N A} -> {n : nat | n < N}), Determinant f (Rank f M N A) (fun (x y : {n : nat | n < Rank f M N A}) => A (hi x) (wi y)) <> FO f).
move=> H2 f M N A r.
apply conj.
move=> H3.
apply conj.
rewrite - H3.
apply (H2 f M N A).
rewrite - H3.
apply (H1 f M N A).
move=> H3.
elim (le_lt_or_eq r (Rank f M N A)).
move=> H4.
apply False_ind.
apply (le_not_lt (Rank f M N A) r (proj2 H3 (Rank f M N A) (H2 f M N A)) H4).
move=> H4.
rewrite H4.
reflexivity.
apply (H1 f M N A r (proj1 H3)).
move=> f M N A.
suff: (Rank f M N A = Rank f M N A).
move=> H2.
elim (proj1 (proj1 (RankDef2 f M N A (Rank f M N A)) H2)).
move=> hi H3.
exists hi.
suff: (exists (wi : {n : nat | n < Rank f M N A} -> {n : nat | n < N}), forall (p : {n : nat | n < N}), In (VT f (FnVS f (Rank f M N A))) (SpanVS f (FnVS f (Rank f M N A)) (Count (Rank f M N A)) (fun (k m : Count (Rank f M N A)) => A (hi m) (wi k))) (fun (m : Count (Rank f M N A)) => A (hi m) p)).
elim.
move=> wi H4.
exists wi.
move=> H5.
suff: (exists (a : Count (Rank f M N A) -> FT f), ~ (forall (m : Count (Rank f M N A)), a m = FO f) /\ forall (m : Count (Rank f M N A)), MySumF2 {n : nat | n < Rank f M N A} (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) (FPCM f) (fun (n : Count (Rank f M N A)) => Fmul f (a n) (A (hi n) (wi m))) = FO f).
elim.
move=> a H6.
apply (proj1 H6).
apply (proj1 (FiniteLinearlyIndependentVS f (FnVS f N) (Rank f M N A) (fun (m : {n : nat | n < Rank f M N A}) => A (hi m))) H3 a).
apply functional_extensionality.
move=> p.
suff: (MySumF2 (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set (Count (Rank f M N A))) (CountFinite (Rank f M N A))) (VSPCM f (FnVS f N)) (fun (n : Count (Rank f M N A)) => Vmul f (FnVS f N) (a n) (A (hi n))) p = MySumF2 {n : nat | n < Rank f M N A} (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) (FPCM f) (fun (n : Count (Rank f M N A)) => Fmul f (a n) (A (hi n) p))).
move=> H7.
rewrite H7.
suff: (exists (a : Count (Rank f M N A) -> FT f), (fun (m : Count (Rank f M N A)) => A (hi m) p) = MySumF2 (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set (Count (Rank f M N A))) (CountFinite (Rank f M N A))) (VSPCM f (FnVS f (Rank f M N A))) (fun (n : Count (Rank f M N A)) => Vmul f (FnVS f (Rank f M N A)) (a n) (fun k : Count (Rank f M N A) => A (hi k) (wi n)))).
elim.
move=> b H8.
suff: ((fun (n : Count (Rank f M N A)) => Fmul f (a n) (A (hi n) p)) = (fun (m : Count (Rank f M N A)) => MySumF2 (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set (Count (Rank f M N A))) (CountFinite (Rank f M N A))) (FPCM f) (fun (n : Count (Rank f M N A)) => Fmul f (a m) (Fmul f (b n) (A (hi m) (wi n)))))).
move=> H9.
rewrite H9.
rewrite - (MySumF2Pair (Count (Rank f M N A)) (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) (FPCM f) (fun (u v : Count (Rank f M N A)) => Fmul f (a u) (Fmul f (b v) (A (hi u) (wi v))))).
suff: (MySumF2 (Count (Rank f M N A) * Count (Rank f M N A)) (FinitePair (Count (Rank f M N A)) (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A)))) (FPCM f) (fun (uv : Count (Rank f M N A) * Count (Rank f M N A)) => Fmul f (a (fst uv)) (Fmul f (b (snd uv)) (A (hi (fst uv)) (wi (snd uv))))) = MySumF2 (Count (Rank f M N A) * Count (Rank f M N A)) (FinitePair (Count (Rank f M N A)) (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A)))) (FPCM f) (fun (uv : Count (Rank f M N A) * Count (Rank f M N A)) => Fmul f (a (snd uv)) (Fmul f (b (fst uv)) (A (hi (snd uv)) (wi (fst uv)))))).
move=> H10.
rewrite H10.
rewrite (MySumF2Pair (Count (Rank f M N A)) (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) (FPCM f) (fun (v u : Count (Rank f M N A)) => Fmul f (a u) (Fmul f (b v) (A (hi u) (wi v))))).
simpl.
apply (MySumF2O (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) (FPCM f)).
move=> u H11.
suff: (MySumF2 (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) (FPCM f) (fun u0 : Count (Rank f M N A) => Fmul f (a u0) (Fmul f (b u) (A (hi u0) (wi u)))) = Fmul f (b u) (MySumF2 (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) (FPCM f) (fun u0 : Count (Rank f M N A) => Fmul f (a u0) (A (hi u0) (wi u))))).
move=> H12.
rewrite H12.
rewrite (proj2 H6 u).
apply (Fmul_O_r f (b u)).
apply (FiniteSetInduction (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (Fmul_O_r f (b u)).
reflexivity.
move=> C c H12 H13 H14 H15.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H15.
rewrite (Fmul_add_distr_l f (b u)).
rewrite - (Fmul_assoc f (b u) (a c)).
rewrite - (Fmul_assoc f (a c) (b u)).
rewrite (Fmul_comm f (a c) (b u)).
reflexivity.
apply H14.
apply H14.
suff: (FinitePair (Count (Rank f M N A)) (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) = (FiniteIm (Count (Rank f M N A) * Count (Rank f M N A)) (Count (Rank f M N A) * Count (Rank f M N A)) (fun (uv : (Count (Rank f M N A) * Count (Rank f M N A))) => (snd uv, fst uv)) (FinitePair (Count (Rank f M N A)) (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A)))))).
move=> H10.
rewrite {2} H10.
rewrite - (MySumF2BijectiveSame2 (Count (Rank f M N A) * Count (Rank f M N A)) (Count (Rank f M N A) * Count (Rank f M N A))).
apply MySumF2Same.
move=> u H11.
reflexivity.
move=> u1 u2 H11 H12 H13.
apply injective_projections.
suff: (fst u1 = snd (snd u1, fst u1)).
move=> H14.
rewrite H14.
rewrite H13.
reflexivity.
reflexivity.
suff: (snd u1 = fst (snd u1, fst u1)).
move=> H14.
rewrite H14.
rewrite H13.
reflexivity.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u H10.
apply (Im_intro (Count (Rank f M N A) * Count (Rank f M N A)) (Count (Rank f M N A) * Count (Rank f M N A)) (proj1_sig (FinitePair (Count (Rank f M N A)) (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))) (exist (Finite (Count (Rank f M N A))) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A))))) (fun (uv : Count (Rank f M N A) * Count (Rank f M N A)) => (snd uv, fst uv)) (snd u, fst u)).
apply conj.
apply (Full_intro (Count (Rank f M N A)) (snd u)).
apply (Full_intro (Count (Rank f M N A)) (fst u)).
apply injective_projections.
reflexivity.
reflexivity.
move=> u H10.
apply conj.
apply (Full_intro (Count (Rank f M N A)) (fst u)).
apply (Full_intro (Count (Rank f M N A)) (snd u)).
apply functional_extensionality.
move=> m.
suff: (A (hi m) p = let temp := (fun (m : Count (Rank f M N A)) => A (hi m) p) in temp m).
move=> H9.
rewrite H9.
rewrite H8.
simpl.
apply (FiniteSetInduction (Count (Rank f M N A)) (exist (Finite (Count (Rank f M N A))) (Full_set (Count (Rank f M N A))) (CountFinite (Rank f M N A)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Fmul_O_r f (a m)).
move=> C c H10 H11 H12 H13.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite - H13.
apply (Fmul_add_distr_l f (a m)).
apply H12.
apply H12.
reflexivity.
suff: (In (VT f (FnVS f (Rank f M N A))) (SpanVS f (FnVS f (Rank f M N A)) (Count (Rank f M N A)) (fun (k m : Count (Rank f M N A)) => A (hi m) (wi k))) (fun (m : Count (Rank f M N A)) => A (hi m) p)).
rewrite (FiniteSpanVS f (FnVS f (Rank f M N A)) (Rank f M N A) (fun (k m : Count (Rank f M N A)) => A (hi m) (wi k))).
apply.
apply (H4 p).
unfold Count.
apply (FiniteSetInduction {n : nat | n < Rank f M N A} (exist (Finite {n : nat | n < Rank f M N A}) (Full_set {n : nat | n < Rank f M N A}) (CountFinite (Rank f M N A)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H7 H8 H9 H10.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite - H10.
reflexivity.
apply H9.
apply H9.
elim (proj1 (RegularZeroDivisorBothExistRelation f (Rank f M N A) (fun (x y : {n : nat | n < Rank f M N A}) => A (hi x) (wi y)))).
move=> B H6.
suff: (exists (k : Count (Rank f M N A)), ~ (forall (m : Count (Rank f M N A)), B k m = FO f)).
elim.
move=> k H7.
exists (B k).
apply conj.
apply H7.
move=> m.
suff: (FO f = MO f (Rank f M N A) (Rank f M N A) k m).
move=> H8.
rewrite H8.
rewrite - (proj2 (proj2 H6)).
reflexivity.
reflexivity.
apply NNPP.
move=> H7.
apply (proj1 H6).
apply functional_extensionality.
move=> h.
apply NNPP.
move=> H8.
apply H7.
exists h.
move=> H9.
apply H8.
apply functional_extensionality.
move=> w.
apply (H9 w).
move=> H6.
apply (H6 H5).
suff: (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m) <= Rank f M N A).
move=> H4.
suff: (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m) = Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m)).
move=> H5.
elim (proj1 (proj1 (RankDef2 f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m) (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m))) H5)).
move=> F H6.
suff: (exists (wi : Count (Rank f M N A) -> Count N), forall (x : Count (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m))), exists (y : Count (Rank f M N A)), wi y = F x).
elim.
move=> wi H7.
exists wi.
move=> p.
apply NNPP.
move=> H8.
apply (lt_irrefl (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m))).
apply (proj2 (proj1 (RankDef2 f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m) (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m))) H5) (S (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m)))).
elim (Proposition_5_2_exists f (FnVS f (Rank f M N A)) (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m))).
move=> H9.
elim.
move=> H10 H11.
exists (fun (x : Count (S (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m)))) => match excluded_middle_informative (proj1_sig x < Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m)) with
  | left H => (F (exist (fun (y : nat) => y < Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m)) (proj1_sig x) H))
  | right _ => p
end).
apply (proj2 (H11 (fun (m : {n : nat | n < S (Rank f N (Rank f M N A) (fun (m : {n0 : nat | n0 < N}) (k : {n0 : nat | n0 < Rank f M N A}) => A (hi k) m))}) (k : {n : nat | n < Rank f M N A}) => A (hi k) match excluded_middle_informative (proj1_sig m < Rank f N (Rank f M N A) (fun (m0 : {n : nat | n < N}) (k0 : {n : nat | n < Rank f M N A}) => A (hi k0) m0)) with
  | left H => F (exist (fun y : nat => y < Rank f N (Rank f M N A) (fun (m0 : {n : nat | n < N}) (k0 : {n : nat | n < Rank f M N A}) => A (hi k0) m0)) (proj1_sig m) H)
  | right _ => p
end))).
apply conj.
simpl.
suff: ((fun (m : Count (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m))) (k : {n : nat | n < Rank f M N A}) => A (hi k) match excluded_middle_informative (proj1_sig m < Rank f N (Rank f M N A) (fun (m0 : {n : nat | n < N}) (k0 : {n : nat | n < Rank f M N A}) => A (hi k0) m0)) with
  | left H => F (exist (fun y : nat => y < Rank f N (Rank f M N A) (fun (m0 : {n : nat | n < N}) (k0 : {n : nat | n < Rank f M N A}) => A (hi k0) m0)) (proj1_sig m) H)
  | right _ => p
end) = (fun (m : {n : nat | n < Rank f N (Rank f M N A) (fun (m : {n0 : nat | n0 < N}) (k : {n0 : nat | n0 < Rank f M N A}) => A (hi k) m)}) (k : {n : nat | n < Rank f M N A}) => A (hi k) (F m))).
move=> H12.
rewrite H12.
apply H6.
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (proj1_sig m < Rank f N (Rank f M N A) (fun (m0 : {n : nat | n < N}) (k0 : {n : nat | n < Rank f M N A}) => A (hi k0) m0))).
move=> H12.
suff: ((exist (fun y : nat => y < Rank f N (Rank f M N A) (fun (m0 : {n : nat | n < N}) (k0 : {n : nat | n < Rank f M N A}) => A (hi k0) m0)) (proj1_sig m) H12) = m).
move=> H13.
rewrite H13.
reflexivity.
apply sig_map.
reflexivity.
move=> H12.
elim (H12 (proj2_sig m)).
simpl.
elim (excluded_middle_informative (Rank f N (Rank f M N A) (fun (m0 : {n : nat | n < N}) (k0 : {n : nat | n < Rank f M N A}) => A (hi k0) m0) < Rank f N (Rank f M N A) (fun (m0 : {n : nat | n < N}) (k0 : {n : nat | n < Rank f M N A}) => A (hi k0) m0))).
move=> H12.
elim (lt_irrefl (Rank f N (Rank f M N A) (fun (m0 : {n : nat | n < N}) (k0 : {n : nat | n < Rank f M N A}) => A (hi k0) m0)) H12).
move=> H12.
suff: ((fun (m : Count (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m))) (k : {n : nat | n < Rank f M N A}) => A (hi k) match excluded_middle_informative (proj1_sig m < Rank f N (Rank f M N A) (fun (m0 : {n : nat | n < N}) (k0 : {n : nat | n < Rank f M N A}) => A (hi k0) m0)) with
  | left H => F (exist (fun y : nat => y < Rank f N (Rank f M N A) (fun (m0 : {n : nat | n < N}) (k0 : {n : nat | n < Rank f M N A}) => A (hi k0) m0)) (proj1_sig m) H)
  | right _ => p
end) = (fun (m : Count (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m))) (k : {n : nat | n < Rank f M N A}) => A (hi k) (F m))).
move=> H13.
rewrite H13.
rewrite (FiniteSpanVS f (FnVS f (Rank f M N A)) (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m))).
move=> H14.
apply H8.
elim H14.
move=> a H15.
rewrite H15.
apply (FiniteSetInduction (Count (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m))) (exist (Finite (Count (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m)))) (Full_set (Count (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m)))) (CountFinite (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m))))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS f (FnVS f (Rank f M N A)) (Count (Rank f M N A)) (fun (k m : Count (Rank f M N A)) => A (hi m) (wi k))))).
move=> B b H16 H17 H18 H19.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS f (FnVS f (Rank f M N A)) (Count (Rank f M N A)) (fun (k m : Count (Rank f M N A)) => A (hi m) (wi k)))).
apply H19.
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f (Rank f M N A)) (Count (Rank f M N A)) (fun (k m : Count (Rank f M N A)) => A (hi m) (wi k)))) (a b)).
elim (H7 b).
move=> d H20.
rewrite - H20.
apply (SpanContainSelfVS f (FnVS f (Rank f M N A)) (Count (Rank f M N A)) (fun (k m : Count (Rank f M N A)) => A (hi m) (wi k))).
apply H18.
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (proj1_sig m < Rank f N (Rank f M N A) (fun (m0 : {n : nat | n < N}) (k0 : {n : nat | n < Rank f M N A}) => A (hi k0) m0))).
move=> H13.
suff: ((exist (fun (y : nat) => y < Rank f N (Rank f M N A) (fun (m0 : {n : nat | n < N}) (k0 : {n : nat | n < Rank f M N A}) => A (hi k0) m0)) (proj1_sig m) H13) = m).
move=> H14.
rewrite H14.
reflexivity.
apply sig_map.
reflexivity.
move=> H13.
elim (H13 (proj2_sig m)).
elim (le_lt_or_eq O N (le_O_n N)).
move=> H7.
exists (fun (m : Count (Rank f M N A)) => match excluded_middle_informative (proj1_sig m < Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m)) with
  | left H => F (exist (fun (n : nat) => n < Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m)) (proj1_sig m) H)
  | right _ => exist (fun (n : nat) => n < N) O H7
end).
move=> x.
exists (exist (fun (n : nat) => n < Rank f M N A) (proj1_sig x) (le_trans (S (proj1_sig x)) (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m)) (Rank f M N A) (proj2_sig x) H4)).
simpl.
elim (excluded_middle_informative (proj1_sig x < Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m))).
move=> H8.
suff: ((exist (fun (n : nat) => n < Rank f N (Rank f M N A) (fun (m : {n0 : nat | n0 < N}) (k : {n0 : nat | n0 < Rank f M N A}) => A (hi k) m)) (proj1_sig x) H8) = x).
move=> H9.
rewrite H9.
reflexivity.
apply sig_map.
reflexivity.
move=> H8.
elim (H8 (proj2_sig x)).
move=> H7.
suff: (Rank f M N A = O).
move=> H8.
suff: (Count (Rank f M N A) -> False).
move=> H9.
exists (fun (m : Count (Rank f M N A)) => match (H9 m) with
end).
move=> x.
elim (H9 (exist (fun (n : nat) => n < Rank f M N A) (proj1_sig x) (le_trans (S (proj1_sig x)) (Rank f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m)) (Rank f M N A) (proj2_sig x) H4))).
rewrite H8.
move=> m.
apply (lt_irrefl O (le_trans (S O) (S (proj1_sig m)) O (le_n_S O (proj1_sig m) (le_O_n (proj1_sig m))) (proj2_sig m))).
elim (le_lt_or_eq (Rank f M N A) N).
rewrite - {2} H7.
move=> H8.
elim (le_not_lt O (Rank f M N A) (le_O_n (Rank f M N A)) H8).
move=> H8.
rewrite H8.
rewrite H7.
reflexivity.
apply (RankLeW f M N A).
reflexivity.
apply (RankLeW f N (Rank f M N A) (fun (m : {n : nat | n < N}) (k : {n : nat | n < Rank f M N A}) => A (hi k) m)).
reflexivity.
move=> f M N A k.
elim.
move=> hi.
elim.
move=> wi H1.
suff: (Rank f M N A = Rank f M N A).
move=> H2.
apply (proj2 (proj1 (RankDef2 f M N A (Rank f M N A)) H2) k).
exists hi.
apply (proj2 (FiniteLinearlyIndependentVS f (FnVS f N) k (fun (m : {n : nat | n < k}) => A (hi m)))).
move=> a H3.
suff: (forall (m : {n : nat | n < k}), MySumF2 (Count k) (exist (Finite (Count k)) (Full_set (Count k)) (CountFinite k)) (FPCM f) (fun (n : Count k) => Fmul f (a n) (A (hi n) (wi m))) = FO f).
move=> H4.
suff: (Mmult f 1 k k (fun (_ : Count 1) (n : Count k) => a n) (fun (m n : Count k) => A (hi m) (wi n)) = MO f 1 k).
move=> H5.
suff: ((fun (_ : Count 1) (n : Count k) => a n) = MO f 1 k).
move=> H6 m.
suff: (FO f = MO f 1 k (exist (fun (n : nat) => n < 1) O (le_n 1)) m).
move=> H7.
rewrite H7.
rewrite - H6.
reflexivity.
reflexivity.
rewrite - (Mmult_I_r f 1 k (fun (_ : Count 1) (n : Count k) => a n)).
rewrite - (InvMatrixMultR f k (fun (m n : Count k) => A (hi m) (wi n))).
rewrite - (Mmult_assoc f 1 k k k).
rewrite H5.
apply (Mmult_O_l f 1 k k).
apply H1.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
apply H4.
move=> m.
suff: (FO f = VO f (FnVS f N) (wi m)).
move=> H4.
rewrite H4.
rewrite - H3.
apply (FiniteSetInduction (Count k) (exist (Finite (Count k)) (Full_set (Count k)) (CountFinite k))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H5 H6 H7 H8.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H8.
reflexivity.
apply H7.
apply H7.
reflexivity.
reflexivity.
Qed.

Lemma RankTrans : forall (f : Field) (M N : nat) (A : Matrix f M N), Rank f N M (MTranspose f M N A) = Rank f M N A.
Proof.
move=> f M N A.
apply (proj2 (RankMinorDeterminant f N M (MTranspose f M N A) (Rank f M N A))).
suff: (is_max_nat (fun k : nat => exists (hi : {n : nat | n < k} -> {n : nat | n < M}) (wi : {n : nat | n < k} -> {n : nat | n < N}), Determinant f k (fun x y : {n : nat | n < k} => A (hi x) (wi y)) <> FO f) (Rank f M N A)).
move=> H1.
suff: ((fun (k : nat) => exists (hi : {n : nat | n < k} -> {n : nat | n < N}) (wi : {n : nat | n < k} -> {n : nat | n < M}), Determinant f k (fun x y : {n : nat | n < k} => MTranspose f M N A (hi x) (wi y)) <> FO f) = (fun (k : nat) => exists (hi : {n : nat | n < k} -> {n : nat | n < M}) (wi : {n : nat | n < k} -> {n : nat | n < N}), Determinant f k (fun x y : {n : nat | n < k} => A (hi x) (wi y)) <> FO f)).
move=> H2.
rewrite H2.
apply H1.
apply Extensionality_Ensembles.
apply conj.
move=> r.
elim.
move=> hi.
elim.
move=> wi.
rewrite (DeterminantTrans f r (fun (x y : {n : nat | n < r}) => A (wi x) (hi y))).
move=> H2.
exists wi.
exists hi.
apply H2.
move=> r.
elim.
move=> hi.
elim.
move=> wi H2.
exists wi.
exists hi.
rewrite (DeterminantTrans f r (fun (x y : {n : nat | n < r}) => A (hi x) (wi y))).
apply H2.
apply (proj1 (RankMinorDeterminant f M N A (Rank f M N A))).
reflexivity.
Qed.

Lemma RankAddTransformH : forall (f : Field) (M N : nat) (A : Matrix f M N) (p q : {n : nat | n < M}) (c : FT f), proj1_sig p <> proj1_sig q -> Rank f M N (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
  | left _ => Fadd f (A x y) (Fmul f c (A p y))
  | right _ => A x y
end) = Rank f M N A.
Proof.
move=> f M N A p q c H1.
suff: (forall (W1 W2 : Ensemble (Fn f N)), W1 = W2 -> forall (H1 : SubspaceVS f (FnVS f N) W1) (H2 : SubspaceVS f (FnVS f N) W2) (H3 : FiniteDimensionVS f (SubspaceMakeVS f (FnVS f N) W1 H1)) (H4 : FiniteDimensionVS f (SubspaceMakeVS f (FnVS f N) W2 H2)), DimensionSubspaceVS f (FnVS f N) W1 H1 H3 = DimensionSubspaceVS f (FnVS f N) W2 H2 H4).
move=> H2.
apply H2.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> x H3.
rewrite H3.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A))).
move=> cm u H4 H5.
apply (proj1 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)).
apply H5.
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) (proj1_sig x u)).
unfold In.
elim (Nat.eq_dec (proj1_sig u) (proj1_sig q)).
move=> H6.
apply (proj1 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A) (A u) (Fnmul f N c (A p))).
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A u).
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) c (A p) (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A p)).
move=> H6.
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A u).
move=> v.
elim.
move=> x H3.
rewrite H3.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end)))).
move=> cm u H4 H5.
elim (classic (proj1_sig u = proj1_sig q)).
move=> H6.
suff: (A u = Fnminus f N ((fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end) u) (Fnmul f N c (A p))).
move=> H7.
rewrite H7.
apply (proj1 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end))).
apply H5.
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end)))).
apply (proj1 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end))).
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} (fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end) u).
apply (SubspaceMakeVSVoppSub f (FnVS f N) (SpanVS f (FnVS f N) {n : nat | n < M} (fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end)) (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end))).
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end)))).
suff: (A p = ((fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end) p)).
move=> H8.
rewrite {2} H8.
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} (fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end) p).
elim (Nat.eq_dec (proj1_sig p) (proj1_sig q)).
move=> H8.
elim (H1 H8).
move=> H8.
reflexivity.
elim (Nat.eq_dec (proj1_sig u) (proj1_sig q)).
move=> H7.
apply functional_extensionality.
move=> w.
unfold Fnminus.
unfold Fnmul.
unfold Fnadd.
unfold Fnopp.
rewrite (Fadd_assoc f (A u w) (Fmul f c (A p w)) (Fopp f (Fmul f c (A p w)))).
rewrite (Fadd_opp_r f (Fmul f c (A p w))).
rewrite (Fadd_O_r f (A u w)).
reflexivity.
move=> H7.
elim (H7 H6).
move=> H6.
suff: (A u = (fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end) u).
move=> H7.
rewrite H7.
apply (proj1 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end))).
apply H5.
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end)))).
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} (fun (x0 : {n : nat | n < M}) (y0 : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
  | left _ => Fadd f (A x0 y0) (Fmul f c (A p y0))
  | right _ => A x0 y0
end) u).
elim (Nat.eq_dec (proj1_sig u) (proj1_sig q)).
move=> H7.
elim (H6 H7).
move=> H7.
reflexivity.
move=> W1 W2 H2.
rewrite H2.
move=> H3 H4.
suff: (H3 = H4).
move=> H5.
rewrite H5.
move=> H6 H7.
suff: (H6 = H7).
move=> H8.
rewrite H8.
reflexivity.
apply proof_irrelevance.
apply proof_irrelevance.
Qed.

Lemma RankAddTransformW : forall (f : Field) (M N : nat) (A : Matrix f M N) (p q : {n : nat | n < N}) (c : FT f), proj1_sig p <> proj1_sig q -> Rank f M N (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig y) (proj1_sig q) with
  | left _ => Fadd f (A x y) (Fmul f c (A x p))
  | right _ => A x y
end) = Rank f M N A.
Proof.
move=> f M N A p q c H1.
rewrite - (ElementaryMatrixAddNatureR f M N A p q c H1).
rewrite - (RankTrans f M N (Mmult f M N N A (ElementaryMatrixAdd f N p q c))).
rewrite (MTransMult f M N N A (ElementaryMatrixAdd f N p q c)).
rewrite (ElementaryMatrixAddTrans f N p q c).
rewrite (ElementaryMatrixAddNatureL f N M (MTranspose f M N A) q p c).
rewrite (RankAddTransformH f N M (MTranspose f M N A) p q c H1).
apply (RankTrans f M N A).
move=> H2.
apply H1.
rewrite H2.
reflexivity.
Qed.

Lemma RankMultiplyTransformH : forall (f : Field) (M N : nat) (A : Matrix f M N) (p : {n : nat | (n < M)}) (c : FT f), c <> FO f -> Rank f M N (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end) = Rank f M N A.
Proof.
move=> f M N A p c H1.
suff: (forall (W1 W2 : Ensemble (Fn f N)), W1 = W2 -> forall (H1 : SubspaceVS f (FnVS f N) W1) (H2 : SubspaceVS f (FnVS f N) W2) (H3 : FiniteDimensionVS f (SubspaceMakeVS f (FnVS f N) W1 H1)) (H4 : FiniteDimensionVS f (SubspaceMakeVS f (FnVS f N) W2 H2)), DimensionSubspaceVS f (FnVS f N) W1 H1 H3 = DimensionSubspaceVS f (FnVS f N) W2 H2 H4).
move=> H2.
apply H2.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> x H3.
rewrite H3.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A))).
move=> cm u H4 H5.
apply (proj1 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A) cm).
apply H5.
elim (Nat.eq_dec (proj1_sig u) (proj1_sig p)).
move=> H6.
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) (proj1_sig x u)).
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) c (A u)).
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A u).
move=> H6.
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) (proj1_sig x u)).
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A u).
move=> v.
elim.
move=> x H3.
rewrite H3.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end)))).
move=> cm u H4 H5.
apply (proj1 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end))).
apply H5.
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end))) (proj1_sig x u) (A u)).
elim (classic (proj1_sig u = proj1_sig p)).
move=> H6.
suff: (A u = Fnmul f N (Finv f c) ((fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end) u)).
move=> H7.
rewrite H7.
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end))) (Finv f c)).
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end) u).
rewrite - {1} (Vmul_I_l f (FnVS f N) (A u)).
rewrite - (Finv_l f c H1).
rewrite - (Vmul_assoc f (FnVS f N) (Finv f c) c (A u)).
elim (Nat.eq_dec (proj1_sig u) (proj1_sig p)).
move=> H7.
reflexivity.
move=> H7.
elim (H7 H6).
move=> H6.
suff: (A u = (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end) u).
move=> H7.
rewrite H7.
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end) u).
elim (Nat.eq_dec (proj1_sig u) (proj1_sig p)).
move=> H7.
elim (H6 H7).
move=> H7.
reflexivity.
move=> W1 W2 H2.
rewrite H2.
move=> H3 H4.
suff: (H3 = H4).
move=> H5.
rewrite H5.
move=> H6 H7.
suff: (H6 = H7).
move=> H8.
rewrite H8.
reflexivity.
apply proof_irrelevance.
apply proof_irrelevance.
Qed.

Lemma RankMultiplyTransformW : forall (f : Field) (M N : nat) (A : Matrix f M N) (p : {n : nat | n < N}) (c : FT f), c <> FO f -> Rank f M N (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end) = Rank f M N A.
Proof.
move=> f M N A p c H1.
rewrite - (ElementaryMatrixMultiplyNatureR f M N A p c).
rewrite - (RankTrans f M N (Mmult f M N N A (ElementaryMatrixMultiply f N p c))).
rewrite (MTransMult f M N N A (ElementaryMatrixMultiply f N p c)).
rewrite (ElementaryMatrixMultiplyTrans f N p c).
rewrite (ElementaryMatrixMultiplyNatureL f N M (MTranspose f M N A) p c).
rewrite (RankMultiplyTransformH f N M (MTranspose f M N A) p c H1).
apply (RankTrans f M N A).
Qed.

Lemma RankSwapH : forall (f : Field) (M N : nat) (A : Matrix f M N) (p q : {n : nat | n < M}), Rank f M N (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => A q y
  | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
    | left _ => A p y
    | right _ => A x y
  end
end) = Rank f M N A.
Proof.
move=> f M N A p q.
suff: (forall (W1 W2 : Ensemble (Fn f N)), W1 = W2 -> forall (H1 : SubspaceVS f (FnVS f N) W1) (H2 : SubspaceVS f (FnVS f N) W2) (H3 : FiniteDimensionVS f (SubspaceMakeVS f (FnVS f N) W1 H1)) (H4 : FiniteDimensionVS f (SubspaceMakeVS f (FnVS f N) W2 H2)), DimensionSubspaceVS f (FnVS f N) W1 H1 H3 = DimensionSubspaceVS f (FnVS f N) W2 H2 H4).
move=> H1.
apply H1.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> x H2.
rewrite H2.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A))).
move=> cm u H3 H4.
apply (proj1 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)).
apply H4.
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} A)) (proj1_sig x u)).
elim (Nat.eq_dec (proj1_sig u) (proj1_sig p)).
move=> H5.
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A q).
move=> H5.
elim (Nat.eq_dec (proj1_sig u) (proj1_sig q)).
move=> H6.
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A p).
move=> H6.
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} A u).
move=> v.
elim.
move=> x H2.
rewrite H2.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => A q y
  | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
    | left _ => A p y
    | right _ => A x y
  end
end)))).
move=> cm u H3 H4.
apply (proj1 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => A q y
  | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
    | left _ => A p y
    | right _ => A x y
  end
end)) cm (Vmul f (FnVS f N) (proj1_sig x u) (A u))).
apply H4.
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f N) {n : nat | n < M} (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => A q y
  | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
    | left _ => A p y
    | right _ => A x y
  end
end))) (proj1_sig x u) (A u)).
elim (classic (proj1_sig u = proj1_sig p)).
move=> H5.
suff: (A u = (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => A q y
  | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
    | left _ => A p y
    | right _ => A x y
  end
end) q).
move=> H6.
rewrite H6.
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => A q y
  | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
    | left _ => A p y
    | right _ => A x y
  end
end) q).
elim (Nat.eq_dec (proj1_sig q) (proj1_sig p)).
move=> H6.
apply functional_extensionality.
move=> y.
suff: (u = q).
move=> H7.
rewrite H7.
reflexivity.
apply sig_map.
rewrite H5.
rewrite - H6.
reflexivity.
move=> H6.
elim (Nat.eq_dec (proj1_sig q) (proj1_sig q)).
move=> H7.
suff: (u = p).
move=> H8.
rewrite H8.
reflexivity.
apply sig_map.
apply H5.
move=> H7.
apply False_ind.
apply H7.
reflexivity.
move=> H5.
elim (classic (proj1_sig u = proj1_sig q)).
move=> H6.
suff: (A u = (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => A q y
  | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
    | left _ => A p y
    | right _ => A x y
  end
end) p).
move=> H7.
rewrite H7.
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => A q y
  | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
    | left _ => A p y
    | right _ => A x y
  end
end) p).
elim (Nat.eq_dec (proj1_sig p) (proj1_sig p)).
move=> H7.
suff: (u = q).
move=> H8.
rewrite H8.
reflexivity.
apply sig_map.
apply H6.
move=> H7.
apply False_ind.
apply H7.
reflexivity.
move=> H6.
suff: (A u = (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => A q y
  | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
    | left _ => A p y
    | right _ => A x y
  end
end) u).
move=> H7.
rewrite H7.
apply (SpanContainSelfVS f (FnVS f N) {n : nat | n < M} (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => A q y
  | right _ => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
    | left _ => A p y
    | right _ => A x y
  end
end) u).
elim (Nat.eq_dec (proj1_sig u) (proj1_sig p)).
move=> H7.
elim (H5 H7).
move=> H7.
elim (Nat.eq_dec (proj1_sig u) (proj1_sig q)).
move=> H8.
elim (H6 H8).
move=> H8.
reflexivity.
move=> W1 W2 H1.
rewrite H1.
move=> H2 H3.
suff: (H2 = H3).
move=> H4.
rewrite H4.
move=> H5 H6.
suff: (H5 = H6).
move=> H7.
rewrite H7.
reflexivity.
apply proof_irrelevance.
apply proof_irrelevance.
Qed.

Lemma RankSwapW : forall (f : Field) (M N : nat) (A : Matrix f M N) (p q : {n : nat | n < N}), Rank f M N (fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => A x q
  | right _ => match Nat.eq_dec (proj1_sig y) (proj1_sig q) with
    | left _ => A x p
    | right _ => A x y
  end
end) = Rank f M N A.
Proof.
move=> f M N A p q.
rewrite - (ElementaryMatrixSwapNatureR f M N A p q).
rewrite - (RankTrans f M N (Mmult f M N N A (ElementaryMatrixSwap f N p q))).
rewrite (MTransMult f M N N A (ElementaryMatrixSwap f N p q)).
rewrite (ElementaryMatrixSwapTrans f N p q).
rewrite (ElementaryMatrixSwapNatureL f N M (MTranspose f M N A) p q).
rewrite (RankSwapH f N M (MTranspose f M N A) p q).
apply (RankTrans f M N A).
Qed.

Definition RankNormalForm (f : Field) (M N r : nat) := fun (x : {n : nat | n < M}) (y : {n : nat | n < N}) => match Nat.eq_dec (proj1_sig x) (proj1_sig y) with
  | left _ => match excluded_middle_informative (proj1_sig x < r) with
    | left _ => FI f
    | right _ => FO f
  end
  | right _ => FO f
end.

Lemma TransformableToRankNormalForm : forall (f : Field) (M N : nat) (A : Matrix f M N), exists (r : nat), r <= M /\ r <= N /\ exists (B : Matrix f M M) (C : Matrix f N N), ElementaryTransformable f M B /\ ElementaryTransformable f N C /\ Mmult f M M N B (Mmult f M N N A C) = RankNormalForm f M N r.
Proof.
suff: (forall (f : Field) (M N : nat), (forall (A : Matrix f M N), exists (r : nat), r <= M /\ r <= N /\ (exists (B : Matrix f M M) (C : Matrix f N N), ElementaryTransformable f M B /\ ElementaryTransformable f N C /\ Mmult f M M N B (Mmult f M N N A C) = RankNormalForm f M N r)) -> (forall (A : Matrix f (S M) (S N)), exists (r : nat), r <= S M /\ r <= S N /\ (exists (B : Matrix f (S M) (S M)) (C : Matrix f (S N) (S N)), ElementaryTransformable f (S M) B /\ ElementaryTransformable f (S N) C /\ Mmult f (S M) (S M) (S N) B (Mmult f (S M) (S N) (S N) A C) = RankNormalForm f (S M) (S N) r))).
move=> H1 f.
elim.
move=> N A.
exists O.
apply conj.
apply (le_n O).
apply conj.
apply (le_0_n N).
exists (MI f O).
exists (MI f N).
apply conj.
exists nil.
apply conj.
apply (Forall_nil (fun (x : Matrix f O O) => ElementaryMatrix f O x)).
reflexivity.
apply conj.
exists nil.
apply conj.
apply (Forall_nil (fun (x : Matrix f N N) => ElementaryMatrix f N x)).
reflexivity.
apply functional_extensionality.
move=> x.
elim (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) (proj2_sig x)).
move=> M H2.
elim.
move=> A.
exists O.
apply conj.
apply (le_0_n (S M)).
apply conj.
apply (le_n O).
exists (MI f (S M)).
exists (MI f O).
apply conj.
exists nil.
apply conj.
apply (Forall_nil (fun (x : Matrix f (S M) (S M)) => ElementaryMatrix f (S M) x)).
reflexivity.
apply conj.
exists nil.
apply conj.
apply (Forall_nil (fun (x : Matrix f O O) => ElementaryMatrix f O x)).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) (proj2_sig y)).
move=> N H3.
apply (H1 f M N (H2 N)).
move=> f M N H1.
suff: (forall (A : Matrix f (S M) (S N)), (exists (m : Count (S M)) (n : Count (S N)), A m n <> FO f) -> exists (r : nat), r <= S M /\ r <= S N /\ (exists (B : Matrix f (S M) (S M)) (C : Matrix f (S N) (S N)), ElementaryTransformable f (S M) B /\ ElementaryTransformable f (S N) C /\ Mmult f (S M) (S M) (S N) B (Mmult f (S M) (S N) (S N) A C) = RankNormalForm f (S M) (S N) r)).
move=> H2 A.
elim (classic (exists (m : Count (S M)) (n : Count (S N)), A m n <> FO f)).
apply (H2 A).
move=> H3.
exists O.
apply conj.
apply (le_0_n (S M)).
apply conj.
apply (le_0_n (S N)).
exists (MI f (S M)).
exists (MI f (S N)).
apply conj.
exists nil.
apply conj.
apply (Forall_nil (fun (x : Matrix f (S M) (S M)) => ElementaryMatrix f (S M) x)).
reflexivity.
apply conj.
exists nil.
apply conj.
apply (Forall_nil (fun (x : Matrix f (S N) (S N)) => ElementaryMatrix f (S N) x)).
reflexivity.
suff: (A = MO f (S M) (S N)).
move=> H4.
rewrite H4.
rewrite (Mmult_O_l f (S M) (S N) (S N) (MI f (S N))).
rewrite (Mmult_O_r f (S M) (S M) (S N) (MI f (S M))).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold RankNormalForm.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H5.
elim (excluded_middle_informative (proj1_sig x < 0)).
move=> H6.
elim (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) H6).
move=> H6.
reflexivity.
move=> H5.
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply NNPP.
move=> H4.
apply H3.
exists x.
exists y.
apply H4.
suff: (forall (A : Matrix f (S M) (S N)) (B : Matrix f (S M) (S M)), ElementaryMatrix f (S M) B -> (exists (r : nat), r <= S M /\ r <= S N /\ (exists (C : Matrix f (S M) (S M)) (D : Matrix f (S N) (S N)), ElementaryTransformable f (S M) C /\ ElementaryTransformable f (S N) D /\ Mmult f (S M) (S M) (S N) C (Mmult f (S M) (S N) (S N) (Mmult f (S M) (S M) (S N) B A) D) = RankNormalForm f (S M) (S N) r) ) -> (exists (r : nat), r <= S M /\ r <= S N /\ (exists (C : Matrix f (S M) (S M)) (D : Matrix f (S N) (S N)), ElementaryTransformable f (S M) C /\ ElementaryTransformable f (S N) D /\ Mmult f (S M) (S M) (S N) C (Mmult f (S M) (S N) (S N) A D) = RankNormalForm f (S M) (S N) r) )).
suff: (forall (A : Matrix f (S M) (S N)) (B : Matrix f (S N) (S N)), ElementaryMatrix f (S N) B -> (exists (r : nat), r <= S M /\ r <= S N /\ (exists (C : Matrix f (S M) (S M)) (D : Matrix f (S N) (S N)), ElementaryTransformable f (S M) C /\ ElementaryTransformable f (S N) D /\ Mmult f (S M) (S M) (S N) C (Mmult f (S M) (S N) (S N) (Mmult f (S M) (S N) (S N) A B) D) = RankNormalForm f (S M) (S N) r) ) -> (exists (r : nat), r <= S M /\ r <= S N /\ (exists (C : Matrix f (S M) (S M)) (D : Matrix f (S N) (S N)), ElementaryTransformable f (S M) C /\ ElementaryTransformable f (S N) D /\ Mmult f (S M) (S M) (S N) C (Mmult f (S M) (S N) (S N) A D) = RankNormalForm f (S M) (S N) r) )).
suff: (S M = 1 + M).
move=> H2.
rewrite H2.
suff: (S N = 1 + N).
move=> H3.
rewrite H3.
move=> H4 H5.
suff: (O < 1 + M).
move=> H6.
suff: (O < 1 + N).
move=> H7.
suff: (forall (A : Matrix f (1 + M) (1 + N)), A (exist (fun (n : nat) => n < 1 + M) O H6) (exist (fun (n : nat) => n < 1 + N) O H7) <> FO f -> exists r : nat, r <= 1 + M /\ r <= 1 + N /\ (exists (B : Matrix f (1 + M) (1 + M)) (C : Matrix f (1 + N) (1 + N)), ElementaryTransformable f (1 + M) B /\ ElementaryTransformable f (1 + N) C /\ Mmult f (1 + M) (1 + M) (1 + N) B (Mmult f (1 + M) (1 + N) (1 + N) A C) = RankNormalForm f (1 + M) (1 + N) r)).
move=> H8 A.
elim.
move=> m.
elim.
move=> k H9.
elim (classic (proj1_sig m = O)).
move=> H10.
elim (classic (proj1_sig k = O)).
move=> H11.
apply (H8 A).
suff: ((exist (fun (n : nat) => n < 1 + M) 0 H6) = m).
move=> H12.
suff: ((exist (fun (n : nat) => n < 1 + N) 0 H7) = k).
move=> H13.
rewrite H12.
rewrite H13.
apply H9.
apply sig_map.
rewrite H11.
reflexivity.
apply sig_map.
rewrite H10.
reflexivity.
move=> H11.
apply (H4 A (ElementaryMatrixSwap f (1 + N) (exist (fun (n : nat) => n < 1 + N) 0 H7) k)).
apply (ElementaryMatrixSwap_intro f (1 + N) (exist (fun (n : nat) => n < 1 + N) 0 H7) k).
move=> H12.
apply H11.
rewrite - H12.
reflexivity.
apply (H8 (Mmult f (1 + M) (1 + N) (1 + N) A (ElementaryMatrixSwap f (1 + N) (exist (fun (n : nat) => n < 1 + N) 0 H7) k))).
rewrite (ElementaryMatrixSwapNatureR f (1 + M) (1 + N) A (exist (fun (n : nat) => n < 1 + N) 0 H7) k).
elim (Nat.eq_dec (proj1_sig (exist (fun (n : nat) => n < 1 + N) 0 H7)) (proj1_sig (exist (fun (n : nat) => n < 1 + N) 0 H7))).
move=> H12.
suff: ((exist (fun (n : nat) => n < 1 + M) 0 H6) = m).
move=> H13.
rewrite H13.
apply H9.
apply sig_map.
rewrite H10.
reflexivity.
move=> H12.
apply False_ind.
apply H12.
reflexivity.
move=> H10.
elim (classic (proj1_sig k = O)).
move=> H11.
apply (H5 A (ElementaryMatrixSwap f (1 + M) (exist (fun (n : nat) => n < 1 + M) 0 H6) m)).
apply (ElementaryMatrixSwap_intro f (1 + M) (exist (fun (n : nat) => n < 1 + M) 0 H6) m).
move=> H12.
apply H10.
rewrite - H12.
reflexivity.
apply (H8 (Mmult f (1 + M) (1 + M) (1 + N) (ElementaryMatrixSwap f (1 + M) (exist (fun (n : nat) => n < 1 + M) 0 H6) m) A)).
rewrite (ElementaryMatrixSwapNatureL f (1 + M) (1 + N) A (exist (fun (n : nat) => n < 1 + M) 0 H6) m).
elim (Nat.eq_dec (proj1_sig (exist (fun n : nat => n < 1 + M) 0 H6)) (proj1_sig (exist (fun n : nat => n < 1 + M) 0 H6))).
move=> H12.
suff: ((exist (fun (n : nat) => n < 1 + N) 0 H7) = k).
move=> H13.
rewrite H13.
apply H9.
apply sig_map.
rewrite H11.
reflexivity.
move=> H12.
apply False_ind.
apply H12.
reflexivity.
move=> H11.
apply (H5 A (ElementaryMatrixSwap f (1 + M) (exist (fun (n : nat) => n < 1 + M) 0 H6) m)).
apply (ElementaryMatrixSwap_intro f (1 + M) (exist (fun (n : nat) => n < 1 + M) 0 H6) m).
move=> H12.
apply H10.
rewrite - H12.
reflexivity.
apply (H4 (Mmult f (1 + M) (1 + M) (1 + N) (ElementaryMatrixSwap f (1 + M) (exist (fun (n : nat) => n < 1 + M) 0 H6) m) A) (ElementaryMatrixSwap f (1 + N) (exist (fun (n : nat) => n < 1 + N) 0 H7) k)).
apply (ElementaryMatrixSwap_intro f (1 + N) (exist (fun (n : nat) => n < 1 + N) 0 H7) k).
move=> H12.
apply H11.
rewrite - H12.
reflexivity.
apply (H8 (Mmult f (1 + M) (1 + N) (1 + N) (Mmult f (1 + M) (1 + M) (1 + N) (ElementaryMatrixSwap f (1 + M) (exist (fun (n : nat) => n < 1 + M) 0 H6) m) A) (ElementaryMatrixSwap f (1 + N) (exist (fun (n : nat) => n < 1 + N) 0 H7) k))).
rewrite (ElementaryMatrixSwapNatureL f (1 + M) (1 + N)).
rewrite (ElementaryMatrixSwapNatureR f (1 + M) (1 + N)).
elim (Nat.eq_dec (proj1_sig (exist (fun (n : nat) => n < 1 + M) 0 H6)) (proj1_sig (exist (fun (n : nat) => n < 1 + M) 0 H6))).
move=> H12.
elim (Nat.eq_dec (proj1_sig (exist (fun n : nat => n < 1 + N) 0 H7)) (proj1_sig (exist (fun n : nat => n < 1 + N) 0 H7))).
move=> H13.
apply H9.
move=> H13.
apply False_ind.
apply H13.
reflexivity.
move=> H12.
apply False_ind.
apply H12.
reflexivity.
suff: (forall (A : Matrix f (1 + M) (1 + N)), A (exist (fun (n : nat) => n < 1 + M) 0 H6) (exist (fun (n : nat) => n < 1 + N) 0 H7) = FI f -> exists (r : nat), r <= 1 + M /\ r <= 1 + N /\ (exists (B : Matrix f (1 + M) (1 + M)) (C : Matrix f (1 + N) (1 + N)), ElementaryTransformable f (1 + M) B /\ ElementaryTransformable f (1 + N) C /\ Mmult f (1 + M) (1 + M) (1 + N) B (Mmult f (1 + M) (1 + N) (1 + N) A C) = RankNormalForm f (1 + M) (1 + N) r)).
move=> H8 A H9.
apply (H5 A (ElementaryMatrixMultiply f (1 + M) (exist (fun (n : nat) => n < 1 + M) 0 H6) (Finv f (A (exist (fun (n : nat) => n < 1 + M) 0 H6) (exist (fun (n : nat) => n < 1 + N) 0 H7))))).
apply (ElementaryMatrixMultiply_intro f (1 + M) (exist (fun (n : nat) => n < 1 + M) 0 H6) (Finv f (A (exist (fun (n : nat) => n < 1 + M) 0 H6) (exist (fun (n : nat) => n < 1 + N) 0 H7)))).
apply (Finv_neq_O_compat f (A (exist (fun (n : nat) => n < 1 + M) 0 H6) (exist (fun (n : nat) => n < 1 + N) 0 H7)) H9).
apply (H8 (Mmult f (1 + M) (1 + M) (1 + N) (ElementaryMatrixMultiply f (1 + M) (exist (fun (n : nat) => n < 1 + M) 0 H6) (Finv f (A (exist (fun (n : nat) => n < 1 + M) 0 H6) (exist (fun (n : nat) => n < 1 + N) 0 H7)))) A)).
rewrite (ElementaryMatrixMultiplyNatureL f (1 + M) (1 + N) A (exist (fun (n : nat) => n < 1 + M) 0 H6) (Finv f (A (exist (fun (n : nat) => n < 1 + M) 0 H6) (exist (fun (n : nat) => n < 1 + N) 0 H7)))).
elim (Nat.eq_dec (proj1_sig (exist (fun (n : nat) => n < 1 + M) 0 H6)) (proj1_sig (exist (fun (n : nat) => n < 1 + M) 0 H6))).
move=> H10.
apply (Finv_l f (A (exist (fun (n : nat) => n < 1 + M) 0 H6) (exist (fun (n : nat) => n < 1 + N) 0 H7)) H9).
move=> H10.
apply False_ind.
apply H10.
reflexivity.
suff: (forall (k : nat), k <= M -> forall (A : Matrix f (S M) (S N)), (forall (m : Count M), proj1_sig m >= k -> A (AddConnect 1 M (inr m)) (exist (fun (n : nat) => n < 1 + N) 0 H7) = FO f) -> (A (exist (fun (n : nat) => n < 1 + M) 0 H6) (exist (fun (n : nat) => n < 1 + N) 0 H7) = FI f) -> exists (r : nat), r <= 1 + M /\ r <= 1 + N /\ (exists (B : Matrix f (1 + M) (1 + M)) (C : Matrix f (1 + N) (1 + N)), ElementaryTransformable f (1 + M) B /\ ElementaryTransformable f (1 + N) C /\ Mmult f (1 + M) (1 + M) (1 + N) B (Mmult f (1 + M) (1 + N) (1 + N) A C) = RankNormalForm f (1 + M) (1 + N) r)).
move=> H8 A.
apply (H8 M (le_n M) A).
move=> m H9.
elim (le_not_lt M (proj1_sig m) H9 (proj2_sig m)).
suff: (forall (k : nat), k <= N -> forall (A : Matrix f (S M) (S N)), (forall (m : Count M), A (AddConnect 1 M (inr m)) (exist (fun (n : nat) => n < 1 + N) 0 H7) = FO f) -> (forall (m : Count N), proj1_sig m >= k -> A (exist (fun (n : nat) => n < 1 + M) 0 H6) (AddConnect 1 N (inr m)) = FO f) -> (A (exist (fun (n : nat) => n < 1 + M) 0 H6) (exist (fun (n : nat) => n < 1 + N) 0 H7) = FI f) -> exists (r : nat), r <= 1 + M /\ r <= 1 + N /\ (exists (B : Matrix f (1 + M) (1 + M)) (C : Matrix f (1 + N) (1 + N)), ElementaryTransformable f (1 + M) B /\ ElementaryTransformable f (1 + N) C /\ Mmult f (1 + M) (1 + M) (1 + N) B (Mmult f (1 + M) (1 + N) (1 + N) A C) = RankNormalForm f (1 + M) (1 + N) r)).
move=> H8.
elim.
move=> H9 A H10.
apply (H8 N (le_n N) A).
move=> m.
apply (H10 m (le_0_n (proj1_sig m))).
move=> m H11.
elim (le_not_lt N (proj1_sig m) H11 (proj2_sig m)).
move=> k H9 H10 A H11 H12.
elim (classic (A (AddConnect 1 M (inr (exist (fun (l : nat) => l < M) k H10))) (exist (fun n : nat => n < 1 + N) 0 H7) = FO f)).
move=> H13.
apply (H9 (le_trans k (S k) M (le_S k k (le_n k)) H10) A).
move=> m H14.
elim (le_lt_or_eq k (proj1_sig m) H14).
move=> H15.
apply (H11 m H15).
move=> H15.
suff: (m = (exist (fun (l : nat) => l < M) k H10)).
move=> H16.
rewrite H16.
apply H13.
apply sig_map.
rewrite - H15.
reflexivity.
apply H12.
move=> H13.
apply (H5 A (ElementaryMatrixAdd f (1 + M) (AddConnect 1 M (inr (exist (fun (l : nat) => l < M) k H10))) (exist (fun (n : nat) => n < 1 + M) 0 H6) (Fopp f (A (AddConnect 1 M (inr (exist (fun (l : nat) => l < M) k H10))) (exist (fun (n : nat) => n < 1 + N) 0 H7))))).
apply (ElementaryMatrixAdd_intro f (1 + M) (AddConnect 1 M (inr (exist (fun (l : nat) => l < M) k H10))) (exist (fun (n : nat) => n < 1 + M) 0 H6) (Fopp f (A (AddConnect 1 M (inr (exist (fun (l : nat) => l < M) k H10))) (exist (fun (n : nat) => n < 1 + N) 0 H7)))).
rewrite - (proj2 (AddConnectNature 1 M) (exist (fun (l : nat) => l < M) k H10)).
simpl.
move=> H14.
suff: (let temp := (S k) in match temp with
  | O => False
  | S k => True
end).
rewrite H14.
apply.
apply I.
apply (Fopp_neq_O_compat f (A (AddConnect 1 M (inr (exist (fun (l : nat) => l < M) k H10))) (exist (fun (n : nat) => n < 1 + N) 0 H7)) H13).
rewrite (ElementaryMatrixAddNatureL f (1 + M) (1 + N) A).
apply (H9 (le_trans k (S k) M (le_S k k (le_n k)) H10)).
move=> m H14.
elim (Nat.eq_dec (proj1_sig (AddConnect 1 M (inr m))) (proj1_sig (AddConnect 1 M (inr (exist (fun (l : nat) => l < M) k H10))))).
move=> H15.
rewrite H12.
rewrite (Fmul_I_r f).
suff: (AddConnect 1 M (inr m) = AddConnect 1 M (inr (exist (fun (l : nat) => l < M) k H10))).
move=> H16.
rewrite H16.
apply (Fadd_opp_r f).
apply sig_map.
apply H15.
move=> H15.
apply (H11 m).
elim (le_lt_or_eq k (proj1_sig m) H14).
apply.
move=> H16.
apply False_ind.
apply H15.
suff: (m = (exist (fun (l : nat) => l < M) k H10)).
move=> H17.
rewrite H17.
reflexivity.
apply sig_map.
rewrite - H16.
reflexivity.
elim (Nat.eq_dec (proj1_sig (exist (fun (n : nat) => n < 1 + M) 0 H6)) (proj1_sig (AddConnect 1 M (inr (exist (fun (l : nat) => l < M) k H10))))).
rewrite - (proj2 (AddConnectNature 1 M) (exist (fun (l : nat) => l < M) k H10)).
simpl.
move=> H14.
suff: (let temp := O in match temp with
  | O => False
  | S k => True
end).
elim.
rewrite H14.
apply I.
move=> H14.
apply H12.
rewrite - (proj2 (AddConnectNature 1 M) (exist (fun (l : nat) => l < M) k H10)).
simpl.
move=> H14.
suff: (let temp := (S k) in match temp with
  | O => False
  | S k => True
end).
rewrite H14.
elim.
apply I.
suff: (forall (A : Matrix f M N), exists (r : nat), r <= 1 + M /\ r <= 1 + N /\ (exists (B : Matrix f (1 + M) (1 + M)) (C : Matrix f (1 + N) (1 + N)), ElementaryTransformable f (1 + M) B /\ ElementaryTransformable f (1 + N) C /\ Mmult f (1 + M) (1 + M) (1 + N) B (Mmult f (1 + M) (1 + N) (1 + N) (MBlockH f 1 M (1 + N) (MBlockW f 1 1 N (fun (m n : Count 1) => FI f) (MO f 1 N)) (MBlockW f M 1 N (MO f M 1) A)) C) = RankNormalForm f (1 + M) (1 + N) r)).
move=> H8.
elim.
move=> H9 A H10 H11 H12.
suff: (A = MBlockH f 1 M (1 + N) (MBlockW f 1 1 N (fun (m n : Count 1) => FI f) (MO f 1 N)) (MBlockW f M 1 N (MO f M 1) (fun (m : Count M) (k : Count N) => A (AddConnect 1 M (inr m)) (AddConnect 1 N (inr k))))).
move=> H13.
rewrite H13.
apply (H8 (fun (m : Count M) (k : Count N) => A (AddConnect 1 M (inr m)) (AddConnect 1 N (inr k)))).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
elim (le_or_lt 1 (proj1_sig x)).
move=> H13.
suff: (match AddConnectInv 1 M x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = 1 + proj1_sig k
end).
elim (AddConnectInv 1 M x).
move=> H14.
elim.
move=> x0 H14.
elim (le_or_lt 1 (proj1_sig y)).
move=> H15.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = 1 + proj1_sig k
end).
elim (AddConnectInv 1 N y).
move=> H16.
elim.
move=> y0 H16.
suff: (x = AddConnect 1 M (inr x0)).
suff: (y = AddConnect 1 N (inr y0)).
move=> H17 H18.
rewrite H17.
rewrite H18.
reflexivity.
apply sig_map.
rewrite H16.
apply (proj2 (AddConnectNature 1 N) y0).
apply sig_map.
rewrite H14.
apply (proj2 (AddConnectNature 1 M) x0).
apply (proj2 (AddConnectInvNature 1 N) y H15).
move=> H15.
suff: (match AddConnectInv 1 N y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N y).
move=> y0 H16.
suff: (x = AddConnect 1 M (inr x0)).
move=> H17.
suff: (y = (exist (fun (n : nat) => n < 1 + N) 0 H7)).
move=> H18.
rewrite H17.
rewrite H18.
apply (H10 x0).
apply sig_map.
rewrite H16.
apply (le_antisym (proj1_sig y0) O).
apply (le_S_n (proj1_sig y0) O (proj2_sig y0)).
apply (le_0_n (proj1_sig y0)).
apply sig_map.
rewrite H14.
apply (proj2 (AddConnectNature 1 M) x0).
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 N) y H15).
apply (proj2 (AddConnectInvNature 1 M) x H13).
move=> H13.
suff: (match AddConnectInv 1 M x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 M x).
move=> x0 H14.
elim (le_or_lt 1 (proj1_sig y)).
move=> H15.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = 1 + proj1_sig k
end).
elim (AddConnectInv 1 N y).
move=> H16.
elim.
move=> y0 H16.
suff: (x = (exist (fun (n : nat) => n < 1 + M) 0 H6)).
move=> H17.
suff: (y = AddConnect 1 N (inr y0)).
move=> H18.
rewrite H17.
rewrite H18.
apply (H11 y0 (le_0_n (proj1_sig y0))).
apply sig_map.
rewrite H16.
apply (proj2 (AddConnectNature 1 N) y0).
apply sig_map.
rewrite H14.
apply (le_antisym (proj1_sig x0) O).
apply (le_S_n (proj1_sig x0) O (proj2_sig x0)).
apply (le_0_n (proj1_sig x0)).
apply (proj2 (AddConnectInvNature 1 N) y H15).
move=> H15.
suff: (match AddConnectInv 1 N y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N y).
move=> y0 H16.
suff: (x = (exist (fun (n : nat) => n < 1 + M) 0 H6)).
move=> H17.
suff: (y = (exist (fun (n : nat) => n < 1 + N) 0 H7)).
move=> H18.
rewrite H17.
rewrite H18.
apply H12.
apply sig_map.
apply (le_antisym (proj1_sig y) O).
apply (le_S_n (proj1_sig y) O H15).
apply (le_0_n (proj1_sig y)).
apply sig_map.
apply (le_antisym (proj1_sig x) O).
apply (le_S_n (proj1_sig x) O H13).
apply (le_0_n (proj1_sig x)).
move=> H16.
elim.
apply (proj1 (AddConnectInvNature 1 N) y H15).
move=> H14.
elim.
apply (proj1 (AddConnectInvNature 1 M) x H13).
move=> k H9 H10 A H11 H12 H13.
elim (classic (A (exist (fun (n : nat) => n < 1 + M) 0 H6) (AddConnect 1 N (inr (exist (fun (l : nat) => l < N) k H10))) = FO f)).
move=> H14.
apply (H9 (le_trans k (S k) N (le_S k k (le_n k)) H10) A).
move=> m.
apply (H11 m).
move=> m H15.
elim (le_lt_or_eq k (proj1_sig m) H15).
move=> H16.
apply (H12 m H16).
move=> H16.
suff: (m = (exist (fun (l : nat) => l < N) k H10)).
move=> H17.
rewrite H17.
apply H14.
apply sig_map.
rewrite - H16.
reflexivity.
apply H13.
move=> H14.
apply (H4 A (ElementaryMatrixAdd f (1 + N) (exist (fun (n : nat) => n < 1 + N) 0 H7) (AddConnect 1 N (inr (exist (fun (l : nat) => l < N) k H10))) (Fopp f (A (exist (fun (n : nat) => n < 1 + M) 0 H6) (AddConnect 1 N (inr (exist (fun (l : nat) => l < N) k H10))))))).
apply (ElementaryMatrixAdd_intro f (1 + N) (exist (fun (n : nat) => n < 1 + N) 0 H7) (AddConnect 1 N (inr (exist (fun (l : nat) => l < N) k H10))) (Fopp f (A (exist (fun (n : nat) => n < 1 + M) 0 H6) (AddConnect 1 N (inr (exist (fun (l : nat) => l < N) k H10)))))).
rewrite - (proj2 (AddConnectNature 1 N) (exist (fun (l : nat) => l < N) k H10)).
simpl.
move=> H15.
suff: (let temp := O in match temp with
  | O => False
  | S k => True
end).
apply.
rewrite H15.
apply I.
apply (Fopp_neq_O_compat f (A (exist (fun (n : nat) => n < 1 + M) 0 H6) (AddConnect 1 N (inr (exist (fun (l : nat) => l < N) k H10)))) H14).
rewrite (ElementaryMatrixAddNatureR f (1 + M) (1 + N) A).
apply (H9 (le_trans k (S k) N (le_S k k (le_n k)) H10)).
move=> m.
elim (Nat.eq_dec (proj1_sig (exist (fun (n : nat) => n < 1 + N) 0 H7)) (proj1_sig (AddConnect 1 N (inr (exist (fun (l : nat) => l < N) k H10))))).
rewrite - (proj2 (AddConnectNature 1 N) (exist (fun (l : nat) => l < N) k H10)).
simpl.
move=> H15.
suff: (let temp := O in match temp with
  | O => False
  | S k => True
end).
elim.
rewrite H15.
apply I.
move=> H15.
apply (H11 m).
move=> m H15.
elim (Nat.eq_dec (proj1_sig (AddConnect 1 N (inr m))) (proj1_sig (AddConnect 1 N (inr (exist (fun (l : nat) => l < N) k H10))))).
move=> H16.
rewrite H13.
rewrite (Fmul_I_r f).
suff: (AddConnect 1 N (inr m) = AddConnect 1 N (inr (exist (fun (l : nat) => l < N) k H10))).
move=> H17.
rewrite H17.
apply (Fadd_opp_r f).
apply sig_map.
apply H16.
move=> H16.
apply (H12 m).
elim (le_lt_or_eq k (proj1_sig m) H15).
apply.
move=> H17.
apply False_ind.
apply H16.
suff: (m = (exist (fun (l : nat) => l < N) k H10)).
move=> H18.
rewrite H18.
reflexivity.
apply sig_map.
rewrite - H17.
reflexivity.
elim (Nat.eq_dec (proj1_sig (exist (fun (n : nat) => n < 1 + N) 0 H7)) (proj1_sig (AddConnect 1 N (inr (exist (fun (l : nat) => l < N) k H10))))).
rewrite - (proj2 (AddConnectNature 1 N) (exist (fun (l : nat) => l < N) k H10)).
simpl.
move=> H15.
suff: (let temp := O in match temp with
  | O => False
  | S k => True
end).
elim.
rewrite H15.
apply I.
move=> H15.
apply H13.
rewrite - (proj2 (AddConnectNature 1 N) (exist (fun (l : nat) => l < N) k H10)).
simpl.
move=> H15.
suff: (let temp := O in match temp with
  | O => False
  | S k => True
end).
elim.
rewrite H15.
apply I.
suff: (forall (K : nat) (A : Matrix f K K), ElementaryMatrix f K A -> ElementaryMatrix f (1 + K) (MBlockH f 1 K (1 + K) (MBlockW f 1 1 K (fun (m n : Count 1) => FI f) (MO f 1 K)) (MBlockW f K 1 K (MO f K 1) A))).
move=> H8.
suff: (forall (K : nat) (AL : list (Matrix f K K)), MyProdFL (MMM f (1 + K)) (map (fun (X : Matrix f K K) => MBlockH f 1 K (1 + K) (MBlockW f 1 1 K (fun (m n : Count 1) => FI f) (MO f 1 K)) (MBlockW f K 1 K (MO f K 1) X)) AL) = MBlockH f 1 K (1 + K) (MBlockW f 1 1 K (fun (m n : Count 1) => FI f) (MO f 1 K)) (MBlockW f K 1 K (MO f K 1) (MyProdFL (MMM f K) AL))).
move=> H9 A.
elim (H1 A).
move=> r H10.
elim (proj2 (proj2 H10)).
move=> B.
elim.
move=> C H11.
elim (proj1 H11).
move=> BL H12.
elim (proj1 (proj2 H11)).
move=> CL H13.
exists (1 + r).
apply conj.
apply (plus_le_compat_l r M 1 (proj1 H10)).
apply conj.
apply (plus_le_compat_l r N 1 (proj1 (proj2 H10))).
exists (MBlockH f 1 M (1 + M) (MBlockW f 1 1 M (fun (m n : Count 1) => FI f) (MO f 1 M)) (MBlockW f M 1 M (MO f M 1) B)).
exists (MBlockH f 1 N (1 + N) (MBlockW f 1 1 N (fun (m n : Count 1) => FI f) (MO f 1 N)) (MBlockW f N 1 N (MO f N 1) C)).
apply conj.
exists (map (fun (X : Matrix f M M) => MBlockH f 1 M (1 + M) (MBlockW f 1 1 M (fun (m n : Count 1) => FI f) (MO f 1 M)) (MBlockW f M 1 M (MO f M 1) X)) BL).
apply conj.
apply Forall_forall.
move=> X H14.
elim (proj1 (in_map_iff (fun (X : Matrix f M M) => MBlockH f 1 M (1 + M) (MBlockW f 1 1 M (fun (m n : Count 1) => FI f) (MO f 1 M)) (MBlockW f M 1 M (MO f M 1) X)) BL X) H14).
move=> Y H15.
rewrite - (proj1 H15).
apply (H8 M Y).
apply (proj1 (Forall_forall (ElementaryMatrix f M) BL) (proj1 H12) Y (proj2 H15)).
rewrite (proj2 H12).
rewrite (H9 M BL).
reflexivity.
apply conj.
exists (map (fun (X : Matrix f N N) => MBlockH f 1 N (1 + N) (MBlockW f 1 1 N (fun (m n : Count 1) => FI f) (MO f 1 N)) (MBlockW f N 1 N (MO f N 1) X)) CL).
apply conj.
apply Forall_forall.
move=> X H14.
elim (proj1 (in_map_iff (fun (X : Matrix f N N) => MBlockH f 1 N (1 + N) (MBlockW f 1 1 N (fun (m n : Count 1) => FI f) (MO f 1 N)) (MBlockW f N 1 N (MO f N 1) X)) CL X) H14).
move=> Y H15.
rewrite - (proj1 H15).
apply (H8 N Y).
apply (proj1 (Forall_forall (ElementaryMatrix f N) CL) (proj1 H13) Y (proj2 H15)).
rewrite (proj2 H13).
rewrite (H9 N CL).
reflexivity.
suff: (RankNormalForm f (1 + M) (1 + N) (1 + r) = MBlockH f 1 M (1 + N) (MBlockW f 1 1 N (fun (m n : Count 1) => FI f) (MO f 1 N)) (MBlockW f M 1 N (MO f M 1) (RankNormalForm f M N r))).
move=> H14.
rewrite H14.
suff: (Mmult f 1 1 1 (fun (m n : Count 1) => FI f) (fun (m n : Count 1) => FI f) = (fun (m n : Count 1) => FI f)).
move=> H15.
suff: (Mmult f (1 + M) (1 + N) (1 + N) (MBlockH f 1 M (1 + N) (MBlockW f 1 1 N (fun _ _ : Count 1 => FI f) (MO f 1 N)) (MBlockW f M 1 N (MO f M 1) A)) (MBlockH f 1 N (1 + N) (MBlockW f 1 1 N (fun _ _ : Count 1 => FI f) (MO f 1 N)) (MBlockW f N 1 N (MO f N 1) C)) = MBlockH f 1 M (1 + N) (MBlockW f 1 1 N (fun (m n : Count 1) => FI f) (MO f 1 N)) (MBlockW f M 1 N (MO f M 1) (Mmult f M N N A C))).
move=> H16.
rewrite H16.
rewrite (MBlockHWWHSame f 1 M 1 M).
rewrite MBlockHWMult.
rewrite MBlockHMult.
rewrite MBlockHMult.
rewrite MBlockWMult.
rewrite MBlockWMult.
rewrite MBlockWMult.
rewrite MBlockWMult.
rewrite MBlockHPlus.
rewrite MBlockWPlus.
rewrite MBlockWPlus.
rewrite Mmult_O_l.
rewrite Mmult_O_l.
rewrite Mmult_O_l.
rewrite Mmult_O_l.
rewrite Mmult_O_r.
rewrite Mmult_O_r.
rewrite Mplus_O_l.
rewrite Mplus_O_l.
rewrite Mplus_O_l.
rewrite (Mplus_comm f 1 1).
rewrite Mplus_O_l.
rewrite H15.
rewrite (proj2 (proj2 H11)).
reflexivity.
rewrite (MBlockHWWHSame f 1 M 1 N (fun _ _ : Count 1 => FI f) (MO f 1 N) (MO f M 1) A).
rewrite MBlockHWMult.
rewrite MBlockHMult.
rewrite MBlockHMult.
rewrite MBlockWMult.
rewrite MBlockWMult.
rewrite MBlockWMult.
rewrite MBlockWMult.
rewrite MBlockHPlus.
rewrite MBlockWPlus.
rewrite MBlockWPlus.
rewrite Mmult_O_l.
rewrite Mmult_O_l.
rewrite Mmult_O_l.
rewrite Mmult_O_l.
rewrite Mmult_O_r.
rewrite Mmult_O_r.
rewrite Mplus_O_l.
rewrite Mplus_O_l.
rewrite Mplus_O_l.
rewrite (Mplus_comm f 1 1).
rewrite Mplus_O_l.
rewrite H15.
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
suff: ((exist (Finite (Count 1)) (Full_set {n : nat | n < 1}) (CountFinite 1)) = FiniteSingleton (Count 1) (exist (fun (n : nat) => n < 1) O (le_n 1))).
move=> H15.
rewrite H15.
rewrite MySumF2Singleton.
apply (Fmul_I_r f (FI f)).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> m H15.
suff: (m = (exist (fun (n : nat) => n < 1) 0 (le_n 1))).
move=> H16.
rewrite H16.
apply (In_singleton (Count 1) (exist (fun (n : nat) => n < 1) 0 (le_n 1))).
apply sig_map.
apply le_antisym.
apply (le_S_n (proj1_sig m) O (proj2_sig m)).
apply (le_0_n (proj1_sig m)).
move=> m H15.
apply (Full_intro (Count 1) m).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
unfold RankNormalForm.
elim (le_or_lt 1 (proj1_sig y)).
move=> H14.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = 1 + proj1_sig k
end).
elim (AddConnectInv 1 N y).
move=> H15.
elim.
move=> y0 H15.
elim (le_or_lt 1 (proj1_sig x)).
move=> H16.
suff: (match AddConnectInv 1 M x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = 1 + proj1_sig k
end).
elim (AddConnectInv 1 M x).
move=> x0.
elim.
move=> x0 H17.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H18.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y0)).
move=> H19.
elim (excluded_middle_informative (proj1_sig x < 1 + r)).
move=> H20.
elim (excluded_middle_informative (proj1_sig x0 < r)).
move=> H21.
reflexivity.
move=> H21.
apply False_ind.
apply H21.
apply (plus_lt_reg_l (proj1_sig x0) r 1).
rewrite - H17.
apply H20.
move=> H20.
elim (excluded_middle_informative (proj1_sig x0 < r)).
move=> H21.
apply False_ind.
apply H20.
rewrite H17.
apply (plus_lt_compat_l (proj1_sig x0) r 1 H21).
move=> H21.
reflexivity.
move=> H19.
apply False_ind.
apply H19.
apply (plus_reg_l (proj1_sig x0) (proj1_sig y0) 1).
rewrite - H15.
rewrite - H17.
apply H18.
move=> H18.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y0)).
move=> H19.
apply False_ind.
apply H18.
rewrite H15.
rewrite H17.
rewrite H19.
reflexivity.
move=> H19.
reflexivity.
apply (proj2 (AddConnectInvNature 1 M) x H16).
move=> H16.
suff: (match AddConnectInv 1 M x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 M x).
move=> x0 H17.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H18.
apply False_ind.
suff: (O = S (proj1_sig y0)).
move=> H19.
suff: (let temp := O in match temp with
  | O => False
  | S _ => True
end).
apply.
rewrite H19.
apply I.
suff: (proj1_sig x = O).
move=> H19.
rewrite - H19.
rewrite H18.
apply H15.
apply (le_antisym (proj1_sig x) O (le_S_n (proj1_sig x) O H16) (le_0_n (proj1_sig x))).
move=> H18.
reflexivity.
move=> m.
elim.
apply (proj1 (AddConnectInvNature 1 M) x H16).
apply (proj2 (AddConnectInvNature 1 N) y H14).
move=> H14.
suff: (match AddConnectInv 1 N y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N y).
move=> y0 H15.
elim (le_or_lt 1 (proj1_sig x)).
move=> H16.
suff: (match AddConnectInv 1 M x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = 1 + proj1_sig k
end).
elim (AddConnectInv 1 M x).
move=> x0.
elim.
move=> x0 H17.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H18.
apply False_ind.
suff: (O = S (proj1_sig x0)).
move=> H19.
suff: (let temp := O in match temp with
  | O => False
  | S _ => True
end).
apply.
rewrite H19.
apply I.
suff: (proj1_sig y = O).
move=> H19.
rewrite - H19.
rewrite - H18.
apply H17.
apply (le_antisym (proj1_sig y) O (le_S_n (proj1_sig y) O H14) (le_0_n (proj1_sig y))).
move=> H18.
reflexivity.
apply (proj2 (AddConnectInvNature 1 M) x H16).
move=> H16.
suff: (match AddConnectInv 1 M x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 M x).
move=> x0 H17.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H18.
elim (excluded_middle_informative (proj1_sig x < 1 + r)).
move=> H19.
reflexivity.
move=> H19.
apply False_ind.
apply H19.
rewrite H17.
apply (le_trans (S (proj1_sig x0)) 1 (1 + r) (proj2_sig x0) (le_plus_l 1 r)).
move=> H18.
apply False_ind.
suff: (forall (m : Count 1), proj1_sig m = O).
move=> H19.
apply H18.
rewrite H15.
rewrite H17.
rewrite (H19 y0).
apply (H19 x0).
move=> m.
apply (le_antisym (proj1_sig m) O (le_S_n (proj1_sig m) O (proj2_sig m)) (le_0_n (proj1_sig m))).
move=> m.
elim.
apply (proj1 (AddConnectInvNature 1 M) x H16).
move=> m.
elim.
apply (proj1 (AddConnectInvNature 1 N) y H14).
move=> K.
elim.
simpl.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H9.
suff: (x = y).
move=> H10.
rewrite H10.
elim (AddConnectInv 1 K y).
move=> m.
reflexivity.
move=> m.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H11.
reflexivity.
move=> H11.
apply False_ind.
apply H11.
reflexivity.
apply sig_map.
apply H9.
move=> H9.
elim (le_or_lt 1 (proj1_sig x)).
move=> H10.
suff: (match AddConnectInv 1 K x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = 1 + proj1_sig k
end).
elim (AddConnectInv 1 K x).
move=> x0.
elim.
move=> x0 H11.
elim (le_or_lt 1 (proj1_sig y)).
move=> H12.
suff: (match AddConnectInv 1 K y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = 1 + proj1_sig k
end).
elim (AddConnectInv 1 K y).
move=> y0.
elim.
move=> y0 H13.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y0)).
move=> H14.
apply False_ind.
apply H9.
rewrite H11.
rewrite H13.
rewrite H14.
reflexivity.
move=> H14.
reflexivity.
apply (proj2 (AddConnectInvNature 1 K) y H12).
move=> H12.
suff: (match AddConnectInv 1 K y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 K y).
move=> y0 H13.
reflexivity.
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 K) y H12).
apply (proj2 (AddConnectInvNature 1 K) x H10).
move=> H10.
suff: (match AddConnectInv 1 K x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr k => False
end).
elim (AddConnectInv 1 K x).
move=> x0 H11.
elim (le_or_lt 1 (proj1_sig y)).
move=> H12.
suff: (match AddConnectInv 1 K y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = 1 + proj1_sig k
end).
elim (AddConnectInv 1 K y).
move=> y0.
elim.
move=> y0 H13.
reflexivity.
apply (proj2 (AddConnectInvNature 1 K) y H12).
move=> H12.
apply False_ind.
apply H9.
suff: (forall (m : nat), m < 1 -> m = O).
move=> H13.
rewrite (H13 (proj1_sig y) H12).
apply (H13 (proj1_sig x) H10).
move=> m H13.
apply (le_antisym m O (le_S_n m O H13) (le_0_n m)).
move=> x0.
elim.
apply (proj1 (AddConnectInvNature 1 K) x H10).
move=> A AL H9.
suff: (MyProdFL (MMM f (1 + K)) (map (fun X : Matrix f K K => MBlockH f 1 K (1 + K) (MBlockW f 1 1 K (fun _ _ : Count 1 => FI f) (MO f 1 K)) (MBlockW f K 1 K (MO f K 1) X)) (A :: AL)) = Mmult f (1 + K) (1 + K) (1 + K) (MBlockH f 1 K (1 + K) (MBlockW f 1 1 K (fun _ _ : Count 1 => FI f) (MO f 1 K)) (MBlockW f K 1 K (MO f K 1) A)) (MyProdFL (MMM f (1 + K)) (map (fun X : Matrix f K K => MBlockH f 1 K (1 + K) (MBlockW f 1 1 K (fun _ _ : Count 1 => FI f) (MO f 1 K)) (MBlockW f K 1 K (MO f K 1) X)) AL))).
move=> H10.
rewrite H10.
rewrite H9.
suff: (Mmult f 1 1 1 (fun (m n : Count 1) => FI f) (fun (m n : Count 1) => FI f) = (fun (m n : Count 1) => FI f)).
move=> H11.
rewrite (MBlockHWWHSame f 1 K 1 K).
rewrite MBlockHWMult.
rewrite MBlockHMult.
rewrite MBlockHMult.
rewrite MBlockWMult.
rewrite MBlockWMult.
rewrite MBlockWMult.
rewrite MBlockWMult.
rewrite MBlockHPlus.
rewrite MBlockWPlus.
rewrite MBlockWPlus.
rewrite Mmult_O_l.
rewrite Mmult_O_l.
rewrite Mmult_O_l.
rewrite Mmult_O_l.
rewrite Mmult_O_r.
rewrite Mmult_O_r.
rewrite Mplus_O_l.
rewrite Mplus_O_l.
rewrite Mplus_O_l.
rewrite H11.
rewrite (Mplus_comm f 1 1).
rewrite Mplus_O_l.
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
suff: ((exist (Finite (Count 1)) (Full_set {n : nat | n < 1}) (CountFinite 1)) = FiniteSingleton (Count 1) (exist (fun (n : nat) => n < 1) O (le_n 1))).
move=> H11.
rewrite H11.
rewrite MySumF2Singleton.
apply (Fmul_I_r f (FI f)).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> m H11.
suff: (m = (exist (fun (n : nat) => n < 1) 0 (le_n 1))).
move=> H12.
rewrite H12.
apply (In_singleton (Count 1) (exist (fun (n : nat) => n < 1) 0 (le_n 1))).
apply sig_map.
apply le_antisym.
apply (le_S_n (proj1_sig m) O (proj2_sig m)).
apply (le_0_n (proj1_sig m)).
move=> m H15.
apply (Full_intro (Count 1) m).
reflexivity.
move=> K A.
elim.
move=> p q c H8 H9.
suff: (MBlockH f 1 K (1 + K) (MBlockW f 1 1 K (fun _ _ : Count 1 => FI f) (MO f 1 K)) (MBlockW f K 1 K (MO f K 1) (ElementaryMatrixAdd f K p q c)) = ElementaryMatrixAdd f (1 + K) (AddConnect 1 K (inr p)) (AddConnect 1 K (inr q)) c).
move=> H10.
rewrite H10.
apply (ElementaryMatrixAdd_intro f (1 + K) (AddConnect 1 K (inr p)) (AddConnect 1 K (inr q)) c).
rewrite - (proj2 (AddConnectNature 1 K) p).
rewrite - (proj2 (AddConnectNature 1 K) q).
move=> H11.
apply (H8 (plus_reg_l (proj1_sig p) (proj1_sig q) 1 H11)).
apply H9.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
unfold ElementaryMatrixAdd.
elim (le_or_lt 1 (proj1_sig x)).
move=> H10.
suff: (match AddConnectInv 1 K x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = 1 + proj1_sig k
end).
elim (AddConnectInv 1 K x).
move=> x0.
elim.
move=> x0 H11.
elim (le_or_lt 1 (proj1_sig y)).
move=> H12.
suff: (match AddConnectInv 1 K y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = 1 + proj1_sig k
end).
elim (AddConnectInv 1 K y).
move=> y0.
elim.
move=> y0 H13.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y0)).
move=> H14.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H15.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig p)).
move=> H16.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr p)))).
move=> H17.
reflexivity.
move=> H17.
reflexivity.
move=> H16.
reflexivity.
move=> H15.
apply False_ind.
apply H15.
rewrite H11.
rewrite H13.
rewrite H14.
reflexivity.
move=> H14.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
rewrite H11.
rewrite H13.
move=> H15.
apply False_ind.
apply H14.
apply (plus_reg_l (proj1_sig x0) (proj1_sig y0) 1 H15).
move=> H15.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig p)).
move=> H16.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr p)))).
move=> H17.
elim (Nat.eq_dec (proj1_sig y0) (proj1_sig q)).
move=> H18.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
move=> H19.
reflexivity.
elim.
rewrite H13.
rewrite H18.
apply (proj2 (AddConnectNature 1 K) q).
move=> H18.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
rewrite H13.
rewrite - (proj2 (AddConnectNature 1 K) q).
move=> H19.
elim H18.
apply (plus_reg_l (proj1_sig y0) (proj1_sig q) 1 H19).
move=> H19.
reflexivity.
elim.
rewrite H11.
rewrite H16.
apply (proj2 (AddConnectNature 1 K) p).
move=> H16.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr p)))).
rewrite H11.
rewrite - (proj2 (AddConnectNature 1 K) p).
move=> H17.
elim H16.
apply (plus_reg_l (proj1_sig x0) (proj1_sig p) 1 H17).
move=> H17.
elim (Nat.eq_dec (proj1_sig y0) (proj1_sig q)).
move=> H18.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
move=> H19.
reflexivity.
move=> H19.
reflexivity.
move=> H18.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
move=> H19.
reflexivity.
move=> H19.
reflexivity.
apply (proj2 (AddConnectInvNature 1 K) y H12).
move=> H12.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H13.
elim (le_not_lt 1 (proj1_sig y)).
rewrite - H13.
rewrite H11.
apply (le_plus_l 1 (proj1_sig x0)).
apply H12.
move=> H13.
suff: (match AddConnectInv 1 K y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 K y).
move=> y0 H14.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr p)))).
move=> H15.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
rewrite H14.
rewrite - (proj2 (AddConnectNature 1 K) q).
move=> H16.
suff: (O = S (proj1_sig q)).
discriminate.
rewrite - (le_antisym (proj1_sig y0) O (le_S_n (proj1_sig y0) O (proj2_sig y0)) (le_0_n (proj1_sig y0))).
apply H16.
move=> H16.
reflexivity.
move=> H15.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
move=> H16.
reflexivity.
move=> H16.
reflexivity.
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 K) y H12).
apply (proj2 (AddConnectInvNature 1 K) x H10).
move=> H10.
suff: (match AddConnectInv 1 K x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 K x).
move=> x0 H11.
elim (le_or_lt 1 (proj1_sig y)).
move=> H12.
suff: (match AddConnectInv 1 K y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = 1 + proj1_sig k
end).
elim (AddConnectInv 1 K y).
move=> y0.
elim.
move=> y0 H13.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
rewrite H11.
rewrite H13.
move=> H14.
suff: (O = S (proj1_sig y0)).
discriminate.
rewrite - (le_antisym (proj1_sig x0) O (le_S_n (proj1_sig x0) O (proj2_sig x0)) (le_0_n (proj1_sig x0))).
apply H14.
move=> H14.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr p)))).
rewrite H11.
rewrite - (proj2 (AddConnectNature 1 K) p).
move=> H15.
suff: (O = S (proj1_sig p)).
discriminate.
rewrite - (le_antisym (proj1_sig x0) O (le_S_n (proj1_sig x0) O (proj2_sig x0)) (le_0_n (proj1_sig x0))).
apply H15.
move=> H15.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
move=> H16.
reflexivity.
move=> H16.
reflexivity.
apply (proj2 (AddConnectInvNature 1 K) y H12).
move=> H12.
suff: (match AddConnectInv 1 K y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 K y).
move=> y0 H13.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr p)))).
move=> H14.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
rewrite H13.
rewrite - (proj2 (AddConnectNature 1 K) q).
move=> H15.
suff: (O = S (proj1_sig q)).
discriminate.
rewrite - (le_antisym (proj1_sig y0) O (le_S_n (proj1_sig y0) O (proj2_sig y0)) (le_0_n (proj1_sig y0))).
apply H15.
move=> H15.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H16.
reflexivity.
elim.
rewrite H11.
rewrite H13.
suff: (forall (m : nat), m < 1 -> m = 0).
move=> H16.
rewrite (H16 (proj1_sig y0) (proj2_sig y0)).
apply (H16 (proj1_sig x0) (proj2_sig x0)).
move=> m H16.
apply (le_antisym m O (le_S_n m O H16) (le_0_n m)).
move=> H14.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H15.
reflexivity.
elim.
suff: (forall (m : nat), m < 1 -> m = 0).
move=> H15.
rewrite (H15 (proj1_sig y) H12).
apply (H15 (proj1_sig x) H10).
move=> m H15.
apply (le_antisym m O (le_S_n m O H15) (le_0_n m)).
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 K) y H12).
move=> x0.
elim.
apply (proj1 (AddConnectInvNature 1 K) x H10).
move=> p c H8.
suff: (MBlockH f 1 K (1 + K) (MBlockW f 1 1 K (fun _ _ : Count 1 => FI f) (MO f 1 K)) (MBlockW f K 1 K (MO f K 1) (ElementaryMatrixMultiply f K p c)) = ElementaryMatrixMultiply f (1 + K) (AddConnect 1 K (inr p)) c).
move=> H9.
rewrite H9.
apply (ElementaryMatrixMultiply_intro f (1 + K) (AddConnect 1 K (inr p)) c H8).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
unfold ElementaryMatrixMultiply.
elim (le_or_lt 1 (proj1_sig x)).
move=> H9.
suff: (match AddConnectInv 1 K x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = 1 + proj1_sig k
end).
elim (AddConnectInv 1 K x).
move=> x0.
elim.
move=> x0 H10.
elim (le_or_lt 1 (proj1_sig y)).
move=> H11.
suff: (match AddConnectInv 1 K y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = 1 + proj1_sig k
end).
elim (AddConnectInv 1 K y).
move=> y0.
elim.
move=> y0 H12.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y0)).
move=> H13.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H14.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig p)).
move=> H15.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr p)))).
move=> H16.
reflexivity.
move=> H16.
apply False_ind.
apply H16.
rewrite H10.
rewrite H15.
apply (proj2 (AddConnectNature 1 K) p).
move=> H15.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr p)))).
rewrite - (proj2 (AddConnectNature 1 K) p).
rewrite H10.
move=> H16.
apply False_ind.
apply H15.
apply (plus_reg_l (proj1_sig x0) (proj1_sig p) 1 H16).
move=> H16.
reflexivity.
move=> H14.
apply False_ind.
apply H14.
rewrite H10.
rewrite H13.
rewrite H12.
reflexivity.
move=> H13.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
rewrite H10.
rewrite H12.
move=> H14.
apply False_ind.
apply H13.
apply (plus_reg_l (proj1_sig x0) (proj1_sig y0) 1 H14).
move=> H14.
reflexivity.
apply (proj2 (AddConnectInvNature 1 K) y H11).
move=> H11.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H12.
elim (le_not_lt 1 (proj1_sig y)).
rewrite - H12.
rewrite H10.
apply (le_plus_l 1 (proj1_sig x0)).
apply H11.
move=> H12.
suff: (match AddConnectInv 1 K y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 K y).
reflexivity.
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 K) y H11).
apply (proj2 (AddConnectInvNature 1 K) x H9).
move=> H9.
suff: (match AddConnectInv 1 K x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 K x).
move=> x0 H10.
elim (le_or_lt 1 (proj1_sig y)).
move=> H11.
suff: (match AddConnectInv 1 K y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = 1 + proj1_sig k
end).
elim (AddConnectInv 1 K y).
move=> y0.
elim.
move=> y0 H12.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H13.
elim (le_not_lt 1 (proj1_sig x)).
rewrite H13.
apply H11.
apply H9.
move=> H13.
reflexivity.
apply (proj2 (AddConnectInvNature 1 K) y H11).
move=> H11.
suff: (match AddConnectInv 1 K y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 K y).
move=> y0 H12.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H13.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr p)))).
rewrite - (proj2 (AddConnectNature 1 K) p).
move=> H14.
suff: (O = S (proj1_sig p)).
discriminate.
rewrite - (le_antisym (proj1_sig x0) O (le_S_n (proj1_sig x0) O (proj2_sig x0)) (le_0_n (proj1_sig x0))).
rewrite - H10.
apply H14.
move=> H14.
reflexivity.
elim.
rewrite H10.
rewrite H12.
suff: (forall (m : nat), m < 1 -> m = 0).
move=> H13.
rewrite (H13 (proj1_sig y0) (proj2_sig y0)).
apply (H13 (proj1_sig x0) (proj2_sig x0)).
move=> m H13.
apply (le_antisym m O (le_S_n m O H13) (le_0_n m)).
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 K) y H11).
move=> x0.
elim.
apply (proj1 (AddConnectInvNature 1 K) x H9).
move=> p q H8.
suff: (MBlockH f 1 K (1 + K) (MBlockW f 1 1 K (fun _ _ : Count 1 => FI f) (MO f 1 K)) (MBlockW f K 1 K (MO f K 1) (ElementaryMatrixSwap f K p q)) = ElementaryMatrixSwap f (1 + K) (AddConnect 1 K (inr p)) (AddConnect 1 K (inr q))).
move=> H9.
rewrite H9.
apply (ElementaryMatrixSwap_intro f (1 + K) (AddConnect 1 K (inr p)) (AddConnect 1 K (inr q))).
rewrite - (proj2 (AddConnectNature 1 K) p).
rewrite - (proj2 (AddConnectNature 1 K) q).
move=> H10.
apply H8.
apply (plus_reg_l (proj1_sig p) (proj1_sig q) 1 H10).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
unfold ElementaryMatrixSwap.
elim (le_or_lt 1 (proj1_sig x)).
move=> H9.
suff: (match AddConnectInv 1 K x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = 1 + proj1_sig k
end).
elim (AddConnectInv 1 K x).
move=> x0.
elim.
move=> x0 H10.
elim (le_or_lt 1 (proj1_sig y)).
move=> H11.
suff: (match AddConnectInv 1 K y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = 1 + proj1_sig k
end).
elim (AddConnectInv 1 K y).
move=> y0.
elim.
move=> y0 H12.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y0)).
move=> H13.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H14.
rewrite H13.
rewrite H14.
elim (Nat.eq_dec (proj1_sig y0) (proj1_sig p)).
move=> H15.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr p)))).
move=> H16.
elim (Nat.eq_dec (proj1_sig y0) (proj1_sig q)).
move=> H17.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
move=> H18.
reflexivity.
move=> H18.
apply False_ind.
apply H18.
rewrite - (proj2 (AddConnectNature 1 K) q).
rewrite H12.
rewrite H17.
reflexivity.
move=> H17.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
rewrite - (proj2 (AddConnectNature 1 K) q).
rewrite H12.
move=> H18.
apply False_ind.
apply H17.
apply (plus_reg_l (proj1_sig y0) (proj1_sig q) 1 H18).
move=> H18.
reflexivity.
move=> H16.
apply False_ind.
apply H16.
rewrite - (proj2 (AddConnectNature 1 K) p).
rewrite H12.
rewrite H15.
reflexivity.
move=> H15.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr p)))).
rewrite - (proj2 (AddConnectNature 1 K) p).
rewrite H12.
move=> H16.
apply False_ind.
apply H15.
apply (plus_reg_l (proj1_sig y0) (proj1_sig p) 1 H16).
move=> H16.
elim (Nat.eq_dec (proj1_sig y0) (proj1_sig q)).
move=> H17.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
move=> H18.
reflexivity.
move=> H18.
apply False_ind.
apply H18.
rewrite H12.
rewrite - (proj2 (AddConnectNature 1 K) q).
rewrite H17.
reflexivity.
move=> H17.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
rewrite H12.
rewrite - (proj2 (AddConnectNature 1 K) q).
move=> H18.
apply False_ind.
apply H17.
apply (plus_reg_l (proj1_sig y0) (proj1_sig q) 1 H18).
move=> H18.
reflexivity.
move=> H14.
apply False_ind.
apply H14.
rewrite H10.
rewrite H12.
rewrite H13.
reflexivity.
move=> H13.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H14.
apply False_ind.
apply H13.
apply (plus_reg_l (proj1_sig x0) (proj1_sig y0) 1).
rewrite - H10.
rewrite - H12.
apply H14.
move=> H14.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig p)).
move=> H15.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr p)))).
move=> H16.
elim (Nat.eq_dec (proj1_sig y0) (proj1_sig q)).
move=> H17.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
move=> H18.
reflexivity.
move=> H18.
apply False_ind.
apply H18.
rewrite H12.
rewrite - (proj2 (AddConnectNature 1 K) q).
rewrite H17.
reflexivity.
move=> H17.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
rewrite - (proj2 (AddConnectNature 1 K) q).
move=> H18.
apply False_ind.
apply H17.
apply (plus_reg_l (proj1_sig y0) (proj1_sig q) 1).
rewrite - H18.
rewrite H12.
reflexivity.
move=> H18.
reflexivity.
move=> H16.
apply False_ind.
apply H16.
rewrite H10.
rewrite H15.
apply (proj2 (AddConnectNature 1 K) p).
move=> H15.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr p)))).
rewrite H10.
rewrite - (proj2 (AddConnectNature 1 K) p).
move=> H16.
apply False_ind.
apply H15.
apply (plus_reg_l (proj1_sig x0) (proj1_sig p) 1 H16).
move=> H16.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig q)).
move=> H17.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr q)))).
move=> H18.
elim (Nat.eq_dec (proj1_sig y0) (proj1_sig p)).
move=> H19.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr p)))).
move=> H20.
reflexivity.
move=> H20.
apply False_ind.
apply H20.
rewrite H12.
rewrite H19.
apply (proj2 (AddConnectNature 1 K) p).
move=> H19.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr p)))).
rewrite H12.
rewrite - (proj2 (AddConnectNature 1 K) p).
move=> H20.
apply False_ind.
apply H19.
apply (plus_reg_l (proj1_sig y0) (proj1_sig p) 1 H20).
move=> H20.
reflexivity.
move=> H18.
apply False_ind.
apply H18.
rewrite H10.
rewrite H17.
apply (proj2 (AddConnectNature 1 K) q).
move=> H17.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr q)))).
rewrite H10.
rewrite - (proj2 (AddConnectNature 1 K) q).
move=> H18.
apply False_ind.
apply H17.
apply (plus_reg_l (proj1_sig x0) (proj1_sig q) 1 H18).
move=> H18.
reflexivity.
apply (proj2 (AddConnectInvNature 1 K) y H11).
move=> H11.
suff: (match AddConnectInv 1 K y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 K y).
move=> y0 H12.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr q)))).
rewrite H12.
rewrite - (proj2 (AddConnectNature 1 K) q).
move=> H13.
apply False_ind.
suff: (proj1_sig y0 = O).
move=> H14.
suff: (O = S (proj1_sig q)).
discriminate.
rewrite - H14.
apply H13.
apply (le_antisym (proj1_sig y0) O (le_S_n (proj1_sig y0) O (proj2_sig y0)) (le_0_n (proj1_sig y0))).
move=> H13.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect 1 K (inr p)))).
rewrite H12.
rewrite - (proj2 (AddConnectNature 1 K) p).
move=> H14.
apply False_ind.
suff: (proj1_sig y0 = O).
move=> H15.
suff: (O = S (proj1_sig p)).
discriminate.
rewrite - H15.
apply H14.
apply (le_antisym (proj1_sig y0) O (le_S_n (proj1_sig y0) O (proj2_sig y0)) (le_0_n (proj1_sig y0))).
move=> H14.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H15.
apply False_ind.
suff: (O = S (proj1_sig x0)).
discriminate.
suff: (proj1_sig y0 = O).
move=> H16.
rewrite - H16.
rewrite - H12.
rewrite - H15.
apply H10.
apply (le_antisym (proj1_sig y0) O (le_S_n (proj1_sig y0) O (proj2_sig y0)) (le_0_n (proj1_sig y0))).
move=> H15.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr p)))).
move=> H16.
reflexivity.
move=> H16.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr q)))).
move=> H17.
reflexivity.
move=> H17.
reflexivity.
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 K) y H11).
apply (proj2 (AddConnectInvNature 1 K) x H9).
move=> H9.
suff: (match AddConnectInv 1 K x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 K x).
move=> x0 H10.
elim (le_or_lt 1 (proj1_sig y)).
move=> H11.
suff: (match AddConnectInv 1 K y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = 1 + proj1_sig k
end).
elim (AddConnectInv 1 K y).
move=> y0.
elim.
move=> y0 H12.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr q)))).
rewrite H10.
rewrite - (proj2 (AddConnectNature 1 K) q).
move=> H13.
apply False_ind.
suff: (proj1_sig x0 = O).
move=> H14.
suff: (O = S (proj1_sig q)).
discriminate.
rewrite - H14.
apply H13.
apply (le_antisym (proj1_sig x0) O (le_S_n (proj1_sig x0) O (proj2_sig x0)) (le_0_n (proj1_sig x0))).
move=> H13.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr p)))).
rewrite H10.
rewrite - (proj2 (AddConnectNature 1 K) p).
move=> H14.
apply False_ind.
suff: (proj1_sig x0 = O).
move=> H15.
suff: (O = S (proj1_sig p)).
discriminate.
rewrite - H15.
apply H14.
apply (le_antisym (proj1_sig x0) O (le_S_n (proj1_sig x0) O (proj2_sig x0)) (le_0_n (proj1_sig x0))).
move=> H14.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H15.
apply False_ind.
suff: (O = S (proj1_sig y0)).
discriminate.
suff: (proj1_sig x0 = O).
move=> H16.
rewrite - H16.
rewrite - H10.
rewrite H15.
apply H12.
apply (le_antisym (proj1_sig x0) O (le_S_n (proj1_sig x0) O (proj2_sig x0)) (le_0_n (proj1_sig x0))).
move=> H15.
reflexivity.
apply (proj2 (AddConnectInvNature 1 K) y H11).
move=> H11.
suff: (match AddConnectInv 1 K y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 K y).
move=> y0 H12.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr p)))).
rewrite - (proj2 (AddConnectNature 1 K) p).
rewrite H10.
move=> H13.
apply False_ind.
suff: (proj1_sig x0 = O).
move=> H14.
suff: (O = S (proj1_sig p)).
discriminate.
rewrite - H14.
apply H13.
apply (le_antisym (proj1_sig x0) O (le_S_n (proj1_sig x0) O (proj2_sig x0)) (le_0_n (proj1_sig x0))).
move=> H13.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect 1 K (inr q)))).
rewrite - (proj2 (AddConnectNature 1 K) q).
rewrite H10.
move=> H14.
apply False_ind.
suff: (proj1_sig x0 = O).
move=> H15.
suff: (O = S (proj1_sig q)).
discriminate.
rewrite - H15.
apply H14.
apply (le_antisym (proj1_sig x0) O (le_S_n (proj1_sig x0) O (proj2_sig x0)) (le_0_n (proj1_sig x0))).
move=> H14.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H15.
reflexivity.
move=> H15.
apply False_ind.
apply H15.
suff: (forall (m : nat), m < 1 -> m = 0).
move=> H16.
rewrite (H16 (proj1_sig y) H11).
apply (H16 (proj1_sig x) H9).
move=> m H16.
apply (le_antisym m O (le_S_n m O H16) (le_0_n m)).
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 K) y H11).
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 K) x H9).
apply (le_n_S O N (le_0_n N)).
apply (le_n_S O M (le_0_n M)).
reflexivity.
reflexivity.
move=> A B H2.
elim.
move=> r H3.
elim (proj2 (proj2 H3)).
move=> C.
elim.
move=> D H4.
exists r.
apply conj.
apply (proj1 H3).
apply conj.
apply (proj1 (proj2 H3)).
exists C.
exists (Mmult f (S N) (S N) (S N) B D).
apply conj.
apply (proj1 H4).
apply conj.
apply (ElementaryTransformableConnect f (S N) B D).
exists (B :: nil).
apply conj.
apply Forall_cons.
apply H2.
apply Forall_nil.
simpl.
rewrite (Mmult_I_r f (S N) (S N) B).
reflexivity.
apply (proj1 (proj2 H4)).
rewrite - (Mmult_assoc f (S M) (S N) (S N) (S N) A B D).
apply (proj2 (proj2 H4)).
move=> A B H2.
elim.
move=> r H3.
elim (proj2 (proj2 H3)).
move=> C.
elim.
move=> D H4.
exists r.
apply conj.
apply (proj1 H3).
apply conj.
apply (proj1 (proj2 H3)).
exists (Mmult f (S M) (S M) (S M) C B).
exists D.
apply conj.
apply (ElementaryTransformableConnect f (S M) C B).
apply (proj1 H4).
exists (B :: nil).
apply conj.
apply Forall_cons.
apply H2.
apply Forall_nil.
simpl.
rewrite (Mmult_I_r f (S M) (S M) B).
reflexivity.
apply conj.
apply (proj1 (proj2 H4)).
rewrite (Mmult_assoc f (S M) (S M) (S M) (S N) C B (Mmult f (S M) (S N) (S N) A D)).
rewrite - (Mmult_assoc f (S M) (S M) (S N) (S N) B A D).
apply (proj2 (proj2 H4)).
Qed.

Lemma RankElementaryMatrixL : forall (f : Field) (M N : nat) (A : Matrix f M N) (B : Matrix f M M), ElementaryMatrix f M B -> Rank f M N (Mmult f M M N B A) = Rank f M N A.
Proof.
move=> f M N A B.
elim.
move=> p q c H1 H2.
rewrite (ElementaryMatrixAddNatureL f M N A p q c H1).
apply (RankAddTransformH f M N A q p c).
move=> H3.
apply H1.
rewrite H3.
reflexivity.
move=> p c H1.
rewrite (ElementaryMatrixMultiplyNatureL f M N A p c).
apply (RankMultiplyTransformH f M N A p c H1).
move=> p q H1.
rewrite (ElementaryMatrixSwapNatureL f M N A p q).
apply (RankSwapH f M N A p q).
Qed.

Lemma RankElementaryTransformableL : forall (f : Field) (M N : nat) (A : Matrix f M N) (B : Matrix f M M), ElementaryTransformable f M B -> Rank f M N (Mmult f M M N B A) = Rank f M N A.
Proof.
move=> f M N.
suff: (forall (BL : list (Matrix f M M)), Forall (ElementaryMatrix f M) BL -> forall (A : Matrix f M N), Rank f M N (Mmult f M M N (MyProdFL (MMM f M) BL) A) = Rank f M N A).
move=> H1 A B.
elim.
move=> BL H2.
rewrite (proj2 H2).
apply (H1 BL (proj1 H2) A).
elim.
move=> H1 A.
simpl.
rewrite (Mmult_I_l f M N A).
reflexivity.
move=> a l H1 H2 A.
simpl.
rewrite (Mmult_assoc f M M M N a (MyProdFL (MMM f M) l) A).
rewrite (RankElementaryMatrixL f M N (Mmult f M M N (MyProdFL (MMM f M) l) A) a (Forall_inv H2)).
apply (H1 (Forall_inv_tail H2) A).
Qed.

Lemma RankElementaryMatrixR : forall (f : Field) (M N : nat) (A : Matrix f M N) (B : Matrix f N N), ElementaryMatrix f N B -> Rank f M N (Mmult f M N N A B) = Rank f M N A.
Proof.
move=> f M N A B.
elim.
move=> p q c H1 H2.
rewrite (ElementaryMatrixAddNatureR f M N A p q c H1).
apply (RankAddTransformW f M N A p q c H1).
move=> p c H1.
rewrite (ElementaryMatrixMultiplyNatureR f M N A p c).
apply (RankMultiplyTransformW f M N A p c H1).
move=> p q H1.
rewrite (ElementaryMatrixSwapNatureR f M N A p q).
apply (RankSwapW f M N A p q).
Qed.

Lemma RankElementaryTransformableR : forall (f : Field) (M N : nat) (A : Matrix f M N) (B : Matrix f N N), ElementaryTransformable f N B -> Rank f M N (Mmult f M N N A B) = Rank f M N A.
Proof.
move=> f M N.
suff: (forall (BL : list (Matrix f N N)), Forall (ElementaryMatrix f N) BL -> forall (A : Matrix f M N), Rank f M N (Mmult f M N N A (MyProdFL (MMM f N) BL)) = Rank f M N A).
move=> H1 A B.
elim.
move=> BL H2.
rewrite (proj2 H2).
apply (H1 BL (proj1 H2) A).
elim.
move=> H1 A.
simpl.
rewrite (Mmult_I_r f M N A).
reflexivity.
move=> a l H1 H2 A.
simpl.
rewrite - (Mmult_assoc f M N N N A a (MyProdFL (MMM f N) l)).
rewrite (H1 (Forall_inv_tail H2) (Mmult f M N N A a)).
apply (RankElementaryMatrixR f M N A a (Forall_inv H2)).
Qed.

Lemma RankNormalFormRank : forall (f : Field) (M N : nat) (r : nat), r <= M -> r <= N -> Rank f M N (RankNormalForm f M N r) = r.
Proof.
move=> f M N r H1 H2.
apply (proj2 (RankDef2 f M N (RankNormalForm f M N r) r)).
apply conj.
exists (fun (m : {n : nat | n < r}) => exist (fun (n : nat) => n < M) (proj1_sig m) (le_trans (S (proj1_sig m)) r M (proj2_sig m) H1)).
apply (FiniteLinearlyIndependentVS f (FnVS f N) r).
move=> a H3.
suff: (forall (m : Count r), a m = MySumF2 (Count r) (exist (Finite (Count r)) (Full_set (Count r)) (CountFinite r)) (VSPCM f (FnVS f N)) (fun (n : Count r) => Vmul f (FnVS f N) (a n) (RankNormalForm f M N r (exist (fun (n0 : nat) => n0 < M) (proj1_sig n) (Nat.le_trans (S (proj1_sig n)) r M (proj2_sig n) H1)))) (exist (fun (n : nat) => n < N) (proj1_sig m) (le_trans (S (proj1_sig m)) r N (proj2_sig m) H2))).
move=> H4 m.
rewrite (H4 m).
rewrite H3.
reflexivity.
move=> m.
suff: (MySumF2 (Count r) (exist (Finite (Count r)) (Full_set (Count r)) (CountFinite r)) (VSPCM f (FnVS f N)) (fun (n : Count r) => Vmul f (FnVS f N) (a n) (RankNormalForm f M N r (exist (fun (n0 : nat) => n0 < M) (proj1_sig n) (Nat.le_trans (S (proj1_sig n)) r M (proj2_sig n) H1)))) (exist (fun (n : nat) => n < N) (proj1_sig m) (Nat.le_trans (S (proj1_sig m)) r N (proj2_sig m) H2)) = MySumF2 (Count r) (exist (Finite (Count r)) (Full_set (Count r)) (CountFinite r)) (FPCM f) (fun (n : Count r) => Fmul f (a n) (RankNormalForm f M N r (exist (fun (n0 : nat) => n0 < M) (proj1_sig n) (Nat.le_trans (S (proj1_sig n)) r M (proj2_sig n) H1)) (exist (fun (n : nat) => n < N) (proj1_sig m) (Nat.le_trans (S (proj1_sig m)) r N (proj2_sig m) H2))))).
move=> H5.
rewrite H5.
rewrite (MySumF2Included (Count r) (FiniteSingleton (Count r) m)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
unfold RankNormalForm.
simpl.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H6.
elim (excluded_middle_informative (proj1_sig m < r)).
move=> H7.
rewrite (Fmul_I_r f (a m)).
rewrite (Fadd_O_r f (a m)).
reflexivity.
move=> H7.
elim (H7 (proj2_sig m)).
move=> H6.
apply False_ind.
apply H6.
reflexivity.
move=> u.
elim.
move=> u0 H6 H7.
unfold RankNormalForm.
simpl.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig m)).
move=> H8.
apply False_ind.
apply H6.
suff: (u0 = m).
move=> H9.
rewrite H9.
apply (In_singleton (Count r) m).
apply sig_map.
apply H8.
move=> H8.
apply (Fmul_O_r f (a u0)).
move=> u H6.
apply (Full_intro (Count r) u).
apply (FiniteSetInduction (Count r) (exist (Finite (Count r)) (Full_set (Count r)) (CountFinite r))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite - H7.
reflexivity.
apply H6.
apply H6.
move=> k.
elim.
move=> G H3.
suff: (forall (m : Count k), proj1_sig (G m) < r).
move=> H4.
apply (CountInjectiveLe k r (fun (m : Count k) => exist (fun (n : nat) => n < r) (proj1_sig (G m)) (H4 m))).
move=> m1 m2 H5.
apply (LinearlyIndependentInjectiveVS f (FnVS f N) {n : nat | n < k} (fun m : {n : nat | n < k} => RankNormalForm f M N r (G m)) H3).
suff: (G m1 = G m2).
move=> H6.
rewrite H6.
reflexivity.
apply sig_map.
suff: (proj1_sig (G m1) = proj1_sig (exist (fun (n : nat) => n < r) (proj1_sig (G m1)) (H4 m1))).
move=> H6.
rewrite H6.
rewrite H5.
reflexivity.
reflexivity.
move=> m.
elim (le_or_lt r (proj1_sig (G m))).
move=> H4.
apply False_ind.
apply (FI_neq_FO f).
suff: (FI f = match excluded_middle_informative (m = m) with
  | left _ => FI f
  | right _ => FO f
end).
move=> H5.
rewrite H5.
suff: (MySumF2 (Count k) (exist (Finite (Count k)) (Full_set (Count k)) (CountFinite k)) (VSPCM f (FnVS f N)) (fun (n : Count k) => Vmul f (FnVS f N) (match excluded_middle_informative (m = n) with
  | left _ => FI f
  | right _ => FO f
end) (RankNormalForm f M N r (G n))) = VO f (FnVS f N)).
move=> H6.
apply (proj1 (FiniteLinearlyIndependentVS f (FnVS f N) k (fun (m : {n : nat | n < k}) => RankNormalForm f M N r (G m))) H3 (fun (l : Count k) => match excluded_middle_informative (m = l) with
  | left _ => FI f
  | right _ => FO f
end) H6 m).
apply MySumF2O.
move=> u H6.
elim (excluded_middle_informative (m = u)).
move=> H7.
rewrite - H7.
unfold RankNormalForm.
rewrite (Vmul_I_l f (FnVS f N)).
apply functional_extensionality.
move=> l.
elim (Nat.eq_dec (proj1_sig (G m)) (proj1_sig l)).
move=> H8.
elim (excluded_middle_informative (proj1_sig (G m) < r)).
move=> H9.
elim (le_not_lt r (proj1_sig (G m)) H4 H9).
move=> H9.
reflexivity.
move=> H8.
reflexivity.
move=> H7.
apply (Vmul_O_l f (FnVS f N)).
elim (excluded_middle_informative (m = m)).
move=> H5.
reflexivity.
move=> H5.
apply False_ind.
apply H5.
reflexivity.
apply.
Qed.

Lemma RankNormalFormNature : forall (f : Field) (M N : nat) (A : Matrix f M N) (r : nat), r <= M -> r <= N -> Rank f M N A = r <-> exists (B : Matrix f M M) (C : Matrix f N N), ElementaryTransformable f M B /\ ElementaryTransformable f N C /\ Mmult f M M N B (Mmult f M N N A C) = RankNormalForm f M N r.
Proof.
move=> f M N A r H1 H2.
apply conj.
move=> H3.
elim (TransformableToRankNormalForm f M N A).
move=> r0 H4.
suff: (r = r0).
move=> H5.
rewrite H5.
apply (proj2 (proj2 H4)).
suff: (Rank f M N A = r0).
move=> H5.
rewrite - H5.
rewrite H3.
reflexivity.
elim (proj2 (proj2 H4)).
move=> B.
elim.
move=> C H6.
rewrite - (RankElementaryTransformableR f M N A C (proj1 (proj2 H6))).
rewrite - (RankElementaryTransformableL f M N (Mmult f M N N A C) B (proj1 H6)).
rewrite (proj2 (proj2 H6)).
apply (RankNormalFormRank f M N r0 (proj1 H4) (proj1 (proj2 H4))).
elim.
move=> B.
elim.
move=> C H3.
rewrite - (RankElementaryTransformableR f M N A C (proj1 (proj2 H3))).
rewrite - (RankElementaryTransformableL f M N (Mmult f M N N A C) B (proj1 H3)).
rewrite (proj2 (proj2 H3)).
apply (RankNormalFormRank f M N r H1 H2).
Qed.

Lemma ElementaryTransformableRegular : forall (f : Field) (N : nat) (A : Matrix f N N), ElementaryTransformable f N A <-> RegularMatrix f N A.
Proof.
suff: (forall (f : Field) (N : nat) (A : Matrix f N N), ElementaryTransformable f N A -> RegularMatrix f N A).
move=> H1.
suff: (forall (f : Field) (N : nat) (A : Matrix f N N), ElementaryTransformable f N A -> ElementaryTransformable f N (InvMatrix f N A)).
move=> H2 f N A.
apply conj.
apply (H1 f N A).
move=> H3.
elim (TransformableToRankNormalForm f N N A).
move=> r H4.
elim (proj2 (proj2 H4)).
move=> B.
elim.
move=> C H5.
suff: (A = Mmult f N N N (InvMatrix f N B) (InvMatrix f N C)).
move=> H6.
rewrite H6.
apply (ElementaryTransformableConnect f N (InvMatrix f N B) (InvMatrix f N C)).
apply (H2 f N B (proj1 H5)).
apply (H2 f N C (proj1 (proj2 H5))).
suff: (MI f N = Mmult f N N N B (Mmult f N N N A C)).
move=> H6.
rewrite - (Mmult_I_r f N N (InvMatrix f N B)).
rewrite H6.
rewrite - (Mmult_assoc f N N N N (InvMatrix f N B) B (Mmult f N N N A C)).
rewrite (InvMatrixMultL f N B (H1 f N B (proj1 H5))).
rewrite (Mmult_I_l f N N (Mmult f N N N A C)).
rewrite (Mmult_assoc f N N N N A C (InvMatrix f N C)).
rewrite (InvMatrixMultR f N C (H1 f N C (proj1 (proj2 H5)))).
rewrite (Mmult_I_r f N N A).
reflexivity.
rewrite (proj2 (proj2 H5)).
suff: (r = N).
move=> H6.
rewrite H6.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MI.
unfold RankNormalForm.
elim (excluded_middle_informative (proj1_sig x < N)).
move=> H7.
reflexivity.
move=> H7.
elim (H7 (proj2_sig x)).
elim (le_lt_or_eq r N (proj1 H4)).
move=> H6.
apply False_ind.
suff: (RegularMatrix f N (Mmult f N N N B (Mmult f N N N A C))).
move=> H7.
apply H7.
rewrite (proj2 (proj2 H5)).
unfold Determinant.
apply MySumF2O.
move=> u H8.
rewrite (MySumF2Included {n : nat | n < N} (FiniteSingleton {n : nat | n < N} (exist (fun (k : nat) => k < N) r H6))).
rewrite MySumF2Singleton.
unfold RankNormalForm.
simpl.
elim (Nat.eq_dec r (proj1_sig (proj1_sig u (exist (fun k : nat => k < N) r H6)))).
move=> H9.
elim (excluded_middle_informative (r < r)).
move=> H10.
elim (lt_irrefl r H10).
move=> H10.
rewrite (Fmul_O_l f).
apply (Fmul_O_r f).
move=> H9.
rewrite (Fmul_O_l f).
apply (Fmul_O_r f).
move=> m H9.
apply (Full_intro {n : nat | n < N} m).
apply (RegularMatrixChain f N B (Mmult f N N N A C) (H1 f N B (proj1 H5)) (RegularMatrixChain f N A C H3 (H1 f N C (proj1 (proj2 H5))))).
apply.
suff: (forall (f : Field) (N : nat) (AL : list (Matrix f N N)), Forall (ElementaryMatrix f N) AL -> ElementaryTransformable f N (InvMatrix f N (MyProdFL (MMM f N) AL))).
move=> H2 f N A.
elim.
move=> AL H3.
rewrite (proj2 H3).
apply (H2 f N AL (proj1 H3)).
move=> f N.
elim.
simpl.
suff: (InvMatrix f N (MI f N) = MI f N).
move=> H2.
rewrite H2.
exists nil.
apply conj.
apply Forall_nil.
reflexivity.
rewrite {2} (InvMatrixMultUniqueRStrong f N (MI f N) (MI f N)).
reflexivity.
apply (Mmult_I_l f N N (MI f N)).
move=> a l H2 H3.
simpl.
rewrite (InvMatrixMult f N a (MyProdFL (MMM f N) l)).
apply (ElementaryTransformableConnect f N (InvMatrix f N (MyProdFL (MMM f N) l)) (InvMatrix f N a)).
apply (H2 (Forall_inv_tail H3)).
exists ((InvMatrix f N a) :: nil).
apply conj.
apply Forall_cons.
elim (Forall_inv H3).
move=> p q c H4 H5.
rewrite (InvMatrixElementaryMatrixAdd f N p q c H4).
apply (ElementaryMatrixAdd_intro f N p q (Fopp f c) H4).
apply (Fopp_neq_O_compat f c H5).
move=> p c H4.
rewrite (InvMatrixElementaryMatrixMultiply f N p c H4).
apply (ElementaryMatrixMultiply_intro f N p (Finv f c)).
apply (Finv_neq_O_compat f c H4).
move=> p q H4.
rewrite (InvMatrixElementaryMatrixSwap f N p q).
apply (ElementaryMatrixSwap_intro f N p q H4).
apply Forall_nil.
simpl.
rewrite (Mmult_I_r f N N (InvMatrix f N a)).
reflexivity.
apply (H1 f N a).
exists (a :: nil).
apply conj.
apply Forall_cons.
apply (Forall_inv H3).
apply Forall_nil.
simpl.
rewrite (Mmult_I_r f N N a).
reflexivity.
apply (H1 f N).
exists l.
apply conj.
apply (Forall_inv_tail H3).
reflexivity.
suff: (forall (f : Field) (N : nat) (AL : list (Matrix f N N)), Forall (ElementaryMatrix f N) AL -> RegularMatrix f N (MyProdFL (MMM f N) AL)).
move=> H1 f N A.
elim.
move=> AL H2.
rewrite (proj2 H2).
apply (H1 f N AL (proj1 H2)).
move=> f N.
elim.
move=> H1.
simpl.
unfold RegularMatrix.
rewrite (DeterminantI f N).
apply (FI_neq_FO f).
move=> a l H1 H2.
apply (RegularMatrixChain f N a (MyProdFL (MMM f N) l)).
apply (ElementaryMatrixRegular f N a).
apply (Forall_inv H2).
apply (H1 (Forall_inv_tail H2)).
Qed.

Lemma RegularMatrixRank : forall (f : Field) (N : nat) (A : Matrix f N N), RegularMatrix f N A <-> Rank f N N A = N.
Proof.
move=> f N A.
apply conj.
move=> H1.
elim (TransformableToRankNormalForm f N N A).
move=> r H2.
elim (proj2 (proj2 H2)).
move=> B.
elim.
move=> C H3.
suff: (N = r).
move=> H4.
rewrite {3} H4.
apply (RankNormalFormNature f N N A r (proj1 H2) (proj1 H2)).
exists B.
exists C.
apply H3.
elim (le_lt_or_eq r N (proj1 H2)).
move=> H4.
apply False_ind.
suff: (RegularMatrix f N (Mmult f N N N B (Mmult f N N N A C))).
move=> H5.
apply H5.
rewrite (proj2 (proj2 H3)).
unfold Determinant.
apply MySumF2O.
move=> u H6.
rewrite (MySumF2Included {n : nat | n < N} (FiniteSingleton {n : nat | n < N} (exist (fun (k : nat) => k < N) r H4))).
rewrite MySumF2Singleton.
unfold RankNormalForm.
simpl.
elim (Nat.eq_dec r (proj1_sig (proj1_sig u (exist (fun k : nat => k < N) r H4)))).
move=> H7.
elim (excluded_middle_informative (r < r)).
move=> H8.
elim (lt_irrefl r H8).
move=> H8.
rewrite (Fmul_O_l f).
apply (Fmul_O_r f).
move=> H7.
rewrite (Fmul_O_l f).
apply (Fmul_O_r f).
move=> m H7.
apply (Full_intro {n : nat | n < N} m).
apply (RegularMatrixChain f N B (Mmult f N N N A C) (proj1 (ElementaryTransformableRegular f N B) (proj1 H3)) (RegularMatrixChain f N A C H1 (proj1 (ElementaryTransformableRegular f N C) (proj1 (proj2 H3))))).
move=> H4.
rewrite H4.
reflexivity.
move=> H1.
elim (proj1 (RankNormalFormNature f N N A N (le_n N) (le_n N)) H1).
move=> B.
elim.
move=> C H2 H3.
apply (FI_neq_FO f).
rewrite - (DeterminantI f N).
suff: (MI f N = RankNormalForm f N N N).
move=> H4.
rewrite H4.
rewrite - (proj2 (proj2 H2)).
rewrite (DeterminantMult f N B (Mmult f N N N A C)).
rewrite (DeterminantMult f N A C).
rewrite H3.
rewrite (Fmul_O_l f).
apply (Fmul_O_r f).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MI.
unfold RankNormalForm.
elim (excluded_middle_informative (proj1_sig x < N)).
move=> H4.
reflexivity.
move=> H4.
elim (H4 (proj2_sig x)).
Qed.

Lemma RankMultLeL : forall (f : Field) (M N K : nat) (A : Matrix f N K) (B : Matrix f M N), Rank f M K (Mmult f M N K B A) <= Rank f N K A.
Proof.
move=> f M N K A B.
unfold Rank.
apply (Proposition_5_9_1_2_subspace f (FnVS f K) (SpanVS f (FnVS f K) {n : nat | n < M} (Mmult f M N K B A)) (SpanVS f (FnVS f K) {n : nat | n < N} A) (SpanSubspaceVS f (FnVS f K) {n : nat | n < M} (Mmult f M N K B A)) (SpanSubspaceVS f (FnVS f K) {n : nat | n < N} A)).
move=> x.
elim.
move=> a H1.
rewrite H1.
apply (FiniteSetInduction {n : nat | n < M} (exist (Finite {n : nat | n < M}) (fun (t : {n : nat | n < M}) => proj1_sig a t <> FO f) (proj2_sig a))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS f (FnVS f K) {n : nat | n < N} A))).
move=> C c H2 H3 H4 H5.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS f (FnVS f K) {n : nat | n < N} A)).
apply H5.
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f K) {n : nat | n < N} A))).
unfold Mmult.
suff: ((fun (y : {n : nat | n < K}) => MySumF2 {n : nat | n < N} (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N)) (FPCM f) (fun (n : Count N) => Fmul f (B c n) (A n y))) = MySumF2 {n : nat | n < N} (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM f (FnVS f K)) (fun (n : Count N) => Vmul f (FnVS f K) (B c n) (A n))).
move=> H6.
rewrite H6.
apply (FiniteSetInduction {n : nat | n < N} (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS f (FnVS f K) {n : nat | n < N} A))).
move=> D d H7 H8 H9 H10.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS f (FnVS f K) {n : nat | n < N} A)).
apply H10.
apply (proj1 (proj2 (SpanSubspaceVS f (FnVS f K) {n : nat | n < N} A))).
apply (SpanContainSelfVS f (FnVS f K) {n : nat | n < N} A d).
apply H9.
apply functional_extensionality.
move=> m.
apply (FiniteSetInduction {n : nat | n < N} (exist (Finite (Count N)) (Full_set {n : nat | n < N}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> D d H6 H7 H8 H9.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H9.
reflexivity.
apply H8.
apply H8.
apply H4.
Qed.

Lemma RankMultLeR : forall (f : Field) (M N K : nat) (A : Matrix f M N) (B : Matrix f N K), Rank f M K (Mmult f M N K A B) <= Rank f M N A.
Proof.
move=> f M N K A B.
rewrite - (RankTrans f M K (Mmult f M N K A B)).
rewrite - (RankTrans f M N A).
rewrite (MTransMult f M N K A B).
apply (RankMultLeL f K N M (MTranspose f M N A) (MTranspose f N K B)).
Qed.

End Matrix.
