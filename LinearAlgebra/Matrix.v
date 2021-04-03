Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "Tools" as Tools.
Add LoadPath "BasicProperty" as BasicProperty.
Add LoadPath "BasicNotation" as BasicNotation.

From mathcomp Require Import ssreflect.
Require Import Coq.Sets.Ensembles.
Require Export QArith_base.
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
Require Import BasicProperty.MappingProperty.
Require Import BasicNotation.Parity.
Require Import BasicNotation.Permutation.

Section Matrix.

Definition FPCM (f : Field) := mkCommutativeMonoid (FT f) (FO f) (Fadd f) (Fadd_comm f) (Fadd_O_r f) (Fadd_assoc f).

Definition FMCM (f : Field) := mkCommutativeMonoid (FT f) (FI f) (Fmul f) (Fmul_comm f) (Fmul_I_r f) (Fmul_assoc f).

Definition Matrix (f : Field) (M N : nat) := {n : nat| (n < M)%nat } -> {n : nat| (n < N)%nat } -> (FT f).

Definition Mplus (f : Field) (M N : nat) := fun (A B : Matrix f M N) (x : {n : nat| (n < M)%nat }) (y : {n : nat| (n < N)%nat }) => (Fadd f (A x y) (B x y)).

Definition Mmult (f : Field) (M N K : nat) := fun (A : Matrix f M N) (B : Matrix f N K) (x : {n : nat| (n < M)%nat }) (y : {n : nat| (n < K)%nat }) => MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat| (n < N) %nat}) (CountFinite N)) (FPCM f) (fun (n : Count N) => Fmul f (A x n) (B n y)).

Definition Mopp (f : Field) (M N : nat) := fun (A : Matrix f M N) (x : {n : nat| (n < M)%nat }) (y : {n : nat| (n < N)%nat }) => (Fopp f (A x y)).

Definition MO (f : Field) (M N : nat) := fun (x : {n : nat| (n < M)%nat }) (y : {n : nat| (n < N)%nat }) => (FO f).

Definition MI (f : Field) (N : nat) := fun (x : {n : nat| (n < N)%nat }) (y : {n : nat| (n < N)%nat }) => match (Nat.eq_dec (proj1_sig x) (proj1_sig y)) with
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

Lemma Mmult_I_l : forall (f : Field) (M N : nat) (A : Matrix f M N), (Mmult f M N N A (MI f N)) = A.
Proof.
move=> f M N A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
rewrite (MySumF2Excluded {n : nat | (n < N)%nat} (FPCM f) (fun n : Count N => Fmul f (A x n) (MI f N n y)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (fun (m : {n : nat | (n < N)%nat}) => proj1_sig m = proj1_sig y)).
suff: (FiniteIntersection {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (fun m : {n : nat | (n < N)%nat} => proj1_sig m = proj1_sig y)) = FiniteSingleton {n : nat | (n < N)%nat} y.
move=> H1.
rewrite H1.
rewrite MySumF2Singleton.
suff: (MySumF2 {n : nat | (n < N)%nat} (FiniteIntersection {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (Complement {n : nat | (n < N)%nat} (fun m : {n : nat | (n < N)%nat} => proj1_sig m = proj1_sig y))) (FPCM f) (fun n : Count N => Fmul f (A x n) (MI f N n y)) = FO f).
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

Lemma Mmult_I_r : forall (f : Field) (M N : nat) (A : Matrix f M N), (Mmult f M M N (MI f M) A) = A.
Proof.
move=> f M N A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
rewrite (MySumF2Excluded {n : nat | (n < M)%nat} (FPCM f) (fun n : Count M => Fmul f (MI f M x n) (A n y)) (exist (Finite (Count M)) (Full_set {n : nat | (n < M)%nat}) (CountFinite M)) (fun (m : {n : nat | (n < M)%nat}) => proj1_sig m = proj1_sig x)).
suff: (FiniteIntersection {n : nat | (n < M)%nat} (exist (Finite (Count M)) (Full_set {n : nat | (n < M)%nat}) (CountFinite M)) (fun m : {n : nat | (n < M)%nat} => proj1_sig m = proj1_sig x)) = FiniteSingleton {n : nat | (n < M)%nat} x.
move=> H1.
rewrite H1.
rewrite MySumF2Singleton.
suff: (MySumF2 {n : nat | (n < M)%nat} (FiniteIntersection {n : nat | (n < M)%nat} (exist (Finite (Count M)) (Full_set {n : nat | (n < M)%nat}) (CountFinite M)) (Complement {n : nat | (n < M)%nat} (fun m : {n : nat | (n < M)%nat} => proj1_sig m = proj1_sig x))) (FPCM f) (fun n : Count M => Fmul f (MI f M x n) (A n y)) = FO f).
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

Lemma Mmult_assoc : forall (f : Field) (M N K L : nat) (A : Matrix f M N) (B : Matrix f N K) (C : Matrix f K L), (Mmult f M K L (Mmult f M N K A B) C) = (Mmult f M N L A (Mmult f N K L B C)).
Proof.
move=> f M N K L A B C.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (Mmult f M K L (Mmult f M N K A B) C x y = MySumF2 ({n : nat | (n < N)%nat} * {n : nat | (n < K)%nat}) (FinitePair {n : nat | (n < N)%nat} {n : nat | (n < K)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (exist (Finite (Count K)) (Full_set {n : nat | (n < K)%nat}) (CountFinite K))) (FPCM f) (fun (nm : ({n : nat | (n < N)%nat} * {n : nat | (n < K)%nat})) => Fmul f (Fmul f (A x (fst nm)) (B (fst nm) (snd nm))) (C (snd nm) y))).
move=> H1.
rewrite H1.
suff: (Mmult f M N L A (Mmult f N K L B C) x y = MySumF2 ({n : nat | (n < N)%nat} * {n : nat | (n < K)%nat}) (FinitePair {n : nat | (n < N)%nat} {n : nat | (n < K)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (exist (Finite (Count K)) (Full_set {n : nat | (n < K)%nat}) (CountFinite K))) (FPCM f) (fun (nm : ({n : nat | (n < N)%nat} * {n : nat | (n < K)%nat})) => Fmul f (Fmul f (A x (fst nm)) (B (fst nm) (snd nm))) (C (snd nm) y))).
move=> H2.
rewrite H2.
reflexivity.
rewrite (MySumF2Pair {n : nat | (n < N)%nat} {n : nat | (n < K)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (exist (Finite (Count K)) (Full_set {n : nat | (n < K)%nat}) (CountFinite K)) (FPCM f) (fun (n0 : {n : nat | (n < N)%nat}) (k0 : {n : nat | (n < K)%nat}) => Fmul f (Fmul f (A x n0) (B n0 k0)) (C k0 y))).
unfold Mmult.
suff: ((fun n : Count N => Fmul f (A x n) (MySumF2 {n0 : nat | (n0 < K)%nat} (exist (Finite (Count K)) (Full_set {n0 : nat | (n0 < K)%nat}) (CountFinite K)) (FPCM f) (fun n0 : Count K => Fmul f (B n n0) (C n0 y)))) = (fun u : {n : nat | (n < N)%nat} => MySumF2 {n : nat | (n < K)%nat} (exist (Finite (Count K)) (Full_set {n : nat | (n < K)%nat}) (CountFinite K)) (FPCM f) (fun k0 : {n : nat | (n < K)%nat} => Fmul f (Fmul f (A x u) (B u k0)) (C k0 y)))).
move=> H2.
rewrite H2.
reflexivity.
apply functional_extensionality.
move=> k.
apply (FiniteSetInduction (Count K) (exist (Finite (Count K)) (Full_set {n0 : nat | (n0 < K)%nat}) (CountFinite K))).
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
suff: (MySumF2 ({n : nat | (n < N)%nat} * {n : nat | (n < K)%nat}) (FinitePair {n : nat | (n < N)%nat} {n : nat | (n < K)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (exist (Finite (Count K)) (Full_set {n : nat | (n < K)%nat}) (CountFinite K))) (FPCM f) (fun nm : {n : nat | (n < N)%nat} * {n : nat | (n < K)%nat} => Fmul f (Fmul f (A x (fst nm)) (B (fst nm) (snd nm))) (C (snd nm) y)) = MySumF2 ({n : nat | (n < K)%nat} * {n : nat | (n < N)%nat}) (FinitePair {n : nat | (n < K)%nat} {n : nat | (n < N)%nat} (exist (Finite (Count K)) (Full_set {n : nat | (n < K)%nat}) (CountFinite K)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))) (FPCM f) (fun nm : {n : nat | (n < K)%nat} * {n : nat | (n < N)%nat} => Fmul f (Fmul f (A x (snd nm)) (B (snd nm) (fst nm))) (C (fst nm) y))).
move=> H2.
rewrite H2.
unfold Mmult.
rewrite (MySumF2Pair {n : nat | (n < K)%nat} {n : nat | (n < N)%nat} (exist (Finite (Count K)) (Full_set {n : nat | (n < K)%nat}) (CountFinite K)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FPCM f) (fun (n0 : {n : nat | (n < K)%nat}) (k0 : {n : nat | (n < N)%nat}) => Fmul f (Fmul f (A x k0) (B k0 n0)) (C n0 y))).
suff: ((fun n : Count K => Fmul f (MySumF2 {n0 : nat | (n0 < N)%nat} (exist (Finite (Count N)) (Full_set {n0 : nat | (n0 < N)%nat}) (CountFinite N)) (FPCM f) (fun n0 : Count N => Fmul f (A x n0) (B n0 n))) (C n y)) = (fun u : {n : nat | (n < K)%nat} => MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FPCM f) (fun k0 : {n : nat | (n < N)%nat} => Fmul f (Fmul f (A x k0) (B k0 u)) (C u y)))).
move=> H3.
rewrite H3.
reflexivity.
apply functional_extensionality.
move=> k.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (Full_set {n0 : nat | (n0 < N)%nat}) (CountFinite N))).
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
suff: (forall u : ({n : nat | (n < N)%nat} * {n : nat | (n < K)%nat}), proj1_sig (FinitePair {n : nat | (n < N)%nat} {n : nat | (n < K)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (exist (Finite (Count K)) (Full_set {n : nat | (n < K)%nat}) (CountFinite K))) u -> proj1_sig (FinitePair {n : nat | (n < K)%nat} {n : nat | (n < N)%nat} (exist (Finite (Count K)) (Full_set {n : nat | (n < K)%nat}) (CountFinite K)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))) ((fun nm : {n : nat | (n < N)%nat} * {n : nat | (n < K)%nat} => (snd nm, fst nm)) u)).
move=> H1.
rewrite - (MySumF2BijectiveSame ({n : nat | (n < N)%nat} * {n : nat | (n < K)%nat}) (FinitePair {n : nat | (n < N)%nat} {n : nat | (n < K)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (exist (Finite (Count K)) (Full_set {n : nat | (n < K)%nat}) (CountFinite K))) ({n : nat | (n < K)%nat} * {n : nat | (n < N)%nat}) (FinitePair {n : nat | (n < K)%nat} {n : nat | (n < N)%nat} (exist (Finite (Count K)) (Full_set {n : nat | (n < K)%nat}) (CountFinite K)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))) (FPCM f) (fun nm : {n : nat | (n < K)%nat} * {n : nat | (n < N)%nat} => Fmul f (Fmul f (A x (snd nm)) (B (snd nm) (fst nm))) (C (fst nm) y)) (fun (nm : {n : nat | (n < N)%nat} * {n : nat | (n < K)%nat}) => (snd nm, fst nm)) H1).
reflexivity.
simpl.
suff: (forall u : ({n : nat | (n < K)%nat} * {n : nat | (n < N)%nat}), proj1_sig (FinitePair {n : nat | (n < K)%nat} {n : nat | (n < N)%nat} (exist (Finite (Count K)) (Full_set {n : nat | (n < K)%nat}) (CountFinite K)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))) u -> proj1_sig (FinitePair {n : nat | (n < N)%nat} {n : nat | (n < K)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (exist (Finite (Count K)) (Full_set {n : nat | (n < K)%nat}) (CountFinite K))) ((fun nm : {n : nat | (n < K)%nat} * {n : nat | (n < N)%nat} => (snd nm, fst nm)) u)).
move=> H2.
exists (fun u : {u : {n : nat | (n < K)%nat} * {n : nat | (n < N)%nat} | Full_set {n : nat | (n < K)%nat} (fst u) /\ Full_set {n : nat | (n < N)%nat} (snd u)} => exist (fun uv : {n : nat | (n < N)%nat} * {n : nat | (n < K)%nat} => Full_set {n : nat | (n < N)%nat} (fst uv) /\ Full_set {n : nat | (n < K)%nat} (snd uv)) (snd (proj1_sig u), fst (proj1_sig u)) (H2 (proj1_sig u) (proj2_sig u))).
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
apply (FiniteSetInduction {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
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
rewrite - (Fadd_assoc f (Fadd f (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (B n y))) (Fmul f (A x b0) (B b0 y))) (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y))) (Fmul f (A x b0) (C b0 y))).
rewrite (Fadd_assoc f (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (B n y))) (Fmul f (A x b0) (B b0 y)) (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y)))).
rewrite (Fadd_comm f (Fmul f (A x b0) (B b0 y)) (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y)))).
rewrite - (Fadd_assoc f (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (B n y))) (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y))) (Fmul f (A x b0) (B b0 y))).
rewrite (Fadd_assoc f (Fadd f (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (B n y))) (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y)))) (Fmul f (A x b0) (B b0 y)) (Fmul f (A x b0) (C b0 y))).
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
apply (FiniteSetInduction {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
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
rewrite - (Fadd_assoc f (Fadd f (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y))) (Fmul f (A x b0) (C b0 y))) (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (B x n) (C n y))) (Fmul f (B x b0) (C b0 y))).
rewrite (Fadd_assoc f (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y))) (Fmul f (A x b0) (C b0 y)) (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (B x n) (C n y)))).
rewrite (Fadd_comm f (Fmul f (A x b0) (C b0 y)) (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (B x n) (C n y)))).
rewrite - (Fadd_assoc f (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y))) (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (B x n) (C n y))) (Fmul f (A x b0) (C b0 y))).
rewrite (Fadd_assoc f (Fadd f (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (A x n) (C n y))) (MySumF2 {n : nat | (n < N)%nat} B0 (FPCM f) (fun n : Count N => Fmul f (B x n) (C n y)))) (Fmul f (A x b0) (C b0 y)) (Fmul f (B x b0) (C b0 y))).
rewrite (Fmul_add_distr_r f).
reflexivity.
apply H3.
apply H3.
apply H3.
Qed.

Definition VMmult (f : Field) (M N : nat) := fun (c : FT f) (A : Matrix f M N) (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => (Fmul f c (A x y)).

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

Lemma VMmult_I_l : forall (f : Field) (M N : nat) (A : Matrix f M N), (VMmult f M N (FI f) A) = A.
Proof.
move=> f M N A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply Fmul_I_l.
Qed.

Definition MTranspose (f : Field) (M N : nat) := fun (A : Matrix f M N) (x : {n : nat | (n < N)%nat}) (y : {n : nat | (n < M)%nat}) => A y x.

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

Lemma blockdividesub : forall (m1 m2 : nat) (x : {n : nat | (n < m1 + m2)%nat}), (m1 <= proj1_sig x)%nat -> {y : {n : nat | (n < m2)%nat} | (m1 + proj1_sig y = proj1_sig x)%nat}.
Proof.
move=> m1 m2 x H1.
suff: ((proj1_sig x - m1) < m2)%nat.
move=> H2.
exists (exist (fun n : nat => (n < m2)%nat) (proj1_sig x - m1)%nat H2).
unfold proj1_sig at 1.
apply (le_plus_minus_r m1 (proj1_sig x) H1).
apply (plus_lt_reg_l (proj1_sig x - m1)%nat m2 m1).
rewrite (le_plus_minus_r m1 (proj1_sig x) H1).
apply (proj2_sig x).
Qed.

Definition MBlockH := fun (f : Field) (M1 M2 N : nat) (A1 : Matrix f M1 N) (A2 : Matrix f M2 N) (x : {n : nat | (n < M1 + M2)%nat}) (y : {n : nat | (n < N)%nat}) => match (le_lt_dec M1 (proj1_sig x)) with
  | left a => A2 (proj1_sig (blockdividesub M1 M2 x a)) y
  | right b => A1 (exist (fun (n : nat) => (n < M1)%nat) (proj1_sig x) b) y
end.

Definition MBlockW := fun (f : Field) (M N1 N2 : nat) (A1 : Matrix f M N1) (A2 : Matrix f M N2) (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N1 + N2)%nat}) => match (le_lt_dec N1 (proj1_sig y)) with
  | left a => A2 x (proj1_sig (blockdividesub N1 N2 y a))
  | right b => A1 x (exist (fun (n : nat) => (n < N1)%nat) (proj1_sig y) b)
end.

Lemma MBlockHPlus : forall (f : Field) (M1 M2 N : nat) (A1 B1 : Matrix f M1 N) (A2 B2 : Matrix f M2 N), Mplus f (M1 + M2)%nat N (MBlockH f M1 M2 N A1 A2) (MBlockH f M1 M2 N B1 B2) = MBlockH f M1 M2 N (Mplus f M1 N A1 B1) (Mplus f M2 N A2 B2).
Proof.
move=> f M1 M2 N A1 B1 A2 B2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mplus.
unfold MBlockH.
elim (le_lt_dec M1 (proj1_sig x)).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockWPlus : forall (f : Field) (M N1 N2 : nat) (A1 B1 : Matrix f M N1) (A2 B2 : Matrix f M N2), Mplus f M (N1 + N2)%nat (MBlockW f M N1 N2 A1 A2) (MBlockW f M N1 N2 B1 B2) = MBlockW f M N1 N2 (Mplus f M N1 A1 B1) (Mplus f M N2 A2 B2).
Proof.
move=> f M N1 N2 A1 B1 A2 B2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mplus.
unfold MBlockW.
elim (le_lt_dec N1 (proj1_sig y)).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockHOpp : forall (f : Field) (M1 M2 N : nat) (A1 : Matrix f M1 N) (A2 : Matrix f M2 N), Mopp f (M1 + M2)%nat N (MBlockH f M1 M2 N A1 A2) = MBlockH f M1 M2 N (Mopp f M1 N A1) (Mopp f M2 N A2).
Proof.
move=> f M1 M2 N A1 A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mopp.
unfold MBlockH.
elim (le_lt_dec M1 (proj1_sig x)).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockWOpp : forall (f : Field) (M N1 N2 : nat) (A1 : Matrix f M N1) (A2 : Matrix f M N2), Mopp f M (N1 + N2)%nat (MBlockW f M N1 N2 A1 A2) = MBlockW f M N1 N2 (Mopp f M N1 A1) (Mopp f M N2 A2).
Proof.
move=> f M N1 N2 A1 A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mopp.
unfold MBlockW.
elim (le_lt_dec N1 (proj1_sig y)).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockHMult : forall (f : Field) (M1 M2 N K : nat) (A1 : Matrix f M1 N) (A2 : Matrix f M2 N) (B : Matrix f N K), Mmult f (M1 + M2)%nat N K (MBlockH f M1 M2 N A1 A2) B = MBlockH f M1 M2 K (Mmult f M1 N K A1 B) (Mmult f M2 N K A2 B).
Proof.
move=> f M1 M2 N K A1 A2 B.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
unfold MBlockH.
elim (le_lt_dec M1 (proj1_sig x)).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockWMult : forall (f : Field) (M N K1 K2 : nat) (A : Matrix f M N) (B1 : Matrix f N K1) (B2 : Matrix f N K2), Mmult f M N (K1 + K2)%nat A (MBlockW f N K1 K2 B1 B2) = MBlockW f M K1 K2 (Mmult f M N K1 A B1) (Mmult f M N K2 A B2).
Proof.
move=> f M N K1 K2 A B1 B2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
unfold MBlockW.
elim (le_lt_dec K1 (proj1_sig y)).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockHWMult : forall (f : Field) (M N1 N2 K : nat) (A1 : Matrix f M N1) (A2 : Matrix f M N2) (B1 : Matrix f N1 K) (B2 : Matrix f N2 K), Mmult f M (N1 + N2)%nat K (MBlockW f M N1 N2 A1 A2) (MBlockH f N1 N2 K B1 B2) = Mplus f M K (Mmult f M N1 K A1 B1) (Mmult f M N2 K A2 B2).
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
rewrite (MySumF2Excluded {n : nat | (n < N1 + N2)%nat} (FPCM f) (fun n : Count (N1 + N2) => Fmul f match le_lt_dec N1 (proj1_sig n) with
  | left a => A2 x (proj1_sig (blockdividesub N1 N2 n a))
  | right b => A1 x (exist (fun n0 : nat => (n0 < N1)%nat) (proj1_sig n) b)
end match le_lt_dec N1 (proj1_sig n) with
  | left a => B2 (proj1_sig (blockdividesub N1 N2 n a)) y
  | right b => B1 (exist (fun n0 : nat => (n0 < N1)%nat) (proj1_sig n) b) y
end) (exist (Finite (Count (N1 + N2))) (Full_set {n : nat | (n < N1 + N2)%nat}) (CountFinite (N1 + N2))) (fun (m : {n : nat | (n < N1 + N2)%nat}) => (proj1_sig m < N1)%nat)).
suff: ((MySumF2 {n : nat | (n < N1 + N2)%nat} (FiniteIntersection {n : nat | (n < N1 + N2)%nat} (exist (Finite (Count (N1 + N2))) (Full_set {n : nat | (n < N1 + N2)%nat}) (CountFinite (N1 + N2))) (fun m : {n : nat | (n < N1 + N2)%nat} => (proj1_sig m < N1)%nat)) (FPCM f) (fun n : Count (N1 + N2) => Fmul f match le_lt_dec N1 (proj1_sig n) with
  | left a => A2 x (proj1_sig (blockdividesub N1 N2 n a))
  | right b => A1 x (exist (fun n0 : nat => (n0 < N1)%nat) (proj1_sig n) b)
end match le_lt_dec N1 (proj1_sig n) with
  | left a => B2 (proj1_sig (blockdividesub N1 N2 n a)) y
  | right b => B1 (exist (fun n0 : nat => (n0 < N1)%nat) (proj1_sig n) b) y
end)) = (MySumF2 {n : nat | (n < N1)%nat} (exist (Finite (Count N1)) (Full_set {n : nat | (n < N1)%nat}) (CountFinite N1)) (FPCM f) (fun n : Count N1 => Fmul f (A1 x n) (B1 n y)))).
move=> H1.
rewrite H1.
suff: ((MySumF2 {n : nat | (n < N1 + N2)%nat} (FiniteIntersection {n : nat | (n < N1 + N2)%nat} (exist (Finite (Count (N1 + N2))) (Full_set {n : nat | (n < N1 + N2)%nat}) (CountFinite (N1 + N2))) (Complement {n : nat | (n < N1 + N2)%nat} (fun m : {n : nat | (n < N1 + N2)%nat} => (proj1_sig m < N1)%nat))) (FPCM f) (fun n : Count (N1 + N2) => Fmul f match le_lt_dec N1 (proj1_sig n) with
  | left a => A2 x (proj1_sig (blockdividesub N1 N2 n a))
  | right b => A1 x (exist (fun n0 : nat => (n0 < N1)%nat) (proj1_sig n) b)
end match le_lt_dec N1 (proj1_sig n) with
  | left a => B2 (proj1_sig (blockdividesub N1 N2 n a)) y
  | right b => B1 (exist (fun n0 : nat => (n0 < N1)%nat) (proj1_sig n) b) y
end)) = (MySumF2 {n : nat | (n < N2)%nat} (exist (Finite (Count N2)) (Full_set {n : nat | (n < N2)%nat}) (CountFinite N2)) (FPCM f) (fun n : Count N2 => Fmul f (A2 x n) (B2 n y)))).
move=> H2.
rewrite H2.
reflexivity.
suff: (forall (u : {n : nat | (n < N2)%nat}), (N1 + proj1_sig u < N1 + N2)%nat).
move=> H2.
suff: (forall (u : {n : nat | (n < N2)%nat}), proj1_sig (exist (Finite (Count N2)) (Full_set {n : nat | (n < N2)%nat}) (CountFinite N2)) u -> proj1_sig (FiniteIntersection {n : nat | (n < N1 + N2)%nat} (exist (Finite (Count (N1 + N2))) (Full_set {n : nat | (n < N1 + N2)%nat}) (CountFinite (N1 + N2))) (Complement {n : nat | (n < N1 + N2)%nat} (fun m : {n : nat | (n < N1 + N2)%nat} => (proj1_sig m < N1)%nat))) ((fun (u1 : {n : nat | (n < N2)%nat}) => (exist (fun (n : nat) => (n < N1 + N2)%nat) (N1 + proj1_sig u1)%nat (H2 u1))) u)).
move=> H3.
rewrite - (MySumF2BijectiveSame {n : nat | (n < N2)%nat} (exist (Finite (Count N2)) (Full_set {n : nat | (n < N2)%nat}) (CountFinite N2)) {n : nat | (n < N1 + N2)%nat} (FiniteIntersection {n : nat | (n < N1 + N2)%nat} (exist (Finite (Count (N1 + N2))) (Full_set {n : nat | (n < N1 + N2)%nat}) (CountFinite (N1 + N2))) (Complement {n : nat | (n < N1 + N2)%nat} (fun m : {n : nat | (n < N1 + N2)%nat} => (proj1_sig m < N1)%nat))) (FPCM f) (fun n : Count (N1 + N2) => Fmul f match le_lt_dec N1 (proj1_sig n) with
  | left a => A2 x (proj1_sig (blockdividesub N1 N2 n a))
  | right b => A1 x (exist (fun n0 : nat => (n0 < N1)%nat) (proj1_sig n) b)
end match le_lt_dec N1 (proj1_sig n) with
  | left a => B2 (proj1_sig (blockdividesub N1 N2 n a)) y
  | right b => B1 (exist (fun n0 : nat => (n0 < N1)%nat) (proj1_sig n) b) y
end) (fun (u1 : {n : nat | (n < N2)%nat}) => (exist (fun (n : nat) => (n < N1 + N2)%nat) (N1 + proj1_sig u1)%nat (H2 u1))) H3).
apply (MySumF2Same {n : nat | (n < N2)%nat} (exist (Finite (Count N2)) (Full_set {n : nat | (n < N2)%nat}) (CountFinite N2)) (FPCM f)).
simpl.
move=> u H4.
elim (le_lt_dec N1 (N1 + proj1_sig u)).
move=> H5.
suff: (u = (proj1_sig (blockdividesub N1 N2 (exist (fun n : nat => (n < N1 + N2)%nat) (N1 + proj1_sig u)%nat (H2 u)) H5))).
move=> H6.
rewrite {7} H6.
rewrite {11} H6.
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig u) (proj1_sig (proj1_sig (blockdividesub N1 N2 (exist (fun n : nat => (n < N1 + N2)%nat) (N1 + proj1_sig u)%nat (H2 u)) H5))) N1).
rewrite (proj2_sig (blockdividesub N1 N2 (exist (fun n : nat => (n < N1 + N2)%nat) (N1 + proj1_sig u)%nat (H2 u)) H5)).
reflexivity.
move=> H5.
apply False_ind.
apply (lt_not_le (N1 + proj1_sig u)%nat N1 H5).
rewrite - {1} (plus_0_r N1).
apply (plus_le_compat_l 0 (proj1_sig u) N1 (le_0_n (proj1_sig u))).
simpl.
suff: (forall (x : {u : {n : nat | (n < N1 + N2)%nat} | Intersection {n : nat | (n < N1 + N2)%nat} (Complement {n : nat | (n < N1 + N2)%nat} (fun m : {n : nat | (n < N1 + N2)%nat} => (proj1_sig m < N1)%nat)) (Full_set {n : nat | (n < N1 + N2)%nat}) u}), (proj1_sig (proj1_sig x) - N1 < N2)%nat).
move=> H4.
suff: (forall (x : {u : {n : nat | (n < N1 + N2)%nat} | Intersection {n : nat | (n < N1 + N2)%nat} (Complement {n : nat | (n < N1 + N2)%nat} (fun m : {n : nat | (n < N1 + N2)%nat} => (proj1_sig m < N1)%nat)) (Full_set {n : nat | (n < N1 + N2)%nat}) u}), Full_set {n : nat | (n < N2)%nat} (exist (fun (n : nat) => (n < N2)%nat) (proj1_sig (proj1_sig x) - N1)%nat (H4 x))).
move=> H5.
exists (fun (x : {u : {n : nat | (n < N1 + N2)%nat} | Intersection {n : nat | (n < N1 + N2)%nat} (Complement {n : nat | (n < N1 + N2)%nat} (fun m : {n : nat | (n < N1 + N2)%nat} => (proj1_sig m < N1)%nat)) (Full_set {n : nat | (n < N1 + N2)%nat}) u}) => exist (fun (u : {n : nat | (n < N2)%nat}) => Full_set {n : nat | (n < N2)%nat} u) (exist (fun (n : nat) => (n < N2)%nat) (proj1_sig (proj1_sig x) - N1)%nat (H4 x)) (H5 x)).
apply conj.
move=> x0.
apply sig_map.
simpl.
apply sig_map.
simpl.
apply (minus_plus N1 (proj1_sig (proj1_sig x0))).
move=> y0.
apply sig_map.
simpl.
apply sig_map.
simpl.
apply (le_plus_minus_r N1 (proj1_sig (proj1_sig y0))).
elim (le_or_lt N1 (proj1_sig (proj1_sig y0))%nat).
apply.
elim (proj2_sig y0).
move=> y1 H6 H7 H8.
apply False_ind.
apply (H6 H8).
move=> x0.
apply (Full_intro {n : nat | (n < N2)%nat} (exist (fun n : nat => (n < N2)%nat) (proj1_sig (proj1_sig x0) - N1)%nat (H4 x0))).
move=> x0.
apply (plus_lt_reg_l (proj1_sig (proj1_sig x0) - N1) N2 N1).
rewrite (le_plus_minus_r N1 (proj1_sig (proj1_sig x0))).
apply (proj2_sig (proj1_sig x0)).
elim (le_or_lt N1 (proj1_sig (proj1_sig x0))%nat).
apply.
elim (proj2_sig x0).
move=> x1 H4 H5 H6.
apply False_ind.
apply (H4 H6).
move=> u H3.
unfold FiniteIntersection.
simpl.
apply (Intersection_intro {n : nat | (n < N1 + N2)%nat}).
apply (le_not_lt N1 (N1 + proj1_sig u)).
rewrite - {1} (plus_0_r N1).
apply (plus_le_compat_l 0 (proj1_sig u) N1 (le_0_n (proj1_sig u))).
apply (Full_intro {n : nat | (n < N1 + N2)%nat}).
move=> u.
apply (plus_lt_compat_l (proj1_sig u) N2 N1).
apply (proj2_sig u).
suff: (forall (u : {n : nat | (n < N1)%nat}), (proj1_sig u < N1 + N2)%nat).
move=> H1.
suff: (forall (u : {n : nat | (n < N1)%nat}), proj1_sig (exist (Finite (Count N1)) (Full_set {n : nat | (n < N1)%nat}) (CountFinite N1)) u -> proj1_sig (FiniteIntersection {n : nat | (n < N1 + N2)%nat} (exist (Finite (Count (N1 + N2))) (Full_set {n : nat | (n < N1 + N2)%nat}) (CountFinite (N1 + N2))) (fun m : {n : nat | (n < N1 + N2)%nat} => (proj1_sig m < N1)%nat)) ((fun (u1 : {n : nat | (n < N1)%nat}) => (exist (fun (n : nat) => (n < N1 + N2)%nat) (proj1_sig u1)%nat (H1 u1))) u)).
move=> H2.
rewrite - (MySumF2BijectiveSame {n : nat | (n < N1)%nat} (exist (Finite (Count N1)) (Full_set {n : nat | (n < N1)%nat}) (CountFinite N1)) {n : nat | (n < N1 + N2)%nat} (FiniteIntersection {n : nat | (n < N1 + N2)%nat} (exist (Finite (Count (N1 + N2))) (Full_set {n : nat | (n < N1 + N2)%nat}) (CountFinite (N1 + N2))) (fun m : {n : nat | (n < N1 + N2)%nat} => (proj1_sig m < N1)%nat)) (FPCM f) (fun n : Count (N1 + N2) => Fmul f match le_lt_dec N1 (proj1_sig n) with
  | left a => A2 x (proj1_sig (blockdividesub N1 N2 n a))
  | right b => A1 x (exist (fun n0 : nat => (n0 < N1)%nat) (proj1_sig n) b)
end match le_lt_dec N1 (proj1_sig n) with
  | left a => B2 (proj1_sig (blockdividesub N1 N2 n a)) y
  | right b => B1 (exist (fun n0 : nat => (n0 < N1)%nat) (proj1_sig n) b) y
end) (fun (u1 : {n : nat | (n < N1)%nat}) => (exist (fun (n : nat) => (n < N1 + N2)%nat) (proj1_sig u1)%nat (H1 u1))) H2).
apply (MySumF2Same {n : nat | (n < N1)%nat} (exist (Finite (Count N1)) (Full_set {n : nat | (n < N1)%nat}) (CountFinite N1)) (FPCM f)).
simpl.
move=> u H3.
elim (le_lt_dec N1 (proj1_sig u)).
move=> H4.
apply False_ind.
apply (lt_not_le (proj1_sig u) N1 (proj2_sig u) H4).
move=> H4.
suff: (u = (exist (fun n0 : nat => (n0 < N1)%nat) (proj1_sig u) H4)).
move=> H5.
rewrite {3} H5.
rewrite {4} H5.
reflexivity.
apply sig_map.
reflexivity.
simpl.
suff: (forall (x : {u : {n : nat | (n < N1 + N2)%nat} | Intersection {n : nat | (n < N1 + N2)%nat} (fun m : {n : nat | (n < N1 + N2)%nat} => (proj1_sig m < N1)%nat) (Full_set {n : nat | (n < N1 + N2)%nat}) u}), (proj1_sig (proj1_sig x) < N1)%nat).
move=> H3.
suff: (forall (x : {u : {n : nat | (n < N1 + N2)%nat} | Intersection {n : nat | (n < N1 + N2)%nat} (fun m : {n : nat | (n < N1 + N2)%nat} => (proj1_sig m < N1)%nat) (Full_set {n : nat | (n < N1 + N2)%nat}) u}), Full_set {n : nat | (n < N1)%nat} (exist (fun (n : nat) => (n < N1)%nat) (proj1_sig (proj1_sig x))%nat (H3 x))).
move=> H4.
exists (fun (x : {u : {n : nat | (n < N1 + N2)%nat} | Intersection {n : nat | (n < N1 + N2)%nat} (fun m : {n : nat | (n < N1 + N2)%nat} => (proj1_sig m < N1)%nat) (Full_set {n : nat | (n < N1 + N2)%nat}) u}) => exist (fun (u : {n : nat | (n < N1)%nat}) => Full_set {n : nat | (n < N1)%nat} u) (exist (fun (n : nat) => (n < N1)%nat) (proj1_sig (proj1_sig x))%nat (H3 x)) (H4 x)).
apply conj.
move=> x0.
apply sig_map.
simpl.
apply sig_map.
simpl.
reflexivity.
move=> y0.
apply sig_map.
simpl.
apply sig_map.
simpl.
reflexivity.
move=> x0.
apply (Full_intro {n : nat | (n < N1)%nat} (exist (fun n : nat => (n < N1)%nat) (proj1_sig (proj1_sig x0)) (H3 x0))).
move=> x0.
elim (proj2_sig x0).
move=> x1 H3 H4.
apply H3.
simpl.
move=> u H2.
apply (Intersection_intro {n : nat | (n < N1 + N2)%nat}).
apply (proj2_sig u).
apply (Full_intro {n : nat | (n < N1 + N2)%nat} (exist (fun n : nat => (n < N1 + N2)%nat) (proj1_sig u) (H1 u))).
move=> u.
apply (lt_le_trans (proj1_sig u) N1 (N1 + N2)%nat (proj2_sig u)).
rewrite - {1} (plus_0_r N1).
apply (plus_le_compat_l 0 N2 N1 (le_0_n N2)).
Qed.

Lemma MBlockHVMult : forall (f : Field) (M1 M2 N : nat) (c : FT f) (A1 : Matrix f M1 N) (A2 : Matrix f M2 N), VMmult f (M1 + M2)%nat N c (MBlockH f M1 M2 N A1 A2) = MBlockH f M1 M2 N (VMmult f M1 N c A1) (VMmult f M2 N c A2).
Proof.
move=> f M1 M2 N c A1 A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold VMmult.
unfold MBlockH.
elim (le_lt_dec M1 (proj1_sig x)).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockWVMult : forall (f : Field) (M N1 N2 : nat) (c : FT f) (A1 : Matrix f M N1) (A2 : Matrix f M N2), VMmult f M (N1 + N2)%nat c (MBlockW f M N1 N2 A1 A2) = MBlockW f M N1 N2 (VMmult f M N1 c A1) (VMmult f M N2 c A2).
Proof.
move=> f M N1 N2 c A1 A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold VMmult.
unfold MBlockW.
elim (le_lt_dec N1 (proj1_sig y)).
move=> H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma MBlockHTranspose : forall (f : Field) (M1 M2 N : nat) (A1 : Matrix f M1 N) (A2 : Matrix f M2 N), MTranspose f (M1 + M2)%nat N (MBlockH f M1 M2 N A1 A2) = MBlockW f N M1 M2 (MTranspose f M1 N A1) (MTranspose f M2 N A2).
Proof.
move=> f M1 M2 N A1 A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
reflexivity.
Qed.

Lemma MBlockWTranspose : forall (f : Field) (M N1 N2 : nat) (A1 : Matrix f M N1) (A2 : Matrix f M N2), MTranspose f M (N1 + N2)%nat (MBlockW f M N1 N2 A1 A2) = MBlockH f N1 N2 M (MTranspose f M N1 A1) (MTranspose f M N2 A2).
Proof.
move=> f M N1 N2 A1 A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
reflexivity.
Qed.

Definition Determinant (f : Field) (N : nat) (A : Matrix f N N) := MySumF2 (Permutation N) (exist (Finite (Permutation N)) (Full_set (Permutation N)) (PermutationFinite N)) (FPCM f) (fun (P : Permutation N) => Fmul f (match PermutationParity N P with
  | OFF => (FI f)
  | ON => Fopp f (FI f)
end) (MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat| (n < N) %nat}) (CountFinite N)) (FMCM f) (fun (k : {n : nat | (n < N)%nat}) => A k (proj1_sig P k)))).

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
suff: (exists (k : {n : nat | (n < N)%nat}), k <> proj1_sig u k).
elim.
move=> k H2.
rewrite (MySumF2Included {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} k) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f)).
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
apply (Full_intro {n : nat | (n < N)%nat} l).
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
suff: ((N > O)%nat).
move=> H3.
rewrite (MySumF2Included {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} (exist (fun (k : nat) => (k < N)%nat) O H3))).
rewrite MySumF2Singleton.
unfold MO.
simpl.
rewrite (Fmul_O_l f).
apply (Fmul_O_r f).
move=> k H4.
apply (Full_intro {n : nat | (n < N)%nat} k).
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
end (MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)%nat} => A k (proj1_sig P k)))) = (fun x : Permutation N => Fmul f match PermutationParity N (PermutationInv N x) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)%nat} => MTranspose f N N A k (proj1_sig (PermutationInv N x) k))))).
move=> H2.
rewrite H2.
reflexivity.
apply functional_extensionality.
move=> k.
unfold MTranspose.
rewrite (PermutationInvParity N k).
suff: ((exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) = FiniteIm {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig (PermutationInv N k)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
move=> H2.
rewrite {1} H2.
rewrite - (MySumF2BijectiveSame2 {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (proj1_sig (PermutationInv N k))).
unfold Basics.compose.
suff: ((fun (l : {n : nat | (n < N)%nat}) => A (proj1_sig (PermutationInv N k) l) (proj1_sig k (proj1_sig (PermutationInv N k) l))) = (fun (l : {n : nat | (n < N)%nat}) => A (proj1_sig (PermutationInv N k) l) l)).
move=> H3.
rewrite H3.
reflexivity.
apply functional_extensionality.
move=> l.
unfold PermutationInv at 2.
simpl.
rewrite (proj2 (proj2_sig (BijectiveInvExist {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig k) (proj2_sig k))) l).
reflexivity.
move=> u1 u2 H3 H4.
apply (BijInj {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig (PermutationInv N k)) (proj2_sig (PermutationInv N k))).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> m H2.
apply (Im_intro {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (Full_set {n : nat | (n < N)%nat}) (proj1_sig (PermutationInv N k)) (proj1_sig k m)).
apply (Full_intro {n : nat | (n < N)%nat} (proj1_sig k m)).
unfold PermutationInv.
simpl.
rewrite (proj1 (proj2_sig (BijectiveInvExist {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig k) (proj2_sig k))) m).
reflexivity.
move=> m H2.
apply (Full_intro {n : nat | (n < N)%nat} m).
unfold PermutationInv.
move=> u1 u2 H2 H3 H4.
apply sig_map.
apply functional_extensionality.
move=> l.
apply (BijInj {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig (BijectiveInvExist {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig u1) (proj2_sig u1)))).
apply (PermutationInvSub N u1).
rewrite (proj1 (proj2_sig (BijectiveInvExist {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig u1) (proj2_sig u1))) l).
suff: (proj1_sig (BijectiveInvExist {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig u1) (proj2_sig u1)) = proj1_sig (exist (fun f : {n : nat | (n < N)%nat} -> {n : nat | (n < N)%nat} => Bijective f) (proj1_sig (BijectiveInvExist {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig u1) (proj2_sig u1))) (PermutationInvSub N u1))).
move=> H5.
rewrite H5.
rewrite H4.
simpl.
rewrite (proj1 (proj2_sig (BijectiveInvExist {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig u2) (proj2_sig u2))) l).
reflexivity.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> p H1.
apply (Im_intro (Permutation N) (Permutation N) (Full_set (Permutation N)) (PermutationInv N) (PermutationInv N p)).
apply (Full_intro (Permutation N) (PermutationInv N p)).
apply sig_map.
apply (InvUnique {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig (PermutationInv N p))).
apply conj.
apply (proj2 (proj2_sig (BijectiveInvExist {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig p) (proj2_sig p)))).
apply (proj1 (proj2_sig (BijectiveInvExist {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig p) (proj2_sig p)))).
apply (proj2_sig (BijectiveInvExist {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig (exist (fun f0 : {n : nat | (n < N)%nat} -> {n : nat | (n < N)%nat} => Bijective f0) (proj1_sig (BijectiveInvExist {n : nat | (n < N)%nat} {n : nat | (n < N)%nat} (proj1_sig p) (proj2_sig p))) (PermutationInvSub N p))) (proj2_sig (PermutationInv N p)))).
move=> k H1.
apply (Full_intro (Permutation N) k).
Qed.

Lemma DeterminantMultiLinearityHPlus : forall (f : Field) (N : nat) (A : Matrix f N N) (p : {n : nat | (n < N)%nat}) (b : {n : nat | (n < N)%nat} -> FT f), Determinant f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => Fadd f (A x y) (b y)
  | right _ => A x y
end) = Fadd f (Determinant f N A) (Determinant f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
  | left _ => (b y)
  | right _ => A x y
end)).
Proof.
move=> f N A p b.
unfold Determinant.
apply (MySumF2Distr (Permutation N) (FPCM f)).
move=> u H1.
simpl.
suff: ((MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)%nat} => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => Fadd f (A k (proj1_sig u k)) (b (proj1_sig u k))
  | right _ => A k (proj1_sig u k)
end)) = Fadd f (MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)%nat} => A k (proj1_sig u k))) (MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)%nat} => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => b (proj1_sig u k)
  | right _ => A k (proj1_sig u k)
end))).
move=> H2.
rewrite H2.
apply (Fmul_add_distr_l f).
rewrite (MySumF2Included {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} p) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
rewrite (MySumF2Included {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} p) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
rewrite (MySumF2Included {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} p) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
elim (Nat.eq_dec (proj1_sig p) (proj1_sig p)).
move=> H2.
simpl.
suff: ((MySumF2 {n : nat | (n < N)%nat} (FiniteIntersection {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (Complement {n : nat | (n < N)%nat} (Singleton {n : nat | (n < N)%nat} p))) (FMCM f) (fun (k : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => Fadd f (A k (proj1_sig u k)) (b (proj1_sig u k))
  | right _ => A k (proj1_sig u k)
end)) = (MySumF2 {n : nat | (n < N)%nat} (FiniteIntersection {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (Complement {n : nat | (n < N)%nat} (Singleton {n : nat | (n < N)%nat} p))) (FMCM f) (fun (k : {n : nat | (n < N)%nat}) => A k (proj1_sig u k)))).
move=> H3.
rewrite H3.
suff: ((MySumF2 {n : nat | (n < N)%nat} (FiniteIntersection {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (Complement {n : nat | (n < N)%nat} (Singleton {n : nat | (n < N)%nat} p))) (FMCM f) (fun (k : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => b (proj1_sig u k)
  | right _ => A k (proj1_sig u k)
end)) = (MySumF2 {n : nat | (n < N)%nat} (FiniteIntersection {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (Complement {n : nat | (n < N)%nat} (Singleton {n : nat | (n < N)%nat} p))) (FMCM f) (fun (k : {n : nat | (n < N)%nat}) => A k (proj1_sig u k)))).
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
apply (Full_intro {n : nat | (n < N)%nat} k).
move=> k H2.
apply (Full_intro {n : nat | (n < N)%nat} k).
move=> k H2.
apply (Full_intro {n : nat | (n < N)%nat} k).
Qed.

Lemma DeterminantMultiLinearityWPlus : forall (f : Field) (N : nat) (A : Matrix f N N) (p : {n : nat | (n < N)%nat}) (b : {n : nat | (n < N)%nat} -> FT f), Determinant f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => Fadd f (A x y) (b x)
  | right _ => A x y
end) = Fadd f (Determinant f N A) (Determinant f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => b x
  | right _ => A x y
end)).
Proof.
move=> f N A p b.
rewrite - (DeterminantTrans f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => Fadd f (A x y) (b x)
  | right _ => A x y
end)).
rewrite - (DeterminantTrans f N A).
rewrite - (DeterminantTrans f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => b x
  | right _ => A x y
end)).
apply (DeterminantMultiLinearityHPlus f N (MTranspose f N N A) p b).
Qed.

Lemma DeterminantMultiLinearityHMult : forall (f : Field) (N : nat) (A : Matrix f N N) (p : {n : nat | (n < N)%nat}) (c : FT f), Determinant f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
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
end (MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)%nat} => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => Fmul f c (A k (proj1_sig b k))
  | right _ => A k (proj1_sig b k)
end))) = Fmul f c (Fmul f match PermutationParity N b with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)%nat} => A k (proj1_sig b k))))).
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
rewrite (MySumF2Included {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} p) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
rewrite (MySumF2Included {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} p) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
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
rewrite (MySumF2Same {n : nat | (n < N)%nat} (FiniteIntersection {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (Complement {n : nat | (n < N)%nat} (Singleton {n : nat | (n < N)%nat} p))) (FMCM f) (fun (k : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => Fmul f c (A k (proj1_sig b k))
  | right _ => A k (proj1_sig b k)
end) (fun (k : {n : nat | (n < N)%nat}) => A k (proj1_sig b k))).
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
apply (Full_intro {n : nat | (n < N)%nat} k).
move=> k H1.
apply (Full_intro {n : nat | (n < N)%nat} k).
Qed.

Lemma DeterminantMultiLinearityWMult : forall (f : Field) (N : nat) (A : Matrix f N N) (p : {n : nat | (n < N)%nat}) (c : FT f), Determinant f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end) = Fmul f c (Determinant f N A).
Proof.
move=> f N A p c.
rewrite - (DeterminantTrans f N (fun x y : {n : nat | (n < N)%nat} => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => Fmul f c (A x y)
  | right _ => A x y
end)).
rewrite - (DeterminantTrans f N A).
apply (DeterminantMultiLinearityHMult f N (MTranspose f N N A) p c).
Qed.

Lemma DeterminantSwapH : forall (f : Field) (N : nat) (A : Matrix f N N) (p q : {n : nat | (n < N)%nat}), proj1_sig p <> proj1_sig q -> Determinant f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig x) (proj1_sig p) with
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
end (MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)%nat} => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => A q (proj1_sig b k)
  | right _ => match Nat.eq_dec (proj1_sig k) (proj1_sig q) with
    | left _ => A p (proj1_sig b k)
    | right _ => A k (proj1_sig b k)
  end
end))) = Fopp f (Fmul f match PermutationParity N (PermutationCompose N b (PermutationSwap N p q)) with
  | ON => Fopp f (FI f)
  | OFF => FI f
end (MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)%nat} => A k (proj1_sig (PermutationCompose N b (PermutationSwap N p q)) k))))).
move=> H7.
rewrite H7.
rewrite (Fopp_add_distr f).
reflexivity.
suff: ((MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)%nat} => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => A q (proj1_sig b k)
  | right _ => match Nat.eq_dec (proj1_sig k) (proj1_sig q) with
    | left _ => A p (proj1_sig b k)
    | right _ => A k (proj1_sig b k)
  end
end)) = (MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)%nat} => A k (proj1_sig (PermutationCompose N b (PermutationSwap N p q)) k)))).
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
rewrite (MySumF2Included {n : nat | (n < N)%nat} (FiniteUnion {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} p) (FiniteSingleton {n : nat | (n < N)%nat} q)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f)).
rewrite (MySumF2Included {n : nat | (n < N)%nat} (FiniteUnion {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} p) (FiniteSingleton {n : nat | (n < N)%nat} q)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f)).
rewrite (MySumF2Same {n : nat | (n < N)%nat} (FiniteIntersection {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (Complement {n : nat | (n < N)%nat} (proj1_sig (FiniteUnion {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} p) (FiniteSingleton {n : nat | (n < N)%nat} q))))) (FMCM f) (fun k : {n : nat | (n < N)%nat} => match Nat.eq_dec (proj1_sig k) (proj1_sig p) with
  | left _ => A q (proj1_sig b k)
  | right _ => match Nat.eq_dec (proj1_sig k) (proj1_sig q) with
    | left _ => A p (proj1_sig b k)
    | right _ => A k (proj1_sig b k)
  end
end) (fun k : {n : nat | (n < N)%nat} => A k (proj1_sig b (match excluded_middle_informative (k = p) with
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
apply (Full_intro {n : nat | (n < N)%nat} k).
move=> k H7.
apply (Full_intro {n : nat | (n < N)%nat} k).
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

Lemma DeterminantSwapW : forall (f : Field) (N : nat) (A : Matrix f N N) (p q : {n : nat | (n < N)%nat}), proj1_sig p <> proj1_sig q -> Determinant f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => A x q
  | right _ => match Nat.eq_dec (proj1_sig y) (proj1_sig q) with
    | left _ => A x p
    | right _ => A x y
  end
end) = Fopp f (Determinant f N A).
Proof.
move=> f N A p q H1.
rewrite - (DeterminantTrans f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig y) (proj1_sig p) with
  | left _ => A x q
  | right _ => match Nat.eq_dec (proj1_sig y) (proj1_sig q) with
    | left _ => A x p
    | right _ => A x y
  end
end)).
rewrite - (DeterminantTrans f N A).
apply (DeterminantSwapH f N (MTranspose f N N A) p q H1).
Qed.

Lemma DeterminantDuplicateH : forall (f : Field) (N : nat) (A : Matrix f N N) (p q : {n : nat | (n < N)%nat}), proj1_sig p <> proj1_sig q -> A p = A q -> Determinant f N A = FO f.
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
suff: ((MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)%nat} => A k (proj1_sig (PermutationCompose N b (PermutationSwap N p q)) k))) = (MySumF2 {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (FMCM f) (fun k : {n : nat | (n < N)%nat} => A k (proj1_sig b k)))).
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
rewrite (MySumF2Included {n : nat | (n < N)%nat} (FiniteUnion {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} p) (FiniteSingleton {n : nat | (n < N)%nat} q)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
rewrite (MySumF2Included {n : nat | (n < N)%nat} (FiniteUnion {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} p) (FiniteSingleton {n : nat | (n < N)%nat} q)) (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
rewrite MySumF2Union.
rewrite MySumF2Union.
suff: ((MySumF2 {n : nat | (n < N)%nat} (FiniteIntersection {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (Complement {n : nat | (n < N)%nat} (proj1_sig (FiniteUnion {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} p) (FiniteSingleton {n : nat | (n < N)%nat} q))))) (FMCM f) (fun (k : {n : nat | (n < N)%nat}) => A k (proj1_sig (PermutationCompose N b (PermutationSwap N p q)) k))) = (MySumF2 {n : nat | (n < N)%nat} (FiniteIntersection {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N)) (Complement {n : nat | (n < N)%nat} (proj1_sig (FiniteUnion {n : nat | (n < N)%nat} (FiniteSingleton {n : nat | (n < N)%nat} p) (FiniteSingleton {n : nat | (n < N)%nat} q))))) (FMCM f) (fun (k : {n : nat | (n < N)%nat}) => A k (proj1_sig b k)))).
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
apply (Full_intro {n : nat | (n < N)%nat}).
move=> k H9.
apply (Full_intro {n : nat | (n < N)%nat}).
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

Lemma DeterminantDuplicateW : forall (f : Field) (N : nat) (A : Matrix f N N) (p q : {n : nat | (n < N)%nat}), proj1_sig p <> proj1_sig q -> (forall (k : {n : nat | (n < N)%nat}), A k p = A k q) -> Determinant f N A = FO f.
Proof.
move=> f N A p q H1 H2.
rewrite - (DeterminantTrans f N A).
apply (DeterminantDuplicateH f N (MTranspose f N N A) p q H1).
apply functional_extensionality.
move=> k.
apply (H2 k).
Qed.

Lemma DeterminantAddTransformH : forall (f : Field) (N : nat) (A : Matrix f N N) (p q : {n : nat | (n < N)%nat}) (c : FT f), proj1_sig p <> proj1_sig q -> Determinant f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
  | left _ => Fadd f (A x y) (Fmul f c (A p y))
  | right _ => A x y
end) = Determinant f N A.
Proof.
move=> f N A p q c H1.
rewrite (DeterminantMultiLinearityHPlus f N A q (fun (k : {n : nat | (n < N)%nat}) => Fmul f c (A p k))).
suff: ((fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
  | left _ => Fmul f c (A p y)
  | right _ => A x y
end) = (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
  | left _ => Fmul f c ((fun (x0 y0 : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
    | left _ => A p y0
    | right _ => A x0 y0
  end) x y)
  | right _ => (fun (x0 y0 : {n0 : nat | (n0 < N)%nat}) => match Nat.eq_dec (proj1_sig x0) (proj1_sig q) with
    | left _ => A p y0
    | right _ => A x0 y0
  end) x y
end)).
move=> H2.
rewrite H2.
rewrite (DeterminantMultiLinearityHMult f N (fun x y : {n : nat | (n < N)%nat} => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
  | left _ => A p y
  | right _ => A x y
end) q c).
rewrite (DeterminantDuplicateH f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig x) (proj1_sig q) with
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

Lemma DeterminantAddTransformW : forall (f : Field) (N : nat) (A : Matrix f N N) (p q : {n : nat | (n < N)%nat}) (c : FT f), proj1_sig p <> proj1_sig q -> Determinant f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig y) (proj1_sig q) with
  | left _ => Fadd f (A x y) (Fmul f c (A x p))
  | right _ => A x y
end) = Determinant f N A.
Proof.
move=> f N A p q c H1.
rewrite - (DeterminantTrans f N (fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig y) (proj1_sig q) with
  | left _ => Fadd f (A x y) (Fmul f c (A x p))
  | right _ => A x y
end)).
rewrite - (DeterminantTrans f N A).
apply (DeterminantAddTransformH f N (MTranspose f N N A) p q c H1).
Qed.

End Matrix.
