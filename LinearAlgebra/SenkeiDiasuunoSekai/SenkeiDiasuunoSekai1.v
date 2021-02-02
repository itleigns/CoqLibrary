Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "Tools" as Tools.
Add LoadPath "BasicProperty" as BasicProperty.
Add LoadPath "LibraryExtension" as LibraryExtension.

From mathcomp
Require Import ssreflect.
Require Import Coq.Logic.JMeq.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Image.
Require Import MyAlgebraicStructure.MyField.
Require Import MyAlgebraicStructure.MyVectorSpace.
Require Import BasicProperty.MappingProperty.
Require Import Tools.MySum.
Require Import Tools.BasicTools.
Require Import LibraryExtension.DatatypesExtension.
Require Import LibraryExtension.EnsemblesExtension.

Section Senkeidaisuunosekai1.

Definition VSPCM (K : Field) (V : VectorSpace K) : CommutativeMonoid := mkCommutativeMonoid (VT K V) (VO K V) (Vadd K V) (Vadd_comm K V) (Vadd_O_r K V) (Vadd_assoc K V).

Definition DirectSumField (K : Field) (T : Type) := {G : T -> FT K | Finite T (fun (t : T) => G t <> FO K)}.

Definition BasisVS (K : Field) (V : VectorSpace K) (T : Type) := fun (F : T -> VT K V) => Bijective (DirectSumField K T) (VT K V) (fun (g : DirectSumField K T) => MySumF2 T (exist (Finite T) (fun (t : T) => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V) (fun (t : T) => Vmul K V (proj1_sig g t) (F t))).

Lemma IsomorphicSaveBasisVS : forall (K : Field) (V1 V2 : VectorSpace K) (T : Type) (F : T -> VT K V1) (G : VT K V1 -> VT K V2), IsomorphicVS K V1 V2 G -> BasisVS K V1 T F -> BasisVS K V2 T (fun t : T => G (F t)).
Proof.
move=> K V1 V2 T F G H1 H2.
unfold BasisVS.
suff: ((fun g : DirectSumField K T => MySumF2 T (exist (Finite T) (fun t : T => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V2) (fun t : T => Vmul K V2 (proj1_sig g t) (G (F t)))) = (fun g : DirectSumField K T => G (MySumF2 T (exist (Finite T) (fun t : T => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V1) (fun t : T => Vmul K V1 (proj1_sig g t) (F t))))).
move=> H3.
rewrite H3.
apply (BijChain (DirectSumField K T) (VT K V1) (VT K V2) (fun g : DirectSumField K T => MySumF2 T (exist (Finite T) (fun t : T => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V1) (fun t : T => Vmul K V1 (proj1_sig g t) (F t))) G H2 (proj1 H1)).
apply functional_extensionality.
move=> g.
apply (FiniteSetInduction T (exist (Finite T) (fun t : T => proj1_sig g t <> FO K) (proj2_sig g))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite - (Vmul_O_l K V1 (VO K V1)).
rewrite (proj2 (proj2 H1)).
rewrite (Vmul_O_l K V2 (G (VO K V1))).
reflexivity.
move=> B b H3 H4 H5 H6.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H6.
rewrite (proj1 (proj2 H1) (MySumF2 T B (VSPCM K V1) (fun t : T => Vmul K V1 (proj1_sig g t) (F t))) (Vmul K V1 (proj1_sig g b) (F b))).
rewrite (proj2 (proj2 H1) (proj1_sig g b) (F b)).
reflexivity.
apply H5.
apply H5.
Qed.

Lemma BijectiveSaveBasisVS : forall (K : Field) (V : VectorSpace K) (T1 T2 : Type) (F : T1 -> T2) (G : T2 -> VT K V), Bijective T1 T2 F -> BasisVS K V T2 G -> BasisVS K V T1 (fun t : T1 => G (F t)).
Proof.
move=> K V T1 T2 F G H1 H2.
elim H1.
move=> f H3.
unfold BasisVS.
suff: (forall (x : DirectSumField K T1), Finite T2 (fun (t : T2) => proj1_sig x (f t) <> FO K)).
move=> H4.
suff: ((fun g : DirectSumField K T1 => MySumF2 T1 (exist (Finite T1) (fun t : T1 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V) (fun t : T1 => Vmul K V (proj1_sig g t) (G (F t)))) = (fun g : DirectSumField K T1 => (fun g : DirectSumField K T2 => MySumF2 T2 (exist (Finite T2) (fun t : T2 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V) (fun t : T2 => Vmul K V (proj1_sig g t) (G t))) ((fun g : DirectSumField K T1 => exist (fun (G : T2 -> FT K) => Finite T2 (fun t : T2 => G t <> FO K)) (fun (t : T2) => proj1_sig g (f t)) (H4 g)) g))).
move=> H5.
rewrite H5.
apply (BijChain (DirectSumField K T1) (DirectSumField K T2) (VT K V) (fun g : DirectSumField K T1 => exist (fun (G : T2 -> FT K) => Finite T2 (fun t : T2 => G t <> FO K)) (fun (t : T2) => proj1_sig g (f t)) (H4 g)) (fun g : DirectSumField K T2 => MySumF2 T2 (exist (Finite T2) (fun t : T2 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V) (fun t : T2 => Vmul K V (proj1_sig g t) (G t)))).
apply InjSurjBij.
move=> x1 x2 H6.
apply sig_map.
apply functional_extensionality.
move=> t.
suff: (proj1_sig x1 t = proj1_sig (exist (fun G : T2 -> FT K => Finite T2 (fun t : T2 => G t <> FO K)) (fun t : T2 => proj1_sig x1 (f t)) (H4 x1)) (F t)).
move=> H7.
rewrite H7.
rewrite H6.
rewrite - {2} (proj1 H3 t).
reflexivity.
rewrite - {1} (proj1 H3 t).
reflexivity.
move=> y.
suff: (Finite T1 (fun (t : T1) => (proj1_sig y (F t)) <> FO K)).
move=> H6.
exists (exist (fun G : T1 -> FT K => Finite T1 (fun t : T1 => G t <> FO K)) (fun (t : T1) => (proj1_sig y (F t))) H6).
apply sig_map.
simpl.
apply functional_extensionality.
move=> t.
rewrite (proj2 H3 t).
reflexivity.
suff: ((fun t : T1 => proj1_sig y (F t) <> FO K) = Im T2 T1 (fun t : T2 => proj1_sig y t <> FO K) f).
move=> H6.
rewrite H6.
apply finite_image.
apply (proj2_sig y).
apply Extensionality_Ensembles.
apply conj.
move=> t H6.
apply (Im_intro T2 T1 (fun t0 : T2 => proj1_sig y t0 <> FO K) f (F t)).
apply H6.
rewrite (proj1 H3 t).
reflexivity.
move=> t1.
elim.
move=> t2 H6 y0 H7.
rewrite H7.
unfold In.
rewrite (proj2 H3 t2).
apply H6.
apply H2.
apply functional_extensionality.
move=> x.
rewrite - (MySumF2BijectiveSame T1 (exist (Finite T1) (fun t : T1 => proj1_sig x t <> FO K) (proj2_sig x)) T2 (exist (Finite T2) (fun t : T2 => proj1_sig (exist (fun G0 : T2 -> FT K => Finite T2 (fun t0 : T2 => G0 t0 <> FO K)) (fun t0 : T2 => proj1_sig x (f t0)) (H4 x)) t <> FO K) (proj2_sig (exist (fun G0 : T2 -> FT K => Finite T2 (fun t : T2 => G0 t <> FO K)) (fun t : T2 => proj1_sig x (f t)) (H4 x)))) (VSPCM K V) (fun t : T2 => Vmul K V (proj1_sig (exist (fun G0 : T2 -> FT K => Finite T2 (fun t0 : T2 => G0 t0 <> FO K)) (fun t0 : T2 => proj1_sig x (f t0)) (H4 x)) t) (G t)) F).
suff: ((fun t : T1 => Vmul K V (proj1_sig x t) (G (F t))) = (fun u : T1 => Vmul K V (proj1_sig (exist (fun G0 : T2 -> FT K => Finite T2 (fun t0 : T2 => G0 t0 <> FO K)) (fun t0 : T2 => proj1_sig x (f t0)) (H4 x)) (F u)) (G (F u)))).
move=> H5.
rewrite H5.
reflexivity.
apply functional_extensionality.
move=> t.
simpl.
rewrite (proj1 H3 t).
reflexivity.
simpl.
move=> t.
rewrite (proj1 H3 t).
apply.
simpl.
move=> H5.
apply InjSurjBij.
move=> u1 u2 H6.
apply sig_map.
apply (BijInj T1 T2 F H1).
suff: (F (proj1_sig u1) = proj1_sig (exist (fun t : T2 => proj1_sig x (f t) <> FO K) (F (proj1_sig u1)) (H5 (proj1_sig u1) (proj2_sig u1)))).
move=> H7.
rewrite H7.
rewrite H6.
reflexivity.
reflexivity.
move=> u.
exists (exist (fun (t : T1) => proj1_sig x t <> FO K) (f (proj1_sig u)) (proj2_sig u)).
apply sig_map.
simpl.
apply (proj2 H3 (proj1_sig u)).
move=> x.
suff: ((fun t : T2 => proj1_sig x (f t) <> FO K) = Im T1 T2 (fun t : T1 => proj1_sig x t <> FO K) F).
move=> H4.
rewrite H4.
apply finite_image.
apply (proj2_sig x).
apply Extensionality_Ensembles.
apply conj.
move=> t H4.
apply (Im_intro T1 T2 (fun t0 : T1 => proj1_sig x t0 <> FO K) F (f t)).
apply H4.
rewrite (proj2 H3 t).
reflexivity.
move=> t2.
elim.
move=> t1 H4 y0 H5.
rewrite H5.
unfold In.
rewrite (proj1 H3 t1).
apply H4.
Qed.

Lemma CountFinite : forall (N : nat), Finite (Count N) (Full_set (Count N)).
Proof.
move=> N.
apply EnsembleSetFinite.
elim N.
suff: ((fun u : nat => (u < 0)%nat) = Empty_set nat).
move=> H1.
rewrite H1.
apply Empty_is_finite.
apply Extensionality_Ensembles.
apply conj.
move=> n H1.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r n H1).
move=> n.
elim.
move=> n H1.
suff: ((fun u : nat => (u < S n)%nat) = Add nat (fun u : nat => (u < n)%nat) n).
move=> H2.
rewrite H2.
apply (Union_is_finite nat (fun u : nat => (u < n)%nat) H1 n).
apply (lt_irrefl n).
apply Extensionality_Ensembles.
apply conj.
move=> m H2.
elim (classic (m = n)).
move=> H3.
right.
rewrite H3.
reflexivity.
intro H3.
left.
elim (le_lt_or_eq (S m) (S n) H2).
apply (lt_S_n m n).
move=> H4.
apply False_ind.
apply H3.
apply (PeanoNat.Nat.succ_inj m n H4).
move=> m.
elim.
move=> m1 H2.
apply (le_S (S m1) n).
apply H2.
move=> m1 H2.
rewrite H2.
apply (le_n (S m1)).
Qed.

Lemma FiniteBasisVS : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V), (BasisVS K V (Count N) F) <-> forall (v : VT K V), exists! (a : Count N -> FT K), v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun (n : Count N) => Vmul K V (a n) (F n)).
Proof.
move=> K V N F.
unfold BasisVS.
suff: ((fun g : DirectSumField K (Count N) => MySumF2 (Count N) (exist (Finite (Count N)) (fun t : Count N => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V) (fun t : Count N => Vmul K V (proj1_sig g t) (F t))) = (fun g : DirectSumField K (Count N) => MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun t : Count N => Vmul K V (proj1_sig g t) (F t)))).
move=> H1.
rewrite H1.
apply conj.
elim.
move=> G H2 v.
apply (proj1 (unique_existence (fun (a : Count N -> FT K) => v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n))))).
apply conj.
exists (proj1_sig (G v)). 
rewrite (proj2 H2 v).
reflexivity.
move=> a1 a2 H3 H4.
suff: (forall (G : Count N -> FT K), Finite (Count N) (fun t : Count N => G t <> FO K)).
move=> H5.
suff: (a1 = proj1_sig (exist (fun G : Count N -> FT K => Finite (Count N) (fun t : Count N => G t <> FO K)) a1 (H5 a1))).
move=> H6.
rewrite H6.
suff: (a2 = proj1_sig (exist (fun G : Count N -> FT K => Finite (Count N) (fun t : Count N => G t <> FO K)) a2 (H5 a2))).
move=> H7.
rewrite H7.
rewrite - (proj1 H2 (exist (fun G : Count N -> FT K => Finite (Count N) (fun t : Count N => G t <> FO K)) a2 (H5 a2))).
rewrite - (proj1 H2 (exist (fun G : Count N -> FT K => Finite (Count N) (fun t : Count N => G t <> FO K)) a1 (H5 a1))).
rewrite - H3.
rewrite - H4.
reflexivity.
reflexivity.
reflexivity.
move=> G0.
apply (Finite_downward_closed (Count N) (Full_set (Count N)) (CountFinite N) (fun t : Count N => G0 t <> FO K)).
move=> n H5.
apply (Full_intro (Count N) n).
move=> H2.
suff: (forall (v : VT K V), {a : Count N -> FT K | v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n))}).
move=> H3.
suff: (forall (G : Count N -> FT K), Finite (Count N) (fun t : Count N => G t <> FO K)).
move=> H4.
exists (fun (v : VT K V) => exist (fun G : Count N -> FT K => Finite (Count N) (fun t : Count N => G t <> FO K)) (proj1_sig (H3 v)) (H4 (proj1_sig (H3 v)))).
apply conj.
move=> n.
apply sig_map.
simpl.
suff: (forall (v : VT K V), uniqueness (fun (a : Count N -> FT K) => v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n)))).
move=> H5.
apply (H5 (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun t : Count N => Vmul K V (proj1_sig n t) (F t)))).
rewrite - (proj2_sig (H3 (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun t : Count N => Vmul K V (proj1_sig n t) (F t))))).
reflexivity.
reflexivity.
move=> v.
apply (proj2 (proj2 (unique_existence (fun a : Count N -> FT K => v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n0 : Count N => Vmul K V (a n0) (F n0)))) (H2 v))).
move=> y.
rewrite - (proj2_sig (H3 y)).
reflexivity.
move=> G.
apply (Finite_downward_closed (Count N) (Full_set (Count N)) (CountFinite N) (fun t : Count N => G t <> FO K)).
move=> n H4.
apply (Full_intro (Count N) n).
move=> v.
apply (constructive_definite_description (fun (a : Count N -> FT K) => v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n)))).
apply (H2 v).
apply functional_extensionality.
move=> a.
rewrite (MySumF2Excluded (Count N) (VSPCM K V) (fun t : Count N => Vmul K V (proj1_sig a t) (F t)) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun t : Count N => proj1_sig a t <> FO K)).
suff: ((MySumF2 (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Complement (Count N) (fun t : Count N => proj1_sig a t <> FO K))) (VSPCM K V) (fun t : Count N => Vmul K V (proj1_sig a t) (F t))) = VO K V).
move=> H1.
rewrite H1.
simpl.
rewrite (Vadd_O_r K V (MySumF2 (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun t : Count N => proj1_sig a t <> FO K)) (VSPCM K V) (fun t : Count N => Vmul K V (proj1_sig a t) (F t)))).
suff: ((exist (Finite (Count N)) (fun t : Count N => proj1_sig a t <> FO K) (proj2_sig a)) = (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun t : Count N => proj1_sig a t <> FO K))).
move=> H2.
rewrite H2.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> t H2.
apply (Intersection_intro (Count N) (fun t : Count N => proj1_sig a t <> FO K) (Full_set (Count N))).
apply H2.
apply (Full_intro (Count N) t).
move=> t.
elim.
move=> t0 H2 H3.
apply H2.
apply (MySumF2Induction (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Complement (Count N) (fun t : Count N => proj1_sig a t <> FO K)))).
apply conj.
reflexivity.
move=> v n H1 H2.
rewrite H2.
suff: ((proj1_sig a n) = (FO K)).
move=> H3.
rewrite H3.
rewrite (Vmul_O_l K V (F n)).
apply (Vadd_O_r K V (VO K V)).
apply NNPP.
elim H1.
move=> m H3 H4.
apply H3.
Qed.

Definition Fn (F : Field) (N : nat) := (Count N -> FT F).

Definition Fnadd (F : Field) (N : nat) := fun (f1 f2 : Fn F N) => (fun (n : Count N) => Fadd F (f1 n) (f2 n)).

Definition Fnmul (F : Field) (N : nat) := fun (c : FT F) (f : Fn F N) => (fun (n : Count N) => Fmul F c (f n)).

Definition Fnopp (F : Field) (N : nat) := fun (f : (Fn F N)) => (fun (n : Count N) => Fopp F (f n)).

Definition Fnminus (F : Field) (N : nat) := fun (f1 f2 : (Fn F N)) => (Fnadd F N f1 (Fnopp F N f2)).

Definition FnO (F : Field) (N : nat) := (fun (n : Count N) => FO F).

Lemma Fnadd_comm : forall (F : Field) (N : nat) (f1 f2 : Fn F N), (Fnadd F N f1 f2) = (Fnadd F N f2 f1).
Proof.
move=> F N f1 f2.
apply functional_extensionality.
move=> n.
apply (Fadd_comm F (f1 n) (f2 n)).
Qed.

Lemma Fnadd_assoc : forall (F : Field) (N : nat) (f1 f2 f3 : Fn F N), (Fnadd F N (Fnadd F N f1 f2) f3) = (Fnadd F N f1 (Fnadd F N f2 f3)).
Proof.
move=> F N f1 f2 f3.
apply functional_extensionality.
move=> n.
apply (Fadd_assoc F (f1 n) (f2 n) (f3 n)).
Qed.

Lemma Fnadd_O_l : forall (F : Field) (N : nat) (f : Fn F N), (Fnadd F N (FnO F N) f) = f.
Proof.
move=> F N f.
apply functional_extensionality.
move=> n.
apply (Fadd_O_l F (f n)).
Qed.

Lemma Fnadd_opp_r : forall (F : Field) (N : nat) (f : Fn F N), (Fnadd F N f (Fnopp F N f)) = (FnO F N).
Proof.
move=> F N f.
apply functional_extensionality.
move=> n.
apply (Fadd_opp_r F (f n)).
Qed.

Lemma Fnadd_distr_l : forall (F : Field) (N : nat) (c : FT F) (f1 f2 : Fn F N), (Fnmul F N c (Fnadd F N f1 f2)) = (Fnadd F N (Fnmul F N c f1) (Fnmul F N c f2)).
Proof.
move=> F N c f1 f2.
apply functional_extensionality.
move=> n.
apply (Fmul_add_distr_l F c (f1 n) (f2 n)).
Qed.

Lemma Fnadd_distr_r : forall (F : Field) (N : nat) (c1 c2 : FT F) (f : Fn F N), (Fnmul F N (Fadd F c1 c2) f) = (Fnadd F N (Fnmul F N c1 f) (Fnmul F N c2 f)).
Proof.
move=> F N c1 c2 f.
apply functional_extensionality.
move=> n.
apply (Fmul_add_distr_r F c1 c2 (f n)).
Qed.

Lemma Fnmul_assoc : forall (F : Field) (N : nat) (c1 c2 : FT F) (f : Fn F N), (Fnmul F N c1 (Fnmul F N c2 f)) = (Fnmul F N (Fmul F c1 c2) f).
Proof.
move=> F N c1 c2 f.
apply functional_extensionality.
move=> n.
unfold Fnmul.
rewrite (Fmul_assoc F c1 c2 (f n)).
reflexivity.
Qed.

Lemma Fnmul_I_l : forall (F : Field) (N : nat) (f : Fn F N), (Fnmul F N (FI F) f) = f.
Proof.
move=> F N f.
apply functional_extensionality.
move=> n.
apply (Fmul_I_l F (f n)).
Qed.

Definition FnVS (F : Field) (N : nat) := mkVectorSpace F (Fn F N) (FnO F N) (Fnadd F N) (Fnmul F N) (Fnopp F N) (Fnadd_comm F N) (Fnadd_assoc F N) (Fnadd_O_l F N) (Fnadd_opp_r F N) (Fnadd_distr_l F N) (Fnadd_distr_r F N) (Fnmul_assoc F N) (Fnmul_I_l F N).

Definition StandardBasisVS (F : Field) (N : nat) := fun (n : Count N) (m : Count N) => match excluded_middle_informative (proj1_sig n = proj1_sig m) with
  | left _ => FI F
  | right _ => FO F
end.

Lemma StandardBasisNatureVS : forall (F : Field) (N : nat), BasisVS F (FnVS F N) (Count N) (StandardBasisVS F N).
Proof.
move=> F N.
apply (proj2 (FiniteBasisVS F (FnVS F N) N (StandardBasisVS F N))).
move=> v.
apply (proj1 (unique_existence (fun (a : Count N -> FT F) => v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM F (FnVS F N)) (fun n : Count N => Vmul F (FnVS F N) (a n) (StandardBasisVS F N n))))).
apply conj.
exists (fun (n : Count N) => v n).
apply functional_extensionality.
move=> m.
rewrite (MySumF2Excluded (Count N) (VSPCM F (FnVS F N)) (fun (n : Count N) => Vmul F (FnVS F N) (v n) (StandardBasisVS F N n)) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun (k : Count N) => k = m)).
suff: ((MySumF2 (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Complement (Count N) (fun k : Count N => k = m))) (VSPCM F (FnVS F N)) (fun n : Count N => Vmul F (FnVS F N) (v n) (StandardBasisVS F N n))) m = FO F).
move=> H1.
simpl.
unfold Fnadd.
rewrite H1.
rewrite (Fadd_O_r F (MySumF2 (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun k : Count N => k = m)) (VSPCM F (FnVS F N)) (fun n : Count N => Fnmul F N (v n) (StandardBasisVS F N n)) m)).
suff: ((FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun k : Count N => k = m)) = FiniteSingleton (Count N) m).
move=> H2.
rewrite H2.
rewrite MySumF2Singleton.
unfold Fnmul.
unfold StandardBasisVS.
elim (excluded_middle_informative (proj1_sig m = proj1_sig m)).
move=> H3.
rewrite (Fmul_I_r F (v m)).
reflexivity.
move=> H3.
apply False_ind.
apply H3.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> n.
elim.
move=> n0 H2 H3.
rewrite H2.
apply (In_singleton (Count N) m).
move=> n.
elim.
apply (Intersection_intro (Count N) (fun k : Count N => k = m) (Full_set (Count N))).
reflexivity.
apply (Full_intro (Count N) m).
apply (FiniteSetInduction (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Complement (Count N) (fun k : Count N => k = m)))).
apply conj.
rewrite MySumF2Empty.
reflexivity.
move=> B b H1 H2 H3 H4.
rewrite MySumF2Add.
simpl.
unfold Fnadd.
rewrite H4.
suff: ((Fnmul F N (v b) (StandardBasisVS F N b) m) = FO F).
move=> H5.
rewrite H5.
apply (Fadd_O_l F (FO F)).
unfold StandardBasisVS.
unfold Fnmul.
elim (excluded_middle_informative (proj1_sig b = proj1_sig m)).
elim H2.
move=> k H5 H6 H7.
apply False_ind.
apply H5.
apply sig_map.
apply H7.
move=> H5.
apply (Fmul_O_r F (v b)).
apply H3.
move=> m1 m2 H1 H2.
suff: (forall (m : Fn F N), m = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM F (FnVS F N)) (fun n : Count N => Vmul F (FnVS F N) (m n) (StandardBasisVS F N n))).
move=> H3.
rewrite (H3 m1).
rewrite (H3 m2).
rewrite - H1.
apply H2.
move=> m.
apply functional_extensionality.
move=> n.
rewrite (MySumF2Excluded (Count N) (VSPCM F (FnVS F N)) (fun (n0 : Count N) => Vmul F (FnVS F N) (m n0) (StandardBasisVS F N n0)) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun (k : Count N) => k = n)).
simpl.
unfold Fnadd.
suff: ((FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun k : Count N => k = n)) = FiniteSingleton (Count N) n).
move=> H3.
rewrite H3.
suff: ((MySumF2 (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Complement (Count N) (fun k : Count N => k = n))) (VSPCM F (FnVS F N)) (fun n0 : Count N => Fnmul F N (m n0) (StandardBasisVS F N n0)) n) = FO F).
move=> H4.
rewrite H4.
rewrite (Fadd_O_r F (MySumF2 (Count N) (FiniteSingleton (Count N) n) (VSPCM F (FnVS F N)) (fun n0 : Count N => Fnmul F N (m n0) (StandardBasisVS F N n0)) n)).
rewrite MySumF2Singleton.
unfold Fnmul.
unfold StandardBasisVS.
elim (excluded_middle_informative (proj1_sig n = proj1_sig n)).
move=> H5.
rewrite (Fmul_I_r F (m n)).
reflexivity.
move=> H5.
apply False_ind.
apply H5.
reflexivity.
apply (FiniteSetInduction (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Complement (Count N) (fun k : Count N => k = n)))).
apply conj.
rewrite MySumF2Empty.
reflexivity.
move=> B b H4 H5 H6 H7.
rewrite MySumF2Add.
simpl.
unfold Fnadd.
rewrite H7.
unfold Fnmul.
unfold StandardBasisVS.
elim (excluded_middle_informative (proj1_sig b = proj1_sig n)).
elim H5.
move=> b0 H8 H9 H10.
apply False_ind.
apply H8.
apply sig_map.
apply H10.
move=> H8.
rewrite (Fmul_O_r F (m b)).
apply (Fadd_O_l F (FO F)).
apply H6.
apply sig_map.
apply Extensionality_Ensembles.
simpl.
apply conj.
move=> k.
elim.
move=> k0 H3 H4.
rewrite H3.
apply (In_singleton (Count N) n).
move=> k.
elim.
apply (Intersection_intro (Count N) (fun k0 : Count N => k0 = n) (Full_set (Count N)) n).
reflexivity.
apply (Full_intro (Count N) n).
Qed.

Lemma Proposition_2_3_1 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V), (BasisVS K V (Count N) F) <-> (Bijective (Fn K N) (VT K V) (fun (a : Fn K N) => MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun (n : Count N) => Vmul K V (a n) (F n)))).
Proof.
move=> K V N F.
unfold BasisVS.
suff: (forall (a : Fn K N), Finite (Count N) (fun (t : Count N) => a t <> FO K)).
move=> H1.
suff: (forall (g : DirectSumField K (Count N)), MySumF2 (Count N) (exist (Finite (Count N)) (fun t : Count N => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V) (fun t : Count N => Vmul K V (proj1_sig g t) (F t)) = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V ((proj1_sig g) n) (F n))).
move=> H2.
apply conj.
elim.
move=> G H3.
exists (fun (v : VT K V) => proj1_sig (G v)).
apply conj.
move=> f.
suff: (f = proj1_sig (exist (fun (a : Fn K N) => Finite (Count N) (fun t : Count N => a t <> FO K)) f (H1 f))).
move=> H4.
rewrite {1} H4.
rewrite - (H2 (exist (fun (a : Fn K N) => Finite (Count N) (fun t : Count N => a t <> FO K)) f (H1 f))).
rewrite (proj1 H3 (exist (fun (a : Fn K N) => Finite (Count N) (fun t : Count N => a t <> FO K)) f (H1 f))).
reflexivity.
reflexivity.
move=> v.
rewrite - (H2 (G v)).
apply (proj2 H3 v).
elim.
move=> G H3.
exists (fun (v : VT K V) => exist (fun (a : Fn K N) => Finite (Count N) (fun t : Count N => a t <> FO K)) (G v) (H1 (G v))).
apply conj.
move=> f.
apply sig_map.
simpl.
rewrite (H2 f).
apply (proj1 H3 (proj1_sig f)).
move=> v.
rewrite (H2 (exist (fun a : Fn K N => Finite (Count N) (fun t0 : Count N => a t0 <> FO K)) (G v) (H1 (G v)))).
apply (proj2 H3 v).
move=> g.
rewrite (MySumF2Excluded (Count N) (VSPCM K V) (fun n : Count N => Vmul K V (proj1_sig g n) (F n)) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun t : Count N => proj1_sig g t <> FO K)).
suff: ((MySumF2 (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Complement (Count N) (fun t : Count N => proj1_sig g t <> FO K))) (VSPCM K V) (fun n : Count N => Vmul K V (proj1_sig g n) (F n))) = VO K V).
move=> H2.
rewrite H2.
simpl.
rewrite (Vadd_O_r K V (MySumF2 (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun t : Count N => proj1_sig g t <> FO K)) (VSPCM K V) (fun n : Count N => Vmul K V (proj1_sig g n) (F n)))).
suff: ((exist (Finite (Count N)) (fun t : Count N => proj1_sig g t <> FO K) (proj2_sig g)) = (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))(fun t : Count N => proj1_sig g t <> FO K))).
move=> H3.
rewrite H3.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> n H3.
apply (Intersection_intro (Count N) (fun t : Count N => proj1_sig g t <> FO K) (Full_set (Count N))).
apply H3.
apply (Full_intro (Count N) n).
move=> n.
elim.
move=> n0 H3 H4.
apply H3.
apply MySumF2Induction.
apply conj.
reflexivity.
move=> v n H2 H3.
rewrite H3.
suff: ((proj1_sig g n) = FO K).
move=> H4.
rewrite H4.
rewrite (Vmul_O_l K V (F n)).
apply (Vadd_O_l K V (VO K V)).
elim H2.
move=> m H4 H5.
apply NNPP.
apply H4.
move=> a.
apply (Finite_downward_closed (Count N) (Full_set (Count N)) (CountFinite N) (fun t : Count N => a t <> FO K)).
move=> t H1.
apply (Full_intro (Count N) t).
Qed.

Lemma Proposition_2_3_2 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V), (BasisVS K V (Count N) F) <-> ((forall (v : VT K V), exists (a : Count N -> FT K), v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n))) /\ (forall (a : Count N -> FT K), MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n)) = VO K V -> a = FnO K N)).
Proof.
move=> K V N F.
apply conj.
move=> H1.
suff: (forall v : VT K V, exists! a : Count N -> FT K, v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n))).
move=> H2.
apply conj.
move=> v.
apply (proj1 (proj2 (unique_existence (fun (a : Count N -> FT K) => v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n)))) (H2 v))).
move=> a0 H3. 
apply (proj2 (proj2 (unique_existence (fun (a : Count N -> FT K) => VO K V = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n)))) (H2 (VO K V))) a0 (FnO K N)).
rewrite H3.
reflexivity.
apply (MySumF2Induction (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
reflexivity.
move=> v n H4 H5.
rewrite H5.
rewrite (Vmul_O_l K V (F n)).
rewrite - {1} (Vadd_O_r K V v).
reflexivity.
apply (proj1 (FiniteBasisVS K V N F) H1).
move=> H1.
apply (proj2 (FiniteBasisVS K V N F)).
move=> v.
apply (proj1 (unique_existence (fun (a : Count N -> FT K) => v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n))))).
apply conj.
apply (proj1 H1 v).
move=> a1 a2 H2 H3.
rewrite - (Vadd_O_r K (FnVS K N) a1).
rewrite - (Vadd_O_l K (FnVS K N) a2).
rewrite - {1} (Vadd_opp_l K (FnVS K N) a2).
rewrite - (Vadd_assoc K (FnVS K N) a1 (Vopp K (FnVS K N) a2) a2).
simpl.
suff: (Fnminus K N a1 a2 = FnO K N).
unfold Fnminus.
move=> H4.
rewrite H4.
reflexivity.
apply (proj2 H1 (Fnminus K N a1 a2)).
suff: (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (Fnminus K N a1 a2 n) (F n)) = Vadd K V (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a1 n) (F n))) (Vopp K V (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a2 n) (F n))))).
move=> H4.
rewrite H4.
rewrite - H2.
rewrite - H3.
apply (Vadd_opp_r K V v).
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite (Vadd_opp_r K V (VO K V)).
reflexivity.
move=> B b H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H7.
rewrite (Vopp_add_distr K V (MySumF2 (Count N) B (VSPCM K V) (fun n : Count N => Vmul K V (a2 n) (F n))) (Vmul K V (a2 b) (F b))).
rewrite (Vadd_assoc K V (MySumF2 (Count N) B (VSPCM K V) (fun n : Count N => Vmul K V (a1 n) (F n))) (Vmul K V (a1 b) (F b)) (Vadd K V (Vopp K V (MySumF2 (Count N) B (VSPCM K V) (fun n : Count N => Vmul K V (a2 n) (F n)))) (Vopp K V (Vmul K V (a2 b) (F b))))).
rewrite - (Vadd_assoc K V (Vmul K V (a1 b) (F b)) (Vopp K V (MySumF2 (Count N) B (VSPCM K V) (fun n : Count N => Vmul K V (a2 n) (F n)))) (Vopp K V (Vmul K V (a2 b) (F b)))).
rewrite (Vadd_comm K V (Vmul K V (a1 b) (F b)) (Vopp K V (MySumF2 (Count N) B (VSPCM K V) (fun n : Count N => Vmul K V (a2 n) (F n))))).
rewrite (Vadd_assoc K V (Vopp K V (MySumF2 (Count N) B (VSPCM K V) (fun n : Count N => Vmul K V (a2 n) (F n)))) (Vmul K V (a1 b) (F b)) (Vopp K V (Vmul K V (a2 b) (F b)))).
rewrite (Vadd_assoc K V (MySumF2 (Count N) B (VSPCM K V) (fun n : Count N => Vmul K V (a1 n) (F n))) (Vopp K V (MySumF2 (Count N) B (VSPCM K V) (fun n : Count N => Vmul K V (a2 n) (F n)))) (Vmul K V (Fnminus K N a1 a2 b) (F b))).
rewrite (Vopp_mul_distr_l K V (a2 b) (F b)).
rewrite - (Vmul_add_distr_r K V (a1 b) (Fopp K (a2 b)) (F b)).
reflexivity.
apply H6.
apply H6.
apply H6.
Qed.

Definition PairVST (K : Field) (V1 V2 : VectorSpace K) := prod (VT K V1) (VT K V2).

Definition PairVSVO (K : Field) (V1 V2 : VectorSpace K) := (VO K V1, VO K V2).

Definition PairVSVadd (K : Field) (V1 V2 : VectorSpace K) := fun (v1 v2 : PairVST K V1 V2) => (Vadd K V1 (fst v1) (fst v2), Vadd K V2 (snd v1) (snd v2)).

Definition PairVSVmul (K : Field) (V1 V2 : VectorSpace K) := fun (f : FT K) (v : PairVST K V1 V2) => (Vmul K V1 f (fst v), Vmul K V2 f (snd v)).

Definition PairVSVopp (K : Field) (V1 V2 : VectorSpace K) := fun (v : PairVST K V1 V2) => (Vopp K V1 (fst v), Vopp K V2 (snd v)).

Lemma PairVSVadd_comm : forall (K : Field) (V1 V2 : VectorSpace K) (v1 v2 : PairVST K V1 V2), PairVSVadd K V1 V2 v1 v2 = PairVSVadd K V1 V2 v2 v1.
Proof.
move=> K V1 V2 v1 v2.
apply injective_projections.
apply (Vadd_comm K V1 (fst v1) (fst v2)).
apply (Vadd_comm K V2 (snd v1) (snd v2)).
Qed.

Lemma PairVSVadd_assoc : forall (K : Field) (V1 V2 : VectorSpace K) (v1 v2 v3 : PairVST K V1 V2), PairVSVadd K V1 V2 (PairVSVadd K V1 V2 v1 v2) v3 = PairVSVadd K V1 V2 v1 (PairVSVadd K V1 V2 v2 v3).
Proof.
move=> K V1 V2 v1 v2 v3.
apply injective_projections.
apply (Vadd_assoc K V1 (fst v1) (fst v2) (fst v3)).
apply (Vadd_assoc K V2 (snd v1) (snd v2) (snd v3)).
Qed.

Lemma PairVSVadd_O_l : forall (K : Field) (V1 V2 : VectorSpace K) (v : PairVST K V1 V2), PairVSVadd K V1 V2 (PairVSVO K V1 V2) v = v.
Proof.
move=> K V1 V2 v.
apply injective_projections.
apply (Vadd_O_l K V1 (fst v)).
apply (Vadd_O_l K V2 (snd v)).
Qed.

Lemma PairVSVadd_opp_r : forall (K : Field) (V1 V2 : VectorSpace K) (v : PairVST K V1 V2), PairVSVadd K V1 V2 v (PairVSVopp K V1 V2 v) = PairVSVO K V1 V2.
Proof.
move=> K V1 V2 v.
apply injective_projections.
apply (Vadd_opp_r K V1 (fst v)).
apply (Vadd_opp_r K V2 (snd v)).
Qed.

Lemma PairVSVmul_add_distr_l : forall (K : Field) (V1 V2 : VectorSpace K) (f : FT K) (v1 v2 : PairVST K V1 V2), PairVSVmul K V1 V2 f (PairVSVadd K V1 V2 v1 v2) = (PairVSVadd K V1 V2 (PairVSVmul K V1 V2 f v1) (PairVSVmul K V1 V2 f v2)).
Proof.
move=> K V1 V2 f v1 v2.
apply injective_projections.
apply (Vmul_add_distr_l K V1 f (fst v1) (fst v2)).
apply (Vmul_add_distr_l K V2 f (snd v1) (snd v2)).
Qed.

Lemma PairVSVmul_add_distr_r : forall (K : Field) (V1 V2 : VectorSpace K) (f1 f2 : FT K) (v : PairVST K V1 V2), (PairVSVmul K V1 V2 (Fadd K f1 f2) v) = (PairVSVadd K V1 V2 (PairVSVmul K V1 V2 f1 v) (PairVSVmul K V1 V2 f2 v)).
Proof.
move=> K V1 V2 f1 f2 v.
apply injective_projections.
apply (Vmul_add_distr_r K V1 f1 f2 (fst v)).
apply (Vmul_add_distr_r K V2 f1 f2 (snd v)).
Qed.

Lemma PairVSVmul_assoc : forall (K : Field) (V1 V2 : VectorSpace K) (f1 f2 : FT K) (v : PairVST K V1 V2), (PairVSVmul K V1 V2 f1 (PairVSVmul K V1 V2 f2 v)) = (PairVSVmul K V1 V2 (Fmul K f1 f2) v).
Proof.
move=> K V1 V2 f1 f2 v.
apply injective_projections.
apply (Vmul_assoc K V1 f1 f2 (fst v)).
apply (Vmul_assoc K V2 f1 f2 (snd v)).
Qed.

Lemma PairVSVmul_I_l : forall (K : Field) (V1 V2 : VectorSpace K) (v : PairVST K V1 V2), (PairVSVmul K V1 V2 (FI K) v) = v.
Proof.
move=> K V1 V2 v.
apply injective_projections.
apply (Vmul_I_l K V1 (fst v)).
apply (Vmul_I_l K V2 (snd v)).
Qed.

Definition PairVS (K : Field) (V1 V2 : VectorSpace K) := mkVectorSpace K (PairVST K V1 V2) (PairVSVO K V1 V2) (PairVSVadd K V1 V2) (PairVSVmul K V1 V2) (PairVSVopp K V1 V2) (PairVSVadd_comm K V1 V2) (PairVSVadd_assoc K V1 V2) (PairVSVadd_O_l K V1 V2) (PairVSVadd_opp_r K V1 V2) (PairVSVmul_add_distr_l K V1 V2) (PairVSVmul_add_distr_r K V1 V2) (PairVSVmul_assoc K V1 V2) (PairVSVmul_I_l K V1 V2).

Definition PairSystemVS (K : Field) (T1 T2 : Type) (V1 V2 : VectorSpace K) (a1 : T1 -> (VT K V1)) (a2 : T2 -> (VT K V2)) := fun (t : T1 + T2) => match t with
  | inl t1 => (a1 t1, VO K V2)
  | inr t2 => (VO K V1, a2 t2)
end.

Lemma PairBasisVS : forall (K : Field) (T1 T2 : Type) (V1 V2 : VectorSpace K) (a1 : T1 -> (VT K V1)) (a2 : T2 -> (VT K V2)), (BasisVS K V1 T1 a1) -> (BasisVS K V2 T2 a2) -> (BasisVS K (PairVS K V1 V2) (T1 + T2) (PairSystemVS K T1 T2 V1 V2 a1 a2)).
Proof.
move=> K T1 T2 V1 V2 a1 a2 H1 H2.
suff: (forall (g : DirectSumField K (T1 + T2)), Finite T1 (fun t : T1 => proj1_sig g (inl t) <> FO K)).
move=> H3.
suff: (forall (g : DirectSumField K (T1 + T2)), Finite T2 (fun t : T2 => proj1_sig g (inr t) <> FO K)).
move=> H4.
suff: (forall (g : DirectSumField K (T1 + T2)), fst (MySumF2 (T1 + T2) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K (PairVS K V1 V2)) (fun t : T1 + T2 => Vmul K (PairVS K V1 V2) (proj1_sig g t) (PairSystemVS K T1 T2 V1 V2 a1 a2 t))) = MySumF2 T1 (exist (Finite T1) (fun t : T1 => proj1_sig g (inl t) <> FO K) (H3 g)) (VSPCM K V1) (fun t : T1 => Vmul K V1 (proj1_sig g (inl t)) (a1 t))).
move=> H5.
suff: (forall (g : DirectSumField K (T1 + T2)), snd (MySumF2 (T1 + T2) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K (PairVS K V1 V2)) (fun t : T1 + T2 => Vmul K (PairVS K V1 V2) (proj1_sig g t) (PairSystemVS K T1 T2 V1 V2 a1 a2 t))) = MySumF2 T2 (exist (Finite T2) (fun t : T2 => proj1_sig g (inr t) <> FO K) (H4 g)) (VSPCM K V2) (fun t : T2 => Vmul K V2 (proj1_sig g (inr t)) (a2 t))).
move=> H6.
apply (InjSurjBij (DirectSumField K (T1 + T2)) (VT K V1 * VT K V2) (fun g : DirectSumField K (T1 + T2) => MySumF2 (T1 + T2) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K (PairVS K V1 V2)) (fun t : T1 + T2 => Vmul K (PairVS K V1 V2) (proj1_sig g t) (PairSystemVS K T1 T2 V1 V2 a1 a2 t)))).
move=> x1 x2 H7.
apply sig_map.
apply functional_extensionality.
elim.
suff: (exist (fun (G : T1 -> FT K) => Finite T1 (fun t : T1 => G t <> FO K)) (fun (t : T1) => proj1_sig x1 (inl t)) (H3 x1) = exist (fun (G : T1 -> FT K) => Finite T1 (fun t : T1 => G t <> FO K)) (fun (t : T1) => proj1_sig x2 (inl t)) (H3 x2)).
move=> H8 t.
suff: (proj1_sig x1 (inl t) = proj1_sig (exist (fun G : T1 -> FT K => Finite T1 (fun t : T1 => G t <> FO K)) (fun t : T1 => proj1_sig x1 (inl t)) (H3 x1)) t).
move=> H9.
rewrite H9.
rewrite H8.
reflexivity.
reflexivity.
suff: (Injective (DirectSumField K T1) (VT K V1) (fun g : DirectSumField K T1 => MySumF2 T1 (exist (Finite T1) (fun t : T1 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V1) (fun t : T1 => Vmul K V1 (proj1_sig g t) (a1 t)))).
move=> H8.
apply (H8 (exist (fun G : T1 -> FT K => Finite T1 (fun t : T1 => G t <> FO K)) (fun t : T1 => proj1_sig x1 (inl t)) (H3 x1)) (exist (fun G : T1 -> FT K => Finite T1 (fun t : T1 => G t <> FO K)) (fun t : T1 => proj1_sig x2 (inl t)) (H3 x2))).
simpl.
rewrite - (H5 x1).
rewrite - (H5 x2).
rewrite H7.
reflexivity.
apply (BijInj (DirectSumField K T1) (VT K V1) (fun g : DirectSumField K T1 => MySumF2 T1 (exist (Finite T1) (fun t : T1 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V1) (fun t : T1 => Vmul K V1 (proj1_sig g t) (a1 t))) H1).
suff: (exist (fun (G : T2 -> FT K) => Finite T2 (fun t : T2 => G t <> FO K)) (fun (t : T2) => proj1_sig x1 (inr t)) (H4 x1) = exist (fun (G : T2 -> FT K) => Finite T2 (fun t : T2 => G t <> FO K)) (fun (t : T2) => proj1_sig x2 (inr t)) (H4 x2)).
move=> H8 t.
suff: (proj1_sig x1 (inr t) = proj1_sig (exist (fun G : T2 -> FT K => Finite T2 (fun t : T2 => G t <> FO K)) (fun t : T2 => proj1_sig x1 (inr t)) (H4 x1)) t).
move=> H9.
rewrite H9.
rewrite H8.
reflexivity.
reflexivity.
suff: (Injective (DirectSumField K T2) (VT K V2) (fun g : DirectSumField K T2 => MySumF2 T2 (exist (Finite T2) (fun t : T2 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V2) (fun t : T2 => Vmul K V2 (proj1_sig g t) (a2 t)))).
move=> H8.
apply (H8 (exist (fun G : T2 -> FT K => Finite T2 (fun t : T2 => G t <> FO K)) (fun t : T2 => proj1_sig x1 (inr t)) (H4 x1)) (exist (fun G : T2 -> FT K => Finite T2 (fun t : T2 => G t <> FO K)) (fun t : T2 => proj1_sig x2 (inr t)) (H4 x2))).
simpl.
rewrite - (H6 x1).
rewrite - (H6 x2).
rewrite H7.
reflexivity.
apply (BijInj (DirectSumField K T2) (VT K V2) (fun g : DirectSumField K T2 => MySumF2 T2 (exist (Finite T2) (fun t : T2 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V2) (fun t : T2 => Vmul K V2 (proj1_sig g t) (a2 t))) H2).
move=> v.
suff: (Surjective (DirectSumField K T1) (VT K V1) (fun g : DirectSumField K T1 => MySumF2 T1 (exist (Finite T1) (fun t : T1 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V1) (fun t : T1 => Vmul K V1 (proj1_sig g t) (a1 t)))).
move=> H7.
suff: (Surjective (DirectSumField K T2) (VT K V2) (fun g : DirectSumField K T2 => MySumF2 T2 (exist (Finite T2) (fun t : T2 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V2) (fun t : T2 => Vmul K V2 (proj1_sig g t) (a2 t)))).
move=> H8.
elim (H7 (fst v)).
move=> x1 H9.
elim (H8 (snd v)).
move=> x2 H10.
suff: (Finite (T1 + T2) (fun t : T1 + T2 => (fun t0 : T1 + T2 => match t0 with
  | inl t0l => proj1_sig x1 t0l
  | inr t0r => proj1_sig x2 t0r
end) t <> FO K)).
move=> H11.
exists (exist (fun (G : T1 + T2 -> FT K) => Finite (T1 + T2) (fun t : T1 + T2 => G t <> FO K)) (fun t0 : T1 + T2 => match t0 with
  | inl t0l => proj1_sig x1 t0l
  | inr t0r => proj1_sig x2 t0r
end) H11).
apply injective_projections.
simpl.
rewrite (H5 (exist (fun (G : T1 + T2 -> FT K) => Finite (T1 + T2) (fun t : T1 + T2 => G t <> FO K)) (fun t0 : T1 + T2 => match t0 with
  | inl t0l => proj1_sig x1 t0l
  | inr t0r => proj1_sig x2 t0r
end) H11)).
simpl.
suff: ((exist (Finite T1) (fun t : T1 => proj1_sig x1 t <> FO K) (H3 (exist (fun G : T1 + T2 -> FT K => Finite (T1 + T2) (fun t : T1 + T2 => G t <> FO K)) (fun t0 : T1 + T2 => match t0 with
  | inl t0l => proj1_sig x1 t0l
  | inr t0r => proj1_sig x2 t0r
end) H11))) = (exist (Finite T1) (fun t : T1 => proj1_sig x1 t <> FO K) (proj2_sig x1))).
move=> H12.
rewrite H12.
apply H9.
apply sig_map.
reflexivity.
simpl.
rewrite (H6 (exist (fun (G : T1 + T2 -> FT K) => Finite (T1 + T2) (fun t : T1 + T2 => G t <> FO K)) (fun t0 : T1 + T2 => match t0 with
  | inl t0l => proj1_sig x1 t0l
  | inr t0r => proj1_sig x2 t0r
end) H11)).
simpl.
suff: ((exist (Finite T2) (fun t : T2 => proj1_sig x2 t <> FO K) (H4 (exist (fun G : T1 + T2 -> FT K => Finite (T1 + T2) (fun t : T1 + T2 => G t <> FO K)) (fun t0 : T1 + T2 => match t0 with
  | inl t0l => proj1_sig x1 t0l
  | inr t0r => proj1_sig x2 t0r
end) H11))) = (exist (Finite T2) (fun t : T2 => proj1_sig x2 t <> FO K) (proj2_sig x2))).
move=> H12.
rewrite H12.
apply H10.
apply sig_map.
reflexivity.
suff: ((fun t : T1 + T2 => match t with
  | inl t0l => proj1_sig x1 t0l
  | inr t0r => proj1_sig x2 t0r
end <> FO K) = Union (T1 + T2) (fun t : T1 + T2 => match t with
  | inl t0l => proj1_sig x1 t0l <> FO K
  | inr _ => False
end) (fun t : T1 + T2 => match t with
  | inl _ => False
  | inr t0r => proj1_sig x2 t0r <> FO K
end)).
move=> H11.
rewrite H11.
apply (Union_preserves_Finite (T1 + T2) (fun t : T1 + T2 => match t with
  | inl t0l => proj1_sig x1 t0l <> FO K
  | inr _ => False
end) (fun t : T1 + T2 => match t with
  | inl _ => False
  | inr t0r => proj1_sig x2 t0r <> FO K
end)).
suff: ((fun t : T1 + T2 => match t with
  | inl t0l => proj1_sig x1 t0l <> FO K
  | inr _ => False
end) = Im T1 (T1 + T2) (fun (t : T1) => proj1_sig x1 t <> FO K) inl).
move=> H12.
rewrite H12.
apply (finite_image T1 (T1 + T2) (fun t : T1 => proj1_sig x1 t <> FO K) inl).
apply (proj2_sig x1).
apply Extensionality_Ensembles.
apply conj.
unfold Included.
unfold In.
elim.
move=> t1 H12.
apply (Im_intro T1 (T1 + T2) (fun t : T1 => proj1_sig x1 t <> FO K) inl t1).
apply H12.
reflexivity.
move=> t2 H12.
apply False_ind.
apply H12.
move=> t.
elim.
move=> t1 H12 tt H13.
rewrite H13.
apply H12.
suff: ((fun t : T1 + T2 => match t with
  | inl _ => False
  | inr t0r => proj1_sig x2 t0r <> FO K
end) = Im T2 (T1 + T2) (fun (t : T2) => proj1_sig x2 t <> FO K) inr).
move=> H12.
rewrite H12.
apply (finite_image T2 (T1 + T2) (fun t : T2 => proj1_sig x2 t <> FO K) inr).
apply (proj2_sig x2).
apply Extensionality_Ensembles.
apply conj.
unfold Included.
unfold In.
elim.
move=> t1 H12.
apply False_ind.
apply H12.
move=> t2 H12.
apply (Im_intro T2 (T1 + T2) (fun t : T2 => proj1_sig x2 t <> FO K) inr t2).
apply H12.
reflexivity.
move=> t.
elim.
move=> t2 H12 tt H13.
rewrite H13.
apply H12.
apply Extensionality_Ensembles.
apply conj.
unfold Included.
unfold In.
elim.
move=> t1 H11.
left.
apply H11.
move=> t2 H11.
right.
apply H11.
unfold Included.
unfold In.
elim.
move=> t1 H11.
suff: (In (T1 + T2) (fun t : T1 + T2 => match t with
  | inl t0l => proj1_sig x1 t0l <> FO K
  | inr _ => False
end) (inl t1) \/ In (T1 + T2) (fun t : T1 + T2 => match t with
  | inl _ => False
  | inr t0r => proj1_sig x2 t0r <> FO K
end) (inl t1)).
elim.
apply.
move=> H12 H13.
apply H12.
elim H11.
move=> t12 H12.
left.
apply H12.
move=> t12 H12.
right.
apply H12.
move=> t2 H11.
suff: (In (T1 + T2) (fun t : T1 + T2 => match t with
  | inl t0l => proj1_sig x1 t0l <> FO K
  | inr _ => False
end) (inr t2) \/ In (T1 + T2) (fun t : T1 + T2 => match t with
  | inl _ => False
  | inr t0r => proj1_sig x2 t0r <> FO K
end) (inr t2)).
elim.
move=> H12 H13.
apply H12.
apply.
elim H11.
move=> t12 H12.
left.
apply H12.
move=> t12 H12.
right.
apply H12.
apply (BijSurj (DirectSumField K T2) (VT K V2) (fun g : DirectSumField K T2 => MySumF2 T2 (exist (Finite T2) (fun t : T2 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V2) (fun t : T2 => Vmul K V2 (proj1_sig g t) (a2 t))) H2).
apply (BijSurj (DirectSumField K T1) (VT K V1) (fun g : DirectSumField K T1 => MySumF2 T1 (exist (Finite T1) (fun t : T1 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V1) (fun t : T1 => Vmul K V1 (proj1_sig g t) (a1 t))) H1).
move=> g.
rewrite (MySumF2Excluded (T1 + T2) (VSPCM K (PairVS K V1 V2)) (fun t : T1 + T2 => Vmul K (PairVS K V1 V2) (proj1_sig g t) (PairSystemVS K T1 T2 V1 V2 a1 a2 t)) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (fun t : T1 + T2 => match t with
  | inl t1 => False
  | inr t2 => True
end)).
simpl.
suff: ((snd (MySumF2 (T1 + T2) (FiniteIntersection (T1 + T2) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (Complement (T1 + T2) (fun t : T1 + T2 => match t with
  | inl _ => False
  | inr _ => True
end))) (VSPCM K (PairVS K V1 V2)) (fun t : T1 + T2 => PairVSVmul K V1 V2 (proj1_sig g t) (PairSystemVS K T1 T2 V1 V2 a1 a2 t)))) = VO K V2).
move=> H6.
rewrite H6.
rewrite (Vadd_O_r K V2).
rewrite - (MySumF2BijectiveSame T2 (exist (Finite T2) (fun t : T2 => proj1_sig g (inr t) <> FO K) (H4 g)) (T1 + T2) (FiniteIntersection (T1 + T2) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (fun t : T1 + T2 => match t with
  | inl _ => False
  | inr _ => True
end)) (VSPCM K (PairVS K V1 V2)) (fun t : T1 + T2 => PairVSVmul K V1 V2 (proj1_sig g t) (PairSystemVS K T1 T2 V1 V2 a1 a2 t)) inr).
apply (FiniteSetInduction T2 (exist (Finite T2) (fun t : T2 => proj1_sig g (inr t) <> FO K) (H4 g))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H7 H8 H9 H10.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H10.
reflexivity.
apply H9.
apply H9.
simpl.
move=> t2 H7.
apply (Intersection_intro (T1 + T2) (fun t : T1 + T2 => match t with
  | inl _ => False
  | inr _ => True
end) (fun t : T1 + T2 => proj1_sig g t <> FO K) (inr t2)).
apply I.
apply H7.
move=> H7.
apply InjSurjBij.
move=> u1 u2 H8.
apply sig_map.
suff: (inr T1 (proj1_sig u1) = inr T1 (proj1_sig u2)).
move=> H9.
suff: (proj1_sig u1 = let temp := (fun (t : T1 + T2) => match t with 
  | inl _ => proj1_sig u1
  | inr t2 => t2
end) in temp (inr (proj1_sig u1))).
move=> H10.
rewrite H10.
rewrite H9.
reflexivity.
reflexivity.
suff: (inr (proj1_sig u1) = proj1_sig (exist (proj1_sig (FiniteIntersection (T1 + T2) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (fun t : T1 + T2 => match t with
  | inl _ => False
  | inr _ => True
end))) (inr (proj1_sig u1)) (H7 (proj1_sig u1) (proj2_sig u1)))).
move=> H9.
rewrite H9.
rewrite H8.
reflexivity.
reflexivity.
move=> u.
suff: (exists x : {u0 : T2 | proj1_sig (exist (Finite T2) (fun t : T2 => proj1_sig g (inr t) <> FO K) (H4 g)) u0}, proj1_sig (exist (proj1_sig (FiniteIntersection (T1 + T2) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (fun t : T1 + T2 => match t with
  | inl _ => False
  | inr _ => True
end))) (inr (proj1_sig x)) (H7 (proj1_sig x) (proj2_sig x))) = proj1_sig u).
elim.
move=> x H8.
exists x.
apply sig_map.
apply H8.
suff: (In (T1 + T2) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj1_sig u)).
suff: (In (T1 + T2) (fun t : T1 + T2 => match t with
  | inl _ => False
  | inr _ => True
end) (proj1_sig u)).
elim (proj1_sig u).
move=> t1 H8.
apply False_ind.
apply H8.
move=> t2 H8 H9.
exists (exist (fun (u0 : T2) => proj1_sig (exist (Finite T2) (fun t : T2 => proj1_sig g (inr t) <> FO K) (H4 g)) u0) t2 H9).
reflexivity.
elim (proj2_sig u).
move=> t H8 H9.
apply H8.
elim (proj2_sig u).
move=> t H8 H9.
apply H9.
apply (FiniteSetInduction (T1 + T2) (FiniteIntersection (T1 + T2) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (Complement (T1 + T2) (fun t : T1 + T2 => match t with
  | inl _ => False
  | inr _ => True
end)))).
apply conj.
rewrite MySumF2Empty.
reflexivity.
move=> B b H6 H7 H8 H9.
rewrite MySumF2Add.
simpl.
rewrite H9.
suff: ((Vmul K V2 (proj1_sig g b) (snd (PairSystemVS K T1 T2 V1 V2 a1 a2 b))) = VO K V2).
move=> H10.
rewrite H10.
apply (Vadd_O_r K V2 (VO K V2)).
elim H7.
elim.
move=> a H10 H11.
simpl.
apply (Vmul_O_r K V2 (proj1_sig g (inl a))).
move=> a H10 H11.
apply False_ind.
apply H10.
apply I.
apply H8.
move=> g.
rewrite (MySumF2Excluded (T1 + T2) (VSPCM K (PairVS K V1 V2)) (fun t : T1 + T2 => Vmul K (PairVS K V1 V2) (proj1_sig g t) (PairSystemVS K T1 T2 V1 V2 a1 a2 t)) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (fun t : T1 + T2 => match t with
  | inl t1 => True
  | inr t2 => False
end)).
simpl.
suff: ((fst (MySumF2 (T1 + T2) (FiniteIntersection (T1 + T2) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (Complement (T1 + T2) (fun t : T1 + T2 => match t with
  | inl _ => True
  | inr _ => False
end))) (VSPCM K (PairVS K V1 V2)) (fun t : T1 + T2 => PairVSVmul K V1 V2 (proj1_sig g t) (PairSystemVS K T1 T2 V1 V2 a1 a2 t)))) = VO K V1).
move=> H5.
rewrite H5.
rewrite (Vadd_O_r K V1).
rewrite - (MySumF2BijectiveSame T1 (exist (Finite T1) (fun t : T1 => proj1_sig g (inl t) <> FO K) (H3 g)) (T1 + T2) (FiniteIntersection (T1 + T2) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (fun t : T1 + T2 => match t with
  | inl _ => True
  | inr _ => False
end)) (VSPCM K (PairVS K V1 V2)) (fun t : T1 + T2 => PairVSVmul K V1 V2 (proj1_sig g t) (PairSystemVS K T1 T2 V1 V2 a1 a2 t)) inl).
apply (FiniteSetInduction T1 (exist (Finite T1) (fun t : T1 => proj1_sig g (inl t) <> FO K) (H3 g))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H6 H7 H8 H9.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H9.
reflexivity.
apply H8.
apply H8.
simpl.
move=> t1 H6.
apply (Intersection_intro (T1 + T2) (fun t : T1 + T2 => match t with
  | inl _ => True
  | inr _ => False
end) (fun t : T1 + T2 => proj1_sig g t <> FO K) (inl t1)).
apply I.
apply H6.
move=> H6.
apply InjSurjBij.
move=> u1 u2 H7.
apply sig_map.
suff: (inl T2 (proj1_sig u1) = inl T2 (proj1_sig u2)).
move=> H8.
suff: (proj1_sig u1 = let temp := (fun (t : T1 + T2) => match t with 
  | inl t1 => t1
  | inr t2 => proj1_sig u1
end) in temp (inl (proj1_sig u1))).
move=> H9.
rewrite H9.
rewrite H8.
reflexivity.
reflexivity.
suff: (inl (proj1_sig u1) = proj1_sig (exist (proj1_sig (FiniteIntersection (T1 + T2) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (fun t : T1 + T2 => match t with
  | inl _ => True
  | inr _ => False
end))) (inl (proj1_sig u1)) (H6 (proj1_sig u1) (proj2_sig u1)))).
move=> H8.
rewrite H8.
rewrite H7.
reflexivity.
reflexivity.
move=> u.
suff: (exists  x : {u0 : T1 | proj1_sig (exist (Finite T1) (fun t : T1 => proj1_sig g (inl t) <> FO K) (H3 g)) u0}, proj1_sig (exist (proj1_sig (FiniteIntersection (T1 + T2) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (fun t : T1 + T2 => match t with
  | inl _ => True
  | inr _ => False
end))) (inl (proj1_sig x)) (H6 (proj1_sig x) (proj2_sig x))) = proj1_sig u).
elim.
move=> x H7.
exists x.
apply sig_map.
apply H7.
suff: (In (T1 + T2) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj1_sig u)).
suff: (In (T1 + T2) (fun t : T1 + T2 => match t with
  | inl _ => True
  | inr _ => False
end) (proj1_sig u)).
elim (proj1_sig u).
move=> t1 H7 H8.
exists (exist (fun (u0 : T1) => proj1_sig (exist (Finite T1) (fun t : T1 => proj1_sig g (inl t) <> FO K) (H3 g)) u0) t1 H8).
reflexivity.
move=> t2 H7.
apply False_ind.
apply H7.
elim (proj2_sig u).
move=> t H7 H8.
apply H7.
elim (proj2_sig u).
move=> t H7 H8.
apply H8.
apply (FiniteSetInduction (T1 + T2) (FiniteIntersection (T1 + T2) (exist (Finite (T1 + T2)) (fun t : T1 + T2 => proj1_sig g t <> FO K) (proj2_sig g)) (Complement (T1 + T2) (fun t : T1 + T2 => match t with
  | inl _ => True
  | inr _ => False
end)))).
apply conj.
rewrite MySumF2Empty.
reflexivity.
move=> B b H5 H6 H7 H8.
rewrite MySumF2Add.
simpl.
rewrite H8.
suff: ((Vmul K V1 (proj1_sig g b) (fst (PairSystemVS K T1 T2 V1 V2 a1 a2 b))) = VO K V1).
move=> H9.
rewrite H9.
apply (Vadd_O_r K V1 (VO K V1)).
elim H6.
elim.
move=> a H9 H10.
apply False_ind.
apply H9.
apply I.
simpl.
move=> a H9 H10.
apply (Vmul_O_r K V1 (proj1_sig g (inr a))).
apply H7.
move=> g.
elim (classic (Inhabited T2 (fun t : T2 => proj1_sig g (inr t) <> FO K))).
elim.
move=> t2 H4.
suff: ((fun t : T2 => proj1_sig g (inr t) <> FO K) = Im (T1 + T2) T2 (fun t : T1 + T2 => proj1_sig g t <> FO K) (fun t : T1 + T2 => match t with
  | inl _ => t2
  | inr t0 => t0
end)).
move=> H5.
rewrite H5.
apply (finite_image (T1 + T2) T2 (fun t : T1 + T2 => proj1_sig g t <> FO K) (fun t : T1 + T2 => match t with
  | inl _ => t2
  | inr t0 => t0
end)).
apply (proj2_sig g).
apply Extensionality_Ensembles.
apply conj.
move=> t H5.
exists (inr t).
apply H5.
reflexivity.
move=> t12.
elim.
move=> t0 H5 t1 H6.
rewrite H6.
move: H5.
elim t0.
move=> a H7.
apply H4.
move=> b.
apply.
move=> H4.
suff: ((fun t : T2 => proj1_sig g (inr t) <> FO K) = Empty_set T2).
move=> H5.
rewrite H5.
apply Empty_is_finite.
apply Extensionality_Ensembles.
apply conj.
move=> t H5.
apply False_ind.
apply H4.
apply (Inhabited_intro T2 (fun t0 : T2 => proj1_sig g (inr t0) <> FO K) t H5).
move=> t.
elim.
move=> g.
elim (classic (Inhabited T1 (fun t : T1 => proj1_sig g (inl t) <> FO K))).
elim.
move=> t1 H3.
suff: ((fun t : T1 => proj1_sig g (inl t) <> FO K) = Im (T1 + T2) T1 (fun t : T1 + T2 => proj1_sig g t <> FO K) (fun t : T1 + T2 => match t with
  | inl t0 => t0
  | inr _ => t1
end)).
move=> H4.
rewrite H4.
apply (finite_image (T1 + T2) T1 (fun t : T1 + T2 => proj1_sig g t <> FO K) (fun t : T1 + T2 => match t with
  | inl t0 => t0
  | inr _ => t1
end)).
apply (proj2_sig g).
apply Extensionality_Ensembles.
apply conj.
move=> t H4.
exists (inl t).
apply H4.
reflexivity.
move=> t12.
elim.
move=> t0 H4 t2 H5.
rewrite H5.
move: H4.
elim t0.
move=> a H6.
apply H6.
move=> b H6.
apply H3.
move=> H3.
suff: ((fun t : T1 => proj1_sig g (inl t) <> FO K) = Empty_set T1).
move=> H4.
rewrite H4.
apply Empty_is_finite.
apply Extensionality_Ensembles.
apply conj.
move=> t H4.
apply False_ind.
apply H3.
apply (Inhabited_intro T1 (fun t0 : T1 => proj1_sig g (inl t0) <> FO K) t H4).
move=> t.
elim.
Qed.

Definition DirectProdVST (K : Field) (T : Type) (V : T -> VectorSpace K) := forall (t : T), VT K (V t).

Definition DirectProdVSVO (K : Field) (T : Type) (V : T -> VectorSpace K) := fun (t : T) => VO K (V t).

Definition DirectProdVSVadd (K : Field) (T : Type) (V : T -> VectorSpace K) := fun (v1 v2 : DirectProdVST K T V) (t : T) => Vadd K (V t) (v1 t) (v2 t).

Definition DirectProdVSVmul (K : Field) (T : Type) (V : T -> VectorSpace K) := fun (f : FT K) (v : DirectProdVST K T V) (t : T) => Vmul K (V t) f (v t).

Definition DirectProdVSVopp (K : Field) (T : Type) (V : T -> VectorSpace K) := fun (v : DirectProdVST K T V) (t : T) => Vopp K (V t) (v t).

Lemma DirectProdVSVadd_comm : forall (K : Field) (T : Type) (V : T -> VectorSpace K) (v1 v2 : DirectProdVST K T V), DirectProdVSVadd K T V v1 v2 = DirectProdVSVadd K T V v2 v1.
Proof.
move=> K T V v1 v2.
unfold DirectProdVSVadd.
apply functional_extensionality_dep.
move=> t.
apply (Vadd_comm K (V t) (v1 t) (v2 t)).
Qed.

Lemma DirectProdVSVadd_assoc : forall (K : Field) (T : Type) (V : T -> VectorSpace K) (v1 v2 v3 : DirectProdVST K T V), DirectProdVSVadd K T V (DirectProdVSVadd K T V v1 v2) v3 = DirectProdVSVadd K T V v1 (DirectProdVSVadd K T V v2 v3).
Proof.
move=> K T V v1 v2 v3.
apply functional_extensionality_dep.
move=> t.
apply (Vadd_assoc K (V t) (v1 t) (v2 t) (v3 t)).
Qed.

Lemma DirectProdVSVadd_O_l : forall (K : Field) (T : Type) (V : T -> VectorSpace K) (v : DirectProdVST K T V), DirectProdVSVadd K T V (DirectProdVSVO K T V) v = v.
Proof.
move=> K T V v.
apply functional_extensionality_dep.
move=> t.
apply (Vadd_O_l K (V t) (v t)).
Qed.

Lemma DirectProdVSVadd_opp_r : forall (K : Field) (T : Type) (V : T -> VectorSpace K) (v : DirectProdVST K T V), DirectProdVSVadd K T V v (DirectProdVSVopp K T V v) = DirectProdVSVO K T V.
Proof.
move=> K T V v.
apply functional_extensionality_dep.
move=> t.
apply (Vadd_opp_r K (V t) (v t)).
Qed.

Lemma DirectProdVSVmul_add_distr_l : forall (K : Field) (T : Type) (V : T -> VectorSpace K) (f : FT K) (v1 v2 : DirectProdVST K T V), DirectProdVSVmul K T V f (DirectProdVSVadd K T V v1 v2) = (DirectProdVSVadd K T V (DirectProdVSVmul K T V f v1) (DirectProdVSVmul K T V f v2)).
Proof.
move=> K T V f v1 v2.
apply functional_extensionality_dep.
move=> t.
apply (Vmul_add_distr_l K (V t) f (v1 t) (v2 t)).
Qed.

Lemma DirectProdVSVmul_add_distr_r : forall (K : Field) (T : Type) (V : T -> VectorSpace K) (f1 f2 : FT K) (v : DirectProdVST K T V), (DirectProdVSVmul K T V (Fadd K f1 f2) v) = (DirectProdVSVadd K T V (DirectProdVSVmul K T V f1 v) (DirectProdVSVmul K T V f2 v)).
Proof.
move=> K T V f1 f2 v.
apply functional_extensionality_dep.
move=> t.
apply (Vmul_add_distr_r K (V t) f1 f2 (v t)).
Qed.

Lemma DirectProdVSVmul_assoc : forall (K : Field) (T : Type) (V : T -> VectorSpace K) (f1 f2 : FT K) (v : DirectProdVST K T V), (DirectProdVSVmul K T V f1 (DirectProdVSVmul K T V f2 v)) = (DirectProdVSVmul K T V (Fmul K f1 f2) v).
Proof.
move=> K T V f1 f2 v.
apply functional_extensionality_dep.
move=> t.
apply (Vmul_assoc K (V t) f1 f2 (v t)).
Qed.

Lemma DirectProdVSVmul_I_l : forall (K : Field) (T : Type) (V : T -> VectorSpace K) (v : DirectProdVST K T V), (DirectProdVSVmul K T V (FI K) v) = v.
Proof.
move=> K T V v.
apply functional_extensionality_dep.
move=> t.
apply (Vmul_I_l K (V t) (v t)).
Qed.

Definition DirectProdVS (K : Field) (T : Type) (V : T -> VectorSpace K) := mkVectorSpace K (DirectProdVST K T V) (DirectProdVSVO K T V) (DirectProdVSVadd K T V) (DirectProdVSVmul K T V) (DirectProdVSVopp K T V) (DirectProdVSVadd_comm K T V) (DirectProdVSVadd_assoc K T V) (DirectProdVSVadd_O_l K T V) (DirectProdVSVadd_opp_r K T V) (DirectProdVSVmul_add_distr_l K T V) (DirectProdVSVmul_add_distr_r K T V) (DirectProdVSVmul_assoc K T V) (DirectProdVSVmul_I_l K T V).

Definition DirectProdSystemVS (K : Field) (T : Type) (tf : T -> Type) (V : T -> VectorSpace K) (a : forall (t : T), (tf t) -> (VT K (V t))) := fun (t : sumT T tf) => match t with
  | inT t0 ti => fun (t1 : T) => match (excluded_middle_informative (t0 = t1)) with
     | left H => a t1 (TypeEqConvert (tf t0) (tf t1) (f_equal tf H) ti)
     | right _ => VO K (V t1)
  end
end.

Lemma DirectProductBasisVS : forall (K : Field) (N : nat) (T : {n : nat | n < N} -> Type) (V : {n : nat | n < N} -> VectorSpace K) (a : forall (t : {n : nat | n < N}), (T t) -> (VT K (V t))), (forall (k : {n : nat | n < N}), (BasisVS K (V k) (T k) (a k))) -> (BasisVS K (DirectProdVS K {n : nat | n < N} V) (sumT {n : nat | n < N} T) (DirectProdSystemVS K {n : nat | n < N} T V a)).
Proof.
move=> K N T V a H1.
suff: (forall (v : DirectSumField K (sumT {n : nat | n < N} T)) (m : {n : nat | n < N}), Finite (T m) (fun (t : T m) => proj1_sig v (inT {n : nat | n < N} T m t) <> FO K)).
move=> H2.
suff: (forall (v : DirectSumField K (sumT {n : nat | n < N} T)) (m : {n : nat | n < N}), MySumF2 (T m) (exist (Finite (T m)) (fun t0 : T m => proj1_sig v (inT {n : nat | n < N} T m t0) <> FO K) (H2 v m)) (VSPCM K (V m)) (fun t0 : T m => Vmul K (V m) (proj1_sig v (inT {n : nat | n < N} T m t0)) (a m t0)) = (MySumF2 (sumT {n : nat | n < N} T) (exist (Finite (sumT {n : nat | n < N} T)) (fun t : sumT {n : nat | n < N} T => proj1_sig v t <> FO K) (proj2_sig v)) (VSPCM K (DirectProdVS K {n : nat | n < N} V)) (fun t : sumT {n : nat | n < N} T => Vmul K (DirectProdVS K {n : nat | n < N} V) (proj1_sig v t) (DirectProdSystemVS K {n : nat | n < N} T V a t))) m).
move=> H3.
apply (InjSurjBij (DirectSumField K (sumT {n : nat | n < N} T)) (VT K (DirectProdVS K {n : nat | n < N} V))).
move=> v1 v2 H4.
apply sig_map.
apply functional_extensionality.
elim.
move=> m t.
suff: (exist (fun (G : T m -> FT K) => Finite (T m) (fun t : T m => G t <> FO K)) (fun (t : T m) => proj1_sig v1 (inT {n : nat | n < N} T m t)) (H2 v1 m) = exist (fun (G : T m -> FT K) => Finite (T m) (fun t : T m => G t <> FO K)) (fun (t : T m) => proj1_sig v2 (inT {n : nat | n < N} T m t)) (H2 v2 m)).
move=> H5.
suff: (proj1_sig v1 (inT {n : nat | n < N} T m t) = proj1_sig (exist (fun G : T m -> FT K => Finite (T m) (fun t : T m => G t <> FO K)) (fun t : T m => proj1_sig v1 (inT {n : nat | n < N} T m t)) (H2 v1 m)) t).
move=> H6.
rewrite H6.
rewrite H5.
reflexivity.
reflexivity.
apply (BijInj (DirectSumField K (T m)) (VT K (V m)) (fun (g : DirectSumField K (T m)) => MySumF2 (T m) (exist (Finite (T m)) (fun t : T m => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K (V m)) (fun t : T m => Vmul K (V m) (proj1_sig g t) (a m t)))).
apply (H1 m).
simpl.
rewrite (H3 v1 m).
rewrite (H3 v2 m).
rewrite H4.
reflexivity.
suff: (forall (m : {n : nat | n < N}), {f : (VT K (V m)) -> (DirectSumField K (T m)) | (forall (x : DirectSumField K (T m)), f ((fun g : DirectSumField K (T m) => MySumF2 (T m) (exist (Finite (T m)) (fun t : T m => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K (V m)) (fun t : T m => Vmul K (V m) (proj1_sig g t) (a m t))) x) = x) /\ (forall (y : VT K (V m)), (fun g : DirectSumField K (T m) => MySumF2 (T m) (exist (Finite (T m)) (fun t : T m => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K (V m)) (fun t : T m => Vmul K (V m) (proj1_sig g t) (a m t))) (f y) = y)}).
move=> H4 v.
suff: (Finite (sumT {n : nat | n < N} T) (fun (t : sumT {n : nat | n < N} T) => match t with
  | inT m t0 => proj1_sig (proj1_sig (H4 m) (v m)) t0
end <> FO K)).
move=> H5.
exists (exist (fun (G : (sumT {n : nat | n < N} T) -> (FT K)) => Finite (sumT {n : nat | n < N} T) (fun t : (sumT {n : nat | n < N} T) => G t <> FO K)) (fun (t : sumT {n : nat | n < N} T) => match t with
  | inT m t0 => proj1_sig (proj1_sig (H4 m) (v m)) t0
end) H5).
apply functional_extensionality_dep.
move=> m.
simpl.
rewrite - (H3 (exist (fun (G : (sumT {n : nat | n < N} T) -> (FT K)) => Finite (sumT {n : nat | n < N} T) (fun t : (sumT {n : nat | n < N} T) => G t <> FO K)) (fun (t : sumT {n : nat | n < N} T) => match t with
  | inT m t0 => proj1_sig (proj1_sig (H4 m) (v m)) t0
end) H5) m).
simpl.
suff: ((H2 (exist (fun G : sumT {n : nat | n < N} T -> FT K => Finite (sumT {n : nat | n < N} T) (fun t : sumT {n : nat | n < N} T => G t <> FO K)) (fun t : sumT {n : nat | n < N} T => match t with
  | inT m0 t0 => proj1_sig (proj1_sig (H4 m0) (v m0)) t0
end) H5) m) = (proj2_sig (proj1_sig (H4 m) (v m)))).
move=> H6.
rewrite H6.
apply (proj2 (proj2_sig (H4 m)) (v m)).
apply proof_irrelevance.
suff: (forall (k : nat), k <= N -> Finite (sumT {n : nat | n < N} T) (fun t : sumT {n : nat | n < N} T => match t with
  | inT m t0 => proj1_sig (proj1_sig (H4 m) (v m)) t0 <> FO K /\ proj1_sig m < k 
end)).
move=> H5.
suff: ( (fun t : sumT {n : nat | n < N} T => match t with
  | inT m t0 => proj1_sig (proj1_sig (H4 m) (v m)) t0
end <> FO K) = (fun t : sumT {n : nat | n < N} T => match t with
  | inT m t0 => proj1_sig (proj1_sig (H4 m) (v m)) t0 <> FO K /\ proj1_sig m < N
end)).
move=> H6.
rewrite H6.
apply (H5 N (le_n N)).
apply Extensionality_Ensembles.
apply conj.
unfold Included.
unfold In.
elim.
move=> m t H6.
apply conj.
apply H6.
apply (proj2_sig m).
unfold Included.
unfold In.
elim.
move=> m t H6.
apply (proj1 H6).
suff: (forall (m0 : {n : nat | n < N}), Finite (sumT {n : nat | n < N} T) (fun t : sumT {n : nat | n < N} T => match t with
  | inT m t0 => proj1_sig (proj1_sig (H4 m) (v m)) t0 <> FO K /\ m = m0
end)).
move=> H5.
elim.
move=> H6.
suff: ((fun t : sumT {n : nat | n < N} T => match t with
  | inT m t0 => proj1_sig (proj1_sig (H4 m) (v m)) t0 <> FO K /\ proj1_sig m < 0
end) = Empty_set (sumT {n : nat | n < N} T)).
move=> H7.
rewrite H7.
apply (Empty_is_finite (sumT {n : nat | n < N} T)).
apply Extensionality_Ensembles.
apply conj.
elim.
move=> m t.
elim.
move=> H7 H8.
apply False_ind.
apply (lt_not_le (proj1_sig m) 0 H8 (le_0_n (proj1_sig m))).
move=> t.
elim.
move=> k H6 H7.
suff: ((fun t : sumT {n0 : nat | n0 < N} T => match t with
  | inT m t0 => proj1_sig (proj1_sig (H4 m) (v m)) t0 <> FO K /\ proj1_sig m < S k
end) = Union (sumT {n0 : nat | n0 < N} T) (fun t : sumT {n0 : nat | n0 < N} T => match t with
  | inT m t0 => proj1_sig (proj1_sig (H4 m) (v m)) t0 <> FO K /\ proj1_sig m < k
end) (fun t : sumT {n : nat | n < N} T => match t with
  | inT m t0 => proj1_sig (proj1_sig (H4 m) (v m)) t0 <> FO K /\ m = (exist (fun (n : nat) => n < N) k H7)
end)).
move=> H8.
rewrite H8.
apply (Union_preserves_Finite (sumT {n : nat | n < N} T) (fun t : sumT {n0 : nat | n0 < N} T => match t with
  | inT m t0 => proj1_sig (proj1_sig (H4 m) (v m)) t0 <> FO K /\ proj1_sig m < k
end) (fun t : sumT {n : nat | n < N} T => match t with
  | inT m t0 => proj1_sig (proj1_sig (H4 m) (v m)) t0 <> FO K /\ m = exist (fun n : nat => n < N) k H7
end)).
apply H6.
apply (le_trans k (S k) N (le_S k k (le_n k)) H7).
apply (H5 (exist (fun n : nat => n < N) k H7)).
apply Extensionality_Ensembles.
apply conj.
unfold Included.
unfold In.
elim.
move=> m t H8.
elim (le_lt_or_eq (proj1_sig m) k).
move=> H9.
left.
apply conj.
apply (proj1 H8).
apply H9.
move=> H9.
right.
apply conj.
apply (proj1 H8).
apply sig_map.
apply H9.
apply (le_S_n (proj1_sig m) k (proj2 H8)).
move=> t.
elim.
elim.
move=> m t0 H8.
apply conj.
apply (proj1 H8).
apply (le_trans (S (proj1_sig m)) k (S k) (proj2 H8) (le_S k k (le_n k))).
elim.
move=> m t0 H8.
apply conj.
apply (proj1 H8).
rewrite (proj2 H8).
apply (le_n (S k)).
move=> m0.
suff: ((fun t : sumT {n : nat | n < N} T => match t with
  | inT m t0 => proj1_sig (proj1_sig (H4 m) (v m)) t0 <> FO K /\ m = m0
end) = Im (T m0) (sumT {n : nat | n < N} T) (fun t0 : T m0 => proj1_sig (proj1_sig (H4 m0) (v m0)) t0 <> FO K) (inT {n : nat | n < N} T m0)).
move=> H5.
rewrite H5.
apply (finite_image (T m0) (sumT {n : nat | n < N} T) (fun t0 : T m0 => proj1_sig (proj1_sig (H4 m0) (v m0)) t0 <> FO K) (inT {n : nat | n < N} T m0)).
apply (proj2_sig (proj1_sig (H4 m0) (v m0))).
apply Extensionality_Ensembles.
apply conj.
elim.
move=> m t H5.
rewrite - (proj2 H5).
apply (Im_intro (T m) (sumT {n : nat | n < N} T) (fun t0 : T m => proj1_sig (proj1_sig (H4 m) (v m)) t0 <> FO K) (inT {n : nat | n < N} T m) t).
apply (proj1 H5).
reflexivity.
move=> t.
elim.
move=> t0 H5 y H6.
rewrite H6.
apply conj.
apply H5.
reflexivity.
move=> m.
apply constructive_definite_description.
apply (proj1 (unique_existence (fun x : VT K (V m) -> DirectSumField K (T m) => (forall x0 : DirectSumField K (T m), x (MySumF2 (T m) (exist (Finite (T m)) (fun t : T m => proj1_sig x0 t <> FO K) (proj2_sig x0)) (VSPCM K (V m)) (fun t : T m => Vmul K (V m) (proj1_sig x0 t) (a m t))) = x0) /\ (forall y : VT K (V m), MySumF2 (T m) (exist (Finite (T m)) (fun t : T m => proj1_sig (x y) t <> FO K) (proj2_sig (x y))) (VSPCM K (V m)) (fun t : T m => Vmul K (V m) (proj1_sig (x y) t) (a m t)) = y)))).
apply conj.
apply (H1 m).
move=> x1 x2 H4 H5.
apply functional_extensionality.
move=> v.
unfold BasisVS in H1.
apply (BijInj (DirectSumField K (T m)) (VT K (V m)) (fun g : DirectSumField K (T m) => MySumF2 (T m) (exist (Finite (T m)) (fun t : T m => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K (V m)) (fun t : T m => Vmul K (V m) (proj1_sig g t) (a m t))) (H1 m)).
rewrite (proj2 H5 v).
apply (proj2 H4 v).
move=> v m.
rewrite (MySumF2Excluded (sumT {n : nat | n < N} T) (VSPCM K (DirectProdVS K {n : nat | n < N} V)) (fun t : sumT {n : nat | n < N} T => Vmul K (DirectProdVS K {n : nat | n < N} V) (proj1_sig v t) (DirectProdSystemVS K {n : nat | n < N} T V a t)) (exist (Finite (sumT {n : nat | n < N} T)) (fun t : sumT {n : nat | n < N} T => proj1_sig v t <> FO K) (proj2_sig v)) (fun t : sumT {n : nat | n < N} T => match t with
  | inT m0 _ => m0 = m
end)).
simpl.
unfold DirectProdVSVadd.
suff: (MySumF2 (sumT {n : nat | n < N} T) (FiniteIntersection (sumT {n : nat | n < N} T) (exist (Finite (sumT {n : nat | n < N} T)) (fun t : sumT {n : nat | n < N} T => proj1_sig v t <> FO K) (proj2_sig v)) (Complement (sumT {n : nat | n < N} T) (fun t : sumT {n : nat | n < N} T => match t with
  | inT m0 _ => m0 = m
end))) (VSPCM K (DirectProdVS K {n : nat | n < N} V)) (fun t : sumT {n : nat | n < N} T => DirectProdVSVmul K {n : nat | n < N} V (proj1_sig v t) (DirectProdSystemVS K {n : nat | n < N} T V a t)) m = VO K (V m)).
move=> H3.
rewrite H3.
rewrite (Vadd_O_r K (V m)).
suff: ((FiniteIntersection (sumT {n : nat | n < N} T) (exist (Finite (sumT {n : nat | n < N} T)) (fun t : sumT {n : nat | n < N} T => proj1_sig v t <> FO K) (proj2_sig v)) (fun t : sumT {n : nat | n < N} T => match t with
  | inT m0 _ => m0 = m
end)) = FiniteIm (T m) (sumT {n : nat | n < N} T) (inT {n : nat | n < N} T m) (exist (Finite (T m)) (fun t0 : T m => proj1_sig v (inT {n : nat | n < N} T m t0) <> FO K) (H2 v m))).
move=> H4.
rewrite H4.
apply (FiniteSetInduction (T m) (exist (Finite (T m)) (fun t0 : T m => proj1_sig v (inT {n : nat | n < N} T m t0) <> FO K) (H2 v m))).
apply conj.
suff: ((FiniteIm (T m) (sumT {n : nat | n < N} T) (inT {n : nat | n < N} T m) (FiniteEmpty (T m))) = (FiniteEmpty (sumT {n : nat | n < N} T))).
move=> H5.
rewrite H5.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0.
elim.
move=> t.
elim.
move=> B b H5 H6 H7 H8.
suff: ((FiniteIm (T m) (sumT {n : nat | n < N} T) (inT {n : nat | n < N} T m) (FiniteAdd (T m) B b)) = (FiniteAdd (sumT {n : nat | n < N} T) (FiniteIm (T m) (sumT {n : nat | n < N} T) (inT {n : nat | n < N} T m) B) (inT {n : nat | n < N} T m b))).
move=> H9.
rewrite H9.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
unfold DirectProdVSVadd.
rewrite H8.
unfold DirectProdVSVmul.
elim (excluded_middle_informative (m = m)).
move=> H10.
suff: (b = (TypeEqConvert (T m) (T m) (f_equal T H10) b)).
move=> H11.
rewrite - H11.
reflexivity.
apply JMeq_eq.
apply (proj2_sig (TypeEqConvertExist (T m) (T m) (f_equal T H10)) b).
move=> H10.
apply False_ind.
apply H10.
reflexivity.
move=> H10.
suff: (~ In (T m) (proj1_sig B) b).
suff: (b = let temp := (fun (t : (sumT {n : nat | n < N} T)) => match t with
  | inT m0 t0 => match excluded_middle_informative (m0 = m) with 
    | left H => TypeEqConvert (T m0) (T m) (f_equal T H) t0 
    | right _ => b
  end
end) in temp (inT {n : nat | n < N} T m b)).
move=> H11.
rewrite H11.
elim H10.
move=> x H12 y H13.
rewrite H13.
simpl.
elim (excluded_middle_informative (m = m)).
move=> H14.
suff: (x = (TypeEqConvert (T m) (T m) (f_equal T H14) x)).
move=> H15.
rewrite - H15.
move=> H16.
apply (H16 H12).
apply JMeq_eq.
apply (proj2_sig (TypeEqConvertExist (T m) (T m) (f_equal T H14)) x).
move=> H14 H15.
apply H14.
reflexivity.
simpl.
elim (excluded_middle_informative (m = m)).
move=> H11.
apply JMeq_eq.
apply (proj2_sig (TypeEqConvertExist (T m) (T m) (f_equal T H11)) b).
move=> H11.
reflexivity.
apply H7.
apply H7.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t0 H9 y H10.
rewrite H10.
elim H9.
move=> t1 H11.
left.
apply (Im_intro (T m) (sumT {n : nat | n < N} T) (proj1_sig B) (inT {n : nat | n < N} T m) t1 H11).
reflexivity.
move=> t1.
elim.
right.
apply (In_singleton (sumT {n : nat | n < N} T) (inT {n : nat | n < N} T m b)).
move=> t.
elim.
move=> t0.
elim.
move=> t1 H9 y H10.
rewrite H10.
apply (Im_intro (T m) (sumT {n : nat | n < N} T) (proj1_sig (FiniteAdd (T m) B b)) (inT {n : nat | n < N} T m) t1).
left.
apply H9.
reflexivity.
move=> t0.
elim.
apply (Im_intro (T m) (sumT {n : nat | n < N} T) (proj1_sig (FiniteAdd (T m) B b)) (inT {n : nat | n < N} T m) b).
right.
apply (In_singleton (T m) b).
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
unfold In.
elim.
move=> m0 t0 H4.
simpl.
rewrite - H4.
move=> H5.
apply (Im_intro (T m0) (sumT {n : nat | n < N} T) (fun t1 : T m0 => proj1_sig v (inT {n : nat | n < N} T m0 t1) <> FO K) (inT {n : nat | n < N} T m0) t0).
apply H5.
reflexivity.
move=> t.
elim.
move=> t0 H4 y H5.
rewrite H5.
simpl.
apply Intersection_intro.
reflexivity.
apply H4.
apply (FiniteSetInduction (sumT {n : nat | n < N} T) (FiniteIntersection (sumT {n : nat | n < N} T) (exist (Finite (sumT {n : nat | n < N} T)) (fun t : sumT {n : nat | n < N} T => proj1_sig v t <> FO K) (proj2_sig v)) (Complement (sumT {n : nat | n < N} T) (fun t : sumT {n : nat | n < N} T => match t with
  | inT m0 _ => m0 = m
end)))).
apply conj.
rewrite MySumF2Empty.
reflexivity.
move=> B b H3 H4 H5 H6.
rewrite MySumF2Add.
simpl.
unfold DirectProdVSVadd.
rewrite H6.
unfold DirectProdSystemVS.
suff: (~ In (sumT {n : nat | n < N} T) (fun t : sumT {n : nat | n < N} T => match t with
  | inT m0 _ => m0 = m
end) b).
unfold In.
unfold DirectProdVSVmul.
elim b.
move=> m0 t0 H7.
elim (excluded_middle_informative (m0 = m)).
move=> H8.
apply False_ind.
apply (H7 H8).
move=> H8.
rewrite (Vmul_O_r K (V m) (proj1_sig v (inT {n : nat | n < N} T m0 t0))).
apply (Vadd_O_r K (V m)).
elim H4.
move=> t H7 H8 H9.
apply (H7 H9).
apply H5.
move=> v m.
elim (proj2 (CountFiniteBijective {m : sumT {n : nat | n < N} T | proj1_sig v m <> FO K})).
move=> n.
elim.
move=> f.
elim.
move=> g H2.
apply FiniteSigSame.
apply (CountFiniteInjective {t : T m | proj1_sig v (inT {n0 : nat | n0 < N} T m t) <> FO K} n (fun (t : {t : T m | proj1_sig v (inT {n0 : nat | n0 < N} T m t) <> FO K}) => g (exist (fun (m : sumT {n : nat | n < N} T) => proj1_sig v m <> FO K) (inT {n0 : nat | n0 < N} T m (proj1_sig t)) (proj2_sig t)))).
move=> m1 m2 H3.
suff: ((exist (fun m : sumT {n : nat | n < N} T => proj1_sig v m <> FO K) (inT {n0 : nat | n0 < N} T m (proj1_sig m1)) (proj2_sig m1)) = (exist (fun m : sumT {n : nat | n < N} T => proj1_sig v m <> FO K) (inT {n0 : nat | n0 < N} T m (proj1_sig m2)) (proj2_sig m2))).
move=> H4.
apply sig_map.
suff: (proj1_sig m1 = (fun (t : sumT {n : nat | n < N} T) => match t with 
  | inT m3 t0 => match excluded_middle_informative (m3 = m) with 
    | left H => (TypeEqConvert (T m3) (T m) (f_equal T H) t0) 
    | right _ => proj1_sig m1
  end
end) (proj1_sig (exist (fun m : sumT {n : nat | n < N} T => proj1_sig v m <> FO K) (inT {n0 : nat | n0 < N} T m (proj1_sig m1)) (proj2_sig m1)))).
move=> H5.
rewrite H5.
rewrite H4.
simpl.
elim (excluded_middle_informative (m = m)).
move=> H6.
apply JMeq_eq.
apply JMeq_sym.
apply (proj2_sig (TypeEqConvertExist (T m) (T m) (f_equal T H6)) (proj1_sig m2)).
move=> H6.
apply False_ind.
apply H6.
reflexivity.
simpl.
elim (excluded_middle_informative (m = m)).
move=> H5.
apply JMeq_eq.
apply (proj2_sig (TypeEqConvertExist (T m) (T m) (f_equal T H5)) (proj1_sig m1)).
move=> H5.
reflexivity.
rewrite - (proj2 H2 (exist (fun m0 : sumT {n0 : nat | n0 < N} T => proj1_sig v m0 <> FO K) (inT {n0 : nat | n0 < N} T m (proj1_sig m1)) (proj2_sig m1))).
rewrite H3.
apply (proj2 H2 (exist (fun m : sumT {n : nat | n < N} T => proj1_sig v m <> FO K) (inT {n0 : nat | n0 < N} T m (proj1_sig m2)) (proj2_sig m2))).
apply (FiniteSigSame (sumT {n : nat | n < N} T)).
apply (proj2_sig v).
Qed.

Definition SubspaceVS (K : Field) (V : VectorSpace K) := fun (W : Ensemble (VT K V)) => (forall (v1 v2 : VT K V), In (VT K V) W v1 -> In (VT K V) W v2 -> In (VT K V) W (Vadd K V v1 v2)) /\ (forall (f : FT K) (v : VT K V), In (VT K V) W v -> In (VT K V) W (Vmul K V f v)) /\ (In (VT K V) W (VO K V)).

Lemma SubspaceMakeVSVoppSub : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)), (SubspaceVS K V W) -> forall (v : VT K V), (In (VT K V) W v) -> (In (VT K V) W (Vopp K V v)).
Proof.
move=> K V W H1 v H2.
rewrite - (Vmul_I_l K V (Vopp K V v)).
rewrite - (Vopp_mul_distr_r K V (FI K) v).
rewrite (Vopp_mul_distr_l K V (FI K) v).
apply (proj1 (proj2 H1) (Fopp K (FI K)) v H2).
Qed.

Definition SubspaceMakeVST (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) := {x : (VT K V) | In (VT K V) W x}.

Definition SubspaceMakeVSVO (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) := (exist W (VO K V) (proj2 (proj2 H))).

Definition SubspaceMakeVSVadd (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) := fun (v1 v2 : SubspaceMakeVST K V W H) => (exist W (Vadd K V (proj1_sig v1) (proj1_sig v2)) (proj1 H (proj1_sig v1) (proj1_sig v2) (proj2_sig v1) (proj2_sig v2))).

Definition SubspaceMakeVSVmul (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) := fun (f : FT K) (v : SubspaceMakeVST K V W H) => (exist W (Vmul K V f (proj1_sig v)) (proj1 (proj2 H) f (proj1_sig v) (proj2_sig v))).

Definition SubspaceMakeVSVopp (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) := fun (v : SubspaceMakeVST K V W H) => (exist W (Vopp K V (proj1_sig v)) (SubspaceMakeVSVoppSub K V W H (proj1_sig v) (proj2_sig v))).

Lemma SubspaceMakeVSVadd_comm : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) (v1 v2 : SubspaceMakeVST K V W H), SubspaceMakeVSVadd K V W H v1 v2 = SubspaceMakeVSVadd K V W H v2 v1.
Proof.
move=> K V W H1 v1 v2.
apply sig_map.
apply (Vadd_comm K V (proj1_sig v1) (proj1_sig v2)).
Qed.

Lemma SubspaceMakeVSVadd_assoc : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) (v1 v2 v3 : SubspaceMakeVST K V W H), SubspaceMakeVSVadd K V W H (SubspaceMakeVSVadd K V W H v1 v2) v3 = SubspaceMakeVSVadd K V W H v1 (SubspaceMakeVSVadd K V W H v2 v3).
Proof.
move=> K V W H1 v1 v2 v3.
apply sig_map.
apply (Vadd_assoc K V (proj1_sig v1) (proj1_sig v2) (proj1_sig v3)).
Qed.

Lemma SubspaceMakeVSVadd_O_l : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) (v : SubspaceMakeVST K V W H), SubspaceMakeVSVadd K V W H (SubspaceMakeVSVO K V W H) v = v.
Proof.
move=> K V W H1 v.
apply sig_map.
apply (Vadd_O_l K V (proj1_sig v)).
Qed.

Lemma SubspaceMakeVSVadd_opp_r : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) (v : SubspaceMakeVST K V W H), SubspaceMakeVSVadd K V W H v (SubspaceMakeVSVopp K V W H v) = SubspaceMakeVSVO K V W H.
Proof.
move=> K V W H1 v.
apply sig_map.
apply (Vadd_opp_r K V (proj1_sig v)).
Qed.

Lemma SubspaceMakeVSVmul_add_distr_l : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) (f : FT K) (v1 v2 : SubspaceMakeVST K V W H), SubspaceMakeVSVmul K V W H f (SubspaceMakeVSVadd K V W H v1 v2) = (SubspaceMakeVSVadd K V W H (SubspaceMakeVSVmul K V W H f v1) (SubspaceMakeVSVmul K V W H f v2)).
Proof.
move=> K V W H1 f v1 v2.
apply sig_map.
apply (Vmul_add_distr_l K V f (proj1_sig v1) (proj1_sig v2)).
Qed.

Lemma SubspaceMakeVSVmul_add_distr_r : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) (f1 f2 : FT K) (v : SubspaceMakeVST K V W H), (SubspaceMakeVSVmul K V W H (Fadd K f1 f2) v) = (SubspaceMakeVSVadd K V W H (SubspaceMakeVSVmul K V W H f1 v) (SubspaceMakeVSVmul K V W H f2 v)).
Proof.
move=> K V W H f1 f2 v.
apply sig_map.
apply (Vmul_add_distr_r K V f1 f2 (proj1_sig v)).
Qed.

Lemma SubspaceMakeVSVmul_assoc : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) (f1 f2 : FT K) (v : SubspaceMakeVST K V W H), (SubspaceMakeVSVmul K V W H f1 (SubspaceMakeVSVmul K V W H f2 v)) = (SubspaceMakeVSVmul K V W H (Fmul K f1 f2) v).
Proof.
move=> K V W H f1 f2 v.
apply sig_map.
apply (Vmul_assoc K V f1 f2 (proj1_sig v)).
Qed.

Lemma SubspaceMakeVSVmul_I_l : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) (v : SubspaceMakeVST K V W H), (SubspaceMakeVSVmul K V W H (FI K) v) = v.
Proof.
move=> K V W H v.
apply sig_map.
apply (Vmul_I_l K V (proj1_sig v)).
Qed.

Definition SubspaceMakeVS (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) := mkVectorSpace K (SubspaceMakeVST K V W H) (SubspaceMakeVSVO K V W H) (SubspaceMakeVSVadd K V W H) (SubspaceMakeVSVmul K V W H) (SubspaceMakeVSVopp K V W H) (SubspaceMakeVSVadd_comm K V W H) (SubspaceMakeVSVadd_assoc K V W H) (SubspaceMakeVSVadd_O_l K V W H) (SubspaceMakeVSVadd_opp_r K V W H) (SubspaceMakeVSVmul_add_distr_l K V W H) (SubspaceMakeVSVmul_add_distr_r K V W H) (SubspaceMakeVSVmul_assoc K V W H) (SubspaceMakeVSVmul_I_l K V W H).

Definition BasisSubspaceVS (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) (T : Type) (F : T -> VT K V) := exists (H1 : forall (t : T), In (VT K V) W (F t)), BasisVS K (SubspaceMakeVS K V W H) T (fun (t : T) => exist W (F t) (H1 t)).

Lemma FullsetSubspaceVS : forall (K : Field) (V : VectorSpace K), SubspaceVS K V (Full_set (VT K V)).
Proof.
move=> K V.
apply conj.
move=> v1 v2 H1 H2.
apply (Full_intro (VT K V) (Vadd K V v1 v2)).
apply conj.
move=> f v H1.
apply (Full_intro (VT K V) (Vmul K V f v)).
apply (Full_intro (VT K V) (VO K V)).
Qed.

Lemma VOSubspaceVS : forall (K : Field) (V : VectorSpace K), SubspaceVS K V (Singleton (VT K V) (VO K V)).
Proof.
move=> K V.
apply conj.
move=> v1 v2.
elim.
elim.
rewrite (Vadd_O_l K V (VO K V)).
apply (In_singleton (VT K V) (VO K V)).
apply conj.
move=> f v.
elim.
rewrite (Vmul_O_r K V f).
apply (In_singleton (VT K V) (VO K V)).
apply (In_singleton (VT K V) (VO K V)).
Qed.

Lemma SingleSubspaceVS : forall (K : Field) (V : VectorSpace K) (v : VT K V), SubspaceVS K V (fun (v0 : VT K V) => exists (f : FT K), v0 = Vmul K V f v).
Proof.
move=> K V v.
apply conj.
move=> v1 v2.
elim.
move=> f1 H1.
elim.
move=> f2 H2.
exists (Fadd K f1 f2).
rewrite H1.
rewrite H2.
rewrite (Vmul_add_distr_r K V f1 f2 v).
reflexivity.
apply conj.
move=> f v0.
elim.
move=> g H1.
exists (Fmul K f g).
rewrite H1.
apply (Vmul_assoc K V f g v).
exists (FO K).
rewrite (Vmul_O_l K V v).
reflexivity.
Qed.

Lemma Formula_P18_1 : forall (K : Field) (V : VectorSpace K) (x : VT K V) (H : SubspaceVS K V (fun (v0 : VT K V) => exists (f : FT K), v0 = Vmul K V f x)), x <> VO K V -> BasisSubspaceVS K V (fun (v0 : VT K V) => exists (f : FT K), v0 = Vmul K V f x) H {n : nat | n < S O} (fun (m : {n : nat | n < S O}) => x).
Proof.
move=> K V x H1 H2.
unfold BasisSubspaceVS.
suff: (forall (m : {n : nat | n < S O}), In (VT K V) (fun v0 : VT K V => exists f : FT K, v0 = Vmul K V f x) x).
move=> H3.
exists H3.
apply FiniteBasisVS.
move=> v.
apply (proj1 (unique_existence (fun (a : Count 1 -> FT K) => v = MySumF2 (Count 1) (exist (Finite (Count 1)) (Full_set (Count 1)) (CountFinite 1)) (VSPCM K (SubspaceMakeVS K V (fun v0 : VT K V => exists f : FT K, v0 = Vmul K V f x) H1)) (fun n : Count 1 => Vmul K (SubspaceMakeVS K V (fun v0 : VT K V => exists f : FT K, v0 = Vmul K V f x) H1) (a n) (exist (fun v0 : VT K V => exists f : FT K, v0 = Vmul K V f x) x (H3 n)))))).
apply conj.
elim (proj2_sig v).
move=> f H4.
exists (fun (n : Count 1) => f).
suff: ((exist (Finite (Count 1)) (Full_set (Count 1)) (CountFinite 1)) = FiniteSingleton (Count 1) (exist (fun (n : nat) => n < S O) O (le_n (S O)))).
move=> H5.
rewrite H5.
rewrite MySumF2Singleton.
apply sig_map.
apply H4.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> n H5.
suff: ((exist (fun n : nat => n < 1) 0 (le_n 1)) = n).
move=> H6.
rewrite H6.
apply In_singleton.
apply sig_map.
simpl.
elim (le_lt_or_eq (proj1_sig n) O).
move=> H6.
apply False_ind.
apply (le_not_lt O (proj1_sig n)).
apply le_0_n.
apply H6.
move=> H6.
rewrite H6.
reflexivity.
apply (le_S_n (proj1_sig n) O (proj2_sig n)).
move=> t H5.
apply (Full_intro (Count 1) t).
suff: (forall (x0 : Count 1 -> FT K), proj1_sig (MySumF2 (Count 1) (exist (Finite (Count 1)) (Full_set (Count 1)) (CountFinite 1)) (VSPCM K (SubspaceMakeVS K V (fun v0 : VT K V => exists f : FT K, v0 = Vmul K V f x) H1)) (fun n : Count 1 => Vmul K (SubspaceMakeVS K V (fun v0 : VT K V => exists f : FT K, v0 = Vmul K V f x) H1) (x0 n) (exist (fun v0 : VT K V => exists f : FT K, v0 = Vmul K V f x) x (H3 n)))) = Vmul K V (x0 (exist (fun n : nat => n < 1) 0 (le_n 1))) x).
move=> H4 x1 x2 H5 H6.
apply functional_extensionality.
move=> n.
suff: (n = (exist (fun n : nat => n < 1) 0 (le_n 1))).
move=> H7.
apply (Vmul_eq_reg_r K V x (x1 n) (x2 n)).
rewrite H7.
rewrite - (H4 x1).
rewrite - (H4 x2).
rewrite - H5.
rewrite - H6.
reflexivity.
apply H2.
apply sig_map.
elim (le_lt_or_eq (proj1_sig n) O).
move=> H7.
apply False_ind.
apply (le_not_lt O (proj1_sig n)).
apply le_0_n.
apply H7.
apply.
apply (le_S_n (proj1_sig n) O (proj2_sig n)).
move=> x0.
suff: ((exist (Finite (Count 1)) (Full_set (Count 1)) (CountFinite 1)) = FiniteSingleton (Count 1) (exist (fun (n : nat) => n < S O) O (le_n (S O)))).
move=> H4.
rewrite H4.
rewrite MySumF2Singleton.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> n H4.
suff: ((exist (fun n : nat => n < 1) 0 (le_n 1)) = n).
move=> H5.
rewrite H5.
apply In_singleton.
apply sig_map.
elim (le_lt_or_eq (proj1_sig n) O).
move=> H5.
apply False_ind.
apply (le_not_lt O (proj1_sig n)).
apply le_0_n.
apply H5.
move=> H5.
rewrite H5.
reflexivity.
apply (le_S_n (proj1_sig n) O (proj2_sig n)).
move=> t H4.
apply (Full_intro (Count 1) t).
move=> m.
exists (FI K).
rewrite (Vmul_I_l K V x).
reflexivity.
Qed.

Lemma Formula_P18_2 : forall (K : Field) (V : VectorSpace K) (x : VT K V), x = VO K V -> (fun (v0 : VT K V) => exists (f : FT K), v0 = Vmul K V f x) = (Singleton (VT K V) (VO K V)).
Proof.
move=> K V x H1.
rewrite H1.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> k H2.
rewrite H2.
rewrite (Vmul_O_r K V k).
apply In_singleton.
move=> t.
elim.
exists (FO K).
rewrite (Vmul_O_r K V (FO K)).
reflexivity.
Qed.

Inductive SumEnsembleVS (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) : Ensemble (VT K V) := 
  | SumEnsembleVS_intro : forall (x1 x2 : VT K V), In (VT K V) W1 x1 -> In (VT K V) W2 x2 -> In (VT K V) (SumEnsembleVS K V W1 W2) (Vadd K V x1 x2).

Lemma SumSubspaceVS : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)), SubspaceVS K V W1 -> SubspaceVS K V W2 -> SubspaceVS K V (SumEnsembleVS K V W1 W2).
Proof.
move=> K V W1 W2 H1 H2.
apply conj.
move=> v1 v2.
elim.
move=> w11 w12 H3 H4.
elim.
move=> w21 w22 H5 H6.
rewrite - (Vadd_assoc K V (Vadd K V w11 w12) w21 w22).
rewrite (Vadd_comm K V (Vadd K V w11 w12) w21).
rewrite - (Vadd_assoc K V w21 w11 w12).
rewrite (Vadd_assoc K V (Vadd K V w21 w11) w12 w22).
apply (SumEnsembleVS_intro K V W1 W2 (Vadd K V w21 w11) (Vadd K V w12 w22)).
apply (proj1 H1 w21 w11 H5 H3).
apply (proj1 H2 w12 w22 H4 H6).
apply conj.
move=> f v.
elim.
move=> v1 v2 H3 H4.
rewrite (Vmul_add_distr_l K V f v1 v2).
apply (SumEnsembleVS_intro K V W1 W2 (Vmul K V f v1) (Vmul K V f v2)).
apply (proj1 (proj2 H1) f v1 H3).
apply (proj1 (proj2 H2) f v2 H4).
rewrite - (Vadd_O_r K V (VO K V)).
apply (SumEnsembleVS_intro K V W1 W2 (VO K V) (VO K V)).
apply (proj2 (proj2 H1)).
apply (proj2 (proj2 H2)).
Qed.

Inductive SumTEnsembleVS (K : Field) (V : VectorSpace K) (T : Type) (W : T -> Ensemble (VT K V)) : Ensemble (VT K V) := 
  | SumTEnsembleVS_intro : forall (a : T -> VT K V) (H : Finite T (fun (t : T) => a t <> VO K V)), (forall (t : T), In (VT K V) (W t) (a t)) -> In (VT K V) (SumTEnsembleVS K V T W) (MySumF2 T (exist (Finite T) (fun (t : T) => a t <> VO K V) H) (VSPCM K V) a).

Lemma FiniteSumTEnsembleVS : forall (K : Field) (V : VectorSpace K) (N : nat) (W : {n : nat | n < N} -> Ensemble (VT K V)), SumTEnsembleVS K V {n : nat | n < N} W = (fun (t : VT K V) => exists (a : {n : nat | n < N} -> VT K V), (forall (m : {n : nat | n < N}), In (VT K V) (W m) (a m)) /\ (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) a = t)).
Proof.
move=> K V N W.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> a H1 H2.
exists a.
apply conj.
apply H2.
rewrite (MySumF2Included {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => a t <> VO K V) H1) (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) a).
rewrite (MySumF2O {n : nat | n < N} (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (Complement {n : nat | n < N} (proj1_sig (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => a t <> VO K V) H1)))) (VSPCM K V) a).
apply (Vadd_O_r K V).
move=> u.
elim.
move=> m H3 H4.
apply NNPP.
apply H3.
move=> m H3.
apply (Full_intro {n : nat | n < N} m).
move=> v.
elim.
move=> a H1.
rewrite - (proj2 H1).
suff: (Finite {n : nat | n < N} (fun t : {n : nat | n < N} => a t <> VO K V)).
move=> H2.
suff: ((MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) a) = (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => a t <> VO K V) H2) (VSPCM K V) a)).
move=> H3.
rewrite H3.
apply (SumTEnsembleVS_intro K V {n : nat | n < N} W a H2).
apply (proj1 H1).
rewrite (MySumF2Included {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => a t <> VO K V) H2) (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) a).
rewrite (MySumF2O {n : nat | n < N} (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (Complement {n : nat | n < N} (proj1_sig (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => a t <> VO K V) H2)))) (VSPCM K V) a).
apply (Vadd_O_r K V).
move=> u.
elim.
move=> m H3 H4.
apply NNPP.
apply H3.
move=> m H3.
apply (Full_intro {n : nat | n < N} m).
apply (Finite_downward_closed {n : nat | n < N} (Full_set {n : nat | n < N}) (CountFinite N)).
move=> t H2.
apply (Full_intro {n : nat | n < N} t).
Qed.

Lemma SumTSubspaceVS : forall (K : Field) (V : VectorSpace K) (T : Type) (W : T -> Ensemble (VT K V)), (forall (t : T), SubspaceVS K V (W t)) -> SubspaceVS K V (SumTEnsembleVS K V T W).
Proof.
move=> K V T W H1.
apply conj.
move=> v1 v2.
elim.
move=> w1 H2 H3.
elim.
move=> w2 H4 H5.
suff: (Finite T (fun t : T => Vadd K V (w1 t) (w2 t) <> VO K V)).
move=> H6.
suff: ((MySumF2 T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (VSPCM K V) w1) = (MySumF2 T (FiniteUnion T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (exist (Finite T) (fun t : T => w2 t <> VO K V) H4)) (VSPCM K V) w1)).
move=> H7.
rewrite H7.
suff: ((MySumF2 T (exist (Finite T) (fun t : T => w2 t <> VO K V) H4) (VSPCM K V) w2) = (MySumF2 T (FiniteUnion T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (exist (Finite T) (fun t : T => w2 t <> VO K V) H4)) (VSPCM K V) w2)).
move=> H8.
rewrite H8.
suff: ((Vadd K V (MySumF2 T (FiniteUnion T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (exist (Finite T) (fun t : T => w2 t <> VO K V) H4)) (VSPCM K V) w1) (MySumF2 T (FiniteUnion T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (exist (Finite T) (fun t : T => w2 t <> VO K V) H4)) (VSPCM K V) w2)) = (MySumF2 T (FiniteUnion T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (exist (Finite T) (fun t : T => w2 t <> VO K V) H4)) (VSPCM K V) (fun (t : T) => Vadd K V (w1 t) (w2 t)))).
move=> H9.
rewrite H9.
suff: ((MySumF2 T (FiniteUnion T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (exist (Finite T) (fun t : T => w2 t <> VO K V) H4)) (VSPCM K V) (fun t : T => Vadd K V (w1 t) (w2 t))) = (MySumF2 T (exist (Finite T) (fun t : T => Vadd K V (w1 t) (w2 t) <> VO K V) H6) (VSPCM K V) (fun t : T => Vadd K V (w1 t) (w2 t)))).
move=> H10.
rewrite H10.
apply (SumTEnsembleVS_intro K V T W (fun (t : T) => Vadd K V (w1 t) (w2 t)) H6).
move=> t.
apply (proj1 (H1 t) (w1 t) (w2 t)).
apply (H3 t).
apply (H5 t).
rewrite (MySumF2Included T (exist (Finite T) (fun t : T => Vadd K V (w1 t) (w2 t) <> VO K V) H6) (FiniteUnion T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (exist (Finite T) (fun t : T => w2 t <> VO K V) H4)) (VSPCM K V) (fun t : T => Vadd K V (w1 t) (w2 t))).
rewrite (MySumF2O T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (exist (Finite T) (fun t : T => w2 t <> VO K V) H4)) (Complement T (proj1_sig (exist (Finite T) (fun t : T => Vadd K V (w1 t) (w2 t) <> VO K V) H6)))) (VSPCM K V) (fun t : T => Vadd K V (w1 t) (w2 t))).
apply (Vadd_O_r K V).
move=> t.
elim.
move=> t0 H10 H11.
apply NNPP.
apply H10.
simpl.
move=> t H10.
apply NNPP.
move=> H11.
apply H10.
suff: (w1 t = VO K V).
move=> H12.
rewrite H12.
suff: (w2 t = VO K V).
move=> H13.
rewrite H13.
apply (Vadd_O_r K V).
apply NNPP.
move=> H13.
apply H11.
right.
apply H13.
apply NNPP.
move=> H12.
apply H11.
left.
apply H12.
apply (FiniteSetInduction T (FiniteUnion T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (exist (Finite T) (fun t : T => w2 t <> VO K V) H4))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Vadd_O_r K V (VO K V)).
move=> B b H9 H10 H11 H12.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite - H12.
rewrite - (Vadd_assoc K V (Vadd K V (MySumF2 T B (VSPCM K V) w1) (w1 b)) (MySumF2 T B (VSPCM K V) w2) (w2 b)).
rewrite (Vadd_comm K V (Vadd K V (MySumF2 T B (VSPCM K V) w1) (w1 b)) (MySumF2 T B (VSPCM K V) w2)).
rewrite - (Vadd_assoc K V (MySumF2 T B (VSPCM K V) w2) (MySumF2 T B (VSPCM K V) w1) (w1 b)).
rewrite (Vadd_assoc K V (Vadd K V (MySumF2 T B (VSPCM K V) w2) (MySumF2 T B (VSPCM K V) w1)) (w1 b) (w2 b)).
rewrite (Vadd_comm K V (MySumF2 T B (VSPCM K V) w2) (MySumF2 T B (VSPCM K V) w1)).
reflexivity.
apply H11.
apply H11.
apply H11.
rewrite (MySumF2Included T (exist (Finite T) (fun t : T => w2 t <> VO K V) H4) (FiniteUnion T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (exist (Finite T) (fun t : T => w2 t <> VO K V) H4)) (VSPCM K V) w2).
rewrite (MySumF2O T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (exist (Finite T) (fun t : T => w2 t <> VO K V) H4)) (Complement T (proj1_sig (exist (Finite T) (fun t : T => w2 t <> VO K V) H4)))) (VSPCM K V) w2).
simpl.
rewrite (Vadd_O_r K V).
reflexivity.
move=> t.
elim.
move=> t0 H8 H9.
apply NNPP.
apply H8.
move=> t H8.
right.
apply H8.
rewrite (MySumF2Included T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (FiniteUnion T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (exist (Finite T) (fun t : T => w2 t <> VO K V) H4)) (VSPCM K V) w1).
rewrite (MySumF2O T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => w1 t <> VO K V) H2) (exist (Finite T) (fun t : T => w2 t <> VO K V) H4)) (Complement T (proj1_sig (exist (Finite T) (fun t : T => w1 t <> VO K V) H2)))) (VSPCM K V) w1).
simpl.
rewrite (Vadd_O_r K V).
reflexivity.
move=> t.
elim.
move=> t0 H7 H8.
apply NNPP.
apply H7.
move=> t H7.
left.
apply H7.
apply (Finite_downward_closed T (Union T (fun t : T => w1 t <> VO K V) (fun t : T => w2 t <> VO K V))).
apply (Union_preserves_Finite T (fun t : T => w1 t <> VO K V) (fun t : T => w2 t <> VO K V)).
apply H2.
apply H4.
move=> t H6.
apply NNPP.
move=> H7.
apply H6.
suff: (w1 t = VO K V).
move=> H8.
suff: (w2 t = VO K V).
move=> H9.
rewrite H8.
rewrite H9.
apply (Vadd_O_r K V (VO K V)).
apply NNPP.
move=> H9.
apply H7.
right.
apply H9.
apply NNPP.
move=> H8.
apply H7.
left.
apply H8.
apply conj.
move=> f v H2.
elim (classic (f = FO K)).
move=> H3.
rewrite H3.
rewrite (Vmul_O_l K V v).
suff: (Finite T (fun (t : T) => VO K V <> VO K V)).
move=> H4.
suff: (exist (Finite T) (fun _ : T => VO K V <> VO K V) H4 = FiniteEmpty T).
move=> H5.
suff: ((MySumF2 T (exist (Finite T) (fun _ : T => VO K V <> VO K V) H4) (VSPCM K V) (fun _ : T => VO K V)) = (VO K V)).
move=> H6.
rewrite - H6.
apply (SumTEnsembleVS_intro K V T W (fun (t : T) => VO K V)).
move=> t.
apply (proj2 (proj2 (H1 t))).
rewrite H5.
apply MySumF2Empty.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> t H5.
apply False_ind.
apply H5.
reflexivity.
move=> t.
elim.
suff: ((fun _ : T => VO K V <> VO K V) = Empty_set T).
move=> H4.
rewrite H4.
apply (Empty_is_finite T).
apply Extensionality_Ensembles.
apply conj.
move=> t H4.
apply False_ind.
apply H4.
reflexivity.
move=> t.
elim.
move=> H3.
elim H2.
move=> a H4 H5.
suff: ((fun t : T => Vmul K V f (a t) <> VO K V) = (fun t : T => a t <> VO K V)).
move=> H6.
suff: (Finite T (fun t : T => Vmul K V f (a t) <> VO K V)).
move=> H7.
suff: ((Vmul K V f (MySumF2 T (exist (Finite T) (fun t : T => a t <> VO K V) H4) (VSPCM K V) a)) = (MySumF2 T (exist (Finite T) (fun t : T => Vmul K V f (a t) <> VO K V) H7) (VSPCM K V) (fun (t : T) => Vmul K V f (a t)))).
move=> H8.
rewrite H8.
apply (SumTEnsembleVS_intro K V T W (fun t : T => Vmul K V f (a t)) H7).
move=> t.
apply (proj1 (proj2 (H1 t)) f (a t) (H5 t)).
suff: ((exist (Finite T) (fun t : T => a t <> VO K V) H4) = (exist (Finite T) (fun t : T => Vmul K V f (a t) <> VO K V) H7)).
move=> H8.
rewrite H8.
apply (FiniteSetInduction T (exist (Finite T) (fun t : T => Vmul K V f (a t) <> VO K V) H7)).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Vmul_O_r K V f).
move=> B b H9 H10 H11 H12.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite - H12.
apply (Vmul_add_distr_l K V f (MySumF2 T B (VSPCM K V) a) (a b)).
apply H11.
apply H11.
apply sig_map.
simpl.
rewrite H6.
reflexivity.
rewrite H6.
apply H4.
apply Extensionality_Ensembles.
apply conj.
move=> t H6 H7.
apply H6.
rewrite H7.
apply (Vmul_O_r K V f).
move=> t H6 H7.
apply H6.
rewrite - (Vmul_I_l K V (a t)).
rewrite - (Finv_l K f H3).
rewrite - (Vmul_assoc K V (Finv K f) f (a t)).
rewrite H7.
apply (Vmul_O_r K V (Finv K f)).
suff: (Finite T (fun (t : T) => VO K V <> VO K V)).
move=> H2.
suff: (exist (Finite T) (fun _ : T => VO K V <> VO K V) H2 = FiniteEmpty T).
move=> H3.
suff: ((MySumF2 T (exist (Finite T) (fun _ : T => VO K V <> VO K V) H2) (VSPCM K V) (fun _ : T => VO K V)) = (VO K V)).
move=> H4.
rewrite - H4.
apply (SumTEnsembleVS_intro K V T W (fun (t : T) => VO K V)).
move=> t.
apply (proj2 (proj2 (H1 t))).
rewrite H3.
apply MySumF2Empty.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> t H3.
apply False_ind.
apply H3.
reflexivity.
move=> t.
elim.
suff: ((fun _ : T => VO K V <> VO K V) = Empty_set T).
move=> H2.
rewrite H2.
apply (Empty_is_finite T).
apply Extensionality_Ensembles.
apply conj.
move=> t H2.
apply False_ind.
apply H2.
reflexivity.
move=> t.
elim.
Qed.

Lemma IntersectionSubspaceVS : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)), SubspaceVS K V W1 -> SubspaceVS K V W2 -> SubspaceVS K V (Intersection (VT K V) W1 W2).
Proof.
move=> K V W1 W2 H1 H2.
apply conj.
move=> v1 v2.
elim.
move=> v10 H3 H4.
elim.
move=> v20 H5 H6.
apply (Intersection_intro (VT K V) W1 W2 (Vadd K V v10 v20)).
apply (proj1 H1 v10 v20 H3 H5).
apply (proj1 H2 v10 v20 H4 H6).
apply conj.
move=> f v.
elim.
move=> v0 H3 H4.
apply (Intersection_intro (VT K V) W1 W2 (Vmul K V f v0)).
apply (proj1 (proj2 H1) f v0 H3).
apply (proj1 (proj2 H2) f v0 H4).
apply (Intersection_intro (VT K V) W1 W2 (VO K V)).
apply (proj2 (proj2 H1)).
apply (proj2 (proj2 H2)).
Qed.

Lemma IntersectionTSubspaceVS : forall (K : Field) (V : VectorSpace K) (T : Type) (W : T -> Ensemble (VT K V)), (forall (t : T), SubspaceVS K V (W t)) -> SubspaceVS K V (IntersectionT (VT K V) T W).
Proof.
move=> K V T W H1.
apply conj.
move=> v1 v2.
elim.
move=> v10 H2.
elim.
move=> v20 H3.
apply (IntersectionT_intro (VT K V) T W (Vadd K V v10 v20)).
move=> t.
apply (proj1 (H1 t) v10 v20 (H2 t) (H3 t)).
apply conj.
move=> f v.
elim.
move=> v0 H2.
apply (IntersectionT_intro (VT K V) T W (Vmul K V f v0)).
move=> t.
apply (proj1 (proj2 (H1 t)) f v0 (H2 t)).
apply (IntersectionT_intro (VT K V) T W (VO K V)).
move=> t.
apply (proj2 (proj2 (H1 t))).
Qed.

Definition SpanVS (K : Field) (V : VectorSpace K) (T : Type) (x : T -> VT K V) := fun (v : VT K V) => exists (a : DirectSumField K T), v = MySumF2 T (exist (Finite T) (fun (t : T) => proj1_sig a t <> FO K) (proj2_sig a)) (VSPCM K V) (fun (t : T) => Vmul K V (proj1_sig a t) (x t)).

Lemma BijectiveSaveSpanVS : forall (K : Field) (V : VectorSpace K) (T1 T2 : Type) (F : T1 -> T2) (G : T2 -> VT K V), Bijective T1 T2 F -> SpanVS K V T2 G = SpanVS K V T1 (fun t : T1 => G (F t)).
Proof.
move=> K V T1 T2 F G H1.
elim H1.
move=> Finv H2.
apply Extensionality_Ensembles.
apply conj.
suff: (forall (a : DirectSumField K T2), Finite T1 (fun t : T1 => proj1_sig a (F t) <> FO K)).
move=> H3.
suff: (forall (a : DirectSumField K T2), MySumF2 T2 (exist (Finite T2) (fun t : T2 => proj1_sig a t <> FO K) (proj2_sig a)) (VSPCM K V) (fun t : T2 => Vmul K V (proj1_sig a t) (G t)) = MySumF2 T1 (exist (Finite T1) (fun t : T1 => proj1_sig a (F t) <> FO K) (H3 a)) (VSPCM K V) (fun t : T1 => Vmul K V (proj1_sig a (F t)) (G (F t)))).
move=> H4 t.
elim.
move=> a H5.
rewrite H5.
rewrite (H4 a).
exists (exist (fun (a0 : T1 -> FT K) => Finite T1 (fun t : T1 => a0 t <> FO K)) (fun t : T1 => proj1_sig a (F t)) (H3 a)).
reflexivity.
move=> a.
rewrite (MySumF2BijectiveSame T1 (exist (Finite T1) (fun t : T1 => proj1_sig a (F t) <> FO K) (H3 a)) T2 (exist (Finite T2) (fun t : T2 => proj1_sig a t <> FO K) (proj2_sig a)) (VSPCM K V) (fun t : T2 => Vmul K V (proj1_sig a t) (G t)) F).
reflexivity.
simpl.
apply InjSurjBij.
move=> u1 u2 H4.
apply sig_map.
rewrite - (proj1 H2 (proj1_sig u1)).
suff: (F (proj1_sig u1) = proj1_sig (exist (fun t : T2 => proj1_sig a t <> FO K) (F (proj1_sig u1)) (proj2_sig u1))).
move=> H5.
rewrite H5.
rewrite H4.
apply (proj1 H2 (proj1_sig u2)).
reflexivity.
move=> v.
suff: (proj1_sig a (F (Finv (proj1_sig v))) <> FO K).
move=> H4.
exists (exist (fun (u : T1) => proj1_sig a (F u) <> FO K) (Finv (proj1_sig v)) H4).
apply sig_map.
apply (proj2 H2 (proj1_sig v)).
rewrite (proj2 H2 (proj1_sig v)).
apply (proj2_sig v).
move=> a.
suff: ((fun t : T1 => proj1_sig a (F t) <> FO K) = Im T2 T1 (fun t : T2 => proj1_sig a t <> FO K) Finv).
move=> H3.
rewrite H3.
apply finite_image.
apply (proj2_sig a).
apply Extensionality_Ensembles.
apply conj.
move=> t H3.
apply (Im_intro T2 T1 (fun t0 : T2 => proj1_sig a t0 <> FO K) Finv (F t)).
apply H3.
rewrite (proj1 H2 t).
reflexivity.
move=> t.
elim.
move=> t0 H3 t1 H4.
rewrite H4.
unfold In.
rewrite (proj2 H2 t0).
apply H3.
suff: (forall (a : DirectSumField K T1), Finite T2 (fun t : T2 => proj1_sig a (Finv t) <> FO K)).
move=> H3.
suff: (forall (a : DirectSumField K T1), MySumF2 T1 (exist (Finite T1) (fun t : T1 => proj1_sig a t <> FO K) (proj2_sig a)) (VSPCM K V) (fun t : T1 => Vmul K V (proj1_sig a t) (G (F t))) = MySumF2 T2 (exist (Finite T2) (fun t : T2 => proj1_sig a (Finv t) <> FO K) (H3 a)) (VSPCM K V) (fun t : T2 => Vmul K V (proj1_sig a (Finv t)) (G t))).
move=> H4 v.
elim.
move=> a H5.
rewrite H5.
rewrite (H4 a).
exists (exist (fun (a : T2 -> FT K) => Finite T2 (fun t : T2 => a t <> FO K)) (fun t : T2 => proj1_sig a (Finv t)) (H3 a)).
reflexivity.
move=> a.
suff: ((fun t : T1 => Vmul K V (proj1_sig a t) (G (F t))) = (fun t : T1 => Vmul K V (proj1_sig a (Finv (F t))) (G (F t)))).
move=> H4.
rewrite H4.
suff: (forall u : T1, proj1_sig (exist (Finite T1) (fun t : T1 => proj1_sig a t <> FO K) (proj2_sig a)) u -> proj1_sig (exist (Finite T2) (fun t : T2 => proj1_sig a (Finv t) <> FO K) (H3 a)) (F u)).
move=> H5.
apply (MySumF2BijectiveSame T1 (exist (Finite T1) (fun t : T1 => proj1_sig a t <> FO K) (proj2_sig a)) T2 (exist (Finite T2) (fun t : T2 => proj1_sig a (Finv t) <> FO K) (H3 a)) (VSPCM K V) (fun t : T2 => Vmul K V (proj1_sig a (Finv t)) (G t)) F H5).
simpl.
apply InjSurjBij.
move=> u1 u2 H6.
apply sig_map.
rewrite - (proj1 H2 (proj1_sig u1)).
suff: (F (proj1_sig u1) = proj1_sig (exist (fun t : T2 => proj1_sig a (Finv t) <> FO K) (F (proj1_sig u1)) (H5 (proj1_sig u1) (proj2_sig u1)))).
move=> H7.
rewrite H7.
rewrite H6.
apply (proj1 H2 (proj1_sig u2)).
reflexivity.
move=> u.
exists (exist (fun (u : T1) => proj1_sig a u <> FO K) (Finv (proj1_sig u)) (proj2_sig u)).
apply sig_map.
apply (proj2 H2 (proj1_sig u)).
move=> u.
simpl.
rewrite (proj1 H2 u).
apply.
apply functional_extensionality.
move=> t.
rewrite (proj1 H2 t).
reflexivity.
move=> a.
suff: ((fun t : T2 => proj1_sig a (Finv t) <> FO K) = Im T1 T2 (fun t : T1 => proj1_sig a t <> FO K) F).
move=> H3.
rewrite H3.
apply finite_image.
apply (proj2_sig a).
apply Extensionality_Ensembles.
apply conj.
move=> t H3.
apply (Im_intro T1 T2 (fun t0 : T1 => proj1_sig a t0 <> FO K) F (Finv t)).
apply H3.
rewrite (proj2 H2 t).
reflexivity.
move=> t.
elim.
move=> t0 H3 t1 H4.
rewrite H4.
unfold In.
rewrite (proj1 H2 t0).
apply H3.
Qed.

Lemma FiniteSpanVS : forall (K : Field) (V : VectorSpace K) (N : nat) (x : Count N -> VT K V), SpanVS K V (Count N) x = fun (v : VT K V) => exists (a : Count N -> FT K), v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun (n : Count N) => Vmul K V (a n) (x n)).
Proof.
move=> K V N x.
suff: (forall (a : DirectSumField K (Count N)), MySumF2 (Count N) (exist (Finite (Count N)) (fun t : Count N => proj1_sig a t <> FO K) (proj2_sig a)) (VSPCM K V) (fun t : Count N => Vmul K V (proj1_sig a t) (x t)) = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (proj1_sig a n) (x n))).
move=> H1.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> a H2.
exists (proj1_sig a).
rewrite H2.
rewrite (H1 a).
reflexivity.
move=> v.
elim.
move=> a H2.
suff: (Finite (Count N) (fun (n : Count N) => a n <> FO K)).
move=> H3.
exists (exist (fun (G : Count N -> FT K) => Finite (Count N) (fun (n : Count N) => G n <> FO K)) a H3).
rewrite H2.
rewrite (H1 (exist (fun (G : Count N -> FT K) => Finite (Count N) (fun (n : Count N) => G n <> FO K)) a H3)).
reflexivity.
apply (Finite_downward_closed (Count N) (Full_set (Count N)) (CountFinite N) (fun (n : Count N) => a n <> FO K)).
move=> n H3.
apply (Full_intro (Count N) n).
move=> a.
rewrite (MySumF2Included (Count N) (exist (Finite (Count N)) (fun t : Count N => proj1_sig a t <> FO K) (proj2_sig a)) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (proj1_sig a n) (x n))).
rewrite (MySumF2O (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Complement (Count N) (proj1_sig (exist (Finite (Count N)) (fun t : Count N => proj1_sig a t <> FO K) (proj2_sig a))))) (VSPCM K V) (fun n : Count N => Vmul K V (proj1_sig a n) (x n))).
simpl.
rewrite (Vadd_O_r K V).
reflexivity.
move=> u.
elim.
move=> u0 H1 H2.
suff: (proj1_sig a u0 = FO K).
move=> H3.
rewrite H3.
apply (Vmul_O_l K V (x u0)).
apply NNPP.
apply H1.
move=> n H1.
apply (Full_intro (Count N) n).
Qed.

Lemma SpanSubspaceVS (K : Field) (V : VectorSpace K) (T : Type) (x : T -> VT K V) : SubspaceVS K V (SpanVS K V T x).
Proof.
apply conj.
move=> v1 v2.
elim.
move=> a1 H1.
elim.
move=> a2 H2.
suff: (Finite T (fun (t : T) => Fadd K (proj1_sig a1 t) (proj1_sig a2 t) <> FO K)).
move=> H3.
exists (exist (fun (G : T -> FT K) => Finite T (fun t : T => G t <> FO K)) (fun (t : T) => Fadd K (proj1_sig a1 t) (proj1_sig a2 t)) H3).
suff: (MySumF2 T (exist (Finite T) (fun t : T => proj1_sig (exist (fun G : T -> FT K => Finite T (fun t0 : T => G t0 <> FO K)) (fun t0 : T => Fadd K (proj1_sig a1 t0) (proj1_sig a2 t0)) H3) t <> FO K) (proj2_sig (exist (fun G : T -> FT K => Finite T (fun t : T => G t <> FO K)) (fun t : T => Fadd K (proj1_sig a1 t) (proj1_sig a2 t)) H3))) (VSPCM K V) (fun t : T => Vmul K V (proj1_sig (exist (fun G : T -> FT K => Finite T (fun t0 : T => G t0 <> FO K)) (fun t0 : T => Fadd K (proj1_sig a1 t0) (proj1_sig a2 t0)) H3) t) (x t)) = MySumF2 T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (VSPCM K V) (fun t : T => Vmul K V (proj1_sig (exist (fun G : T -> FT K => Finite T (fun t0 : T => G t0 <> FO K)) (fun t0 : T => Fadd K (proj1_sig a1 t0) (proj1_sig a2 t0)) H3) t) (x t))).
move=> H4.
rewrite H4.
suff: (v1 = MySumF2 T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a1 t) (x t))).
move=> H5.
rewrite H5.
suff: (v2 = MySumF2 T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a2 t) (x t))).
move=> H6.
rewrite H6.
apply (FiniteSetInduction T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Vadd_O_l K V (VO K V)).
move=> B b H7 H8 H9.
simpl.
move=> H10.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite - H10.
rewrite - (Vadd_assoc K V (Vadd K V (MySumF2 T B (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a1 t) (x t))) (Vmul K V (proj1_sig a1 b) (x b))) (MySumF2 T B (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a2 t) (x t))) (Vmul K V (proj1_sig a2 b) (x b))).
rewrite (Vadd_comm K V (Vadd K V (MySumF2 T B (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a1 t) (x t))) (Vmul K V (proj1_sig a1 b) (x b))) (MySumF2 T B (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a2 t) (x t)))).
rewrite - (Vadd_assoc K V (MySumF2 T B (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a2 t) (x t))) (MySumF2 T B (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a1 t) (x t))) (Vmul K V (proj1_sig a1 b) (x b))).
rewrite (Vadd_comm K V (MySumF2 T B (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a2 t) (x t))) (MySumF2 T B (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a1 t) (x t)))).
rewrite (Vadd_assoc K V (Vadd K V (MySumF2 T B (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a1 t) (x t))) (MySumF2 T B (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a2 t) (x t)))) (Vmul K V (proj1_sig a1 b) (x b)) (Vmul K V (proj1_sig a2 b) (x b))).
rewrite (Vmul_add_distr_r K V (proj1_sig a1 b) (proj1_sig a2 b) (x b)).
reflexivity.
apply H9.
apply H9.
apply H9.
rewrite H2.
rewrite (MySumF2Excluded T (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a2 t) (x t)) (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (fun t : T => proj1_sig a2 t <> FO K)).
suff: ((MySumF2 T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (Complement T (fun t : T => proj1_sig a2 t <> FO K))) (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a2 t) (x t))) = VO K V).
move=> H6.
rewrite H6.
simpl.
rewrite (Vadd_O_r K V (MySumF2 T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (fun t : T => proj1_sig a2 t <> FO K)) (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a2 t) (x t)))).
suff: ((exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2)) = (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (fun t : T => proj1_sig a2 t <> FO K))).
move=> H7.
rewrite - H7.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> t H7.
apply (Intersection_intro T (fun t0 : T => proj1_sig a2 t0 <> FO K) (Union T (fun t0 : T => proj1_sig a1 t0 <> FO K) (fun t0 : T => proj1_sig a2 t0 <> FO K)) t).
apply H7.
right.
apply H7.
move=> t.
elim.
move=> t0 H7 H8.
apply H7.
apply (MySumF2Induction T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (Complement T (fun t : T => proj1_sig a2 t <> FO K)))).
apply conj.
reflexivity.
simpl.
move=> v u H6 H7.
rewrite H7.
suff: (proj1_sig a2 u = FO K).
move=> H8.
rewrite H8.
rewrite (Vmul_O_l K V (x u)).
apply (Vadd_O_l K V (VO K V)).
apply NNPP.
elim H6.
move=> u0 H8 H9 H10.
apply (H8 H10).
rewrite H1.
rewrite (MySumF2Excluded T (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a1 t) (x t)) (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (fun t : T => proj1_sig a1 t <> FO K)).
suff: ((MySumF2 T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (Complement T (fun t : T => proj1_sig a1 t <> FO K))) (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a1 t) (x t))) = VO K V).
move=> H5.
rewrite H5.
simpl.
rewrite (Vadd_O_r K V (MySumF2 T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (fun t : T => proj1_sig a1 t <> FO K)) (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a1 t) (x t)))).
suff: ((exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) = (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (fun t : T => proj1_sig a1 t <> FO K))).
move=> H6.
rewrite - H6.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> t H6.
apply (Intersection_intro T (fun t0 : T => proj1_sig a1 t0 <> FO K) (Union T (fun t0 : T => proj1_sig a1 t0 <> FO K) (fun t0 : T => proj1_sig a2 t0 <> FO K)) t).
apply H6.
left.
apply H6.
move=> t.
elim.
move=> t0 H6 H7.
apply H6.
apply (MySumF2Induction T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (Complement T (fun t : T => proj1_sig a1 t <> FO K)))).
apply conj.
reflexivity.
simpl.
move=> v u H5 H6.
rewrite H6.
suff: (proj1_sig a1 u = FO K).
move=> H7.
rewrite H7.
rewrite (Vmul_O_l K V (x u)).
apply (Vadd_O_l K V (VO K V)).
apply NNPP.
elim H5.
move=> u0 H7 H8 H9.
apply (H7 H9).
rewrite (MySumF2Excluded T (VSPCM K V) (fun t : T => Vmul K V (proj1_sig (exist (fun G : T -> FT K => Finite T (fun t0 : T => G t0 <> FO K)) (fun t0 : T => Fadd K (proj1_sig a1 t0) (proj1_sig a2 t0)) H3) t) (x t)) (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (fun t : T => proj1_sig (exist (fun G : T -> FT K => Finite T (fun t0 : T => G t0 <> FO K)) (fun t0 : T => Fadd K (proj1_sig a1 t0) (proj1_sig a2 t0)) H3) t <> FO K)).
suff: ((MySumF2 T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (Complement T (fun t : T => proj1_sig (exist (fun G : T -> FT K => Finite T (fun t0 : T => G t0 <> FO K)) (fun t0 : T => Fadd K (proj1_sig a1 t0) (proj1_sig a2 t0)) H3) t <> FO K))) (VSPCM K V) (fun t : T => Vmul K V (proj1_sig (exist (fun G : T -> FT K => Finite T (fun t0 : T => G t0 <> FO K)) (fun t0 : T => Fadd K (proj1_sig a1 t0) (proj1_sig a2 t0)) H3) t) (x t))) = VO K V).
move=> H4.
rewrite H4.
simpl.
rewrite (Vadd_O_r K V (MySumF2 T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (fun t : T => Fadd K (proj1_sig a1 t) (proj1_sig a2 t) <> FO K)) (VSPCM K V) (fun t : T => Vmul K V (Fadd K (proj1_sig a1 t) (proj1_sig a2 t)) (x t)))).
suff: ((exist (Finite T) (fun t : T => Fadd K (proj1_sig a1 t) (proj1_sig a2 t) <> FO K) H3) = (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (fun t : T => Fadd K (proj1_sig a1 t) (proj1_sig a2 t) <> FO K))).
move=> H5.
rewrite H5.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> t H5.
apply (Intersection_intro T (fun t0 : T => Fadd K (proj1_sig a1 t0) (proj1_sig a2 t0) <> FO K) (Union T (fun t0 : T => proj1_sig a1 t0 <> FO K) (fun t0 : T => proj1_sig a2 t0 <> FO K)) t).
apply H5.
apply NNPP.
move=> H6.
apply H5.
suff: (proj1_sig a1 t = FO K).
move=> H7.
rewrite H7.
suff: (proj1_sig a2 t = FO K).
move=> H8.
rewrite H8.
apply (Fadd_O_l K (FO K)).
apply NNPP.
move=> H8.
apply H6.
right.
apply H8.
apply NNPP.
move=> H7.
apply H6.
left.
apply H7.
move=> t.
elim.
move=> t0 H5 H6.
apply H5.
apply (MySumF2Induction T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig a1 t <> FO K) (proj2_sig a1)) (exist (Finite T) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a2))) (Complement T (fun t : T => proj1_sig (exist (fun G : T -> FT K => Finite T (fun t0 : T => G t0 <> FO K)) (fun t0 : T => Fadd K (proj1_sig a1 t0) (proj1_sig a2 t0)) H3) t <> FO K)))).
apply conj.
reflexivity.
simpl.
move=> v u H4 H5.
rewrite H5.
suff: ((Fadd K (proj1_sig a1 u) (proj1_sig a2 u)) = FO K).
move=> H6.
rewrite H6.
rewrite (Vmul_O_l K V (x u)).
apply (Vadd_O_l K V (VO K V)).
elim H4.
move=> u0 H6 H7.
apply NNPP.
move=> H8.
apply (H6 H8).
suff: (Finite T (Union T (fun t : T => proj1_sig a1 t <> FO K) (fun t : T => proj1_sig a2 t <> FO K))).
move=> H3.
apply (Finite_downward_closed T (Union T (fun t : T => proj1_sig a1 t <> FO K) (fun t : T => proj1_sig a2 t <> FO K)) H3 (fun t : T => Fadd K (proj1_sig a1 t) (proj1_sig a2 t) <> FO K)).
move=> t H4.
apply NNPP.
move=> H5.
apply H4.
suff: (proj1_sig a1 t) = (FO K).
move=> H6.
suff: (proj1_sig a2 t) = (FO K).
move=> H7.
rewrite H6.
rewrite H7.
apply (Fadd_O_r K (FO K)).
apply NNPP.
move=> H7.
apply H5.
right.
apply H7.
apply NNPP.
move=> H6.
apply H5.
left.
apply H6.
apply (Union_preserves_Finite T (fun t : T => proj1_sig a1 t <> FO K) (fun t : T => proj1_sig a2 t <> FO K) (proj2_sig a1) (proj2_sig a2)).
apply conj.
move=> f v.
elim.
move=> a H1.
elim (classic (f = (FO K))).
move=> H2.
rewrite H2.
rewrite (Vmul_O_l K V v).
suff: (Finite T (fun (t : T) => FO K <> FO K)).
move=> H3.
exists (exist (fun (G : T -> FT K) => Finite T (fun t : T => G t <> FO K)) (fun (t : T) => FO K) H3).
suff: ((exist (Finite T) (fun t : T => proj1_sig (exist (fun G : T -> FT K => Finite T (fun t0 : T => G t0 <> FO K)) (fun _ : T => FO K) H3) t <> FO K) (proj2_sig (exist (fun G : T -> FT K => Finite T (fun t : T => G t <> FO K)) (fun _ : T => FO K) H3))) = FiniteEmpty T).
move=> H4.
rewrite H4.
rewrite MySumF2Empty.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> t H4.
apply False_ind.
apply H4.
reflexivity.
move=> t.
elim.
suff: ((fun _ : T => FO K <> FO K) = Empty_set T).
move=> H3.
rewrite H3.
apply (Empty_is_finite T).
apply Extensionality_Ensembles.
apply conj.
move=> t H3.
apply False_ind.
apply H3.
reflexivity.
move=> t.
elim.
move=> H2.
suff: (Finite T (fun (t : T) => Fmul K f (proj1_sig a t) <> FO K)).
move=> H3.
exists (exist (fun (G : T -> FT K) => Finite T (fun t : T => G t <> FO K)) (fun (t : T) => Fmul K f (proj1_sig a t)) H3).
rewrite H1.
suff: ((exist (Finite T) (fun t : T => proj1_sig a t <> FO K) (proj2_sig a)) = (exist (Finite T) (fun t : T => proj1_sig (exist (fun G : T -> FT K => Finite T (fun t0 : T => G t0 <> FO K)) (fun t0 : T => Fmul K f (proj1_sig a t0)) H3) t <> FO K) (proj2_sig (exist (fun G : T -> FT K => Finite T (fun t : T => G t <> FO K)) (fun t : T => Fmul K f (proj1_sig a t)) H3)))).
move=> H4.
rewrite H4.
simpl.
apply (FiniteSetInduction T (exist (Finite T) (fun t : T => Fmul K f (proj1_sig a t) <> FO K) H3)).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Vmul_O_r K V f).
move=> B b H5 H6 H7 H8.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite (Vmul_add_distr_l K V f (MySumF2 T B (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a t) (x t))) (Vmul K V (proj1_sig a b) (x b))).
rewrite H8.
rewrite (Vmul_assoc K V f (proj1_sig a b) (x b)).
reflexivity.
apply H7.
apply H7.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> t H4 H5.
apply H4.
rewrite - (Fmul_I_l K (proj1_sig a t)).
rewrite - (Finv_l K f).
rewrite (Fmul_assoc K (Finv K f) f (proj1_sig a t)).
rewrite H5.
apply (Fmul_O_r K (Finv K f)).
apply H2.
move=> t H4 H5.
apply H4.
rewrite H5.
apply (Fmul_O_r K f).
suff: ((fun t : T => Fmul K f (proj1_sig a t) <> FO K) = (fun t : T => proj1_sig a t <> FO K)).
move=> H3.
rewrite H3.
apply (proj2_sig a).
apply Extensionality_Ensembles.
apply conj.
move=> t H3 H4.
apply H3.
rewrite H4.
apply (Fmul_O_r K f).
move=> t H3 H4.
apply H3.
rewrite - (Fmul_I_l K (proj1_sig a t)).
rewrite - (Finv_l K f).
rewrite (Fmul_assoc K (Finv K f) f (proj1_sig a t)).
rewrite H4.
apply (Fmul_O_r K (Finv K f)).
apply H2.
suff: (Finite T (fun (t : T) => FO K <> FO K)).
move=> H1.
exists (exist (fun (G : T -> FT K) => Finite T (fun t : T => G t <> FO K)) (fun (t : T) => FO K) H1).
suff: ((exist (Finite T) (fun t : T => proj1_sig (exist (fun G : T -> FT K => Finite T (fun t0 : T => G t0 <> FO K)) (fun _ : T => FO K) H1) t <> FO K) (proj2_sig (exist (fun G : T -> FT K => Finite T (fun t : T => G t <> FO K)) (fun _ : T => FO K) H1))) = FiniteEmpty T).
move=> H2.
rewrite H2.
rewrite MySumF2Empty.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> t H2.
apply False_ind.
apply H2.
reflexivity.
move=> t.
elim.
suff: ((fun _ : T => FO K <> FO K) = Empty_set T).
move=> H1.
rewrite H1.
apply (Empty_is_finite T).
apply Extensionality_Ensembles.
apply conj.
move=> t H1.
apply False_ind.
apply H1.
reflexivity.
move=> t.
elim.
Qed.

Lemma SpanContainSelfVS : forall (K : Field) (V : VectorSpace K) (T : Type) (x : T -> VT K V) (t : T), In (VT K V) (SpanVS K V T x) (x t).
Proof.
move=> K V T x t.
elim (classic (FI K = FO K)).
move=> H1.
rewrite - (Vmul_I_l K V (x t)).
rewrite H1.
rewrite (Vmul_O_l K V (x t)).
apply (proj2 (proj2 (SpanSubspaceVS K V T x))).
move=> H1.
suff: (Finite T (fun t0 : T => (fun (t1 : T) => match (excluded_middle_informative (t1 = t)) with
  | left _ => FI K
  | right _ => FO K
end) t0 <> FO K)).
move=> H2. 
exists (exist (fun (G : T -> FT K) => Finite T (fun t : T => G t <> FO K)) (fun t0 : T => (fun (t1 : T) => match (excluded_middle_informative (t1 = t)) with
  | left _ => FI K
  | right _ => FO K
end) t0) H2).
suff: ((exist (Finite T) (fun t0 : T => proj1_sig (exist (fun G : T -> FT K => Finite T (fun t1 : T => G t1 <> FO K)) (fun t1 : T => match excluded_middle_informative (t1 = t) with
  | left _ => FI K
  | right _ => FO K 
end) H2) t0 <> FO K) (proj2_sig (exist (fun G : T -> FT K => Finite T (fun t0 : T => G t0 <> FO K)) (fun t0 : T => match excluded_middle_informative (t0 = t) with
  | left _ => FI K
  | right _ => FO K 
end) H2))) = FiniteSingleton T t).
move=> H3.
rewrite H3.
rewrite MySumF2Singleton.
simpl.
elim (excluded_middle_informative (t = t)).
move=> H4.
rewrite (Vmul_I_l K V (x t)).
reflexivity.
move=> H4.
apply False_ind.
apply H4.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> t0.
unfold In.
elim (excluded_middle_informative (t0 = t)).
move=> H3 H4.
rewrite H3.
apply (In_singleton T t).
move=> H3 H4.
apply False_ind.
apply H4.
reflexivity.
move=> t0.
elim.
unfold In.
elim (excluded_middle_informative (t = t)).
move=> H3.
apply H1.
move=> H3 H4.
apply H3.
reflexivity.
suff: ((fun t0 : T => (match excluded_middle_informative (t0 = t) with
  | left _ =>  FI K
  | right _ => FO K
end) <> FO K) = Singleton T t).
move=> H2.
rewrite H2.
apply (Singleton_is_finite T t).
apply Extensionality_Ensembles.
apply conj.
move=> t0.
unfold In.
elim (excluded_middle_informative (t0 = t)).
move=> H2 H3.
rewrite H2.
apply (In_singleton T t).
move=> H2 H3.
apply False_ind.
apply H3.
reflexivity.
move=> t0.
elim.
unfold In.
elim (excluded_middle_informative (t = t)).
move=> H2.
apply H1.
move=> H2 H3.
apply H2.
reflexivity.
Qed.

Definition GeneratingSystemVS (K : Field) (V : VectorSpace K) (T : Type) (F : T -> VT K V) := Full_set (VT K V) = SpanVS K V T F.

Lemma IsomorphicSaveGeneratingSystemVS : forall (K : Field) (V1 V2 : VectorSpace K) (T : Type) (F : T -> VT K V1) (G : VT K V1 -> VT K V2), IsomorphicVS K V1 V2 G -> GeneratingSystemVS K V1 T F -> GeneratingSystemVS K V2 T (fun t : T => G (F t)).
Proof.
move=> K V1 V2 T F G H1 H2.
apply Extensionality_Ensembles.
apply conj.
move=> v2 H3.
elim (BijSurj (VT K V1) (VT K V2) G (proj1 H1) v2).
move=> v1 H4.
suff: (In (VT K V1) (SpanVS K V1 T F) v1).
elim.
move=> x H5.
exists x.
rewrite - H4.
rewrite H5.
apply (FiniteSetInduction T (exist (Finite T) (fun t : T => proj1_sig x t <> FO K) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite - (Vmul_O_l K V1 (VO K V1)).
rewrite (proj2 (proj2 H1)).
rewrite (Vmul_O_l K V2 (G (VO K V1))).
reflexivity.
move=> B b H6 H7 H8 H9.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite (proj1 (proj2 H1) (MySumF2 T B (VSPCM K V1) (fun t : T => Vmul K V1 (proj1_sig x t) (F t))) (Vmul K V1 (proj1_sig x b) (F b))).
rewrite H9.
rewrite (proj2 (proj2 H1) (proj1_sig x b) (F b)).
reflexivity.
apply H8.
apply H8.
rewrite - H2.
apply (Full_intro (VT K V1) v1).
move=> v H3.
apply (Full_intro (VT K V2) v).
Qed.

Lemma BijectiveSaveGeneratingSystemVS : forall (K : Field) (V : VectorSpace K) (T1 T2 : Type) (F : T1 -> T2) (G : T2 -> VT K V), Bijective T1 T2 F -> GeneratingSystemVS K V T2 G -> GeneratingSystemVS K V T1 (fun t : T1 => G (F t)).
Proof.
move=> K V T1 T2 F G H1 H2.
suff: (SpanVS K V T1 (fun t : T1 => G (F t)) = SpanVS K V T2 G).
move=> H3.
unfold GeneratingSystemVS.
rewrite H3.
apply H2.
rewrite (BijectiveSaveSpanVS K V T1 T2 F G H1).
reflexivity.
Qed.

Lemma FiniteGeneratingSystemVS : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V), (GeneratingSystemVS K V (Count N) F) <-> (Full_set (VT K V) = (fun (v : VT K V) => exists (a : Count N -> FT K), v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n)))).
Proof.
move=> K V N F.
unfold GeneratingSystemVS.
rewrite (FiniteSpanVS K V N F).
apply conj.
apply.
apply.
Qed.

Lemma Proposition_4_9 : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)), SubspaceVS K V W1 -> SubspaceVS K V W2 -> forall (H : forall (x : ({v : VT K V | In (VT K V) W1 v} * {v : VT K V | In (VT K V) W2 v})), In (VT K V) (SumEnsembleVS K V W1 W2) (Vadd K V (proj1_sig (fst x)) (proj1_sig (snd x)))), (Intersection (VT K V) W1 W2 = Singleton (VT K V) (VO K V)) <-> Bijective ({v : VT K V | In (VT K V) W1 v} * {v : VT K V | In (VT K V) W2 v}) {v : VT K V | In (VT K V) (SumEnsembleVS K V W1 W2) v} (fun (x : ({v : VT K V | In (VT K V) W1 v} * {v : VT K V | In (VT K V) W2 v})) => exist (SumEnsembleVS K V W1 W2) (Vadd K V (proj1_sig (fst x)) (proj1_sig (snd x))) (H x)).
Proof.
move=> K V W1 W2 H1 H2 H3.
apply conj.
move=> H4.
apply (InjSurjBij ({v : VT K V | In (VT K V) W1 v} * {v : VT K V | In (VT K V) W2 v}) {v : VT K V | In (VT K V) (SumEnsembleVS K V W1 W2) v}).
move=> x1 x2 H5.
suff: (Vadd K V (proj1_sig (fst x1)) (Vopp K V (proj1_sig (fst x2))) = Vadd K V (proj1_sig (snd x2)) (Vopp K V (proj1_sig (snd x1)))).
move=> H6.
suff: (Vadd K V (proj1_sig (fst x1)) (Vopp K V (proj1_sig (fst x2))) = VO K V).
move=> H7.
apply injective_projections.
apply sig_map.
apply (Vminus_diag_uniq K V).
apply H7.
apply sig_map.
apply (Vminus_diag_uniq_sym K V).
rewrite - H6.
apply H7.
suff: (In (VT K V) (Singleton (VT K V) (VO K V)) (Vadd K V (proj1_sig (fst x1)) (Vopp K V (proj1_sig (fst x2))))).
elim.
reflexivity.
rewrite - H4.
apply (Intersection_intro (VT K V) W1 W2 (Vadd K V (proj1_sig (fst x1)) (Vopp K V (proj1_sig (fst x2))))).
apply (proj1 H1 (proj1_sig (fst x1)) (Vopp K V (proj1_sig (fst x2)))).
apply (proj2_sig (fst x1)).
apply (SubspaceMakeVSVoppSub K V W1 H1 (proj1_sig (fst x2)) (proj2_sig (fst x2))).
rewrite H6.
apply (proj1 H2 (proj1_sig (snd x2)) (Vopp K V (proj1_sig (snd x1)))).
apply (proj2_sig (snd x2)).
apply (SubspaceMakeVSVoppSub K V W2 H2 (proj1_sig (snd x1)) (proj2_sig (snd x1))).
apply (Vadd_eq_reg_r K V (proj1_sig (fst x2))).
rewrite (Vadd_assoc K V (proj1_sig (fst x1)) (Vopp K V (proj1_sig (fst x2))) (proj1_sig (fst x2))).
rewrite (Vadd_opp_l K V (proj1_sig (fst x2))).
rewrite (Vadd_O_r K V (proj1_sig (fst x1))).
rewrite (Vadd_comm K V (Vadd K V (proj1_sig (snd x2)) (Vopp K V (proj1_sig (snd x1)))) (proj1_sig (fst x2))).
rewrite - (Vadd_assoc K V (proj1_sig (fst x2)) (proj1_sig (snd x2)) (Vopp K V (proj1_sig (snd x1)))).
apply (Vadd_eq_reg_r K V (proj1_sig (snd x1))).
rewrite (Vadd_assoc K V (Vadd K V (proj1_sig (fst x2)) (proj1_sig (snd x2))) (Vopp K V (proj1_sig (snd x1))) (proj1_sig (snd x1))).
rewrite (Vadd_opp_l K V (proj1_sig (snd x1))).
rewrite (Vadd_O_r K V).
suff: (Vadd K V (proj1_sig (fst x1)) (proj1_sig (snd x1)) = proj1_sig (exist (SumEnsembleVS K V W1 W2) (Vadd K V (proj1_sig (fst x1)) (proj1_sig (snd x1))) (H3 x1))).
move=> H6.
rewrite H6.
rewrite H5.
reflexivity.
reflexivity.
move=> y.
suff: (exists (y1 y2 : VT K V), In (VT K V) W1 y1 /\ In (VT K V) W2 y2 /\ Vadd K V y1 y2 = proj1_sig y).
elim.
move=> y1.
elim.
move=> y2 H5.
exists (exist W1 y1 (proj1 H5), exist W2 y2 (proj1 (proj2 H5))).
apply sig_map.
apply (proj2 (proj2 H5)).
elim (proj2_sig y).
move=> y1 y2 H5 H6.
exists y1.
exists y2.
apply conj.
apply H5.
apply conj.
apply H6.
reflexivity.
move=> H4.
apply Extensionality_Ensembles.
apply conj.
move=> x.
elim.
move=> x0 H5 H6.
suff: (x0 = (VO K V)).
move=> H7.
rewrite H7.
apply (In_singleton (VT K V) (VO K V)).
suff: (In (VT K V) W2 (Vopp K V x0)).
move=> H7.
suff: ((exist W1 (VO K V) (proj2 (proj2 H1)), exist W2 (VO K V) (proj2 (proj2 H2))) = (exist W1 x0 H5, exist W2 (Vopp K V x0) H7)).
move=> H8.
suff: (VO K V = proj1_sig (fst (exist W1 (VO K V) (proj2 (proj2 H1)), exist W2 (VO K V) (proj2 (proj2 H2))))).
move=> H9.
rewrite H9.
rewrite H8.
reflexivity.
reflexivity.
apply (BijInj ({v : VT K V | In (VT K V) W1 v} * {v : VT K V | In (VT K V) W2 v}) {v : VT K V | In (VT K V) (SumEnsembleVS K V W1 W2) v} (fun (x : {v : VT K V | In (VT K V) W1 v} * {v : VT K V | In (VT K V) W2 v}) => exist (SumEnsembleVS K V W1 W2) (Vadd K V (proj1_sig (fst x)) (proj1_sig (snd x))) (H3 x)) H4).
apply sig_map.
simpl.
rewrite (Vadd_O_r K V (VO K V)).
rewrite (Vadd_opp_r K V x0).
reflexivity.
apply (SubspaceMakeVSVoppSub K V W2 H2 x0 H6).
move=> x.
elim.
apply (Intersection_intro (VT K V) W1 W2 (VO K V)).
apply (proj2 (proj2 H1)).
apply (proj2 (proj2 H2)).
Qed.

Lemma Corollary_4_10 : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2) (H3 : SubspaceVS K V (Intersection (VT K V) W1 W2)) (H4 : SubspaceVS K V (SumEnsembleVS K V W1 W2)) (T1 T2 T3 : Type) (x : T1 -> VT K V) (y : T2 -> VT K V) (z : T3 -> VT K V), BasisSubspaceVS K V (Intersection (VT K V) W1 W2) H3 T1 x -> BasisSubspaceVS K V W1 H1 (T1 + T2) (fun (t : T1 + T2) => match t with | inl t0 => x t0 | inr t0 => y t0 end) -> BasisSubspaceVS K V W2 H2 (T1 + T3) (fun (t : T1 + T3) => match t with | inl t0 => x t0 | inr t0 => z t0 end) -> BasisSubspaceVS K V (SumEnsembleVS K V W1 W2) H4 (T1 + T2 + T3) (fun (t : T1 + T2 + T3) => match t with | inl t0 => (match t0 with | inl t1 => x t1 | inr t1 => y t1 end) | inr t0 => z t0 end).
Proof.
move=> K V W1 W2 H1 H2 H3 H4 T1 T2 T3 x y z H5 H6 H7.
suff: (let W3 := SpanVS K V T3 z in BasisSubspaceVS K V (SumEnsembleVS K V W1 W2) H4 (T1 + T2 + T3) (fun t : T1 + T2 + T3 => match t with
  | inl (inl t1) => x t1
  | inl (inr t1) => y t1
  | inr t0 => z t0
end)).
apply.
move=> W3.
suff: (SubspaceVS K V W3).
move=> H8.
suff: (BasisSubspaceVS K V W3 H8 T3 z).
move=> H9.
suff: (SumEnsembleVS K V W1 W2 = SumEnsembleVS K V W1 W3).
move=> H10.
suff: (SubspaceVS K V (SumEnsembleVS K V W1 W3)).
move=> H11.
suff: (BasisSubspaceVS K V (SumEnsembleVS K V W1 W3) H11 (T1 + T2 + T3) (fun t : T1 + T2 + T3 => match t with
  | inl (inl t1) => x t1
  | inl (inr t1) => y t1
  | inr t0 => z t0
end)).
suff: (forall (U : Type) (P : U -> Prop) (Q : forall (u : U), P u -> Prop) (u1 u2 : U), (u1 = u2) -> (forall (H1 : P u1) (H2 : P u2), Q u1 H1 -> Q u2 H2)).
move=> H12.
apply (H12 (Ensemble (VT K V)) (SubspaceVS K V) (fun (u : (Ensemble (VT K V))) (H : SubspaceVS K V u) => BasisSubspaceVS K V u H (T1 + T2 + T3) (fun t : T1 + T2 + T3 => match t with
  | inl (inl t1) => x t1
  | inl (inr t1) => y t1
  | inr t0 => z t0
end))).
rewrite H10.
reflexivity.
move=> U P Q u1 u2 H12.
rewrite H12.
move=> H13 H14.
suff: (H13 = H14).
move=> H15.
rewrite H15.
apply.
apply proof_irrelevance.
suff: (forall (t : T1 + T2 + T3), In (VT K V) (SumEnsembleVS K V W1 W3) (match t with
  | inl (inl t1) => x t1
  | inl (inr t1) => y t1
  | inr t0 => z t0
end)).
move=> H12.
exists H12.
elim H6.
move=> H13 H14.
elim H9.
move=> H15 H16.
suff: ((fun t : T1 + T2 + T3 => exist (SumEnsembleVS K V W1 W3) match t with
  | inl (inl t1) => x t1
  | inl (inr t1) => y t1
  | inr t0 => z t0
end (H12 t)) = (fun t : T1 + T2 + T3 => exist (SumEnsembleVS K V W1 W3) (Vadd K V (proj1_sig (fst match t with
  | inl t0 => (exist W1 match t0 with
    | inl t1 => x t1
    | inr t1 => y t1
  end (H13 t0), exist W3 (VO K V) (proj2 (proj2 H8)))
  | inr t0 => (exist W1 (VO K V) (proj2 (proj2 H1)), exist W3 (z t0) (H15 t0))
end)) (proj1_sig (snd match t with
  | inl t0 => (exist W1 match t0 with
    | inl t1 => x t1
    | inr t1 => y t1
  end (H13 t0), exist W3 (VO K V) (proj2 (proj2 H8)))
  | inr t0 => (exist W1 (VO K V) (proj2 (proj2 H1)), exist W3 (z t0) (H15 t0))
end))) (SumEnsembleVS_intro K V W1 W3 (proj1_sig (fst match t with
  | inl t0 => (exist W1 match t0 with
    | inl t1 => x t1
    | inr t1 => y t1
  end (H13 t0), exist W3 (VO K V) (proj2 (proj2 H8)))
  | inr t0 => (exist W1 (VO K V) (proj2 (proj2 H1)), exist W3 (z t0) (H15 t0))
end)) (proj1_sig (snd match t with
  | inl t0 => (exist W1 match t0 with
    | inl t1 => x t1
    | inr t1 => y t1
  end (H13 t0), exist W3 (VO K V) (proj2 (proj2 H8)))
  | inr t0 => (exist W1 (VO K V) (proj2 (proj2 H1)), exist W3 (z t0) (H15 t0))
end)) (proj2_sig (fst match t with
  | inl t0 => (exist W1 match t0 with
    | inl t1 => x t1
    | inr t1 => y t1
  end (H13 t0), exist W3 (VO K V) (proj2 (proj2 H8)))
  | inr t0 => (exist W1 (VO K V) (proj2 (proj2 H1)), exist W3 (z t0) (H15 t0))
end)) (proj2_sig (snd match t with
  | inl t0 => (exist W1 match t0 with
    | inl t1 => x t1
    | inr t1 => y t1
  end (H13 t0), exist W3 (VO K V) (proj2 (proj2 H8)))
  | inr t0 => (exist W1 (VO K V) (proj2 (proj2 H1)), exist W3 (z t0) (H15 t0))
end))))).
move=> H17.
rewrite H17.
apply (IsomorphicSaveBasisVS K (PairVS K (SubspaceMakeVS K V W1 H1) (SubspaceMakeVS K V W3 H8)) (SubspaceMakeVS K V (SumEnsembleVS K V W1 W3) H11) (T1 + T2 + T3) (fun (t : T1 + T2 + T3) => match t with
  | inl t0 => (exist W1 match t0 with
    | inl t1 => x t1
    | inr t1 => y t1
  end (H13 t0), exist W3 (VO K V) (proj2 (proj2 H8)))
  | inr t0 => (exist W1 (VO K V) (proj2 (proj2 H1)), exist W3 (z t0) (H15 t0))
end) (fun (v : VT K (PairVS K (SubspaceMakeVS K V W1 H1) (SubspaceMakeVS K V W3 H8))) => exist (SumEnsembleVS K V W1 W3) (Vadd K V (proj1_sig (fst v)) (proj1_sig (snd v))) (SumEnsembleVS_intro K V W1 W3 (proj1_sig (fst v)) (proj1_sig (snd v)) (proj2_sig (fst v)) (proj2_sig (snd v))))).
apply conj.
apply (Proposition_4_9 K V W1 W3).
apply H1.
apply H8.
apply Extensionality_Ensembles.
apply conj.
move=> v H18.
elim H5.
move=> H19 H20.
suff: (In (VT K V) (Intersection (VT K V) W1 W2) v).
move=> H21.
elim (BijSurj (DirectSumField K T1) (VT K (SubspaceMakeVS K V (Intersection (VT K V) W1 W2) H3)) (fun g : DirectSumField K T1 => MySumF2 T1 (exist (Finite T1) (fun t : T1 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K (SubspaceMakeVS K V (Intersection (VT K V) W1 W2) H3)) (fun t : T1 => Vmul K (SubspaceMakeVS K V (Intersection (VT K V) W1 W2) H3) (proj1_sig g t) (exist (Intersection (VT K V) W1 W2) (x t) (H19 t)))) H20 (exist (Intersection (VT K V) W1 W2) v H21)).
move=> xt H22.
suff: (In (VT K V) W3 v).
move=> H23.
elim H9.
move=> H24 H25.
elim (BijSurj (DirectSumField K T3) (VT K (SubspaceMakeVS K V W3 H8)) (fun g : DirectSumField K T3 => MySumF2 T3 (exist (Finite T3) (fun t : T3 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K (SubspaceMakeVS K V W3 H8)) (fun t : T3 => Vmul K (SubspaceMakeVS K V W3 H8) (proj1_sig g t) (exist W3 (z t) (H24 t)))) H25 (exist W3 v H23)).
move=> zt H26.
suff: (proj1_sig zt = fun (t : T3) => FO K).
move=> H27.
suff: (v = proj1_sig (exist W3 v H23)).
move=> H28.
rewrite H28.
rewrite - H26.
suff: ((proj1_sig (MySumF2 T3 (exist (Finite T3) (fun t : T3 => proj1_sig zt t <> FO K) (proj2_sig zt)) (VSPCM K (SubspaceMakeVS K V W3 H8)) (fun t : T3 => Vmul K (SubspaceMakeVS K V W3 H8) (proj1_sig zt t) (exist W3 (z t) (H24 t))))) = VO K V).
move=> H29.
rewrite H29.
apply (In_singleton (VT K V) (VO K V)).
suff: ((MySumF2 T3 (exist (Finite T3) (fun t : T3 => proj1_sig zt t <> FO K) (proj2_sig zt)) (VSPCM K (SubspaceMakeVS K V W3 H8)) (fun t : T3 => Vmul K (SubspaceMakeVS K V W3 H8) (proj1_sig zt t) (exist W3 (z t) (H24 t)))) = exist W3 (VO K V) (proj2 (proj2 H8))).
move=> H30.
rewrite H30.
reflexivity.
apply (FiniteSetInduction T3 (exist (Finite T3) (fun t : T3 => proj1_sig zt t <> FO K) (proj2_sig zt))).
apply conj.
rewrite MySumF2Empty.
reflexivity.
move=> B b H29 H30 H31 H32.
rewrite MySumF2Add.
simpl.
rewrite H32.
rewrite H27.
unfold SubspaceMakeVSVadd.
unfold SubspaceMakeVSVmul.
apply sig_map.
simpl.
rewrite (Vmul_O_l K V (z b)).
apply (Vadd_O_r K V (VO K V)).
apply H31.
reflexivity.
suff: (Finite (T1 + T3) (fun (t : T1 + T3) => match t with | inl t0 => proj1_sig xt t0 | inr _ => FO K end <> FO K)).
move=> H27.
suff: (Finite (T1 + T3) (fun (t : T1 + T3) => match t with | inl _ => FO K | inr t0 => proj1_sig zt t0 end <> FO K)).
move=> H28.
suff: ((fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig zt t0
end) = (fun t : T1 + T3 => FO K)).
move=> H29.
apply functional_extensionality.
move=> t.
suff: (let temp := (fun _ : T1 + T3 => FO K) in proj1_sig zt t = FO K).
apply.
move=> temp.
suff: (FO K = temp (inr T1 t)).
move=> H30.
rewrite {2} H30.
suff: (temp = (fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig zt t0
end)).
move=> H31.
rewrite H31.
reflexivity.
rewrite H29.
unfold temp.
reflexivity.
reflexivity.
suff: ((fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig zt t0
end) = (fun t : T1 + T3 => match t with
  | inl t0 => proj1_sig xt t0
  | inr _ => FO K
end)).
move=> H29.
apply functional_extensionality.
elim.
move=> t.
reflexivity.
move=> t.
suff: (let temp := (fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig zt t0
end) in proj1_sig zt t = FO K).
apply.
move=> temp.
suff: (proj1_sig zt t = temp (inr T1 t)).
move=> H30.
rewrite H30.
suff: (temp = (fun t : T1 + T3 => match t with
  | inl t0 => proj1_sig xt t0
  | inr _ => FO K
end)).
move=> H31.
rewrite H31.
reflexivity.
rewrite - H29.
reflexivity.
reflexivity.
suff: (exist (fun (G : T1 + T3 -> FT K) => Finite (T1 + T3) (fun t : T1 + T3 => G t <> FO K)) (fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig zt t0
end) H28 = exist (fun (G : T1 + T3 -> FT K) => Finite (T1 + T3) (fun t : T1 + T3 => G t <> FO K)) (fun t : T1 + T3 => match t with
  | inl t0 => proj1_sig xt t0
  | inr _ => FO K
end) H27).
move=> H29.
suff: ((fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig zt t0
end) = proj1_sig (exist (fun (G : T1 + T3 -> FT K) => Finite (T1 + T3) (fun t : T1 + T3 => G t <> FO K)) (fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig zt t0
end) H28)).
move=> H30.
rewrite H30.
rewrite H29.
reflexivity.
reflexivity.
elim H7.
move=> H29 H30.
unfold BasisVS in H30.
apply (BijInj (DirectSumField K (T1 + T3)) (VT K (SubspaceMakeVS K V W2 H2)) (fun g : DirectSumField K (T1 + T3) => MySumF2 (T1 + T3) (exist (Finite (T1 + T3)) (fun t : T1 + T3 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t : T1 + T3 => Vmul K (SubspaceMakeVS K V W2 H2) (proj1_sig g t) (exist W2 match t with
  | inl t0 => x t0
  | inr t0 => z t0
end (H29 t)))) H30).
simpl.
apply sig_map.
suff: (proj1_sig (MySumF2 (T1 + T3) (exist (Finite (T1 + T3)) (fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig zt t0
end <> FO K) H28) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t : T1 + T3 => SubspaceMakeVSVmul K V W2 H2 match t with
  | inl _ => FO K
  | inr t0 => proj1_sig zt t0
end (exist W2 match t with
  | inl t0 => x t0
  | inr t0 => z t0
end (H29 t)))) = proj1_sig (MySumF2 T3 (exist (Finite T3) (fun t : T3 => proj1_sig zt t <> FO K) (proj2_sig zt)) (VSPCM K (SubspaceMakeVS K V W3 H8)) (fun t : T3 => Vmul K (SubspaceMakeVS K V W3 H8) (proj1_sig zt t) (exist W3 (z t) (H24 t))))).
move=> H31.
rewrite H31.
rewrite H26.
suff: (proj1_sig (MySumF2 (T1 + T3) (exist (Finite (T1 + T3)) (fun t : T1 + T3 => match t with
  | inl t0 => proj1_sig xt t0
  | inr _ => FO K
end <> FO K) H27) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t : T1 + T3 => SubspaceMakeVSVmul K V W2 H2 match t with
  | inl t0 => proj1_sig xt t0
  | inr _ => FO K
end (exist W2 match t with
  | inl t0 => x t0
  | inr t0 => z t0
end (H29 t)))) = proj1_sig (MySumF2 T1 (exist (Finite T1) (fun t : T1 => proj1_sig xt t <> FO K) (proj2_sig xt)) (VSPCM K (SubspaceMakeVS K V (Intersection (VT K V) W1 W2) H3)) (fun t : T1 => Vmul K (SubspaceMakeVS K V (Intersection (VT K V) W1 W2) H3) (proj1_sig xt t) (exist (Intersection (VT K V) W1 W2) (x t) (H19 t))))).
move=> H32.
rewrite H32.
rewrite H22.
reflexivity.
rewrite - (MySumF2BijectiveSame T1 (exist (Finite T1) (fun t : T1 => proj1_sig xt t <> FO K) (proj2_sig xt)) (T1 + T3) (exist (Finite (T1 + T3)) (fun t : T1 + T3 => match t with
  | inl t0 => proj1_sig xt t0
  | inr _ => FO K
end <> FO K) H27) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t : T1 + T3 => SubspaceMakeVSVmul K V W2 H2 match t with
  | inl t0 => proj1_sig xt t0
  | inr _ => FO K
end (exist W2 match t with
  | inl t0 => x t0
  | inr t0 => z t0
end (H29 t))) (fun (t : T1) => inl T3 t)).
apply (FiniteSetInduction T1 (exist (Finite T1) (fun t : T1 => proj1_sig xt t <> FO K) (proj2_sig xt))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H32 H33 H34 H35.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H35.
reflexivity.
apply H34.
apply H34.
simpl.
apply InjSurjBij.
move=> u1 u2 H32.
apply sig_map.
apply (injective_inl T1 T3).
suff: (inl (proj1_sig u1) = proj1_sig (exist (fun t : T1 + T3 => match t with
  | inl t0 => proj1_sig xt t0
  | inr _ => FO K
end <> FO K) (inl (proj1_sig u1)) (proj2_sig u1))).
move=> H33.
rewrite H33.
rewrite H32.
reflexivity.
reflexivity.
elim.
elim.
move=> t H32.
exists (exist (fun (u : T1) => proj1_sig xt u <> FO K) t H32).
reflexivity.
move=> t H32.
apply False_ind.
apply H32.
reflexivity.
rewrite - (MySumF2BijectiveSame T3 (exist (Finite T3) (fun t : T3 => proj1_sig zt t <> FO K) (proj2_sig zt)) (T1 + T3) (exist (Finite (T1 + T3)) (fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig zt t0
end <> FO K) H28) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t : T1 + T3 => SubspaceMakeVSVmul K V W2 H2 match t with
  | inl _ => FO K
  | inr t0 => proj1_sig zt t0
end (exist W2 match t with
  | inl t0 => x t0
  | inr t0 => z t0
end (H29 t))) (fun (t : T3) => inr T1 t)).
apply (FiniteSetInduction T3 (exist (Finite T3) (fun t : T3 => proj1_sig zt t <> FO K) (proj2_sig zt))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H31 H32 H33 H34.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H34.
reflexivity.
apply H33.
apply H33.
simpl.
apply InjSurjBij.
move=> u1 u2 H31.
apply sig_map.
apply (injective_inr T1 T3).
suff: (inr (proj1_sig u1) = proj1_sig (exist (fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig zt t0
end <> FO K) (inr (proj1_sig u1)) (proj2_sig u1))).
move=> H32.
rewrite H32.
rewrite H31.
reflexivity.
reflexivity.
elim.
elim.
move=> t H31.
apply False_ind.
apply H31.
reflexivity.
move=> t H31.
exists (exist (fun (u : T3) => proj1_sig zt u <> FO K) t H31).
reflexivity.
apply (Finite_downward_closed (T1 + T3) (Im T3 (T1 + T3) (fun (t : T3) => proj1_sig zt t <> FO K) (fun (t : T3) => inr T1 t))).
apply finite_image.
apply (proj2_sig zt).
elim.
move=> t1 H28.
apply False_ind.
apply H28.
reflexivity.
move=> t3 H29.
apply (Im_intro T3 (T1 + T3) (fun t : T3 => proj1_sig zt t <> FO K) (fun t : T3 => inr t) t3).
apply H29.
reflexivity.
apply (Finite_downward_closed (T1 + T3) (Im T1 (T1 + T3) (fun (t : T1) => proj1_sig xt t <> FO K) (fun (t : T1) => inl T3 t))).
apply finite_image.
apply (proj2_sig xt).
elim.
move=> t1 H27.
apply (Im_intro T1 (T1 + T3) (fun t : T1 => proj1_sig xt t <> FO K) (fun t : T1 => inl t) t1).
apply H27.
reflexivity.
move=> t3 H27.
apply False_ind.
apply H27.
reflexivity.
elim H18.
move=> v0 H23 H24.
apply H24.
apply (Intersection_intro (VT K V) W1 W2 v).
elim H18.
move=> v0 H21 H22.
apply H21.
elim H18.
move=> v0 H21.
elim.
move=> x0 H22.
rewrite H22.
apply (FiniteSetInduction T3 (exist (Finite T3) (fun t : T3 => proj1_sig x0 t <> FO K) (proj2_sig x0))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 H2)).
move=> B b H23 H24 H25 H26.
rewrite MySumF2Add.
apply (proj1 H2).
apply H26.
apply (proj1 (proj2 H2)).
elim H7.
move=> H27 H28.
apply (H27 (inr T1 b)).
apply H25.
move=> t.
elim.
apply (Intersection_intro (VT K V) W1 W3 (VO K V) (proj2 (proj2 H1)) (proj2 (proj2 H8))).
apply conj.
move=> v1 v2.
apply sig_map.
simpl.
rewrite (Vadd_assoc K V (proj1_sig (fst v1)) (proj1_sig (fst v2)) (Vadd K V (proj1_sig (snd v1)) (proj1_sig (snd v2)))).
rewrite - (Vadd_assoc K V (proj1_sig (fst v2)) (proj1_sig (snd v1)) (proj1_sig (snd v2))).
rewrite (Vadd_comm K V (proj1_sig (fst v2)) (proj1_sig (snd v1))).
rewrite (Vadd_assoc K V (proj1_sig (snd v1)) (proj1_sig (fst v2)) (proj1_sig (snd v2))).
rewrite (Vadd_assoc K V (proj1_sig (fst v1)) (proj1_sig (snd v1)) (Vadd K V (proj1_sig (fst v2)) (proj1_sig (snd v2)))).
reflexivity.
move=> c v.
apply sig_map.
simpl.
rewrite (Vmul_add_distr_l K V).
reflexivity.
apply (PairBasisVS K (T1 + T2) T3 (SubspaceMakeVS K V W1 H1) (SubspaceMakeVS K V W3 H8)).
apply H14.
apply H16.
apply functional_extensionality.
move=> t.
apply sig_map.
simpl.
elim t.
elim.
move=> t1.
simpl.
rewrite (Vadd_O_r K V (x t1)).
reflexivity.
move=> t2.
simpl.
rewrite (Vadd_O_r K V (y t2)).
reflexivity.
move=> t3.
simpl.
rewrite (Vadd_O_l K V (z t3)).
reflexivity.
elim.
move=> t.
rewrite - (Vadd_O_r K V (match t with
  | inl t1 => x t1
  | inr t1 => y t1
end)).
apply (SumEnsembleVS_intro K V W1 W3 (match t with
  | inl t1 => x t1
  | inr t1 => y t1
end) (VO K V)).
elim H6.
move=> H12 H13.
apply (H12 t).
apply (proj2 (proj2 H8)).
move=> t.
rewrite - (Vadd_O_l K V (z t)).
elim H9.
move=> H12 H13.
apply (SumEnsembleVS_intro K V W1 W3 (VO K V) (z t) (proj2 (proj2 H1)) (H12 t)).
apply (SumSubspaceVS K V W1 W3 H1 H8).
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> t1 t2 H10 H11.
elim H7.
move=> H12 H13.
elim (BijSurj (DirectSumField K (T1 + T3)) (VT K (SubspaceMakeVS K V W2 H2)) (fun g : DirectSumField K (T1 + T3) => MySumF2 (T1 + T3) (exist (Finite (T1 + T3)) (fun t : T1 + T3 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t : T1 + T3 => Vmul K (SubspaceMakeVS K V W2 H2) (proj1_sig g t) (exist W2 match t with
  | inl t0 => x t0
  | inr t0 => z t0
end (H12 t)))) H13 (exist W2 t2 H11)).
move=> x0 H14.
suff: (Vadd K V t1 t2 = (Vadd K V (Vadd K V t1 (proj1_sig (MySumF2 (T1 + T3) (FiniteIntersection (T1 + T3) (exist (Finite (T1 + T3)) (fun t0 : T1 + T3 => proj1_sig x0 t0 <> FO K) (proj2_sig x0)) (fun t0 : T1 + T3 => match t0 with
  | inl _ => True
  | inr _ => False
end)) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t0 : T1 + T3 => Vmul K (SubspaceMakeVS K V W2 H2) (proj1_sig x0 t0) (exist W2 match t0 with
  | inl t3 => x t3
  | inr t3 => z t3
end (H12 t0)))))) (proj1_sig (MySumF2 (T1 + T3) (FiniteIntersection (T1 + T3) (exist (Finite (T1 + T3)) (fun t0 : T1 + T3 => proj1_sig x0 t0 <> FO K) (proj2_sig x0)) (Complement (T1 + T3) (fun t0 : T1 + T3 => match t0 with
  | inl _ => True
  | inr _ => False
end))) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t0 : T1 + T3 => Vmul K (SubspaceMakeVS K V W2 H2) (proj1_sig x0 t0) (exist W2 match t0 with
  | inl t3 => x t3
  | inr t3 => z t3
end (H12 t0))))))).
move=> H15.
rewrite H15.
apply (SumEnsembleVS_intro K V W1 W3 (Vadd K V t1 (proj1_sig (MySumF2 (T1 + T3) (FiniteIntersection (T1 + T3) (exist (Finite (T1 + T3)) (fun t0 : T1 + T3 => proj1_sig x0 t0 <> FO K) (proj2_sig x0)) (fun t0 : T1 + T3 => match t0 with
  | inl _ => True
  | inr _ => False
end)) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t0 : T1 + T3 => Vmul K (SubspaceMakeVS K V W2 H2) (proj1_sig x0 t0) (exist W2 match t0 with
  | inl t3 => x t3
  | inr t3 => z t3
end (H12 t0)))))) (proj1_sig ((MySumF2 (T1 + T3) (FiniteIntersection (T1 + T3) (exist (Finite (T1 + T3)) (fun t0 : T1 + T3 => proj1_sig x0 t0 <> FO K) (proj2_sig x0)) (Complement (T1 + T3) (fun t0 : T1 + T3 => match t0 with
  | inl _ => True
  | inr _ => False
end))) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t0 : T1 + T3 => Vmul K (SubspaceMakeVS K V W2 H2) (proj1_sig x0 t0) (exist W2 match t0 with
  | inl t3 => x t3
  | inr t3 => z t3
end (H12 t0))))))).
apply (proj1 H1).
apply H10.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 H1)).
move=> cm u H16 H17.
apply (proj1 H1).
apply H17.
apply (proj1 (proj2 H1)).
suff: (In (T1 + T3) (fun t0 : T1 + T3 => match t0 with
  | inl _ => True
  | inr _ => False
end) u).
simpl.
unfold In.
elim u.
move=> t10 H18.
elim H6.
move=> H19 H20.
apply (H19 (inl t10)).
move=> t30 H18.
apply False_ind.
apply H18.
elim H16.
move=> u0 H18 H19.
apply H18.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 H8)).
move=> cm u H16 H17.
apply (proj1 H8).
apply H17.
apply (proj1 (proj2 H8)).
suff: (In (T1 + T3) (Complement (T1 + T3) (fun t0 : T1 + T3 => match t0 with
  | inl _ => True
  | inr _ => False
end)) u).
simpl.
unfold In.
elim u.
move=> t10 H18.
apply False_ind.
apply H18.
apply I.
move=> t30 H18.
elim H9.
move=> H19 H20.
apply (H19 t30).
elim H16.
move=> u0 H18 H19.
apply H18.
rewrite Vadd_assoc.
suff: (t2 = proj1_sig (MySumF2 (T1 + T3) (exist (Finite (T1 + T3)) (fun t : T1 + T3 => proj1_sig x0 t <> FO K) (proj2_sig x0)) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t : T1 + T3 => Vmul K (SubspaceMakeVS K V W2 H2) (proj1_sig x0 t) (exist W2 match t with
  | inl t0 => x t0
  | inr t0 => z t0
end (H12 t))))).
move=> H15.
rewrite H15.
rewrite (MySumF2Excluded (T1 + T3) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t0 : T1 + T3 => Vmul K (SubspaceMakeVS K V W2 H2) (proj1_sig x0 t0) (exist W2 match t0 with
  | inl t3 => x t3
  | inr t3 => z t3
end (H12 t0))) (exist (Finite (T1 + T3)) (fun t0 : T1 + T3 => proj1_sig x0 t0 <> FO K) (proj2_sig x0)) (fun (t : T1 + T3) => match t with inl _ => True | inr _ => False end)).
reflexivity.
suff: (t2 = proj1_sig (exist W2 t2 H11)).
move=> H15.
rewrite H15.
rewrite - H14.
reflexivity.
reflexivity.
move=> t.
elim.
move=> t1 t3 H10 H11.
apply (SumEnsembleVS_intro K V W1 W2 t1 t3 H10).
elim H11.
move=> x0 H12.
rewrite H12.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 H2)).
move=> cm u H13 H14.
apply (proj1 H2).
apply H14.
apply (proj1 (proj2 H2)).
elim H7.
move=> H15 H16.
apply (H15 (inr u)).
exists (SpanContainSelfVS K V T3 z).
apply InjSurjBij.
move=> x1 x2 H9.
suff: (forall (x : DirectSumField K T3), Finite (T1 + T3) (fun (t : T1 + T3) => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig x t0
end <> FO K)).
move=> H10.
suff: (exist (fun (G : T1 + T3 -> FT K) => Finite (T1 + T3) (fun t : T1 + T3 => G t <> FO K)) (fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig x1 t0
end) (H10 x1) = exist (fun (G : T1 + T3 -> FT K) => Finite (T1 + T3) (fun t : T1 + T3 => G t <> FO K)) (fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig x2 t0
end) (H10 x2)).
move=> H11.
apply sig_map.
apply functional_extensionality.
move=> t3.
suff: (proj1_sig x1 t3 = proj1_sig (exist (fun G : T1 + T3 -> FT K => Finite (T1 + T3) (fun t : T1 + T3 => G t <> FO K)) (fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig x1 t0
end) (H10 x1)) (inr t3)).
move=> H12.
rewrite H12.
rewrite H11.
reflexivity.
reflexivity.
elim H7.
move=> H11 H12.
apply (BijInj (DirectSumField K (T1 + T3)) (VT K (SubspaceMakeVS K V W2 H2)) (fun g : DirectSumField K (T1 + T3) => MySumF2 (T1 + T3) (exist (Finite (T1 + T3)) (fun t : T1 + T3 => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t : T1 + T3 => Vmul K (SubspaceMakeVS K V W2 H2) (proj1_sig g t) (exist W2 match t with
  | inl t0 => x t0
  | inr t0 => z t0
end (H11 t)))) H12).
simpl.
suff: (forall (x2 : DirectSumField K T3), proj1_sig (MySumF2 (T1 + T3) (exist (Finite (T1 + T3)) (fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig x2 t0
end <> FO K) (H10 x2)) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t : T1 + T3 => SubspaceMakeVSVmul K V W2 H2 match t with
  | inl _ => FO K
  | inr t0 => proj1_sig x2 t0
end (exist W2 match t with
  | inl t0 => x t0
  | inr t0 => z t0
end (H11 t)))) = proj1_sig (MySumF2 T3 (exist (Finite T3) (fun t : T3 => proj1_sig x2 t <> FO K) (proj2_sig x2)) (VSPCM K (SubspaceMakeVS K V W3 H8)) (fun t : T3 => Vmul K (SubspaceMakeVS K V W3 H8) (proj1_sig x2 t) (exist W3 (z t) (SpanContainSelfVS K V T3 z t))))).
move=> H13.
apply sig_map.
rewrite (H13 x1).
rewrite (H13 x2).
rewrite H9.
reflexivity.
move=> x0.
rewrite - (MySumF2BijectiveSame T3 (exist (Finite T3) (fun t : T3 => proj1_sig x0 t <> FO K) (proj2_sig x0)) (T1 + T3) (exist (Finite (T1 + T3)) (fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig x0 t0
end <> FO K) (H10 x0)) (VSPCM K (SubspaceMakeVS K V W2 H2)) (fun t : T1 + T3 => SubspaceMakeVSVmul K V W2 H2 match t with
  | inl _ => FO K
  | inr t0 => proj1_sig x0 t0
end (exist W2 match t with
  | inl t0 => x t0
  | inr t0 => z t0
end (H11 t))) (fun (t : T3) => inr t)).
apply (FiniteSetInduction T3 (exist (Finite T3) (fun t : T3 => proj1_sig x0 t <> FO K) (proj2_sig x0))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H13 H14 H15 H16.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H16.
reflexivity.
apply H15.
apply H15.
simpl.
apply InjSurjBij.
move=> u1 u2 H13.
apply sig_map.
apply (injective_inr T1 T3).
suff: (inr (proj1_sig u1) = proj1_sig (exist (fun t : T1 + T3 => match t with
  | inl _ => FO K
  | inr t0 => proj1_sig x0 t0
end <> FO K) (inr (proj1_sig u1)) (proj2_sig u1))).
move=> H14.
rewrite H14.
rewrite H13.
reflexivity.
reflexivity.
elim.
elim.
move=> t1 H13.
apply False_ind.
apply H13.
reflexivity.
move=> t3 H13.
exists (exist (fun (u : T3) => proj1_sig x0 u <> FO K) t3 H13).
reflexivity.
move=> x0.
apply (Finite_downward_closed (T1 + T3) (Im T3 (T1 + T3) (fun (t : T3) => proj1_sig x0 t <> FO K) (fun (t : T3) => inr T1 t))).
apply finite_image.
apply (proj2_sig x0).
move=> t.
unfold In.
elim t.
move=> t1 H10.
apply False_ind.
apply H10.
reflexivity.
move=> t3 H10.
apply (Im_intro T3 (T1 + T3) (fun t0 : T3 => proj1_sig x0 t0 <> FO K) (fun t0 : T3 => inr t0) t3).
apply H10.
reflexivity.
move=> y0.
elim (proj2_sig y0).
move=> x0 H9.
exists x0.
apply sig_map.
rewrite H9.
apply (FiniteSetInduction T3 (exist (Finite T3) (fun t : T3 => proj1_sig x0 t <> FO K) (proj2_sig x0))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H10 H11 H12 H13.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H13.
reflexivity.
apply H12.
apply H12.
apply SpanSubspaceVS.
Qed.

Lemma SumEnsembleBasisVS : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2) (H3 : SubspaceVS K V (SumEnsembleVS K V W1 W2)) (T1 T2 : Type) (x : T1 -> VT K V) (y : T2 -> VT K V), (Intersection (VT K V) W1 W2) = (Singleton (VT K V) (VO K V)) -> BasisSubspaceVS K V W1 H1 T1 x -> BasisSubspaceVS K V W2 H2 T2 y -> BasisSubspaceVS K V (SumEnsembleVS K V W1 W2) H3 (T1 + T2) (fun (t : T1 + T2) => match t with | inl t0 => x t0 | inr t0 => y t0 end).
Proof.
move=> K V W1 W2 H1 H2 H3 T1 T2 x y H4 H5 H6.
suff: (SubspaceVS K V (Intersection (VT K V) W1 W2)).
move=> H7.
suff: (BasisSubspaceVS K V (Intersection (VT K V) W1 W2) H7 {n : nat | Empty_set nat n} (fun (m : {n : nat | Empty_set nat n}) => match (proj2_sig m) with end)).
move=> H8.
suff: (BasisSubspaceVS K V (SumEnsembleVS K V W1 W2) H3 ({n : nat | Empty_set nat n} + T1 + T2) (fun t : {n : nat | Empty_set nat n} + T1 + T2 => match t with
  | inl (inl t1) => match proj2_sig t1 with end
  | inl (inr t1) => x t1
  | inr t0 => y t0
end)).
elim.
move=> H9 H10.
suff: (forall (t : T1 + T2), In (VT K V) (SumEnsembleVS K V W1 W2) match t with
  | inl t0 => x t0
  | inr t0 => y t0
end).
move=> H11.
exists H11.
suff: ((fun t : T1 + T2 => exist (SumEnsembleVS K V W1 W2) match t with
  | inl t0 => x t0
  | inr t0 => y t0
end (H11 t)) = (fun (t : T1 + T2) => (fun t : {n : nat | Empty_set nat n} + T1 + T2 => exist (SumEnsembleVS K V W1 W2) match t with
  | inl (inl t1) => match proj2_sig t1 with end
  | inl (inr t1) => x t1
  | inr t0 => y t0
end (H9 t)) ((fun t : T1 + T2 => match t with
  | inl t0 => (inl (inr t0))
  | inr t0 => (inr t0)
end) t))).
move=> H12.
rewrite H12.
apply (BijectiveSaveBasisVS K (SubspaceMakeVS K V (SumEnsembleVS K V W1 W2) H3) (T1 + T2) ({n : nat | Empty_set nat n} + T1 + T2) (fun t : T1 + T2 => match t with
  | inl t0 => (inl (inr t0))
  | inr t0 => (inr t0)
end) (fun t : {n : nat | Empty_set nat n} + T1 + T2 => exist (SumEnsembleVS K V W1 W2) match t with
  | inl (inl t1) => match proj2_sig t1 with end
  | inl (inr t1) => x t1
  | inr t0 => y t0
end (H9 t))).
apply InjSurjBij.
move=> t1 t2.
elim t1.
move=> t10.
elim t2.
move=> t11 H13.
suff: (t10 = t11).
move=> H14.
rewrite H14.
reflexivity.
apply (injective_inr {n : nat | Empty_set nat n} T1).
apply (injective_inl ({n : nat | Empty_set nat n} + T1) T2).
apply H13.
move=> t11 H13.
apply False_ind.
suff: (In ({n : nat | Empty_set nat n} + T1 + T2) (fun (t : {n : nat | Empty_set nat n} + T1 + T2) => match t with 
  | inl t0 => True
  | inr t0 => False
end) (inl (inr t10))).
rewrite H13.
apply.
apply I.
move=> t11.
elim t2.
move=> t12 H13.
apply False_ind.
suff: (In ({n : nat | Empty_set nat n} + T1 + T2) (fun (t : {n : nat | Empty_set nat n} + T1 + T2) => match t with 
  | inl t0 => False
  | inr t0 => True
end) (inr t11)).
rewrite H13.
apply.
apply I.
move=> t12 H13.
suff: (t11 = t12).
move=> H14.
rewrite H14.
reflexivity.
apply (injective_inr ({n : nat | Empty_set nat n} + T1) T2).
apply H13.
elim.
elim.
move=> t.
elim (proj2_sig t).
move=> t1.
exists (inl t1).
reflexivity.
move=> t2.
exists (inr t2).
reflexivity.
apply H10.
apply functional_extensionality.
move=> t.
apply sig_map.
simpl.
elim t.
move=> t1.
reflexivity.
move=> t2.
reflexivity.
elim.
move=> t1.
elim H5.
move=> H11 H12.
rewrite - (Vadd_O_r K V (x t1)).
apply (SumEnsembleVS_intro K V W1 W2 (x t1) (VO K V)).
apply (H11 t1).
apply (proj2 (proj2 H2)).
move=> t2.
rewrite - (Vadd_O_l K V (y t2)).
apply (SumEnsembleVS_intro K V W1 W2 (VO K V) (y t2)).
apply (proj2 (proj2 H1)).
elim H6.
move=> H11 H12.
apply (H11 t2).
apply (Corollary_4_10 K V W1 W2 H1 H2 H7 H3 {n : nat | Empty_set nat n} T1 T2 (fun (m : {n : nat | Empty_set nat n}) => match (proj2_sig m) with end) x y H8).
suff: (forall t : {n : nat | Empty_set nat n} + T1, In (VT K V) W1 match t with
  | inl t0 => match proj2_sig t0 with end
  | inr t0 => x t0
end).
move=> H9.
exists H9.
elim H5.
move=> H10 H11.
suff: ((fun t : {n : nat | Empty_set nat n} + T1 => exist W1 match t with
  | inl t0 => match proj2_sig t0 with end
  | inr t0 => x t0
end (H9 t)) = (fun t : {n : nat | Empty_set nat n} + T1 => exist W1 (x match t with
  | inl t0 => match proj2_sig t0 with end
  | inr t0 => t0
end) (H10 match t with
  | inl t0 => match proj2_sig t0 with end
  | inr t0 => t0
end))).
move=> H12.
rewrite H12.
apply (BijectiveSaveBasisVS K (SubspaceMakeVS K V W1 H1) ({n : nat | Empty_set nat n} + T1) T1 (fun t : ({n : nat | Empty_set nat n} + T1) => match t with
  | inl t0 => match (proj2_sig t0) with end
  | inr t0 => t0
end) (fun (t : T1) => exist W1 (x t) (H10 t))).
exists (fun (t : T1) => inr {n : nat | Empty_set nat n} t).
apply conj.
elim.
move=> t.
elim (proj2_sig t).
move=> t1.
reflexivity.
move=> t1.
reflexivity.
apply H11.
apply functional_extensionality.
elim.
move=> t.
elim (proj2_sig t).
move=> t1.
apply sig_map.
reflexivity.
elim H5.
move=> H9 H10.
elim.
move=> t.
elim (proj2_sig t).
apply H9.
suff: (forall t : {n : nat | Empty_set nat n} + T2, In (VT K V) W2 match t with
  | inl t0 => match proj2_sig t0 with end
  | inr t0 => y t0
end).
move=> H9.
exists H9.
elim H6.
move=> H10 H11.
suff: ((fun t : {n : nat | Empty_set nat n} + T2 => exist W2 match t with
  | inl t0 => match proj2_sig t0 with end
  | inr t0 => y t0
end (H9 t)) = (fun t : {n : nat | Empty_set nat n} + T2 => exist W2 (y match t with
  | inl t0 => match proj2_sig t0 with end
  | inr t0 => t0
end) (H10 match t with
  | inl t0 => match proj2_sig t0 with end
  | inr t0 => t0
end))).
move=> H12.
rewrite H12.
apply (BijectiveSaveBasisVS K (SubspaceMakeVS K V W2 H2) ({n : nat | Empty_set nat n} + T2) T2 (fun t : ({n : nat | Empty_set nat n} + T2) => match t with
  | inl t0 => match (proj2_sig t0) with end
  | inr t0 => t0
end) (fun (t : T2) => exist W2 (y t) (H10 t))).
exists (fun (t : T2) => inr {n : nat | Empty_set nat n} t).
apply conj.
elim.
move=> t.
elim (proj2_sig t).
move=> t1.
reflexivity.
move=> t1.
reflexivity.
apply H11.
apply functional_extensionality.
elim.
move=> t.
elim (proj2_sig t).
move=> t1.
apply sig_map.
reflexivity.
elim H6.
move=> H9 H10.
elim.
move=> t.
elim (proj2_sig t).
apply H9.
unfold BasisSubspaceVS.
suff: (forall t : {n : nat | Empty_set nat n}, In (VT K V) (Intersection (VT K V) W1 W2) match proj2_sig t with end).
move=> H8.
exists H8.
apply InjSurjBij.
move=> x1 x2 H9.
apply sig_map.
apply functional_extensionality.
move=> t.
elim (proj2_sig t).
move=> t.
suff: (Finite {n : nat | Empty_set nat n} (fun (t : {n : nat | Empty_set nat n}) => match (proj2_sig t) with end <> FO K)).
move=> H9.
exists (exist (fun (G : {n : nat | Empty_set nat n} -> FT K) => Finite {n : nat | Empty_set nat n} (fun t : {n : nat | Empty_set nat n} => G t <> FO K)) (fun (t : {n : nat | Empty_set nat n}) => match (proj2_sig t) with end) H9).
suff: ((exist (Finite {n : nat | Empty_set nat n}) (fun t0 : {n : nat | Empty_set nat n} => proj1_sig (exist (fun G : {n : nat | Empty_set nat n} -> FT K => Finite {n : nat | Empty_set nat n} (fun t1 : {n : nat | Empty_set nat n} => G t1 <> FO K)) (fun t1 : {n : nat | Empty_set nat n} => match proj2_sig t1 with end) H9) t0 <> FO K) (proj2_sig (exist (fun G : {n : nat | Empty_set nat n} -> FT K => Finite {n : nat | Empty_set nat n} (fun t0 : {n : nat | Empty_set nat n} => G t0 <> FO K)) (fun t0 : {n : nat | Empty_set nat n} => match proj2_sig t0 with end) H9))) = FiniteEmpty {n : nat | Empty_set nat n}).
move=> H10.
rewrite H10.
rewrite MySumF2Empty.
apply sig_map.
simpl.
suff: (In (VT K V) (Intersection (VT K V) W1 W2) (proj1_sig t)).
rewrite {1} H4.
elim.
reflexivity.
apply (proj2_sig t).
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> t0.
elim (proj2_sig t0).
move=> t0.
elim (proj2_sig t0).
suff: ((fun t0 : {n : nat | Empty_set nat n} => match proj2_sig t0 with end <> FO K) = Empty_set {n : nat | Empty_set nat n}).
move=> H9.
rewrite H9.
apply Empty_is_finite.
apply Extensionality_Ensembles.
apply conj.
move=> t0.
elim (proj2_sig t0).
move=> t0.
elim (proj2_sig t0).
move=> t.
elim (proj2_sig t).
apply (IntersectionSubspaceVS K V W1 W2 H1 H2).
Qed.

Lemma Formula_P23 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : {n : nat | n < N} -> VT K V) (H : forall (t : (forall (m : {n : nat | n < N}), {v : VT K V | exists (f : FT K), v = Vmul K V f (F m)})), In (VT K V) (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun (m : {n : nat | n < N}) => proj1_sig (t m)))), BasisVS K V {n : nat | n < N} F <-> ((Bijective (DirectProdVST K {n : nat | n < N} (fun (m : {n : nat | n < N}) => SubspaceMakeVS K V (fun (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m)) (SingleSubspaceVS K V (F m)))) {w : VT K V | SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m)) w} (fun (t : forall (m : {n : nat | n < N}), {v : VT K V | exists (f : FT K), v = Vmul K V f (F m)}) => exist (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun (m : {n : nat | n < N}) => proj1_sig (t m))) (H t))) /\ (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m)) = Full_set (VT K V)) /\ forall (m : {n : nat | n < N}), (F m) <> VO K V).
Proof.
move=> K V N F H1.
apply conj.
move=> H2.
suff: (forall m : {n : nat | n < N}, F m <> VO K V).
move=> H3.
apply conj.
apply InjSurjBij.
move=> x1 x2 H4.
suff: (exists (a : {n : nat | n < N} -> FT K), (forall (m : {n : nat | n < N}), proj1_sig (x1 m) = Vmul K V (a m) (F m)) /\ forall (m : {n : nat | n < N}), proj1_sig (x2 m) = Vmul K V (a m) (F m)).
elim.
move=> a H5.
apply functional_extensionality_dep.
move=> m.
apply sig_map.
rewrite (proj2 H5 m).
apply (proj1 H5 m).
suff: (forall (m : {n : nat | n < N}), {f : FT K | proj1_sig (x1 m) = Vmul K V f (F m)}).
move=> H5.
exists (fun (m : {n : nat | n < N}) => proj1_sig (H5 m)).
apply conj.
move=> m.
apply (proj2_sig (H5 m)).
suff: (forall (m : {n : nat | n < N}), {f : FT K | proj1_sig (x2 m) = Vmul K V f (F m)}).
move=> H6.
suff: ((fun (m : {n : nat | n < N}) => (proj1_sig (H5 m))) = (fun (m : {n : nat | n < N}) => (proj1_sig (H6 m)))).
move=> H7 m.
suff: ((proj1_sig (H5 m)) = let temp := (fun m : {n : nat | n < N} => proj1_sig (H5 m)) in temp m).
move=> H8.
rewrite H8.
rewrite H7.
apply (proj2_sig (H6 m)).
reflexivity.
apply (proj2 (proj2 (unique_existence (fun (a : Count N -> FT K) => MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun m : {n : nat | n < N} => proj1_sig (x1 m)) = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n)))) (proj1 (FiniteBasisVS K V N F) H2 (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun m : {n : nat | n < N} => proj1_sig (x1 m)))))).
suff: ((fun m : {n : nat | n < N} => proj1_sig (x1 m)) = (fun n : Count N => Vmul K V (proj1_sig (H5 n)) (F n))).
move=> H7.
rewrite H7.
reflexivity.
apply functional_extensionality.
move=> m.
apply (proj2_sig (H5 m)).
suff: (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun m : {n : nat | n < N} => proj1_sig (x1 m)) = proj1_sig (exist (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun m : {n : nat | n < N} => proj1_sig (x1 m))) (H1 x1))).
move=> H7.
rewrite H7.
rewrite H4.
simpl.
suff: ((fun m : {n : nat | n < N} => proj1_sig (x2 m)) = (fun n : Count N => Vmul K V (proj1_sig (H6 n)) (F n))).
move=> H8.
rewrite H8.
reflexivity.
apply functional_extensionality.
move=> m.
apply (proj2_sig (H6 m)).
reflexivity.
move=> m.
apply (constructive_definite_description (fun (f : FT K) => proj1_sig (x2 m) = Vmul K V f (F m))).
apply (proj1 (unique_existence (fun (f : FT K) => proj1_sig (x2 m) = Vmul K V f (F m)))).
apply conj.
apply (proj2_sig (x2 m)).
move=> f1 f2 H6 H7.
apply (Vmul_eq_reg_r K V (F m) f1 f2).
rewrite - H6.
apply H7.
apply (H3 m).
move=> m.
apply (constructive_definite_description (fun (f : FT K) => proj1_sig (x1 m) = Vmul K V f (F m))).
apply (proj1 (unique_existence (fun (f : FT K) => proj1_sig (x1 m) = Vmul K V f (F m)))).
apply conj.
apply (proj2_sig (x1 m)).
move=> f1 f2 H5 H6.
apply (Vmul_eq_reg_r K V (F m) f1 f2).
rewrite - H5.
apply H6.
apply (H3 m).
move=> v.
suff: (In (VT K V) (fun t : VT K V => exists a : {n : nat | n < N} -> VT K V, (forall m : {n : nat | n < N}, In (VT K V) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F m)) (a m)) /\ MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) a = t) (proj1_sig v)).
elim.
move=> a H4.
exists (fun (m : {n : nat | n < N}) => exist (fun v : VT K V => exists f : FT K, v = Vmul K V f (F m)) (a m) (proj1 H4 m)).
apply sig_map.
apply (proj2 H4).
rewrite - (FiniteSumTEnsembleVS K V N (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))).
apply (proj2_sig v).
apply conj.
apply Extensionality_Ensembles.
apply conj.
move=> v H4.
apply (Full_intro (VT K V) v).
move=> v H4.
elim (proj1 (proj2 (unique_existence (fun (a : Count N -> FT K) => v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n)))) (proj1 (FiniteBasisVS K V N F) H2 v))).
move=> a H5.
rewrite H5.
rewrite (FiniteSumTEnsembleVS K V N (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))).
exists (fun n : Count N => Vmul K V (a n) (F n)).
apply conj.
move=> m.
exists (a m).
reflexivity.
reflexivity.
apply H3.
move=> m H3.
apply (FI_neq_FO K).
suff: ((fun (k : {n : nat | n < N}) => match excluded_middle_informative (k = m) with | left _ => FI K | right _ => FO K end) = (fun (k : {n : nat | n < N}) => FO K)).
move=> H5.
suff: (FI K = let temp := (fun (k : {n : nat | n < N}) => match excluded_middle_informative (k = m) with | left _ => FI K | right _ => FO K end) in temp m).
move=> H6.
rewrite H6.
rewrite H5.
reflexivity.
simpl.
elim (excluded_middle_informative (m = m)).
move=> H6.
reflexivity.
move=> H6.
apply False_ind.
apply H6.
reflexivity.
apply (proj2 (proj2 (unique_existence (fun (t : {n : nat | n < N} -> FT K) => VO K V = MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun m : {n : nat | n < N} => Vmul K V (t m) (F m)))) (proj1 (FiniteBasisVS K V N F) H2 (VO K V))) ).
rewrite MySumF2O.
reflexivity.
move=> u H4.
elim (excluded_middle_informative (u = m)).
move=> H5.
rewrite H5.
rewrite H3.
apply (Vmul_O_r K V (FI K)).
move=> H5.
apply (Vmul_O_l K V (F u)).
rewrite MySumF2O.
reflexivity.
move=> u H4.
apply (Vmul_O_l K V (F u)).
move=> H2.
apply (proj2 (FiniteBasisVS K V N F)).
move=> v.
apply (proj1 (unique_existence (fun (a : {n : nat | n < N} -> FT K) => v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n))))).
apply conj.
suff: (In (VT K V) (fun t : VT K V => exists a : {n : nat | n < N} -> VT K V, (forall m : {n : nat | n < N}, In (VT K V) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F m)) (a m)) /\ MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) a = t) v).
elim.
move=> a H3.
suff: (forall (m : {n : nat | n < N}), {f : FT K | a m = Vmul K V f (F m)}).
move=> H4.
exists (fun (m : {n : nat | n < N}) => proj1_sig (H4 m)).
rewrite - (proj2 H3).
suff: (a = (fun n : Count N => Vmul K V (proj1_sig (H4 n)) (F n))).
move=> H5.
rewrite {1} H5.
reflexivity.
apply functional_extensionality.
move=> m.
apply (proj2_sig (H4 m)).
move=> m.
apply (constructive_definite_description (fun (f : FT K) => a m = Vmul K V f (F m))).
apply (proj1 (unique_existence (fun (f : FT K) => a m = Vmul K V f (F m)))).
apply conj.
elim (proj1 H3 m).
move=> f H4.
exists f.
apply H4.
move=> f1 f2 H4 H5.
apply (Vmul_eq_reg_r K V (F m) f1 f2).
rewrite - H4.
apply H5.
apply (proj2 (proj2 H2) m).
rewrite - (FiniteSumTEnsembleVS K V N (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))).
rewrite (proj1 (proj2 H2)).
apply (Full_intro (VT K V) v).
suff: (forall (a : {n : nat | n < N} -> FT K) (m : {n : nat | n < N}), In (VT K V) (fun (v : VT K V) => exists f : FT K, v = Vmul K V f (F m)) (Vmul K V (a m) (F m))).
move=> H3 a1 a2 H4 H5.
suff: ((fun n : Count N => exist (fun v : VT K V => exists f : FT K, v = Vmul K V f (F n)) (Vmul K V (a1 n) (F n)) (H3 a1 n)) = (fun n : Count N => exist (fun v : VT K V => exists f : FT K, v = Vmul K V f (F n)) (Vmul K V (a2 n) (F n)) (H3 a2 n))).
move=> H6.
apply functional_extensionality.
move=> m.
apply (Vmul_eq_reg_r K V (F m) (a1 m) (a2 m)).
suff: (Vmul K V (a1 m) (F m) = let temp := (fun n : Count N => exist (fun v : VT K V => exists f : FT K, v = Vmul K V f (F n)) (Vmul K V (a1 n) (F n)) (H3 a1 n)) in proj1_sig (temp m)).
move=> H7.
rewrite H7.
rewrite H6.
reflexivity.
reflexivity.
apply (proj2 (proj2 H2) m).
apply (BijInj (DirectProdVST K {n : nat | n < N} (fun m : {n : nat | n < N} => SubspaceMakeVS K V (fun v : VT K V => exists f : FT K, v = Vmul K V f (F m)) (SingleSubspaceVS K V (F m)))) {w : VT K V | SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m)) w} (fun t : forall m : {n : nat | n < N}, {v : VT K V | exists f : FT K, v = Vmul K V f (F m)} => exist (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun m : {n : nat | n < N} => proj1_sig (t m))) (H1 t))).
apply (proj1 H2).
apply sig_map.
simpl.
rewrite - H4.
apply H5.
move=> a m.
exists (a m).
reflexivity.
Qed.

Definition LinearlyIndependentVS (K : Field) (V : VectorSpace K) (T : Type) (F : T -> VT K V) := BasisVS K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F)) T (fun (t : T) => exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t)).

Lemma IsomorphicSaveLinearlyIndependentVS : forall (K : Field) (V1 V2 : VectorSpace K) (T : Type) (F : T -> VT K V1) (G : VT K V1 -> VT K V2), IsomorphicVS K V1 V2 G -> LinearlyIndependentVS K V1 T F -> LinearlyIndependentVS K V2 T (fun t : T => G (F t)).
Proof.
move=> K V1 V2 T F G H1 H2.
unfold LinearlyIndependentVS.
suff: (forall (v : VT K V1), (SpanVS K V1 T F) v -> (SpanVS K V2 T (fun t : T => G (F t))) (G v)).
move=> H3.
suff: ((fun t : T => exist (SpanVS K V2 T (fun t0 : T => G (F t0))) (G (F t)) (SpanContainSelfVS K V2 T (fun t0 : T => G (F t0)) t)) = (fun t : T => exist (SpanVS K V2 T (fun t0 : T => G (F t0))) (G (proj1_sig (exist (SpanVS K V1 T F) (F t) (SpanContainSelfVS K V1 T F t)))) (H3 (proj1_sig (exist (SpanVS K V1 T F) (F t) (SpanContainSelfVS K V1 T F t))) (proj2_sig (exist (SpanVS K V1 T F) (F t) (SpanContainSelfVS K V1 T F t)))))).
move=> H4.
rewrite H4.
apply (IsomorphicSaveBasisVS K (SubspaceMakeVS K V1 (SpanVS K V1 T F) (SpanSubspaceVS K V1 T F)) (SubspaceMakeVS K V2 (SpanVS K V2 T (fun t : T => G (F t))) (SpanSubspaceVS K V2 T (fun t : T => G (F t)))) T (fun t : T => exist (SpanVS K V1 T F) (F t) (SpanContainSelfVS K V1 T F t)) (fun v0 : {v : VT K V1 | SpanVS K V1 T F v} => exist (SpanVS K V2 T (fun t : T => G (F t))) (G (proj1_sig v0)) (H3 (proj1_sig v0) (proj2_sig v0)))).
apply conj.
apply (InjSurjBij {v : VT K V1 | SpanVS K V1 T F v} {v : VT K V2 | SpanVS K V2 T (fun t : T => G (F t)) v}).
move=> v1 v2 H5.
apply sig_map.
apply (BijInj (VT K V1) (VT K V2) G (proj1 H1) (proj1_sig v1) (proj1_sig v2)).
suff: (G (proj1_sig v1) = proj1_sig (exist (SpanVS K V2 T (fun t : T => G (F t))) (G (proj1_sig v1)) (H3 (proj1_sig v1) (proj2_sig v1)))).
move=> H6.
rewrite H6.
rewrite H5.
reflexivity.
reflexivity.
move=> v.
elim (BijSurj (VT K V1) (VT K V2) G (proj1 H1) (proj1_sig v)).
move=> v0 H5.
suff: (In (VT K V1) (SpanVS K V1 T F) v0).
move=> H6.
exists (exist (SpanVS K V1 T F) v0 H6).
apply sig_map.
apply H5.
elim (proj2_sig v).
move=> x H6.
exists x.
apply (BijInj (VT K V1) (VT K V2) G (proj1 H1) v0 (MySumF2 T (exist (Finite T) (fun t : T => proj1_sig x t <> FO K) (proj2_sig x)) (VSPCM K V1) (fun t : T => Vmul K V1 (proj1_sig x t) (F t)))).
rewrite H5.
rewrite H6.
apply (FiniteSetInduction T (exist (Finite T) (fun t : T => proj1_sig x t <> FO K) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite - (Vmul_O_l K V1 (VO K V1)).
rewrite (proj2 (proj2 H1)).
rewrite (Vmul_O_l K V2 (G (VO K V1))).
reflexivity.
move=> B b H7 H8 H9 H10.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite (proj1 (proj2 H1) (MySumF2 T B (VSPCM K V1) (fun t : T => Vmul K V1 (proj1_sig x t) (F t))) (Vmul K V1 (proj1_sig x b) (F b))).
rewrite H10.
rewrite (proj2 (proj2 H1) (proj1_sig x b) (F b)).
reflexivity.
apply H9.
apply H9.
apply conj.
move=> v1 v2.
apply sig_map.
apply (proj1 (proj2 H1) (proj1_sig v1) (proj1_sig v2)).
move=> c v.
apply sig_map.
apply (proj2 (proj2 H1) c (proj1_sig v)).
apply H2.
apply functional_extensionality.
move=> t.
apply sig_map.
reflexivity.
move=> v.
elim.
move=> x H3.
exists x.
rewrite H3.
apply (FiniteSetInduction T (exist (Finite T) (fun t : T => proj1_sig x t <> FO K) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite - (Vmul_O_l K V1 (VO K V1)).
rewrite (proj2 (proj2 H1)).
rewrite (Vmul_O_l K V2 (G (VO K V1))).
reflexivity.
move=> B b H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite (proj1 (proj2 H1) (MySumF2 T B (VSPCM K V1) (fun t : T => Vmul K V1 (proj1_sig x t) (F t))) (Vmul K V1 (proj1_sig x b) (F b))).
rewrite H7.
rewrite (proj2 (proj2 H1) (proj1_sig x b) (F b)).
reflexivity.
apply H6.
apply H6.
Qed.

Lemma BijectiveSaveLinearlyIndependentVS : forall (K : Field) (V : VectorSpace K) (T1 T2 : Type) (F : T1 -> T2) (G : T2 -> VT K V), Bijective T1 T2 F -> LinearlyIndependentVS K V T2 G -> LinearlyIndependentVS K V T1 (fun t : T1 => G (F t)).
Proof.
move=> K V T1 T2 F G H1 H2.
suff: (forall (x : T1 -> VT K V) (A1 A2 : Ensemble (VT K V)), A1 = A2 -> forall (H1 : SubspaceVS K V A1) (H2 : SubspaceVS K V A2) (H3 : forall (t : T1), In (VT K V) A1 (x t)) (H4 : forall (t : T1), In (VT K V) A2 (x t)), BasisVS K (SubspaceMakeVS K V A1 H1) T1 (fun t : T1 => exist A1 (x t) (H3 t)) -> BasisVS K (SubspaceMakeVS K V A2 H2) T1 (fun t : T1 => exist A2 (x t) (H4 t))).
move=> H3.
suff: (SpanVS K V T2 G = SpanVS K V T1 (fun t : T1 => G (F t))).
move=> H4.
suff: (forall t : T1, In (VT K V) (SpanVS K V T2 G) (G (F t))).
move=> H5.
apply (H3 (fun t : T1 => G (F t)) (SpanVS K V T2 G) (SpanVS K V T1 (fun t : T1 => G (F t))) H4 (SpanSubspaceVS K V T2 G) (SpanSubspaceVS K V T1 (fun t : T1 => G (F t))) H5 (SpanContainSelfVS K V T1 (fun t0 : T1 => G (F t0)))).
suff: ((fun t : T1 => exist (SpanVS K V T2 G) (G (F t)) (H5 t)) = (fun t : T1 => exist (SpanVS K V T2 G) (G (F t)) (SpanContainSelfVS K V T2 G (F t)))).
move=> H6.
rewrite H6.
apply (BijectiveSaveBasisVS K (SubspaceMakeVS K V (SpanVS K V T2 G) (SpanSubspaceVS K V T2 G)) T1 T2 F (fun t : T2 => exist (SpanVS K V T2 G) (G t) (SpanContainSelfVS K V T2 G t)) H1 H2).
apply functional_extensionality.
move=> t.
apply sig_map.
reflexivity.
move=> t.
apply (SpanContainSelfVS K V T2 G (F t)).
apply (BijectiveSaveSpanVS K V T1 T2 F G H1).
move=> x A1 A2 H3.
rewrite H3.
move=> H4 H5 H6 H7.
suff: (H4 = H5).
move=> H8.
suff: (H6 = H7).
move=> H9.
rewrite H8.
rewrite H9.
apply.
apply proof_irrelevance.
apply proof_irrelevance.
Qed.

Lemma FiniteLinearlyIndependentVS : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V), (LinearlyIndependentVS K V (Count N) F) <-> (forall (a : Count N -> FT K), MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun (n : Count N) => Vmul K V (a n) (F n)) = VO K V -> forall (m : Count N), a m = FO K).
Proof.
move=> K V N F.
apply conj.
suff: (forall (a : Count N -> FT K), In (VT K V) (SpanVS K V (Count N) F) (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n)))).
move=> H1 H2 a H3.
suff: (a = (fun (m : Count N) => FO K)).
move=> H4 m.
rewrite H4.
reflexivity.
suff: (In (VT K V) (SpanVS K V (Count N) F) (VO K V)).
move=> H4.
apply (proj2 (proj2 (unique_existence (fun (a : Count N -> FT K) => (exist (SpanVS K V (Count N) F) (VO K V) H4) = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K (SubspaceMakeVS K V (SpanVS K V (Count N) F) (SpanSubspaceVS K V (Count N) F))) (fun n : Count N => Vmul K (SubspaceMakeVS K V (SpanVS K V (Count N) F) (SpanSubspaceVS K V (Count N) F)) (a n) (exist (SpanVS K V (Count N) F) (F n) (SpanContainSelfVS K V (Count N) F n))))) (proj1 (FiniteBasisVS K (SubspaceMakeVS K V (SpanVS K V (Count N) F) (SpanSubspaceVS K V (Count N) F)) N (fun t : Count N => exist (SpanVS K V (Count N) F) (F t) (SpanContainSelfVS K V (Count N) F t))) H2 (exist (SpanVS K V (Count N) F) (VO K V) H4)))) .
suff: (proj1_sig (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K (SubspaceMakeVS K V (SpanVS K V (Count N) F) (SpanSubspaceVS K V (Count N) F))) (fun n : Count N => Vmul K (SubspaceMakeVS K V (SpanVS K V (Count N) F) (SpanSubspaceVS K V (Count N) F)) (a n) (exist (SpanVS K V (Count N) F) (F n) (SpanContainSelfVS K V (Count N) F n)))) = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n))).
move=> H5.
apply sig_map.
rewrite H5.
rewrite H3.
reflexivity.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H5 H6 H7 H8.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H8.
reflexivity.
apply H7.
apply H7.
rewrite MySumF2O.
apply sig_map.
reflexivity.
move=> u H5.
rewrite (Vmul_O_l K).
apply sig_map.
reflexivity.
apply (proj2 (proj2 (SpanSubspaceVS K V (Count N) F))).
move=> a.
rewrite (FiniteSpanVS K V N F).
exists a.
reflexivity.
move=> H1.
apply (proj2 (FiniteBasisVS K (SubspaceMakeVS K V (SpanVS K V (Count N) F) (SpanSubspaceVS K V (Count N) F)) N (fun t : Count N => exist (SpanVS K V (Count N) F) (F t) (SpanContainSelfVS K V (Count N) F t)))).
move=> v. 
apply (unique_existence (fun (a : Count N -> FT K) => v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K (SubspaceMakeVS K V (SpanVS K V (Count N) F) (SpanSubspaceVS K V (Count N) F))) (fun n : Count N => Vmul K (SubspaceMakeVS K V (SpanVS K V (Count N) F) (SpanSubspaceVS K V (Count N) F)) (a n) (exist (SpanVS K V (Count N) F) (F n) (SpanContainSelfVS K V (Count N) F n))))).
apply conj.
suff: (In (VT K V) (fun v : VT K V => exists a : Count N -> FT K, v = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a n) (F n))) (proj1_sig v)).
elim.
move=> a H2.
exists a.
apply sig_map.
rewrite H2.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H3 H4 H5 H6.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H6.
reflexivity.
apply H5.
apply H5.
rewrite - (FiniteSpanVS K V N F).
apply (proj2_sig v).
move=> a1 a2 H2 H3.
suff: (forall (m : Count N), Fadd K (a1 m) (Fopp K (a2 m)) = FO K).
move=> H4.
apply functional_extensionality.
move=> m.
apply (Fminus_diag_uniq K (a1 m) (a2 m) (H4 m)).
apply H1.
suff: (VO K V = proj1_sig (VO K (SubspaceMakeVS K V (SpanVS K V (Count N) F) (SpanSubspaceVS K V (Count N) F)))).
move=> H4.
rewrite H4.
rewrite - (Vadd_opp_r K (SubspaceMakeVS K V (SpanVS K V (Count N) F) (SpanSubspaceVS K V (Count N) F)) v).
rewrite {1} H2.
rewrite H3.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite (Vadd_opp_r K V (VO K V)).
reflexivity.
move=> B b H5 H6 H7 H8.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H8.
simpl.
suff: (forall (t1 t2 : VT K V), Vadd K V (Vadd K V t1 (Vopp K V t2)) (Vmul K V (Fadd K (a1 b) (Fopp K (a2 b))) (F b)) = Vadd K V (Vadd K V t1 (Vmul K V (a1 b) (F b))) (Vopp K V (Vadd K V t2 (Vmul K V (a2 b) (F b))))).
move=> H9.
apply (H9 (proj1_sig (MySumF2 (Count N) B (VSPCM K (SubspaceMakeVS K V (SpanVS K V (Count N) F) (SpanSubspaceVS K V (Count N) F))) (fun n : Count N => SubspaceMakeVSVmul K V (SpanVS K V (Count N) F) (SpanSubspaceVS K V (Count N) F) (a1 n) (exist (SpanVS K V (Count N) F) (F n) (SpanContainSelfVS K V (Count N) F n))))) (proj1_sig (MySumF2 (Count N) B (VSPCM K (SubspaceMakeVS K V (SpanVS K V (Count N) F) (SpanSubspaceVS K V (Count N) F))) (fun n : Count N => SubspaceMakeVSVmul K V (SpanVS K V (Count N) F) (SpanSubspaceVS K V (Count N) F) (a2 n) (exist (SpanVS K V (Count N) F) (F n) (SpanContainSelfVS K V (Count N) F n)))))).
move=> t1 t2.
rewrite (Vmul_add_distr_r K V (a1 b) (Fopp K (a2 b)) (F b)).
rewrite (Vadd_assoc K V t1 (Vopp K V t2) (Vadd K V (Vmul K V (a1 b) (F b)) (Vmul K V (Fopp K (a2 b)) (F b)))).
rewrite - (Vadd_assoc K V (Vopp K V t2) (Vmul K V (a1 b) (F b)) (Vmul K V (Fopp K (a2 b)) (F b))).
rewrite (Vadd_comm K V (Vopp K V t2) (Vmul K V (a1 b) (F b))).
rewrite (Vadd_assoc K V t1 (Vmul K V (a1 b) (F b)) (Vopp K V (Vadd K V t2 (Vmul K V (a2 b) (F b))))).
rewrite (Vadd_assoc K V (Vmul K V (a1 b) (F b)) (Vopp K V t2) (Vmul K V (Fopp K (a2 b)) (F b))).
rewrite (Vopp_add_distr K V t2 (Vmul K V (a2 b) (F b))).
rewrite (Vopp_mul_distr_l K V (a2 b) (F b)).
reflexivity.
apply H7.
apply H7.
apply H7.
reflexivity.
Qed.

Lemma BasisLIGeVS : forall (K : Field) (V : VectorSpace K) (T : Type) (F : T -> VT K V), BasisVS K V T F <-> (GeneratingSystemVS K V T F /\ LinearlyIndependentVS K V T F).
Proof.
move=> K V T F.
apply conj.
move=> H1.
suff: (GeneratingSystemVS K V T F).
move=> H2.
apply conj.
apply H2.
unfold LinearlyIndependentVS.
suff: (forall (v : VT K V), In (VT K V) (Full_set (VT K V)) v).
rewrite H2.
move=> H3.
suff: ((fun t : T => exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t)) = (fun t : T => exist (SpanVS K V T F) (F t) (H3 (F t)))).
move=> H4.
rewrite H4.
apply (IsomorphicSaveBasisVS K V (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F)) T F (fun (v : VT K V) => exist (SpanVS K V T F) v (H3 v))).
apply conj.
exists (fun (w : {v : VT K V | SpanVS K V T F v}) => proj1_sig w).
apply conj.
move=> x.
reflexivity.
move=> y.
apply sig_map.
reflexivity.
apply conj.
move=> x y.
apply sig_map.
reflexivity.
move=> c x.
apply sig_map.
reflexivity.
apply H1.
apply functional_extensionality.
move=> t.
apply sig_map.
reflexivity.
move=> v.
apply (Full_intro (VT K V) v).
apply Extensionality_Ensembles.
apply conj.
elim H1.
move=> G H2 v H3.
exists (G v).
rewrite (proj2 H2 v).
reflexivity.
move=> v H2.
apply (Full_intro (VT K V) v).
unfold LinearlyIndependentVS.
move=> H1.
suff: (F = (fun (t : T) => proj1_sig (exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t)))).
move=> H2.
rewrite H2.
apply (IsomorphicSaveBasisVS K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F)) V T (fun t : T => exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t)) (fun (w : {v : VT K V | SpanVS K V T F v}) => proj1_sig w)).
apply conj.
suff: (forall (v : VT K V), In (VT K V) (Full_set (VT K V)) v).
rewrite (proj1 H1).
move=> H3.
exists (fun (v : VT K V) => exist (SpanVS K V T F) v (H3 v)).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
reflexivity.
move=> v.
apply (Full_intro (VT K V) v).
apply conj.
move=> x y.
reflexivity.
move=> c x.
reflexivity.
apply (proj2 H1).
apply functional_extensionality.
move=> t.
reflexivity.
Qed.

Lemma Proposition_5_2 : forall (K : Field) (V : VectorSpace K) (N : nat) (H1 : forall (m : Count N), proj1_sig m < S N) (H2 : N < S N) (F : Count (S N) -> VT K V), (LinearlyIndependentVS K V (Count (S N)) F) <-> (LinearlyIndependentVS K V (Count N) (fun (m : Count N) => F (exist (fun (n : nat) => n < S N) (proj1_sig m) (H1 m))) /\ ~ (In (VT K V) (SpanVS K V (Count N) (fun (m : Count N) => F (exist (fun (n : nat) => n < S N) (proj1_sig m) (H1 m)))) (F (exist (fun (n : nat) => n < S N) N H2)))).
Proof.
move=> K V N H1 H2 F.
apply conj.
move=> H3.
apply conj.
apply (proj2 (FiniteLinearlyIndependentVS K V N (fun m : Count N => F (exist (fun n : nat => n < S N) (proj1_sig m) (H1 m))))).
move=> a H4.
suff: (forall (m : Count (S N)), (fun (n : Count (S N)) => match excluded_middle_informative (proj1_sig n < N) with
  | left H => a (exist (fun (k : nat) => k < N) (proj1_sig n) H)
  | right _ => FO K  
end) m = FO K).
move=> H5 m.
rewrite - (H5 (exist (fun (n : nat) => n < S N) (proj1_sig m) (H1 m))).
simpl.
elim (excluded_middle_informative (proj1_sig m < N)).
move=> H6.
suff: ((exist (fun k : nat => k < N) (proj1_sig m) H6) = m).
move=> H7.
rewrite H7.
reflexivity.
apply sig_map.
reflexivity.
move=> H6.
apply False_ind.
apply H6.
apply (proj2_sig m).
apply (proj1 (FiniteLinearlyIndependentVS K V (S N) F) H3).
rewrite (MySumF2Excluded (Count (S N)) (VSPCM K V) (fun n : Count (S N) => Vmul K V match excluded_middle_informative (proj1_sig n < N) with
  | left H => a (exist (fun k : nat => k < N) (proj1_sig n) H)
  | right _ => FO K
end (F n)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (fun (n : Count (S N)) => proj1_sig n < N)).
rewrite (MySumF2O (Count (S N)) (FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (Complement (Count (S N)) (fun n : Count (S N) => proj1_sig n < N)))).
simpl.
rewrite (Vadd_O_r K V).
rewrite - (MySumF2BijectiveSame (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Count (S N)) (FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (fun n : Count (S N) => proj1_sig n < N)) (VSPCM K V) (fun n : Count (S N) => Vmul K V match excluded_middle_informative (proj1_sig n < N) with
  | left H => a (exist (fun k : nat => k < N) (proj1_sig n) H)
  | right _ => FO K
end (F n)) (fun (n : Count N) => (exist (fun n0 : nat => n0 < S N) (proj1_sig n) (H1 n)))).
simpl.
suff: ((fun u : Count N => Vmul K V match excluded_middle_informative (proj1_sig u < N) with
  | left H => a (exist (fun k : nat => k < N) (proj1_sig u) H)
  | right _ => FO K
end (F (exist (fun n0 : nat => n0 < S N) (proj1_sig u) (H1 u)))) = (fun n : Count N => Vmul K V (a n) (F (exist (fun n0 : nat => n0 < S N) (proj1_sig n) (H1 n))))).
move=> H5.
rewrite H5.
apply H4.
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (proj1_sig m < N)).
move=> H5.
suff: ((exist (fun k : nat => k < N) (proj1_sig m) H5) = m).
move=> H6.
rewrite H6.
reflexivity.
apply sig_map.
reflexivity.
move=> H5.
apply False_ind.
apply H5.
apply (proj2_sig m).
simpl.
move=> u H5.
apply (Intersection_intro (Count (S N))).
apply (proj2_sig u).
apply (Full_intro (Count (S N))).
simpl.
move=> H5.
suff: (forall (u0 : {u : Count (S N) | Intersection (Count (S N)) (fun n : Count (S N) => proj1_sig n < N) (Full_set (Count (S N))) u}), proj1_sig (proj1_sig u0) < N).
move=> H6.
exists (fun (u0 : {u : Count (S N) | Intersection (Count (S N)) (fun n : Count (S N) => proj1_sig n < N) (Full_set (Count (S N))) u}) => (exist (Full_set (Count N)) (exist (fun n : nat => n < N) (proj1_sig (proj1_sig u0)) (H6 u0)) (Full_intro (Count N) (exist (fun n : nat => n < N) (proj1_sig (proj1_sig u0)) (H6 u0))))).
apply conj.
move=> x.
apply sig_map.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
reflexivity.
move=> u0.
elim (proj2_sig u0).
move=> m H6 H7.
apply H6.
move=> u H5.
elim (excluded_middle_informative (proj1_sig u < N)).
elim H5.
move=> m H6 H7 H8.
apply False_ind.
apply H6.
apply H8.
move=> H6.
apply (Vmul_O_l K V (F u)).
rewrite (FiniteSpanVS K V N).
elim.
move=> a H4.
apply (FI_neq_FO K).
rewrite - (Fopp_involutive K (FI K)).
apply (Fopp_eq_O_compat K (Fopp K (FI K))).
suff: (forall (m : Count (S N)), (fun n : Count (S N) => match excluded_middle_informative (proj1_sig n < N) with
  | left H => a (exist (fun k : nat => k < N) (proj1_sig n) H)
  | right _ => Fopp K (FI K)
end) m = FO K).
move=> H5.
rewrite - (H5 (exist (fun (n : nat) => n < S N) N H2)).
simpl.
elim (excluded_middle_informative (N < N)).
move=> H6.
apply False_ind.
apply (lt_irrefl N H6).
move=> H6.
reflexivity.
apply (proj1 (FiniteLinearlyIndependentVS K V (S N) F) H3).
rewrite (MySumF2Excluded (Count (S N)) (VSPCM K V) (fun n : Count (S N) => Vmul K V match excluded_middle_informative (proj1_sig n < N) with
  | left H => a (exist (fun k : nat => k < N) (proj1_sig n) H)
  | right _ => Fopp K (FI K)
end (F n)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (fun (n : Count (S N)) => proj1_sig n < N)).
suff: ((MySumF2 (Count (S N)) (FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (fun n : Count (S N) => proj1_sig n < N)) (VSPCM K V) (fun n : Count (S N) => Vmul K V match excluded_middle_informative (proj1_sig n < N) with
  | left H => a (exist (fun k : nat => k < N) (proj1_sig n) H)
  | right _ => Fopp K (FI K)
end (F n))) = F (exist (fun n : nat => n < S N) N H2)).
move=> H5.
rewrite H5.
suff: ((MySumF2 (Count (S N)) (FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (Complement (Count (S N)) (fun n : Count (S N) => proj1_sig n < N))) (VSPCM K V) (fun n : Count (S N) => Vmul K V match excluded_middle_informative (proj1_sig n < N) with
  | left H => a (exist (fun k : nat => k < N) (proj1_sig n) H)
  | right _ => Fopp K (FI K)
end (F n))) = Vopp K V (F (exist (fun n : nat => n < S N) N H2))).
move=> H6.
rewrite H6.
apply (Vadd_opp_r K V).
suff: ((FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (Complement (Count (S N)) (fun n : Count (S N) => proj1_sig n < N))) = (FiniteSingleton (Count (S N)) (exist (fun n : nat => n < S N) N H2))).
move=> H7.
rewrite H7.
rewrite MySumF2Singleton.
simpl.
elim (excluded_middle_informative (N < N)).
move=> H8.
apply False_ind.
apply (lt_irrefl N H8).
move=> H8.
rewrite (Vopp_mul_distr_l_reverse K V (FI K) (F (exist (fun n : nat => n < S N) N H2))).
rewrite (Vmul_I_l K V).
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> m.
elim.
move=> m0 H6 H7.
suff: (m0 = (exist (fun n : nat => n < S N) N H2)).
move=> H8.
rewrite H8.
apply (In_singleton (Count (S N)) (exist (fun n : nat => n < S N) N H2)).
apply sig_map.
simpl.
elim (le_lt_or_eq (proj1_sig m0) N).
move=> H8.
apply False_ind.
apply H6.
apply H8.
apply.
apply (le_S_n (proj1_sig m0) N (proj2_sig m0)).
move=> m.
elim.
apply Intersection_intro.
apply (lt_irrefl N).
apply (Full_intro (Count (S N)) (exist (fun n : nat => n < S N) N H2)).
rewrite H4.
rewrite - (MySumF2BijectiveSame (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Count (S N)) (FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (fun n : Count (S N) => proj1_sig n < N)) (VSPCM K V) (fun n : Count (S N) => Vmul K V match excluded_middle_informative (proj1_sig n < N) with
  | left H => a (exist (fun k : nat => k < N) (proj1_sig n) H)
  | right _ => Fopp K (FI K)
end (F n)) (fun (n : Count N) => (exist (fun n0 : nat => n0 < S N) (proj1_sig n) (H1 n)))).
simpl.
suff: ((fun u : Count N => Vmul K V match excluded_middle_informative (proj1_sig u < N) with
  | left H => a (exist (fun k : nat => k < N) (proj1_sig u) H)
  | right _ => Fopp K (FI K)
end (F (exist (fun n0 : nat => n0 < S N) (proj1_sig u) (H1 u)))) = (fun n : Count N => Vmul K V (a n) (F (exist (fun n0 : nat => n0 < S N) (proj1_sig n) (H1 n))))).
move=> H5.
rewrite H5.
reflexivity.
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (proj1_sig m < N)).
move=> H5.
suff: ((exist (fun k : nat => k < N) (proj1_sig m) H5) = m).
move=> H6.
rewrite H6.
reflexivity.
apply sig_map.
reflexivity.
move=> H5.
apply False_ind.
apply H5.
apply (proj2_sig m).
move=> u H5.
apply (Intersection_intro (Count (S N))).
apply (proj2_sig u).
apply (Full_intro (Count (S N))).
simpl.
move=> H5.
suff: (forall (u0 : {u : Count (S N) | Intersection (Count (S N)) (fun n : Count (S N) => proj1_sig n < N) (Full_set (Count (S N))) u}), proj1_sig (proj1_sig u0) < N).
move=> H6.
exists (fun (u0 : {u : Count (S N) | Intersection (Count (S N)) (fun n : Count (S N) => proj1_sig n < N) (Full_set (Count (S N))) u}) => (exist (Full_set (Count N)) (exist (fun n : nat => n < N) (proj1_sig (proj1_sig u0)) (H6 u0)) (Full_intro (Count N) (exist (fun n : nat => n < N) (proj1_sig (proj1_sig u0)) (H6 u0))))).
apply conj.
move=> x.
apply sig_map.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
reflexivity.
move=> u0.
elim (proj2_sig u0).
move=> m H6 H7.
apply H6.
move=> H3.
apply (proj2 (FiniteLinearlyIndependentVS K V (S N) F)).
move=> a H4.
suff: (a (exist (fun n : nat => n < S N) N H2) = FO K).
move=> H5.
suff: (forall (m : Count N), a (exist (fun n : nat => n < S N) (proj1_sig m) (H1 m)) = FO K).
move=> H6 m.
elim (le_lt_or_eq (proj1_sig m) N).
move=> H7.
rewrite - (H6 (exist (fun n : nat => n < N) (proj1_sig m) H7)).
suff: ((exist (fun n : nat => n < S N) (proj1_sig (exist (fun n : nat => n < N) (proj1_sig m) H7)) (H1 (exist (fun n : nat => n < N) (proj1_sig m) H7))) = m).
move=> H8.
rewrite H8.
reflexivity.
apply sig_map.
reflexivity.
move=> H7.
suff: (m = (exist (fun n : nat => n < S N) N H2)).
move=> H8.
rewrite H8.
apply H5.
apply sig_map.
apply H7.
apply (le_S_n (proj1_sig m) N (proj2_sig m)).
apply (proj1 (FiniteLinearlyIndependentVS K V N (fun m : Count N => F (exist (fun n : nat => n < S N) (proj1_sig m) (H1 m)))) (proj1 H3)).
rewrite - H4.
rewrite (MySumF2Excluded (Count (S N)) (VSPCM K V) (fun n : Count (S N) => Vmul K V (a n) (F n)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (fun (n : Count (S N)) => proj1_sig n < N)).
rewrite - (MySumF2BijectiveSame (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Count (S N)) (FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (fun n : Count (S N) => proj1_sig n < N)) (VSPCM K V) (fun n : Count (S N) => Vmul K V (a n) (F n)) (fun (n : Count N) => (exist (fun n0 : nat => n0 < S N) (proj1_sig n) (H1 n)))).
suff: ((FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (Complement (Count (S N)) (fun n : Count (S N) => proj1_sig n < N))) = (FiniteSingleton (Count (S N)) (exist (fun n : nat => n < S N) N H2))).
move=> H6.
rewrite H6.
rewrite MySumF2Singleton.
rewrite H5.
rewrite (Vmul_O_l K V).
simpl.
rewrite (Vadd_O_r K V).
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> m.
elim.
move=> m0 H6 H7.
suff: (m0 = exist (fun n : nat => n < S N) N H2).
move=> H8.
rewrite H8.
apply (In_singleton (Count (S N))).
apply sig_map.
simpl.
elim (le_lt_or_eq (proj1_sig m0) N).
move=> H8.
apply False_ind.
apply H6.
apply H8.
apply.
apply (le_S_n (proj1_sig m0) N (proj2_sig m0)).
move=> m.
elim.
apply (Intersection_intro (Count (S N))).
apply (lt_irrefl N).
apply (Full_intro (Count (S N))).
move=> u H6.
apply (Intersection_intro (Count (S N))).
apply (proj2_sig u).
apply (Full_intro (Count (S N))).
move=> H6.
simpl.
suff: (forall (u0 : {u : Count (S N) | Intersection (Count (S N)) (fun n : Count (S N) => proj1_sig n < N) (Full_set (Count (S N))) u}), proj1_sig (proj1_sig u0) < N).
move=> H7.
exists (fun (u0 : {u : Count (S N) | Intersection (Count (S N)) (fun n : Count (S N) => proj1_sig n < N) (Full_set (Count (S N))) u}) => (exist (Full_set (Count N)) (exist (fun n : nat => n < N) (proj1_sig (proj1_sig u0)) (H7 u0)) (Full_intro (Count N) (exist (fun n : nat => n < N) (proj1_sig (proj1_sig u0)) (H7 u0))))).
apply conj.
move=> x.
apply sig_map.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
reflexivity.
move=> u0.
elim (proj2_sig u0).
move=> m H7 H8.
apply H7.
apply NNPP.
move=> H5.
apply (proj2 H3).
rewrite (FiniteSpanVS K V N (fun m : Count N => F (exist (fun n : nat => n < S N) (proj1_sig m) (H1 m)))).
exists (fun (m : Count N) => Fopp K (Fmul K (Finv K (a (exist (fun n : nat => n < S N) N H2))) (a (exist (fun (n : nat) => n < S N) (proj1_sig m) (H1 m))))).
suff: (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (Fopp K (Fmul K (Finv K (a (exist (fun n0 : nat => n0 < S N) N H2))) (a (exist (fun n0 : nat => n0 < S N) (proj1_sig n) (H1 n))))) (F (exist (fun n0 : nat => n0 < S N) (proj1_sig n) (H1 n)))) = Vmul K V (Fopp K (Finv K (a (exist (fun n0 : nat => n0 < S N) N H2)))) (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a (exist (fun n0 : nat => n0 < S N) (proj1_sig n) (H1 n))) (F (exist (fun n0 : nat => n0 < S N) (proj1_sig n) (H1 n)))))).
move=> H6.
rewrite H6.
suff: ((MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM K V) (fun n : Count N => Vmul K V (a (exist (fun n0 : nat => n0 < S N) (proj1_sig n) (H1 n))) (F (exist (fun n0 : nat => n0 < S N) (proj1_sig n) (H1 n))))) = Vopp K V (Vmul K V (a (exist (fun n0 : nat => n0 < S N) N H2)) (F (exist (fun n : nat => n < S N) N H2)))).
move=> H7.
rewrite H7.
rewrite (Vmul_opp_opp K V).
rewrite (Vmul_assoc K V).
rewrite (Finv_l K (a (exist (fun n0 : nat => n0 < S N) N H2)) H5).
rewrite (Vmul_I_l K V).
reflexivity.
apply (Vadd_opp_r_uniq K V).
rewrite (Vadd_comm K V).
rewrite - H4.
rewrite (MySumF2Excluded (Count (S N)) (VSPCM K V) (fun n : Count (S N) => Vmul K V (a n) (F n)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (fun (n : Count (S N)) => proj1_sig n < N)).
rewrite - (MySumF2BijectiveSame (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Count (S N)) (FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (fun n : Count (S N) => proj1_sig n < N)) (VSPCM K V) (fun n : Count (S N) => Vmul K V (a n) (F n)) (fun (n : Count N) => (exist (fun n0 : nat => n0 < S N) (proj1_sig n) (H1 n)))).
suff: ((FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (Complement (Count (S N)) (fun n : Count (S N) => proj1_sig n < N))) = (FiniteSingleton (Count (S N)) (exist (fun n : nat => n < S N) N H2))).
move=> H7.
rewrite H7.
rewrite MySumF2Singleton.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> m.
elim.
move=> m0 H7 H8.
suff: (m0 = exist (fun n : nat => n < S N) N H2).
move=> H9.
rewrite H9.
apply (In_singleton (Count (S N))).
apply sig_map.
simpl.
elim (le_lt_or_eq (proj1_sig m0) N).
move=> H9.
apply False_ind.
apply H7.
apply H9.
apply.
apply (le_S_n (proj1_sig m0) N (proj2_sig m0)).
move=> m.
elim.
apply (Intersection_intro (Count (S N))).
apply (lt_irrefl N).
apply (Full_intro (Count (S N))).
move=> u H7.
apply (Intersection_intro (Count (S N))).
apply (proj2_sig u).
apply (Full_intro (Count (S N))).
move=> H7.
simpl.
suff: (forall (u0 : {u : Count (S N) | Intersection (Count (S N)) (fun n : Count (S N) => proj1_sig n < N) (Full_set (Count (S N))) u}), proj1_sig (proj1_sig u0) < N).
move=> H8.
exists (fun (u0 : {u : Count (S N) | Intersection (Count (S N)) (fun n : Count (S N) => proj1_sig n < N) (Full_set (Count (S N))) u}) => (exist (Full_set (Count N)) (exist (fun n : nat => n < N) (proj1_sig (proj1_sig u0)) (H8 u0)) (Full_intro (Count N) (exist (fun n : nat => n < N) (proj1_sig (proj1_sig u0)) (H8 u0))))).
apply conj.
move=> x.
apply sig_map.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
reflexivity.
move=> u.
elim (proj2_sig u).
move=> m H8 H9.
apply H8.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (Vmul_O_r K V).
reflexivity.
move=> B b H6 H7 H8 H9.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H9.
simpl.
rewrite (Vmul_add_distr_l K V).
rewrite (Vmul_assoc K V (Fopp K (Finv K (a (exist (fun n0 : nat => n0 < S N) N H2)))) (a (exist (fun n0 : nat => n0 < S N) (proj1_sig b) (H1 b)))).
rewrite (Fopp_mul_distr_l K (Finv K (a (exist (fun n0 : nat => n0 < S N) N H2))) (a (exist (fun n0 : nat => n0 < S N) (proj1_sig b) (H1 b)))).
reflexivity.
apply H8.
apply H8.
Qed.

End Senkeidaisuunosekai1.





