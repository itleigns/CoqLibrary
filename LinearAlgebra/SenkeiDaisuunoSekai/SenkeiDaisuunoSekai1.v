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
Require Import Coq.Program.Basics.
Require Import MyAlgebraicStructure.MyField.
Require Import MyAlgebraicStructure.MyVectorSpace.
Require Import BasicProperty.MappingProperty.
Require Import BasicProperty.NatProperty.
Require Import Tools.MySum.
Require Import Tools.BasicTools.
Require Import LibraryExtension.DatatypesExtension.
Require Import LibraryExtension.EnsemblesExtension.

Section Senkeidaisuunosekai1.

Definition VSPCM (K : Field) (V : VectorSpace K) : CommutativeMonoid := mkCommutativeMonoid (VT K V) (VO K V) (Vadd K V) (Vadd_comm K V) (Vadd_O_r K V) (Vadd_assoc K V).

Definition DirectSumField (K : Field) (T : Type) := {G : T -> FT K | Finite T (fun (t : T) => G t <> FO K)}.

Definition BasisVS (K : Field) (V : VectorSpace K) (T : Type) := fun (F : T -> VT K V) => Bijective (DirectSumField K T) (VT K V) (fun (g : DirectSumField K T) => MySumF2 T (exist (Finite T) (fun (t : T) => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K V) (fun (t : T) => Vmul K V (proj1_sig g t) (F t))).

Lemma BijectiveSaveBasisVS : forall (K : Field) (V : VectorSpace K) (T1 T2 : Type) (F : T1 -> T2) (G : T2 -> VT K V), Bijective T1 T2 F -> BasisVS K V T2 G -> BasisVS K V T1 (compose G F).
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

Lemma IsomorphicSaveBasisVS : forall (K : Field) (V1 V2 : VectorSpace K) (T : Type) (F : T -> VT K V1) (G : VT K V1 -> VT K V2), IsomorphicVS K V1 V2 G -> BasisVS K V1 T F -> BasisVS K V2 T (compose G F).
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

Definition OVST (F : Field) := (Count 1).

Definition OVSadd (F : Field) := fun (f1 f2 : OVST F) => exist (fun (n : nat) => n < S O) O (le_n (S O)).

Definition OVSmul (F : Field) := fun (c : FT F) (f : OVST F) => exist (fun (n : nat) => n < S O) O (le_n (S O)).

Definition OVSopp (F : Field) := fun (f : OVST F) => exist (fun (n : nat) => n < S O) O (le_n (S O)).

Definition OVSO (F : Field) := exist (fun (n : nat) => n < S O) O (le_n (S O)).

Lemma OVSadd_comm : forall (F : Field) (f1 f2 : OVST F), (OVSadd F f1 f2) = (OVSadd F f2 f1).
Proof.
move=> F f1 f2.
reflexivity.
Qed.

Lemma OVSadd_assoc : forall (F : Field) (f1 f2 f3 : OVST F), (OVSadd F (OVSadd F f1 f2) f3) = (OVSadd F f1 (OVSadd F f2 f3)).
Proof.
move=> F f1 f2 f3.
reflexivity.
Qed.

Lemma OVSadd_O_l : forall (F : Field) (f : OVST F), (OVSadd F (OVSO F) f) = f.
Proof.
move=> F f.
apply sig_map.
elim (le_lt_or_eq (proj1_sig f) O).
move=> H1.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig f) H1).
move=> H1.
rewrite H1.
reflexivity.
apply (le_S_n (proj1_sig f) O (proj2_sig f)).
Qed.

Lemma OVSadd_opp_r : forall (F : Field) (f : OVST F), (OVSadd F f (OVSopp F f)) = (OVSO F).
Proof.
move=> F f.
reflexivity.
Qed.

Lemma OVSadd_distr_l : forall (F : Field) (c : FT F) (f1 f2 : OVST F), (OVSmul F c (OVSadd F f1 f2)) = (OVSadd F (OVSmul F c f1) (OVSmul F c f2)).
Proof.
move=> F c f1 f2.
reflexivity.
Qed.

Lemma OVSadd_distr_r : forall (F : Field) (c1 c2 : FT F) (f : OVST F), (OVSmul F (Fadd F c1 c2) f) = (OVSadd F (OVSmul F c1 f) (OVSmul F c2 f)).
Proof.
move=> F c1 c2 f.
reflexivity.
Qed.

Lemma OVSmul_assoc : forall (F : Field) (c1 c2 : FT F) (f : OVST F), (OVSmul F c1 (OVSmul F c2 f)) = (OVSmul F (Fmul F c1 c2) f).
Proof.
move=> F c1 c2 f.
reflexivity.
Qed.

Lemma OVSmul_I_l : forall (F : Field) (f : OVST F), (OVSmul F (FI F) f) = f.
Proof.
move=> F f.
apply sig_map.
elim (le_lt_or_eq (proj1_sig f) O).
move=> H1.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig f) H1).
move=> H1.
rewrite H1.
reflexivity.
apply (le_S_n (proj1_sig f) O (proj2_sig f)).
Qed.

Definition OVS (F : Field) := mkVectorSpace F (OVST F) (OVSO F) (OVSadd F) (OVSmul F) (OVSopp F) (OVSadd_comm F) (OVSadd_assoc F) (OVSadd_O_l F) (OVSadd_opp_r F) (OVSadd_distr_l F) (OVSadd_distr_r F) (OVSmul_assoc F) (OVSmul_I_l F).

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

Lemma Formula_P18_1_exists : forall (K : Field) (V : VectorSpace K) (x : VT K V), exists (H : SubspaceVS K V (fun (v0 : VT K V) => exists (f : FT K), v0 = Vmul K V f x)), x <> VO K V -> BasisSubspaceVS K V (fun (v0 : VT K V) => exists (f : FT K), v0 = Vmul K V f x) H {n : nat | n < S O} (fun (m : {n : nat | n < S O}) => x).
Proof.
move=> K V x.
exists (SingleSubspaceVS K V x).
apply (Formula_P18_1 K V x (SingleSubspaceVS K V x)).
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

Lemma BijectiveSaveSpanVS : forall (K : Field) (V : VectorSpace K) (T1 T2 : Type) (F : T1 -> T2) (G : T2 -> VT K V), Bijective T1 T2 F -> SpanVS K V T2 G = SpanVS K V T1 (compose G F).
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

Lemma BijectiveSaveGeneratingSystemVS : forall (K : Field) (V : VectorSpace K) (T1 T2 : Type) (F : T1 -> T2) (G : T2 -> VT K V), Bijective T1 T2 F -> GeneratingSystemVS K V T2 G -> GeneratingSystemVS K V T1 (compose G F).
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

Lemma IsomorphicSaveGeneratingSystemVS : forall (K : Field) (V1 V2 : VectorSpace K) (T : Type) (F : T -> VT K V1) (G : VT K V1 -> VT K V2), IsomorphicVS K V1 V2 G -> GeneratingSystemVS K V1 T F -> GeneratingSystemVS K V2 T (compose G F).
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

Lemma SurjectiveSaveGeneratingSystemVS : forall (K : Field) (V : VectorSpace K) (T1 T2 : Type) (F : T1 -> T2) (G : T2 -> VT K V), Surjective T1 T2 F -> GeneratingSystemVS K V T2 G -> GeneratingSystemVS K V T1 (compose G F).
Proof.
move=> K V T1 T2 F G H1 H2.
apply Extensionality_Ensembles.
apply conj.
move=> v.
rewrite H2.
elim.
move=> x H3.
rewrite H3.
suff: (SubspaceVS K V (SpanVS K V T1 (fun t : T1 => G (F t)))).
move=> H4.
apply (FiniteSetInduction T2 (exist (Finite T2) (fun t : T2 => proj1_sig x t <> FO K) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 H4)).
move=> B b H5 H6 H7 H8.
rewrite MySumF2Add.
apply (proj1 H4).
apply H8.
apply (proj1 (proj2 H4) (proj1_sig x b) (G b)).
elim (H1 b).
move=> t H9.
rewrite - H9.
apply (SpanContainSelfVS K V T1 (fun t : T1 => G (F t)) t).
apply H7.
apply (SpanSubspaceVS K V).
move=> v H3.
apply (Full_intro (VT K V) v).
Qed.

Lemma SurjectiveSaveGeneratingSystemVS2 : forall (K : Field) (V1 V2 : VectorSpace K) (T : Type) (F : T -> VT K V1) (G : VT K V1 -> VT K V2), (Surjective (VT K V1) (VT K V2) G /\ (forall (x y : VT K V1), G (Vadd K V1 x y) = Vadd K V2 (G x) (G y)) /\ (forall (c : FT K) (x : VT K V1), G (Vmul K V1 c x) = Vmul K V2 c (G x))) -> GeneratingSystemVS K V1 T F -> GeneratingSystemVS K V2 T (compose G F).
Proof.
move=> K V1 V2 T F G H1 H2.
apply Extensionality_Ensembles.
apply conj.
move=> v H3.
elim (proj1 H1 v).
move=> u H4.
rewrite - H4.
suff: (In (VT K V1) (Full_set (VT K V1)) u).
rewrite H2.
elim.
move=> x H5.
rewrite H5.
exists x.
apply (FiniteSetInduction T (exist (Finite T) (fun t : T => proj1_sig x t <> FO K) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite - (Vmul_O_l K V1 (VO K V1)).
rewrite (proj2 (proj2 H1) (FO K) (VO K V1)).
apply (Vmul_O_l K V2 (G (VO K V1))).
move=> B b H6 H7 H8 H9.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite (proj1 (proj2 H1)).
rewrite (proj2 (proj2 H1) (proj1_sig x b) (F b)).
rewrite H9.
reflexivity.
apply H8.
apply H8.
apply (Full_intro (VT K V1) u).
move=> v H3.
apply (Full_intro (VT K V2) v).
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

Lemma Proposition_4_9_exists : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)), SubspaceVS K V W1 -> SubspaceVS K V W2 -> exists (H : forall (x : ({v : VT K V | In (VT K V) W1 v} * {v : VT K V | In (VT K V) W2 v})), In (VT K V) (SumEnsembleVS K V W1 W2) (Vadd K V (proj1_sig (fst x)) (proj1_sig (snd x)))), (Intersection (VT K V) W1 W2 = Singleton (VT K V) (VO K V)) <-> Bijective ({v : VT K V | In (VT K V) W1 v} * {v : VT K V | In (VT K V) W2 v}) {v : VT K V | In (VT K V) (SumEnsembleVS K V W1 W2) v} (fun (x : ({v : VT K V | In (VT K V) W1 v} * {v : VT K V | In (VT K V) W2 v})) => exist (SumEnsembleVS K V W1 W2) (Vadd K V (proj1_sig (fst x)) (proj1_sig (snd x))) (H x)).
Proof.
move=> K V W1 W2 H1 H2.
suff: (forall (x : {v : VT K V | In (VT K V) W1 v} * {v : VT K V | In (VT K V) W2 v}), In (VT K V) (SumEnsembleVS K V W1 W2) (Vadd K V (proj1_sig (fst x)) (proj1_sig (snd x)))).
move=> H3.
exists H3.
apply (Proposition_4_9 K V W1 W2 H1 H2 H3).
move=> x.
apply (SumEnsembleVS_intro K V W1 W2 (proj1_sig (fst x)) (proj1_sig (snd x)) (proj2_sig (fst x)) (proj2_sig (snd x))).
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

Lemma Corollary_4_10_exists : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2), exists (H3 : SubspaceVS K V (Intersection (VT K V) W1 W2)) (H4 : SubspaceVS K V (SumEnsembleVS K V W1 W2)), forall (T1 T2 T3 : Type) (x : T1 -> VT K V) (y : T2 -> VT K V) (z : T3 -> VT K V), BasisSubspaceVS K V (Intersection (VT K V) W1 W2) H3 T1 x -> BasisSubspaceVS K V W1 H1 (T1 + T2) (fun (t : T1 + T2) => match t with | inl t0 => x t0 | inr t0 => y t0 end) -> BasisSubspaceVS K V W2 H2 (T1 + T3) (fun (t : T1 + T3) => match t with | inl t0 => x t0 | inr t0 => z t0 end) -> BasisSubspaceVS K V (SumEnsembleVS K V W1 W2) H4 (T1 + T2 + T3) (fun (t : T1 + T2 + T3) => match t with | inl t0 => (match t0 with | inl t1 => x t1 | inr t1 => y t1 end) | inr t0 => z t0 end).
Proof.
move=> K V W1 W2 H1 H2.
suff: (SubspaceVS K V (Intersection (VT K V) W1 W2)).
move=> H3.
suff: (SubspaceVS K V (SumEnsembleVS K V W1 W2)).
move=> H4.
exists H3.
exists H4.
apply (Corollary_4_10 K V W1 W2 H1 H2 H3 H4).
apply (SumSubspaceVS K V W1 W2 H1 H2).
apply (IntersectionSubspaceVS K V W1 W2 H1 H2).
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

Lemma SumEnsembleBasisVS_exists : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2), exists (H3 : SubspaceVS K V (SumEnsembleVS K V W1 W2)), forall (T1 T2 : Type) (x : T1 -> VT K V) (y : T2 -> VT K V), (Intersection (VT K V) W1 W2) = (Singleton (VT K V) (VO K V)) -> BasisSubspaceVS K V W1 H1 T1 x -> BasisSubspaceVS K V W2 H2 T2 y -> BasisSubspaceVS K V (SumEnsembleVS K V W1 W2) H3 (T1 + T2) (fun (t : T1 + T2) => match t with | inl t0 => x t0 | inr t0 => y t0 end).
Proof.
move=> K V W1 W2 H1 H2.
suff: (SubspaceVS K V (SumEnsembleVS K V W1 W2)).
move=> H3.
exists H3.
apply (SumEnsembleBasisVS K V W1 W2 H1 H2 H3).
apply (SumSubspaceVS K V W1 W2 H1 H2).
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

Lemma Formula_P23_exists : forall (K : Field) (V : VectorSpace K) (N : nat) (F : {n : nat | n < N} -> VT K V), exists (H : forall (t : (forall (m : {n : nat | n < N}), {v : VT K V | exists (f : FT K), v = Vmul K V f (F m)})), In (VT K V) (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun (m : {n : nat | n < N}) => proj1_sig (t m)))), BasisVS K V {n : nat | n < N} F <-> ((Bijective (DirectProdVST K {n : nat | n < N} (fun (m : {n : nat | n < N}) => SubspaceMakeVS K V (fun (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m)) (SingleSubspaceVS K V (F m)))) {w : VT K V | SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m)) w} (fun (t : forall (m : {n : nat | n < N}), {v : VT K V | exists (f : FT K), v = Vmul K V f (F m)}) => exist (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun (m : {n : nat | n < N}) => proj1_sig (t m))) (H t))) /\ (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m)) = Full_set (VT K V)) /\ forall (m : {n : nat | n < N}), (F m) <> VO K V).
Proof.
move=> K V N F.
suff: (forall (t : forall m : {n : nat | n < N}, {v : VT K V | exists f : FT K, v = Vmul K V f (F m)}), In (VT K V) (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun m : {n : nat | n < N} => proj1_sig (t m)))).
move=> H1.
exists H1.
apply (Formula_P23 K V N F H1).
move=> t.
rewrite (FiniteSumTEnsembleVS K V N (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))).
exists (fun (m : {n : nat | n < N}) => proj1_sig (t m)).
apply conj.
move=> m.
apply (proj2_sig (t m)).
reflexivity.
Qed.

Definition LinearlyIndependentVS (K : Field) (V : VectorSpace K) (T : Type) (F : T -> VT K V) := BasisVS K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F)) T (fun (t : T) => exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t)).

Lemma BijectiveSaveLinearlyIndependentVS : forall (K : Field) (V : VectorSpace K) (T1 T2 : Type) (F : T1 -> T2) (G : T2 -> VT K V), Bijective T1 T2 F -> LinearlyIndependentVS K V T2 G -> LinearlyIndependentVS K V T1 (compose G F).
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

Lemma IsomorphicSaveLinearlyIndependentVS : forall (K : Field) (V1 V2 : VectorSpace K) (T : Type) (F : T -> VT K V1) (G : VT K V1 -> VT K V2), IsomorphicVS K V1 V2 G -> LinearlyIndependentVS K V1 T F -> LinearlyIndependentVS K V2 T (compose G F).
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

Lemma LinearlyIndependentVSDef2 : forall (K : Field) (V : VectorSpace K) (T : Type) (F : T -> VT K V), LinearlyIndependentVS K V T F <-> (forall (a : DirectSumField K T), MySumF2 T (exist (Finite T) (fun t : T => proj1_sig a t <> FO K) (proj2_sig a)) (VSPCM K V) (fun (t : T) => Vmul K V (proj1_sig a t) (F t)) = VO K V -> forall (t : T), proj1_sig a t = FO K).
Proof.
move=> K V T F.
apply conj.
move=> H1 a H2.
suff: (Finite T (fun (t : T) => FO K <> FO K)).
move=> H3.
suff: (a = exist (fun (G : T -> FT K) => Finite T (fun (t : T) => G t <> FO K)) (fun (t : T) => FO K) H3).
move=> H4 t.
rewrite H4.
reflexivity.
apply (BijInj (DirectSumField K T) (VT K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F))) (fun (g : DirectSumField K T) => MySumF2 T (exist (Finite T) (fun t : T => proj1_sig g t <> FO K) (proj2_sig g)) (VSPCM K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F))) (fun t : T => Vmul K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F)) (proj1_sig g t) (exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t)))) H1).
simpl.
apply sig_map.
rewrite (MySumF2O T (exist (Finite T) (fun _ : T => FO K <> FO K) H3)).
simpl.
suff: (proj1_sig (MySumF2 T (exist (Finite T) (fun t : T => proj1_sig a t <> FO K) (proj2_sig a)) (VSPCM K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F))) (fun t : T => SubspaceMakeVSVmul K V (SpanVS K V T F) (SpanSubspaceVS K V T F) (proj1_sig a t) (exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t)))) = MySumF2 T (exist (Finite T) (fun t : T => proj1_sig a t <> FO K) (proj2_sig a)) (VSPCM K V) (fun t : T => Vmul K V (proj1_sig a t) (F t))).
move=> H4.
rewrite H4.
rewrite H2.
reflexivity.
apply (FiniteSetInduction T (exist (Finite T) (fun t : T => proj1_sig a t <> FO K) (proj2_sig a))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite - H7.
reflexivity.
apply H6.
apply H6.
move=> u H4.
apply False_ind.
apply H4.
reflexivity.
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
move=> H1.
apply InjSurjBij.
move=> g1 g2 H2.
suff: (forall (t : T), Fadd K (proj1_sig g1 t) (Fopp K (proj1_sig g2 t)) = FO K).
move=> H3.
apply sig_map.
apply functional_extensionality.
move=> t.
apply (Fminus_diag_uniq K (proj1_sig g1 t) (proj1_sig g2 t) (H3 t)).
suff: (Finite T (fun (t : T) => Fadd K (proj1_sig g1 t) (Fopp K (proj1_sig g2 t)) <> FO K)).
move=> H3.
apply (H1 (exist (fun (G : T -> FT K) => Finite T (fun (t : T) => G t <> FO K)) (fun (t : T) => Fadd K (proj1_sig g1 t) (Fopp K (proj1_sig g2 t))) H3)).
simpl.
suff: (MySumF2 T (exist (Finite T) (fun t : T => Fadd K (proj1_sig g1 t) (Fopp K (proj1_sig g2 t)) <> FO K) H3) (VSPCM K V) (fun t : T => Vmul K V (Fadd K (proj1_sig g1 t) (Fopp K (proj1_sig g2 t))) (F t)) = Vadd K V (proj1_sig (MySumF2 T (exist (Finite T) (fun t : T => proj1_sig g1 t <> FO K) (proj2_sig g1)) (VSPCM K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F))) (fun t : T => Vmul K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F)) (proj1_sig g1 t) (exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t))))) (Vopp K V (proj1_sig (MySumF2 T (exist (Finite T) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g2)) (VSPCM K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F))) (fun t : T => Vmul K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F)) (proj1_sig g2 t) (exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t))))))).
move=> H4.
rewrite H4.
rewrite H2.
apply (Vadd_opp_r K V).
suff: (MySumF2 T (exist (Finite T) (fun t : T => Fadd K (proj1_sig g1 t) (Fopp K (proj1_sig g2 t)) <> FO K) H3) (VSPCM K V) (fun t : T => Vmul K V (Fadd K (proj1_sig g1 t) (Fopp K (proj1_sig g2 t))) (F t)) = MySumF2 T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig g1 t <> FO K) (proj2_sig g1)) (exist (Finite T) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g2))) (VSPCM K V) (fun t : T => Vmul K V (Fadd K (proj1_sig g1 t) (Fopp K (proj1_sig g2 t))) (F t))).
move=> H4.
rewrite H4.
suff: ((MySumF2 T (exist (Finite T) (fun t : T => proj1_sig g1 t <> FO K) (proj2_sig g1)) (VSPCM K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F))) (fun t : T => Vmul K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F)) (proj1_sig g1 t) (exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t)))) = (MySumF2 T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig g1 t <> FO K) (proj2_sig g1)) (exist (Finite T) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g2))) (VSPCM K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F))) (fun t : T => Vmul K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F)) (proj1_sig g1 t) (exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t))))).
move=> H5.
rewrite H5.
suff: ((MySumF2 T (exist (Finite T) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g2)) (VSPCM K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F))) (fun t : T => Vmul K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F)) (proj1_sig g2 t) (exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t)))) = (MySumF2 T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig g1 t <> FO K) (proj2_sig g1)) (exist (Finite T) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g2))) (VSPCM K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F))) (fun t : T => Vmul K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F)) (proj1_sig g2 t) (exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t))))).
move=> H6.
rewrite H6.
apply (FiniteSetInduction T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig g1 t <> FO K) (proj2_sig g1)) (exist (Finite T) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g2)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite (Vadd_opp_r K V).
reflexivity.
move=> B b H7 H8 H9 H10.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H10.
simpl.
rewrite (Vadd_assoc K V (proj1_sig (MySumF2 T B (VSPCM K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F))) (fun t : T => SubspaceMakeVSVmul K V (SpanVS K V T F) (SpanSubspaceVS K V T F) (proj1_sig g1 t) (exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t))))) (Vmul K V (proj1_sig g1 b) (F b))).
rewrite (Vopp_add_distr K V).
rewrite - (Vadd_assoc K V (Vmul K V (proj1_sig g1 b) (F b)) (Vopp K V (proj1_sig (MySumF2 T B (VSPCM K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F))) (fun t : T => SubspaceMakeVSVmul K V (SpanVS K V T F) (SpanSubspaceVS K V T F) (proj1_sig g2 t) (exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t))))))).
rewrite (Vadd_comm K V (Vmul K V (proj1_sig g1 b) (F b))).
rewrite (Vadd_assoc K V (Vopp K V (proj1_sig (MySumF2 T B (VSPCM K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F))) (fun t : T => SubspaceMakeVSVmul K V (SpanVS K V T F) (SpanSubspaceVS K V T F) (proj1_sig g2 t) (exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t))))))).
rewrite - (Vadd_assoc K V (proj1_sig (MySumF2 T B (VSPCM K (SubspaceMakeVS K V (SpanVS K V T F) (SpanSubspaceVS K V T F))) (fun t : T => SubspaceMakeVSVmul K V (SpanVS K V T F) (SpanSubspaceVS K V T F) (proj1_sig g1 t) (exist (SpanVS K V T F) (F t) (SpanContainSelfVS K V T F t)))))).
rewrite (Vmul_add_distr_r K V).
rewrite (Vopp_mul_distr_l K V).
reflexivity.
apply H9.
apply H9.
apply H9.
rewrite (MySumF2Included T (exist (Finite T) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g2)) (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig g1 t <> FO K) (proj2_sig g1)) (exist (Finite T) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g2)))).
rewrite (MySumF2O T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig g1 t <> FO K) (proj2_sig g1)) (exist (Finite T) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g2))) (Complement T (proj1_sig (exist (Finite T) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g2)))))).
apply sig_map.
simpl.
rewrite (Vadd_O_r K).
reflexivity.
move=> u.
elim.
move=> u0 H6 H7.
apply sig_map.
simpl.
suff: ((proj1_sig g2 u0) = FO K).
move=> H8.
rewrite H8.
apply (Vmul_O_l K V (F u0)).
apply NNPP.
apply H6.
move=> t H6.
right.
apply H6.
rewrite (MySumF2Included T (exist (Finite T) (fun t : T => proj1_sig g1 t <> FO K) (proj2_sig g1)) (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig g1 t <> FO K) (proj2_sig g1)) (exist (Finite T) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g2)))).
rewrite (MySumF2O T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig g1 t <> FO K) (proj2_sig g1)) (exist (Finite T) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g2))) (Complement T (proj1_sig (exist (Finite T) (fun t : T => proj1_sig g1 t <> FO K) (proj2_sig g1)))))).
apply sig_map.
simpl.
rewrite (Vadd_O_r K).
reflexivity.
move=> u.
elim.
move=> u0 H5 H6.
apply sig_map.
simpl.
suff: ((proj1_sig g1 u0) = FO K).
move=> H7.
rewrite H7.
apply (Vmul_O_l K V (F u0)).
apply NNPP.
apply H5.
move=> t H5.
left.
apply H5.
rewrite (MySumF2Included T (exist (Finite T) (fun t : T => Fadd K (proj1_sig g1 t) (Fopp K (proj1_sig g2 t)) <> FO K) H3) (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig g1 t <> FO K) (proj2_sig g1)) (exist (Finite T) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g2)))).
rewrite (MySumF2O T (FiniteIntersection T (FiniteUnion T (exist (Finite T) (fun t : T => proj1_sig g1 t <> FO K) (proj2_sig g1)) (exist (Finite T) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g2))) (Complement T (proj1_sig (exist (Finite T) (fun t : T => Fadd K (proj1_sig g1 t) (Fopp K (proj1_sig g2 t)) <> FO K) H3))))).
simpl.
rewrite (Vadd_O_r K).
reflexivity.
move=> u.
elim.
move=> u0 H4 H5.
simpl.
suff: ((Fadd K (proj1_sig g1 u0) (Fopp K (proj1_sig g2 u0))) = FO K).
move=> H6.
rewrite H6.
apply (Vmul_O_l K V (F u0)).
apply NNPP.
apply H4.
move=> t H4.
apply NNPP.
move=> H5.
apply H4.
suff: ((proj1_sig g1 t) = FO K).
move=> H6.
suff: ((proj1_sig g2 t) = FO K).
move=> H7.
rewrite H6.
rewrite H7.
apply (Fadd_opp_r K).
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
apply (Finite_downward_closed T (Union T (fun t : T => proj1_sig g1 t <> FO K) (fun t : T => proj1_sig g2 t <> FO K))).
apply (Union_preserves_Finite T (fun t : T => proj1_sig g1 t <> FO K) (fun t : T => proj1_sig g2 t <> FO K) (proj2_sig g1) (proj2_sig g2)).
move=> t H3.
apply NNPP.
move=> H4.
apply H3.
suff: ((proj1_sig g1 t) = FO K).
move=> H5.
suff: ((proj1_sig g2 t) = FO K).
move=> H6.
rewrite H5.
rewrite H6.
apply (Fadd_opp_r K).
apply NNPP.
move=> H6.
apply H4.
right.
apply H6.
apply NNPP.
move=> H5.
apply H4.
left.
apply H5.
move=> v.
elim (proj2_sig v).
move=> x H2.
exists x.
apply sig_map.
rewrite H2.
apply (FiniteSetInduction T (exist (Finite T) (fun t : T => proj1_sig x t <> FO K) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H3 H4 H5 H6.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite - H6.
reflexivity.
apply H5.
apply H5.
Qed.

Lemma LinearlyIndependentVSDef3 : forall (K : Field) (V : VectorSpace K) (T : Type) (F : T -> VT K V), LinearlyIndependentVS K V T F <-> (forall (a : T -> FT K) (A : {X : Ensemble T | Finite T X}), MySumF2 T A (VSPCM K V) (fun (t : T) => Vmul K V (a t) (F t)) = VO K V -> forall (t : T), In T (proj1_sig A) t -> a t = FO K).
Proof.
move=> K V T F.
apply conj.
move=> H1 a A H2.
suff: (forall (t : T), match excluded_middle_informative ((proj1_sig A) t) with 
  | left _ => a t
  | right _ => FO K
end = FO K).
move=> H3 t H4.
rewrite - (H3 t).
elim (excluded_middle_informative (proj1_sig A t)).
move=> H5.
reflexivity.
move=> H5.
apply False_ind.
apply (H5 H4).
suff: (Finite T (fun (t : T) => (match excluded_middle_informative (proj1_sig A t) with 
  | left _ => a t 
  | right _ => FO K
end) <> FO K)).
move=> H3.
apply (proj1 (LinearlyIndependentVSDef2 K V T F) H1 (exist (fun (G : T -> FT K) => Finite T (fun (t : T) => G t <> FO K)) (fun (t : T) => (match excluded_middle_informative (proj1_sig A t) with 
  | left _ => a t 
  | right _ => FO K
end)) H3)).
simpl.
rewrite - H2.
rewrite (MySumF2Included T (exist (Finite T) (fun t : T => (match excluded_middle_informative (proj1_sig A t) with
  | left _=> a t 
  | right _ => FO K
end) <> FO K) H3) A).
rewrite (MySumF2O T (FiniteIntersection T A (Complement T (proj1_sig (exist (Finite T) (fun t : T => (match excluded_middle_informative (proj1_sig A t) with
  | left _ => a t
  | right _ => FO K
end) <> FO K) H3))))).
rewrite (CM_O_r (VSPCM K V)).
apply (MySumF2Same T (exist (Finite T) (fun t : T => (match excluded_middle_informative (proj1_sig A t) with
  | left _=> a t 
  | right _ => FO K
end) <> FO K) H3) (VSPCM K V)).
move=> u.
simpl.
elim (excluded_middle_informative (proj1_sig A u)).
move=> H4 H5.
reflexivity.
move=> H4 H5.
apply False_ind.
apply H5.
reflexivity.
move=> u.
elim.
move=> u0 H4 H5.
suff: (a u0 = FO K).
move=> H6.
rewrite H6.
apply (Vmul_O_l K V).
apply NNPP.
move=> H6.
apply H4.
unfold In.
simpl.
elim (excluded_middle_informative (proj1_sig A u0)).
move=> H7.
apply H6.
move=> H7.
apply False_ind.
apply (H7 H5).
move=> t.
simpl.
unfold In.
elim (excluded_middle_informative (proj1_sig A t)).
move=> H4 H5.
apply H4.
move=> H4 H5.
apply False_ind.
apply H5.
reflexivity.
apply (Finite_downward_closed T (proj1_sig A) (proj2_sig A)).
move=> t.
unfold In.
elim (excluded_middle_informative (proj1_sig A t)).
move=> H3 H4.
apply H3.
move=> H3 H4.
apply False_ind.
apply H4.
reflexivity.
move=> H1.
apply (proj2 (LinearlyIndependentVSDef2 K V T F)).
move=> a H2 t.
elim (classic (proj1_sig a t = FO K)).
apply.
apply (H1 (proj1_sig a) (exist (Finite T) (fun t : T => proj1_sig a t <> FO K) (proj2_sig a)) H2).
Qed.

Lemma InjectiveSaveLinearlyIndependentVS : forall (K : Field) (V : VectorSpace K) (T1 T2 : Type) (F : T1 -> T2) (G : T2 -> VT K V), Injective T1 T2 F -> LinearlyIndependentVS K V T2 G -> LinearlyIndependentVS K V T1 (compose G F).
Proof.
move=> K V T1 T2 F G H1 H2.
apply (proj2 (LinearlyIndependentVSDef3 K V T1 (fun t : T1 => G (F t)))).
move=> a A H3.
suff: (forall (t2 : T2), (exists (t1 : T1), t2 = F t1) -> {t1 : T1 | F t1 = t2}).
move=> H4.
suff: (Finite T2 (fun (t2 : T2) => exists (t1 : T1), t2 = F t1 /\ In T1 (proj1_sig A) t1)).
move=> H5.
suff: (forall (t : T2), In T2 (fun (t2 : T2) => exists (t1 : T1), t2 = F t1 /\ In T1 (proj1_sig A) t1) t -> match excluded_middle_informative (exists (t1 : T1), t = F t1) with
  | left H => a (proj1_sig (H4 t H))
  | right _ => FO K
end = FO K).
move=> H6 t H7.
rewrite - (H6 (F t)).
elim (excluded_middle_informative (exists (t1 : T1), F t = F t1)).
move=> H8.
suff: ((proj1_sig (H4 (F t) H8)) = t).
move=> H9.
rewrite H9.
reflexivity.
apply H1.
apply (proj2_sig (H4 (F t) H8)).
move=> H8.
apply False_ind.
apply H8.
exists t.
reflexivity.
exists t.
apply conj.
reflexivity.
apply H7.
apply (proj1 (LinearlyIndependentVSDef3 K V T2 G) H2 (fun (t2 : T2) => match excluded_middle_informative (exists (t1 : T1), t2 = F t1) with
  | left H => (a (proj1_sig (H4 t2 H)))
  | right _ => FO K
end) (exist (Finite T2) (fun (t2 : T2) => exists (t1 : T1), t2 = F t1 /\ In T1 (proj1_sig A) t1) H5)).
rewrite - H3.
rewrite - (MySumF2BijectiveSame T1 A T2 (exist (Finite T2) (fun t2 : T2 => exists t1 : T1, t2 = F t1 /\ In T1 (proj1_sig A) t1) H5) (VSPCM K V) (fun (t : T2) => Vmul K V match excluded_middle_informative (exists t1 : T1, t = F t1) with
  | left H => a (proj1_sig (H4 t H))
  | right _ => FO K
end (G t)) F).
suff: ((fun u : T1 => Vmul K V match excluded_middle_informative (exists t1 : T1, F u = F t1) with
  | left H => a (proj1_sig (H4 (F u) H))
  | right _ => FO K
end (G (F u))) = (fun t : T1 => Vmul K V (a t) (G (F t)))).
move=> H6.
rewrite H6.
reflexivity.
apply functional_extensionality.
move=> u.
elim (excluded_middle_informative (exists t1 : T1, F u = F t1)).
move=> H6.
suff: ((proj1_sig (H4 (F u) H6)) = u).
move=> H7.
rewrite H7.
reflexivity.
apply H1.
apply (proj2_sig (H4 (F u) H6)).
move=> H6.
apply False_ind.
apply H6.
exists u.
reflexivity.
move=> u H6.
exists u.
apply conj.
reflexivity.
apply H6.
move=> H6.
simpl.
apply InjSurjBij.
move=> u1 u2 H7.
apply sig_map.
apply H1.
suff: (F (proj1_sig u1) = proj1_sig (exist (fun t2 : T2 => exists t1 : T1, t2 = F t1 /\ In T1 (proj1_sig A) t1) (F (proj1_sig u1)) (H6 (proj1_sig u1) (proj2_sig u1)))).
move=> H8.
rewrite H8.
rewrite H7.
reflexivity.
reflexivity.
elim.
move=> u H7.
elim H7.
move=> t H8.
exists (exist (proj1_sig A) t (proj2 H8)).
apply sig_map.
simpl.
rewrite(proj1 H8).
reflexivity.
suff: ((fun t2 : T2 => exists t1 : T1, t2 = F t1 /\ In T1 (proj1_sig A) t1) = Im T1 T2 (proj1_sig A) F).
move=> H5.
rewrite H5.
apply (finite_image T1 T2 (proj1_sig A) F (proj2_sig A)).
apply Extensionality_Ensembles.
apply conj.
move=> t2.
elim.
move=> t1 H5.
apply (Im_intro T1 T2 (proj1_sig A) F t1 (proj2 H5)).
apply (proj1 H5).
move=> t2.
elim.
move=> t1 H5 y H6.
exists t1.
apply conj.
apply H6.
apply H5.
move=> t2 H4.
apply (constructive_definite_description (fun (t1 : T1) => F t1 = t2)).
apply (proj1 (unique_existence (fun (t1 : T1) => F t1 = t2))).
apply conj.
elim H4.
move=> t1 H5.
exists t1.
rewrite H5.
reflexivity.
move=> x1 x2 H5 H6.
apply H1.
rewrite H6.
apply H5.
Qed.

Lemma InjectiveSaveLinearlyIndependentVS2 : forall (K : Field) (V1 V2 : VectorSpace K) (T : Type) (F : T -> VT K V1) (G : VT K V1 -> VT K V2), (Injective (VT K V1) (VT K V2) G /\ (forall (x y : VT K V1), G (Vadd K V1 x y) = Vadd K V2 (G x) (G y)) /\ (forall (c : FT K) (x : VT K V1), G (Vmul K V1 c x) = Vmul K V2 c (G x))) -> LinearlyIndependentVS K V1 T F -> LinearlyIndependentVS K V2 T (compose G F).
Proof.
move=> K V1 V2 T F G H1 H2.
apply (proj2 (LinearlyIndependentVSDef3 K V2 T (fun t : T => G (F t)))).
move=> a A H3.
apply (proj1 (LinearlyIndependentVSDef3 K V1 T F) H2 a A).
apply (proj1 H1).
rewrite - (Vmul_O_l K V1 (VO K V1)).
rewrite (proj2 (proj2 H1) (FO K) (VO K V1)).
rewrite (Vmul_O_l K V2 (G (VO K V1))).
rewrite - H3.
apply (FiniteSetInduction T A).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite - (Vmul_O_l K V1 (VO K V1)).
rewrite (proj2 (proj2 H1) (FO K) (VO K V1)).
apply (Vmul_O_l K V2 (G (VO K V1))).
move=> B b H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite (proj1 (proj2 H1)).
rewrite (proj2 (proj2 H1) (a b) (F b)).
rewrite H7.
reflexivity.
apply H6.
apply H6.
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

Lemma BasisLIGeVS : forall (K : Field) (V : VectorSpace K) (T : Type) (F : T -> VT K V), BasisVS K V T F <-> (LinearlyIndependentVS K V T F /\ GeneratingSystemVS K V T F).
Proof.
move=> K V T F.
apply conj.
move=> H1.
suff: (GeneratingSystemVS K V T F).
move=> H2.
apply conj.
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
apply H2.
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
rewrite (proj2 H1).
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
apply (proj1 H1).
apply functional_extensionality.
move=> t.
reflexivity.
Qed.

Lemma SubspaceBasisLinearlyIndependentVS : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) (T : Type) (F : T -> VT K V), BasisSubspaceVS K V W H T F -> LinearlyIndependentVS K V T F.
Proof.
move=> K V W H1 T F.
elim.
move=> H2 H3.
apply (InjectiveSaveLinearlyIndependentVS2 K (SubspaceMakeVS K V W H1) V T (fun (t : T) => exist W (F t) (H2 t)) (fun (v : {w : VT K V | In (VT K V) W w}) => proj1_sig v)).
apply conj.
move=> v1 v2.
apply sig_map.
apply conj.
move=> v1 v2.
reflexivity.
move=> c v.
reflexivity.
apply (proj1 (proj1 (BasisLIGeVS K (SubspaceMakeVS K V W H1) T (fun t : T => exist W (F t) (H2 t))) H3)).
Qed.

Lemma LinearlyIndependentNotContainVOVS : forall (K : Field) (V : VectorSpace K) (T : Type) (F : T -> VT K V), LinearlyIndependentVS K V T F -> forall (t : T), (F t) <> VO K V.
Proof.
move=> K V T F H1 t H2.
suff: (MySumF2 T (FiniteSingleton T t) (VSPCM K V) (fun t : T => Vmul K V (FI K) (F t)) = VO K V).
move=> H3.
apply (FI_neq_FO K).
apply (proj1 (LinearlyIndependentVSDef3 K V T F) H1 (fun (t0 : T) => FI K) (FiniteSingleton T t) H3 t).
apply (In_singleton T t).
rewrite MySumF2Singleton.
rewrite H2.
apply (Vmul_O_r K V (FI K)).
Qed.

Lemma Formula_P25 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : {n : nat | n < N} -> VT K V) (H : forall (t : (forall (m : {n : nat | n < N}), {v : VT K V | exists (f : FT K), v = Vmul K V f (F m)})), In (VT K V) (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun (m : {n : nat | n < N}) => proj1_sig (t m)))), LinearlyIndependentVS K V {n : nat | n < N} F <-> ((Bijective (DirectProdVST K {n : nat | n < N} (fun (m : {n : nat | n < N}) => SubspaceMakeVS K V (fun (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m)) (SingleSubspaceVS K V (F m)))) {w : VT K V | SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m)) w} (fun (t : forall (m : {n : nat | n < N}), {v : VT K V | exists (f : FT K), v = Vmul K V f (F m)}) => exist (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun (m : {n : nat | n < N}) => proj1_sig (t m))) (H t))) /\ forall (m : {n : nat | n < N}), (F m) <> VO K V).
Proof.
move=> K V N F H1.
elim (Formula_P23_exists K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) N (fun t : {n : nat | n < N} => exist (SpanVS K V {n : nat | n < N} F) (F t) (SpanContainSelfVS K V {n : nat | n < N} F t))).
move=> H2 H3.
suff: (Bijective (DirectProdVST K {n : nat | n < N} (fun m : {n : nat | n < N} => SubspaceMakeVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (fun v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) (SingleSubspaceVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))))) {w : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) | SumTEnsembleVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) w} (fun t : forall m : {n : nat | n < N}, {v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) | exists f : FT K,  v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))} => exist (SumTEnsembleVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m)))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) (fun m : {n : nat | n < N} => proj1_sig (t m))) (H2 t)) <-> Bijective (DirectProdVST K {n : nat | n < N} (fun m : {n : nat | n < N} => SubspaceMakeVS K V (fun v : VT K V => exists f : FT K, v = Vmul K V f (F m)) (SingleSubspaceVS K V (F m)))) {w : VT K V | SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m)) w} (fun t : forall m : {n : nat | n < N}, {v : VT K V | exists f : FT K, v = Vmul K V f (F m)} => exist (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun m : {n : nat | n < N} => proj1_sig (t m))) (H1 t))).
move=> H4.
apply conj.
move=> H5.
apply conj.
apply (proj1 H4).
apply (proj1 H3).
apply H5.
move=> m H6.
apply (proj2 (proj2 (proj1 H3 H5)) m).
apply sig_map.
apply H6.
move=> H5.
apply (proj2 H3).
apply conj.
apply (proj2 H4).
apply (proj1 H5).
apply conj.
apply Extensionality_Ensembles.
apply conj.
move=> x H6.
apply Full_intro.
move=> x H6.
elim (proj2_sig x).
move=> f H7.
suff: (forall (t : {n : nat | n < N}), In (VT K V) (SpanVS K V {n : nat | n < N} F) (Vmul K V (proj1_sig f t) (F t))).
move=> H8.
suff: (forall (t : {n : nat | n < N}), exists f0 : FT K, (exist (SpanVS K V {n : nat | n < N} F) (Vmul K V (proj1_sig f t) (F t)) (H8 t)) = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f0 (exist (SpanVS K V {n : nat | n < N} F) (F t) (SpanContainSelfVS K V {n : nat | n < N} F t))).
move=> H9.
suff: (Finite {n : nat | n < N} (fun (t : {n : nat | n < N}) => (exist (SpanVS K V {n : nat | n < N} F) (Vmul K V (proj1_sig f t) (F t)) (H8 t)) <> (VO K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))))).
move=> H10. 
suff: (x = (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => exist (SpanVS K V {n : nat | n < N} F) (Vmul K V (proj1_sig f t) (F t)) (H8 t) <> VO K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) H10) (VSPCM K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) (fun t : {n : nat | n < N} => exist (SpanVS K V {n : nat | n < N} F) (Vmul K V (proj1_sig f t) (F t)) (H8 t)))).
move=> H11.
rewrite H11.
apply (SumTEnsembleVS_intro K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f0 : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f0 (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) (fun (t : {n : nat | n < N}) => (exist (SpanVS K V {n : nat | n < N} F) (Vmul K V (proj1_sig f t) (F t)) (H8 t))) H10).
move=> t.
exists (proj1_sig f t).
apply sig_map.
reflexivity.
apply sig_map.
rewrite H7.
rewrite (MySumF2Included {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => exist (SpanVS K V {n : nat | n < N} F) (Vmul K V (proj1_sig f t) (F t)) (H8 t) <> VO K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) H10) (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => proj1_sig f t <> FO K) (proj2_sig f))).
rewrite (MySumF2O {n : nat | n < N} (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => proj1_sig f t <> FO K) (proj2_sig f)) (Complement {n : nat | n < N} (proj1_sig (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => exist (SpanVS K V {n : nat | n < N} F) (Vmul K V (proj1_sig f t) (F t)) (H8 t) <> VO K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) H10))))).
simpl.
rewrite (Vadd_O_r K V).
apply (FiniteSetInduction {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => exist (SpanVS K V {n : nat | n < N} F) (Vmul K V (proj1_sig f t) (F t)) (H8 t) <> SubspaceMakeVSVO K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) H10)).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H11 H12 H13 H14.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H14.
reflexivity.
apply H13.
apply H13.
move=> u H11.
elim H11.
move=> u0 H12 H13.
apply NNPP.
move=> H14.
apply H12.
move=> H15.
apply H14.
suff: ((Vmul K V (proj1_sig f u0) (F u0)) = (proj1_sig (exist (SpanVS K V {n : nat | n < N} F) (Vmul K V (proj1_sig f u0) (F u0)) (H8 u0)))).
move=> H16.
rewrite H16.
rewrite H15.
reflexivity.
reflexivity.
move=> m H11 H12.
apply H11.
apply sig_map.
simpl.
rewrite H12.
apply (Vmul_O_l K V).
apply (Finite_downward_closed {n : nat | n < N} (Full_set {n : nat | n < N}) (CountFinite N)).
move=> m H10.
apply (Full_intro {n : nat | n < N} m).
move=> t.
exists (proj1_sig f t).
apply sig_map.
reflexivity.
move=> t.
apply (proj1 (proj2 (SpanSubspaceVS K V {n : nat | n < N} F))).
apply (SpanContainSelfVS K V {n : nat | n < N} F).
move=> m H6.
apply (proj2 H5 m).
suff: (F m = proj1_sig (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))).
move=> H7.
rewrite H7.
rewrite H6.
reflexivity.
reflexivity.
suff: (exists (g : (DirectProdVST K {n : nat | n < N} (fun m : {n : nat | n < N} => SubspaceMakeVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (fun v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) (SingleSubspaceVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))))) -> (DirectProdVST K {n : nat | n < N} (fun m : {n : nat | n < N} => SubspaceMakeVS K V (fun v : VT K V => exists f : FT K, v = Vmul K V f (F m)) (SingleSubspaceVS K V (F m))))) (h : {w : VT K V | SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m)) w} -> {w : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) | SumTEnsembleVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) w}), Bijective (DirectProdVST K {n : nat | n < N} (fun m : {n : nat | n < N} => SubspaceMakeVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (fun v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) (SingleSubspaceVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))))) (DirectProdVST K {n : nat | n < N} (fun m : {n : nat | n < N} => SubspaceMakeVS K V (fun v : VT K V => exists f : FT K, v = Vmul K V f (F m)) (SingleSubspaceVS K V (F m)))) g /\ Bijective {w : VT K V | SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m)) w} {w : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) | SumTEnsembleVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F)  (SpanSubspaceVS K V {n : nat | n < N} F)) {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) w} h /\ ((fun t : forall m : {n : nat | n < N}, {v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) | exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))} => exist (SumTEnsembleVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f : FT K,  v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m)))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) (fun m : {n : nat | n < N} => proj1_sig (t m))) (H2 t)) = compose (compose h (fun t : forall m : {n : nat | n < N}, {v : VT K V | exists f : FT K, v = Vmul K V f (F m)} => exist (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun m : {n : nat | n < N} => proj1_sig (t m))) (H1 t))) g)).
elim.
move=> g.
elim.
move=> h H5.
apply conj.
move=> H6.
elim (proj1 H5).
move=> ginv H7.
elim (proj1 (proj2 H5)).
move=> hinv H8.
suff: ((fun t : forall m : {n : nat | n < N}, {v : VT K V | exists f : FT K, v = Vmul K V f (F m)} => exist (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun m : {n : nat | n < N} => proj1_sig (t m))) (H1 t)) = (compose hinv (compose (fun t : forall m : {n : nat | n < N}, {v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) | exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))} => exist (SumTEnsembleVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m)))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) (fun m : {n : nat | n < N} => proj1_sig (t m))) (H2 t)) ginv))).
move=> H9.
rewrite H9.
apply BijChain.
apply BijChain.
exists g.
apply conj.
move=> x.
apply (proj2 H7 x).
move=> y.
apply (proj1 H7 y).
apply H6.
exists h.
apply conj.
move=> x.
apply (proj2 H8 x).
move=> y.
apply (proj1 H8 y).
rewrite (proj2 (proj2 H5)).
apply functional_extensionality.
move=> x.
unfold compose.
rewrite (proj2 H7).
rewrite (proj1 H8).
reflexivity.
move=> H6.
rewrite (proj2 (proj2 H5)).
apply BijChain.
apply (proj1 H5).
apply BijChain.
apply H6.
apply (proj1 (proj2 H5)).
suff: (forall (m : {n : nat | n < N}), {gm : (VT K (SubspaceMakeVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (fun v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) (SingleSubspaceVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))))) -> (VT K (SubspaceMakeVS K V (fun v : VT K V => exists f : FT K, v = Vmul K V f (F m)) (SingleSubspaceVS K V (F m)))) | (forall (x : VT K (SubspaceMakeVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (fun v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) (SingleSubspaceVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))))), proj1_sig (proj1_sig x) = proj1_sig (gm x)) /\ Bijective (VT K (SubspaceMakeVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (fun v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) (SingleSubspaceVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))))) (VT K (SubspaceMakeVS K V (fun v : VT K V => exists f : FT K, v = Vmul K V f (F m)) (SingleSubspaceVS K V (F m)))) gm}).
move=> H4.
exists (fun (x : DirectProdVST K {n : nat | n < N} (fun m : {n : nat | n < N} => SubspaceMakeVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (fun v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) (SingleSubspaceVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))))) (m : {n : nat | n < N}) => proj1_sig (H4 m) (x m)).
suff: {h : {w : VT K V | SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m)) w} -> {w : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) | SumTEnsembleVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) w} | (forall (x : {w : VT K V | SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m)) w}), proj1_sig x = proj1_sig (proj1_sig (h x))) /\ Bijective {w : VT K V | SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m)) w} {w : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) | SumTEnsembleVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) w} h}.
move=> H5.
exists (proj1_sig H5).
apply conj.
apply ForallSavesBijective_dep.
move=> m.
apply (proj2 (proj2_sig (H4 m))).
apply conj.
apply (proj2 (proj2_sig H5)).
apply functional_extensionality_dep.
move=> m.
apply sig_map.
apply sig_map.
simpl.
unfold compose.
rewrite - (proj1 (proj2_sig H5)).
simpl.
apply (FiniteSetInduction {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H6 H7 H8 H9.
simpl.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite - H9.
rewrite - (proj1 (proj2_sig (H4 b))).
reflexivity.
apply H8.
apply H8.
suff: ((SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))) = (SpanVS K V {n : nat | n < N} F)).
move=> H5.
suff: (forall (w : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))), SumTEnsembleVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) w).
move=> H6.
exists (compose  (proj1_sig (BijectiveSigFull (VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) (SumTEnsembleVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m)))) H6 )) (proj1_sig (BijectiveSameSig (VT K V) (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))) (SpanVS K V {n : nat | n < N} F) H5)) ).
apply conj.
move=> x.
unfold compose.
rewrite - (proj1 (proj2_sig (BijectiveSigFull (VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) (SumTEnsembleVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m)))) H6))).
apply (proj1 (proj2_sig (BijectiveSameSig (VT K V) (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))) (SpanVS K V {n : nat | n < N} F) H5))).
apply BijChain.
apply (proj2 (proj2_sig (BijectiveSameSig (VT K V) (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))) (SpanVS K V {n : nat | n < N} F) H5))).
apply (proj2 (proj2_sig (BijectiveSigFull (VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) (SumTEnsembleVS K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m)))) H6))).
move=> w.
elim (proj2_sig w).
move=> x H6.
suff: (forall (m : {n : nat | n < N}), In (VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) (fun  (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) (Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (proj1_sig x m) (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) ).
move=> H7.
suff: (Finite {n : nat | n < N} (fun t : {n : nat | n < N} => Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (proj1_sig x t) (exist (SpanVS K V {n : nat | n < N} F) (F t) (SpanContainSelfVS K V {n : nat | n < N} F t)) <> VO K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)))).
move=> H8.
suff: (w = (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => Vmul K  (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (proj1_sig x t) (exist (SpanVS K V {n : nat | n < N} F) (F t) (SpanContainSelfVS K V {n : nat | n < N} F t)) <> VO K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) H8) (VSPCM K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) (fun m : {n : nat | n < N} => Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (proj1_sig x m) (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))))).
move=> H9.
rewrite H9.
apply (SumTEnsembleVS_intro K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) => exists f : FT K, v = Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) (fun (m : {n : nat | n < N}) => (Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (proj1_sig x m) (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) )).
move=> m.
exists (proj1_sig x m).
reflexivity.
apply sig_map.
rewrite H6.
rewrite (MySumF2Included {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (proj1_sig x t) (exist (SpanVS K V {n : nat | n < N} F) (F t) (SpanContainSelfVS K V {n : nat | n < N} F t)) <> VO K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) H8) (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => proj1_sig x t <> FO K) (proj2_sig x))).
rewrite (MySumF2O {n : nat | n < N} (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => proj1_sig x t <> FO K) (proj2_sig x)) (Complement {n : nat | n < N} (proj1_sig (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (proj1_sig x t) (exist (SpanVS K V {n : nat | n < N} F) (F t) (SpanContainSelfVS K V {n : nat | n < N} F t)) <> VO K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) H8))))).
rewrite (CM_O_r (VSPCM K V)).
apply (FiniteSetInduction {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => Vmul K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F)) (proj1_sig x t) (exist (SpanVS K V {n : nat | n < N} F) (F t) (SpanContainSelfVS K V {n : nat | n < N} F t)) <> VO K (SubspaceMakeVS K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F))) H8)).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H9 H10 H11 H12.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H12.
reflexivity.
apply H11.
apply H11.
move=> u.
elim.
move=> m H9 H10.
apply NNPP.
move=> H11.
apply H9.
simpl.
move=> H12.
apply H11.
suff: (Vmul K V (proj1_sig x m) (F m) = (proj1_sig (SubspaceMakeVSVmul K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F) (proj1_sig x m) (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))))).
move=> H13.
rewrite H13.
rewrite H12.
reflexivity.
reflexivity.
move=> m H9 H10.
apply H9.
rewrite H10.
apply (Vmul_O_l K).
apply (Finite_downward_closed {n : nat | n < N} (Full_set {n : nat | n < N}) (CountFinite N)).
move=> m H8.
apply (Full_intro {n : nat | n < N} m).
move=> m.
exists (proj1_sig x m).
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> a H5 H6.
suff: (forall (t : {n : nat | n < N}), {f : FT K | a t = Vmul K V f (F t)}).
move=> H7.
suff: (Finite {n : nat | n < N} (fun (m : {n : nat | n < N}) => proj1_sig (H7 m) <> FO K)).
move=> H8.
exists (exist (fun (G : {n : nat | n < N} -> FT K) => Finite {n : nat | n < N} (fun (t : {n : nat | n < N}) => G t <> FO K)) (fun (m : {n : nat | n < N}) => proj1_sig (H7 m)) H8).
simpl.
suff: (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => a t <> VO K V) H5) (VSPCM K V) a = MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) a).
move=> H9.
rewrite H9.
suff: (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => proj1_sig (H7 t) <> FO K) H8) (VSPCM K V) (fun t : {n : nat | n < N} => Vmul K V (proj1_sig (H7 t)) (F t)) = MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun t : {n : nat | n < N} => Vmul K V (proj1_sig (H7 t)) (F t))).
move=> H10.
rewrite H10.
suff: (a = (fun t : {n : nat | n < N} => Vmul K V (proj1_sig (H7 t)) (F t))).
move=> H11.
rewrite - H11.
reflexivity.
apply functional_extensionality.
move=> m.
apply (proj2_sig (H7 m)).
rewrite (MySumF2Included {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => proj1_sig (H7 t) <> FO K) H8) (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N))).
rewrite (MySumF2O {n : nat | n < N} (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (Complement {n : nat | n < N} (proj1_sig (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => proj1_sig (H7 t) <> FO K) H8))))).
rewrite (CM_O_r (VSPCM K V)).
reflexivity.
move=> u.
elim.
move=> u0 H10 H11.
suff: (proj1_sig (H7 u0) = FO K).
move=> H12.
rewrite H12.
apply (Vmul_O_l K V (F u0)).
apply NNPP.
apply H10.
move=> m H10.
apply (Full_intro {n : nat | n < N} m).
rewrite (MySumF2Included {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => a t <> VO K V) H5) (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N))).
rewrite (MySumF2O {n : nat | n < N} (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (Complement {n : nat | n < N} (proj1_sig (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => a t <> VO K V) H5))))).
rewrite (CM_O_r (VSPCM K V)).
reflexivity.
move=> u.
elim.
move=> u0 H9 H10.
apply NNPP.
apply H9.
move=> m H9.
apply (Full_intro {n : nat | n < N} m).
apply (Finite_downward_closed {n : nat | n < N} (Full_set {n : nat | n < N}) (CountFinite N)).
move=> m H8.
apply (Full_intro {n : nat | n < N} m).
move=> m.
elim (excluded_middle_informative (F m <> VO K V)).
move=> H7.
apply (constructive_definite_description (fun (f : FT K) => a m = Vmul K V f (F m))).
apply (proj1 (unique_existence (fun (f : FT K) => a m = Vmul K V f (F m)))).
apply conj.
elim (H6 m).
move=> f H8.
exists f.
apply H8.
move=> f1 f2 H8 H9.
apply (Vmul_eq_reg_r K V (F m) f1 f2).
rewrite - H8.
apply H9.
apply H7.
move=> H7.
exists (FO K).
elim (H6 m).
move=> f H8.
rewrite H8.
suff: (F m = VO K V).
move=> H9.
rewrite H9.
rewrite (Vmul_O_r K V f).
rewrite (Vmul_O_r K V (FO K)).
reflexivity.
apply NNPP.
apply H7.
suff: (SubspaceVS K V (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m)))).
move=> H5.
suff: (forall (m : {n : nat | n < N}), In (VT K V) (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))) (F m)).
move=> H6 m.
elim.
move=> x H7.
rewrite H7.
apply (MySumF2Induction {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun t : {n : nat | n < N} => proj1_sig x t <> FO K) (proj2_sig x))).
apply conj.
apply (proj2 (proj2 H5)).
move=> B b H8 H9.
apply (proj1 H5 B (Vmul K V (proj1_sig x b) (F b)) H9 (proj1 (proj2 H5) (proj1_sig x b) (F b) (H6 b))).
move=> m.
elim (classic (F m = VO K V)).
move=> H6.
rewrite H6.
apply (proj2 (proj2 H5)).
move=> H6.
suff: (Finite {n : nat | n < N} (fun (k : {n : nat | n < N}) => match excluded_middle_informative (k = m) with
  | left _ => F m 
  | right _ => VO K V
end <> VO K V)).
move=> H7.
suff: (F m = (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (fun (k : {n : nat | n < N}) => match excluded_middle_informative (k = m) with
  | left _ => F m 
  | right _ => VO K V
end <> VO K V) H7) (VSPCM K V) (fun k : {n : nat | n < N} => match excluded_middle_informative (k = m) with
  | left _ => F m 
  | right _ => VO K V
end))).
move=> H8.
rewrite H8.
apply (SumTEnsembleVS_intro K V {n : nat | n < N} (fun (m0 : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m0)) (fun (k : {n : nat | n < N}) => match excluded_middle_informative (k = m) with 
  | left _ => F m
  | right _ => VO K V
end) H7).
move=> k.
elim (excluded_middle_informative (k = m)).
move=> H9.
rewrite H9.
exists (FI K).
rewrite (Vmul_I_l K V (F m)).
reflexivity.
move=> H9.
exists (FO K).
rewrite (Vmul_O_l K V (F k)).
reflexivity.
suff: ((exist (Finite {n : nat | n < N}) (fun k : {n : nat | n < N} => (match excluded_middle_informative (k = m) with
  | left _ => F m 
  | right _ => VO K V
end) <> VO K V) H7) = FiniteSingleton {n : nat | n < N} m).
move=> H8.
rewrite H8.
rewrite MySumF2Singleton.
elim (excluded_middle_informative (m = m)).
move=> H9.
reflexivity.
move=> H9.
apply False_ind.
apply H9.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> k H8.
suff: (k = m).
move=> H9.
rewrite H9.
apply (In_singleton {n : nat | n < N} m).
apply NNPP.
move=> H9.
apply H8.
elim (excluded_middle_informative (k = m)).
move=> H10.
apply False_ind.
apply (H9 H10).
move=> H10.
reflexivity.
move=> k.
elim.
unfold In.
simpl.
elim (excluded_middle_informative (m = m)).
move=> H8.
apply H6.
move=> H8.
apply False_ind.
apply H8.
reflexivity.
apply (Finite_downward_closed {n : nat | n < N} (Full_set {n : nat | n < N}) (CountFinite N)).
move=> k H7.
apply (Full_intro {n : nat | n < N} k).
apply SumTSubspaceVS.
move=> m.
apply (SingleSubspaceVS K V).
move=> m.
elim (BijectiveSameSig {x : VT K V | In (VT K V) (SpanVS K V {n : nat | n < N} F) x} (fun v : {x : VT K V | In (VT K V) (SpanVS K V {n : nat | n < N} F) x} => exists f : FT K, v = SubspaceMakeVSVmul K V (SpanVS K V {n : nat | n < N} F) (SpanSubspaceVS K V {n : nat | n < N} F) f (exist (SpanVS K V {n : nat | n < N} F) (F m) (SpanContainSelfVS K V {n : nat | n < N} F m))) (fun v : {x : VT K V | In (VT K V) (SpanVS K V {n : nat | n < N} F) x} => exists f : FT K, proj1_sig v = Vmul K V f (F m))).
move=> g1 H4.
elim (BijectiveSigSigInv (VT K V) (SpanVS K V {n : nat | n < N} F) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F m))).
move=> g2 H5.
elim (BijectiveSameSig (VT K V) (Intersection (VT K V) (SpanVS K V {n : nat | n < N} F) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F m))) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F m))).
move=> g3 H6.
exists (compose g3 (compose g2 g1)).
apply conj.
move=> x.
rewrite - (proj1 H6).
rewrite - (proj1 H5).
rewrite - (proj1 H4).
reflexivity.
apply BijChain.
apply BijChain.
apply (proj2 H4).
apply (proj2 H5).
apply (proj2 H6).
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> w H6 H7.
apply H7.
move=> v H6.
apply Intersection_intro.
elim H6.
move=> f H7.
rewrite H7.
apply (proj1 (proj2 (SpanSubspaceVS K V {n : nat | n < N} F)) f (F m)).
apply SpanContainSelfVS.
apply H6.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> f H4.
exists f.
rewrite H4.
reflexivity.
move=> v.
elim.
move=> f H4.
exists f.
apply sig_map.
apply H4.
Qed.

Lemma Formula_P25_exists : forall (K : Field) (V : VectorSpace K) (N : nat) (F : {n : nat | n < N} -> VT K V), exists (H : forall (t : (forall (m : {n : nat | n < N}), {v : VT K V | exists (f : FT K), v = Vmul K V f (F m)})), In (VT K V) (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun (m : {n : nat | n < N}) => proj1_sig (t m)))), LinearlyIndependentVS K V {n : nat | n < N} F <-> ((Bijective (DirectProdVST K {n : nat | n < N} (fun (m : {n : nat | n < N}) => SubspaceMakeVS K V (fun (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m)) (SingleSubspaceVS K V (F m)))) {w : VT K V | SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m)) w} (fun (t : forall (m : {n : nat | n < N}), {v : VT K V | exists (f : FT K), v = Vmul K V f (F m)}) => exist (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists (f : FT K), v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun (m : {n : nat | n < N}) => proj1_sig (t m))) (H t))) /\ forall (m : {n : nat | n < N}), (F m) <> VO K V).
Proof.
move=> K V N F.
suff: (forall (t : forall m : {n : nat | n < N}, {v : VT K V | exists f : FT K, v = Vmul K V f (F m)}), In (VT K V) (SumTEnsembleVS K V {n : nat | n < N} (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))) (MySumF2 {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (VSPCM K V) (fun m : {n : nat | n < N} => proj1_sig (t m)))).
move=> H1.
exists H1.
apply (Formula_P25 K V N F H1).
move=> t.
rewrite (FiniteSumTEnsembleVS K V N (fun (m : {n : nat | n < N}) (v : VT K V) => exists f : FT K, v = Vmul K V f (F m))).
exists (fun (m : {n : nat | n < N}) => proj1_sig (t m)).
apply conj.
move=> m.
apply (proj2_sig (t m)).
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

Lemma Proposition_5_2_exists : forall (K : Field) (V : VectorSpace K) (N : nat), exists (H1 : forall (m : Count N), proj1_sig m < S N) (H2 : N < S N), forall (F : Count (S N) -> VT K V), (LinearlyIndependentVS K V (Count (S N)) F) <-> (LinearlyIndependentVS K V (Count N) (fun (m : Count N) => F (exist (fun (n : nat) => n < S N) (proj1_sig m) (H1 m))) /\ ~ (In (VT K V) (SpanVS K V (Count N) (fun (m : Count N) => F (exist (fun (n : nat) => n < S N) (proj1_sig m) (H1 m)))) (F (exist (fun (n : nat) => n < S N) N H2)))).
Proof.
move=> K V N.
exists (fun (m : Count N) => le_S (S (proj1_sig m)) N (proj2_sig m)).
exists (le_n (S N)).
apply (Proposition_5_2 K V N (fun (m : Count N) => le_S (S (proj1_sig m)) N (proj2_sig m)) (le_n (S N))).
Qed.

Lemma Theorem_5_4 : forall (K : Field) (V : VectorSpace K) (N1 N2 : nat) (F1 : Count N1 -> VT K V) (F2 : Count N2 -> VT K V), BasisVS K V (Count N1) F1 -> BasisVS K V (Count N2) F2 -> N1 = N2.
Proof.
move=> K V N1 N2 F1 F2 H1 H2.
suff: (exists (f : Count N1 -> Count N2), Bijective (Count N1) (Count N2) f).
move=> H3.
suff: (exists (f : Count N2 -> Count N2), Bijective (Count N2) (Count N2) f).
move=> H4.
apply (cardinal_is_functional (Count N2) (Full_set (Count N2)) N1 (proj1 (CountCardinalBijective (Count N2) N1) H3) (Full_set (Count N2)) N2 (proj1 (CountCardinalBijective (Count N2) N2) H4)).
reflexivity.
exists (fun (m : Count N2) => m).
exists (fun (m : Count N2) => m).
apply conj.
move=> x.
reflexivity.
move=> y.
reflexivity.
suff: (let W1 := (fun (m : nat) => SpanVS K V {n : Count N1 | proj1_sig n < m} (fun (k : {n : Count N1 | proj1_sig n < m}) => F1 (proj1_sig k))) in exists (f : Count N1 -> Count N2), Bijective (Count N1) (Count N2) f).
apply.
move=> W1.
suff: (let W2 := (fun (m : nat) => SpanVS K V {n : Count N2 | proj1_sig n < m} (fun (k : {n : Count N2 | proj1_sig n < m}) => F2 (proj1_sig k))) in exists (f : Count N1 -> Count N2), Bijective (Count N1) (Count N2) f).
apply.
move=> W2.
suff: (forall (k : Count N1), {m : nat | is_min_nat (fun (n : nat) => In (VT K V) (SumEnsembleVS K V (W1 (proj1_sig k)) (W2 n)) (F1 k)) m}).
move=> H3.
suff: (forall (k : Count N2), {m : nat | is_min_nat (fun (n : nat) => In (VT K V) (SumEnsembleVS K V (W1 n) (W2 (proj1_sig k))) (F2 k)) m}).
move=> H4.
suff: (forall (k : Count N1), {m : Count N2 | S (proj1_sig m) = proj1_sig (H3 k)}).
move=> H5.
suff: (forall (k : Count N2), {m : Count N1 | S (proj1_sig m) = proj1_sig (H4 k)}).
move=> H6.
suff: (forall (m : Count N1), W1 (S (proj1_sig m)) = SumEnsembleVS K V (W1 (proj1_sig m)) (fun (v : VT K V) => exists (f : FT K), v = Vmul K V f (F1 m))).
move=> H12.
suff: (forall (m : Count N2), W2 (S (proj1_sig m)) = SumEnsembleVS K V (W2 (proj1_sig m)) (fun (v : VT K V) => exists (f : FT K), v = Vmul K V f (F2 m))).
move=> H13.
suff: (forall (n1 n2 : nat), n1 <= n2 -> Included (VT K V) (W1 n1) (W1 n2)).
move=> H7.
suff: (forall (n1 n2 : nat), n1 <= n2 -> Included (VT K V) (W2 n1) (W2 n2)).
move=> H8.
suff: (forall (n1 n2 m : nat), n1 <= n2 -> Included (VT K V) (SumEnsembleVS K V (W1 n1) (W2 m)) (SumEnsembleVS K V (W1 n2) (W2 m))).
move=> H9.
suff: (forall (n1 n2 m : nat), n1 <= n2 -> Included (VT K V) (SumEnsembleVS K V (W1 m) (W2 n1)) (SumEnsembleVS K V (W1 m) (W2 n2))).
move=> H10.
suff: (forall (w1 : VT K V) (w2 : VT K V) (A : Ensemble (VT K V)), (SubspaceVS K V A) -> ~ (In (VT K V) A w1) -> (In (VT K V) (SumEnsembleVS K V A (fun (v : VT K V) => exists (f : FT K), v = Vmul K V f w2)) w1) -> (In (VT K V) (SumEnsembleVS K V A (fun (v : VT K V) => exists (f : FT K), v = Vmul K V f w1)) w2)).
move=> H11.
suff: (forall (n1 : Count N1) (n2 : Count N2), (proj1_sig (H5 n1)) = n2 <-> (proj1_sig (H6 n2)) = n1).
move=> H14.
exists (fun (k : Count N1) => proj1_sig (H5 k)).
exists (fun (k : Count N2) => proj1_sig (H6 k)).
apply conj.
move=> x.
apply (proj1 (H14 x (proj1_sig (H5 x)))).
reflexivity.
move=> y.
apply (proj2 (H14 (proj1_sig (H6 y)) y)).
reflexivity.
move=> n1 n2.
suff: (proj1_sig (H5 n1) = n2 <-> ((SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2)) <> SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (proj1_sig n2))) /\ (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2)) <> SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2)))) /\ (SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (proj1_sig n2)) = SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (S (proj1_sig n2)))) /\ (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2))) = SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (S (proj1_sig n2)))))).
move=> H14.
suff: (proj1_sig (H6 n2) = n1 <-> ((SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2)) <> SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (proj1_sig n2))) /\ (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2)) <> SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2)))) /\ (SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (proj1_sig n2)) = SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (S (proj1_sig n2)))) /\ (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2))) = SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (S (proj1_sig n2)))))).
move=> H15.
apply conj.
move=> H16.
apply (proj2 H15).
apply (proj1 H14).
apply H16.
move=> H16.
apply (proj2 H14).
apply (proj1 H15).
apply H16.
apply conj.
move=> H15.
suff: (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2)) <>
SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (proj1_sig n2))).
move=> H16.
suff: (SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (proj1_sig n2)) =
SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (S (proj1_sig n2)))).
move=> H17.
suff: (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2))) =
SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (S (proj1_sig n2)))).
move=> H18.
apply conj.
apply H16.
apply conj.
rewrite H18.
rewrite - H17.
apply H16.
apply conj.
apply H17.
apply H18.
apply Extensionality_Ensembles.
apply conj.
apply (H9 (proj1_sig n1) (S (proj1_sig n1)) (S (proj1_sig n2))).
apply (le_S (proj1_sig n1) (proj1_sig n1) (le_n (proj1_sig n1))).
suff: (SubspaceVS K V (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2))))).
move=> H18.
suff: (In (VT K V) (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2)))) (F1 n1)).
move=> H19 v.
rewrite (H12 n1).
elim.
move=> v1 v2 H20 H21.
apply (proj1 H18 v1 v2).
elim H20.
move=> v11 v12 H22 H23.
apply (proj1 H18 v11 v12).
rewrite - (Vadd_O_r K V v11).
apply (SumEnsembleVS_intro K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2))) v11 (VO K V)).
apply H22.
suff: (SubspaceVS K V (W2 (S (proj1_sig n2)))).
move=> H24.
apply (proj2 (proj2 H24)).
apply (SpanSubspaceVS K V).
elim H23.
move=> f H24.
rewrite H24.
apply (proj1 (proj2 H18) f (F1 n1)).
apply H19.
rewrite - (Vadd_O_l K V v2).
apply (SumEnsembleVS_intro K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2))) (VO K V) v2).
suff: (SubspaceVS K V (W1 (proj1_sig n1))).
move=> H22.
apply (proj2 (proj2 H22)).
apply (SpanSubspaceVS K V).
apply H21.
rewrite (H13 n2).
suff: ((SumEnsembleVS K V (W1 (proj1_sig n1)) (SumEnsembleVS K V (W2 (proj1_sig n2)) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F2 n2)))) = (SumEnsembleVS K V (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2))) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F2 n2)))).
move=> H19.
rewrite H19.
apply (H11 (F2 n2) (F1 n1) (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2)))).
apply (SumSubspaceVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2))).
apply (SpanSubspaceVS K V).
apply (SpanSubspaceVS K V).
rewrite - H15.
move=> H20.
apply (lt_irrefl (proj1_sig (proj1_sig (H6 n2)))).
unfold lt.
rewrite (proj2_sig (H6 n2)).
apply (proj2 (proj2_sig (H4 n2)) (proj1_sig (proj1_sig (H6 n2)))).
apply H20.
suff: ((SumEnsembleVS K V (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2))) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F1 n1))) = (SumEnsembleVS K V (SumEnsembleVS K V (W1 (proj1_sig n1)) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F1 n1))) (W2 (proj1_sig n2)))).
move=> H20.
rewrite H20.
rewrite - (H12 n1).
rewrite H17.
rewrite - (Vadd_O_l K V (F2 n2)).
apply (SumEnsembleVS_intro K V (W1 (S (proj1_sig n1))) (W2 (S (proj1_sig n2))) (VO K V) (F2 n2)).
suff: (SubspaceVS K V (W1 (S (proj1_sig n1)))).
move=> H21.
apply (proj2 (proj2 H21)).
apply (SpanSubspaceVS K V).
rewrite (H13 n2).
rewrite - {2} (Vadd_O_l K V (F2 n2)).
apply (SumEnsembleVS_intro K V (W2 (proj1_sig n2)) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F2 n2)) (VO K V) (F2 n2)).
suff: (SubspaceVS K V (W2 (proj1_sig n2))).
move=> H21.
apply (proj2 (proj2 H21)).
apply (SpanSubspaceVS K V).
exists (FI K).
rewrite (Vmul_I_l K V (F2 n2)).
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> v1 v2 H20 H21.
elim H20.
move=> v11 v12 H22 H23.
rewrite (Vadd_assoc K V v11 v12 v2).
rewrite (Vadd_comm K V v12 v2).
rewrite - (Vadd_assoc K V v11 v2 v12).
apply (SumEnsembleVS_intro K V).
apply (SumEnsembleVS_intro K V).
apply H22.
apply H21.
apply H23.
move=> v.
elim.
move=> v1 v12 H20 H21.
elim H20.
move=> v11 v2 H22 H23.
rewrite (Vadd_assoc K V v11 v2 v12).
rewrite (Vadd_comm K V v2 v12).
rewrite - (Vadd_assoc K V v11 v12 v2).
apply (SumEnsembleVS_intro K V).
apply (SumEnsembleVS_intro K V).
apply H22.
apply H21.
apply H23.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> v11 v1 H19 H20.
elim H20.
move=> v12 v2 H21 H22.
rewrite - (Vadd_assoc K V v11 v12 v2).
apply (SumEnsembleVS_intro K V).
apply (SumEnsembleVS_intro K V).
apply H19.
apply H21.
apply H22.
move=> v.
elim.
move=> v1 v2 H19 H20.
elim H19.
move=> v11 v12 H21 H22.
rewrite (Vadd_assoc K V v11 v12 v2).
apply (SumEnsembleVS_intro K V).
apply H21.
apply (SumEnsembleVS_intro K V).
apply H22.
apply H20.
apply (SumSubspaceVS K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2)))).
apply (SpanSubspaceVS K V).
apply (SpanSubspaceVS K V).
apply Extensionality_Ensembles.
apply conj.
apply (H10 (proj1_sig n2) (S (proj1_sig n2)) (S (proj1_sig n1))).
apply (le_S (proj1_sig n2) (proj1_sig n2) (le_n (proj1_sig n2))).
rewrite (H13 n2).
move=> v.
elim.
move=> v1 v2 H17 H18.
elim H18.
move=> v11 v12 H19 H20.
rewrite - (Vadd_assoc K V v1 v11 v12).
suff: (SubspaceVS K V (SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (proj1_sig n2)))).
move=> H21.
apply (proj1 H21 (Vadd K V v1 v11) v12).
apply (SumEnsembleVS_intro K V (W1 (S (proj1_sig n1))) (W2 (proj1_sig n2)) v1 v11 H17 H19).
elim H20.
move=> f H22.
rewrite H22.
apply (proj1 (proj2 H21) f (F2 n2)).
rewrite - H15.
rewrite (proj2_sig (H6 n2)).
apply (proj1 (proj2_sig (H4 n2))).
apply (SumSubspaceVS K V (W1 (S (proj1_sig n1))) (W2 (proj1_sig n2))).
apply (SpanSubspaceVS K V).
apply (SpanSubspaceVS K V).
move=> H16.
suff: (In (VT K V) (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2))) (F2 n2)).
rewrite - H15.
move=> H17.
apply (lt_irrefl (proj1_sig (proj1_sig (H6 n2)))).
unfold lt.
rewrite (proj2_sig (H6 n2)).
apply (proj2 (proj2_sig (H4 n2)) (proj1_sig (proj1_sig (H6 n2)))).
apply H17.
rewrite H16.
rewrite - H15.
rewrite (proj2_sig (H6 n2)).
apply (proj1 (proj2_sig (H4 n2))).
move=> H15.
apply sig_map.
apply PeanoNat.Nat.succ_inj.
rewrite (proj2_sig (H6 n2)).
apply (is_min_nat_unique (fun (n : nat) => In (VT K V) (SumEnsembleVS K V (W1 n) (W2 (proj1_sig n2))) (F2 n2)) (proj1_sig (H4 n2)) (S (proj1_sig n1))).
apply (proj2_sig (H4 n2)).
apply conj.
unfold In.
rewrite (proj1 (proj2 (proj2 H15))).
rewrite (H13 n2).
rewrite - {2} (Vadd_O_l K V (F2 n2)).
apply (SumEnsembleVS_intro K V).
suff: (SubspaceVS K V (W1 (S (proj1_sig n1)))).
move=> H16.
apply (proj2 (proj2 H16)).
apply (SpanSubspaceVS K V).
rewrite - {2} (Vadd_O_l K V (F2 n2)).
apply (SumEnsembleVS_intro K V).
suff: (SubspaceVS K V (W2 (proj1_sig n2))).
move=> H16.
apply (proj2 (proj2 H16)).
apply (SpanSubspaceVS K V).
exists (FI K).
rewrite (Vmul_I_l K V (F2 n2)).
reflexivity.
move=> m H16.
elim (le_or_lt m (proj1_sig n1)).
move=> H17.
apply False_ind.
suff: (~ In (VT K V) (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2))) (F2 n2)).
move=> H18.
apply H18.
apply (H9 m (proj1_sig n1) (proj1_sig n2) H17 (F2 n2) H16).
move=> H18.
apply (proj1 (proj2 H15)).
apply Extensionality_Ensembles.
apply conj.
apply (H10 (proj1_sig n2) (S (proj1_sig n2)) (proj1_sig n1)).
apply (le_S (proj1_sig n2) (proj1_sig n2) (le_n (proj1_sig n2))).
rewrite (H13 n2).
move=> v.
elim.
move=> v1 v2 H19.
elim.
move=> v21 v22 H20 H21.
rewrite - (Vadd_assoc K V v1 v21 v22).
suff: (SubspaceVS K V (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2)))).
move=> H22.
apply (proj1 H22 (Vadd K V v1 v21) v22).
apply (SumEnsembleVS_intro K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2)) v1 v21). 
apply H19.
apply H20.
elim H21.
move=> f H23.
rewrite H23.
apply (proj1 (proj2 H22) f (F2 n2)).
apply H18.
apply (SumSubspaceVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2))).
apply (SpanSubspaceVS K V).
apply (SpanSubspaceVS K V).
apply.
apply conj.
move=> H14.
suff: (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2)) <>
SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2)))).
move=> H15.
suff: (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2))) =
SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (S (proj1_sig n2)))).
move=> H16.
suff: (SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (proj1_sig n2)) =
SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (S (proj1_sig n2)))).
move=> H17.
apply conj.
rewrite H17.
rewrite - H16.
apply H15.
apply conj.
apply H15.
apply conj.
apply H17.
apply H16.
apply Extensionality_Ensembles.
apply conj.
apply (H10 (proj1_sig n2) (S (proj1_sig n2)) (S (proj1_sig n1))).
apply (le_S (proj1_sig n2) (proj1_sig n2) (le_n (proj1_sig n2))).
suff: (SubspaceVS K V (SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (proj1_sig n2)))).
move=> H17.
suff: (In (VT K V) (SumEnsembleVS K V (W1 (S (proj1_sig n1))) (W2 (proj1_sig n2))) (F2 n2)).
move=> H18 v.
rewrite (H13 n2).
elim.
move=> v1 v2 H19.
elim.
move=> v11 v12 H20 H21.
rewrite - (Vadd_assoc K V v1 v11 v12).
apply (proj1 H17 (Vadd K V v1 v11) v12).
apply (SumEnsembleVS_intro K V (W1 (S (proj1_sig n1))) (W2 (proj1_sig n2)) v1 v11 H19 H20).
elim H21.
move=> f H22.
rewrite H22.
apply (proj1 (proj2 H17) f (F2 n2)).
apply H18.
rewrite (H12 n1).
suff: ((SumEnsembleVS K V (SumEnsembleVS K V (W1 (proj1_sig n1)) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F1 n1))) (W2 (proj1_sig n2))) = (SumEnsembleVS K V (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2))) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F1 n1)))).
move=> H18.
rewrite H18.
apply (H11 (F1 n1) (F2 n2) (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2)))).
apply (SumSubspaceVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2))).
apply (SpanSubspaceVS K V).
apply (SpanSubspaceVS K V).
rewrite - H14.
move=> H19.
apply (lt_irrefl (proj1_sig (proj1_sig (H5 n1)))).
unfold lt.
rewrite (proj2_sig (H5 n1)).
apply (proj2 (proj2_sig (H3 n1)) (proj1_sig (proj1_sig (H5 n1)))).
apply H19.
suff: ((SumEnsembleVS K V (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2))) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F2 n2))) = (SumEnsembleVS K V (W1 (proj1_sig n1)) (SumEnsembleVS K V (W2 (proj1_sig n2)) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F2 n2))))).
move=> H19.
rewrite H19.
rewrite - (H13 n2).
rewrite H16.
rewrite - (Vadd_O_r K V (F1 n1)).
apply (SumEnsembleVS_intro K V (W1 (S (proj1_sig n1))) (W2 (S (proj1_sig n2))) (F1 n1) (VO K V)).
rewrite (H12 n1).
rewrite - {2} (Vadd_O_l K V (F1 n1)).
apply (SumEnsembleVS_intro K V (W1 (proj1_sig n1)) (fun v : VT K V => exists f : FT K, v = Vmul K V f (F1 n1)) (VO K V) (F1 n1)).
suff: (SubspaceVS K V (W1 (proj1_sig n1))).
move=> H20.
apply (proj2 (proj2 H20)).
apply (SpanSubspaceVS K V).
exists (FI K).
rewrite (Vmul_I_l K V (F1 n1)).
reflexivity.
suff: (SubspaceVS K V (W2 (S (proj1_sig n2)))).
move=> H20.
apply (proj2 (proj2 H20)).
apply (SpanSubspaceVS K V).
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> v1 v2 H19 H20.
elim H19.
move=> v11 v12 H21 H22.
rewrite (Vadd_assoc K V v11 v12 v2).
apply (SumEnsembleVS_intro K V).
apply H21.
apply (SumEnsembleVS_intro K V).
apply H22.
apply H20.
move=> v.
elim.
move=> v11 v1 H19 H20.
elim H20.
move=> v12 v2 H21 H22.
rewrite - (Vadd_assoc K V v11 v12 v2).
apply (SumEnsembleVS_intro K V).
apply (SumEnsembleVS_intro K V).
apply H19.
apply H21.
apply H22.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> v1 v12 H18 H19.
elim H18.
move=> v11 v2 H20 H21.
rewrite (Vadd_assoc K V v11 v2 v12).
rewrite (Vadd_comm K V v2 v12).
rewrite - (Vadd_assoc K V v11 v12 v2).
apply (SumEnsembleVS_intro K V).
apply (SumEnsembleVS_intro K V).
apply H20.
apply H19.
apply H21.
move=> v.
elim.
move=> v1 v2 H18 H19.
elim H18.
move=> v11 v12 H20 H21.
rewrite (Vadd_assoc K V v11 v12 v2).
rewrite (Vadd_comm K V v12 v2).
rewrite - (Vadd_assoc K V v11 v2 v12).
apply (SumEnsembleVS_intro K V).
apply (SumEnsembleVS_intro K V).
apply H20.
apply H19.
apply H21.
apply (SumSubspaceVS K V (W1 (S (proj1_sig n1))) (W2 (proj1_sig n2))).
apply (SpanSubspaceVS K V).
apply (SpanSubspaceVS K V).
apply Extensionality_Ensembles.
apply conj.
apply (H9 (proj1_sig n1) (S (proj1_sig n1)) (S (proj1_sig n2))).
apply (le_S (proj1_sig n1) (proj1_sig n1) (le_n (proj1_sig n1))).
rewrite (H12 n1).
move=> v.
elim.
move=> v1 v12 H16 H17.
elim H16.
move=> v11 v2 H18 H19.
suff: (SubspaceVS K V (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2))))).
move=> H20.
rewrite (Vadd_assoc K V v11 v2 v12).
rewrite (Vadd_comm K V v2 v12).
rewrite - (Vadd_assoc K V v11 v12 v2).
apply (proj1 H20 (Vadd K V v11 v12) v2).
apply (SumEnsembleVS_intro K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2))) v11 v12 H18 H17).
elim H19.
move=> f H21.
rewrite H21.
apply (proj1 (proj2 H20) f (F1 n1)).
rewrite - H14.
rewrite (proj2_sig (H5 n1)).
apply (proj1 (proj2_sig (H3 n1))).
apply (SumSubspaceVS K V (W1 (proj1_sig n1)) (W2 (S (proj1_sig n2)))).
apply (SpanSubspaceVS K V).
apply (SpanSubspaceVS K V).
move=> H15.
suff: (In (VT K V) (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2))) (F1 n1)).
rewrite - H14.
move=> H16.
apply (lt_irrefl (proj1_sig (proj1_sig (H5 n1)))).
unfold lt.
rewrite (proj2_sig (H5 n1)).
apply (proj2 (proj2_sig (H3 n1)) (proj1_sig (proj1_sig (H5 n1)))).
apply H16.
rewrite H15.
rewrite - H14.
rewrite (proj2_sig (H5 n1)).
apply (proj1 (proj2_sig (H3 n1))).
move=> H14.
apply sig_map.
apply PeanoNat.Nat.succ_inj.
rewrite (proj2_sig (H5 n1)).
apply (is_min_nat_unique (fun (n : nat) => In (VT K V) (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 n)) (F1 n1)) (proj1_sig (H3 n1)) (S (proj1_sig n2))).
apply (proj2_sig (H3 n1)).
apply conj.
unfold In.
rewrite (proj2 (proj2 (proj2 H14))).
rewrite (H12 n1).
rewrite - {2} (Vadd_O_r K V (F1 n1)).
apply (SumEnsembleVS_intro K V).
rewrite - {2} (Vadd_O_l K V (F1 n1)).
apply (SumEnsembleVS_intro K V).
suff: (SubspaceVS K V (W1 (proj1_sig n1))).
move=> H15.
apply (proj2 (proj2 H15)).
apply (SpanSubspaceVS K V).
exists (FI K).
rewrite (Vmul_I_l K V (F1 n1)).
reflexivity.
suff: (SubspaceVS K V (W2 (S (proj1_sig n2)))).
move=> H15.
apply (proj2 (proj2 H15)).
apply (SpanSubspaceVS K V).
move=> m H15.
elim (le_or_lt m (proj1_sig n2)).
move=> H16.
apply False_ind.
suff: (~ In (VT K V) (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2))) (F1 n1)).
move=> H17.
apply H17.
apply (H10 m (proj1_sig n2) (proj1_sig n1) H16 (F1 n1) H15).
move=> H17.
apply (proj1 H14).
apply Extensionality_Ensembles.
apply conj.
apply (H9 (proj1_sig n1) (S (proj1_sig n1)) (proj1_sig n2)).
apply (le_S (proj1_sig n1) (proj1_sig n1) (le_n (proj1_sig n1))).
rewrite (H12 n1).
move=> v.
elim.
move=> v1 v12 H18 H19.
elim H18.
move=> v11 v2 H20 H21.
rewrite (Vadd_assoc K V v11 v2 v12).
rewrite (Vadd_comm K V v2 v12).
rewrite - (Vadd_assoc K V v11 v12 v2).
suff: (SubspaceVS K V (SumEnsembleVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2)))).
move=> H22.
apply (proj1 H22 (Vadd K V v11 v12) v2).
apply (SumEnsembleVS_intro K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2)) v11 v12 H20 H19). 
elim H21.
move=> f H23.
rewrite H23.
apply (proj1 (proj2 H22) f (F1 n1) H17).
apply (SumSubspaceVS K V (W1 (proj1_sig n1)) (W2 (proj1_sig n2))).
apply (SpanSubspaceVS K V).
apply (SpanSubspaceVS K V).
apply.
move=> w1 w2 A H11 H14 H15.
suff: (exists (a : VT K V) (f : FT K), w1 = Vadd K V a (Vmul K V f w2) /\ In (VT K V) A a).
elim.
move=> a.
elim.
move=> f H16.
suff: (f <> FO K).
move=> H17.
rewrite - (Vmul_I_l K V w2).
rewrite - (Finv_l K f H17).
suff: (SubspaceVS K V(SumEnsembleVS K V A (fun v : VT K V => exists f0 : FT K, v = Vmul K V f0 w1))).
move=> H18.
rewrite - (Vmul_assoc K V (Finv K f) f w2).
apply (proj1 (proj2 H18) (Finv K f) (Vmul K V f w2)).
suff: (Vmul K V f w2 = Vadd K V (Vopp K V a) w1).
move=> H19.
rewrite H19.
apply (SumEnsembleVS_intro K V A (fun v : VT K V => exists f0 : FT K, v = Vmul K V f0 w1) (Vopp K V a) w1). 
apply (SubspaceMakeVSVoppSub K V A H11 a (proj2 H16)).
exists (FI K).
rewrite (Vmul_I_l K V w1).
reflexivity.
apply (Vadd_eq_reg_l K V a (Vmul K V f w2) (Vadd K V (Vopp K V a) w1)).
rewrite - (Vadd_assoc K V a (Vopp K V a) w1).
rewrite (Vadd_opp_r K V a).
rewrite (Vadd_O_l K V w1).
rewrite (proj1 H16).
reflexivity.
apply (SumSubspaceVS K V A (fun v : VT K V => exists f0 : FT K, v = Vmul K V f0 w1)).
apply H11.
apply (SingleSubspaceVS K V w1).
move=> H17.
apply H14.
rewrite (proj1 H16).
rewrite H17.
rewrite (Vmul_O_l K V w2).
rewrite (Vadd_O_r K V a).
apply (proj2 H16).
elim H15.
move=> v1 v2 H16 H17.
exists v1.
elim H17.
move=> f H18.
exists f.
apply conj.
rewrite H18.
reflexivity.
apply H16.
move=> n1 n2 m H10 v.
elim.
move=> v1 v2 H11 H14.
apply (SumEnsembleVS_intro K V (W1 m) (W2 n2) v1 v2 H11).
apply (H8 n1 n2 H10 v2 H14).
move=> n1 n2 m H9 v.
elim.
move=> v1 v2 H10 H11.
apply (SumEnsembleVS_intro K V (W1 n2) (W2 m) v1 v2).
apply (H7 n1 n2 H9 v1 H10).
apply H11.
move=> n1 n2.
elim.
move=> v.
apply.
move=> m H8 H9.
elim (le_or_lt N2 m).
move=> H10.
suff: (W2 (S m) = W2 m).
move=> H11.
rewrite H11.
apply H9.
unfold W2.
suff: (forall (n : Count N2), proj1_sig n < S m).
move=> H11.
suff: ((fun k : {n : Count N2 | proj1_sig n < m} => F2 (proj1_sig k)) = compose (fun k : {n : Count N2 | proj1_sig n < S m} => F2 (proj1_sig k)) (fun (l : {n : Count N2 | proj1_sig n < m}) => exist (fun (k : Count N2) => proj1_sig k < S m) (proj1_sig l) (H11 (proj1_sig l)))).
move=> H14.
rewrite H14.
apply (BijectiveSaveSpanVS K V {n : Count N2 | proj1_sig n < m} {n : Count N2 | proj1_sig n < S m} (fun l : {n : Count N2 | proj1_sig n < m} => exist (fun k : Count N2 => proj1_sig k < S m) (proj1_sig l) (H11 (proj1_sig l))) (fun k : {n : Count N2 | proj1_sig n < S m} => F2 (proj1_sig k))).
suff: (forall (n : Count N2), proj1_sig n < m).
move=> H15.
exists (fun l : {n : Count N2 | proj1_sig n < S m} => exist (fun k : Count N2 => proj1_sig k < m) (proj1_sig l) (H15 (proj1_sig l))).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
reflexivity.
move=> n.
apply (le_trans (S (proj1_sig n)) N2 m (proj2_sig n) H10).
apply functional_extensionality.
move=> k.
reflexivity.
move=> n.
apply (le_trans (S (proj1_sig n)) N2 (S m) (proj2_sig n) (le_S N2 m H10)).
move=> H10.
rewrite (H13 (exist (fun (n : nat) => n < N2) m H10)).
move=> v H11.
rewrite - (Vadd_O_r K V v).
apply (SumEnsembleVS_intro K V).
apply (H9 v H11).
exists (FO K).
rewrite (Vmul_O_l K V).
reflexivity.
move=> n1 n2.
elim.
move=> v.
apply.
move=> m H7 H8.
elim (le_or_lt N1 m).
move=> H9.
suff: (W1 (S m) = W1 m).
move=> H10.
rewrite H10.
apply H8.
unfold W1.
suff: (forall (n : Count N1), proj1_sig n < S m).
move=> H10.
suff: ((fun k : {n : Count N1 | proj1_sig n < m} => F1 (proj1_sig k)) = compose (fun k : {n : Count N1 | proj1_sig n < S m} => F1 (proj1_sig k)) (fun (l : {n : Count N1 | proj1_sig n < m}) => exist (fun (k : Count N1) => proj1_sig k < S m) (proj1_sig l) (H10 (proj1_sig l)))).
move=> H11.
rewrite H11.
apply (BijectiveSaveSpanVS K V {n : Count N1 | proj1_sig n < m} {n : Count N1 | proj1_sig n < S m} (fun l : {n : Count N1 | proj1_sig n < m} => exist (fun k : Count N1 => proj1_sig k < S m) (proj1_sig l) (H10 (proj1_sig l))) (fun k : {n : Count N1 | proj1_sig n < S m} => F1 (proj1_sig k))).
suff: (forall (n : Count N1), proj1_sig n < m).
move=> H14.
exists (fun l : {n : Count N1 | proj1_sig n < S m} => exist (fun k : Count N1 => proj1_sig k < m) (proj1_sig l) (H14 (proj1_sig l))).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
reflexivity.
move=> n.
apply (le_trans (S (proj1_sig n)) N1 m (proj2_sig n) H9).
apply functional_extensionality.
move=> k.
reflexivity.
move=> n.
apply (le_trans (S (proj1_sig n)) N1 (S m) (proj2_sig n) (le_S N1 m H9)).
move=> H9.
rewrite (H12 (exist (fun (n : nat) => n < N1) m H9)).
move=> v H10.
rewrite - (Vadd_O_r K V v).
apply (SumEnsembleVS_intro K V).
apply (H8 v H10).
exists (FO K).
rewrite (Vmul_O_l K V).
reflexivity.
move=> m.
unfold W2.
suff: (forall (m : (Count (S (proj1_sig m)))), proj1_sig m < N2).
move=> H13.
rewrite (BijectiveSaveSpanVS K V (Count (S (proj1_sig m))) {n : Count N2 | proj1_sig n < S (proj1_sig m)} (fun (k : Count (S (proj1_sig m))) => exist (fun (l : Count N2) => proj1_sig l < S (proj1_sig m)) (exist (fun (l : nat) => l < N2) (proj1_sig k) (H13 k)) (proj2_sig k))).
suff: (forall (m : (Count (proj1_sig m))), proj1_sig m < N2).
move=> H14.
rewrite (BijectiveSaveSpanVS K V (Count (proj1_sig m)) {n : Count N2 | proj1_sig n < proj1_sig m} (fun (k : Count (proj1_sig m)) => exist (fun (l : Count N2) => proj1_sig l < proj1_sig m) (exist (fun (l : nat) => l < N2) (proj1_sig k) (H14 k)) (proj2_sig k))).
simpl.
rewrite (FiniteSpanVS K V (S (proj1_sig m))).
rewrite (FiniteSpanVS K V (proj1_sig m)).
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> x H15.
rewrite H15.
elim (MySumF2Sn2_exists (proj1_sig m)).
move=> H16.
elim.
move=> H17 H18.
rewrite H18.
apply (SumEnsembleVS_intro K V).
exists (fun m0 : Count (proj1_sig m) => (x (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H16 m0)))).
suff: ((fun m0 : Count (proj1_sig m) => Vmul K V (x (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H16 m0))) (F2 (exist (fun l : nat => l < N2) (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H16 m0))) (H13 (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H16 m0)))))) = (fun n : Count (proj1_sig m) => Vmul K V (x (exist (fun n0 : nat => n0 < S (proj1_sig m)) (proj1_sig n) (H16 n))) (F2 (exist (fun l : nat => l < N2) (proj1_sig n) (H14 n))))).
move=> H19.
rewrite H19.
reflexivity.
apply functional_extensionality.
move=> n.
suff: ((H13 (exist (fun n0 : nat => n0 < S (proj1_sig m)) (proj1_sig n) (H16 n))) = (H14 n)).
move=> H19.
rewrite H19.
reflexivity.
apply proof_irrelevance.
exists (x (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H17)).
unfold compose.
suff: ((exist (fun l : nat => l < N2) (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H17)) (H13 (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H17))) = m).
move=> H19.
simpl.
rewrite H19.
reflexivity.
apply sig_map.
reflexivity.
move=> v.
elim.
move=> v1 v2 H15 H16.
elim H16.
move=> f H17.
rewrite H17.
elim H15.
move=> x H18.
rewrite H18.
exists (fun (k : Count (S (proj1_sig m))) => match (excluded_middle_informative (proj1_sig k < proj1_sig m)) with
  | left H => x (exist (fun (l : nat) => l < proj1_sig m) (proj1_sig k) H) 
  | right _ => f
end).
elim (MySumF2Sn2_exists (proj1_sig m)).
move=> H19.
elim.
move=> H20 H21.
rewrite H21.
suff: ((fun n : Count (proj1_sig m) => Vmul K V (x n) (F2 (exist (fun l : nat => l < N2) (proj1_sig n) (H14 n)))) = (fun m0 : Count (proj1_sig m) => Vmul K V match excluded_middle_informative (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H19 m0)) < proj1_sig m) with
  | left H => x (exist (fun l : nat => l < proj1_sig m) (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H19 m0))) H)
  | right _ => f
end (F2 (exist (fun l : nat => l < N2) (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H19 m0))) (H13 (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H19 m0))))))).
move=> H22.
rewrite H22.
suff: (Vmul K V f (F2 m) = Vmul K V match excluded_middle_informative (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H20) < proj1_sig m) with
  | left H => x (exist (fun l : nat => l < proj1_sig m) (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H20)) H)
  | right _ => f 
end (F2 (exist (fun l : nat => l < N2) (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H20)) (H13 (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H20))))).
move=> H23.
rewrite H23.
reflexivity.
simpl.
suff: ((exist (fun l : nat => l < N2) (proj1_sig m) (H13 (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H20))) = m).
move=> H23.
rewrite H23.
elim (excluded_middle_informative (proj1_sig m < proj1_sig m)).
move=> H24.
apply False_ind.
apply (lt_irrefl (proj1_sig m) H24).
move=> H24.
reflexivity.
apply sig_map.
reflexivity.
apply functional_extensionality.
move=> n.
simpl.
elim (excluded_middle_informative (proj1_sig n < proj1_sig m)).
move=> H22.
suff: ((exist (fun l : nat => l < proj1_sig m) (proj1_sig n) H22) = n).
move=> H23.
suff: ((exist (fun l : nat => l < N2) (proj1_sig n) (H13 (exist (fun n0 : nat => n0 < S (proj1_sig m)) (proj1_sig n) (H19 n)))) = (exist (fun l : nat => l < N2) (proj1_sig n) (H14 n))).
move=> H24.
rewrite H23.
rewrite H24.
reflexivity.
apply sig_map.
reflexivity.
apply sig_map.
reflexivity.
move=> H22.
apply False_ind.
apply H22.
apply (proj2_sig n).
exists (fun (l : {n : Count N2 | proj1_sig n < proj1_sig m}) => exist (fun (k : nat) => k < proj1_sig m) (proj1_sig (proj1_sig l)) (proj2_sig l)).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
reflexivity.
move=> k.
apply (lt_trans (proj1_sig k) (proj1_sig m) N2 (proj2_sig k) (proj2_sig m)).
exists (fun (l : {n : Count N2 | proj1_sig n < S (proj1_sig m)}) => exist (fun (k : nat) => k < S (proj1_sig m)) (proj1_sig (proj1_sig l)) (proj2_sig l)).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
reflexivity.
move=> k.
apply (le_trans (S (proj1_sig k)) (S (proj1_sig m)) N2 (proj2_sig k) (proj2_sig m)).
move=> m.
unfold W1.
suff: (forall (m : (Count (S (proj1_sig m)))), proj1_sig m < N1).
move=> H7.
rewrite (BijectiveSaveSpanVS K V (Count (S (proj1_sig m))) {n : Count N1 | proj1_sig n < S (proj1_sig m)} (fun (k : Count (S (proj1_sig m))) => exist (fun (l : Count N1) => proj1_sig l < S (proj1_sig m)) (exist (fun (l : nat) => l < N1) (proj1_sig k) (H7 k)) (proj2_sig k))).
suff: (forall (m : (Count (proj1_sig m))), proj1_sig m < N1).
move=> H8.
rewrite (BijectiveSaveSpanVS K V (Count (proj1_sig m)) {n : Count N1 | proj1_sig n < proj1_sig m} (fun (k : Count (proj1_sig m)) => exist (fun (l : Count N1) => proj1_sig l < proj1_sig m) (exist (fun (l : nat) => l < N1) (proj1_sig k) (H8 k)) (proj2_sig k))).
simpl.
rewrite (FiniteSpanVS K V (S (proj1_sig m))).
rewrite (FiniteSpanVS K V (proj1_sig m)).
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> x H9.
rewrite H9.
elim (MySumF2Sn2_exists (proj1_sig m)).
move=> H10.
elim.
move=> H11 H12.
rewrite H12.
apply (SumEnsembleVS_intro K V).
exists (fun m0 : Count (proj1_sig m) => (x (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H10 m0)))).
suff: ((fun m0 : Count (proj1_sig m) => Vmul K V (x (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H10 m0))) (F1 (exist (fun l : nat => l < N1) (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H10 m0))) (H7 (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H10 m0)))))) = (fun n : Count (proj1_sig m) => Vmul K V (x (exist (fun n0 : nat => n0 < S (proj1_sig m)) (proj1_sig n) (H10 n))) (F1 (exist (fun l : nat => l < N1) (proj1_sig n) (H8 n))))).
move=> H13.
rewrite H13.
reflexivity.
apply functional_extensionality.
move=> n.
suff: ((H7 (exist (fun n0 : nat => n0 < S (proj1_sig m)) (proj1_sig n) (H10 n))) = (H8 n)).
move=> H13.
rewrite H13.
reflexivity.
apply proof_irrelevance.
exists (x (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H11)).
suff: ((exist (fun l : nat => l < N1) (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H11)) (H7 (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H11))) = m).
move=> H13.
unfold compose.
simpl.
rewrite H13.
reflexivity.
apply sig_map.
reflexivity.
move=> v.
elim.
move=> v1 v2 H9 H10.
elim H10.
move=> f H11.
rewrite H11.
elim H9.
move=> x H12.
rewrite H12.
exists (fun (k : Count (S (proj1_sig m))) => match (excluded_middle_informative (proj1_sig k < proj1_sig m)) with
  | left H => x (exist (fun (l : nat) => l < proj1_sig m) (proj1_sig k) H) 
  | right _ => f
end).
elim (MySumF2Sn2_exists (proj1_sig m)).
move=> H13.
elim.
move=> H14 H15.
rewrite H15.
suff: ((fun n : Count (proj1_sig m) => Vmul K V (x n) (F1 (exist (fun l : nat => l < N1) (proj1_sig n) (H8 n)))) = (fun m0 : Count (proj1_sig m) => Vmul K V match excluded_middle_informative (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H13 m0)) < proj1_sig m) with
  | left H => x (exist (fun l : nat => l < proj1_sig m) (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H13 m0))) H)
  | right _ => f
end (F1 (exist (fun l : nat => l < N1) (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H13 m0))) (H7 (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H13 m0))))))).
move=> H16.
rewrite H16.
suff: (Vmul K V f (F1 m) = Vmul K V match excluded_middle_informative (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H14) < proj1_sig m) with
  | left H => x (exist (fun l : nat => l < proj1_sig m) (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H14)) H)
  | right _ => f
end (F1 (exist (fun l : nat => l < N1) (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H14)) (H7 (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H14))))).
move=> H17.
rewrite H17.
reflexivity.
simpl.
suff: ((exist (fun l : nat => l < N1) (proj1_sig m) (H7 (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H14))) = m).
move=> H17.
rewrite H17.
elim (excluded_middle_informative (proj1_sig m < proj1_sig m)).
move=> H18.
apply False_ind.
apply (lt_irrefl (proj1_sig m) H18).
move=> H18.
reflexivity.
apply sig_map.
reflexivity.
apply functional_extensionality.
move=> n.
simpl.
elim (excluded_middle_informative (proj1_sig n < proj1_sig m)).
move=> H16.
suff: ((exist (fun l : nat => l < proj1_sig m) (proj1_sig n) H16) = n).
move=> H17.
suff: ((exist (fun l : nat => l < N1) (proj1_sig n) (H7 (exist (fun n0 : nat => n0 < S (proj1_sig m)) (proj1_sig n) (H13 n)))) = (exist (fun l : nat => l < N1) (proj1_sig n) (H8 n))).
move=> H18.
rewrite H17.
rewrite H18.
reflexivity.
apply sig_map.
reflexivity.
apply sig_map.
reflexivity.
move=> H16.
apply False_ind.
apply H16.
apply (proj2_sig n).
exists (fun (l : {n : Count N1 | proj1_sig n < proj1_sig m}) => exist (fun (k : nat) => k < proj1_sig m) (proj1_sig (proj1_sig l)) (proj2_sig l)).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
reflexivity.
move=> k.
apply (lt_trans (proj1_sig k) (proj1_sig m) N1 (proj2_sig k) (proj2_sig m)).
exists (fun (l : {n : Count N1 | proj1_sig n < S (proj1_sig m)}) => exist (fun (k : nat) => k < S (proj1_sig m)) (proj1_sig (proj1_sig l)) (proj2_sig l)).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
reflexivity.
move=> k.
apply (le_trans (S (proj1_sig k)) (S (proj1_sig m)) N1 (proj2_sig k) (proj2_sig m)).
move=> k.
suff: (proj1_sig (H4 k) <> O /\ proj1_sig (H4 k) < S N1).
elim (proj1_sig (H4 k)).
move=> H6.
apply constructive_definite_description.
apply False_ind.
apply (proj1 H6).
reflexivity.
move=> n H6 H7.
exists (exist (fun (k : nat) => k < N1) n (lt_S_n n N1 (proj2 H7))).
reflexivity.
apply conj.
move=> H6.
suff: (In (VT K V) (SumEnsembleVS K V (W1 (proj1_sig (H4 k))) (W2 (proj1_sig k))) (F2 k)).
rewrite H6.
suff: (SumEnsembleVS K V (W1 0) (W2 (proj1_sig k)) = (W2 (proj1_sig k))).
move=> H7.
rewrite H7.
unfold W2.
suff: (forall (m : Count (proj1_sig k)), proj1_sig m < N2).
move=> H8.
rewrite (BijectiveSaveSpanVS K V (Count (proj1_sig k)) {n : Count N2 | proj1_sig n < proj1_sig k} (fun (m : Count (proj1_sig k)) => exist (fun (n : Count N2) => proj1_sig n < proj1_sig k) (exist (fun (n : nat) => n < N2) (proj1_sig m) (H8 m)) (proj2_sig m))).
simpl.
rewrite (FiniteSpanVS K V (proj1_sig k) (fun t : Count (proj1_sig k) => F2 (exist (fun n : nat => n < N2) (proj1_sig t) (H8 t)))).
elim.
move=> a H9.
apply (FI_neq_FO K).
rewrite - (Fopp_involutive K (FI K)).
apply (Fopp_eq_O_compat K (Fopp K (FI K))).
suff: (Fopp K (FI K) = (fun (m : Count N2) => match excluded_middle_informative (proj1_sig m <= proj1_sig k) with
  | left _ => match excluded_middle_informative (proj1_sig m < proj1_sig k) with
    | left H => a (exist (fun (n : nat) => n < proj1_sig k) (proj1_sig m) H)
    | right _ => Fopp K (FI K)
  end
  | right _ => FO K
end) k).
move=> H10.
rewrite H10.
apply (proj1 (FiniteLinearlyIndependentVS K V N2 F2) (proj1 (proj1 (BasisLIGeVS K V (Count N2) F2) H2)) (fun (m : Count N2) => match excluded_middle_informative (proj1_sig m <= proj1_sig k) with
  | left _ => match excluded_middle_informative (proj1_sig m < proj1_sig k) with
    | left H => a (exist (fun (n : nat) => n < proj1_sig k) (proj1_sig m) H)
    | right _ => Fopp K (FI K)
  end
  | right _ => FO K
end)).
rewrite (MySumF2Included (Count N2) (FiniteIntersection (Count N2) (exist (Finite (Count N2)) (Full_set (Count N2)) (CountFinite N2)) (fun (n : Count N2) => proj1_sig n <= proj1_sig k)) (exist (Finite (Count N2)) (Full_set (Count N2)) (CountFinite N2))).
rewrite (MySumF2O (Count N2) (FiniteIntersection (Count N2) (exist (Finite (Count N2)) (Full_set (Count N2)) (CountFinite N2)) (Complement (Count N2) (proj1_sig (FiniteIntersection (Count N2) (exist (Finite (Count N2)) (Full_set (Count N2)) (CountFinite N2)) (fun n : Count N2 => proj1_sig n <= proj1_sig k)))))).
rewrite (MySumF2Included (Count N2) (FiniteIntersection (Count N2) (exist (Finite (Count N2)) (Full_set (Count N2)) (CountFinite N2)) (fun n : Count N2 => proj1_sig n < proj1_sig k)) (FiniteIntersection (Count N2) (exist (Finite (Count N2)) (Full_set (Count N2)) (CountFinite N2)) (fun n : Count N2 => proj1_sig n <= proj1_sig k))).
suff: (FiniteIntersection (Count N2) (FiniteIntersection (Count N2) (exist (Finite (Count N2)) (Full_set (Count N2)) (CountFinite N2)) (fun n : Count N2 => proj1_sig n <= proj1_sig k)) (Complement (Count N2) (proj1_sig (FiniteIntersection (Count N2) (exist (Finite (Count N2)) (Full_set (Count N2)) (CountFinite N2)) (fun n : Count N2 => proj1_sig n < proj1_sig k)))) = FiniteSingleton (Count N2) k).
move=> H11.
rewrite H11.
rewrite MySumF2Singleton.
elim (excluded_middle_informative (proj1_sig k <= proj1_sig k)).
move=> H12.
elim (excluded_middle_informative (proj1_sig k < proj1_sig k)).
move=> H13.
apply False_ind.
apply (lt_irrefl (proj1_sig k) H13).
move=> H13.
rewrite (Vopp_mul_distr_l_reverse K V (FI K) (F2 k)).
rewrite (Vmul_I_l K V (F2 k)).
rewrite H9.
rewrite - (MySumF2BijectiveSame (Count (proj1_sig k)) (exist (Finite (Count (proj1_sig k))) (Full_set (Count (proj1_sig k))) (CountFinite (proj1_sig k))) (Count N2) (FiniteIntersection (Count N2) (exist (Finite (Count N2)) (Full_set (Count N2)) (CountFinite N2)) (fun n : Count N2 => proj1_sig n < proj1_sig k)) (VSPCM K V) (fun m : Count N2 => Vmul K V (match excluded_middle_informative (proj1_sig m <= proj1_sig k) with
  | left _ => match excluded_middle_informative (proj1_sig m < proj1_sig k) with
    | left H => a (exist (fun (n : nat) => n < proj1_sig k) (proj1_sig m) H)
    | right _ => Fopp K (FI K)
  end
  | right _ => FO K
end) (F2 m)) (fun n : Count (proj1_sig k) => (exist (fun n0 : nat => n0 < N2) (proj1_sig n) (H8 n)))).
suff: ((fun u : Count (proj1_sig k) => Vmul K V (match excluded_middle_informative (proj1_sig (exist (fun n0 : nat => n0 < N2) (proj1_sig u) (H8 u)) <= proj1_sig k) with 
  | left _ => match excluded_middle_informative (proj1_sig (exist (fun n0 : nat => n0 < N2) (proj1_sig u) (H8 u)) < proj1_sig k) with
    | left H => a (exist (fun n : nat => n < proj1_sig k) (proj1_sig (exist (fun n0 : nat => n0 < N2) (proj1_sig u) (H8 u))) H)
    | right _ => Fopp K (FI K)
  end
  | right _ =>  FO K 
end) (F2 (exist (fun n0 : nat => n0 < N2) (proj1_sig u) (H8 u)))) = (fun n : Count (proj1_sig k) => Vmul K V (a n) (F2 (exist (fun n0 : nat => n0 < N2) (proj1_sig n) (H8 n))))).
move=> H14.
rewrite H14.
simpl.
rewrite (Vadd_opp_r K V).
apply (Vadd_O_r K V (VO K V)).
apply functional_extensionality.
move=> u.
elim (excluded_middle_informative (proj1_sig (exist (fun n0 : nat => n0 < N2) (proj1_sig u) (H8 u)) <= proj1_sig k)).
move=> H14.
elim (excluded_middle_informative (proj1_sig (exist (fun n0 : nat => n0 < N2) (proj1_sig u) (H8 u)) < proj1_sig k)).
move=> H15.
suff: ((exist (fun n : nat => n < proj1_sig k) (proj1_sig (exist (fun n0 : nat => n0 < N2) (proj1_sig u) (H8 u))) H15) = u).
move=> H16.
rewrite H16.
reflexivity.
apply sig_map.
reflexivity.
move=> H15.
apply False_ind.
apply H15.
apply (proj2_sig u).
move=> H14.
apply False_ind.
apply H14.
apply (lt_le_weak (proj1_sig u) (proj1_sig k) (proj2_sig u)).
move=> u H14.
apply (Intersection_intro (Count N2)).
apply (proj2_sig u).
apply (Full_intro (Count N2)).
simpl.
move=> H14.
apply InjSurjBij.
move=> u1 u2 H15.
apply sig_map.
apply sig_map.
suff: (proj1_sig (proj1_sig u1) = proj1_sig (proj1_sig (exist (Intersection (Count N2) (fun n : Count N2 => proj1_sig n < proj1_sig k) (Full_set (Count N2))) (exist (fun n0 : nat => n0 < N2) (proj1_sig (proj1_sig u1)) (H8 (proj1_sig u1))) (H14 (proj1_sig u1) (proj2_sig u1))))).
move=> H16.
rewrite H16.
rewrite H15.
reflexivity.
reflexivity.
move=> t.
suff: (proj1_sig (proj1_sig t) < proj1_sig k).
move=> H15.
exists (exist (Full_set (Count (proj1_sig k))) (exist (fun (n : nat) => n < proj1_sig k) (proj1_sig (proj1_sig t)) H15) (Full_intro (Count (proj1_sig k)) (exist (fun (n : nat) => n < proj1_sig k) (proj1_sig (proj1_sig t)) H15))).
apply sig_map.
apply sig_map.
reflexivity.
elim (proj2_sig t).
move=> u H15 H16.
apply H15.
move=> H12.
apply False_ind.
apply H12.
apply (le_n (proj1_sig k)).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> m H11.
suff: (m = k).
move=> H12.
rewrite H12.
apply (In_singleton (Count N2)).
apply sig_map.
elim H11.
move=> u H12 H13.
elim (le_lt_or_eq (proj1_sig u) (proj1_sig k)).
move=> H14.
apply False_ind.
apply H12.
apply (Intersection_intro (Count N2)).
apply H14.
apply (Full_intro (Count N2)).
apply.
elim H13.
move=> n H14 H15.
apply H14.
move=> m H11.
apply (Intersection_intro (Count N2)).
move=> H12.
suff: (~ proj1_sig m < proj1_sig k).
move=> H13.
apply H13.
elim H12.
move=> n H14 H15.
apply H14.
elim H11.
apply (lt_irrefl (proj1_sig k)).
elim H11.
apply (Intersection_intro (Count N2)).
apply (le_n (proj1_sig k)).
apply (Full_intro (Count N2) k).
move=> u.
elim.
move=> u0 H11.
apply (Intersection_intro (Count N2)).
apply (lt_le_weak (proj1_sig u0) (proj1_sig k) H11).
move=> u.
elim.
move=> w H11 H12.
elim (excluded_middle_informative (proj1_sig w <= proj1_sig k)).
move=> H13.
apply False_ind.
apply H11.
apply (Intersection_intro (Count N2)).
apply H13.
apply (Full_intro (Count N2) w).
move=> H13.
apply (Vmul_O_l K V (F2 w)).
move=> v H11.
apply (Full_intro (Count N2) v).
elim (excluded_middle_informative (proj1_sig k <= proj1_sig k)).
move=> H10.
elim (excluded_middle_informative (proj1_sig k < proj1_sig k)).
move=> H11.
apply False_ind.
apply (lt_irrefl (proj1_sig k) H11).
move=> H11.
reflexivity.
move=> H10.
apply False_ind.
apply H10.
apply (le_n (proj1_sig k)).
exists (fun (m : {n : Count N2 | proj1_sig n < proj1_sig k}) => exist (fun (l : nat) => l < proj1_sig k) (proj1_sig (proj1_sig m)) (proj2_sig m)).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
reflexivity.
move=> m.
apply (lt_trans (proj1_sig m) (proj1_sig k) N2 (proj2_sig m) (proj2_sig k)).
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> v1 v2 H7 H8.
suff: (v1 = VO K V).
move=> H9.
rewrite H9.
rewrite (Vadd_O_l K V v2).
apply H8.
elim H7.
move=> x H9.
rewrite H9.
suff: ((exist (Finite {n : Count N1 | proj1_sig n < 0}) (fun t : {n : Count N1 | proj1_sig n < 0} => proj1_sig x t <> FO K) (proj2_sig x)) = (FiniteEmpty {n : Count N1 | proj1_sig n < 0})).
move=> H10.
rewrite H10.
apply (MySumF2Empty {n : Count N1 | proj1_sig n < 0} (VSPCM K V) (fun t : {n : Count N1 | proj1_sig n < 0} => Vmul K V (proj1_sig x t) (F1 (proj1_sig t)))).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig (proj1_sig u)) (proj2_sig u)).
move=> u.
elim.
move=> v H7.
rewrite - (Vadd_O_l K V v).
apply (SumEnsembleVS_intro K V).
suff: (SubspaceVS K V (W1 0)).
move=> H8.
apply (proj2 (proj2 H8)).
apply (SpanSubspaceVS K V).
apply H7.
apply (proj1 (proj2_sig (H4 k))).
apply (le_n_S (proj1_sig (H4 k)) N1).
apply (proj2 (proj2_sig (H4 k)) N1).
unfold In.
rewrite - (Vadd_O_r K V (F2 k)).
apply (SumEnsembleVS_intro K V).
unfold W1.
rewrite (BijectiveSaveSpanVS K V (Count N1) {n : Count N1 | proj1_sig n < N1} (fun (m : Count N1) => exist (fun (m : Count N1) => proj1_sig m < N1) m (proj2_sig m))).
simpl.
rewrite - (proj2 (proj1 (BasisLIGeVS K V (Count N1) F1) H1)).
apply (Full_intro (VT K V) (F2 k)).
exists (fun (m : {n : Count N1 | proj1_sig n < N1}) => proj1_sig m).
apply conj.
move=> x.
reflexivity.
move=> y.
apply sig_map.
reflexivity.
suff: (SubspaceVS K V (W2 (proj1_sig k))).
move=> H6.
apply (proj2 (proj2 H6)).
apply (SpanSubspaceVS K V).
move=> k.
suff: (proj1_sig (H3 k) <> O /\ proj1_sig (H3 k) < S N2).
elim (proj1_sig (H3 k)).
move=> H5.
apply constructive_definite_description.
apply False_ind.
apply (proj1 H5).
reflexivity.
move=> n H5 H6.
exists (exist (fun (k : nat) => k < N2) n (lt_S_n n N2 (proj2 H6))).
reflexivity.
apply conj.
move=> H5.
suff: (In (VT K V) (SumEnsembleVS K V (W1 (proj1_sig k)) (W2 (proj1_sig (H3 k)))) (F1 k)).
rewrite H5.
suff: (SumEnsembleVS K V (W1 (proj1_sig k)) (W2 0) = (W1 (proj1_sig k))).
move=> H6.
rewrite H6.
unfold W1.
suff: (forall (m : Count (proj1_sig k)), proj1_sig m < N1).
move=> H7.
rewrite (BijectiveSaveSpanVS K V (Count (proj1_sig k)) {n : Count N1 | proj1_sig n < proj1_sig k} (fun (m : Count (proj1_sig k)) => exist (fun (n : Count N1) => proj1_sig n < proj1_sig k) (exist (fun (n : nat) => n < N1) (proj1_sig m) (H7 m)) (proj2_sig m))).
simpl.
rewrite (FiniteSpanVS K V (proj1_sig k) (fun t : Count (proj1_sig k) => F1 (exist (fun n : nat => n < N1) (proj1_sig t) (H7 t)))).
elim.
move=> a H8.
apply (FI_neq_FO K).
rewrite - (Fopp_involutive K (FI K)).
apply (Fopp_eq_O_compat K (Fopp K (FI K))).
suff: (Fopp K (FI K) = (fun (m : Count N1) => match excluded_middle_informative (proj1_sig m <= proj1_sig k) with
  | left _ => match excluded_middle_informative (proj1_sig m < proj1_sig k) with
    | left H => a (exist (fun (n : nat) => n < proj1_sig k) (proj1_sig m) H)
    | right _ => Fopp K (FI K)
  end
  | right _ => FO K
end) k).
move=> H9.
rewrite H9.
apply (proj1 (FiniteLinearlyIndependentVS K V N1 F1) (proj1 (proj1 (BasisLIGeVS K V (Count N1) F1) H1)) (fun (m : Count N1) => match excluded_middle_informative (proj1_sig m <= proj1_sig k) with
  | left _ => match excluded_middle_informative (proj1_sig m < proj1_sig k) with
    | left H => a (exist (fun (n : nat) => n < proj1_sig k) (proj1_sig m) H)
    | right _ => Fopp K (FI K)
  end
  | right _ => FO K
end)).
rewrite (MySumF2Included (Count N1) (FiniteIntersection (Count N1) (exist (Finite (Count N1)) (Full_set (Count N1)) (CountFinite N1)) (fun (n : Count N1) => proj1_sig n <= proj1_sig k)) (exist (Finite (Count N1)) (Full_set (Count N1)) (CountFinite N1))).
rewrite (MySumF2O (Count N1) (FiniteIntersection (Count N1) (exist (Finite (Count N1)) (Full_set (Count N1)) (CountFinite N1)) (Complement (Count N1) (proj1_sig (FiniteIntersection (Count N1) (exist (Finite (Count N1)) (Full_set (Count N1)) (CountFinite N1)) (fun n : Count N1 => proj1_sig n <= proj1_sig k)))))).
rewrite (MySumF2Included (Count N1) (FiniteIntersection (Count N1) (exist (Finite (Count N1)) (Full_set (Count N1)) (CountFinite N1)) (fun n : Count N1 => proj1_sig n < proj1_sig k)) (FiniteIntersection (Count N1) (exist (Finite (Count N1)) (Full_set (Count N1)) (CountFinite N1)) (fun n : Count N1 => proj1_sig n <= proj1_sig k))).
suff: (FiniteIntersection (Count N1) (FiniteIntersection (Count N1) (exist (Finite (Count N1)) (Full_set (Count N1)) (CountFinite N1)) (fun n : Count N1 => proj1_sig n <= proj1_sig k)) (Complement (Count N1) (proj1_sig (FiniteIntersection (Count N1) (exist (Finite (Count N1)) (Full_set (Count N1)) (CountFinite N1)) (fun n : Count N1 => proj1_sig n < proj1_sig k)))) = FiniteSingleton (Count N1) k).
move=> H10.
rewrite H10.
rewrite MySumF2Singleton.
elim (excluded_middle_informative (proj1_sig k <= proj1_sig k)).
move=> H11.
elim (excluded_middle_informative (proj1_sig k < proj1_sig k)).
move=> H12.
apply False_ind.
apply (lt_irrefl (proj1_sig k) H12).
move=> H12.
rewrite (Vopp_mul_distr_l_reverse K V (FI K) (F1 k)).
rewrite (Vmul_I_l K V (F1 k)).
rewrite H8.
rewrite - (MySumF2BijectiveSame (Count (proj1_sig k)) (exist (Finite (Count (proj1_sig k))) (Full_set (Count (proj1_sig k))) (CountFinite (proj1_sig k))) (Count N1) (FiniteIntersection (Count N1) (exist (Finite (Count N1)) (Full_set (Count N1)) (CountFinite N1)) (fun n : Count N1 => proj1_sig n < proj1_sig k)) (VSPCM K V) (fun m : Count N1 => Vmul K V (match excluded_middle_informative (proj1_sig m <= proj1_sig k) with
  | left _ => match excluded_middle_informative (proj1_sig m < proj1_sig k) with
    | left H => a (exist (fun (n : nat) => n < proj1_sig k) (proj1_sig m) H)
    | right _ => Fopp K (FI K)
  end
  | right _ => FO K
end) (F1 m)) (fun n : Count (proj1_sig k) => (exist (fun n0 : nat => n0 < N1) (proj1_sig n) (H7 n)))).
suff: ((fun u : Count (proj1_sig k) => Vmul K V (match excluded_middle_informative (proj1_sig (exist (fun n0 : nat => n0 < N1) (proj1_sig u) (H7 u)) <= proj1_sig k) with
  | left _ => match excluded_middle_informative (proj1_sig (exist (fun n0 : nat => n0 < N1) (proj1_sig u) (H7 u)) < proj1_sig k) with
    | left H => a (exist (fun n : nat => n < proj1_sig k) (proj1_sig (exist (fun n0 : nat => n0 < N1) (proj1_sig u) (H7 u))) H)
    | right _ => Fopp K (FI K)
  end
  | right _ =>  FO K 
end) (F1 (exist (fun n0 : nat => n0 < N1) (proj1_sig u) (H7 u)))) = (fun n : Count (proj1_sig k) => Vmul K V (a n) (F1 (exist (fun n0 : nat => n0 < N1) (proj1_sig n) (H7 n))))).
move=> H13.
rewrite H13.
simpl.
rewrite (Vadd_opp_r K V).
apply (Vadd_O_r K V (VO K V)).
apply functional_extensionality.
move=> u.
elim (excluded_middle_informative (proj1_sig (exist (fun n0 : nat => n0 < N1) (proj1_sig u) (H7 u)) <= proj1_sig k)).
move=> H13.
elim (excluded_middle_informative (proj1_sig (exist (fun n0 : nat => n0 < N1) (proj1_sig u) (H7 u)) < proj1_sig k)).
move=> H14.
suff: ((exist (fun n : nat => n < proj1_sig k) (proj1_sig (exist (fun n0 : nat => n0 < N1) (proj1_sig u) (H7 u))) H14) = u).
move=> H15.
rewrite H15.
reflexivity.
apply sig_map.
reflexivity.
move=> H14.
apply False_ind.
apply H14.
apply (proj2_sig u).
move=> H13.
apply False_ind.
apply H13.
apply (lt_le_weak (proj1_sig u) (proj1_sig k) (proj2_sig u)).
move=> u H13.
apply (Intersection_intro (Count N1)).
apply (proj2_sig u).
apply (Full_intro (Count N1)).
simpl.
move=> H13.
apply InjSurjBij.
move=> u1 u2 H14.
apply sig_map.
apply sig_map.
suff: (proj1_sig (proj1_sig u1) = proj1_sig (proj1_sig (exist (Intersection (Count N1) (fun n : Count N1 => proj1_sig n < proj1_sig k) (Full_set (Count N1))) (exist (fun n0 : nat => n0 < N1) (proj1_sig (proj1_sig u1)) (H7 (proj1_sig u1))) (H13 (proj1_sig u1) (proj2_sig u1))))).
move=> H15.
rewrite H15.
rewrite H14.
reflexivity.
reflexivity.
move=> t.
suff: (proj1_sig (proj1_sig t) < proj1_sig k).
move=> H14.
exists (exist (Full_set (Count (proj1_sig k))) (exist (fun (n : nat) => n < proj1_sig k) (proj1_sig (proj1_sig t)) H14) (Full_intro (Count (proj1_sig k)) (exist (fun (n : nat) => n < proj1_sig k) (proj1_sig (proj1_sig t)) H14))).
apply sig_map.
apply sig_map.
reflexivity.
elim (proj2_sig t).
move=> u H14 H15.
apply H14.
move=> H11.
apply False_ind.
apply H11.
apply (le_n (proj1_sig k)).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> m H10.
suff: (m = k).
move=> H11.
rewrite H11.
apply (In_singleton (Count N1)).
apply sig_map.
elim H10.
move=> u H11 H12.
elim (le_lt_or_eq (proj1_sig u) (proj1_sig k)).
move=> H13.
apply False_ind.
apply H11.
apply (Intersection_intro (Count N1)).
apply H13.
apply (Full_intro (Count N1)).
apply.
elim H12.
move=> n H13 H14.
apply H13.
move=> m H10.
apply (Intersection_intro (Count N1)).
move=> H11.
suff: (~ proj1_sig m < proj1_sig k).
move=> H12.
apply H12.
elim H11.
move=> n H13 H14.
apply H13.
elim H10.
apply (lt_irrefl (proj1_sig k)).
elim H10.
apply (Intersection_intro (Count N1)).
apply (le_n (proj1_sig k)).
apply (Full_intro (Count N1) k).
move=> u.
elim.
move=> u0 H10.
apply (Intersection_intro (Count N1)).
apply (lt_le_weak (proj1_sig u0) (proj1_sig k) H10).
move=> u.
elim.
move=> w H10 H11.
elim (excluded_middle_informative (proj1_sig w <= proj1_sig k)).
move=> H12.
apply False_ind.
apply H10.
apply (Intersection_intro (Count N1)).
apply H12.
apply (Full_intro (Count N1) w).
move=> H12.
apply (Vmul_O_l K V (F1 w)).
move=> v H10.
apply (Full_intro (Count N1) v).
elim (excluded_middle_informative (proj1_sig k <= proj1_sig k)).
move=> H9.
elim (excluded_middle_informative (proj1_sig k < proj1_sig k)).
move=> H10.
apply False_ind.
apply (lt_irrefl (proj1_sig k) H10).
move=> H10.
reflexivity.
move=> H9.
apply False_ind.
apply H9.
apply (le_n (proj1_sig k)).
exists (fun (m : {n : Count N1 | proj1_sig n < proj1_sig k}) => exist (fun (l : nat) => l < proj1_sig k) (proj1_sig (proj1_sig m)) (proj2_sig m)).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
reflexivity.
move=> m.
apply (lt_trans (proj1_sig m) (proj1_sig k) N1 (proj2_sig m) (proj2_sig k)).
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> v1 v2 H6 H7.
suff: (v2 = VO K V).
move=> H8.
rewrite H8.
rewrite (Vadd_O_r K V v1).
apply H6.
elim H7.
move=> x H8.
rewrite H8.
suff: ((exist (Finite {n : Count N2 | proj1_sig n < 0}) (fun t : {n : Count N2 | proj1_sig n < 0} => proj1_sig x t <> FO K) (proj2_sig x)) = (FiniteEmpty {n : Count N2 | proj1_sig n < 0})).
move=> H9.
rewrite H9.
apply (MySumF2Empty {n : Count N2 | proj1_sig n < 0} (VSPCM K V) (fun t : {n : Count N2 | proj1_sig n < 0} => Vmul K V (proj1_sig x t) (F2 (proj1_sig t)))).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig (proj1_sig u)) (proj2_sig u)).
move=> u.
elim.
move=> v H6.
rewrite - (Vadd_O_r K V v).
apply (SumEnsembleVS_intro K V).
apply H6.
suff: (SubspaceVS K V (W2 0)).
move=> H7.
apply (proj2 (proj2 H7)).
apply (SpanSubspaceVS K V).
apply (proj1 (proj2_sig (H3 k))).
apply (le_n_S (proj1_sig (H3 k)) N2).
apply (proj2 (proj2_sig (H3 k)) N2).
unfold In.
rewrite - (Vadd_O_l K V (F1 k)).
apply (SumEnsembleVS_intro K V).
suff: (SubspaceVS K V (W1 (proj1_sig k))).
move=> H5.
apply (proj2 (proj2 H5)).
apply (SpanSubspaceVS K V).
unfold W2.
rewrite (BijectiveSaveSpanVS K V (Count N2) {n : Count N2 | proj1_sig n < N2} (fun (m : Count N2) => exist (fun (m : Count N2) => proj1_sig m < N2) m (proj2_sig m))).
simpl.
rewrite - (proj2 (proj1 (BasisLIGeVS K V (Count N2) F2) H2)).
apply (Full_intro (VT K V) (F1 k)).
exists (fun (m : {n : Count N2 | proj1_sig n < N2}) => proj1_sig m).
apply conj.
move=> x.
reflexivity.
move=> y.
apply sig_map.
reflexivity.
move=> k.
apply min_nat_get.
apply (Inhabited_intro nat (fun n : nat => In (VT K V) (SumEnsembleVS K V (W1 n) (W2 (proj1_sig k))) (F2 k)) N1).
unfold In.
rewrite - (Vadd_O_r K V (F2 k)).
apply (SumEnsembleVS_intro K V).
unfold W1.
rewrite (BijectiveSaveSpanVS K V (Count N1) {n : Count N1 | proj1_sig n < N1} (fun (m : Count N1) => exist (fun (m : Count N1) => proj1_sig m < N1) m (proj2_sig m))).
simpl.
rewrite - (proj2 (proj1 (BasisLIGeVS K V (Count N1) F1) H1)).
apply (Full_intro (VT K V) (F2 k)).
exists (fun (m : {n : Count N1 | proj1_sig n < N1}) => proj1_sig m).
apply conj.
move=> x.
reflexivity.
move=> y.
apply sig_map.
reflexivity.
suff: (SubspaceVS K V (W2 (proj1_sig k))).
move=> H4.
apply (proj2 (proj2 H4)).
apply (SpanSubspaceVS K V).
move=> k.
apply min_nat_get.
apply (Inhabited_intro nat (fun n : nat => In (VT K V) (SumEnsembleVS K V (W1 (proj1_sig k)) (W2 n)) (F1 k)) N2).
unfold In.
rewrite - (Vadd_O_l K V (F1 k)).
apply (SumEnsembleVS_intro K V).
suff: (SubspaceVS K V (W1 (proj1_sig k))).
move=> H5.
apply (proj2 (proj2 H5)).
apply (SpanSubspaceVS K V).
unfold W2.
rewrite (BijectiveSaveSpanVS K V (Count N2) {n : Count N2 | proj1_sig n < N2} (fun (m : Count N2) => exist (fun (m : Count N2) => proj1_sig m < N2) m (proj2_sig m))).
simpl.
rewrite - (proj2 (proj1 (BasisLIGeVS K V (Count N2) F2) H2)).
apply (Full_intro (VT K V) (F1 k)).
exists (fun (m : {n : Count N2 | proj1_sig n < N2}) => proj1_sig m).
apply conj.
move=> x.
reflexivity.
move=> y.
apply sig_map.
reflexivity.
Qed.

Definition FiniteDimensionVS (K : Field) (V : VectorSpace K) := exists (N : nat) (F : Count N -> VT K V), BasisVS K V (Count N) F.

Lemma DimensionVSsub : forall (K : Field) (V : VectorSpace K), FiniteDimensionVS K V -> {N : nat | exists (F : Count N -> VT K V), BasisVS K V (Count N) F}.
Proof.
move=> K V H1.
apply (constructive_definite_description (fun (N : nat) => exists (F : Count N -> VT K V), BasisVS K V (Count N) F)).
apply (proj1 (unique_existence (fun (N : nat) => exists (F : Count N -> VT K V), BasisVS K V (Count N) F))).
apply conj.
apply H1.
move=> N1 N2 H2 H3.
elim H2.
move=> F1 H4.
elim H3.
move=> F2 H5.
apply (Theorem_5_4 K V N1 N2 F1 F2 H4 H5).
Qed.

Definition DimensionVS (K : Field) (V : VectorSpace K) (H : FiniteDimensionVS K V) := proj1_sig (DimensionVSsub K V H).

Lemma DimensionVSNature : forall (K : Field) (V : VectorSpace K) (H : FiniteDimensionVS K V), exists (F : Count (DimensionVS K V H) -> VT K V), BasisVS K V (Count (DimensionVS K V H)) F.
Proof.
move=> K V H1.
apply (proj2_sig (DimensionVSsub K V H1)).
Qed.

Lemma DimensionVSNature2 : forall (K : Field) (V : VectorSpace K) (H : FiniteDimensionVS K V) (N : nat) (F : Count N -> VT K V), BasisVS K V (Count N) F -> (DimensionVS K V H) = N.
Proof.
move=> K V H1 N F H2.
elim (DimensionVSNature K V H1).
move=> G H3.
apply (Theorem_5_4 K V (DimensionVS K V H1) N G F H3 H2).
Qed.

Definition DimensionSubspaceVS (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H : SubspaceVS K V W) := DimensionVS K (SubspaceMakeVS K V W H).

Lemma DimensionSubspaceVSNature : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H1 : SubspaceVS K V W) (H2 : FiniteDimensionVS K (SubspaceMakeVS K V W H1)), exists (F : Count (DimensionSubspaceVS K V W H1 H2) -> VT K V), BasisSubspaceVS K V W H1 (Count (DimensionSubspaceVS K V W H1 H2)) F.
Proof.
move=> K V W H1 H2.
elim (DimensionVSNature K (SubspaceMakeVS K V W H1) H2).
move=> F H3.
exists (compose (fun (v : {w : VT K V | In (VT K V) W w}) => proj1_sig v) F).
exists (fun (m : Count (DimensionVS K (SubspaceMakeVS K V W H1) H2)) => proj2_sig (F m)).
suff: ((fun t : Count (DimensionSubspaceVS K V W H1 H2) => exist W (compose (fun v : {w : VT K V | In (VT K V) W w} => proj1_sig v) F t) (proj2_sig (F t))) = F).
move=> H4.
rewrite H4.
apply H3.
apply functional_extensionality.
move=> m.
apply sig_map.
reflexivity.
Qed.

Lemma DimensionSubspaceVSNature2 : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H1 : SubspaceVS K V W) (H2 : FiniteDimensionVS K (SubspaceMakeVS K V W H1)) (N : nat) (F : Count N -> VT K V), BasisSubspaceVS K V W H1 (Count N) F -> (DimensionSubspaceVS K V W H1 H2) = N.
Proof.
move=> K V W H1 H2 N F.
elim.
move=> H3 H4.
elim (DimensionVSNature K (SubspaceMakeVS K V W H1) H2).
move=> G H5.
apply (Theorem_5_4 K (SubspaceMakeVS K V W H1) (DimensionSubspaceVS K V W H1 H2) N G (fun t : Count N => exist W (F t) (H3 t)) H5 H4).
Qed.

Lemma FnVSDimension : forall (K : Field) (N : nat), exists (H : FiniteDimensionVS K (FnVS K N)), (DimensionVS K (FnVS K N) H) = N.
Proof.
move=> K N.
suff: (FiniteDimensionVS K (FnVS K N)).
move=> H1.
exists H1.
apply (DimensionVSNature2 K (FnVS K N) H1 N (StandardBasisVS K N) (StandardBasisNatureVS K N)).
exists N.
exists (StandardBasisVS K N).
apply (StandardBasisNatureVS K N).
Qed.

Lemma OVSDimension : forall (K : Field), exists (H : FiniteDimensionVS K (OVS K)), (DimensionVS K (OVS K) H) = O.
Proof.
move=> K.
suff: (BasisVS K (OVS K) (Count O) (fun (m : Count O) => OVSO K)).
move=> H1.
suff: (FiniteDimensionVS K (OVS K)).
move=> H2.
exists H2.
apply (DimensionVSNature2 K (OVS K) H2 O (fun (m : Count O) => OVSO K) H1).
exists O.
exists (fun (m : Count O) => OVSO K).
apply H1.
apply (proj2 (FiniteBasisVS K (OVS K) O (fun (m : Count O) => OVSO K))).
move=> v.
exists (fun (m : Count O) => FO K).
apply conj.
suff: (forall (w : VT K (OVS K)), proj1_sig w = O).
move=> H1.
apply sig_map.
rewrite H1.
rewrite H1.
reflexivity.
move=> w.
elim (le_lt_or_eq (proj1_sig w) O).
move=> H1.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig w) H1).
apply.
apply (le_S_n (proj1_sig w) O (proj2_sig w)).
move=> x H1.
apply functional_extensionality.
move=> m.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig m) (proj2_sig m)).
Qed.

Lemma VOSubspaceVSDimension : forall (K : Field) (V : VectorSpace K), exists (H : FiniteDimensionVS K (SubspaceMakeVS K V (Singleton (VT K V) (VO K V)) (VOSubspaceVS K V))), (DimensionSubspaceVS K V (Singleton (VT K V) (VO K V)) (VOSubspaceVS K V) H) = O.
Proof.
move=> K V.
suff: (BasisVS K (SubspaceMakeVS K V (Singleton (VT K V) (VO K V)) (VOSubspaceVS K V)) (Count O) (fun (m : Count O) => SubspaceMakeVSVO K V (Singleton (VT K V) (VO K V)) (VOSubspaceVS K V))).
move=> H1.
suff: (FiniteDimensionVS K (SubspaceMakeVS K V (Singleton (VT K V) (VO K V)) (VOSubspaceVS K V))).
move=> H2.
exists H2.
apply (DimensionVSNature2 K (SubspaceMakeVS K V (Singleton (VT K V) (VO K V)) (VOSubspaceVS K V)) H2 O (fun (m : Count O) => (SubspaceMakeVSVO K V (Singleton (VT K V) (VO K V)) (VOSubspaceVS K V))) H1).
exists O.
exists (fun (m : Count O) => SubspaceMakeVSVO K V (Singleton (VT K V) (VO K V)) (VOSubspaceVS K V)).
apply H1.
apply (proj2 (FiniteBasisVS K (SubspaceMakeVS K V (Singleton (VT K V) (VO K V)) (VOSubspaceVS K V)) O (fun (m : Count O) => SubspaceMakeVSVO K V (Singleton (VT K V) (VO K V)) (VOSubspaceVS K V)))).
move=> v.
exists (fun (m : Count O) => FO K).
apply conj.
apply sig_map.
rewrite MySumF2O.
elim (proj2_sig v).
reflexivity.
move=> m.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig m) (proj2_sig m)).
move=> v0 H1.
apply functional_extensionality.
move=> m.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig m) (proj2_sig m)).
Qed.

Lemma Theorem_5_6_sub : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V), GeneratingSystemVS K V (Count N) F -> BasisVS K V ({m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun (k : {n : Count N | proj1_sig n < proj1_sig m}) => F (proj1_sig k))) (F m)}) (fun (k : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)}) => F (proj1_sig k)).
Proof.
move=> K V N F H1.
suff: (forall (l : nat), l <= N -> SpanVS K V {m : Count N | proj1_sig m < l /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} (fun k : {m : Count N | proj1_sig m < l /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) = SpanVS K V {m : Count N | proj1_sig m < l} (fun k : {m : Count N | proj1_sig m < l} => F (proj1_sig k))).
move=> H2.
suff: (forall (l : nat), l <= N -> LinearlyIndependentVS K V {m : Count N | proj1_sig m < l /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} (fun k : {m : Count N | proj1_sig m < l /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))).
move=> H3.
elim (BijectiveSameSig (Count N) (fun (m : Count N) => ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)) (fun (m : Count N) => proj1_sig m < N /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m))).
move=> g H4.
suff: ((fun k : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) = (fun t : {t : Count N | In (Count N) (fun m : Count N => ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)) t} => F (proj1_sig (g t)))).
move=> H5.
rewrite H5.
apply (BijectiveSaveBasisVS K V {t : Count N | In (Count N) (fun m : Count N => ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)) t} {t : Count N | In (Count N) (fun m : Count N => proj1_sig m < N /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)) t} g (fun k : {m : Count N | proj1_sig m < N /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) (proj2 H4)).
apply BasisLIGeVS.
apply conj.
apply (H3 N (le_n N)).
unfold GeneratingSystemVS.
rewrite H1.
rewrite (H2 N (le_n N)).
apply (BijectiveSaveSpanVS K V {m : Count N | proj1_sig m < N} (Count N) (fun (k : {m : Count N | proj1_sig m < N}) => proj1_sig k) F).
exists (fun (m : Count N) => exist (fun (m : Count N) => proj1_sig m < N) m (proj2_sig m)).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
reflexivity.
apply functional_extensionality.
move=> k.
rewrite (proj1 H4 k).
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> m H4.
apply conj.
apply (proj2_sig m).
apply H4.
move=> m H4.
apply (proj2 H4).
elim.
move=> H3.
apply (LinearlyIndependentVSDef3 K V).
move=> a A H4 k.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig (proj1_sig k)) (proj1 (proj2_sig k))).
move=> n H3 H4.
elim (classic (In (VT K V) (SpanVS K V {k : Count N | proj1_sig k < n} (fun k : {k : Count N | proj1_sig k < n} => F (proj1_sig k))) (F (exist (fun (k : nat) => k < N) n H4)))).
move=> H5.
elim (BijectiveSameSig (Count N) (fun (m : Count N) => proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)) (fun (m : Count N) => proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m))).
move=> g H6.
suff: ((fun k : {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) = (fun t : {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig (g t)))).
move=> H7.
rewrite H7.
apply (BijectiveSaveLinearlyIndependentVS K V {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} g (fun k : {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))).
apply (proj2 H6).
apply (H3 (le_trans n (S n) N (le_S n n (le_n n)) H4)).
apply functional_extensionality.
move=> k.
rewrite (proj1 H6 k).
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> m H6.
apply conj.
elim (le_lt_or_eq (proj1_sig m) n (le_S_n (proj1_sig m) n (proj1 H6))).
apply.
move=> H7.
apply False_ind.
apply (proj2 H6).
rewrite H7.
suff: (m = (exist (fun k : nat => k < N) n H4)).
move=> H8.
rewrite H8.
apply H5.
apply sig_map.
apply H7.
apply (proj2 H6).
move=> m H6.
apply conj.
apply (le_S (S (proj1_sig m)) n (proj1 H6)).
apply (proj2 H6).
move=> H5.
suff: (exists (M : nat) (f : {n : nat | n < M} -> {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)}), Bijective {n : nat | n < M} {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} f).
elim.
move=> M.
elim.
move=> f H6.
suff: (proj1_sig (exist (fun k : nat => k < N) n H4) < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig (exist (fun k : nat => k < N) n H4)} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig (exist (fun k : nat => k < N) n H4)} => F (proj1_sig k))) (F (exist (fun k : nat => k < N) n H4))).
move=> H7.
elim H6.
move=> g H9.
suff: ((fun k : {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) = (fun t : {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => match excluded_middle_informative (proj1_sig match excluded_middle_informative (proj1_sig (proj1_sig t) < n) with
  | left H => exist (fun l : nat => l < S M) (proj1_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig t) (conj H (proj2 (proj2_sig t)))))) (PeanoNat.Nat.le_trans (S (proj1_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig t) (conj H (proj2 (proj2_sig t))))))) M (S M) (proj2_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k :  {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig t) (conj H (proj2 (proj2_sig t)))))) (le_S M M (le_n M)))
  | right _ => exist (fun l : nat => l < S M) M (le_n (S M))
end < M) with
  | left H => F (proj1_sig (f (exist (fun k : nat => k < M) (proj1_sig match excluded_middle_informative (proj1_sig (proj1_sig t) < n) with
    | left H0 => exist (fun l : nat => l < S M) (proj1_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig t) (conj H0 (proj2 (proj2_sig t)))))) (PeanoNat.Nat.le_trans (S (proj1_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig t) (conj H0 (proj2 (proj2_sig t))))))) M (S M) (proj2_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig t) (conj H0 (proj2 (proj2_sig t)))))) (le_S M M (le_n M)))
    | right _ => exist (fun l : nat => l < S M) M (le_n (S M))
  end) H)))
  | right _ => F (exist (fun k : nat => k < N) n H4)
end)).
move=> H10.
rewrite H10.
apply (BijectiveSaveLinearlyIndependentVS K V {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} (Count (S M)) (fun (k : {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)}) => match excluded_middle_informative (proj1_sig (proj1_sig k) < n) with
  | left H => exist (fun (l : nat) => l < S M) (proj1_sig (g (exist (fun (l : Count N) => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig k) (conj H (proj2 (proj2_sig k)))))) (le_trans (S (proj1_sig (g (exist (fun (l : Count N) => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig k) (conj H (proj2 (proj2_sig k))))))) M (S M) (proj2_sig (g (exist (fun (l : Count N) => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig k) (conj H (proj2 (proj2_sig k)))))) (le_S M M (le_n M)))
  | right _ => exist (fun (l : nat) => l < S M) M (le_n (S M))
end) (fun m : Count (S M) => match excluded_middle_informative (proj1_sig m < M) with
  | left H => F (proj1_sig (f (exist (fun k : nat => k < M) (proj1_sig m) H)))
  | right _ => F (exist (fun k : nat => k < N) n H4)
end)).
apply InjSurjBij.
move=> l1 l2.
elim (excluded_middle_informative (proj1_sig (proj1_sig l1) < n)).
move=> H11.
elim (excluded_middle_informative (proj1_sig (proj1_sig l2) < n)).
move=> H12 H13.
suff: ((exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig l1) (conj H11 (proj2 (proj2_sig l1)))) = (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig l2) (conj H12 (proj2 (proj2_sig l2))))).
move=> H14.
apply sig_map.
suff: (proj1_sig l1 = proj1_sig (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig l1) (conj H11 (proj2 (proj2_sig l1))))).
move=> H15.
rewrite H15.
rewrite H14.
reflexivity.
reflexivity.
apply (BijInj {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} {n : nat | n < M} g).
exists f.
apply conj.
apply (proj2 H9).
apply (proj1 H9).
suff: (proj1_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig l1) (conj H11 (proj2 (proj2_sig l1))))) = proj1_sig (exist (fun l : nat => l < S M) (proj1_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig l1) (conj H11 (proj2 (proj2_sig l1)))))) (PeanoNat.Nat.le_trans (S (proj1_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig l1) (conj H11 (proj2 (proj2_sig l1))))))) M (S M) (proj2_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig l1) (conj H11 (proj2 (proj2_sig l1)))))) (le_S M M (le_n M))))).
move=> H14.
apply sig_map.
rewrite H14.
rewrite H13.
reflexivity.
reflexivity.
move=> H12 H13.
apply False_ind.
suff: (~ proj1_sig (exist (fun l : nat => l < S M) M (le_n (S M))) < M).
move=> H14.
apply H14.
rewrite - H13.
simpl.
apply (proj2_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig l1) (conj H11 (proj2 (proj2_sig l1)))))).
apply (lt_irrefl M).
move=> H11.
elim (excluded_middle_informative (proj1_sig (proj1_sig l2) < n)).
move=> H12 H13.
apply False_ind.
suff: (~ proj1_sig (exist (fun l : nat => l < S M) M (le_n (S M))) < M).
move=> H14.
apply H14.
rewrite H13.
simpl.
apply (proj2_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig l2) (conj H12 (proj2 (proj2_sig l2)))))).
apply (lt_irrefl M).
move=> H12 H13.
apply sig_map.
apply sig_map.
suff: (proj1_sig (proj1_sig l1) = n).
move=> H14.
suff: (proj1_sig (proj1_sig l2) = n).
move=> H15.
rewrite H15.
apply H14.
elim (le_lt_or_eq (proj1_sig (proj1_sig l2)) n (le_S_n (proj1_sig (proj1_sig l2)) n (proj1 (proj2_sig l2)))).
move=> H15.
apply False_ind.
apply (H12 H15).
apply.
elim (le_lt_or_eq (proj1_sig (proj1_sig l1)) n (le_S_n (proj1_sig (proj1_sig l1)) n (proj1 (proj2_sig l1)))).
move=> H14.
apply False_ind.
apply (H11 H14).
apply.
move=> m.
elim (classic (proj1_sig m < M)).
move=> H11.
suff: (proj1_sig (proj1_sig (f (exist (fun k : nat => k < M) (proj1_sig m) H11))) < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig (proj1_sig (f (exist (fun k : nat => k < M) (proj1_sig m) H11)))} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig (proj1_sig (f (exist (fun k : nat => k < M) (proj1_sig m) H11)))} => F (proj1_sig k))) (F (proj1_sig (f (exist (fun k : nat => k < M) (proj1_sig m) H11))))).
move=> H12.
exists (exist (fun (m : Count N) => proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)) (proj1_sig (f (exist (fun (k : nat) => k < M) (proj1_sig m) H11))) H12).
simpl.
elim (excluded_middle_informative (proj1_sig (proj1_sig (f (exist (fun k : nat => k < M) (proj1_sig m) H11))) < n)).
move=> H13.
simpl.
suff: ((exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k))) (F l)) (proj1_sig (f (exist (fun k : nat => k < M) (proj1_sig m) H11))) (conj H13 (proj2 H12))) = (f (exist (fun k : nat => k < M) (proj1_sig m) H11))).
move=> H14.
rewrite H14.
rewrite (proj1 H9).
apply sig_map.
reflexivity.
apply sig_map.
reflexivity.
move=> H13.
apply False_ind.
apply H13.
apply (proj1 (proj2_sig (f (exist (fun k : nat => k < M) (proj1_sig m) H11)))).
apply conj.
apply le_S.
apply (proj1 (proj2_sig (f (exist (fun k : nat => k < M) (proj1_sig m) H11)))).
apply (proj2 (proj2_sig (f (exist (fun k : nat => k < M) (proj1_sig m) H11)))).
move=> H11.
exists (exist (fun (m : Count N) => proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {l : Count N | proj1_sig l < proj1_sig m} (fun k : {l : Count N | proj1_sig l < proj1_sig m} => F (proj1_sig k))) (F m)) (exist (fun k : nat => k < N) n H4) (conj (le_n (S n)) H5)).
simpl.
elim (excluded_middle_informative (n < n)).
move=> H12.
apply False_ind.
apply (lt_irrefl n H12).
move=> H12.
apply sig_map.
elim (le_lt_or_eq (proj1_sig m) M (le_S_n (proj1_sig m) M (proj2_sig m))).
move=> H13.
apply False_ind.
apply (H11 H13).
move=> H13.
rewrite H13.
reflexivity.
elim (Proposition_5_2_exists K V M).
move=> H11.
elim.
move=> H12 H13.
apply H13.
apply conj.
suff: ((fun m : Count M => match excluded_middle_informative (proj1_sig (exist (fun n0 : nat => n0 < S M) (proj1_sig m) (H11 m)) < M) with
  | left H => F (proj1_sig (f (exist (fun k : nat => k < M) (proj1_sig (exist (fun n0 : nat => n0 < S M) (proj1_sig m) (H11 m))) H)))
  | right _ => F (exist (fun k : nat => k < N) n H4)
end) = (fun t : Count M => F (proj1_sig (f t)))).
move=> H14.
rewrite H14.
apply (BijectiveSaveLinearlyIndependentVS K V (Count M) {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} f (fun k : {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))).
apply H6.
apply H3.
apply (le_trans n (S n) N (le_S n n (le_n n)) H4).
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (proj1_sig (exist (fun n0 : nat => n0 < S M) (proj1_sig m) (H11 m)) < M)).
move=> H14.
suff: ((exist (fun k : nat => k < M) (proj1_sig (exist (fun n0 : nat => n0 < S M) (proj1_sig m) (H11 m))) H14) = m).
move=> H15.
rewrite H15.
reflexivity.
apply sig_map.
reflexivity.
move=> H14.
apply False_ind.
apply (H14 (proj2_sig m)).
simpl.
elim (excluded_middle_informative (M < M)).
move=> H14.
apply False_ind.
apply (lt_irrefl M H14).
move=> H14.
suff: ((fun m : Count M => match excluded_middle_informative (proj1_sig m < M) with
  | left H => F (proj1_sig (f (exist (fun k : nat => k < M) (proj1_sig m) H)))
  | right _ => F (exist (fun k : nat => k < N) n H4)
end) = (fun t : Count M => F (proj1_sig (f t)))).
move=> H15.
rewrite H15.
rewrite - (BijectiveSaveSpanVS K V (Count M) {l : Count N | proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {m : Count N | proj1_sig m < proj1_sig l} (fun k : {m : Count N | proj1_sig m < proj1_sig l} => F (proj1_sig k))) (F l)} f (fun k : {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {l : Count N | proj1_sig l < proj1_sig m} (fun k : {l : Count N | proj1_sig l < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))).
rewrite (H2 n).
apply H5.
apply (le_trans n (S n) N (le_S n n (le_n n)) H4).
apply H6.
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (proj1_sig m < M)).
move=> H15.
suff: ((exist (fun k : nat => k < M) (proj1_sig m) H15) = m).
move=> H16.
rewrite H16.
reflexivity.
apply sig_map.
reflexivity.
move=> H15.
apply False_ind.
apply (H15 (proj2_sig m)).
apply functional_extensionality.
move=> k.
elim (excluded_middle_informative (proj1_sig (proj1_sig k) < n)).
move=> H10.
simpl.
elim (excluded_middle_informative (proj1_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k0 : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k0))) (F l)) (proj1_sig k) (conj H10 (proj2 (proj2_sig k))))) < M)).
move=> H11.
suff: ((exist (fun k0 : nat => k0 < M) (proj1_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k0 : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k0))) (F l)) (proj1_sig k) (conj H10 (proj2 (proj2_sig k)))))) H11) = (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k0 : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k0))) (F l)) (proj1_sig k) (conj H10 (proj2 (proj2_sig k)))))).
move=> H12.
rewrite H12.
rewrite (proj2 H9).
reflexivity.
apply sig_map.
reflexivity.
move=> H11.
apply False_ind.
apply H11.
apply (proj2_sig (g (exist (fun l : Count N => proj1_sig l < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig l} (fun k0 : {n0 : Count N | proj1_sig n0 < proj1_sig l} => F (proj1_sig k0))) (F l)) (proj1_sig k) (conj H10 (proj2 (proj2_sig k)))))).
move=> H10.
elim (excluded_middle_informative (proj1_sig (exist (fun l : nat => l < S M) M (le_n (S M))) < M)).
move=> H11.
apply False_ind.
apply (lt_irrefl M H11).
move=> H11.
elim (le_lt_or_eq (proj1_sig (proj1_sig k)) n).
move=> H12.
apply False_ind.
apply (H10 H12).
move=> H12.
suff: ((proj1_sig k) = (exist (fun k0 : nat => k0 < N) n H4)).
move=> H13.
rewrite H13.
reflexivity.
apply sig_map.
apply H12.
apply (le_S_n (proj1_sig (proj1_sig k)) n (proj1 (proj2_sig k))).
apply conj.
apply (le_n (S n)).
apply H5.
apply CountFiniteBijective.
apply (FiniteSigSame (Count N)).
apply (Finite_downward_closed (Count N) (Full_set (Count N)) (CountFinite N)).
move=> m H6.
apply (Full_intro (Count N) m).
elim.
move=> H2.
elim (BijectiveSameSig (Count N) (fun (m : Count N) => proj1_sig m < O) (fun (m : Count N) => proj1_sig m < 0 /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m))).
move=> G H3.
suff: ((fun k : {m : Count N | proj1_sig m < 0} => F (proj1_sig k)) = (compose (fun k : {m : Count N | proj1_sig m < 0 /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) G)).
move=> H4.
rewrite H4.
apply (BijectiveSaveSpanVS K V {m : Count N | proj1_sig m < 0} {m : Count N | proj1_sig m < 0 /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} G).
apply (proj2 H3).
apply functional_extensionality.
move=> k.
unfold compose.
rewrite (proj1 H3).
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> m H3.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig m) H3).
move=> m H3.
apply (proj1 H3).
move=> n H2 H3.
elim (classic (In (VT K V) (SpanVS K V {m : Count N | proj1_sig m < n} (fun k : {m : Count N | proj1_sig m < n} => F (proj1_sig k))) (F (exist (fun (k : nat) => k < N) n H3)))).
move=> H4.
suff: (SpanVS K V {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} (fun k : {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) = SpanVS K V {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} (fun k : {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))).
move=> H5.
rewrite H5.
rewrite H2.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> x H6.
rewrite H6.
suff: (SubspaceVS K V (SpanVS K V {m : Count N | proj1_sig m < S n} (fun k : {m : Count N | proj1_sig m < S n} => F (proj1_sig k)))).
move=> H7.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 H7)).
move=> cm u H8 H9.
apply (proj1 H7 cm (Vmul K V (proj1_sig x u) (F (proj1_sig u))) H9).
apply (proj1 (proj2 H7) (proj1_sig x u)).
suff: (proj1_sig u = proj1_sig (exist (fun (m : Count N) => proj1_sig m < S n) (proj1_sig u) (le_S (S (proj1_sig (proj1_sig u))) n (proj2_sig u)))).
move=> H10.
rewrite H10.
apply (SpanContainSelfVS K V {m : Count N | proj1_sig m < S n} (fun k : {m : Count N | proj1_sig m < S n} => F (proj1_sig k)) (exist (fun m : Count N => proj1_sig m < S n) (proj1_sig u) (le_S (S (proj1_sig (proj1_sig u))) n (proj2_sig u)))).
reflexivity.
apply (SpanSubspaceVS K V).
move=> v.
elim.
move=> x H6.
rewrite H6.
suff: (SubspaceVS K V (SpanVS K V {m : Count N | proj1_sig m < n} (fun k : {m : Count N | proj1_sig m < n} => F (proj1_sig k)))).
move=> H7.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 H7)).
move=> cm u H8 H9.
apply (proj1 H7 cm (Vmul K V (proj1_sig x u) (F (proj1_sig u))) H9).
apply (proj1 (proj2 H7) (proj1_sig x u)).
elim (le_lt_or_eq (proj1_sig (proj1_sig u)) n).
move=> H10.
suff: (proj1_sig u = proj1_sig (exist (fun (m : Count N) => proj1_sig m < n) (proj1_sig u) H10)).
move=> H11.
rewrite H11.
apply (SpanContainSelfVS K V {m : Count N | proj1_sig m < n} (fun k : {m : Count N | proj1_sig m < n} => F (proj1_sig k)) (exist (fun m : Count N => proj1_sig m < n) (proj1_sig u) H10)).
reflexivity.
move=> H10.
suff: (proj1_sig u = (exist (fun k : nat => k < N) n H3)).
move=> H11.
rewrite H11.
apply H4.
apply sig_map.
apply H10.
apply (le_S_n (proj1_sig (proj1_sig u)) n (proj2_sig u)).
apply (SpanSubspaceVS K V).
apply (le_trans n (S n) N (le_S n n (le_n n)) H3).
elim (BijectiveSameSig (Count N) (fun (m : Count N) => proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)) (fun (m : Count N) => proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m))).
move=> G H5.
suff: ((fun k : {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) = (fun t : {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig (G t)))).
move=> H6.
rewrite H6.
apply (BijectiveSaveSpanVS K V {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} G (fun k : {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))).
apply (proj2 H5).
apply functional_extensionality.
move=> k.
rewrite (proj1 H5 k).
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> m H5.
apply conj.
apply (le_S (S (proj1_sig m)) n (proj1 H5)).
apply (proj2 H5).
move=> m H5.
apply conj.
elim (le_lt_or_eq (proj1_sig m) n).
apply.
move=> H6.
apply False_ind.
apply (proj2 H5).
rewrite H6.
suff: (m = (exist (fun k : nat => k < N) n H3)).
move=> H7.
rewrite H7.
apply H4.
apply sig_map.
apply H6.
apply (le_S_n (proj1_sig m) n (proj1 H5)).
apply (proj2 H5).
move=> H4.
suff: (SpanVS K V {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} (fun k : {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) = SumEnsembleVS K V (SpanVS K V {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} (fun k : {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))) (fun (v : VT K V) => exists (f : FT K), v = Vmul K V f (F (exist (fun (l : nat) => l < N) n H3)))).
move=> H5.
rewrite H5.
rewrite H2.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> v1 v2 H6 H7.
suff: (SubspaceVS K V (SpanVS K V {m : Count N | proj1_sig m < S n} (fun k : {m : Count N | proj1_sig m < S n} => F (proj1_sig k)))).
move=> H8.
apply (proj1 H8 v1 v2).
elim H6.
move=> x H9.
rewrite H9.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 H8)).
move=> cm u H10 H11.
apply (proj1 H8 cm).
apply H11.
apply (proj1 (proj2 H8)).
suff: (proj1_sig u = proj1_sig (exist (fun (m : Count N) => proj1_sig m < S n) (proj1_sig u) (le_S (S (proj1_sig (proj1_sig u))) n (proj2_sig u)))).
move=> H12.
rewrite H12.
apply (SpanContainSelfVS K V {m : Count N | proj1_sig m < S n} (fun k : {m : Count N | proj1_sig m < S n} => F (proj1_sig k)) (exist (fun (m : Count N) => proj1_sig m < S n) (proj1_sig u) (le_S (S (proj1_sig (proj1_sig u))) n (proj2_sig u)))).
reflexivity.
elim H7.
move=> f H9.
rewrite H9.
apply (proj1 (proj2 H8)).
suff: ((exist (fun l : nat => l < N) n H3) = proj1_sig (exist (fun (m : Count N) => proj1_sig m < S n) (exist (fun l : nat => l < N) n H3) (le_n (S n)))).
move=> H10.
rewrite H10.
apply (SpanContainSelfVS K V {m : Count N | proj1_sig m < S n} (fun k : {m : Count N | proj1_sig m < S n} => F (proj1_sig k)) (exist (fun (m : Count N) => proj1_sig m < S n) (exist (fun l : nat => l < N) n H3) (le_n (S n)))).
reflexivity.
apply (SpanSubspaceVS K V).
move=> v.
elim.
move=> x H6.
rewrite H6.
suff: (SubspaceVS K V (SumEnsembleVS K V (SpanVS K V {m : Count N | proj1_sig m < n} (fun k : {m : Count N | proj1_sig m < n} => F (proj1_sig k))) (fun v0 : VT K V => exists f : FT K, v0 = Vmul K V f (F (exist (fun l : nat => l < N) n H3))))).
move=> H7.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 H7)).
move=> cm u H8 H9.
apply (proj1 H7).
apply H9.
apply (proj1 (proj2 H7)).
elim (le_lt_or_eq (proj1_sig (proj1_sig u)) n).
move=> H10.
rewrite - (Vadd_O_r K V (F (proj1_sig u))).
apply SumEnsembleVS_intro.
suff: ((proj1_sig u) = proj1_sig (exist (fun (m : Count N) => proj1_sig m < n) (proj1_sig u) H10)).
move=> H11.
rewrite H11.
apply (SpanContainSelfVS K V {m : Count N | proj1_sig m < n} (fun k : {m : Count N | proj1_sig m < n} => F (proj1_sig k)) (exist (fun (m : Count N) => proj1_sig m < n) (proj1_sig u) H10)).
reflexivity.
exists (FO K).
rewrite (Vmul_O_l K V).
reflexivity.
move=> H10.
rewrite - (Vadd_O_l K V (F (proj1_sig u))).
apply SumEnsembleVS_intro.
suff: (SubspaceVS K V (SpanVS K V {m : Count N | proj1_sig m < n} (fun k : {m : Count N | proj1_sig m < n} => F (proj1_sig k)))).
move=> H11.
apply (proj2 (proj2 H11)).
apply (SpanSubspaceVS K V).
exists (FI K).
rewrite (Vmul_I_l K V (F (exist (fun l : nat => l < N) n H3))).
suff: (proj1_sig u = (exist (fun l : nat => l < N) n H3)).
move=> H11.
rewrite H11.
reflexivity.
apply sig_map.
apply H10.
apply (le_S_n (proj1_sig (proj1_sig u)) n (proj2_sig u)).
apply (SumSubspaceVS K V).
apply (SpanSubspaceVS K V).
apply (SingleSubspaceVS K V).
apply (le_trans n (S n) N (le_S n n (le_n n)) H3).
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> x H5.
rewrite H5.
suff: (SubspaceVS K V (SumEnsembleVS K V (SpanVS K V {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} (fun k : {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))) (fun v0 : VT K V => exists f : FT K, v0 = Vmul K V f (F (exist (fun l : nat => l < N) n H3))))).
move=> H6.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 H6)).
move=> cm u H7 H8.
apply (proj1 H6 cm).
apply H8.
apply (proj1 (proj2 H6) (proj1_sig x u) (F (proj1_sig u))).
elim (le_lt_or_eq (proj1_sig (proj1_sig u)) n).
move=> H9.
rewrite - (Vadd_O_r K V (F (proj1_sig u))).
apply SumEnsembleVS_intro.
suff: ((proj1_sig u) = proj1_sig (exist (fun (m : Count N) => proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)) (proj1_sig u) (conj H9 (proj2 (proj2_sig u))))).
move=> H10.
rewrite H10.
apply (SpanContainSelfVS K V {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} (fun k : {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) (exist (fun (m : Count N) => proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)) (proj1_sig u) (conj H9 (proj2 (proj2_sig u))))).
reflexivity.
exists (FO K).
rewrite (Vmul_O_l K V).
reflexivity.
move=> H9.
rewrite - (Vadd_O_l K V (F (proj1_sig u))).
apply SumEnsembleVS_intro.
apply (proj2 (proj2 (SpanSubspaceVS K V {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} (fun k : {m : Count N | proj1_sig m < n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))))).
exists (FI K).
rewrite (Vmul_I_l K V).
suff: (proj1_sig u = exist (fun l : nat => l < N) n H3).
move=> H10.
rewrite H10.
reflexivity.
apply sig_map.
apply H9.
apply (le_S_n (proj1_sig (proj1_sig u)) n (proj1 (proj2_sig u))).
apply (SumSubspaceVS K V).
apply (SpanSubspaceVS K V).
apply (SingleSubspaceVS K V).
move=> v.
elim.
move=> v1 v2 H5 H6.
suff: (SubspaceVS K V (SpanVS K V {m : Count N | proj1_sig m < S n /\  ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} (fun k : {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)))).
move=> H7.
apply (proj1 H7 v1 v2).
elim H5.
move=> x H8.
rewrite H8.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 H7)).
move=> cm u H9 H10.
apply (proj1 H7 cm).
apply H10.
apply (proj1 (proj2 H7) (proj1_sig x u) (F (proj1_sig u))).
suff: (proj1_sig u = proj1_sig (exist (fun (m : Count N) => proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)) (proj1_sig u) (conj (le_S (S (proj1_sig (proj1_sig u))) n (proj1 (proj2_sig u))) (proj2 (proj2_sig u))))).
move=> H11.
rewrite H11.
apply (SpanContainSelfVS K V {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} (fun k : {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) (exist (fun m : Count N => proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)) (proj1_sig u) (conj (le_S (S (proj1_sig (proj1_sig u))) n (proj1 (proj2_sig u))) (proj2 (proj2_sig u))))).
reflexivity.
elim H6.
move=> f H8.
rewrite H8.
apply (proj1 (proj2 H7) f).
suff: ((exist (fun l : nat => l < N) n H3) = proj1_sig (exist (fun (m : Count N) => proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)) (exist (fun l : nat => l < N) n H3) (conj (le_n (S n)) H4))).
move=> H9.
rewrite H9.
apply (SpanContainSelfVS K V {m : Count N | proj1_sig m < S n /\ ~ In (VT K V)  (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} (fun k : {m : Count N | proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) (exist (fun (m : Count N) => proj1_sig m < S n /\ ~ In (VT K V) (SpanVS K V {n0 : Count N | proj1_sig n0 < proj1_sig m} (fun k : {n0 : Count N | proj1_sig n0 < proj1_sig m} => F (proj1_sig k))) (F m)) (exist (fun l : nat => l < N) n H3) (conj (le_n (S n)) H4))).
reflexivity.
apply (SpanSubspaceVS K V).
Qed.

Lemma Theorem_5_6 : forall (K : Field) (V : VectorSpace K) (M N : nat), M <= N -> forall (H : forall (m : Count M), proj1_sig m < N) (F : Count N -> VT K V), LinearlyIndependentVS K V (Count M) (fun (m : Count M) => F (exist (fun (n : nat) => n < N) (proj1_sig m) (H m))) -> GeneratingSystemVS K V (Count N) F -> BasisVS K V {m : Count N | proj1_sig m < M \/ (M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m))} (fun (k : {m : Count N | proj1_sig m < M \/ (M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m))}) => F (proj1_sig k)).
Proof.
move=> K V M N H1 H2 F H3 H4.
elim (BijectiveSameSig (Count N) (fun (m : Count N) => proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)) (fun (m : Count N) => ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m))).
move=> G H5.
suff: ((fun k : {m : Count N | proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) = compose (fun k : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) G).
move=> H6.
rewrite H6.
apply (BijectiveSaveBasisVS K V {m : Count N | proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} {t : Count N | In (Count N) (fun m : Count N => ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)) t} G (fun k : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))).
apply (proj2 H5).
apply (Theorem_5_6_sub K V N F H4).
apply functional_extensionality.
move=> m.
unfold compose.
rewrite (proj1 H5 m).
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> m.
elim.
move=> H5.
suff: (forall (k : (Count (proj1_sig m))), proj1_sig k < N).
move=> H6.
unfold In.
rewrite (BijectiveSaveSpanVS K V (Count (proj1_sig m)) {n : Count N | proj1_sig n < proj1_sig m} (fun (k : (Count (proj1_sig m))) => exist (fun (l : Count N) => proj1_sig l < proj1_sig m) (exist (fun (l : nat) => l < N) (proj1_sig k) (H6 k)) (proj2_sig k))).
elim (Proposition_5_2_exists K V (proj1_sig m)).
move=> H7.
elim.
move=> H8 H9.
simpl.
suff: (forall (k : (Count (S (proj1_sig m)))), proj1_sig k < N).
move=> H10.
suff: ((fun t : Count (proj1_sig m) => F (exist (fun l : nat => l < N) (proj1_sig t) (H6 t))) = (fun m0 : Count (proj1_sig m) => F (exist (fun l : nat => l < N) (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H7 m0))) (H10 (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m0) (H7 m0)))))).
move=> H11.
unfold compose.
rewrite H11.
suff: (m = (exist (fun l : nat => l < N) (proj1_sig (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H8)) (H10 (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig m) H8)))).
move=> H12.
rewrite {8} H12.
apply (H9 (fun (k : (Count (S (proj1_sig m)))) => F (exist (fun (l : nat) => l < N) (proj1_sig k) (H10 k)))).
suff: (forall (k : (Count (S (proj1_sig m)))), proj1_sig k < M).
move=> H13.
suff: ((fun k : Count (S (proj1_sig m)) => F (exist (fun l : nat => l < N) (proj1_sig k) (H10 k))) = (fun t : Count (S (proj1_sig m)) => F (exist (fun n : nat => n < N) (proj1_sig (exist (fun l : nat => l < M) (proj1_sig t) (H13 t))) (H2 (exist (fun l : nat => l < M) (proj1_sig t) (H13 t)))))).
move=> H14.
rewrite H14.
apply (InjectiveSaveLinearlyIndependentVS K V (Count (S (proj1_sig m))) (Count M) (fun k : Count (S (proj1_sig m)) => (exist (fun l : nat => l < M) (proj1_sig k) (H13 k))) (fun m : Count M => F (exist (fun n : nat => n < N) (proj1_sig m) (H2 m)))).
move=> n1 n2 H15.
apply sig_map.
suff: (proj1_sig n1 = proj1_sig (exist (fun l : nat => l < M) (proj1_sig n1) (H13 n1))).
move=> H16.
rewrite H16.
rewrite H15.
reflexivity.
reflexivity.
apply H3.
apply functional_extensionality.
move=> k.
suff: ((exist (fun l : nat => l < N) (proj1_sig k) (H10 k)) = (exist (fun n : nat => n < N) (proj1_sig (exist (fun l : nat => l < M) (proj1_sig k) (H13 k))) (H2 (exist (fun l : nat => l < M) (proj1_sig k) (H13 k))))).
move=> H14.
rewrite H14.
reflexivity.
apply sig_map.
reflexivity.
move=> k.
apply (le_trans (S (proj1_sig k)) (S (proj1_sig m)) M (proj2_sig k) H5).
apply sig_map.
reflexivity.
apply functional_extensionality.
move=> k.
simpl.
suff: (H6 k = H10 (exist (fun n : nat => n < S (proj1_sig m)) (proj1_sig k) (H7 k))).
move=> H11.
rewrite H11.
reflexivity.
apply proof_irrelevance.
move=> k.
apply (le_trans (S (proj1_sig k)) (S (proj1_sig m)) N (proj2_sig k) (proj2_sig m)).
exists (fun (l : {n : Count N | proj1_sig n < proj1_sig m}) => exist (fun (k : nat) => k < proj1_sig m) (proj1_sig (proj1_sig l)) (proj2_sig l)).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
reflexivity.
move=> k.
apply (lt_trans (proj1_sig k) (proj1_sig m) N (proj2_sig k) (proj2_sig m)).
move=> H5.
apply (proj2 H5).
move=> m H5.
elim (le_or_lt M (proj1_sig m)).
move=> H6.
right.
apply conj.
apply H6.
apply H5.
move=> H6.
left.
apply H6.
Qed.

Lemma Theorem_5_6_exists : forall (K : Field) (V : VectorSpace K) (M N : nat), M <= N -> exists (H : forall (m : Count M), proj1_sig m < N), forall (F : Count N -> VT K V), LinearlyIndependentVS K V (Count M) (fun (m : Count M) => F (exist (fun (n : nat) => n < N) (proj1_sig m) (H m))) -> GeneratingSystemVS K V (Count N) F -> BasisVS K V {m : Count N | proj1_sig m < M \/ (M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m))} (fun (k : {m : Count N | proj1_sig m < M \/ (M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m))}) => F (proj1_sig k)).
Proof.
move=> K V M N H1.
suff: (forall m : Count M, proj1_sig m < N).
move=> H2.
exists H2.
apply (Theorem_5_6 K V M N H1 H2).
move=> m.
apply (le_trans (S (proj1_sig m)) M N (proj2_sig m) H1).
Qed.

Lemma Corollary_5_7_1 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V), GeneratingSystemVS K V (Count N) F -> FiniteDimensionVS K V.
Proof.
move=> K V N F H1.
suff: (BasisVS K V {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} (fun k : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))).
move=> H2.
elim (proj2 (CountFiniteBijective {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)})).
move=> M.
elim.
move=> G H3.
exists M.
exists (compose (fun k : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) G).
apply (BijectiveSaveBasisVS K V (Count M) {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} G (fun k : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))).
apply H3.
apply H2.
apply (FiniteSigSame (Count N)).
apply (Finite_downward_closed (Count N) (Full_set (Count N)) (CountFinite N)).
move=> m H3.
apply (Full_intro (Count N) m).
apply (Theorem_5_6_sub K V N F H1).
Qed.

Lemma Corollary_5_7_2 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V), GeneratingSystemVS K V (Count N) F -> forall (H : FiniteDimensionVS K V), DimensionVS K V H <= N.
Proof.
move=> K V N F H1 H2.
suff: (BasisVS K V {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} (fun k : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))).
move=> H3.
elim (proj2 (CountFiniteBijective {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)})).
move=> M.
elim.
move=> G H4.
rewrite (DimensionVSNature2 K V H2 M (compose (fun k : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) G)).
elim (CountCardinalInjective {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} N (fun (k : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)}) => proj1_sig k)).
move=> M2 H5.
rewrite - (cardinal_is_functional {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} (Full_set {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)}) M2 (proj2 H5) (Full_set {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)}) M).
apply (proj1 H5).
apply CountCardinalBijective.
exists G.
apply H4.
reflexivity.
move=> k1 k2.
apply sig_map.
apply (BijectiveSaveBasisVS K V (Count M) {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} G (fun k : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))).
apply H4.
apply H3.
apply (FiniteSigSame (Count N)).
apply (Finite_downward_closed (Count N) (Full_set (Count N)) (CountFinite N)).
move=> m H4.
apply (Full_intro (Count N) m).
apply (Theorem_5_6_sub K V N F H1).
Qed.

Lemma Corollary_5_7_2_exists : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V), GeneratingSystemVS K V (Count N) F -> exists (H : FiniteDimensionVS K V), DimensionVS K V H <= N.
Proof.
move=> K V N F H1.
exists (Corollary_5_7_1 K V N F H1).
apply (Corollary_5_7_2 K V N F H1 (Corollary_5_7_1 K V N F H1)).
Qed.

Lemma Corollary_5_7_3 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V) (H : FiniteDimensionVS K V), LinearlyIndependentVS K V (Count N) F -> DimensionVS K V H >= N.
Proof.
move=> K V N F H1 H2.
elim H1.
move=> M.
elim.
move=> G H3.
suff: (forall (m : Count (N + M)), ~ (proj1_sig m < N) -> (proj1_sig m - N) < M).
move=> H4.
suff: (GeneratingSystemVS K V (Count (N + M)) (fun (m : Count (N + M)) => match excluded_middle_informative (proj1_sig m < N) with 
  | left H => F (exist (fun (k : nat) => k < N) (proj1_sig m) H)
  | right H => G (exist (fun (k : nat) => k < M) (proj1_sig m - N) (H4 m H))
end)).
move=> H5.
elim (Theorem_5_6_exists K V N (N + M)).
move=> H6 H7.
suff: (let T := {m : Count (N + M) | proj1_sig m < N \/ N <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m} => match excluded_middle_informative (proj1_sig (proj1_sig k) < N) with
  | left H => F (exist (fun k0 : nat => k0 < N) (proj1_sig (proj1_sig k)) H)
  | right H => G (exist (fun k0 : nat => k0 < M) (proj1_sig (proj1_sig k) - N) (H4 (proj1_sig k) H))
end)) match excluded_middle_informative (proj1_sig m < N) with
  | left H => F (exist (fun k : nat => k < N) (proj1_sig m) H)
  | right H => G (exist (fun k : nat => k < M) (proj1_sig m - N) (H4 m H))
end} in let F2 := (fun k : {m : Count (N + M) | proj1_sig m < N \/ N <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m} => match excluded_middle_informative (proj1_sig (proj1_sig k) < N) with
  | left H => F (exist (fun k0 : nat => k0 < N) (proj1_sig (proj1_sig k)) H)
  | right H => G (exist (fun k0 : nat => k0 < M) (proj1_sig (proj1_sig k) - N) (H4 (proj1_sig k) H))
end)) match excluded_middle_informative (proj1_sig m < N) with
  | left H => F (exist (fun k : nat => k < N) (proj1_sig m) H)
  | right H => G (exist (fun k : nat => k < M) (proj1_sig m - N) (H4 m H))
end} => match excluded_middle_informative (proj1_sig (proj1_sig k) < N) with
  | left H => F (exist (fun k0 : nat => k0 < N) (proj1_sig (proj1_sig k)) H)
  | right H => G (exist (fun k0 : nat => k0 < M) (proj1_sig (proj1_sig k) - N) (H4 (proj1_sig k) H))
end) in DimensionVS K V H1 >= N).
apply.
move=> T F2.
suff: (BasisVS K V T F2).
move=> H8.
elim (proj2 (CountFiniteBijective T)).
move=> L.
elim.
move=> g H9.
elim H9.
move=> ginv H10.
rewrite (DimensionVSNature2 K V H1 L (compose F2 g)).
suff: (forall (m : (Count N)), proj1_sig m < N + M).
move=> H11.
suff: ({F3 : Count N -> T | Injective (Count N) T F3}).
move=> H12.
elim (CountCardinalInjective (Count N) L (compose ginv (proj1_sig H12))).
move=> N2 H13.
rewrite - (cardinal_is_functional (Count N) (Full_set (Count N)) N2 (proj2 H13) (Full_set (Count N)) N).
apply (proj1 H13).
apply (proj1 (CountCardinalBijective (Count N) N)).
exists (fun (m : Count N) => m).
exists (fun (m : Count N) => m).
apply conj.
move=> x.
reflexivity.
move=> y.
reflexivity.
reflexivity.
apply (InjChain (Count N) T (Count L) (proj1_sig H12) ginv).
apply (proj2_sig H12).
apply (BijInj T (Count L) ginv).
exists g.
apply conj.
apply (proj2 H10).
apply (proj1 H10).
suff: (forall (m : (Count N)), proj1_sig m < N + M).
move=> H12.
suff: (forall (k : (Count N)), In (Count (N + M)) (fun (m : Count (N + M)) => proj1_sig m < N \/ N <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m} => match excluded_middle_informative (proj1_sig (proj1_sig k) < N) with
  | left H => F (exist (fun k0 : nat => k0 < N) (proj1_sig (proj1_sig k)) H)
  | right H => G (exist (fun k0 : nat => k0 < M) (proj1_sig (proj1_sig k) - N) (H4 (proj1_sig k) H))
end)) match excluded_middle_informative (proj1_sig m < N) with
  | left H => F (exist (fun k : nat => k < N) (proj1_sig m) H)
  | right H => G (exist (fun k : nat => k < M) (proj1_sig m - N) (H4 m H))
end) (exist (fun (m : nat) => m < N + M) (proj1_sig k) (H12 k))).
move=> H13.
exists (fun (k : Count N) => exist (fun (m : Count (N + M)) => proj1_sig m < N \/ N <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m} => match excluded_middle_informative (proj1_sig (proj1_sig k) < N) with
  | left H => F (exist (fun k0 : nat => k0 < N) (proj1_sig (proj1_sig k)) H)
  | right H => G (exist (fun k0 : nat => k0 < M) (proj1_sig (proj1_sig k) - N) (H4 (proj1_sig k) H))
end)) match excluded_middle_informative (proj1_sig m < N) with
  | left H => F (exist (fun k : nat => k < N) (proj1_sig m) H)
  | right H => G (exist (fun k : nat => k < M) (proj1_sig m - N) (H4 m H))
end) (exist (fun (m : nat) => m < N + M) (proj1_sig k) (H12 k)) (H13 k)).
move=> k1 k2 H14.
apply sig_map.
suff: (proj1_sig k1 = proj1_sig (proj1_sig (exist (fun m : Count (N + M) => proj1_sig m < N \/ N <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m} => match excluded_middle_informative (proj1_sig (proj1_sig k) < N) with
  | left H => F (exist (fun k0 : nat => k0 < N) (proj1_sig (proj1_sig k)) H)
  | right H => G (exist (fun k0 : nat => k0 < M) (proj1_sig (proj1_sig k) - N) (H4 (proj1_sig k) H))
end)) match excluded_middle_informative (proj1_sig m < N) with
  | left H => F (exist (fun k : nat => k < N) (proj1_sig m) H)
  | right H => G (exist (fun k : nat => k < M) (proj1_sig m - N) (H4 m H))
end) (exist (fun m : nat => m < N + M) (proj1_sig k1) (H12 k1)) (H13 k1)))).
move=> H15.
rewrite H15.
rewrite H14.
reflexivity.
reflexivity.
move=> k.
left.
apply (proj2_sig k).
apply H11.
move=> m.
apply (le_trans (S (proj1_sig m)) N (N + M) (proj2_sig m) (Plus.le_plus_l N M)).
apply (BijectiveSaveBasisVS K V (Count L) T g F2).
apply H9.
apply H8.
apply (FiniteSigSame (Count (N + M))).
apply (Finite_downward_closed (Count (N + M)) (Full_set (Count (N + M))) (CountFinite (N + M))).
move=> m H9.
apply (Full_intro (Count (N + M)) m).
apply (H7 (fun (m : Count (N + M)) => match excluded_middle_informative (proj1_sig m < N) with 
  | left H => F (exist (fun (k : nat) => k < N) (proj1_sig m) H)
  | right H => G (exist (fun (k : nat) => k < M) (proj1_sig m - N) (H4 m H))
end)).
suff: ((fun m : Count N => match excluded_middle_informative (proj1_sig (exist (fun n : nat => n < N + M) (proj1_sig m) (H6 m)) < N) with
   | left H => F (exist (fun k : nat => k < N) (proj1_sig (exist (fun n : nat => n < N + M) (proj1_sig m) (H6 m))) H)
   | right H => G (exist (fun k : nat => k < M) (proj1_sig (exist (fun n0 : nat => n0 < N + M) (proj1_sig m) (H6 m)) - N) (H4 (exist (fun n0 : nat => n0 < N + M) (proj1_sig m) (H6 m)) H))
end) = F).
move=> H8.
rewrite H8.
apply H2.
apply functional_extensionality.
move=> k.
simpl.
elim (excluded_middle_informative (proj1_sig k < N)).
move=> H8.
suff: ((exist (fun k0 : nat => k0 < N) (proj1_sig k) H8) = k).
move=> H9.
rewrite H9.
reflexivity.
apply sig_map.
reflexivity.
move=> H8.
apply False_ind.
apply (H8 (proj2_sig k)).
apply H5.
apply (Plus.le_plus_l N M).
apply Extensionality_Ensembles.
apply conj.
rewrite (proj2 (proj1 (BasisLIGeVS K V (Count M) G) H3)).
move=> v.
elim.
move=> x H5.
rewrite H5.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 (SpanSubspaceVS K V (Count (N + M)) (fun m : Count (N + M) => match excluded_middle_informative (proj1_sig m < N) with
  | left H => F (exist (fun k : nat => k < N) (proj1_sig m) H)
  | right H => G (exist (fun k : nat => k < M) (proj1_sig m - N) (H4 m H))
end)))).
move=> cm u H6 H7.
apply (proj1 (SpanSubspaceVS K V (Count (N + M)) (fun m : Count (N + M) => match excluded_middle_informative (proj1_sig m < N) with
  | left H => F (exist (fun k : nat => k < N) (proj1_sig m) H)
  | right H => G (exist (fun k : nat => k < M) (proj1_sig m - N) (H4 m H))
end)) cm).
apply H7.
apply (proj1 (proj2 (SpanSubspaceVS K V (Count (N + M)) (fun m : Count (N + M) => match excluded_middle_informative (proj1_sig m < N) with
  | left H => F (exist (fun k : nat => k < N) (proj1_sig m) H)
  | right H => G (exist (fun k : nat => k < M) (proj1_sig m - N) (H4 m H))
end))) (proj1_sig x u) (G u)).
suff: (N + proj1_sig u < N + M).
move=> H8.
suff: (G u = (fun m : Count (N + M) => match excluded_middle_informative (proj1_sig m < N) with
  | left H => F (exist (fun k : nat => k < N) (proj1_sig m) H)
  | right H => G (exist (fun k : nat => k < M) (proj1_sig m - N) (H4 m H))
end) (exist (fun (k : nat) => k < N + M) (N + proj1_sig u) H8)).
move=> H9.
rewrite H9.
apply (SpanContainSelfVS K V (Count (N + M)) (fun m : Count (N + M) => match excluded_middle_informative (proj1_sig m < N) with
  | left H => F (exist (fun k : nat => k < N) (proj1_sig m) H)
  | right H => G (exist (fun k : nat => k < M) (proj1_sig m - N) (H4 m H))
end) (exist (fun (k : nat) => k < N + M) (N + proj1_sig u) H8)).
simpl.
elim (excluded_middle_informative (N + proj1_sig u < N)).
move=> H9.
apply False_ind.
apply (lt_irrefl N).
apply (le_trans (S N) (S (N + proj1_sig u)) N).
apply (le_n_S N (N + proj1_sig u)).
apply (Plus.le_plus_l N (proj1_sig u)).
apply H9.
move=> H9.
suff: (u = (exist (fun k : nat => k < M) (N + proj1_sig u - N) (H4 (exist (fun k : nat => k < N + M) (N + proj1_sig u) H8) H9))).
move=> H10.
rewrite {1} H10.
reflexivity.
apply sig_map.
rewrite - {1} (Minus.minus_plus N (proj1_sig u)).
reflexivity.
apply (Plus.plus_lt_compat_l (proj1_sig u) M N).
apply (proj2_sig u).
move=> v H5.
apply (Full_intro (VT K V) v).
move=> m H4.
apply (Plus.plus_lt_reg_l (proj1_sig m - N) M N).
rewrite (Minus.le_plus_minus_r N (proj1_sig m)).
apply (proj2_sig m).
elim (le_or_lt N (proj1_sig m)).
apply.
move=> H5.
apply False_ind.
apply (H4 H5).
Qed.

Lemma Corollary_5_7_trans : forall (K : Field) (V : VectorSpace K) (N M : nat) (F1 : Count N -> VT K V) (F2 : Count M -> VT K V), LinearlyIndependentVS K V (Count N) F1 -> GeneratingSystemVS K V (Count M) F2 -> N <= M.
Proof.
move=> K V N M F1 F2 H1 H2.
elim (Corollary_5_7_2_exists K V M F2 H2).
move=> H3 H4.
apply (le_trans N (DimensionVS K V H3) M (Corollary_5_7_3 K V N F1 H3 H1) H4).
Qed.

Lemma Corollary_5_7_4 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V), GeneratingSystemVS K V (Count N) F -> forall (H : FiniteDimensionVS K V), DimensionVS K V H = N -> BasisVS K V (Count N) F.
Proof.
move=> K V N F H1 H2 H3.
elim (BijectiveSigFull (Count N) (fun (m : Count N) => ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m))).
move=> G H4.
suff: (F = compose (fun k : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) G).
move=> H5.
rewrite H5.
apply (BijectiveSaveBasisVS K V (Count N) {t : Count N | In (Count N) (fun m : Count N => ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)) t} G (fun k : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k))).
apply (proj2 H4).
apply (Theorem_5_6_sub K V N F H1).
apply functional_extensionality.
move=> k.
unfold compose.
rewrite {1} (proj1 H4 k).
reflexivity.
move=> k.
apply NNPP.
move=> H4.
apply (lt_irrefl N).
suff: (cardinal (Count N) (Add (Count N) (fun m : Count N => ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)) k) (S N)).
move=> H5.
elim (CountCardinalInjective {l : Count N | In (Count N) (Add (Count N) (fun (m : Count N) => ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)) k) l} N (fun (x : {l : Count N | In (Count N) (Add (Count N) (fun (m : Count N) => ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)) k) l}) => proj1_sig x)).
move=> M H6.
unfold lt.
rewrite (cardinal_is_functional (Count N) (Add (Count N) (fun m : Count N => ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)) k) (S N) H5 (Add (Count N) (fun m : Count N => ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)) k) M).
apply (proj1 H6).
apply (CardinalSigSame (Count N)).
apply (proj2 H6).
reflexivity.
move=> m1 m2.
apply sig_map.
apply (card_add (Count N)).
apply (CardinalSigSame (Count N)).
elim (proj2 (CountFiniteBijective {t : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig t} (fun k0 : {n : Count N | proj1_sig n < proj1_sig t} => F (proj1_sig k0))) (F t)})).
move=> N2.
elim.
move=> f H5.
suff: (N = N2).
move=> H6.
rewrite {29} H6.
apply CountCardinalBijective.
exists f.
apply H5.
rewrite - H3.
apply (DimensionVSNature2 K V H2 N2 (compose (fun k : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k))) (F m)} => F (proj1_sig k)) f)).
apply (BijectiveSaveBasisVS K V (Count N2) {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k0 : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k0))) (F m)} f (fun k0 : {m : Count N | ~ In (VT K V) (SpanVS K V {n : Count N | proj1_sig n < proj1_sig m} (fun k0 : {n : Count N | proj1_sig n < proj1_sig m} => F (proj1_sig k0))) (F m)} => F (proj1_sig k0)) H5 (Theorem_5_6_sub K V N F H1)).
apply (FiniteSigSame (Count N)).
apply (Finite_downward_closed (Count N) (Full_set (Count N))).
apply (CountFinite N).
move=> m H5.
apply (Full_intro (Count N) m).
apply H4.
Qed.

Lemma Corollary_5_7_4_exists : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V), GeneratingSystemVS K V (Count N) F -> exists (H : FiniteDimensionVS K V), DimensionVS K V H = N -> BasisVS K V (Count N) F.
Proof.
move=> K V N F H1.
exists (Corollary_5_7_1 K V N F H1).
apply (Corollary_5_7_4 K V N F H1 (Corollary_5_7_1 K V N F H1)).
Qed.

Lemma Corollary_5_7_5 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V), LinearlyIndependentVS K V (Count N) F -> forall (H : FiniteDimensionVS K V), DimensionVS K V H = N -> BasisVS K V (Count N) F.
Proof.
move=> K V N F H1 H2 H3.
apply (proj2 (BasisLIGeVS K V (Count N) F)).
apply conj.
apply H1.
elim H2.
move=> M.
elim.
move=> G H4.
suff: (forall (m : Count (N + M)), ~ proj1_sig m < N -> proj1_sig m - N < M).
move=> H5.
suff: (let F2 := (fun (m : Count (N + M)) => match excluded_middle_informative (proj1_sig m < N) with
  | left H => F (exist (fun (k : nat) => k < N) (proj1_sig m) H)
  | right H => G (exist (fun (k : nat) => k < M) (proj1_sig m - N) (H5 m H))
end) in GeneratingSystemVS K V (Count N) F).
apply.
move=> F2.
suff: (forall (m : Count M), In (VT K V) (SpanVS K V (Count N) F) (G m)).
move=> H7.
apply Extensionality_Ensembles.
apply conj.
rewrite (proj2 (proj1 (BasisLIGeVS K V (Count M) G) H4)).
move=> v.
elim.
move=> x H8.
rewrite H8.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 (SpanSubspaceVS K V (Count N) F))).
move=> cm u H9 H10.
apply (proj1 (SpanSubspaceVS K V (Count N) F) cm).
apply H10.
apply (proj1 (proj2 (SpanSubspaceVS K V (Count N) F)) (proj1_sig x u) (G u) (H7 u)).
move=> v H8.
apply (Full_intro (VT K V) v).
suff: (forall (m : Count (N + M)), N <= proj1_sig m -> In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)).
move=> H7.
suff: (forall (n : nat), n <= M -> forall (m : Count M), proj1_sig m < n -> In (VT K V) (SpanVS K V (Count N) F) (G m)).
move=> H8 m.
apply (H8 M (le_n M) m (proj2_sig m)).
elim.
move=> H8 m H9.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig m) H9).
move=> n H8 H9 m H10.
elim (le_lt_or_eq (proj1_sig m) n).
apply (H8 (le_trans n (S n) M (le_S n n (le_n n)) H9) m).
move=> H11.
suff: (In (VT K V) (SpanVS K V {l : Count (N + M) | proj1_sig l < N + n} (fun k : {l : Count (N + M) | proj1_sig l < N + n} => F2 (proj1_sig k))) (G m)).
elim.
move=> x H12.
rewrite H12.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 (SpanSubspaceVS K V (Count N) F))).
move=> cm u H13 H14.
apply (proj1 (SpanSubspaceVS K V (Count N) F) cm).
apply H14.
apply (proj1 (proj2 (SpanSubspaceVS K V (Count N) F)) (proj1_sig x u) (F2 (proj1_sig u))).
unfold F2.
elim (excluded_middle_informative (proj1_sig (proj1_sig u) < N)).
move=> H15.
apply (SpanContainSelfVS K V (Count N) F (exist (fun k : nat => k < N) (proj1_sig (proj1_sig u)) H15)).
move=> H15.
apply (H8 (le_trans n (S n) M (le_S n n (le_n n)) H9) (exist (fun k : nat => k < M) (proj1_sig (proj1_sig u) - N) (H5 (proj1_sig u) H15))).
simpl.
apply (Plus.plus_lt_reg_l (proj1_sig (proj1_sig u) - N) n N).
rewrite (Minus.le_plus_minus_r N (proj1_sig (proj1_sig u))).
apply (proj2_sig u).
elim (le_or_lt N (proj1_sig (proj1_sig u))).
apply.
move=> H16.
apply False_ind.
apply (H15 H16).
suff: (N + n < N + M).
move=> H12.
suff: (G m = F2 (exist (fun (k : nat) => k < N + M) (N + n) H12)).
move=> H13.
rewrite H13.
apply (H7 (exist (fun (k : nat) => k < N + M) (N + n) H12)).
apply (Plus.le_plus_l N n).
unfold F2.
simpl.
elim (excluded_middle_informative (N + n < N)).
move=> H13.
apply False_ind.
apply (lt_irrefl N).
apply (le_trans (S N) (S (N + n)) N).
apply (le_n_S N (N + n) (Plus.le_plus_l N n)).
apply H13.
move=> H13.
suff: (m = (exist (fun k : nat => k < M) (N + n - N) (H5 (exist (fun k : nat => k < N + M) (N + n) H12) H13))).
move=> H14.
rewrite H14.
reflexivity.
apply sig_map.
simpl.
rewrite (Minus.minus_plus N n).
apply H11.
rewrite - H11.
apply (Plus.plus_lt_compat_l (proj1_sig m) M N (proj2_sig m)).
apply (le_S_n (proj1_sig m) n H10).
move=> m H7.
apply NNPP.
move=> H8.
apply (lt_irrefl N).
unfold lt.
rewrite - {2} H3.
suff: (forall (l : nat) (H : l < N), In (Count (N + M)) (fun (m : Count (N + M)) => proj1_sig m < N \/ N <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (exist (fun (n : nat) => n < N + M) l (le_trans (S l) N (N + M) H (Plus.le_plus_l N M)))).
move=> H9.
suff: (In (Count (N + M)) (fun (m : Count (N + M)) => proj1_sig m < N \/ N <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) m).
move=> H10.
apply (Corollary_5_7_3 K V (S N) (compose (fun k : {m : Count (N + M) | proj1_sig m < N \/ N <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)} => F2 (proj1_sig k)) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l < N) with
  | left H => exist (fun m : Count (N + M) => proj1_sig m < N \/ N <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (exist (fun n : nat => n < N + M) (proj1_sig l) (PeanoNat.Nat.le_trans (S (proj1_sig l)) N (N + M) H (Plus.le_plus_l N M))) (H9 (proj1_sig l) H)
  | right _ => exist (fun m : Count (N + M) => proj1_sig m < N \/ N <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) m H10
end))).
apply (InjectiveSaveLinearlyIndependentVS K V (Count (S N)) {m0 : Count (N + M) | proj1_sig m0 < N \/ N <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m0} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)} (fun l : Count (S N) => match excluded_middle_informative (proj1_sig l < N) with
  | left H => exist (fun m0 : Count (N + M) => proj1_sig m0 < N \/ N <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m0} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)) (exist (fun n : nat => n < N + M) (proj1_sig l) (PeanoNat.Nat.le_trans (S (proj1_sig l)) N (N + M) H (Plus.le_plus_l N M))) (H9 (proj1_sig l) H)
  | right _ => exist (fun m0 : Count (N + M) => proj1_sig m0 < N \/ N <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n0 : Count (N + M) | proj1_sig n0 < proj1_sig m0} (fun k : {n0 : Count (N + M) | proj1_sig n0 < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)) m H10
end) (fun k : {m0 : Count (N + M) | proj1_sig m0 < N \/ N <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m0} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)} => F2 (proj1_sig k))).
move=> n1 n2.
elim (excluded_middle_informative (proj1_sig n1 < N)).
move=> H11.
elim (excluded_middle_informative (proj1_sig n2 < N)).
move=> H12 H13.
apply sig_map.
suff: (proj1_sig n1 = proj1_sig (proj1_sig (exist (fun m0 : Count (N + M) => proj1_sig m0 < N \/ N <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m0} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)) (exist (fun n : nat => n < N + M) (proj1_sig n1) (PeanoNat.Nat.le_trans (S (proj1_sig n1)) N (N + M) H11 (Plus.le_plus_l N M))) (H9 (proj1_sig n1) H11)))).
move=> H14.
rewrite H14.
rewrite H13.
reflexivity.
reflexivity.
move=> H12 H13.
apply False_ind.
apply (le_not_lt N (proj1_sig (proj1_sig (exist (fun m0 : Count (N + M) => proj1_sig m0 < N \/ N <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m0} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)) (exist (fun n : nat => n < N + M) (proj1_sig n1) (PeanoNat.Nat.le_trans (S (proj1_sig n1)) N (N + M) H11 (Plus.le_plus_l N M))) (H9 (proj1_sig n1) H11))))).
rewrite H13.
apply H7.
apply H11.
move=> H11.
elim (excluded_middle_informative (proj1_sig n2 < N)).
move=> H12 H13.
apply False_ind.
apply (le_not_lt N (proj1_sig (proj1_sig (exist (fun m0 : Count (N + M) => proj1_sig m0 < N \/ N <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n0 : Count (N + M) | proj1_sig n0 < proj1_sig m0} (fun k : {n0 : Count (N + M) | proj1_sig n0 < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)) m H10)))).
apply H7.
rewrite H13.
apply H12.
move=> H12 H13.
apply sig_map.
elim (le_lt_or_eq (proj1_sig n1) N).
move=> H14.
apply False_ind.
apply (H11 H14).
move=> H14.
rewrite H14.
elim (le_lt_or_eq (proj1_sig n2) N).
move=> H15.
apply False_ind.
apply (H12 H15).
move=> H15.
rewrite H15.
reflexivity.
apply (le_S_n (proj1_sig n2) N (proj2_sig n2)).
apply (le_S_n (proj1_sig n1) N (proj2_sig n1)).
apply (proj1 (BasisLIGeVS K V {m0 : Count (N + M) | proj1_sig m0 < N \/ N <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m0} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)} (fun k : {m0 : Count (N + M) | proj1_sig m0 < N \/ N <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n : Count (N + M) | proj1_sig n < proj1_sig m0} (fun k : {n : Count (N + M) | proj1_sig n < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)} => F2 (proj1_sig k)))).
suff: (forall m : Count N, proj1_sig m < N + M).
move=> H11.
apply (Theorem_5_6 K V N (N + M) (Plus.le_plus_l N M) H11 F2).
suff: ((fun m0 : Count N => F2 (exist (fun n : nat => n < N + M) (proj1_sig m0) (H11 m0))) = F).
move=> H12.
rewrite H12.
apply H1.
apply functional_extensionality.
move=> k.
unfold F2.
simpl.
elim (excluded_middle_informative (proj1_sig k < N)).
move=> H12.
suff: ((exist (fun k0 : nat => k0 < N) (proj1_sig k) H12) = k).
move=> H13.
rewrite H13.
reflexivity.
apply sig_map.
reflexivity.
move=> H12.
apply False_ind.
apply (H12 (proj2_sig k)).
apply Extensionality_Ensembles.
apply conj.
rewrite (proj2 (proj1 (BasisLIGeVS K V (Count M) G) H4)).
move=> k.
elim.
move=> x H12.
rewrite H12.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 (SpanSubspaceVS K V (Count (N + M)) F2))).
move=> cm u H13 H14.
apply (proj1 (SpanSubspaceVS K V (Count (N + M)) F2)).
apply H14.
apply (proj1 (proj2 (SpanSubspaceVS K V (Count (N + M)) F2)) (proj1_sig x u) (G u)).
suff: (N + proj1_sig u < N + M).
move=> H15.
suff: (G u = F2 (exist (fun (k : nat) => k < N + M) (N + proj1_sig u) H15)).
move=> H16.
rewrite H16.
apply (SpanContainSelfVS K V (Count (N + M)) F2 (exist (fun k0 : nat => k0 < N + M) (N + proj1_sig u) H15)).
unfold F2.
simpl.
elim (excluded_middle_informative (N + proj1_sig u < N)).
move=> H16.
apply False_ind.
apply (lt_irrefl N).
apply (le_trans (S N) (S (N + proj1_sig u)) N).
apply (le_n_S N (N + proj1_sig u)).
apply (Plus.le_plus_l N (proj1_sig u)).
apply H16.
move=> H16.
suff: (u = (exist (fun k0 : nat => k0 < M) (N + proj1_sig u - N) (H5 (exist (fun k0 : nat => k0 < N + M) (N + proj1_sig u) H15) H16))).
move=> H17.
rewrite {1} H17.
reflexivity.
apply sig_map.
simpl.
rewrite (Minus.minus_plus N (proj1_sig u)).
reflexivity.
apply (Plus.plus_lt_compat_l (proj1_sig u) M N).
apply (proj2_sig u).
move=> v H12.
apply (Full_intro (VT K V) v).
move=> k.
apply (le_trans (S (proj1_sig k)) N (N + M) (proj2_sig k) (Plus.le_plus_l N M)).
right.
apply conj.
apply H7.
apply H8.
move=> l H9.
left.
apply H9.
move=> m H5.
apply (Plus.plus_lt_reg_l (proj1_sig m - N) M N).
rewrite (Minus.le_plus_minus_r N (proj1_sig m)).
apply (proj2_sig m).
elim (le_or_lt N (proj1_sig m)).
apply.
move=> H6.
apply False_ind.
apply (H5 H6).
Qed.

Lemma Corollary_5_8_1_1 : forall (K : Field) (V : VectorSpace K), FiniteDimensionVS K V -> exists (N : nat) (F : Count N -> VT K V), GeneratingSystemVS K V (Count N) F.
Proof.
move=> K V.
elim.
move=> N.
elim.
move=> F H1.
exists N.
exists F.
apply (proj2 (proj1 (BasisLIGeVS K V (Count N) F) H1)).
Qed.

Lemma Corollary_5_8_1_2 : forall (K : Field) (V : VectorSpace K), (exists (N : nat) (F : Count N -> VT K V), GeneratingSystemVS K V (Count N) F) -> exists (M : nat), forall (N : nat) (F : Count N -> VT K V), LinearlyIndependentVS K V (Count N) F -> N <= M.
Proof.
move=> K V.
elim.
move=> N.
elim.
move=> F H1.
exists N.
move=> L G H2.
apply (Corollary_5_7_trans K V L N G F H2 H1).
Qed.

Lemma Corollary_5_8_1_3 : forall (K : Field) (V : VectorSpace K), (exists (M : nat), forall (N : nat) (F : Count N -> VT K V), LinearlyIndependentVS K V (Count N) F -> N <= M) -> FiniteDimensionVS K V.
Proof.
move=> K V H1.
elim (min_nat_exist (fun (M : nat) => forall (N : nat) (F : Count N -> VT K V), LinearlyIndependentVS K V (Count N) F -> N <= M)).
suff: (forall (L : nat), is_min_nat (fun M : nat => forall (N : nat) (F : Count N -> VT K V), LinearlyIndependentVS K V (Count N) F -> N <= M) L -> exists (F : Count L -> VT K V), LinearlyIndependentVS K V (Count L) F).
move=> H2 L H3.
exists L.
elim (H2 L H3).
move=> F H4.
exists F.
apply (proj2 (BasisLIGeVS K V (Count L) F)).
apply conj.
apply H4.
apply Extensionality_Ensembles.
apply conj.
move=> v H5.
apply NNPP.
move=> H6.
apply (lt_irrefl L).
suff: (LinearlyIndependentVS K V (Count (S L)) (fun (m : Count (S L)) => match excluded_middle_informative (proj1_sig m < L) with
  | left H => F (exist (fun (k : nat) => k < L) (proj1_sig m) H)
  | right _ => v
end)).
move=> H7.
apply (proj1 H3 (S L) (fun (m : Count (S L)) => match excluded_middle_informative (proj1_sig m < L) with
  | left H => F (exist (fun (k : nat) => k < L) (proj1_sig m) H)
  | right _ => v
end) H7).
elim (Proposition_5_2_exists K V L).
move=> H7.
elim.
move=> H8 H9.
apply (proj2 (H9 (fun (m : Count (S L)) => match excluded_middle_informative (proj1_sig m < L) with
  | left H => F (exist (fun (k : nat) => k < L) (proj1_sig m) H)
  | right _ => v
end))).
apply conj.
simpl.
suff: ((fun m : Count L => match excluded_middle_informative (proj1_sig m < L) with
  | left H => F (exist (fun k : nat => k < L) (proj1_sig m) H)
  | right _ => v
end) = F).
move=> H10.
rewrite H10.
apply H4.
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (proj1_sig m < L)).
move=> H10.
suff: ((exist (fun k : nat => k < L) (proj1_sig m) H10) = m).
move=> H11.
rewrite H11.
reflexivity.
apply sig_map.
reflexivity.
move=> H10.
apply False_ind.
apply (H10 (proj2_sig m)).
simpl.
elim (excluded_middle_informative (L < L)).
move=> H10.
apply False_ind.
apply (lt_irrefl L H10).
move=> H10.
suff: ((fun m : Count L => match excluded_middle_informative (proj1_sig m < L) with
  | left H => F (exist (fun k : nat => k < L) (proj1_sig m) H)
  | right _ => v
end) = F).
move=> H11.
rewrite H11.
apply H6.
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (proj1_sig m < L)).
move=> H11.
suff: ((exist (fun k : nat => k < L) (proj1_sig m) H11) = m).
move=> H12.
rewrite H12.
reflexivity.
apply sig_map.
reflexivity.
move=> H11.
apply False_ind.
apply (H11 (proj2_sig m)).
move=> v H5.
apply (Full_intro (VT K V) v).
elim.
move=> H2.
exists (fun (m : Count O) => VO K V).
apply (LinearlyIndependentVSDef3 K V (Count O) (fun _ : Count 0 => VO K V)).
move=> a A H3 m H4.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig m) (proj2_sig m)).
move=> n H2 H3.
apply NNPP.
move=> H4.
apply (lt_irrefl n).
apply (proj2 H3 n).
move=> k F H5.
apply (le_S_n k n).
elim (le_lt_or_eq k (S n)).
apply.
move=> H6.
apply False_ind.
apply H4.
rewrite - H6.
exists F.
apply H5.
apply (proj1 H3 k F H5).
elim H1.
move=> M H2.
apply (Inhabited_intro nat (fun L : nat => forall (N : nat) (F : Count N -> VT K V), LinearlyIndependentVS K V (Count N) F -> N <= L) M H2).
Qed.

Lemma Corollary_5_8_1_4 : forall (K : Field) (V : VectorSpace K), FiniteDimensionVS K V -> exists M : nat, forall (N : nat) (F : Count N -> VT K V), LinearlyIndependentVS K V (Count N) F -> N <= M.
Proof.
move=> K V H1.
apply (Corollary_5_8_1_2 K V).
apply (Corollary_5_8_1_1 K V H1).
Qed.

Lemma Corollary_5_8_1_5 : forall (K : Field) (V : VectorSpace K), (exists (N : nat) (F : Count N -> VT K V), GeneratingSystemVS K V (Count N) F) -> FiniteDimensionVS K V.
Proof.
move=> K V H1.
apply (Corollary_5_8_1_3 K V).
apply (Corollary_5_8_1_2 K V H1).
Qed.

Lemma Corollary_5_8_1_6 : forall (K : Field) (V : VectorSpace K), (exists M : nat, forall (N : nat) (F : Count N -> VT K V), LinearlyIndependentVS K V (Count N) F -> N <= M) -> exists (N : nat) (F : Count N -> VT K V), GeneratingSystemVS K V (Count N) F.
Proof.
move=> K V H1.
apply (Corollary_5_8_1_1 K V).
apply (Corollary_5_8_1_3 K V H1).
Qed.

Lemma Corollary_5_8_2_1 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V) (H : FiniteDimensionVS K V), BasisVS K V (Count N) F -> (GeneratingSystemVS K V (Count N) F /\ DimensionVS K V H = N).
Proof.
move=> K V N F H1 H2.
apply conj.
apply (proj2 (proj1 (BasisLIGeVS K V (Count N) F) H2)).
apply (DimensionVSNature2 K V H1 N F H2).
Qed.

Lemma Corollary_5_8_2_3 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V) (H : FiniteDimensionVS K V), (LinearlyIndependentVS K V (Count N) F /\ DimensionVS K V H = N) -> BasisVS K V (Count N) F.
Proof.
move=> K V N F H1 H2.
apply (Corollary_5_7_5 K V N F (proj1 H2) H1 (proj2 H2)).
Qed.

Lemma Corollary_5_8_2_4 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V) (H : FiniteDimensionVS K V), BasisVS K V (Count N) F -> (LinearlyIndependentVS K V (Count N) F /\ DimensionVS K V H = N).
Proof. 
move=> K V N F H1 H2.
apply conj.
apply (proj1 (proj1 (BasisLIGeVS K V (Count N) F) H2)).
apply (DimensionVSNature2 K V H1 N F H2).
Qed.

Lemma Corollary_5_8_2_5 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V) (H : FiniteDimensionVS K V), (GeneratingSystemVS K V (Count N) F /\ DimensionVS K V H = N) -> BasisVS K V (Count N) F.
Proof.
move=> K V N F H1 H2.
apply (Corollary_5_7_4 K V N F (proj1 H2) H1 (proj2 H2)).
Qed.

Lemma Corollary_5_8_2_2 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V) (H : FiniteDimensionVS K V), (GeneratingSystemVS K V (Count N) F /\ DimensionVS K V H = N) -> (LinearlyIndependentVS K V (Count N) F /\ DimensionVS K V H = N).
Proof.
move=> K V N F H1 H2.
apply (Corollary_5_8_2_4 K V N F H1).
apply (Corollary_5_8_2_5 K V N F H1 H2).
Qed.

Lemma Corollary_5_8_2_6 : forall (K : Field) (V : VectorSpace K) (N : nat) (F : Count N -> VT K V) (H : FiniteDimensionVS K V), (LinearlyIndependentVS K V (Count N) F /\ DimensionVS K V H = N) -> (GeneratingSystemVS K V (Count N) F /\ DimensionVS K V H = N).
Proof.
move=> K V N F H1 H2.
apply (Corollary_5_8_2_1 K V N F H1).
apply (Corollary_5_8_2_3 K V N F H1 H2).
Qed.

Lemma IsomorphicSaveFiniteDimensionVS : forall (K : Field) (V1 V2 : VectorSpace K) (G : VT K V1 -> VT K V2), IsomorphicVS K V1 V2 G -> FiniteDimensionVS K V1 -> FiniteDimensionVS K V2.
Proof.
move=> K V1 V2 G H1.
elim.
move=> N.
elim.
move=> F H2.
exists N.
exists (compose G F).
apply (IsomorphicSaveBasisVS K V1 V2 (Count N) F G H1 H2). 
Qed.

Lemma SurjectiveSaveFiniteDimensionVS : forall (K : Field) (V1 V2 : VectorSpace K) (G : VT K V1 -> VT K V2), Surjective (VT K V1) (VT K V2) G /\ (forall x y : VT K V1, G (Vadd K V1 x y) = Vadd K V2 (G x) (G y)) /\ (forall (c : FT K) (x : VT K V1), G (Vmul K V1 c x) = Vmul K V2 c (G x)) -> FiniteDimensionVS K V1 -> FiniteDimensionVS K V2.
Proof.
move=> K V1 V2 G H1 H2.
apply (Corollary_5_8_1_5 K V2).
elim (Corollary_5_8_1_1 K V1 H2).
move=> N.
elim.
move=> F H3.
exists N.
exists (compose G F).
apply (SurjectiveSaveGeneratingSystemVS2 K V1 V2 (Count N) F G H1 H3). 
Qed.

Lemma IsomorphicSaveDimensionVS : forall (K : Field) (V1 V2 : VectorSpace K) (G : VT K V1 -> VT K V2) (H1 : FiniteDimensionVS K V1) (H2 : FiniteDimensionVS K V2), IsomorphicVS K V1 V2 G -> DimensionVS K V1 H1 = DimensionVS K V2 H2.
Proof.
move=> K V1 V2 G H1 H2 H3.
elim H1.
move=> N.
elim.
move=> F H4.
rewrite (DimensionVSNature2 K V2 H2 N (compose G F)).
apply (DimensionVSNature2 K V1 H1 N F H4).
apply (IsomorphicSaveBasisVS K V1 V2 (Count N) F G H3 H4). 
Qed.

Lemma IsomorphicSaveDimensionVS_exists : forall (K : Field) (V1 V2 : VectorSpace K) (G : VT K V1 -> VT K V2) (H1 : FiniteDimensionVS K V1), IsomorphicVS K V1 V2 G -> exists (H2 : FiniteDimensionVS K V2), DimensionVS K V1 H1 = DimensionVS K V2 H2.
Proof.
move=> K V1 V2 G H1 H2.
exists (IsomorphicSaveFiniteDimensionVS K V1 V2 G H2 H1).
apply (IsomorphicSaveDimensionVS K V1 V2 G H1 (IsomorphicSaveFiniteDimensionVS K V1 V2 G H2 H1) H2). 
Qed.

Lemma Proposition_5_9_1_1 : forall (K : Field) (V : VectorSpace K), FiniteDimensionVS K V -> forall (W : Ensemble (VT K V)) (H : SubspaceVS K V W), FiniteDimensionVS K (SubspaceMakeVS K V W H). 
Proof.
move=> K V H1 W H2.
apply (Corollary_5_8_1_3 K (SubspaceMakeVS K V W H2)).
elim (Corollary_5_8_1_4 K V H1).
move=> M H3.
exists M.
move=> N F H4.
apply (H3 N (compose (fun (v : {w : VT K V | In (VT K V) W w}) => proj1_sig v) F)).
apply (InjectiveSaveLinearlyIndependentVS2 K (SubspaceMakeVS K V W H2) V (Count N) F (fun v : {w : VT K V | In (VT K V) W w} => proj1_sig v)).
apply conj.
move=> v1 v2.
apply sig_map.
apply conj.
move=> v1 v2.
reflexivity.
move=> c v.
reflexivity.
apply H4.
Qed.

Lemma Proposition_5_9_1_2 : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H1 : SubspaceVS K V W) (H2 : FiniteDimensionVS K V) (H3 : FiniteDimensionVS K (SubspaceMakeVS K V W H1)), DimensionVS K V H2 >= DimensionSubspaceVS K V W H1 H3. 
Proof.
move=> K V W H1 H2 H3.
elim (DimensionVSNature K (SubspaceMakeVS K V W H1) H3).
move=> F H4.
apply (Corollary_5_7_3 K V (DimensionSubspaceVS K V W H1 H3) (compose (fun (v : {w : VT K V | In (VT K V) W w}) => proj1_sig v) F)).
apply (InjectiveSaveLinearlyIndependentVS2 K (SubspaceMakeVS K V W H1) V (Count (DimensionSubspaceVS K V W H1 H3)) F (fun v : {w : VT K V | In (VT K V) W w} => proj1_sig v)).
apply conj.
move=> v1 v2.
apply sig_map.
apply conj.
move=> v1 v2.
reflexivity.
move=> c v.
reflexivity.
apply (proj1 (proj1 (BasisLIGeVS K (SubspaceMakeVS K V W H1) (Count (DimensionSubspaceVS K V W H1 H3)) F) H4)).
Qed.

Lemma Proposition_5_9_1_2_exists : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H1 : SubspaceVS K V W) (H2 : FiniteDimensionVS K V), exists (H3 : FiniteDimensionVS K (SubspaceMakeVS K V W H1)), DimensionVS K V H2 >= DimensionSubspaceVS K V W H1 H3. 
Proof.
move=> K V W H1 H2.
exists (Proposition_5_9_1_1 K V H2 W H1).
apply (Proposition_5_9_1_2 K V W H1 H2 (Proposition_5_9_1_1 K V H2 W H1)).
Qed.

Lemma Proposition_5_9_1_3 : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H1 : SubspaceVS K V W) (H2 : FiniteDimensionVS K V) (H3 : FiniteDimensionVS K (SubspaceMakeVS K V W H1)), DimensionVS K V H2 = DimensionSubspaceVS K V W H1 H3 <-> W = (Full_set (VT K V)). 
Proof.
move=> K V W H1 H2 H3.
apply conj.
move=> H4.
apply Extensionality_Ensembles.
apply conj.
move=> w H5.
apply (Full_intro (VT K V) w).
elim (DimensionSubspaceVSNature K V W H1 H3).
move=> F H5.
suff: (GeneratingSystemVS K V (Count (DimensionSubspaceVS K V W H1 H3)) F).
move=> H6.
rewrite H6.
move=> v.
elim.
move=> x H7.
rewrite H7.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 H1)).
move=> cm u H8 H9.
apply (proj1 H1).
apply H9.
apply (proj1 (proj2 H1)).
elim H5.
move=> H10 H11.
apply (H10 u).
apply (Corollary_5_8_2_6 K V (DimensionSubspaceVS K V W H1 H3) F H2).
apply conj.
apply (SubspaceBasisLinearlyIndependentVS K V W H1 (Count (DimensionSubspaceVS K V W H1 H3)) F H5).
apply H4.
move=> H4.
suff: (forall (v : VT K V), In (VT K V) W v).
move=> H5.
unfold DimensionSubspaceVS.
apply (IsomorphicSaveDimensionVS K V (SubspaceMakeVS K V W H1) (fun (v : VT K V) => exist W v (H5 v)) H2 H3).
apply conj.
exists (fun (v : {w : VT K V | In (VT K V) W w}) => proj1_sig v).
apply conj.
move=> x.
reflexivity.
move=> y.
apply sig_map.
reflexivity.
apply conj.
move=> v1 v2.
apply sig_map.
reflexivity.
move=> c v.
apply sig_map.
reflexivity.
rewrite H4.
move=> v.
apply (Full_intro (VT K V) v).
Qed.

Lemma Proposition_5_9_1_3_exists : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H1 : SubspaceVS K V W) (H2 : FiniteDimensionVS K V), exists (H3 : FiniteDimensionVS K (SubspaceMakeVS K V W H1)), DimensionVS K V H2 = DimensionSubspaceVS K V W H1 H3 <-> W = (Full_set (VT K V)). 
Proof.
move=> K V W H1 H2.
exists (Proposition_5_9_1_1 K V H2 W H1).
apply (Proposition_5_9_1_3 K V W H1 H2 (Proposition_5_9_1_1 K V H2 W H1)).
Qed.

Lemma Proposition_5_9_2 : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H1 : SubspaceVS K V W) (H2 : FiniteDimensionVS K V) (M : nat) (F : Count M -> VT K V) (H3 : forall (m : Count (DimensionVS K V H2)), ~ proj1_sig m < M -> proj1_sig m - M < DimensionVS K V H2 - M), BasisSubspaceVS K V W H1 (Count M) F -> exists (G : Count (DimensionVS K V H2 - M) -> VT K V), BasisVS K V (Count (DimensionVS K V H2)) (fun (m : Count (DimensionVS K V H2)) => match excluded_middle_informative (proj1_sig m < M) with
  | left H => F (exist (fun (n : nat) => n < M) (proj1_sig m) H)
  | right H => G (exist (fun (n : nat) => n < DimensionVS K V H2 - M) (proj1_sig m - M) (H3 m H))
end).
Proof.
move=> K V W H1 H2 M F H20 H3.
elim H2.
move=> N.
elim.
move=> G H4.
suff: (forall m : Count M, proj1_sig m < M + N).
move=> H5.
suff: (forall m : Count (M + N), ~ proj1_sig m < M -> proj1_sig m - M < N).
move=> H6.
suff: (let F2 := (fun (m : Count (M + N)) => match excluded_middle_informative (proj1_sig m < M) with
  | left H => F (exist (fun (n : nat) => n < M) (proj1_sig m) H)
  | right H => G (exist (fun (n : nat) => n < N) (proj1_sig m - M) (H6 m H))
end) in exists G0 : Count (DimensionVS K V H2 - M) -> VT K V, BasisVS K V (Count (DimensionVS K V H2)) (fun m : Count (DimensionVS K V H2) => match excluded_middle_informative (proj1_sig m < M) with
  | left H => F (exist (fun n : nat => n < M) (proj1_sig m) H)
  | right H => G0 (exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig m - M) (H20 m H))
end)).
apply.
move=> F2.
suff: (BasisVS K V {m : Count (M + N) | proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)} (fun k : {m : Count (M + N) | proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)} => F2 (proj1_sig k))).
move=> H18.
elim (proj2 (CountCardinalBijective {m : Count (M + N) | M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)} (DimensionVS K V H2 - M))).
move=> G2 H7.
exists (fun (m : Count (DimensionVS K V H2 - M)) => F2 (proj1_sig (G2 m))).
suff: (forall (m : Count (DimensionVS K V H2)) (H : proj1_sig m < M), In (Count (M + N)) (fun (m : Count (M + N)) => proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (exist (fun (n : nat) => n < M + N) (proj1_sig m) (H5 (exist (fun (n : nat) => n < M) (proj1_sig m) H)))).
move=> H9.
suff: (forall (m : Count (DimensionVS K V H2)) (H : ~ proj1_sig m < M), In (Count (M + N)) (fun (m : Count (M + N)) => proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig (G2 (exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig m - M) (H20 m H))))).
move=> H10.
suff: ((fun m : Count (DimensionVS K V H2) => match excluded_middle_informative (proj1_sig m < M) with
  | left H => F (exist (fun n : nat => n < M) (proj1_sig m) H)
  | right H => F2 (proj1_sig (G2 (exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig m - M) (H20 m H))))
end) = compose (fun k : {m : Count (M + N) | proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)} => F2 (proj1_sig k)) (fun (m : Count (DimensionVS K V H2)) => match excluded_middle_informative (proj1_sig m < M) with
  | left H => exist (fun (m : Count (M + N)) => proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (exist (fun n : nat => n < M + N) (proj1_sig m) (H5 (exist (fun n : nat => n < M) (proj1_sig m) H))) (H9 m H)
  | right H => exist (fun (m : Count (M + N)) => proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig (G2 (exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig m - M) (H20 m H)))) (H10 m H)
end)).
move=> H11.
rewrite H11.
apply (BijectiveSaveBasisVS K V (Count (DimensionVS K V H2)) {m : Count (M + N) | proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)} (fun m : Count (DimensionVS K V H2) => match excluded_middle_informative (proj1_sig m < M) with
  | left H => exist (fun m0 : Count (M + N) => proj1_sig m0 < M \/ M <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m0} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)) (exist (fun n : nat => n < M + N) (proj1_sig m) (H5 (exist (fun n : nat => n < M) (proj1_sig m) H))) (H9 m H)
  | right H => exist (fun m0 : Count (M + N) => proj1_sig m0 < M \/ M <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m0} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)) (proj1_sig (G2 (exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig m - M) (H20 m H)))) (H10 m H)
end) (fun k : {m : Count (M + N) | proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)} => F2 (proj1_sig k))).
apply InjSurjBij.
move=> k1 k2.
elim (excluded_middle_informative (proj1_sig k1 < M)).
move=> H12.
elim (excluded_middle_informative (proj1_sig k2 < M)).
move=> H13 H14.
apply sig_map.
suff: (proj1_sig k1 = proj1_sig (proj1_sig (exist (fun m0 : Count (M + N) => proj1_sig m0 < M \/ M <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m0} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)) (exist (fun n : nat => n < M + N) (proj1_sig k1) (H5 (exist (fun n : nat => n < M) (proj1_sig k1) H12))) (H9 k1 H12)))).
move=> H15.
rewrite H15.
rewrite H14.
reflexivity.
reflexivity.
move=> H13 H14.
apply False_ind.
apply (le_not_lt M (proj1_sig (proj1_sig (exist (fun m0 : Count (M + N) => proj1_sig m0 < M \/ M <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m0} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)) (exist (fun n : nat => n < M + N) (proj1_sig k1) (H5 (exist (fun n : nat => n < M) (proj1_sig k1) H12))) (H9 k1 H12))))).
rewrite H14.
apply (proj1 (proj2_sig (G2 (exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig k2 - M) (H20 k2 H13))))).
apply H12.
move=> H12.
elim (excluded_middle_informative (proj1_sig k2 < M)).
move=> H13 H14.
apply False_ind.
apply (le_not_lt M (proj1_sig (proj1_sig (exist (fun m0 : Count (M + N) => proj1_sig m0 < M \/ M <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m0} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)) (proj1_sig (G2 (exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig k1 - M) (H20 k1 H12)))) (H10 k1 H12))))).
apply (proj1 (proj2_sig (G2 (exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig k1 - M) (H20 k1 H12))))).
rewrite H14.
apply H13.
move=> H13 H14.
apply sig_map.
suff: (proj1_sig k1 - M = proj1_sig k2 - M).
move=> H15.
rewrite - (Minus.le_plus_minus_r M (proj1_sig k1)).
rewrite - (Minus.le_plus_minus_r M (proj1_sig k2)).
rewrite H15.
reflexivity.
elim (le_or_lt M (proj1_sig k2)).
apply.
move=> H16.
apply False_ind.
apply (H13 H16).
elim (le_or_lt M (proj1_sig k1)).
apply.
move=> H16.
apply False_ind.
apply (H12 H16).
suff: ((exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig k1 - M) (H20 k1 H12)) = (exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig k2 - M) (H20 k2 H13))).
move=> H15.
suff: (proj1_sig k1 - M = proj1_sig (exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig k1 - M) (H20 k1 H12))).
move=> H16.
rewrite H16.
rewrite H15.
reflexivity.
reflexivity.
apply (BijInj {n : nat | n < DimensionVS K V H2 - M} {m : Count (M + N) | M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)} G2 H7).
apply sig_map.
suff: (proj1_sig (G2 (exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig k1 - M) (H20 k1 H12))) = proj1_sig (exist (fun m0 : Count (M + N) => proj1_sig m0 < M \/ M <= proj1_sig m0 /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m0} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m0} => F2 (proj1_sig k))) (F2 m0)) (proj1_sig (G2 (exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig k1 - M) (H20 k1 H12)))) (H10 k1 H12))).
move=> H15.
rewrite H15.
rewrite H14.
reflexivity.
reflexivity.
move=> v.
elim (classic (proj1_sig (proj1_sig v) < M)).
move=> H12.
suff: (M <= DimensionVS K V H2).
move=> H13.
exists (exist (fun (n : nat) => n < DimensionVS K V H2) (proj1_sig (proj1_sig v)) (le_trans (S (proj1_sig (proj1_sig v))) M (DimensionVS K V H2) H12 H13)).
simpl.
elim (excluded_middle_informative (proj1_sig (proj1_sig v) < M)).
move=> H14.
apply sig_map.
apply sig_map.
reflexivity.
move=> H15.
apply False_ind.
apply (H15 H12).
suff: (FiniteDimensionVS K (SubspaceMakeVS K V W H1)).
move=> H13.
rewrite - (DimensionSubspaceVSNature2 K V W H1 H13 M F).
apply (Proposition_5_9_1_2 K V W H1 H2 H13).
apply H3.
apply (Proposition_5_9_1_1 K V H2 W H1).
move=> H12.
elim H7.
move=> G2Inv H13.
suff: (M <= proj1_sig (proj1_sig v) /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig (proj1_sig v)} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig (proj1_sig v)} => F2 (proj1_sig k))) (F2 (proj1_sig v))).
move=> H14.
suff: (proj1_sig (G2Inv (exist (fun (m : Count (M + N)) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H14)) + M < DimensionVS K V H2).
move=> H15.
exists (exist (fun (n : nat) => n < DimensionVS K V H2) (proj1_sig (G2Inv (exist (fun (m : Count (M + N)) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H14)) + M) H15).
simpl.
elim (excluded_middle_informative (proj1_sig (G2Inv (exist (fun m : Count (M + N) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H14)) + M < M)).
move=> H16.
apply False_ind.
apply (le_not_lt M (proj1_sig (G2Inv (exist (fun m : Count (M + N) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H14)) + M)).
apply Plus.le_plus_r.
apply H16.
move=> H16.
apply sig_map.
simpl.
suff: ((exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig (G2Inv (exist (fun m : Count (M + N) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H14)) + M - M) (H20 (exist (fun n : nat => n < DimensionVS K V H2) (proj1_sig (G2Inv (exist (fun m : Count (M + N) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun  k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H14)) + M) H15) H16)) = (G2Inv (exist (fun m : Count (M + N) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H14))).
move=> H17.
rewrite H17.
rewrite (proj2 H13).
reflexivity.
apply sig_map.
simpl.
rewrite Plus.plus_comm.
apply Minus.minus_plus.
rewrite - {2} (Minus.le_plus_minus_r M (DimensionVS K V H2)).
rewrite Plus.plus_comm.
apply Plus.plus_lt_compat_l.
apply (proj2_sig (G2Inv (exist (fun m : Count (M + N) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H14))).
suff: (FiniteDimensionVS K (SubspaceMakeVS K V W H1)).
move=> H15.
rewrite - (DimensionSubspaceVSNature2 K V W H1 H15 M F).
apply (Proposition_5_9_1_2 K V W H1 H2 H15).
apply H3.
apply (Proposition_5_9_1_1 K V H2 W H1).
apply conj.
elim (le_or_lt M (proj1_sig (proj1_sig v))).
apply.
move=> H14.
apply False_ind.
apply (H12 H14).
elim (proj2_sig v).
move=> H14.
apply False_ind.
apply (H12 H14).
move=> H14.
apply (proj2 H14).
apply H18.
apply functional_extensionality.
move=> m.
unfold compose.
elim (excluded_middle_informative (proj1_sig m < M)).
move=> H11.
simpl.
unfold F2.
simpl.
elim (excluded_middle_informative (proj1_sig m < M)).
move=> H12.
suff: (H11 = H12).
move=> H13.
rewrite H13.
reflexivity.
apply proof_irrelevance.
move=> H12.
apply False_ind.
apply (H12 H11).
move=> H11.
reflexivity.
move=> m H10.
right.
apply (proj2_sig (G2 (exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig m - M) (H20 m H10)))).
move=> m H9.
left.
apply H9.
elim (proj2 (CountFiniteBijective {m : Count (M + N) | M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)})).
move=> L.
elim.
move=> f H7.
suff: (DimensionVS K V H2 - M = L).
move=> H8.
rewrite H8.
apply CountCardinalBijective.
exists f.
apply H7.
apply (Plus.plus_reg_l (DimensionVS K V H2 - M) L M).
rewrite (Minus.le_plus_minus_r M (DimensionVS K V H2)).
suff: (exists (g : {n : nat | n < M + L} -> {m : Count (M + N) | proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)}), Bijective {n : nat | n < M + L} {m : Count (M + N) | proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)} g).
elim.
move=> g H8.
apply (DimensionVSNature2 K V H2 (M + L) (compose (fun k : {m : Count (M + N) | proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)} => F2 (proj1_sig k)) g)).
apply (BijectiveSaveBasisVS K V (Count (M + L)) {m : Count (M + N) | proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)} g (fun k : {m : Count (M + N) | proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)} => F2 (proj1_sig k))).
apply H8.
apply H18.
suff: (forall (m : Count (M + L)) (H : proj1_sig m < M), (fun m : Count (M + N) => proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (exist (fun (n : nat) => n < M + N) (proj1_sig m) (H5 (exist (fun (n : nat) => n < M) (proj1_sig m) H)))).
move=> H8.
suff: (forall (m : Count (M + L)), ~ proj1_sig m < M -> proj1_sig m - M < L).
move=> H9.
suff: (forall (m : Count (M + L)) (H : ~ proj1_sig m < M), (fun m : Count (M + N) => proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig (f (exist (fun (n : nat) => n < L) (proj1_sig m - M) (H9 m H))))).
move=> H10.
exists (fun (m : Count (M + L)) => match excluded_middle_informative (proj1_sig m < M) with
  | left H => exist (fun m : Count (M + N) => proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (exist (fun (n : nat) => n < M + N) (proj1_sig m) (H5 (exist (fun (n : nat) => n < M) (proj1_sig m) H))) (H8 m H)
  | right H => exist (fun m : Count (M + N) => proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig (f (exist (fun (n : nat) => n < L) (proj1_sig m - M) (H9 m H)))) (H10 m H)
end).
apply InjSurjBij.
move=> k1 k2.
elim (excluded_middle_informative (proj1_sig k1 < M)).
move=> H11.
elim (excluded_middle_informative (proj1_sig k2 < M)).
move=> H12 H13.
suff: (proj1_sig k1 = proj1_sig (proj1_sig (exist (fun m : Count (M + N) => proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (exist (fun n : nat => n < M + N) (proj1_sig k1) (H5 (exist (fun n : nat => n < M) (proj1_sig k1) H11))) (H8 k1 H11)))).
move=> H14.
apply sig_map.
rewrite H14.
rewrite H13.
reflexivity.
reflexivity.
move=> H12 H13.
apply False_ind.
apply (le_not_lt M (proj1_sig (proj1_sig (exist (fun m : Count (M + N) => proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (exist (fun n : nat => n < M + N) (proj1_sig k1) (H5 (exist (fun n : nat => n < M) (proj1_sig k1) H11))) (H8 k1 H11))))).
rewrite H13.
apply (proj1 (proj2_sig (f (exist (fun n : nat => n < L) (proj1_sig k2 - M) (H9 k2 H12))))).
apply H11.
move=> H11.
elim (excluded_middle_informative (proj1_sig k2 < M)).
move=> H12 H13.
apply False_ind.
apply (le_not_lt M (proj1_sig (proj1_sig (exist (fun m : Count (M + N) => proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig (f (exist (fun n : nat => n < L) (proj1_sig k1 - M) (H9 k1 H11)))) (H10 k1 H11))))).
apply (proj1 (proj2_sig (f (exist (fun n : nat => n < L) (proj1_sig k1 - M) (H9 k1 H11))))).
rewrite H13.
apply H12.
move=> H12 H13.
apply sig_map.
suff: (proj1_sig k1 - M = proj1_sig k2 - M).
move=> H14.
rewrite - (Minus.le_plus_minus_r M (proj1_sig k1)).
rewrite - (Minus.le_plus_minus_r M (proj1_sig k2)).
rewrite H14.
reflexivity.
elim (le_or_lt M (proj1_sig k2)).
apply.
move=> H15.
apply False_ind.
apply (H12 H15).
elim (le_or_lt M (proj1_sig k1)).
apply.
move=> H15.
apply False_ind.
apply (H11 H15).
suff: ((exist (fun n : nat => n < L) (proj1_sig k1 - M) (H9 k1 H11)) = (exist (fun n : nat => n < L) (proj1_sig k2 - M) (H9 k2 H12))).
move=> H14.
suff: (proj1_sig k1 - M = proj1_sig (exist (fun n : nat => n < L) (proj1_sig k1 - M) (H9 k1 H11))).
move=> H15.
rewrite H15.
rewrite H14.
reflexivity.
reflexivity.
apply (BijInj {n : nat | n < L} {m : Count (M + N) | M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)} f H7).
apply sig_map.
suff: (proj1_sig (f (exist (fun n : nat => n < L) (proj1_sig k1 - M) (H9 k1 H11))) = proj1_sig (exist (fun m : Count (M + N) => proj1_sig m < M \/ M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig (f (exist (fun n : nat => n < L) (proj1_sig k1 - M) (H9 k1 H11)))) (H10 k1 H11))).
move=> H14.
rewrite H14.
rewrite H13.
reflexivity.
reflexivity.
move=> v.
elim (proj2_sig v).
move=> H11.
exists (exist (fun (n : nat) => n < M + L) (proj1_sig (proj1_sig v)) (le_trans (S (proj1_sig (proj1_sig v))) M (M + L) H11 (Plus.le_plus_l M L))).
simpl.
elim (excluded_middle_informative (proj1_sig (proj1_sig v) < M)).
move=> H12.
apply sig_map.
apply sig_map.
reflexivity.
move=> H12.
apply False_ind.
apply (H12 H11).
move=> H11.
elim H7.
move=> finv H12.
suff: (M + proj1_sig (finv (exist (fun (m : Count (M + N)) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H11)) < M + L).
move=> H13.
exists (exist (fun (n : nat) => n < M + L) (M + proj1_sig (finv (exist (fun (m : Count (M + N)) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H11))) H13).
simpl.
elim (excluded_middle_informative (M + proj1_sig (finv (exist (fun m : Count (M + N) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H11)) < M)).
move=> H14.
apply False_ind.
apply (lt_irrefl M).
apply (le_trans (S M) (S (M + proj1_sig (finv (exist (fun m : Count (M + N) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H11)))) M).
apply le_n_S.
apply (Plus.le_plus_l M).
apply H14.
move=> H14.
apply sig_map.
apply sig_map.
simpl.
suff: ((exist (fun n : nat => n < L) (M + proj1_sig (finv (exist (fun m : Count (M + N) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H11)) - M) (H9 (exist (fun n : nat => n < M + L) (M + proj1_sig (finv (exist (fun m : Count (M + N) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H11))) H13) H14)) = (finv (exist (fun m : Count (M + N) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H11))).
move=> H15.
rewrite H15.
rewrite (proj2 H12).
reflexivity.
apply sig_map.
apply Minus.minus_plus.
apply Plus.plus_lt_compat_l.
apply (proj2_sig (finv (exist (fun m : Count (M + N) => M <= proj1_sig m /\ ~ In (VT K V) (SpanVS K V {n : Count (M + N) | proj1_sig n < proj1_sig m} (fun k : {n : Count (M + N) | proj1_sig n < proj1_sig m} => F2 (proj1_sig k))) (F2 m)) (proj1_sig v) H11))).
move=> m H10.
right.
apply (proj2_sig (f (exist (fun n : nat => n < L) (proj1_sig m - M) (H9 m H10)))).
move=> m H9.
apply (Plus.plus_lt_reg_l (proj1_sig m - M) L M).
rewrite - (Minus.le_plus_minus M (proj1_sig m)).
apply (proj2_sig m).
elim (le_or_lt M (proj1_sig m)).
apply.
move=> H10.
apply False_ind.
apply (H9 H10).
move=> m H8.
left.
apply H8.
apply (Corollary_5_7_3 K V M F H2).
apply (SubspaceBasisLinearlyIndependentVS K V W H1 (Count M) F H3).
apply (FiniteSigSame (Count (M + N))).
apply (Finite_downward_closed (Count (M + N)) (Full_set (Count (M + N))) (CountFinite (M + N))).
move=> v H7.
apply (Full_intro (Count (M + N)) v).
apply (Theorem_5_6 K V M (M + N) (Plus.le_plus_l M N) H5 F2).
suff: ((fun m : Count M => F2 (exist (fun n : nat => n < M + N) (proj1_sig m) (H5 m))) = F).
move=> H12.
rewrite H12.
apply (SubspaceBasisLinearlyIndependentVS K V W H1 (Count M) F H3).
apply functional_extensionality.
move=> m.
unfold F2.
simpl.
elim (excluded_middle_informative (proj1_sig m < M)).
move=> H12.
suff: ((exist (fun n : nat => n < M) (proj1_sig m) H12) = m).
move=> H13.
rewrite H13.
reflexivity.
apply sig_map.
reflexivity.
move=> H12.
apply False_ind.
apply (H12 (proj2_sig m)).
apply Extensionality_Ensembles.
apply conj.
rewrite (proj2 (proj1 (BasisLIGeVS K V (Count N) G) H4)).
move=> v.
elim.
move=> x H12.
rewrite H12.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 (SpanSubspaceVS K V (Count (M + N)) F2))).
move=> cm u H13 H14.
apply (proj1 (SpanSubspaceVS K V (Count (M + N)) F2)).
apply H14.
apply (proj1 (proj2 (SpanSubspaceVS K V (Count (M + N)) F2))).
suff: (M + proj1_sig u < M + N).
move=> H15.
suff: (G u = F2 (exist (fun (n : nat) => n < M + N) (M + proj1_sig u) H15)).
move=> H16.
rewrite H16.
apply (SpanContainSelfVS K V (Count (M + N)) F2 (exist (fun (n : nat) => n < M + N) (M + proj1_sig u) H15)).
unfold F2.
simpl.
elim (excluded_middle_informative (M + proj1_sig u < M)).
move=> H16.
apply False_ind.
apply (lt_irrefl M).
apply (le_trans (S M) (S (M + proj1_sig u)) M).
apply (le_n_S M (M + proj1_sig u) (Plus.le_plus_l M (proj1_sig u))).
apply H16.
move=> H16.
suff: (u = (exist (fun n : nat => n < N) (M + proj1_sig u - M) (H6 (exist (fun n : nat => n < M + N) (M + proj1_sig u) H15) H16))).
move=> H17.
rewrite {1} H17.
reflexivity.
apply sig_map.
simpl.
rewrite Minus.minus_plus.
reflexivity.
apply (Plus.plus_lt_compat_l (proj1_sig u) N M (proj2_sig u)).
move=> v H12.
apply (Full_intro (VT K V) v).
move=> m H6.
apply (Plus.plus_lt_reg_l (proj1_sig m - M) N M).
rewrite (Minus.le_plus_minus_r M (proj1_sig m)).
apply (proj2_sig m).
elim (le_or_lt M (proj1_sig m)).
apply.
move=> H7.
apply False_ind.
apply (H6 H7).
move=> m.
apply (le_trans (S (proj1_sig m)) M (M + N) (proj2_sig m) (Plus.le_plus_l M N)).
Qed.

Lemma Proposition_5_9_2_exists : forall (K : Field) (V : VectorSpace K) (W : Ensemble (VT K V)) (H1 : SubspaceVS K V W) (H2 : FiniteDimensionVS K V) (M : nat) (F : Count M -> VT K V), exists (H3 : forall m : Count (DimensionVS K V H2), ~ proj1_sig m < M -> proj1_sig m - M < DimensionVS K V H2 - M), BasisSubspaceVS K V W H1 (Count M) F -> exists G : Count (DimensionVS K V H2 - M) -> VT K V, BasisVS K V (Count (DimensionVS K V H2)) (fun m : Count (DimensionVS K V H2) => match excluded_middle_informative (proj1_sig m < M) with
  | left H => F (exist (fun n : nat => n < M) (proj1_sig m) H)
  | right H => G (exist (fun n : nat => n < DimensionVS K V H2 - M) (proj1_sig m - M) (H3 m H))
end).
Proof.
move=> K V W H1 H2 M F.
suff: (forall m : Count (DimensionVS K V H2), ~ proj1_sig m < M -> proj1_sig m - M < DimensionVS K V H2 - M).
move=> H3.
exists H3.
apply (Proposition_5_9_2 K V W H1 H2 M F H3).
move=> m H3.
apply (Plus.plus_lt_reg_l (proj1_sig m - M) (DimensionVS K V H2 - M) M).
suff: (M <= proj1_sig m).
move=> H4.
rewrite (Minus.le_plus_minus_r M (proj1_sig m) H4).
rewrite (Minus.le_plus_minus_r M (DimensionVS K V H2)).
apply (proj2_sig m).
apply (le_trans M (proj1_sig m) (DimensionVS K V H2) H4 (lt_le_weak (proj1_sig m) (DimensionVS K V H2) (proj2_sig m))).
elim (le_or_lt M (proj1_sig m)).
apply.
move=> H4.
apply False_ind.
apply (H3 H4).
Qed.

Lemma Proposition_5_9_3 : forall (K : Field) (V : VectorSpace K) (W1 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : FiniteDimensionVS K V), exists (W2 : Ensemble (VT K V)), (SubspaceVS K V W2) /\ (Full_set (VT K V) = SumEnsembleVS K V W1 W2) /\ (Singleton (VT K V) (VO K V) = Intersection (VT K V) W1 W2).
Proof.
move=> K V W1 H1 H2.
elim (DimensionSubspaceVSNature K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)).
move=> F H3.
elim (Proposition_5_9_2_exists K V W1 H1 H2 (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) F).
move=> H4.
elim.
move=> G H5.
exists (SpanVS K V (Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) G).
apply conj.
apply SpanSubspaceVS.
apply conj.
apply Extensionality_Ensembles.
apply conj.
rewrite (proj2 (proj1 (BasisLIGeVS K V (Count (DimensionVS K V H2)) (fun m : Count (DimensionVS K V H2) => match excluded_middle_informative (proj1_sig m < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) with
  | left H => F (exist (fun n : nat => n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig m) H)
  | right H => G (exist (fun n : nat => n < DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig m - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (H4 m H))
end)) H5)).
move=> v.
elim.
move=> x H6.
rewrite H6.
rewrite (MySumF2Excluded (Count (DimensionVS K V H2)) (VSPCM K V) (fun t : Count (DimensionVS K V H2) => Vmul K V (proj1_sig x t) match excluded_middle_informative (proj1_sig t < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) with
  | left H => F (exist (fun n : nat => n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig t) H)
  | right H => G (exist (fun n : nat => n < DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig t - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (H4 t H))
end) (exist (Finite (Count (DimensionVS K V H2))) (fun t : Count (DimensionVS K V H2) => proj1_sig x t <> FO K) (proj2_sig x)) (fun t : Count (DimensionVS K V H2) => proj1_sig t < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))).
apply SumEnsembleVS_intro.
apply MySumF2Induction.
apply conj.
apply (proj2 (proj2 H1)).
move=> cm u H7 H8.
apply (proj1 H1).
apply H8.
apply (proj1 (proj2 H1)).
elim (excluded_middle_informative (proj1_sig u < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))).
move=> H9.
elim H3.
move=> H10 H11.
apply H10.
move=> H9.
apply False_ind.
apply H9.
elim H7.
move=> t H10 H11.
apply H10.
apply MySumF2Induction.
apply conj.
apply SpanSubspaceVS.
move=> cm u H7 H8.
apply SpanSubspaceVS.
apply H8.
apply SpanSubspaceVS.
elim (excluded_middle_informative (proj1_sig u < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))).
elim H7.
move=> t H9 H10 H11.
apply False_ind.
apply (H9 H11).
move=> H9.
apply SpanContainSelfVS.
move=> v H6.
apply (Full_intro (VT K V) v).
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
apply Intersection_intro.
apply (proj2 (proj2 H1)).
apply SpanSubspaceVS.
move=> v.
elim.
move=> v0 H6 H7.
elim H3.
move=> H8 H9.
elim (proj1 (FiniteBasisVS K (SubspaceMakeVS K V W1 H1) (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (fun t : Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) => exist W1 (F t) (H8 t))) H9 (exist W1 v0 H6)).
move=> x H10.
suff: (In (VT K V) (fun v : VT K V => exists a : Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) -> FT K, v = MySumF2 (Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) (exist (Finite (Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (Full_set (Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (CountFinite (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (VSPCM K V) (fun n : Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) => Vmul K V (a n) (G n))) v0).
elim.
move=> y H11.
suff: ((fun (m : Count (DimensionVS K V H2)) => match excluded_middle_informative (proj1_sig m < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) with 
  | left H => x (exist (fun (n : nat) => n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig m) H)
  | right _ => FO K
end) = (fun (m : Count (DimensionVS K V H2)) => match excluded_middle_informative (proj1_sig m < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) with 
  | left _ => FO K
  | right H => y (exist (fun n : nat => n < DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig m - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (H4 m H))
end)).
move=> H12.
suff: (forall (m : Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))), x m = FO K).
move=> H13.
suff: (v0 = proj1_sig (exist W1 v0 H6)).
move=> H14.
rewrite H14.
rewrite (proj1 H10).
suff: ((proj1_sig (MySumF2 (Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) (exist (Finite (Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (Full_set (Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (CountFinite (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (VSPCM K (SubspaceMakeVS K V W1 H1)) (fun n : Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) => Vmul K (SubspaceMakeVS K V W1 H1) (x n) (exist W1 (F n) (H8 n))))) = VO K V).
move=> H15.
rewrite H15.
apply In_singleton.
apply MySumF2Induction.
apply conj.
reflexivity.
move=> cm u H15 H16.
rewrite (H13 u).
rewrite (Vmul_O_l K).
simpl.
rewrite H16.
apply (Vadd_O_l K V (VO K V)).
reflexivity.
move=> m.
suff: (proj1_sig m < DimensionVS K V H2).
move=> H13.
suff: (x m = let temp := (fun m : Count (DimensionVS K V H2) => match excluded_middle_informative (proj1_sig m < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) with
  | left _ => FO K
  | right H => y (exist (fun n : nat => n < DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig m - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (H4 m H))
end) in temp (exist (fun (n : nat) => n < DimensionVS K V H2) (proj1_sig m) H13)).
move=> H14.
rewrite H14.
simpl.
elim (excluded_middle_informative (proj1_sig m < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))).
move=> H15.
reflexivity.
move=> H15.
apply False_ind.
apply (H15 (proj2_sig m)).
rewrite - H12.
simpl.
elim (excluded_middle_informative (proj1_sig m < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))).
move=> H14.
suff: (m = (exist (fun n : nat => n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig m) H14)).
move=> H15.
rewrite {1} H15.
reflexivity.
apply sig_map.
reflexivity.
move=> H14.
apply False_ind.
apply (H14 (proj2_sig m)).
apply (le_trans (S (proj1_sig m)) (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (DimensionVS K V H2) (proj2_sig m)).
apply (Proposition_5_9_1_2 K V W1 H1 H2 (Proposition_5_9_1_1 K V H2 W1 H1)).
apply (proj2 (unique_existence (fun (a : Count (DimensionVS K V H2) -> FT K) => v0 = MySumF2 (Count (DimensionVS K V H2)) (exist (Finite (Count (DimensionVS K V H2))) (Full_set (Count (DimensionVS K V H2))) (CountFinite (DimensionVS K V H2))) (VSPCM K V) (fun n : Count (DimensionVS K V H2) => Vmul K V (a n) match excluded_middle_informative (proj1_sig n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) with
  | left H => F (exist (fun n0 : nat => n0 < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig n) H)
  | right H => G (exist (fun n0 : nat => n0 < DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig n - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (H4 n H))
end)))).
apply (proj1 (FiniteBasisVS K V (DimensionVS K V H2) (fun m : Count (DimensionVS K V H2) => match excluded_middle_informative (proj1_sig m < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) with
  | left H => F (exist (fun n : nat => n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig m) H)
  | right H => G (exist (fun n : nat => n < DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig m - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (H4 m H))
end)) H5 v0).
rewrite (MySumF2Included (Count (DimensionVS K V H2)) (FiniteIntersection (Count (DimensionVS K V H2)) (exist (Finite (Count (DimensionVS K V H2))) (Full_set (Count (DimensionVS K V H2))) (CountFinite (DimensionVS K V H2))) (fun n : Count (DimensionVS K V H2) => proj1_sig n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) (exist (Finite (Count (DimensionVS K V H2))) (Full_set (Count (DimensionVS K V H2))) (CountFinite (DimensionVS K V H2)))).
rewrite (MySumF2O (Count (DimensionVS K V H2)) (FiniteIntersection (Count (DimensionVS K V H2)) (exist (Finite (Count (DimensionVS K V H2))) (Full_set (Count (DimensionVS K V H2))) (CountFinite (DimensionVS K V H2))) (Complement (Count (DimensionVS K V H2)) (proj1_sig (FiniteIntersection (Count (DimensionVS K V H2)) (exist (Finite (Count (DimensionVS K V H2))) (Full_set (Count (DimensionVS K V H2))) (CountFinite (DimensionVS K V H2))) (fun n : Count (DimensionVS K V H2) => proj1_sig n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))))))).
simpl.
rewrite (Vadd_O_r K V).
suff: (v0 = proj1_sig (exist W1 v0 H6)).
move=> H13.
rewrite H13.
rewrite (proj1 H10).
suff: (forall (m : Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))), proj1_sig m < DimensionVS K V H2).
move=> H12.
rewrite - (MySumF2BijectiveSame (Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) (exist (Finite (Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (Full_set (Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (CountFinite (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (Count (DimensionVS K V H2)) (FiniteIntersection (Count (DimensionVS K V H2)) (exist (Finite (Count (DimensionVS K V H2))) (Full_set (Count (DimensionVS K V H2))) (CountFinite (DimensionVS K V H2))) (fun n : Count (DimensionVS K V H2) => proj1_sig n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) (VSPCM K V) (fun n : Count (DimensionVS K V H2) => Vmul K V match excluded_middle_informative (proj1_sig n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) with
  | left H => x (exist (fun n0 : nat => n0 < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig n) H)
  | right _ => FO K
end match excluded_middle_informative (proj1_sig n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) with
  | left H => F (exist (fun n0 : nat => n0 < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig n) H)
  | right H => G (exist (fun n0 : nat => n0 < DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig n - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (H4 n H))
end) (fun (m : Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) => exist (fun (n : nat) => n < DimensionVS K V H2) (proj1_sig m) (H12 m))).
apply (FiniteSetInduction (Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) (exist (Finite (Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (Full_set (Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (CountFinite (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H14 H15 H16 H17.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H17.
elim (excluded_middle_informative (proj1_sig b < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))).
move=> H18.
suff: ((exist (fun n0 : nat => n0 < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig b) H18) = b).
move=> H19.
rewrite H19.
reflexivity.
apply sig_map.
reflexivity.
move=> H18.
apply False_ind.
apply (H18 (proj2_sig b)).
apply H16.
apply H16.
move=> u H14.
apply Intersection_intro.
apply (proj2_sig u).
apply (Full_intro (Count (DimensionVS K V H2))).
move=> H14.
simpl.
apply InjSurjBij.
move=> k1 k2 H15.
apply sig_map.
apply sig_map.
suff: (proj1_sig (proj1_sig k1) = proj1_sig (proj1_sig (exist (Intersection (Count (DimensionVS K V H2)) (fun n : Count (DimensionVS K V H2) => proj1_sig n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (Full_set (Count (DimensionVS K V H2)))) (exist (fun n : nat => n < DimensionVS K V H2) (proj1_sig (proj1_sig k1)) (H12 (proj1_sig k1))) (H14 (proj1_sig k1) (proj2_sig k1))))).
move=> H16.
rewrite H16.
rewrite H15.
reflexivity.
reflexivity.
move=> u.
suff: (proj1_sig (proj1_sig u) < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)).
move=> H15.
exists (exist (Full_set (Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (exist (fun (n : nat) => n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig (proj1_sig u)) H15) (Full_intro (Count (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) (exist (fun (n : nat) => n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig (proj1_sig u)) H15))).
apply sig_map.
apply sig_map.
reflexivity.
elim (proj2_sig u).
move=> u0 H15 H16.
apply H15.
move=> m.
apply (le_trans (S (proj1_sig m)) (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (DimensionVS K V H2) (proj2_sig m)).
apply (Proposition_5_9_1_2 K V W1 H1 H2 (Proposition_5_9_1_1 K V H2 W1 H1)).
reflexivity.
move=> u H12.
elim (excluded_middle_informative (proj1_sig u < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))).
elim H12.
move=> u0 H13 H14 H15.
apply False_ind.
apply H13.
apply Intersection_intro.
apply H15.
apply Full_intro.
move=> H13.
apply (Vmul_O_l K V).
move=> m H12.
apply (Full_intro (Count (DimensionVS K V H2)) m).
rewrite H11.
rewrite (MySumF2Included (Count (DimensionVS K V H2)) (FiniteIntersection (Count (DimensionVS K V H2)) (exist (Finite (Count (DimensionVS K V H2))) (Full_set (Count (DimensionVS K V H2))) (CountFinite (DimensionVS K V H2))) (fun n : Count (DimensionVS K V H2) => ~ proj1_sig n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) (exist (Finite (Count (DimensionVS K V H2))) (Full_set (Count (DimensionVS K V H2))) (CountFinite (DimensionVS K V H2)))).
rewrite (MySumF2O (Count (DimensionVS K V H2)) (FiniteIntersection (Count (DimensionVS K V H2)) (exist (Finite (Count (DimensionVS K V H2))) (Full_set (Count (DimensionVS K V H2))) (CountFinite (DimensionVS K V H2))) (Complement (Count (DimensionVS K V H2)) (proj1_sig (FiniteIntersection (Count (DimensionVS K V H2)) (exist (Finite (Count (DimensionVS K V H2))) (Full_set (Count (DimensionVS K V H2))) (CountFinite (DimensionVS K V H2))) (fun n : Count (DimensionVS K V H2) => ~ proj1_sig n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))))))).
simpl.
rewrite (Vadd_O_r K V).
suff: (forall (m : Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))), proj1_sig m + (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) < DimensionVS K V H2).
move=> H12.
rewrite - (MySumF2BijectiveSame (Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) (exist (Finite (Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (Full_set (Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (CountFinite (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (Count (DimensionVS K V H2)) (FiniteIntersection (Count (DimensionVS K V H2)) (exist (Finite (Count (DimensionVS K V H2))) (Full_set (Count (DimensionVS K V H2))) (CountFinite (DimensionVS K V H2))) (fun n : Count (DimensionVS K V H2) => ~ proj1_sig n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) (VSPCM K V) (fun n : Count (DimensionVS K V H2) => Vmul K V match excluded_middle_informative (proj1_sig n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) with
  | left _ => FO K
  | right H => y (exist (fun n0 : nat => n0 < DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig n - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (H4 n H))
end match excluded_middle_informative (proj1_sig n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) with
  | left H => F (exist (fun n0 : nat => n0 < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig n) H)
  | right H => G (exist (fun n0 : nat => n0 < DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig n - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (H4 n H))
end) (fun (m : Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) => exist (fun (n : nat) => n < DimensionVS K V H2) (proj1_sig m + DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (H12 m))).
apply (FiniteSetInduction (Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) (exist (Finite (Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (Full_set (Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (CountFinite (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H13 H14 H15 H16.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H16.
elim (excluded_middle_informative (proj1_sig b + DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1) < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))).
move=> H17.
apply False_ind.
apply (lt_not_le (proj1_sig b + DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) H17 (Plus.le_plus_r (proj1_sig b) (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))).
move=> H17.
suff: ((exist (fun n0 : nat => n0 < DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig b + DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1) - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (H4 (exist (fun n : nat => n < DimensionVS K V H2) (proj1_sig b + DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (H12 b)) H17)) = b).
move=> H18.
rewrite H18.
reflexivity.
apply sig_map.
simpl.
rewrite Plus.plus_comm.
apply Minus.minus_plus.
apply H15.
apply H15.
move=> u H13.
apply Intersection_intro.
move=> H14.
apply False_ind.
apply (le_not_lt (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig u + DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (Plus.le_plus_r (proj1_sig u) (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) H14).
apply (Full_intro (Count (DimensionVS K V H2))).
move=> H13.
simpl.
apply InjSurjBij.
move=> k1 k2 H14.
apply sig_map.
apply sig_map.
apply (Plus.plus_reg_l (proj1_sig (proj1_sig k1)) (proj1_sig (proj1_sig k2)) (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))).
rewrite (Plus.plus_comm (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))).
rewrite (Plus.plus_comm (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))).
suff: (proj1_sig (proj1_sig k1) + DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1) = proj1_sig (proj1_sig (exist (Intersection (Count (DimensionVS K V H2)) (fun n : Count (DimensionVS K V H2) => ~ proj1_sig n < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (Full_set (Count (DimensionVS K V H2)))) (exist (fun n : nat => n < DimensionVS K V H2) (proj1_sig (proj1_sig k1) + DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (H12 (proj1_sig k1))) (H13 (proj1_sig k1) (proj2_sig k1))))).
move=> H15.
rewrite H15.
rewrite H14.
reflexivity.
reflexivity.
move=> u.
suff: (proj1_sig (proj1_sig u) - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1) < DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)).
move=> H14.
exists (exist (Full_set (Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)))) (exist (fun (n : nat) => n < DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig (proj1_sig u) - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) H14) (Full_intro (Count (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))) (exist (fun (n : nat) => n < DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig (proj1_sig u) - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) H14))).
apply sig_map.
apply sig_map.
simpl.
rewrite Plus.plus_comm.
apply Minus.le_plus_minus_r.
elim (proj2_sig u).
move=> m H15 H16.
elim (le_or_lt (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig m)).
apply.
move=> H17.
apply False_ind.
apply (H15 H17).
apply (Plus.plus_lt_reg_l (proj1_sig (proj1_sig u) - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))).
rewrite (Minus.le_plus_minus_r (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (DimensionVS K V H2)).
rewrite (Minus.le_plus_minus_r (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig (proj1_sig u))).
apply (proj2_sig (proj1_sig u)).
elim (proj2_sig u).
move=> u0 H14 H15.
elim (le_or_lt (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (proj1_sig u0)).
apply.
move=> H16.
apply False_ind.
apply (H14 H16).
apply (Proposition_5_9_1_2 K V W1 H1 H2 (Proposition_5_9_1_1 K V H2 W1 H1)).
move=> m.
rewrite - {2} (Minus.le_plus_minus_r (DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) (DimensionVS K V H2)).
rewrite Plus.plus_comm.
apply Plus.plus_lt_compat_l.
apply (proj2_sig m).
apply (Proposition_5_9_1_2 K V W1 H1 H2 (Proposition_5_9_1_1 K V H2 W1 H1)).
move=> u H12.
elim (excluded_middle_informative (proj1_sig u < DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1))).
move=> H13.
apply (Vmul_O_l K V).
elim H12.
move=> u0 H13 H14 H15.
apply False_ind.
apply H13.
apply Intersection_intro.
apply H15.
apply (Full_intro (Count (DimensionVS K V H2)) u0).
move=> m H12.
apply (Full_intro (Count (DimensionVS K V H2)) m).
rewrite - (FiniteSpanVS K V (DimensionVS K V H2 - DimensionSubspaceVS K V W1 H1 (Proposition_5_9_1_1 K V H2 W1 H1)) G).
apply H7.
apply H3.
Qed.

Lemma Proposition_5_9_1_1_subspace : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2), Included (VT K V) W1 W2 -> FiniteDimensionVS K (SubspaceMakeVS K V W2 H2) -> FiniteDimensionVS K (SubspaceMakeVS K V W1 H1). 
Proof.
move=> K V W1 W2 H1 H2 H3 H4.
suff: (SubspaceVS K (SubspaceMakeVS K V W2 H2) (fun (v : (SubspaceMakeVST K V W2 H2)) => In (VT K V) W1 (proj1_sig v))).
move=> H5.
suff: (FiniteDimensionVS K (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H5)).
apply (IsomorphicSaveFiniteDimensionVS K (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H5) (SubspaceMakeVS K V W1 H1) (fun (v : (SubspaceMakeVST K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H5)) => exist W1 (proj1_sig (proj1_sig v)) (proj2_sig v))).
apply conj.
exists (fun (v : (SubspaceMakeVST K V W1 H1)) => exist (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) (exist W2 (proj1_sig v) (H3 (proj1_sig v) (proj2_sig v))) (proj2_sig v)).
apply conj.
move=> x.
apply sig_map.
apply sig_map.
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
apply (Proposition_5_9_1_1 K (SubspaceMakeVS K V W2 H2) H4).
apply conj.
move=> v1 v2 H5 H6.
apply (proj1 H1 (proj1_sig v1) (proj1_sig v2) H5 H6).
apply conj.
move=> c v H5.
apply (proj1 (proj2 H1) c (proj1_sig v) H5).
apply (proj2 (proj2 H1)).
Qed.

Lemma Proposition_5_9_1_2_subspace : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2), Included (VT K V) W1 W2 -> forall (H3 : FiniteDimensionVS K (SubspaceMakeVS K V W2 H2)) (H4 : FiniteDimensionVS K (SubspaceMakeVS K V W1 H1)), DimensionSubspaceVS K V W2 H2 H3 >= DimensionSubspaceVS K V W1 H1 H4.
Proof.
move=> K V W1 W2 H1 H2 H3 H5 H4.
suff: (SubspaceVS K (SubspaceMakeVS K V W2 H2) (fun (v : (SubspaceMakeVST K V W2 H2)) => In (VT K V) W1 (proj1_sig v))).
move=> H6.
suff: (IsomorphicVS K (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H6) (SubspaceMakeVS K V W1 H1) (fun v : SubspaceMakeVST K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H6 => exist W1 (proj1_sig (proj1_sig v)) (proj2_sig v))).
move=> H7.
suff: (FiniteDimensionVS K (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H6)).
move=> H8.
unfold DimensionSubspaceVS.
rewrite - (IsomorphicSaveDimensionVS K (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H6) (SubspaceMakeVS K V W1 H1) (fun v : SubspaceMakeVST K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H6 => exist W1 (proj1_sig (proj1_sig v)) (proj2_sig v)) H8 H4 H7).
apply (Proposition_5_9_1_2 K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H6 H5 H8).
apply (Proposition_5_9_1_1 K (SubspaceMakeVS K V W2 H2) H5).
apply conj.
exists (fun (v : (SubspaceMakeVST K V W1 H1)) => exist (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) (exist W2 (proj1_sig v) (H3 (proj1_sig v) (proj2_sig v))) (proj2_sig v)).
apply conj.
move=> x.
apply sig_map.
apply sig_map.
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
apply conj.
move=> v1 v2 H6 H7.
apply (proj1 H1 (proj1_sig v1) (proj1_sig v2) H6 H7).
apply conj.
move=> c v H6.
apply (proj1 (proj2 H1) c (proj1_sig v) H6).
apply (proj2 (proj2 H1)).
Qed.

Lemma Proposition_5_9_1_2_subspace_exists : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2), Included (VT K V) W1 W2 -> forall (H3 : FiniteDimensionVS K (SubspaceMakeVS K V W2 H2)), exists (H4 : FiniteDimensionVS K (SubspaceMakeVS K V W1 H1)), DimensionSubspaceVS K V W2 H2 H3 >= DimensionSubspaceVS K V W1 H1 H4.
Proof.
move=> K V W1 W2 H1 H2 H3 H4.
suff: (FiniteDimensionVS K (SubspaceMakeVS K V W1 H1)).
move=> H5.
exists H5.
apply (Proposition_5_9_1_2_subspace K V W1 W2 H1 H2 H3 H4 H5).
apply (Proposition_5_9_1_1_subspace K V W1 W2 H1 H2 H3 H4).
Qed.

Lemma Proposition_5_9_1_3_subspace : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2), Included (VT K V) W1 W2 -> forall (H3 : FiniteDimensionVS K (SubspaceMakeVS K V W2 H2)) (H4 : FiniteDimensionVS K (SubspaceMakeVS K V W1 H1)), DimensionSubspaceVS K V W1 H1 H4 = DimensionSubspaceVS K V W2 H2 H3 <-> W1 = W2.
Proof.
move=> K V W1 W2 H1 H2 H3 H5 H4.
suff: (SubspaceVS K (SubspaceMakeVS K V W2 H2) (fun (v : (SubspaceMakeVST K V W2 H2)) => In (VT K V) W1 (proj1_sig v))).
move=> H6.
suff: (IsomorphicVS K (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H6) (SubspaceMakeVS K V W1 H1) (fun v : SubspaceMakeVST K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H6 => exist W1 (proj1_sig (proj1_sig v)) (proj2_sig v))).
move=> H7.
suff: (FiniteDimensionVS K (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H6)).
move=> H8.
unfold DimensionSubspaceVS.
rewrite - (IsomorphicSaveDimensionVS K (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H6) (SubspaceMakeVS K V W1 H1) (fun v : SubspaceMakeVST K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H6 => exist W1 (proj1_sig (proj1_sig v)) (proj2_sig v)) H8 H4 H7).
suff: (DimensionVS K (SubspaceMakeVS K V W2 H2) H5 = DimensionVS K (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H6) H8 <-> (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) = Full_set (SubspaceMakeVST K V W2 H2)).
move=> H9.
apply conj.
move=> H10.
suff: ((fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) = Full_set (SubspaceMakeVST K V W2 H2)).
move=> H11.
apply Extensionality_Ensembles.
apply conj.
move=> v.
apply (H3 v).
move=> v H12.
suff: (In (SubspaceMakeVST K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) (exist W2 v H12)).
apply.
rewrite H11.
apply (Full_intro (SubspaceMakeVST K V W2 H2)).
apply (proj1 H9).
rewrite H10.
reflexivity.
move=> H10.
rewrite (proj2 H9).
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> v H11.
apply (Full_intro (SubspaceMakeVST K V W2 H2) v).
move=> v H11.
rewrite H10.
apply (proj2_sig v).
apply (Proposition_5_9_1_3 K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H6 H5 H8).
apply (Proposition_5_9_1_1 K (SubspaceMakeVS K V W2 H2) H5).
apply conj.
exists (fun (v : (SubspaceMakeVST K V W1 H1)) => exist (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) (exist W2 (proj1_sig v) (H3 (proj1_sig v) (proj2_sig v))) (proj2_sig v)).
apply conj.
move=> x.
apply sig_map.
apply sig_map.
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
apply conj.
move=> v1 v2 H6 H7.
apply (proj1 H1 (proj1_sig v1) (proj1_sig v2) H6 H7).
apply conj.
move=> c v H6.
apply (proj1 (proj2 H1) c (proj1_sig v) H6).
apply (proj2 (proj2 H1)).
Qed.

Lemma Proposition_5_9_1_3_subspace_exists : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2), Included (VT K V) W1 W2 -> forall (H3 : FiniteDimensionVS K (SubspaceMakeVS K V W2 H2)), exists (H4 : FiniteDimensionVS K (SubspaceMakeVS K V W1 H1)), DimensionSubspaceVS K V W1 H1 H4 = DimensionSubspaceVS K V W2 H2 H3 <-> W1 = W2.
Proof.
move=> K V W1 W2 H1 H2 H3 H4.
suff: (FiniteDimensionVS K (SubspaceMakeVS K V W1 H1)).
move=> H5.
exists H5.
apply (Proposition_5_9_1_3_subspace K V W1 W2 H1 H2 H3 H4 H5).
apply (Proposition_5_9_1_1_subspace K V W1 W2 H1 H2 H3 H4).
Qed.

Lemma Proposition_5_9_2_subspace : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2) (H3 : FiniteDimensionVS K (SubspaceMakeVS K V W2 H2)), Included (VT K V) W1 W2 -> forall (M : nat) (F : Count M -> VT K V) (H4 : forall m : Count (DimensionSubspaceVS K V W2 H2 H3), ~ proj1_sig m < M -> proj1_sig m - M < DimensionSubspaceVS K V W2 H2 H3 - M), BasisSubspaceVS K V W1 H1 (Count M) F -> exists (G : Count (DimensionSubspaceVS K V W2 H2 H3 - M) -> VT K V), BasisSubspaceVS K V W2 H2 (Count (DimensionSubspaceVS K V W2 H2 H3)) (fun m : Count (DimensionSubspaceVS K V W2 H2 H3) => match excluded_middle_informative (proj1_sig m < M) with
  | left H => F (exist (fun n : nat => n < M) (proj1_sig m) H)
  | right H => G (exist (fun n : nat => n < DimensionSubspaceVS K V W2 H2 H3 - M) (proj1_sig m - M) (H4 m H))
end).
Proof.
move=> K V W1 W2 H1 H2 H3 H4 M F H5 H6.
suff: (SubspaceVS K (SubspaceMakeVS K V W2 H2) (fun (v : (SubspaceMakeVST K V W2 H2)) => In (VT K V) W1 (proj1_sig v))).
move=> H7.
suff: (IsomorphicVS K (SubspaceMakeVS K V W1 H1) (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H7) (fun (v : SubspaceMakeVST K V W1 H1) => exist (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) (exist W2 (proj1_sig v) (H4 (proj1_sig v) (proj2_sig v))) (proj2_sig v))).
move=> H8.
suff: (FiniteDimensionVS K (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H7)).
move=> H9.
suff: (forall (m : Count M), In (VT K V) W2 (F m)).
move=> H10.
elim (Proposition_5_9_2 K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H7 H3 M (fun (m : Count M) => exist W2 (F m) (H10 m)) H5).
move=> G H11.
exists (fun (m : Count (DimensionSubspaceVS K V W2 H2 H3 - M)) => proj1_sig (G m)).
suff: (forall t : Count (DimensionSubspaceVS K V W2 H2 H3), In (VT K V) W2 match excluded_middle_informative (proj1_sig t < M) with
  | left H => F (exist (fun n : nat => n < M) (proj1_sig t) H)
  | right H => proj1_sig (G (exist (fun n : nat => n < DimensionSubspaceVS K V W2 H2 H3 - M) (proj1_sig t - M) (H5 t H)))
end).
move=> H12.
exists H12.
suff: ((fun t : Count (DimensionSubspaceVS K V W2 H2 H3) => exist W2 match excluded_middle_informative (proj1_sig t < M) with
  | left H => F (exist (fun n : nat => n < M) (proj1_sig t) H)
  | right H => proj1_sig (G (exist (fun n : nat => n < DimensionSubspaceVS K V W2 H2 H3 - M) (proj1_sig t - M) (H5 t H)))
end (H12 t)) = (fun m : Count (DimensionVS K (SubspaceMakeVS K V W2 H2) H3) => match excluded_middle_informative (proj1_sig m < M) with
  | left H => exist W2 (F (exist (fun n : nat => n < M) (proj1_sig m) H)) (H10 (exist (fun n : nat => n < M) (proj1_sig m) H))
  | right H => G (exist (fun n : nat => n < DimensionVS K (SubspaceMakeVS K V W2 H2) H3 - M) (proj1_sig m - M) (H5 m H))
end)).
move=> H13.
rewrite H13.
apply H11.
apply functional_extensionality.
move=> m.
apply sig_map.
simpl.
elim (excluded_middle_informative (lt (@proj1_sig nat (fun n : nat => lt n (DimensionVS K (SubspaceMakeVS K V W2 H2) H3)) m) M)).
move=> H13.
elim (excluded_middle_informative (proj1_sig m < M)).
move=> H14.
simpl.
suff: (H14 = H13).
move=> H15.
rewrite H15.
reflexivity.
apply proof_irrelevance.
move=> H14.
apply False_ind.
apply (H14 H13).
move=> H13.
elim (excluded_middle_informative (proj1_sig m < M)).
move=> H14.
apply False_ind.
apply (H13 H14).
move=> H14.
suff: (H14 = H13).
move=> H15.
rewrite H15.
reflexivity.
apply proof_irrelevance.
move=> m.
elim (excluded_middle_informative (proj1_sig m < M)).
move=> H12.
apply (H4 (F (exist (fun n : nat => n < M) (proj1_sig m) H12))).
elim H6.
move=> H13 H14.
apply (H13 (exist (fun n : nat => n < M) (proj1_sig m) H12)).
move=> H12.
apply (proj2_sig (G (exist (fun n : nat => n < DimensionSubspaceVS K V W2 H2 H3 - M) (proj1_sig m - M) (H5 m H12)))).
elim H6.
move=> H11 H12.
exists H11.
suff: ((fun t : Count M => exist (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) (exist W2 (F t) (H10 t)) (H11 t)) = (fun t : Count M => exist (fun v0 : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v0)) (exist W2 (proj1_sig (exist W1 (F t) (H11 t))) (H4 (proj1_sig (exist W1 (F t) (H11 t))) (proj2_sig (exist W1 (F t) (H11 t))))) (proj2_sig (exist W1 (F t) (H11 t))))).
move=> H13.
rewrite H13.
apply (IsomorphicSaveBasisVS K (SubspaceMakeVS K V W1 H1) (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H7) (Count M) (fun t : Count M => exist W1 (F t) (H11 t)) (fun v : SubspaceMakeVST K V W1 H1 => exist (fun v0 : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v0)) (exist W2 (proj1_sig v) (H4 (proj1_sig v) (proj2_sig v))) (proj2_sig v)) H8 H12).
apply functional_extensionality.
move=> m.
apply sig_map.
apply sig_map.
reflexivity.
elim H6.
move=> H10 H11 m.
apply (H4 (F m) (H10 m)).
apply (Proposition_5_9_1_1 K (SubspaceMakeVS K V W2 H2) H3 (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H7).
apply conj.
exists (fun (t : (SubspaceMakeVST K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H7)) => exist W1 (proj1_sig (proj1_sig t)) (proj2_sig t)).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
apply sig_map.
reflexivity.
apply conj.
move=> x y.
apply sig_map.
apply sig_map.
reflexivity.
move=> c x.
apply sig_map.
apply sig_map.
reflexivity.
apply conj.
move=> x y H7 H8.
apply (proj1 H1 (proj1_sig x) (proj1_sig y) H7 H8).
apply conj.
move=> f x H7.
apply (proj1 (proj2 H1) f (proj1_sig x) H7).
apply (proj2 (proj2 H1)).
Qed.

Lemma Proposition_5_9_2_subspace_exists : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2) (H3 : FiniteDimensionVS K (SubspaceMakeVS K V W2 H2)), Included (VT K V) W1 W2 -> forall (M : nat) (F : Count M -> VT K V), exists (H4 : forall m : Count (DimensionSubspaceVS K V W2 H2 H3), ~ proj1_sig m < M -> proj1_sig m - M < DimensionSubspaceVS K V W2 H2 H3 - M), BasisSubspaceVS K V W1 H1 (Count M) F -> exists (G : Count (DimensionSubspaceVS K V W2 H2 H3 - M) -> VT K V), BasisSubspaceVS K V W2 H2 (Count (DimensionSubspaceVS K V W2 H2 H3)) (fun m : Count (DimensionSubspaceVS K V W2 H2 H3) => match excluded_middle_informative (proj1_sig m < M) with
  | left H => F (exist (fun n : nat => n < M) (proj1_sig m) H)
  | right H => G (exist (fun n : nat => n < DimensionSubspaceVS K V W2 H2 H3 - M) (proj1_sig m - M) (H4 m H))
end).
Proof.
move=> K V W1 W2 H1 H2 H3 H4 M F.
suff: (forall m : Count (DimensionSubspaceVS K V W2 H2 H3), ~ proj1_sig m < M -> proj1_sig m - M < DimensionSubspaceVS K V W2 H2 H3 - M).
move=> H5.
exists H5.
apply (Proposition_5_9_2_subspace K V W1 W2 H1 H2 H3 H4 M F H5).
move=> m H5.
apply (Plus.plus_lt_reg_l (proj1_sig m - M) (DimensionSubspaceVS K V W2 H2 H3 - M) M).
suff: (M <= proj1_sig m).
move=> H6.
rewrite (Minus.le_plus_minus_r M (proj1_sig m) H6).
rewrite (Minus.le_plus_minus_r M (DimensionSubspaceVS K V W2 H2 H3)).
apply (proj2_sig m).
apply (le_trans M (proj1_sig m) (DimensionSubspaceVS K V W2 H2 H3) H6 (lt_le_weak (proj1_sig m) (DimensionSubspaceVS K V W2 H2 H3) (proj2_sig m))).
elim (le_or_lt M (proj1_sig m)).
apply.
move=> H6.
apply False_ind.
apply (H5 H6).
Qed.

Lemma Proposition_5_9_3_subspace : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)), SubspaceVS K V W1 -> forall (H1 : SubspaceVS K V W2) (H2 : FiniteDimensionVS K (SubspaceMakeVS K V W2 H1)), Included (VT K V) W1 W2 -> exists (W3 : Ensemble (VT K V)), SubspaceVS K V W3 /\ W2 = SumEnsembleVS K V W1 W3 /\ Singleton (VT K V) (VO K V) = Intersection (VT K V) W1 W3.
Proof.
move=> K V W1 W2 H1 H2 H3 H4.
suff: (SubspaceVS K (SubspaceMakeVS K V W2 H2) (fun (v : (SubspaceMakeVST K V W2 H2)) => In (VT K V) W1 (proj1_sig v))).
move=> H5.
suff: (IsomorphicVS K (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H5) (SubspaceMakeVS K V W1 H1) (fun v : SubspaceMakeVST K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) H5 => exist W1 (proj1_sig (proj1_sig v)) (proj2_sig v))).
move=> H6.
elim (Proposition_5_9_3 K (SubspaceMakeVS K V W2 H2) (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v))).
move=> W3 H7.
exists (fun (v : VT K V) => exists (w : SubspaceMakeVST K V W2 H2), v = proj1_sig w /\ In (SubspaceMakeVST K V W2 H2) W3 w).
apply conj.
apply conj.
move=> v1 v2 H8 H9.
elim H8.
move=> w1 H10.
elim H9.
move=> w2 H11.
exists (SubspaceMakeVSVadd K V W2 H2 w1 w2).
apply conj.
rewrite (proj1 H10).
rewrite (proj1 H11).
reflexivity.
apply (proj1 (proj1 H7) w1 w2 (proj2 H10) (proj2 H11)).
apply conj.
move=> f v.
elim.
move=> w H8.
exists (SubspaceMakeVSVmul K V W2 H2 f w).
apply conj.
rewrite (proj1 H8).
reflexivity.
apply (proj1 (proj2 (proj1 H7)) f w (proj2 H8)).
exists (SubspaceMakeVSVO K V W2 H2).
apply conj.
reflexivity.
apply (proj2 (proj2 (proj1 H7))).
apply conj.
apply Extensionality_Ensembles.
apply conj.
move=> w H8.
suff: (In (SubspaceMakeVST K V W2 H2) (Full_set (VT K (SubspaceMakeVS K V W2 H2))) (exist W2 w H8)).
rewrite (proj1 (proj2 H7)).
suff: (w = proj1_sig (exist W2 w H8)).
move=> H9.
rewrite {2} H9.
elim.
move=> v1 v2 H10 H11.
apply SumEnsembleVS_intro.
apply H10.
exists v2.
apply conj.
reflexivity.
apply H11.
reflexivity.
apply Full_intro.
move=> v.
elim.
move=> v1 v2 H8 H9.
apply (proj1 H2 v1 v2 (H4 v1 H8)).
elim H9.
move=> w2 H10.
rewrite (proj1 H10).
apply (proj2_sig w2).
apply Extensionality_Ensembles.
apply conj.
move=> w.
elim.
apply Intersection_intro.
apply (proj2 (proj2 H1)).
exists (SubspaceMakeVSVO K V W2 H2).
apply conj.
reflexivity.
apply (proj2 (proj2 (proj1 H7))).
move=> w H8.
suff: (In (VT K V) W2 w).
move=> H9.
suff: (w = proj1_sig (exist W2 w H9)).
move=> H10.
rewrite H10.
suff: (In (VT K (SubspaceMakeVS K V W2 H2)) (Singleton (VT K (SubspaceMakeVS K V W2 H2)) (VO K (SubspaceMakeVS K V W2 H2))) (exist W2 w H9)).
elim.
apply (In_singleton (VT K V) (VO K V)).
rewrite (proj2 (proj2 H7)).
apply Intersection_intro.
suff: (In (VT K V) W1 w).
apply.
elim H8.
move=> v H11 H12.
apply H11.
suff: (exists u : SubspaceMakeVST K V W2 H2, w = proj1_sig u /\ In (SubspaceMakeVST K V W2 H2) W3 u).
elim.
move=> u H11.
suff: ((exist W2 w H9) = u).
move=> H12.
rewrite H12.
apply (proj2 H11).
apply sig_map.
apply (proj1 H11).
elim H8.
move=> v H11 H12.
apply H12.
reflexivity.
apply (H4 w).
elim H8.
move=> v H9 H10.
apply H9.
apply H5.
apply H3.
apply conj.
exists (fun (v : SubspaceMakeVST K V W1 H1) => exist (fun v : SubspaceMakeVST K V W2 H2 => In (VT K V) W1 (proj1_sig v)) (exist W2 (proj1_sig v) (H4 (proj1_sig v) (proj2_sig v))) (proj2_sig v)).
apply conj.
move=> x.
apply sig_map.
apply sig_map.
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
apply conj.
move=> v1 v2 H5 H6.
apply (proj1 H1 (proj1_sig v1) (proj1_sig v2) H5 H6).
apply conj.
move=> f v H5.
apply (proj1 (proj2 H1) f (proj1_sig v) H5).
apply (proj2 (proj2 H1)).
Qed.

Lemma LinearlyIndependentSpanIntersectionVS : forall (K : Field) (V : VectorSpace K) (T : Type) (F : T -> VT K V) (A B : Ensemble T), LinearlyIndependentVS K V T F -> Intersection (VT K V) (SpanVS K V {t : T | In T A t} (fun (x : {t : T | In T A t}) => F (proj1_sig x))) (SpanVS K V {t : T | In T B t} (fun (x : {t : T | In T B t}) => F (proj1_sig x))) = (SpanVS K V {t : T | In T (Intersection T A B) t} (fun (x : {t : T | In T (Intersection T A B) t}) => F (proj1_sig x))).
Proof.
move=> K V T F A B H1.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> v0 H2 H3.
elim H2.
move=> x1 H4.
elim H3.
move=> x2 H5.
suff: (forall (t0 : {t : T | In T A t}), ~ In T B (proj1_sig t0) -> proj1_sig x1 t0 = FO K).
move=> H6.
suff: (forall (t0 : {t : T | In T (Intersection T A B) t}), In T A (proj1_sig t0)).
move=> H7.
suff: (Finite {t : T | In T (Intersection T A B) t} (fun (t0 : {t : T | In T (Intersection T A B) t}) => proj1_sig x1 (exist A (proj1_sig t0) (H7 t0)) <> FO K)).
move=> H8.
exists (exist (fun (G : {t : T | In T (Intersection T A B) t} -> FT K) => Finite {t : T | In T (Intersection T A B) t} (fun (t0 : {t : T | In T (Intersection T A B) t}) => G t0 <> FO K)) (fun (t0 : {t : T | In T (Intersection T A B) t}) => proj1_sig x1 (exist A (proj1_sig t0) (H7 t0))) H8).
simpl.
rewrite H4.
suff: ((exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1)) = FiniteIm {t : T | In T (Intersection T A B) t} {t : T | In T A t} (fun (t0 : {t : T | In T (Intersection T A B) t}) => exist A (proj1_sig t0) (H7 t0)) (exist (Finite {t : T | In T (Intersection T A B) t}) (fun t : {t : T | In T (Intersection T A B) t} => proj1_sig x1 (exist A (proj1_sig t) (H7 t)) <> FO K) H8)).
move=> H9.
rewrite H9.
rewrite - (MySumF2BijectiveSame2 {t : T | In T (Intersection T A B) t} {t : T | In T A t} (exist (Finite {t : T | In T (Intersection T A B) t}) (fun t : {t : T | In T (Intersection T A B) t} => proj1_sig x1 (exist A (proj1_sig t) (H7 t)) <> FO K) H8) (fun (t0 : {t : T | In T (Intersection T A B) t}) => exist A (proj1_sig t0) (H7 t0))).
reflexivity.
move=> u1 u2 H10 H11 H12.
apply sig_map.
suff: (proj1_sig u1 = proj1_sig (exist A (proj1_sig u1) (H7 u1))).
move=> H13.
rewrite H13.
rewrite H12.
reflexivity.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> t H9.
suff: (In T (Intersection T A B) (proj1_sig t)).
move=> H10.
apply (Im_intro {t0 : T | In T (Intersection T A B) t0} {t0 : T | In T A t0} (fun t0 : {t0 : T | In T (Intersection T A B) t0} => proj1_sig x1 (exist A (proj1_sig t0) (H7 t0)) <> FO K) (fun t0 : {t0 : T | In T (Intersection T A B) t0} => exist A (proj1_sig t0) (H7 t0)) (exist (Intersection T A B) (proj1_sig t) H10)).
unfold In.
simpl.
suff: ((exist A (proj1_sig t) (H7 (exist (Intersection T A B) (proj1_sig t) H10))) = t).
move=> H11.
rewrite H11.
apply H9.
apply sig_map.
reflexivity.
apply sig_map.
reflexivity.
apply (Intersection_intro T A B (proj1_sig t) (proj2_sig t)).
apply NNPP.
move=> H10.
apply H9.
apply (H6 t H10).
move=> t0.
elim.
move=> x H9 y H10.
rewrite H10.
apply H9.
suff: (Finite {t : {t : T | In T A t} | proj1_sig x1 t <> FO K} (Full_set {t : {t : T | In T A t} | proj1_sig x1 t <> FO K})).
move=> H8.
suff: (forall (t : {t : {t : T | In T A t} | proj1_sig x1 t <> FO K}), Intersection T A B (proj1_sig (proj1_sig t))).
move=> H9.
apply (Finite_downward_closed {t : T | In T (Intersection T A B) t} (Im {t : {t : T | In T A t} | proj1_sig x1 t <> FO K} {t : T | In T (Intersection T A B) t} (Full_set {t : {t : T | In T A t} | proj1_sig x1 t <> FO K}) (fun (t : {t : {t : T | In T A t} | proj1_sig x1 t <> FO K}) => exist (Intersection T A B) (proj1_sig (proj1_sig t)) (H9 t)))).
apply finite_image.
apply (FiniteSigSame {t : T | In T A t}).
apply (proj2_sig x1).
move=> t H10.
apply (Im_intro {t0 : {t0 : T | In T A t0} | proj1_sig x1 t0 <> FO K} {t0 : T | In T (Intersection T A B) t0} (Full_set {t0 : {t0 : T | In T A t0} | proj1_sig x1 t0 <> FO K}) (fun t0 : {t0 : {t0 : T | In T A t0} | proj1_sig x1 t0 <> FO K} => exist (Intersection T A B) (proj1_sig (proj1_sig t0)) (H9 t0))  (exist (fun (t0 : {t0 : T | In T A t0}) => proj1_sig x1 t0 <> FO K) (exist A (proj1_sig t) (H7 t)) H10)).
apply Full_intro.
apply sig_map.
reflexivity.
move=> t.
apply Intersection_intro.
apply (proj2_sig (proj1_sig t)).
apply NNPP.
move=> H9.
apply (proj2_sig t).
apply (H6 (proj1_sig t) H9).
apply (FiniteSigSame {t : T | In T A t}).
apply (proj2_sig x1).
move=> t.
elim (proj2_sig t).
move=> x H7 H8.
apply H7.
suff: (forall (t : T), ~ In T B t -> (fun (t : T) => match excluded_middle_informative (A t) with
  | left H => proj1_sig x1 (exist A t H)
  | right _ => FO K 
end) t = FO K).
move=> H6 t H7.
suff: (proj1_sig x1 t = (fun (t : T) => match excluded_middle_informative (A t) with
  | left H => proj1_sig x1 (exist A t H)
  | right _ => FO K
end) (proj1_sig t)).
move=> H8.
rewrite H8.
apply (H6 (proj1_sig t) H7).
elim (excluded_middle_informative (A (proj1_sig t))).
move=> H8.
suff: (t = (exist A (proj1_sig t) H8)).
move=> H9.
rewrite {1} H9.
reflexivity.
apply sig_map.
reflexivity.
move=> H8.
apply False_ind.
apply (H8 (proj2_sig t)).
suff: ((fun (t : T) => match excluded_middle_informative (A t) with
  | left H => proj1_sig x1 (exist A t H)
  | right _ => FO K
end) = (fun (t : T) => match excluded_middle_informative (B t) with
  | left H => proj1_sig x2 (exist B t H)
  | right _ => FO K
end)).
move=> H6 t H7.
suff: (match excluded_middle_informative (A t) with
  | left H => proj1_sig x1 (exist A t H)
  | right _ => FO K
end = let temp := (fun t : T => match excluded_middle_informative (A t) with
  | left H => proj1_sig x1 (exist A t H)
  | right _ => FO K
end) in temp t).
move=> H8.
rewrite H8.
rewrite H6.
simpl.
elim (excluded_middle_informative (B t)).
move=> H9.
apply False_ind.
apply (H7 H9).
move=> H9.
reflexivity.
reflexivity.
suff: (forall (t : T), In T (proj1_sig (FiniteUnion T (FiniteIm {t : T | In T A t} T (fun (t : {t : T | In T A t}) => proj1_sig t) (exist (Finite {t : T | In T A t}) (fun (t : {t : T | In T A t}) => proj1_sig x1 t <> FO K) (proj2_sig x1))) (FiniteIm {t : T | In T B t} T (fun (t : {t : T | In T B t}) => proj1_sig t) (exist (Finite {t : T | In T B t}) (fun (t : {t : T | In T B t}) => proj1_sig x2 t <> FO K) (proj2_sig x2))))) t -> (Fadd K ((fun t : T => match excluded_middle_informative (A t) with
  | left H => proj1_sig x1 (exist A t H)
  | right _ => FO K
end) t) (Fopp K ((fun t : T => match excluded_middle_informative (B t) with
  | left H => proj1_sig x2 (exist B t H)
  | right _ => FO K
end) t)) = FO K)).
move=> H6.
apply functional_extensionality.
move=> t.
elim (classic (In T (proj1_sig (FiniteUnion T (FiniteIm {t0 : T | In T A t0} T (fun t0 : {t0 : T | In T A t0} => proj1_sig t0) (exist (Finite {t0 : T | In T A t0}) (fun t0 : {t0 : T | In T A t0} => proj1_sig x1 t0 <> FO K) (proj2_sig x1))) (FiniteIm {t0 : T | In T B t0} T (fun t0 : {t0 : T | In T B t0} => proj1_sig t0) (exist (Finite {t0 : T | In T B t0}) (fun t0 : {t0 : T | In T B t0} => proj1_sig x2 t0 <> FO K) (proj2_sig x2))))) t)).
move=> H7.
apply (Fminus_diag_uniq K).
apply (H6 t H7).
move=> H7.
elim (excluded_middle_informative (A t)).
move=> H8.
suff: (proj1_sig x1 (exist A t H8) = FO K).
move=> H9.
rewrite H9.
elim (excluded_middle_informative (B t)).
move=> H10.
apply NNPP.
move=> H11.
apply H7.
right.
apply (Im_intro {t0 : T | In T B t0} T (fun t0 : {t0 : T | In T B t0} => proj1_sig x2 t0 <> FO K) (fun t0 : {t0 : T | In T B t0} => proj1_sig t0) (exist B t H10)).
move=> H12.
apply H11.
rewrite H12.
reflexivity.
reflexivity.
move=> H10.
reflexivity.
apply NNPP.
move=> H9.
apply H7.
left.
apply (Im_intro {t0 : T | In T A t0} T (fun t0 : {t0 : T | In T A t0} => proj1_sig x1 t0 <> FO K) (fun t0 : {t0 : T | In T A t0} => proj1_sig t0) (exist A t H8)).
apply H9.
reflexivity.
move=> H8.
elim (excluded_middle_informative (B t)).
move=> H9.
apply NNPP.
move=> H10.
apply H7.
right.
apply (Im_intro {t0 : T | In T B t0} T (fun t0 : {t0 : T | In T B t0} => proj1_sig x2 t0 <> FO K) (fun t0 : {t0 : T | In T B t0} => proj1_sig t0) (exist B t H9)).
move=> H11.
apply H10.
rewrite H11.
reflexivity.
reflexivity.
move=> H9.
reflexivity.
apply (proj1 (LinearlyIndependentVSDef3 K V T F) H1).
suff: (MySumF2 T (FiniteUnion T (FiniteIm {t : T | In T A t} T (fun t : {t : T | In T A t} => proj1_sig t) (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1))) (FiniteIm {t : T | In T B t} T (fun t : {t : T | In T B t} => proj1_sig t) (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} => proj1_sig x2 t <> FO K) (proj2_sig x2)))) (VSPCM K V) (fun t : T => Vmul K V (Fadd K match excluded_middle_informative (A t) with
  | left H => proj1_sig x1 (exist A t H)
  | right _ => FO K
end (Fopp K match excluded_middle_informative (B t) with
  | left H => proj1_sig x2 (exist B t H)
  | right _ => FO K
end)) (F t)) = Vadd K V (MySumF2 T (FiniteUnion T (FiniteIm {t : T | In T A t} T (fun t : {t : T | In T A t} => proj1_sig t) (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1))) (FiniteIm {t : T | In T B t} T (fun t : {t : T | In T B t} => proj1_sig t) (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} => proj1_sig x2 t <> FO K) (proj2_sig x2)))) (VSPCM K V) (fun t : T => Vmul K V (match excluded_middle_informative (A t) with
  | left H => proj1_sig x1 (exist A t H)
  | right _ => FO K
end) (F t))) (Vopp K V (MySumF2 T (FiniteUnion T (FiniteIm {t : T | In T A t} T (fun t : {t : T | In T A t} => proj1_sig t) (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1))) (FiniteIm {t : T | In T B t} T (fun t : {t : T | In T B t} => proj1_sig t) (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} => proj1_sig x2 t <> FO K) (proj2_sig x2)))) (VSPCM K V) (fun t : T => Vmul K V (match excluded_middle_informative (B t) with
  | left H => proj1_sig x2 (exist B t H)
  | right _ => FO K
end) (F t))))).
move=> H6.
rewrite H6.
apply (Vminus_diag_eq K V).
suff: (MySumF2 T (FiniteUnion T (FiniteIm {t : T | In T A t} T (fun t : {t : T | In T A t} => proj1_sig t) (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1))) (FiniteIm {t : T | In T B t} T (fun t : {t : T | In T B t} => proj1_sig t) (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} => proj1_sig x2 t <> FO K) (proj2_sig x2)))) (VSPCM K V) (fun t : T => Vmul K V match excluded_middle_informative (A t) with
  | left H => proj1_sig x1 (exist A t H)
  | right _ => FO K
end (F t)) = v0).
move=> H7.
suff: (MySumF2 T (FiniteUnion T (FiniteIm {t : T | In T A t} T (fun t : {t : T | In T A t} => proj1_sig t) (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1))) (FiniteIm {t : T | In T B t} T (fun t : {t : T | In T B t} => proj1_sig t) (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} => proj1_sig x2 t <> FO K) (proj2_sig x2)))) (VSPCM K V) (fun t : T => Vmul K V match excluded_middle_informative (B t) with
  | left H => proj1_sig x2 (exist B t H)
  | right _ => FO K
end (F t)) = v0).
move=> H8.
rewrite H7.
rewrite H8.
reflexivity.
rewrite H5.
rewrite (MySumF2Included T (FiniteIm {t : T | In T B t} T (fun t : {t : T | In T B t} => proj1_sig t) (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} => proj1_sig x2 t <> FO K) (proj2_sig x2))) (FiniteUnion T (FiniteIm {t : T | In T A t} T (fun t : {t : T | In T A t} => proj1_sig t) (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1))) (FiniteIm {t : T | In T B t} T (fun t : {t : T | In T B t} => proj1_sig t) (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} => proj1_sig x2 t <> FO K) (proj2_sig x2))))).
rewrite (MySumF2O T (FiniteIntersection T (FiniteUnion T (FiniteIm {t : T | In T A t} T (fun t : {t : T | In T A t} => proj1_sig t) (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1))) (FiniteIm {t : T | In T B t} T (fun t : {t : T | In T B t} => proj1_sig t) (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} => proj1_sig x2 t <> FO K) (proj2_sig x2)))) (Complement T (proj1_sig (FiniteIm {t : T | In T B t} T (fun t : {t : T | In T B t} => proj1_sig t) (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} => proj1_sig x2 t <> FO K) (proj2_sig x2))))))).
rewrite (CM_O_r (VSPCM K V)).
rewrite - (MySumF2BijectiveSame2 {t : T | In T B t} T (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} => proj1_sig x2 t <> FO K) (proj2_sig x2)) (fun t : {t : T | In T B t} => proj1_sig t)).
suff: ((compose (fun t : T => Vmul K V match excluded_middle_informative (B t) with
  | left H => proj1_sig x2 (exist B t H)
  | right _ => FO K
end (F t)) (fun t : {t : T | In T B t} => proj1_sig t)) = (fun t : {t : T | In T B t} => Vmul K V (proj1_sig x2 t) (F (proj1_sig t)))).
move=> H8.
rewrite H8.
reflexivity.
apply functional_extensionality.
move=> t.
unfold compose.
elim (excluded_middle_informative (B (proj1_sig t))).
move=> H8.
suff: ((exist B (proj1_sig t) H8) = t).
move=> H9.
rewrite H9.
reflexivity.
apply sig_map.
reflexivity.
move=> H8.
apply False_ind.
apply (H8 (proj2_sig t)).
move=> u1 u2 H8 H9.
apply sig_map.
move=> u H8.
elim (excluded_middle_informative (B u)).
move=> H9.
suff: ((proj1_sig x2 (exist B u H9)) = FO K).
move=> H10.
rewrite H10.
apply (Vmul_O_l K V).
suff: ((Complement T (proj1_sig (FiniteIm {t : T | In T B t} T (fun t : {t : T | In T B t} => proj1_sig t) (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} =>  proj1_sig x2 t <> FO K) (proj2_sig x2))))) u).
move=> H10.
apply NNPP.
move=> H11.
apply H10.
apply (Im_intro {t : T | In T B t} T (fun t : {t : T | In T B t} => proj1_sig x2 t <> FO K) (fun t : {t : T | In T B t} => proj1_sig t) (exist B u H9)).
apply H11.
reflexivity.
elim H8.
move=> t H10 H11.
apply H10.
move=> H9.
apply (Vmul_O_l K V).
move=> t H8.
right.
apply H8.
rewrite H4.
rewrite (MySumF2Included T (FiniteIm {t : T | In T A t} T (fun t : {t : T | In T A t} => proj1_sig t) (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1))) (FiniteUnion T (FiniteIm {t : T | In T A t} T (fun t : {t : T | In T A t} => proj1_sig t) (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1))) (FiniteIm {t : T | In T B t} T (fun t : {t : T | In T B t} => proj1_sig t) (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} => proj1_sig x2 t <> FO K) (proj2_sig x2))))).
rewrite (MySumF2O T (FiniteIntersection T (FiniteUnion T (FiniteIm {t : T | In T A t} T (fun t : {t : T | In T A t} => proj1_sig t) (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1))) (FiniteIm {t : T | In T B t} T (fun t : {t : T | In T B t} => proj1_sig t) (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} => proj1_sig x2 t <> FO K) (proj2_sig x2)))) (Complement T (proj1_sig (FiniteIm {t : T | In T A t} T (fun t : {t : T | In T A t} => proj1_sig t) (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1))))))).
rewrite (CM_O_r (VSPCM K V)).
rewrite - (MySumF2BijectiveSame2 {t : T | In T A t} T (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1)) (fun t : {t : T | In T A t} => proj1_sig t)).
suff: ((compose (fun t : T => Vmul K V match excluded_middle_informative (A t) with
  | left H => proj1_sig x1 (exist A t H)
  | right _ => FO K
end (F t)) (fun t : {t : T | In T A t} => proj1_sig t)) = (fun t : {t : T | In T A t} => Vmul K V (proj1_sig x1 t) (F (proj1_sig t)))).
move=> H7.
rewrite H7.
reflexivity.
apply functional_extensionality.
move=> t.
unfold compose.
elim (excluded_middle_informative (A (proj1_sig t))).
move=> H7.
suff: ((exist A (proj1_sig t) H7) = t).
move=> H8.
rewrite H8.
reflexivity.
apply sig_map.
reflexivity.
move=> H7.
apply False_ind.
apply (H7 (proj2_sig t)).
move=> u1 u2 H7 H8.
apply sig_map.
move=> u H7.
elim (excluded_middle_informative (A u)).
move=> H8.
suff: ((proj1_sig x1 (exist A u H8)) = FO K).
move=> H9.
rewrite H9.
apply (Vmul_O_l K V).
suff: ((Complement T (proj1_sig (FiniteIm {t : T | In T A t} T (fun t : {t : T | In T A t} => proj1_sig t) (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1))))) u).
move=> H9.
apply NNPP.
move=> H10.
apply H9.
apply (Im_intro {t : T | In T A t} T (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (fun t : {t : T | In T A t} => proj1_sig t) (exist A u H8)).
apply H10.
reflexivity.
elim H7.
move=> t H9 H10.
apply H9.
move=> H8.
apply (Vmul_O_l K V).
move=> t H7.
left.
apply H7.
apply (FiniteSetInduction T (FiniteUnion T (FiniteIm {t : T | In T A t} T (fun t : {t : T | In T A t} => proj1_sig t) (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => proj1_sig x1 t <> FO K) (proj2_sig x1))) (FiniteIm {t : T | In T B t} T (fun t : {t : T | In T B t} => proj1_sig t) (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} => proj1_sig x2 t <> FO K) (proj2_sig x2))))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite (Vadd_opp_r K V).
reflexivity.
move=> C c H6 H7 H8 H9.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H9.
simpl.
rewrite (Vopp_add_distr K V).
rewrite - (Vadd_assoc K V (Vadd K V (MySumF2 T C (VSPCM K V) (fun t : T => Vmul K V match excluded_middle_informative (A t) with
  | left H => proj1_sig x1 (exist A t H)
  | right _ => FO K
end (F t))) (Vmul K V match excluded_middle_informative (A c) with
  | left H => proj1_sig x1 (exist A c H)
  | right _ => FO K
end (F c))) (Vopp K V (MySumF2 T C (VSPCM K V) (fun t : T => Vmul K V match excluded_middle_informative (B t) with
  | left H => proj1_sig x2 (exist B t H)
  | right _ => FO K
end (F t))))).
rewrite (Vadd_assoc K V (MySumF2 T C (VSPCM K V) (fun t : T => Vmul K V match excluded_middle_informative (A t) with
  | left H => proj1_sig x1 (exist A t H)
  | right _ => FO K
end (F t))) (Vmul K V match excluded_middle_informative (A c) with
  | left H => proj1_sig x1 (exist A c H)
  | right _ => FO K
end (F c))).
rewrite (Vadd_comm K V (Vmul K V match excluded_middle_informative (A c) with
  | left H => proj1_sig x1 (exist A c H)
  | right _ => FO K
end (F c)) (Vopp K V (MySumF2 T C (VSPCM K V) (fun t : T => Vmul K V match excluded_middle_informative (B t) with
  | left H => proj1_sig x2 (exist B t H)
  | right _ => FO K
end (F t))))).
rewrite - (Vadd_assoc K V (MySumF2 T C (VSPCM K V) (fun t : T => Vmul K V match excluded_middle_informative (A t) with
  | left H => proj1_sig x1 (exist A t H)
  | right _ => FO K
end (F t))) (Vopp K V (MySumF2 T C (VSPCM K V) (fun t : T => Vmul K V match excluded_middle_informative (B t) with
  | left H => proj1_sig x2 (exist B t H)
  | right _ => FO K
end (F t))))).
rewrite (Vadd_assoc K V (Vadd K V (MySumF2 T C (VSPCM K V) (fun t : T => Vmul K V match excluded_middle_informative (A t) with
  | left H => proj1_sig x1 (exist A t H)
  | right _ => FO K
end (F t))) (Vopp K V (MySumF2 T C (VSPCM K V) (fun t : T => Vmul K V match excluded_middle_informative (B t) with
  | left H => proj1_sig x2 (exist B t H)
  | right _ => FO K
end (F t))))) (Vmul K V match excluded_middle_informative (A c) with
  | left H => proj1_sig x1 (exist A c H)
  | right _ => FO K
end (F c))).
rewrite (Vmul_add_distr_r K V).
rewrite (Vopp_mul_distr_l K V).
reflexivity.
apply H8.
apply H8.
apply H8.
move=> v.
elim.
move=> x H2.
rewrite H2.
apply Intersection_intro.
suff: (forall (t : {t : T | In T (Intersection T A B) t}), In T A (proj1_sig t)).
move=> H3.
suff: ((fun t : {t : T | In T (Intersection T A B) t} => Vmul K V (proj1_sig x t) (F (proj1_sig t))) = compose (fun t : {t : T | In T A t} => Vmul K V match excluded_middle_informative (Intersection T A B (proj1_sig t)) with
  | left H => proj1_sig x (exist (Intersection T A B) (proj1_sig t) H) 
  | right _ => FO K
end (F (proj1_sig t))) (fun (t : {t : T | In T (Intersection T A B) t}) => exist A (proj1_sig t) (H3 t))).
move=> H4.
rewrite H4.
rewrite (MySumF2BijectiveSame2 {t : T | In T (Intersection T A B) t} {t : T | In T A t} (exist (Finite {t : T | In T (Intersection T A B) t}) (fun t : {t : T | In T (Intersection T A B) t} => proj1_sig x t <> FO K) (proj2_sig x)) (fun (t : {t : T | In T (Intersection T A B) t}) => exist A (proj1_sig t) (H3 t)) (VSPCM K V)).
suff: (Finite {t : T | In T A t} (fun t : {t : T | In T A t} => match excluded_middle_informative (Intersection T A B (proj1_sig t)) with
  | left H => proj1_sig x (exist (Intersection T A B) (proj1_sig t) H)
  | right _ => FO K
end <> FO K)).
move=> H5.
exists (exist (fun (G : {t : T | In T A t} -> FT K) => Finite {t : T | In T A t} (fun (t : {t : T | In T A t}) => G t <> FO K)) (fun t : {t : T | In T A t} => match excluded_middle_informative (Intersection T A B (proj1_sig t)) with
  | left H => proj1_sig x (exist (Intersection T A B) (proj1_sig t) H)
  | right _ => FO K
end) H5).
simpl.
suff: ((FiniteIm {t : T | In T (Intersection T A B) t}  {t : T | In T A t} (fun t : {t : T | In T (Intersection T A B) t} => exist A (proj1_sig t) (H3 t)) (exist (Finite {t : T | In T (Intersection T A B) t}) (fun t : {t : T | In T (Intersection T A B) t} => proj1_sig x t <> FO K) (proj2_sig x))) = (exist (Finite {t : T | In T A t}) (fun t : {t : T | In T A t} => match excluded_middle_informative (Intersection T A B (proj1_sig t)) with
  | left H => proj1_sig x (exist (Intersection T A B) (proj1_sig t) H)
  | right _ => FO K
end <> FO K) H5)).
move=> H6.
rewrite H6.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> x0 H6 y0 H7.
rewrite H7.
unfold In.
simpl.
elim (excluded_middle_informative (Intersection T A B (@proj1_sig T (fun t0 : T => Intersection T A B t0) x0))).
move=> H8.
suff: ((exist (Intersection T A B) (proj1_sig x0) H8) = x0).
move=> H9.
rewrite H9.
apply H6.
apply sig_map.
reflexivity.
move=> H8 H9.
apply (H8 (proj2_sig x0)).
simpl.
move=> t.
unfold In.
elim (excluded_middle_informative (Intersection T A B (@proj1_sig T (fun t0 : T => A t0) t))).
move=> H6 H7.
apply (Im_intro {t0 : T | Intersection T A B t0} {t0 : T | A t0} (fun t0 : {t0 : T | Intersection T A B t0} => proj1_sig x t0 <> FO K) (fun t0 : {t0 : T | Intersection T A B t0} => exist A (proj1_sig t0) (H3 t0)) (exist (Intersection T A B) (proj1_sig t) H6)).
apply H7.
apply sig_map.
reflexivity.
move=> H6 H7.
apply False_ind.
apply H7.
reflexivity.
suff: (Im {t : T | In T (Intersection T A B) t} {t : T | In T A t} (fun t : {t : T | In T (Intersection T A B) t} => proj1_sig x t <> FO K) (fun t : {t : T | In T (Intersection T A B) t} => exist A (proj1_sig t) (H3 t)) = (fun t : {t : T | In T A t} => match excluded_middle_informative (Intersection T A B (proj1_sig t)) with
  | left H => proj1_sig x (exist (Intersection T A B) (proj1_sig t) H)
  | right _ => FO K
end <> FO K)).
move=> H5.
rewrite - H5.
apply finite_image.
apply (proj2_sig x).
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> x0 H5 y0 H6.
rewrite H6.
unfold In.
simpl.
elim (excluded_middle_informative (Intersection T A B (@proj1_sig T (fun t0 : T => Intersection T A B t0) x0))).
move=> H7.
suff: ((exist (Intersection T A B) (proj1_sig x0) H7) = x0).
move=> H8.
rewrite H8.
apply H5.
apply sig_map.
reflexivity.
move=> H7 H8.
apply (H7 (proj2_sig x0)).
simpl.
move=> t.
unfold In.
elim (excluded_middle_informative (Intersection T A B (@proj1_sig T (fun t0 : T => A t0) t))).
move=> H5 H6.
apply (Im_intro {t0 : T | Intersection T A B t0} {t0 : T | A t0} (fun t0 : {t0 : T | Intersection T A B t0} => proj1_sig x t0 <> FO K) (fun t0 : {t0 : T | Intersection T A B t0} => exist A (proj1_sig t0) (H3 t0)) (exist (Intersection T A B) (proj1_sig t) H5)).
apply H6.
apply sig_map.
reflexivity.
move=> H5 H6.
apply False_ind.
apply H6.
reflexivity.
move=> u1 u2 H5 H6 H7.
apply sig_map.
suff: (proj1_sig u1 = proj1_sig (exist A (proj1_sig u1) (H3 u1))).
move=> H8.
rewrite H8.
rewrite H7.
reflexivity.
reflexivity.
apply functional_extensionality.
move=> t.
unfold compose.
elim (excluded_middle_informative (Intersection T A B (@proj1_sig T (fun t0 : T => In T A t0) (@exist T A (@proj1_sig T (fun t0 : T => In T (Intersection T A B) t0) t) (H3 t))))).
move=> H4.
simpl.
suff: ((exist (Intersection T A B) (proj1_sig t) H4) = t).
move=> H5.
rewrite H5.
reflexivity.
apply sig_map.
reflexivity.
move=> H4.
apply False_ind.
apply (H4 (proj2_sig t)).
move=> t.
elim (proj2_sig t).
move=> t0 H3 H4.
apply H3.
suff: (forall (t : {t : T | In T (Intersection T A B) t}), In T B (proj1_sig t)).
move=> H3.
suff: ((fun t : {t : T | In T (Intersection T A B) t} => Vmul K V (proj1_sig x t) (F (proj1_sig t))) = compose (fun t : {t : T | In T B t} => Vmul K V match excluded_middle_informative (Intersection T A B (proj1_sig t)) with
  | left H => proj1_sig x (exist (Intersection T A B) (proj1_sig t) H) 
  | right _ => FO K
end (F (proj1_sig t))) (fun (t : {t : T | In T (Intersection T A B) t}) => exist B (proj1_sig t) (H3 t))).
move=> H4.
rewrite H4.
rewrite (MySumF2BijectiveSame2 {t : T | In T (Intersection T A B) t} {t : T | In T B t} (exist (Finite {t : T | In T (Intersection T A B) t}) (fun t : {t : T | In T (Intersection T A B) t} => proj1_sig x t <> FO K) (proj2_sig x)) (fun (t : {t : T | In T (Intersection T A B) t}) => exist B (proj1_sig t) (H3 t)) (VSPCM K V)).
suff: (Finite {t : T | In T B t} (fun t : {t : T | In T B t} => match excluded_middle_informative (Intersection T A B (proj1_sig t)) with
  | left H => proj1_sig x (exist (Intersection T A B) (proj1_sig t) H)
  | right _ => FO K
end <> FO K)).
move=> H5.
exists (exist (fun (G : {t : T | In T B t} -> FT K) => Finite {t : T | In T B t} (fun (t : {t : T | In T B t}) => G t <> FO K)) (fun t : {t : T | In T B t} => match excluded_middle_informative (Intersection T A B (proj1_sig t)) with
  | left H => proj1_sig x (exist (Intersection T A B) (proj1_sig t) H)
  | right _ => FO K
end) H5).
simpl.
suff: ((FiniteIm {t : T | In T (Intersection T A B) t} {t : T | In T B t} (fun t : {t : T | In T (Intersection T A B) t} => exist B (proj1_sig t) (H3 t)) (exist (Finite {t : T | In T (Intersection T A B) t}) (fun t : {t : T | In T (Intersection T A B) t} => proj1_sig x t <> FO K) (proj2_sig x))) = (exist (Finite {t : T | In T B t}) (fun t : {t : T | In T B t} => match excluded_middle_informative (Intersection T A B (proj1_sig t)) with
  | left H => proj1_sig x (exist (Intersection T A B) (proj1_sig t) H)
  | right _ => FO K
end <> FO K) H5)).
move=> H6.
rewrite H6.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> x0 H6 y0 H7.
rewrite H7.
unfold In.
simpl.
elim (excluded_middle_informative (Intersection T A B (@proj1_sig T (fun t0 : T => Intersection T A B t0) x0))).
move=> H8.
suff: ((exist (Intersection T A B) (proj1_sig x0) H8) = x0).
move=> H9.
rewrite H9.
apply H6.
apply sig_map.
reflexivity.
move=> H8 H9.
apply (H8 (proj2_sig x0)).
simpl.
move=> t.
unfold In.
elim (excluded_middle_informative (Intersection T A B (@proj1_sig T (fun t0 : T => B t0) t))).
move=> H6 H7.
apply (Im_intro {t0 : T | Intersection T A B t0} {t0 : T | B t0} (fun t0 : {t0 : T | Intersection T A B t0} => proj1_sig x t0 <> FO K) (fun t0 : {t0 : T | Intersection T A B t0} => exist B (proj1_sig t0) (H3 t0)) (exist (Intersection T A B) (proj1_sig t) H6)).
apply H7.
apply sig_map.
reflexivity.
move=> H6 H7.
apply False_ind.
apply H7.
reflexivity.
suff: (Im {t : T | In T (Intersection T A B) t} {t : T | In T B t} (fun t : {t : T | In T (Intersection T A B) t} => proj1_sig x t <> FO K) (fun t : {t : T | In T (Intersection T A B) t} => exist B (proj1_sig t) (H3 t)) = (fun t : {t : T | In T B t} => match excluded_middle_informative (Intersection T A B (proj1_sig t)) with
  | left H => proj1_sig x (exist (Intersection T A B) (proj1_sig t) H)
  | right _ => FO K
end <> FO K)).
move=> H5.
rewrite - H5.
apply finite_image.
apply (proj2_sig x).
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim.
move=> x0 H5 y0 H6.
rewrite H6.
unfold In.
simpl.
elim (excluded_middle_informative (Intersection T A B (@proj1_sig T (fun t0 : T => Intersection T A B t0) x0))).
move=> H7.
suff: ((exist (Intersection T A B) (proj1_sig x0) H7) = x0).
move=> H8.
rewrite H8.
apply H5.
apply sig_map.
reflexivity.
move=> H7 H8.
apply (H7 (proj2_sig x0)).
simpl.
move=> t.
unfold In.
elim (excluded_middle_informative (Intersection T A B (@proj1_sig T (fun t0 : T => B t0) t))).
move=> H5 H6.
apply (Im_intro {t0 : T | Intersection T A B t0} {t0 : T | B t0} (fun t0 : {t0 : T | Intersection T A B t0} => proj1_sig x t0 <> FO K) (fun t0 : {t0 : T | Intersection T A B t0} => exist B (proj1_sig t0) (H3 t0)) (exist (Intersection T A B) (proj1_sig t) H5)).
apply H6.
apply sig_map.
reflexivity.
move=> H5 H6.
apply False_ind.
apply H6.
reflexivity.
move=> u1 u2 H5 H6 H7.
apply sig_map.
suff: (proj1_sig u1 = proj1_sig (exist B (proj1_sig u1) (H3 u1))).
move=> H8.
rewrite H8.
rewrite H7.
reflexivity.
reflexivity.
apply functional_extensionality.
move=> t.
unfold compose.
elim (excluded_middle_informative (Intersection T A B (@proj1_sig T (fun t0 : T => In T B t0) (@exist T B (@proj1_sig T (fun t0 : T => In T (Intersection T A B) t0) t) (H3 t))))).
move=> H4.
simpl.
suff: ((exist (Intersection T A B) (proj1_sig t) H4) = t).
move=> H5.
rewrite H5.
reflexivity.
apply sig_map.
reflexivity.
move=> H4.
apply False_ind.
apply (H4 (proj2_sig t)).
move=> t.
elim (proj2_sig t).
move=> t0 H3 H4.
apply H4.
Qed.

Lemma LinearlyIndependentSpanIntersectionVS2 : forall (K : Field) (V : VectorSpace K) (T : Type) (F : T -> VT K V) (A B : Ensemble T), LinearlyIndependentVS K V T F -> Intersection T A B = Empty_set T -> Intersection (VT K V) (SpanVS K V {t : T | In T A t} (fun (x : {t : T | In T A t}) => F (proj1_sig x))) (SpanVS K V {t : T | In T B t} (fun (x : {t : T | In T B t}) => F (proj1_sig x))) = Singleton (VT K V) (VO K V).
Proof.
move=> K V T F A B H1 H2.
rewrite (LinearlyIndependentSpanIntersectionVS K V T F A B H1).
rewrite H2.
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> x H3.
rewrite H3.
rewrite MySumF2O.
apply (In_singleton (VT K V) (VO K V)).
move=> u.
elim (proj2_sig u).
move=> v.
elim.
apply SpanSubspaceVS.
Qed.

Lemma DimensionSumEnsembleVS : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2) (H3 : SubspaceVS K V (Intersection (VT K V) W1 W2)) (H4 : SubspaceVS K V (SumEnsembleVS K V W1 W2)) (H5 : FiniteDimensionVS K (SubspaceMakeVS K V (SumEnsembleVS K V W1 W2) H4)) (H6 : FiniteDimensionVS K (SubspaceMakeVS K V (Intersection (VT K V) W1 W2) H3)) (H7 : FiniteDimensionVS K (SubspaceMakeVS K V W1 H1)) (H8 : FiniteDimensionVS K (SubspaceMakeVS K V W2 H2)), DimensionSubspaceVS K V (SumEnsembleVS K V W1 W2) H4 H5 + DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 = DimensionSubspaceVS K V W1 H1 H7 + DimensionSubspaceVS K V W2 H2 H8.
Proof.
move=> K V W1 W2 H1 H2 H3 H4 H5 H6 H7 H8.
elim (Proposition_5_9_3 K (SubspaceMakeVS K V W1 H1) (fun (t : (SubspaceMakeVST K V W1 H1)) => In (VT K V) (Intersection (VT K V) W1 W2) (proj1_sig t))).
move=> W3 H9.
elim (Proposition_5_9_3 K (SubspaceMakeVS K V W2 H2) (fun (t : (SubspaceMakeVST K V W2 H2)) => In (VT K V) (Intersection (VT K V) W1 W2) (proj1_sig t))).
move=> W4 H10.
elim (DimensionSubspaceVSNature K V (Intersection (VT K V) W1 W2) H3 H6).
move=> F1 H11.
elim (Proposition_5_9_1_1 K (SubspaceMakeVS K V W1 H1) H7 W3 (proj1 H9)).
move=> N2.
elim.
move=> F2 H12.
elim (Proposition_5_9_1_1 K (SubspaceMakeVS K V W2 H2) H8 W4 (proj1 H10)).
move=> N3.
elim.
move=> F3 H13.
suff: (BasisSubspaceVS K V W1 H1 (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + (Count N2)) (fun t : (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + (Count N2)) => match t with
  | inl t0 => F1 t0
  | inr t0 => proj1_sig (proj1_sig (F2 t0))
end)).
move=> H14.
suff: (BasisSubspaceVS K V W2 H2 (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + (Count N3)) (fun t : (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + (Count N3)) => match t with
  | inl t0 => F1 t0
  | inr t0 => proj1_sig (proj1_sig (F3 t0))
end)).
move=> H15.
suff: (BasisSubspaceVS K V (SumEnsembleVS K V W1 W2) H4 (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + (Count N2) + (Count N3)) (fun t : (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + (Count N2) + (Count N3)) => match t with
  | inl (inl t1) => F1 t1
  | inl (inr t1) => proj1_sig (proj1_sig (F2 t1))
  | inr t0 => proj1_sig (proj1_sig (F3 t0))
end)).
move=> H16.
suff: (forall (N M : nat), {f : Count (N + M) -> Count N + Count M | Bijective (Count (N + M)) (Count N + Count M) f}).
move=> H17.
suff: (DimensionSubspaceVS K V (SumEnsembleVS K V W1 W2) H4 H5 = DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2 + N3).
move=> H18.
rewrite H18.
suff: (DimensionSubspaceVS K V W1 H1 H7 = DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2).
move=> H19.
rewrite H19.
suff: (DimensionSubspaceVS K V W2 H2 H8 = DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N3).
move=> H20.
rewrite H20.
rewrite - (Plus.plus_assoc (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2)).
rewrite (Plus.plus_comm N3).
reflexivity.
apply (DimensionSubspaceVSNature2 K V W2 H2 H8 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N3) (compose (fun t : Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + Count N3 => match t with
  | inl t0 => F1 t0
  | inr t0 => proj1_sig (proj1_sig (F3 t0))
end) (proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N3)))).
elim H15.
move=> H20 H21.
exists (fun (t : Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N3)) => H20 (proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N3) t)).
apply (BijectiveSaveBasisVS K (SubspaceMakeVS K V W2 H2) (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N3)) (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + Count N3) (proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N3)) (fun t : Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + Count N3 => exist W2 match t with
  | inl t0 => F1 t0
  | inr t0 => proj1_sig (proj1_sig (F3 t0))
end (H20 t)) (proj2_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N3)) H21).
apply (DimensionSubspaceVSNature2 K V W1 H1 H7 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2) (compose (fun t : Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + Count N2 => match t with
  | inl t0 => F1 t0
  | inr t0 => proj1_sig (proj1_sig (F2 t0))
end) (proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N2)))).
elim H14.
move=> H19 H20.
exists (fun (t : Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2)) => H19 (proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N2) t)).
apply (BijectiveSaveBasisVS K (SubspaceMakeVS K V W1 H1) (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2)) (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + Count N2) (proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N2)) (fun t : Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + Count N2 => exist W1 match t with
  | inl t0 => F1 t0
  | inr t0 => proj1_sig (proj1_sig (F2 t0))
end (H19 t)) (proj2_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N2)) H20).
suff: {f : Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2 + N3) -> Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + Count N2 + Count N3 | Bijective (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2 + N3)) (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + Count N2 + Count N3) f}.
move=> H18.
elim H16.
move=> H19 H20.
apply (DimensionSubspaceVSNature2 K V (SumEnsembleVS K V W1 W2) H4 H5 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2 + N3) (compose (fun t : Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + Count N2 + Count N3 => match t with
  | inl (inl t1) => F1 t1
  | inl (inr t1) => proj1_sig (proj1_sig (F2 t1))
  | inr t0 => proj1_sig (proj1_sig (F3 t0))
end) (proj1_sig H18))).
exists (fun (t : Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2 + N3)) => H19 (proj1_sig H18 t)).
apply (BijectiveSaveBasisVS K (SubspaceMakeVS K V (SumEnsembleVS K V W1 W2) H4) (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2 + N3)) (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + Count N2 + Count N3) (proj1_sig H18) (fun t : Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + Count N2 + Count N3 => exist (SumEnsembleVS K V W1 W2) match t with
  | inl (inl t1) => F1 t1
  | inl (inr t1) => proj1_sig (proj1_sig (F2 t1))
  | inr t0 => proj1_sig (proj1_sig (F3 t0))
end (H19 t)) (proj2_sig H18) H20).
exists (fun (t : Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2 + N3)) => match proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2) N3) t with 
  | inl t => inl (proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N2) t)
  | inr t => inr t
end).
elim (proj2_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2) N3)).
move=> ginv1 H18.
elim (proj2_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N2)).
move=> ginv2 H19.
exists (fun (t : (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + Count N2 + Count N3)) => match t with
  | inl (inl t0) => ginv1 (inl (ginv2 (inl t0)))
  | inl (inr t0) => ginv1 (inl (ginv2 (inr t0)))
  | inr t0 => ginv1 (inr t0)
end).
apply conj.
move=> x.
apply (BijInj (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2 + N3)) (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2) + Count N3) (proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2) N3)) (proj2_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2) N3))).
elim (proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2) N3) x).
move=> x2.
apply (BijInj (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2) + Count N3) (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2 + N3)) ginv1).
exists (proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2) N3)).
apply conj.
apply (proj2 H18).
apply (proj1 H18).
rewrite (proj1 H18).
suff: (match proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N2) x2 with
  | inl t0 => ginv2 (inl t0)
  | inr t0 => ginv2 (inr t0)
end = x2).
move=> H20.
rewrite - {2} H20.
elim (proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N2) x2).
move=> x3.
reflexivity.
move=> x3.
reflexivity.
apply (BijInj (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 + N2)) (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) + Count N2) (proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N2)) (proj2_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N2))).
elim (proj1_sig (H17 (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6) N2) x2).
move=> x3.
apply (proj2 H19).
move=> x3.
apply (proj2 H19).
move=> x3.
apply (proj2 H18).
move=> y.
elim y.
move=> y1.
elim y1.
move=> y2.
rewrite (proj2 H18).
rewrite (proj2 H19).
reflexivity.
move=> y2.
rewrite (proj2 H18).
rewrite (proj2 H19).
reflexivity.
move=> y2.
rewrite (proj2 H18).
reflexivity.
move=> N M.
suff: (forall (m : Count (N + M)), ~ proj1_sig m < N -> proj1_sig m - N < M).
move=> H17.
exists (fun (m : Count (N + M)) => match excluded_middle_informative (proj1_sig m < N) with
  | left H => inl (exist (fun (n : nat) => n < N) (proj1_sig m) H)
  | right H => inr (exist (fun (n : nat) => n < M) (proj1_sig m - N) (H17 m H))
end).
suff: (forall (m : Count N), proj1_sig m < N + M).
move=> H18.
suff: (forall (m : Count M), N + proj1_sig m < N + M).
move=> H19.
exists (fun (m : Count N + Count M) => match m with
  | inl t0 => exist (fun (n : nat) => n < N + M) (proj1_sig t0) (H18 t0)
  | inr t0 => exist (fun (n : nat) => n < N + M) (N + proj1_sig t0) (H19 t0)
end).
apply conj.
move=> x.
elim (excluded_middle_informative (proj1_sig x < N)).
move=> H20.
apply sig_map.
reflexivity.
move=> H20.
apply sig_map.
simpl.
apply (Minus.le_plus_minus_r N (proj1_sig x)).
elim (le_or_lt N (proj1_sig x)).
apply.
move=> H21.
apply False_ind.
apply (H20 H21).
move=> y.
elim (excluded_middle_informative (proj1_sig match y with
  | inl t0 => exist (fun n : nat => n < N + M) (proj1_sig t0) (H18 t0)
  | inr t0 => exist (fun n : nat => n < N + M) (N + proj1_sig t0) (H19 t0)
end < N)).
elim y.
move=> y1 H20.
suff: ((exist (fun n : nat => n < N) (proj1_sig (exist (fun n : nat => n < N + M) (proj1_sig y1) (H18 y1))) H20) = y1).
move=> H21.
rewrite H21.
reflexivity.
apply sig_map.
reflexivity.
move=> y1 H20.
apply False_ind.
apply (lt_irrefl N).
apply (le_trans (S N) (S (N + proj1_sig y1)) N).
apply (le_n_S N (N + proj1_sig y1) (Plus.le_plus_l N (proj1_sig y1))).
apply H20.
elim y.
move=> y1 H20.
apply False_ind.
apply (H20 (proj2_sig y1)).
move=> y1 H20.
suff: ((exist (fun n : nat => n < M) (proj1_sig (exist (fun n : nat => n < N + M) (N + proj1_sig y1) (H19 y1)) - N) (H17 (exist (fun n : nat => n < N + M) (N + proj1_sig y1) (H19 y1)) H20)) = y1).
move=> H21.
rewrite H21.
reflexivity.
apply sig_map.
simpl.
apply (Minus.minus_plus N (proj1_sig y1)).
move=> m.
apply (Plus.plus_lt_compat_l (proj1_sig m) M N).
apply (proj2_sig m).
move=> m.
apply (le_trans (S (proj1_sig m)) N (N + M) (proj2_sig m) (Plus.le_plus_l N M)).
move=> m H17.
apply (Plus.plus_lt_reg_l (proj1_sig m - N) M N).
rewrite (Minus.le_plus_minus_r N (proj1_sig m)).
apply (proj2_sig m).
elim (le_or_lt N (proj1_sig m)).
apply.
move=> H18.
apply False_ind.
apply (H17 H18).
apply (Corollary_4_10 K V W1 W2 H1 H2 H3 H4 (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6)) (Count N2) (Count N3)).
apply H11.
apply H14.
apply H15.
suff: (SubspaceVS K V (fun (v : VT K V) => exists (w : SubspaceMakeVST K V W2 H2), In (SubspaceMakeVST K V W2 H2) W4 w /\ v = proj1_sig w)).
move=> H15.
suff: (W2 = SumEnsembleVS K V (Intersection (VT K V) W1 W2) (fun (v : VT K V) => exists (w : SubspaceMakeVST K V W2 H2), In (SubspaceMakeVST K V W2 H2) W4 w /\ v = proj1_sig w)).
move=> H16.
suff: (SubspaceVS K V (SumEnsembleVS K V (Intersection (VT K V) W1 W2) (fun (v : VT K V) => exists (w : SubspaceMakeVST K V W2 H2), In (SubspaceMakeVST K V W2 H2) W4 w /\ v = proj1_sig w))).
move=> H17.
suff: (BasisSubspaceVS K V W2 H2 = BasisSubspaceVS K V (SumEnsembleVS K V (Intersection (VT K V) W1 W2) (fun (v : VT K V) => exists (w : SubspaceMakeVST K V W2 H2), In (SubspaceMakeVST K V W2 H2) W4 w /\ v = proj1_sig w)) H17).
move=> H18.
rewrite H18.
apply (SumEnsembleBasisVS K V (Intersection (VT K V) W1 W2) (fun v : VT K V => exists w : SubspaceMakeVST K V W2 H2, In (SubspaceMakeVST K V W2 H2) W4 w /\ v = proj1_sig w) H3 H15 H17 (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6)) (Count N3)).
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> v1.
elim.
move=> v2 H19 H20 H21.
suff: (v2 = proj1_sig (exist W2 v2 H20)).
move=> H22.
rewrite H22.
suff: (In (VT K (SubspaceMakeVS K V W2 H2)) (Singleton (VT K (SubspaceMakeVS K V W2 H2)) (VO K (SubspaceMakeVS K V W2 H2))) (exist W2 v2 H20)).
elim.
apply (In_singleton (VT K V) (VO K V)).
rewrite (proj2 (proj2 H10)).
apply Intersection_intro.
apply Intersection_intro.
apply H19.
apply H20.
elim H21.
move=> v3 H23.
suff: ((exist W2 v2 H20) = v3).
move=> H24.
rewrite H24.
apply (proj1 H23).
apply sig_map.
apply (proj2 H23).
reflexivity.
move=> v.
elim.
apply Intersection_intro.
apply H3.
apply H15.
apply H11.
suff: (forall v : VT K (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) W4 (proj1 H10)), In (VT K V) (fun v : VT K V => exists w : SubspaceMakeVST K V W2 H2, In (SubspaceMakeVST K V W2 H2) W4 w /\ v = proj1_sig w) (proj1_sig (proj1_sig v))).
move=> H19.
exists (fun (t : Count N3) => H19 (F3 t)).
apply (IsomorphicSaveBasisVS K (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) W4 (proj1 H10)) (SubspaceMakeVS K V (fun v : VT K V => exists w : SubspaceMakeVST K V W2 H2, In (SubspaceMakeVST K V W2 H2) W4 w /\ v = proj1_sig w) H15) (Count N3) F3 (fun v0 : VT K (SubspaceMakeVS K (SubspaceMakeVS K V W2 H2) W4 (proj1 H10)) => exist (fun v : VT K V => exists w : SubspaceMakeVST K V W2 H2, In (SubspaceMakeVST K V W2 H2) W4 w /\ v = proj1_sig w) (proj1_sig (proj1_sig v0)) (H19 v0))).
apply conj.
apply InjSurjBij.
move=> x1 x2 H20.
apply sig_map.
apply sig_map.
suff: (proj1_sig (proj1_sig x1) = proj1_sig (exist (fun v : VT K V => exists w : SubspaceMakeVST K V W2 H2, In (SubspaceMakeVST K V W2 H2) W4 w /\ v = proj1_sig w) (proj1_sig (proj1_sig x1)) (H19 x1))).
move=> H21.
rewrite H21.
rewrite H20.
reflexivity.
reflexivity.
move=> v.
elim (proj2_sig v).
move=> v1 H20.
exists (exist W4 v1 (proj1 H20)).
apply sig_map.
rewrite {3} (proj2 H20).
reflexivity.
apply conj.
move=> x y.
apply sig_map.
reflexivity.
move=> c x.
apply sig_map.
reflexivity.
apply H13.
move=> v.
exists (proj1_sig v).
apply conj.
apply (proj2_sig v).
reflexivity.
suff: (forall (W1 W2 : Ensemble (VT K V)), W1 = W2 -> forall (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2), BasisSubspaceVS K V W1 H1 = BasisSubspaceVS K V W2 H2).
move=> H18.
apply (H18 W2 (SumEnsembleVS K V (Intersection (VT K V) W1 W2) (fun v : VT K V => exists w : SubspaceMakeVST K V W2 H2, In (SubspaceMakeVST K V W2 H2) W4 w /\ v = proj1_sig w)) H16 H2 H17).
move=> W5 W6 H18.
rewrite H18.
move=> H19 H20.
suff: (H19 = H20).
move=> H21.
rewrite H21.
reflexivity.
apply proof_irrelevance.
rewrite - H16.
apply H2.
apply Extensionality_Ensembles.
apply conj.
move=> w H16.
suff: (w = proj1_sig (exist W2 w H16)).
move=> H17.
rewrite H17.
suff: (In (VT K (SubspaceMakeVS K V W2 H2)) (Full_set (VT K (SubspaceMakeVS K V W2 H2))) (exist W2 w H16)).
rewrite (proj1 (proj2 H10)).
elim.
move=> u1 u2 H18 H19.
apply SumEnsembleVS_intro.
apply H18.
exists u2.
apply conj.
apply H19.
reflexivity.
apply Full_intro.
reflexivity.
move=> u.
elim.
move=> u1 u2 H16 H17.
apply (proj1 H2 u1 u2).
elim H16.
move=> u3 H18 H19.
apply H19.
elim H17.
move=> u3 H18.
rewrite (proj2 H18).
apply (proj2_sig u3).
apply conj.
move=> v1 v2 H15 H16.
elim H15.
move=> w1 H17.
elim H16.
move=> w2 H18.
exists (SubspaceMakeVSVadd K V W2 H2 w1 w2).
apply conj.
apply (proj1 (proj1 H10) w1 w2 (proj1 H17) (proj1 H18)).
rewrite (proj2 H17).
rewrite (proj2 H18).
reflexivity.
apply conj.
move=> f v.
elim.
move=> w H15.
exists (SubspaceMakeVSVmul K V W2 H2 f w).
apply conj.
apply (proj1 (proj2 (proj1 H10)) f w (proj1 H15)).
rewrite (proj2 H15).
reflexivity.
exists (SubspaceMakeVSVO K V W2 H2).
apply conj.
apply (proj2 (proj2 (proj1 H10))).
reflexivity.
suff: (SubspaceVS K V (fun (v : VT K V) => exists (w : SubspaceMakeVST K V W1 H1), In (SubspaceMakeVST K V W1 H1) W3 w /\ v = proj1_sig w)).
move=> H14.
suff: (W1 = SumEnsembleVS K V (Intersection (VT K V) W1 W2) (fun (v : VT K V) => exists (w : SubspaceMakeVST K V W1 H1), In (SubspaceMakeVST K V W1 H1) W3 w /\ v = proj1_sig w)).
move=> H15.
suff: (SubspaceVS K V (SumEnsembleVS K V (Intersection (VT K V) W1 W2) (fun (v : VT K V) => exists (w : SubspaceMakeVST K V W1 H1), In (SubspaceMakeVST K V W1 H1) W3 w /\ v = proj1_sig w))).
move=> H16.
suff: (BasisSubspaceVS K V W1 H1 = BasisSubspaceVS K V (SumEnsembleVS K V (Intersection (VT K V) W1 W2) (fun (v : VT K V) => exists (w : SubspaceMakeVST K V W1 H1), In (SubspaceMakeVST K V W1 H1) W3 w /\ v = proj1_sig w)) H16).
move=> H17.
rewrite H17.
apply (SumEnsembleBasisVS K V (Intersection (VT K V) W1 W2) (fun v : VT K V => exists w : SubspaceMakeVST K V W1 H1, In (SubspaceMakeVST K V W1 H1) W3 w /\ v = proj1_sig w) H3 H14 H16 (Count (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6)) (Count N2)).
apply Extensionality_Ensembles.
apply conj.
move=> v.
elim.
move=> v1.
elim.
move=> v2 H18 H19 H20.
suff: (v2 = proj1_sig (exist W1 v2 H18)).
move=> H21.
rewrite H21.
suff: (In (VT K (SubspaceMakeVS K V W1 H1)) (Singleton (VT K (SubspaceMakeVS K V W1 H1)) (VO K (SubspaceMakeVS K V W1 H1))) (exist W1 v2 H18)).
elim.
apply (In_singleton (VT K V) (VO K V)).
rewrite (proj2 (proj2 H9)).
apply Intersection_intro.
apply Intersection_intro.
apply H18.
apply H19.
elim H20.
move=> v3 H22.
suff: ((exist W1 v2 H18) = v3).
move=> H23.
rewrite H23.
apply (proj1 H22).
apply sig_map.
apply (proj2 H22).
reflexivity.
move=> v.
elim.
apply Intersection_intro.
apply H3.
apply H14.
apply H11.
suff: (forall v : VT K (SubspaceMakeVS K (SubspaceMakeVS K V W1 H1) W3 (proj1 H9)), In (VT K V) (fun v : VT K V => exists w : SubspaceMakeVST K V W1 H1, In (SubspaceMakeVST K V W1 H1) W3 w /\ v = proj1_sig w) (proj1_sig (proj1_sig v))).
move=> H18.
exists (fun (t : Count N2) => H18 (F2 t)).
apply (IsomorphicSaveBasisVS K (SubspaceMakeVS K (SubspaceMakeVS K V W1 H1) W3 (proj1 H9)) (SubspaceMakeVS K V (fun v : VT K V => exists w : SubspaceMakeVST K V W1 H1, In (SubspaceMakeVST K V W1 H1) W3 w /\ v = proj1_sig w) H14) (Count N2) F2 (fun v0 : VT K (SubspaceMakeVS K (SubspaceMakeVS K V W1 H1) W3 (proj1 H9)) => exist (fun v : VT K V => exists w : SubspaceMakeVST K V W1 H1, In (SubspaceMakeVST K V W1 H1) W3 w /\ v = proj1_sig w) (proj1_sig (proj1_sig v0)) (H18 v0))).
apply conj.
apply InjSurjBij.
move=> x1 x2 H19.
apply sig_map.
apply sig_map.
suff: (proj1_sig (proj1_sig x1) = proj1_sig (exist (fun v : VT K V => exists w : SubspaceMakeVST K V W1 H1, In (SubspaceMakeVST K V W1 H1) W3 w /\ v = proj1_sig w) (proj1_sig (proj1_sig x1)) (H18 x1))).
move=> H20.
rewrite H20.
rewrite H19.
reflexivity.
reflexivity.
move=> v.
elim (proj2_sig v).
move=> v1 H19.
exists (exist W3 v1 (proj1 H19)).
apply sig_map.
rewrite {3} (proj2 H19).
reflexivity.
apply conj.
move=> x y.
apply sig_map.
reflexivity.
move=> c x.
apply sig_map.
reflexivity.
apply H12.
move=> v.
exists (proj1_sig v).
apply conj.
apply (proj2_sig v).
reflexivity.
suff: (forall (W1 W2 : Ensemble (VT K V)), W1 = W2 -> forall (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2), BasisSubspaceVS K V W1 H1 = BasisSubspaceVS K V W2 H2).
move=> H17.
apply (H17 W1 (SumEnsembleVS K V (Intersection (VT K V) W1 W2) (fun v : VT K V => exists w : SubspaceMakeVST K V W1 H1, In (SubspaceMakeVST K V W1 H1) W3 w /\ v = proj1_sig w)) H15 H1 H16).
move=> W5 W6 H17.
rewrite H17.
move=> H18 H19.
suff: (H18 = H19).
move=> H20.
rewrite H20.
reflexivity.
apply proof_irrelevance.
rewrite - H15.
apply H1.
apply Extensionality_Ensembles.
apply conj.
move=> w H15.
suff: (w = proj1_sig (exist W1 w H15)).
move=> H16.
rewrite H16.
suff: (In (VT K (SubspaceMakeVS K V W1 H1)) (Full_set (VT K (SubspaceMakeVS K V W1 H1))) (exist W1 w H15)).
rewrite (proj1 (proj2 H9)).
elim.
move=> u1 u2 H17 H18.
apply SumEnsembleVS_intro.
apply H17.
exists u2.
apply conj.
apply H18.
reflexivity.
apply Full_intro.
reflexivity.
move=> u.
elim.
move=> u1 u2 H15 H16.
apply (proj1 H1 u1 u2).
elim H15.
move=> u3 H17 H18.
apply H17.
elim H16.
move=> u3 H17.
rewrite (proj2 H17).
apply (proj2_sig u3).
apply conj.
move=> v1 v2 H14 H15.
elim H14.
move=> w1 H16.
elim H15.
move=> w2 H17.
exists (SubspaceMakeVSVadd K V W1 H1 w1 w2).
apply conj.
apply (proj1 (proj1 H9) w1 w2 (proj1 H16) (proj1 H17)).
rewrite (proj2 H16).
rewrite (proj2 H17).
reflexivity.
apply conj.
move=> f v.
elim.
move=> w H14.
exists (SubspaceMakeVSVmul K V W1 H1 f w).
apply conj.
apply (proj1 (proj2 (proj1 H9)) f w (proj1 H14)).
rewrite (proj2 H14).
reflexivity.
exists (SubspaceMakeVSVO K V W1 H1).
apply conj.
apply (proj2 (proj2 (proj1 H9))).
reflexivity.
apply conj.
move=> v1 v2 H10 H11.
apply (proj1 H3 (proj1_sig v1) (proj1_sig v2) H10 H11).
apply conj.
move=> f v H10.
apply (proj1 (proj2 H3) f (proj1_sig v) H10).
apply (proj2 (proj2 H3)).
apply H8.
apply conj.
move=> v1 v2 H9 H10.
apply (proj1 H3 (proj1_sig v1) (proj1_sig v2) H9 H10).
apply conj.
move=> f v H9.
apply (proj1 (proj2 H3) f (proj1_sig v) H9).
apply (proj2 (proj2 H3)).
apply H7.
Qed.

Lemma DimensionSumEnsembleVS_exists : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2), exists (H3 : SubspaceVS K V (Intersection (VT K V) W1 W2)) (H4 : SubspaceVS K V (SumEnsembleVS K V W1 W2)), forall (H5 : FiniteDimensionVS K (SubspaceMakeVS K V (SumEnsembleVS K V W1 W2) H4)), exists (H6 : FiniteDimensionVS K (SubspaceMakeVS K V (Intersection (VT K V) W1 W2) H3)) (H7 : FiniteDimensionVS K (SubspaceMakeVS K V W1 H1)) (H8 : FiniteDimensionVS K (SubspaceMakeVS K V W2 H2)), DimensionSubspaceVS K V (SumEnsembleVS K V W1 W2) H4 H5 + DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H3 H6 = DimensionSubspaceVS K V W1 H1 H7 + DimensionSubspaceVS K V W2 H2 H8.
Proof.
move=> K V W1 W2 H1 H2.
exists (IntersectionSubspaceVS K V W1 W2 H1 H2).
exists (SumSubspaceVS K V W1 W2 H1 H2).
move=> H3.
suff: (FiniteDimensionVS K (SubspaceMakeVS K V W1 H1)).
move=> H4.
suff: (FiniteDimensionVS K (SubspaceMakeVS K V W2 H2)).
move=> H5.
suff: (FiniteDimensionVS K (SubspaceMakeVS K V (Intersection (VT K V) W1 W2) (IntersectionSubspaceVS K V W1 W2 H1 H2))).
move=> H6.
exists H6.
exists H4.
exists H5.
apply (DimensionSumEnsembleVS K V W1 W2 H1 H2 (IntersectionSubspaceVS K V W1 W2 H1 H2) (SumSubspaceVS K V W1 W2 H1 H2) H3 H6 H4 H5).
apply (Proposition_5_9_1_1_subspace K V (Intersection (VT K V) W1 W2) W1 (IntersectionSubspaceVS K V W1 W2 H1 H2) H1).
move=> v.
elim.
move=> w H6 H7.
apply H6.
apply H4.
apply (Proposition_5_9_1_1_subspace K V W2 (SumEnsembleVS K V W1 W2) H2 (SumSubspaceVS K V W1 W2 H1 H2)).
move=> w H5.
rewrite - (Vadd_O_l K V w).
apply (SumEnsembleVS_intro K V W1 W2 (VO K V) w (proj2 (proj2 H1)) H5).
apply H3.
apply (Proposition_5_9_1_1_subspace K V W1 (SumEnsembleVS K V W1 W2) H1 (SumSubspaceVS K V W1 W2 H1 H2)).
move=> w H5.
rewrite - (Vadd_O_r K V w).
apply (SumEnsembleVS_intro K V W1 W2 w (VO K V) H5 (proj2 (proj2 H2))).
apply H3.
Qed.

Lemma DimensionSumEnsembleVS2 : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2) (H3 : SubspaceVS K V (SumEnsembleVS K V W1 W2)) (H4 : FiniteDimensionVS K (SubspaceMakeVS K V (SumEnsembleVS K V W1 W2) H3)) (H5 : FiniteDimensionVS K (SubspaceMakeVS K V W1 H1)) (H6 : FiniteDimensionVS K (SubspaceMakeVS K V W2 H2)), Intersection (VT K V) W1 W2 = Singleton (VT K V) (VO K V) -> DimensionSubspaceVS K V (SumEnsembleVS K V W1 W2) H3 H4 = DimensionSubspaceVS K V W1 H1 H5 + DimensionSubspaceVS K V W2 H2 H6.
Proof.
move=> K V W1 W2 H1 H2 H3 H4 H5 H6 H7.
suff: (SubspaceVS K V (Intersection (VT K V) W1 W2)).
move=> H8.
suff: (FiniteDimensionVS K (SubspaceMakeVS K V (Intersection (VT K V) W1 W2) H8)).
move=> H9.
rewrite - (DimensionSumEnsembleVS K V W1 W2 H1 H2 H8 H3 H4 H9 H5 H6).
elim (VOSubspaceVSDimension K V).
move=> H10 H11.
suff: (DimensionSubspaceVS K V (Intersection (VT K V) W1 W2) H8 H9 = DimensionSubspaceVS K V (Singleton (VT K V) (VO K V)) (VOSubspaceVS K V) H10).
move=> H12.
rewrite H12.
rewrite H11.
rewrite (Plus.plus_0_r (DimensionSubspaceVS K V (SumEnsembleVS K V W1 W2) H3 H4)).
reflexivity.
suff: (forall (W1 W2 : Ensemble (VT K V)), W1 = W2 -> forall (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2) (H3 : FiniteDimensionVS K (SubspaceMakeVS K V W1 H1)) (H4 : FiniteDimensionVS K (SubspaceMakeVS K V W2 H2)), DimensionSubspaceVS K V W1 H1 H3 = DimensionSubspaceVS K V W2 H2 H4).
move=> H12.
apply (H12 (Intersection (VT K V) W1 W2) (Singleton (VT K V) (VO K V)) H7 H8 (VOSubspaceVS K V) H9 H10).
move=> W3 W4 H12.
rewrite H12.
move=> H13 H14.
suff: (H13 = H14).
move=> H15.
rewrite H15.
move=> H16 H17.
suff: (H16 = H17).
move=> H18.
rewrite H18.
reflexivity.
apply proof_irrelevance.
apply proof_irrelevance.
suff: (forall (W1 W2 : Ensemble (VT K V)), W1 = W2 -> forall (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2), FiniteDimensionVS K (SubspaceMakeVS K V W1 H1) = FiniteDimensionVS K (SubspaceMakeVS K V W2 H2)).
move=> H9.
rewrite (H9 (Intersection (VT K V) W1 W2) (Singleton (VT K V) (VO K V)) H7 H8 (VOSubspaceVS K V)).
elim (VOSubspaceVSDimension K V).
move=> H10 H11.
apply H10.
move=> W3 W4 H9.
rewrite H9.
move=> H10 H11.
suff: (H10 = H11).
move=> H12.
rewrite H12.
reflexivity.
apply proof_irrelevance.
apply (IntersectionSubspaceVS K V W1 W2 H1 H2).
Qed.

Lemma DimensionSumEnsembleVS2_exists : forall (K : Field) (V : VectorSpace K) (W1 W2 : Ensemble (VT K V)) (H1 : SubspaceVS K V W1) (H2 : SubspaceVS K V W2), exists (H3 : SubspaceVS K V (SumEnsembleVS K V W1 W2)), forall (H4 : FiniteDimensionVS K (SubspaceMakeVS K V (SumEnsembleVS K V W1 W2) H3)), exists (H5 : FiniteDimensionVS K (SubspaceMakeVS K V W1 H1)) (H6 : FiniteDimensionVS K (SubspaceMakeVS K V W2 H2)), Intersection (VT K V) W1 W2 = Singleton (VT K V) (VO K V) -> DimensionSubspaceVS K V (SumEnsembleVS K V W1 W2) H3 H4 = DimensionSubspaceVS K V W1 H1 H5 + DimensionSubspaceVS K V W2 H2 H6.
Proof.
move=> K V W1 W2 H1 H2.
exists (SumSubspaceVS K V W1 W2 H1 H2).
move=> H3.
suff: (FiniteDimensionVS K (SubspaceMakeVS K V W1 H1)).
move=> H4.
suff: (FiniteDimensionVS K (SubspaceMakeVS K V W2 H2)).
move=> H5.
exists H4.
exists H5.
move=> H6.
apply (DimensionSumEnsembleVS2 K V W1 W2 H1 H2 (SumSubspaceVS K V W1 W2 H1 H2) H3 H4 H5 H6).
apply (Proposition_5_9_1_1_subspace K V W2 (SumEnsembleVS K V W1 W2) H2 (SumSubspaceVS K V W1 W2 H1 H2)).
move=> w H5.
rewrite - (Vadd_O_l K V w).
apply (SumEnsembleVS_intro K V W1 W2 (VO K V) w (proj2 (proj2 H1)) H5).
apply H3.
apply (Proposition_5_9_1_1_subspace K V W1 (SumEnsembleVS K V W1 W2) H1 (SumSubspaceVS K V W1 W2 H1 H2)).
move=> w H5.
rewrite - (Vadd_O_r K V w).
apply (SumEnsembleVS_intro K V W1 W2 w (VO K V) H5 (proj2 (proj2 H2))).
apply H3.
Qed.

End Senkeidaisuunosekai1.







