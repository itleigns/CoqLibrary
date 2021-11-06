Add LoadPath "Analysis/KaisekiNyuumonn" as Analysis.KaisekiNyuumonn.
Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "BasicProperty" as BasicProperty.
Add LoadPath "BasicNotation" as BasicNotation.
Add LoadPath "Tools" as Tools.
Add LoadPath "LibraryExtension" as LibraryExtension.
Add LoadPath "LinearAlgebra" as LinearAlgebra.
Add LoadPath "LinearAlgebra/SenkeiDaisuunoSekai" as LinearAlgebra.SenkeiDaisuunoSekai.

From mathcomp Require Import ssreflect.
Require Import Reals.
Require Import Classical.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Image.
Require Import MyAlgebraicStructure.MyVectorSpace.
Require Import MyAlgebraicStructure.MyField.
Require Import Analysis.KaisekiNyuumonn.KaisekiNyuumonn1.
Require Import LinearAlgebra.Matrix.
Require Import LinearAlgebra.SenkeiDaisuunoSekai.SenkeiDaisuunoSekai1.
Require Import Tools.MySum.
Require Import BasicProperty.MappingProperty.
Local Open Scope R_scope.

Record RCInner_Product_Space (K : RC) (V : VectorSpace (RCfield K)) : Type := mkRCInner_Product_Space {
  RCip : VT (RCfield K) V -> VT (RCfield K) V -> (RCT K);
  RCip_sym : forall (x y : VT (RCfield K) V), RCip x y = ConjugateRC K (RCip y x);
  RCip_linear_mult_l : forall (c : RCT K) (x y : VT (RCfield K) V), RCip (Vmul (RCfield K) V c x) y = RCmult K c (RCip x y);
  RCip_linear_plus_l : forall (x1 x2 y : VT (RCfield K) V), RCip (Vadd (RCfield K) V x1 x2) y = RCplus K (RCip x1 y) (RCip x2 y);
  RCip_pos : forall (x : VT (RCfield K) V), RCsemipos K (RCip x x);
  RCip_refl : forall (x : VT (RCfield K) V), RCip x x = RCO K <-> x = VO (RCfield K) V
}.

Definition RInner_Product_Space := RCInner_Product_Space RK.

Definition mkRInner_Product_Space : forall (V : VectorSpace Rfield) (Rip : VT Rfield V -> VT Rfield V -> R) (Rip_sym : forall (x y : VT Rfield V), Rip x y = Rip y x) (Rip_linear_mult_l : forall (c : R) (x y : VT Rfield V), Rip (Vmul Rfield V c x) y = c * (Rip x y)) (Rip_linear_plus_l : forall (x1 x2 y : VT Rfield V), Rip (Vadd Rfield V x1 x2) y = (Rip x1 y) + (Rip x2 y)) (Rip_pos : forall (x : VT Rfield V), Rip x x >= 0) (Rip_refl : forall (x : VT Rfield V), Rip x x = 0 <-> x = VO Rfield V), RInner_Product_Space V := mkRCInner_Product_Space RK.

Definition Rip := RCip RK.

Definition Rip_sym : forall (V : VectorSpace Rfield) (r : RInner_Product_Space V) (x y : VT Rfield V), Rip V r x y = Rip V r y x := RCip_sym RK.

Definition Rip_linear_mult_l : forall (V : VectorSpace Rfield) (r : RInner_Product_Space V) (c : R) (x y : VT Rfield V), Rip V r (Vmul Rfield V c x) y = c * (Rip V r x y) := RCip_linear_mult_l RK.

Definition Rip_linear_plus_l : forall (V : VectorSpace Rfield) (r : RInner_Product_Space V) (x1 x2 y : VT Rfield V), Rip V r (Vadd Rfield V x1 x2) y = (Rip V r x1 y) + (Rip V r x2 y) := RCip_linear_plus_l RK.

Definition Rip_pos : forall (V : VectorSpace Rfield) (r : RInner_Product_Space V) (x : VT Rfield V), Rip V r x x >= 0 := RCip_pos RK.

Definition Rip_refl : forall (V : VectorSpace Rfield) (r : RInner_Product_Space V) (x : VT Rfield V), Rip V r x x = 0 <-> x = VO Rfield V := RCip_refl RK.

Definition CInner_Product_Space := RCInner_Product_Space CK.

Definition mkCInner_Product_Space : forall (V : VectorSpace Cfield) (Cip : VT Cfield V -> VT Cfield V -> C) (Cip_sym : forall (x y : VT Cfield V), Cip x y = Conjugate (Cip y x)) (Cip_linear_mult_l : forall (c : C) (x y : VT Cfield V), Cip (Vmul Cfield V c x) y = Cmult c (Cip x y)) (Cip_linear_plus_l : forall (x1 x2 y : VT Cfield V), Cip (Vadd Cfield V x1 x2) y = Cplus (Cip x1 y) (Cip x2 y)) (Cip_pos : forall (x : VT Cfield V), Csemipos (Cip x x)) (Cip_refl : forall (x : VT Cfield V), Cip x x = CO <-> x = VO Cfield V), CInner_Product_Space V := mkRCInner_Product_Space CK.

Definition Cip := RCip CK.

Definition Cip_sym : forall (V : VectorSpace Cfield) (r : CInner_Product_Space V) (x y : VT Cfield V), Cip V r x y = Conjugate (Cip V r y x) := RCip_sym CK.

Definition Cip_linear_mult_l : forall (V : VectorSpace Cfield) (r : CInner_Product_Space V) (c : C) (x y : VT Cfield V), Cip V r (Vmul Cfield V c x) y = Cmult c (Cip V r x y) := RCip_linear_mult_l CK.

Definition Cip_linear_plus_l : forall (V : VectorSpace Cfield) (r : CInner_Product_Space V) (x1 x2 y : VT Cfield V), Cip V r (Vadd Cfield V x1 x2) y = Cplus (Cip V r x1 y) (Cip V r x2 y) := RCip_linear_plus_l CK.

Definition Cip_pos : forall (V : VectorSpace Cfield) (r : CInner_Product_Space V) (x : VT Cfield V), Csemipos (Cip V r x x) := RCip_pos CK.

Definition Cip_refl : forall (V : VectorSpace Cfield) (r : CInner_Product_Space V) (x : VT Cfield V), Cip V r x x = CO <-> x = VO Cfield V := RCip_refl CK.

Definition Cip_pos_re (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x : VT Cfield V) : (Cip V I x x) CRe >= 0 := proj1 (Cip_pos V I x).

Definition Cip_pos_im (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x : VT Cfield V) : (Cip V I x x) CIm = 0 := proj2 (Cip_pos V I x).

Lemma RCip_linear_mult_r : forall (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (c : RCT K) (x y : VT (RCfield K) V), RCip K V I x (Vmul (RCfield K) V c y) = RCmult K (ConjugateRC K c) (RCip K V I x y).
Proof.
move=> K V I c x y.
rewrite (RCip_sym K V I x (Vmul (RCfield K) V c y)).
rewrite (RCip_linear_mult_l K V I c y x).
rewrite (RCip_sym K V I x y).
apply (Proposition_4_8_2_RC K c (RCip K V I y x)).
Qed.

Definition Rip_linear_mult_r : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (c : R) (x y : VT Rfield V), Rip V I x (Vmul Rfield V c y) = c * (Rip V I x y) := RCip_linear_mult_r RK.

Definition Cip_linear_mult_r : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (c : C) (x y : VT Cfield V), Cip V I x (Vmul Cfield V c y) = Cmult (Conjugate c) (Cip V I x y) := RCip_linear_mult_r CK.

Lemma RCip_linear_plus_r : forall (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (x y1 y2 : VT (RCfield K) V), RCip K V I x (Vadd (RCfield K) V y1 y2) = RCplus K (RCip K V I x y1) (RCip K V I x y2).
Proof.
move=> K V I x y1 y2.
rewrite (RCip_sym K V I x (Vadd (RCfield K) V y1 y2)).
rewrite (RCip_linear_plus_l K V I y1 y2 x).
rewrite (RCip_sym K V I x y1).
rewrite (RCip_sym K V I x y2).
apply (Proposition_4_8_1_1_RC K (RCip K V I y1 x) (RCip K V I y2 x)).
Qed.

Definition Rip_linear_plus_r : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (x y1 y2 : VT Rfield V), Rip V I x (Vadd Rfield V y1 y2) = (Rip V I x y1) + (Rip V I x y2) := RCip_linear_plus_r RK.

Definition Cip_linear_plus_r : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x y1 y2 : VT Cfield V), Cip V I x (Vadd Cfield V y1 y2) = Cplus (Cip V I x y1) (Cip V I x y2) := RCip_linear_plus_r CK.

Lemma RCip_mult_0_l : forall (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (x : VT (RCfield K) V), RCip K V I (VO (RCfield K) V) x = RCO K.
Proof.
move=> K V I x.
suff: (VO (RCfield K) V = Vmul (RCfield K) V (RCO K) (VO (RCfield K) V)).
move=> H1.
rewrite H1.
rewrite (RCip_linear_mult_l K V I (RCO K)).
apply (Fmul_O_l (RCfield K)).
rewrite (Vmul_O_r (RCfield K) V (RCO K)).
reflexivity.
Qed.

Definition Rip_mult_0_l : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (x : VT Rfield V), Rip V I (VO Rfield V) x = 0 := RCip_mult_0_l RK.

Definition Cip_mult_0_l : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x : VT Cfield V), Cip V I (VO Cfield V) x = CO := RCip_mult_0_l CK.

Lemma RCip_mult_0_r : forall (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (x : VT (RCfield K) V), RCip K V I x (VO (RCfield K) V) = RCO K.
Proof.
move=> K V I x.
rewrite (RCip_sym K V I x (VO (RCfield K) V)).
rewrite (RCip_mult_0_l K V I x).
apply (ConjugateRCO K).
Qed.

Definition Rip_mult_0_r : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (x : VT Rfield V), Rip V I x (VO Rfield V) = 0 := RCip_mult_0_r RK.

Definition Cip_mult_0_r : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x : VT Cfield V), Cip V I x (VO Cfield V) = CO := RCip_mult_0_r CK.

Lemma RCip_linear_opp_l : forall (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (x y : VT (RCfield K) V), RCip K V I (Vopp (RCfield K) V x) y = RCopp K (RCip K V I x y).
Proof.
move=> K V I x y.
apply (Fadd_opp_r_uniq (RCfield K) (RCip K V I x y) (RCip K V I (Vopp (RCfield K) V x) y)).
simpl.
rewrite - (RCip_linear_plus_l K V I x (Vopp (RCfield K) V x) y).
rewrite (Vadd_opp_r (RCfield K) V x).
apply (RCip_mult_0_l K V I y).
Qed.

Definition Rip_linear_opp_l : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (x y : VT Rfield V), Rip V I (Vopp Rfield V x) y = - (Rip V I x y) := RCip_linear_opp_l RK.

Definition Cip_linear_opp_l : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x y : VT Cfield V), Cip V I (Vopp Cfield V x) y = Copp (Cip V I x y) := RCip_linear_opp_l CK.

Lemma RCip_linear_opp_r : forall (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (x y : VT (RCfield K) V), RCip K V I x (Vopp (RCfield K) V y) = RCopp K (RCip K V I x y).
Proof.
move=> K V I x y.
apply (Fadd_opp_r_uniq (RCfield K) (RCip K V I x y) (RCip K V I x (Vopp (RCfield K) V y))).
simpl.
rewrite - (RCip_linear_plus_r K V I x y (Vopp (RCfield K) V y)).
rewrite (Vadd_opp_r (RCfield K) V y).
apply (RCip_mult_0_r K V I x).
Qed.

Definition Rip_linear_opp_r : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (x y : VT Rfield V), Rip V I x (Vopp Rfield V y) = - (Rip V I x y) := RCip_linear_opp_r RK.

Definition Cip_linear_opp_r : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x y : VT Cfield V), Cip V I x (Vopp Cfield V y) = Copp (Cip V I x y) := RCip_linear_opp_r CK.

Definition RIPNorm (V : VectorSpace Rfield) (I : RInner_Product_Space V) (x : VT Rfield V) := MySqrt (exist (fun (r : R) => r >= 0) (Rip V I x x) (Rip_pos V I x)).

Definition CIPNorm (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x : VT Cfield V) := MySqrt (exist (fun (r : R) => r >= 0) (Cip V I x x CRe) (Cip_pos_re V I x)).

Definition RCIPNorm : forall (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (x : VT (RCfield K) V), R := fun (K : RC) => match K with
  | RK => RIPNorm
  | CK => CIPNorm
end.

Lemma RIPNormNature : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (x : VT Rfield V), RIPNorm V I x >= 0 /\ Rip V I x x = RIPNorm V I x * RIPNorm V I x.
Proof.
move=> V I x.
apply (MySqrtNature (exist (fun (r : R) => r >= 0) (Rip V I x x) (Rip_pos V I x))).
Qed.

Lemma CIPNormNature : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x : VT Cfield V), CIPNorm V I x >= 0 /\ Cip V I x x CRe = CIPNorm V I x * CIPNorm V I x.
Proof.
move=> V I x.
apply (MySqrtNature (exist (fun (r : R) => r >= 0) (Cip V I x x CRe) (Cip_pos_re V I x))).
Qed.

Definition RCIPNormNature : forall (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (x : VT (RCfield K) V), RCIPNorm K V I x >= 0 /\ RCRe K (RCip K V I x x) = RCIPNorm K V I x * RCIPNorm K V I x := fun (K : RC) => match K with
  | RK => RIPNormNature
  | CK => CIPNormNature
end.

Lemma RIPNormNature2 : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (x : VT Rfield V) (y : R), y >= 0 /\ Rip V I x x = y * y -> RIPNorm V I x = y.
Proof.
move=> V I x.
apply (MySqrtNature2 (exist (fun (r : R) => r >= 0) (Rip V I x x) (Rip_pos V I x))).
Qed.

Lemma CIPNormNature2 : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x : VT Cfield V) (y : R), y >= 0 /\ Cip V I x x CRe = y * y -> CIPNorm V I x = y.
Proof.
move=> V I x.
apply (MySqrtNature2 (exist (fun (r : R) => r >= 0) (Cip V I x x CRe) (Cip_pos_re V I x))).
Qed.

Definition RCIPNormNature2 : forall (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (x : VT (RCfield K) V) (y : R), y >= 0 /\ RCRe K (RCip K V I x x) = y * y -> RCIPNorm K V I x = y := fun (K : RC) => match K with
  | RK => RIPNormNature2
  | CK => CIPNormNature2
end.

Definition OrthonormalSystemRC (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (T : Type) (W : T -> VT (RCfield K) V) := (forall (t : T), RCip K V I (W t) (W t) = RCI K) /\ (forall (t1 t2 : T), t1 <> t2 -> RCip K V I (W t1) (W t2) = RCO K).

Definition OrthonormalSystemR (V : VectorSpace Rfield) (I : RInner_Product_Space V) (T : Type) (W : T -> VT Rfield V) := (forall (t : T), Rip V I (W t) (W t) = 1) /\ (forall (t1 t2 : T), t1 <> t2 -> Rip V I (W t1) (W t2) = 0).

Definition OrthonormalSystemC (V : VectorSpace Cfield) (I : CInner_Product_Space V) (T : Type) (W : T -> VT Cfield V) := (forall (t : T), Cip V I (W t) (W t) = CI) /\ (forall (t1 t2 : T), t1 <> t2 -> Cip V I (W t1) (W t2) = CO).

Lemma OrthonormalSystemLinearlyIndependentRC : forall (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (T : Type) (W : T -> VT (RCfield K) V), OrthonormalSystemRC K V I T W -> LinearlyIndependentVS (RCfield K) V T W.
Proof.
move=> K V I T W H1.
apply (proj2 (LinearlyIndependentVSDef3 (RCfield K) V T W)).
move=> a A H2 t H3.
suff: (a t = RCip K V I (MySumF2 T A (VSPCM (RCfield K) V) (fun (t : T) => Vmul (RCfield K) V (a t) (W t))) (W t)).
move=> H4.
rewrite H4.
rewrite H2.
apply (RCip_mult_0_l K V I (W t)).
suff: (RCip K V I (MySumF2 T A (VSPCM (RCfield K) V) (fun (t0 : T) => Vmul (RCfield K) V (a t0) (W t0))) (W t) = MySumF2 T A (FPCM (RCfield K)) (fun (t0 : T) => RCmult K (a t0) (RCip K V I (W t0) (W t)))).
move=> H4.
rewrite H4.
rewrite (MySumF2Included T (FiniteSingleton T t)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (proj1 H1 t).
suff: (RCmult K (a t) (RCI K) = a t).
move=> H5.
rewrite H5.
rewrite (CM_O_r (FPCM (RCfield K)) (a t)).
reflexivity.
apply (Fmul_I_r (RCfield K) (a t)).
move=> u.
elim.
move=> u0 H5 H6.
rewrite (proj2 H1 u0 t).
apply (Fmul_O_r (RCfield K) (a u0)).
move=> H7.
apply H5.
rewrite H7.
apply (In_singleton T t).
move=> t0.
elim.
apply H3.
apply (FiniteSetInduction T A).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (RCip_mult_0_l K V I (W t)).
move=> B b H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (RCip_linear_plus_l K V I).
rewrite H7.
rewrite (RCip_linear_mult_l K V I).
reflexivity.
apply H6.
apply H6.
Qed.

Definition OrthonormalSystemLinearlyIndependentR : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (T : Type) (W : T -> VT Rfield V), OrthonormalSystemR V I T W -> LinearlyIndependentVS Rfield V T W := OrthonormalSystemLinearlyIndependentRC RK.

Definition OrthonormalSystemLinearlyIndependentC : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (T : Type) (W : T -> VT Cfield V), OrthonormalSystemC V I T W -> LinearlyIndependentVS Cfield V T W := OrthonormalSystemLinearlyIndependentRC CK.

Lemma GramSchmidtLinearlyIndepententRC_sub : forall (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (N : nat) (W : Count N -> VT (RCfield K) V), LinearlyIndependentVS (RCfield K) V (Count N) W -> {Z : Count N -> VT (RCfield K) V | OrthonormalSystemRC K V I (Count N) Z /\ forall (m : Count N), In (VT (RCfield K) V) (SpanVS (RCfield K) V {k : Count N | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))) (Z m)}.
Proof.
suff: (forall (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (N : nat) (W : Count N -> VT (RCfield K) V), LinearlyIndependentVS (RCfield K) V (Count N) W -> {Z : Count N -> VT (RCfield K) V | LinearlyIndependentVS (RCfield K) V (Count N) Z /\ (forall (t1 t2 : Count N), t1 <> t2 -> RCip K V I (Z t1) (Z t2) = RCO K) /\ forall (m : Count N), In (VT (RCfield K) V) (SpanVS (RCfield K) V {k : Count N | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))) (Z m)}).
move=> H1 K V I N W H2.
elim (H1 K V I N W H2).
move=> Z H3.
exists (fun (m : Count N) => Vmul (RCfield K) V (IRRC K (/ RCIPNorm K V I (Z m))) (Z m)).
apply conj.
apply conj.
move=> t.
rewrite (RCip_linear_mult_l K V I).
rewrite (RCip_linear_mult_r K V I).
rewrite - (RCmult_assoc K).
suff: (RCRe K (RCip K V I (Z t) (Z t)) <> 0).
move=> H4.
suff: (RCIPNorm K V I (Z t) <> 0).
move=> H5.
suff: (forall (K : RC) (r : R), ConjugateRC K (IRRC K r) = IRRC K r).
move=> H6.
rewrite (H6 K (/ RCIPNorm K V I (Z t))).
rewrite - (IRRCmult K (/ RCIPNorm K V I (Z t)) (/ RCIPNorm K V I (Z t))).
rewrite - (Rinv_mult_distr (RCIPNorm K V I (Z t)) (RCIPNorm K V I (Z t)) H5 H5).
rewrite (IRRCinv K (RCIPNorm K V I (Z t) * RCIPNorm K V I (Z t))).
rewrite - (proj2 (RCIPNormNature K V I (Z t))).
suff: (forall (K : RC) (x : RCT K), RCsemipos K x -> IRRC K (RCRe K x) = x).
move=> H7.
rewrite (H7 K (RCip K V I (Z t) (Z t))).
apply (Finv_l (RCfield K) (RCip K V I (Z t) (Z t))).
move=> H8.
apply H4.
rewrite H8.
simpl.
elim K.
reflexivity.
reflexivity.
apply (RCip_pos K V I (Z t)).
elim.
move=> x H7.
reflexivity.
move=> x H7.
simpl.
unfold IRC.
apply functional_extensionality.
move=> k.
elim (CReorCIm k).
move=> H8.
rewrite H8.
apply (CmakeRe (x CRe) 0).
move=> H8.
rewrite H8.
rewrite (proj2 H7).
apply (CmakeIm (x CRe) 0).
move=> H7.
apply H5.
rewrite - (Rmult_1_l (RCIPNorm K V I (Z t))).
rewrite - (Rinv_l (RCIPNorm K V I (Z t)) H5).
rewrite Rmult_assoc.
rewrite H7.
apply Rmult_0_r.
elim.
move=> r.
reflexivity.
move=> r.
simpl.
unfold Conjugate.
unfold IRC.
rewrite (CmakeRe r 0).
rewrite (CmakeIm r 0).
rewrite Ropp_0.
reflexivity.
move=> H5.
apply H4.
rewrite (proj2 (RCIPNormNature K V I (Z t))).
rewrite H5.
apply (Rmult_0_l 0).
move=> H4.
apply (LinearlyIndependentNotContainVOVS (RCfield K) V (Count N) Z (proj1 H3) t).
apply (proj1 (RCip_refl K V I (Z t))).
suff: (forall (K : RC) (x : RCT K), RCsemipos K x -> RCRe K x = 0 -> x = RCO K).
move=> H5.
apply (H5 K (RCip K V I (Z t) (Z t)) (RCip_pos K V I (Z t)) H4).
elim.
move=> x H5.
apply.
move=> x H5 H6.
apply functional_extensionality.
move=> k.
elim (CReorCIm k).
move=> H7.
rewrite H7.
apply H6.
move=> H7.
rewrite H7.
apply (proj2 H5).
move=> t1 t2 H4.
rewrite (RCip_linear_mult_l K V I).
rewrite (RCip_linear_mult_r K V I).
rewrite (proj1 (proj2 H3) t1 t2 H4).
suff: (RCmult K (ConjugateRC K (IRRC K (/ RCIPNorm K V I (Z t2)))) (RCO K) = RCO K).
move=> H5.
rewrite H5.
apply (Fmul_O_r (RCfield K)).
apply (Fmul_O_r (RCfield K)).
move=> m.
apply (proj1 (proj2 (SpanSubspaceVS (RCfield K) V {k : Count N | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))))).
apply (proj2 (proj2 H3) m).
move=> K V I.
elim.
move=> W H1.
exists W.
apply conj.
apply H1.
apply conj.
move=> t1.
elim (le_not_lt 0 (proj1_sig t1) (le_0_n (proj1_sig t1)) (proj2_sig t1)).
move=> m.
elim (le_not_lt 0 (proj1_sig m) (le_0_n (proj1_sig m)) (proj2_sig m)).
move=> N H1 W H2.
suff: (forall m : Count N, (proj1_sig m < S N)%nat).
move=> H3.
suff: ((N < S N)%nat).
move=> H4.
elim (H1 (fun (m : Count N) => W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m)))).
move=> W0 H5.
exists (fun (m : Count (S N)) => match excluded_middle_informative (proj1_sig m < N)%nat with
  | left H => W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig m) H)
  | right _ => Vadd (RCfield K) V (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) (Vopp (RCfield K) V (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM (RCfield K) V) (fun (m : Count N) => Vmul (RCfield K) V (ConjugateRC K (RCmult K (RCip K V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) (RCinv K (RCip K V I (W0 m) (W0 m))))) (W0 m))))
end).
apply conj.
apply (Proposition_5_2 (RCfield K) V N H3 H4).
apply conj.
suff: ((fun (m : Count N) => match excluded_middle_informative (proj1_sig (exist (fun (n : nat) => n < S N) (proj1_sig m) (H3 m)) < N)%nat with
  | left H => W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))) H)
  | right _ => Vadd (RCfield K) V (W (exist (fun k : nat => (k < S N)%nat) N H4)) (Vopp (RCfield K) V (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM (RCfield K) V) (fun m0 : Count N => Vmul (RCfield K) V (ConjugateRC K (RCmult K (RCip K V I (W0 m0) (W (exist (fun k : nat => (k < S N)%nat) N H4))) (RCinv K (RCip K V I (W0 m0) (W0 m0))))) (W0 m0))))
end) = W0).
move=> H6.
rewrite H6.
apply (proj1 H5).
apply functional_extensionality.
move=> k.
elim (excluded_middle_informative (proj1_sig (exist (fun (n : nat) => n < S N) (proj1_sig k) (H3 k)) < N)%nat).
move=> H6.
suff: ((exist (fun (l : nat) => (l < N)%nat) (proj1_sig (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig k) (H3 k))) H6) = k).
move=> H7.
rewrite H7.
reflexivity.
apply sig_map.
reflexivity.
move=> H6.
elim (H6 (proj2_sig k)).
elim (excluded_middle_informative (proj1_sig (exist (fun (n : nat) => n < S N) N H4) < N)%nat).
move=> H6.
elim (lt_irrefl N H6).
move=> H6 H7.
apply (proj2 (proj1 (Proposition_5_2 (RCfield K) V N H3 H4 W) H2)).
suff: (In (VT (RCfield K) V) (SpanVS (RCfield K) V (Count N) (fun (m : Count N) => match excluded_middle_informative (proj1_sig (exist (fun (n : nat) => n < S N) (proj1_sig m) (H3 m)) < N)%nat with
  | left H => W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))) H)
  | right _ => Vadd (RCfield K) V (W (exist (fun k : nat => (k < S N)%nat) N H4)) (Vopp (RCfield K) V (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM (RCfield K) V) (fun m0 : Count N => Vmul (RCfield K) V (ConjugateRC K (RCmult K (RCip K V I (W0 m0) (W (exist (fun k : nat => (k < S N)%nat) N H4))) (RCinv K (RCip K V I (W0 m0) (W0 m0))))) (W0 m0))))
end)) (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) ).
elim.
move=> x H8.
rewrite H8.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (fun (t : Count N) => proj1_sig x t <> FO (RCfield K)) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS (RCfield K) V (Count N) (fun (m : Count N) => W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m)))))).
move=> B b H9 H10 H11 H12.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS (RCfield K) V (Count N) (fun (m : Count N) => W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))))).
apply H12.
apply (proj1 (proj2 (SpanSubspaceVS (RCfield K) V (Count N) (fun (m : Count N) => W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m)))))).
elim (excluded_middle_informative (proj1_sig (exist (fun (n : nat) => n < S N) (proj1_sig b) (H3 b)) < N)%nat).
move=> H13.
suff: ((exist (fun (k : nat) => (k < N)%nat) (proj1_sig (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig b) (H3 b))) H13) = b).
move=> H14.
rewrite H14.
elim (proj2 (proj2 H5) b).
move=> y H15.
rewrite H15.
apply (FiniteSetInduction {k : Count N | (proj1_sig k <= proj1_sig b)%nat} (exist (Finite {k : Count N | (proj1_sig k <= proj1_sig b)%nat}) (fun (t : {k : Count N | (proj1_sig k <= proj1_sig b)%nat}) => proj1_sig y t <> FO (RCfield K)) (proj2_sig y))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS (RCfield K) V (Count N) (fun (m : Count N) => W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m)))))).
move=> D d H16 H17 H18 H19.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS (RCfield K) V (Count N) (fun (m : Count N) => W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))))).
apply H19.
apply (proj1 (proj2 (SpanSubspaceVS (RCfield K) V (Count N) (fun (m : Count N) => W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m)))))).
apply (SpanContainSelfVS (RCfield K) V (Count N) (fun (m : Count N) => W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))) (proj1_sig d)).
apply H18.
apply sig_map.
reflexivity.
move=> H13.
elim (H13 (proj2_sig b)).
apply H11.
rewrite - {3} (Vadd_O_r (RCfield K) V (W (exist (fun (k : nat) => (k < S N)%nat) N H4))).
rewrite - (Vadd_opp_l (RCfield K) V (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM (RCfield K) V) (fun (m : Count N) => Vmul (RCfield K) V (ConjugateRC K (RCmult K (RCip K V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) (RCinv K (RCip K V I (W0 m) (W0 m))))) (W0 m)))).
rewrite - (Vadd_assoc (RCfield K) V (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) (Vopp (RCfield K) V (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM (RCfield K) V) (fun (m : Count N) => Vmul (RCfield K) V (ConjugateRC K (RCmult K (RCip K V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) (RCinv K (RCip K V I (W0 m) (W0 m))))) (W0 m)))) (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM (RCfield K) V) (fun (m : Count N) => Vmul (RCfield K) V (ConjugateRC K (RCmult K (RCip K V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) (RCinv K (RCip K V I (W0 m) (W0 m))))) (W0 m)))).
apply (SpanSubspaceVS (RCfield K) V).
apply H7.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun (P : {X : Ensemble (Count N) | Finite (Count N) X}) => In (VT (RCfield K) V) (SpanVS (RCfield K) V (Count N) (fun (m : Count N) => match excluded_middle_informative (proj1_sig (exist (fun (n : nat) => n < S N) (proj1_sig m) (H3 m)) < N)%nat with
  | left H => W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))) H)
  | right _ => Vadd (RCfield K) V (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) (Vopp (RCfield K) V (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM (RCfield K) V) (fun m0 : Count N => Vmul (RCfield K) V (ConjugateRC K (RCmult K (RCip K V I (W0 m0) (W (exist (fun k : nat => (k < S N)%nat) N H4))) (RCinv K (RCip K V I (W0 m0) (W0 m0))))) (W0 m0))))
end)) (MySumF2 (Count N) P (VSPCM (RCfield K) V) (fun (m : Count N) => Vmul (RCfield K) V (ConjugateRC K (RCmult K (RCip K V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) (RCinv K (RCip K V I (W0 m) (W0 m))))) (W0 m))))).
apply conj.
rewrite MySumF2Empty.
apply (SpanSubspaceVS (RCfield K) V (Count N)).
move=> B b H8 H9 H10 H11.
rewrite MySumF2Add.
apply (SpanSubspaceVS (RCfield K) V (Count N)).
apply H11.
apply (SpanSubspaceVS (RCfield K) V (Count N)).
suff: ((fun (m : Count N) => match excluded_middle_informative (proj1_sig (exist (fun (n : nat) => n < S N) (proj1_sig m) (H3 m)) < N)%nat with
  | left H => W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))) H)
  | right _ => Vadd (RCfield K) V (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) (Vopp (RCfield K) V (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM (RCfield K) V) (fun m0 : Count N => Vmul (RCfield K) V (ConjugateRC K (RCmult K (RCip K V I (W0 m0) (W (exist (fun k : nat => (k < S N)%nat) N H4))) (RCinv K (RCip K V I (W0 m0) (W0 m0))))) (W0 m0))))
end) = W0).
move=> H12.
rewrite H12.
apply (SpanContainSelfVS (RCfield K) V (Count N) W0 b).
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (proj1_sig (exist (fun (n : nat) => n < S N) (proj1_sig m) (H3 m)) < N)%nat).
move=> H12.
suff: ((exist (fun (k : nat) => (k < N)%nat) (proj1_sig (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))) H12) = m).
move=> H13.
rewrite H13.
reflexivity.
apply sig_map.
reflexivity.
move=> H12.
elim (H12 (proj2_sig m)).
apply H10.
apply conj.
suff: (forall (t1 t2 : Count (S N)), (proj1_sig t1 < proj1_sig t2)%nat -> RCip K V I match excluded_middle_informative (proj1_sig t1 < N)%nat with
  | left H => W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H)
  | right _ => Vadd (RCfield K) V (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) (Vopp (RCfield K) V (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM (RCfield K) V) (fun m0 : Count N => Vmul (RCfield K) V (ConjugateRC K (RCmult K (RCip K V I (W0 m0) (W (exist (fun k : nat => (k < S N)%nat) N H4))) (RCinv K (RCip K V I (W0 m0) (W0 m0))))) (W0 m0))))
end match excluded_middle_informative (proj1_sig t2 < N)%nat with
  | left H => W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t2) H)
  | right _ => Vadd (RCfield K) V (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) (Vopp (RCfield K) V (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM (RCfield K) V) (fun m0 : Count N => Vmul (RCfield K) V (ConjugateRC K (RCmult K (RCip K V I (W0 m0) (W (exist (fun k : nat => (k < S N)%nat) N H4))) (RCinv K (RCip K V I (W0 m0) (W0 m0))))) (W0 m0))))
end = RCO K).
move=> H6 t1 t2 H7.
elim (le_or_lt (proj1_sig t1) (proj1_sig t2)).
move=> H8.
elim (le_lt_or_eq (proj1_sig t1) (proj1_sig t2) H8).
apply (H6 t1 t2).
move=> H9.
apply False_ind.
apply H7.
apply sig_map.
apply H9.
move=> H8.
rewrite (RCip_sym K V I).
rewrite (H6 t2 t1 H8).
apply (ConjugateRCO K).
move=> t1 t2 H6.
elim (excluded_middle_informative (proj1_sig t1 < N)%nat).
move=> H7.
elim (excluded_middle_informative (proj1_sig t2 < N)%nat).
move=> H8.
apply (proj1 (proj2 H5)).
move=> H9.
apply (lt_irrefl (proj1_sig t1)).
suff: (proj1_sig t1 = proj1_sig (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7)).
move=> H10.
rewrite {2} H10.
rewrite H9.
apply H6.
reflexivity.
move=> H8.
rewrite (RCip_linear_plus_r K V I).
rewrite (RCip_linear_opp_r K V I).
suff: (RCip K V I (W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7)) (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM (RCfield K) V) (fun (m : Count N) => Vmul (RCfield K) V (ConjugateRC K (RCmult K (RCip K V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) (RCinv K (RCip K V I (W0 m) (W0 m))))) (W0 m))) = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (FPCM (RCfield K)) (fun (m : Count N) => RCip K V I (W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7)) (Vmul (RCfield K) V (ConjugateRC K (RCmult K (RCip K V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) (RCinv K (RCip K V I (W0 m) (W0 m))))) (W0 m)))).
move=> H9.
rewrite H9.
rewrite (MySumF2Included (Count N) (FiniteSingleton (Count N) (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7)) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (RCip_linear_mult_r K V I).
rewrite ConjugateRCInvolutive.
rewrite RCmult_assoc.
rewrite RCinv_l.
suff: (RCmult K (RCip K V I (W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7)) (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) (RCI K) = RCip K V I (W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7)) (W (exist (fun (k : nat) => (k < S N)%nat) N H4))).
move=> H10.
rewrite H10.
rewrite (CM_O_r (FPCM (RCfield K))).
apply RCplus_opp_r.
apply (Fmul_I_r (RCfield K)).
move=> H10.
apply (LinearlyIndependentNotContainVOVS (RCfield K) V (Count N) W0 (proj1 H5) (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7)).
apply (proj1 (RCip_refl K V I (W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7))) H10).
move=> u.
elim.
move=> u0 H10 H11.
rewrite (RCip_linear_mult_r K V I).
rewrite (proj1 (proj2 H5) (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7) u0).
apply (Fmul_O_r (RCfield K)).
move=> H12.
apply H10.
rewrite H12.
apply (In_singleton (Count N) u0).
move=> m H10.
apply (Full_intro (Count N) m).
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (RCip_mult_0_r K V I).
move=> B b H9 H10 H11 H12.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (RCip_linear_plus_r K V I).
rewrite H12.
reflexivity.
apply H11.
apply H11.
move=> H7.
apply False_ind.
apply H7.
apply (le_trans (S (proj1_sig t1)) (proj1_sig t2) N H6 (le_S_n (proj1_sig t2) N (proj2_sig t2))).
move=> m.
elim (excluded_middle_informative (proj1_sig m < N)%nat).
move=> H6.
elim (proj2 (proj2 H5) (exist (fun (k : nat) => (k < N)%nat) (proj1_sig m) H6)).
move=> x H7.
rewrite H7.
apply (FiniteSetInduction {k : Count N | (proj1_sig k <= proj1_sig (exist (fun (k0 : nat) => k0 < N) (proj1_sig m) H6))%nat} (exist (Finite {k : Count N | (proj1_sig k <= proj1_sig (exist (fun (k0 : nat) => k0 < N) (proj1_sig m) H6))%nat}) (fun t : {k : Count N | (proj1_sig k <= proj1_sig (exist (fun (k0 : nat) => k0 < N) (proj1_sig m) H6))%nat} => proj1_sig x t <> FO (RCfield K)) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
apply (SpanSubspaceVS (RCfield K) V).
move=> B b H8 H9 H10 H11.
rewrite MySumF2Add.
apply (SpanSubspaceVS (RCfield K) V).
apply H11.
apply (SpanSubspaceVS (RCfield K) V).
suff: (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig b)) (H3 (proj1_sig b)) = proj1_sig (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig b)) (H3 (proj1_sig b))) (proj2_sig b))).
move=> H12.
rewrite H12.
apply (SpanContainSelfVS (RCfield K) V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat} (fun (x0 : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x0)) (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig b)) (H3 (proj1_sig b))) (proj2_sig b))).
reflexivity.
apply H10.
move=> H6.
apply (SpanSubspaceVS (RCfield K) V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))).
suff: (proj1_sig (exist (fun (k : nat) => (k < S N)%nat) N H4) <= proj1_sig m)%nat.
move=> H7.
suff: (exist (fun (k : nat) => (k < S N)%nat) N H4 = proj1_sig (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (k : nat) => (k < S N)%nat) N H4) H7)).
move=> H8.
rewrite H8.
apply (SpanContainSelfVS (RCfield K) V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x)) (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (k : nat) => (k < S N)%nat) N H4) H7)).
reflexivity.
elim (le_or_lt N (proj1_sig m)).
apply.
move=> H7.
elim (H6 H7).
apply (SubspaceMakeVSVoppSub (RCfield K) V (SpanVS (RCfield K) V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))) (SpanSubspaceVS (RCfield K) V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x)))).
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS (RCfield K) V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))))).
move=> B b H7 H8 H9 H10.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS (RCfield K) V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x)))).
apply H10.
apply (proj1 (proj2 (SpanSubspaceVS (RCfield K) V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))))).
elim (proj2 (proj2 H5) b).
move=> x H11.
rewrite H11.
apply (FiniteSetInduction {k : Count N | (proj1_sig k <= proj1_sig b)%nat} (exist (Finite {k : Count N | (proj1_sig k <= proj1_sig b)%nat}) (fun (t : {k : Count N | (proj1_sig k <= proj1_sig b)%nat}) => proj1_sig x t <> FO (RCfield K)) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS (RCfield K) V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))))).
move=> D d H12 H13 H14 H15.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS (RCfield K) V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x)))).
apply H15.
apply (proj1 (proj2 (SpanSubspaceVS (RCfield K) V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))))).
suff: (proj1_sig (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig d)) (H3 (proj1_sig d))) <= proj1_sig m)%nat.
move=> H16.
suff: (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig d)) (H3 (proj1_sig d)) = proj1_sig (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig d)) (H3 (proj1_sig d))) H16)).
move=> H17.
rewrite H17.
apply (SpanContainSelfVS (RCfield K) V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat} (fun (y : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig y)) (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig d)) (H3 (proj1_sig d))) H16)).
reflexivity.
apply (le_trans (proj1_sig (proj1_sig d)) (proj1_sig b) (proj1_sig m) (proj2_sig d)).
apply (le_S_n (proj1_sig b) (proj1_sig m)).
apply (le_trans (S (proj1_sig b)) N (S (proj1_sig m)) (proj2_sig b)).
apply (le_S N (proj1_sig m)).
elim (le_or_lt N (proj1_sig m)).
apply.
move=> H16.
elim (H6 H16).
apply H14.
apply H9.
apply (proj1 (proj1 (Proposition_5_2 (RCfield K) V N H3 H4 W) H2)).
elim (Proposition_5_2_exists (RCfield K) V N).
move=> H4.
elim.
move=> H5 H6.
apply H5.
elim (Proposition_5_2_exists (RCfield K) V N).
move=> H4 H5.
apply H4.
Qed.

Definition GramSchmidtLinearlyIndepententR_sub : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (N : nat) (W : Count N -> VT Rfield V), LinearlyIndependentVS Rfield V (Count N) W -> {Z : Count N -> VT Rfield V | OrthonormalSystemR V I (Count N) Z /\ forall (m : Count N), In (VT Rfield V) (SpanVS Rfield V {k : Count N | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))) (Z m)} := GramSchmidtLinearlyIndepententRC_sub RK.

Definition GramSchmidtLinearlyIndepententC_sub : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (N : nat) (W : Count N -> VT Cfield V), LinearlyIndependentVS Cfield V (Count N) W -> {Z : Count N -> VT Cfield V | OrthonormalSystemC V I (Count N) Z /\ forall (m : Count N), In (VT Cfield V) (SpanVS Cfield V {k : Count N | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))) (Z m)} := GramSchmidtLinearlyIndepententRC_sub CK.

Lemma GramSchmidtLinearlyIndepententRC : forall (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (N : nat) (W : Count N -> VT (RCfield K) V), LinearlyIndependentVS (RCfield K) V (Count N) W -> {Z : Count N -> VT (RCfield K) V | OrthonormalSystemRC K V I (Count N) Z /\ SpanVS (RCfield K) V (Count N) W = SpanVS (RCfield K) V (Count N) Z}.
Proof.
move=> K V I N W H1.
elim (GramSchmidtLinearlyIndepententRC_sub K V I N W H1).
move=> Z H2.
exists Z.
suff: (forall (U : Count N -> VT (RCfield K) V), LinearlyIndependentVS (RCfield K) V (Count N) U -> FiniteDimensionVS (RCfield K) (SubspaceMakeVS (RCfield K) V (SpanVS (RCfield K) V (Count N) U) (SpanSubspaceVS (RCfield K) V (Count N) U))).
move=> H3.
suff: (forall (U : Count N -> VT (RCfield K) V) (H : LinearlyIndependentVS (RCfield K) V (Count N) U), DimensionSubspaceVS (RCfield K) V (SpanVS (RCfield K) V (Count N) U) (SpanSubspaceVS (RCfield K) V (Count N) U) (H3 U H) = N).
move=> H4.
apply conj.
apply (proj1 H2).
suff: (Included (VT (RCfield K) V) (SpanVS (RCfield K) V (Count N) Z) (SpanVS (RCfield K) V (Count N) W)).
move=> H5.
rewrite (proj1 (Proposition_5_9_1_3_subspace (RCfield K) V (SpanVS (RCfield K) V (Count N) Z) (SpanVS (RCfield K) V (Count N) W) (SpanSubspaceVS (RCfield K) V (Count N) Z) (SpanSubspaceVS (RCfield K) V (Count N) W) H5 (H3 W H1) (H3 Z (OrthonormalSystemLinearlyIndependentRC K V I (Count N) Z (proj1 H2))))).
reflexivity.
rewrite (H4 W H1).
apply (H4 Z (OrthonormalSystemLinearlyIndependentRC K V I (Count N) Z (proj1 H2))).
move=> v.
elim.
move=> x H5.
rewrite H5.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (fun (t : Count N) => proj1_sig x t <> FO (RCfield K)) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS (RCfield K) V (Count N) W))).
move=> B b H6 H7 H8 H9.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS (RCfield K) V (Count N) W)).
apply H9.
apply (proj1 (proj2 (SpanSubspaceVS (RCfield K) V (Count N) W))).
elim (proj2 H2 b).
move=> y H10.
rewrite H10.
apply (FiniteSetInduction {k : Count N | (proj1_sig k <= proj1_sig b)%nat} (exist (Finite {k : Count N | (proj1_sig k <= proj1_sig b)%nat}) (fun (t : {k : Count N | (proj1_sig k <= proj1_sig b)%nat}) => proj1_sig y t <> FO (RCfield K)) (proj2_sig y))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS (RCfield K) V (Count N) W))).
move=> D d H11 H12 H13 H14.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS (RCfield K) V (Count N) W)).
apply H14.
apply (proj1 (proj2 (SpanSubspaceVS (RCfield K) V (Count N) W))).
apply (SpanContainSelfVS (RCfield K) V (Count N) W (proj1_sig d)).
apply H13.
apply H8.
move=> U H4.
apply (DimensionVSNature2 (RCfield K) (SubspaceMakeVS (RCfield K) V (SpanVS (RCfield K) V (Count N) U) (SpanSubspaceVS (RCfield K) V (Count N) U)) (H3 U H4) N (fun (m : Count N) => exist (SpanVS (RCfield K) V (Count N) U) (U m) (SpanContainSelfVS (RCfield K) V (Count N) U m)) H4).
move=> U H3.
exists N.
exists (fun (m : Count N) => exist (SpanVS (RCfield K) V (Count N) U) (U m) (SpanContainSelfVS (RCfield K) V (Count N) U m)).
apply H3.
Qed.

Definition GramSchmidtLinearlyIndepententR : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (N : nat) (W : Count N -> VT Rfield V), LinearlyIndependentVS Rfield V (Count N) W -> {Z : Count N -> VT Rfield V | OrthonormalSystemR V I (Count N) Z /\ SpanVS Rfield V (Count N) W = SpanVS Rfield V (Count N) Z} := GramSchmidtLinearlyIndepententRC RK.

Definition GramSchmidtLinearlyIndepententC : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (N : nat) (W : Count N -> VT Cfield V), LinearlyIndependentVS Cfield V (Count N) W -> {Z : Count N -> VT Cfield V | OrthonormalSystemC V I (Count N) Z /\ SpanVS Cfield V (Count N) W = SpanVS Cfield V (Count N) Z} := GramSchmidtLinearlyIndepententRC CK.

Lemma GramSchmidtBasisRC : forall (K : RC) (V : VectorSpace (RCfield K)) (I : RCInner_Product_Space K V) (N : nat) (W : Count N -> VT (RCfield K) V), BasisVS (RCfield K) V (Count N) W -> {Z : Count N -> VT (RCfield K) V | OrthonormalSystemRC K V I (Count N) Z /\ BasisVS (RCfield K) V (Count N) Z /\ forall (m : Count N), In (VT (RCfield K) V) (SpanVS (RCfield K) V {k : Count N | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))) (Z m)}.
Proof.
move=> K V I N W H1.
elim (GramSchmidtLinearlyIndepententRC_sub K V I N W).
move=> Z H2.
exists Z.
apply conj.
apply (proj1 H2).
apply conj.
suff: (FiniteDimensionVS (RCfield K) V).
move=> H3.
apply (Corollary_5_8_2_3 (RCfield K) V N Z H3).
apply conj.
apply (OrthonormalSystemLinearlyIndependentRC K V I (Count N) Z (proj1 H2)).
apply (DimensionVSNature2 (RCfield K) V H3 N W H1).
exists N.
exists W.
apply H1.
apply (proj2 H2).
apply (proj1 (proj1 (BasisLIGeVS (RCfield K) V (Count N) W) H1)).
Qed.

Definition GramSchmidtBasisR : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (N : nat) (W : Count N -> VT Rfield V), BasisVS Rfield V (Count N) W -> {Z : Count N -> VT Rfield V | OrthonormalSystemR V I (Count N) Z /\ BasisVS Rfield V (Count N) Z /\ forall (m : Count N), In (VT Rfield V) (SpanVS Rfield V {k : Count N | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))) (Z m)} := GramSchmidtBasisRC RK.

Definition GramSchmidtBasisC : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (N : nat) (W : Count N -> VT Cfield V), BasisVS Cfield V (Count N) W -> {Z : Count N -> VT Cfield V | OrthonormalSystemC V I (Count N) Z /\ BasisVS Cfield V (Count N) Z /\ forall (m : Count N), In (VT Cfield V) (SpanVS Cfield V {k : Count N | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))) (Z m)} := GramSchmidtBasisRC CK.

Definition AdjointMatrix (M N : nat) (A : Matrix Cfield M N) := (fun (x : {n : nat | (n < N)%nat}) (y : {n : nat | (n < M)%nat}) => Conjugate (A y x)).

Definition AdjointMatrixRC : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M N), Matrix (RCfield K) N M := (fun (K : RC) (M N : nat) (A : Matrix (RCfield K) M N) (x : {n : nat | (n < N)%nat}) (y : {n : nat | (n < M)%nat}) => ConjugateRC K (A y x)).

Lemma AdjointMatrixPlus : forall (M N : nat) (A B : Matrix Cfield M N), AdjointMatrix M N (Mplus Cfield M N A B) = Mplus Cfield N M (AdjointMatrix M N A) (AdjointMatrix M N B).
Proof.
move=> M N A B.
unfold AdjointMatrix.
unfold Mplus.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply (Proposition_4_8_1_1 (A y x) (B y x)).
Qed.

Definition AdjointMatrixRCPlus : forall (K : RC) (M N : nat) (A B : Matrix (RCfield K) M N), AdjointMatrixRC K M N (Mplus (RCfield K) M N A B) = Mplus (RCfield K) N M (AdjointMatrixRC K M N A) (AdjointMatrixRC K M N B) := fun (K : RC) => match K with
  | RK => MTransPlus Rfield
  | CK => AdjointMatrixPlus
end.

Lemma AdjointMatrixMult : forall (M N K : nat) (A : Matrix Cfield M N) (B : Matrix Cfield N K), AdjointMatrix M K (Mmult Cfield M N K A B) = Mmult Cfield K N M (AdjointMatrix N K B) (AdjointMatrix M N A).
Proof.
move=> M N K A B.
unfold AdjointMatrix.
unfold Mmult.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply (FiniteSetInduction {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply ConjugateCO.
move=> C c H1 H2 H3 H4.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite Proposition_4_8_1_1.
rewrite H4.
rewrite (Proposition_4_8_2 (A y c) (B c x)).
rewrite Cmult_comm.
reflexivity.
apply H3.
apply H3.
Qed.

Definition AdjointMatrixRCMult : forall (K : RC) (L M N : nat) (A : Matrix (RCfield K) L M) (B : Matrix (RCfield K) M N), AdjointMatrixRC K L N (Mmult (RCfield K) L M N A B) = Mmult (RCfield K) N M L (AdjointMatrixRC K M N B) (AdjointMatrixRC K L M A) := fun (K : RC) => match K with
  | RK => MTransMult Rfield
  | CK => AdjointMatrixMult
end.

Lemma AdjointMatrixVMmult : forall (M N : nat) (c : C) (A : Matrix Cfield M N), AdjointMatrix M N (VMmult Cfield M N c A) = VMmult Cfield N M (Conjugate c) (AdjointMatrix M N A).
Proof.
move=> M N c A.
unfold AdjointMatrix.
unfold VMmult.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply (Proposition_4_8_2 c (A y x)).
Qed.

Definition AdjointMatrixRCVMmult : forall (K : RC) (M N : nat) (c : RCT K) (A : Matrix (RCfield K) M N), AdjointMatrixRC K M N (VMmult (RCfield K) M N c A) = VMmult (RCfield K) N M (ConjugateRC K c) (AdjointMatrixRC K M N A) := fun (K : RC) => match K with
  | RK => MTransVMult Rfield
  | CK => AdjointMatrixVMmult
end.

Lemma AdjointMatrixInvolutive : forall (M N : nat) (A : Matrix Cfield M N), AdjointMatrix N M (AdjointMatrix M N A) = A.
Proof.
move=> M N A.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply (ConjugateInvolutive (A x y)).
Qed.

Definition AdjointMatrixRCInvolutive : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M N), AdjointMatrixRC K N M (AdjointMatrixRC K M N A) = A := fun (K : RC) => match K with
  | RK => MTransTrans Rfield
  | CK => AdjointMatrixInvolutive
end.

Definition MSymmetric (f : Field) (N : nat) (A : Matrix f N N) := MTranspose f N N A = A.

Definition HermitianMatrix (N : nat) (A : Matrix Cfield N N) := AdjointMatrix N N A = A.

Definition HermitianMatrixRC (K : RC) (N : nat) (A : Matrix (RCfield K) N N) := AdjointMatrixRC K N N A = A.

Definition OrthogonalMatrix (N : nat) (A : Matrix Rfield N N) := Mmult Rfield N N N (MTranspose Rfield N N A) A = MI Rfield N.

Definition UnitaryMatrix (N : nat) (A : Matrix Cfield N N) := Mmult Cfield N N N (AdjointMatrix N N A) A = MI Cfield N.

Definition UnitaryMatrixRC (K : RC) (N : nat) (A : Matrix (RCfield K) N N) := Mmult (RCfield K) N N N (AdjointMatrixRC K N N A) A = MI (RCfield K) N.

Definition MDiag (f : Field) (N : nat) (a : {n : nat | (n < N)%nat} -> FT f) := fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig x) (proj1_sig y) with
  | left _ => a x
  | right _ => FO f
end.

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

Lemma UnitaryMatrixRCChain : forall (K : RC) (N : nat) (A B : Matrix (RCfield K) N N), UnitaryMatrixRC K N A -> UnitaryMatrixRC K N B -> UnitaryMatrixRC K N (Mmult (RCfield K) N N N A B).
Proof.
move=> K N A B H1 H2.
unfold UnitaryMatrixRC.
rewrite (AdjointMatrixRCMult K N N N A B).
rewrite (Mmult_assoc (RCfield K) N N N N (AdjointMatrixRC K N N B) (AdjointMatrixRC K N N A) (Mmult (RCfield K) N N N A B)).
rewrite - (Mmult_assoc (RCfield K) N N N N (AdjointMatrixRC K N N A) A B).
rewrite H1.
rewrite (Mmult_I_l (RCfield K) N N B).
apply H2.
Qed.

Definition OrthogonalMatrixChain : forall (N : nat) (A B : Matrix Rfield N N), OrthogonalMatrix N A -> OrthogonalMatrix N B -> OrthogonalMatrix N (Mmult Rfield N N N A B) := UnitaryMatrixRCChain RK.

Definition UnitaryMatrixChain : forall (N : nat) (A B : Matrix Cfield N N), UnitaryMatrix N A -> UnitaryMatrix N B -> UnitaryMatrix N (Mmult Cfield N N N A B) := UnitaryMatrixRCChain CK.

Definition RCnInner_Product_Space (K : RC) (N : nat) := mkRCInner_Product_Space K (FnVS (RCfield K) N) (RCnInnerProduct K N) (Proposition_4_2_3 K N) (Proposition_4_2_2_1 K N) (Proposition_4_2_1_1 K N) (Proposition_4_2_4_1 K N) (fun (x : RCn K N) => conj (Proposition_4_2_4_2 K N x) (Proposition_4_2_4_3 K N x)).

Definition RnInner_Product_Space (N : nat) := mkRInner_Product_Space (RnVS N) (RnInnerProduct N) (Proposition_4_2_3_R N) (Proposition_4_2_2_1_R N) (Proposition_4_2_1_1_R N) (Proposition_4_2_4_1_R N) (fun (x : Rn N) => conj (Proposition_4_2_4_2_R N x) (Proposition_4_2_4_3_R N x)).

Definition CnInner_Product_Space (N : nat) := mkCInner_Product_Space (CnVS N) (CnInnerProduct N) (Proposition_4_2_3_C N) (Proposition_4_2_2_1_C N) (Proposition_4_2_1_1_C N) (Proposition_4_2_4_1_C N) (fun (x : Cn N) => conj (Proposition_4_2_4_2_C N x) (Proposition_4_2_4_3_C N x)).

Lemma RCnInnerProductMatrix : forall (K : RC) (N : nat) (x y : RCn K N), RCnInnerProduct K N x y = ConjugateRC K (Mmult (RCfield K) 1 N 1 (AdjointMatrixRC K N 1 (MVectorToMatrix (RCfield K) N x)) (MVectorToMatrix (RCfield K) N y) Single Single).
Proof.
move=> K N x y.
unfold RCnInnerProduct.
unfold Mmult.
unfold MVectorToMatrix.
unfold AdjointMatrix.
unfold Count.
apply (FiniteSetInduction (Count N) (exist (Finite {n : nat | (n < N)%nat}) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite ConjugateRCO.
reflexivity.
move=> B b H1 H2 H3 H4.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H4.
simpl.
rewrite Proposition_4_8_1_1_RC.
rewrite Proposition_4_8_2_RC.
rewrite ConjugateRCInvolutive.
reflexivity.
apply H3.
apply H3.
Qed.

Definition RnInnerProductMatrix : forall (N : nat) (x y : Rn N), RnInnerProduct N x y = Mmult Rfield 1 N 1 (MTranspose Rfield N 1 (MVectorToMatrix Rfield N x)) (MVectorToMatrix Rfield N y) Single Single := RCnInnerProductMatrix RK.

Definition CnInnerProductMatrix : forall (N : nat) (x y : Cn N), CnInnerProduct N x y = Conjugate (Mmult Cfield 1 N 1 (AdjointMatrix N 1 (MVectorToMatrix Cfield N x)) (MVectorToMatrix Cfield N y) Single Single) := RCnInnerProductMatrix CK.

Lemma BlockHAdjointMatrix : forall (M1 M2 N : nat) (A1 : Matrix Cfield M1 N) (A2 : Matrix Cfield M2 N), AdjointMatrix (M1 + M2) N (MBlockH Cfield M1 M2 N A1 A2) = MBlockW Cfield N M1 M2 (AdjointMatrix M1 N A1) (AdjointMatrix M2 N A2).
Proof.
move=> M1 M2 N A1 A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold AdjointMatrix.
unfold MBlockH.
unfold MBlockW.
elim (AddConnectInv M1 M2 y).
reflexivity.
reflexivity.
Qed.

Definition BlockHAdjointMatrixRC : forall (K : RC) (M1 M2 N : nat) (A1 : Matrix (RCfield K) M1 N) (A2 : Matrix (RCfield K) M2 N), AdjointMatrixRC K (M1 + M2) N (MBlockH (RCfield K) M1 M2 N A1 A2) = MBlockW (RCfield K) N M1 M2 (AdjointMatrixRC K M1 N A1) (AdjointMatrixRC K M2 N A2) := fun (K : RC) => match K with
  | RK => MBlockHTranspose Rfield
  | CK => BlockHAdjointMatrix
end.

Lemma BlockWAdjointMatrix : forall (M N1 N2 : nat) (A1 : Matrix Cfield M N1) (A2 : Matrix Cfield M N2), AdjointMatrix M (N1 + N2) (MBlockW Cfield M N1 N2 A1 A2) = MBlockH Cfield N1 N2 M (AdjointMatrix M N1 A1) (AdjointMatrix M N2 A2).
Proof.
move=> M N1 N2 A1 A2.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold AdjointMatrix.
unfold MBlockH.
unfold MBlockW.
elim (AddConnectInv N1 N2 x).
reflexivity.
reflexivity.
Qed.

Definition BlockWAdjointMatrixRC : forall (K : RC) (M N1 N2 : nat) (A1 : Matrix (RCfield K) M N1) (A2 : Matrix (RCfield K) M N2), AdjointMatrixRC K M (N1 + N2) (MBlockW (RCfield K) M N1 N2 A1 A2) = MBlockH (RCfield K) N1 N2 M (AdjointMatrixRC K M N1 A1) (AdjointMatrixRC K M N2 A2) := fun (K : RC) => match K with
  | RK => MBlockWTranspose Rfield
  | CK => BlockWAdjointMatrix
end.

Lemma AdjointMatrixO : forall (M N : nat), AdjointMatrix M N (MO Cfield M N) = MO Cfield N M.
Proof.
move=> M N.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply ConjugateCO.
Qed.

Definition AdjointMatrixRCO : forall (K : RC) (M N : nat), AdjointMatrixRC K M N (MO (RCfield K) M N) = MO (RCfield K) N M := fun (K : RC) => match K with
  | RK => MTransO Rfield
  | CK => AdjointMatrixO
end.

Lemma AdjointMatrixI : forall (N : nat), AdjointMatrix N N (MI Cfield N) = MI Cfield N.
Proof.
move=> N.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold AdjointMatrix.
unfold Conjugate.
unfold MI.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig x)).
move=> H1.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H2.
apply functional_extensionality.
move=> n.
elim (CReorCIm n).
move=> H3.
rewrite H3.
apply (CmakeRe (FI Cfield CRe) (- FI Cfield CIm)).
move=> H3.
rewrite H3.
rewrite (CmakeIm (FI Cfield CRe) (- FI Cfield CIm)).
simpl.
unfold CI.
rewrite (CmakeIm 1 0).
apply Ropp_0.
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
apply functional_extensionality.
move=> n.
elim (CReorCIm n).
move=> H3.
rewrite H3.
apply (CmakeRe 0 (- 0)).
move=> H3.
rewrite H3.
rewrite (CmakeIm 0 (- 0)).
apply Ropp_0.
Qed.

Definition AdjointMatrixRCI : forall (K : RC) (N : nat), AdjointMatrixRC K N N (MI (RCfield K) N) = MI (RCfield K) N := fun (K : RC) => match K with
  | RK => MTransI Rfield
  | CK => AdjointMatrixI
end.

Lemma HermitianMatrixTransformableToDiag : forall (N : nat) (A : Matrix Cfield N N), HermitianMatrix N A -> exists (V : Matrix Cfield N N) (D : {n : nat | (n < N)%nat} -> C), UnitaryMatrix N V /\ MDiag Cfield N D = Mmult Cfield N N N (AdjointMatrix N N V) (Mmult Cfield N N N A V).
Proof.
elim.
move=> A H1.
exists (MI Cfield O).
exists (fun (m : {n : nat | (n < 0)%nat}) => CI).
apply conj.
unfold UnitaryMatrix.
apply functional_extensionality.
move=> m.
elim (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) (proj2_sig m)).
apply functional_extensionality.
move=> m.
elim (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) (proj2_sig m)).
move=> N H1 A H2.
suff: (exists (V : Matrix Cfield (S N) (S N)), UnitaryMatrix (S N) V /\ forall (m : {n : nat | (n < S N)%nat}), (proj1_sig m > O)%nat -> Mmult Cfield (S N) (S N) (S N) (AdjointMatrix (S N) (S N) V) (Mmult Cfield (S N) (S N) (S N) A V) m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = CO).
elim.
move=> V H3.
suff: (exists (B : Matrix Cfield N N) (la : C), HermitianMatrix N B /\ Mmult Cfield (S N) (S N) (S N) (AdjointMatrix (S N) (S N) V) (Mmult Cfield (S N) (S N) (S N) A V) = MBlockH Cfield 1 N (S N) (MBlockW Cfield 1 1 N (fun (_ _ : {n : nat | (n < 1)%nat}) => la) (MO Cfield 1 N)) (MBlockW Cfield N 1 N (MO Cfield N 1) B)).
elim.
move=> B.
elim.
move=> la H4.
elim (H1 B (proj1 H4)).
move=> W.
elim.
move=> D H5.
exists (Mmult Cfield (S N) (S N) (S N) V (MBlockH Cfield 1 N (S N) (MBlockW Cfield 1 1 N (fun _ _ : {n : nat | (n < 1)%nat} => CI) (MO Cfield 1 N)) (MBlockW Cfield N 1 N (MO Cfield N 1) W))).
exists (fun (m : {n : nat | (n < 1 + N)%nat}) => match AddConnectInv 1 N m with
  | inl _ => la
  | inr m0 => D m0
end).
apply conj.
apply (UnitaryMatrixChain (S N)).
apply (proj1 H3).
unfold UnitaryMatrix.
rewrite (BlockHAdjointMatrix 1 N (S N)).
rewrite (BlockWAdjointMatrix 1 1 N).
rewrite (BlockWAdjointMatrix N 1 N).
rewrite (MBlockHWMult Cfield (S N) 1 N (S N)).
rewrite (MBlockHMult Cfield 1 N 1 (S N)).
rewrite (MBlockHMult Cfield 1 N N (S N)).
rewrite (MBlockWMult Cfield 1 1 1 N).
rewrite (MBlockWMult Cfield N 1 1 N).
rewrite (MBlockWMult Cfield 1 N 1 N).
rewrite (MBlockWMult Cfield N N 1 N).
rewrite (Mmult_O_r Cfield 1 1 N).
rewrite (Mmult_O_r Cfield N 1 N).
rewrite (Mmult_O_r Cfield 1 N 1).
rewrite (Mmult_O_r Cfield N N 1).
rewrite (AdjointMatrixO N 1).
rewrite (AdjointMatrixO 1 N).
rewrite (Mmult_O_l Cfield 1 N N).
rewrite (Mmult_O_l Cfield N 1 1).
rewrite (proj1 H5).
rewrite (MBlockHPlus Cfield 1 N (S N)).
rewrite (MBlockWPlus Cfield 1 1 N).
rewrite (MBlockWPlus Cfield N 1 N).
rewrite (Mplus_comm Cfield 1 1).
rewrite (Mplus_O_l Cfield 1 1).
rewrite (Mplus_O_l Cfield 1 N).
rewrite (Mplus_O_l Cfield N 1).
rewrite (Mplus_O_l Cfield N N).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H6.
suff: (x = y).
move=> H7.
rewrite H7.
elim (AddConnectInv 1 N y).
move=> k.
unfold Mmult.
suff: (exist (Finite (Count 1)) (Full_set {n : nat | (n < 1)%nat}) (CountFinite 1) = FiniteSingleton {n : nat | (n < 1)%nat} (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1))).
move=> H8.
rewrite H8.
rewrite MySumF2Singleton.
rewrite (Fmul_I_r Cfield).
apply ConjugateCI.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> m H8.
suff: ((exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1)) = m).
move=> H9.
rewrite H9.
apply (In_singleton (Count 1) m).
apply sig_map.
elim (le_lt_or_eq O (proj1_sig m) (le_0_n (proj1_sig m))).
move=> H9.
elim (le_not_lt 1 (proj1_sig m) H9 (proj2_sig m)).
apply.
move=> m H8.
apply (Full_intro (Count 1) m).
move=> m.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H8.
reflexivity.
move=> H8.
apply False_ind.
apply H8.
reflexivity.
apply sig_map.
apply H6.
move=> H6.
elim (le_or_lt 1 (proj1_sig x)).
move=> H7.
suff: (match AddConnectInv 1 N x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N x).
move=> x0.
elim.
move=> x0 H8.
elim (le_or_lt 1 (proj1_sig y)).
move=> H9.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H10.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y0)).
move=> H11.
apply False_ind.
apply H6.
rewrite H8.
rewrite H10.
rewrite H11.
reflexivity.
move=> H11.
reflexivity.
apply (proj2 (AddConnectInvNature 1 N) y H9).
move=> H9.
suff: (match AddConnectInv 1 N y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N y).
move=> y0 H10.
reflexivity.
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 N) y H9).
apply (proj2 (AddConnectInvNature 1 N) x H7).
move=> H7.
suff: (match AddConnectInv 1 N x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N x).
move=> x0 H8.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H9.
reflexivity.
apply (proj2 (AddConnectInvNature 1 N) y).
elim (le_or_lt 1 (proj1_sig y)).
apply.
move=> H9.
apply False_ind.
apply H6.
suff: (forall (n : nat), (n < 1)%nat -> n = O).
move=> H10.
rewrite (H10 (proj1_sig y) H9).
apply (H10 (proj1_sig x) H7).
move=> n H10.
elim (le_lt_or_eq n 0 (le_S_n n 0 H10)).
move=> H11.
elim (le_not_lt O n (le_0_n n) H11).
apply.
move=> x0.
elim.
apply (proj1 (AddConnectInvNature 1 N) x H7).
rewrite (AdjointMatrixMult (S N) (S N) (S N)).
rewrite (Mmult_assoc Cfield (S N) (S N) (S N) (S N)).
rewrite - (Mmult_assoc Cfield (S N) (S N) (S N) (S N) A).
rewrite - (Mmult_assoc Cfield (S N) (S N) (S N) (S N) (AdjointMatrix (S N) (S N) V)).
rewrite (proj2 H4).
rewrite (BlockHAdjointMatrix 1 N (S N)).
rewrite (BlockWAdjointMatrix 1 1 N).
rewrite (BlockWAdjointMatrix N 1 N).
rewrite (MBlockHWWHSame Cfield 1 N 1 N (fun (_ _ : {n : nat | (n < 1)%nat}) => la)).
rewrite (MBlockHWMult Cfield (S N) 1 N (S N)).
rewrite (MBlockHMult Cfield 1 N 1 (S N)).
rewrite (MBlockHMult Cfield 1 N N (S N)).
rewrite (MBlockWMult Cfield 1 1 1 N).
rewrite (MBlockWMult Cfield N 1 1 N).
rewrite (MBlockWMult Cfield 1 N 1 N).
rewrite (MBlockWMult Cfield N N 1 N).
rewrite (Mmult_O_r Cfield 1 1 N).
rewrite (Mmult_O_r Cfield N 1 N).
rewrite (Mmult_O_r Cfield 1 N 1).
rewrite (Mmult_O_r Cfield N N 1).
rewrite (AdjointMatrixO N 1).
rewrite (AdjointMatrixO 1 N).
rewrite (Mmult_O_l Cfield 1 N N).
rewrite (Mmult_O_l Cfield N 1 1).
rewrite (MBlockHPlus Cfield 1 N (S N)).
rewrite (MBlockWPlus Cfield 1 1 N).
rewrite (MBlockWPlus Cfield N 1 N).
rewrite (Mplus_comm Cfield 1 1).
rewrite (Mplus_O_l Cfield 1 1).
rewrite (Mplus_O_l Cfield 1 N).
rewrite (Mplus_O_l Cfield N 1).
rewrite (Mplus_O_l Cfield N N).
rewrite (MBlockHWMult Cfield (S N) 1 N (S N)).
rewrite (MBlockHMult Cfield 1 N 1 (S N)).
rewrite (MBlockHMult Cfield 1 N N (S N)).
rewrite (MBlockWMult Cfield 1 1 1 N).
rewrite (MBlockWMult Cfield N 1 1 N).
rewrite (MBlockWMult Cfield 1 N 1 N).
rewrite (MBlockWMult Cfield N N 1 N).
rewrite (Mmult_O_r Cfield 1 1 N).
rewrite (Mmult_O_r Cfield N 1 N).
rewrite (Mmult_O_r Cfield 1 N 1).
rewrite (Mmult_O_r Cfield N N 1).
rewrite (Mmult_O_l Cfield 1 N N).
rewrite (Mmult_O_l Cfield N 1 1).
rewrite (MBlockHPlus Cfield 1 N (S N)).
rewrite (MBlockWPlus Cfield 1 1 N).
rewrite (MBlockWPlus Cfield N 1 N).
rewrite (Mplus_comm Cfield 1 1).
rewrite (Mplus_O_l Cfield 1 1).
rewrite (Mplus_O_l Cfield 1 N).
rewrite (Mplus_O_l Cfield N 1).
rewrite (Mplus_O_l Cfield N N).
rewrite - (proj2 H5).
unfold MDiag.
unfold MBlockH.
unfold MBlockW.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H6.
suff: (x = y).
move=> H7.
rewrite H7.
elim (AddConnectInv 1 N y).
move=> x0.
unfold Mmult.
suff: (exist (Finite (Count 1)) (Full_set {n : nat | (n < 1)%nat}) (CountFinite 1) = FiniteSingleton {n : nat | (n < 1)%nat} (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1))).
move=> H8.
rewrite H8.
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
suff: (Fmul Cfield la CI = la).
move=> H9.
rewrite H9.
unfold AdjointMatrix.
rewrite ConjugateCI.
suff: (Fmul Cfield CI la = la).
move=> H10.
rewrite H10.
reflexivity.
apply (Fmul_I_l Cfield la).
apply (Fmul_I_r Cfield la).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> m H8.
suff: ((exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1)) = m).
move=> H9.
rewrite H9.
apply (In_singleton (Count 1) m).
apply sig_map.
elim (le_lt_or_eq O (proj1_sig m) (le_0_n (proj1_sig m))).
move=> H9.
elim (le_not_lt 1 (proj1_sig m) H9 (proj2_sig m)).
apply.
move=> m H8.
apply (Full_intro (Count 1) m).
move=> x0.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig x0)).
move=> H8.
reflexivity.
move=> H8.
apply False_ind.
apply H8.
reflexivity.
apply sig_map.
apply H6.
move=> H6.
elim (le_or_lt 1 (proj1_sig x)).
move=> H7.
suff: (match AddConnectInv 1 N x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N x).
move=> x0.
elim.
move=> x0 H8.
elim (le_or_lt 1 (proj1_sig y)).
move=> H9.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H10.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y0)).
move=> H11.
apply False_ind.
apply H6.
rewrite H8.
rewrite H10.
rewrite H11.
reflexivity.
move=> H11.
reflexivity.
apply (proj2 (AddConnectInvNature 1 N) y H9).
move=> H9.
suff: (match AddConnectInv 1 N y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N y).
move=> y0 H10.
reflexivity.
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 N) y H9).
apply (proj2 (AddConnectInvNature 1 N) x H7).
move=> H7.
suff: (match AddConnectInv 1 N x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N x).
move=> x0 H8.
elim (le_or_lt 1 (proj1_sig y)).
move=> H9.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H10.
reflexivity.
apply (proj2 (AddConnectInvNature 1 N) y H9).
move=> H9.
apply False_ind.
apply H6.
suff: (forall (n : nat), (n < 1)%nat -> n = O).
move=> H10.
rewrite (H10 (proj1_sig y) H9).
apply (H10 (proj1_sig x) H7).
move=> n H10.
elim (le_lt_or_eq n 0 (le_S_n n 0 H10)).
move=> H11.
elim (le_not_lt O n (le_0_n n) H11).
apply.
move=> x0.
elim.
apply (proj1 (AddConnectInvNature 1 N) x H7).
exists (fun (x y : {n : nat | (n < N)%nat}) => Mmult Cfield (S N) (S N) (S N) (AdjointMatrix (S N) (S N) V) (Mmult Cfield (S N) (S N) (S N) A V) (AddConnect 1 N (inr x)) (AddConnect 1 N (inr y))).
exists (Mmult Cfield (S N) (S N) (S N) (AdjointMatrix (S N) (S N) V) (Mmult Cfield (S N) (S N) (S N) A V) (AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1)))) (AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1))))).
suff: (HermitianMatrix (S N) (Mmult Cfield (S N) (S N) (S N) (fun (x0 y0 : {n : nat | (n < S N)%nat}) => Conjugate (V y0 x0)) (Mmult Cfield (S N) (S N) (S N) A V))).
move=> H4.
apply conj.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite - {1} H4.
unfold AdjointMatrix.
apply ConjugateInvolutive.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
elim (le_or_lt 1 (proj1_sig x)).
move=> H5.
suff: (match AddConnectInv 1 N x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N x).
move=> x0.
elim.
move=> x0 H6.
elim (le_or_lt 1 (proj1_sig y)).
move=> H7.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H8.
suff: (x = AddConnect 1 N (inr x0)).
move=> H9.
suff: (y = AddConnect 1 N (inr y0)).
move=> H10.
rewrite H9.
rewrite H10.
reflexivity.
apply sig_map.
rewrite H8.
apply (proj2 (AddConnectNature 1 N) y0).
apply sig_map.
rewrite H6.
apply (proj2 (AddConnectNature 1 N) x0).
apply (proj2 (AddConnectInvNature 1 N) y H7).
move=> H7.
suff: (match AddConnectInv 1 N y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N y).
move=> y0 H8.
suff: (y = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H9.
rewrite H9.
apply (proj2 H3 x H5).
elim (le_lt_or_eq (proj1_sig y) O (le_S_n (proj1_sig y) O H7)).
move=> H9.
elim (le_not_lt 0 (proj1_sig y) (le_0_n (proj1_sig y)) H9).
move=> H9.
apply sig_map.
apply H9.
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 N) y H7).
apply (proj2 (AddConnectInvNature 1 N) x H5).
move=> H5.
suff: (match AddConnectInv 1 N x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N x).
move=> x0 H6.
elim (le_or_lt 1 (proj1_sig y)).
move=> H7.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H8.
rewrite - H4.
suff: (x = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H9.
rewrite H9.
simpl.
unfold AdjointMatrix.
rewrite (proj2 H3 y H7).
apply ConjugateCO.
elim (le_lt_or_eq (proj1_sig x) O (le_S_n (proj1_sig x) O H5)).
move=> H9.
elim (le_not_lt 0 (proj1_sig x) (le_0_n (proj1_sig x)) H9).
move=> H9.
apply sig_map.
apply H9.
apply (proj2 (AddConnectInvNature 1 N) y H7).
move=> H7.
suff: (match AddConnectInv 1 N y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N y).
move=> y0 H8.
suff: (x = AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1)))).
move=> H9.
suff: (y = AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1)))).
move=> H10.
rewrite H9.
rewrite H10.
reflexivity.
apply sig_map.
rewrite H8.
rewrite (proj1 (AddConnectNature 1 N) y0).
suff: (y0 = (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1))).
move=> H10.
rewrite H10.
reflexivity.
apply sig_map.
elim (le_lt_or_eq (proj1_sig y0) O (le_S_n (proj1_sig y0) O (proj2_sig y0))).
move=> H10.
elim (le_not_lt O (proj1_sig y0) (le_0_n (proj1_sig y0)) H10).
apply.
apply sig_map.
rewrite H6.
rewrite (proj1 (AddConnectNature 1 N) x0).
suff: (x0 = (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1))).
move=> H9.
rewrite H9.
reflexivity.
apply sig_map.
elim (le_lt_or_eq (proj1_sig x0) O (le_S_n (proj1_sig x0) O (proj2_sig x0))).
move=> H9.
elim (le_not_lt O (proj1_sig x0) (le_0_n (proj1_sig x0)) H9).
apply.
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 N) y H7).
move=> x0.
elim.
apply (proj1 (AddConnectInvNature 1 N) x H5).
unfold HermitianMatrix.
rewrite (AdjointMatrixMult (S N) (S N)).
rewrite (AdjointMatrixMult (S N) (S N)).
rewrite H2.
unfold AdjointMatrix.
suff: ((fun (x y : {n : nat | (n < S N)%nat}) => Conjugate (Conjugate (V x y))) = V).
move=> H4.
rewrite H4.
apply (Mmult_assoc Cfield (S N) (S N) (S N)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply ConjugateInvolutive.
suff: (let Aform := fun (u : {n : nat | (n < S N)%nat} -> C) => CnInnerProduct (S N) u (MVmult Cfield (S N) (S N) A u) CRe in exists (V : Matrix Cfield (S N) (S N)), UnitaryMatrix (S N) V /\ (forall (m : {n : nat | (n < S N)%nat}), (proj1_sig m > 0)%nat -> Mmult Cfield (S N) (S N) (S N) (AdjointMatrix (S N) (S N) V) (Mmult Cfield (S N) (S N) (S N) A V) m (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) = CO)).
apply.
move=> Aform.
suff: (exists (v : {n : nat | (n < S N)%nat} -> C), CnInnerProduct (S N) v v = CI /\ forall (w : {n : nat | (n < S N)%nat} -> C), CnInnerProduct (S N) w w = CI -> Aform w <= Aform v).
elim.
move=> v H3.
suff: (exists (V : Matrix Cfield (S N) (S N)), UnitaryMatrix (S N) V /\ V (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))) = (fun (m : Count (S N)) => Conjugate (v m))).
elim.
move=> V H4.
exists (AdjointMatrix (S N) (S N) V).
apply conj.
unfold UnitaryMatrix.
suff: (AdjointMatrix (S N) (S N) (AdjointMatrix (S N) (S N) V) = V).
move=> H5.
rewrite H5.
suff: (AdjointMatrix (S N) (S N) V = InvMatrix Cfield (S N) V).
move=> H6.
rewrite H6.
apply (InvMatrixMultR Cfield (S N) V).
apply (proj2 (RegularInvLExistRelation Cfield (S N) V)).
exists (AdjointMatrix (S N) (S N) V).
apply (proj1 H4).
apply (InvMatrixMultUniqueLStrong Cfield (S N) V (AdjointMatrix (S N) (S N) V) (proj1 H4)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply (ConjugateInvolutive (V x y)).
suff: (forall (x y : {n : nat | (n < S N)%nat} -> C), CnInnerProduct (S N) x y = Conjugate (Mmult Cfield 1 (S N) 1 (AdjointMatrix (S N) 1 (MVectorToMatrix Cfield (S N) x)) (MVectorToMatrix Cfield (S N) y) (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1)) (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1)))).
move=> H5.
suff: (forall (w : {n : nat | (n < S N)%nat} -> C), Aform w <= Aform v * CnInnerProduct (S N) w w CRe).
move=> H6 m H7.
suff: (AdjointMatrix (S N) (S N) (AdjointMatrix (S N) (S N) V) = V).
move=> H8.
rewrite H8.
suff: (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) CRe = Aform v).
move=> H9.
suff: (forall (r1 r2 : R), (forall (eps : R), Aform v + (1 + 1) * eps * r1 + eps * eps * r2 <= (1 + eps * eps) * Aform v) -> r1 = 0).
move=> H10.
apply functional_extensionality.
move=> n.
elim (CReorCIm n).
move=> H11.
rewrite H11.
apply (H10 (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m (exist (fun (n0 : nat) => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) CRe) (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m m CRe)).
move=> eps.
suff: (Aform v + (1 + 1) * eps * Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m (exist (fun n0 : nat => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) CRe + eps * eps * Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m m CRe) = Aform (MMatrixToVector Cfield (S N) (Mmult Cfield (S N) (S N) 1 (AdjointMatrix (S N) (S N) V) (MVectorToMatrix Cfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
  | left _ => CI
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => Cmake eps 0
    | right _ => CO
  end
end)))).
move=> H12.
rewrite H12.
suff: ((1 + eps * eps) * Aform v = Aform v * CnInnerProduct (S N) (MMatrixToVector Cfield (S N) (Mmult Cfield (S N) (S N) 1 (AdjointMatrix (S N) (S N) V) (MVectorToMatrix Cfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
  | left _ => CI
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => Cmake eps 0
    | right _ => CO
  end
end)))) (MMatrixToVector Cfield (S N) (Mmult Cfield (S N) (S N) 1 (AdjointMatrix (S N) (S N) V) (MVectorToMatrix Cfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
  | left _ => CI
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => Cmake eps 0
    | right _ => CO
  end
end)))) CRe).
move=> H13.
rewrite H13.
apply H6.
rewrite (Rmult_comm (1 + eps * eps) (Aform v)).
apply Rmult_eq_compat_l.
rewrite H5.
rewrite (proj2 (MVectorMatrixRelation Cfield (S N))).
rewrite AdjointMatrixMult.
rewrite H8.
rewrite - (Mmult_assoc Cfield).
rewrite (Mmult_assoc Cfield 1 (S N) (S N) (S N)).
suff: (AdjointMatrix (S N) (S N) V = InvMatrix Cfield (S N) V).
move=> H13.
rewrite H13.
rewrite (InvMatrixMultR Cfield (S N) V).
rewrite Mmult_I_r.
rewrite - H5.
unfold CnInnerProduct.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))))).
rewrite MySumF2Singleton.
simpl.
elim (excluded_middle_informative (O = O)).
move=> H14.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
elim (excluded_middle_informative (proj1_sig m = O)).
move=> H15.
elim (lt_irrefl (proj1_sig m)).
rewrite {1} H15.
apply H7.
move=> H15.
rewrite ConjugateCI.
rewrite (Cmult_1_l CI).
elim (excluded_middle_informative (@eq (Count (S N)) m m)).
move=> H16.
simpl.
unfold Cplus.
unfold Fnadd.
unfold CI.
unfold CO.
unfold RnO.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
simpl.
rewrite Rmult_0_l.
rewrite Rminus_0_r.
rewrite Rplus_0_r.
reflexivity.
elim.
reflexivity.
move=> u.
elim.
move=> u0 H15 H16.
suff: (In (Count (S N)) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H16.
move=> u1 H17 H18 H19.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H20.
elim H17.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H21.
rewrite H21.
apply (In_singleton (Count (S N))).
apply sig_map.
apply H20.
move=> H20.
elim (excluded_middle_informative (u1 = m)).
move=> H21.
elim H19.
rewrite H21.
apply (In_singleton (Count (S N)) m).
move=> H21.
apply (Fmul_O_l Cfield (Conjugate CO)).
apply H15.
move=> u.
elim.
apply Intersection_intro.
move=> H15.
apply (le_not_lt (proj1_sig m) 0).
elim H15.
apply (le_n O).
apply H7.
apply (Full_intro (Count (S N)) m).
move=> H14.
apply False_ind.
apply H14.
reflexivity.
move=> u H14.
apply (Full_intro (Count (S N)) u).
apply (proj2 (RegularInvLExistRelation Cfield (S N) V)).
exists (AdjointMatrix (S N) (S N) V).
apply (proj1 H4).
apply (InvMatrixMultUniqueLStrong Cfield (S N) V (AdjointMatrix (S N) (S N) V) (proj1 H4)).
unfold Aform at 2.
rewrite H5.
rewrite (proj2 (MVectorMatrixRelation Cfield (S N))).
rewrite AdjointMatrixMult.
rewrite H8.
suff: (Mmult Cfield (S N) (S N) 1 (AdjointMatrix (S N) (S N) V) (MVectorToMatrix Cfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = 0%nat) with
  | left _ => CI
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => Cmake eps 0
    | right _ => CO
  end
end)) = MVectorToMatrix Cfield (S N) (MVmult Cfield (S N) (S N) (AdjointMatrix (S N) (S N) V) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = 0%nat) with
  | left _ => CI
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => Cmake eps 0
    | right _ => CO
  end
end))).
move=> H12.
rewrite H12.
unfold MVmult.
rewrite (proj2 (MVectorMatrixRelation Cfield (S N))).
rewrite (proj2 (MVectorMatrixRelation Cfield (S N))).
rewrite (proj2 (MVectorMatrixRelation Cfield (S N))).
rewrite (Mmult_assoc Cfield 1 (S N) (S N) 1).
rewrite - (Mmult_assoc Cfield (S N) (S N) (S N) 1 A).
rewrite - (Mmult_assoc Cfield (S N) (S N) (S N) 1 V).
unfold Mmult at 5.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))))).
rewrite MySumF2Singleton.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
unfold MVectorToMatrix at 1.
unfold AdjointMatrix at 3.
simpl.
elim (excluded_middle_informative (O = O)).
move=> H13.
unfold MVectorToMatrix at 2.
unfold AdjointMatrix at 4.
elim (excluded_middle_informative (proj1_sig m = O)).
move=> H14.
elim (lt_irrefl (proj1_sig m)).
rewrite {1} H14.
apply H7.
move=> H14.
elim (excluded_middle_informative (@eq (Count (S N)) m m)).
move=> H15.
unfold Mmult at 5.
unfold Mmult at 7.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))))).
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))) (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m)).
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m) (FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N))) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))))))).
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite MySumF2O.
unfold MVectorToMatrix.
simpl.
elim (excluded_middle_informative (O = O)).
move=> H16.
elim (excluded_middle_informative (proj1_sig m = O)).
move=> H17.
elim (H14 H17).
move=> H17.
elim (excluded_middle_informative (@eq (Count (S N)) m m)).
move=> H18.
rewrite ConjugateCI.
rewrite Cmult_1_l.
rewrite Cmult_comm.
rewrite Cmult_1_l.
rewrite (Cmult_comm (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m (exist (fun (n0 : nat) => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))))).
rewrite Cmult_1_l.
unfold Cplus.
unfold Fnadd.
unfold Conjugate.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite CmakeIm.
simpl.
rewrite Rmult_0_r.
rewrite Rplus_0_r.
rewrite Rminus_0_r.
rewrite Rmult_0_r.
rewrite Rplus_0_r.
rewrite Rminus_0_r.
rewrite Rmult_0_r.
rewrite Ropp_0.
rewrite Rmult_0_l.
rewrite Rminus_0_r.
rewrite (Rmult_assoc (1 + 1)).
rewrite (Rmult_plus_distr_r 1 1).
rewrite Rmult_1_l.
rewrite (Rmult_plus_distr_l eps).
rewrite H9.
rewrite (Rmult_comm (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) (exist (fun (n0 : nat) => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) m CRe) eps).
rewrite (Rmult_comm (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m m CRe) eps).
unfold CO.
unfold RnO.
rewrite Rplus_0_r.
rewrite - Rmult_assoc.
rewrite - Rplus_assoc.
rewrite - Rplus_assoc.
suff: (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) (exist (fun n0 : nat => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) m CRe = Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m (exist (fun n0 : nat => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) CRe).
move=> H19.
rewrite H19.
reflexivity.
suff: (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) = AdjointMatrix (S N) (S N) (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)))).
move=> H19.
rewrite {1} H19.
unfold AdjointMatrix.
unfold Conjugate.
apply CmakeRe.
rewrite AdjointMatrixMult.
rewrite AdjointMatrixMult.
rewrite H8.
rewrite H2.
rewrite Mmult_assoc.
reflexivity.
move=> H18.
apply False_ind.
apply H18.
reflexivity.
move=> H16.
apply False_ind.
apply H16.
reflexivity.
move=> u.
elim.
move=> u0 H16 H17.
suff: (In (Count (S N)) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H17.
move=> u1 H18 H19 H20.
unfold MVectorToMatrix.
unfold AdjointMatrix.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H21.
elim H18.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H22.
rewrite H22.
apply (In_singleton (Count (S N))).
apply sig_map.
apply H21.
move=> H21.
elim (excluded_middle_informative (u1 = m)).
move=> H22.
rewrite H22.
elim H20.
rewrite H22.
apply (In_singleton (Count (S N)) m).
move=> H22.
apply (Fmul_O_r Cfield).
apply H16.
move=> u.
elim.
move=> u0 H16 H17.
suff: (In (Count (S N)) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H17.
move=> u1 H18 H19 H20.
unfold MVectorToMatrix.
unfold AdjointMatrix.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H21.
elim H18.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H22.
rewrite H22.
apply (In_singleton (Count (S N))).
apply sig_map.
apply H21.
move=> H21.
elim (excluded_middle_informative (u1 = m)).
move=> H22.
rewrite H22.
elim H20.
rewrite H22.
apply (In_singleton (Count (S N)) m).
move=> H22.
apply (Fmul_O_r Cfield).
apply H16.
move=> u.
elim.
apply Intersection_intro.
move=> H16.
elim (le_not_lt (proj1_sig m) O).
elim H16.
apply (le_n O).
apply H7.
apply (Full_intro (Count (S N)) m).
move=> u.
elim.
apply Intersection_intro.
move=> H16.
elim (le_not_lt (proj1_sig m) O).
elim H16.
apply (le_n O).
apply H7.
apply (Full_intro (Count (S N)) m).
move=> u H16.
apply (Full_intro (Count (S N)) u).
move=> u H16.
apply (Full_intro (Count (S N)) u).
move=> H15.
apply False_ind.
apply H15.
reflexivity.
move=> H13.
apply False_ind.
apply H13.
reflexivity.
move=> u.
elim.
move=> u0 H13 H14.
suff: (In (Count (S N)) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H14.
move=> u1 H15 H16 H17.
unfold MVectorToMatrix.
unfold AdjointMatrix.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H18.
elim H15.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H19.
rewrite H19.
apply (In_singleton (Count (S N))).
apply sig_map.
apply H18.
move=> H18.
elim (excluded_middle_informative (u1 = m)).
move=> H19.
rewrite H19.
elim H17.
rewrite H19.
apply (In_singleton (Count (S N)) m).
move=> H19.
rewrite ConjugateCO.
apply (Fmul_O_l Cfield).
apply H13.
move=> u.
elim.
apply Intersection_intro.
move=> H13.
elim (le_not_lt (proj1_sig m) O).
elim H13.
apply (le_n O).
apply H7.
apply (Full_intro (Count (S N)) m).
move=> u H13.
apply (Full_intro (Count (S N)) u).
unfold MVmult.
rewrite (proj2 (MVectorMatrixRelation Cfield (S N))).
reflexivity.
move=> H11.
rewrite H11.
apply (H10 (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m (exist (fun (n0 : nat) => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) CIm) (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m m CRe)).
move=> eps.
suff: (Aform v + (1 + 1) * eps * Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m (exist (fun n0 : nat => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) CIm + eps * eps * Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m m CRe) = Aform (MMatrixToVector Cfield (S N) (Mmult Cfield (S N) (S N) 1 (AdjointMatrix (S N) (S N) V) (MVectorToMatrix Cfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
  | left _ => CI
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => Cmake 0 eps
    | right _ => CO
  end
end)))).
move=> H12.
rewrite H12.
suff: ((1 + eps * eps) * Aform v = Aform v * CnInnerProduct (S N) (MMatrixToVector Cfield (S N) (Mmult Cfield (S N) (S N) 1 (AdjointMatrix (S N) (S N) V) (MVectorToMatrix Cfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
  | left _ => CI
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => Cmake 0 eps
    | right _ => CO
  end
end)))) (MMatrixToVector Cfield (S N) (Mmult Cfield (S N) (S N) 1 (AdjointMatrix (S N) (S N) V) (MVectorToMatrix Cfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
  | left _ => CI
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => Cmake 0 eps
    | right _ => CO
  end
end)))) CRe).
move=> H13.
rewrite H13.
apply H6.
rewrite (Rmult_comm (1 + eps * eps) (Aform v)).
apply Rmult_eq_compat_l.
rewrite H5.
rewrite (proj2 (MVectorMatrixRelation Cfield (S N))).
rewrite AdjointMatrixMult.
rewrite H8.
rewrite - (Mmult_assoc Cfield).
rewrite (Mmult_assoc Cfield 1 (S N) (S N) (S N)).
suff: (AdjointMatrix (S N) (S N) V = InvMatrix Cfield (S N) V).
move=> H13.
rewrite H13.
rewrite (InvMatrixMultR Cfield (S N) V).
rewrite Mmult_I_r.
rewrite - H5.
unfold CnInnerProduct.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))))).
rewrite MySumF2Singleton.
simpl.
elim (excluded_middle_informative (O = O)).
move=> H14.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
elim (excluded_middle_informative (proj1_sig m = O)).
move=> H15.
elim (lt_irrefl (proj1_sig m)).
rewrite {1} H15.
apply H7.
move=> H15.
rewrite ConjugateCI.
rewrite (Cmult_1_l CI).
elim (excluded_middle_informative (@eq (Count (S N)) m m)).
move=> H16.
simpl.
unfold Cplus.
unfold Fnadd.
unfold CI.
unfold CO.
unfold RnO.
simpl.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite Rmult_0_l.
rewrite Rplus_0_r.
unfold Rminus.
rewrite Rplus_0_l.
rewrite (Ropp_mult_distr_r eps (- eps)).
rewrite (Ropp_involutive eps).
reflexivity.
elim.
reflexivity.
move=> u.
elim.
move=> u0 H15 H16.
suff: (In (Count (S N)) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H16.
move=> u1 H17 H18 H19.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H20.
elim H17.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H21.
rewrite H21.
apply (In_singleton (Count (S N))).
apply sig_map.
apply H20.
move=> H20.
elim (excluded_middle_informative (u1 = m)).
move=> H21.
elim H19.
rewrite H21.
apply (In_singleton (Count (S N)) m).
move=> H21.
apply (Fmul_O_l Cfield (Conjugate CO)).
apply H15.
move=> u.
elim.
apply Intersection_intro.
move=> H15.
apply (le_not_lt (proj1_sig m) 0).
elim H15.
apply (le_n O).
apply H7.
apply (Full_intro (Count (S N)) m).
move=> H14.
apply False_ind.
apply H14.
reflexivity.
move=> u H14.
apply (Full_intro (Count (S N)) u).
apply (proj2 (RegularInvLExistRelation Cfield (S N) V)).
exists (AdjointMatrix (S N) (S N) V).
apply (proj1 H4).
apply (InvMatrixMultUniqueLStrong Cfield (S N) V (AdjointMatrix (S N) (S N) V) (proj1 H4)).
unfold Aform at 2.
rewrite H5.
rewrite (proj2 (MVectorMatrixRelation Cfield (S N))).
rewrite AdjointMatrixMult.
rewrite H8.
suff: (Mmult Cfield (S N) (S N) 1 (AdjointMatrix (S N) (S N) V) (MVectorToMatrix Cfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = 0%nat) with
  | left _ => CI
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => Cmake 0 eps
    | right _ => CO
  end
end)) = MVectorToMatrix Cfield (S N) (MVmult Cfield (S N) (S N) (AdjointMatrix (S N) (S N) V) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = 0%nat) with
  | left _ => CI
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => Cmake 0 eps
    | right _ => CO
  end
end))).
move=> H12.
rewrite H12.
unfold MVmult.
rewrite (proj2 (MVectorMatrixRelation Cfield (S N))).
rewrite (proj2 (MVectorMatrixRelation Cfield (S N))).
rewrite (proj2 (MVectorMatrixRelation Cfield (S N))).
rewrite (Mmult_assoc Cfield 1 (S N) (S N) 1).
rewrite - (Mmult_assoc Cfield (S N) (S N) (S N) 1 A).
rewrite - (Mmult_assoc Cfield (S N) (S N) (S N) 1 V).
unfold Mmult at 5.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))))).
rewrite MySumF2Singleton.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
unfold MVectorToMatrix at 1.
unfold AdjointMatrix at 3.
simpl.
elim (excluded_middle_informative (O = O)).
move=> H13.
unfold MVectorToMatrix at 2.
unfold AdjointMatrix at 4.
elim (excluded_middle_informative (proj1_sig m = O)).
move=> H14.
elim (lt_irrefl (proj1_sig m)).
rewrite {1} H14.
apply H7.
move=> H14.
elim (excluded_middle_informative (@eq (Count (S N)) m m)).
move=> H15.
unfold Mmult at 5.
unfold Mmult at 7.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))))).
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))) (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m)).
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m) (FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N))) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))))))).
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite MySumF2O.
unfold MVectorToMatrix.
simpl.
elim (excluded_middle_informative (O = O)).
move=> H16.
elim (excluded_middle_informative (proj1_sig m = O)).
move=> H17.
elim (H14 H17).
move=> H17.
elim (excluded_middle_informative (@eq (Count (S N)) m m)).
move=> H18.
rewrite ConjugateCI.
rewrite Cmult_1_l.
rewrite Cmult_comm.
rewrite Cmult_1_l.
rewrite (Cmult_comm (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m (exist (fun (n0 : nat) => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))))).
rewrite Cmult_1_l.
unfold Cplus.
unfold Fnadd.
simpl.
unfold Cmult.
unfold Conjugate.
rewrite Rplus_0_r.
rewrite Rplus_0_r.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite Rmult_0_r.
rewrite Rplus_0_r.
rewrite Rmult_0_l.
unfold Rminus.
rewrite Rplus_0_l.
rewrite Rplus_0_l.
rewrite Rmult_0_r.
rewrite Rplus_0_r.
rewrite Rplus_0_r.
rewrite (Ropp_mult_distr_l (- eps)).
rewrite Ropp_involutive.
rewrite Ropp_mult_distr_l.
rewrite (Rmult_assoc (1 + 1)).
rewrite (Rmult_plus_distr_r 1 1).
rewrite Rmult_1_l.
rewrite (Rmult_plus_distr_l eps).
rewrite H9.
rewrite (Rmult_comm (- Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) (exist (fun (n0 : nat) => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) m CIm) eps).
rewrite (Rmult_comm (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m m CRe) eps).
rewrite - Rmult_assoc.
rewrite - Rplus_assoc.
rewrite - Rplus_assoc.
suff: (- Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) (exist (fun n0 : nat => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) m CIm = Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m (exist (fun n0 : nat => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) CIm).
move=> H19.
rewrite H19.
reflexivity.
suff: (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) = AdjointMatrix (S N) (S N) (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)))).
move=> H19.
rewrite {2} H19.
unfold AdjointMatrix.
unfold Conjugate.
rewrite CmakeIm.
reflexivity.
rewrite AdjointMatrixMult.
rewrite AdjointMatrixMult.
rewrite H8.
rewrite H2.
rewrite Mmult_assoc.
reflexivity.
move=> H18.
apply False_ind.
apply H18.
reflexivity.
move=> H16.
apply False_ind.
apply H16.
reflexivity.
move=> u.
elim.
move=> u0 H16 H17.
suff: (In (Count (S N)) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H17.
move=> u1 H18 H19 H20.
unfold MVectorToMatrix.
unfold AdjointMatrix.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H21.
elim H18.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H22.
rewrite H22.
apply (In_singleton (Count (S N))).
apply sig_map.
apply H21.
move=> H21.
elim (excluded_middle_informative (u1 = m)).
move=> H22.
rewrite H22.
elim H20.
rewrite H22.
apply (In_singleton (Count (S N)) m).
move=> H22.
apply (Fmul_O_r Cfield).
apply H16.
move=> u.
elim.
move=> u0 H16 H17.
suff: (In (Count (S N)) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H17.
move=> u1 H18 H19 H20.
unfold MVectorToMatrix.
unfold AdjointMatrix.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H21.
elim H18.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H22.
rewrite H22.
apply (In_singleton (Count (S N))).
apply sig_map.
apply H21.
move=> H21.
elim (excluded_middle_informative (u1 = m)).
move=> H22.
rewrite H22.
elim H20.
rewrite H22.
apply (In_singleton (Count (S N)) m).
move=> H22.
apply (Fmul_O_r Cfield).
apply H16.
move=> u.
elim.
apply Intersection_intro.
move=> H16.
elim (le_not_lt (proj1_sig m) O).
elim H16.
apply (le_n O).
apply H7.
apply (Full_intro (Count (S N)) m).
move=> u.
elim.
apply Intersection_intro.
move=> H16.
elim (le_not_lt (proj1_sig m) O).
elim H16.
apply (le_n O).
apply H7.
apply (Full_intro (Count (S N)) m).
move=> u H16.
apply (Full_intro (Count (S N)) u).
move=> u H16.
apply (Full_intro (Count (S N)) u).
move=> H15.
apply False_ind.
apply H15.
reflexivity.
move=> H13.
apply False_ind.
apply H13.
reflexivity.
move=> u.
elim.
move=> u0 H13 H14.
suff: (In (Count (S N)) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H14.
move=> u1 H15 H16 H17.
unfold MVectorToMatrix.
unfold AdjointMatrix.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H18.
elim H15.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H19.
rewrite H19.
apply (In_singleton (Count (S N))).
apply sig_map.
apply H18.
move=> H18.
elim (excluded_middle_informative (u1 = m)).
move=> H19.
rewrite H19.
elim H17.
rewrite H19.
apply (In_singleton (Count (S N)) m).
move=> H19.
rewrite ConjugateCO.
apply (Fmul_O_l Cfield).
apply H13.
move=> u.
elim.
apply Intersection_intro.
move=> H13.
elim (le_not_lt (proj1_sig m) O).
elim H13.
apply (le_n O).
apply H7.
apply (Full_intro (Count (S N)) m).
move=> u H13.
apply (Full_intro (Count (S N)) u).
unfold MVmult.
rewrite (proj2 (MVectorMatrixRelation Cfield (S N))).
reflexivity.
move=> r1 r2 H10.
suff: (forall (eps : R), eps * ((1 + 1) * r1 + eps * (r2 - Aform v)) <= 0).
move=> H11.
elim (Rmult_integral (1 + 1) r1).
move=> H12.
apply False_ind.
apply (Rle_not_lt 0 (1 + 1)).
rewrite H12.
right.
reflexivity.
apply (Rlt_trans 0 1 (1 + 1) Rlt_0_1 (Rlt_plus_1 1)).
apply.
elim (Rle_or_lt ((1 + 1) * r1) 0).
elim.
move=> H12.
suff: (r1 < 0).
move=> H13.
apply False_ind.
elim (Rle_or_lt 0 (r2 - Aform v)).
move=> H14.
apply (Rle_not_lt 0 (- (1) * ((1 + 1) * r1 + - (1) * (r2 - Aform v))) (H11 (- (1)))).
rewrite - Rmult_opp_opp.
rewrite Ropp_involutive.
rewrite Rmult_1_l.
apply Ropp_gt_lt_0_contravar.
rewrite - (Rplus_0_r 0).
apply Rplus_lt_le_compat.
apply H12.
rewrite - Ropp_mult_distr_l.
apply Rge_le.
apply Ropp_0_le_ge_contravar.
rewrite Rmult_1_l.
apply H14.
move=> H14.
apply (Rle_not_lt 0 ((- (r1 / (r2 - Aform v))) * ((1 + 1) * r1 + (- (r1 / (r2 - Aform v))) * (r2 - Aform v))) (H11 (- (r1 / (r2 - Aform v))))).
rewrite - Rmult_opp_opp.
rewrite Ropp_involutive.
apply Rmult_lt_0_compat.
unfold Rdiv.
rewrite - Rmult_opp_opp.
apply Rmult_lt_0_compat.
apply (Ropp_gt_lt_0_contravar r1 H13).
apply Ropp_gt_lt_0_contravar.
apply Rinv_lt_0_compat.
apply H14.
rewrite - Ropp_mult_distr_l.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_r.
rewrite Rmult_1_l.
rewrite Rplus_assoc.
rewrite (Rplus_opp_r r1).
rewrite Rplus_0_r.
apply (Ropp_gt_lt_0_contravar r1 H13).
apply (Rlt_not_eq (r2 - Aform v) 0 H14).
apply (Rmult_lt_reg_l (1 + 1)).
apply (Rlt_trans 0 1 (1 + 1) Rlt_0_1 (Rlt_plus_1 1)).
rewrite (Rmult_0_r (1 + 1)).
apply H12.
apply.
move=> H12.
apply False_ind.
suff: (r1 > 0).
move=> H13.
elim (Rle_or_lt 0 (r2 - Aform v)).
move=> H14.
apply (Rle_not_lt 0 (1 * ((1 + 1) * r1 + 1 * (r2 - Aform v))) (H11 1)).
rewrite Rmult_1_l.
rewrite - (Rplus_0_r 0).
apply Rplus_lt_le_compat.
apply H12.
rewrite Rmult_1_l.
apply H14.
move=> H14.
apply (Rle_not_lt 0 ((- (r1 / (r2 - Aform v))) * ((1 + 1) * r1 + (- (r1 / (r2 - Aform v))) * (r2 - Aform v))) (H11 (- (r1 / (r2 - Aform v))))).
apply Rmult_lt_0_compat.
rewrite Ropp_mult_distr_r.
apply Rmult_lt_0_compat.
apply H13.
apply Ropp_gt_lt_0_contravar.
apply Rinv_lt_0_compat.
apply H14.
rewrite - Ropp_mult_distr_l.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_r.
rewrite Rmult_1_l.
rewrite Rplus_assoc.
rewrite (Rplus_opp_r r1).
rewrite Rplus_0_r.
apply H13.
apply (Rlt_not_eq (r2 - Aform v) 0 H14).
apply (Rmult_lt_reg_l (1 + 1)).
apply (Rlt_trans 0 1 (1 + 1) Rlt_0_1 (Rlt_plus_1 1)).
rewrite (Rmult_0_r (1 + 1)).
apply H12.
move=> eps.
rewrite (Rmult_plus_distr_l eps).
rewrite - (Rmult_assoc eps eps).
rewrite (Rmult_plus_distr_l (eps * eps)).
rewrite - Rplus_assoc.
apply (Rplus_le_reg_r ((1 + eps * eps) * Aform v)).
rewrite Rplus_0_l.
rewrite {1} (Rmult_plus_distr_r 1 (eps* eps)).
rewrite Rmult_1_l.
rewrite (Rplus_comm (Aform v)).
rewrite - Rplus_assoc.
rewrite (Rplus_assoc (eps * ((1 + 1) * r1) + eps * eps * r2)).
rewrite - (Rmult_plus_distr_l (eps * eps)).
rewrite Rplus_opp_l.
rewrite Rmult_0_r.
rewrite Rplus_0_r.
rewrite Rplus_comm.
rewrite - Rplus_assoc.
rewrite - Rmult_assoc.
rewrite (Rmult_comm eps (1 + 1)).
apply (H10 eps).
unfold Aform.
suff: (Mmult Cfield (S N) (S N) (S N) V (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) = Conjugate (CnInnerProduct (S N) v (MVmult Cfield (S N) (S N) A v))).
move=> H9.
rewrite H9.
unfold Conjugate.
apply CmakeRe.
rewrite (H5 v (MVmult Cfield (S N) (S N) A v)).
unfold Mmult at 1.
unfold Mmult at 2.
rewrite ConjugateInvolutive.
apply MySumF2Same.
move=> u0 H9.
unfold MVmult.
unfold MVectorToMatrix.
unfold MMatrixToVector.
unfold AdjointMatrix.
unfold Mmult.
rewrite (proj2 H4).
apply (Fmul_eq_compat_l Cfield).
apply (MySumF2Same {n : nat | (n < S N)%nat} (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N))) (FPCM Cfield) (fun (n : Count (S N)) => Fmul Cfield (A u0 n) (Conjugate (Conjugate (v n)))) (fun (n : Count (S N)) => Fmul Cfield (A u0 n) (v n))).
move=> u1 H10.
rewrite ConjugateInvolutive.
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply ConjugateInvolutive.
move=> w.
elim (classic (forall (m : Count (S N)), w m = CO)).
move=> H6.
suff: (Aform w = 0).
move=> H7.
rewrite H7.
suff: (CnInnerProduct (S N) w w CRe = 0).
move=> H8.
rewrite H8.
rewrite Rmult_0_r.
right.
reflexivity.
unfold CnInnerProduct.
rewrite MySumF2O.
reflexivity.
move=> u H8.
rewrite (H6 u).
apply (Fmul_O_l Cfield (Conjugate CO)).
unfold Aform.
unfold CnInnerProduct.
rewrite MySumF2O.
reflexivity.
move=> u H7.
rewrite (H6 u).
apply (Fmul_O_l Cfield).
move=> H6.
suff: (CnInnerProduct (S N) w w CRe <> 0).
move=> H7.
apply (Rmult_le_reg_r (/ CnInnerProduct (S N) w w CRe)).
apply Rinv_0_lt_compat.
elim (Cip_pos_re (FnVS Cfield (S N)) (CnInner_Product_Space (S N)) w).
apply.
move=> H8.
elim (H7 H8).
rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite (Rmult_1_r (Aform v)).
suff: (/ CnInnerProduct (S N) w w CRe >= 0).
move=> H8.
suff: (Aform w * / CnInnerProduct (S N) w w CRe = Aform (Vmul Cfield (FnVS Cfield (S N)) (Cmake (MySqrt (exist (fun (r : R) => r >= 0) (/ CnInnerProduct (S N) w w CRe) H8)) 0) w)).
move=> H9.
rewrite H9.
apply (proj2 H3).
suff: (CnInnerProduct (S N) = Cip (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
move=> H10.
rewrite {1} H10.
rewrite (Cip_linear_mult_l (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
rewrite (Cip_linear_mult_r (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
rewrite - Cmult_assoc.
unfold Cmult at 2.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite Rmult_0_l.
rewrite Rminus_0_r.
rewrite Ropp_0.
rewrite Rmult_0_l.
rewrite Rmult_0_r.
rewrite - (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (/ CnInnerProduct (S N) w w CRe) H8))).
simpl.
rewrite Rplus_0_r.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite Rinv_l.
rewrite Rmult_0_l.
rewrite Rminus_0_r.
suff: (CnInnerProduct (S N) w w CIm = 0).
move=> H11.
rewrite H11.
rewrite Rmult_0_l.
rewrite Rmult_0_r.
rewrite Rplus_0_r.
reflexivity.
apply (Cip_pos_im (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
apply H7.
reflexivity.
unfold Aform.
suff: (CnInnerProduct (S N) = Cip (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
move=> H9.
rewrite {3} H9.
rewrite (Cip_linear_mult_l (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
suff: (MVmult Cfield (S N) (S N) A (Vmul Cfield (FnVS Cfield (S N)) (Cmake (MySqrt (exist (fun (r : R) => r >= 0) (/ CnInnerProduct (S N) w w CRe) H8)) 0) w) = Vmul Cfield (FnVS Cfield (S N)) (Cmake (MySqrt (exist (fun r : R => r >= 0) (/ CnInnerProduct (S N) w w CRe) H8)) 0) (MVmult Cfield (S N) (S N) A w)).
move=> H10.
rewrite H10.
rewrite (Cip_linear_mult_r (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
rewrite - Cmult_assoc.
unfold Cmult at 2.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite Rmult_0_l.
rewrite Rminus_0_r.
rewrite Ropp_0.
rewrite Rmult_0_l.
rewrite Rmult_0_r.
rewrite - (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (/ CnInnerProduct (S N) w w CRe) H8))).
rewrite Rplus_0_r.
simpl.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite Rmult_0_l.
rewrite Rminus_0_r.
apply Rmult_comm.
unfold MVmult.
unfold MMatrixToVector.
unfold MVectorToMatrix.
apply functional_extensionality.
move=> x.
unfold Mmult.
unfold Vmul.
simpl.
apply (FiniteSetInduction {n : nat | (n < S N)%nat} (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
suff: (CMe (FPCM Cfield) = FO Cfield).
move=> H10.
rewrite {1} H10.
rewrite - (Fmul_O_r Cfield (Cmake (MySqrt (exist (fun (r : R) => r >= 0) (/ CnInnerProduct (S N) w w CRe) H8)) 0)).
reflexivity.
reflexivity.
move=> B b H10 H11 H12 H13.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H13.
rewrite - Cmult_assoc.
rewrite (Cmult_comm (A x b)).
rewrite Cmult_assoc.
rewrite Cmult_plus_distr_l.
reflexivity.
apply H12.
apply H12.
reflexivity.
left.
apply Rinv_0_lt_compat.
elim (Cip_pos_re (FnVS Cfield (S N)) (CnInner_Product_Space (S N)) w).
apply.
move=> H8.
elim (H7 H8).
apply H7.
move=> H7.
apply H6.
move=> m.
rewrite (proj1 (Cip_refl (FnVS Cfield (S N)) (CnInner_Product_Space (S N)) w)).
reflexivity.
apply functional_extensionality.
move=> n.
elim (CReorCIm n).
move=> H8.
rewrite H8.
apply H7.
move=> H8.
rewrite H8.
apply (Cip_pos_im (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
move=> x y.
unfold CnInnerProduct.
unfold MVectorToMatrix.
unfold AdjointMatrix.
unfold Mmult.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S N)%nat} (exist (Finite {n : nat | (n < S N)%nat}) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite ConjugateCO.
reflexivity.
move=> B b H5 H6 H7 H8.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H8.
rewrite Proposition_4_8_1_1.
rewrite Proposition_4_8_2.
rewrite ConjugateInvolutive.
reflexivity.
apply H7.
apply H7.
suff: (SubspaceVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)).
move=> H4.
suff: (FiniteDimensionVS Cfield (SubspaceMakeVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4)).
move=> H5.
suff: (exists (B : Count N -> Cn (S N)), BasisSubspaceVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 (Count N) B).
elim.
move=> B H6.
elim (GramSchmidtLinearlyIndepententC (FnVS Cfield (S N)) (CnInner_Product_Space (S N)) N B).
move=> W H7.
exists (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => (fun (m : Count (S N)) => Conjugate (v m))
  | inr n => W n
end).
apply conj.
suff: (UnitaryMatrix (S N) (AdjointMatrix (S N) (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => (fun (m : Count (S N)) => Conjugate (v m))
  | inr n => W n
end))).
move=> H8.
unfold UnitaryMatrix.
suff: (AdjointMatrix (S N) (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => (fun (m : Count (S N)) => Conjugate (v m))
  | inr n => W n
end) = InvMatrix Cfield (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => (fun (m : Count (S N)) => Conjugate (v m))
  | inr n => W n
end)).
move=> H9.
rewrite H9.
apply (InvMatrixMultL Cfield (S N)).
apply (proj2 (RegularInvRExistRelation Cfield (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => (fun (m : Count (S N)) => Conjugate (v m))
  | inr n => W n
end))).
exists (AdjointMatrix (S N) (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => (fun (m : Count (S N)) => Conjugate (v m))
  | inr n => W n
end)).
rewrite - H8.
suff: ((AdjointMatrix (S N) (S N) (AdjointMatrix (S N) (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => (fun (m : Count (S N)) => Conjugate (v m))
  | inr n => W n
end))) = (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => (fun (m : Count (S N)) => Conjugate (v m))
  | inr n => W n
end)).
move=> H10.
rewrite H10.
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply ConjugateInvolutive.
apply (InvMatrixMultUniqueRStrong Cfield (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => (fun (m : Count (S N)) => Conjugate (v m))
  | inr n => W n
end) (AdjointMatrix (S N) (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => (fun (m : Count (S N)) => Conjugate (v m))
  | inr n => W n
end))).
rewrite - H8.
suff: ((AdjointMatrix (S N) (S N) (AdjointMatrix (S N) (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => (fun (m : Count (S N)) => Conjugate (v m))
  | inr n => W n
end))) = (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => (fun (m : Count (S N)) => Conjugate (v m))
  | inr n => W n
end)).
move=> H9.
rewrite H9.
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply ConjugateInvolutive.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H8.
suff: (x = y).
move=> H9.
rewrite H9.
unfold Mmult.
unfold AdjointMatrix.
elim (AddConnectInv 1 N y).
move=> H10.
suff: (FI Cfield = CnInnerProduct (S N) v v).
move=> H11.
rewrite H11.
unfold CnInnerProduct.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S N)%nat} (exist (Finite {n : nat | (n < S N)%nat}) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> D d H12 H13 H14 H15.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H15.
rewrite ConjugateInvolutive.
rewrite ConjugateInvolutive.
rewrite Cmult_comm.
reflexivity.
apply H14.
apply H14.
rewrite (proj1 H3).
reflexivity.
move=> m.
simpl.
rewrite - (proj1 (proj1 H7) m).
simpl.
unfold CnInnerProduct.
unfold Count.
apply (MySumF2Same {n : nat | (n < S N)%nat} (exist (Finite {n : nat | (n < S N)%nat}) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N))) (FPCM Cfield) (fun (n : {n : nat | (n < S N)%nat}) => Cmult (Conjugate (Conjugate (W m n))) (Conjugate (W m n))) (fun (n : {n : nat | (n < S N)%nat}) => Cmult (W m n) (Conjugate (W m n)))).
move=> u H10.
rewrite ConjugateInvolutive.
reflexivity.
apply sig_map.
apply H8.
move=> H8.
suff: (forall (t : Count N), CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) (W t) = CO).
move=> H9.
unfold Mmult.
unfold AdjointMatrix.
elim (le_or_lt 1 (proj1_sig x)).
move=> H10.
suff: (match AddConnectInv 1 N x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N x).
move=> x0.
elim.
move=> x0 H11.
elim (le_or_lt 1 (proj1_sig y)).
move=> H12.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H13.
simpl.
rewrite - (proj2 (proj1 H7) x0 y0).
simpl.
unfold CnInnerProduct.
unfold Count.
apply (MySumF2Same {n : nat | (n < S N)%nat} (exist (Finite {n : nat | (n < S N)%nat}) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N))) (FPCM Cfield)).
move=> u H14.
rewrite ConjugateInvolutive.
reflexivity.
move=> H14.
apply H8.
rewrite H13.
rewrite H11.
rewrite H14.
reflexivity.
apply (proj2 (AddConnectInvNature 1 N) y H12).
move=> H12.
suff: (match AddConnectInv 1 N y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N y).
move=> y0 H13.
simpl.
rewrite - ConjugateCO.
rewrite - (H9 x0).
unfold CnInnerProduct.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S N)%nat} (exist (Finite {n : nat | (n < S N)%nat}) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite ConjugateCO.
reflexivity.
move=> D d H14 H15 H16 H17.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H17.
simpl.
rewrite Proposition_4_8_1_1.
rewrite Proposition_4_8_2.
rewrite Cmult_comm.
rewrite ConjugateInvolutive.
reflexivity.
apply H16.
apply H16.
move=> H13.
elim.
apply (proj1 (AddConnectInvNature 1 N) y H12).
apply (proj2 (AddConnectInvNature 1 N) x H10).
move=> H10.
suff: (match AddConnectInv 1 N x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N x).
move=> x0 H11.
elim (le_or_lt 1 (proj1_sig y)).
move=> H12.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H13.
simpl.
rewrite - (H9 y0).
unfold CnInnerProduct.
unfold Count.
apply (MySumF2Same {n : nat | (n < S N)%nat} (exist (Finite {n : nat | (n < S N)%nat}) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N))) (FPCM Cfield)).
move=> u H14.
rewrite ConjugateInvolutive.
reflexivity.
apply (proj2 (AddConnectInvNature 1 N) y H12).
move=> H12.
apply False_ind.
apply H8.
suff: (forall (n : nat), (n < 1)%nat -> n = O).
move=> H13.
rewrite (H13 (proj1_sig y) H12).
apply (H13 (proj1_sig x) H10).
move=> n H13.
elim (le_lt_or_eq n O (le_S_n n O H13)).
move=> H14.
elim (le_not_lt O n (le_0_n n) H14).
apply.
move=> x0.
elim.
apply (proj1 (AddConnectInvNature 1 N) x H10).
move=> t.
elim H6.
move=> H9 H10.
suff: (In (Cn (S N)) (SpanVS Cfield (FnVS Cfield (S N)) (Count N) B) (W t)).
elim.
move=> a H11.
rewrite H11.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (fun (t0 : Count N) => proj1_sig a t0 <> FO Cfield) (proj2_sig a))).
apply conj.
rewrite MySumF2Empty.
apply (Cip_mult_0_r (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
move=> D d H12 H13 H14 H15.
rewrite MySumF2Add.
simpl.
suff: (CnInnerProduct (S N) = Cip (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
move=> H16.
rewrite H16.
suff: (Fnadd Cfield (S N) = Vadd Cfield (FnVS Cfield (S N))).
move=> H17.
rewrite H17.
rewrite (Cip_linear_plus_r (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
suff: (Fnmul Cfield (S N) = Vmul Cfield (FnVS Cfield (S N))).
move=> H18.
rewrite H18.
rewrite (Cip_linear_mult_r (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
simpl.
rewrite H15.
rewrite (H9 d).
rewrite Cplus_0_l.
apply (Fmul_O_r Cfield).
reflexivity.
reflexivity.
reflexivity.
apply H14.
rewrite (proj2 H7).
apply (SpanContainSelfVS Cfield (FnVS Cfield (S N)) (Count N) W t).
suff: (match AddConnectInv 1 N (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) return Prop with
  | inl k => proj1_sig (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))).
move=> H8 H9.
reflexivity.
move=> H8.
elim.
apply (proj1 (AddConnectInvNature 1 N) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))).
apply (le_n 1).
apply (SubspaceBasisLinearlyIndependentVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 (Count N) B H6).
suff: (DimensionSubspaceVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 H5 = N).
move=> H6.
suff: (exists (B : Count (DimensionSubspaceVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 H5) -> Cn (S N)), BasisSubspaceVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 (Count (DimensionSubspaceVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 H5)) B).
rewrite H6.
apply.
apply (DimensionSubspaceVSNature Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 H5).
suff: (SubspaceVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m)))).
move=> H6.
elim (DimensionSumEnsembleVS2_exists Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H6 H4).
move=> H7 H8.
suff: (FiniteDimensionVS Cfield (SubspaceMakeVS Cfield (FnVS Cfield (S N)) (SumEnsembleVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) H7)).
move=> H9.
elim (H8 H9).
move=> H10.
elim.
move=> H11 H12.
apply (plus_reg_l (DimensionSubspaceVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 H5) N 1).
suff: ((1 + N)%nat = DimensionSubspaceVS Cfield (FnVS Cfield (S N)) (SumEnsembleVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) H7 H9).
move=> H13.
rewrite H13.
suff: (1%nat = DimensionSubspaceVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) H6 H10).
move=> H14.
rewrite H14.
rewrite H12.
suff: (H5 = H11).
move=> H15.
unfold DimensionSubspaceVS.
rewrite H15.
reflexivity.
apply proof_irrelevance.
apply Extensionality_Ensembles.
apply conj.
move=> u.
elim.
move=> u0 H15 H16.
suff: (u0 = VO Cfield (FnVS Cfield (S N))).
move=> H17.
rewrite H17.
apply In_singleton.
elim H15.
move=> c H17.
suff: (c = CO).
move=> H18.
rewrite H17.
rewrite H18.
apply (Vmul_O_l Cfield (FnVS Cfield (S N)) (fun (m : Count (S N)) => Conjugate (v m))).
suff: (CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) u0 = CO).
rewrite H17.
suff: (CnInnerProduct (S N) = Cip (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
move=> H18.
rewrite H18.
rewrite Cip_linear_mult_r.
suff: ((Cip (FnVS Cfield (S N)) (CnInner_Product_Space (S N)) (fun (m : Count (S N)) => Conjugate (v m)) (fun (m : Count (S N)) => Conjugate (v m))) = CI).
move=> H19.
rewrite H19.
rewrite Cmult_comm.
rewrite (Cmult_1_l (Conjugate c)).
move=> H20.
rewrite - (ConjugateInvolutive c).
rewrite H20.
apply ConjugateCO.
rewrite - (proj1 H3).
simpl.
unfold CnInnerProduct.
apply (MySumF2Same (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (FPCM Cfield)).
move=> u1 H19.
rewrite ConjugateInvolutive.
apply Cmult_comm.
reflexivity.
apply H16.
move=> u.
elim.
apply (proj2 (proj2 (IntersectionSubspaceVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H6 H4))).
rewrite (DimensionSubspaceVSNature2 Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) H6 H10 1 (fun (m : Count 1) => (fun (m : Count (S N)) => Conjugate (v m)))).
reflexivity.
suff: (exists (f : C), (fun (m : Count (S N)) => Conjugate (v m)) = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))).
move=> H14.
exists (fun (m : Count 1) => H14).
apply (proj2 (BasisLIGeVS Cfield (SubspaceMakeVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) H6) (Count 1) (fun (m : Count 1) => exist (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) (fun (m : Count (S N)) => Conjugate (v m)) H14))).
apply conj.
apply FiniteLinearlyIndependentVS.
move=> a H15 m.
suff: (MySumF2 (Count 1) (exist (Finite (Count 1)) (Full_set (Count 1)) (CountFinite 1)) (VSPCM Cfield (SubspaceMakeVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) H6)) (fun (n : Count 1) => Vmul Cfield (SubspaceMakeVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) H6) (a n) (exist (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) (fun (m : Count (S N)) => Conjugate (v m)) H14)) = VO Cfield (SubspaceMakeVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) H6)).
suff: (exist (Finite (Count 1)) (Full_set (Count 1)) (CountFinite 1) = FiniteSingleton (Count 1) m).
move=> H16.
rewrite H16.
rewrite MySumF2Singleton.
move=> H17.
suff: (Fnmul Cfield (S N) (a m) (fun (m : Count (S N)) => Conjugate (v m)) = VO Cfield (FnVS Cfield (S N))).
move=> H18.
elim (Vmul_integral Cfield (FnVS Cfield (S N)) (a m) (fun (m : Count (S N)) => Conjugate (v m)) H18).
apply.
simpl.
move=> H19.
apply False_ind.
apply CI_neq_CO.
rewrite - (proj1 H3).
apply (Cip_refl (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
apply functional_extensionality.
move=> u.
simpl.
rewrite - (ConjugateInvolutive (v u)).
suff: (Conjugate (v u) = FnO Cfield (S N) u).
move=> H20.
rewrite H20.
apply ConjugateCO.
rewrite - H19.
reflexivity.
suff: (Fnmul Cfield (S N) (a m) (fun (m0 : Count (S N)) => Conjugate (v m0)) = proj1_sig (Vmul Cfield (SubspaceMakeVS Cfield (FnVS Cfield (S N)) (fun w : Cn (S N) => exists f : C, w = Fnmul Cfield (S N) f (fun m : Count (S N) => Conjugate (v m))) H6) (a m) (exist (fun w : Cn (S N) => exists f : C, w = Fnmul Cfield (S N) f (fun m : Count (S N) => Conjugate (v m))) (fun m : Count (S N) => Conjugate (v m)) H14))).
move=> H18.
rewrite H18.
rewrite H17.
reflexivity.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u H16.
suff: (m = u).
move=> H17.
rewrite H17.
apply (In_singleton (Count 1) u).
apply sig_map.
suff: (forall (n : nat), (n < 1)%nat -> n = O).
move=> H17.
rewrite (H17 (proj1_sig u) (proj2_sig u)).
apply (H17 (proj1_sig m) (proj2_sig m)).
move=> n H17.
elim (le_lt_or_eq n O (le_S_n n O H17)).
move=> H18.
elim (le_not_lt O n (le_0_n n) H18).
apply.
move=> u H16.
apply (Full_intro (Count 1) u).
apply H15.
apply Extensionality_Ensembles.
apply conj.
move=> m H15.
elim (proj2_sig m).
move=> c H16.
rewrite FiniteSpanVS.
exists (fun (a : Count 1) => c).
suff: (exist (Finite (Count 1)) (Full_set (Count 1)) (CountFinite 1) = FiniteSingleton (Count 1) (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1))).
move=> H17.
rewrite H17.
rewrite MySumF2Singleton.
apply sig_map.
apply H16.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u H17.
suff: ((exist (fun (n : nat) => (n < 1)%nat) O (le_n 1)) = u).
move=> H18.
rewrite H18.
apply (In_singleton (Count 1) u).
apply sig_map.
elim (le_lt_or_eq (proj1_sig u) O (le_S_n (proj1_sig u) O (proj2_sig u))).
move=> H18.
elim (le_not_lt O (proj1_sig u) (le_0_n (proj1_sig u)) H18).
move=> H18.
rewrite H18.
reflexivity.
move=> u H17.
apply (Full_intro (Count 1) u).
move=> m H15.
apply Full_intro.
exists CI.
rewrite (Fnmul_I_l Cfield (S N)).
reflexivity.
suff: (FiniteDimensionVS Cfield (FnVS Cfield (S N))).
move=> H13.
suff: (DimensionVS Cfield (FnVS Cfield (S N)) H13 = S N).
move=> H14.
elim (DimensionVSNature Cfield (FnVS Cfield (S N)) H13).
rewrite H14.
move=> a H15.
unfold DimensionSubspaceVS.
suff: (forall (z : Cn (S N)), In (Cn (S N)) (SumEnsembleVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) z).
move=> H16.
rewrite (DimensionVSNature2 Cfield (SubspaceMakeVS Cfield (FnVS Cfield (S N)) (SumEnsembleVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) H7) H9 (S N) (fun (m : Count (S N)) => exist (SumEnsembleVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) (a m) (H16 (a m)))).
reflexivity.
apply (IsomorphicSaveBasisVS Cfield (FnVS Cfield (S N)) (SubspaceMakeVS Cfield (FnVS Cfield (S N)) (SumEnsembleVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) H7) (Count (S N)) a (fun (z : Cn (S N)) => exist (SumEnsembleVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) z (H16 z))).
apply conj.
exists (fun (m : (SubspaceMakeVST Cfield (FnVS Cfield (S N)) (SumEnsembleVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) H7)) => proj1_sig m).
apply conj.
move=> m.
reflexivity.
move=> m.
apply sig_map.
reflexivity.
apply conj.
move=> x y.
apply sig_map.
reflexivity.
move=> c x.
apply sig_map.
reflexivity.
apply H15.
move=> z.
suff: (z = Fnadd Cfield (S N) (Fnmul Cfield (S N) (Conjugate (CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) z)) (fun (m : Count (S N)) => Conjugate (v m))) (Fnminus Cfield (S N) z (Fnmul Cfield (S N) (Conjugate (CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) z)) (fun (m : Count (S N)) => Conjugate (v m))))).
move=> H16.
rewrite H16.
apply (SumEnsembleVS_intro Cfield (FnVS Cfield (S N))).
exists (Conjugate (CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) z)).
reflexivity.
unfold Fnminus.
unfold In.
suff: (CnInnerProduct (S N) = Cip (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
move=> H17.
rewrite H17.
suff: (Fnadd Cfield (S N) = Vadd Cfield (FnVS Cfield (S N))).
move=> H18.
rewrite H18.
suff: (Fnmul Cfield (S N) = Vmul Cfield (FnVS Cfield (S N))).
move=> H19.
rewrite H19.
suff: (Fnopp Cfield (S N) = Vopp Cfield (FnVS Cfield (S N))).
move=> H20.
rewrite H20.
rewrite Cip_linear_plus_r.
rewrite Cip_linear_opp_r.
rewrite Cip_linear_mult_r.
suff: ((Cip (FnVS Cfield (S N)) (CnInner_Product_Space (S N)) (fun (m : Count (S N)) => Conjugate (v m)) (fun (m : Count (S N)) => Conjugate (v m))) = CI).
move=> H21.
rewrite H21.
rewrite Cmult_comm.
rewrite Cmult_1_l.
rewrite ConjugateInvolutive.
apply Cplus_opp_r.
rewrite - (proj1 H3).
simpl.
unfold CnInnerProduct.
apply (MySumF2Same (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (FPCM Cfield)).
move=> u H21.
rewrite ConjugateInvolutive.
apply Cmult_comm.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
unfold Fnminus.
rewrite (Fnadd_comm Cfield (S N) z).
rewrite - (Fnadd_assoc Cfield (S N)).
rewrite (Fnadd_opp_r Cfield (S N)).
rewrite (Fnadd_O_l Cfield (S N) z).
reflexivity.
elim (FnVSDimension Cfield (S N)).
move=> H14 H15.
suff: (H13 = H14).
move=> H16.
rewrite H16.
rewrite H15.
reflexivity.
apply proof_irrelevance.
apply (FnVSFiniteDimension Cfield (S N)).
apply (Proposition_5_9_1_1 Cfield (FnVS Cfield (S N))).
apply (FnVSFiniteDimension Cfield (S N)).
apply conj.
move=> x y.
elim.
move=> c1 H6.
elim.
move=> c2 H7.
exists (Cplus c1 c2).
rewrite H6.
rewrite H7.
rewrite - (Vmul_add_distr_r Cfield (FnVS Cfield (S N)) c1 c2 (fun (m : Count (S N)) => Conjugate (v m))).
reflexivity.
apply conj.
move=> f x.
elim.
move=> c H6.
exists (Cmult f c).
rewrite H6.
apply (Vmul_assoc Cfield (FnVS Cfield (S N))).
exists CO.
rewrite - (Vmul_O_l Cfield (FnVS Cfield (S N)) (fun (m : Count (S N)) => Conjugate (v m))).
reflexivity.
apply (Proposition_5_9_1_1 Cfield (FnVS Cfield (S N))).
apply (FnVSFiniteDimension Cfield (S N)).
apply conj.
move=> x y H4 H5.
unfold In.
suff: (CnInnerProduct (S N) = Cip (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
move=> H6.
rewrite H6.
rewrite (Cip_linear_plus_r (FnVS Cfield (S N)) (CnInner_Product_Space (S N)) (fun (m : Count (S N)) => Conjugate (v m)) x y).
simpl.
rewrite H4.
rewrite H5.
apply (Cplus_0_l CO).
reflexivity.
apply conj.
move=> f x H4.
unfold In.
suff: (CnInnerProduct (S N) = Cip (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
move=> H6.
rewrite H6.
rewrite (Cip_linear_mult_r (FnVS Cfield (S N)) (CnInner_Product_Space (S N)) f (fun (m : Count (S N)) => Conjugate (v m)) x).
simpl.
rewrite H4.
apply (Fmul_O_r Cfield).
reflexivity.
apply (Cip_mult_0_r (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
elim (Theorem_7_3_2_1 (Rn_met (S N * 2)) (fun (x : Rn (S N * 2)) => Aform (CnRnConvertInv (S N) x)) (fun (x : Rn (S N * 2)) => RnInnerProduct (S N * 2) x x = 1)).
move=> z H4.
suff: (forall (y : R), In R (Im (Base (Rn_met (S N * 2))) R (fun (x : Rn (S N * 2)) => RnInnerProduct (S N * 2) x x = 1) (fun (x : Rn (S N * 2)) => Aform (CnRnConvertInv (S N) x))) y -> y <= z).
elim (proj1 H4).
move=> x H5 y H6 H7.
exists (CnRnConvertInv (S N) x).
suff: (forall (v : Count (S N) -> C), CnInnerProduct (S N) v v = CI <-> RnInnerProduct (S N * 2) (CnRnConvert (S N) v) (CnRnConvert (S N) v) = 1).
move=> H8.
apply conj.
apply H8.
rewrite (proj2 (CnRnConvertInvRelation (S N)) x).
apply H5.
move=> w H9.
rewrite - H6.
apply H7.
apply (Im_intro (Base (Rn_met (S N * 2))) R (fun (x0 : Rn (S N * 2)) => RnInnerProduct (S N * 2) x0 x0 = 1) (fun (x0 : Rn (S N * 2)) => Aform (CnRnConvertInv (S N) x0)) (CnRnConvert (S N) w)).
apply H8.
apply H9.
rewrite (proj1 (CnRnConvertInvRelation (S N)) w).
reflexivity.
move=> v.
apply conj.
move=> H8.
rewrite - (CnRnInnerProductRelation (S N) v).
rewrite H8.
apply (CmakeRe 1 0).
move=> H8.
apply functional_extensionality.
move=> k.
elim (CReorCIm k).
move=> H9.
rewrite H9.
rewrite (CnRnInnerProductRelation (S N) v).
unfold CI.
rewrite (CmakeRe 1 0).
apply H8.
move=> H9.
rewrite H9.
unfold CI.
rewrite (CmakeIm 1 0).
apply (Cip_pos_im (FnVS Cfield (S N)) (CnInner_Product_Space (S N)) v).
apply (proj2 H4).
suff: (O < S N * 2)%nat.
move=> H4.
apply (Inhabited_intro (Base (Rn_met (S N * 2))) (fun (x : Rn (S N * 2)) => RnInnerProduct (S N * 2) x x = 1) (fun (m : Count (S N * 2)) => match excluded_middle_informative (m = exist (fun (k : nat) => (k < S N * 2)%nat) O H4) with
  | left _ => 1
  | right _ => 0
end)).
unfold In.
unfold RnInnerProduct.
rewrite (MySumF2Included (Count (S N * 2)) (FiniteSingleton (Count (S N * 2)) (exist (fun (k : nat) => (k < S N * 2)%nat) O H4))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
elim (excluded_middle_informative (@eq (Count (S N * 2)) (exist (fun (k : nat) => (k < S N * 2)%nat) O H4) (exist (fun (k : nat) => (k < S N * 2)%nat) O H4))).
move=> H5.
rewrite (Rmult_1_r 1).
apply (CM_O_r RPCM 1).
elim.
reflexivity.
move=> u.
elim.
move=> u0 H5 H6.
elim (excluded_middle_informative (@eq (Count (S N * 2)) u0 (exist (fun (k : nat) => (k < S N * 2)%nat) O H4))).
move=> H7.
elim H5.
rewrite H7.
apply (In_singleton (Count (S N * 2))).
move=> H7.
apply (Rmult_0_r 0).
move=> m H5.
apply (Full_intro (Count (S N * 2)) m).
simpl.
apply (le_n_S O (S (N * 2)) (le_0_n (S (N * 2)))).
suff: (forall (m : Count (S N * 2)) (a : Base (Rn_met (S N * 2))), ContinuousMet (Rn_met (S N * 2)) R_met (fun (x : Base (Rn_met (S N * 2))) => x m) (Full_set (Base (Rn_met (S N * 2)))) a).
move=> H4 x H5.
unfold Aform.
unfold CnInnerProduct.
apply (FiniteSetInduction (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N)))).
apply conj.
move=> eps H6.
exists 1.
apply conj.
apply Rlt_0_1.
move=> y H7.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (proj2 (dist_refl R_met 0 0)).
apply H6.
reflexivity.
move=> B b H6 H7 H8 H9.
suff: ((fun (x0 : Rn (S N * 2)) => MySumF2 (Count (S N)) (FiniteAdd (Count (S N)) B b) (FPCM Cfield) (fun (n : Count (S N)) => Cmult (CnRnConvertInv (S N) x0 n) (Conjugate (MVmult Cfield (S N) (S N) A (fun (m : Count (S N)) => CnRnConvertInv (S N) x0 m) n))) CRe) = (fun (x0 : Rn (S N * 2)) => (MySumF2 (Count (S N)) B (FPCM Cfield) (fun n : Count (S N) => Cmult (CnRnConvertInv (S N) x0 n) (Conjugate (MVmult Cfield (S N) (S N) A (fun (m : Count (S N)) => CnRnConvertInv (S N) x0 m) n))) CRe) + (Cmult (CnRnConvertInv (S N) x0 b) (Conjugate (MVmult Cfield (S N) (S N) A (fun (m : Count (S N)) => CnRnConvertInv (S N) x0 m) b)) CRe))).
move=> H10.
rewrite H10.
apply Theorem_6_6_3_1_R.
apply H9.
apply (Theorem_6_8_2 (Rn_met (S N * 2)) 2 (fun r : Base (Rn_met (S N * 2)) => Cmult (CnRnConvertInv (S N) r b) (Conjugate (MVmult Cfield (S N) (S N) A (fun (m : Count (S N)) => CnRnConvertInv (S N) r m) b))) (Full_set (Base (Rn_met (S N * 2)))) x).
apply Theorem_6_6_3_5_C.
apply Theorem_6_8_2.
move=> n.
elim (CReorCIm n).
move=> H11.
rewrite H11.
suff: ((fun (r : Base (Rn_met (S N * 2))) => CnRnConvertInv (S N) r b CRe) = (fun (r : Base (Rn_met (S N * 2))) => (r (MultConnect (S N) 2 (b, CRe))))).
move=> H12.
rewrite H12.
apply H4.
apply functional_extensionality.
move=> r.
apply CmakeRe.
move=> H11.
rewrite H11.
suff: ((fun r : Base (Rn_met (S N * 2)) => CnRnConvertInv (S N) r b CIm) = (fun (r : Base (Rn_met (S N * 2))) => (r (MultConnect (S N) 2 (b, CIm))))).
move=> H12.
rewrite H12.
apply H4.
apply functional_extensionality.
move=> r.
apply CmakeIm.
unfold MVmult.
unfold MMatrixToVector.
unfold MVectorToMatrix.
unfold Mmult.
apply (FiniteSetInduction {n : nat | (n < S N)%nat} (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
apply conj.
move=> eps H11.
exists 1.
apply conj.
apply Rlt_0_1.
move=> y H12.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (proj2 (dist_refl (Rn_met 2) (Conjugate (CMe (FPCM Cfield))) (Conjugate (CMe (FPCM Cfield))))).
apply H11.
reflexivity.
move=> D d H11 H12 H13 H14 .
suff: ((fun (r : Base (Rn_met (S N * 2))) => Conjugate (MySumF2 {n : nat | (n < S N)%nat} (FiniteAdd {n : nat | (n < S N)%nat} D d) (FPCM Cfield) (fun (n : Count (S N)) => Fmul Cfield (A b n) (CnRnConvertInv (S N) r n)))) = (fun (r : Base (Rn_met (S N * 2))) => Cplus (Conjugate (MySumF2 {n : nat | (n < S N)%nat} D (FPCM Cfield) (fun (n : Count (S N)) => Fmul Cfield (A b n) (CnRnConvertInv (S N) r n)))) (Conjugate (Fmul Cfield (A b d) (CnRnConvertInv (S N) r d))))).
move=> H15.
rewrite H15.
apply Theorem_6_6_3_1_Rn.
apply H14.
suff: (ContinuousMet (Rn_met (S N * 2)) (Rn_met 2) (fun r : Base (Rn_met (S N * 2)) => Fmul Cfield (A b d) (CnRnConvertInv (S N) r d)) (Full_set (Base (Rn_met (S N * 2)))) x).
move=> H16.
apply Theorem_6_8_2.
move=> n.
elim (CReorCIm n).
move=> H17.
rewrite H17.
suff: ((fun (r : Base (Rn_met (S N * 2))) => Conjugate (Fmul Cfield (A b d) (CnRnConvertInv (S N) r d)) CRe) = (fun (r : Base (Rn_met (S N * 2))) => Fmul Cfield (A b d) (CnRnConvertInv (S N) r d) CRe)).
move=> H18.
rewrite H18.
apply (Theorem_6_8_2 (Rn_met (S N * 2)) 2 (fun (r : Base (Rn_met (S N * 2))) => Fmul Cfield (A b d) (CnRnConvertInv (S N) r d))).
apply H16.
apply functional_extensionality.
move=> r.
apply CmakeRe.
move=> H17.
rewrite H17.
suff: ((fun (r : Base (Rn_met (S N * 2))) => Conjugate (Fmul Cfield (A b d) (CnRnConvertInv (S N) r d)) CIm) = (fun (r : Base (Rn_met (S N * 2))) => - Fmul Cfield (A b d) (CnRnConvertInv (S N) r d) CIm)).
move=> H18.
rewrite H18.
apply Theorem_6_6_3_4_R.
apply (Theorem_6_8_2 (Rn_met (S N * 2)) 2 (fun (r : Base (Rn_met (S N * 2))) => Fmul Cfield (A b d) (CnRnConvertInv (S N) r d))).
apply H16.
apply functional_extensionality.
move=> r.
apply CmakeIm.
apply Theorem_6_6_3_5_C.
move=> eps H16.
exists 1.
apply conj.
apply Rlt_0_1.
move=> y H17.
rewrite (proj2 (dist_refl (Rn_met 2) (A b d) (A b d))).
apply H16.
reflexivity.
apply Theorem_6_8_2.
move=> n.
elim (CReorCIm n).
move=> H16.
rewrite H16.
suff: ((fun (r : Base (Rn_met (S N * 2))) => CnRnConvertInv (S N) r d CRe) = (fun (r : Base (Rn_met (S N * 2))) => (r (MultConnect (S N) 2 (d, CRe))))).
move=> H17.
rewrite H17.
apply H4.
apply functional_extensionality.
move=> r.
apply CmakeRe.
move=> H16.
rewrite H16.
suff: ((fun (r : Base (Rn_met (S N * 2))) => CnRnConvertInv (S N) r d CIm) = (fun (r : Base (Rn_met (S N * 2))) => (r (MultConnect (S N) 2 (d, CIm))))).
move=> H17.
rewrite H17.
apply H4.
apply functional_extensionality.
move=> r.
apply CmakeIm.
apply functional_extensionality.
move=> r.
rewrite MySumF2Add.
apply Proposition_4_8_1_1.
apply H13.
apply functional_extensionality.
move=> m.
rewrite MySumF2Add.
reflexivity.
apply H8.
move=> m a eps H4.
exists eps.
apply conj.
apply H4.
move=> x.
unfold dist.
unfold R_met.
unfold Rn_met.
unfold Rn_dist.
unfold R_dist.
simpl.
move=> H5.
apply (Rle_lt_trans (Rabs (x m - a m)) (RnNorm (S N * 2) (Rnminus (S N * 2) x a)) eps).
suff: (Rabs (x m - a m) * Rabs (x m - a m) <= RnNorm (S N * 2) (Rnminus (S N * 2) x a) * RnNorm (S N * 2) (Rnminus (S N * 2) x a)).
move=> H6.
apply Rnot_lt_le.
move=> H7.
apply (Rle_not_lt (RnNorm (S N * 2) (Rnminus (S N * 2) x a) * RnNorm (S N * 2) (Rnminus (S N * 2) x a)) (Rabs (x m - a m) * Rabs (x m - a m)) H6).
apply Rmult_le_0_lt_compat.
apply Rge_le.
apply (proj1 (RnNormNature (S N * 2) (Rnminus (S N * 2) x a))).
apply Rge_le.
apply (proj1 (RnNormNature (S N * 2) (Rnminus (S N * 2) x a))).
apply H7.
apply H7.
suff: (Rabs (x m - a m) * Rabs (x m - a m) = (x m - a m) * (x m - a m)).
move=> H6.
rewrite H6.
rewrite - (Rplus_0_r ((x m - a m) * (x m - a m))).
rewrite - (proj2 (RnNormNature (S N * 2) (Rnminus (S N * 2) x a))).
unfold RnInnerProduct.
rewrite (MySumF2Included (Count (S N * 2)) (FiniteSingleton (Count (S N * 2)) m)).
rewrite MySumF2Singleton.
apply Rplus_le_compat_l.
apply MySumF2Induction.
apply conj.
right.
reflexivity.
move=> cm u H7 H8.
apply Rplus_le_le_0_compat.
apply H8.
apply Rle_0_sqr.
move=> u H7.
apply (Full_intro (Count (S N * 2)) u).
unfold Rabs.
elim (Rcase_abs (x m - a m)).
move=> H6.
apply Rmult_opp_opp.
move=> H6.
reflexivity.
apply (proj2 H5).
apply (Theorem_7_2_2_2 (S N * 2)).
apply conj.
exists (RnO (S N * 2)).
exists (1 + 1).
move=> x H4.
unfold In.
unfold NeighborhoodMet.
suff: (dist (Rn_met (S N * 2)) x (RnO (S N * 2)) = 1).
move=> H5.
rewrite H5.
apply Rlt_plus_1.
apply (RnNormNature2 (S N * 2)).
apply conj.
left.
apply Rlt_0_1.
suff: (Rnminus (S N * 2) x (RnO (S N * 2)) = x).
move=> H5.
rewrite H5.
rewrite (Rmult_1_r 1).
apply H4.
apply functional_extensionality.
move=> m.
apply Rminus_0_r.
apply (proj2 (Proposition_7_1_2 (Rn_met (S N * 2)) (fun (x : Rn (S N * 2)) => RnInnerProduct (S N * 2) x x = 1))).
move=> x H4.
elim (Rle_or_lt (Rn_dist (S N * 2) x (RnO (S N * 2))) 1).
elim.
move=> H5.
exists (1 - Rn_dist (S N * 2) x (RnO (S N * 2))).
apply conj.
apply Rgt_minus.
apply H5.
move=> u H6.
suff: (Rn_dist (S N * 2) u (RnO (S N * 2)) < 1).
move=> H7 H8.
apply (Rlt_not_eq (Rn_dist (S N * 2) u (RnO (S N * 2))) 1 H7).
apply RnNormNature2.
apply conj.
left.
apply Rlt_0_1.
suff: (Rnminus (S N * 2) u (RnO (S N * 2)) = u).
move=> H9.
rewrite H9.
rewrite (Rmult_1_r 1).
apply H8.
apply functional_extensionality.
move=> m.
apply Rminus_0_r.
apply (Rle_lt_trans (Rn_dist (S N * 2) u (RnO (S N * 2))) (dist (Rn_met (S N * 2)) u x + Rn_dist (S N * 2) x (RnO (S N * 2))) 1).
apply (Rn_dist_tri (S N * 2)).
rewrite - (Rplus_0_r 1).
rewrite - (Rplus_opp_l (Rn_dist (S N * 2) x (RnO (S N * 2)))).
rewrite - Rplus_assoc.
apply Rplus_lt_compat_r.
apply H6.
move=> H5.
elim H4.
unfold In.
rewrite (proj2 (RnNormNature (S N * 2) x)).
suff: (Rnminus (S N * 2) x (RnO (S N * 2)) = x).
move=> H6.
rewrite - H6.
suff: (RnNorm (S N * 2) (Rnminus (S N * 2) x (RnO (S N * 2))) = 1).
move=> H7.
rewrite H7.
apply (Rmult_1_r 1).
apply H5.
apply functional_extensionality.
move=> m.
apply Rminus_0_r.
move=> H5.
exists (Rn_dist (S N * 2) x (RnO (S N * 2)) - 1).
apply conj.
apply Rgt_minus.
apply H5.
move=> u H6.
suff: (Rn_dist (S N * 2) u (RnO (S N * 2)) > 1).
move=> H7 H8.
apply (Rgt_not_eq (Rn_dist (S N * 2) u (RnO (S N * 2))) 1 H7).
apply RnNormNature2.
apply conj.
left.
apply Rlt_0_1.
suff: (Rnminus (S N * 2) u (RnO (S N * 2)) = u).
move=> H9.
rewrite H9.
rewrite (Rmult_1_r 1).
apply H8.
apply functional_extensionality.
move=> m.
apply Rminus_0_r.
apply (Rlt_le_trans 1 (Rn_dist (S N * 2) x (RnO (S N * 2)) - dist (Rn_met (S N * 2)) u x) (Rn_dist (S N * 2) u (RnO (S N * 2)))).
rewrite - (Rplus_0_r 1).
rewrite - (Rplus_opp_r (dist (Rn_met (S N * 2)) u x)).
rewrite - Rplus_assoc.
apply Rplus_lt_compat_r.
rewrite Rplus_comm.
rewrite - (Rplus_0_r (Rn_dist (S N * 2) x (RnO (S N * 2)))).
rewrite - (Rplus_opp_l 1).
rewrite - Rplus_assoc.
apply Rplus_lt_compat_r.
apply H6.
rewrite - (Rplus_0_r (Rn_dist (S N * 2) u (RnO (S N * 2)))).
rewrite - (Rplus_opp_r (dist (Rn_met (S N * 2)) u x)).
rewrite - Rplus_assoc.
apply Rplus_le_compat_r.
rewrite Rplus_comm.
rewrite dist_sym.
apply (Rn_dist_tri (S N * 2) x (RnO (S N * 2)) u).
Qed.

Lemma SymmetricTransformableToDiag : forall (N : nat) (A : Matrix Rfield N N), MSymmetric Rfield N A -> exists (V : Matrix Rfield N N) (D : {n : nat | (n < N)%nat} -> R), OrthogonalMatrix N V /\ MDiag Rfield N D = Mmult Rfield N N N (MTranspose Rfield N N V) (Mmult Rfield N N N A V).
Proof.
elim.
move=> A H1.
exists (MI Rfield O).
exists (fun (m : {n : nat | (n < 0)%nat}) => 1).
apply conj.
unfold OrthogonalMatrix.
rewrite (MTransI Rfield O).
apply (Mmult_I_r Rfield O O (MI Rfield O)).
apply functional_extensionality.
move=> m.
elim (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) (proj2_sig m)).
move=> N H1 A H2.
suff: (exists (V : Matrix Rfield (S N) (S N)), OrthogonalMatrix (S N) V /\ forall (m : {n : nat | (n < S N)%nat}), (proj1_sig m > O)%nat -> Mmult Rfield (S N) (S N) (S N) (MTranspose Rfield (S N) (S N) V) (Mmult Rfield (S N) (S N) (S N) A V) m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = 0).
elim.
move=> V H3.
suff: (exists (B : Matrix Rfield N N) (la : R), MSymmetric Rfield N B /\ Mmult Rfield (S N) (S N) (S N) (MTranspose Rfield (S N) (S N) V) (Mmult Rfield (S N) (S N) (S N) A V) = MBlockH Rfield 1 N (S N) (MBlockW Rfield 1 1 N (fun (_ _ : {n : nat | (n < 1)%nat}) => la) (MO Rfield 1 N)) (MBlockW Rfield N 1 N (MO Rfield N 1) B)).
elim.
move=> B.
elim.
move=> la H4.
elim (H1 B (proj1 H4)).
move=> W.
elim.
move=> D H5.
exists (Mmult Rfield (S N) (S N) (S N) V (MBlockH Rfield 1 N (S N) (MBlockW Rfield 1 1 N (fun _ _ : {n : nat | (n < 1)%nat} => 1) (MO Rfield 1 N)) (MBlockW Rfield N 1 N (MO Rfield N 1) W))).
exists (fun (m : {n : nat | (n < 1 + N)%nat}) => match AddConnectInv 1 N m with
  | inl _ => la
  | inr m0 => D m0
end).
apply conj.
apply (OrthogonalMatrixChain (S N)).
apply (proj1 H3).
unfold OrthogonalMatrix.
rewrite (MBlockHTranspose Rfield 1 N (S N)).
rewrite (MBlockWTranspose Rfield 1 1 N).
rewrite (MBlockWTranspose Rfield N 1 N).
rewrite (MBlockHWMult Rfield (S N) 1 N (S N)).
rewrite (MBlockHMult Rfield 1 N 1 (S N)).
rewrite (MBlockHMult Rfield 1 N N (S N)).
rewrite (MBlockWMult Rfield 1 1 1 N).
rewrite (MBlockWMult Rfield N 1 1 N).
rewrite (MBlockWMult Rfield 1 N 1 N).
rewrite (MBlockWMult Rfield N N 1 N).
rewrite (Mmult_O_r Rfield 1 1 N).
rewrite (Mmult_O_r Rfield N 1 N).
rewrite (Mmult_O_r Rfield 1 N 1).
rewrite (Mmult_O_r Rfield N N 1).
rewrite (MTransO Rfield N 1).
rewrite (MTransO Rfield 1 N).
rewrite (Mmult_O_l Rfield 1 N N).
rewrite (Mmult_O_l Rfield N 1 1).
rewrite (proj1 H5).
rewrite (MBlockHPlus Rfield 1 N (S N)).
rewrite (MBlockWPlus Rfield 1 1 N).
rewrite (MBlockWPlus Rfield N 1 N).
rewrite (Mplus_comm Rfield 1 1).
rewrite (Mplus_O_l Rfield 1 1).
rewrite (Mplus_O_l Rfield 1 N).
rewrite (Mplus_O_l Rfield N 1).
rewrite (Mplus_O_l Rfield N N).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H6.
suff: (x = y).
move=> H7.
rewrite H7.
elim (AddConnectInv 1 N y).
move=> k.
unfold Mmult.
suff: (exist (Finite (Count 1)) (Full_set {n : nat | (n < 1)%nat}) (CountFinite 1) = FiniteSingleton {n : nat | (n < 1)%nat} (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1))).
move=> H8.
rewrite H8.
rewrite MySumF2Singleton.
apply (Fmul_I_r Rfield (FI Rfield)).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> m H8.
suff: ((exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1)) = m).
move=> H9.
rewrite H9.
apply (In_singleton (Count 1) m).
apply sig_map.
elim (le_lt_or_eq O (proj1_sig m) (le_0_n (proj1_sig m))).
move=> H9.
elim (le_not_lt 1 (proj1_sig m) H9 (proj2_sig m)).
apply.
move=> m H8.
apply (Full_intro (Count 1) m).
move=> m.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H8.
reflexivity.
move=> H8.
apply False_ind.
apply H8.
reflexivity.
apply sig_map.
apply H6.
move=> H6.
elim (le_or_lt 1 (proj1_sig x)).
move=> H7.
suff: (match AddConnectInv 1 N x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N x).
move=> x0.
elim.
move=> x0 H8.
elim (le_or_lt 1 (proj1_sig y)).
move=> H9.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H10.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y0)).
move=> H11.
apply False_ind.
apply H6.
rewrite H8.
rewrite H10.
rewrite H11.
reflexivity.
move=> H11.
reflexivity.
apply (proj2 (AddConnectInvNature 1 N) y H9).
move=> H9.
suff: (match AddConnectInv 1 N y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N y).
move=> y0 H10.
reflexivity.
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 N) y H9).
apply (proj2 (AddConnectInvNature 1 N) x H7).
move=> H7.
suff: (match AddConnectInv 1 N x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N x).
move=> x0 H8.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H9.
reflexivity.
apply (proj2 (AddConnectInvNature 1 N) y).
elim (le_or_lt 1 (proj1_sig y)).
apply.
move=> H9.
apply False_ind.
apply H6.
suff: (forall (n : nat), (n < 1)%nat -> n = O).
move=> H10.
rewrite (H10 (proj1_sig y) H9).
apply (H10 (proj1_sig x) H7).
move=> n H10.
elim (le_lt_or_eq n 0 (le_S_n n 0 H10)).
move=> H11.
elim (le_not_lt O n (le_0_n n) H11).
apply.
move=> x0.
elim.
apply (proj1 (AddConnectInvNature 1 N) x H7).
rewrite (MTransMult Rfield (S N) (S N) (S N)).
rewrite (Mmult_assoc Rfield (S N) (S N) (S N) (S N)).
rewrite - (Mmult_assoc Rfield (S N) (S N) (S N) (S N) A).
rewrite - (Mmult_assoc Rfield (S N) (S N) (S N) (S N) (MTranspose Rfield (S N) (S N) V)).
rewrite (proj2 H4).
rewrite (MBlockHTranspose Rfield 1 N (S N)).
rewrite (MBlockWTranspose Rfield 1 1 N).
rewrite (MBlockWTranspose Rfield N 1 N).
rewrite (MBlockHWWHSame Rfield 1 N 1 N (fun (_ _ : {n : nat | (n < 1)%nat}) => la)).
rewrite (MBlockHWMult Rfield (S N) 1 N (S N)).
rewrite (MBlockHMult Rfield 1 N 1 (S N)).
rewrite (MBlockHMult Rfield 1 N N (S N)).
rewrite (MBlockWMult Rfield 1 1 1 N).
rewrite (MBlockWMult Rfield N 1 1 N).
rewrite (MBlockWMult Rfield 1 N 1 N).
rewrite (MBlockWMult Rfield N N 1 N).
rewrite (Mmult_O_r Rfield 1 1 N).
rewrite (Mmult_O_r Rfield N 1 N).
rewrite (Mmult_O_r Rfield 1 N 1).
rewrite (Mmult_O_r Rfield N N 1).
rewrite (MTransO Rfield N 1).
rewrite (MTransO Rfield 1 N).
rewrite (Mmult_O_l Rfield 1 N N).
rewrite (Mmult_O_l Rfield N 1 1).
rewrite (MBlockHPlus Rfield 1 N (S N)).
rewrite (MBlockWPlus Rfield 1 1 N).
rewrite (MBlockWPlus Rfield N 1 N).
rewrite (Mplus_comm Rfield 1 1).
rewrite (Mplus_O_l Rfield 1 1).
rewrite (Mplus_O_l Rfield 1 N).
rewrite (Mplus_O_l Rfield N 1).
rewrite (Mplus_O_l Rfield N N).
rewrite (MBlockHWMult Rfield (S N) 1 N (S N)).
rewrite (MBlockHMult Rfield 1 N 1 (S N)).
rewrite (MBlockHMult Rfield 1 N N (S N)).
rewrite (MBlockWMult Rfield 1 1 1 N).
rewrite (MBlockWMult Rfield N 1 1 N).
rewrite (MBlockWMult Rfield 1 N 1 N).
rewrite (MBlockWMult Rfield N N 1 N).
rewrite (Mmult_O_r Rfield 1 1 N).
rewrite (Mmult_O_r Rfield N 1 N).
rewrite (Mmult_O_r Rfield 1 N 1).
rewrite (Mmult_O_r Rfield N N 1).
rewrite (Mmult_O_l Rfield 1 N N).
rewrite (Mmult_O_l Rfield N 1 1).
rewrite (MBlockHPlus Rfield 1 N (S N)).
rewrite (MBlockWPlus Rfield 1 1 N).
rewrite (MBlockWPlus Rfield N 1 N).
rewrite (Mplus_comm Rfield 1 1).
rewrite (Mplus_O_l Rfield 1 1).
rewrite (Mplus_O_l Rfield 1 N).
rewrite (Mplus_O_l Rfield N 1).
rewrite (Mplus_O_l Rfield N N).
rewrite - (proj2 H5).
unfold MDiag.
unfold MBlockH.
unfold MBlockW.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H6.
suff: (x = y).
move=> H7.
rewrite H7.
elim (AddConnectInv 1 N y).
move=> x0.
unfold Mmult.
suff: (exist (Finite (Count 1)) (Full_set {n : nat | (n < 1)%nat}) (CountFinite 1) = FiniteSingleton {n : nat | (n < 1)%nat} (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1))).
move=> H8.
rewrite H8.
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
suff: (Fmul Rfield la 1 = la).
move=> H9.
rewrite H9.
unfold MTranspose.
suff: (Fmul Rfield 1 la = la).
move=> H10.
rewrite H10.
reflexivity.
apply (Fmul_I_l Rfield la).
apply (Fmul_I_r Rfield la).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> m H8.
suff: ((exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1)) = m).
move=> H9.
rewrite H9.
apply (In_singleton (Count 1) m).
apply sig_map.
elim (le_lt_or_eq O (proj1_sig m) (le_0_n (proj1_sig m))).
move=> H9.
elim (le_not_lt 1 (proj1_sig m) H9 (proj2_sig m)).
apply.
move=> m H8.
apply (Full_intro (Count 1) m).
move=> x0.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig x0)).
move=> H8.
reflexivity.
move=> H8.
apply False_ind.
apply H8.
reflexivity.
apply sig_map.
apply H6.
move=> H6.
elim (le_or_lt 1 (proj1_sig x)).
move=> H7.
suff: (match AddConnectInv 1 N x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N x).
move=> x0.
elim.
move=> x0 H8.
elim (le_or_lt 1 (proj1_sig y)).
move=> H9.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H10.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y0)).
move=> H11.
apply False_ind.
apply H6.
rewrite H8.
rewrite H10.
rewrite H11.
reflexivity.
move=> H11.
reflexivity.
apply (proj2 (AddConnectInvNature 1 N) y H9).
move=> H9.
suff: (match AddConnectInv 1 N y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N y).
move=> y0 H10.
reflexivity.
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 N) y H9).
apply (proj2 (AddConnectInvNature 1 N) x H7).
move=> H7.
suff: (match AddConnectInv 1 N x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N x).
move=> x0 H8.
elim (le_or_lt 1 (proj1_sig y)).
move=> H9.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H10.
reflexivity.
apply (proj2 (AddConnectInvNature 1 N) y H9).
move=> H9.
apply False_ind.
apply H6.
suff: (forall (n : nat), (n < 1)%nat -> n = O).
move=> H10.
rewrite (H10 (proj1_sig y) H9).
apply (H10 (proj1_sig x) H7).
move=> n H10.
elim (le_lt_or_eq n 0 (le_S_n n 0 H10)).
move=> H11.
elim (le_not_lt O n (le_0_n n) H11).
apply.
move=> x0.
elim.
apply (proj1 (AddConnectInvNature 1 N) x H7).
exists (fun (x y : {n : nat | (n < N)%nat}) => Mmult Rfield (S N) (S N) (S N) (MTranspose Rfield (S N) (S N) V) (Mmult Rfield (S N) (S N) (S N) A V) (AddConnect 1 N (inr x)) (AddConnect 1 N (inr y))).
exists (Mmult Rfield (S N) (S N) (S N) (MTranspose Rfield (S N) (S N) V) (Mmult Rfield (S N) (S N) (S N) A V) (AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1)))) (AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1))))).
suff: (MSymmetric Rfield (S N) (Mmult Rfield (S N) (S N) (S N) (fun (x0 y0 : {n : nat | (n < S N)%nat}) => V y0 x0) (Mmult Rfield (S N) (S N) (S N) A V))).
move=> H4.
apply conj.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MTranspose.
rewrite - {1} H4.
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
elim (le_or_lt 1 (proj1_sig x)).
move=> H5.
suff: (match AddConnectInv 1 N x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N x).
move=> x0.
elim.
move=> x0 H6.
elim (le_or_lt 1 (proj1_sig y)).
move=> H7.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H8.
suff: (x = AddConnect 1 N (inr x0)).
move=> H9.
suff: (y = AddConnect 1 N (inr y0)).
move=> H10.
rewrite H9.
rewrite H10.
reflexivity.
apply sig_map.
rewrite H8.
apply (proj2 (AddConnectNature 1 N) y0).
apply sig_map.
rewrite H6.
apply (proj2 (AddConnectNature 1 N) x0).
apply (proj2 (AddConnectInvNature 1 N) y H7).
move=> H7.
suff: (match AddConnectInv 1 N y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N y).
move=> y0 H8.
suff: (y = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H9.
rewrite H9.
apply (proj2 H3 x H5).
elim (le_lt_or_eq (proj1_sig y) O (le_S_n (proj1_sig y) O H7)).
move=> H9.
elim (le_not_lt 0 (proj1_sig y) (le_0_n (proj1_sig y)) H9).
move=> H9.
apply sig_map.
apply H9.
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 N) y H7).
apply (proj2 (AddConnectInvNature 1 N) x H5).
move=> H5.
suff: (match AddConnectInv 1 N x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N x).
move=> x0 H6.
elim (le_or_lt 1 (proj1_sig y)).
move=> H7.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H8.
rewrite - H4.
suff: (x = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H9.
rewrite H9.
apply (proj2 H3 y H7).
elim (le_lt_or_eq (proj1_sig x) O (le_S_n (proj1_sig x) O H5)).
move=> H9.
elim (le_not_lt 0 (proj1_sig x) (le_0_n (proj1_sig x)) H9).
move=> H9.
apply sig_map.
apply H9.
apply (proj2 (AddConnectInvNature 1 N) y H7).
move=> H7.
suff: (match AddConnectInv 1 N y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N y).
move=> y0 H8.
suff: (x = AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1)))).
move=> H9.
suff: (y = AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1)))).
move=> H10.
rewrite H9.
rewrite H10.
reflexivity.
apply sig_map.
rewrite H8.
rewrite (proj1 (AddConnectNature 1 N) y0).
suff: (y0 = (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1))).
move=> H10.
rewrite H10.
reflexivity.
apply sig_map.
elim (le_lt_or_eq (proj1_sig y0) O (le_S_n (proj1_sig y0) O (proj2_sig y0))).
move=> H10.
elim (le_not_lt O (proj1_sig y0) (le_0_n (proj1_sig y0)) H10).
apply.
apply sig_map.
rewrite H6.
rewrite (proj1 (AddConnectNature 1 N) x0).
suff: (x0 = (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1))).
move=> H9.
rewrite H9.
reflexivity.
apply sig_map.
elim (le_lt_or_eq (proj1_sig x0) O (le_S_n (proj1_sig x0) O (proj2_sig x0))).
move=> H9.
elim (le_not_lt O (proj1_sig x0) (le_0_n (proj1_sig x0)) H9).
apply.
move=> y0.
elim.
apply (proj1 (AddConnectInvNature 1 N) y H7).
move=> x0.
elim.
apply (proj1 (AddConnectInvNature 1 N) x H5).
unfold MSymmetric.
rewrite (MTransMult Rfield (S N) (S N)).
rewrite (MTransMult Rfield (S N) (S N)).
rewrite H2.
apply (Mmult_assoc Rfield (S N) (S N) (S N)).
suff: (let Aform := fun (u : {n : nat | (n < S N)%nat} -> R) => RnInnerProduct (S N) u (MVmult Rfield (S N) (S N) A u) in exists (V : Matrix Rfield (S N) (S N)), OrthogonalMatrix (S N) V /\ (forall (m : {n : nat | (n < S N)%nat}), (proj1_sig m > 0)%nat -> Mmult Rfield (S N) (S N) (S N) (MTranspose Rfield (S N) (S N) V) (Mmult Rfield (S N) (S N) (S N) A V) m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) = 0)).
apply.
move=> Aform.
suff: (exists (v : {n : nat | (n < S N)%nat} -> R), RnNorm (S N) v = 1 /\ forall (w : {n : nat | (n < S N)%nat} -> R), RnNorm (S N) w = 1 -> Aform w <= Aform v).
elim.
move=> v H3.
suff: (exists (V : Matrix Rfield (S N) (S N)), OrthogonalMatrix (S N) V /\ V (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))) = v).
elim.
move=> V H4.
exists (MTranspose Rfield (S N) (S N) V).
apply conj.
unfold OrthogonalMatrix.
rewrite (MTransTrans Rfield (S N) (S N) V).
suff: (MTranspose Rfield (S N) (S N) V = InvMatrix Rfield (S N) V).
move=> H5.
rewrite H5.
apply (InvMatrixMultR Rfield (S N) V).
apply (proj2 (RegularInvLExistRelation Rfield (S N) V)).
exists (MTranspose Rfield (S N) (S N) V).
apply (proj1 H4).
apply (InvMatrixMultUniqueLStrong Rfield (S N) V (MTranspose Rfield (S N) (S N) V) (proj1 H4)).
suff: (forall (x y : {n : nat | (n < S N)%nat} -> R), RnInnerProduct (S N) x y = Mmult Rfield 1 (S N) 1 (MTranspose Rfield (S N) 1 (MVectorToMatrix Rfield (S N) x)) (MVectorToMatrix Rfield (S N) y) (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1)) (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1))).
move=> H5.
suff: (forall (w : {n : nat | (n < S N)%nat} -> R), Aform w <= Aform v * RnInnerProduct (S N) w w).
move=> H6 m H7.
rewrite (MTransTrans Rfield (S N) (S N) V).
suff: (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) = Aform v).
move=> H8.
suff: (forall (eps : R), Aform v + (1 + 1) * eps * (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N)))) + eps * eps * (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m) <= (1 + eps * eps) * Aform v).
move=> H9.
suff: (forall (eps : R), eps * ((1 + 1) * Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))) + eps * (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m - Aform v)) <= 0).
move=> H10.
elim (Rmult_integral (1 + 1) (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))))).
move=> H11.
apply False_ind.
apply (Rle_not_lt 0 (1 + 1)).
rewrite H11.
right.
reflexivity.
apply (Rlt_trans 0 1 (1 + 1) Rlt_0_1 (Rlt_plus_1 1)).
apply.
elim (Rle_or_lt ((1 + 1) * (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))))) 0).
elim.
move=> H11.
apply False_ind.
elim (Rle_or_lt 0 (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m - Aform v)).
move=> H12.
apply (Rle_not_lt 0 (- 1 * ((1 + 1) * Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m (exist (fun n : nat => (n < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) + (- 1) * (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m - Aform v))) (H10 (- 1))).
rewrite - Rmult_opp_opp.
apply Rmult_lt_0_compat.
rewrite (Ropp_involutive 1).
apply Rlt_0_1.
apply Ropp_gt_lt_0_contravar.
rewrite - (Rplus_0_r 0).
apply Rplus_lt_le_compat.
apply H11.
rewrite - (Rmult_0_l (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m - Aform v)).
apply Rmult_le_compat_r.
apply H12.
apply Rge_le.
apply Ropp_0_le_ge_contravar.
left.
apply Rlt_0_1.
move=> H12.
elim (Proposition_1_1 ((1 + 1) * Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))) 0).
move=> x H13.
apply (Rle_not_lt 0 ((- x / (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m - Aform v)) * ((1 + 1) * Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m (exist (fun n : nat => (n < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) + (- x / (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m - Aform v)) * (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m - Aform v))) (H10 (- x / (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m - Aform v)))).
rewrite - Rmult_opp_opp.
apply Rmult_lt_0_compat.
apply Ropp_gt_lt_0_contravar.
rewrite - (Rmult_0_r (- x)).
apply (Rmult_gt_compat_l (- x)).
apply (Ropp_gt_lt_0_contravar x (proj2 H13)).
apply Rinv_lt_0_compat.
apply H12.
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite (Rmult_1_r (- x)).
apply Ropp_gt_lt_0_contravar.
apply Rlt_minus.
apply (proj1 H13).
apply Rlt_not_eq.
apply H12.
apply H11.
apply.
move=> H11.
apply False_ind.
elim (Rle_or_lt 0 (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m - Aform v)).
move=> H12.
apply (Rle_not_lt 0 (1 * ((1 + 1) * Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m (exist (fun n : nat => (n < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) + 1 * (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m - Aform v))) (H10 1)).
rewrite Rmult_1_l.
rewrite Rmult_1_l.
apply Rplus_lt_le_0_compat.
apply H11.
apply H12.
move=> H12.
elim (Proposition_1_1 0 ((1 + 1) * Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))) H11).
move=> x H13.
apply (Rle_not_lt 0 ((x / (- (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m - Aform v))) * ((1 + 1) * Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))) + (x / (- (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m - Aform v))) * (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m - Aform v))) (H10 (x / (- (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m - Aform v))))).
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
apply (proj1 H13).
apply Rinv_0_lt_compat.
apply Ropp_gt_lt_0_contravar.
apply H12.
unfold Rdiv.
rewrite - Ropp_inv_permute.
rewrite Rmult_assoc.
rewrite Ropp_mult_distr_l_reverse.
rewrite Rinv_l.
rewrite Ropp_mult_distr_r_reverse.
rewrite Rmult_1_r.
apply Rgt_minus.
apply (proj2 H13).
apply Rlt_not_eq.
apply H12.
apply Rlt_not_eq.
apply H12.
move=> eps.
apply (Rplus_le_reg_l ((1 + eps * eps) * Aform v)).
rewrite Rplus_0_r.
rewrite {1} (Rmult_plus_distr_r 1 (eps * eps) (Aform v)).
rewrite Rmult_plus_distr_l.
rewrite (Rmult_1_l (Aform v)).
rewrite - (Rmult_assoc eps eps).
rewrite Rmult_minus_distr_l.
unfold Rminus.
rewrite Rplus_assoc.
rewrite - (Rplus_assoc (eps * ((1 + 1) * Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))))).
rewrite (Rplus_comm (eps * ((1 + 1) * Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))) + eps * eps * Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m)).
rewrite - (Rplus_assoc (eps * eps * Aform v)).
rewrite Rplus_opp_r.
rewrite Rplus_0_l.
rewrite - (Rmult_assoc eps).
rewrite (Rmult_comm eps (1 + 1)).
rewrite - Rplus_assoc.
apply (H9 eps).
move=> eps.
suff: (Aform v + (1 + 1) * eps * Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) + eps * eps * Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m = Aform (MMatrixToVector Rfield (S N) (Mmult Rfield (S N) (S N) 1 (MTranspose Rfield (S N) (S N) V) (MVectorToMatrix Rfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
  | left _ => 1
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => eps
    | right _ => 0
  end
end))))).
move=> H9.
rewrite H9.
rewrite Rmult_comm.
suff: (1 + eps * eps = RnInnerProduct (S N) (MMatrixToVector Rfield (S N) (Mmult Rfield (S N) (S N) 1 (MTranspose Rfield (S N) (S N) V) (MVectorToMatrix Rfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
  | left _ => 1
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => eps
    | right _ => 0
  end
end)))) (MMatrixToVector Rfield (S N) (Mmult Rfield (S N) (S N) 1 (MTranspose Rfield (S N) (S N) V) (MVectorToMatrix Rfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
  | left _ => 1
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => eps
    | right _ => 0
  end
end))))).
move=> H10.
rewrite H10.
apply H6.
rewrite H5.
rewrite (proj2 (MVectorMatrixRelation Rfield (S N))).
rewrite MTransMult.
rewrite Mmult_assoc.
rewrite MTransTrans.
rewrite - (Mmult_assoc Rfield (S N) (S N) (S N) 1 V).
suff: (Mmult Rfield (S N) (S N) (S N) V (MTranspose Rfield (S N) (S N) V) = MI Rfield (S N)).
move=> H10.
rewrite H10.
rewrite Mmult_I_l.
rewrite - H5.
unfold RnInnerProduct.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))))).
rewrite MySumF2Singleton.
simpl.
elim (excluded_middle_informative (O = O)).
move=> H11.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
elim (excluded_middle_informative (proj1_sig m = O)).
move=> H12.
elim (lt_irrefl (proj1_sig m)).
rewrite {1} H12.
apply H7.
move=> H12.
elim (excluded_middle_informative (@eq (Count (S N)) m m)).
move=> H13.
rewrite CM_O_r.
rewrite Rmult_1_l.
reflexivity.
move=> H13.
apply False_ind.
apply H13.
reflexivity.
move=> u.
elim.
move=> u0 H12 H13.
suff: (In (Count (S N)) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H13.
move=> u1 H14 H15 H16.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H17.
elim H14.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H18.
rewrite H18.
apply (In_singleton (Count (S N))).
apply sig_map.
apply H17.
move=> H17.
elim (excluded_middle_informative (u1 = m)).
move=> H18.
elim H16.
rewrite H18.
apply (In_singleton (Count (S N)) m).
move=> H18.
apply (Rmult_0_r 0).
apply H12.
move=> u.
elim.
apply Intersection_intro.
move=> H12.
apply (le_not_lt (proj1_sig m) 0).
elim H12.
apply (le_n O).
apply H7.
apply (Full_intro (Count (S N)) m).
move=> H11.
apply False_ind.
apply H11.
reflexivity.
move=> u H11.
apply (Full_intro (Count (S N)) u).
suff: (MTranspose Rfield (S N) (S N) V = InvMatrix Rfield (S N) V).
move=> H10.
rewrite H10.
apply (InvMatrixMultR Rfield (S N) V).
apply (proj2 (RegularInvLExistRelation Rfield (S N) V)).
exists (MTranspose Rfield (S N) (S N) V).
apply (proj1 H4).
apply (InvMatrixMultUniqueLStrong Rfield (S N) V (MTranspose Rfield (S N) (S N) V) (proj1 H4)).
unfold Aform at 2.
rewrite (H5 (MMatrixToVector Rfield (S N) (Mmult Rfield (S N) (S N) 1 (MTranspose Rfield (S N) (S N) V) (MVectorToMatrix Rfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
  | left _ => 1
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => eps
    | right _ => 0
  end
end))))).
rewrite (proj2 (MVectorMatrixRelation Rfield (S N))).
rewrite MTransMult.
suff: (MVectorToMatrix Rfield (S N) (MVmult Rfield (S N) (S N) A (MMatrixToVector Rfield (S N) (Mmult Rfield (S N) (S N) 1 (MTranspose Rfield (S N) (S N) V) (MVectorToMatrix Rfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
  | left _ => 1
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => eps
    | right _ => 0
  end
end))))) = Mmult Rfield (S N) (S N) 1 A (Mmult Rfield (S N) (S N) 1 (MTranspose Rfield (S N) (S N) V) (MVectorToMatrix Rfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
  | left _ => 1
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => eps
    | right _ => 0
  end
end))) ).
move=> H9.
rewrite H9.
rewrite (Mmult_assoc Rfield 1 (S N) (S N) 1).
rewrite - (Mmult_assoc Rfield (S N) (S N) (S N) 1).
rewrite - (Mmult_assoc Rfield (S N) (S N) (S N) 1 (Mmult Rfield (S N) (S N) (S N) V A)).
unfold Mmult at 5.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))))).
rewrite MySumF2Singleton.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
unfold MVectorToMatrix at 1.
unfold MTranspose at 3.
simpl.
elim (excluded_middle_informative (O = O)).
move=> H10.
unfold MVectorToMatrix at 2.
unfold MTranspose at 4.
elim (excluded_middle_informative (proj1_sig m = O)).
move=> H11.
elim (lt_irrefl (proj1_sig m)).
rewrite {1} H11.
apply H7.
move=> H11.
elim (excluded_middle_informative (@eq (Count (S N)) m m)).
move=> H12.
rewrite Rplus_0_r.
unfold Mmult at 5.
unfold Mmult at 7.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))))).
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))) (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m)).
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m) (FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N))) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))))))).
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite MySumF2O.
unfold MVectorToMatrix.
simpl.
elim (excluded_middle_informative (O = O)).
move=> H13.
elim (excluded_middle_informative (proj1_sig m = O)).
move=> H14.
elim (H11 H14).
move=> H14.
elim (excluded_middle_informative (@eq (Count (S N)) m m)).
move=> H15.
rewrite Rmult_1_l.
rewrite Rmult_1_r.
rewrite Rplus_0_r.
rewrite Rmult_1_r.
rewrite Rplus_0_r.
rewrite - H8.
rewrite (Rmult_assoc (1 + 1)).
rewrite (Rmult_plus_distr_r 1 1).
rewrite Rmult_1_l.
rewrite (Mmult_assoc Rfield (S N) (S N) (S N) (S N) V A).
rewrite (Rplus_assoc (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))) (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) m * eps)).
rewrite (Rmult_comm (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) m) eps).
rewrite (Rmult_comm (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m) eps).
rewrite (Rmult_plus_distr_l eps).
rewrite - (Rmult_assoc eps eps).
rewrite - (Rplus_assoc (eps * Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) m)).
suff: (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) m = Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) ).
move=> H17.
rewrite H17.
rewrite Rplus_assoc.
reflexivity.
suff: (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) = MTranspose Rfield (S N) (S N) (Mmult Rfield (S N) (S N) (S N) V (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)))).
move=> H16.
rewrite {1} H16.
reflexivity.
rewrite MTransMult.
rewrite MTransMult.
rewrite MTransTrans.
rewrite H2.
rewrite (Mmult_assoc Rfield (S N) (S N) (S N) (S N) V A).
reflexivity.
move=> H15.
elim (H15 H12).
move=> H13.
elim (H13 H10).
move=> u.
elim.
move=> u0 H13 H14.
suff: (In (Count (S N)) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H14.
move=> u1 H15 H16 H17.
unfold MVectorToMatrix.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H18.
elim H15.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H19.
rewrite H19.
apply (In_singleton (Count (S N))).
apply sig_map.
apply H18.
move=> H18.
elim (excluded_middle_informative (u1 = m)).
move=> H19.
rewrite H19.
elim H17.
rewrite H19.
apply (In_singleton (Count (S N)) m).
move=> H19.
apply Rmult_0_r.
apply H13.
move=> u.
elim.
move=> u0 H13 H14.
suff: (In (Count (S N)) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H14.
move=> u1 H15 H16 H17.
unfold MVectorToMatrix.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H18.
elim H15.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H19.
rewrite H19.
apply (In_singleton (Count (S N))).
apply sig_map.
apply H18.
move=> H18.
elim (excluded_middle_informative (u1 = m)).
move=> H19.
rewrite H19.
elim H17.
rewrite H19.
apply (In_singleton (Count (S N)) m).
move=> H19.
apply Rmult_0_r.
apply H13.
move=> k H13.
apply Intersection_intro.
elim H13.
move=> H14.
apply H11.
elim H14.
reflexivity.
apply (Full_intro (Count (S N)) k).
move=> u.
elim.
apply Intersection_intro.
move=> H13.
elim H11.
elim H13.
reflexivity.
apply (Full_intro (Count (S N)) m).
move=> u H13.
apply (Full_intro (Count (S N)) u).
move=> u H13.
apply (Full_intro (Count (S N)) u).
move=> H12.
apply False_ind.
apply H12.
reflexivity.
move=> H10.
apply False_ind.
apply H10.
reflexivity.
move=> u.
elim.
move=> u0 H10 H11.
suff: (In (Count (S N)) (Complement (Count (S N)) (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H11.
move=> u1 H12 H13 H14.
unfold MVectorToMatrix.
unfold MTranspose.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H15.
elim H12.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H16.
rewrite H16.
apply (In_singleton (Count (S N))).
apply sig_map.
apply H15.
move=> H15.
elim (excluded_middle_informative (u1 = m)).
move=> H16.
rewrite H16.
elim H14.
rewrite H16.
apply (In_singleton (Count (S N)) m).
move=> H16.
apply Rmult_0_l.
apply H10.
move=> u.
elim.
apply Intersection_intro.
move=> H10.
elim (le_not_lt (proj1_sig m) O).
elim H10.
apply (le_n O).
apply H7.
apply (Full_intro (Count (S N)) m).
move=> u H10.
apply (Full_intro (Count (S N)) u).
unfold MVectorToMatrix.
unfold MMatrixToVector.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
reflexivity.
unfold Aform.
rewrite (H5 v (MVmult Rfield (S N) (S N) A v)).
unfold Mmult at 1.
unfold Mmult at 2.
apply MySumF2Same.
unfold MVmult.
unfold MVectorToMatrix.
unfold MMatrixToVector.
unfold MTranspose.
unfold Mmult.
rewrite (proj2 H4).
reflexivity.
move=> w.
elim (classic (w = RnO (S N))).
move=> H6.
rewrite H6.
rewrite (Proposition_4_2_4_3_R (S N) (RnO (S N))).
rewrite Rmult_0_r.
unfold Aform.
unfold RnInnerProduct.
rewrite MySumF2O.
right.
reflexivity.
move=> u H7.
apply Rmult_0_l.
reflexivity.
move=> H6.
rewrite - (Rmult_1_r (Aform w)).
rewrite - (Rinv_l (RnInnerProduct (S N) w w)).
rewrite - Rmult_assoc.
apply Rmult_le_compat_r.
apply Rge_le.
apply Proposition_4_2_4_1_R.
suff: (Aform w * / RnInnerProduct (S N) w w = Aform (Rnmult (S N) (/ RnNorm (S N) w) w)).
move=> H7.
rewrite H7.
apply H3.
rewrite Proposition_4_4_1_R.
rewrite Rabs_right.
apply Rinv_l.
move=> H8.
apply H6.
apply (Proposition_4_4_3_2_R (S N) w H8).
left.
apply Rinv_0_lt_compat.
elim (Proposition_4_4_3_1_R (S N) w).
apply.
move=> H8.
apply False_ind.
apply H6.
apply (Proposition_4_4_3_2_R (S N) w H8).
rewrite (proj2 (RnNormNature (S N) w)).
unfold Aform.
unfold RnInnerProduct.
apply (FiniteSetInduction (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply Rmult_0_l.
move=> B b H7 H8 H9 H10.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite Rmult_plus_distr_r.
rewrite H10.
apply Rplus_eq_compat_l.
unfold Rnmult.
unfold Fnmul.
simpl.
unfold MVmult.
unfold MMatrixToVector.
unfold MVectorToMatrix.
rewrite (Rmult_comm (/ RnNorm (S N) w) (w b)).
rewrite Rmult_assoc.
rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
rewrite (Rinv_mult_distr (RnNorm (S N) w) (RnNorm (S N) w)).
rewrite Rmult_comm.
rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
rewrite VMmult_assoc_r.
reflexivity.
move=> H11.
apply H6.
apply (Proposition_4_4_3_2_R (S N) w H11).
move=> H11.
apply H6.
apply (Proposition_4_4_3_2_R (S N) w H11).
apply H9.
apply H9.
move=> H7.
apply H6.
apply (Proposition_4_2_4_2_R (S N) w H7).
move=> x y.
reflexivity.
suff: (SubspaceVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)).
move=> H4.
suff: (FiniteDimensionVS Rfield (SubspaceMakeVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4)).
move=> H5.
suff: (exists (B : Count N -> Rn (S N)), BasisSubspaceVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 (Count N) B).
elim.
move=> B H6.
elim (GramSchmidtLinearlyIndepententR (RnVS (S N)) (RnInner_Product_Space (S N)) N B).
move=> W H7.
exists (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => v
  | inr n => W n
end).
apply conj.
suff: (OrthogonalMatrix (S N) (MTranspose Rfield (S N) (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => v
  | inr n => W n
end))).
move=> H8.
unfold OrthogonalMatrix.
suff: (MTranspose Rfield (S N) (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => v
  | inr n => W n
end) = InvMatrix Rfield (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => v
  | inr n => W n
end)).
move=> H9.
rewrite H9.
apply (InvMatrixMultL Rfield (S N)).
apply (proj2 (RegularInvRExistRelation Rfield (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => v
  | inr n => W n
end))).
exists (MTranspose Rfield (S N) (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => v
  | inr n => W n
end)).
apply H8.
apply (InvMatrixMultUniqueRStrong Rfield (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => v
  | inr n => W n
end) (MTranspose Rfield (S N) (S N) (fun (m : Count (S N)) => match AddConnectInv 1 N m with
  | inl _ => v
  | inr n => W n
end)) H8).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H8.
suff: (x = y).
move=> H9.
rewrite H9.
unfold Mmult.
unfold MTranspose.
elim (AddConnectInv 1 N y).
move=> H10.
suff: (FI Rfield = RnInnerProduct (S N) v v).
move=> H11.
rewrite H11.
reflexivity.
rewrite (proj2 (RnNormNature (S N) v)).
rewrite (proj1 H3).
rewrite (Rmult_1_r 1).
reflexivity.
move=> m.
simpl.
rewrite - (proj1 (proj1 H7) m).
simpl.
reflexivity.
apply sig_map.
apply H8.
move=> H8.
suff: (forall (t : Count N), RnInnerProduct (S N) v (W t) = 0).
move=> H9.
unfold Mmult.
unfold MTranspose.
elim (le_or_lt 1 (proj1_sig x)).
move=> H10.
suff: (match AddConnectInv 1 N x return Prop with
  | inl _ => False
  | inr k => proj1_sig x = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N x).
move=> x0.
elim.
move=> x0 H11.
elim (le_or_lt 1 (proj1_sig y)).
move=> H12.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H13.
simpl.
rewrite - (proj2 (proj1 H7) x0 y0).
reflexivity.
move=> H14.
apply H8.
rewrite H13.
rewrite H11.
rewrite H14.
reflexivity.
apply (proj2 (AddConnectInvNature 1 N) y H12).
move=> H12.
suff: (match AddConnectInv 1 N y return Prop with
  | inl k => proj1_sig y = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N y).
move=> y0 H13.
simpl.
rewrite - (H9 x0).
apply (Proposition_4_2_3_R).
move=> H13.
elim.
apply (proj1 (AddConnectInvNature 1 N) y H12).
apply (proj2 (AddConnectInvNature 1 N) x H10).
move=> H10.
suff: (match AddConnectInv 1 N x return Prop with
  | inl k => proj1_sig x = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N x).
move=> x0 H11.
elim (le_or_lt 1 (proj1_sig y)).
move=> H12.
suff: (match AddConnectInv 1 N y return Prop with
  | inl _ => False
  | inr k => proj1_sig y = (1 + proj1_sig k)%nat
end).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
move=> y0 H13.
simpl.
rewrite - (H9 y0).
reflexivity.
apply (proj2 (AddConnectInvNature 1 N) y H12).
move=> H12.
apply False_ind.
apply H8.
suff: (forall (n : nat), (n < 1)%nat -> n = O).
move=> H13.
rewrite (H13 (proj1_sig y) H12).
apply (H13 (proj1_sig x) H10).
move=> n H13.
elim (le_lt_or_eq n O (le_S_n n O H13)).
move=> H14.
elim (le_not_lt O n (le_0_n n) H14).
apply.
move=> x0.
elim.
apply (proj1 (AddConnectInvNature 1 N) x H10).
move=> t.
elim H6.
move=> H9 H10.
suff: (In (Rn (S N)) (SpanVS Rfield (RnVS (S N)) (Count N) B) (W t)).
elim.
move=> a H11.
rewrite H11.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (fun (t0 : Count N) => proj1_sig a t0 <> FO Rfield) (proj2_sig a))).
apply conj.
rewrite MySumF2Empty.
apply (Rip_mult_0_r (RnVS (S N)) (RnInner_Product_Space (S N)) v).
move=> C c H12 H13 H14 H15.
rewrite MySumF2Add.
simpl.
rewrite (Proposition_4_2_1_2_R (S N) v).
rewrite H15.
rewrite (Proposition_4_2_2_2_R (S N)).
rewrite (H9 c).
rewrite Rmult_0_r.
apply Rplus_0_r.
apply H14.
rewrite (proj2 H7).
apply (SpanContainSelfVS Rfield (RnVS (S N)) (Count N) W t).
suff: (match AddConnectInv 1 N (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) return Prop with
  | inl k => proj1_sig (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) = proj1_sig k
  | inr _ => False
end).
elim (AddConnectInv 1 N (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))).
move=> H8 H9.
reflexivity.
move=> H8.
elim.
apply (proj1 (AddConnectInvNature 1 N) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))).
apply (le_n 1).
apply (SubspaceBasisLinearlyIndependentVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 (Count N) B H6).
suff: (DimensionSubspaceVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 H5 = N).
move=> H6.
suff: (exists (B : Count (DimensionSubspaceVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 H5) -> Rn (S N)), BasisSubspaceVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 (Count (DimensionSubspaceVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 H5)) B).
rewrite H6.
apply.
apply (DimensionSubspaceVSNature Rfield (RnVS (S N)) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 H5).
suff: (SubspaceVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v)).
move=> H6.
elim (DimensionSumEnsembleVS2_exists Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H6 H4).
move=> H7 H8.
suff: (FiniteDimensionVS Rfield (SubspaceMakeVS Rfield (RnVS (S N)) (SumEnsembleVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) H7)).
move=> H9.
elim (H8 H9).
move=> H10.
elim.
move=> H11 H12.
apply (plus_reg_l (DimensionSubspaceVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 H5) N 1).
suff: ((1 + N)%nat = DimensionSubspaceVS Rfield (RnVS (S N)) (SumEnsembleVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists f : R, w = Rnmult (S N) f v) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) H7 H9).
move=> H13.
rewrite H13.
suff: (1%nat = DimensionSubspaceVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) H6 H10).
move=> H14.
rewrite H14.
rewrite H12.
suff: (H5 = H11).
move=> H15.
unfold DimensionSubspaceVS.
rewrite H15.
reflexivity.
apply proof_irrelevance.
apply Extensionality_Ensembles.
apply conj.
move=> u.
elim.
move=> u0 H15 H16.
suff: (u0 = RnO (S N)).
move=> H17.
rewrite H17.
apply (In_singleton (Rn (S N)) (RnO (S N))).
elim H15.
move=> c H17.
suff: (c = 0).
move=> H18.
rewrite H17.
rewrite H18.
apply (Vmul_O_l Rfield (RnVS (S N)) v).
suff: (RnInnerProduct (S N) v u0 = 0).
rewrite H17.
rewrite (Proposition_4_2_2_2_R (S N) c v v).
suff: (RnInnerProduct (S N) v v = 1).
move=> H18.
rewrite H18.
rewrite (Rmult_1_r c).
apply.
rewrite (proj2 (RnNormNature (S N) v)).
rewrite (proj1 H3).
apply (Rmult_1_r 1).
apply H16.
move=> u.
elim.
apply (proj2 (proj2 (IntersectionSubspaceVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H6 H4))).
rewrite (DimensionSubspaceVSNature2 Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) H6 H10 1 (fun (m : Count 1) => v)).
reflexivity.
suff: (exists (f : R), v = Rnmult (S N) f v).
move=> H14.
exists (fun (m : Count 1) => H14).
apply (proj2 (BasisLIGeVS Rfield (SubspaceMakeVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) H6) (Count 1) (fun (m : Count 1) => exist (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) v H14))).
apply conj.
apply FiniteLinearlyIndependentVS.
move=> a H15 m.
suff: (MySumF2 (Count 1) (exist (Finite (Count 1)) (Full_set (Count 1)) (CountFinite 1)) (VSPCM Rfield (SubspaceMakeVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) H6)) (fun (n : Count 1) => Vmul Rfield (SubspaceMakeVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) H6) (a n) (exist (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) v H14)) = VO Rfield (SubspaceMakeVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) H6)).
suff: (exist (Finite (Count 1)) (Full_set (Count 1)) (CountFinite 1) = FiniteSingleton (Count 1) m).
move=> H16.
rewrite H16.
rewrite MySumF2Singleton.
move=> H17.
suff: (Rnmult (S N) (a m) v = RnO (S N)).
move=> H18.
elim (Vmul_integral Rfield (RnVS (S N)) (a m) v H18).
apply.
move=> H19.
apply False_ind.
apply R1_neq_R0.
rewrite - (proj1 H3).
apply (Proposition_4_4_3_3_R (S N) v H19).
suff: (Rnmult (S N) (a m) v = proj1_sig (Vmul Rfield (SubspaceMakeVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) H6) (a m) (exist (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) v H14))).
move=> H18.
rewrite H18.
rewrite H17.
reflexivity.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u H16.
suff: (m = u).
move=> H17.
rewrite H17.
apply (In_singleton (Count 1) u).
apply sig_map.
suff: (forall (n : nat), (n < 1)%nat -> n = O).
move=> H17.
rewrite (H17 (proj1_sig u) (proj2_sig u)).
apply (H17 (proj1_sig m) (proj2_sig m)).
move=> n H17.
elim (le_lt_or_eq n O (le_S_n n O H17)).
move=> H18.
elim (le_not_lt O n (le_0_n n) H18).
apply.
move=> u H16.
apply (Full_intro (Count 1) u).
apply H15.
apply Extensionality_Ensembles.
apply conj.
move=> m H15.
elim (proj2_sig m).
move=> c H16.
rewrite FiniteSpanVS.
exists (fun (a : Count 1) => c).
suff: (exist (Finite (Count 1)) (Full_set (Count 1)) (CountFinite 1) = FiniteSingleton (Count 1) (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1))).
move=> H17.
rewrite H17.
rewrite MySumF2Singleton.
apply sig_map.
apply H16.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u H17.
suff: ((exist (fun (n : nat) => (n < 1)%nat) O (le_n 1)) = u).
move=> H18.
rewrite H18.
apply (In_singleton (Count 1) u).
apply sig_map.
elim (le_lt_or_eq (proj1_sig u) O (le_S_n (proj1_sig u) O (proj2_sig u))).
move=> H18.
elim (le_not_lt O (proj1_sig u) (le_0_n (proj1_sig u)) H18).
move=> H18.
rewrite H18.
reflexivity.
move=> u H17.
apply (Full_intro (Count 1) u).
move=> m H15.
apply Full_intro.
exists 1.
unfold Rnmult.
rewrite (Fnmul_I_l Rfield (S N) v).
reflexivity.
suff: (FiniteDimensionVS Rfield (RnVS (S N))).
move=> H13.
suff: (DimensionVS Rfield (RnVS (S N)) H13 = S N).
move=> H14.
elim (DimensionVSNature Rfield (RnVS (S N)) H13).
rewrite H14.
move=> a H15.
unfold DimensionSubspaceVS.
suff: (forall (z : Rn (S N)), In (Rn (S N)) (SumEnsembleVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) z).
move=> H16.
rewrite (DimensionVSNature2 Rfield (SubspaceMakeVS Rfield (RnVS (S N)) (SumEnsembleVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) H7) H9 (S N) (fun (m : Count (S N)) => exist (SumEnsembleVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) (a m) (H16 (a m)))).
reflexivity.
apply (IsomorphicSaveBasisVS Rfield (FnVS Rfield (S N)) (SubspaceMakeVS Rfield (RnVS (S N)) (SumEnsembleVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) H7) (Count (S N)) a (fun (z : Rn (S N)) => exist (SumEnsembleVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) z (H16 z))).
apply conj.
exists (fun (m : (SubspaceMakeVST Rfield (RnVS (S N)) (SumEnsembleVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) H7)) => proj1_sig m).
apply conj.
move=> m.
reflexivity.
move=> m.
apply sig_map.
reflexivity.
apply conj.
move=> x y.
apply sig_map.
reflexivity.
move=> c x.
apply sig_map.
reflexivity.
apply H15.
move=> z.
suff: (z = Rnplus (S N) (Rnmult (S N) (RnInnerProduct (S N) v z) v) (Rnminus (S N) z (Rnmult (S N) (RnInnerProduct (S N) v z) v))).
move=> H16.
rewrite H16.
apply (SumEnsembleVS_intro Rfield (RnVS (S N))).
exists (RnInnerProduct (S N) v z).
reflexivity.
unfold Rnminus.
unfold In.
rewrite (Proposition_4_2_1_2_R (S N)).
suff: (RnInnerProduct (S N) v (Rnopp (S N) (Rnmult (S N) (RnInnerProduct (S N) v z) v)) = Rip (RnVS (S N)) (RnInner_Product_Space (S N)) v (Vopp Rfield (RnVS (S N)) (Rnmult (S N) (RnInnerProduct (S N) v z) v))).
move=> H17.
rewrite H17.
rewrite (Rip_linear_opp_r (RnVS (S N)) (RnInner_Product_Space (S N))).
simpl.
rewrite (Proposition_4_2_2_2_R (S N)).
rewrite (proj2 (RnNormNature (S N) v)).
rewrite (proj1 H3).
rewrite (Rmult_1_l 1).
rewrite Rmult_1_r.
apply Rplus_opp_r.
reflexivity.
unfold Rnminus.
unfold Fnminus.
unfold Rnplus.
unfold Rnmult.
rewrite (Fnadd_comm Rfield (S N) z).
rewrite - (Fnadd_assoc Rfield (S N)).
rewrite (Fnadd_opp_r Rfield (S N)).
rewrite (Fnadd_O_l Rfield (S N) z).
reflexivity.
elim (FnVSDimension Rfield (S N)).
move=> H14 H15.
suff: (H13 = H14).
move=> H16.
rewrite H16.
rewrite H15.
reflexivity.
apply proof_irrelevance.
apply (FnVSFiniteDimension Rfield (S N)).
apply (Proposition_5_9_1_1 Rfield (RnVS (S N))).
apply (FnVSFiniteDimension Rfield (S N)).
apply conj.
move=> x y.
elim.
move=> c1 H6.
elim.
move=> c2 H7.
exists (c1 + c2).
rewrite H6.
rewrite H7.
rewrite - (Vmul_add_distr_r Rfield (RnVS (S N)) c1 c2 v).
reflexivity.
apply conj.
move=> f x.
elim.
move=> c H6.
exists (f * c).
rewrite H6.
apply (Vmul_assoc Rfield (RnVS (S N))).
exists 0.
rewrite - (Vmul_O_l Rfield (RnVS (S N)) v).
reflexivity.
apply (Proposition_5_9_1_1 Rfield (RnVS (S N))).
apply (FnVSFiniteDimension Rfield (S N)).
apply conj.
move=> x y H4 H5.
unfold In.
rewrite (Proposition_4_2_1_2_R (S N) v x y).
rewrite H4.
rewrite H5.
apply (Rplus_0_r 0).
apply conj.
move=> f x H4.
unfold In.
rewrite (Proposition_4_2_2_2_R (S N) f v x).
rewrite H4.
apply (Rmult_0_r f).
apply (Rip_mult_0_r (RnVS (S N)) (RnInner_Product_Space (S N)) v).
elim (Theorem_7_3_2_1 (Rn_met (S N)) Aform (fun (x : Rn (S N)) => RnInnerProduct (S N) x x = 1)).
move=> z H3.
suff: (forall (y : R), In R (Im (Base (Rn_met (S N))) R (fun (x : Rn (S N)) => RnInnerProduct (S N) x x = 1) Aform) y -> y <= z).
elim (proj1 H3).
move=> x H4 y H5 H6.
exists x.
apply conj.
apply (RnNormNature2 (S N) x).
apply conj.
left.
apply Rlt_0_1.
rewrite (Rmult_1_r 1).
apply H4.
move=> w H7.
rewrite - H5.
apply (H6 (Aform w)).
apply (Im_intro (Base (Rn_met (S N))) R (fun (x0 : Rn (S N)) => RnInnerProduct (S N) x0 x0 = 1) Aform w).
unfold In.
rewrite (proj2 (RnNormNature (S N) w)).
rewrite H7.
apply (Rmult_1_r 1).
reflexivity.
apply (proj2 H3).
apply (Inhabited_intro (Base (Rn_met (S N))) (fun (x : Rn (S N)) => RnInnerProduct (S N) x x = 1) (fun (m : Count (S N)) => match excluded_middle_informative (m = exist (fun (k : nat) => (k < S N)%nat) O (le_n_S O N (le_0_n N))) with
  | left _ => 1
  | right _ => 0
end)).
unfold In.
unfold RnInnerProduct.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (k : nat) => (k < S N)%nat) O (le_n_S O N (le_0_n N))))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
elim (excluded_middle_informative (@eq (Count (S N)) (exist (fun (k : nat) => (k < S N)%nat) O (le_n_S 0 N (le_0_n N))) (exist (fun (k : nat) => (k < S N)%nat) O (le_n_S 0 N (le_0_n N))))).
move=> H3.
rewrite (Rmult_1_r 1).
apply (CM_O_r RPCM 1).
elim.
reflexivity.
move=> u.
elim.
move=> u0 H3 H4.
elim (excluded_middle_informative (@eq (Count (S N)) u0 (exist (fun (k : nat) => (k < S N)%nat) O (le_n_S 0 N (le_0_n N))))).
move=> H5.
elim H3.
rewrite H5.
apply (In_singleton (Count (S N))).
move=> H5.
apply (Rmult_0_r 0).
move=> m H3.
apply (Full_intro (Count (S N)) m).
suff: (forall (m : Count (S N)) (a : Base (Rn_met (S N))), ContinuousMet (Rn_met (S N)) R_met (fun (x : Base (Rn_met (S N))) => x m) (Full_set (Base (Rn_met (S N)))) a).
move=> H3 x H4.
unfold Aform.
unfold RnInnerProduct.
suff: (forall (m : Count (S N)), ContinuousMet (Rn_met (S N)) R_met (fun (r : Base (Rn_met (S N))) => MySumF2 {n : nat | (n < S N)%nat} (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N))) (FPCM Rfield) (fun (n : Count (S N)) => Fmul Rfield (A m n) (r n))) (Full_set (Base (Rn_met (S N)))) x).
move=> H5.
apply (FiniteSetInduction (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N)))).
apply conj.
move=> eps H6.
exists 1.
apply conj.
apply Rlt_0_1.
move=> y H7.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite (proj2 (R_dist_refl 0 0)).
apply H6.
reflexivity.
move=> B b H6 H7 H8 H9.
suff: (forall (eps : R), eps > 0 -> exists (alp : R), alp > 0 /\ (forall (x0 : Base (Rn_met (S N))), Full_set (Base (Rn_met (S N))) x0 /\ dist (Rn_met (S N)) x0 x < alp -> dist R_met (CMc RPCM (MySumF2 (Count (S N)) B RPCM (fun n : Count (S N) => x0 n * MVmult Rfield (S N) (S N) A x0 n)) (x0 b * MVmult Rfield (S N) (S N) A x0 b)) (CMc RPCM (MySumF2 (Count (S N)) B RPCM (fun n : Count (S N) => x n * MVmult Rfield (S N) (S N) A x n)) (x b * MVmult Rfield (S N) (S N) A x b)) < eps)).
move=> H10 eps H11.
elim (H10 eps H11).
move=> alp H12.
exists alp.
apply conj.
apply (proj1 H12).
move=> x0.
rewrite MySumF2Add.
rewrite MySumF2Add.
apply (proj2 H12).
apply H8.
apply H8.
apply Theorem_6_6_3_1_R.
apply H9.
apply Theorem_6_6_3_5_R.
apply H3.
apply (H5 b).
move=> m.
apply (FiniteSetInduction {n : nat | (n < S N)%nat} (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
apply conj.
move=> eps H5.
exists 1.
apply conj.
apply Rlt_0_1.
move=> y H6.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite (proj2 (R_dist_refl 0 0)).
apply H5.
reflexivity.
move=> B b H5 H6 H7 H8.
suff: ((fun (r : Base (Rn_met (S N))) => MySumF2 {n : nat | (n < S N)%nat} (FiniteAdd {n : nat | (n < S N)%nat} B b) (FPCM Rfield) (fun n : Count (S N) => Fmul Rfield (A m n) (r n))) = (fun (r : Base (Rn_met (S N))) => MySumF2 {n : nat | (n < S N)%nat} B (FPCM Rfield) (fun n : Count (S N) => Fmul Rfield (A m n) (r n)) + (A m b) * (r b))).
move=> H12.
rewrite H12.
apply Theorem_6_6_3_1_R.
apply H8.
apply Theorem_6_6_3_3_R.
apply H3.
apply functional_extensionality.
move=> r.
apply MySumF2Add.
apply H7.
move=> m a eps H3.
exists eps.
apply conj.
apply H3.
move=> x.
unfold dist.
unfold R_met.
unfold Rn_met.
unfold Rn_dist.
unfold R_dist.
simpl.
move=> H4.
apply (Rle_lt_trans (Rabs (x m - a m)) (RnNorm (S N) (Rnminus (S N) x a)) eps).
suff: (Rabs (x m - a m) * Rabs (x m - a m) <= RnNorm (S N) (Rnminus (S N) x a) * RnNorm (S N) (Rnminus (S N) x a)).
move=> H5.
apply Rnot_lt_le.
move=> H6.
apply (Rle_not_lt (RnNorm (S N) (Rnminus (S N) x a) * RnNorm (S N) (Rnminus (S N) x a)) (Rabs (x m - a m) * Rabs (x m - a m)) H5).
apply Rmult_le_0_lt_compat.
apply Rge_le.
apply (proj1 (RnNormNature (S N) (Rnminus (S N) x a))).
apply Rge_le.
apply (proj1 (RnNormNature (S N) (Rnminus (S N) x a))).
apply H6.
apply H6.
suff: (Rabs (x m - a m) * Rabs (x m - a m) = (x m - a m) * (x m - a m)).
move=> H5.
rewrite H5.
rewrite - (Rplus_0_r ((x m - a m) * (x m - a m))).
rewrite - (proj2 (RnNormNature (S N) (Rnminus (S N) x a))).
unfold RnInnerProduct.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m)).
rewrite MySumF2Singleton.
apply Rplus_le_compat_l.
apply MySumF2Induction.
apply conj.
right.
reflexivity.
move=> cm u H6 H7.
apply Rplus_le_le_0_compat.
apply H7.
apply Rle_0_sqr.
move=> u H6.
apply (Full_intro (Count (S N)) u).
unfold Rabs.
elim (Rcase_abs (x m - a m)).
move=> H5.
apply Rmult_opp_opp.
move=> H5.
reflexivity.
apply (proj2 H4).
apply (Theorem_7_2_2_2 (S N)).
apply conj.
exists (RnO (S N)).
exists (1 + 1).
move=> x H3.
unfold In.
unfold NeighborhoodMet.
suff: (dist (Rn_met (S N)) x (RnO (S N)) = 1).
move=> H4.
rewrite H4.
apply Rlt_plus_1.
apply (RnNormNature2 (S N)).
apply conj.
left.
apply Rlt_0_1.
suff: (Rnminus (S N) x (RnO (S N)) = x).
move=> H4.
rewrite H4.
rewrite (Rmult_1_r 1).
apply H3.
apply functional_extensionality.
move=> m.
apply Rminus_0_r.
apply (proj2 (Proposition_7_1_2 (Rn_met (S N)) (fun (x : Rn (S N)) => RnInnerProduct (S N) x x = 1))).
move=> x H3.
elim (Rle_or_lt (Rn_dist (S N) x (RnO (S N))) 1).
elim.
move=> H4.
exists (1 - Rn_dist (S N) x (RnO (S N))).
apply conj.
apply Rgt_minus.
apply H4.
move=> u H5.
suff: (Rn_dist (S N) u (RnO (S N)) < 1).
move=> H6 H7.
apply (Rlt_not_eq (Rn_dist (S N) u (RnO (S N))) 1 H6).
apply RnNormNature2.
apply conj.
left.
apply Rlt_0_1.
suff: (Rnminus (S N) u (RnO (S N)) = u).
move=> H8.
rewrite H8.
rewrite (Rmult_1_r 1).
apply H7.
apply functional_extensionality.
move=> m.
apply Rminus_0_r.
apply (Rle_lt_trans (Rn_dist (S N) u (RnO (S N))) (dist (Rn_met (S N)) u x + Rn_dist (S N) x (RnO (S N))) 1).
apply (Rn_dist_tri (S N)).
rewrite - (Rplus_0_r 1).
rewrite - (Rplus_opp_l (Rn_dist (S N) x (RnO (S N)))).
rewrite - Rplus_assoc.
apply Rplus_lt_compat_r.
apply H5.
move=> H4.
elim H3.
unfold In.
rewrite (proj2 (RnNormNature (S N) x)).
suff: (Rnminus (S N) x (RnO (S N)) = x).
move=> H5.
rewrite - H5.
suff: (RnNorm (S N) (Rnminus (S N) x (RnO (S N))) = 1).
move=> H6.
rewrite H6.
apply (Rmult_1_r 1).
apply H4.
apply functional_extensionality.
move=> m.
apply Rminus_0_r.
move=> H4.
exists (Rn_dist (S N) x (RnO (S N)) - 1).
apply conj.
apply Rgt_minus.
apply H4.
move=> u H5.
suff: (Rn_dist (S N) u (RnO (S N)) > 1).
move=> H6 H7.
apply (Rgt_not_eq (Rn_dist (S N) u (RnO (S N))) 1 H6).
apply RnNormNature2.
apply conj.
left.
apply Rlt_0_1.
suff: (Rnminus (S N) u (RnO (S N)) = u).
move=> H8.
rewrite H8.
rewrite (Rmult_1_r 1).
apply H7.
apply functional_extensionality.
move=> m.
apply Rminus_0_r.
apply (Rlt_le_trans 1 (Rn_dist (S N) x (RnO (S N)) - dist (Rn_met (S N)) u x) (Rn_dist (S N) u (RnO (S N)))).
rewrite - (Rplus_0_r 1).
rewrite - (Rplus_opp_r (dist (Rn_met (S N)) u x)).
rewrite - Rplus_assoc.
apply Rplus_lt_compat_r.
rewrite Rplus_comm.
rewrite - (Rplus_0_r (Rn_dist (S N) x (RnO (S N)))).
rewrite - (Rplus_opp_l 1).
rewrite - Rplus_assoc.
apply Rplus_lt_compat_r.
apply H5.
rewrite - (Rplus_0_r (Rn_dist (S N) u (RnO (S N)))).
rewrite - (Rplus_opp_r (dist (Rn_met (S N)) u x)).
rewrite - Rplus_assoc.
apply Rplus_le_compat_r.
rewrite Rplus_comm.
rewrite dist_sym.
apply (Rn_dist_tri (S N) x (RnO (S N)) u).
Qed.

Definition HermitianMatrixRCTransformableToDiag : forall (K : RC) (N : nat) (A : Matrix (RCfield K) N N), HermitianMatrixRC K N A -> exists (V : Matrix (RCfield K) N N) (D : RCn K N), UnitaryMatrixRC K N V /\ MDiag (RCfield K) N D = Mmult (RCfield K) N N N (AdjointMatrixRC K N N V) (Mmult (RCfield K) N N N A V) := fun (K : RC) => match K with
  | RK => SymmetricTransformableToDiag
  | CK => HermitianMatrixTransformableToDiag
end.

Definition UpperTriangularMatrix (f : Field) (M N : nat) (A : Matrix f M N) := forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}), (proj1_sig x > proj1_sig y)%nat -> A x y = FO f.

Definition UpperTriangularMatrixStrong (f : Field) (M N : nat) (A : Matrix f M N) := forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}), A x y <> FO f -> forall (z : {n : nat | (n < M)%nat}), (proj1_sig z < proj1_sig x)%nat -> exists (w : {n : nat | (n < N)%nat}), (proj1_sig w < proj1_sig y)%nat /\ A z w <> FO f.

Lemma UpperTriangularMatrixStrongUpperTriangular : forall (f : Field) (M N : nat) (A : Matrix f M N), UpperTriangularMatrixStrong f M N A -> UpperTriangularMatrix f M N A.
Proof.
move=> f M N A H1.
unfold UpperTriangularMatrix.
suff: (forall (m : nat), (m <= N)%nat -> forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}), (proj1_sig y < m)%nat -> (proj1_sig x > proj1_sig y)%nat -> A x y = FO f).
move=> H2 x y H3.
apply (H2 N (le_n N) x y (proj2_sig y) H3).
elim.
move=> H2 x y H3.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) H3).
move=> n H2 H3 x y H4 H5.
elim (le_lt_or_eq (proj1_sig y) n (le_S_n (proj1_sig y) n H4)).
move=> H6.
apply (H2 (le_trans n (S n) N (le_S n n (le_n n)) H3) x y H6 H5).
move=> H6.
apply NNPP.
move=> H7.
suff: (exists (xpre : {n : nat | (n < M)%nat}), proj1_sig x = S (proj1_sig xpre)).
elim.
move=> xpre H8.
elim (H1 x y H7 xpre).
move=> y0 H9.
apply (proj2 H9).
apply (H2 (le_trans n (S n) N (le_S n n (le_n n)) H3) xpre y0).
rewrite - H6.
apply (proj1 H9).
apply (le_trans (S (proj1_sig y0)) (proj1_sig y) (proj1_sig xpre)).
apply (proj1 H9).
apply (le_S_n (proj1_sig y) (proj1_sig xpre)).
rewrite - H8.
apply H5.
rewrite H8.
apply (le_n (S (proj1_sig xpre))).
suff: (forall (w z : nat), (w > z)%nat -> exists (prew : nat), w = S prew).
move=> H8.
elim (H8 (proj1_sig x) (proj1_sig y) H5).
move=> prew H9.
suff: (prew < M)%nat.
move=> H10.
exists (exist (fun (k : nat) => (k < M)%nat) prew H10).
apply H9.
apply (le_trans (S prew) (S (proj1_sig x)) M).
rewrite H9.
apply (le_S (S prew) (S prew) (le_n (S prew))).
apply (proj2_sig x).
elim.
move=> z H8.
elim (le_not_lt O z (le_0_n z) H8).
move=> w0 H8 z H9.
exists w0.
reflexivity.
Qed.

Definition UpperTriangularNormalFormRC (K : RC) (M N : nat) (A : Matrix (RCfield K) M N) := UpperTriangularMatrixStrong (RCfield K) M N A /\ forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}), (forall (z : {n : nat | (n < N)%nat}), (proj1_sig y > proj1_sig z)%nat -> A x z = RCO K) -> RCsemipos K (A x y).

Definition UpperTriangularNormalFormR (M N : nat) (A : Matrix Rfield M N) := UpperTriangularMatrixStrong Rfield M N A /\ forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}), (forall (z : {n : nat | (n < N)%nat}), (proj1_sig y > proj1_sig z)%nat -> A x z = 0) -> A x y >= 0.

Definition UpperTriangularNormalFormC (M N : nat) (A : Matrix Cfield M N) := UpperTriangularMatrixStrong Cfield M N A /\ forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}), (forall (z : {n : nat | (n < N)%nat}), (proj1_sig y > proj1_sig z)%nat -> A x z = CO) -> (A x y CRe >= 0 /\ A x y CIm = 0).

Lemma UpperTriangularNormalFormCholeskyR : forall (M N : nat) (A B : Matrix Rfield M N), UpperTriangularNormalFormR M N A -> UpperTriangularNormalFormR M N B -> Mmult Rfield N M N (MTranspose Rfield M N A) A = Mmult Rfield N M N (MTranspose Rfield M N B) B -> A = B.
Proof.
elim.
move=> N A B H1 H2 H3.
apply functional_extensionality.
move=> x.
elim (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) (proj2_sig x)).
move=> M H1.
elim.
move=> A B H2 H3 H4.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) (proj2_sig y)).
move=> N H2 A B H3 H4 H5.
elim (classic (Mmult Rfield (S N) (S M) (S N) (MTranspose Rfield (S M) (S N) A) A (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = 0)).
move=> H6.
suff: (forall (D : Matrix Rfield (S M) (S N)), UpperTriangularNormalFormR (S M) (S N) D -> (Mmult Rfield (S N) (S M) (S N) (MTranspose Rfield (S M) (S N) D) D (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = 0) -> forall (m : {n : nat | (n < S M)%nat}), D m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = 0).
move=> H7.
suff: (forall (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < 1)%nat}), A m (AddConnect 1 N (inl k)) = 0).
move=> H8.
suff: (forall (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < 1)%nat}), B m (AddConnect 1 N (inl k)) = 0).
move=> H9.
suff: ((fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) => A m (AddConnect 1 N (inr k))) = (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) => B m (AddConnect 1 N (inr k)))).
move=> H10.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite - (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0.
rewrite (H9 x y0).
apply (H8 x y0).
move=> y0.
suff: (A x (AddConnect 1 N (inr y0)) = let temp := (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) => A m (AddConnect 1 N (inr k))) in temp x y0).
move=> H11.
rewrite H11.
rewrite H10.
reflexivity.
reflexivity.
apply H2.
apply conj.
move=> x y H10 z H11.
elim (proj1 H3 x (AddConnect 1 N (inr y)) H10 z).
move=> w.
rewrite - (proj2 (AddConnectInvRelation 1 N) w).
elim (AddConnectInv 1 N w).
move=> w0 H12.
elim (proj2 H12 (H8 z w0)).
move=> w0 H12.
exists w0.
apply conj.
apply (plus_lt_reg_l (proj1_sig w0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) w0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply (proj1 H12).
apply (proj2 H12).
apply H11.
move=> x y H10.
apply (proj2 H3 x (AddConnect 1 N (inr y))).
move=> z.
rewrite - (proj2 (AddConnectInvRelation 1 N) z).
elim (AddConnectInv 1 N z).
move=> z0 H11.
apply (H8 x z0).
move=> z0 H11.
apply (H10 z0).
apply (plus_lt_reg_l (proj1_sig z0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) z0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply H11.
apply conj.
move=> x y H10 z H11.
elim (proj1 H4 x (AddConnect 1 N (inr y)) H10 z).
move=> w.
rewrite - (proj2 (AddConnectInvRelation 1 N) w).
elim (AddConnectInv 1 N w).
move=> w0 H12.
elim (proj2 H12 (H9 z w0)).
move=> w0 H12.
exists w0.
apply conj.
apply (plus_lt_reg_l (proj1_sig w0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) w0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply (proj1 H12).
apply (proj2 H12).
apply H11.
move=> x y H10.
apply (proj2 H4 x (AddConnect 1 N (inr y))).
move=> z.
rewrite - (proj2 (AddConnectInvRelation 1 N) z).
elim (AddConnectInv 1 N z).
move=> z0 H11.
apply (H9 x z0).
move=> z0 H11.
apply (H10 z0).
apply (plus_lt_reg_l (proj1_sig z0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) z0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply H11.
suff: (forall (D : Matrix Rfield (S M) (S N)), (forall (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < 1)%nat}), D m (AddConnect 1 N (inl k)) = 0) -> Mmult Rfield N (S M) N (MTranspose Rfield (S M) N (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) => D m (AddConnect 1 N (inr k)))) (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) => D m (AddConnect 1 N (inr k))) = (fun (x y : {n : nat | (n < N)%nat}) => Mmult Rfield (S N) (S M) (S N) (MTranspose Rfield (S M) (S N) D) D (AddConnect 1 N (inr x)) (AddConnect 1 N (inr y)))).
move=> H10.
rewrite (H10 A H8).
rewrite (H10 B H9).
rewrite H5.
reflexivity.
move=> D H10.
suff: (D = MBlockW Rfield (S M) 1 N (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < 1)%nat}) => D m (AddConnect 1 N (inl k))) (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) => D m (AddConnect 1 N (inr k)))).
move=> H11.
rewrite {4} H11.
rewrite {3} H11.
rewrite (MBlockWTranspose Rfield (S M) 1 N).
rewrite (MBlockHMult Rfield 1 N (S M) (S N)).
rewrite (MBlockWMult Rfield N (S M) 1 N).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
rewrite (proj1 (AddConnectInvRelation 1 N) (inr x)).
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 N) (inr y)).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockW.
rewrite - {1} (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0.
reflexivity.
move=> y0.
reflexivity.
move=> m k.
suff: (AddConnect 1 N (inl k) = (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N)))).
move=> H9.
rewrite H9.
apply (H7 B H4).
rewrite - H5.
apply H6.
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 N) k).
elim (le_lt_or_eq (proj1_sig k) O (le_S_n (proj1_sig k) O (proj2_sig k))).
move=> H9.
elim (le_not_lt O (proj1_sig k) (le_0_n (proj1_sig k)) H9).
apply.
move=> m k.
suff: (AddConnect 1 N (inl k) = (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N)))).
move=> H8.
rewrite H8.
apply (H7 A H3).
apply H6.
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 N) k).
elim (le_lt_or_eq (proj1_sig k) O (le_S_n (proj1_sig k) O (proj2_sig k))).
move=> H8.
elim (le_not_lt O (proj1_sig k) (le_0_n (proj1_sig k)) H8).
apply.
move=> D H7 H8.
suff: (forall (m : {n : nat | (n < S M)%nat}), (proj1_sig m > O)%nat -> D m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = 0).
move=> H9 m.
elim (le_lt_or_eq O (proj1_sig m) (le_0_n (proj1_sig m))).
move=> H10.
apply (H9 m H10).
move=> H10.
suff: (D m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) * D m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = 0).
move=> H11.
elim (Rmult_integral (D m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N)))) (D m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N)))) H11).
apply.
apply.
rewrite - H8.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < S M)%nat} (FiniteSingleton {n : nat | (n < S M)%nat} m)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
reflexivity.
move=> u.
elim.
move=> u0 H11 H12.
unfold MTranspose.
rewrite (H9 u0).
apply (Rmult_0_r 0).
elim (le_lt_or_eq O (proj1_sig u0) (le_0_n (proj1_sig u0))).
apply.
move=> H13.
elim H11.
suff: (m = u0).
move=> H14.
rewrite H14.
apply In_singleton.
apply sig_map.
rewrite - H10.
apply H13.
move=> u H11.
apply (Full_intro {n : nat | (n < S M)%nat} u).
move=> m H9.
apply (UpperTriangularMatrixStrongUpperTriangular Rfield (S M) (S N) D (proj1 H7)).
apply H9.
move=> H6.
suff: (forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < 1)%nat}), A (AddConnect 1 M (inr x)) (AddConnect 1 N (inl y)) = 0).
move=> H7.
suff: (forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < 1)%nat}), B (AddConnect 1 M (inr x)) (AddConnect 1 N (inl y)) = 0).
move=> H8.
suff: (forall (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}), A (AddConnect 1 M (inl x)) y = B (AddConnect 1 M (inl x)) y).
move=> H9.
suff: ((fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => A (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y))) = (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => B (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y)))).
move=> H10.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite - (proj2 (AddConnectInvRelation 1 M) x).
elim (AddConnectInv 1 M x).
move=> x0.
apply (H9 x0 y).
move=> x0.
rewrite - (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0.
rewrite (H8 x0 y0).
apply (H7 x0 y0).
move=> y0.
suff: (A (AddConnect 1 M (inr x0)) (AddConnect 1 N (inr y0)) = let temp := (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => A (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y))) in temp x0 y0).
move=> H11.
rewrite H11.
rewrite H10.
reflexivity.
reflexivity.
apply (H1 N).
apply conj.
move=> x y H10 z H11.
elim (proj1 H3 (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y)) H10 (AddConnect 1 M (inr z))).
move=> w.
rewrite - (proj2 (AddConnectInvRelation 1 N) w).
elim (AddConnectInv 1 N w).
move=> w0 H12.
elim (proj2 H12 (H7 z w0)).
move=> w0 H12.
exists w0.
apply conj.
apply (plus_lt_reg_l (proj1_sig w0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) w0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply (proj1 H12).
apply (proj2 H12).
rewrite - (proj2 (AddConnectNature 1 M) z).
rewrite - (proj2 (AddConnectNature 1 M) x).
apply (plus_lt_compat_l (proj1_sig z) (proj1_sig x) 1 H11).
move=> x y H10.
apply (proj2 H3 (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y))).
move=> z.
rewrite - (proj2 (AddConnectInvRelation 1 N) z).
elim (AddConnectInv 1 N z).
move=> z0 H11.
apply (H7 x z0).
move=> z0 H11.
apply (H10 z0).
apply (plus_lt_reg_l (proj1_sig z0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) z0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply H11.
apply conj.
move=> x y H10 z H11.
elim (proj1 H4 (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y)) H10 (AddConnect 1 M (inr z))).
move=> w.
rewrite - (proj2 (AddConnectInvRelation 1 N) w).
elim (AddConnectInv 1 N w).
move=> w0 H12.
elim (proj2 H12 (H8 z w0)).
move=> w0 H12.
exists w0.
apply conj.
apply (plus_lt_reg_l (proj1_sig w0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) w0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply (proj1 H12).
apply (proj2 H12).
rewrite - (proj2 (AddConnectNature 1 M) z).
rewrite - (proj2 (AddConnectNature 1 M) x).
apply (plus_lt_compat_l (proj1_sig z) (proj1_sig x) 1 H11).
move=> x y H10.
apply (proj2 H4 (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y))).
move=> z.
rewrite - (proj2 (AddConnectInvRelation 1 N) z).
elim (AddConnectInv 1 N z).
move=> z0 H11.
apply (H8 x z0).
move=> z0 H11.
apply (H10 z0).
apply (plus_lt_reg_l (proj1_sig z0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) z0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply H11.
suff: (forall (D : Matrix Rfield (S M) (S N)), (forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < 1)%nat}), D (AddConnect 1 M (inr x)) (AddConnect 1 N (inl y)) = 0) -> Mmult Rfield N M N (MTranspose Rfield M N (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => D (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y)))) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => D (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y))) = (fun (x y : {n : nat | (n < N)%nat}) => Mmult Rfield (S N) M (S N) (MTranspose Rfield M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inr x)) y) (AddConnect 1 N (inr x)) (AddConnect 1 N (inr y)))).
move=> H10.
rewrite (H10 A H7).
rewrite (H10 B H8).
suff: (Mmult Rfield (S N) M (S N) (MTranspose Rfield M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inr x)) y) = Mmult Rfield (S N) M (S N) (MTranspose Rfield M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => B (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => B (AddConnect 1 M (inr x)) y)).
move=> H11.
rewrite H11.
reflexivity.
rewrite - (Mplus_O_l Rfield (S N) (S N) (Mmult Rfield (S N) M (S N) (MTranspose Rfield M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inr x)) y))).
rewrite - (Mplus_O_l Rfield (S N) (S N) (Mmult Rfield (S N) M (S N) (MTranspose Rfield M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => B (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => B (AddConnect 1 M (inr x)) y))).
rewrite - (Mplus_opp_r Rfield (S N) (S N) (Mmult Rfield (S N) 1 (S N) (MTranspose Rfield 1 (S N) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y)) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y))).
rewrite (Mplus_comm Rfield (S N) (S N) (Mmult Rfield (S N) 1 (S N) (MTranspose Rfield 1 (S N) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y)) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y))).
rewrite Mplus_assoc.
rewrite Mplus_assoc.
suff: (Mplus Rfield (S N) (S N) (Mmult Rfield (S N) 1 (S N) (MTranspose Rfield 1 (S N) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y)) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y)) (Mmult Rfield (S N) M (S N) (MTranspose Rfield M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inr x)) y)) = Mplus Rfield (S N) (S N) (Mmult Rfield (S N) 1 (S N) (MTranspose Rfield 1 (S N) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y)) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y)) (Mmult Rfield (S N) M (S N) (MTranspose Rfield M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => B (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => B (AddConnect 1 M (inr x)) y))).
move=> H11.
rewrite H11.
reflexivity.
suff: ((fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y) = (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => B (AddConnect 1 M (inl x)) y)).
move=> H12.
rewrite {3} H12.
rewrite {3} H12.
suff: (forall (D : Matrix Rfield (S M) (S N)), Mplus Rfield (S N) (S N) (Mmult Rfield (S N) 1 (S N) (MTranspose Rfield 1 (S N) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inl x)) y)) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inl x)) y)) (Mmult Rfield (S N) M (S N) (MTranspose Rfield M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inr x)) y)) = Mmult Rfield (S N) (S M) (S N) (MTranspose Rfield (S M) (S N) D) D).
move=> H13.
rewrite (H13 A).
rewrite (H13 B).
apply H5.
move=> D.
suff: (D = MBlockH Rfield 1 M (S N) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inl x)) y) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inr x)) y)).
move=> H13.
rewrite {5} H13.
rewrite {7} H13.
rewrite (MBlockHTranspose Rfield 1 M (S N)).
rewrite (MBlockHWMult Rfield (S N) 1 M (S N)).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
rewrite - {1} (proj2 (AddConnectInvRelation 1 M) x).
elim (AddConnectInv 1 M x).
move=> x0.
reflexivity.
move=> x0.
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply (H9 x y).
move=> D H10.
suff: ((fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inr x)) y) = MBlockW Rfield M 1 N (MO Rfield M 1) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => D (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y)))).
move=> H11.
rewrite H11.
rewrite (MBlockWTranspose Rfield M 1 N).
rewrite (MBlockHMult Rfield 1 N M (S N)).
rewrite (MBlockWMult Rfield N M 1 N).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 N) (inr x)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inr y)).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockW.
rewrite - {1} (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0.
apply (H10 x y0).
move=> y0.
reflexivity.
suff: (forall (D : Matrix Rfield (S M) (S N)), UpperTriangularNormalFormR (S M) (S N) D -> (forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < 1)%nat}), D (AddConnect 1 M (inr x)) (AddConnect 1 N (inl y)) = 0) -> forall (x y : {n : nat | (n < 1)%nat}), D (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) * D (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) = Mmult Rfield (S N) (S M) (S N) (MTranspose Rfield (S M) (S N) D) D (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N)))).
move=> H9.
suff: (forall (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < 1)%nat}), A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) > 0).
move=> H10.
suff: (forall (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < 1)%nat}), A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) = B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y))).
move=> H11.
suff: (forall (K : nat) (x : {n : nat | (n < 1)%nat}), AddConnect 1 K (inl x) = (exist (fun (n : nat) => (n < S K)%nat) O (le_n_S O K (le_0_n K)))).
move=> H12 x y.
rewrite - (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0.
apply (H11 x y0).
move=> y0.
rewrite - (Rmult_1_l (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inr y0)))).
rewrite - (Rmult_1_l (B (AddConnect 1 M (inl x)) (AddConnect 1 N (inr y0)))).
rewrite - (Rinv_l (A (AddConnect 1 M (inl x)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))))).
rewrite Rmult_assoc.
rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
suff: (A (AddConnect 1 M (inl x)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = B (AddConnect 1 M (inl x)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N)))).
move=> H13.
rewrite {2} H13.
suff: (forall (D : Matrix Rfield (S M) (S N)), (D (exist (fun n : nat => (n < S M)%nat) 0%nat (le_n_S 0 M (le_0_n M))) (exist (fun n : nat => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))) > 0) -> (forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < 1)%nat}), D (AddConnect 1 M (inr x)) (AddConnect 1 N (inl y)) = 0) -> D (AddConnect 1 M (inl x)) (exist (fun n : nat => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))) * D (AddConnect 1 M (inl x)) (AddConnect 1 N (inr y0)) = Mmult Rfield (S N) (S M) (S N) (MTranspose Rfield (S M) (S N) D) D (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) (AddConnect 1 N (inr y0))).
move=> H14.
rewrite (H14 A).
rewrite (H14 B).
rewrite H5.
reflexivity.
rewrite - (H12 M x).
rewrite - H13.
rewrite - (H12 N x).
apply (H10 x x).
apply H8.
rewrite - (H12 M x).
rewrite - (H12 N x).
apply (H10 x x).
apply H7.
move=> D H14 H15.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < S M)%nat} (FiniteSingleton {n : nat | (n < S M)%nat} (exist (fun (n : nat) => (n < S M)%nat) O (le_n_S O M (le_0_n M))))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
unfold MTranspose.
rewrite CM_O_r.
rewrite - (H12 M x).
reflexivity.
move=> u.
elim.
move=> u0.
rewrite - (proj2 (AddConnectInvRelation 1 M) u0).
elim (AddConnectInv 1 M u0).
move=> u1.
elim.
rewrite (H12 M u1).
apply In_singleton.
move=> u1 H16 H17.
unfold MTranspose.
rewrite - (H12 N x).
rewrite (H15 u1 x).
apply Rmult_0_l.
move=> u H16.
apply (Full_intro {n : nat | (n < S M)%nat} u).
rewrite - (H12 N x).
apply (H11 x x).
rewrite - (H12 N x).
apply (Rgt_not_eq (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl x))) 0 (H10 x x)).
move=> K x.
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 K) x).
elim (le_lt_or_eq (proj1_sig x) O (le_S_n (proj1_sig x) O (proj2_sig x))).
move=> H12.
elim (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) H12).
apply.
move=> x y.
suff: (B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) > 0).
move=> H11.
suff: (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) * A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) = B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) * B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y))).
move=> H12.
elim (Rle_or_lt (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y))) (B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)))).
elim.
move=> H13.
elim (Rlt_not_eq (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) * A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y))) (B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) * B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)))).
apply Rmult_gt_0_lt_compat.
apply (H10 x y).
apply H11.
apply H13.
apply H13.
apply H12.
apply.
move=> H13.
elim (Rlt_not_eq (B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) * B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y))) (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) * A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)))).
apply Rmult_gt_0_lt_compat.
apply H11.
apply (H10 x y).
apply H13.
apply H13.
rewrite H12.
reflexivity.
rewrite (H9 A H3 H7).
rewrite (H9 B H4 H8).
rewrite H5.
reflexivity.
elim (proj2 H4 (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y))).
apply.
move=> H11.
apply False_ind.
apply H6.
rewrite H5.
rewrite - (H9 B H4 H8 x y).
rewrite H11.
apply (Rmult_0_r 0).
move=> z.
rewrite - (proj1 (AddConnectNature 1 N) y).
move=> H11.
elim (le_not_lt (proj1_sig y) (proj1_sig z)).
elim (le_lt_or_eq (proj1_sig y) O (le_S_n (proj1_sig y) O (proj2_sig y))).
move=> H12.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) H12).
move=> H12.
rewrite H12.
apply (le_0_n (proj1_sig z)).
apply H11.
move=> x y.
elim (proj2 H3 (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y))).
apply.
move=> H10.
apply False_ind.
apply H6.
rewrite - (H9 A H3 H7 x y).
rewrite H10.
apply (Rmult_0_r 0).
move=> z.
rewrite - (proj1 (AddConnectNature 1 N) y).
move=> H10.
elim (le_not_lt (proj1_sig y) (proj1_sig z)).
elim (le_lt_or_eq (proj1_sig y) O (le_S_n (proj1_sig y) O (proj2_sig y))).
move=> H11.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) H11).
move=> H11.
rewrite H11.
apply (le_0_n (proj1_sig z)).
apply H10.
move=> D H9 H10 x y.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < S M)%nat} (FiniteSingleton {n : nat | (n < S M)%nat} (AddConnect 1 M (inl x)))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
suff: (AddConnect 1 N (inl y) = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H11.
rewrite H11.
reflexivity.
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 N) y).
elim (le_lt_or_eq (proj1_sig y) O (le_S_n (proj1_sig y) O (proj2_sig y))).
move=> H11.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) H11).
move=> H11.
rewrite H11.
reflexivity.
move=> u.
elim.
move=> u0.
rewrite - (proj2 (AddConnectInvRelation 1 M) u0).
elim (AddConnectInv 1 M u0).
move=> u1.
elim.
suff: (x = u1).
move=> H11.
rewrite H11.
apply In_singleton.
apply sig_map.
elim (le_lt_or_eq (proj1_sig u1) O (le_S_n (proj1_sig u1) O (proj2_sig u1))).
move=> H11.
elim (le_not_lt O (proj1_sig u1) (le_0_n (proj1_sig u1)) H11).
move=> H11.
rewrite H11.
elim (le_lt_or_eq (proj1_sig x) O (le_S_n (proj1_sig x) O (proj2_sig x))).
move=> H12.
elim (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) H12).
apply.
move=> u1 H11 H12.
suff: ((exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))) = (AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1))))).
move=> H13.
rewrite H13.
rewrite H10.
apply Rmult_0_r.
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 N)).
reflexivity.
move=> u H11.
apply (Full_intro {n : nat | (n < S M)%nat} u).
move=> x y.
apply (UpperTriangularMatrixStrongUpperTriangular Rfield (S M) (S N) B (proj1 H4)).
rewrite - (proj1 (AddConnectNature 1 N) y).
rewrite - (proj2 (AddConnectNature 1 M) x).
apply (le_trans (S (proj1_sig y)) 1 (1 + proj1_sig x) (proj2_sig y) (le_plus_l 1 (proj1_sig x))).
move=> x y.
apply (UpperTriangularMatrixStrongUpperTriangular Rfield (S M) (S N) A (proj1 H3)).
rewrite - (proj1 (AddConnectNature 1 N) y).
rewrite - (proj2 (AddConnectNature 1 M) x).
apply (le_trans (S (proj1_sig y)) 1 (1 + proj1_sig x) (proj2_sig y) (le_plus_l 1 (proj1_sig x))).
Qed.

Lemma UpperTriangularNormalFormCholeskyC : forall (M N : nat) (A B : Matrix Cfield M N), UpperTriangularNormalFormC M N A -> UpperTriangularNormalFormC M N B -> Mmult Cfield N M N (AdjointMatrix M N A) A = Mmult Cfield N M N (AdjointMatrix M N B) B -> A = B.
Proof.
elim.
move=> N A B H1 H2 H3.
apply functional_extensionality.
move=> x.
elim (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) (proj2_sig x)).
move=> M H1.
elim.
move=> A B H2 H3 H4.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) (proj2_sig y)).
move=> N H2 A B H3 H4 H5.
elim (classic (Mmult Cfield (S N) (S M) (S N) (AdjointMatrix (S M) (S N) A) A (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = CO)).
move=> H6.
suff: (forall (D : Matrix Cfield (S M) (S N)), UpperTriangularNormalFormC (S M) (S N) D -> (Mmult Cfield (S N) (S M) (S N) (AdjointMatrix (S M) (S N) D) D (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = CO) -> forall (m : {n : nat | (n < S M)%nat}), D m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = CO).
move=> H7.
suff: (forall (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < 1)%nat}), A m (AddConnect 1 N (inl k)) = CO).
move=> H8.
suff: (forall (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < 1)%nat}), B m (AddConnect 1 N (inl k)) = CO).
move=> H9.
suff: ((fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) => A m (AddConnect 1 N (inr k))) = (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) => B m (AddConnect 1 N (inr k)))).
move=> H10.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite - (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0.
rewrite (H9 x y0).
apply (H8 x y0).
move=> y0.
suff: (A x (AddConnect 1 N (inr y0)) = let temp := (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) => A m (AddConnect 1 N (inr k))) in temp x y0).
move=> H11.
rewrite H11.
rewrite H10.
reflexivity.
reflexivity.
apply H2.
apply conj.
move=> x y H10 z H11.
elim (proj1 H3 x (AddConnect 1 N (inr y)) H10 z).
move=> w.
rewrite - (proj2 (AddConnectInvRelation 1 N) w).
elim (AddConnectInv 1 N w).
move=> w0 H12.
elim (proj2 H12 (H8 z w0)).
move=> w0 H12.
exists w0.
apply conj.
apply (plus_lt_reg_l (proj1_sig w0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) w0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply (proj1 H12).
apply (proj2 H12).
apply H11.
move=> x y H10.
apply (proj2 H3 x (AddConnect 1 N (inr y))).
move=> z.
rewrite - (proj2 (AddConnectInvRelation 1 N) z).
elim (AddConnectInv 1 N z).
move=> z0 H11.
apply (H8 x z0).
move=> z0 H11.
apply (H10 z0).
apply (plus_lt_reg_l (proj1_sig z0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) z0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply H11.
apply conj.
move=> x y H10 z H11.
elim (proj1 H4 x (AddConnect 1 N (inr y)) H10 z).
move=> w.
rewrite - (proj2 (AddConnectInvRelation 1 N) w).
elim (AddConnectInv 1 N w).
move=> w0 H12.
elim (proj2 H12 (H9 z w0)).
move=> w0 H12.
exists w0.
apply conj.
apply (plus_lt_reg_l (proj1_sig w0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) w0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply (proj1 H12).
apply (proj2 H12).
apply H11.
move=> x y H10.
apply (proj2 H4 x (AddConnect 1 N (inr y))).
move=> z.
rewrite - (proj2 (AddConnectInvRelation 1 N) z).
elim (AddConnectInv 1 N z).
move=> z0 H11.
apply (H9 x z0).
move=> z0 H11.
apply (H10 z0).
apply (plus_lt_reg_l (proj1_sig z0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) z0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply H11.
suff: (forall (D : Matrix Cfield (S M) (S N)), (forall (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < 1)%nat}), D m (AddConnect 1 N (inl k)) = CO) -> Mmult Cfield N (S M) N (AdjointMatrix (S M) N (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) => D m (AddConnect 1 N (inr k)))) (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) => D m (AddConnect 1 N (inr k))) = (fun (x y : {n : nat | (n < N)%nat}) => Mmult Cfield (S N) (S M) (S N) (AdjointMatrix (S M) (S N) D) D (AddConnect 1 N (inr x)) (AddConnect 1 N (inr y)))).
move=> H10.
rewrite (H10 A H8).
rewrite (H10 B H9).
rewrite H5.
reflexivity.
move=> D H10.
suff: (D = MBlockW Cfield (S M) 1 N (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < 1)%nat}) => D m (AddConnect 1 N (inl k))) (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) => D m (AddConnect 1 N (inr k)))).
move=> H11.
rewrite {4} H11.
rewrite {3} H11.
rewrite (BlockWAdjointMatrix (S M) 1 N).
rewrite (MBlockHMult Cfield 1 N (S M) (S N)).
rewrite (MBlockWMult Cfield N (S M) 1 N).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
rewrite (proj1 (AddConnectInvRelation 1 N) (inr x)).
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 N) (inr y)).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockW.
rewrite - {1} (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0.
reflexivity.
move=> y0.
reflexivity.
move=> m k.
suff: (AddConnect 1 N (inl k) = (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N)))).
move=> H9.
rewrite H9.
apply (H7 B H4).
rewrite - H5.
apply H6.
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 N) k).
elim (le_lt_or_eq (proj1_sig k) O (le_S_n (proj1_sig k) O (proj2_sig k))).
move=> H9.
elim (le_not_lt O (proj1_sig k) (le_0_n (proj1_sig k)) H9).
apply.
move=> m k.
suff: (AddConnect 1 N (inl k) = (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N)))).
move=> H8.
rewrite H8.
apply (H7 A H3).
apply H6.
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 N) k).
elim (le_lt_or_eq (proj1_sig k) O (le_S_n (proj1_sig k) O (proj2_sig k))).
move=> H8.
elim (le_not_lt O (proj1_sig k) (le_0_n (proj1_sig k)) H8).
apply.
move=> D H7 H8.
suff: (forall (m : {n : nat | (n < S M)%nat}), (proj1_sig m > O)%nat -> D m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = CO).
move=> H9 m.
elim (le_lt_or_eq O (proj1_sig m) (le_0_n (proj1_sig m))).
move=> H10.
apply (H9 m H10).
move=> H10.
suff: (Cmult (Conjugate (D m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))))) (D m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N)))) = CO).
move=> H11.
elim (Fmul_integral Cfield (Conjugate (D m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))))) (D m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N)))) H11).
move=> H12.
rewrite - (ConjugateInvolutive (D m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))))).
rewrite H12.
apply ConjugateCO.
apply.
rewrite - H8.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < S M)%nat} (FiniteSingleton {n : nat | (n < S M)%nat} m)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
reflexivity.
move=> u.
elim.
move=> u0 H11 H12.
unfold AdjointMatrix.
rewrite (H9 u0).
apply (Fmul_O_r Cfield).
elim (le_lt_or_eq O (proj1_sig u0) (le_0_n (proj1_sig u0))).
apply.
move=> H13.
elim H11.
suff: (m = u0).
move=> H14.
rewrite H14.
apply In_singleton.
apply sig_map.
rewrite - H10.
apply H13.
move=> u H11.
apply (Full_intro {n : nat | (n < S M)%nat} u).
move=> m H9.
apply (UpperTriangularMatrixStrongUpperTriangular Cfield (S M) (S N) D (proj1 H7)).
apply H9.
move=> H6.
suff: (forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < 1)%nat}), A (AddConnect 1 M (inr x)) (AddConnect 1 N (inl y)) = CO).
move=> H7.
suff: (forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < 1)%nat}), B (AddConnect 1 M (inr x)) (AddConnect 1 N (inl y)) = CO).
move=> H8.
suff: (forall (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}), A (AddConnect 1 M (inl x)) y = B (AddConnect 1 M (inl x)) y).
move=> H9.
suff: ((fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => A (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y))) = (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => B (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y)))).
move=> H10.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite - (proj2 (AddConnectInvRelation 1 M) x).
elim (AddConnectInv 1 M x).
move=> x0.
apply (H9 x0 y).
move=> x0.
rewrite - (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0.
rewrite (H8 x0 y0).
apply (H7 x0 y0).
move=> y0.
suff: (A (AddConnect 1 M (inr x0)) (AddConnect 1 N (inr y0)) = let temp := (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => A (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y))) in temp x0 y0).
move=> H11.
rewrite H11.
rewrite H10.
reflexivity.
reflexivity.
apply (H1 N).
apply conj.
move=> x y H10 z H11.
elim (proj1 H3 (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y)) H10 (AddConnect 1 M (inr z))).
move=> w.
rewrite - (proj2 (AddConnectInvRelation 1 N) w).
elim (AddConnectInv 1 N w).
move=> w0 H12.
elim (proj2 H12 (H7 z w0)).
move=> w0 H12.
exists w0.
apply conj.
apply (plus_lt_reg_l (proj1_sig w0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) w0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply (proj1 H12).
apply (proj2 H12).
rewrite - (proj2 (AddConnectNature 1 M) z).
rewrite - (proj2 (AddConnectNature 1 M) x).
apply (plus_lt_compat_l (proj1_sig z) (proj1_sig x) 1 H11).
move=> x y H10.
apply (proj2 H3 (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y))).
move=> z.
rewrite - (proj2 (AddConnectInvRelation 1 N) z).
elim (AddConnectInv 1 N z).
move=> z0 H11.
apply (H7 x z0).
move=> z0 H11.
apply (H10 z0).
apply (plus_lt_reg_l (proj1_sig z0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) z0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply H11.
apply conj.
move=> x y H10 z H11.
elim (proj1 H4 (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y)) H10 (AddConnect 1 M (inr z))).
move=> w.
rewrite - (proj2 (AddConnectInvRelation 1 N) w).
elim (AddConnectInv 1 N w).
move=> w0 H12.
elim (proj2 H12 (H8 z w0)).
move=> w0 H12.
exists w0.
apply conj.
apply (plus_lt_reg_l (proj1_sig w0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) w0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply (proj1 H12).
apply (proj2 H12).
rewrite - (proj2 (AddConnectNature 1 M) z).
rewrite - (proj2 (AddConnectNature 1 M) x).
apply (plus_lt_compat_l (proj1_sig z) (proj1_sig x) 1 H11).
move=> x y H10.
apply (proj2 H4 (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y))).
move=> z.
rewrite - (proj2 (AddConnectInvRelation 1 N) z).
elim (AddConnectInv 1 N z).
move=> z0 H11.
apply (H8 x z0).
move=> z0 H11.
apply (H10 z0).
apply (plus_lt_reg_l (proj1_sig z0) (proj1_sig y) 1).
rewrite (proj2 (AddConnectNature 1 N) z0).
rewrite (proj2 (AddConnectNature 1 N) y).
apply H11.
suff: (forall (D : Matrix Cfield (S M) (S N)), (forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < 1)%nat}), D (AddConnect 1 M (inr x)) (AddConnect 1 N (inl y)) = CO) -> Mmult Cfield N M N (AdjointMatrix M N (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => D (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y)))) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => D (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y))) = (fun (x y : {n : nat | (n < N)%nat}) => Mmult Cfield (S N) M (S N) (AdjointMatrix M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inr x)) y) (AddConnect 1 N (inr x)) (AddConnect 1 N (inr y)))).
move=> H10.
rewrite (H10 A H7).
rewrite (H10 B H8).
suff: (Mmult Cfield (S N) M (S N) (AdjointMatrix M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inr x)) y) = Mmult Cfield (S N) M (S N) (AdjointMatrix M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => B (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => B (AddConnect 1 M (inr x)) y)).
move=> H11.
rewrite H11.
reflexivity.
rewrite - (Mplus_O_l Cfield (S N) (S N) (Mmult Cfield (S N) M (S N) (AdjointMatrix M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inr x)) y))).
rewrite - (Mplus_O_l Cfield (S N) (S N) (Mmult Cfield (S N) M (S N) (AdjointMatrix M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => B (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => B (AddConnect 1 M (inr x)) y))).
rewrite - (Mplus_opp_r Cfield (S N) (S N) (Mmult Cfield (S N) 1 (S N) (AdjointMatrix 1 (S N) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y)) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y))).
rewrite (Mplus_comm Cfield (S N) (S N) (Mmult Cfield (S N) 1 (S N) (AdjointMatrix 1 (S N) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y)) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y))).
rewrite Mplus_assoc.
rewrite Mplus_assoc.
suff: (Mplus Cfield (S N) (S N) (Mmult Cfield (S N) 1 (S N) (AdjointMatrix 1 (S N) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y)) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y)) (Mmult Cfield (S N) M (S N) (AdjointMatrix M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inr x)) y)) = Mplus Cfield (S N) (S N) (Mmult Cfield (S N) 1 (S N) (AdjointMatrix 1 (S N) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y)) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y)) (Mmult Cfield (S N) M (S N) (AdjointMatrix M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => B (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => B (AddConnect 1 M (inr x)) y))).
move=> H11.
rewrite H11.
reflexivity.
suff: ((fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => A (AddConnect 1 M (inl x)) y) = (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => B (AddConnect 1 M (inl x)) y)).
move=> H12.
rewrite {3} H12.
rewrite {3} H12.
suff: (forall (D : Matrix Cfield (S M) (S N)), Mplus Cfield (S N) (S N) (Mmult Cfield (S N) 1 (S N) (AdjointMatrix 1 (S N) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inl x)) y)) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inl x)) y)) (Mmult Cfield (S N) M (S N) (AdjointMatrix M (S N) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inr x)) y)) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inr x)) y)) = Mmult Cfield (S N) (S M) (S N) (AdjointMatrix (S M) (S N) D) D).
move=> H13.
rewrite (H13 A).
rewrite (H13 B).
apply H5.
move=> D.
suff: (D = MBlockH Cfield 1 M (S N) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inl x)) y) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inr x)) y)).
move=> H13.
rewrite {5} H13.
rewrite {7} H13.
rewrite (BlockHAdjointMatrix 1 M (S N)).
rewrite (MBlockHWMult Cfield (S N) 1 M (S N)).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
rewrite - {1} (proj2 (AddConnectInvRelation 1 M) x).
elim (AddConnectInv 1 M x).
move=> x0.
reflexivity.
move=> x0.
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply (H9 x y).
move=> D H10.
suff: ((fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) => D (AddConnect 1 M (inr x)) y) = MBlockW Cfield M 1 N (MO Cfield M 1) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => D (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y)))).
move=> H11.
rewrite H11.
rewrite (BlockWAdjointMatrix M 1 N).
rewrite (MBlockHMult Cfield 1 N M (S N)).
rewrite (MBlockWMult Cfield N M 1 N).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 N) (inr x)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inr y)).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockW.
rewrite - {1} (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0.
apply (H10 x y0).
move=> y0.
reflexivity.
suff: (forall (D : Matrix Cfield (S M) (S N)), UpperTriangularNormalFormC (S M) (S N) D -> (forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < 1)%nat}), D (AddConnect 1 M (inr x)) (AddConnect 1 N (inl y)) = CO) -> forall (x y : {n : nat | (n < 1)%nat}), Cmult (Conjugate (D (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)))) (D (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y))) = Mmult Cfield (S N) (S M) (S N) (AdjointMatrix (S M) (S N) D) D (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N)))).
move=> H9.
suff: (forall (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < 1)%nat}), A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CIm = 0).
move=> H10.
suff: (forall (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < 1)%nat}), A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe > 0).
move=> H11.
suff: (forall (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < 1)%nat}), A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) = B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y))).
move=> H12.
suff: (forall (K : nat) (x : {n : nat | (n < 1)%nat}), AddConnect 1 K (inl x) = (exist (fun (n : nat) => (n < S K)%nat) O (le_n_S O K (le_0_n K)))).
move=> H13 x y.
rewrite - (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0.
apply (H12 x y0).
move=> y0.
rewrite - (Cmult_1_l (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inr y0)))).
rewrite - (Cmult_1_l (B (AddConnect 1 M (inl x)) (AddConnect 1 N (inr y0)))).
rewrite - (Cinv_l (Conjugate (A (AddConnect 1 M (inl x)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N)))))).
rewrite Cmult_assoc.
rewrite Cmult_assoc.
apply (Fmul_eq_compat_l Cfield).
suff: (A (AddConnect 1 M (inl x)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = B (AddConnect 1 M (inl x)) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N)))).
move=> H14.
rewrite {2} H14.
suff: (forall (D : Matrix Cfield (S M) (S N)), (D (exist (fun n : nat => (n < S M)%nat) 0%nat (le_n_S 0 M (le_0_n M))) (exist (fun n : nat => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))) CRe > 0) -> (forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < 1)%nat}), D (AddConnect 1 M (inr x)) (AddConnect 1 N (inl y)) = CO) -> Cmult (Conjugate (D (AddConnect 1 M (inl x)) (exist (fun n : nat => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))))) (D (AddConnect 1 M (inl x)) (AddConnect 1 N (inr y0))) = Mmult Cfield (S N) (S M) (S N) (AdjointMatrix (S M) (S N) D) D (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) (AddConnect 1 N (inr y0))).
move=> H15.
rewrite (H15 A).
rewrite (H15 B).
rewrite H5.
reflexivity.
rewrite - (H13 M x).
rewrite - H14.
rewrite - (H13 N x).
apply (H11 x x).
apply H8.
rewrite - (H13 M x).
rewrite - (H13 N x).
apply (H11 x x).
apply H7.
move=> D H15 H16.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < S M)%nat} (FiniteSingleton {n : nat | (n < S M)%nat} (exist (fun (n : nat) => (n < S M)%nat) O (le_n_S O M (le_0_n M))))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
unfold AdjointMatrix.
rewrite CM_O_r.
rewrite - (H13 M x).
reflexivity.
move=> u.
elim.
move=> u0.
rewrite - (proj2 (AddConnectInvRelation 1 M) u0).
elim (AddConnectInv 1 M u0).
move=> u1.
elim.
rewrite (H13 M u1).
apply In_singleton.
move=> u1 H17 H18.
unfold AdjointMatrix.
rewrite - (H13 N x).
rewrite (H16 u1 x).
rewrite ConjugateCO.
apply (Fmul_O_l Cfield).
move=> u H17.
apply (Full_intro {n : nat | (n < S M)%nat} u).
rewrite - (H13 N x).
apply (H12 x x).
rewrite - (H13 N x).
move=> H14.
apply (Rgt_not_eq (Conjugate (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl x))) CRe) 0).
unfold Conjugate.
rewrite CmakeRe.
apply (H11 x x).
rewrite H14.
reflexivity.
move=> K x.
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 K) x).
elim (le_lt_or_eq (proj1_sig x) O (le_S_n (proj1_sig x) O (proj2_sig x))).
move=> H13.
elim (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) H13).
apply.
move=> x y.
suff: (B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe > 0).
move=> H12.
suff: (B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CIm = 0).
move=> H13.
suff: (Cmult (Conjugate (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)))) (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y))) = Cmult (Conjugate (B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)))) (B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)))).
move=> H14.
elim (Rle_or_lt (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe) (B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe)).
elim.
move=> H15.
elim (Rlt_not_eq (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe * A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe) (B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe * B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe)).
apply Rmult_gt_0_lt_compat.
apply (H11 x y).
apply H12.
apply H15.
apply H15.
suff: (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe * A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe = Cmult (Conjugate (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)))) (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y))) CRe).
move=> H16.
rewrite H16.
rewrite H14.
unfold Cmult.
rewrite CmakeRe.
rewrite H13.
rewrite Rmult_0_r.
unfold Rminus.
rewrite Ropp_0.
rewrite Rplus_0_r.
unfold Conjugate.
rewrite CmakeRe.
reflexivity.
unfold Cmult.
rewrite CmakeRe.
rewrite (H10 x y).
rewrite Rmult_0_r.
unfold Rminus.
rewrite Ropp_0.
rewrite Rplus_0_r.
unfold Conjugate.
rewrite CmakeRe.
reflexivity.
move=> H15.
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H16.
rewrite H16.
apply H15.
move=> H16.
rewrite H16.
rewrite H13.
apply (H10 x y).
move=> H15.
elim (Rlt_not_eq (B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe * B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe) (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe * A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe)).
apply Rmult_gt_0_lt_compat.
apply H12.
apply (H11 x y).
apply H15.
apply H15.
suff: (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe * A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) CRe = Cmult (Conjugate (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)))) (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y))) CRe).
move=> H16.
rewrite H16.
rewrite H14.
unfold Cmult.
rewrite CmakeRe.
rewrite H13.
rewrite Rmult_0_r.
unfold Rminus.
rewrite Ropp_0.
rewrite Rplus_0_r.
unfold Conjugate.
rewrite CmakeRe.
reflexivity.
unfold Cmult.
rewrite CmakeRe.
rewrite (H10 x y).
rewrite Rmult_0_r.
unfold Rminus.
rewrite Ropp_0.
rewrite Rplus_0_r.
unfold Conjugate.
rewrite CmakeRe.
reflexivity.
rewrite (H9 A H3 H7).
rewrite (H9 B H4 H8).
rewrite H5.
reflexivity.
suff: (forall (z : {n : nat | (n < S N)%nat}), (proj1_sig (AddConnect 1 N (inl y)) > proj1_sig z)%nat -> B (AddConnect 1 M (inl x)) z = CO).
move=> H13.
apply (proj2 (proj2 H4 (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) H13)).
move=> z.
rewrite - (proj1 (AddConnectNature 1 N) y).
move=> H13.
elim (le_not_lt (proj1_sig y) (proj1_sig z)).
elim (le_lt_or_eq (proj1_sig y) O (le_S_n (proj1_sig y) O (proj2_sig y))).
move=> H14.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) H14).
move=> H14.
rewrite H14.
apply (le_0_n (proj1_sig z)).
apply H13.
suff: (forall (z : {n : nat | (n < S N)%nat}), (proj1_sig (AddConnect 1 N (inl y)) > proj1_sig z)%nat -> B (AddConnect 1 M (inl x)) z = CO).
move=> H12.
elim (proj1 (proj2 H4 (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) H12)).
apply.
move=> H13.
apply False_ind.
apply H6.
rewrite H5.
rewrite - (H9 B H4 H8 x y).
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H14.
rewrite H14.
unfold Cmult.
rewrite CmakeRe.
rewrite H13.
rewrite (proj2 (proj2 H4 (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) H12)).
rewrite Rmult_0_r.
rewrite Rmult_0_r.
apply (Rplus_opp_r 0).
move=> H14.
rewrite H14.
unfold Cmult.
rewrite CmakeIm.
rewrite H13.
rewrite (proj2 (proj2 H4 (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) H12)).
rewrite Rmult_0_r.
rewrite Rmult_0_r.
apply (Rplus_0_r 0).
move=> z.
rewrite - (proj1 (AddConnectNature 1 N) y).
move=> H12.
elim (le_not_lt (proj1_sig y) (proj1_sig z)).
elim (le_lt_or_eq (proj1_sig y) O (le_S_n (proj1_sig y) O (proj2_sig y))).
move=> H13.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) H13).
move=> H13.
rewrite H13.
apply (le_0_n (proj1_sig z)).
apply H12.
move=> x y.
suff: (forall (z : {n : nat | (n < S N)%nat}), (proj1_sig (AddConnect 1 N (inl y)) > proj1_sig z)%nat -> A (AddConnect 1 M (inl x)) z = CO).
move=> H11.
elim (proj1 (proj2 H3 (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) H11)).
apply.
move=> H12.
apply False_ind.
apply H6.
rewrite - (H9 A H3 H7 x y).
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H13.
rewrite H13.
unfold Cmult.
rewrite CmakeRe.
rewrite H12.
rewrite (proj2 (proj2 H3 (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) H11)).
rewrite Rmult_0_r.
rewrite Rmult_0_r.
apply (Rplus_opp_r 0).
move=> H13.
rewrite H13.
unfold Cmult.
rewrite CmakeIm.
rewrite H12.
rewrite (proj2 (proj2 H3 (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) H11)).
rewrite Rmult_0_r.
rewrite Rmult_0_r.
apply (Rplus_0_r 0).
move=> z.
rewrite - (proj1 (AddConnectNature 1 N) y).
move=> H11.
elim (le_not_lt (proj1_sig y) (proj1_sig z)).
elim (le_lt_or_eq (proj1_sig y) O (le_S_n (proj1_sig y) O (proj2_sig y))).
move=> H12.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) H12).
move=> H12.
rewrite H12.
apply (le_0_n (proj1_sig z)).
apply H11.
move=> x y.
suff: (forall (z : {n : nat | (n < S N)%nat}), (proj1_sig (AddConnect 1 N (inl y)) > proj1_sig z)%nat -> A (AddConnect 1 M (inl x)) z = CO).
move=> H10.
apply (proj2 (proj2 H3 (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) H10)).
move=> z.
rewrite - (proj1 (AddConnectNature 1 N) y).
move=> H10.
elim (le_not_lt (proj1_sig y) (proj1_sig z)).
elim (le_lt_or_eq (proj1_sig y) O (le_S_n (proj1_sig y) O (proj2_sig y))).
move=> H11.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) H11).
move=> H11.
rewrite H11.
apply (le_0_n (proj1_sig z)).
apply H10.
move=> D H9 H10 x y.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < S M)%nat} (FiniteSingleton {n : nat | (n < S M)%nat} (AddConnect 1 M (inl x)))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
suff: (AddConnect 1 N (inl y) = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H11.
rewrite H11.
reflexivity.
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 N) y).
elim (le_lt_or_eq (proj1_sig y) O (le_S_n (proj1_sig y) O (proj2_sig y))).
move=> H11.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) H11).
move=> H11.
rewrite H11.
reflexivity.
move=> u.
elim.
move=> u0.
rewrite - (proj2 (AddConnectInvRelation 1 M) u0).
elim (AddConnectInv 1 M u0).
move=> u1.
elim.
suff: (x = u1).
move=> H11.
rewrite H11.
apply In_singleton.
apply sig_map.
elim (le_lt_or_eq (proj1_sig u1) O (le_S_n (proj1_sig u1) O (proj2_sig u1))).
move=> H11.
elim (le_not_lt O (proj1_sig u1) (le_0_n (proj1_sig u1)) H11).
move=> H11.
rewrite H11.
elim (le_lt_or_eq (proj1_sig x) O (le_S_n (proj1_sig x) O (proj2_sig x))).
move=> H12.
elim (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) H12).
apply.
move=> u1 H11 H12.
suff: ((exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))) = (AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1))))).
move=> H13.
rewrite H13.
rewrite H10.
apply (Fmul_O_r Cfield).
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 N)).
reflexivity.
move=> u H11.
apply (Full_intro {n : nat | (n < S M)%nat} u).
move=> x y.
apply (UpperTriangularMatrixStrongUpperTriangular Cfield (S M) (S N) B (proj1 H4)).
rewrite - (proj1 (AddConnectNature 1 N) y).
rewrite - (proj2 (AddConnectNature 1 M) x).
apply (le_trans (S (proj1_sig y)) 1 (1 + proj1_sig x) (proj2_sig y) (le_plus_l 1 (proj1_sig x))).
move=> x y.
apply (UpperTriangularMatrixStrongUpperTriangular Cfield (S M) (S N) A (proj1 H3)).
rewrite - (proj1 (AddConnectNature 1 N) y).
rewrite - (proj2 (AddConnectNature 1 M) x).
apply (le_trans (S (proj1_sig y)) 1 (1 + proj1_sig x) (proj2_sig y) (le_plus_l 1 (proj1_sig x))).
Qed.

Definition UpperTriangularNormalFormCholeskyRC : forall (K : RC) (M N : nat) (A B : Matrix (RCfield K) M N), UpperTriangularNormalFormRC K M N A -> UpperTriangularNormalFormRC K M N B -> Mmult (RCfield K) N M N (AdjointMatrixRC K M N A) A = Mmult (RCfield K) N M N (AdjointMatrixRC K M N B) B -> A = B := fun (K : RC) => match K with
  | RK => UpperTriangularNormalFormCholeskyR
  | CK => UpperTriangularNormalFormCholeskyC
end.

Lemma HouseholderRSig : forall (N : nat) (x y : Rn N), RnNorm N x = RnNorm N y -> {Q : Matrix Rfield N N | OrthogonalMatrix N Q /\ Mmult Rfield N N 1 Q (MVectorToMatrix Rfield N x) = MVectorToMatrix Rfield N y /\ Mmult Rfield N N 1 Q (MVectorToMatrix Rfield N y) = MVectorToMatrix Rfield N x}.
Proof.
suff: (forall (N : nat) (x y : {n : nat | (n < N)%nat} -> R), RnInnerProduct N x y = 0 -> {Q : Matrix Rfield N N | OrthogonalMatrix N Q /\ Mmult Rfield N N 1 Q (MVectorToMatrix Rfield N x) = MVectorToMatrix Rfield N x /\ Mmult Rfield N N 1 Q (MVectorToMatrix Rfield N y) = Mopp Rfield N 1 (MVectorToMatrix Rfield N y)}).
move=> H1 N x y H2.
elim (H1 N (Rnplus N x y) (Rnplus N x (Rnopp N y))).
move=> Q H3.
exists Q.
suff: (forall (a b : R), / (1 + 1) * ((a + b) - (a - b)) = b).
move=> H4.
suff: (forall (a b : R), / (1 + 1) * ((a + b) + (a - b)) = a).
move=> H5.
apply conj.
apply (proj1 H3).
apply conj.
suff: (VMmult Rfield N 1 (/ (1 + 1)) (Mplus Rfield N 1 (MVectorToMatrix Rfield N (Rnplus N x y)) (MVectorToMatrix Rfield N (Rnplus N x (Rnopp N y)))) = MVectorToMatrix Rfield N x).
move=> H6.
rewrite - H6.
rewrite (VMmult_assoc_r Rfield N N 1 (/ (1 + 1)) Q).
rewrite (Mmult_plus_distr_l Rfield N N 1 Q).
rewrite (proj1 (proj2 H3)).
rewrite (proj2 (proj2 H3)).
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
apply H4.
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
apply H5.
suff: (VMmult Rfield N 1 (/ (1 + 1)) (Mplus Rfield N 1 (MVectorToMatrix Rfield N (Rnplus N x y)) (VMmult Rfield N 1 (- 1) (MVectorToMatrix Rfield N (Rnplus N x (Rnopp N y))))) = MVectorToMatrix Rfield N y).
move=> H6.
rewrite - H6.
rewrite (VMmult_assoc_r Rfield N N 1 (/ (1 + 1)) Q).
rewrite (Mmult_plus_distr_l Rfield N N 1 Q).
rewrite (VMmult_assoc_r Rfield N N 1 (- (1)) Q).
rewrite (proj1 (proj2 H3)).
rewrite (proj2 (proj2 H3)).
suff: (forall (a b : R), / (1 + 1) * (a + b + (- (1)) * - (a - b)) = a).
move=> H7.
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
apply H7.
move=> a b.
rewrite (Rmult_opp_opp 1 (a - b)).
rewrite (Rmult_1_l (a - b)).
apply (H5 a b).
suff: (forall (a b : R), / (1 + 1) * (a + b + (- (1)) * (a - b)) = b).
move=> H6.
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
apply H6.
move=> a b.
rewrite (Ropp_mult_distr_l_reverse 1 (a - b)).
rewrite (Rmult_1_l (a - b)).
apply (H4 a b).
move=> a b.
rewrite - (Ropp_minus_distr b a).
rewrite (Rplus_comm a b).
apply (H4 b a).
move=> a b.
unfold Rminus.
rewrite (Ropp_plus_distr a (- b)).
rewrite (Ropp_involutive b).
rewrite - (Rplus_assoc (a + b) (- a) b).
rewrite (Rplus_comm (a + b) (- a)).
rewrite - (Rplus_assoc (- a) a b).
rewrite (Rplus_opp_l a).
rewrite (Rplus_0_l b).
rewrite - (Rmult_1_l b).
rewrite - (Rmult_plus_distr_r 1 1 b).
rewrite - (Rmult_assoc (/ (1 + 1)) (1 + 1) b).
rewrite (Rinv_l (1 + 1)).
reflexivity.
apply (Rgt_not_eq (1 + 1) 0).
apply (Rlt_trans 0 1 (1 + 1) Rlt_0_1 (Rlt_plus_1 1)).
rewrite (Proposition_4_2_1_1_R N).
rewrite (Proposition_4_2_1_2_R N).
rewrite (Proposition_4_2_1_2_R N).
rewrite - Rplus_assoc.
rewrite (Rplus_assoc (RnInnerProduct N x x)).
rewrite (Proposition_4_2_3_R N y x).
rewrite - (Proposition_4_2_1_2_R N x).
unfold Rnplus.
unfold Rnopp.
rewrite (Fnadd_comm Rfield N (Fnopp Rfield N y)).
rewrite (Fnadd_opp_r Rfield N y).
unfold RnInnerProduct at 2.
rewrite MySumF2O.
simpl.
rewrite (Rplus_0_r (RnInnerProduct N x x)).
suff: (RnInnerProduct N y (Rnopp N y) = - RnInnerProduct N y y).
move=> H3.
rewrite H3.
rewrite (proj2 (RnNormNature N x)).
rewrite (proj2 (RnNormNature N y)).
rewrite H2.
apply (Rplus_opp_r (RnNorm N y * RnNorm N y)).
apply (Rip_linear_opp_r (RnVS N) (RnInner_Product_Space N)).
move=> u H3.
apply (Rmult_0_r (x u)).
move=> N x y H1.
elim (excluded_middle_informative (y = RnO N)).
move=> H2.
exists (MI Rfield N).
apply conj.
unfold OrthogonalMatrix.
rewrite (MTransI Rfield N).
apply (Mmult_I_r Rfield N N (MI Rfield N)).
apply conj.
apply (Mmult_I_l Rfield N 1 (MVectorToMatrix Rfield N x)).
rewrite (Mmult_I_l Rfield N 1 (MVectorToMatrix Rfield N y)).
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
rewrite H2.
suff: (0 = - 0).
apply.
rewrite Ropp_0.
reflexivity.
move=> H2.
exists (Mplus Rfield N N (MI Rfield N) (VMmult Rfield N N (- (2 / RnInnerProduct N y y)) (Mmult Rfield N 1 N (MVectorToMatrix Rfield N y) (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y))))).
apply conj.
unfold OrthogonalMatrix.
rewrite (MTransPlus Rfield N N).
rewrite (MTransVMult Rfield N N).
rewrite (MTransI Rfield N).
rewrite (MTransMult Rfield N 1 N).
rewrite (MTransTrans Rfield N 1).
rewrite (Mmult_plus_distr_l Rfield N N N).
rewrite (Mmult_plus_distr_r Rfield N N N).
rewrite (Mmult_plus_distr_r Rfield N N N).
rewrite (Mmult_I_r Rfield N N (MI Rfield N)).
rewrite (Mmult_I_r Rfield N N).
rewrite (Mmult_I_l Rfield N N).
rewrite (Mplus_assoc Rfield N N (MI Rfield N)).
rewrite - (Mplus_assoc Rfield N N (VMmult Rfield N N (- (2 / RnInnerProduct N y y)) (Mmult Rfield N 1 N (MVectorToMatrix Rfield N y) (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y))))).
rewrite - (VMmult_plus_distr_r Rfield N N (- (2 / RnInnerProduct N y y)) (- (2 / RnInnerProduct N y y))).
suff: (Mmult Rfield N N N (VMmult Rfield N N (- (2 / RnInnerProduct N y y)) (Mmult Rfield N 1 N (MVectorToMatrix Rfield N y) (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y)))) (VMmult Rfield N N (- (2 / RnInnerProduct N y y)) (Mmult Rfield N 1 N (MVectorToMatrix Rfield N y) (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y)))) = Mopp Rfield N N (VMmult Rfield N N (Fadd Rfield (- (2 / RnInnerProduct N y y)) (- (2 / RnInnerProduct N y y))) (Mmult Rfield N 1 N (MVectorToMatrix Rfield N y) (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y))))).
move=> H3.
rewrite H3.
rewrite (Mplus_opp_r Rfield N N).
rewrite (Mplus_comm Rfield N N).
apply (Mplus_O_l Rfield N N).
rewrite (VMmult_assoc_l Rfield N N N (- (2 / RnInnerProduct N y y))).
rewrite (VMmult_assoc_r Rfield N N N (- (2 / RnInnerProduct N y y))).
rewrite (VMmult_assoc_reverse Rfield N N (- (2 / RnInnerProduct N y y)) (- (2 / RnInnerProduct N y y))).
rewrite (Mmult_assoc Rfield N 1 N N).
rewrite - (Mmult_assoc Rfield 1 N 1 N).
suff: (Mmult Rfield 1 1 N (Mmult Rfield 1 N 1 (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y)) (MVectorToMatrix Rfield N y)) (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y)) = VMmult Rfield 1 N (RnInnerProduct N y y) (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y))).
move=> H3.
rewrite H3.
rewrite (VMmult_assoc_r Rfield N 1 N (RnInnerProduct N y y)).
rewrite (VMmult_assoc_reverse Rfield N N).
suff: (Fmul Rfield (Fmul Rfield (- (2 / RnInnerProduct N y y)) (- (2 / RnInnerProduct N y y))) (RnInnerProduct N y y) = - (Fadd Rfield (- (2 / RnInnerProduct N y y)) (- (2 / RnInnerProduct N y y)))).
move=> H4.
rewrite H4.
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
apply Ropp_mult_distr_l_reverse.
simpl.
rewrite Rmult_assoc.
rewrite {2} Ropp_mult_distr_l.
rewrite (Rmult_assoc (- (2))).
rewrite (Rinv_l (RnInnerProduct N y y)).
rewrite (Rmult_1_r (- (2))).
rewrite Rmult_opp_opp.
rewrite Ropp_plus_distr.
rewrite (Ropp_involutive (2 / RnInnerProduct N y y)).
rewrite {2} /2.
rewrite - (INR_IPR 2).
simpl.
rewrite (Rmult_plus_distr_l (2 / RnInnerProduct N y y) 1 1).
rewrite (Rmult_1_r (2 / RnInnerProduct N y y)).
reflexivity.
move=> H4.
apply H2.
apply (Proposition_4_2_4_2_R N y H4).
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
unfold Mmult at 1.
suff: (exist (Finite (Count 1)) (Full_set {n : nat | (n < 1)%nat}) (CountFinite 1) = FiniteSingleton (Count 1) h).
move=> H3.
rewrite H3.
rewrite MySumF2Singleton.
apply Rmult_eq_compat_r.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u H3.
suff: (u = h).
move=> H4.
rewrite H4.
apply In_singleton.
apply sig_map.
elim (le_lt_or_eq (proj1_sig u) O (le_S_n (proj1_sig u) O (proj2_sig u))).
move=> H4.
elim (le_not_lt O (proj1_sig u) (le_0_n (proj1_sig u)) H4).
move=> H4.
elim (le_lt_or_eq (proj1_sig h) O (le_S_n (proj1_sig h) O (proj2_sig h))).
move=> H5.
elim (le_not_lt O (proj1_sig h) (le_0_n (proj1_sig h)) H5).
move=> H5.
rewrite H5.
apply H4.
move=> u H3.
apply Full_intro.
apply conj.
rewrite (Mmult_plus_distr_r Rfield N N 1).
rewrite (VMmult_assoc_l Rfield N N 1).
rewrite (Mmult_assoc Rfield N 1 N 1).
suff: (Mmult Rfield 1 N 1 (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y)) (MVectorToMatrix Rfield N x) = MO Rfield 1 1).
move=> H3.
rewrite H3.
rewrite - (VMmult_assoc_l Rfield N 1 1).
rewrite (Mmult_O_r Rfield N 1 1).
rewrite (Mplus_comm Rfield N 1).
rewrite (Mmult_I_l Rfield N 1).
apply (Mplus_O_l Rfield N 1).
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
unfold Mmult.
simpl.
rewrite - H1.
apply (Proposition_4_2_3_R N y x).
rewrite (Mmult_plus_distr_r Rfield N N 1).
rewrite (Mmult_I_l Rfield N 1).
rewrite (VMmult_assoc_l Rfield N N 1).
rewrite (Mmult_assoc Rfield N 1 N 1).
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
unfold Mplus.
unfold VMmult.
unfold Mmult at 1.
suff: (exist (Finite (Count 1)) (Full_set {n : nat | (n < 1)%nat}) (CountFinite 1) = FiniteSingleton (Count 1) w).
move=> H3.
rewrite H3.
rewrite MySumF2Singleton.
suff: (Mmult Rfield 1 N 1 (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y)) (MVectorToMatrix Rfield N y) w w = RnInnerProduct N y y).
move=> H4.
rewrite H4.
simpl.
rewrite - Ropp_mult_distr_l.
rewrite (Rmult_assoc 2).
rewrite (Rmult_comm (MVectorToMatrix Rfield N y h w)).
rewrite - (Rmult_assoc (/ RnInnerProduct N y y)).
rewrite Rinv_l.
rewrite Rmult_1_l.
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
rewrite (Rmult_plus_distr_r 1 1).
rewrite Rmult_1_l.
rewrite Ropp_plus_distr.
rewrite - Rplus_assoc.
rewrite Rplus_opp_r.
apply Rplus_0_l.
move=> H5.
apply (H2 (Proposition_4_2_4_2_R N y H5)).
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u H3.
suff: (u = w).
move=> H4.
rewrite H4.
apply In_singleton.
apply sig_map.
elim (le_lt_or_eq (proj1_sig u) O (le_S_n (proj1_sig u) O (proj2_sig u))).
move=> H4.
elim (le_not_lt O (proj1_sig u) (le_0_n (proj1_sig u)) H4).
move=> H4.
elim (le_lt_or_eq (proj1_sig w) O (le_S_n (proj1_sig w) O (proj2_sig w))).
move=> H5.
elim (le_not_lt O (proj1_sig w) (le_0_n (proj1_sig w)) H5).
move=> H5.
rewrite H5.
apply H4.
move=> u H3.
apply Full_intro.
Qed.

Lemma HouseholderCSig : forall (N : nat) (x y : Cn N), CnInnerProduct N x x = CnInnerProduct N y y -> CnInnerProduct N x y = CnInnerProduct N y x -> {Q : Matrix Cfield N N | UnitaryMatrix N Q /\ Mmult Cfield N N 1 Q (MVectorToMatrix Cfield N x) = MVectorToMatrix Cfield N y /\ Mmult Cfield N N 1 Q (MVectorToMatrix Cfield N y) = MVectorToMatrix Cfield N x}.
Proof.
suff: (forall (N : nat) (x y : {n : nat | (n < N)%nat} -> C), CnInnerProduct N x y = CO -> {Q : Matrix Cfield N N | UnitaryMatrix N Q /\ Mmult Cfield N N 1 Q (MVectorToMatrix Cfield N x) = MVectorToMatrix Cfield N x /\ Mmult Cfield N N 1 Q (MVectorToMatrix Cfield N y) = Mopp Cfield N 1 (MVectorToMatrix Cfield N y)}).
move=> H1 N x y H2 H3.
elim (H1 N (Fnadd Cfield N x y) (Fnadd Cfield N x (Fnopp Cfield N y))).
move=> Q H4.
exists Q.
suff: (forall (a b : C), Cmult (Cmake (/ (1 + 1)) 0) (Cminus (Cplus a b) (Cminus a b)) = b).
move=> H5.
suff: (forall (a b : C), Cmult (Cmake (/ (1 + 1)) 0) (Cplus (Cplus a b) (Cminus a b)) = a).
move=> H6.
apply conj.
apply (proj1 H4).
apply conj.
suff: (VMmult Cfield N 1 (Cmake (/ (1 + 1)) 0) (Mplus Cfield N 1 (MVectorToMatrix Cfield N (Fnadd Cfield N x y)) (MVectorToMatrix Cfield N (Fnadd Cfield N x (Fnopp Cfield N y)))) = MVectorToMatrix Cfield N x).
move=> H7.
rewrite - H7.
rewrite (VMmult_assoc_r Cfield N N 1 (Cmake (/ (1 + 1)) 0) Q).
rewrite (Mmult_plus_distr_l Cfield N N 1 Q).
rewrite (proj1 (proj2 H4)).
rewrite (proj2 (proj2 H4)).
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
apply H5.
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
apply H6.
suff: (VMmult Cfield N 1 (Cmake (/ (1 + 1)) 0) (Mplus Cfield N 1 (MVectorToMatrix Cfield N (Fnadd Cfield N x y)) (VMmult Cfield N 1 (Copp CI) (MVectorToMatrix Cfield N (Fnadd Cfield N x (Fnopp Cfield N y))))) = MVectorToMatrix Cfield N y).
move=> H7.
rewrite - H7.
rewrite (VMmult_assoc_r Cfield N N 1 (Cmake (/ (1 + 1)) 0) Q).
rewrite (Mmult_plus_distr_l Cfield N N 1 Q).
rewrite (VMmult_assoc_r Cfield N N 1 (Copp CI) Q).
rewrite (proj1 (proj2 H4)).
rewrite (proj2 (proj2 H4)).
suff: (forall (a b : C), Cmult (Cmake (/ (1 + 1)) 0) (Cplus (Cplus a b) (Cmult (Copp CI) (Copp (Cminus a b)))) = a).
move=> H8.
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
apply H8.
move=> a b.
suff: (Cmult (Copp CI) (Copp (Cminus a b)) = Cmult CI (Cminus a b)).
move=> H8.
rewrite H8.
rewrite (Cmult_1_l (Cminus a b)).
apply (H6 a b).
apply (Fmul_opp_opp Cfield CI (Cminus a b)).
suff: (forall (a b : C), Cmult (Cmake (/ (1 + 1)) 0) (Cplus (Cplus a b) (Cmult (Copp CI) (Cminus a b))) = b).
move=> H7.
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
apply H7.
move=> a b.
suff: (Cmult (Copp CI) (Cminus a b) = Copp (Cmult CI (Cminus a b))).
move=> H7.
rewrite H7.
rewrite (Cmult_1_l (Cminus a b)).
apply (H5 a b).
apply (Fopp_mul_distr_l_reverse Cfield CI (Cminus a b)).
move=> a b.
suff: (Copp (Cminus b a) = Cminus a b).
move=> H6.
rewrite - H6.
rewrite (Cplus_comm a b).
apply (H5 b a).
apply (Fopp_minus_distr Cfield b a).
move=> a b.
suff: (Cminus (Cplus a b) (Cminus a b) = Cplus b b).
move=> H5.
rewrite H5.
rewrite - (Cmult_1_l b).
suff: (Cmult (Cplus CI CI) b = Cplus (Cmult CI b) (Cmult CI b)).
move=> H6.
rewrite - H6.
rewrite - Cmult_assoc.
unfold CI.
unfold Cmult at 2.
unfold Cplus.
unfold Fnadd.
simpl.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite (Rplus_0_r 0).
rewrite (Rinv_l (1 + 1)).
rewrite (Rmult_0_r 0).
rewrite (Rmult_0_r (/ (1 + 1))).
rewrite (Rmult_0_l (1 + 1)).
rewrite (Rminus_0_r 1).
rewrite (Rplus_0_r 0).
reflexivity.
apply (Rgt_not_eq (1 + 1) 0).
apply (Rlt_trans 0 1 (1 + 1) Rlt_0_1 (Rlt_plus_1 1)).
apply (Fmul_add_distr_r Cfield CI CI b).
unfold Cminus.
unfold Cplus.
unfold Fnminus.
unfold Fnopp.
unfold Fnadd.
simpl.
apply functional_extensionality.
move=> z.
rewrite (Ropp_plus_distr (a z) (- b z)).
rewrite (Ropp_involutive (b z)).
rewrite - (Rplus_assoc (a z + b z) (- a z) (b z)).
rewrite (Rplus_comm (a z + b z) (- a z)).
rewrite - (Rplus_assoc (- a z) (a z) (b z)).
rewrite (Rplus_opp_l (a z)).
rewrite (Rplus_0_l (b z)).
reflexivity.
suff: (forall (x y1 y2 : Cn N), CnInnerProduct N x (Fnadd Cfield N y1 y2) = Cplus (CnInnerProduct N x y1) (CnInnerProduct N x y2)).
move=> H4.
suff: (forall (x y : Cn N), CnInnerProduct N x (Fnopp Cfield N y) = Copp (CnInnerProduct N x y)).
move=> H5.
rewrite (Proposition_4_2_1_1_C N).
rewrite (H4 x x (Fnopp Cfield N y)).
rewrite (H4 y x (Fnopp Cfield N y)).
rewrite (H5 x y).
rewrite (H5 y y).
rewrite H3.
rewrite - Cplus_assoc.
rewrite (Cplus_assoc (CnInnerProduct N x x)).
rewrite (Cplus_comm (Copp (CnInnerProduct N y x))).
rewrite Cplus_opp_r.
rewrite (Cplus_comm (CnInnerProduct N x x)).
rewrite Cplus_0_l.
rewrite H2.
apply Cplus_opp_r.
apply (Cip_linear_opp_r (FnVS Cfield N) (CnInner_Product_Space N)).
apply (Cip_linear_plus_r (FnVS Cfield N) (CnInner_Product_Space N)).
move=> N x y H1.
elim (excluded_middle_informative (y = FnO Cfield N)).
move=> H2.
exists (MI Cfield N).
apply conj.
unfold UnitaryMatrix.
rewrite (AdjointMatrixI N).
apply (Mmult_I_r Cfield N N (MI Cfield N)).
apply conj.
apply (Mmult_I_l Cfield N 1 (MVectorToMatrix Cfield N x)).
rewrite (Mmult_I_l Cfield N 1 (MVectorToMatrix Cfield N y)).
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
rewrite H2.
suff: (CO = Copp CO).
apply.
suff: (Copp CO = CO).
move=> H3.
rewrite H3.
reflexivity.
apply (Fopp_O Cfield).
move=> H2.
exists (Mplus Cfield N N (MI Cfield N) (VMmult Cfield N N (Cmake (- (2 / CnInnerProduct N y y CRe)) 0) (Mmult Cfield N 1 N (MVectorToMatrix Cfield N y) (AdjointMatrix N 1 (MVectorToMatrix Cfield N y))))).
apply conj.
suff: (Conjugate (Cmake (- (2 / CnInnerProduct N y y CRe)) 0) = Cmake (- (2 / CnInnerProduct N y y CRe)) 0).
move=> H3.
unfold UnitaryMatrix.
rewrite (AdjointMatrixPlus N N).
rewrite (AdjointMatrixVMmult N N).
rewrite (AdjointMatrixI N).
rewrite (AdjointMatrixMult N 1 N).
rewrite (AdjointMatrixInvolutive N 1).
rewrite (Mmult_plus_distr_l Cfield N N N).
rewrite (Mmult_plus_distr_r Cfield N N N).
rewrite (Mmult_plus_distr_r Cfield N N N).
rewrite (Mmult_I_r Cfield N N (MI Cfield N)).
rewrite (Mmult_I_r Cfield N N).
rewrite (Mmult_I_l Cfield N N).
rewrite (Mplus_assoc Cfield N N (MI Cfield N)).
rewrite H3.
rewrite - (Mplus_assoc Cfield N N (VMmult Cfield N N (Cmake (- (2 / CnInnerProduct N y y CRe)) 0) (Mmult Cfield N 1 N (MVectorToMatrix Cfield N y) (AdjointMatrix N 1 (MVectorToMatrix Cfield N y))))).
rewrite - (VMmult_plus_distr_r Cfield N N (Cmake (- (2 / CnInnerProduct N y y CRe)) 0) (Cmake (- (2 / CnInnerProduct N y y CRe)) 0)).
suff: (Mmult Cfield N N N (VMmult Cfield N N (Cmake (- (2 / CnInnerProduct N y y CRe)) 0) (Mmult Cfield N 1 N (MVectorToMatrix Cfield N y) (AdjointMatrix N 1 (MVectorToMatrix Cfield N y)))) (VMmult Cfield N N (Cmake (- (2 / CnInnerProduct N y y CRe)) 0) (Mmult Cfield N 1 N (MVectorToMatrix Cfield N y) (AdjointMatrix N 1 (MVectorToMatrix Cfield N y)))) = Mopp Cfield N N (VMmult Cfield N N (Fadd Cfield (Cmake (- (2 / CnInnerProduct N y y CRe)) 0) (Cmake (- (2 / CnInnerProduct N y y CRe)) 0)) (Mmult Cfield N 1 N (MVectorToMatrix Cfield N y) (AdjointMatrix N 1 (MVectorToMatrix Cfield N y))))).
move=> H4.
rewrite H4.
rewrite (Mplus_opp_r Cfield N N).
rewrite (Mplus_comm Cfield N N).
apply (Mplus_O_l Cfield N N).
rewrite (VMmult_assoc_l Cfield N N N (Cmake (- (2 / CnInnerProduct N y y CRe)) 0)).
rewrite (VMmult_assoc_r Cfield N N N (Cmake (- (2 / CnInnerProduct N y y CRe)) 0)).
rewrite (VMmult_assoc_reverse Cfield N N (Cmake (- (2 / CnInnerProduct N y y CRe)) 0) (Cmake (- (2 / CnInnerProduct N y y CRe)) 0)).
rewrite (Mmult_assoc Cfield N 1 N N).
rewrite - (Mmult_assoc Cfield 1 N 1 N).
suff: (Mmult Cfield 1 1 N (Mmult Cfield 1 N 1 (AdjointMatrix N 1 (MVectorToMatrix Cfield N y)) (MVectorToMatrix Cfield N y)) (AdjointMatrix N 1 (MVectorToMatrix Cfield N y)) = VMmult Cfield 1 N (CnInnerProduct N y y) (AdjointMatrix N 1 (MVectorToMatrix Cfield N y))).
move=> H4.
rewrite H4.
rewrite (VMmult_assoc_r Cfield N 1 N (CnInnerProduct N y y)).
rewrite (VMmult_assoc_reverse Cfield N N).
suff: (Fmul Cfield (Fmul Cfield (Cmake (- (2 / CnInnerProduct N y y CRe)) 0) (Cmake (- (2 / CnInnerProduct N y y CRe)) 0)) (CnInnerProduct N y y) = Copp (Fadd Cfield (Cmake (- (2 / CnInnerProduct N y y CRe)) 0) (Cmake (- (2 / CnInnerProduct N y y CRe)) 0))).
move=> H5.
rewrite H5.
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
apply (Fopp_mul_distr_l_reverse Cfield).
simpl.
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H5.
rewrite H5.
unfold Cmult at 2.
rewrite CmakeIm.
rewrite (Rmult_0_r 0).
rewrite Rmult_0_r.
rewrite Rmult_0_l.
rewrite Rminus_0_r.
rewrite (Rplus_0_r 0).
rewrite CmakeRe.
unfold Cmult.
suff: (CnInnerProduct N y y CIm = 0).
move=> H6.
rewrite H6.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite (Rmult_0_r 0).
rewrite Rminus_0_r.
rewrite Rmult_opp_opp.
rewrite Rmult_assoc.
rewrite (Rmult_assoc 2 (/ CnInnerProduct N y y CRe) (CnInnerProduct N y y CRe)).
rewrite (Rinv_l (CnInnerProduct N y y CRe)).
rewrite (Rmult_1_r 2).
unfold Copp.
unfold Rnopp.
unfold Fnopp.
unfold Cplus.
unfold Rnplus.
unfold Fnadd.
simpl.
rewrite CmakeRe.
rewrite Ropp_plus_distr.
rewrite (Ropp_involutive (2 / CnInnerProduct N y y CRe)).
rewrite {2} /2.
rewrite - (INR_IPR 2).
simpl.
rewrite (Rmult_plus_distr_l (2 / CnInnerProduct N y y CRe) 1 1).
rewrite (Rmult_1_r (2 / CnInnerProduct N y y CRe)).
reflexivity.
move=> H7.
apply H2.
apply (Proposition_4_2_4_2_C N y).
apply functional_extensionality.
move=> w.
elim (CReorCIm w).
move=> H8.
rewrite H8.
apply H7.
move=> H8.
rewrite H8.
apply H6.
apply (Cip_pos_im (FnVS Cfield N) (CnInner_Product_Space N) y).
move=> H5.
rewrite H5.
unfold Cmult at 2.
rewrite CmakeIm.
rewrite (Rmult_0_r 0).
rewrite Rmult_0_r.
rewrite Rmult_0_l.
rewrite Rminus_0_r.
rewrite (Rplus_0_r 0).
rewrite CmakeRe.
unfold Cmult.
suff: (CnInnerProduct N y y CIm = 0).
move=> H6.
rewrite H6.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite CmakeRe.
rewrite Rmult_0_l.
rewrite Rmult_0_r.
rewrite Rplus_0_r.
unfold Copp.
unfold Rnopp.
unfold Fnopp.
unfold Cplus.
unfold Rnplus.
unfold Fnadd.
simpl.
rewrite CmakeIm.
rewrite (Rplus_0_l 0).
rewrite Ropp_0.
reflexivity.
apply (Cip_pos_im (FnVS Cfield N) (CnInner_Product_Space N) y).
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
unfold Mmult at 1.
suff: (exist (Finite (Count 1)) (Full_set {n : nat | (n < 1)%nat}) (CountFinite 1) = FiniteSingleton (Count 1) h).
move=> H4.
rewrite H4.
rewrite MySumF2Singleton.
apply (Fmul_eq_compat_r Cfield).
unfold Mmult.
unfold CnInnerProduct.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < N)%nat} (exist (Finite {n : nat | (n < N)%nat}) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H5 H6 H7 H8.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H8.
rewrite (Cmult_comm (y b) (Conjugate (y b))).
reflexivity.
apply H7.
apply H7.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u H4.
suff: (u = h).
move=> H5.
rewrite H5.
apply In_singleton.
apply sig_map.
elim (le_lt_or_eq (proj1_sig u) O (le_S_n (proj1_sig u) O (proj2_sig u))).
move=> H5.
elim (le_not_lt O (proj1_sig u) (le_0_n (proj1_sig u)) H5).
move=> H5.
elim (le_lt_or_eq (proj1_sig h) O (le_S_n (proj1_sig h) O (proj2_sig h))).
move=> H6.
elim (le_not_lt O (proj1_sig h) (le_0_n (proj1_sig h)) H6).
move=> H6.
rewrite H6.
apply H5.
move=> u H4.
apply Full_intro.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite Ropp_0.
reflexivity.
apply conj.
rewrite (Mmult_plus_distr_r Cfield N N 1).
rewrite (VMmult_assoc_l Cfield N N 1).
rewrite (Mmult_assoc Cfield N 1 N 1).
suff: (Mmult Cfield 1 N 1 (AdjointMatrix N 1 (MVectorToMatrix Cfield N y)) (MVectorToMatrix Cfield N x) = MO Cfield 1 1).
move=> H3.
rewrite H3.
rewrite - (VMmult_assoc_l Cfield N 1 1).
rewrite (Mmult_O_r Cfield N 1 1).
rewrite (Mplus_comm Cfield N 1).
rewrite (Mmult_I_l Cfield N 1).
apply (Mplus_O_l Cfield N 1).
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
unfold Mmult.
simpl.
rewrite - H1.
unfold CnInnerProduct.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < N)%nat} (exist (Finite {n : nat | (n < N)%nat}) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H3 H4 H5 H6.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H6.
rewrite (Cmult_comm (x b) (Conjugate (y b))).
reflexivity.
apply H5.
apply H5.
rewrite (Mmult_plus_distr_r Cfield N N 1).
rewrite (Mmult_I_l Cfield N 1).
rewrite (VMmult_assoc_l Cfield N N 1).
rewrite (Mmult_assoc Cfield N 1 N 1).
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
unfold Mplus.
unfold VMmult.
unfold Mmult at 1.
suff: (exist (Finite (Count 1)) (Full_set {n : nat | (n < 1)%nat}) (CountFinite 1) = FiniteSingleton (Count 1) w).
move=> H3.
rewrite H3.
rewrite MySumF2Singleton.
suff: (Mmult Cfield 1 N 1 (AdjointMatrix N 1 (MVectorToMatrix Cfield N y)) (MVectorToMatrix Cfield N y) w w = Conjugate (CnInnerProduct N y y)).
move=> H4.
rewrite H4.
simpl.
rewrite (Cmult_comm (MVectorToMatrix Cfield N y h w)).
rewrite - Cmult_assoc.
unfold Conjugate.
unfold Cmult at 2.
suff: (CnInnerProduct N y y CIm = 0).
move=> H5.
rewrite H5.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite (Rmult_0_l (- 0)).
rewrite Rminus_0_r.
rewrite Ropp_0.
rewrite Rmult_0_r.
rewrite Rmult_0_l.
rewrite Rplus_0_r.
rewrite - Ropp_mult_distr_l.
rewrite (Rmult_assoc 2).
rewrite Rinv_l.
rewrite Rmult_1_r.
suff: (Cmake (- (2)) 0 = Cplus (Copp CI) (Copp CI)).
move=> H6.
rewrite H6.
rewrite Cmult_comm.
rewrite Cmult_plus_distr_l.
suff: (Cmult (MVectorToMatrix Cfield N y h w) (Copp CI) = Copp (Cmult (MVectorToMatrix Cfield N y h w) CI)).
move=> H7.
rewrite H7.
rewrite Cmult_comm.
rewrite Cmult_1_l.
rewrite - Cplus_assoc.
rewrite Cplus_opp_r.
apply Cplus_0_l.
apply (Fopp_mul_distr_r_reverse Cfield).
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H6.
rewrite H6.
unfold Cplus.
unfold Rnplus.
unfold Fnadd.
unfold Copp.
unfold Rnopp.
unfold Fnopp.
simpl.
unfold CI.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite /2.
rewrite - (INR_IPR 2).
apply (Ropp_plus_distr 1 1).
move=> H6.
rewrite H6.
unfold Cplus.
unfold Rnplus.
unfold Fnadd.
unfold Copp.
unfold Rnopp.
unfold Fnopp.
simpl.
unfold CI.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite Ropp_0.
rewrite (Rplus_0_l 0).
reflexivity.
move=> H6.
apply H2.
apply (Proposition_4_2_4_2_C N y).
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H7.
rewrite H7.
apply H6.
move=> H7.
rewrite H7.
apply H5.
apply (Cip_pos_im (FnVS Cfield N) (CnInner_Product_Space N) y).
unfold Mmult.
unfold CnInnerProduct.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < N)%nat} (exist (Finite {n : nat | (n < N)%nat}) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite ConjugateCO.
reflexivity.
move=> B b H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H7.
rewrite Proposition_4_8_1_1.
rewrite (Proposition_4_8_2 (y b) (Conjugate (y b))).
rewrite (ConjugateInvolutive (y b)).
reflexivity.
apply H6.
apply H6.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u H3.
suff: (u = w).
move=> H4.
rewrite H4.
apply In_singleton.
apply sig_map.
elim (le_lt_or_eq (proj1_sig u) O (le_S_n (proj1_sig u) O (proj2_sig u))).
move=> H4.
elim (le_not_lt O (proj1_sig u) (le_0_n (proj1_sig u)) H4).
move=> H4.
elim (le_lt_or_eq (proj1_sig w) O (le_S_n (proj1_sig w) O (proj2_sig w))).
move=> H5.
elim (le_not_lt O (proj1_sig w) (le_0_n (proj1_sig w)) H5).
move=> H5.
rewrite H5.
apply H4.
move=> u H3.
apply Full_intro.
Qed.

Lemma HouseholderRCSig : forall (K : RC) (N : nat) (x y : RCn K N), RCnInnerProduct K N x x = RCnInnerProduct K N y y -> RCnInnerProduct K N x y = RCnInnerProduct K N y x -> {Q : Matrix (RCfield K) N N | UnitaryMatrixRC K N Q /\ Mmult (RCfield K) N N 1 Q (MVectorToMatrix (RCfield K) N x) = MVectorToMatrix (RCfield K) N y /\ Mmult (RCfield K) N N 1 Q (MVectorToMatrix (RCfield K) N y) = MVectorToMatrix (RCfield K) N x}.
Proof.
elim.
move=> N x y H1 H2.
apply (HouseholderRSig N x y).
apply (RnNormNature2 N x (RnNorm N y)).
apply conj.
apply (proj1 (RnNormNature N y)).
rewrite - (proj2 (RnNormNature N y)).
apply H1.
apply HouseholderCSig.
Qed.

Definition HouseholderR (N : nat) (x y : Rn N) (H : RnNorm N x = RnNorm N y) := proj1_sig (HouseholderRSig N x y H).

Definition HouseholderC (N : nat) (x y : Cn N) (H1 : CnInnerProduct N x x = CnInnerProduct N y y) (H2 : CnInnerProduct N x y = CnInnerProduct N y x) := proj1_sig (HouseholderCSig N x y H1 H2).

Definition HouseholderRC (K : RC) (N : nat) (x y : RCn K N) (H1 : RCnInnerProduct K N x x = RCnInnerProduct K N y y) (H2 : RCnInnerProduct K N x y = RCnInnerProduct K N y x) := proj1_sig (HouseholderRCSig K N x y H1 H2).

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

Lemma SameNormConvertUnitaryCSig : forall (N : nat) (x y : Cn N), CnNorm N x = CnNorm N y -> {Q : Matrix Cfield N N | UnitaryMatrix N Q /\ Mmult Cfield N N 1 Q (MVectorToMatrix Cfield N x) = MVectorToMatrix Cfield N y}.
Proof.
move=> N x y H1.
elim (excluded_middle_informative (CnInnerProduct N x y = CnInnerProduct N y x)).
move=> H2.
elim (HouseholderCSig N x y).
move=> Q H3.
exists Q.
apply conj.
apply (proj1 H3).
apply (proj1 (proj2 H3)).
apply functional_extensionality.
move=> k.
elim (CReorCIm k).
move=> H3.
rewrite H3.
rewrite (proj2 (CnNormNature N y)).
rewrite - H1.
apply (proj2 (CnNormNature N x)).
move=> H3.
rewrite H3.
rewrite (proj2 (Proposition_4_2_4_1_C N y)).
apply (proj2 (Proposition_4_2_4_1_C N x)).
apply H2.
move=> H2.
suff: (CnInnerProduct N x y CIm <> 0).
move=> H3.
suff: (Cnorm (CnInnerProduct N x y) <> 0).
move=> H4.
elim (HouseholderCSig N x (Fnmul Cfield N (Rnmult 2 (/ Cnorm (CnInnerProduct N x y)) (CnInnerProduct N x y)) y)).
move=> Q H5.
exists (Mmult Cfield N N N (VMmult Cfield N N (Rnmult 2 (/ Cnorm (CnInnerProduct N x y)) (Conjugate (CnInnerProduct N x y))) (MI Cfield N)) Q).
suff: (Cnorm (CnInnerProduct N x y) <> 0).
move=> H6.
apply conj.
apply (UnitaryMatrixChain N).
unfold UnitaryMatrix.
rewrite (AdjointMatrixVMmult N N).
rewrite (AdjointMatrixI N).
rewrite (VMmult_assoc_l Cfield N N N).
rewrite (VMmult_assoc_r Cfield N N N).
rewrite (VMmult_assoc_reverse Cfield N N).
suff: (Fmul Cfield (Conjugate (Rnmult 2 (/ Cnorm (CnInnerProduct N x y)) (Conjugate (CnInnerProduct N x y)))) (Rnmult 2 (/ Cnorm (CnInnerProduct N x y)) (Conjugate (CnInnerProduct N x y))) = CI).
move=> H7.
rewrite H7.
rewrite (Mmult_I_l Cfield N N (MI Cfield N)).
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
apply (Cmult_1_l (MI Cfield N h w)).
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H7.
rewrite H7.
simpl.
unfold Cmult.
unfold Rnmult.
unfold Fnmul.
rewrite CmakeRe.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CRe)).
rewrite (Rmult_comm (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CRe)).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
unfold Rminus.
rewrite Ropp_mult_distr_l_reverse.
rewrite Ropp_involutive.
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * - CnInnerProduct N x y CIm)).
rewrite (Rmult_comm (/ Cnorm (CnInnerProduct N x y) * - CnInnerProduct N x y CIm)).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
rewrite - Rmult_plus_distr_l.
rewrite (Rmult_opp_opp (CnInnerProduct N x y CIm) (CnInnerProduct N x y CIm)).
suff: (CnInnerProduct N x y CRe * CnInnerProduct N x y CRe + CnInnerProduct N x y CIm * CnInnerProduct N x y CIm = Cnorm (CnInnerProduct N x y) * Cnorm (CnInnerProduct N x y)).
move=> H8.
rewrite H8.
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rinv_l (Cnorm (CnInnerProduct N x y)) H4).
rewrite (Rmult_1_r (/ Cnorm (CnInnerProduct N x y))).
unfold CI.
rewrite CmakeRe.
apply (Rinv_l (Cnorm (CnInnerProduct N x y)) H4).
rewrite CnormDefinition.
apply (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (CnInnerProduct N x y CRe * CnInnerProduct N x y CRe + CnInnerProduct N x y CIm * CnInnerProduct N x y CIm) (CnormSqrtSub (CnInnerProduct N x y))))).
move=> H7.
rewrite H7.
simpl.
unfold Cmult.
unfold Rnmult.
unfold Fnmul.
rewrite CmakeIm.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CRe)).
rewrite (Rmult_comm (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CRe)).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
rewrite Ropp_mult_distr_r.
rewrite Ropp_involutive.
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CIm)).
rewrite (Rmult_comm (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CIm)).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
rewrite - Rmult_plus_distr_l.
rewrite (Rmult_comm (CnInnerProduct N x y CIm) (CnInnerProduct N x y CRe)).
rewrite - Rmult_plus_distr_l.
rewrite (Rplus_opp_l (CnInnerProduct N x y CIm)).
rewrite Rmult_0_r.
unfold CI.
rewrite CmakeIm.
apply Rmult_0_r.
apply (proj1 H5).
rewrite (Mmult_assoc Cfield N N N 1).
rewrite (proj1 (proj2 H5)).
rewrite (VMmult_assoc_l Cfield N N 1).
rewrite (Mmult_I_l Cfield N 1).
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
unfold VMmult.
unfold MVectorToMatrix.
unfold Rnmult.
unfold Fnmul.
simpl.
rewrite - Cmult_assoc.
unfold Cmult at 2.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CRe)).
rewrite (Rmult_comm (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CRe)).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
unfold Rminus.
rewrite Ropp_mult_distr_l.
rewrite Ropp_mult_distr_r.
rewrite Ropp_involutive.
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CIm)).
rewrite (Rmult_comm (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CIm)).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
rewrite - Rmult_plus_distr_l.
suff: (CnInnerProduct N x y CRe * CnInnerProduct N x y CRe + CnInnerProduct N x y CIm * CnInnerProduct N x y CIm = Cnorm (CnInnerProduct N x y) * Cnorm (CnInnerProduct N x y)).
move=> H7.
rewrite H7.
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rinv_l (Cnorm (CnInnerProduct N x y)) H4).
rewrite (Rmult_1_r (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rinv_l (Cnorm (CnInnerProduct N x y)) H4).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CRe)).
rewrite (Rmult_comm (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CRe)).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * - CnInnerProduct N x y CIm)).
rewrite (Rmult_comm (/ Cnorm (CnInnerProduct N x y) * - CnInnerProduct N x y CIm)).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
rewrite - Rmult_plus_distr_l.
rewrite (Rmult_comm (CnInnerProduct N x y CRe) (CnInnerProduct N x y CIm)).
rewrite - Rmult_plus_distr_r.
rewrite (Rplus_opp_r (CnInnerProduct N x y CIm)).
rewrite (Rmult_0_l (CnInnerProduct N x y CRe)).
rewrite Rmult_0_r.
apply (Cmult_1_l (y h)).
rewrite CnormDefinition.
apply (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (CnInnerProduct N x y CRe * CnInnerProduct N x y CRe + CnInnerProduct N x y CIm * CnInnerProduct N x y CIm) (CnormSqrtSub (CnInnerProduct N x y))))).
apply H4.
suff: (forall (c : C) (x y : Cn N), CnInnerProduct N x (Fnmul Cfield N c y) = Cmult (Conjugate c) (CnInnerProduct N x y)).
move=> H5.
rewrite H5.
rewrite (Proposition_4_2_2_1_C N).
rewrite - Cmult_assoc.
unfold Cmult at 2.
unfold Conjugate.
unfold Rnmult.
unfold Fnmul.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CRe)).
rewrite (Rmult_comm (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CRe)).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
unfold Rminus.
rewrite Ropp_mult_distr_l.
rewrite Ropp_involutive.
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CIm)).
rewrite (Rmult_comm (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CIm)).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
rewrite - Rmult_plus_distr_l.
suff: (CnInnerProduct N x y CRe * CnInnerProduct N x y CRe + CnInnerProduct N x y CIm * CnInnerProduct N x y CIm = Cnorm (CnInnerProduct N x y) * Cnorm (CnInnerProduct N x y)).
move=> H6.
rewrite H6.
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rinv_l (Cnorm (CnInnerProduct N x y)) H4).
rewrite (Rmult_1_r (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rinv_l (Cnorm (CnInnerProduct N x y)) H4).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CRe)).
rewrite (Rmult_comm (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CRe)).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
rewrite - Ropp_mult_distr_l.
rewrite Ropp_mult_distr_r.
rewrite Ropp_mult_distr_r.
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CIm)).
rewrite (Rmult_comm (/ Cnorm (CnInnerProduct N x y) * CnInnerProduct N x y CIm)).
rewrite - (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y) * / Cnorm (CnInnerProduct N x y))).
rewrite - Rmult_plus_distr_l.
rewrite (Rmult_comm (CnInnerProduct N x y CRe) (CnInnerProduct N x y CIm)).
rewrite - Rmult_plus_distr_l.
rewrite (Rplus_opp_r (CnInnerProduct N x y CRe)).
rewrite (Rmult_0_r (CnInnerProduct N x y CIm)).
rewrite Rmult_0_r.
suff: (Cmult (Cmake 1 0) (CnInnerProduct N y y) = CnInnerProduct N y y).
move=> H7.
rewrite H7.
apply functional_extensionality.
move=> k.
elim (CReorCIm k).
move=> H8.
rewrite H8.
rewrite (proj2 (CnNormNature N y)).
rewrite - H1.
apply (proj2 (CnNormNature N x)).
move=> H8.
rewrite H8.
rewrite (proj2 (Proposition_4_2_4_1_C N y)).
apply (proj2 (Proposition_4_2_4_1_C N x)).
apply Cmult_1_l.
rewrite CnormDefinition.
apply (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (CnInnerProduct N x y CRe * CnInnerProduct N x y CRe + CnInnerProduct N x y CIm * CnInnerProduct N x y CIm) (CnormSqrtSub (CnInnerProduct N x y))))).
apply (Cip_linear_mult_r (FnVS Cfield N) (CnInner_Product_Space N)).
rewrite (Proposition_4_2_2_1_C N).
rewrite (Proposition_4_2_3_C N).
rewrite (Proposition_4_2_2_1_C N).
unfold Conjugate.
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H5.
rewrite H5.
rewrite CmakeRe.
reflexivity.
move=> H5.
rewrite H5.
rewrite CmakeIm.
unfold Cmult.
unfold Rnmult.
unfold Fnmul.
rewrite CmakeIm.
suff: (CnInnerProduct N y x CIm = - CnInnerProduct N x y CIm).
move=> H6.
rewrite H6.
suff: (CnInnerProduct N y x CRe = CnInnerProduct N x y CRe).
move=> H7.
rewrite H7.
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_assoc (/ Cnorm (CnInnerProduct N x y))).
rewrite (Rmult_comm (CnInnerProduct N x y CIm) (CnInnerProduct N x y CRe)).
rewrite - Ropp_mult_distr_r.
rewrite - Ropp_mult_distr_r.
rewrite Rplus_opp_l.
apply Ropp_0.
rewrite (Proposition_4_2_3_C N y x).
unfold Conjugate.
apply CmakeRe.
rewrite (Proposition_4_2_3_C N y x).
unfold Conjugate.
apply CmakeIm.
move=> H4.
apply (Rgt_not_eq (CnInnerProduct N x y CRe * CnInnerProduct N x y CRe + CnInnerProduct N x y CIm * CnInnerProduct N x y CIm) 0).
rewrite - (Rplus_0_l 0).
apply (Rplus_ge_gt_compat (CnInnerProduct N x y CRe * CnInnerProduct N x y CRe) 0 (CnInnerProduct N x y CIm * CnInnerProduct N x y CIm) 0).
apply Formula_1_3.
elim (Rle_or_lt (CnInnerProduct N x y CIm) 0).
elim.
move=> H5.
rewrite - (Rmult_opp_opp (CnInnerProduct N x y CIm) (CnInnerProduct N x y CIm)).
apply (Rmult_gt_0_compat (- CnInnerProduct N x y CIm) (- CnInnerProduct N x y CIm)).
apply (Ropp_gt_lt_0_contravar (CnInnerProduct N x y CIm) H5).
apply (Ropp_gt_lt_0_contravar (CnInnerProduct N x y CIm) H5).
move=> H5.
elim (H3 H5).
move=> H5.
apply (Rmult_gt_0_compat (CnInnerProduct N x y CIm) (CnInnerProduct N x y CIm) H5 H5).
suff: (CnInnerProduct N x y CRe * CnInnerProduct N x y CRe + CnInnerProduct N x y CIm * CnInnerProduct N x y CIm = Cnorm (CnInnerProduct N x y) * Cnorm (CnInnerProduct N x y)).
move=> H5.
rewrite H5.
rewrite H4.
apply (Rmult_0_r 0).
rewrite CnormDefinition.
apply (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (CnInnerProduct N x y CRe * CnInnerProduct N x y CRe + CnInnerProduct N x y CIm * CnInnerProduct N x y CIm) (CnormSqrtSub (CnInnerProduct N x y))))).
move=> H3.
apply H2.
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H4.
rewrite H4.
rewrite (Proposition_4_2_3_C N x y).
unfold Conjugate.
apply CmakeRe.
move=> H4.
rewrite H4.
rewrite (Proposition_4_2_3_C N y x).
unfold Conjugate.
rewrite CmakeIm.
rewrite H3.
rewrite Ropp_0.
reflexivity.
Qed.

Lemma SameNormConvertUnitaryRCSig : forall (K : RC) (N : nat) (x y : RCn K N), RCnNorm K N x = RCnNorm K N y -> {Q : Matrix (RCfield K) N N | UnitaryMatrixRC K N Q /\ Mmult (RCfield K) N N 1 Q (MVectorToMatrix (RCfield K) N x) = MVectorToMatrix (RCfield K) N y}.
Proof.
elim.
move=> N x y H1.
elim (HouseholderRSig N x y H1).
move=> Q H2.
exists Q.
apply conj.
apply (proj1 H2).
apply (proj1 (proj2 H2)).
apply SameNormConvertUnitaryCSig.
Qed.

Lemma QRStrongRC1 : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M N), exists (Q : Matrix (RCfield K) M M), (UnitaryMatrixRC K M Q) /\ exists (U : Matrix (RCfield K) M N), UpperTriangularNormalFormRC K M N U /\ A = Mmult (RCfield K) M M N Q U.
Proof.
move=> K.
suff: (forall (M N : nat) (A : Matrix (RCfield K) M N), exists (Q : Matrix (RCfield K) M M), UnitaryMatrixRC K M Q /\ UpperTriangularNormalFormRC K M N (Mmult (RCfield K) M M N Q A)).
move=> H1 M N A.
elim (H1 M N A).
move=> Q H2.
exists (AdjointMatrixRC K M M Q).
apply conj.
unfold UnitaryMatrixRC.
rewrite (AdjointMatrixRCInvolutive K M M Q).
suff: (AdjointMatrixRC K M M Q = InvMatrix (RCfield K) M Q).
move=> H3.
rewrite H3.
apply (InvMatrixMultR (RCfield K) M Q).
apply (proj2 (RegularInvLExistRelation (RCfield K) M Q)).
exists (AdjointMatrixRC K M M Q).
apply (proj1 H2).
apply (InvMatrixMultUniqueLStrong (RCfield K) M Q (AdjointMatrixRC K M M Q) (proj1 H2)).
exists (Mmult (RCfield K) M M N Q A).
apply conj.
apply (proj2 H2).
rewrite - (Mmult_assoc (RCfield K) M M M N).
rewrite (proj1 H2).
rewrite (Mmult_I_l (RCfield K) M N A).
reflexivity.
elim.
move=> N A.
exists (MI (RCfield K) O).
apply conj.
unfold UnitaryMatrixRC.
rewrite (AdjointMatrixRCI K O).
apply (Mmult_I_r (RCfield K) O O (MI (RCfield K) O)).
apply conj.
move=> x.
elim (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) (proj2_sig x)).
move=> x.
elim (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) (proj2_sig x)).
move=> M H1.
elim.
move=> A.
exists (MI (RCfield K) (S M)).
apply conj.
unfold UnitaryMatrixRC.
rewrite (AdjointMatrixRCI K (S M)).
apply (Mmult_I_r (RCfield K) (S M) (S M) (MI (RCfield K) (S M))).
apply conj.
move=> x y.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) (proj2_sig y)).
move=> x y.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) (proj2_sig y)).
move=> N H2 A.
elim (classic (AdjointMatrixRC K (S M) (S N) A (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = FnO (RCfield K) (S M))).
move=> H3.
elim (H2 (fun (x : {n : nat | (n < S M)%nat}) (y : {n : nat | (n < N)%nat}) => A x (AddConnect 1 N (inr y)))).
move=> Q H4.
exists Q.
apply conj.
apply (proj1 H4).
apply conj.
move=> x y.
rewrite - (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0.
elim.
apply (MySumF2O {n : nat | (n < S M)%nat} (exist (Finite (Count (S M))) (Full_set {n : nat | (n < S M)%nat}) (CountFinite (S M))) (FPCM (RCfield K))).
move=> u H5.
suff: (ConjugateRC K (AdjointMatrixRC K (S M) (S N) A (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) u) = A u (AddConnect 1 N (inl y0))).
move=> H6.
rewrite - H6.
rewrite H3.
simpl.
rewrite ConjugateRCO.
apply (Fmul_O_r (RCfield K) (Q x u)).
suff: ((exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) = AddConnect 1 N (inl y0)).
move=> H6.
rewrite H6.
apply (ConjugateRCInvolutive K (A u (AddConnect 1 N (inl y0)))).
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 N) y0).
elim (le_lt_or_eq (proj1_sig y0) O (le_S_n (proj1_sig y0) O (proj2_sig y0))).
move=> H6.
elim (le_not_lt O (proj1_sig y0) (le_0_n (proj1_sig y0)) H6).
move=> H6.
rewrite H6.
reflexivity.
move=> y0 H5 z H6.
elim (proj1 (proj2 H4) x y0 H5 z).
move=> w H7.
exists (AddConnect 1 N (inr w)).
apply conj.
rewrite - (proj2 (AddConnectNature 1 N) w).
rewrite - (proj2 (AddConnectNature 1 N) y0).
apply (plus_lt_compat_l (proj1_sig w) (proj1_sig y0) 1 (proj1 H7)).
apply (proj2 H7).
apply H6.
move=> x y.
rewrite - (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0 H5.
suff: (Mmult (RCfield K) (S M) (S M) (S N) Q A x (AddConnect 1 N (inl y0)) = RCO K).
move=> H6.
rewrite H6.
suff: (forall (K : RC), RCsemipos K (RCO K)).
move=> H7.
apply (H7 K).
elim.
right.
reflexivity.
apply conj.
right.
reflexivity.
reflexivity.
apply (MySumF2O {n : nat | (n < S M)%nat} (exist (Finite (Count (S M))) (Full_set {n : nat | (n < S M)%nat}) (CountFinite (S M))) (FPCM (RCfield K))).
move=> u H6.
suff: (ConjugateRC K (AdjointMatrixRC K (S M) (S N) A (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) u) = A u (AddConnect 1 N (inl y0))).
move=> H7.
rewrite - H7.
rewrite H3.
simpl.
rewrite ConjugateRCO.
apply (Fmul_O_r (RCfield K) (Q x u)).
suff: ((exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) = AddConnect 1 N (inl y0)).
move=> H7.
rewrite H7.
apply (ConjugateRCInvolutive K (A u (AddConnect 1 N (inl y0)))).
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 N) y0).
elim (le_lt_or_eq (proj1_sig y0) O (le_S_n (proj1_sig y0) O (proj2_sig y0))).
move=> H7.
elim (le_not_lt O (proj1_sig y0) (le_0_n (proj1_sig y0)) H7).
move=> H7.
rewrite H7.
reflexivity.
move=> y0 H5.
apply (proj2 (proj2 H4) x y0).
move=> z H6.
apply (H5 (AddConnect 1 N (inr z))).
rewrite - (proj2 (AddConnectNature 1 N) y0).
rewrite - (proj2 (AddConnectNature 1 N) z).
apply (plus_lt_compat_l (proj1_sig z) (proj1_sig y0) 1 H6).
move=> H3.
suff: (forall (K : RC) (x : RCn K (S M)), exists (c : RCT K), RCsemipos K c /\ RCnNorm K (S M) x = RCnNorm K (S M) (fun (m : Count (S M)) => match AddConnectInv 1 M m with
  | inl _ => c
  | inr _ => RCO K
end)).
move=> H4.
elim (H4 K (MTranspose (RCfield K) (S M) (S N) A (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))))).
move=> c H5.
elim (SameNormConvertUnitaryRCSig K (S M) (MTranspose (RCfield K) (S M) (S N) A (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))) (fun (m : Count (S M)) => match AddConnectInv 1 M m with
  | inl _ => c
  | inr _ => RCO K
end) (proj2 H5)).
move=> Q1 H6.
elim (H1 N (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => Mmult (RCfield K) (S M) (S M) (S N) Q1 A (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y)))).
move=> Q2 H7.
exists (Mmult (RCfield K) (S M) (S M) (S M) (MBlockH (RCfield K) 1 M (S M) (MBlockW (RCfield K) 1 1 M (MI (RCfield K) 1) (MO (RCfield K) 1 M)) (MBlockW (RCfield K) M 1 M (MO (RCfield K) M 1) Q2)) Q1).
apply conj.
apply (UnitaryMatrixRCChain K (S M)).
unfold UnitaryMatrixRC.
rewrite (BlockHAdjointMatrixRC K 1 M (S M)).
rewrite (BlockWAdjointMatrixRC K 1 1 M).
rewrite (BlockWAdjointMatrixRC K M 1 M).
rewrite (MBlockHWMult (RCfield K) (S M) 1 M (S M)).
rewrite (AdjointMatrixRCI K 1).
rewrite (AdjointMatrixRCO K 1 M).
rewrite (MBlockHMult (RCfield K) 1 M 1 (S M)).
rewrite (MBlockHMult (RCfield K) 1 M M (S M)).
rewrite (MBlockWMult (RCfield K) 1 1 1 M).
rewrite (MBlockWMult (RCfield K) M 1 1 M).
rewrite (MBlockWMult (RCfield K) 1 M 1 M).
rewrite (MBlockWMult (RCfield K) M M 1 M).
rewrite (Mmult_I_l (RCfield K) 1 1 (MI (RCfield K) 1)).
rewrite (Mmult_I_l (RCfield K) 1 M (MO (RCfield K) 1 M)).
rewrite (Mmult_I_r (RCfield K) M 1 (MO (RCfield K) M 1)).
rewrite (Mmult_O_r (RCfield K) M 1 M (MO (RCfield K) M 1)).
rewrite (Mmult_O_r (RCfield K) 1 M 1).
rewrite (AdjointMatrixRCO K M 1).
rewrite (Mmult_O_l (RCfield K) 1 M M Q2).
rewrite (Mmult_O_r (RCfield K) M M 1 (AdjointMatrixRC K M M Q2)).
rewrite (proj1 H7).
rewrite (MBlockHPlus (RCfield K) 1 M (S M)).
rewrite (MBlockWPlus (RCfield K) 1 1 M).
rewrite (MBlockWPlus (RCfield K) M 1 M).
rewrite (Mplus_O_l (RCfield K) 1 M (MO (RCfield K) 1 M)).
rewrite (Mplus_O_l (RCfield K) M 1 (MO (RCfield K) M 1)).
rewrite (Mplus_O_l (RCfield K) M M (MI (RCfield K) M)).
rewrite (Mplus_comm (RCfield K) 1 1).
rewrite (Mplus_O_l (RCfield K) 1 1 (MI (RCfield K) 1)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite - {2} (proj2 (AddConnectInvRelation 1 M) x).
rewrite - {2} (proj2 (AddConnectInvRelation 1 M) y).
unfold MBlockH.
unfold MBlockW.
elim (AddConnectInv 1 M x).
move=> x0.
elim (AddConnectInv 1 M y).
move=> y0.
unfold MI.
rewrite - (proj1 (AddConnectNature 1 M) x0).
rewrite - (proj1 (AddConnectNature 1 M) y0).
reflexivity.
move=> y0.
unfold MI.
rewrite - (proj1 (AddConnectNature 1 M) x0).
rewrite - (proj2 (AddConnectNature 1 M) y0).
elim (Nat.eq_dec (proj1_sig x0) (1 + proj1_sig y0)).
move=> H8.
elim (lt_irrefl (proj1_sig x0)).
apply (le_trans (S (proj1_sig x0)) 1 (proj1_sig x0)).
apply (proj2_sig x0).
rewrite H8.
apply (le_plus_l 1 (proj1_sig y0)).
move=> H8.
reflexivity.
move=> x0.
elim (AddConnectInv 1 M y).
move=> y0.
unfold MI.
rewrite - (proj2 (AddConnectNature 1 M) x0).
rewrite - (proj1 (AddConnectNature 1 M) y0).
elim (Nat.eq_dec (1 + proj1_sig x0) (proj1_sig y0)).
move=> H8.
elim (lt_irrefl (1 + proj1_sig x0)).
apply (le_trans (S (1 + proj1_sig x0)) 1 (1 + proj1_sig x0)).
rewrite H8.
apply (proj2_sig y0).
apply (le_plus_l 1 (proj1_sig x0)).
move=> H8.
reflexivity.
move=> y0.
unfold MI.
rewrite - (proj2 (AddConnectNature 1 M) x0).
rewrite - (proj2 (AddConnectNature 1 M) y0).
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y0)).
move=> H8.
elim (Nat.eq_dec (1 + proj1_sig x0) (1 + proj1_sig y0)).
move=> H9.
reflexivity.
elim.
rewrite H8.
reflexivity.
move=> H8.
elim (Nat.eq_dec (1 + proj1_sig x0) (1 + proj1_sig y0)).
move=> H9.
elim H8.
apply (plus_reg_l (proj1_sig x0) (proj1_sig y0) 1 H9).
move=> H9.
reflexivity.
apply (proj1 H6).
rewrite (Mmult_assoc (RCfield K) (S M) (S M) (S M) (S N)).
suff: (exists (d : RCT K), (RCsemipos K d) /\ (d <> RCO K) /\ exists (a : Matrix (RCfield K) 1 N), Mmult (RCfield K) (S M) (S M) (S N) Q1 A = MBlockH (RCfield K) 1 M (S N) (MBlockW (RCfield K) 1 1 N (fun (x y : {n : nat | (n < 1)%nat}) => d) a) (MBlockW (RCfield K) M 1 N (MO (RCfield K) M 1) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => Mmult (RCfield K) (S M) (S M) (S N) Q1 A (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y))))).
elim.
move=> d H8.
elim (proj2 (proj2 H8)).
move=> a H9.
rewrite H9.
rewrite (MBlockHWWHSame (RCfield K) 1 M 1 M).
rewrite (MBlockHWMult (RCfield K) (S M) 1 M (S N)).
rewrite (MBlockHMult (RCfield K) 1 M 1 (S N)).
rewrite (MBlockHMult (RCfield K) 1 M M (S N)).
rewrite (MBlockWMult (RCfield K) 1 1 1 N).
rewrite (MBlockWMult (RCfield K) 1 M 1 N).
rewrite (MBlockWMult (RCfield K) M 1 1 N).
rewrite (MBlockWMult (RCfield K) M M 1 N).
rewrite (MBlockHPlus (RCfield K) 1 M (S N)).
rewrite (MBlockWPlus (RCfield K) 1 1 N).
rewrite (MBlockWPlus (RCfield K) M 1 N).
rewrite (Mmult_I_l (RCfield K) 1 1).
rewrite (Mmult_O_l (RCfield K) 1 M 1 (MO (RCfield K) M 1)).
rewrite (Mmult_I_l (RCfield K) 1 N a).
rewrite (Mmult_O_l (RCfield K) 1 M N).
rewrite (Mmult_O_l (RCfield K) M 1 1).
rewrite (Mmult_O_r (RCfield K) M M 1 Q2).
rewrite (Mmult_O_l (RCfield K) M 1 N a).
rewrite (Mplus_O_l (RCfield K) M 1 (MO (RCfield K) M 1)).
rewrite (Mplus_O_l (RCfield K) M N).
rewrite (Mplus_comm (RCfield K) 1 1).
rewrite (Mplus_O_l (RCfield K) 1 1).
rewrite (Mplus_comm (RCfield K) 1 N a (MO (RCfield K) 1 N)).
rewrite (Mplus_O_l (RCfield K) 1 N a).
apply conj.
move=> x.
rewrite - (proj2 (AddConnectInvRelation 1 M) x).
elim (AddConnectInv 1 M x).
move=> x0 y H10 z.
rewrite - (proj1 (AddConnectNature 1 M) x0).
suff: (proj1_sig x0 = O).
move=> H11.
rewrite H11.
move=> H12.
elim (le_not_lt O (proj1_sig z) (le_0_n (proj1_sig z)) H12).
elim (le_lt_or_eq (proj1_sig x0) O (le_S_n (proj1_sig x0) O (proj2_sig x0))).
move=> H11.
elim (le_not_lt O (proj1_sig x0) (le_0_n (proj1_sig x0)) H11).
apply.
move=> x0 y.
rewrite - (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0.
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 M) (inr x0)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inl y0)).
elim.
reflexivity.
move=> y0.
unfold MBlockH at 1.
rewrite (proj1 (AddConnectInvRelation 1 M) (inr x0)).
unfold MBlockW at 1.
rewrite (proj1 (AddConnectInvRelation 1 N) (inr y0)).
move=> H10 z.
rewrite - (proj2 (AddConnectInvRelation 1 M) z).
elim (AddConnectInv 1 M z).
move=> z0 H11.
exists (AddConnect 1 N (inl z0)).
apply conj.
rewrite - (proj1 (AddConnectNature 1 N) z0).
rewrite - (proj2 (AddConnectNature 1 N) y0).
apply (le_trans (S (proj1_sig z0)) 1 (1 + proj1_sig y0) (proj2_sig z0) (le_plus_l 1 (proj1_sig y0))).
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 M) (inl z0)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inl z0)).
move=> H12.
apply (proj1 (proj2 H8) H12).
move=> z0.
rewrite - (proj2 (AddConnectNature 1 M) x0).
rewrite - (proj2 (AddConnectNature 1 N) y0).
rewrite - (proj2 (AddConnectNature 1 M) z0).
move=> H11.
elim (proj1 (proj2 H7) x0 y0 H10 z0 (plus_lt_reg_l (proj1_sig z0) (proj1_sig x0) 1 H11)).
move=> w0 H12.
exists (AddConnect 1 N (inr w0)).
apply conj.
rewrite - (proj2 (AddConnectNature 1 N) w0).
apply (plus_lt_compat_l (proj1_sig w0) (proj1_sig y0) 1 (proj1 H12)).
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 M) (inr z0)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inr w0)).
apply (proj2 H12).
move=> x.
rewrite - (proj2 (AddConnectInvRelation 1 M) x).
elim (AddConnectInv 1 M x).
move=> x0 y.
rewrite - (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0 H10.
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 M) (inl x0)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inl y0)).
apply (proj1 H8).
move=> y0.
unfold MBlockH at 1.
rewrite (proj1 (AddConnectInvRelation 1 M) (inl x0)).
unfold MBlockW at 1.
move=> H10.
apply False_ind.
apply (proj1 (proj2 H8)).
suff: (match AddConnectInv 1 N (AddConnect 1 N (inl x0)) with
  | inl _ => d
  | inr y0 => a x0 y0
end = RCO K).
rewrite (proj1 (AddConnectInvRelation 1 N) (inl x0)).
move=> H11.
rewrite H11.
reflexivity.
apply (H10 (AddConnect 1 N (inl x0))).
rewrite - (proj1 (AddConnectNature 1 N) x0).
rewrite - (proj2 (AddConnectNature 1 N) y0).
apply (le_trans (S (proj1_sig x0)) 1 (1 + proj1_sig y0) (proj2_sig x0) (le_plus_l 1 (proj1_sig y0))).
move=> x0 y.
rewrite - (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0 H10.
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 M) (inr x0)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inl y0)).
suff: (forall (K : RC), RCsemipos K (RCO K)).
move=> H11.
apply (H11 K).
elim.
right.
reflexivity.
apply conj.
right.
reflexivity.
reflexivity.
move=> y0 H10.
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 M) (inr x0)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inr y0)).
apply (proj2 (proj2 H7) x0 y0).
move=> z0 H11.
suff: (MBlockH (RCfield K) 1 M (S N) (MBlockW (RCfield K) 1 1 N (fun (x y : {n : nat | (n < 1)%nat}) => d) a) (MBlockW (RCfield K) M 1 N (MO (RCfield K) M 1) (Mmult (RCfield K) M M N Q2 (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => Mmult (RCfield K) (S M) (S M) (S N) Q1 A (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y))))) (AddConnect 1 M (inr x0)) (AddConnect 1 N (inr z0)) = RCO K).
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 M) (inr x0)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inr z0)).
apply.
apply (H10 (AddConnect 1 N (inr z0))).
rewrite - (proj2 (AddConnectNature 1 N) y0).
rewrite - (proj2 (AddConnectNature 1 N) z0).
apply (plus_lt_compat_l (proj1_sig z0) (proj1_sig y0) 1 H11).
exists c.
apply conj.
apply (proj1 H5).
apply conj.
move=> H8.
apply H3.
suff: (forall (k : Count (S M)), MTranspose (RCfield K) (S M) (S N) A (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) k = RCO K).
move=> H9.
apply functional_extensionality.
move=> k.
unfold AdjointMatrixRC.
suff: (A k (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))) = RCO K).
move=> H10.
rewrite H10.
apply (ConjugateRCO K).
apply (H9 k).
suff: (MTranspose (RCfield K) (S M) (S N) A (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) = RCnO K (S M)).
move=> H9.
rewrite H9.
move=> k.
reflexivity.
apply Proposition_4_4_3_2.
rewrite (proj2 H5).
rewrite H8.
suff: ((fun (m : Count (S M)) => match AddConnectInv 1 M m with
  | inl _
  | _ => RCO K
end) = RCnO K (S M)).
move=> H9.
rewrite H9.
apply Proposition_4_4_3_3.
reflexivity.
apply functional_extensionality.
move=> k.
elim (AddConnectInv 1 M k).
reflexivity.
reflexivity.
exists (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < N)%nat}) => Mmult (RCfield K) (S M) (S M) (S N) Q1 A (AddConnect 1 M (inl x)) (AddConnect 1 N (inr y))).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
rewrite - {1} (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0.
suff: (Mmult (RCfield K) (S M) (S M) (S N) Q1 A x (AddConnect 1 N (inl y0)) = let temp := (fun (m : Count (S M)) => match AddConnectInv 1 M m with
  | inl _ => c
  | inr x0 => MO (RCfield K) M 1 x0 y0
end) in temp x).
apply.
rewrite - (proj1 (MVectorMatrixRelation (RCfield K) (S M)) (fun (m : Count (S M)) => match AddConnectInv 1 M m with
  | inl _ => c
  | inr x0 => MO (RCfield K) M 1 x0 y0
end)).
rewrite - (proj2 H6).
suff: (AddConnect 1 N (inl y0) = (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N)))).
move=> H8.
rewrite H8.
reflexivity.
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 N) y0).
elim (le_lt_or_eq (proj1_sig y0) O (le_S_n (proj1_sig y0) O (proj2_sig y0))).
move=> H8.
elim (le_not_lt O (proj1_sig y0) (le_0_n (proj1_sig y0)) H8).
apply.
move=> y0.
rewrite - {1} (proj2 (AddConnectInvRelation 1 M) x).
elim (AddConnectInv 1 M x).
move=> H8.
reflexivity.
move=> H8.
reflexivity.
elim.
move=> x.
exists (RnNorm (S M) x).
apply conj.
apply (Proposition_4_4_3_1_R (S M) x).
apply RnNormNature2.
apply conj.
apply RnNormNature.
rewrite - (proj2 (RnNormNature (S M) (fun m : Count (S M) => match AddConnectInv 1 M m with
  | inl _ => RnNorm (S M) x
  | inr _ => RCO RK
end))).
unfold RnInnerProduct at 2.
rewrite (MySumF2Included (Count (S M)) (FiniteSingleton (Count (S M)) (exist (fun (n : nat) => (n < S M)%nat) O (le_n_S 0 M (le_0_n M))))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
suff: (exist (fun (n : nat) => (n < S M)%nat) O (le_n_S 0 M (le_0_n M)) = AddConnect 1 M (inl Single)).
move=> H4.
rewrite H4.
rewrite (proj1 (AddConnectInvRelation 1 M)).
apply (proj2 (RnNormNature (S M) x)).
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 M) Single).
reflexivity.
move=> u.
elim.
move=> u0.
rewrite - (proj2 (AddConnectInvRelation 1 M) u0).
elim (AddConnectInv 1 M u0).
move=> u1 H4 H5.
elim H4.
suff: (exist (fun (n : nat) => (n < S M)%nat) O (le_n_S 0 M (le_0_n M)) = AddConnect 1 M (inl u1)).
move=> H6.
rewrite H6.
apply In_singleton.
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 M) u1).
elim (le_lt_or_eq (proj1_sig u1) O (le_S_n (proj1_sig u1) O (proj2_sig u1))).
move=> H6.
elim (le_not_lt O (proj1_sig u1) (le_0_n (proj1_sig u1)) H6).
move=> H6.
rewrite H6.
reflexivity.
move=> u1 H4 H5.
rewrite (proj1 (AddConnectInvRelation 1 M) (inr u1)).
apply (Rmult_0_r 0).
move=> u H6.
apply (Full_intro (Count (S M)) u).
move=> x.
exists (Cmake (CnNorm (S M) x) 0).
apply conj.
apply conj.
rewrite CmakeRe.
apply (Proposition_4_4_3_1_C (S M) x).
apply (CmakeIm (CnNorm (S M) x) 0).
apply CnNormNature2.
apply conj.
apply CnNormNature.
rewrite - (proj2 (CnNormNature (S M) (fun (m : Count (S M)) => match AddConnectInv 1 M m with
  | inl _ => Cmake (CnNorm (S M) x) 0
  | inr _ => CO
end))).
unfold CnInnerProduct at 2.
rewrite (MySumF2Included (Count (S M)) (FiniteSingleton (Count (S M)) (exist (fun (n : nat) => (n < S M)%nat) O (le_n_S 0 M (le_0_n M))))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
suff: (exist (fun (n : nat) => (n < S M)%nat) O (le_n_S 0 M (le_0_n M)) = AddConnect 1 M (inl Single)).
move=> H4.
rewrite H4.
rewrite (proj1 (AddConnectInvRelation 1 M)).
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite Rmult_0_l.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite - (proj2 (CnNormNature (S M) x)).
rewrite Rminus_0_r.
reflexivity.
apply sig_map.
apply (proj1 (AddConnectNature 1 M) Single).
move=> u.
elim.
move=> u0.
rewrite - (proj2 (AddConnectInvRelation 1 M) u0).
elim (AddConnectInv 1 M u0).
move=> u1 H5 H6.
elim H5.
suff: (exist (fun (n : nat) => (n < S M)%nat) O (le_n_S 0 M (le_0_n M)) = AddConnect 1 M (inl u1)).
move=> H7.
rewrite H7.
apply In_singleton.
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 M) u1).
elim (le_lt_or_eq (proj1_sig u1) O (le_S_n (proj1_sig u1) O (proj2_sig u1))).
move=> H7.
elim (le_not_lt O (proj1_sig u1) (le_0_n (proj1_sig u1)) H7).
move=> H7.
rewrite H7.
reflexivity.
move=> u1 H5 H6.
rewrite (proj1 (AddConnectInvRelation 1 M) (inr u1)).
apply (Fmul_O_l Cfield (Conjugate CO)).
move=> u H5.
apply (Full_intro (Count (S M)) u).
Qed.

Definition QRStrongC1 : forall (M N : nat) (A : Matrix Cfield M N), exists (Q : Matrix Cfield M M), (UnitaryMatrix M Q) /\ exists (U : Matrix Cfield M N), UpperTriangularNormalFormC M N U /\ A = Mmult Cfield M M N Q U := QRStrongRC1 CK.

Definition QRStrongR1 : forall (M N : nat) (A : Matrix Rfield M N), exists (Q : Matrix Rfield M M), (OrthogonalMatrix M Q) /\ exists (U : Matrix Rfield M N), UpperTriangularNormalFormR M N U /\ A = Mmult Rfield M M N Q U := QRStrongRC1 RK.

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

Lemma SingularDecompositionRCH : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M), exists (U : Matrix (RCfield K) (M + N)%nat (M + N)%nat), (UnitaryMatrixRC K (M + N)%nat U) /\ exists (V : Matrix (RCfield K) M M), (UnitaryMatrixRC K M V) /\ exists (sigma : Rn M), ((forall (m : Count M), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) /\ A = Mmult (RCfield K) (M + N)%nat (M + N)%nat M U (Mmult (RCfield K) (M + N)%nat M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (sigma m))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))).
Proof.
move=> K.
suff: (forall (M N : nat) (A : Matrix (RCfield K) (M + N) M), exists (U : Matrix (RCfield K) (M + N) (M + N)), UnitaryMatrixRC K (M + N) U /\ (exists (V : Matrix (RCfield K) M M), UnitaryMatrixRC K M V /\ (exists (sigma : {n : nat | (n < M)%nat} -> R), (forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ A = Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (sigma m))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))))).
move=> H1 M N A.
suff: (forall (k : nat), (k <= M)%nat -> exists (U : Matrix (RCfield K) (M + N) (M + N)), UnitaryMatrixRC K (M + N) U /\ (exists (V : Matrix (RCfield K) M M), UnitaryMatrixRC K M V /\ (exists (sigma : {n : nat | (n < M)%nat} -> R), (forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m2 < k)%nat -> (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 < k)%nat -> (proj1_sig m2 >= k)%nat -> sigma m1 >= sigma m2) /\ A = Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (sigma m))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))))).
move=> H2.
elim (H2 M (le_n M)).
move=> U H3.
elim (proj2 H3).
move=> V H4.
elim (proj2 H4).
move=> sigma H5.
exists U.
apply conj.
apply (proj1 H3).
exists V.
apply conj.
apply (proj1 H4).
exists sigma.
apply conj.
apply (proj1 H5).
apply conj.
move=> m1 m2.
apply (proj1 (proj2 H5) m1 m2 (proj2_sig m2)).
apply (proj2 (proj2 H5)).
elim.
move=> H2.
elim (H1 M N A).
move=> U H3.
exists U.
apply conj.
apply (proj1 H3).
elim (proj2 H3).
move=> V H4.
exists V.
apply conj.
apply (proj1 H4).
elim (proj2 H4).
move=> sigma H5.
exists sigma.
apply conj.
apply (proj1 H5).
apply conj.
move=> m1 m2 H6.
elim (le_not_lt O (proj1_sig m2) (le_0_n (proj1_sig m2)) H6).
apply conj.
move=> m1 m2 H6.
elim (le_not_lt O (proj1_sig m1) (le_0_n (proj1_sig m1)) H6).
apply (proj2 H5).
move=> k H2 H3.
elim (H2 (le_trans k (S k) M (le_S k k (le_n k)) H3)).
move=> U H4.
elim (proj2 H4).
move=> V H5.
elim (proj2 H5).
move=> sigma H6.
suff: (exists (m : {n : nat | (n < M)%nat}), (proj1_sig m >= k)%nat /\ forall (l : {n : nat | (n < M)%nat}), (proj1_sig l >= k)%nat -> sigma m >= sigma l).
elim.
move=> m H7.
exists (Mmult (RCfield K) (M + N) (M + N) (M + N) U (ElementaryMatrixSwap (RCfield K) (M + N) (AddConnect M N (inl (exist (fun (n : nat) => (n < M)%nat) k H3))) (AddConnect M N (inl m)))).
apply conj.
apply (UnitaryMatrixRCChain K (M + N)).
apply (proj1 H4).
unfold UnitaryMatrixRC.
suff: (AdjointMatrixRC K (M + N) (M + N) (ElementaryMatrixSwap (RCfield K) (M + N) (AddConnect M N (inl (exist (fun n : nat => (n < M)%nat) k H3))) (AddConnect M N (inl m))) = MTranspose (RCfield K) (M + N) (M + N) (ElementaryMatrixSwap (RCfield K) (M + N) (AddConnect M N (inl (exist (fun n : nat => (n < M)%nat) k H3))) (AddConnect M N (inl m)))).
move=> H8.
rewrite H8.
rewrite (ElementaryMatrixSwapTrans (RCfield K) (M + N)).
rewrite - {1} (InvMatrixElementaryMatrixSwap (RCfield K) (M + N)).
apply (InvMatrixMultL (RCfield K) (M + N)).
elim (classic (k = proj1_sig m)).
move=> H9.
suff: (ElementaryMatrixSwap (RCfield K) (M + N) (AddConnect M N (inl (exist (fun (n : nat) => (n < M)%nat) k H3))) (AddConnect M N (inl m)) = MI (RCfield K) (M + N)).
move=> H10.
rewrite H10.
unfold RegularMatrix.
rewrite (DeterminantI (RCfield K) (M + N)).
apply (FI_neq_FO (RCfield K)).
suff: (exist (fun (n : nat) => (n < M)%nat) k H3 = m).
move=> H10.
rewrite H10.
unfold ElementaryMatrixSwap.
unfold MI.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H11.
rewrite H11.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect M N (inl m)))).
move=> H12.
reflexivity.
move=> H12.
reflexivity.
move=> H11.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect M N (inl m)))).
move=> H12.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect M N (inl m)))).
move=> H13.
elim H11.
rewrite H13.
apply H12.
move=> H13.
reflexivity.
move=> H12.
reflexivity.
apply sig_map.
apply H9.
move=> H9.
unfold RegularMatrix.
rewrite (DeterminantElementaryMatrixSwap (RCfield K) (M + N)).
move=> H10.
apply (FI_neq_FO (RCfield K)).
rewrite - (Fopp_involutive (RCfield K) (FI (RCfield K))).
rewrite H10.
apply (Fopp_O (RCfield K)).
rewrite - (proj1 (AddConnectNature M N)).
rewrite - (proj1 (AddConnectNature M N)).
apply H9.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold AdjointMatrixRC.
unfold MTranspose.
unfold ElementaryMatrixSwap.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect M N (inl (exist (fun n : nat => (n < M)%nat) k H3))))).
move=> H8.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect M N (inl m)))).
move=> H9.
apply ConjugateRCI.
move=> H9.
apply ConjugateRCO.
move=> H8.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect M N (inl m)))).
move=> H9.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect M N (inl (exist (fun n : nat => (n < M)%nat) k H3))))).
move=> H10.
apply ConjugateRCI.
move=> H10.
apply ConjugateRCO.
move=> H9.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig x)).
move=> H10.
apply ConjugateRCI.
move=> H10.
apply ConjugateRCO.
exists (Mmult (RCfield K) M M M V (ElementaryMatrixSwap (RCfield K) M (exist (fun (n : nat) => (n < M)%nat) k H3) m)).
apply conj.
apply (UnitaryMatrixRCChain K M).
apply (proj1 H5).
unfold UnitaryMatrixRC.
suff: (AdjointMatrixRC K M M (ElementaryMatrixSwap (RCfield K) M (exist (fun n : nat => (n < M)%nat) k H3) m) = MTranspose (RCfield K) M M (ElementaryMatrixSwap (RCfield K) M (exist (fun n : nat => (n < M)%nat) k H3) m)).
move=> H8.
rewrite H8.
rewrite (ElementaryMatrixSwapTrans (RCfield K) M).
rewrite - {1} (InvMatrixElementaryMatrixSwap (RCfield K) M).
apply (InvMatrixMultL (RCfield K) M).
elim (classic (k = proj1_sig m)).
move=> H9.
suff: (ElementaryMatrixSwap (RCfield K) M (exist (fun (n : nat) => (n < M)%nat) k H3) m = MI (RCfield K) M).
move=> H10.
rewrite H10.
unfold RegularMatrix.
rewrite (DeterminantI (RCfield K) M).
apply (FI_neq_FO (RCfield K)).
suff: (exist (fun (n : nat) => (n < M)%nat) k H3 = m).
move=> H10.
rewrite H10.
unfold ElementaryMatrixSwap.
unfold MI.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H11.
rewrite H11.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig m)).
move=> H12.
reflexivity.
move=> H12.
reflexivity.
move=> H11.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig m)).
move=> H12.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig m)).
move=> H13.
elim H11.
rewrite H13.
apply H12.
move=> H13.
reflexivity.
move=> H12.
reflexivity.
apply sig_map.
apply H9.
move=> H9.
unfold RegularMatrix.
rewrite (DeterminantElementaryMatrixSwap (RCfield K) M).
move=> H10.
apply (FI_neq_FO (RCfield K)).
rewrite - (Fopp_involutive (RCfield K) (FI (RCfield K))).
rewrite H10.
apply (Fopp_O (RCfield K)).
apply H9.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold AdjointMatrixRC.
unfold MTranspose.
unfold ElementaryMatrixSwap.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H8.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig m)).
move=> H9.
apply ConjugateRCI.
move=> H9.
apply ConjugateRCO.
move=> H8.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig m)).
move=> H9.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H10.
apply ConjugateRCI.
move=> H10.
apply ConjugateRCO.
move=> H9.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig x)).
move=> H10.
apply ConjugateRCI.
move=> H10.
apply ConjugateRCO.
exists (fun (l : {n : nat | (n < M)%nat}) => match excluded_middle_informative (l = exist (fun (n : nat) => (n < M)%nat) k H3) with
  | left _ => sigma m
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => sigma (exist (fun (n : nat) => (n < M)%nat) k H3)
    | right _ => sigma l
  end
end).
apply conj.
move=> l.
elim (excluded_middle_informative (l = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H8.
apply (proj1 H6 m).
move=> H8.
elim (excluded_middle_informative (l = m)).
move=> H9.
apply (proj1 H6 (exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H9.
apply (proj1 H6 l).
apply conj.
move=> m1 m2 H8.
elim (le_lt_or_eq (proj1_sig m2) k (le_S_n (proj1_sig m2) k H8)).
move=> H9 H10.
elim (excluded_middle_informative (m1 = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H11.
elim (lt_irrefl (proj1_sig m1)).
rewrite {2} H11.
apply (le_trans (S (proj1_sig m1)) (S (proj1_sig m2)) k (le_n_S (proj1_sig m1) (proj1_sig m2) H10) H9).
move=> H11.
elim (excluded_middle_informative (m1 = m)).
move=> H12.
elim (lt_irrefl (proj1_sig m1)).
rewrite {2} H12.
apply (le_trans (S (proj1_sig m1)) (S (proj1_sig m2)) (proj1_sig m) (le_n_S (proj1_sig m1) (proj1_sig m2) H10) (le_trans (S (proj1_sig m2)) k (proj1_sig m) H9 (proj1 H7))).
move=> H12.
elim (excluded_middle_informative (m2 = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H13.
elim (lt_irrefl (proj1_sig m2)).
rewrite {2} H13.
apply H9.
move=> H13.
elim (excluded_middle_informative (m2 = m)).
move=> H14.
elim (lt_irrefl (proj1_sig m2)).
rewrite {2} H14.
apply (le_trans (S (proj1_sig m2)) k (proj1_sig m) H9 (proj1 H7)).
move=> H14.
apply (proj1 (proj2 H6) m1 m2 H9 H10).
move=> H9 H10.
elim (excluded_middle_informative (m2 = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H11.
elim (excluded_middle_informative (m1 = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H12.
right.
reflexivity.
move=> H12.
elim (excluded_middle_informative (m1 = m)).
move=> H13.
elim (le_not_lt (proj1_sig m1) k).
rewrite - H9.
apply H10.
elim (le_lt_or_eq k (proj1_sig m1)).
apply.
move=> H14.
elim H12.
apply sig_map.
rewrite - H14.
reflexivity.
rewrite H13.
apply (proj1 H7).
move=> H13.
apply (proj1 (proj2 (proj2 H6)) m1 m).
elim (le_lt_or_eq (proj1_sig m1) (proj1_sig m2)).
rewrite H11.
apply.
move=> H14.
elim H12.
apply sig_map.
rewrite H14.
rewrite H11.
reflexivity.
apply H10.
apply (proj1 H7).
elim.
apply sig_map.
apply H9.
apply conj.
move=> m1 m2 H8 H9.
elim (excluded_middle_informative (m1 = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H10.
elim (excluded_middle_informative (m2 = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H11.
right.
reflexivity.
move=> H11.
elim (excluded_middle_informative (m2 = m)).
move=> H12.
apply (proj2 H7).
apply (le_n k).
move=> H12.
apply (proj2 H7).
apply (le_trans k (S k) (proj1_sig m2) (le_S k k (le_n k)) H9).
move=> H10.
elim (excluded_middle_informative (m1 = m)).
move=> H11.
elim H10.
apply sig_map.
apply (le_antisym (proj1_sig m1) k).
apply (le_S_n (proj1_sig m1) k H8).
rewrite H11.
apply (proj1 H7).
move=> H11.
elim (excluded_middle_informative (m2 = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H12.
apply (proj1 (proj2 (proj2 H6)) m1 m).
elim (le_lt_or_eq (proj1_sig m1) k (le_S_n (proj1_sig m1) k H8)).
apply.
move=> H13.
elim H10.
apply sig_map.
apply H13.
apply (proj1 H7).
move=> H12.
elim (excluded_middle_informative (m2 = m)).
move=> H13.
apply (proj1 (proj2 (proj2 H6)) m1).
elim (le_lt_or_eq (proj1_sig m1) k (le_S_n (proj1_sig m1) k H8)).
apply.
move=> H14.
elim H10.
apply sig_map.
apply H14.
apply (le_n k).
move=> H13.
apply (proj1 (proj2 (proj2 H6)) m1 m2).
elim (le_lt_or_eq (proj1_sig m1) k (le_S_n (proj1_sig m1) k H8)).
apply.
move=> H14.
elim H10.
apply sig_map.
apply H14.
apply (le_trans k (S k) (proj1_sig m2) (le_S k k (le_n k)) H9).
rewrite (AdjointMatrixRCMult K M M M V).
rewrite - (Mmult_assoc (RCfield K) (M + N) M M M).
rewrite - (Mmult_assoc (RCfield K) (M + N) (M + N) M M).
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) M).
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) M M).
rewrite (proj2 (proj2 (proj2 H6))).
suff: (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => IRRC K (sigma l))) (MO (RCfield K) N M) = Mmult (RCfield K) (M + N) (M + N) M (ElementaryMatrixSwap (RCfield K) (M + N) (AddConnect M N (inl (exist (fun (n : nat) => (n < M)%nat) k H3))) (AddConnect M N (inl m))) (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => IRRC K match excluded_middle_informative (l = exist (fun (n : nat) => (n < M)%nat) k H3) with
  | left _ => sigma m
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => sigma (exist (fun (n : nat) => (n < M)%nat) k H3)
    | right _ => sigma l
  end
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M (ElementaryMatrixSwap (RCfield K) M (exist (fun (n : nat) => (n < M)%nat) k H3) m)))).
move=> H8.
rewrite H8.
reflexivity.
suff: (AdjointMatrixRC K M M (ElementaryMatrixSwap (RCfield K) M (exist (fun n : nat => (n < M)%nat) k H3) m) = MTranspose (RCfield K) M M (ElementaryMatrixSwap (RCfield K) M (exist (fun n : nat => (n < M)%nat) k H3) m)).
move=> H8.
rewrite H8.
rewrite (ElementaryMatrixSwapTrans (RCfield K) M).
rewrite (MBlockHMult (RCfield K) M N M M).
rewrite (Mmult_O_l (RCfield K) N M M).
rewrite (ElementaryMatrixSwapNatureR (RCfield K) M M).
rewrite (ElementaryMatrixSwapNatureL (RCfield K) (M + N) M).
unfold MBlockH.
unfold MDiag.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite - (proj2 (AddConnectInvRelation M N) x).
rewrite {1} (proj2 (AddConnectInvRelation M N) x).
elim (AddConnectInv M N x).
move=> x0.
rewrite (proj1 (AddConnectInvRelation M N) (inl m)).
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y)).
move=> H9.
suff: (x0 = y).
move=> H10.
rewrite H10.
rewrite - (proj1 (AddConnectNature M N) y).
rewrite - (proj1 (AddConnectNature M N) (exist (fun (n : nat) => (n < M)%nat) k H3)).
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H11.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H12.
elim (excluded_middle_informative (m = m)).
move=> H13.
elim (excluded_middle_informative (m = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H14.
suff: (y = m).
move=> H15.
rewrite H15.
reflexivity.
rewrite H14.
apply sig_map.
apply H11.
move=> H14.
suff: (y = exist (fun (n : nat) => (n < M)%nat) k H3).
move=> H15.
rewrite H15.
reflexivity.
apply sig_map.
apply H11.
elim.
reflexivity.
elim.
reflexivity.
rewrite (proj1 (AddConnectInvRelation M N) (inl (exist (fun (n : nat) => (n < M)%nat) k H3))).
rewrite - (proj1 (AddConnectNature M N) m).
move=> H11.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig m)).
move=> H12.
elim (Nat.eq_dec (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3)) (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H13.
elim (excluded_middle_informative (exist (fun (n : nat) => (n < M)%nat) k H3 = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H14.
suff: (y = m).
move=> H15.
rewrite H15.
reflexivity.
apply sig_map.
apply H12.
elim.
reflexivity.
elim.
reflexivity.
move=> H12.
rewrite (proj1 (AddConnectInvRelation M N) (inl y)).
elim (Nat.eq_dec (proj1_sig y) (proj1_sig y)).
move=> H13.
elim (excluded_middle_informative (y = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H14.
elim H11.
rewrite H14.
reflexivity.
move=> H14.
elim (excluded_middle_informative (y = m)).
move=> H15.
elim H12.
rewrite H15.
reflexivity.
move=> H15.
reflexivity.
elim.
reflexivity.
apply sig_map.
apply H9.
move=> H9.
rewrite - (proj1 (AddConnectNature M N) x0).
rewrite - (proj1 (AddConnectNature M N) (exist (fun (n : nat) => (n < M)%nat) k H3)).
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H10.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H11.
elim H9.
rewrite H11.
apply H10.
move=> H11.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig m)).
move=> H12.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H13.
elim H11.
rewrite H12.
apply H13.
move=> H13.
reflexivity.
move=> H12.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig y)).
move=> H13.
elim H12.
rewrite H13.
reflexivity.
move=> H13.
reflexivity.
move=> H10.
rewrite (proj1 (AddConnectInvRelation M N) (inl (exist (fun (n : nat) => (n < M)%nat) k H3))).
rewrite - (proj1 (AddConnectNature M N) m).
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig m)).
move=> H11.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H12.
elim (Nat.eq_dec (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3)) (proj1_sig m)).
move=> H13.
elim H10.
rewrite H11.
rewrite H13.
reflexivity.
move=> H13.
reflexivity.
move=> H12.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig m)).
move=> H13.
elim H9.
rewrite H13.
apply H11.
move=> H13.
elim (Nat.eq_dec (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3)) (proj1_sig y)).
move=> H14.
elim H12.
rewrite H14.
reflexivity.
move=> H14.
reflexivity.
move=> H11.
rewrite (proj1 (AddConnectInvRelation M N) (inl x0)).
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig m)).
move=> H12.
elim (H11 H12).
move=> H12.
elim (excluded_middle_informative (x0 = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H13.
elim H10.
rewrite H13.
reflexivity.
move=> H13.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H14.
elim H13.
apply sig_map.
apply H14.
move=> H14.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
reflexivity.
move=> H15.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig m)).
move=> H16.
reflexivity.
move=> H16.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y)).
move=> H17.
elim (H9 H17).
move=> H17.
reflexivity.
move=> x0.
rewrite - (proj1 (AddConnectNature M N) (exist (fun (n : nat) => (n < M)%nat) k H3)).
rewrite - (proj2 (AddConnectNature M N) x0).
elim (Nat.eq_dec (M + proj1_sig x0) (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
simpl.
move=> H9.
elim (le_not_lt M k).
rewrite - H9.
apply (le_plus_l M (proj1_sig x0)).
apply H3.
move=> H9.
rewrite - (proj1 (AddConnectNature M N) m).
elim (Nat.eq_dec (M + proj1_sig m) (proj1_sig m)).
simpl.
move=> H10.
elim (le_not_lt M (proj1_sig m)).
rewrite - H10.
apply (le_plus_l M (proj1_sig m)).
apply (proj2_sig m).
move=> H10.
elim (Nat.eq_dec (M + proj1_sig x0) (proj1_sig m)).
move=> H11.
elim (le_not_lt M (proj1_sig m)).
rewrite - H11.
apply (le_plus_l M (proj1_sig x0)).
apply (proj2_sig m).
move=> H11.
rewrite (proj1 (AddConnectInvRelation M N) (inr x0)).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold AdjointMatrixRC.
unfold MTranspose.
unfold ElementaryMatrixSwap.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H8.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig m)).
move=> H9.
apply ConjugateRCI.
move=> H9.
apply ConjugateRCO.
move=> H8.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig m)).
move=> H9.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H10.
apply ConjugateRCI.
move=> H10.
apply ConjugateRCO.
move=> H9.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig x)).
move=> H10.
apply ConjugateRCI.
move=> H10.
apply ConjugateRCO.
suff: (forall (k : nat), (k > O)%nat -> (k <= M)%nat -> exists (m : {n : nat | (n < M)%nat}), (proj1_sig m >= M - k)%nat /\ (forall (l : {n : nat | (n < M)%nat}), (proj1_sig l >= M - k)%nat -> sigma m >= sigma l)).
move=> H7.
elim (H7 (M - k)%nat).
rewrite - (plus_minus M (M - k) k).
move=> m H8.
exists m.
apply H8.
rewrite (plus_comm (M - k) k).
apply (le_plus_minus k M).
apply (le_trans k (S k) M (le_S k k (le_n k)) H3).
apply (plus_lt_reg_l O (M - k) k).
rewrite (le_plus_minus_r k M).
rewrite (plus_0_r k).
apply H3.
apply (le_trans k (S k) M (le_S k k (le_n k)) H3).
rewrite - (plus_0_l (M - k)).
rewrite {2} (le_plus_minus k M).
apply (plus_le_compat_r 0 k (M - k) (le_0_n k)).
apply (le_trans k (S k) M (le_S k k (le_n k)) H3).
elim.
move=> H7.
elim (lt_irrefl O H7).
move=> k0 H7.
elim k0.
move=> H8 H9.
suff: (M - 1 < M)%nat.
move=> H10.
exists (exist (fun (n : nat) => (n < M)%nat) (M - 1)%nat H10).
apply conj.
apply (le_n (M - 1)%nat).
move=> l H11.
suff: (exist (fun (n : nat) => (n < M)%nat) (M - 1)%nat H10 = l).
move=> H12.
rewrite H12.
right.
reflexivity.
apply sig_map.
apply (le_antisym (M - 1) (proj1_sig l) H11).
apply (plus_le_reg_l (proj1_sig l) (M - 1)%nat 1).
rewrite (le_plus_minus_r 1 M H9).
apply (proj2_sig l).
rewrite {2} (le_plus_minus 1 M H9).
apply (le_n (S (M - 1))%nat).
move=> k1 H8 H9 H10.
elim H8.
move=> m H11.
suff: (M - S (S k1) < M)%nat.
move=> H12.
elim (Rgt_or_ge (sigma (exist (fun (n : nat) => (n < M)%nat) (M - S (S k1))%nat H12)) (sigma m)).
move=> H13.
exists (exist (fun (n : nat) => (n < M)%nat) (M - S (S k1))%nat H12).
apply conj.
apply (le_n (M - S (S k1))).
move=> l H14.
elim (le_lt_or_eq (M - S (S k1)) (proj1_sig l) H14).
move=> H15.
left.
apply (Rgt_ge_trans (sigma (exist (fun (n : nat) => (n < M)%nat) (M - S (S k1))%nat H12)) (sigma m) (sigma l) H13).
apply (proj2 H11 l).
suff: (M - S k1 = S (M - S (S k1)))%nat.
move=> H16.
rewrite H16.
apply H15.
rewrite (minus_Sn_m M (S (S k1)) H10).
reflexivity.
move=> H15.
suff: (exist (fun (n : nat) => (n < M)%nat) (M - S (S k1))%nat H12 = l).
move=> H16.
rewrite H16.
right.
reflexivity.
apply sig_map.
apply H15.
move=> H13.
exists m.
apply conj.
apply (le_trans (M - S (S k1)) (M - S k1) (proj1_sig m)).
suff: (M - S k1 = S (M - S (S k1)))%nat.
move=> H14.
rewrite H14.
apply (le_S (M - S (S k1)) (M - S (S k1)) (le_n (M - S (S k1)))).
rewrite (minus_Sn_m M (S (S k1)) H10).
reflexivity.
apply (proj1 H11).
move=> l H14.
elim (le_lt_or_eq (M - S (S k1)) (proj1_sig l)).
move=> H15.
apply (proj2 H11 l).
suff: (M - S k1 = S (M - S (S k1)))%nat.
move=> H16.
rewrite H16.
apply H15.
rewrite (minus_Sn_m M (S (S k1)) H10).
reflexivity.
move=> H15.
suff: (exist (fun (n : nat) => (n < M)%nat) (M - S (S k1))%nat H12 = l).
move=> H16.
rewrite - H16.
apply H13.
apply sig_map.
apply H15.
apply H14.
rewrite - (plus_0_l (M - S (S k1))).
rewrite {2} (le_plus_minus (S (S k1)) M).
apply (plus_lt_compat_r 0 (S (S k1)) (M - S (S k1)) (le_n_S O (S k1) (le_0_n (S k1)))).
apply H10.
apply (le_n_S O k1 (le_0_n k1)).
apply (le_trans (S k1) (S (S k1)) M (le_S (S k1) (S k1) (le_n (S k1))) H10).
move=> M N A.
elim (HermitianMatrixRCTransformableToDiag K M (Mmult (RCfield K) M (M + N) M (AdjointMatrixRC K (M + N) M A) A)).
move=> V.
elim.
move=> sigma H1.
suff: (forall (m : {n : nat | (n < M)%nat}), RCsemipos K (sigma m) /\ RCRe K (sigma m) >= 0).
move=> H2.
suff: (exists (U : Matrix (RCfield K) (M + N) (M + N)), UnitaryMatrixRC K (M + N) U /\ A = Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (RCRe K (sigma m)) (proj2 (H2 m)))))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))).
elim.
move=> U H3.
exists U.
apply conj.
apply (proj1 H3).
exists V.
apply conj.
apply (proj1 H1).
exists (fun (m : {n : nat | (n < M)%nat}) => MySqrt (exist (fun (r : R) => r >= 0) (RCRe K (sigma m)) (proj2 (H2 m)))).
apply conj.
move=> m.
apply (proj1 (MySqrtNature (exist (fun (r : R) => r >= 0) (RCRe K (sigma m)) (proj2 (H2 m))))).
apply (proj2 H3).
elim (QRStrongRC1 K (M + N) M A).
move=> Q1.
elim.
move=> H3.
elim.
move=> U1 H4.
elim (QRStrongRC1 K (M + N) M (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (RCRe K (sigma m)) (proj2 (H2 m)))))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))).
move=> Q2.
elim.
move=> H5.
elim.
move=> U2 H6.
exists (Mmult (RCfield K) (M + N) (M + N) (M + N) Q1 (AdjointMatrixRC K (M + N) (M + N) Q2)).
apply conj.
apply (UnitaryMatrixRCChain K (M + N) Q1 (AdjointMatrixRC K (M + N) (M + N) Q2)).
apply H3.
unfold UnitaryMatrixRC.
rewrite (AdjointMatrixRCInvolutive K (M + N) (M + N) Q2).
apply (proj1 (MmultILRSame (RCfield K) (M + N) (AdjointMatrixRC K (M + N) (M + N) Q2) Q2) H5).
rewrite (proj2 H6).
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) M Q1 (AdjointMatrixRC K (M + N) (M + N) Q2) (Mmult (RCfield K) (M + N) (M + N) M Q2 U2)).
rewrite - (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) M (AdjointMatrixRC K (M + N) (M + N) Q2) Q2 U2).
rewrite H5.
suff: (U2 = U1).
move=> H7.
rewrite H7.
rewrite (Mmult_I_l (RCfield K) (M + N) M U1).
apply (proj2 H4).
apply (UpperTriangularNormalFormCholeskyRC K (M + N) M U2 U1 (proj1 H6) (proj1 H4)).
rewrite - {2} (Mmult_I_l (RCfield K) (M + N) M U2).
rewrite - H5.
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) M (AdjointMatrixRC K (M + N) (M + N) Q2) Q2 U2).
rewrite - (Mmult_assoc (RCfield K) M (M + N) (M + N) M).
rewrite - (AdjointMatrixRCMult K (M + N) (M + N) M Q2 U2).
rewrite - (proj2 H6).
rewrite (AdjointMatrixRCMult K (M + N) M M).
rewrite (AdjointMatrixRCInvolutive K M M V).
rewrite (Mmult_assoc (RCfield K) M M (M + N) M).
rewrite - (Mmult_assoc (RCfield K) M (M + N) M M).
suff: (Mmult (RCfield K) M (M + N) M (AdjointMatrixRC K (M + N) M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (RCRe K (sigma m)) (proj2 (H2 m)))))) (MO (RCfield K) N M))) (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (RCRe K (sigma m)) (proj2 (H2 m)))))) (MO (RCfield K) N M)) = MDiag (RCfield K) M sigma).
move=> H7.
rewrite H7.
rewrite (proj2 H1).
rewrite - (Mmult_assoc (RCfield K) M M M M V).
rewrite - (Mmult_assoc (RCfield K) M M M M V).
rewrite (proj1 (MmultILRSame (RCfield K) M (AdjointMatrixRC K M M V) V) (proj1 H1)).
rewrite (Mmult_I_l (RCfield K) M M).
rewrite (Mmult_assoc (RCfield K) M M M M).
rewrite (proj1 (MmultILRSame (RCfield K) M (AdjointMatrixRC K M M V) V) (proj1 H1)).
rewrite (Mmult_I_r (RCfield K) M M).
rewrite (proj2 H4).
rewrite (AdjointMatrixRCMult K (M + N) (M + N) M Q1 U1).
rewrite (Mmult_assoc (RCfield K) M (M + N) (M + N) M).
rewrite - (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) M).
rewrite H3.
rewrite (Mmult_I_l (RCfield K) (M + N) M U1).
reflexivity.
rewrite (BlockHAdjointMatrixRC K M N M).
rewrite (MBlockHWMult (RCfield K) M M N M).
rewrite (Mmult_O_r (RCfield K) M N M).
rewrite (Mplus_comm (RCfield K) M M).
rewrite (Mplus_O_l (RCfield K) M M).
suff: (AdjointMatrixRC K M M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (RCRe K (sigma m)) (proj2 (H2 m)))))) = MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (RCRe K (sigma m)) (proj2 (H2 m)))))).
move=> H7.
rewrite H7.
rewrite (MDiagMult (RCfield K) M).
suff: ((fun (m : {n : nat | (n < M)%nat}) => Fmul (RCfield K) (IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (RCRe K (sigma m)) (proj2 (H2 m)))) ) (IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (RCRe K (sigma m)) (proj2 (H2 m)))) )) = sigma).
move=> H8.
rewrite H8.
reflexivity.
apply functional_extensionality.
move=> m.
simpl.
rewrite - IRRCmult.
rewrite - (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (RCRe K (sigma m)) (proj2 (H2 m))))).
simpl.
suff: (forall (K : RC) (c : RCT K), RCsemipos K c -> IRRC K (RCRe K c) = c).
move=> H8.
apply (H8 K (sigma m)).
apply (proj1 (H2 m)).
elim.
move=> c H8.
reflexivity.
move=> c H8.
apply functional_extensionality.
move=> k.
elim (CReorCIm k).
move=> H9.
rewrite H9.
apply (CmakeRe (c CRe) 0).
move=> H9.
rewrite H9.
rewrite (proj2 H8).
apply (CmakeIm (c CRe) 0).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold AdjointMatrixRC.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig x)).
move=> H7.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H8.
suff: (x = y).
move=> H9.
rewrite H9.
suff: (forall (K : RC) (r : R), ConjugateRC K (IRRC K r) = IRRC K r).
move=> H10.
apply (H10 K).
elim.
move=> r.
reflexivity.
move=> r.
simpl.
unfold Conjugate.
apply functional_extensionality.
move=> k.
elim (CReorCIm k).
move=> H10.
rewrite H10.
apply (CmakeRe (IRC r CRe) (- IRC r CIm)).
move=> H10.
rewrite H10.
rewrite (CmakeIm (IRC r CRe) (- IRC r CIm)).
unfold IRC.
rewrite (CmakeIm r 0).
apply Ropp_0.
apply sig_map.
apply H8.
elim.
rewrite H7.
reflexivity.
move=> H7.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H8.
elim H7.
rewrite H8.
reflexivity.
move=> H8.
apply ConjugateRCO.
suff: (forall (m : {n : nat | (n < M)%nat}), RCsemipos K (sigma m)).
move=> H2 m.
apply conj.
apply (H2 m).
suff: (forall (K : RC) (c : RCT K), RCsemipos K c -> RCRe K c >= 0).
move=> H3.
apply (H3 K (sigma m) (H2 m)).
elim.
move=> c.
apply.
move=> c H3.
apply (proj1 H3).
move=> m.
suff: (sigma m = MDiag (RCfield K) M sigma m m).
move=> H2.
rewrite H2.
rewrite (proj2 H1).
rewrite (Mmult_assoc (RCfield K) M (M + N) M M).
rewrite - (Mmult_assoc (RCfield K) M M (M + N) M).
rewrite - (AdjointMatrixRCMult K (M + N) M M).
unfold Mmult at 1.
apply MySumF2Induction.
apply conj.
suff: (forall (K : RC), RCsemipos K (RCO K)).
move=> H3.
apply (H3 K).
elim.
right.
reflexivity.
apply conj.
right.
reflexivity.
reflexivity.
move=> cm u H3 H4.
apply RCsemiposplus.
apply H4.
suff: (forall (K : RC) (c : RCT K), RCsemipos K (RCmult K (ConjugateRC K c) c)).
move=> H5.
apply (H5 K (Mmult (RCfield K) (M + N) M M A V u m)).
elim.
move=> c.
apply (Formula_1_3 c).
move=> c.
simpl.
unfold Conjugate.
unfold Cmult.
rewrite (CmakeRe (c CRe) (- c CIm)).
rewrite (CmakeIm (c CRe) (- c CIm)).
rewrite - Ropp_mult_distr_l.
unfold Rminus.
rewrite Ropp_involutive.
rewrite - Ropp_mult_distr_l.
rewrite (Rmult_comm (c CRe) (c CIm)).
rewrite Rplus_opp_r.
apply conj.
rewrite (CmakeRe (c CRe * c CRe + c CIm * c CIm) 0).
rewrite - (Rplus_0_r 0).
apply Rplus_ge_compat.
apply Formula_1_3.
apply Formula_1_3.
apply (CmakeIm (c CRe * c CRe + c CIm * c CIm) 0).
unfold MDiag.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H2.
reflexivity.
elim.
reflexivity.
unfold HermitianMatrixRC.
rewrite (AdjointMatrixRCMult K M (M + N) M).
rewrite (AdjointMatrixRCInvolutive K (M + N) M A).
reflexivity.
Qed.

Definition SingularDecompositionRH : forall (M N : nat) (A : Matrix Rfield (M + N) M), exists (U : Matrix Rfield (M + N)%nat (M + N)%nat), (OrthogonalMatrix (M + N)%nat U) /\ exists (V : Matrix Rfield M M), (OrthogonalMatrix M V) /\ exists (sigma : Rn M), ((forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) /\ A = Mmult Rfield (M + N)%nat (M + N)%nat M U (Mmult Rfield (M + N)%nat M M (MBlockH Rfield M N M (MDiag Rfield M sigma) (MO Rfield N M)) (MTranspose Rfield M M V))) := SingularDecompositionRCH RK.

Definition SingularDecompositionCH : forall (M N : nat) (A : Matrix Cfield (M + N) M), exists (U : Matrix Cfield (M + N)%nat (M + N)%nat), (UnitaryMatrix (M + N)%nat U) /\ exists (V : Matrix Cfield M M), (UnitaryMatrix M V) /\ exists (sigma : Rn M), ((forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) /\ A = Mmult Cfield (M + N)%nat (M + N)%nat M U (Mmult Cfield (M + N)%nat M M (MBlockH Cfield M N M (MDiag Cfield M (fun (m : {n : nat | (n < M)%nat}) => IRC (sigma m))) (MO Cfield N M)) (AdjointMatrix M M V))) := SingularDecompositionRCH CK.

Lemma SingularValueNatureRCHSub : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M) (U : Matrix (RCfield K) (M + N) (M + N)) (V : Matrix (RCfield K) M M) (sigma : {n : nat | (n < M)%nat} -> R), UnitaryMatrixRC K (M + N) U -> UnitaryMatrixRC K M V -> ((forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2)) -> A = Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (sigma m))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)) -> (forall (m : {n : nat | (n < M)%nat}), is_max (fun (r0 : R) => exists (W : Ensemble (RCn K M)) (H1 : SubspaceVS (RCfield K) (FnVS (RCfield K) M) W) (H2 : FiniteDimensionVS (RCfield K) (SubspaceMakeVS (RCfield K) (FnVS (RCfield K) M) W H1)), DimensionSubspaceVS (RCfield K) (FnVS (RCfield K) M) W H1 H2 = S (proj1_sig m) /\ is_min (fun (r1 : R) => exists (x : RCn K M), In (RCn K M) W x /\ RCnNorm K M x = 1 /\ RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x))) = r1) r0) (sigma m)).
Proof.
move=> K.
suff: (forall (M : nat) (N : nat) (Q : Matrix (RCfield K) M N) (x y : RCn K N), Mmult (RCfield K) N M N (AdjointMatrixRC K M N Q) Q = MI (RCfield K) N -> RCnInnerProduct K M (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M N 1 Q (MVectorToMatrix (RCfield K) N x))) (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M N 1 Q (MVectorToMatrix (RCfield K) N y))) = RCnInnerProduct K N x y).
move=> H1 M N A U V sigma H2 H3 H4 H5 m.
apply conj.
exists (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig m))) (fun (n : Count (S (proj1_sig m))) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m))))).
exists (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig m))) (fun (n : Count (S (proj1_sig m))) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m))))).
suff: (FiniteDimensionVS (RCfield K) (SubspaceMakeVS (RCfield K) (FnVS (RCfield K) M) (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig m))) (fun (n : Count (S (proj1_sig m))) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m))))) (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig m))) (fun (n : Count (S (proj1_sig m))) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m))))))).
move=> H6.
exists H6.
apply conj.
apply (DimensionSubspaceVSNature2 (RCfield K) (FnVS (RCfield K) M) (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig m))) (fun (n : Count (S (proj1_sig m))) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m))))) (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig m))) (fun (n : Count (S (proj1_sig m))) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m))))) H6 (S (proj1_sig m)) (fun (n : Count (S (proj1_sig m))) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m))))).
exists (SpanContainSelfVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig m))) (fun (n : Count (S (proj1_sig m))) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m))))).
apply (proj2 (FiniteLinearlyIndependentVS (RCfield K) (FnVS (RCfield K) M) (S (proj1_sig m)) (fun (n : Count (S (proj1_sig m))) => MTranspose (RCfield K) M M V (exist (fun k : nat => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m)))))).
move=> a H7 k.
suff: (a k = RCnInnerProduct K M (VO (RCfield K) (FnVS (RCfield K) M)) (MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig k) (le_trans (S (proj1_sig k)) (S (proj1_sig m)) M (proj2_sig k) (proj2_sig m))))).
move=> H8.
rewrite H8.
apply (MySumF2O (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (FPCM (RCfield K))).
move=> u H9.
apply (Fmul_O_l (RCfield K)).
suff: (VO (RCfield K) (FnVS (RCfield K) M) = MMatrixToVector (RCfield K) M (Mmult (RCfield K) M (S (proj1_sig m)) 1 (fun (x : Count M) (y : Count (S (proj1_sig m))) => V x (exist (fun (l : nat) => (l < M)%nat) (proj1_sig y) (le_trans (S (proj1_sig y)) (S (proj1_sig m)) M (proj2_sig y) (proj2_sig m)))) (MVectorToMatrix (RCfield K) (S (proj1_sig m)) a))).
move=> H8.
rewrite H8.
suff: (MTranspose (RCfield K) M M V (exist (fun (l : nat) => (l < M)%nat) (proj1_sig k) (le_trans (S (proj1_sig k)) (S (proj1_sig m)) M (proj2_sig k) (proj2_sig m))) = MMatrixToVector (RCfield K) M (Mmult (RCfield K) M (S (proj1_sig m)) 1 (fun (x : Count M) (y : Count (S (proj1_sig m))) => V x (exist (fun (l : nat) => (l < M)%nat) (proj1_sig y) (le_trans (S (proj1_sig y)) (S (proj1_sig m)) M (proj2_sig y) (proj2_sig m)))) (MVectorToMatrix (RCfield K) (S (proj1_sig m)) (MI (RCfield K) (S (proj1_sig m)) k)))).
move=> H9.
rewrite H9.
rewrite (H1 M (S (proj1_sig m)) (fun (x : Count M) (y : Count (S (proj1_sig m))) => V x (exist (fun (l : nat) => (l < M)%nat) (proj1_sig y) (le_trans (S (proj1_sig y)) (S (proj1_sig m)) M (proj2_sig y) (proj2_sig m))))).
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count (S (proj1_sig m))) (FiniteSingleton (Count (S (proj1_sig m))) k)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
unfold MI.
elim (Nat.eq_dec (proj1_sig k) (proj1_sig k)).
move=> H10.
simpl.
rewrite ConjugateRCI.
rewrite (RCmult_comm K (a k) (RCI K)).
rewrite (RCmult_1_l K (a k)).
rewrite (RCplus_comm K (a k) (RCO K)).
rewrite (RCplus_0_l K (a k)).
reflexivity.
elim.
reflexivity.
move=> u.
elim.
move=> u0 H10 H11.
unfold MI.
elim (Nat.eq_dec (proj1_sig k) (proj1_sig u0)).
move=> H12.
elim H10.
suff: (k = u0).
move=> H13.
rewrite H13.
apply (In_singleton (Count (S (proj1_sig m))) u0).
apply sig_map.
apply H12.
move=> H12.
simpl.
rewrite ConjugateRCO.
apply (Fmul_O_r (RCfield K) (a u0)).
move=> u H10.
apply (Full_intro (Count (S (proj1_sig m))) u).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (Mmult (RCfield K) (S (proj1_sig m)) M (S (proj1_sig m)) (AdjointMatrixRC K M (S (proj1_sig m)) (fun (x0 : Count M) (y0 : Count (S (proj1_sig m))) => V x0 (exist (fun (l : nat) => (l < M)%nat) (proj1_sig y0) (le_trans (S (proj1_sig y0)) (S (proj1_sig m)) M (proj2_sig y0) (proj2_sig m))))) (fun (x0 : Count M) (y0 : Count (S (proj1_sig m))) => V x0 (exist (fun (l : nat) => (l < M)%nat) (proj1_sig y0) (le_trans (S (proj1_sig y0)) (S (proj1_sig m)) M (proj2_sig y0) (proj2_sig m)))) x y = Mmult (RCfield K) M M M (AdjointMatrixRC K M M V) V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig x) (le_trans (S (proj1_sig x)) (S (proj1_sig m)) M (proj2_sig x) (proj2_sig m))) (exist (fun (k : nat) => (k < M)%nat) (proj1_sig y) (le_trans (S (proj1_sig y)) (S (proj1_sig m)) M (proj2_sig y) (proj2_sig m)))).
move=> H10.
rewrite H10.
rewrite H3.
unfold MI.
elim (Nat.eq_dec (proj1_sig (exist (fun (k0 : nat) => (k0 < M)%nat) (proj1_sig x) (le_trans (S (proj1_sig x)) (S (proj1_sig m)) M (proj2_sig x) (proj2_sig m)))) (proj1_sig (exist (fun (k0 : nat) => (k0 < M)%nat) (proj1_sig y) (le_trans (S (proj1_sig y)) (S (proj1_sig m)) M (proj2_sig y) (proj2_sig m))))).
move=> H11.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H12.
reflexivity.
elim.
apply H11.
move=> H11.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H12.
elim (H11 H12).
move=> H12.
reflexivity.
reflexivity.
unfold Mmult.
unfold MMatrixToVector.
unfold MVectorToMatrix.
apply functional_extensionality.
move=> x.
rewrite (MySumF2Included (Count (S (proj1_sig m))) (FiniteSingleton (Count (S (proj1_sig m))) k)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
unfold MI.
elim (Nat.eq_dec (proj1_sig k) (proj1_sig k)).
move=> H9.
simpl.
rewrite RCmult_comm.
rewrite RCmult_1_l.
rewrite RCplus_comm.
rewrite RCplus_0_l.
reflexivity.
elim.
reflexivity.
move=> u.
elim.
move=> u0 H9 H10.
unfold MI.
elim (Nat.eq_dec (proj1_sig k) (proj1_sig u0)).
move=> H11.
elim H9.
suff: (k = u0).
move=> H12.
rewrite H12.
apply (In_singleton (Count (S (proj1_sig m))) u0).
apply sig_map.
apply H11.
move=> H11.
apply (Fmul_O_r (RCfield K)).
move=> u H9.
apply (Full_intro (Count (S (proj1_sig m))) u).
rewrite - H7.
apply functional_extensionality.
move=> x.
unfold Mmult.
unfold MMatrixToVector.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S (proj1_sig m))%nat} (exist (Finite {n : nat | (n < S (proj1_sig m))%nat}) (Full_set {n : nat | (n < S (proj1_sig m))%nat}) (CountFinite (S (proj1_sig m))))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H8 H9 H10 H11.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H11.
rewrite RCmult_comm.
reflexivity.
apply H10.
apply H10.
suff: (forall (M N : nat) (Q : Matrix (RCfield K) M N) (x : RCn K N), Mmult (RCfield K) N M N (AdjointMatrixRC K M N Q) Q = MI (RCfield K) N -> RCnNorm K M (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M N 1 Q (MVectorToMatrix (RCfield K) N x))) = RCnNorm K N x).
move=> H7.
apply conj.
exists (MTranspose (RCfield K) M M V m).
apply conj.
suff: (m = exist (fun (k : nat) => (k < M)%nat) (proj1_sig (exist (fun (l : nat) => (l < S (proj1_sig m))%nat) (proj1_sig m) (le_n (S (proj1_sig m))))) (le_trans (S (proj1_sig (exist (fun (l : nat) => (l < S (proj1_sig m))%nat) (proj1_sig m) (le_n (S (proj1_sig m)))))) (S (proj1_sig m)) M (proj2_sig (exist (fun (l : nat) => (l < S (proj1_sig m))%nat) (proj1_sig m) (le_n (S (proj1_sig m))))) (proj2_sig m))).
move=> H8.
rewrite {8} H8.
apply (SpanContainSelfVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig m))) (fun (n : Count (S (proj1_sig m))) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m))))).
apply sig_map.
reflexivity.
apply conj.
apply RCnNormNature2.
apply conj.
left.
apply Rlt_0_1.
simpl.
rewrite RCnInnerProductMatrix.
rewrite (Rmult_1_l 1).
suff: (Mmult (RCfield K) 1 M 1 (AdjointMatrixRC K M 1 (MVectorToMatrix (RCfield K) M (MTranspose (RCfield K) M M V m))) (MVectorToMatrix (RCfield K) M (MTranspose (RCfield K) M M V m)) Single Single = Mmult (RCfield K) M M M (AdjointMatrixRC K M M V) V m m).
move=> H8.
rewrite H8.
suff: (Mmult (RCfield K) M M M (AdjointMatrixRC K M M V) V = MI (RCfield K) M).
move=> H9.
rewrite H9.
unfold MI.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H10.
suff: (forall (K : RC), RCRe K (ConjugateRC K (FI (RCfield K))) = 1).
move=> H11.
apply (H11 K).
elim.
reflexivity.
simpl.
rewrite ConjugateCI.
apply (CmakeRe 1 0).
elim.
reflexivity.
apply H3.
reflexivity.
rewrite H5.
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) M 1).
rewrite - (proj2 (MVectorMatrixRelation (RCfield K) (M + N)) (Mmult (RCfield K) (M + N) M 1 (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => IRRC K (sigma l))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)) (MVectorToMatrix (RCfield K) M (MTranspose (RCfield K) M M V m)))).
rewrite (H7 (M + N)%nat (M + N)%nat U).
rewrite (Mmult_assoc (RCfield K) (M + N) M M 1).
apply RCnNormNature2.
apply conj.
apply (proj1 H4 m).
simpl.
unfold RCnInnerProduct.
suff: (Mmult (RCfield K) M M 1 (AdjointMatrixRC K M M V) (MVectorToMatrix (RCfield K) M (MTranspose (RCfield K) M M V m)) = MVectorToMatrix (RCfield K) M (MI (RCfield K) M m)).
move=> H8.
rewrite H8.
rewrite (MySumF2Included (Count (M + N)) (FiniteSingleton (Count (M + N)) (AddConnect M N (inl m)))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
unfold Mmult.
unfold MMatrixToVector.
rewrite (MySumF2Included (Count M) (FiniteSingleton (Count M) m)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
unfold MBlockH.
rewrite (proj1 (AddConnectInvRelation M N) (inl m)).
unfold MDiag.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H9.
unfold MVectorToMatrix.
unfold MI.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H10.
rewrite (Fmul_I_r (RCfield K) (IRRC K (sigma m))).
suff: (forall (K : RC) (r : R), ConjugateRC K (IRRC K r) = IRRC K r).
move=> H11.
suff: (forall (K : RC) (r : R), RCRe K (IRRC K r) = r).
move=> H12.
rewrite (H11 K (sigma m)).
rewrite - (IRRCmult K (sigma m) (sigma m)).
apply (H12 K (sigma m * sigma m)).
elim.
move=> r.
reflexivity.
move=> r.
apply (CmakeRe r 0).
elim.
move=> r.
reflexivity.
move=> r.
simpl.
unfold Conjugate.
unfold IRC.
rewrite (CmakeRe r 0).
rewrite (CmakeIm r 0).
rewrite Ropp_0.
reflexivity.
elim.
reflexivity.
elim.
reflexivity.
move=> u.
elim.
move=> u0 H9 H10.
unfold MVectorToMatrix.
unfold MI.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig u0)).
move=> H11.
elim H9.
suff: (m = u0).
move=> H12.
rewrite H12.
apply (In_singleton (Count M) u0).
apply sig_map.
apply H11.
move=> H11.
apply (Fmul_O_r (RCfield K)).
move=> u H9.
apply (Full_intro (Count M) u).
move=> u.
elim.
move=> u0 H9 H10.
unfold MMatrixToVector.
unfold MVectorToMatrix.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < M)%nat} (FiniteSingleton {n : nat | (n < M)%nat} m)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
unfold MI.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H11.
suff: (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => IRRC K (sigma l))) (MO (RCfield K) N M) u0 m = RCO K).
move=> H12.
rewrite H12.
rewrite (Fmul_I_r (RCfield K) (RCO K)).
apply (Fmul_O_l (RCfield K)).
unfold MBlockH.
suff: (proj1_sig u0 <> proj1_sig m).
rewrite - {1} (proj2 (AddConnectInvRelation M N) u0).
elim (AddConnectInv M N u0).
move=> u1.
rewrite - (proj1 (AddConnectNature M N) u1).
move=> H12.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig u1) (proj1_sig m)).
move=> H13.
elim (H12 H13).
move=> H13.
reflexivity.
move=> u1 H12.
reflexivity.
move=> H12.
apply H9.
suff: (u0 = AddConnect M N (inl m)).
move=> H13.
rewrite H13.
apply (In_singleton (Count (M + N)) (AddConnect M N (inl m))).
apply sig_map.
rewrite H12.
apply (proj1 (AddConnectNature M N) m).
elim.
reflexivity.
move=> u1.
elim.
move=> u2 H11 H12.
unfold MI.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig u2)).
move=> H13.
elim H11.
suff: (m = u2).
move=> H14.
rewrite H14.
apply (In_singleton {n : nat | (n < M)%nat} u2).
apply sig_map.
apply H13.
move=> H13.
apply (Fmul_O_r (RCfield K)).
move=> u1 H11.
apply (Full_intro {n : nat | (n < M)%nat} u1).
move=> u H9.
apply (Full_intro {n : nat | (n < M + N)%nat} u).
rewrite - (MTransI (RCfield K)).
rewrite - H3.
apply functional_extensionality.
move=> z.
apply functional_extensionality.
move=> w.
unfold MVectorToMatrix.
unfold Mmult.
apply MySumF2Same.
move=> u H8.
reflexivity.
apply H2.
move=> r.
elim.
move=> v.
rewrite FiniteSpanVS.
elim.
elim.
move=> a H8.
rewrite H8.
move=> H9.
rewrite - (proj2 H9).
suff: (MVectorToMatrix (RCfield K) M (MySumF2 (Count (S (proj1_sig m))) (exist (Finite (Count (S (proj1_sig m)))) (Full_set (Count (S (proj1_sig m)))) (CountFinite (S (proj1_sig m)))) (VSPCM (RCfield K) (FnVS (RCfield K) M)) (fun (n : Count (S (proj1_sig m))) => Vmul (RCfield K) (FnVS (RCfield K) M) (a n) (MTranspose (RCfield K) M M V (exist (fun k : nat => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m)))))) = Mmult (RCfield K) M M 1 V (MVectorToMatrix (RCfield K) M (fun (n : Count M) => match excluded_middle_informative (proj1_sig n < S (proj1_sig m))%nat with
  | left H => a (exist (fun (l : nat) => (l < S (proj1_sig m))%nat) (proj1_sig n) H)
  | right _ => RCO K
end))).
move=> H10.
rewrite H10.
rewrite H5.
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) M 1).
rewrite (Mmult_assoc (RCfield K) (M + N) M M 1).
rewrite - (Mmult_assoc (RCfield K) M M M 1).
rewrite H3.
rewrite (Mmult_I_l (RCfield K) M 1).
suff: (Mmult (RCfield K) (M + N) M 1 (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => IRRC K (sigma l))) (MO (RCfield K) N M)) (MVectorToMatrix (RCfield K) M (fun (n : Count M) => match excluded_middle_informative (proj1_sig n < S (proj1_sig m))%nat with
  | left H => a (exist (fun (l : nat) => (l < S (proj1_sig m))%nat) (proj1_sig n) H)
  | right _ => RCO K
end)) = MVectorToMatrix (RCfield K) (M + N) ((fun (n : Count (M + N)) => match excluded_middle_informative (proj1_sig n < S (proj1_sig m))%nat with
  | left H => RCmult K (IRRC K (sigma (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M H (proj2_sig m))))) (a (exist (fun (l : nat) => (l < S (proj1_sig m))%nat) (proj1_sig n) H))
  | right _ => RCO K
end))).
move=> H11.
rewrite H11.
rewrite (H7 (M + N)%nat (M + N)%nat U).
suff: (forall (r1 r2 : R), r1 >= 0 -> r2 >= 0 -> r1 * r1 >= r2 * r2 -> r1 >= r2).
move=> H12.
apply H12.
apply RCnNormNature.
apply (proj1 H4 m).
rewrite - (proj2 (RCnNormNature K (M + N) (fun n : Count (M + N) => match excluded_middle_informative (proj1_sig n < S (proj1_sig m))%nat with
  | left H => RCmult K (IRRC K (sigma (exist (fun k : nat => (k < M)%nat) (proj1_sig n) (Nat.le_trans (S (proj1_sig n)) (S (proj1_sig m)) M H (proj2_sig m))))) (a (exist (fun l : nat => (l < S (proj1_sig m))%nat) (proj1_sig n) H))
  | right _ => RCO K
end))).
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count (M + N)) (FiniteIntersection (Count (M + N)) (exist (Finite (Count (M + N))) (Full_set (Count (M + N))) (CountFinite (M + N))) (fun (n : Count (M + N)) => (proj1_sig n < S (proj1_sig m))%nat))).
suff: (FiniteIntersection (Count (M + N)) (exist (Finite (Count (M + N))) (Full_set (Count (M + N))) (CountFinite (M + N))) (fun (n : Count (M + N)) => (proj1_sig n < S (proj1_sig m))%nat) = FiniteIm (Count (S (proj1_sig m))) (Count (M + N)) (fun (n : Count (S (proj1_sig m))) => (AddConnect M N (inl (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m)))))) (exist (Finite (Count (S (proj1_sig m)))) (Full_set (Count (S (proj1_sig m)))) (CountFinite (S (proj1_sig m))))).
move=> H13.
rewrite H13.
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count (M + N))).
rewrite CM_O_r.
rewrite - (Rmult_1_r (sigma m * sigma m)).
suff: (1 = RCRe K (RCnInnerProduct K (S (proj1_sig m)) a a)).
move=> H14.
rewrite H14.
unfold RCnInnerProduct.
apply (FiniteSetInduction (Count (S (proj1_sig m))) (exist (Finite (Count (S (proj1_sig m)))) (Full_set (Count (S (proj1_sig m)))) (CountFinite (S (proj1_sig m))))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
right.
suff: (sigma m * sigma m * RCRe K (RCO K) = RCRe K (RCO K)).
move=> H15.
rewrite H15.
reflexivity.
suff: (RCRe K (RCO K) = 0).
move=> H15.
rewrite H15.
apply (Rmult_0_r (sigma m * sigma m)).
elim K.
reflexivity.
reflexivity.
move=> B b H15 H16 H17 H18.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
unfold Basics.compose.
rewrite - (proj1 (AddConnectNature M N)).
simpl.
elim (excluded_middle_informative (proj1_sig b < S (proj1_sig m)))%nat.
move=> H19.
suff: ((exist (fun (l : nat) => (l < S (proj1_sig m))%nat) (proj1_sig b) H19) = b).
move=> H20.
rewrite H20.
rewrite RCReplus.
rewrite RCReplus.
rewrite Rmult_plus_distr_l.
apply Rplus_ge_compat.
apply H18.
unfold Basics.compose.
rewrite Proposition_4_8_2_RC.
rewrite RCmult_assoc.
rewrite (RCmult_comm K (a b)).
rewrite RCmult_assoc.
rewrite - RCmult_assoc.
rewrite (RCmult_comm K (a b)).
suff: (forall (K : RC) (r : R), ConjugateRC K (IRRC K r) = IRRC K r).
move=> H21.
suff: (forall (K : RC) (r : R) (c : RCT K), RCRe K (RCmult K (IRRC K r) c) = r * RCRe K c).
move=> H22.
rewrite (H21 K).
rewrite - (IRRCmult K).
rewrite (H22 K).
apply Rmult_ge_compat_r.
suff: (forall (K : RC) (c : RCT K), RCRe K (RCmult K (ConjugateRC K c) c) >= 0).
move=> H23.
apply (H23 K (a b)).
elim.
apply Formula_1_3.
move=> c.
simpl.
unfold Cmult.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
unfold Rminus.
rewrite Ropp_mult_distr_l.
rewrite Ropp_involutive.
rewrite - (Rplus_0_l 0).
apply Rplus_ge_compat.
apply Formula_1_3.
apply Formula_1_3.
apply Rmult_ge_compat.
apply (proj1 H4 m).
apply (proj1 H4 m).
apply (proj2 H4).
apply (le_S_n (proj1_sig b) (proj1_sig m) (proj2_sig b)).
apply (proj2 H4).
apply (le_S_n (proj1_sig b) (proj1_sig m) (proj2_sig b)).
elim.
move=> r1 r2.
reflexivity.
move=> r0 c.
simpl.
unfold IRC.
unfold Cmult.
rewrite (CmakeRe r0 0).
rewrite (CmakeIm r0 0).
rewrite (Rmult_0_l (c CIm)).
rewrite Rminus_0_r.
apply CmakeRe.
elim.
move=> r0.
reflexivity.
move=> r0.
simpl.
unfold Conjugate.
unfold IRC.
rewrite (CmakeRe r0 0).
rewrite (CmakeIm r0 0).
rewrite Ropp_0.
reflexivity.
apply sig_map.
reflexivity.
move=> H19.
elim (H19 (proj2_sig b)).
apply H17.
apply H17.
rewrite - (Rmult_1_r 1).
rewrite - (proj1 H9).
rewrite - (proj2 (RCnNormNature K M (MySumF2 (Count (S (proj1_sig m))) (exist (Finite (Count (S (proj1_sig m)))) (Full_set (Count (S (proj1_sig m)))) (CountFinite (S (proj1_sig m)))) (VSPCM (RCfield K) (FnVS (RCfield K) M)) (fun n : Count (S (proj1_sig m)) => Vmul (RCfield K) (FnVS (RCfield K) M) (a n) (MTranspose (RCfield K) M M V (exist (fun k : nat => (k < M)%nat) (proj1_sig n) (Nat.le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m)))))))).
suff: (MySumF2 (Count (S (proj1_sig m))) (exist (Finite (Count (S (proj1_sig m)))) (Full_set (Count (S (proj1_sig m)))) (CountFinite (S (proj1_sig m)))) (VSPCM (RCfield K) (FnVS (RCfield K) M)) (fun (n : Count (S (proj1_sig m))) => Fnmul (RCfield K) M (a n) (MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m))))) = (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M (S (proj1_sig m)) 1 (fun (x : Count M) (y : Count (S (proj1_sig m))) => V x (exist (fun (l : nat) => (l < M)%nat) (proj1_sig y) (le_trans (S (proj1_sig y)) (S (proj1_sig m)) M (proj2_sig y) (proj2_sig m)))) (MVectorToMatrix (RCfield K) (S (proj1_sig m)) a)))).
move=> H14.
rewrite H14.
rewrite (H1 M (S (proj1_sig m)) (fun (x : Count M) (y : Count (S (proj1_sig m))) => V x (exist (fun (l : nat) => (l < M)%nat) (proj1_sig y) (le_trans (S (proj1_sig y)) (S (proj1_sig m)) M (proj2_sig y) (proj2_sig m)))) a).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (Mmult (RCfield K) (S (proj1_sig m)) M (S (proj1_sig m)) (AdjointMatrixRC K M (S (proj1_sig m)) (fun (x0 : Count M) (y0 : Count (S (proj1_sig m))) => V x0 (exist (fun (l : nat) => (l < M)%nat) (proj1_sig y0) (le_trans (S (proj1_sig y0)) (S (proj1_sig m)) M (proj2_sig y0) (proj2_sig m))))) (fun (x0 : Count M) (y0 : Count (S (proj1_sig m))) => V x0 (exist (fun (l : nat) => (l < M)%nat) (proj1_sig y0) (le_trans (S (proj1_sig y0)) (S (proj1_sig m)) M (proj2_sig y0) (proj2_sig m)))) x y = Mmult (RCfield K) M M M (AdjointMatrixRC K M M V) V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig x) (le_trans (S (proj1_sig x)) (S (proj1_sig m)) M (proj2_sig x) (proj2_sig m))) (exist (fun (k : nat) => (k < M)%nat) (proj1_sig y) (le_trans (S (proj1_sig y)) (S (proj1_sig m)) M (proj2_sig y) (proj2_sig m)))).
move=> H15.
rewrite H15.
rewrite H3.
unfold MI.
elim (Nat.eq_dec (proj1_sig (exist (fun (k0 : nat) => (k0 < M)%nat) (proj1_sig x) (le_trans (S (proj1_sig x)) (S (proj1_sig m)) M (proj2_sig x) (proj2_sig m)))) (proj1_sig (exist (fun (k0 : nat) => (k0 < M)%nat) (proj1_sig y) (le_trans (S (proj1_sig y)) (S (proj1_sig m)) M (proj2_sig y) (proj2_sig m))))).
move=> H16.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H17.
reflexivity.
elim.
apply H16.
move=> H16.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H17.
elim (H16 H17).
move=> H17.
reflexivity.
reflexivity.
apply functional_extensionality.
move=> x.
unfold MMatrixToVector.
unfold Mmult.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S (proj1_sig m))%nat} (exist (Finite {n : nat | (n < S (proj1_sig m))%nat}) (Full_set {n : nat | (n < S (proj1_sig m))%nat}) (CountFinite (S (proj1_sig m))))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H14 H15 H16 H17.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H17.
rewrite RCmult_comm.
reflexivity.
apply H16.
apply H16.
move=> u.
elim.
move=> u0 H14 H15.
elim (excluded_middle_informative (proj1_sig u0 < S (proj1_sig m))%nat).
move=> H16.
elim H14.
apply (Im_intro (Count (S (proj1_sig m))) (Count (M + N)) (Full_set (Count (S (proj1_sig m)))) (fun (n : Count (S (proj1_sig m))) => AddConnect M N (inl (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m))))) (exist (fun (k : nat) => (k < S (proj1_sig m))%nat) (proj1_sig u0) H16)).
apply (Full_intro (Count (S (proj1_sig m)))).
apply sig_map.
rewrite - (proj1 (AddConnectNature M N)).
reflexivity.
move=> H16.
apply (Fmul_O_l (RCfield K)).
move=> u1 u2 H14 H15 H16.
apply sig_map.
suff: (proj1_sig u1 = proj1_sig (AddConnect M N (inl (exist (fun (k : nat) => (k < M)%nat) (proj1_sig u1) (le_trans (S (proj1_sig u1)) (S (proj1_sig m)) M (proj2_sig u1) (proj2_sig m)))))).
move=> H17.
rewrite H17.
rewrite H16.
rewrite - (proj1 (AddConnectNature M N) (exist (fun (k : nat) => (k < M)%nat) (proj1_sig u2) (le_trans (S (proj1_sig u2)) (S (proj1_sig m)) M (proj2_sig u2) (proj2_sig m)))).
reflexivity.
apply (proj1 (AddConnectNature M N) (exist (fun (k : nat) => (k < M)%nat) (proj1_sig u1) (le_trans (S (proj1_sig u1)) (S (proj1_sig m)) M (proj2_sig u1) (proj2_sig m)))).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u.
elim.
move=> u0 H13 H14.
apply (Im_intro (Count (S (proj1_sig m))) (Count (M + N)) (Full_set (Count (S (proj1_sig m)))) (fun (n : Count (S (proj1_sig m))) => AddConnect M N (inl (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m))))) (exist (fun (k : nat) => (k < S (proj1_sig m))%nat) (proj1_sig u0) H13)).
apply (Full_intro (Count (S (proj1_sig m))) (exist (fun (k : nat) => (k < S (proj1_sig m))%nat) (proj1_sig u0) H13)).
apply sig_map.
apply (proj1 (AddConnectNature M N) (exist (fun (k : nat) => (k < M)%nat) (proj1_sig (exist (fun (k : nat) => (k < S (proj1_sig m))%nat) (proj1_sig u0) H13)) (le_trans (S (proj1_sig (exist (fun (k : nat) => (k < S (proj1_sig m))%nat) (proj1_sig u0) H13))) (S (proj1_sig m)) M (proj2_sig (exist (fun (k : nat) => (k < S (proj1_sig m))%nat) (proj1_sig u0) H13)) (proj2_sig m)))).
move=> u1.
elim.
move=> x H13 y H14.
rewrite H14.
apply (Intersection_intro (Count (M + N))).
unfold In.
rewrite - (proj1 (AddConnectNature M N)).
apply (proj2_sig x).
apply (Full_intro (Count (M + N))).
move=> u H13.
apply (Full_intro (Count (M + N)) u).
move=> r1 r2 H12 H13 H14.
apply (Rnot_gt_ge r2 r1).
move=> H15.
apply (Rge_not_gt (r2 * r2) (r1 * r1) H14).
apply (Rmult_le_0_lt_compat r1 r2 r1 r2 (Rge_le r1 0 H12) (Rge_le r1 0 H12) H15 H15).
apply H2.
rewrite (MBlockHMult (RCfield K) M N M 1).
rewrite (Mmult_O_l (RCfield K) N M 1).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
rewrite - {2} (proj2 (AddConnectInvRelation M N) x).
elim (AddConnectInv M N x).
move=> x0.
unfold MVectorToMatrix.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < M)%nat} (FiniteSingleton {n : nat | (n < M)%nat} x0)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
rewrite - (proj1 (AddConnectNature M N) x0).
elim (excluded_middle_informative (proj1_sig x0 < S (proj1_sig m))%nat).
move=> H11.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig x0)).
move=> H12.
suff: (x0 = (exist (fun (k : nat) => (k < M)%nat) (proj1_sig x0) (le_trans (S (proj1_sig x0)) (S (proj1_sig m)) M H11 (proj2_sig m)))).
move=> H13.
rewrite {1} H13.
reflexivity.
apply sig_map.
reflexivity.
elim.
reflexivity.
move=> H11.
apply (Fmul_O_r (RCfield K) (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => IRRC K (sigma l)) x0 x0)).
move=> u.
elim.
move=> u0 H11 H12.
elim (excluded_middle_informative (proj1_sig u0 < S (proj1_sig m))%nat).
move=> H13.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig u0)).
move=> H14.
elim H11.
suff: (x0 = u0).
move=> H15.
rewrite H15.
apply (In_singleton (Count M) u0).
apply sig_map.
apply H14.
move=> H14.
apply (Fmul_O_l (RCfield K)).
move=> H13.
apply (Fmul_O_r (RCfield K)).
move=> u H11.
apply (Full_intro (Count M) u).
move=> x0.
unfold MVectorToMatrix.
elim (excluded_middle_informative (proj1_sig (AddConnect M N (inr x0)) < S (proj1_sig m))%nat).
move=> H11.
apply False_ind.
apply (le_not_lt (S (proj1_sig m)) (proj1_sig (AddConnect M N (inr x0)))).
rewrite - (proj2 (AddConnectNature M N) x0).
apply (le_trans (S (proj1_sig m)) M (M + proj1_sig x0) (proj2_sig m) (le_plus_l M (proj1_sig x0))).
apply H11.
move=> H11.
reflexivity.
suff: (forall (n : nat) (H1 H2 : (n <= M)%nat) (A : Matrix (RCfield K) M M) (x : RCn K M), (forall (k : Count M), (proj1_sig k >= n)%nat -> x k = RCO K) -> Mmult (RCfield K) M M 1 A (MVectorToMatrix (RCfield K) M x) = Mmult (RCfield K) M n 1 (fun (y : Count M) (z : Count n) => A y (exist (fun (l : nat) => (l < M)%nat) (proj1_sig z) (le_trans (S (proj1_sig z)) n M (proj2_sig z) H2))) (MVectorToMatrix (RCfield K) n (fun (k : Count n) => x (exist (fun (l : nat) => (l < M)%nat) (proj1_sig k) (le_trans (S (proj1_sig k)) n M (proj2_sig k) H2))))).
move=> H10.
rewrite (H10 (S (proj1_sig m)) (proj2_sig m) (proj2_sig m) V).
unfold MVectorToMatrix.
unfold Mmult.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S (proj1_sig m))%nat} (exist (Finite {n : nat | (n < S (proj1_sig m))%nat}) (Full_set {n : nat | (n < S (proj1_sig m))%nat}) (CountFinite (S (proj1_sig m))))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H11 H12 H13 H14.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H14.
elim (excluded_middle_informative (proj1_sig b < S (proj1_sig m))%nat).
move=> H15.
rewrite RCmult_comm.
suff: ((exist (fun (l : nat) => (l < S (proj1_sig m))%nat) (proj1_sig b) H15) = b).
move=> H16.
rewrite H16.
reflexivity.
apply sig_map.
reflexivity.
move=> H15.
elim (H15 (proj2_sig b)).
apply H13.
apply H13.
move=> k H11.
elim (excluded_middle_informative (proj1_sig k < S (proj1_sig m))%nat).
move=> H12.
elim (le_not_lt (S (proj1_sig m)) (proj1_sig k) H11 H12).
move=> H12.
reflexivity.
move=> n H10.
suff: (M = n + (M - n))%nat.
move=> H11.
rewrite H11.
move=> H12 B x H13.
suff: (B = MBlockW (RCfield K) (n + (M - n)) n (M - n) (fun (y : Count (n + (M - n))) (z : Count n) => B y (exist (fun (l : nat) => (l < n + (M - n))%nat) (proj1_sig z) (le_trans (S (proj1_sig z)) n (n + (M - n)) (proj2_sig z) H12))) (fun (y : Count (n + (M - n))) (z : Count (M - n)) => B y (AddConnect n (M - n) (inr z)))).
move=> H14.
rewrite {1} H14.
suff: (MVectorToMatrix (RCfield K) (n + (M - n)) x = MBlockH (RCfield K) n (M - n) 1 (MVectorToMatrix (RCfield K) n (fun (k : Count n) => x (exist (fun (l : nat) => (l < n + (M - n))%nat) (proj1_sig k) (le_trans (S (proj1_sig k)) n (n + (M - n)) (proj2_sig k) H12)))) (MO (RCfield K) (M - n) 1)).
move=> H15.
rewrite H15.
rewrite (MBlockHWMult (RCfield K) (n + (M - n)) n (M - n) 1).
rewrite (Mmult_O_r (RCfield K) (n + (M - n)) (M - n) 1).
rewrite (Mplus_comm (RCfield K) (n + (M - n)) 1).
apply (Mplus_O_l (RCfield K) (n + (M - n)) 1).
apply functional_extensionality.
move=> z.
apply functional_extensionality.
move=> w.
unfold MBlockH.
rewrite - {1} (proj2 (AddConnectInvRelation n (M - n)) z).
elim (AddConnectInv n (M - n) z).
move=> z0.
unfold MVectorToMatrix.
suff: (AddConnect n (M - n) (inl z0) = (exist (fun (l : nat) => (l < n + (M - n))%nat) (proj1_sig z0) (le_trans (S (proj1_sig z0)) n (n + (M - n)) (proj2_sig z0) H12))).
move=> H15.
rewrite H15.
reflexivity.
apply sig_map.
rewrite - (proj1 (AddConnectNature n (M - n)) z0).
reflexivity.
move=> z0.
apply (H13 (AddConnect n (M - n) (inr z0))).
rewrite - (proj2 (AddConnectNature n (M - n)) z0).
apply (le_plus_l n (proj1_sig z0)).
apply functional_extensionality.
move=> z.
apply functional_extensionality.
move=> w.
unfold MBlockW.
rewrite - {1} (proj2 (AddConnectInvRelation n (M - n)) w).
elim (AddConnectInv n (M - n) w).
move=> w0.
suff: (AddConnect n (M - n) (inl w0) = (exist (fun (l : nat) => (l < n + (M - n))%nat) (proj1_sig w0) (le_trans (S (proj1_sig w0)) n (n + (M - n)) (proj2_sig w0) H12))).
move=> H14.
rewrite H14.
reflexivity.
apply sig_map.
rewrite - (proj1 (AddConnectNature n (M - n)) w0).
reflexivity.
move=> w0.
reflexivity.
apply (le_plus_minus n M H10).
move=> M0 N0 Q x H7.
apply RCnNormNature2.
apply conj.
apply RCnNormNature.
rewrite - (proj2 (RCnNormNature K N0 x)).
rewrite (H1 M0 N0 Q x x H7).
reflexivity.
exists (S (proj1_sig m)).
exists (fun (l : Count (S (proj1_sig m))) => exist (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig m))) (fun (n : Count (S (proj1_sig m))) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m))))) (MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig l) (le_trans (S (proj1_sig l)) (S (proj1_sig m)) M (proj2_sig l) (proj2_sig m)))) (SpanContainSelfVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig m))) (fun (n : Count (S (proj1_sig m))) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m)))) l)).
apply (proj2 (FiniteLinearlyIndependentVS (RCfield K) (FnVS (RCfield K) M) (S (proj1_sig m)) (fun (n : Count (S (proj1_sig m))) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (S (proj1_sig m)) M (proj2_sig n) (proj2_sig m)))))).
move=> a H6 k.
suff: (a k = RCnInnerProduct K M (VO (RCfield K) (FnVS (RCfield K) M)) (MTranspose (RCfield K) M M V (exist (fun k : nat => (k < M)%nat) (proj1_sig k) (le_trans (S (proj1_sig k)) (S (proj1_sig m)) M (proj2_sig k) (proj2_sig m))))).
move=> H7.
rewrite H7.
unfold RCnInnerProduct.
apply (MySumF2O (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (FPCM (RCfield K))).
move=> u H8.
apply (Fmul_O_l (RCfield K)).
suff: (VO (RCfield K) (FnVS (RCfield K) M) = MMatrixToVector (RCfield K) M (Mmult (RCfield K) M (S (proj1_sig m)) 1 (fun (x : Count M) (y : Count (S (proj1_sig m))) => V x (exist (fun (l : nat) => (l < M)%nat) (proj1_sig y) (le_trans (S (proj1_sig y)) (S (proj1_sig m)) M (proj2_sig y) (proj2_sig m)))) (MVectorToMatrix (RCfield K) (S (proj1_sig m)) a))).
move=> H7.
rewrite H7.
suff: (MTranspose (RCfield K) M M V (exist (fun (l : nat) => (l < M)%nat) (proj1_sig k) (le_trans (S (proj1_sig k)) (S (proj1_sig m)) M (proj2_sig k) (proj2_sig m))) = MMatrixToVector (RCfield K) M (Mmult (RCfield K) M (S (proj1_sig m)) 1 (fun (x : Count M) (y : Count (S (proj1_sig m))) => V x (exist (fun (l : nat) => (l < M)%nat) (proj1_sig y) (le_trans (S (proj1_sig y)) (S (proj1_sig m)) M (proj2_sig y) (proj2_sig m)))) (MVectorToMatrix (RCfield K) (S (proj1_sig m)) (MI (RCfield K) (S (proj1_sig m)) k)))).
move=> H8.
rewrite H8.
rewrite (H1 M (S (proj1_sig m)) (fun (x : Count M) (y : Count (S (proj1_sig m))) => V x (exist (fun (l : nat) => (l < M)%nat) (proj1_sig y) (le_trans (S (proj1_sig y)) (S (proj1_sig m)) M (proj2_sig y) (proj2_sig m))))).
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count (S (proj1_sig m))) (FiniteSingleton (Count (S (proj1_sig m))) k)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
unfold MI.
elim (Nat.eq_dec (proj1_sig k) (proj1_sig k)).
move=> H9.
simpl.
rewrite ConjugateRCI.
rewrite RCmult_comm.
rewrite (RCmult_1_l K (a k)).
rewrite RCplus_comm.
rewrite (RCplus_0_l K (a k)).
reflexivity.
elim.
reflexivity.
move=> u.
elim.
move=> u0 H9 H10.
unfold MI.
elim (Nat.eq_dec (proj1_sig k) (proj1_sig u0)).
move=> H11.
elim H9.
suff: (k = u0).
move=> H12.
rewrite H12.
apply (In_singleton (Count (S (proj1_sig m))) u0).
apply sig_map.
apply H11.
move=> H11.
simpl.
rewrite ConjugateRCO.
apply (Fmul_O_r (RCfield K) (a u0)).
move=> u H9.
apply (Full_intro (Count (S (proj1_sig m))) u).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (Mmult (RCfield K) (S (proj1_sig m)) M (S (proj1_sig m)) (AdjointMatrixRC K M (S (proj1_sig m)) (fun (x0 : Count M) (y0 : Count (S (proj1_sig m))) => V x0 (exist (fun (l : nat) => (l < M)%nat) (proj1_sig y0) (le_trans (S (proj1_sig y0)) (S (proj1_sig m)) M (proj2_sig y0) (proj2_sig m))))) (fun (x0 : Count M) (y0 : Count (S (proj1_sig m))) => V x0 (exist (fun (l : nat) => (l < M)%nat) (proj1_sig y0) (le_trans (S (proj1_sig y0)) (S (proj1_sig m)) M (proj2_sig y0) (proj2_sig m)))) x y = Mmult (RCfield K) M M M (AdjointMatrixRC K M M V) V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig x) (le_trans (S (proj1_sig x)) (S (proj1_sig m)) M (proj2_sig x) (proj2_sig m))) (exist (fun (k : nat) => (k < M)%nat) (proj1_sig y) (le_trans (S (proj1_sig y)) (S (proj1_sig m)) M (proj2_sig y) (proj2_sig m)))).
move=> H9.
rewrite H9.
rewrite H3.
unfold MI.
elim (Nat.eq_dec (proj1_sig (exist (fun (k0 : nat) => (k0 < M)%nat) (proj1_sig x) (le_trans (S (proj1_sig x)) (S (proj1_sig m)) M (proj2_sig x) (proj2_sig m)))) (proj1_sig (exist (fun (k0 : nat) => (k0 < M)%nat) (proj1_sig y) (le_trans (S (proj1_sig y)) (S (proj1_sig m)) M (proj2_sig y) (proj2_sig m))))).
move=> H10.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H11.
reflexivity.
elim.
apply H10.
move=> H10.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H11.
elim (H10 H11).
move=> H11.
reflexivity.
reflexivity.
unfold Mmult.
unfold MMatrixToVector.
unfold MVectorToMatrix.
apply functional_extensionality.
move=> x.
rewrite (MySumF2Included (Count (S (proj1_sig m))) (FiniteSingleton (Count (S (proj1_sig m))) k)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
unfold MI.
elim (Nat.eq_dec (proj1_sig k) (proj1_sig k)).
move=> H8.
simpl.
rewrite RCmult_comm.
rewrite RCmult_1_l.
rewrite RCplus_comm.
rewrite RCplus_0_l.
reflexivity.
elim.
reflexivity.
move=> u.
elim.
move=> u0 H8 H9.
unfold MI.
elim (Nat.eq_dec (proj1_sig k) (proj1_sig u0)).
move=> H10.
elim H8.
suff: (k = u0).
move=> H11.
rewrite H11.
apply (In_singleton (Count (S (proj1_sig m))) u0).
apply sig_map.
apply H10.
move=> H10.
apply (Fmul_O_r (RCfield K)).
move=> u H8.
apply (Full_intro (Count (S (proj1_sig m))) u).
rewrite - H6.
apply functional_extensionality.
move=> x.
unfold Mmult.
unfold MMatrixToVector.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S (proj1_sig m))%nat} (exist (Finite {n : nat | (n < S (proj1_sig m))%nat}) (Full_set {n : nat | (n < S (proj1_sig m))%nat}) (CountFinite (S (proj1_sig m))))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H7 H8 H9 H10.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H10.
rewrite RCmult_comm.
reflexivity.
apply H9.
apply H9.
suff: (forall (n : nat), n < M - (proj1_sig m) -> proj1_sig m + n < M)%nat.
move=> H6.
suff: (forall (W : Ensemble (RCn K M)) (H7 : SubspaceVS (RCfield K) (FnVS (RCfield K) M) W) (H8 : FiniteDimensionVS (RCfield K) (SubspaceMakeVS (RCfield K) (FnVS (RCfield K) M) W H7)), DimensionSubspaceVS (RCfield K) (FnVS (RCfield K) M) W H7 H8 = S (proj1_sig m) -> exists (x : RCn K M), In (RCn K M) W x /\ RCnNorm K M x = 1 /\ In (RCn K M) (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (M - (proj1_sig m))) (fun (n : Count (M - (proj1_sig m))) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n))))) x).
move=> H7 r.
elim.
move=> W.
elim.
move=> H8.
elim.
move=> H9 H10.
elim (H7 W H8 H9 (proj1 H10)).
rewrite (FiniteSpanVS (RCfield K) (FnVS (RCfield K) M) (M - proj1_sig m)).
move=> x H11.
apply (Rle_trans r (RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x)))) (sigma m)).
apply Rge_le.
apply (proj2 (proj2 H10)).
exists x.
apply conj.
apply (proj1 H11).
apply conj.
apply (proj1 (proj2 H11)).
reflexivity.
suff: (forall (r1 r2 : R), r1 >= 0 -> r2 >= 0 -> r1 * r1 <= r2 * r2 -> r1 <= r2).
move=> H12.
apply H12.
apply RCnNormNature.
apply (proj1 H4 m).
rewrite - (proj2 (RCnNormNature K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x))))).
rewrite H5.
elim (proj2 (proj2 H11)).
move=> a H13.
suff: (exists (g : Count M -> Count (proj1_sig m + (M - proj1_sig m))), forall (v : Count M), proj1_sig (g v) = proj1_sig v).
elim.
move=> g H14.
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) M 1 U).
simpl.
suff: (Mmult (RCfield K) (M + N) M 1 (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => IRRC K (sigma l))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)) (MVectorToMatrix (RCfield K) M x) = MVectorToMatrix (RCfield K) (M + N) (fun (n : Count (M + N)) => match AddConnectInv M N n with
  | inl n0 => RCmult K (IRRC K (sigma n0)) (match AddConnectInv (proj1_sig m) (M - proj1_sig m) (g n0) with
    | inl n1 => RCO K
    | inr n1 => a n1
  end)
  | inr n0 => RCO K
end)).
move=> H15.
rewrite H15.
rewrite (H1 (M + N) (M + N) U)%nat.
rewrite - (Rmult_1_r (sigma m * sigma m)).
suff: (RCRe K (RCnInnerProduct K (M - proj1_sig m) a a) = 1).
move=> H16.
rewrite - H16.
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count (M + N)) (FiniteIntersection (Count (M + N)) (exist (Finite (Count (M + N))) (Full_set (Count (M + N))) (CountFinite (M + N))) (fun (n : Count (M + N)) => proj1_sig m <= proj1_sig n < M)%nat)).
suff: (exists (g : Count (proj1_sig m + (M - proj1_sig m)) -> Count M), forall (v : Count (proj1_sig m + (M - proj1_sig m))), proj1_sig (g v) = proj1_sig v).
elim.
move=> ginv H17.
suff: (FiniteIntersection (Count (M + N)) (exist (Finite (Count (M + N))) (Full_set (Count (M + N))) (CountFinite (M + N))) (fun (n : Count (M + N)) => (proj1_sig m <= proj1_sig n < M)%nat) = FiniteIm (Count (M - proj1_sig m)) (Count (M + N)) (fun (n : Count (M - proj1_sig m)) => AddConnect M N (inl (ginv (AddConnect (proj1_sig m) (M - proj1_sig m) (inr n))))) (exist (Finite (Count (M - proj1_sig m))) (Full_set (Count (M - proj1_sig m))) (CountFinite (M - proj1_sig m)))).
move=> H18.
rewrite H18.
rewrite - (MySumF2BijectiveSame2 (Count (M - proj1_sig m)) (Count (M + N))).
rewrite (MySumF2O (Count (M + N))).
rewrite (CM_O_r (FPCM (RCfield K))).
unfold RCnInnerProduct.
apply (FiniteSetInduction (Count (M - proj1_sig m)) (exist (Finite (Count (M - proj1_sig m))) (Full_set (Count (M - proj1_sig m))) (CountFinite (M - proj1_sig m)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
suff: (RCRe K (CMe (RCPCM K)) = 0).
move=> H19.
rewrite H19.
rewrite (Rmult_0_r (sigma m * sigma m)).
right.
reflexivity.
elim K.
reflexivity.
reflexivity.
move=> B b H19 H20 H21 H22.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite RCReplus.
rewrite RCReplus.
rewrite Rmult_plus_distr_l.
apply Rplus_le_compat.
apply H22.
unfold Basics.compose.
rewrite (proj1 (AddConnectInvRelation M N)).
suff: (g (ginv (AddConnect (proj1_sig m) (M - proj1_sig m) (inr b))) = AddConnect (proj1_sig m) (M - proj1_sig m) (inr b)).
move=> H23.
rewrite H23.
rewrite (proj1 (AddConnectInvRelation (proj1_sig m) (M - proj1_sig m))).
rewrite Proposition_4_8_2_RC.
rewrite RCmult_assoc.
rewrite (RCmult_comm K (a b)).
rewrite RCmult_assoc.
rewrite - RCmult_assoc.
rewrite (RCmult_comm K (a b)).
suff: (forall (K : RC) (r : R), ConjugateRC K (IRRC K r) = IRRC K r).
move=> H24.
suff: (forall (K : RC) (r : R) (c : RCT K), RCRe K (RCmult K (IRRC K r) c) = r * RCRe K c).
move=> H25.
rewrite (H24 K).
rewrite - (IRRCmult K).
rewrite (H25 K).
apply Rmult_le_compat_r.
suff: (forall (K : RC) (c : RCT K), 0 <= RCRe K (RCmult K (ConjugateRC K c) c)).
move=> H26.
apply (H26 K (a b)).
elim.
move=> c.
apply Rge_le.
apply Formula_1_3.
move=> c.
simpl.
unfold Cmult.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
unfold Rminus.
rewrite Ropp_mult_distr_l.
rewrite Ropp_involutive.
rewrite - (Rplus_0_l 0).
apply Rplus_le_compat.
apply Rge_le.
apply Formula_1_3.
apply Rge_le.
apply Formula_1_3.
apply Rmult_le_compat.
apply Rge_le.
apply (proj1 H4).
apply Rge_le.
apply (proj1 H4).
apply Rge_le.
apply (proj2 H4).
rewrite H17.
rewrite - (proj2 (AddConnectNature (proj1_sig m) (M - proj1_sig m)) b).
apply (le_plus_l (proj1_sig m) (proj1_sig b)).
apply Rge_le.
apply (proj2 H4).
rewrite H17.
rewrite - (proj2 (AddConnectNature (proj1_sig m) (M - proj1_sig m)) b).
apply (le_plus_l (proj1_sig m) (proj1_sig b)).
elim.
move=> r1 r2.
reflexivity.
move=> r0 c.
simpl.
unfold IRC.
unfold Cmult.
rewrite (CmakeRe r0 0).
rewrite (CmakeIm r0 0).
rewrite (Rmult_0_l (c CIm)).
rewrite Rminus_0_r.
apply CmakeRe.
elim.
move=> r0.
reflexivity.
move=> r0.
simpl.
unfold Conjugate.
unfold IRC.
rewrite (CmakeRe r0 0).
rewrite (CmakeIm r0 0).
rewrite Ropp_0.
reflexivity.
apply sig_map.
rewrite H14.
apply H17.
apply H21.
apply H21.
move=> u.
rewrite - {1} (proj2 (AddConnectInvRelation M N) u).
elim (AddConnectInv M N u).
move=> u0 H19.
suff: (proj1_sig (AddConnect M N (inl u0)) < proj1_sig m)%nat.
rewrite - (proj1 (AddConnectNature M N) u0).
rewrite - (H14 u0).
rewrite - {1} (proj2 (AddConnectInvRelation (proj1_sig m) (M - proj1_sig m)) (g u0)).
elim (AddConnectInv (proj1_sig m) (M - proj1_sig m) (g u0)).
move=> u1 H20.
suff: (RCmult K (IRRC K (sigma u0)) (RCO K) = RCO K).
move=> H21.
rewrite H21.
apply (Fmul_O_l (RCfield K)).
apply (Fmul_O_r (RCfield K)).
move=> u1.
rewrite - (proj2 (AddConnectNature (proj1_sig m) (M - proj1_sig m)) u1).
move=> H20.
elim (le_not_lt (proj1_sig m) (proj1_sig m + proj1_sig u1) (le_plus_l (proj1_sig m) (proj1_sig u1)) H20).
suff: (proj1_sig (AddConnect M N (inl u0)) < M)%nat.
elim H19.
move=> u1 H20 H21 H22.
elim (le_or_lt (proj1_sig m) (proj1_sig u1)).
move=> H23.
elim H20.
suff: (proj1_sig u1 - proj1_sig m < M - proj1_sig m)%nat.
move=> H24.
apply (Im_intro (Count (M - proj1_sig m)) (Count (M + N)) (Full_set (Count (M - proj1_sig m))) (fun (n : Count (M - proj1_sig m)) => AddConnect M N (inl (ginv (AddConnect (proj1_sig m) (M - proj1_sig m) (inr n))))) (exist (fun (n : nat) => (n < M - proj1_sig m)%nat) (proj1_sig u1 - proj1_sig m)%nat H24)).
apply (Full_intro (Count (M - proj1_sig m))).
apply sig_map.
rewrite - (proj1 (AddConnectNature M N)).
rewrite H17.
rewrite - (proj2 (AddConnectNature (proj1_sig m) (M - proj1_sig m))).
apply (le_plus_minus (proj1_sig m) (proj1_sig u1) H23).
apply (plus_lt_reg_l (proj1_sig u1 - proj1_sig m) (M - proj1_sig m) (proj1_sig m)).
rewrite (le_plus_minus_r (proj1_sig m) (proj1_sig u1) H23).
rewrite (le_plus_minus_r (proj1_sig m) M (lt_le_weak (proj1_sig m) M (proj2_sig m))).
apply H22.
apply.
rewrite - (proj1 (AddConnectNature M N) u0).
apply (proj2_sig u0).
move=> u0 H19.
apply (Fmul_O_l (RCfield K)).
move=> u1 u2 H19 H20 H21.
apply sig_map.
apply (plus_reg_l (proj1_sig u1) (proj1_sig u2) (proj1_sig m)).
rewrite (proj2 (AddConnectNature (proj1_sig m) (M - proj1_sig m)) u1).
rewrite (proj2 (AddConnectNature (proj1_sig m) (M - proj1_sig m)) u2).
rewrite - H17.
rewrite - H17.
rewrite (proj1 (AddConnectNature M N) (ginv (AddConnect (proj1_sig m) (M - proj1_sig m) (inr u1)))).
rewrite (proj1 (AddConnectNature M N) (ginv (AddConnect (proj1_sig m) (M - proj1_sig m) (inr u2)))).
rewrite H21.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u.
elim.
move=> u0 H19 H20.
suff: (proj1_sig u0 - proj1_sig m < M - proj1_sig m)%nat.
move=> H21.
apply (Im_intro (Count (M - proj1_sig m)) (Count (M + N)) (Full_set (Count (M - proj1_sig m))) (fun (n : Count (M - proj1_sig m)) => AddConnect M N (inl (ginv (AddConnect (proj1_sig m) (M - proj1_sig m) (inr n))))) (exist (fun (n : nat) => (n < M - proj1_sig m)%nat) (proj1_sig u0 - proj1_sig m)%nat H21)).
apply (Full_intro (Count (M - proj1_sig m))).
apply sig_map.
rewrite - (proj1 (AddConnectNature M N)).
rewrite H17.
rewrite - (proj2 (AddConnectNature (proj1_sig m) (M - proj1_sig m))).
apply (le_plus_minus (proj1_sig m) (proj1_sig u0) (proj1 H19)).
apply (plus_lt_reg_l (proj1_sig u0 - proj1_sig m) (M - proj1_sig m) (proj1_sig m)).
rewrite (le_plus_minus_r (proj1_sig m) (proj1_sig u0) (proj1 H19)).
rewrite (le_plus_minus_r (proj1_sig m) M (lt_le_weak (proj1_sig m) M (proj2_sig m))).
apply (proj2 H19).
move=> u.
elim.
move=> u0 H18 v0 H19.
apply Intersection_intro.
rewrite H19.
unfold In.
rewrite - (proj1 (AddConnectNature M N)).
apply conj.
rewrite H17.
rewrite - (proj2 (AddConnectNature (proj1_sig m) (M - proj1_sig m))).
apply (le_plus_l (proj1_sig m) (proj1_sig u0)).
apply (proj2_sig (ginv (AddConnect (proj1_sig m) (M - proj1_sig m) (inr u0)))).
apply (Full_intro (Count (M + N))).
suff: (proj1_sig m + (M - proj1_sig m) = M)%nat.
move=> H17.
rewrite H17.
exists (fun (n : Count M) => n).
reflexivity.
apply (le_plus_minus_r (proj1_sig m) M (lt_le_weak (proj1_sig m) M (proj2_sig m))).
move=> u H17.
apply (Full_intro (Count (M + N))).
rewrite - (H1 M (M - proj1_sig m)%nat (fun (z : {n : nat | (n < M)%nat}) (w : {n : nat | (n < M - proj1_sig m)%nat}) => V z (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig w)%nat (H6 (proj1_sig w) (proj2_sig w))))).
suff: (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M (M - proj1_sig m) 1 (fun (z : {n : nat | (n < M)%nat}) (w : {n : nat | (n < M - proj1_sig m)%nat}) => V z (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig w)%nat (H6 (proj1_sig w) (proj2_sig w)))) (MVectorToMatrix (RCfield K) (M - proj1_sig m) a)) = x).
move=> H16.
rewrite H16.
rewrite (proj2 (RCnNormNature K M x)).
rewrite (proj1 (proj2 H11)).
apply (Rmult_1_l 1).
rewrite H13.
apply functional_extensionality.
move=> k.
unfold Mmult.
unfold MMatrixToVector.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < M - proj1_sig m)%nat} (exist (Finite {n : nat | (n < M - proj1_sig m)%nat}) (Full_set {n : nat | (n < M - proj1_sig m)%nat}) (CountFinite (M - proj1_sig m)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H16 H17 H18 H19.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H19.
rewrite (Fmul_comm (RCfield K)).
reflexivity.
apply H18.
apply H18.
apply functional_extensionality.
move=> p.
apply functional_extensionality.
move=> q.
suff: (Mmult (RCfield K) (M - proj1_sig m) M (M - proj1_sig m) (AdjointMatrixRC K M (M - proj1_sig m) (fun (z : {n : nat | (n < M)%nat}) (w : {n : nat | (n < M - proj1_sig m)%nat}) => V z (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig w)%nat (H6 (proj1_sig w) (proj2_sig w))))) (fun (z : {n : nat | (n < M)%nat}) (w : {n : nat | (n < M - proj1_sig m)%nat}) => V z (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig w)%nat (H6 (proj1_sig w) (proj2_sig w)))) p q = Mmult (RCfield K) M M M (AdjointMatrixRC K M M V) V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig p)%nat (H6 (proj1_sig p) (proj2_sig p))) (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig q)%nat (H6 (proj1_sig q) (proj2_sig q)))).
move=> H16.
rewrite H16.
rewrite H3.
unfold MI.
simpl.
elim (Nat.eq_dec (proj1_sig m + proj1_sig p) (proj1_sig m + proj1_sig q)).
move=> H17.
elim (Nat.eq_dec (proj1_sig p) (proj1_sig q)).
move=> H18.
reflexivity.
elim.
apply (plus_reg_l (proj1_sig p) (proj1_sig q) (proj1_sig m) H17).
elim (Nat.eq_dec (proj1_sig p) (proj1_sig q)).
move=> H18.
elim.
rewrite H18.
reflexivity.
move=> H18.
reflexivity.
reflexivity.
apply H2.
rewrite (Mmult_assoc (RCfield K) (M + N) M M 1).
rewrite (MBlockHMult (RCfield K) M N M 1).
rewrite (Mmult_O_l (RCfield K) N M 1).
suff: (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M (M - proj1_sig m) 1 (fun (z : {n : nat | (n < M)%nat}) (w : {n : nat | (n < M - proj1_sig m)%nat}) => V z (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig w)%nat (H6 (proj1_sig w) (proj2_sig w)))) (MVectorToMatrix (RCfield K) (M - proj1_sig m) a)) = x).
move=> H15.
rewrite - H15.
rewrite (proj2 (MVectorMatrixRelation (RCfield K) M)).
apply functional_extensionality.
move=> p.
apply functional_extensionality.
move=> q.
unfold MBlockH.
unfold MVectorToMatrix.
elim (AddConnectInv M N p).
move=> p0.
unfold Mmult at 1.
rewrite (MySumF2Included {n : nat | (n < M)%nat} (FiniteSingleton {n : nat | (n < M)%nat} p0)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig p0) (proj1_sig p0)).
move=> H16.
rewrite - (Mmult_assoc (RCfield K) M M (M - proj1_sig m) 1).
suff: (proj1_sig (g p0) = proj1_sig p0).
rewrite - {1} (proj2 (AddConnectInvRelation (proj1_sig m) (M - proj1_sig m)) (g p0)).
elim (AddConnectInv (proj1_sig m) (M - proj1_sig m) (g p0)).
move=> p1.
rewrite - (proj1 (AddConnectNature (proj1_sig m) (M - proj1_sig m)) p1).
move=> H17.
unfold Mmult at 1.
rewrite MySumF2O.
reflexivity.
move=> u H18.
suff: (Mmult (RCfield K) M M (M - proj1_sig m) (AdjointMatrixRC K M M V) (fun (z : {n : nat | (n < M)%nat}) (w : {n : nat | (n < M - proj1_sig m)%nat}) => V z (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig w)%nat (H6 (proj1_sig w) (proj2_sig w)))) p0 u = Mmult (RCfield K) M M M (AdjointMatrixRC K M M V) V p0 (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig u)%nat (H6 (proj1_sig u) (proj2_sig u)))).
move=> H19.
rewrite H19.
rewrite H3.
unfold MI.
simpl.
elim (Nat.eq_dec (proj1_sig p0) (proj1_sig m + proj1_sig u)).
move=> H20.
elim (lt_irrefl (proj1_sig p0)).
rewrite {2} H20.
rewrite - H17.
apply (le_trans (S (proj1_sig p1)) (proj1_sig m) (proj1_sig m + proj1_sig u) (proj2_sig p1) (le_plus_l (proj1_sig m) (proj1_sig u))).
move=> H20.
apply (Fmul_O_l (RCfield K) (a u)).
reflexivity.
move=> p1.
rewrite - (proj2 (AddConnectNature (proj1_sig m) (M - proj1_sig m)) p1).
move=> H17.
unfold Mmult at 1.
rewrite (MySumF2Included {n : nat | (n < M - proj1_sig m)%nat} (FiniteSingleton {n : nat | (n < M - proj1_sig m)%nat} p1)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
suff: (Mmult (RCfield K) M M (M - proj1_sig m) (AdjointMatrixRC K M M V) (fun (z : {n : nat | (n < M)%nat}) (w : {n : nat | (n < M - proj1_sig m)%nat}) => V z (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig w)%nat (H6 (proj1_sig w) (proj2_sig w)))) p0 p1 = Mmult (RCfield K) M M M (AdjointMatrixRC K M M V) V p0 (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig p1)%nat (H6 (proj1_sig p1) (proj2_sig p1)))).
move=> H18.
rewrite H18.
rewrite H3.
unfold MI.
simpl.
elim (Nat.eq_dec (proj1_sig p0) (proj1_sig m + proj1_sig p1)).
move=> H19.
rewrite (RCmult_1_l K (a p1)).
reflexivity.
elim.
rewrite H17.
reflexivity.
reflexivity.
move=> u.
elim.
move=> u0 H18 H19.
suff: (Mmult (RCfield K) M M (M - proj1_sig m) (AdjointMatrixRC K M M V) (fun (z : {n : nat | (n < M)%nat}) (w : {n : nat | (n < M - proj1_sig m)%nat}) => V z (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig w)%nat (H6 (proj1_sig w) (proj2_sig w)))) p0 u0 = Mmult (RCfield K) M M M (AdjointMatrixRC K M M V) V p0 (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig u0)%nat (H6 (proj1_sig u0) (proj2_sig u0)))).
move=> H20.
rewrite H20.
rewrite H3.
unfold MI.
simpl.
elim (Nat.eq_dec (proj1_sig p0) (proj1_sig m + proj1_sig u0)).
move=> H21.
elim H18.
suff: (p1 = u0).
move=> H22.
rewrite H22.
apply (In_singleton {n : nat | (n < M - proj1_sig m)%nat} u0).
apply sig_map.
apply (plus_reg_l (proj1_sig p1) (proj1_sig u0) (proj1_sig m)).
rewrite H17.
apply H21.
move=> H21.
apply (Fmul_O_l (RCfield K) (a u0)).
reflexivity.
move=> u H18.
apply (Full_intro {n : nat | (n < M - proj1_sig m)%nat} u).
apply (H14 p0).
elim.
reflexivity.
move=> u.
elim.
move=> u0 H16 H17.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig p0) (proj1_sig u0)).
move=> H18.
elim H16.
suff: (p0 = u0).
move=> H19.
rewrite H19.
apply (In_singleton {n : nat | (n < M)%nat} u0).
apply sig_map.
apply H18.
move=> H18.
apply (Fmul_O_l (RCfield K)).
move=> u H16.
apply (Full_intro {n : nat | (n < M)%nat} u).
move=> p0.
reflexivity.
rewrite H13.
apply functional_extensionality.
move=> k.
unfold Mmult.
unfold MMatrixToVector.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < M - proj1_sig m)%nat} (exist (Finite {n : nat | (n < M - proj1_sig m)%nat}) (Full_set {n : nat | (n < M - proj1_sig m)%nat}) (CountFinite (M - proj1_sig m)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H15 H16 H17 H18.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H18.
rewrite (Fmul_comm (RCfield K)).
reflexivity.
apply H17.
apply H17.
suff: (M = proj1_sig m + (M - proj1_sig m))%nat.
move=> H14.
rewrite - H14.
exists (fun (k : Count M) => k).
move=> v.
reflexivity.
apply (le_plus_minus (proj1_sig m) M).
apply (lt_le_weak (proj1_sig m) M (proj2_sig m)).
move=> r1 r2 H12 H13 H14.
apply (Rnot_lt_le r2 r1).
move=> H15.
apply (Rle_not_lt (r2 * r2) (r1 * r1) H14).
apply (Rmult_le_0_lt_compat r2 r1 r2 r1).
apply (Rge_le r2 0 H13).
apply (Rge_le r2 0 H13).
apply H15.
apply H15.
move=> W H7 H8 H9.
elim (classic (exists (x : RCn K M), In (RCn K M) (Intersection (RCn K M) W (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (M - proj1_sig m)) (fun (n : Count (M - proj1_sig m)) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n)))))) x /\ x <> VO (RCfield K) (FnVS (RCfield K) M))).
elim.
move=> x H10.
exists (Fnmul (RCfield K) M (IRRC K (1 / RCnNorm K M x)) x).
suff: (RCnNorm K M x <> 0).
elim (proj1 H10).
move=> x0 H11 H12 H13.
apply conj.
apply (proj1 (proj2 H7) (IRRC K (1 / RCnNorm K M x0)) x0 H11).
apply conj.
apply RCnNormNature2.
apply conj.
left.
apply Rlt_0_1.
suff: (RCnInnerProduct K M = RCip K (FnVS (RCfield K) M) (RCnInner_Product_Space K M)).
move=> H14.
rewrite H14.
rewrite (RCip_linear_mult_l K (FnVS (RCfield K) M) (RCnInner_Product_Space K M)).
rewrite (RCip_linear_mult_r K (FnVS (RCfield K) M) (RCnInner_Product_Space K M)).
rewrite - RCmult_assoc.
simpl.
suff: (forall (K : RC) (r : R), ConjugateRC K (IRRC K r) = IRRC K r).
move=> H15.
suff: (forall (K : RC) (r : R) (c : RCT K), RCRe K (RCmult K (IRRC K r) c) = r * RCRe K c).
move=> H16.
rewrite (H15 K).
rewrite - (IRRCmult K).
rewrite (H16 K).
unfold Rdiv.
rewrite (Rmult_1_l (/ RCnNorm K M x0)).
rewrite (proj2 (RCnNormNature K M x0)).
rewrite Rmult_assoc.
rewrite - (Rmult_assoc (/ RCnNorm K M x0) (RCnNorm K M x0)).
rewrite (Rinv_l (RCnNorm K M x0) H13).
rewrite (Rmult_1_l (RCnNorm K M x0)).
rewrite (Rmult_1_l 1).
apply (Rinv_l (RCnNorm K M x0) H13).
elim.
move=> r1 r2.
reflexivity.
move=> r0 c.
simpl.
unfold IRC.
unfold Cmult.
rewrite (CmakeRe r0 0).
rewrite (CmakeIm r0 0).
rewrite (Rmult_0_l (c CIm)).
rewrite Rminus_0_r.
apply CmakeRe.
elim.
move=> r0.
reflexivity.
move=> r0.
simpl.
unfold Conjugate.
unfold IRC.
rewrite (CmakeRe r0 0).
rewrite (CmakeIm r0 0).
rewrite Ropp_0.
reflexivity.
reflexivity.
apply (proj1 (proj2 (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) M) (Count (M - proj1_sig m)) (fun (n : Count (M - proj1_sig m)) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n)))))) (IRRC K (1 / RCnNorm K M x0)) x0 H12).
move=> H11.
apply (proj2 H10).
apply (proj1 (RCip_refl K (FnVS (RCfield K) M) (RCnInner_Product_Space K M) x)).
suff: (forall (x : RCn K M), RCnNorm K M x = 0 -> RCnInnerProduct K M x x = RCO K).
move=> H12.
apply (H12 x H11).
elim K.
move=> x0 H12.
suff: (RCnInnerProduct RK M x0 x0 = RCnNorm RK M x0 * RCnNorm RK M x0).
move=> H13.
rewrite H13.
rewrite H12.
apply (Rmult_0_l 0).
apply (proj2 (RnNormNature M x0)).
move=> x0 H12.
apply functional_extensionality.
move=> k.
elim (CReorCIm k).
move=> H13.
rewrite H13.
suff: (RCnInnerProduct CK M x0 x0 CRe = RCnNorm CK M x0 * RCnNorm CK M x0).
move=> H14.
rewrite H14.
rewrite H12.
apply (Rmult_0_l 0).
apply (proj2 (CnNormNature M x0)).
move=> H13.
rewrite H13.
apply (Cip_pos_im (FnVS Cfield M) (CnInner_Product_Space M) x0).
move=> H10.
elim (DimensionSumEnsembleVS2_exists (RCfield K) (FnVS (RCfield K) M) W (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (M - proj1_sig m)) (fun (n : Count (M - proj1_sig m)) => MTranspose (RCfield K) M M V (exist (fun k : nat => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n))))) H7 (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) M) (Count (M - proj1_sig m)) (fun (n : Count (M - proj1_sig m)) => MTranspose (RCfield K) M M V (exist (fun k : nat => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n)))))).
move=> H11 H12.
suff: (FiniteDimensionVS (RCfield K) (SubspaceMakeVS (RCfield K) (FnVS (RCfield K) M) (SumEnsembleVS (RCfield K) (FnVS (RCfield K) M) W (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (M - proj1_sig m)) (fun (n : Count (M - proj1_sig m)) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n)))))) H11)).
move=> H13.
elim (H12 H13).
move=> H14.
elim.
move=> H15 H16.
elim (lt_irrefl M).
unfold lt.
suff: (S M = DimensionSubspaceVS (RCfield K) (FnVS (RCfield K) M) (SumEnsembleVS (RCfield K) (FnVS (RCfield K) M) W (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (M - proj1_sig m)) (fun (n : Count (M - proj1_sig m)) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n)))))) H11 H13).
move=> H17.
rewrite H17.
elim (FnVSDimension (RCfield K) M).
move=> H18 H19.
rewrite - {18} H19.
apply (Proposition_5_9_1_2 (RCfield K) (FnVS (RCfield K) M) (SumEnsembleVS (RCfield K) (FnVS (RCfield K) M) W (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (M - proj1_sig m)) (fun n : Count (M - proj1_sig m) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n)))))) H11 H18 H13).
rewrite H16.
suff: (H14 = H8).
move=> H17.
rewrite H17.
rewrite H9.
rewrite (DimensionSubspaceVSNature2 (RCfield K) (FnVS (RCfield K) M) (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (M - proj1_sig m)) (fun (n : Count (M - proj1_sig m)) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n))))) (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) M) (Count (M - proj1_sig m)) (fun (n : Count (M - proj1_sig m)) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n))))) H15 (M - proj1_sig m) (fun (n : Count (M - proj1_sig m)) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n))))).
rewrite {1} (le_plus_minus (proj1_sig m) M).
reflexivity.
apply (lt_le_weak (proj1_sig m) M (proj2_sig m)).
exists (SpanContainSelfVS (RCfield K) (FnVS (RCfield K) M) (Count (M - proj1_sig m)) (fun (n : Count (M - proj1_sig m)) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n))))).
apply (proj2 (FiniteLinearlyIndependentVS (RCfield K) (FnVS (RCfield K) M) (M - proj1_sig m) (fun (n : Count (M - proj1_sig m)) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n)))))).
move=> a H18 l.
suff: (a l = RCnInnerProduct K M (MySumF2 (Count (M - proj1_sig m)) (exist (Finite (Count (M - proj1_sig m))) (Full_set (Count (M - proj1_sig m))) (CountFinite (M - proj1_sig m))) (VSPCM (RCfield K) (FnVS (RCfield K) M)) (fun (n : Count (M - proj1_sig m)) => Vmul (RCfield K) (FnVS (RCfield K) M) (a n) (MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n)))))) (MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig l)%nat (H6 (proj1_sig l) (proj2_sig l))))).
move=> H19.
rewrite H19.
rewrite H18.
apply (RCip_mult_0_l K (FnVS (RCfield K) M) (RCnInner_Product_Space K M)).
suff: (RCnInnerProduct K M (MySumF2 (Count (M - proj1_sig m)) (exist (Finite (Count (M - proj1_sig m))) (Full_set (Count (M - proj1_sig m))) (CountFinite (M - proj1_sig m))) (VSPCM (RCfield K) (FnVS (RCfield K) M)) (fun (n : Count (M - proj1_sig m)) => Vmul (RCfield K) (FnVS (RCfield K) M) (a n) (MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n)))))) (MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig l)%nat (H6 (proj1_sig l) (proj2_sig l)))) = MySumF2 (Count (M - proj1_sig m)) (exist (Finite (Count (M - proj1_sig m))) (Full_set (Count (M - proj1_sig m))) (CountFinite (M - proj1_sig m))) (FPCM (RCfield K)) (fun (n : Count (M - proj1_sig m)) => RCnInnerProduct K M (Vmul (RCfield K) (FnVS (RCfield K) M) (a n) (MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n))))) (MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig l)%nat (H6 (proj1_sig l) (proj2_sig l)))))).
move=> H19.
rewrite H19.
rewrite (MySumF2Included (Count (M - proj1_sig m)) (FiniteSingleton (Count (M - proj1_sig m)) l)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (CM_O_r (FPCM (RCfield K))).
rewrite (Proposition_4_2_2_1 K M).
suff: (RCnInnerProduct K M (MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig l)%nat (H6 (proj1_sig l) (proj2_sig l)))) (MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig l)%nat (H6 (proj1_sig l) (proj2_sig l)))) = ConjugateRC K (Mmult (RCfield K) M M M (AdjointMatrixRC K M M V) V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig l)%nat (H6 (proj1_sig l) (proj2_sig l))) (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig l)%nat (H6 (proj1_sig l) (proj2_sig l))))).
move=> H20.
rewrite H20.
rewrite H3.
unfold MI.
simpl.
elim (Nat.eq_dec (proj1_sig m + proj1_sig l) (proj1_sig m + proj1_sig l)).
move=> H21.
rewrite ConjugateRCI.
rewrite RCmult_comm.
rewrite (RCmult_1_l K (a l)).
reflexivity.
elim.
reflexivity.
unfold RCnInnerProduct.
unfold Mmult.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < M)%nat} (exist (Finite {n : nat | (n < M)%nat}) (Full_set {n : nat | (n < M)%nat}) (CountFinite M))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite ConjugateRCO.
reflexivity.
move=> B b H20 H21 H22 H23.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H23.
simpl.
rewrite Proposition_4_8_1_1_RC.
rewrite Proposition_4_8_2_RC.
unfold AdjointMatrixRC.
rewrite ConjugateRCInvolutive.
reflexivity.
apply H22.
apply H22.
move=> u.
elim.
move=> u0 H20 H21.
rewrite (Proposition_4_2_2_1 K M).
suff: (RCnInnerProduct K M (MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig u0)%nat (H6 (proj1_sig u0) (proj2_sig u0)))) (MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig l)%nat (H6 (proj1_sig l) (proj2_sig l)))) = ConjugateRC K (Mmult (RCfield K) M M M (AdjointMatrixRC K M M V) V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig u0)%nat (H6 (proj1_sig u0) (proj2_sig u0))) (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig l)%nat (H6 (proj1_sig l) (proj2_sig l))))).
move=> H22.
rewrite H22.
rewrite H3.
unfold MI.
simpl.
elim (Nat.eq_dec (proj1_sig m + proj1_sig u0) (proj1_sig m + proj1_sig l)).
move=> H23.
elim H20.
suff: (u0 = l).
move=> H24.
rewrite H24.
apply (In_singleton (Count (M - proj1_sig m)) l).
apply sig_map.
apply (plus_reg_l (proj1_sig u0) (proj1_sig l) (proj1_sig m) H23).
move=> H23.
rewrite ConjugateRCO.
apply (Fmul_O_r (RCfield K) (a u0)).
unfold RCnInnerProduct.
unfold Mmult.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < M)%nat} (exist (Finite {n : nat | (n < M)%nat}) (Full_set {n : nat | (n < M)%nat}) (CountFinite M))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite ConjugateRCO.
reflexivity.
move=> B b H23 H24 H25 H26.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H26.
simpl.
rewrite Proposition_4_8_1_1_RC.
rewrite Proposition_4_8_2_RC.
unfold AdjointMatrixRC.
rewrite ConjugateRCInvolutive.
reflexivity.
apply H25.
apply H25.
move=> u H20.
apply (Full_intro (Count (M - proj1_sig m)) u).
apply (FiniteSetInduction (Count (M - proj1_sig m)) (exist (Finite (Count (M - proj1_sig m))) (Full_set (Count (M - proj1_sig m))) (CountFinite (M - proj1_sig m)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (RCip_mult_0_l K (FnVS (RCfield K) M) (RCnInner_Product_Space K M)).
move=> B b H19 H20 H21 H22.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Proposition_4_2_1_1 K M).
rewrite (Proposition_4_2_2_1 K M).
rewrite H22.
reflexivity.
apply H21.
apply H21.
apply proof_irrelevance.
apply Extensionality_Ensembles.
apply conj.
move=> v H17.
apply NNPP.
move=> H18.
apply H10.
exists v.
apply conj.
apply H17.
move=> H19.
apply H18.
rewrite H19.
apply (In_singleton (RCn K M) (VO (RCfield K) (FnVS (RCfield K) M))).
move=> u.
elim.
apply (Intersection_intro (RCn K M)).
apply (proj2 (proj2 H7)).
apply (proj2 (proj2 (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) M) (Count (M - proj1_sig m)) (fun (n : Count (M - proj1_sig m)) => MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig m + proj1_sig n)%nat (H6 (proj1_sig n) (proj2_sig n))))))).
apply (Proposition_5_9_1_1 (RCfield K) (FnVS (RCfield K) M) (FnVSFiniteDimension (RCfield K) M)).
move=> n H6.
rewrite {2} (le_plus_minus (proj1_sig m) M).
apply (plus_lt_compat_l n (M - (proj1_sig m)) (proj1_sig m) H6).
apply (le_trans (proj1_sig m) (S (proj1_sig m)) M (le_S (proj1_sig m) (proj1_sig m) (le_n (proj1_sig m))) (proj2_sig m)).
move=> M N Q x y H1.
rewrite (RCnInnerProductMatrix K M).
rewrite (RCnInnerProductMatrix K N x y).
rewrite (proj2 (MVectorMatrixRelation (RCfield K) M)).
rewrite (proj2 (MVectorMatrixRelation (RCfield K) M)).
rewrite (AdjointMatrixRCMult K M N 1 Q).
rewrite (Mmult_assoc (RCfield K) 1 N M 1).
rewrite - (Mmult_assoc (RCfield K) N M N 1).
rewrite H1.
rewrite (Mmult_I_l (RCfield K) N 1).
reflexivity.
Qed.

Definition SingularValueNatureRHSub : forall (M N : nat) (A : Matrix Rfield (M + N) M) (U : Matrix Rfield (M + N) (M + N)) (V : Matrix Rfield M M) (sigma : Rn M), OrthogonalMatrix (M + N) U -> OrthogonalMatrix M V -> ((forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2)) -> A = Mmult Rfield (M + N) (M + N) M U (Mmult Rfield (M + N) M M (MBlockH Rfield M N M (MDiag Rfield M sigma) (MO Rfield N M)) (MTranspose Rfield M M V)) -> (forall (m : {n : nat | (n < M)%nat}), is_max (fun (r0 : R) => exists (W : Ensemble (Rn M)) (H1 : SubspaceVS Rfield (RnVS M) W) (H2 : FiniteDimensionVS Rfield (SubspaceMakeVS Rfield (RnVS M) W H1)), DimensionSubspaceVS Rfield (RnVS M) W H1 H2 = S (proj1_sig m) /\ is_min (fun (r1 : R) => exists (x : Rn M), In (Rn M) W x /\ RnNorm M x = 1 /\ RnNorm (M + N) (MMatrixToVector Rfield (M + N) (Mmult Rfield (M + N) M 1 A (MVectorToMatrix Rfield M x))) = r1) r0) (sigma m)) := SingularValueNatureRCHSub RK.

Definition SingularValueNatureCHSub : forall (M N : nat) (A : Matrix Cfield (M + N) M) (U : Matrix Cfield (M + N) (M + N)) (V : Matrix Cfield M M) (sigma : Rn M), UnitaryMatrix (M + N) U -> UnitaryMatrix M V -> ((forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2)) -> A = Mmult Cfield (M + N) (M + N) M U (Mmult Cfield (M + N) M M (MBlockH Cfield M N M (MDiag Cfield M (fun (m : {n : nat | (n < M)%nat}) => Cmake (sigma m) 0)) (MO Cfield N M)) (AdjointMatrix M M V)) -> (forall (m : {n : nat | (n < M)%nat}), is_max (fun (r0 : R) => exists (W : Ensemble (Cn M)) (H1 : SubspaceVS Cfield (FnVS Cfield M) W) (H2 : FiniteDimensionVS Cfield (SubspaceMakeVS Cfield (FnVS Cfield M) W H1)), DimensionSubspaceVS Cfield (FnVS Cfield M) W H1 H2 = S (proj1_sig m) /\ is_min (fun (r1 : R) => exists (x : Cn M), In (Cn M) W x /\ CnNorm M x = 1 /\ CnNorm (M + N) (MMatrixToVector Cfield (M + N) (Mmult Cfield (M + N) M 1 A (MVectorToMatrix Cfield M x))) = r1) r0) (sigma m)) := SingularValueNatureRCHSub CK.

Lemma SingularValueRCHSig : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M), {sigma : Rn M | (forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) /\ exists (U : Matrix (RCfield K) (M + N) (M + N)) (V : Matrix (RCfield K) M M), UnitaryMatrixRC K (M + N) U /\ UnitaryMatrixRC K M V /\ A = Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (sigma m))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))}.
Proof.
move=> K M N A.
apply constructive_definite_description.
apply (proj1 (unique_existence (fun (x : Rn M) => (forall m : {n : nat | (n < M)%nat}, x m >= 0) /\ (forall m1 m2 : {n : nat | (n < M)%nat}, (proj1_sig m1 <= proj1_sig m2)%nat -> x m1 >= x m2) /\ exists (U : Matrix (RCfield K) (M + N) (M + N)) (V : Matrix (RCfield K) M M), UnitaryMatrixRC K (M + N) U /\ UnitaryMatrixRC K M V /\ A = Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (x m))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))))).
apply conj.
elim (SingularDecompositionRCH K M N A).
move=> U H1.
elim (proj2 H1).
move=> V H2.
elim (proj2 H2).
move=> sigma H3.
exists sigma.
apply conj.
apply (proj1 H3).
apply conj.
apply (proj1 (proj2 H3)).
exists U.
exists V.
apply conj.
apply (proj1 H1).
apply conj.
apply (proj1 H2).
apply (proj2 (proj2 H3)).
move=> sigma1 sigma2 H1 H2.
elim (proj2 (proj2 H1)).
move=> U1.
elim.
move=> V1 H3.
elim (proj2 (proj2 H2)).
move=> U2.
elim.
move=> V2 H4.
apply functional_extensionality.
move=> m.
apply (max_unique (fun (r0 : R) => exists (W : Ensemble (RCn K M)) (H1 : SubspaceVS (RCfield K) (FnVS (RCfield K) M) W) (H2 : FiniteDimensionVS (RCfield K) (SubspaceMakeVS (RCfield K) (FnVS (RCfield K) M) W H1)), DimensionSubspaceVS (RCfield K) (FnVS (RCfield K) M) W H1 H2 = S (proj1_sig m) /\ is_min (fun (r1 : R) => exists (x : RCn K M), In (RCn K M) W x /\ RCnNorm K M x = 1 /\ RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x))) = r1) r0)).
apply conj.
apply (SingularValueNatureRCHSub K M N A U1 V1 sigma1 (proj1 H3) (proj1 (proj2 H3))).
apply conj.
apply (proj1 H1).
apply (proj1 (proj2 H1)).
apply (proj2 (proj2 H3)).
apply (SingularValueNatureRCHSub K M N A U2 V2 sigma2 (proj1 H4) (proj1 (proj2 H4))).
apply conj.
apply (proj1 H2).
apply (proj1 (proj2 H2)).
apply (proj2 (proj2 H4)).
Qed.

Definition SingularValueRHSig : forall (M N : nat) (A : Matrix Rfield (M + N) M), {sigma : {n : nat | (n < M)%nat} -> R | (forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) /\ exists (U : Matrix Rfield (M + N) (M + N)) (V : Matrix Rfield M M), OrthogonalMatrix (M + N) U /\ OrthogonalMatrix M V /\ A = Mmult Rfield (M + N) (M + N) M U (Mmult Rfield (M + N) M M (MBlockH Rfield M N M (MDiag Rfield M sigma) (MO Rfield N M)) (MTranspose Rfield M M V))} := SingularValueRCHSig RK.

Definition SingularValueCHSig : forall (M N : nat) (A : Matrix Cfield (M + N) M), {sigma : {n : nat | (n < M)%nat} -> R | (forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) /\ exists (U : Matrix Cfield (M + N) (M + N)) (V : Matrix Cfield M M), UnitaryMatrix (M + N) U /\ UnitaryMatrix M V /\ A = Mmult Cfield (M + N) (M + N) M U (Mmult Cfield (M + N) M M (MBlockH Cfield M N M (MDiag Cfield M (fun (m : {n : nat | (n < M)%nat}) => Cmake (sigma m) 0)) (MO Cfield N M)) (AdjointMatrix M M V))} := SingularValueRCHSig CK.

Definition SingularValueRCH (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M) := proj1_sig (SingularValueRCHSig K M N A).

Definition SingularValueRH (M N : nat) (A : Matrix Rfield (M + N) M) := proj1_sig (SingularValueRHSig M N A).

Definition SingularValueCH (M N : nat) (A : Matrix Cfield (M + N) M) := proj1_sig (SingularValueCHSig M N A).

Definition SingularValueRCHNature (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M) := proj2_sig (SingularValueRCHSig K M N A).

Definition SingularValueRHNature (M N : nat) (A : Matrix Rfield (M + N) M) := proj2_sig (SingularValueRHSig M N A).

Definition SingularValueCHNature (M N : nat) (A : Matrix Cfield (M + N) M) := proj2_sig (SingularValueCHSig M N A).

Lemma SingularValueRCHNature2 : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M) (U : Matrix (RCfield K) (M + N) (M + N)) (V : Matrix (RCfield K) M M) (sigma : Rn M), (forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) -> UnitaryMatrixRC K (M + N) U -> UnitaryMatrixRC K M V -> A = Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (sigma m))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)) -> SingularValueRCH K M N A = sigma.
Proof.
move=> K M N A U V sigma H1 H2 H3 H4.
apply functional_extensionality.
move=> m.
apply (max_unique (fun (r0 : R) => exists (W : Ensemble (RCn K M)) (H1 : SubspaceVS (RCfield K) (FnVS (RCfield K) M) W) (H2 : FiniteDimensionVS (RCfield K) (SubspaceMakeVS (RCfield K) (FnVS (RCfield K) M) W H1)), DimensionSubspaceVS (RCfield K) (FnVS (RCfield K) M) W H1 H2 = S (proj1_sig m) /\ is_min (fun (r1 : R) => exists (x : RCn K M), In (RCn K M) W x /\ RCnNorm K M x = 1 /\ RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x))) = r1) r0)).
apply conj.
elim (proj2 (proj2 (SingularValueRCHNature K M N A))).
move=> U2.
elim.
move=> V2 H6.
apply (SingularValueNatureRCHSub K M N A U2 V2 (SingularValueRCH K M N A) (proj1 H6) (proj1 (proj2 H6))).
apply conj.
apply (proj1 (SingularValueRCHNature K M N A)).
apply (proj1 (proj2 (SingularValueRCHNature K M N A))).
apply (proj2 (proj2 H6)).
apply (SingularValueNatureRCHSub K M N A U V sigma H2 H3 H1 H4).
Qed.

Definition SingularValueRHNature2 : forall (M N : nat) (A : Matrix Rfield (M + N) M) (U : Matrix Rfield (M + N) (M + N)) (V : Matrix Rfield M M) (sigma : Rn M), (forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) -> OrthogonalMatrix (M + N) U -> OrthogonalMatrix M V -> A = Mmult Rfield (M + N) (M + N) M U (Mmult Rfield (M + N) M M (MBlockH Rfield M N M (MDiag Rfield M sigma) (MO Rfield N M)) (MTranspose Rfield M M V)) -> SingularValueRH M N A = sigma := SingularValueRCHNature2 RK.

Definition SingularValueCHNature2 : forall (M N : nat) (A : Matrix Cfield (M + N) M) (U : Matrix Cfield (M + N) (M + N)) (V : Matrix Cfield M M) (sigma : Rn M), (forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) -> UnitaryMatrix (M + N) U -> UnitaryMatrix M V -> A = Mmult Cfield (M + N) (M + N) M U (Mmult Cfield (M + N) M M (MBlockH Cfield M N M (MDiag Cfield M (fun (m : {n : nat | (n < M)%nat}) => Cmake (sigma m) 0)) (MO Cfield N M)) (AdjointMatrix M M V)) -> SingularValueCH M N A = sigma := SingularValueRCHNature2 CK.
