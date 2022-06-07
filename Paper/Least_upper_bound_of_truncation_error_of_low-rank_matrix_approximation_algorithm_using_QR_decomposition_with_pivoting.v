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
Require Import Coq.Logic.JMeq.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Image.
Require Import MyAlgebraicStructure.MyVectorSpace.
Require Import MyAlgebraicStructure.MyField.
Require Import Analysis.KaisekiNyuumonn.KaisekiNyuumonn1_1.
Require Import Analysis.KaisekiNyuumonn.KaisekiNyuumonn1_2.
Require Import LinearAlgebra.Matrix.
Require Import LinearAlgebra.SenkeiDaisuunoSekai.SenkeiDaisuunoSekai1.
Require Import Tools.MySum.
Require Import Tools.BasicTools.
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

Lemma AdjointMatrixOpp : forall (M N : nat) (A : Matrix Cfield M N), AdjointMatrix M N (Mopp Cfield M N A) = Mopp Cfield N M (AdjointMatrix M N A).
Proof.
move=> M N A.
unfold AdjointMatrix.
unfold Mopp.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply (Proposition_4_8_1_3 (A y x)).
Qed.

Definition AdjointMatrixRCOpp : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M N), AdjointMatrixRC K M N (Mopp (RCfield K) M N A) = Mopp (RCfield K) N M (AdjointMatrixRC K M N A) := fun (K : RC) => match K with
  | RK => MTransOpp Rfield
  | CK => AdjointMatrixOpp
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

Definition HermitianMatrix (N : nat) (A : Matrix Cfield N N) := AdjointMatrix N N A = A.

Definition HermitianMatrixRC (K : RC) (N : nat) (A : Matrix (RCfield K) N N) := AdjointMatrixRC K N N A = A.

Definition OrthogonalMatrix (N : nat) (A : Matrix Rfield N N) := Mmult Rfield N N N (MTranspose Rfield N N A) A = MI Rfield N.

Definition UnitaryMatrix (N : nat) (A : Matrix Cfield N N) := Mmult Cfield N N N (AdjointMatrix N N A) A = MI Cfield N.

Definition UnitaryMatrixRC (K : RC) (N : nat) (A : Matrix (RCfield K) N N) := Mmult (RCfield K) N N N (AdjointMatrixRC K N N A) A = MI (RCfield K) N.

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

Lemma SingularValueRCHNatureSub : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M) (U : Matrix (RCfield K) (M + N) (M + N)) (V : Matrix (RCfield K) M M) (sigma : {n : nat | (n < M)%nat} -> R), UnitaryMatrixRC K (M + N) U -> UnitaryMatrixRC K M V -> ((forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2)) -> A = Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (sigma m))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)) -> (forall (m : {n : nat | (n < M)%nat}), is_max (fun (r0 : R) => exists (W : Ensemble (RCn K M)) (H1 : SubspaceVS (RCfield K) (FnVS (RCfield K) M) W) (H2 : FiniteDimensionVS (RCfield K) (SubspaceMakeVS (RCfield K) (FnVS (RCfield K) M) W H1)), DimensionSubspaceVS (RCfield K) (FnVS (RCfield K) M) W H1 H2 = S (proj1_sig m) /\ is_min (fun (r1 : R) => exists (x : RCn K M), In (RCn K M) W x /\ RCnNorm K M x = 1 /\ RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x))) = r1) r0) (sigma m)).
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

Definition SingularValueRHNatureSub : forall (M N : nat) (A : Matrix Rfield (M + N) M) (U : Matrix Rfield (M + N) (M + N)) (V : Matrix Rfield M M) (sigma : Rn M), OrthogonalMatrix (M + N) U -> OrthogonalMatrix M V -> ((forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2)) -> A = Mmult Rfield (M + N) (M + N) M U (Mmult Rfield (M + N) M M (MBlockH Rfield M N M (MDiag Rfield M sigma) (MO Rfield N M)) (MTranspose Rfield M M V)) -> (forall (m : {n : nat | (n < M)%nat}), is_max (fun (r0 : R) => exists (W : Ensemble (Rn M)) (H1 : SubspaceVS Rfield (RnVS M) W) (H2 : FiniteDimensionVS Rfield (SubspaceMakeVS Rfield (RnVS M) W H1)), DimensionSubspaceVS Rfield (RnVS M) W H1 H2 = S (proj1_sig m) /\ is_min (fun (r1 : R) => exists (x : Rn M), In (Rn M) W x /\ RnNorm M x = 1 /\ RnNorm (M + N) (MMatrixToVector Rfield (M + N) (Mmult Rfield (M + N) M 1 A (MVectorToMatrix Rfield M x))) = r1) r0) (sigma m)) := SingularValueRCHNatureSub RK.

Definition SingularValueCHNatureSub : forall (M N : nat) (A : Matrix Cfield (M + N) M) (U : Matrix Cfield (M + N) (M + N)) (V : Matrix Cfield M M) (sigma : Rn M), UnitaryMatrix (M + N) U -> UnitaryMatrix M V -> ((forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2)) -> A = Mmult Cfield (M + N) (M + N) M U (Mmult Cfield (M + N) M M (MBlockH Cfield M N M (MDiag Cfield M (fun (m : {n : nat | (n < M)%nat}) => Cmake (sigma m) 0)) (MO Cfield N M)) (AdjointMatrix M M V)) -> (forall (m : {n : nat | (n < M)%nat}), is_max (fun (r0 : R) => exists (W : Ensemble (Cn M)) (H1 : SubspaceVS Cfield (FnVS Cfield M) W) (H2 : FiniteDimensionVS Cfield (SubspaceMakeVS Cfield (FnVS Cfield M) W H1)), DimensionSubspaceVS Cfield (FnVS Cfield M) W H1 H2 = S (proj1_sig m) /\ is_min (fun (r1 : R) => exists (x : Cn M), In (Cn M) W x /\ CnNorm M x = 1 /\ CnNorm (M + N) (MMatrixToVector Cfield (M + N) (Mmult Cfield (M + N) M 1 A (MVectorToMatrix Cfield M x))) = r1) r0) (sigma m)) := SingularValueRCHNatureSub CK.

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
apply (SingularValueRCHNatureSub K M N A U1 V1 sigma1 (proj1 H3) (proj1 (proj2 H3))).
apply conj.
apply (proj1 H1).
apply (proj1 (proj2 H1)).
apply (proj2 (proj2 H3)).
apply (SingularValueRCHNatureSub K M N A U2 V2 sigma2 (proj1 H4) (proj1 (proj2 H4))).
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
apply (SingularValueRCHNatureSub K M N A U2 V2 (SingularValueRCH K M N A) (proj1 H6) (proj1 (proj2 H6))).
apply conj.
apply (proj1 (SingularValueRCHNature K M N A)).
apply (proj1 (proj2 (SingularValueRCHNature K M N A))).
apply (proj2 (proj2 H6)).
apply (SingularValueRCHNatureSub K M N A U V sigma H2 H3 H1 H4).
Qed.

Definition SingularValueRHNature2 : forall (M N : nat) (A : Matrix Rfield (M + N) M) (U : Matrix Rfield (M + N) (M + N)) (V : Matrix Rfield M M) (sigma : Rn M), (forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) -> OrthogonalMatrix (M + N) U -> OrthogonalMatrix M V -> A = Mmult Rfield (M + N) (M + N) M U (Mmult Rfield (M + N) M M (MBlockH Rfield M N M (MDiag Rfield M sigma) (MO Rfield N M)) (MTranspose Rfield M M V)) -> SingularValueRH M N A = sigma := SingularValueRCHNature2 RK.

Definition SingularValueCHNature2 : forall (M N : nat) (A : Matrix Cfield (M + N) M) (U : Matrix Cfield (M + N) (M + N)) (V : Matrix Cfield M M) (sigma : Rn M), (forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) -> UnitaryMatrix (M + N) U -> UnitaryMatrix M V -> A = Mmult Cfield (M + N) (M + N) M U (Mmult Cfield (M + N) M M (MBlockH Cfield M N M (MDiag Cfield M (fun (m : {n : nat | (n < M)%nat}) => Cmake (sigma m) 0)) (MO Cfield N M)) (AdjointMatrix M M V)) -> SingularValueCH M N A = sigma := SingularValueRCHNature2 CK.

Lemma SingularValueRCHMaxNature : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M) (m : Count M), is_max (fun (r0 : R) => exists (W : Ensemble (RCn K M)) (H1 : SubspaceVS (RCfield K) (FnVS (RCfield K) M) W) (H2 : FiniteDimensionVS (RCfield K) (SubspaceMakeVS (RCfield K) (FnVS (RCfield K) M) W H1)), DimensionSubspaceVS (RCfield K) (FnVS (RCfield K) M) W H1 H2 = S (proj1_sig m) /\ is_min (fun (r1 : R) => exists (x : RCn K M), In (RCn K M) W x /\ RCnNorm K M x = 1 /\ RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x))) = r1) r0) (SingularValueRCH K M N A m).
Proof.
move=> K M N A.
elim (proj2 (proj2 (SingularValueRCHNature K M N A))).
move=> U.
elim.
move=> V H1.
apply (SingularValueRCHNatureSub K M N A U V (SingularValueRCH K M N A) (proj1 H1) (proj1 (proj2 H1))).
apply conj.
apply (proj1 (SingularValueRCHNature K M N A)).
apply (proj1 (proj2 (SingularValueRCHNature K M N A))).
apply (proj2 (proj2 H1)).
Qed.

Definition SingularValueRHMaxNature : forall (M N : nat) (A : Matrix Rfield (M + N) M) (m : Count M), is_max (fun (r0 : R) => exists (W : Ensemble (Rn M)) (H1 : SubspaceVS Rfield (FnVS Rfield M) W) (H2 : FiniteDimensionVS Rfield (SubspaceMakeVS Rfield (FnVS Rfield M) W H1)), DimensionSubspaceVS Rfield (FnVS Rfield M) W H1 H2 = S (proj1_sig m) /\ is_min (fun (r1 : R) => exists (x : Rn M), In (Rn M) W x /\ RnNorm M x = 1 /\ RnNorm (M + N) (MMatrixToVector Rfield (M + N) (Mmult Rfield (M + N) M 1 A (MVectorToMatrix Rfield M x))) = r1) r0) (SingularValueRH M N A m) := SingularValueRCHMaxNature RK.

Definition SingularValueCHMaxNature : forall (M N : nat) (A : Matrix Cfield (M + N) M) (m : Count M), is_max (fun (r0 : R) => exists (W : Ensemble (Cn M)) (H1 : SubspaceVS Cfield (FnVS Cfield M) W) (H2 : FiniteDimensionVS Cfield (SubspaceMakeVS Cfield (FnVS Cfield M) W H1)), DimensionSubspaceVS Cfield (FnVS Cfield M) W H1 H2 = S (proj1_sig m) /\ is_min (fun (r1 : R) => exists (x : Cn M), In (Cn M) W x /\ CnNorm M x = 1 /\ CnNorm (M + N) (MMatrixToVector Cfield (M + N) (Mmult Cfield (M + N) M 1 A (MVectorToMatrix Cfield M x))) = r1) r0) (SingularValueCH M N A m) := SingularValueRCHMaxNature CK.

Lemma CountReverseMonotonousDecrease : forall (N : nat) (m1 m2 : {n : nat | (n < N)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> (proj1_sig (CountReverse N m2) <= proj1_sig (CountReverse N m1))%nat.
Proof.
move=> N m1 m2 H1.
apply (plus_le_reg_l (proj1_sig (CountReverse N m2)) (proj1_sig (CountReverse N m1)) (S (proj1_sig m1))).
simpl.
rewrite (CountReverseNature N m1).
rewrite - {4} (CountReverseNature N m2).
apply le_n_S.
apply plus_le_compat_r.
apply H1.
Qed.

Lemma SingularValueRCHMinNature : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M) (m : Count M), is_min (fun (r0 : R) => exists (W : Ensemble (RCn K M)) (H1 : SubspaceVS (RCfield K) (FnVS (RCfield K) M) W) (H2 : FiniteDimensionVS (RCfield K) (SubspaceMakeVS (RCfield K) (FnVS (RCfield K) M) W H1)), DimensionSubspaceVS (RCfield K) (FnVS (RCfield K) M) W H1 H2 = (M - (proj1_sig m))%nat /\ is_max (fun (r1 : R) => exists (x : RCn K M), In (RCn K M) W x /\ RCnNorm K M x = 1 /\ RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x))) = r1) r0) (SingularValueRCH K M N A m).
Proof.
move=> K M N.
elim (le_lt_or_eq 0 M (le_0_n M)).
move=> H1 A.
elim (proj2 (proj2 (SingularValueRCHNature K M N A))).
move=> U.
elim.
move=> V H2.
suff: (forall (a b c : R), a * a + b * b = c * c -> c * c - b * b >= 0).
move=> H3.
suff: (forall (a b c : R) (H : a * a + b * b = c * c), a >= 0 -> a = MySqrt (exist (fun (r : R) => r >= 0) (c * c - b * b) (H3 a b c H))).
move=> H4.
suff: (forall (a b : R), a >= 0 -> b >= 0 -> a * a >= b * b -> a >= b).
move=> H5.
suff: (forall (a b : R), a >= 0 -> b >= 0 -> a * a = b * b -> a = b).
move=> H6.
suff: (forall (m : Count M), SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1) - SingularValueRCH K M N A m * SingularValueRCH K M N A m >= 0).
move=> H7.
suff: (let B := Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun m : {n : nat | (n < M)%nat} => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1) - SingularValueRCH K M N A m * SingularValueRCH K M N A m) (H7 m))))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)) in forall (m : Count M), is_min (fun (r0 : R) => exists (W : Ensemble (RCn K M)) (H8 : SubspaceVS (RCfield K) (FnVS (RCfield K) M) W) (H9 : FiniteDimensionVS (RCfield K) (SubspaceMakeVS (RCfield K) (FnVS (RCfield K) M) W H8)), DimensionSubspaceVS (RCfield K) (FnVS (RCfield K) M) W H8 H9 = (M - proj1_sig m)%nat /\ is_max (fun r1 : R => exists x : RCn K M, In (RCn K M) W x /\ RCnNorm K M x = 1 /\ RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x))) = r1) r0) (SingularValueRCH K M N A m)).
apply.
move=> B.
suff: (forall (x : RCn K M), RCnNorm K M x = 1 -> RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x))) * RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x))) + RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 B (MVectorToMatrix (RCfield K) M x))) * RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 B (MVectorToMatrix (RCfield K) M x))) = SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1)).
move=> H8.
suff: (forall (m : Count M), SingularValueRCH K M N A m * SingularValueRCH K M N A m + SingularValueRCH K M N B (CountReverse M m) * SingularValueRCH K M N B (CountReverse M m) = SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1)).
move=> H9 m.
rewrite (H4 (SingularValueRCH K M N A m) (SingularValueRCH K M N B (CountReverse M m)) (SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1)) (H9 m) (proj1 (SingularValueRCHNature K M N A) m)).
apply conj.
elim (proj1 (SingularValueRCHMaxNature K M N B (CountReverse M m))).
move=> W.
elim.
move=> H10.
elim.
move=> H11 H12.
exists W.
exists H10.
exists H11.
apply conj.
rewrite (proj1 H12).
apply (plus_reg_l (S (proj1_sig (CountReverse M m))) (M - proj1_sig m) (proj1_sig m)).
rewrite - plus_Snm_nSm.
simpl.
rewrite (CountReverseNature M m).
rewrite (le_plus_minus_r (proj1_sig m) M).
reflexivity.
apply (le_trans (proj1_sig m) (S (proj1_sig m)) M (le_S (proj1_sig m) (proj1_sig m) (le_n (proj1_sig m))) (proj2_sig m)).
apply conj.
elim (proj1 (proj2 H12)).
move=> x H13.
exists x.
apply conj.
apply (proj1 H13).
apply conj.
apply (proj1 (proj2 H13)).
suff: (RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x))) = SingularValueRCH K M N A m).
move=> H14.
rewrite H14.
apply (H4 (SingularValueRCH K M N A m) (SingularValueRCH K M N B (CountReverse M m)) (SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1)) (H9 m) (proj1 (SingularValueRCHNature K M N A) m)).
apply H6.
apply (RCnNormNature K (M + N)).
apply (proj1 (SingularValueRCHNature K M N A) m).
apply (Rplus_eq_reg_r (RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 B (MVectorToMatrix (RCfield K) M x))) * RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 B (MVectorToMatrix (RCfield K) M x))))).
rewrite {3} (proj2 (proj2 H13)).
rewrite {3} (proj2 (proj2 H13)).
rewrite (H9 m).
apply (H8 x (proj1 (proj2 H13))).
move=> r H13.
apply Rge_le.
apply H5.
apply MySqrtNature.
elim H13.
move=> x H14.
rewrite - (proj2 (proj2 H14)).
apply RCnNormNature.
rewrite - (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1) - SingularValueRCH K M N B (CountReverse M m) * SingularValueRCH K M N B (CountReverse M m)) (H3 (SingularValueRCH K M N A m) (SingularValueRCH K M N B (CountReverse M m)) (SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1)) (H9 m))))).
simpl.
apply Rle_ge.
apply (Rplus_le_reg_r (SingularValueRCH K M N B (CountReverse M m) * SingularValueRCH K M N B (CountReverse M m))).
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
apply (Rplus_le_reg_l (- (r * r))).
rewrite - Rplus_assoc.
rewrite (Rplus_opp_l (r * r)).
rewrite Rplus_0_l.
rewrite Rplus_comm.
apply Rge_le.
elim H13.
move=> x H14.
rewrite - (proj2 (proj2 H14)).
rewrite - (H8 x (proj1 (proj2 H14))).
rewrite Rplus_comm.
rewrite - Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
suff: (RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 B (MVectorToMatrix (RCfield K) M x))) >= SingularValueRCH K M N B (CountReverse M m)).
move=> H15.
apply Rmult_ge_compat.
apply (proj1 (SingularValueRCHNature K M N B) (CountReverse M m)).
apply (proj1 (SingularValueRCHNature K M N B) (CountReverse M m)).
apply H15.
apply H15.
apply (proj2 (proj2 H12)).
exists x.
apply conj.
apply (proj1 H14).
apply conj.
apply (proj1 (proj2 H14)).
reflexivity.
move=> r.
elim.
move=> W.
elim.
move=> H10.
elim.
move=> H11 H12.
elim (proj1 (proj2 H12)).
move=> x H13.
apply H5.
rewrite - (proj2 (proj2 H13)).
apply RCnNormNature.
apply MySqrtNature.
rewrite - (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1) - SingularValueRCH K M N B (CountReverse M m) * SingularValueRCH K M N B (CountReverse M m)) (H3 (SingularValueRCH K M N A m) (SingularValueRCH K M N B (CountReverse M m)) (SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1)) (H9 m))))).
simpl.
apply Rle_ge.
apply (Rplus_le_reg_r (SingularValueRCH K M N B (CountReverse M m) * SingularValueRCH K M N B (CountReverse M m))).
rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
apply (Rplus_le_reg_l (- (r * r))).
rewrite - Rplus_assoc.
rewrite (Rplus_opp_l (r * r)).
rewrite Rplus_0_l.
rewrite Rplus_comm.
rewrite - (proj2 (proj2 H13)).
rewrite - (H8 x (proj1 (proj2 H13))).
rewrite Rplus_comm.
rewrite - Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
suff: (SingularValueRCH K M N B (CountReverse M m) >= RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 B (MVectorToMatrix (RCfield K) M x)))).
move=> H14.
apply Rge_le.
apply Rmult_ge_compat.
apply RCnNormNature.
apply RCnNormNature.
apply H14.
apply H14.
apply Rle_ge.
apply (proj2 (SingularValueRCHMaxNature K M N B (CountReverse M m))).
exists W.
exists H10.
exists H11.
apply conj.
simpl.
rewrite (proj1 H12).
apply (plus_reg_l (M - proj1_sig m)%nat (S (proj1_sig (CountReverse M m))) (proj1_sig m)).
rewrite (le_plus_minus_r (proj1_sig m) M).
rewrite - plus_Snm_nSm.
simpl.
rewrite (CountReverseNature M m).
reflexivity.
apply (le_trans (proj1_sig m) (S (proj1_sig m)) M (le_S (proj1_sig m) (proj1_sig m) (le_n (proj1_sig m))) (proj2_sig m)).
apply conj.
exists x.
apply conj.
apply (proj1 H13).
apply conj.
apply (proj1 (proj2 H13)).
reflexivity.
move=> l.
elim.
move=> y H14.
rewrite - (proj2 (proj2 H14)).
apply H5.
apply RCnNormNature.
apply RCnNormNature.
apply (Rplus_ge_reg_l (RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x))) * RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x))))).
rewrite (H8 x (proj1 (proj2 H13))).
rewrite - (H8 y (proj1 (proj2 H14))).
apply Rplus_ge_compat_r.
suff: (RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M x))) >= RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 A (MVectorToMatrix (RCfield K) M y)))).
move=> H15.
apply Rmult_ge_compat.
apply RCnNormNature.
apply RCnNormNature.
apply H15.
apply H15.
rewrite (proj2 (proj2 H13)).
apply Rle_ge.
apply (proj2 (proj2 H12)).
exists y.
apply conj.
apply (proj1 H14).
apply conj.
apply (proj1 (proj2 H14)).
reflexivity.
suff: (forall (m : Count M), SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A (CountReverse M m) * SingularValueRCH K M N A (CountReverse M m) >= 0).
move=> H9.
suff: (SingularValueRCH K M N B = (fun (m : Count M) => MySqrt (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A (CountReverse M m) * SingularValueRCH K M N A (CountReverse M m)) (H9 m)))).
move=> H10 m.
rewrite H10.
rewrite - (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A (CountReverse M (CountReverse M m)) * SingularValueRCH K M N A (CountReverse M (CountReverse M m))) (H9 (CountReverse M m))))).
simpl.
rewrite (CountReverseInvolutive M m).
unfold Rminus.
rewrite Rplus_comm.
rewrite Rplus_assoc.
rewrite Rplus_opp_l.
apply Rplus_0_r.
apply (SingularValueRCHNature2 K M N B (Mmult (RCfield K) (M + N) (M + N) (M + N) U (MBlockH (RCfield K) M N (M + N) (MBlockW (RCfield K) M M N (ReverseMatrix (RCfield K) M) (MO (RCfield K) M N)) (MBlockW (RCfield K) N M N (MO (RCfield K) N M) (MI (RCfield K) N)))) (Mmult (RCfield K) M M M V (ReverseMatrix (RCfield K) M))).
apply conj.
move=> m.
apply MySqrtNature.
move=> m1 m2 H10.
apply H5.
apply MySqrtNature.
apply MySqrtNature.
rewrite - (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A (CountReverse M m1) * SingularValueRCH K M N A (CountReverse M m1)) (H9 m1)))).
rewrite - (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A (CountReverse M m2) * SingularValueRCH K M N A (CountReverse M m2)) (H9 m2)))).
simpl.
apply Rplus_ge_compat_l.
apply Ropp_ge_contravar.
suff: (SingularValueRCH K M N A (CountReverse M m2) >= SingularValueRCH K M N A (CountReverse M m1)).
move=> H11.
apply Rmult_ge_compat.
apply (proj1 (SingularValueRCHNature K M N A) (CountReverse M m1)).
apply (proj1 (SingularValueRCHNature K M N A) (CountReverse M m1)).
apply H11.
apply H11.
apply (proj1 (proj2 (SingularValueRCHNature K M N A)) (CountReverse M m2) (CountReverse M m1)).
apply (CountReverseMonotonousDecrease M m1 m2 H10).
apply (UnitaryMatrixRCChain K (M + N)).
apply (proj1 H2).
unfold UnitaryMatrixRC.
rewrite (BlockHAdjointMatrixRC K M N (M + N)).
rewrite (BlockWAdjointMatrixRC K M M N).
rewrite (BlockWAdjointMatrixRC K N M N).
rewrite (AdjointMatrixRCO K M N).
rewrite (AdjointMatrixRCO K N M).
rewrite (AdjointMatrixRCI K N).
suff: (AdjointMatrixRC K M M (ReverseMatrix (RCfield K) M) = MTranspose (RCfield K) M M (ReverseMatrix (RCfield K) M)).
move=> H10.
rewrite H10.
rewrite (ReverseMatrixTrans (RCfield K) M).
rewrite (MBlockHWMult (RCfield K) (M + N) M N (M + N)).
rewrite (MBlockHMult (RCfield K) M N M (M + N)).
rewrite (MBlockHMult (RCfield K) M N N (M + N)).
rewrite (MBlockWMult (RCfield K) M M M N).
rewrite (MBlockWMult (RCfield K) N M M N).
rewrite (MBlockWMult (RCfield K) M N M N).
rewrite (MBlockWMult (RCfield K) N N M N).
rewrite (ReverseMatrixInvolutive (RCfield K) M).
rewrite (Mmult_O_r (RCfield K) M M N (ReverseMatrix (RCfield K) M)).
rewrite (Mmult_O_l (RCfield K) N M M (ReverseMatrix (RCfield K) M)).
rewrite (Mmult_O_l (RCfield K) N M N (MO (RCfield K) M N)).
rewrite (Mmult_O_l (RCfield K) M N M (MO (RCfield K) N M)).
rewrite (Mmult_I_r (RCfield K) M N (MO (RCfield K) M N)).
rewrite (Mmult_I_l (RCfield K) N M (MO (RCfield K) N M)).
rewrite (Mmult_I_l (RCfield K) N N (MI (RCfield K) N)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mplus.
unfold MI at 3.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H11.
suff: (x = y).
move=> H12.
rewrite H12.
unfold MBlockH.
unfold MBlockW.
elim (AddConnectInv M N y).
move=> z.
unfold MI.
elim (Nat.eq_dec (proj1_sig z) (proj1_sig z)).
move=> H13.
apply (Fadd_O_r (RCfield K) (FI (RCfield K))).
elim.
reflexivity.
move=> z.
unfold MI.
elim (Nat.eq_dec (proj1_sig z) (proj1_sig z)).
move=> H13.
apply (Fadd_O_l (RCfield K) (FI (RCfield K))).
elim.
reflexivity.
apply sig_map.
apply H11.
rewrite - {1} (proj2 (AddConnectInvRelation M N) x).
rewrite - {1} (proj2 (AddConnectInvRelation M N) y).
unfold MBlockH.
unfold MBlockW.
elim (AddConnectInv M N x).
move=> z.
elim (AddConnectInv M N y).
move=> w.
rewrite - (proj1 (AddConnectNature M N) z).
rewrite - (proj1 (AddConnectNature M N) w).
move=> H11.
unfold MI.
elim (Nat.eq_dec (proj1_sig z) (proj1_sig w)).
move=> H12.
elim (H11 H12).
move=> H12.
apply (Fadd_O_l (RCfield K) (RCO K)).
move=> w H11.
apply (Fadd_O_l (RCfield K) (RCO K)).
move=> z.
elim (AddConnectInv M N y).
move=> w H12.
apply (Fadd_O_l (RCfield K) (RCO K)).
move=> w.
rewrite - (proj2 (AddConnectNature M N) z).
rewrite - (proj2 (AddConnectNature M N) w).
move=> H11.
unfold MI.
elim (Nat.eq_dec (proj1_sig z) (proj1_sig w)).
move=> H12.
elim H11.
rewrite H12.
reflexivity.
move=> H12.
apply (Fadd_O_l (RCfield K) (RCO K)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold AdjointMatrixRC.
unfold MTranspose.
unfold ReverseMatrix.
unfold MI.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (CountReverse M x))).
move=> H10.
apply (ConjugateRCI K).
move=> H10.
apply (ConjugateRCO K).
apply (UnitaryMatrixRCChain K M).
apply (proj1 (proj2 H2)).
unfold UnitaryMatrixRC.
suff: (AdjointMatrixRC K M M (ReverseMatrix (RCfield K) M) = MTranspose (RCfield K) M M (ReverseMatrix (RCfield K) M)).
move=> H10.
rewrite H10.
rewrite (ReverseMatrixTrans (RCfield K) M).
apply (ReverseMatrixInvolutive (RCfield K) M).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold AdjointMatrixRC.
unfold MTranspose.
unfold ReverseMatrix.
unfold MI.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (CountReverse M x))).
move=> H10.
apply (ConjugateRCI K).
move=> H10.
apply (ConjugateRCO K).
rewrite (MBlockHMult (RCfield K) M N M M).
rewrite (Mmult_O_l (RCfield K) N M M).
rewrite (AdjointMatrixRCMult K M M).
rewrite (MBlockHWWHSame (RCfield K) M N M N).
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) M).
rewrite (MBlockHWMult (RCfield K) (M + N) M N M).
rewrite (Mmult_O_r (RCfield K) (M + N) N M).
rewrite (Mplus_comm (RCfield K) (M + N) M).
rewrite (Mplus_O_l (RCfield K) (M + N) M).
rewrite (MBlockHMult (RCfield K) M N M M).
rewrite (Mmult_O_l (RCfield K) N M M).
rewrite - (Mmult_assoc (RCfield K) M M M M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A (CountReverse M m) * SingularValueRCH K M N A (CountReverse M m)) (H9 m)))))).
rewrite - (Mmult_assoc (RCfield K) M M M M (ReverseMatrix (RCfield K) M)).
rewrite - (Mmult_assoc (RCfield K) M M M M (ReverseMatrix (RCfield K) M)).
suff: (AdjointMatrixRC K M M (ReverseMatrix (RCfield K) M) = MTranspose (RCfield K) M M (ReverseMatrix (RCfield K) M)).
move=> H10.
rewrite H10.
rewrite (ReverseMatrixTrans (RCfield K) M).
rewrite (MDiagReverseRelation (RCfield K) M).
unfold B.
rewrite (MBlockHMult (RCfield K) M N M M).
rewrite (Mmult_O_l (RCfield K) N M M).
suff: ((fun (m : {n : nat | (n < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A m * SingularValueRCH K M N A m) (H7 m)))) = (fun (m : Count M) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A (CountReverse M (CountReverse M m)) * SingularValueRCH K M N A (CountReverse M (CountReverse M m))) (H9 (CountReverse M m)))))).
move=> H11.
rewrite H11.
reflexivity.
apply functional_extensionality.
move=> m.
suff: ((exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A m * SingularValueRCH K M N A m) (H7 m)) = (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A (CountReverse M (CountReverse M m)) * SingularValueRCH K M N A (CountReverse M (CountReverse M m))) (H9 (CountReverse M m)))).
move=> H11.
rewrite H11.
reflexivity.
apply sig_map.
simpl.
rewrite (CountReverseInvolutive M m).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold AdjointMatrixRC.
unfold MTranspose.
unfold ReverseMatrix.
unfold MI.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (CountReverse M x))).
move=> H10.
apply (ConjugateRCI K).
move=> H10.
apply (ConjugateRCO K).
move=> m.
apply Rge_minus.
apply Rmult_ge_compat.
apply (proj1 (SingularValueRCHNature K M N A) (CountReverse M m)).
apply (proj1 (SingularValueRCHNature K M N A) (CountReverse M m)).
apply (proj1 (proj2 (SingularValueRCHNature K M N A)) (exist (fun (k : nat) => (k < M)%nat) O H1) (CountReverse M m) (le_0_n (proj1_sig (CountReverse M m)))).
apply (proj1 (proj2 (SingularValueRCHNature K M N A)) (exist (fun (k : nat) => (k < M)%nat) O H1) (CountReverse M m) (le_0_n (proj1_sig (CountReverse M m)))).
suff: (forall (L : nat) (Q : Matrix (RCfield K) L L) (x : RCn K L), UnitaryMatrixRC K L Q -> RCnNorm K L (MMatrixToVector (RCfield K) L (Mmult (RCfield K) L L 1 Q (MVectorToMatrix (RCfield K) L x))) = RCnNorm K L x).
move=> H8.
suff: (forall (x : RCn K M), RCnNorm K M x = 1 -> RCnNorm K M (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))) (MVectorToMatrix (RCfield K) M x))) * RCnNorm K M (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))) (MVectorToMatrix (RCfield K) M x))) + RCnNorm K M (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) 0%nat H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) 0%nat H1) - SingularValueRCH K M N A m * SingularValueRCH K M N A m) (H7 m))))) (MVectorToMatrix (RCfield K) M x))) * RCnNorm K M (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) 0%nat H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) 0%nat H1) - SingularValueRCH K M N A m * SingularValueRCH K M N A m) (H7 m))))) (MVectorToMatrix (RCfield K) M x))) = SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1)).
move=> H9.
suff: (forall (D : Matrix (RCfield K) M M) (x : RCn K M), RCnNorm K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 (MBlockH (RCfield K) M N M D (MO (RCfield K) N M)) (MVectorToMatrix (RCfield K) M x))) = RCnNorm K M (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 D (MVectorToMatrix (RCfield K) M x)))).
move=> H10 x H11.
rewrite {2} (proj2 (proj2 H2)).
rewrite {1} (proj2 (proj2 H2)).
unfold B.
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) M 1 U).
rewrite - (proj2 (MVectorMatrixRelation (RCfield K) (M + N)) (Mmult (RCfield K) (M + N) M 1 (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)) (MVectorToMatrix (RCfield K) M x))).
rewrite (H8 (M + N)%nat U).
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) M 1 U).
rewrite - (proj2 (MVectorMatrixRelation (RCfield K) (M + N)) (Mmult (RCfield K) (M + N) M 1 (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A m * SingularValueRCH K M N A m) (H7 m))))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)) (MVectorToMatrix (RCfield K) M x))).
rewrite (H8 (M + N)%nat U).
rewrite (Mmult_assoc (RCfield K) (M + N) M M 1).
rewrite (Mmult_assoc (RCfield K) (M + N) M M 1).
rewrite - (proj2 (MVectorMatrixRelation (RCfield K) M) (Mmult (RCfield K) M M 1 (AdjointMatrixRC K M M V) (MVectorToMatrix (RCfield K) M x))).
rewrite H10.
rewrite H10.
apply (H9 (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (AdjointMatrixRC K M M V) (MVectorToMatrix (RCfield K) M x)))).
rewrite (H8 M (AdjointMatrixRC K M M V)).
apply H11.
unfold UnitaryMatrixRC.
rewrite (AdjointMatrixRCInvolutive K M M V).
apply (proj1 (MmultILRSame (RCfield K) M (AdjointMatrixRC K M M V) V) (proj1 (proj2 H2))).
apply (proj1 H2).
apply (proj1 H2).
move=> D x.
apply H6.
apply RCnNormNature.
apply RCnNormNature.
rewrite - (proj2 (RCnNormNature K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) M 1 (MBlockH (RCfield K) M N M D (MO (RCfield K) N M)) (MVectorToMatrix (RCfield K) M x))))).
rewrite - (proj2 (RCnNormNature K M (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 D (MVectorToMatrix (RCfield K) M x))))).
rewrite (RCnInnerProductMatrix K (M + N)).
rewrite (RCnInnerProductMatrix K M).
rewrite (proj2 (MVectorMatrixRelation (RCfield K) (M + N))).
rewrite (proj2 (MVectorMatrixRelation (RCfield K) M)).
rewrite (AdjointMatrixRCMult K (M + N) M 1).
rewrite (AdjointMatrixRCMult K M M 1).
rewrite (Mmult_assoc (RCfield K) 1 M (M + N) 1 (AdjointMatrixRC K M 1 (MVectorToMatrix (RCfield K) M x))).
rewrite (Mmult_assoc (RCfield K) 1 M M 1 (AdjointMatrixRC K M 1 (MVectorToMatrix (RCfield K) M x))).
rewrite - (Mmult_assoc (RCfield K) M (M + N) M 1 (AdjointMatrixRC K (M + N) M (MBlockH (RCfield K) M N M D (MO (RCfield K) N M)))).
rewrite - (Mmult_assoc (RCfield K) M M M 1 (AdjointMatrixRC K M M D)).
rewrite (BlockHAdjointMatrixRC K M N M).
rewrite (MBlockHWMult (RCfield K) M M N M).
rewrite (Mmult_O_r (RCfield K) M N M).
rewrite (Mplus_comm (RCfield K) M M).
rewrite (Mplus_O_l (RCfield K) M M).
reflexivity.
move=> x H9.
rewrite - (proj2 (RCnNormNature K M (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))) (MVectorToMatrix (RCfield K) M x))))).
rewrite - (proj2 (RCnNormNature K M (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A m * SingularValueRCH K M N A m) (H7 m))))) (MVectorToMatrix (RCfield K) M x))))).
rewrite - {3} (Rmult_1_r (SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (m : nat) => (m < M)%nat) O H1))).
rewrite - (Rmult_1_l 1).
rewrite - H9.
rewrite - (proj2 (RCnNormNature K M x)).
unfold RCnInnerProduct.
rewrite - (RCReplus K).
suff: (RCplus K = CMc (RCPCM K)).
move=> H10.
rewrite H10.
rewrite - (MySumF2Distr (Count M) (RCPCM K) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => RCmult K (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (MDiag (RCfield K) M (fun (m : {k : nat | (k < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))) (MVectorToMatrix (RCfield K) M x)) n) (ConjugateRC K (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (MDiag (RCfield K) M (fun (m : {k : nat | (k < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))) (MVectorToMatrix (RCfield K) M x)) n))) (fun (n : Count M) => RCmult K (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (MDiag (RCfield K) M (fun (m : {k : nat | (k < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A m * SingularValueRCH K M N A m) (H7 m))))) (MVectorToMatrix (RCfield K) M x)) n) (ConjugateRC K (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (MDiag (RCfield K) M (fun (m : {k : nat | (k < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A m * SingularValueRCH K M N A m) (H7 m))))) (MVectorToMatrix (RCfield K) M x)) n))) (fun (n : Count M) => RCplus K (RCmult K (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (MDiag (RCfield K) M (fun (m : {k : nat | (k < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))) (MVectorToMatrix (RCfield K) M x)) n) (ConjugateRC K (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (MDiag (RCfield K) M (fun (m : {k : nat | (k < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))) (MVectorToMatrix (RCfield K) M x)) n))) ( RCmult K (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (MDiag (RCfield K) M (fun (m : {k : nat | (k < M)%nat}) => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A m * SingularValueRCH K M N A m) (H7 m))))) (MVectorToMatrix (RCfield K) M x)) n) (ConjugateRC K (MMatrixToVector (RCfield K) M (Mmult (RCfield K) M M 1 (MDiag (RCfield K) M (fun m : {k : nat | (k < M)%nat} => IRRC K (MySqrt (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A m * SingularValueRCH K M N A m) (H7 m))))) (MVectorToMatrix (RCfield K) M x)) n))))).
apply (FiniteSetInduction (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
suff: (RCRe K (CMe (RCPCM K)) = 0).
move=> H11.
rewrite H11.
rewrite Rmult_0_r.
reflexivity.
elim K.
reflexivity.
reflexivity.
move=> D d H11 H12 H13 H14.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (RCReplus K).
simpl.
rewrite (RCReplus K (MySumF2 (Count M) D (RCPCM K) (fun (n : Count M) => RCmult K (x n) (ConjugateRC K (x n))))).
rewrite Rmult_plus_distr_l.
rewrite H14.
apply Rplus_eq_compat_l.
unfold MMatrixToVector.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < M)%nat} (FiniteSingleton (Count M) d)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (MySumF2Included {n : nat | (n < M)%nat} (FiniteSingleton (Count M) d)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (CM_O_r (FPCM (RCfield K))).
rewrite (CM_O_r (FPCM (RCfield K))).
unfold MDiag.
elim (Nat.eq_dec (proj1_sig d) (proj1_sig d)).
move=> H15.
unfold MVectorToMatrix.
simpl.
rewrite Proposition_4_8_2_RC.
rewrite Proposition_4_8_2_RC.
suff: (forall (K : RC) (c : R), ConjugateRC K (IRRC K c) = IRRC K c).
move=> H16.
rewrite H16.
rewrite H16.
suff: (forall (a b c : RCT K), RCmult K (RCmult K a b) (RCmult K a c) = RCmult K (RCmult K a a) (RCmult K b c)).
move=> H17.
rewrite H17.
rewrite H17.
rewrite - (IRRCmult K).
rewrite - (IRRCmult K).
suff: (forall (K : RC) (c : R) (d : RCT K), RCRe K (RCmult K (IRRC K c) d) = c * RCRe K d).
move=> H18.
rewrite RCReplus.
rewrite (H18 K).
rewrite (H18 K).
rewrite - (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) * SingularValueRCH K M N A (exist (fun (k : nat) => (k < M)%nat) O H1) - SingularValueRCH K M N A d * SingularValueRCH K M N A d) (H7 d)))).
simpl.
rewrite - Rmult_plus_distr_r.
rewrite Rplus_comm.
unfold Rminus.
rewrite Rplus_assoc.
unfold SingularValueRCH.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
reflexivity.
elim.
move=> c e.
reflexivity.
move=> c e.
simpl.
unfold IRC.
unfold Cmult.
rewrite (CmakeRe (Cmake c 0 CRe * e CRe - Cmake c 0 CIm * e CIm) (Cmake c 0 CRe * e CIm + Cmake c 0 CIm * e CRe)).
rewrite (CmakeRe c 0).
rewrite (CmakeIm c 0).
rewrite (Rmult_0_l (e CIm)).
apply (Rminus_0_r (c * e CRe)).
move=> a b c.
rewrite (RCmult_assoc K a b (RCmult K a c)).
rewrite (RCmult_assoc K a a (RCmult K b c)).
rewrite - (RCmult_assoc K b a c).
rewrite - (RCmult_assoc K a b c).
rewrite (RCmult_comm K a b).
reflexivity.
elim.
move=> c.
reflexivity.
move=> c.
simpl.
unfold Conjugate.
unfold IRC.
rewrite (CmakeRe c 0).
rewrite (CmakeIm c 0).
rewrite Ropp_0.
reflexivity.
elim.
reflexivity.
move=> u.
elim.
move=> u0 H15 H16.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig d) (proj1_sig u0)).
move=> H17.
elim H15.
suff: (d = u0).
move=> H18.
rewrite H18.
apply (In_singleton (Count M) u0).
apply sig_map.
apply H17.
move=> H17.
apply (Fmul_O_l (RCfield K)).
move=> u H15.
apply (Full_intro {n : nat | (n < M)%nat} u).
move=> u.
elim.
move=> u0 H15 H16.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig d) (proj1_sig u0)).
move=> H17.
elim H15.
suff: (d = u0).
move=> H18.
rewrite H18.
apply (In_singleton (Count M) u0).
apply sig_map.
apply H17.
move=> H17.
apply (Fmul_O_l (RCfield K)).
move=> u H15.
apply (Full_intro {n : nat | (n < M)%nat} u).
apply H13.
apply H13.
move=> u H11.
reflexivity.
reflexivity.
move=> L Q x H8.
apply H6.
apply (RCnNormNature K L).
apply (RCnNormNature K L x).
rewrite - (proj2 (RCnNormNature K L (MMatrixToVector (RCfield K) L (Mmult (RCfield K) L L 1 Q (MVectorToMatrix (RCfield K) L x))))).
rewrite - (proj2 (RCnNormNature K L x)).
rewrite (RCnInnerProductMatrix K L (MMatrixToVector (RCfield K) L (Mmult (RCfield K) L L 1 Q (MVectorToMatrix (RCfield K) L x)))).
rewrite (RCnInnerProductMatrix K L x).
rewrite (proj2 (MVectorMatrixRelation (RCfield K) L)).
rewrite (AdjointMatrixRCMult K L L 1).
rewrite (Mmult_assoc (RCfield K) 1 L L 1 (AdjointMatrixRC K L 1 (MVectorToMatrix (RCfield K) L x)) (AdjointMatrixRC K L L Q) (Mmult (RCfield K) L L 1 Q (MVectorToMatrix (RCfield K) L x))).
rewrite - (Mmult_assoc (RCfield K) L L L 1 (AdjointMatrixRC K L L Q) Q (MVectorToMatrix (RCfield K) L x)).
rewrite H8.
rewrite (Mmult_I_l (RCfield K) L 1 (MVectorToMatrix (RCfield K) L x)).
reflexivity.
move=> m.
apply Rge_minus.
apply Rmult_ge_compat.
apply (proj1 (SingularValueRCHNature K M N A) m).
apply (proj1 (SingularValueRCHNature K M N A) m).
apply (proj1 (proj2 (SingularValueRCHNature K M N A)) (exist (fun (k : nat) => (k < M)%nat) O H1) m (le_0_n (proj1_sig m))).
apply (proj1 (proj2 (SingularValueRCHNature K M N A)) (exist (fun (k : nat) => (k < M)%nat) O H1) m (le_0_n (proj1_sig m))).
move=> a b H6 H7 H8.
apply (Rge_antisym a b).
apply (H5 a b H6 H7).
right.
apply H8.
apply (H5 b a H7 H6).
right.
rewrite H8.
reflexivity.
move=> a b H5 H6 H7.
apply (Rnot_lt_ge a b).
move=> H8.
apply (Rge_not_lt (a * a) (b * b) H7).
apply (Rmult_le_0_lt_compat a b a b).
apply (Rge_le a 0 H5).
apply (Rge_le a 0 H5).
apply H8.
apply H8.
move=> a b c H4 H5.
rewrite (MySqrtNature2 (exist (fun (r : R) => r >= 0) (c * c - b * b) (H3 a b c H4)) a).
reflexivity.
apply conj.
apply H5.
apply (Rplus_eq_reg_r (b * b) (c * c - b * b) (a * a)).
rewrite H4.
rewrite (Rplus_assoc (c * c) (- (b * b)) (b * b)).
rewrite (Rplus_opp_l (b * b)).
apply (Rplus_0_r (c * c)).
move=> a b c H3.
rewrite - H3.
unfold Rminus.
rewrite (Rplus_assoc (a * a) (b * b) (- (b * b))).
rewrite (Rplus_opp_r (b * b)).
rewrite (Rplus_0_r (a * a)).
apply (Formula_1_3 a).
move=> H1.
rewrite - H1.
move=> A m.
elim (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) (proj2_sig m)).
Qed.

Lemma RestrictMetRefl : forall (M : Metric_Space) (A : Ensemble (Base M)) (x y : {r : Base M | A r}), dist M (proj1_sig x) (proj1_sig y) = 0 <-> x = y.
Proof.
move=> M A x y.
apply conj.
move=> H1.
apply sig_map.
apply (proj1 (dist_refl M (proj1_sig x) (proj1_sig y)) H1).
move=> H1.
apply (proj2 (dist_refl M (proj1_sig x) (proj1_sig y))).
rewrite H1.
reflexivity.
Qed.

Definition RestrictMet (M : Metric_Space) (A : Ensemble (Base M)) := Build_Metric_Space {r : Base M | A r} (fun (x y : {r : Base M | A r}) => dist M (proj1_sig x) (proj1_sig y)) (fun (x y : {r : Base M | A r}) => dist_pos M (proj1_sig x) (proj1_sig y)) (fun (x y : {r : Base M | A r}) => dist_sym M (proj1_sig x) (proj1_sig y)) (RestrictMetRefl M A) (fun (x y z : {r : Base M | A r}) => dist_tri M (proj1_sig x) (proj1_sig y) (proj1_sig z)).

Lemma MySqrtContinuous : forall (x : {r : R | r >= 0}), ContinuousMet (RestrictMet R_met (fun (r : R) => r >= 0)) R_met MySqrt (Full_set {r : R | r >= 0}) x.
Proof.
move=> x eps H1.
suff: (forall (y : {r : R | r >= 0}), proj1_sig y - proj1_sig x < (eps + MySqrt x) * (eps + MySqrt x) - proj1_sig x -> MySqrt y - MySqrt x < eps).
move=> H2.
suff: (forall (y : {r : R | r >= 0}), proj1_sig y - proj1_sig x > (Rmax (MySqrt x - eps) 0) * (Rmax (MySqrt x - eps) 0) - proj1_sig x -> MySqrt y - MySqrt x > - eps).
move=> H3.
suff: ((eps + MySqrt x) * (eps + MySqrt x) - proj1_sig x > 0).
move=> H4.
elim (proj2_sig x).
move=> H5.
exists (Rmin ((eps + MySqrt x) * (eps + MySqrt x) - proj1_sig x) (proj1_sig x - (Rmax (MySqrt x - eps) 0) * (Rmax (MySqrt x - eps) 0))).
apply conj.
apply Rmin_case.
rewrite (proj2 (MySqrtNature x)).
apply Rgt_minus.
suff: (eps + MySqrt x > MySqrt x).
move=> H6.
apply Rmult_le_0_lt_compat.
apply Rge_le.
apply (proj1 (MySqrtNature x)).
apply Rge_le.
apply (proj1 (MySqrtNature x)).
apply H6.
apply H6.
rewrite - {2} (Rplus_0_l (MySqrt x)).
apply (Rplus_lt_compat_r (MySqrt x) 0 eps H1).
rewrite (proj2 (MySqrtNature x)).
apply Rgt_minus.
suff: (Rmax (MySqrt x - eps) 0 < MySqrt x).
move=> H6.
apply Rmult_le_0_lt_compat.
apply (Rmax_r (MySqrt x - eps) 0).
apply (Rmax_r (MySqrt x - eps) 0).
apply H6.
apply H6.
unfold Rmax.
elim (Rle_dec (MySqrt x - eps)).
move=> H6.
elim (proj1 (MySqrtNature x)).
apply.
move=> H7.
apply (Rnot_le_lt (MySqrt x) 0).
move=> H8.
apply (Rle_not_gt (proj1_sig x) 0).
rewrite (proj2 (MySqrtNature x)).
rewrite H7.
right.
apply (Rmult_0_l 0).
apply H5.
move=> H6.
rewrite - {2} (Rplus_0_r (MySqrt x)).
apply (Rplus_lt_compat_l (MySqrt x) (- eps) 0).
apply (Ropp_lt_gt_0_contravar eps H1).
move=> y H6.
apply Rabs_def1.
apply (H2 y).
apply (Rle_lt_trans (proj1_sig y - proj1_sig x) (Rabs (proj1_sig y - proj1_sig x)) ((eps + MySqrt x) * (eps + MySqrt x) - proj1_sig x)).
apply Rle_abs.
apply (Rlt_le_trans (Rabs (proj1_sig y - proj1_sig x)) (Rmin ((eps + MySqrt x) * (eps + MySqrt x) - proj1_sig x) (proj1_sig x - Rmax (MySqrt x - eps) 0 * Rmax (MySqrt x - eps) 0)) ((eps + MySqrt x) * (eps + MySqrt x) - proj1_sig x)).
apply (proj2 H6).
apply Rmin_l.
apply (H3 y).
apply Ropp_lt_cancel.
rewrite Ropp_minus_distr.
rewrite Ropp_minus_distr.
apply (Rle_lt_trans (proj1_sig x - proj1_sig y) (dist (RestrictMet R_met (fun (r : R) => r >= 0)) y x) (proj1_sig x - Rmax (MySqrt x - eps) 0 * Rmax (MySqrt x - eps) 0)).
rewrite (dist_sym (RestrictMet R_met (fun (r : R) => r >= 0)) y x).
apply Rle_abs.
apply (Rlt_le_trans (dist (RestrictMet R_met (fun (r : R) => r >= 0)) y x) (Rmin ((eps + MySqrt x) * (eps + MySqrt x) - proj1_sig x) (proj1_sig x - Rmax (MySqrt x - eps) 0 * Rmax (MySqrt x - eps) 0)) (proj1_sig x - Rmax (MySqrt x - eps) 0 * Rmax (MySqrt x - eps) 0)).
apply (proj2 H6).
apply Rmin_r.
move=> H5.
exists ((eps + MySqrt x) * (eps + MySqrt x) - proj1_sig x).
apply conj.
apply H4.
move=> y H6.
apply Rabs_def1.
apply (H2 y).
apply (Rle_lt_trans (proj1_sig y - proj1_sig x) (Rabs (proj1_sig y - proj1_sig x)) ((eps + MySqrt x) * (eps + MySqrt x) - proj1_sig x)).
apply Rle_abs.
apply (proj2 H6).
suff: (MySqrt x = 0).
move=> H7.
rewrite H7.
rewrite (Rminus_0_r (MySqrt y)).
apply (Rlt_le_trans (- eps) 0 (MySqrt y)).
apply (Ropp_lt_gt_0_contravar eps H1).
apply (Rge_le (MySqrt y) 0 (proj1 (MySqrtNature y))).
apply (MySqrtNature2 x 0).
apply conj.
right.
reflexivity.
rewrite (Rmult_0_l 0).
apply H5.
rewrite (proj2 (MySqrtNature x)).
apply Rgt_minus.
suff: (eps + MySqrt x > MySqrt x).
move=> H4.
apply Rmult_le_0_lt_compat.
apply Rge_le.
apply (proj1 (MySqrtNature x)).
apply Rge_le.
apply (proj1 (MySqrtNature x)).
apply H4.
apply H4.
rewrite - {2} (Rplus_0_l (MySqrt x)).
apply (Rplus_lt_compat_r (MySqrt x) 0 eps H1).
move=> y.
unfold Rmax.
elim (Rle_dec (MySqrt x - eps) 0).
rewrite (Rmult_0_l 0).
unfold Rminus at 3.
rewrite (Rplus_0_l (- proj1_sig x)).
move=> H3 H4.
apply (Rplus_lt_reg_r (MySqrt x) (- eps) (MySqrt y - MySqrt x)).
unfold Rminus.
rewrite Rplus_assoc.
rewrite (Rplus_opp_l (MySqrt x)).
rewrite (Rplus_0_r (MySqrt y)).
rewrite (Rplus_comm (- eps) (MySqrt x)).
apply (Rle_lt_trans (MySqrt x - eps) 0 (MySqrt y) H3).
elim (proj1 (MySqrtNature y)).
apply.
move=> H5.
apply (Rnot_le_lt (MySqrt y) 0).
move=> H6.
apply (Rgt_not_le (proj1_sig y) 0).
apply (Rplus_lt_reg_r (- proj1_sig x)).
rewrite (Rplus_0_l (- proj1_sig x)).
apply H4.
right.
rewrite (proj2 (MySqrtNature y)).
rewrite H5.
apply (Rmult_0_l 0).
move=> H3 H4.
apply (Rplus_lt_reg_r (MySqrt x)).
rewrite Rplus_assoc.
rewrite (Rplus_opp_l (MySqrt x)).
rewrite (Rplus_0_r (MySqrt y)).
rewrite (Rplus_comm (- eps) (MySqrt x)).
apply (Rnot_le_lt (MySqrt y) (MySqrt x + - eps)).
move=> H5.
apply (Rgt_not_le (proj1_sig y) ((MySqrt x - eps) * (MySqrt x - eps))).
apply (Rplus_lt_reg_r (- proj1_sig x)).
apply H4.
rewrite (proj2 (MySqrtNature y)).
apply (Rmult_le_compat (MySqrt y) (MySqrt x - eps) (MySqrt y) (MySqrt x - eps)).
apply Rge_le.
apply (proj1 (MySqrtNature y)).
apply Rge_le.
apply (proj1 (MySqrtNature y)).
apply H5.
apply H5.
move=> y H2.
apply (Rplus_lt_reg_r (MySqrt x)).
rewrite Rplus_assoc.
rewrite (Rplus_opp_l (MySqrt x)).
rewrite (Rplus_0_r (MySqrt y)).
apply (Rnot_le_lt (eps + MySqrt x) (MySqrt y)).
move=> H3.
apply (Rle_not_lt (proj1_sig y) ((eps + MySqrt x) * (eps + MySqrt x))).
rewrite (proj2 (MySqrtNature y)).
apply (Rmult_le_compat (eps + MySqrt x) (MySqrt y) (eps + MySqrt x) (MySqrt y)).
apply (Rle_trans 0 eps (eps + MySqrt x)).
left.
apply H1.
rewrite - {1} (Rplus_0_r eps).
apply (Rplus_le_compat_l eps 0 (MySqrt x)).
apply Rge_le.
apply (proj1 (MySqrtNature x)).
apply (Rle_trans 0 eps (eps + MySqrt x)).
left.
apply H1.
rewrite - {1} (Rplus_0_r eps).
apply (Rplus_le_compat_l eps 0 (MySqrt x)).
apply Rge_le.
apply (proj1 (MySqrtNature x)).
apply H3.
apply H3.
apply (Rplus_lt_reg_r (- proj1_sig x)).
apply H2.
Qed.

Lemma CnRnConvertContinuous : forall (N : nat) (A : Ensemble (Cn N)) (x : Cn N), ContinuousMet (Cn_met N) (Rn_met (N * 2)) (CnRnConvert N) A x.
Proof.
move=> N A x eps H1.
exists eps.
apply conj.
apply H1.
move=> y H2.
unfold dist.
simpl.
unfold Rn_dist.
suff: (Rnminus (N * 2) (CnRnConvert N y) (CnRnConvert N x) = CnRnConvert N (Cnminus N y x)).
move=> H3.
rewrite H3.
rewrite - (CnRnNormRelation N (Cnminus N y x)).
apply (proj2 H2).
reflexivity.
Qed.

Lemma RCnRnConvertContinuous : forall (K : RC) (N : nat) (A : Ensemble (RCn K N)) (x : RCn K N), ContinuousMet (RCn_met K N) (Rn_met (RCnNum K N)) (RCnRnConvert K N) A x.
Proof.
elim.
move=> N A x eps H1.
exists eps.
apply conj.
apply H1.
move=> y H2.
apply (proj2 H2).
apply CnRnConvertContinuous.
Qed.

Lemma CnRnConvertInvContinuous : forall (N : nat) (A : Ensemble (Rn (N * 2))) (x : Rn (N * 2)), ContinuousMet (Rn_met (N * 2)) (Cn_met N) (CnRnConvertInv N) A x.
Proof.
move=> N A x eps H1.
exists eps.
apply conj.
apply H1.
move=> y H2.
unfold dist.
simpl.
unfold Cn_dist.
suff: (CnRnConvertInv N (Rnminus (N * 2) y x) = Cnminus N (CnRnConvertInv N y) (CnRnConvertInv N x)).
move=> H3.
rewrite - H3.
rewrite (CnRnNormRelation N (CnRnConvertInv N (Rnminus (N * 2) y x))).
rewrite (proj2 (CnRnConvertInvRelation N) (Rnminus (N * 2) y x)).
apply (proj2 H2).
apply functional_extensionality.
move=> m.
apply functional_extensionality.
move=> n.
unfold CnRnConvertInv.
unfold Cnminus.
unfold Fnminus.
unfold Fnadd.
unfold Fnopp.
simpl.
unfold Cplus.
unfold Copp.
unfold Fnadd.
unfold Fnopp.
unfold Rnopp.
simpl.
elim (CReorCIm n).
move=> H3.
rewrite H3.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeRe.
reflexivity.
move=> H3.
rewrite H3.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite CmakeIm.
reflexivity.
Qed.

Lemma RCnRnConvertInvContinuous : forall (K : RC) (N : nat) (A : Ensemble (Rn (RCnNum K N))) (x : Rn (RCnNum K N)), ContinuousMet (Rn_met (RCnNum K N)) (RCn_met K N) (RCnRnConvertInv K N) A x.
Proof.
elim.
move=> N A x eps H1.
exists eps.
apply conj.
apply H1.
move=> y H2.
apply (proj2 H2).
apply CnRnConvertInvContinuous.
Qed.

Lemma VectorComponentContinuousRC : forall (K : RC) (N : nat) (m : Count N) (x : RCn K N), ContinuousMet (RCn_met K N) (RC_met K) (fun (y : RCn K N) => y m) (Full_set (RCn K N)) x.
Proof.
move=> K N m x eps H1.
exists eps.
apply conj.
apply H1.
move=> y H2.
apply (Rle_lt_trans (dist (RC_met K) (y m) (x m)) (dist (RCn_met K N) y x) eps).
unfold dist.
simpl.
suff: (RC_dist K (y m) (x m) * RC_dist K (y m) (x m) <= RCn_dist K N y x * RCn_dist K N y x).
move=> H3.
apply (Rnot_lt_le (RCn_dist K N y x) (RC_dist K (y m) (x m))).
move=> H4.
apply (Rlt_not_le (RC_dist K (y m) (x m) * RC_dist K (y m) (x m)) (RCn_dist K N y x * RCn_dist K N y x)).
apply Rmult_le_0_lt_compat.
apply Rge_le.
apply (RCn_dist_pos K).
apply Rge_le.
apply (RCn_dist_pos K).
apply H4.
apply H4.
apply H3.
suff: (forall (K : RC) (r : R), RCRe K (IRRC K r) = r).
move=> H3.
suff: (RC_dist K (y m) (x m) * RC_dist K (y m) (x m) = RCRe K (RCmult K (RCnminus K N y x m) (ConjugateRC K (RCnminus K N y x m)))).
move=> H4.
rewrite H4.
unfold RCn_dist.
rewrite - (proj2 (RCnNormNature K N (RCnminus K N y x))).
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count N) (FiniteSingleton (Count N) m)).
rewrite RCReplus.
rewrite - (Rplus_0_r (RCRe K (RCmult K (RCnminus K N y x m) (ConjugateRC K (RCnminus K N y x m))))).
rewrite MySumF2Singleton.
apply Rplus_le_compat_l.
apply MySumF2Induction.
apply conj.
right.
elim K.
reflexivity.
reflexivity.
move=> cm u H5 H6.
simpl.
rewrite RCReplus.
apply Rplus_le_le_0_compat.
apply H6.
rewrite - (Proposition_4_8_3_RC K (RCnminus K N y x u)).
rewrite (H3 K).
apply Rge_le.
apply Formula_1_3.
move=> u H5.
apply (Full_intro (Count N) u).
rewrite - (Proposition_4_8_3_RC K (RCnminus K N y x m)).
rewrite (H3 K).
reflexivity.
elim.
move=> r.
reflexivity.
move=> r.
apply (CmakeRe r 0).
apply (proj2 H2).
Qed.

Lemma ConjugateRCContinuous : forall (K : RC) (r : RCT K), ContinuousMet (RC_met K) (RC_met K) (ConjugateRC K) (Full_set (RCT K)) r.
Proof.
elim.
move=> r eps H1.
exists eps.
apply conj.
apply H1.
move=> x H2.
apply (proj2 H2).
move=> r eps H1.
exists eps.
apply conj.
apply H1.
move=> x H2.
unfold dist.
simpl.
suff: (Cnorm (Cplus (Conjugate x) (Copp (Conjugate r))) = Cnorm (Cplus x (Copp r))).
move=> H3.
rewrite H3.
apply (proj2 H2).
rewrite CnormDefinition.
rewrite CnormDefinition.
suff: ((exist (fun (r : R) => r >= 0) (Cplus (Conjugate x) (Copp (Conjugate r)) CRe * Cplus (Conjugate x) (Copp (Conjugate r)) CRe + Cplus (Conjugate x) (Copp (Conjugate r)) CIm * Cplus (Conjugate x) (Copp (Conjugate r)) CIm) (CnormSqrtSub (Cplus (Conjugate x) (Copp (Conjugate r))))) = (exist (fun (r : R) => r >= 0) (Cplus x (Copp r) CRe * Cplus x (Copp r) CRe + Cplus x (Copp r) CIm * Cplus x (Copp r) CIm) (CnormSqrtSub (Cplus x (Copp r))))).
move=> H3.
rewrite H3.
reflexivity.
apply sig_map.
simpl.
unfold Conjugate.
unfold Cplus.
unfold Fnadd.
unfold Copp.
unfold Rnopp.
unfold Fnopp.
rewrite (CmakeRe (x CRe) (- x CIm)).
rewrite (CmakeIm (x CRe) (- x CIm)).
rewrite (CmakeRe (r CRe) (- r CIm)).
rewrite (CmakeIm (r CRe) (- r CIm)).
simpl.
rewrite - (Ropp_plus_distr (x CIm) (- r CIm)).
rewrite (Rmult_opp_opp (x CIm + - r CIm) (x CIm + - r CIm)).
reflexivity.
Qed.

Lemma RCnNormContinuous : forall (K : RC) (N : nat) (r : RCn K N), ContinuousMet (RCn_met K N) R_met (RCnNorm K N) (Full_set (RCn K N)) r.
Proof.
elim.
move=> N r.
apply (Theorem_6_7_2 (Rn_met N) (RestrictMet R_met (fun (r : R) => r >= 0)) R_met (fun (x : Rn N) => (exist (fun (r : R) => r >= 0) (RnInnerProduct N x x) (Proposition_4_2_4_1_R N x))) MySqrt (Full_set (Rn N)) (Full_set {r : R | r >= 0}) r (exist (fun (r : R) => r >= 0) (RnInnerProduct N r r) (Proposition_4_2_4_1_R N r)) (MySqrt (exist (fun (r : R) => r >= 0) (RnInnerProduct N r r) (Proposition_4_2_4_1_R N r)))).
move=> x H1.
apply (Full_intro {r : R | r >= 0} x).
suff: (ContinuousMet (Rn_met N) R_met (fun (x : Rn N) => RnInnerProduct N x x) (Full_set (Rn N)) r).
apply.
unfold RnInnerProduct.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
move=> eps H1.
exists 1.
apply conj.
apply Rlt_0_1.
move=> x H2.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (proj2 (dist_refl R_met (CMe RPCM) (CMe RPCM))).
apply H1.
reflexivity.
move=> B b H1 H2 H3 H4.
suff: ((fun (x : Rn N) => MySumF2 (Count N) (FiniteAdd (Count N) B b) RPCM (fun n : Count N => x n * x n)) = (fun (x : Rn N) => MySumF2 (Count N) B RPCM (fun (n : Count N) => x n * x n) + x b * x b)).
move=> H5.
rewrite H5.
apply Theorem_6_6_3_1_R.
apply H4.
apply Theorem_6_6_2_1_R.
apply (VectorComponentContinuousRC RK N b r).
apply (VectorComponentContinuousRC RK N b r).
apply functional_extensionality.
move=> x.
apply MySumF2Add.
apply H3.
apply MySqrtContinuous.
move=> N r.
apply (Theorem_6_7_2 (Cn_met N) (RestrictMet R_met (fun (r : R) => r >= 0)) R_met (fun (x : Cn N) => (exist (fun (r : R) => r >= 0) (CnInnerProduct N x x CRe) (proj1 (Proposition_4_2_4_1_C N x)))) MySqrt (Full_set (Cn N)) (Full_set {r : R | r >= 0}) r (exist (fun (r : R) => r >= 0) (CnInnerProduct N r r CRe) (proj1 (Proposition_4_2_4_1_C N r))) (MySqrt (exist (fun (r : R) => r >= 0) (CnInnerProduct N r r CRe) (proj1 (Proposition_4_2_4_1_C N r))))).
move=> x H1.
apply (Full_intro {r : R | r >= 0} x).
suff: (ContinuousMet (Cn_met N) R_met (fun (x : Cn N) => CnInnerProduct N x x CRe) (Full_set (Cn N)) r).
apply.
unfold CnInnerProduct.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
move=> eps H1.
exists 1.
apply conj.
apply Rlt_0_1.
move=> x H2.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (proj2 (dist_refl R_met (CMe CPCM CRe) (CMe CPCM CRe))).
apply H1.
reflexivity.
move=> B b H1 H2 H3 H4.
suff: ((fun (x : Cn N) => MySumF2 (Count N) (FiniteAdd (Count N) B b) CPCM (fun (n : Count N) => Cmult (x n) (Conjugate (x n))) CRe) = (fun (x : Cn N) => MySumF2 (Count N) B CPCM (fun (n : Count N) => Cmult (x n) (Conjugate (x n))) CRe + Cmult (x b) (Conjugate (x b)) CRe)).
move=> H5.
rewrite H5.
apply Theorem_6_6_3_1_R.
apply H4.
apply (Theorem_6_7_2 (Cn_met N) C_met R_met (fun (x : Cn N) => Cmult (x b) (Conjugate (x b))) (fun (c : C) => c CRe) (Full_set (Cn N)) (Full_set C) r (Cmult (r b) (Conjugate (r b)))).
move=> x H6.
apply (Full_intro C x).
apply Theorem_6_6_2_1_C.
apply (VectorComponentContinuousRC CK N b r).
apply (Theorem_6_7_2 (Cn_met N) C_met C_met (fun (x : Cn N) => x b) (fun (c : C) => Conjugate c) (Full_set (Cn N)) (Full_set C) r (r b)).
move=> x H6.
apply (Full_intro C x).
apply (VectorComponentContinuousRC CK N b r).
apply (ConjugateRCContinuous CK (r b)).
apply (VectorComponentContinuousRC RK 2 CRe).
apply functional_extensionality.
move=> x.
rewrite MySumF2Add.
reflexivity.
apply H3.
apply MySqrtContinuous.
Qed.

Lemma MVmultContinuousRC : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M N) (x : RCn K N), ContinuousMet (RCn_met K N) (RCn_met K M) (MVmult (RCfield K) M N A) (Full_set (RCn K N)) x.
Proof.
move=> K M N A x.
unfold MVmult.
unfold MMatrixToVector.
unfold Mmult.
unfold MVectorToMatrix.
apply (FiniteSetInduction {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
apply conj.
move=> eps H1.
exists 1.
apply conj.
apply Rlt_0_1.
move=> y H2.
rewrite (proj2 (dist_refl (RCn_met K M) (fun (m : {n : nat | (n < M)%nat}) => MySumF2 {n : nat | (n < N)%nat} (FiniteEmpty {n : nat | (n < N)%nat}) (FPCM (RCfield K)) (fun (n : Count N) => Fmul (RCfield K) (A m n) (y n))) (fun (m : {n : nat | (n < M)%nat}) => MySumF2 {n : nat | (n < N)%nat} (FiniteEmpty {n : nat | (n < N)%nat}) (FPCM (RCfield K)) (fun (n : Count N) => Fmul (RCfield K) (A m n) (x n))))).
apply H1.
apply functional_extensionality.
move=> m.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H1 H2 H3 H4.
suff: (ContinuousMet (RCn_met K N) (RCn_met K M) (fun (v : {n : nat | (n < N)%nat} -> FT (RCfield K)) (m : {n : nat | (n < M)%nat}) => Fmul (RCfield K) (A m b) (v b)) (Full_set (RCn K N)) x).
move=> H5 eps H6.
elim (H4 (eps / 2)).
move=> dlt1 H8.
elim (H5 (eps / 2)).
move=> dlt2 H9.
exists (Rmin dlt1 dlt2).
apply conj.
unfold Rmin.
elim (Rle_dec dlt1 dlt2).
move=> H10.
apply (proj1 H8).
move=> H10.
apply (proj1 H9).
move=> y H10.
unfold dist.
simpl.
unfold RCn_dist.
suff: ((RCnminus K M (fun (m : {n : nat | (n < M)%nat}) => MySumF2 {n : nat | (n < N)%nat} (FiniteAdd {n : nat | (n < N)%nat} B b) (FPCM (RCfield K)) (fun (n : Count N) => RCmult K (A m n) (y n))) (fun (m : {n : nat | (n < M)%nat}) => MySumF2 {n : nat | (n < N)%nat} (FiniteAdd {n : nat | (n < N)%nat} B b) (FPCM (RCfield K)) (fun (n : Count N) => RCmult K (A m n) (x n)))) = (RCnplus K M (RCnminus K M (fun (m : {n : nat | (n < M)%nat}) => MySumF2 {n : nat | (n < N)%nat} B (FPCM (RCfield K)) (fun (n : Count N) => RCmult K (A m n) (y n))) (fun (m : {n : nat | (n < M)%nat}) => MySumF2 {n : nat | (n < N)%nat} B (FPCM (RCfield K)) (fun (n : Count N) => RCmult K (A m n) (x n)))) (RCnminus K M (fun (m : Count M) => (Fmul (RCfield K) (A m b) (y b))) (fun (m : Count M) => (Fmul (RCfield K) (A m b) (x b)))))).
move=> H11.
rewrite H11.
apply (Rle_lt_trans (RCnNorm K M (RCnplus K M (RCnminus K M (fun (m : {n : nat | (n < M)%nat}) => MySumF2 {n : nat | (n < N)%nat} B (FPCM (RCfield K)) (fun (n : Count N) => RCmult K (A m n) (y n))) (fun (m : {n : nat | (n < M)%nat}) => MySumF2 {n : nat | (n < N)%nat} B (FPCM (RCfield K)) (fun (n : Count N) => RCmult K (A m n) (x n)))) (RCnminus K M (fun (m : Count M) => Fmul (RCfield K) (A m b) (y b)) (fun (m : Count M) => Fmul (RCfield K) (A m b) (x b))))) ((RCnNorm K M (RCnminus K M (fun (m : {n : nat | (n < M)%nat}) => MySumF2 {n : nat | (n < N)%nat} B (FPCM (RCfield K)) (fun (n : Count N) => RCmult K (A m n) (y n))) (fun (m : {n : nat | (n < M)%nat}) => MySumF2 {n : nat | (n < N)%nat} B (FPCM (RCfield K)) (fun (n : Count N) => RCmult K (A m n) (x n))))) + (RCnNorm K M (RCnminus K M (fun (m : Count M) => Fmul (RCfield K) (A m b) (y b)) (fun (m : Count M) => Fmul (RCfield K) (A m b) (x b))))) eps ).
apply (Proposition_4_4_2_1 K).
rewrite - (eps2 eps).
apply Rplus_lt_compat.
apply (proj2 H8).
apply conj.
apply (proj1 H10).
apply (Rlt_le_trans (dist (RCn_met K N) y x) (Rmin dlt1 dlt2) dlt1 (proj2 H10) (Rmin_l dlt1 dlt2)).
apply (proj2 H9).
apply conj.
apply (proj1 H10).
apply (Rlt_le_trans (dist (RCn_met K N) y x) (Rmin dlt1 dlt2) dlt2 (proj2 H10) (Rmin_r dlt1 dlt2)).
apply functional_extensionality.
move=> m.
unfold RCnminus.
unfold Fnminus.
unfold RCnplus.
unfold Fnadd.
unfold Fnopp.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
suff: (forall (x y z w : RCT K), RCplus K (RCplus K x y) (RCopp K (RCplus K z w)) = RCplus K (RCplus K x (RCopp K z)) (RCplus K y (RCopp K w))).
move=> H11.
apply H11.
move=> r1 r2 r3 r4.
suff: (RCopp K (RCplus K r3 r4) = RCplus K (RCopp K r3) (RCopp K r4)).
move=> H11.
rewrite H11.
rewrite - (RCplus_assoc K (RCplus K r1 r2) (RCopp K r3) (RCopp K r4)).
rewrite (RCplus_assoc K r1 r2 (RCopp K r3)).
rewrite - (RCplus_assoc K (RCplus K r1 (RCopp K r3)) r2 (RCopp K r4)).
rewrite (RCplus_assoc K r1 (RCopp K r3) r2).
rewrite (RCplus_comm K r2 (RCopp K r3)).
reflexivity.
apply (Fopp_add_distr (RCfield K) r3 r4).
apply H3.
apply H3.
apply (eps2_Rgt_R0 eps H6).
apply (eps2_Rgt_R0 eps H6).
suff: ((fun (v : {n : nat | (n < N)%nat} -> FT (RCfield K)) (m : {n : nat | (n < M)%nat}) => Fmul (RCfield K) (A m b) (v b)) = (fun (v : {n : nat | (n < N)%nat} -> FT (RCfield K)) => RCnRnConvertInv K M (RCnRnConvert K M (fun (m : {n : nat | (n < M)%nat}) => Fmul (RCfield K) (A m b) (v b))))).
move=> H5.
rewrite H5.
apply (Theorem_6_7_2 (RCn_met K N) (Rn_met (RCnNum K M)) (RCn_met K M) (fun (v : {n : nat | (n < N)%nat} -> FT (RCfield K)) => RCnRnConvert K M (fun (m : {n : nat | (n < M)%nat}) => Fmul (RCfield K) (A m b) (v b))) (RCnRnConvertInv K M) (Full_set (RCn K N)) (Full_set (Rn (RCnNum K M))) x (RCnRnConvert K M (fun (m : {n : nat | (n < M)%nat}) => Fmul (RCfield K) (A m b) (x b)))).
move=> y H6.
apply (Full_intro (Rn (RCnNum K M)) y).
suff: (forall (K : RC) (A : Matrix (RCfield K) M N) (x : RCn K N), ContinuousMet (RCn_met K N) (Rn_met (RCnNum K M)) (fun (y : Base (RCn_met K N)) => RCnRnConvert K M (fun (m : {n : nat | (n < M)%nat}) => Fmul (RCfield K) (A m b) (y b))) (Full_set (RCn K N)) x).
apply.
elim.
move=> A0 x0.
apply (proj2 (Theorem_6_8_2 (RCn_met RK N) (RCnNum RK M) (fun (y : Base (RCn_met RK N)) => RCnRnConvert RK M (fun (m : {n : nat | (n < M)%nat}) => Fmul (RCfield RK) (A0 m b) (y b))) (Full_set (RCn RK N)) x0)).
move=> m.
apply Theorem_6_6_3_3_R.
apply VectorComponentContinuousRC.
move=> A0 x0.
apply (proj2 (Theorem_6_8_2 (RCn_met CK N) (RCnNum CK M) (fun (y : Base (RCn_met CK N)) => RCnRnConvert CK M (fun (m : {n : nat | (n < M)%nat}) => Fmul (RCfield CK) (A0 m b) (y b))) (Full_set (RCn CK N)) x0)).
move=> m.
unfold RCnRnConvert.
unfold CnRnConvert.
simpl.
elim (CReorCIm (snd (MultConnectInv M 2 m))).
move=> H6.
rewrite H6.
suff: ((fun (r : RCn CK N) => Cmult (A0 (fst (MultConnectInv M 2 m)) b) (r b) CRe) = (fun (r : RCn CK N) => (A0 (fst (MultConnectInv M 2 m)) b CRe * r b CRe - A0 (fst (MultConnectInv M 2 m)) b CIm * r b CIm))).
move=> H7.
rewrite H7.
apply Theorem_6_6_3_1_R.
apply Theorem_6_6_3_3_R.
apply (Theorem_6_7_2 (RCn_met CK N) C_met R_met (fun (r : Base (RCn_met CK N)) => r b) (fun (c : C) => c CRe) (Full_set (RCn CK N)) (Full_set C) x0 (x0 b) (x0 b CRe)).
move=> z H8.
apply (Full_intro C z).
apply VectorComponentContinuousRC.
apply (VectorComponentContinuousRC RK 2 CRe (x0 b)).
apply Theorem_6_6_3_4_R.
apply Theorem_6_6_3_3_R.
apply (Theorem_6_7_2 (RCn_met CK N) C_met R_met (fun (r : Base (RCn_met CK N)) => r b) (fun (c : C) => c CIm) (Full_set (RCn CK N)) (Full_set C) x0 (x0 b) (x0 b CIm)).
move=> z H8.
apply (Full_intro C z).
apply VectorComponentContinuousRC.
apply (VectorComponentContinuousRC RK 2 CIm (x0 b)).
apply functional_extensionality.
move=> n.
apply CmakeRe.
move=> H6.
rewrite H6.
suff: ((fun (r : RCn CK N) => Cmult (A0 (fst (MultConnectInv M 2 m)) b) (r b) CIm) = (fun (r : RCn CK N) => (A0 (fst (MultConnectInv M 2 m)) b CRe * r b CIm + A0 (fst (MultConnectInv M 2 m)) b CIm * r b CRe))).
move=> H7.
rewrite H7.
apply Theorem_6_6_3_1_R.
apply Theorem_6_6_3_3_R.
apply (Theorem_6_7_2 (RCn_met CK N) C_met R_met (fun (r : Base (RCn_met CK N)) => r b) (fun (c : C) => c CIm) (Full_set (RCn CK N)) (Full_set C) x0 (x0 b) (x0 b CIm)).
move=> z H8.
apply (Full_intro C z).
apply VectorComponentContinuousRC.
apply (VectorComponentContinuousRC RK 2 CIm (x0 b)).
apply Theorem_6_6_3_3_R.
apply (Theorem_6_7_2 (RCn_met CK N) C_met R_met (fun (r : Base (RCn_met CK N)) => r b) (fun (c : C) => c CRe) (Full_set (RCn CK N)) (Full_set C) x0 (x0 b) (x0 b CRe)).
move=> z H8.
apply (Full_intro C z).
apply VectorComponentContinuousRC.
apply (VectorComponentContinuousRC RK 2 CRe (x0 b)).
apply functional_extensionality.
move=> n.
apply CmakeIm.
apply RCnRnConvertInvContinuous.
apply functional_extensionality.
move=> r.
rewrite (proj1 (RCnRnConvertInvRelation K M)).
reflexivity.
Qed.

Lemma ContinuousConstantClosedMet : forall (M1 M2 : Metric_Space) (f : Base M1 -> Base M2), (forall (x : Base M1), ContinuousMet M1 M2 f (Full_set (Base M1)) x) -> forall (r2 : Base M2), ClosedSetMet M1 (fun (r1 : Base M1) => f r1 = r2).
Proof.
move=> M1 M2 f H1 r2.
apply (proj2 (Proposition_7_1_1 M1 (fun (r1 : Base M1) => f r1 = r2))).
move=> an a H2 H3.
apply (Proposition_2_3_met M2 (fun (n : nat) => f (an n))).
move=> eps H4.
elim (H1 a eps H4).
move=> dlt H5.
elim (H3 dlt (proj1 H5)).
move=> N H6.
exists N.
move=> n H7.
apply (proj2 H5 (an n)).
apply conj.
apply (Full_intro (Base M1) (an n)).
apply (H6 n H7).
move=> eps H4.
exists O.
move=> n H5.
rewrite (H2 n).
rewrite (proj2 (dist_refl M2 r2 r2)).
apply H4.
reflexivity.
Qed.

Lemma RCTwoNormSig : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M (S N)), {r : R | is_max (fun (l : R) => exists (x : RCn K (S N)), RCnNorm K (S N) x = 1 /\ RCnNorm K M (MVmult (RCfield K) M (S N) A x) = l) r}.
Proof.
move=> K M N A.
apply constructive_definite_description.
apply (proj1 (unique_existence (is_max (fun (l : R) => exists (x : RCn K (S N)), RCnNorm K (S N) x = 1 /\ RCnNorm K M (MVmult (RCfield K) M (S N) A x) = l)))).
apply conj.
elim (Theorem_7_3_2_1 (Rn_met (RCnNum K (S N))) (fun (x : Rn (RCnNum K (S N))) => RCnNorm K M (MVmult (RCfield K) M (S N) A (RCnRnConvertInv K (S N) x))) (fun (x : Rn (RCnNum K (S N))) => RCnNorm K (S N) (RCnRnConvertInv K (S N) x) = 1)).
move=> r H1.
exists r.
apply conj.
elim (proj1 H1).
move=> x H2 y H3.
rewrite H3.
exists (RCnRnConvertInv K (S N) x).
apply conj.
apply H2.
reflexivity.
move=> l H2.
apply (proj2 H1 l).
elim H2.
move=> x H3.
apply (Im_intro (Rn (RCnNum K (S N))) R (fun (y : Rn (RCnNum K (S N))) => RCnNorm K (S N) (RCnRnConvertInv K (S N) y) = 1) (fun (y : Rn (RCnNum K (S N))) => RCnNorm K M (MVmult (RCfield K) M (S N) A (RCnRnConvertInv K (S N) y))) (RCnRnConvert K (S N) x)).
unfold In.
rewrite (proj1 (RCnRnConvertInvRelation K (S N)) x).
apply (proj1 H3).
rewrite (proj1 (RCnRnConvertInvRelation K (S N)) x).
rewrite (proj2 H3).
reflexivity.
apply (Inhabited_intro (Rn (RCnNum K (S N))) (fun (x : Rn (RCnNum K (S N))) => RCnNorm K (S N) (RCnRnConvertInv K (S N) x) = 1) (RCnRnConvert K (S N) (fun (y : Count (S N)) => match excluded_middle_informative (y = exist (fun (m : nat) => (m < S N)%nat) O (le_n_S O N (le_0_n N))) with
  | left _ => RCI K
  | right _ => RCO K
end))).
unfold In.
apply RCnNormNature2.
apply conj.
left.
apply Rlt_0_1.
rewrite (Rmult_1_l 1).
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (m : nat) => (m < S N)%nat) O (le_n_S O N (le_0_n N))))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
rewrite (proj1 (RCnRnConvertInvRelation K (S N))).
elim (excluded_middle_informative (@eq (Count (S N)) (exist (fun (m : nat) => (m < S N)%nat) O (le_n_S O N (le_0_n N))) (exist (fun (m : nat) => (m < S N)%nat) O (le_n_S O N (le_0_n N))))).
move=> H1.
elim K.
apply (Rmult_1_l 1).
simpl.
rewrite (Cmult_1_l (Conjugate CI)).
unfold Conjugate.
rewrite CmakeRe.
apply (CmakeRe 1 0).
elim.
reflexivity.
move=> u.
elim.
move=> u0 H1 H2.
rewrite (proj1 (RCnRnConvertInvRelation K (S N))).
elim (excluded_middle_informative (@eq (Count (S N)) u0 (exist (fun (m : nat) => (m < S N)%nat) O (le_n_S O N (le_0_n N))))).
move=> H3.
elim H1.
rewrite H3.
apply (In_singleton (Count (S N))).
move=> H3.
apply (Fmul_O_l (RCfield K)).
move=> u H1.
apply (Full_intro (Count (S N)) u).
move=> x H1.
apply (Theorem_6_7_2 (Rn_met (RCnNum K (S N))) (RCn_met K (S N)) R_met (RCnRnConvertInv K (S N)) (fun (y : RCn K (S N)) => RCnNorm K M (MVmult (RCfield K) M (S N) A y)) (Full_set (Rn (RCnNum K (S N)))) (Full_set (RCn K (S N))) x (RCnRnConvertInv K (S N) x)).
move=> y H2.
apply (Full_intro (RCn K (S N)) y).
apply RCnRnConvertInvContinuous.
apply (Theorem_6_7_2 (RCn_met K (S N)) (RCn_met K M) R_met (MVmult (RCfield K) M (S N) A) (RCnNorm K M) (Full_set (RCn K (S N))) (Full_set (RCn K M)) (RCnRnConvertInv K (S N) x) (MVmult (RCfield K) M (S N) A (RCnRnConvertInv K (S N) x))).
move=> y H2.
apply (Full_intro (RCn K M) y).
apply MVmultContinuousRC.
apply RCnNormContinuous.
apply Theorem_7_2_2_2.
apply conj.
exists (RnO (RCnNum K (S N))).
exists (1 + 1).
move=> u H1.
unfold In.
unfold NeighborhoodMet.
unfold dist.
simpl.
unfold Rn_dist.
suff: (Rnminus (RCnNum K (S N)) u (RnO (RCnNum K (S N))) = u).
move=> H2.
rewrite H2.
rewrite - (proj2 (RCnRnConvertInvRelation K (S N)) u).
rewrite - (RCnRnNormRelation K (S N) (RCnRnConvertInv K (S N) u)).
rewrite H1.
apply (Rlt_plus_1 1).
apply functional_extensionality.
move=> m.
apply (Rminus_0_r (u m)).
apply (ContinuousConstantClosedMet (Rn_met (RCnNum K (S N))) R_met).
move=> x.
apply (Theorem_6_7_2 (Rn_met (RCnNum K (S N))) (RCn_met K (S N)) R_met (RCnRnConvertInv K (S N)) (RCnNorm K (S N)) (Full_set (Rn (RCnNum K (S N)))) (Full_set (RCn K (S N))) x (RCnRnConvertInv K (S N) x)).
move=> y H1.
apply (Full_intro (RCn K (S N)) y).
apply RCnRnConvertInvContinuous.
apply RCnNormContinuous.
move=> r1 r2 H1 H2.
apply (Rle_antisym r1 r2).
apply (proj2 H2 r1 (proj1 H1)).
apply (proj2 H1 r2 (proj1 H2)).
Qed.

Definition RCTwoNorm (K : RC) (M N : nat) := match N with
  | O => fun (A : Matrix (RCfield K) M O) => 0
  | S n => fun (A : Matrix (RCfield K) M (S n)) => proj1_sig (RCTwoNormSig K M n A)
end.

Definition RCTwoNormNature (K : RC) (M N : nat) (A : Matrix (RCfield K) M (S N)) : is_max (fun (l : R) => exists (x : RCn K (S N)), RCnNorm K (S N) x = 1 /\ RCnNorm K M (MVmult (RCfield K) M (S N) A x) = l) (RCTwoNorm K M (S N) A) := proj2_sig (RCTwoNormSig K M N A).

Lemma RCTwoNormNature2 : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M (S N)) (r : R), is_max (fun (l : R) => exists (x : RCn K (S N)), RCnNorm K (S N) x = 1 /\ RCnNorm K M (MVmult (RCfield K) M (S N) A x) = l) r -> r = (RCTwoNorm K M (S N) A).
Proof.
move=> K M N A r H1.
apply (Rle_antisym r (RCTwoNorm K M (S N) A)).
apply (proj2 (RCTwoNormNature K M N A) r (proj1 H1)).
apply (proj2 H1 (RCTwoNorm K M (S N) A) (proj1 (RCTwoNormNature K M N A))).
Qed.

Definition RCFrobeniusNorm (K : RC) (M N : nat) (A : Matrix (RCfield K) M N) := RCnNorm K (M * N) (fun (m : Count (M * N)) => A (fst (MultConnectInv M N m)) (snd (MultConnectInv M N m))).

Lemma SingularValueRCHNature2Strong : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M) (U : Matrix (RCfield K) (M + N) (M + N)) (V : Matrix (RCfield K) M M) (pi : Count M -> Count M) (sigma : Rn M), (forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) -> UnitaryMatrixRC K (M + N) U -> UnitaryMatrixRC K M V -> Bijective pi -> A = Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun m : {n : nat | (n < M)%nat} => IRRC K (sigma (pi m)))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)) -> SingularValueRCH K M N A = sigma.
Proof.
move=> K M N A U V pi sigma H1 H2 H3 H4 H5.
apply (SingularValueRCHNature2 K M N A (Mmult (RCfield K) (M + N) (M + N) (M + N) U (MBlockH (RCfield K) M N (M + N) (MBlockW (RCfield K) M M N (fun (m n : Count M) => MI (RCfield K) M n (pi m)) (MO (RCfield K) M N)) (MBlockW (RCfield K) N M N (MO (RCfield K) N M) (MI (RCfield K) N)))) (Mmult (RCfield K) M M M V (fun (m n : Count M) => MI (RCfield K) M n (pi m))) sigma).
apply H1.
apply (UnitaryMatrixRCChain K (M + N)).
apply H2.
unfold UnitaryMatrixRC.
rewrite BlockHAdjointMatrixRC.
rewrite BlockWAdjointMatrixRC.
rewrite BlockWAdjointMatrixRC.
rewrite MBlockHWMult.
rewrite MBlockHMult.
rewrite MBlockHMult.
rewrite MBlockWMult.
rewrite MBlockWMult.
rewrite MBlockWMult.
rewrite MBlockWMult.
rewrite Mmult_O_r.
rewrite Mmult_O_r.
rewrite Mmult_O_r.
rewrite Mmult_O_r.
rewrite AdjointMatrixRCO.
rewrite AdjointMatrixRCO.
rewrite AdjointMatrixRCI.
rewrite Mmult_I_r.
rewrite Mmult_I_r.
rewrite Mmult_O_l.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MI at 4.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H6.
suff: (x = y).
move=> H7.
rewrite H7.
unfold Mplus.
unfold MBlockH.
unfold MBlockW.
elim (AddConnectInv M N y).
move=> m.
unfold MO.
rewrite (Fadd_O_r (RCfield K)).
unfold Mmult.
unfold AdjointMatrixRC.
elim H4.
move=> ipi H8.
rewrite (MySumF2Included {n : nat | (n < M)%nat} (FiniteSingleton {n : nat | (n < M)%nat} (ipi m))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (proj2 H8 m).
rewrite (CM_O_r (FPCM (RCfield K))).
unfold MI.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H9.
simpl.
rewrite ConjugateRCI.
apply RCmult_1_l.
elim.
reflexivity.
move=> u.
elim.
move=> u0 H9 H10.
unfold MI.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig (pi u0))).
move=> H11.
elim H9.
suff: (ipi m = u0).
move=> H12.
rewrite H12.
apply (In_singleton {n : nat | (n < M)%nat} u0).
suff: (m = pi u0).
move=> H12.
rewrite H12.
apply (proj1 H8 u0).
apply sig_map.
apply H11.
move=> H11.
apply (Fmul_O_r (RCfield K)).
move=> u H9.
apply (Full_intro {n : nat | (n < M)%nat} u).
move=> m.
unfold MI.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H8.
apply (Fadd_O_l (RCfield K)).
elim.
reflexivity.
apply sig_map.
apply H6.
unfold Mplus.
unfold MBlockH.
unfold MBlockW.
rewrite - {1} (proj2 (AddConnectInvRelation M N) x).
rewrite - {1} (proj2 (AddConnectInvRelation M N) y).
elim (AddConnectInv M N x).
move=> x0.
elim (AddConnectInv M N y).
move=> y0 H6.
unfold Mmult.
rewrite MySumF2O.
apply (Fadd_O_l (RCfield K)).
move=> u H7.
unfold AdjointMatrixRC.
unfold MI.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig (pi u))).
move=> H8.
elim (Nat.eq_dec (proj1_sig y0) (proj1_sig (pi u))).
move=> H9.
elim H6.
rewrite - (proj1 (AddConnectNature M N) x0).
rewrite - (proj1 (AddConnectNature M N) y0).
rewrite H9.
apply H8.
move=> H9.
apply (Fmul_O_r (RCfield K)).
move=> H8.
simpl.
rewrite ConjugateRCO.
apply (Fmul_O_l (RCfield K)).
move=> y0 H6.
apply (RCplus_0_l K).
move=> x0.
elim (AddConnectInv M N y).
move=> y0 H6.
apply (Fadd_O_l (RCfield K)).
move=> y0 H6.
unfold MI.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y0)).
move=> H7.
elim H6.
suff: (x0 = y0).
move=> H8.
rewrite H8.
reflexivity.
apply sig_map.
apply H7.
move=> H7.
apply (Fadd_O_r (RCfield K)).
apply UnitaryMatrixRCChain.
apply H3.
unfold UnitaryMatrixRC.
unfold Mmult.
unfold MI.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H6.
unfold AdjointMatrixRC.
elim H4.
move=> ipi H7.
suff: (x = y).
move=> H8.
rewrite H8.
rewrite (MySumF2Included {n : nat | (n < M)%nat} (FiniteSingleton {n : nat | (n < M)%nat} (ipi y))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (CM_O_r (FPCM (RCfield K))).
rewrite (proj2 H7 y).
elim (Nat.eq_dec (proj1_sig y) (proj1_sig y)).
move=> H9.
rewrite ConjugateRCI.
apply (RCmult_1_l K).
elim.
reflexivity.
move=> u.
elim.
move=> u0 H9 H10.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (pi u0))).
move=> H11.
elim H9.
suff: (y = pi u0).
move=> H12.
rewrite - (proj1 H7 u0).
rewrite - H12.
apply (In_singleton {n : nat | (n < M)%nat} (ipi y)).
apply sig_map.
apply H11.
move=> H11.
apply (Fmul_O_r (RCfield K)).
move=> u H9.
apply (Full_intro {n : nat | (n < M)%nat} u).
apply sig_map.
apply H6.
move=> H6.
unfold AdjointMatrixRC.
apply MySumF2O.
move=> u H7.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (pi u))).
move=> H8.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (pi u))).
move=> H9.
elim H6.
rewrite H9.
apply H8.
move=> H9.
apply (Fmul_O_r (RCfield K)).
move=> H8.
rewrite ConjugateRCO.
apply (Fmul_O_l (RCfield K)).
rewrite H5.
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) M).
rewrite AdjointMatrixRCMult.
rewrite - (Mmult_assoc (RCfield K) (M + N) M M M).
rewrite - (Mmult_assoc (RCfield K) (M + N) (M + N) M M (MBlockH (RCfield K) M N (M + N) (MBlockW (RCfield K) M M N (fun (m n : Count M) => MI (RCfield K) M n (pi m)) (MO (RCfield K) M N)) (MBlockW (RCfield K) N M N (MO (RCfield K) N M) (MI (RCfield K) N)))).
suff: (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (sigma (pi m)))) (MO (RCfield K) N M) = Mmult (RCfield K) (M + N) (M + N) M (MBlockH (RCfield K) M N (M + N) (MBlockW (RCfield K) M M N (fun (m n : Count M) => MI (RCfield K) M n (pi m)) (MO (RCfield K) M N)) (MBlockW (RCfield K) N M N (MO (RCfield K) N M) (MI (RCfield K) N))) (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (sigma m))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M (fun (m n : Count M) => MI (RCfield K) M n (pi m))))).
move=> H6.
rewrite H6.
reflexivity.
unfold AdjointMatrixRC.
rewrite (MBlockHMult (RCfield K) M N M M).
rewrite (Mmult_O_l (RCfield K) N M M).
suff: (Mmult (RCfield K) M M M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (sigma m))) (fun (x y : {n : nat | (n < M)%nat}) => ConjugateRC K (MI (RCfield K) M x (pi y))) = (fun (x y : {n : nat | (n < M)%nat}) => RCmult K (ConjugateRC K (MI (RCfield K) M x (pi y))) (IRRC K (sigma x)))).
move=> H6.
rewrite H6.
unfold MBlockH at 1.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite - {2} (proj2 (AddConnectInvRelation M N) x).
elim (AddConnectInv M N x).
move=> x0.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y)).
move=> H7.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < M + N)%nat} (FiniteSingleton {n : nat | (n < M + N)%nat} (AddConnect M N (inl (pi x0))))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation M N) (inl (pi x0))).
rewrite (proj1 (AddConnectInvRelation M N) (inl x0)).
suff: (x0 = y).
move=> H8.
rewrite H8.
unfold MI.
elim (Nat.eq_dec (proj1_sig (pi y)) (proj1_sig (pi y))).
move=> H9.
simpl.
rewrite ConjugateRCI.
rewrite RCmult_1_l.
rewrite RCmult_1_l.
reflexivity.
elim.
reflexivity.
apply sig_map.
apply H7.
move=> u.
elim.
move=> u0 H8 H9.
unfold MBlockH.
rewrite (proj1 (AddConnectInvRelation M N) (inl x0)).
suff: (u0 <> AddConnect M N (inl (pi x0))).
rewrite - {1} (proj2 (AddConnectInvRelation M N) u0).
rewrite - {2} (proj2 (AddConnectInvRelation M N) u0).
elim (AddConnectInv M N u0).
move=> u1.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation M N) (inl u1)).
move=> H10.
unfold MI.
elim (Nat.eq_dec (proj1_sig u1) (proj1_sig (pi x0))).
move=> H11.
elim H10.
suff: (u1 = pi x0).
move=> H12.
rewrite H12.
reflexivity.
apply sig_map.
apply H11.
move=> H11.
apply Fmul_O_l.
move=> u1 H10.
apply Fmul_O_r.
move=> H10.
apply H8.
rewrite H10.
apply (In_singleton {n : nat | (n < M + N)%nat}).
move=> u H8.
apply (Full_intro {n : nat | (n < M + N)%nat} u).
move=> H7.
unfold Mmult.
rewrite MySumF2O.
reflexivity.
move=> u H8.
unfold MBlockH.
rewrite (proj1 (AddConnectInvRelation M N) (inl x0)).
unfold MBlockW.
elim (AddConnectInv M N u).
move=> u0.
unfold MI.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig (pi x0))).
move=> H9.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig (pi y))).
move=> H10.
elim H7.
suff: (pi x0 = pi y).
move=> H11.
elim H4.
move=> ipi H12.
rewrite - (proj1 H12 x0).
rewrite H11.
rewrite (proj1 H12 y).
reflexivity.
apply sig_map.
rewrite - H9.
apply H10.
move=> H10.
simpl.
rewrite ConjugateRCO.
rewrite RCmult_1_l.
apply (Fmul_O_l (RCfield K)).
move=> H9.
apply (Fmul_O_l (RCfield K)).
move=> m.
apply (Fmul_O_l (RCfield K)).
move=> x0.
unfold Mmult.
rewrite MySumF2O.
reflexivity.
move=> y0 H7.
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation M N) (inr x0)).
elim (AddConnectInv M N y0).
move=> x1.
apply (Fmul_O_l (RCfield K)).
move=> x1.
apply (Fmul_O_r (RCfield K)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < M)%nat} (FiniteSingleton {n : nat | (n < M)%nat} x)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (CM_O_r (FPCM (RCfield K))).
unfold MDiag.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig x)).
move=> H6.
apply (RCmult_comm K).
elim.
reflexivity.
move=> u.
elim.
move=> u0 H6 H7.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig u0)).
move=> H8.
unfold MI.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig (pi y))).
move=> H9.
elim H6.
suff: (x = u0).
move=> H10.
rewrite H10.
apply (In_singleton {n : nat | (n < M)%nat} u0).
apply sig_map.
apply H8.
move=> H9.
simpl.
rewrite ConjugateRCO.
apply (Fmul_O_r (RCfield K)).
move=> H8.
apply (Fmul_O_l (RCfield K)).
move=> u H6.
apply (Full_intro {n : nat | (n < M)%nat} u).
Qed.

Lemma SingularValueRCHTwoNorm : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (S M + N) (S M)), RCTwoNorm K (S M + N) (S M) A = SingularValueRCH K (S M) N A (exist (fun (n : nat) => (n < S M)%nat) O (le_n_S O M (le_0_n M))).
Proof.
move=> K M N A.
rewrite (RCTwoNormNature2 K (S M + N) M A (SingularValueRCH K (S M) N A (exist (fun (n : nat) => (n < S M)%nat) O (le_n_S O M (le_0_n M))))).
reflexivity.
apply conj.
elim (proj1 (SingularValueRCHMaxNature K (S M) N A (exist (fun (n : nat) => (n < S M)%nat) O (le_n_S 0 M (le_0_n M))))).
move=> V.
elim.
move=> H1.
elim.
move=> H2 H3.
elim (proj1 (proj2 H3)).
move=> x H4.
exists x.
apply conj.
apply (proj1 (proj2 H4)).
apply (proj2 (proj2 H4)).
move=> x H1.
elim (proj1 (SingularValueRCHMinNature K (S M) N A (exist (fun (n : nat) => (n < S M)%nat) O (le_n_S 0 M (le_0_n M))))).
move=> W.
elim.
move=> H2.
elim.
move=> H3 H4.
apply (proj2 (proj2 H4) x).
elim H1.
move=> y H5.
exists y.
apply conj.
rewrite (proj1 (Proposition_5_9_1_3 (RCfield K) (FnVS (RCfield K) (S M)) W H2 (FnVSFiniteDimension (RCfield K) (S M)) H3)).
apply (Full_intro (RCn K (S M)) y).
elim (FnVSDimension (RCfield K) (S M)).
move=> H6 H7.
suff: (FnVSFiniteDimension (RCfield K) (S M) = H6).
move=> H8.
rewrite H8.
rewrite H7.
rewrite (proj1 H4).
reflexivity.
apply proof_irrelevance.
apply H5.
Qed.

Lemma SingularValueRCHApproximateTwoNorm : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M) (U : Matrix (RCfield K) (M + N) (M + N)) (V : Matrix (RCfield K) M M), UnitaryMatrixRC K (M + N) U -> UnitaryMatrixRC K M V -> A = Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun m : {n : nat | (n < M)%nat} => IRRC K (SingularValueRCH K M N A m))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)) -> forall (k : Count M), RCTwoNorm K (M + N) M (Mplus (RCfield K) (M + N) M A (Mopp (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun m : {n : nat | (n < M)%nat} => match excluded_middle_informative (proj1_sig m < proj1_sig k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right _ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))))) = SingularValueRCH K M N A k.
Proof.
move=> K.
elim.
move=> N A U V H1 H2 H3 k.
elim (le_not_lt O (proj1_sig k) (le_0_n (proj1_sig k)) (proj2_sig k)).
move=> M H1 N A U V H2 H3 H4 k.
rewrite SingularValueRCHTwoNorm.
suff: (exists (pi : Count (S M) -> Count (S M)), Bijective pi /\ forall (m : Count (S M)), (((proj1_sig m < proj1_sig k)%nat -> (proj1_sig (pi m) + proj1_sig k >= S M)%nat) /\ ((proj1_sig m >= proj1_sig k)%nat -> (proj1_sig (pi m) + proj1_sig k = proj1_sig m)%nat))).
elim.
move=> pi H5.
rewrite (SingularValueRCHNature2Strong K (S M) N (Mplus (RCfield K) (S M + N) (S M) A (Mopp (RCfield K) (S M + N) (S M) (Mmult (RCfield K) (S M + N) (S M + N) (S M) U (Mmult (RCfield K) (S M + N) (S M) (S M) (MBlockH (RCfield K) (S M) N (S M) (MDiag (RCfield K) (S M) (fun (m : {n : nat | (n < S M)%nat}) => match excluded_middle_informative (proj1_sig m < proj1_sig k)%nat with
  | left _ => IRRC K (SingularValueRCH K (S M) N A m)
  | right _ => RCO K
end)) (MO (RCfield K) N (S M))) (AdjointMatrixRC K (S M) (S M) V))))) U V pi (fun (m : {n : nat | (n < S M)%nat}) => match excluded_middle_informative (proj1_sig m + proj1_sig k < S M)%nat with
  | left H => SingularValueRCH K (S M) N A (exist (fun (n : nat) => (n < S M)%nat) (proj1_sig m + proj1_sig k)%nat H)
  | right _ => 0
end)).
simpl.
elim (excluded_middle_informative (proj1_sig k < S M)%nat).
move=> H6.
suff: ((exist (fun (n : nat) => (n < S M)%nat) (proj1_sig k) H6) = k).
move=> H7.
rewrite H7.
reflexivity.
apply sig_map.
reflexivity.
move=> H6.
elim (H6 (proj2_sig k)).
apply conj.
move=> m.
elim (excluded_middle_informative (proj1_sig m + proj1_sig k < S M)%nat).
move=> H6.
apply (proj1 (SingularValueRCHNature K (S M) N A)).
move=> H6.
right.
reflexivity.
move=> m1 m2 H6.
elim (excluded_middle_informative (proj1_sig m1 + proj1_sig k < S M)%nat).
move=> H7.
elim (excluded_middle_informative (proj1_sig m2 + proj1_sig k < S M)%nat).
move=> H8.
apply (proj1 (proj2 (SingularValueRCHNature K (S M) N A))).
apply (plus_le_compat_r (proj1_sig m1) (proj1_sig m2) (proj1_sig k) H6).
move=> H8.
apply (proj1 (SingularValueRCHNature K (S M) N A)).
move=> H7.
elim (excluded_middle_informative (proj1_sig m2 + proj1_sig k < S M)%nat).
move=> H8.
elim H7.
apply (le_trans (S (proj1_sig m1 + proj1_sig k)) (S (proj1_sig m2 + proj1_sig k)) (S M)).
apply le_n_S.
apply (plus_le_compat_r (proj1_sig m1) (proj1_sig m2) (proj1_sig k) H6).
apply H8.
move=> H8.
right.
reflexivity.
apply H2.
apply H3.
apply (proj1 H5).
suff: (A = Mplus (RCfield K) (S M + N) (S M) (Mmult (RCfield K) (S M + N) (S M + N) (S M) U (Mmult (RCfield K) (S M + N) (S M) (S M) (MBlockH (RCfield K) (S M) N (S M) (MDiag (RCfield K) (S M) (fun (m : {n : nat | (n < S M)%nat}) => IRRC K match excluded_middle_informative (proj1_sig (pi m) + proj1_sig k < S M)%nat with
  | left H => SingularValueRCH K (S M) N A (exist (fun (n : nat) => (n < S M)%nat) (proj1_sig (pi m) + proj1_sig k)%nat H)
  | right _ => 0
end)) (MO (RCfield K) N (S M))) (AdjointMatrixRC K (S M) (S M) V))) (Mmult (RCfield K) (S M + N) (S M + N) (S M) U (Mmult (RCfield K) (S M + N) (S M) (S M) (MBlockH (RCfield K) (S M) N (S M) (MDiag (RCfield K) (S M) (fun (m : {n : nat | (n < S M)%nat}) => match excluded_middle_informative (proj1_sig m < proj1_sig k)%nat with
  | left _ => IRRC K (SingularValueRCH K (S M) N A m)
  | right _ => RCO K
end)) (MO (RCfield K) N (S M))) (AdjointMatrixRC K (S M) (S M) V)))).
move=> H6.
rewrite {1} H6.
rewrite Mplus_assoc.
rewrite Mplus_opp_r.
rewrite Mplus_comm.
apply Mplus_O_l.
rewrite H4.
rewrite - Mmult_plus_distr_l.
rewrite - Mmult_plus_distr_r.
suff: (MBlockH (RCfield K) (S M) N (S M) (MDiag (RCfield K) (S M) (fun (m : {n : nat | (n < S M)%nat}) => IRRC K (SingularValueRCH K (S M) N A m))) (MO (RCfield K) N (S M)) = Mplus (RCfield K) (S M + N) (S M) (MBlockH (RCfield K) (S M) N (S M) (MDiag (RCfield K) (S M) (fun (m : {n : nat | (n < S M)%nat}) => IRRC K match excluded_middle_informative (proj1_sig (pi m) + proj1_sig k < S M)%nat with
  | left H => SingularValueRCH K (S M) N (Mmult (RCfield K) (S M + N) (S M + N) (S M) U (Mmult (RCfield K) (S M + N) (S M) (S M) (MBlockH (RCfield K) (S M) N (S M) (MDiag (RCfield K) (S M) (fun m0 : {n : nat | (n < S M)%nat} => IRRC K (SingularValueRCH K (S M) N A m0))) (MO (RCfield K) N (S M))) (AdjointMatrixRC K (S M) (S M) V))) (exist (fun n : nat => (n < S M)%nat) (proj1_sig (pi m) + proj1_sig k)%nat H)
  | right _ => 0
end)) (MO (RCfield K) N (S M))) (MBlockH (RCfield K) (S M) N (S M) (MDiag (RCfield K) (S M) (fun (m : {n : nat | (n < S M)%nat}) => match excluded_middle_informative (proj1_sig m < proj1_sig k)%nat with
  | left _ => IRRC K (SingularValueRCH K (S M) N (Mmult (RCfield K) (S M + N) (S M + N) (S M) U (Mmult (RCfield K) (S M + N) (S M) (S M) (MBlockH (RCfield K) (S M) N (S M) (MDiag (RCfield K) (S M) (fun m0 : {n0 : nat | (n0 < S M)%nat} => IRRC K (SingularValueRCH K (S M) N A m0))) (MO (RCfield K) N (S M))) (AdjointMatrixRC K (S M) (S M) V))) m)
  | right _ => RCO K
end)) (MO (RCfield K) N (S M)))).
move=> H6.
rewrite - H6.
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mplus.
unfold MBlockH.
elim (AddConnectInv (S M) N x).
move=> x0.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y)).
move=> H6.
elim (excluded_middle_informative (proj1_sig (pi x0) + proj1_sig k < S M)%nat).
move=> H7.
elim (excluded_middle_informative (proj1_sig x0 < proj1_sig k)%nat).
move=> H8.
elim (le_not_lt (S M) (proj1_sig (pi x0) + proj1_sig k) (proj1 (proj2 H5 x0) H8) H7).
move=> H8.
suff: ((exist (fun (n : nat) => (n < S M)%nat) (proj1_sig (pi x0) + proj1_sig k)%nat H7) = x0).
move=> H9.
rewrite Fadd_comm.
rewrite Fadd_O_l.
rewrite H9.
rewrite {1} H4.
reflexivity.
apply sig_map.
apply (proj2 (proj2 H5 x0)).
elim (le_or_lt (proj1_sig k) (proj1_sig x0)).
move=> H9.
apply H9.
move=> H9.
elim (H8 H9).
move=> H7.
elim (excluded_middle_informative (proj1_sig x0 < proj1_sig k)%nat).
move=> H8.
suff: (IRRC K 0 = RCO K).
move=> H9.
rewrite H9.
rewrite Fadd_O_l.
rewrite {1} H4.
reflexivity.
elim K.
reflexivity.
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H9.
rewrite H9.
apply (CmakeRe 0 0).
move=> H9.
rewrite H9.
apply (CmakeIm 0 0).
move=> H8.
elim H7.
rewrite (proj2 (proj2 H5 x0)).
apply (proj2_sig x0).
elim (le_or_lt (proj1_sig k) (proj1_sig x0)).
apply.
move=> H9.
elim (H8 H9).
move=> H6.
rewrite Fadd_O_l.
reflexivity.
move=> y0.
simpl.
rewrite RCplus_0_l.
reflexivity.
suff: (forall (m : Count (S M)), (proj1_sig m < proj1_sig k)%nat -> (proj1_sig m + S M - proj1_sig k < S M)%nat).
move=> H5.
suff: (forall (m : Count (S M)), ~ (proj1_sig m < proj1_sig k)%nat -> (proj1_sig m - proj1_sig k < S M)%nat).
move=> H6.
exists (fun (m : Count (S M)) => match excluded_middle_informative (proj1_sig m < proj1_sig k)%nat with
  | left H => exist (fun (n : nat) => (n < S M)%nat) (proj1_sig m + S M - proj1_sig k)%nat (H5 m H)
  | right H => exist (fun (n : nat) => (n < S M)%nat) (proj1_sig m - proj1_sig k)%nat (H6 m H)
end).
apply conj.
suff: (forall (m : Count (S M)), (proj1_sig m < S M - proj1_sig k)%nat -> (proj1_sig m + proj1_sig k < S M)%nat).
move=> H7.
suff: (forall (m : Count (S M)), ~ (proj1_sig m < S M - proj1_sig k)%nat -> (proj1_sig m + proj1_sig k - S M < S M)%nat).
move=> H8.
exists (fun (m : Count (S M)) => match excluded_middle_informative (proj1_sig m < S M - proj1_sig k)%nat with
  | left H => exist (fun (n : nat) => (n < S M)%nat) (proj1_sig m + proj1_sig k)%nat (H7 m H)
  | right H => exist (fun (n : nat) => (n < S M)%nat) (proj1_sig m + proj1_sig k - S M)%nat (H8 m H)
end).
apply conj.
move=> x.
elim (excluded_middle_informative (proj1_sig x < proj1_sig k)%nat).
move=> H9.
unfold proj1_sig at 1.
elim (excluded_middle_informative (proj1_sig x + S M - proj1_sig k < S M - proj1_sig k)%nat).
move=> H10.
elim (le_not_lt (S M - proj1_sig k) (proj1_sig x + S M - proj1_sig k)).
apply (plus_le_reg_l (S M - proj1_sig k) (proj1_sig x + S M - proj1_sig k) (proj1_sig k)).
rewrite (le_plus_minus_r (proj1_sig k) (S M)).
rewrite (le_plus_minus_r (proj1_sig k) (proj1_sig x + S M)).
apply (le_plus_r (proj1_sig x) (S M)).
apply (le_trans (proj1_sig k) (S M) (proj1_sig x + S M) (lt_le_weak (proj1_sig k) (S M) (proj2_sig k)) (le_plus_r (proj1_sig x) (S M))).
apply (lt_le_weak (proj1_sig k) (S M) (proj2_sig k)).
apply H10.
move=> H10.
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig x + S M - proj1_sig k) (proj1_sig k)).
rewrite (le_plus_minus_r (proj1_sig k) (proj1_sig x + S M)).
rewrite (plus_comm (proj1_sig x) (S M)).
apply (minus_plus (S M) (proj1_sig x)).
apply (le_trans (proj1_sig k) (S M) (proj1_sig x + S M) (lt_le_weak (proj1_sig k) (S M) (proj2_sig k)) (le_plus_r (proj1_sig x) (S M))).
move=> H9.
unfold proj1_sig at 1.
elim (excluded_middle_informative (proj1_sig x - proj1_sig k < S M - proj1_sig k)%nat).
move=> H10.
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig x - proj1_sig k) (proj1_sig k)).
apply (le_plus_minus_r (proj1_sig k) (proj1_sig x)).
elim (le_or_lt (proj1_sig k) (proj1_sig x)).
apply.
move=> H11.
elim (H9 H11).
elim.
apply (plus_lt_reg_l (proj1_sig x - proj1_sig k) (S M - proj1_sig k) (proj1_sig k)).
rewrite (le_plus_minus_r (proj1_sig k) (S M)).
rewrite (le_plus_minus_r (proj1_sig k) (proj1_sig x)).
apply (proj2_sig x).
elim (le_or_lt (proj1_sig k) (proj1_sig x)).
apply.
move=> H10.
elim (H9 H10).
apply (lt_le_weak (proj1_sig k) (S M) (proj2_sig k)).
move=> y.
elim (excluded_middle_informative (proj1_sig y < S M - proj1_sig k)%nat).
move=> H9.
unfold proj1_sig at 1.
elim (excluded_middle_informative (proj1_sig y + proj1_sig k < proj1_sig k)%nat).
move=> H10.
elim (le_not_lt (proj1_sig k) (proj1_sig y + proj1_sig k) (le_plus_r (proj1_sig y) (proj1_sig k)) H10).
move=> H10.
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig y) (proj1_sig k)).
apply (minus_plus (proj1_sig k) (proj1_sig y)).
move=> H9.
unfold proj1_sig at 1.
elim (excluded_middle_informative (proj1_sig y + proj1_sig k - S M < proj1_sig k)%nat).
move=> H10.
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig y + proj1_sig k - S M) (S M)).
rewrite (le_plus_minus_r (S M) (proj1_sig y + proj1_sig k)).
rewrite (plus_comm (proj1_sig y) (proj1_sig k)).
apply (minus_plus (proj1_sig k) (proj1_sig y)).
elim (le_or_lt (S M - proj1_sig k) (proj1_sig y)).
move=> H11.
rewrite {1} (le_plus_minus (proj1_sig k) (S M)).
rewrite (plus_comm (proj1_sig k) (S M - proj1_sig k)).
apply (plus_le_compat_r (S M - proj1_sig k) (proj1_sig y) (proj1_sig k) H11).
apply (lt_le_weak (proj1_sig k) (S M) (proj2_sig k)).
move=> H11.
elim (H9 H11).
elim.
apply (plus_lt_reg_l (proj1_sig y + proj1_sig k - S M) (proj1_sig k) (S M)).
rewrite (le_plus_minus_r (S M) (proj1_sig y + proj1_sig k)).
apply (plus_lt_compat_r (proj1_sig y) (S M) (proj1_sig k) (proj2_sig y)).
elim (le_or_lt (S M - proj1_sig k) (proj1_sig y)).
move=> H10.
rewrite - {1} (le_plus_minus_r (proj1_sig k) (S M)).
rewrite (plus_comm (proj1_sig y) (proj1_sig k)).
apply (plus_le_compat_l (S M - proj1_sig k) (proj1_sig y) (proj1_sig k) H10).
apply (lt_le_weak (proj1_sig k) (S M) (proj2_sig k)).
move=> H10.
elim (H9 H10).
move=> m H8.
apply (plus_lt_reg_l (proj1_sig m + proj1_sig k - S M) (S M) (S M)).
rewrite (le_plus_minus_r (S M) (proj1_sig m + proj1_sig k)).
apply (plus_lt_compat (proj1_sig m) (S M) (proj1_sig k) (S M) (proj2_sig m) (proj2_sig k)).
elim (le_or_lt (S M - proj1_sig k) (proj1_sig m)).
move=> H9.
rewrite {1} (le_plus_minus (proj1_sig k) (S M)).
rewrite (plus_comm (proj1_sig m) (proj1_sig k)).
apply (plus_le_compat_l (S M - proj1_sig k) (proj1_sig m) (proj1_sig k) H9).
apply (lt_le_weak (proj1_sig k) (S M) (proj2_sig k)).
move=> H9.
elim (H8 H9).
move=> m H7.
rewrite - {3} (le_plus_minus_r (proj1_sig k) (S M)).
rewrite (plus_comm (proj1_sig m) (proj1_sig k)).
apply (plus_lt_compat_l (proj1_sig m) (S M - proj1_sig k) (proj1_sig k) H7).
apply (lt_le_weak (proj1_sig k) (S M) (proj2_sig k)).
move=> m.
apply conj.
move=> H7.
elim (excluded_middle_informative (proj1_sig m < proj1_sig k)%nat).
move=> H8.
simpl.
rewrite (plus_comm (proj1_sig m + S M - proj1_sig k) (proj1_sig k)).
rewrite (le_plus_minus_r (proj1_sig k) (proj1_sig m + S M)).
apply (le_plus_r (proj1_sig m) (S M)).
apply (le_trans (proj1_sig k) (S M) (proj1_sig m + S M) (lt_le_weak (proj1_sig k) (S M) (proj2_sig k)) (le_plus_r (proj1_sig m) (S M))).
move=> H8.
elim (H8 H7).
move=> H7.
elim (excluded_middle_informative (proj1_sig m < proj1_sig k)%nat).
move=> H8.
elim (le_not_lt (proj1_sig k) (proj1_sig m) H7 H8).
move=> H8.
simpl.
rewrite (plus_comm (proj1_sig m - proj1_sig k) (proj1_sig k)).
apply (le_plus_minus_r (proj1_sig k) (proj1_sig m)).
apply H7.
move=> m H6.
apply (le_trans (S (proj1_sig m - proj1_sig k)) (S (proj1_sig m)) (S M)).
apply le_n_S.
rewrite {2} (le_plus_minus (proj1_sig k) (proj1_sig m)).
apply le_plus_r.
elim (le_or_lt (proj1_sig k) (proj1_sig m)).
apply.
move=> H7.
elim (H6 H7).
apply (proj2_sig m).
move=> m H5.
apply (plus_lt_reg_l (proj1_sig m + S M - proj1_sig k) (S M) (proj1_sig k)).
rewrite (le_plus_minus_r (proj1_sig k) (proj1_sig m + S M)).
apply (plus_lt_compat_r (proj1_sig m) (proj1_sig k) (S M) H5).
apply (le_trans (proj1_sig k) (S M) (proj1_sig m + S M) (lt_le_weak (proj1_sig k) (S M) (proj2_sig k)) (le_plus_r (proj1_sig m) (S M))).
Qed.

Lemma SingularValueRCHBestApproximateTwoNorm : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M) (k : Count M), is_min (fun (r : R) => exists (B : Matrix (RCfield K) (M + N) M), (Rank (RCfield K) (M + N) M B <= proj1_sig k)%nat /\ RCTwoNorm K (M + N) M (Mplus (RCfield K) (M + N) M A (Mopp (RCfield K) (M + N) M B)) = r) (SingularValueRCH K M N A k).
Proof.
move=> K M N A k.
apply conj.
elim (proj2 (proj2 (SingularValueRCHNature K M N A))).
move=> U.
elim.
move=> V H1.
exists (Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < proj1_sig k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right_ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))).
apply conj.
apply (le_trans (Rank (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < proj1_sig k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right_ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)))) (Rank (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < proj1_sig k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right_ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))) (proj1_sig k)).
apply (RankMultLeL (RCfield K)).
apply (le_trans (Rank (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < proj1_sig k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right_ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))) (Rank (RCfield K) (M + N) M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < proj1_sig k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right_ => RCO K
end)) (MO (RCfield K) N M))) (proj1_sig k)).
apply (RankMultLeR (RCfield K)).
suff: (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < proj1_sig k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right_ => RCO K
end)) (MO (RCfield K) N M) = Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < proj1_sig k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right_ => RCO K
end)) (MO (RCfield K) N M)) (RankNormalForm (RCfield K) M M (proj1_sig k))).
move=> H2.
rewrite H2.
rewrite - {7} (RankNormalFormRank (RCfield K) M M (proj1_sig k)).
apply (RankMultLeL (RCfield K)).
apply (lt_le_weak (proj1_sig k) M (proj2_sig k)).
apply (lt_le_weak (proj1_sig k) M (proj2_sig k)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < M)%nat} (FiniteSingleton {n : nat | (n < M)%nat} y) (exist (Finite (Count M)) (Full_set {n : nat | (n < M)%nat}) (CountFinite M))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
unfold MBlockH.
elim (AddConnectInv M N x).
move=> x0.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y)).
move=> H2.
elim (excluded_middle_informative (proj1_sig x0 < proj1_sig k)%nat).
move=> H3.
unfold RankNormalForm.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig y)).
move=> H4.
elim (excluded_middle_informative (proj1_sig y < proj1_sig k)%nat).
move=> H5.
rewrite (Fmul_I_r (RCfield K)).
reflexivity.
move=> H5.
elim H5.
rewrite - H2.
apply H3.
elim.
reflexivity.
move=> H3.
rewrite (Fmul_O_l (RCfield K)).
reflexivity.
move=> H2.
rewrite (Fmul_O_l (RCfield K)).
reflexivity.
move=> H2.
unfold MO.
rewrite (Fmul_O_l (RCfield K)).
reflexivity.
move=> u.
elim.
move=> u0 H2 H3.
unfold RankNormalForm.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig y)).
move=> H4.
elim H2.
suff: (u0 = y).
move=> H5.
rewrite H5.
apply (In_singleton {n : nat | (n < M)%nat} y).
apply sig_map.
apply H4.
move=> H4.
apply (Fmul_O_r (RCfield K)).
move=> u H2.
apply (Full_intro {n : nat | (n < M)%nat} u).
apply (SingularValueRCHApproximateTwoNorm K M N A U V (proj1 H1) (proj1 (proj2 H1)) (proj2 (proj2 H1)) k).
move=> r.
elim.
move=> B H1.
elim (proj2 (proj2 (SingularValueRCHNature K M N A))).
move=> U.
elim.
move=> V H2.
suff: (forall (m : Count (S (proj1_sig k))), (proj1_sig m < M)%nat).
move=> H3.
suff: (exists (v : RCn K M), RCnNorm K M v = 1 /\ Intersection (RCn K M) (fun (x : RCn K M) => MVmult (RCfield K) (M + N) M B x = RCnO K (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig k))) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H3 m)))) v).
elim.
move=> v H4.
apply (Rge_trans r (RCnNorm K (M + N) (MVmult (RCfield K) (M + N) M A v)) (SingularValueRCH K M N A k)).
rewrite - (proj2 H1).
suff: (MVmult (RCfield K) (M + N) M A v = MVmult (RCfield K) (M + N) M (Mplus (RCfield K) (M + N) M A (Mopp (RCfield K) (M + N) M B)) v).
move=> H5.
rewrite H5.
suff: (forall (m n : nat) (X : Matrix (RCfield K) m n) (v : RCn K n), RCnNorm K n v = 1 -> RCTwoNorm K m n X >= RCnNorm K m (MVmult (RCfield K) m n X v)).
move=> H6.
apply (H6 (M + N)%nat M).
apply (proj1 H4).
move=> m.
elim.
move=> X w H6.
right.
unfold RCTwoNorm.
rewrite (RCnNormNature2 K m (MVmult (RCfield K) m 0 X w) 0).
reflexivity.
apply conj.
right.
reflexivity.
unfold RCnInnerProduct.
rewrite MySumF2O.
rewrite Rmult_0_l.
elim K.
reflexivity.
reflexivity.
move=> u H7.
unfold MVmult.
unfold MMatrixToVector.
unfold Mmult.
rewrite MySumF2O.
apply (Fmul_O_l (RCfield K)).
move=> u0.
elim (le_not_lt O (proj1_sig u0) (le_0_n (proj1_sig u0)) (proj2_sig u0)).
move=> n H6 X w H7.
apply Rle_ge.
apply (proj2 (RCTwoNormNature K m n X)).
exists w.
apply conj.
apply H7.
reflexivity.
unfold MVmult.
rewrite Mmult_plus_distr_r.
suff: (Mmult (RCfield K) (M + N) M 1 (Mopp (RCfield K) (M + N) M B) (MVectorToMatrix (RCfield K) M v) = MO (RCfield K) (M + N) 1).
move=> H5.
rewrite H5.
rewrite Mplus_comm.
rewrite Mplus_O_l.
reflexivity.
elim (proj2 H4).
move=> w H5 H6.
suff: (MO (RCfield K) (M + N) 1 = Mopp (RCfield K) (M + N) 1 (MVectorToMatrix (RCfield K) (M + N) (MVmult (RCfield K) (M + N) M B w))).
move=> H7.
rewrite H7.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MVmult.
unfold Mmult.
unfold Mopp.
rewrite (proj2 (MVectorMatrixRelation (RCfield K) (M + N))).
apply (FiniteSetInduction {n : nat | (n < M)%nat} (exist (Finite (Count M)) (Full_set {n : nat | (n < M)%nat}) (CountFinite M))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
suff: (RCopp K (RCO K) = RCO K).
move=> H8.
rewrite H8.
reflexivity.
apply (Fopp_O (RCfield K)).
move=> C c H8 H9 H10 H11.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite Fopp_add_distr.
rewrite H11.
rewrite Fopp_mul_distr_l.
reflexivity.
apply H10.
apply H10.
rewrite H5.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MVectorToMatrix.
simpl.
unfold RCnO.
simpl.
suff: (RCopp K (RCO K) = RCO K).
move=> H7.
rewrite H7.
reflexivity.
apply (Fopp_O (RCfield K)).
suff: (RCnNorm K M v = 1).
elim (proj2 H4).
move=> v0.
rewrite FiniteSpanVS.
move=> H5 H6 H7.
elim H6.
move=> x H8.
suff: (v0 = MVmult (RCfield K) M M V (fun (m : Count M) => match excluded_middle_informative (proj1_sig m < S (proj1_sig k))%nat with
  | left H => x (exist (fun (l : nat) => (l < S (proj1_sig k))%nat) (proj1_sig m) H)
  | right _ => RCO K
end)).
move=> H9.
suff: (RCnNorm K (S (proj1_sig k)) x = 1).
move=> H10.
rewrite {1} (proj2 (proj2 H2)).
rewrite H9.
unfold MVmult.
rewrite (proj2 (MVectorMatrixRelation (RCfield K) M)).
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) M 1 U).
rewrite (Mmult_assoc (RCfield K) (M + N) M M 1).
rewrite - (Mmult_assoc (RCfield K) M M M 1).
rewrite (proj1 (proj2 H2)).
rewrite Mmult_I_l.
suff: (forall (a b : R), a >= 0 -> b >= 0 -> a * a >= b * b -> a >= b).
move=> H11.
apply H11.
apply RCnNormNature.
apply (proj1 (SingularValueRCHNature K M N A) k).
rewrite - (proj2 (RCnNormNature K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) (M + N) 1 U (Mmult (RCfield K) (M + N) M 1 (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))) (MO (RCfield K) N M)) (MVectorToMatrix (RCfield K) M (fun m : Count M => match excluded_middle_informative (proj1_sig m < S (proj1_sig k))%nat with
  | left H => x (exist (fun (l : nat) => (l < S (proj1_sig k))%nat) (proj1_sig m) H)
  | right _ => RCO K
end))))))).
suff: (forall (X : Matrix (RCfield K) (M + N) 1), RCnInnerProduct K (M + N) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) (M + N) 1 U X)) (MMatrixToVector (RCfield K) (M + N) (Mmult (RCfield K) (M + N) (M + N) 1 U X)) = RCnInnerProduct K (M + N) (MMatrixToVector (RCfield K) (M + N) X) (MMatrixToVector (RCfield K) (M + N) X)).
move=> H12.
rewrite H12.
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count (M + N)) (FiniteIntersection (Count (M + N)) (exist (Finite (Count (M + N))) (Full_set (Count (M + N))) (CountFinite (M + N))) (fun (n : Count (M + N)) => (proj1_sig n < S (proj1_sig k))%nat))).
suff: (forall (n : Count (S (proj1_sig k))), (proj1_sig n < M + N)%nat).
move=> H13.
suff: (FiniteIntersection (Count (M + N)) (exist (Finite (Count (M + N))) (Full_set (Count (M + N))) (CountFinite (M + N))) (fun (n : Count (M + N)) => (proj1_sig n < S (proj1_sig k))%nat) = FiniteIm (Count (S (proj1_sig k))) (Count (M + N)) (fun (m : Count (S (proj1_sig k))) => exist (fun (n : nat) => (n < M + N)%nat) (proj1_sig m) (H13 m)) (exist (Finite (Count (S (proj1_sig k)))) (Full_set (Count (S (proj1_sig k)))) (CountFinite (S (proj1_sig k))))).
move=> H14.
rewrite H14.
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count (M + N)) (FiniteIntersection (Count (M + N)) (exist (Finite (Count (M + N))) (Full_set (Count (M + N))) (CountFinite (M + N))) (Complement (Count (M + N)) (proj1_sig (FiniteIm (Count (S (proj1_sig k))) (Count (M + N)) (fun (m : Count (S (proj1_sig k))) => exist (fun (n : nat) => (n < M + N)%nat) (proj1_sig m) (H13 m)) (exist (Finite (Count (S (proj1_sig k)))) (Full_set (Count (S (proj1_sig k)))) (CountFinite (S (proj1_sig k))))))))).
rewrite CM_O_r.
suff: (SingularValueRCH K M N A k * SingularValueRCH K M N A k = SingularValueRCH K M N A k * SingularValueRCH K M N A k * RCRe K (RCnInnerProduct K (S (proj1_sig k)) x x)).
move=> H15.
rewrite H15.
unfold RCnInnerProduct.
apply (FiniteSetInduction (Count (S (proj1_sig k))) (exist (Finite (Count (S (proj1_sig k)))) (Full_set (Count (S (proj1_sig k)))) (CountFinite (S (proj1_sig k))))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
suff: (RCRe K (CMe (RCPCM K)) = 0).
move=> H16.
rewrite H16.
right.
rewrite (Rmult_0_r (SingularValueRCH K M N A k * SingularValueRCH K M N A k)).
reflexivity.
elim K.
reflexivity.
reflexivity.
move=> D d H16 H17 H18 H19.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite RCReplus.
rewrite RCReplus.
rewrite Rmult_plus_distr_l.
apply Rplus_ge_compat.
apply H19.
unfold Basics.compose.
unfold MMatrixToVector.
unfold Mmult.
unfold MVectorToMatrix.
suff: (proj1_sig d < M)%nat.
move=> H20.
rewrite (MySumF2Included {n : nat | (n < M)%nat} (FiniteSingleton {n : nat | (n < M)%nat} (exist (fun (n : nat) => (n < M)%nat) (proj1_sig d) H20))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
simpl.
elim (excluded_middle_informative (proj1_sig d < S (proj1_sig k))%nat).
move=> H21.
suff: ((exist (fun (n : nat) => (n < M + N)%nat) (proj1_sig d) (H13 d)) = AddConnect M N (inl (exist (fun (n : nat) => (n < M)%nat) (proj1_sig d) H20))).
move=> H22.
rewrite H22.
unfold MBlockH.
rewrite (proj1 (AddConnectInvRelation M N)).
unfold MDiag.
simpl.
elim (Nat.eq_dec (proj1_sig d) (proj1_sig d)).
move=> H23.
suff: ((exist (fun (l : nat) => (l < S (proj1_sig k))%nat) (proj1_sig d) H21) = d).
move=> H24.
rewrite H24.
suff: (forall (a b : RCT K), RCmult K (RCmult K a b) (ConjugateRC K (RCmult K a b)) = RCmult K (RCmult K a (ConjugateRC K a)) (RCmult K b (ConjugateRC K b))).
move=> H25.
rewrite H25.
suff: (forall (K : RC) (x : R), ConjugateRC K (IRRC K x) = IRRC K x).
move=> H26.
rewrite H26.
rewrite - (IRRCmult K).
suff: (forall (K : RC) (a : R) (b : RCT K), RCRe K (RCmult K (IRRC K a) b) = a * RCRe K b).
move=> H27.
rewrite H27.
apply Rmult_ge_compat_r.
suff: (forall (K : RC) (a : RCT K), RCRe K (RCmult K a (ConjugateRC K a)) >= 0).
move=> H28.
apply H28.
elim.
move=> a.
apply Formula_1_3.
move=> a.
simpl.
unfold Conjugate.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite - (Rplus_0_l 0).
apply Rplus_ge_compat.
apply Formula_1_3.
rewrite (Ropp_mult_distr_r (a CIm) (- a CIm)).
rewrite (Ropp_involutive (a CIm)).
apply Formula_1_3.
suff: (SingularValueRCH K M N A (exist (fun (n : nat) => (n < M)%nat) (proj1_sig d) H20) >= SingularValueRCH K M N A k).
move=> H28.
apply Rmult_ge_compat.
apply (proj1 (SingularValueRCHNature K M N A) k).
apply (proj1 (SingularValueRCHNature K M N A) k).
apply H28.
apply H28.
apply (proj1 (proj2 (SingularValueRCHNature K M N A)) (exist (fun (n : nat) => (n < M)%nat) (proj1_sig d) H20) k).
apply (le_S_n (proj1_sig d) (proj1_sig k) H21).
elim.
move=> a b.
reflexivity.
move=> a b.
simpl.
unfold Cmult.
rewrite CmakeRe.
unfold IRC.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite (Rmult_0_l (b CIm)).
apply (Rminus_0_r (a * b CRe)).
elim.
move=> a.
reflexivity.
move=> a.
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H26.
rewrite H26.
apply (CmakeRe (Cmake a 0 CRe) (- (Cmake a 0 CIm))).
move=> H26.
rewrite H26.
simpl.
unfold IRC.
unfold Conjugate.
rewrite (CmakeIm (Cmake a 0 CRe) (- Cmake a 0 CIm)).
rewrite (CmakeIm a 0).
apply Ropp_0.
move=> a b.
rewrite Proposition_4_8_2_RC.
simpl.
rewrite (RCmult_assoc K a b (RCmult K (ConjugateRC K a) (ConjugateRC K b))).
rewrite (RCmult_assoc K a (ConjugateRC K a) (RCmult K b (ConjugateRC K b))).
rewrite (RCmult_comm K b (RCmult K (ConjugateRC K a) (ConjugateRC K b))).
rewrite (RCmult_assoc K (ConjugateRC K a) (ConjugateRC K b) b).
rewrite (RCmult_comm K (ConjugateRC K b) b).
reflexivity.
apply sig_map.
reflexivity.
elim.
reflexivity.
apply sig_map.
rewrite - (proj1 (AddConnectNature M N)).
reflexivity.
move=> H21.
elim (H21 (proj2_sig d)).
move=> u.
elim.
move=> u0 H21 H22.
unfold MBlockH.
suff: (proj1_sig (exist (fun (n : nat) => (n < M + N)%nat) (proj1_sig d) (H13 d)) <> proj1_sig u0).
rewrite - {1} (proj2 (AddConnectInvRelation M N) (exist (fun (n : nat) => (n < M + N)%nat) (proj1_sig d) (H13 d))).
elim (AddConnectInv M N (exist (fun (n : nat) => (n < M + N)%nat) (proj1_sig d) (H13 d))).
move=> d0.
unfold MDiag.
rewrite - (proj1 (AddConnectNature M N) d0).
move=> H23.
elim (Nat.eq_dec (proj1_sig d0) (proj1_sig u0)).
move=> H24.
elim (H23 H24).
move=> H24.
apply Fmul_O_l.
move=> u1 H23.
apply Fmul_O_l.
move=> H23.
elim H21.
suff: ((exist (fun (n : nat) => (n < M)%nat) (proj1_sig d) H20) = u0).
move=> H24.
rewrite H24.
apply (In_singleton {n : nat | (n < M)%nat} u0).
apply sig_map.
apply H23.
move=> u0 H21.
apply (Full_intro {n : nat | (n < M)%nat} u0).
apply (le_trans (S (proj1_sig d)) (S (proj1_sig k)) M (proj2_sig d) (proj2_sig k)).
apply H18.
apply H18.
rewrite (proj2 (RCnNormNature K (S (proj1_sig k)) x)).
rewrite H10.
rewrite (Rmult_1_r 1).
rewrite (Rmult_1_r (SingularValueRCH K M N A k * SingularValueRCH K M N A k)).
reflexivity.
move=> u.
elim.
move=> u0 H15 H16.
unfold MMatrixToVector.
unfold Mmult.
rewrite MySumF2O.
apply (Fmul_O_l (RCfield K)).
move=> u1 H17.
unfold MBlockH.
suff: (proj1_sig u0 >= S (proj1_sig k))%nat.
rewrite - {1} (proj2 (AddConnectInvRelation M N) u0).
elim (AddConnectInv M N u0).
move=> m.
rewrite - (proj1 (AddConnectNature M N) m).
move=> H18.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig u1)).
move=> H19.
unfold MVectorToMatrix.
elim (excluded_middle_informative (proj1_sig u1 < S (proj1_sig k))%nat).
move=> H20.
elim (le_not_lt (S (proj1_sig k)) (proj1_sig m) H18).
rewrite H19.
apply H20.
move=> H20.
apply (Fmul_O_r (RCfield K)).
move=> H19.
apply (Fmul_O_l (RCfield K)).
move=> m H18.
apply (Fmul_O_l (RCfield K)).
elim (le_or_lt (S (proj1_sig k)) (proj1_sig u0)).
apply.
move=> H18.
elim H15.
apply (Im_intro (Count (S (proj1_sig k))) (Count (M + N)) (Full_set (Count (S (proj1_sig k)))) (fun (m : Count (S (proj1_sig k))) => exist (fun (n : nat) => (n < M + N)%nat) (proj1_sig m) (H13 m)) (exist (fun (n : nat) => (n < S (proj1_sig k))%nat) (proj1_sig u0) H18)).
apply (Full_intro (Count (S (proj1_sig k)))).
apply sig_map.
reflexivity.
move=> u1 u2 H15 H16 H17.
apply sig_map.
suff: (proj1_sig u1 = proj1_sig (exist (fun (n : nat) => (n < M + N)%nat) (proj1_sig u1) (H13 u1))).
move=> H18.
rewrite H18.
rewrite H17.
reflexivity.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u.
elim.
move=> u0 H14 H15.
apply (Im_intro (Count (S (proj1_sig k))) (Count (M + N)) (Full_set (Count (S (proj1_sig k)))) (fun (m : Count (S (proj1_sig k))) => exist (fun n : nat => (n < M + N)%nat) (proj1_sig m) (H13 m)) (exist (fun (n : nat) => (n < S (proj1_sig k))%nat) (proj1_sig u0) H14)).
apply (Full_intro (Count (S (proj1_sig k)))).
apply sig_map.
reflexivity.
move=> u.
elim.
move=> u0 H14 y H15.
apply (Intersection_intro (Count (M + N))).
rewrite H15.
apply (proj2_sig u0).
apply (Full_intro (Count (M + N))).
move=> m.
apply (le_trans (S (proj1_sig m)) M (M + N)).
apply (le_trans (S (proj1_sig m)) (S (proj1_sig k)) M (proj2_sig m) (proj2_sig k)).
apply (le_plus_l M N).
move=> u H13.
apply (Full_intro (Count (M + N)) u).
move=> X.
rewrite RCnInnerProductMatrix.
rewrite RCnInnerProductMatrix.
rewrite (proj2 (MVectorMatrixRelation (RCfield K) (M + N))).
rewrite (proj2 (MVectorMatrixRelation (RCfield K) (M + N))).
rewrite (AdjointMatrixRCMult K (M + N) (M + N) 1).
rewrite (Mmult_assoc (RCfield K) 1 (M + N) (M + N) 1).
rewrite - (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) 1 (AdjointMatrixRC K (M + N) (M + N) U) U X).
rewrite (proj1 H2).
rewrite (Mmult_I_l (RCfield K) (M + N) 1 X).
reflexivity.
move=> a b H11 H12 H13.
apply (Rnot_lt_ge a b).
move=> H14.
apply (Rgt_not_ge (a * a) (b * b)).
apply (Rmult_le_0_lt_compat a b a b).
apply (Rge_le a 0 H11).
apply (Rge_le a 0 H11).
apply H14.
apply H14.
apply H13.
apply (RCnNormNature2 K (S (proj1_sig k)) x).
apply conj.
left.
apply Rlt_0_1.
suff: (RCnInnerProduct K (S (proj1_sig k)) x x = RCnInnerProduct K M v0 v0).
move=> H10.
rewrite H10.
rewrite (proj2 (RCnNormNature K M v0)).
rewrite H7.
reflexivity.
rewrite H9.
suff: (forall (y : Count M -> FT (RCfield K)), RCnInnerProduct K M (MVmult (RCfield K) M M V y) (MVmult (RCfield K) M M V y) = RCnInnerProduct K M y y).
move=> H10.
rewrite H10.
unfold RCnInnerProduct at 2.
rewrite (MySumF2Included (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n < S (proj1_sig k))%nat))).
suff: (forall (n : Count (S (proj1_sig k))), (proj1_sig n < M)%nat).
move=> H11.
suff: (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n < S (proj1_sig k))%nat) = FiniteIm (Count (S (proj1_sig k))) (Count M) (fun (m : Count (S (proj1_sig k))) => exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H11 m)) (exist (Finite (Count (S (proj1_sig k)))) (Full_set (Count (S (proj1_sig k)))) (CountFinite (S (proj1_sig k))))).
move=> H12.
rewrite H12.
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count M)).
rewrite CM_O_r.
apply MySumF2Same.
move=> u H13.
unfold Basics.compose.
simpl.
elim (excluded_middle_informative (proj1_sig u < S (proj1_sig k))%nat).
move=> H14.
suff: (u = (exist (fun (l : nat) => (l < S (proj1_sig k))%nat) (proj1_sig u) H14)).
move=> H15.
rewrite - H15.
reflexivity.
apply sig_map.
reflexivity.
move=> H14.
elim (H14 (proj2_sig u)).
move=> u.
elim.
move=> u0 H13 H14.
elim (excluded_middle_informative (proj1_sig u0 < S (proj1_sig k))%nat).
move=> H15.
elim H13.
apply (Im_intro (Count (S (proj1_sig k))) (Count M) (Full_set (Count (S (proj1_sig k)))) (fun (m : Count (S (proj1_sig k))) => exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H11 m)) (exist (fun (n : nat) => (n < S (proj1_sig k))%nat) (proj1_sig u0) H15)).
apply (Full_intro (Count (S (proj1_sig k)))).
apply sig_map.
reflexivity.
move=> H15.
apply (Fmul_O_l (RCfield K)).
move=> u1 u2 H13 H14 H15.
apply sig_map.
suff: (proj1_sig u1 = proj1_sig (exist (fun (n : nat) => (n < M)%nat) (proj1_sig u1) (H11 u1))).
move=> H16.
rewrite H16.
rewrite H15.
reflexivity.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u.
elim.
move=> u0 H12 H13.
apply (Im_intro (Count (S (proj1_sig k))) (Count M) (Full_set (Count (S (proj1_sig k)))) (fun (m : Count (S (proj1_sig k))) => exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H11 m)) (exist (fun (n : nat) => (n < S (proj1_sig k))%nat) (proj1_sig u0) H12)).
apply (Full_intro (Count (S (proj1_sig k)))).
apply sig_map.
reflexivity.
move=> u.
elim.
move=> u0 H12 y H13.
apply (Intersection_intro (Count M)).
rewrite H13.
apply (proj2_sig u0).
apply (Full_intro (Count M)).
move=> m.
apply (le_trans (S (proj1_sig m)) (S (proj1_sig k)) M (proj2_sig m) (proj2_sig k)).
move=> u H11.
apply (Full_intro (Count M) u).
move=> y.
rewrite RCnInnerProductMatrix.
rewrite RCnInnerProductMatrix.
unfold MVmult.
rewrite (proj2 (MVectorMatrixRelation (RCfield K) M)).
rewrite (AdjointMatrixRCMult K M M 1).
rewrite (Mmult_assoc (RCfield K) 1 M M 1).
rewrite - (Mmult_assoc (RCfield K) M M M 1 (AdjointMatrixRC K M M V) V (MVectorToMatrix (RCfield K) M y)).
rewrite (proj1 (proj2 H2)).
rewrite (Mmult_I_l (RCfield K) M 1 (MVectorToMatrix (RCfield K) M y)).
reflexivity.
rewrite H8.
suff: (forall (n : Count (S (proj1_sig k))), (proj1_sig n < M)%nat).
move=> H9.
unfold MVmult.
unfold Mmult.
unfold MMatrixToVector.
apply functional_extensionality.
move=> m.
rewrite (MySumF2Included (Count M) (FiniteIm (Count (S (proj1_sig k))) (Count M) (fun (m : Count (S (proj1_sig k))) => exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H9 m)) (exist (Finite (Count (S (proj1_sig k)))) (Full_set (Count (S (proj1_sig k)))) (CountFinite (S (proj1_sig k)))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count M)).
rewrite CM_O_r.
apply (FiniteSetInduction (Count (S (proj1_sig k))) (exist (Finite (Count (S (proj1_sig k)))) (Full_set (Count (S (proj1_sig k)))) (CountFinite (S (proj1_sig k))))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> C c H10 H11 H12 H13.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H13.
unfold Basics.compose.
unfold MVectorToMatrix.
simpl.
elim (excluded_middle_informative (proj1_sig c < S (proj1_sig k))%nat).
move=> H14.
rewrite (RCmult_comm K).
suff: (c = (exist (fun (l : nat) => (l < S (proj1_sig k))%nat) (proj1_sig c) H14)).
move=> H15.
rewrite - H15.
suff: (H3 = H9).
move=> H16.
rewrite H16.
reflexivity.
apply proof_irrelevance.
apply sig_map.
reflexivity.
move=> H14.
elim (H14 (proj2_sig c)).
apply H12.
apply H12.
move=> u.
elim.
move=> u0 H10 H11.
unfold MVectorToMatrix.
elim (excluded_middle_informative (proj1_sig u0 < S (proj1_sig k))%nat).
move=> H12.
elim H10.
apply (Im_intro (Count (S (proj1_sig k))) (Count M) (Full_set (Count (S (proj1_sig k)))) (fun (m : Count (S (proj1_sig k))) => exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H9 m)) (exist (fun (n : nat) => (n < S (proj1_sig k))%nat) (proj1_sig u0) H12)).
apply (Full_intro (Count (S (proj1_sig k)))).
apply sig_map.
reflexivity.
move=> H12.
apply (Fmul_O_r (RCfield K)).
move=> u1 u2 H10 H11 H12.
apply sig_map.
suff: (proj1_sig u1 = proj1_sig (exist (fun (n : nat) => (n < M)%nat) (proj1_sig u1) (H9 u1))).
move=> H13.
rewrite H13.
rewrite H12.
reflexivity.
reflexivity.
move=> u0 H10.
apply (Full_intro (Count M) u0).
move=> m.
apply (le_trans (S (proj1_sig m)) (S (proj1_sig k)) M (proj2_sig m) (proj2_sig k)).
apply (proj1 H4).
elim (classic (Intersection (RCn K M) (fun (x : RCn K M) => MVmult (RCfield K) (M + N) M B x = RCnO K (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig k))) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H3 m)))) = Singleton (RCn K M) (RCnO K M))).
move=> H4.
elim (RankKerRelationVS_exists (RCfield K) (M + N) M B).
move=> H5.
elim.
move=> H6 H7.
elim (DimensionSumEnsembleVS2_exists (RCfield K) (FnVS (RCfield K) M) (fun (x : RCn K M) => MVmult (RCfield K) (M + N) M B x = RCnO K (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig k))) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H3 m)))) H5 (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig k))) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H3 m))))).
move=> H8 H9.
suff: (FiniteDimensionVS (RCfield K) (SubspaceMakeVS (RCfield K) (FnVS (RCfield K) M) (SumEnsembleVS (RCfield K) (FnVS (RCfield K) M) (fun (x : RCn K M) => MVmult (RCfield K) (M + N) M B x = RCnO K (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig k))) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H3 m))))) H8)).
move=> H10.
elim (H9 H10).
move=> H11.
elim.
move=> H12 H13.
elim (lt_irrefl M).
unfold lt.
suff: (S M <= DimensionSubspaceVS (RCfield K) (FnVS (RCfield K) M) (SumEnsembleVS (RCfield K) (FnVS (RCfield K) M) (fun (x : RCn K M) => MVmult (RCfield K) (M + N) M B x = RCnO K (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig k))) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H3 m))))) H8 H10)%nat.
move=> H14.
apply (le_trans (S M) (DimensionSubspaceVS (RCfield K) (FnVS (RCfield K) M) (SumEnsembleVS (RCfield K) (FnVS (RCfield K) M) (fun (x : RCn K M) => MVmult (RCfield K) (M + N) M B x = RCnO K (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig k))) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H3 m))))) H8 H10) M).
apply H14.
elim (FnVSDimension (RCfield K) M).
move=> H15 H16.
rewrite - {15} H16.
apply (Proposition_5_9_1_2 (RCfield K) (FnVS (RCfield K) M)).
rewrite (H13 H4).
suff: (H11 = H6).
move=> H14.
rewrite H14.
rewrite H7.
rewrite (DimensionSubspaceVSNature2 (RCfield K) (FnVS (RCfield K) M) (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig k))) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H3 m)))) (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig k))) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H3 m)))) H12 (S (proj1_sig k)) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H3 m)))).
rewrite (plus_comm (M - Rank (RCfield K) (M + N) M B) (S (proj1_sig k))).
suff: (M <= proj1_sig k + (M - Rank (RCfield K) (M + N) M B))%nat.
move=> H15.
apply le_n_S.
apply H15.
apply (plus_le_reg_l M (proj1_sig k + (M - Rank (RCfield K) (M + N) M B)) (Rank (RCfield K) (M + N) M B)).
rewrite (plus_comm (proj1_sig k) (M - Rank (RCfield K) (M + N) M B)).
rewrite plus_assoc.
rewrite le_plus_minus_r.
rewrite plus_comm.
apply plus_le_compat_l.
apply (proj1 H1).
apply (RankLeW (RCfield K) (M + N) M B).
exists (SpanContainSelfVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig k))) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H3 m)))).
apply (proj2 (FiniteLinearlyIndependentVS (RCfield K) (FnVS (RCfield K) M) (S (proj1_sig k)) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun n : nat => (n < M)%nat) (proj1_sig m) (H3 m))))).
move=> a H15.
suff: (MVmult (RCfield K) M (S (proj1_sig k)) (fun (x : Count M) (y : Count (S (proj1_sig k))) => V x (exist (fun (n : nat) => (n < M)%nat) (proj1_sig y) (H3 y))) a = MySumF2 (Count (S (proj1_sig k))) (exist (Finite (Count (S (proj1_sig k)))) (Full_set (Count (S (proj1_sig k)))) (CountFinite (S (proj1_sig k)))) (VSPCM (RCfield K) (FnVS (RCfield K) M)) (fun (n : Count (S (proj1_sig k))) => Vmul (RCfield K) (FnVS (RCfield K) M) (a n) (MTranspose (RCfield K) M M V (exist (fun (k : nat) => (k < M)%nat) (proj1_sig n) (H3 n))))).
move=> H16.
suff: (a = MVmult (RCfield K) (S (proj1_sig k)) M (fun (x : Count (S (proj1_sig k))) (y : Count M) => ConjugateRC K (V y (exist (fun (n : nat) => (n < M)%nat) (proj1_sig x) (H3 x)))) (VO (RCfield K) (FnVS (RCfield K) M))).
move=> H17.
rewrite H17.
move=> m.
apply (MySumF2O (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (FPCM (RCfield K))).
move=> u H18.
apply (Fmul_O_r (RCfield K)).
rewrite - H15.
rewrite - H16.
apply functional_extensionality.
move=> m.
unfold MVmult.
rewrite (proj2 (MVectorMatrixRelation (RCfield K) M)).
rewrite - (Mmult_assoc (RCfield K) (S (proj1_sig k)) M (S (proj1_sig k)) 1).
suff: (Mmult (RCfield K) (S (proj1_sig k)) M (S (proj1_sig k)) (fun (x : Count (S (proj1_sig k))) (y : Count M) => ConjugateRC K (V y (exist (fun n : nat => (n < M)%nat) (proj1_sig x) (H3 x)))) (fun (x : Count M) (y : Count (S (proj1_sig k))) => V x (exist (fun n : nat => (n < M)%nat) (proj1_sig y) (H3 y))) = MI (RCfield K) (S (proj1_sig k))).
move=> H17.
rewrite H17.
rewrite Mmult_I_l.
rewrite (proj1 (MVectorMatrixRelation (RCfield K) (S (proj1_sig k)))).
reflexivity.
suff: (Mmult (RCfield K) (S (proj1_sig k)) M (S (proj1_sig k)) (fun (x : Count (S (proj1_sig k))) (y : Count M) => ConjugateRC K (V y (exist (fun n : nat => (n < M)%nat) (proj1_sig x) (H3 x)))) (fun (x : Count M) (y : Count (S (proj1_sig k))) => V x (exist (fun n : nat => (n < M)%nat) (proj1_sig y) (H3 y))) = (fun (x y : Count (S (proj1_sig k))) => Mmult (RCfield K) M M M (AdjointMatrixRC K M M V) V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig x) (H3 x)) (exist (fun (n : nat) => (n < M)%nat) (proj1_sig y) (H3 y))) ).
move=> H18.
rewrite H18.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite (proj1 (proj2 H2)).
reflexivity.
reflexivity.
apply functional_extensionality.
move=> x.
unfold MVmult.
unfold MMatrixToVector.
unfold Mmult.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S (proj1_sig k))%nat} (exist (Finite {n : nat | (n < S (proj1_sig k))%nat}) (Full_set {n : nat | (n < S (proj1_sig k))%nat}) (CountFinite (S (proj1_sig k))))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> C c H16 H17 H18 H19.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H19.
rewrite (RCmult_comm K).
reflexivity.
apply H18.
apply H18.
apply proof_irrelevance.
apply (Proposition_5_9_1_1 (RCfield K) (FnVS (RCfield K) M) (FnVSFiniteDimension (RCfield K) M)).
move=> H4.
elim (classic (exists (v : RCn K M), Intersection (RCn K M) (fun (x : RCn K M) => MVmult (RCfield K) (M + N) M B x = RCnO K (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig k))) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H3 m)))) v /\ v <> RCnO K M)).
elim.
move=> v H5.
exists (RCnmult K M (IRRC K (/ RCnNorm K M v)) v).
apply conj.
rewrite (Proposition_4_4_1 K M).
suff: (forall (r : R), r >= 0 -> RCabs K (IRRC K r) = r).
move=> H6.
rewrite (H6 (/ RCnNorm K M v)).
apply (Rinv_l (RCnNorm K M v)).
move=> H7.
apply (proj2 H5).
apply (Proposition_4_4_3_2 K M v H7).
left.
apply Rinv_0_lt_compat.
elim (Proposition_4_4_3_1 K M v).
apply.
move=> H7.
elim (proj2 H5).
apply (Proposition_4_4_3_2 K M v H7).
move=> x H6.
elim K.
apply (Rabs_right x H6).
simpl.
rewrite CnormDefinition.
apply MySqrtNature2.
apply conj.
apply H6.
simpl.
unfold IRC.
rewrite (CmakeRe x 0).
rewrite (CmakeIm x 0).
rewrite (Rmult_0_l 0).
apply (Rplus_0_r (x * x)).
suff: (SubspaceVS (RCfield K) (FnVS (RCfield K) M) (Intersection (RCn K M) (fun (x : RCn K M) => MVmult (RCfield K) (M + N) M B x = RCnO K (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig k))) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H3 m)))) )).
move=> H6.
apply (proj1 (proj2 H6)).
apply (proj1 H5).
apply IntersectionSubspaceVS.
apply RankKerSubspaceVS.
apply SpanSubspaceVS.
move=> H5.
elim H4.
apply Extensionality_Ensembles.
apply conj.
move=> v H6.
apply NNPP.
move=> H7.
apply H5.
exists v.
apply conj.
apply H6.
move=> H8.
apply H7.
rewrite H8.
apply (In_singleton (RCn K M) (RCnO K M)).
move=> v.
elim.
suff: (SubspaceVS (RCfield K) (FnVS (RCfield K) M) (Intersection (RCn K M) (fun (x : RCn K M) => MVmult (RCfield K) (M + N) M B x = RCnO K (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) M) (Count (S (proj1_sig k))) (fun (m : Count (S (proj1_sig k))) => MTranspose (RCfield K) M M V (exist (fun (n : nat) => (n < M)%nat) (proj1_sig m) (H3 m)))) )).
move=> H6.
apply (proj2 (proj2 H6)).
apply IntersectionSubspaceVS.
apply RankKerSubspaceVS.
apply SpanSubspaceVS.
move=> m.
apply (le_trans (S (proj1_sig m)) (S (proj1_sig k)) M (proj2_sig m) (proj2_sig k)).
Qed.

Lemma UnitaryMatrixRCSaveRCnInnerProductStrong : forall (K : RC) (M N : nat) (Q : Matrix (RCfield K) M N), Mmult (RCfield K) N M N (AdjointMatrixRC K M N Q) Q = MI (RCfield K) N -> forall (x y : RCn K N), RCnInnerProduct K M (MVmult (RCfield K) M N Q x) (MVmult (RCfield K) M N Q y) = RCnInnerProduct K N x y.
Proof.
move=> K M N Q H1 x y.
rewrite RCnInnerProductMatrix.
rewrite RCnInnerProductMatrix.
unfold MVmult.
rewrite (proj2 (MVectorMatrixRelation (RCfield K) M)).
rewrite (proj2 (MVectorMatrixRelation (RCfield K) M)).
rewrite AdjointMatrixRCMult.
rewrite (Mmult_assoc (RCfield K) 1 N M 1).
rewrite - (Mmult_assoc (RCfield K) N M N 1).
rewrite H1.
rewrite (Mmult_I_l (RCfield K)).
reflexivity.
Qed.

Lemma UnitaryMatrixRCSaveRCnNormStrong : forall (K : RC) (M N : nat) (Q : Matrix (RCfield K) M N), Mmult (RCfield K) N M N (AdjointMatrixRC K M N Q) Q = MI (RCfield K) N -> forall (x : RCn K N), RCnNorm K M (MVmult (RCfield K) M N Q x) = RCnNorm K N x.
Proof.
move=> K M N Q H1 x.
apply RCnNormNature2.
apply conj.
apply (proj1 (RCnNormNature K N x)).
rewrite - (proj2 (RCnNormNature K N x)).
rewrite (UnitaryMatrixRCSaveRCnInnerProductStrong K M N Q H1 x).
reflexivity.
Qed.

Definition UnitaryMatrixRCSaveRCnInnerProduct (K : RC) (N : nat) : forall (Q : Matrix (RCfield K) N N), UnitaryMatrixRC K N Q -> forall (x y : RCn K N), RCnInnerProduct K N (MVmult (RCfield K) N N Q x) (MVmult (RCfield K) N N Q y) = RCnInnerProduct K N x y := UnitaryMatrixRCSaveRCnInnerProductStrong K N N.

Definition UnitaryMatrixRCSaveRCnNorm (K : RC) (N : nat) : forall (Q : Matrix (RCfield K) N N), UnitaryMatrixRC K N Q -> forall (x : RCn K N), RCnNorm K N (MVmult (RCfield K) N N Q x) = RCnNorm K N x := UnitaryMatrixRCSaveRCnNormStrong K N N.

Lemma MTransposeMatrixRCSaveRCFrobeniusNormStrong : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M N), RCFrobeniusNorm K N M (MTranspose (RCfield K) M N A) = RCFrobeniusNorm K M N A.
Proof.
move=> K M N A.
unfold RCFrobeniusNorm.
apply RCnNormNature2.
apply conj.
apply (proj1 (RCnNormNature K (M * N) (fun (m : Count (M * N)) => A (fst (MultConnectInv M N m)) (snd (MultConnectInv M N m))))).
rewrite - (proj2 (RCnNormNature K (M * N) (fun (m : Count (M * N)) => A (fst (MultConnectInv M N m)) (snd (MultConnectInv M N m))))).
apply f_equal.
unfold RCnInnerProduct.
suff: ((exist (Finite (Count (N * M))) (Full_set (Count (N * M))) (CountFinite (N * M))) = FiniteIm (Count (M * N)) (Count (N * M)) (fun (m : Count (M * N)) => MultConnect N M (snd (MultConnectInv M N m),fst (MultConnectInv M N m))) (exist (Finite (Count (M * N))) (Full_set (Count (M * N))) (CountFinite (M * N)))).
move=> H1.
rewrite H1.
rewrite - MySumF2BijectiveSame2.
apply (MySumF2Same (Count (M * N)) (exist (Finite (Count (M * N))) (Full_set (Count (M * N))) (CountFinite (M * N))) (RCPCM K)).
move=> u H2.
unfold Basics.compose.
rewrite (proj1 (MultConnectInvRelation N M)).
reflexivity.
move=> u1 u2 H2 H3 H4.
suff: (MultConnectInv M N u1 = MultConnectInv M N u2).
move=> H5.
rewrite - (proj2 (MultConnectInvRelation M N) u1).
rewrite H5.
apply (proj2 (MultConnectInvRelation M N) u2).
suff: ((snd (MultConnectInv M N u1), fst (MultConnectInv M N u1)) = (snd (MultConnectInv M N u2), fst (MultConnectInv M N u2))).
move=> H5.
apply injective_projections.
suff: (fst (MultConnectInv M N u1) = snd (snd (MultConnectInv M N u1), fst (MultConnectInv M N u1))).
move=> H6.
rewrite H6.
rewrite H5.
reflexivity.
reflexivity.
suff: (snd (MultConnectInv M N u1) = fst (snd (MultConnectInv M N u1), fst (MultConnectInv M N u1))).
move=> H6.
rewrite H6.
rewrite H5.
reflexivity.
reflexivity.
rewrite - (proj1 (MultConnectInvRelation N M) (snd (MultConnectInv M N u1), fst (MultConnectInv M N u1))).
rewrite H4.
apply (proj1 (MultConnectInvRelation N M)).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u H1.
apply (Im_intro (Count (M * N)) (Count (N * M)) (Full_set (Count (M * N))) (fun (m : Count (M * N)) => MultConnect N M (snd (MultConnectInv M N m), fst (MultConnectInv M N m))) (MultConnect M N (snd (MultConnectInv N M u), fst (MultConnectInv N M u)))).
apply (Full_intro (Count (M * N))).
rewrite (proj1 (MultConnectInvRelation M N)).
simpl.
suff: ((fst (MultConnectInv N M u), snd (MultConnectInv N M u)) = MultConnectInv N M u).
move=> H2.
rewrite H2.
rewrite (proj2 (MultConnectInvRelation N M) u).
reflexivity.
apply injective_projections.
reflexivity.
reflexivity.
move=> u H1.
apply (Full_intro (Count (N * M)) u).
Qed.

Lemma AdjointMatrixRCSaveRCFrobeniusNormStrong : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M N), RCFrobeniusNorm K N M (AdjointMatrixRC K M N A) = RCFrobeniusNorm K M N A.
Proof.
move=> K M N A.
unfold RCFrobeniusNorm.
apply RCnNormNature2.
apply conj.
apply (proj1 (RCnNormNature K (M * N) (fun (m : Count (M * N)) => A (fst (MultConnectInv M N m)) (snd (MultConnectInv M N m))))).
rewrite - (proj2 (RCnNormNature K (M * N) (fun (m : Count (M * N)) => A (fst (MultConnectInv M N m)) (snd (MultConnectInv M N m))))).
apply f_equal.
unfold RCnInnerProduct.
suff: ((exist (Finite (Count (N * M))) (Full_set (Count (N * M))) (CountFinite (N * M))) = FiniteIm (Count (M * N)) (Count (N * M)) (fun (m : Count (M * N)) => MultConnect N M (snd (MultConnectInv M N m),fst (MultConnectInv M N m))) (exist (Finite (Count (M * N))) (Full_set (Count (M * N))) (CountFinite (M * N)))).
move=> H1.
rewrite H1.
rewrite - MySumF2BijectiveSame2.
apply (MySumF2Same (Count (M * N)) (exist (Finite (Count (M * N))) (Full_set (Count (M * N))) (CountFinite (M * N))) (RCPCM K)).
move=> u H2.
unfold Basics.compose.
rewrite (proj1 (MultConnectInvRelation N M)).
rewrite (RCmult_comm K).
unfold AdjointMatrixRC.
rewrite (ConjugateRCInvolutive K).
reflexivity.
move=> u1 u2 H2 H3 H4.
suff: (MultConnectInv M N u1 = MultConnectInv M N u2).
move=> H5.
rewrite - (proj2 (MultConnectInvRelation M N) u1).
rewrite H5.
apply (proj2 (MultConnectInvRelation M N) u2).
suff: ((snd (MultConnectInv M N u1), fst (MultConnectInv M N u1)) = (snd (MultConnectInv M N u2), fst (MultConnectInv M N u2))).
move=> H5.
apply injective_projections.
suff: (fst (MultConnectInv M N u1) = snd (snd (MultConnectInv M N u1), fst (MultConnectInv M N u1))).
move=> H6.
rewrite H6.
rewrite H5.
reflexivity.
reflexivity.
suff: (snd (MultConnectInv M N u1) = fst (snd (MultConnectInv M N u1), fst (MultConnectInv M N u1))).
move=> H6.
rewrite H6.
rewrite H5.
reflexivity.
reflexivity.
rewrite - (proj1 (MultConnectInvRelation N M) (snd (MultConnectInv M N u1), fst (MultConnectInv M N u1))).
rewrite H4.
apply (proj1 (MultConnectInvRelation N M)).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u H1.
apply (Im_intro (Count (M * N)) (Count (N * M)) (Full_set (Count (M * N))) (fun (m : Count (M * N)) => MultConnect N M (snd (MultConnectInv M N m), fst (MultConnectInv M N m))) (MultConnect M N (snd (MultConnectInv N M u), fst (MultConnectInv N M u)))).
apply (Full_intro (Count (M * N))).
rewrite (proj1 (MultConnectInvRelation M N)).
simpl.
suff: ((fst (MultConnectInv N M u), snd (MultConnectInv N M u)) = MultConnectInv N M u).
move=> H2.
rewrite H2.
rewrite (proj2 (MultConnectInvRelation N M) u).
reflexivity.
apply injective_projections.
reflexivity.
reflexivity.
move=> u H1.
apply (Full_intro (Count (N * M)) u).
Qed.

Lemma UnitaryMatrixRCSaveRCFrobeniusNormStrongL : forall (K : RC) (L M N : nat) (Q : Matrix (RCfield K) L M), Mmult (RCfield K) M L M (AdjointMatrixRC K L M Q) Q = MI (RCfield K) M -> forall (A : Matrix (RCfield K) M N), RCFrobeniusNorm K L N (Mmult (RCfield K) L M N Q A) = RCFrobeniusNorm K M N A.
Proof.
move=> K L M N Q H1 A.
unfold RCFrobeniusNorm.
apply RCnNormNature2.
apply conj.
apply (proj1 (RCnNormNature K (M * N) (fun (m : Count (M * N)) => A (fst (MultConnectInv M N m)) (snd (MultConnectInv M N m))))).
rewrite - (proj2 (RCnNormNature K (M * N) (fun (m : Count (M * N)) => A (fst (MultConnectInv M N m)) (snd (MultConnectInv M N m))))).
apply f_equal.
unfold RCnInnerProduct.
rewrite (MySumF2ImageSum (Count (L * N)) (Count N) (exist (Finite (Count (L * N))) (Full_set (Count (L * N))) (CountFinite (L * N))) (RCPCM K) (fun (n : Count (L * N)) => RCmult K (Mmult (RCfield K) L M N Q A (fst (MultConnectInv L N n)) (snd (MultConnectInv L N n))) (ConjugateRC K (Mmult (RCfield K) L M N Q A (fst (MultConnectInv L N n)) (snd (MultConnectInv L N n))))) (fun (m : Count (L * N)) => snd (MultConnectInv L N m))).
rewrite (MySumF2ImageSum (Count (M * N)) (Count N) (exist (Finite (Count (M * N))) (Full_set (Count (M * N))) (CountFinite (M * N))) (RCPCM K) (fun (n : Count (M * N)) => RCmult K (A (fst (MultConnectInv M N n)) (snd (MultConnectInv M N n))) (ConjugateRC K (A (fst (MultConnectInv M N n)) (snd (MultConnectInv M N n))))) (fun (m : Count (M * N)) => snd (MultConnectInv M N m))).
rewrite (MySumF2Included (Count N) (FiniteIm (Count (M * N)) (Count N) (fun (m : Count (M * N)) => snd (MultConnectInv M N m)) (exist (Finite (Count (M * N))) (Full_set (Count (M * N))) (CountFinite (M * N)))) (FiniteIm (Count (L * N)) (Count N) (fun (m : Count (L * N)) => snd (MultConnectInv L N m)) (exist (Finite (Count (L * N))) (Full_set (Count (L * N))) (CountFinite (L * N))))).
rewrite (MySumF2O (Count N) (FiniteIntersection (Count N) (FiniteIm (Count (L * N)) (Count N) (fun (m : Count (L * N)) => snd (MultConnectInv L N m)) (exist (Finite (Count (L * N))) (Full_set (Count (L * N))) (CountFinite (L * N)))) (Complement (Count N) (proj1_sig (FiniteIm (Count (M * N)) (Count N) (fun (m : Count (M * N)) => snd (MultConnectInv M N m)) (exist (Finite (Count (M * N))) (Full_set (Count (M * N))) (CountFinite (M * N)))))))).
rewrite CM_O_r.
apply (MySumF2Same (Count N) (FiniteIm (Count (M * N)) (Count N) (fun (m : Count (M * N)) => snd (MultConnectInv M N m)) (exist (Finite (Count (M * N))) (Full_set (Count (M * N))) (CountFinite (M * N)))) (RCPCM K)).
move=> u H2.
suff: (forall (X : nat), FiniteIntersection (Count (X * N)) (exist (Finite (Count (X * N))) (Full_set (Count (X * N))) (CountFinite (X * N))) (fun (u1 : Count (X * N)) => snd (MultConnectInv X N u1) = u) = FiniteIm (Count X) (Count (X * N)) (fun (m : Count X) => MultConnect X N (m, u)) (exist (Finite (Count X)) (Full_set (Count X)) (CountFinite X))).
move=> H3.
rewrite (H3 L).
rewrite (H3 M).
suff: (forall (X : nat) (u1 u2 : Count X), In (Count X) (proj1_sig (exist (Finite (Count X)) (Full_set (Count X)) (CountFinite X))) u1 -> In (Count X) (proj1_sig (exist (Finite (Count X)) (Full_set (Count X)) (CountFinite X))) u2 -> MultConnect X N (u1, u) = MultConnect X N (u2, u) -> u1 = u2).
move=> H4.
rewrite - MySumF2BijectiveSame2.
rewrite - MySumF2BijectiveSame2.
suff: (MySumF2 (Count L) (exist (Finite (Count L)) (Full_set (Count L)) (CountFinite L)) (RCPCM K) (Basics.compose (fun (n : Count (L * N)) => RCmult K (Mmult (RCfield K) L M N Q A (fst (MultConnectInv L N n)) (snd (MultConnectInv L N n))) (ConjugateRC K (Mmult (RCfield K) L M N Q A (fst (MultConnectInv L N n)) (snd (MultConnectInv L N n))))) (fun (m : Count L) => MultConnect L N (m, u))) = RCnInnerProduct K L (MVmult (RCfield K) L M Q (MTranspose (RCfield K) M N A u)) (MVmult (RCfield K) L M Q (MTranspose (RCfield K) M N A u))).
move=> H5.
rewrite H5.
suff: (MySumF2 (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (RCPCM K) (Basics.compose (fun (n : Count (M * N)) => RCmult K (A (fst (MultConnectInv M N n)) (snd (MultConnectInv M N n))) (ConjugateRC K (A (fst (MultConnectInv M N n)) (snd (MultConnectInv M N n))))) (fun (m : Count M) => MultConnect M N (m, u))) = RCnInnerProduct K M (MTranspose (RCfield K) M N A u) (MTranspose (RCfield K) M N A u)).
move=> H6.
rewrite H6.
apply (UnitaryMatrixRCSaveRCnInnerProductStrong K L M Q H1).
apply (MySumF2Same (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (RCPCM K)).
move=> u1 H6.
unfold Basics.compose.
rewrite (proj1 (MultConnectInvRelation M N) (u1, u)).
reflexivity.
apply (MySumF2Same (Count L) (exist (Finite (Count L)) (Full_set (Count L)) (CountFinite L)) (RCPCM K)).
move=> u1 H5.
unfold Basics.compose.
rewrite (proj1 (MultConnectInvRelation L N) (u1, u)).
reflexivity.
apply (H4 M).
apply (H4 L).
move=> X u1 u2 H4 H5 H6.
suff: ((u1, u) = (u2, u)).
move=> H7.
suff: (u1 = fst (u1, u)).
move=> H8.
rewrite H8.
rewrite H7.
reflexivity.
reflexivity.
rewrite - (proj1 (MultConnectInvRelation X N) (u1, u)).
rewrite H6.
apply (proj1 (MultConnectInvRelation X N) (u2, u)).
move=> X.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u0.
elim.
move=> u1 H3 H4.
apply (Im_intro (Count X) (Count (X * N)) (Full_set (Count X)) (fun (m : Count X) => MultConnect X N (m, u)) (fst (MultConnectInv X N u1))).
apply (Full_intro (Count X)).
rewrite - {1} (proj2 (MultConnectInvRelation X N) u1).
apply f_equal.
apply injective_projections.
reflexivity.
apply H3.
move=> u0.
elim.
move=> x H3 y H4.
apply (Intersection_intro (Count (X * N))).
rewrite H4.
unfold In.
rewrite (proj1 (MultConnectInvRelation X N) (x, u)).
reflexivity.
apply (Full_intro (Count (X * N))).
elim (le_lt_or_eq O M (le_0_n M)).
move=> H2 u.
elim.
move=> u0.
elim.
apply (Im_intro (Count (M * N)) (Count N) (Full_set (Count (M * N))) (fun (m : Count (M * N)) => snd (MultConnectInv M N m)) (MultConnect M N (exist (fun (n : nat) => (n < M)%nat) O H2 , u0))).
apply (Full_intro (Count (M * N))).
rewrite (proj1 (MultConnectInvRelation M N)).
reflexivity.
move=> H2 u H3.
apply MySumF2O.
move=> u0 H4.
unfold Mmult.
rewrite MySumF2O.
apply (Fmul_O_l (RCfield K)).
move=> u1.
elim (le_not_lt O (proj1_sig u1) (le_0_n (proj1_sig u1))).
rewrite H2.
apply (proj2_sig u1).
elim (le_lt_or_eq O L (le_O_n L)).
move=> H2 u H3.
apply (Im_intro (Count (L * N)) (Count N) (Full_set (Count (L * N))) (fun (m : Count (L * N)) => snd (MultConnectInv L N m)) (MultConnect L N (exist (fun (n : nat) => (n < L)%nat) O H2 , u))).
apply (Full_intro (Count (L * N))).
rewrite (proj1 (MultConnectInvRelation L N)).
reflexivity.
move=> H2.
elim (le_lt_or_eq O M (le_O_n M)).
move=> H3.
elim (RCI_neq_RCO K).
suff: (Mmult (RCfield K) M L M (AdjointMatrixRC K L M Q) Q (exist (fun (n : nat) => (n < M)%nat) O H3) (exist (fun (n : nat) => (n < M)%nat) O H3) = RCO K).
move=> H4.
rewrite - H4.
rewrite H1.
reflexivity.
apply MySumF2O.
move=> u.
elim (le_not_lt O (proj1_sig u) (le_0_n (proj1_sig u))).
rewrite H2.
apply (proj2_sig u).
move=> H3 u.
elim.
move=> u0 H4.
elim (le_not_lt (M * N) (proj1_sig u0)).
rewrite - {1} H3.
rewrite (mult_0_l N).
apply (le_0_n (proj1_sig u0)).
apply (proj2_sig u0).
Qed.

Definition UnitaryMatrixRCSaveRCFrobeniusNormL (K : RC) (M N : nat) : forall (Q : Matrix (RCfield K) M M), UnitaryMatrixRC K M Q -> forall (A : Matrix (RCfield K) M N), RCFrobeniusNorm K M N (Mmult (RCfield K) M M N Q A) = RCFrobeniusNorm K M N A := UnitaryMatrixRCSaveRCFrobeniusNormStrongL K M M N.

Lemma UnitaryMatrixRCSaveRCFrobeniusNormStrongR : forall (K : RC) (L M N : nat) (Q : Matrix (RCfield K) M N), Mmult (RCfield K) M N M Q (AdjointMatrixRC K M N Q) = MI (RCfield K) M -> forall (A : Matrix (RCfield K) L M), RCFrobeniusNorm K L N (Mmult (RCfield K) L M N A Q) = RCFrobeniusNorm K L M A.
Proof.
move=> K L M N Q H1 A.
rewrite - (AdjointMatrixRCSaveRCFrobeniusNormStrong K L N).
rewrite (AdjointMatrixRCMult K L M N).
rewrite (UnitaryMatrixRCSaveRCFrobeniusNormStrongL K N M L (AdjointMatrixRC K M N Q)).
apply (AdjointMatrixRCSaveRCFrobeniusNormStrong K L M A).
rewrite (AdjointMatrixRCInvolutive K M N Q).
apply H1.
Qed.

Lemma UnitaryMatrixRCSaveRCFrobeniusNormR (K : RC) (M N : nat) : forall (Q : Matrix (RCfield K) N N), UnitaryMatrixRC K N Q -> forall (A : Matrix (RCfield K) M N), RCFrobeniusNorm K M N (Mmult (RCfield K) M N N A Q) = RCFrobeniusNorm K M N A.
Proof.
move=> Q H1 A.
apply (UnitaryMatrixRCSaveRCFrobeniusNormStrongR K M N N Q).
apply (proj1 (MmultILRSame (RCfield K) N (AdjointMatrixRC K N N Q) Q)).
apply H1.
Qed.

Lemma SingularValueRCHFrobeniusNorm : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M), RCFrobeniusNorm K (M + N) M A * RCFrobeniusNorm K (M + N) M A = MySumF2 (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n).
Proof.
move=> K M N A.
elim (proj2 (proj2 (SingularValueRCHNature K M N A))).
move=> U.
elim.
move=> V H1.
rewrite {2} (proj2 (proj2 H1)).
rewrite {1} (proj2 (proj2 H1)).
rewrite (UnitaryMatrixRCSaveRCFrobeniusNormL K (M + N) M U (proj1 H1)).
rewrite (UnitaryMatrixRCSaveRCFrobeniusNormStrongR K (M + N) M M (AdjointMatrixRC K M M V)).
unfold RCFrobeniusNorm.
rewrite - (proj2 (RCnNormNature K ((M + N) * M) (fun (m : Count ((M + N) * M)) => MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m0 : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m0))) (MO (RCfield K) N M) (fst (MultConnectInv (M + N) M m)) (snd (MultConnectInv (M + N) M m))))).
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count ((M + N) * M)) (FiniteIm (Count M) (Count ((M + N) * M)) (fun (m : Count M) => MultConnect (M + N) M (AddConnect M N (inl m), m)) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count ((M + N) * M))).
rewrite (CM_O_r (RCPCM K)).
apply (FiniteSetInduction (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
elim K.
reflexivity.
reflexivity.
move=> B b H2 H3 H4 H5.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite (RCReplus K).
rewrite H5.
unfold Basics.compose.
unfold MBlockH.
rewrite (proj1 (MultConnectInvRelation (M + N) M)).
rewrite (proj1 (AddConnectInvRelation M N)).
unfold MDiag.
simpl.
elim (Nat.eq_dec (proj1_sig b) (proj1_sig b)).
move=> H6.
suff: (forall (r : R), ConjugateRC K (IRRC K r) = IRRC K r).
move=> H7.
rewrite H7.
rewrite - (IRRCmult K).
suff: (forall (r : R), RCRe K (IRRC K r) = r).
move=> H8.
rewrite H8.
reflexivity.
move=> r.
elim K.
reflexivity.
apply (CmakeRe r 0).
move=> r.
elim K.
reflexivity.
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H7.
rewrite H7.
simpl.
apply CmakeRe.
move=> H7.
rewrite H7.
simpl.
unfold Conjugate.
unfold IRC.
rewrite CmakeIm.
rewrite CmakeIm.
apply Ropp_0.
elim.
reflexivity.
apply H4.
apply H4.
move=> u.
elim.
move=> u0.
unfold MBlockH.
rewrite - {1} (proj2 (MultConnectInvRelation (M + N) M) u0).
elim (MultConnectInv (M + N) M u0).
move=> u1 u2.
simpl.
rewrite - {1} (proj2 (AddConnectInvRelation M N) u1).
elim (AddConnectInv M N u1).
move=> u3.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig u3) (proj1_sig u2)).
move=> H2.
elim.
apply (Im_intro (Count M) (Count ((M + N) * M)) (Full_set (Count M)) (fun (m : Count M) => MultConnect (M + N) M (AddConnect M N (inl m), m)) u3).
apply (Full_intro (Count M) u3).
suff: (u3 = u2).
move=> H3.
rewrite H3.
reflexivity.
apply sig_map.
apply H2.
move=> H2 H3 H4.
apply (Fmul_O_l (RCfield K)).
move=> u3 H2 H3.
apply (Fmul_O_l (RCfield K)).
move=> u1 u2 H2 H3 H4.
suff: (u1 = snd (AddConnect M N (inl u1), u1)).
move=> H5.
rewrite H5.
rewrite - (proj1 (MultConnectInvRelation (M + N) M) (AddConnect M N (inl u1), u1)).
rewrite H4.
rewrite (proj1 (MultConnectInvRelation (M + N) M) (AddConnect M N (inl u2), u2)).
reflexivity.
reflexivity.
move=> u H2.
apply (Full_intro (Count ((M + N) * M)) u).
rewrite (AdjointMatrixRCInvolutive K M M V).
apply (proj1 (proj2 H1)).
Qed.

Lemma SingularValueRCHApproximateFrobeniusNorm : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M) (U : Matrix (RCfield K) (M + N) (M + N)) (V : Matrix (RCfield K) M M), UnitaryMatrixRC K (M + N) U -> UnitaryMatrixRC K M V -> A = Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (SingularValueRCH K M N A m))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)) -> forall (k : nat), (k <= M)%nat -> forall (H : MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n) >= 0), RCFrobeniusNorm K (M + N) M (Mplus (RCfield K) (M + N) M A (Mopp (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right _ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))))) = MySqrt (exist (fun (r : R) => r >= 0) (MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n)) H).
Proof.
move=> K M N A U V H1 H2 H3 k H4 H5.
suff: (Mplus (RCfield K) (M + N) M A (Mopp (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun m : {n : nat | (n < M)%nat} => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right _ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)))) = Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun m : {n : nat | (n < M)%nat} => match excluded_middle_informative (proj1_sig m >= k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right _ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))).
move=> H6.
rewrite H6.
rewrite (UnitaryMatrixRCSaveRCFrobeniusNormL K (M + N) M U H1).
rewrite (UnitaryMatrixRCSaveRCFrobeniusNormStrongR K (M + N) M M (AdjointMatrixRC K M M V)).
apply RCnNormNature2.
apply conj.
apply (proj1 (MySqrtNature (exist (fun (r : R) => r >= 0) (MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n)) H5))).
suff: (MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n) = MySqrt (exist (fun (r : R) => r >= 0) (MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n)) H5) * MySqrt (exist (fun (r : R) => r >= 0) (MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n)) H5)).
move=> H7.
rewrite - H7.
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count ((M + N) * M)) (FiniteIm (Count M) (Count ((M + N) * M)) (fun (m : Count M) => MultConnect (M + N) M (AddConnect M N (inl m), m)) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count ((M + N) * M))).
rewrite (CM_O_r (RCPCM K)).
apply (FiniteSetInduction (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
elim K.
reflexivity.
reflexivity.
move=> B b H8 H9 H10 H11.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (RCReplus K).
rewrite H11.
unfold Basics.compose.
unfold MBlockH.
rewrite (proj1 (MultConnectInvRelation (M + N) M)).
simpl.
rewrite (proj1 (AddConnectInvRelation M N) (inl b)).
unfold MDiag.
elim (Nat.eq_dec (proj1_sig b) (proj1_sig b)).
move=> H12.
elim (excluded_middle_informative (proj1_sig b >= k)%nat).
move=> H13.
suff: (forall (r : R), ConjugateRC K (IRRC K r) = IRRC K r).
move=> H14.
rewrite (H14 (SingularValueRCH K M N A b)).
rewrite - (IRRCmult K (SingularValueRCH K M N A b) (SingularValueRCH K M N A b)).
suff: (forall (r : R), RCRe K (IRRC K r) = r).
move=> H15.
rewrite H15.
reflexivity.
move=> r.
elim K.
reflexivity.
apply (CmakeRe r 0).
move=> r.
elim K.
reflexivity.
apply functional_extensionality.
move=> n.
elim (CReorCIm n).
move=> H14.
rewrite H14.
apply (CmakeRe (IRRC CK r CRe)).
move=> H14.
rewrite H14.
simpl.
unfold Conjugate.
unfold IRC.
rewrite (CmakeIm (Cmake r 0 CRe) (- Cmake r 0 CIm)).
rewrite (CmakeIm r 0).
apply Ropp_0.
elim H9.
move=> u H13 H14 H15.
elim (H15 H13).
elim.
reflexivity.
apply H10.
apply H10.
move=> u.
elim.
move=> u0.
unfold MBlockH.
rewrite - {1} (proj2 (MultConnectInvRelation (M + N) M) u0).
elim (MultConnectInv (M + N) M u0).
move=> u1 u2.
simpl.
rewrite - {1} (proj2 (AddConnectInvRelation M N) u1).
elim (AddConnectInv M N u1).
move=> u3 H8 H9.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig u3) (proj1_sig u2)).
move=> H10.
elim (excluded_middle_informative (proj1_sig u3 >= k)%nat).
move=> H11.
elim H8.
apply (Im_intro (Count M) (Count ((M + N) * M)) (Intersection (Count M) (fun (n : Count M) => (proj1_sig n >= k)%nat) (Full_set (Count M))) (fun (m : Count M) => MultConnect (M + N) M (AddConnect M N (inl m), m)) u3).
apply (Intersection_intro (Count M) (fun (n : Count M) => (proj1_sig n >= k)%nat) (Full_set (Count M)) u3).
apply H11.
apply (Full_intro (Count M) u3).
suff: (u3 = u2).
move=> H12.
rewrite H12.
reflexivity.
apply sig_map.
apply H10.
move=> H11.
apply (Fmul_O_l (RCfield K)).
move=> H10.
apply (Fmul_O_l (RCfield K)).
move=> u3 H8 H9.
apply (Fmul_O_l (RCfield K)).
move=> u1 u2 H8 H9 H10.
suff: ((AddConnect M N (inl u1), u1) = (AddConnect M N (inl u2), u2)).
move=> H11.
suff: (u1 = snd (AddConnect M N (inl u1), u1)).
move=> H12.
rewrite H12.
rewrite H11.
reflexivity.
reflexivity.
rewrite - (proj1 (MultConnectInvRelation (M + N) M) (AddConnect M N (inl u1), u1)).
rewrite H10.
apply (proj1 (MultConnectInvRelation (M + N) M) (AddConnect M N (inl u2), u2)).
move=> u H8.
apply (Full_intro (Count ((M + N) * M)) u).
apply (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n)) H5))).
rewrite (AdjointMatrixRCInvolutive K).
apply H2.
rewrite - (Mplus_O_l (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m >= k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right _ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)))).
rewrite (Mplus_comm (RCfield K) (M + N) M (MO (RCfield K) (M + N) M)).
rewrite - (Mplus_opp_r (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right _ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)))).
rewrite - (Mplus_assoc (RCfield K) (M + N) M).
suff: (A = Mplus (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m >= k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right _ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))) (Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right _ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)))).
move=> H6.
rewrite {1} H6.
reflexivity.
rewrite - (Mmult_plus_distr_l (RCfield K) (M + N) (M + N) M).
rewrite - (Mmult_plus_distr_r (RCfield K) (M + N) M M).
suff: (Mplus (RCfield K) (M + N) M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m >= k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right _ => RCO K
end)) (MO (RCfield K) N M)) (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right _ => RCO K
end)) (MO (RCfield K) N M)) = MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun m : {n : nat | (n < M)%nat} => IRRC K (SingularValueRCH K M N A m))) (MO (RCfield K) N M)).
move=> H6.
rewrite H6.
apply H3.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mplus.
unfold MBlockH.
elim (AddConnectInv M N x).
move=> x0.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y)).
move=> H6.
elim (excluded_middle_informative (proj1_sig x0 >= k)%nat).
move=> H7.
elim (excluded_middle_informative (proj1_sig x0 < k)%nat).
move=> H8.
elim (le_not_lt k (proj1_sig x0) H7 H8).
move=> H8.
apply (Fadd_O_r (RCfield K)).
move=> H7.
elim (excluded_middle_informative (proj1_sig x0 < k)%nat).
move=> H8.
apply (Fadd_O_l (RCfield K)).
move=> H8.
elim (le_or_lt k (proj1_sig x0)).
move=> H9.
elim (H7 H9).
move=> H9.
elim (H8 H9).
move=> H6.
apply (Fadd_O_l (RCfield K)).
move=> x0.
apply (Fadd_O_l (RCfield K)).
Qed.

Lemma SingularValueRCHRankRelation : forall (K : RC) (M N : nat) (k : nat), (k <= M)%nat -> forall (A : Matrix (RCfield K) (M + N) M), Rank (RCfield K) (M + N) M A = k <-> forall (m : Count M), (((proj1_sig m < k)%nat -> SingularValueRCH K M N A m > 0) /\ ((proj1_sig m >= k)%nat -> SingularValueRCH K M N A m = 0)).
Proof.
move=> K M N k H1 A.
elim (proj2 (proj2 (SingularValueRCHNature K M N A))).
move=> U.
elim.
move=> V H2.
suff: (Rank (RCfield K) (M + N) M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))) (MO (RCfield K) N M)) = Rank (RCfield K) (M + N) M A).
move=> H3.
rewrite - H3.
apply conj.
move=> H4 m.
apply conj.
move=> H5.
elim (proj1 (SingularValueRCHNature K M N A) m).
apply.
move=> H6.
elim (lt_irrefl k).
rewrite - {1} H4.
apply (le_trans (S (Rank (RCfield K) (M + N) M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) l))) (MO (RCfield K) N M)))) (S (proj1_sig m)) k).
apply le_n_S.
rewrite - (RankNormalFormRank (RCfield K) M M (proj1_sig m)).
suff: (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) l))) (MO (RCfield K) N M) = Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) l))) (MO (RCfield K) N M)) (RankNormalForm (RCfield K) M M (proj1_sig m))).
move=> H7.
rewrite H7.
apply (RankMultLeL (RCfield K) (M + N) M M).
rewrite MBlockHMult.
rewrite MDiagMult.
apply functional_extensionality.
move=> p.
apply functional_extensionality.
move=> q.
unfold MBlockH.
elim (AddConnectInv M N p).
move=> p0.
unfold MDiag.
unfold RankNormalForm.
elim (Nat.eq_dec (proj1_sig p0) (proj1_sig q)).
move=> H7.
elim (excluded_middle_informative (proj1_sig p0 < proj1_sig m)%nat).
move=> H8.
simpl.
rewrite (RCmult_comm K).
rewrite (RCmult_1_l K).
reflexivity.
move=> H8.
elim (proj1 (SingularValueRCHNature K M N A) p0).
move=> H9.
elim (Rge_not_gt (proj1_sig (SingularValueRCHSig K M N A) p0) (proj1_sig (SingularValueRCHSig K M N A) m)).
apply (proj1 (proj2 (SingularValueRCHNature K M N A)) m p0).
elim (le_or_lt (proj1_sig m) (proj1_sig p0)).
apply.
move=> H10.
elim (H8 H10).
rewrite H6.
apply H9.
move=> H9.
rewrite H9.
rewrite (Fmul_O_r (RCfield K)).
elim K.
reflexivity.
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H10.
rewrite H10.
apply (CmakeRe 0 0).
move=> H10.
rewrite H10.
apply (CmakeIm 0 0).
move=> H7.
reflexivity.
move=> p0.
rewrite (Mmult_O_l (RCfield K)).
reflexivity.
apply (lt_le_weak (proj1_sig m) M (proj2_sig m)).
apply (lt_le_weak (proj1_sig m) M (proj2_sig m)).
apply H5.
move=> H5.
elim (proj1 (SingularValueRCHNature K M N A) m).
move=> H6.
elim (lt_irrefl k).
rewrite - {2} H4.
suff: (S k = Rank (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) l))) (MO (RCfield K) N M)) (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig l < S k)%nat with
  | left _ => IRRC K (/ proj1_sig (SingularValueRCHSig K M N A) l)
  | right _ => RCO K
end)))).
unfold lt.
move=> H7.
rewrite H7.
apply (RankMultLeR (RCfield K) (M + N) M M).
suff: (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) l))) (MO (RCfield K) N M)) (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig l < S k)%nat with
  | left _ => IRRC K (/ proj1_sig (SingularValueRCHSig K M N A) l)
  | right _ => RCO K
end)) = RankNormalForm (RCfield K) (M + N) M (S k)).
move=> H7.
rewrite H7.
rewrite (RankNormalFormRank (RCfield K) (M + N) M (S k)).
reflexivity.
apply (le_trans (S k) M (M + N)).
apply (le_trans (S k) (S (proj1_sig m)) M (le_n_S k (proj1_sig m) H5) (proj2_sig m)).
apply (le_plus_l M N).
apply (le_trans (S k) (S (proj1_sig m)) M (le_n_S k (proj1_sig m) H5) (proj2_sig m)).
rewrite MBlockHMult.
rewrite MDiagMult.
rewrite Mmult_O_l.
apply functional_extensionality.
move=> p.
apply functional_extensionality.
move=> q.
unfold MBlockH.
rewrite - {2} (proj2 (AddConnectInvRelation M N) p).
elim (AddConnectInv M N p).
move=> p0.
unfold MDiag.
unfold RankNormalForm.
rewrite - (proj1 (AddConnectNature M N) p0).
elim (Nat.eq_dec (proj1_sig p0) (proj1_sig q)).
move=> H7.
elim (excluded_middle_informative (proj1_sig p0 < S k)%nat).
move=> H8.
simpl.
rewrite - (IRRCmult K).
rewrite Rinv_r.
elim K.
reflexivity.
reflexivity.
move=> H9.
apply (Rge_not_gt (proj1_sig (SingularValueRCHSig K M N A) m) (proj1_sig (SingularValueRCHSig K M N A) p0)).
apply (proj1 (proj2 (SingularValueRCHNature K M N A)) p0 m).
apply (le_trans (proj1_sig p0) k (proj1_sig m)).
apply (le_S_n (proj1_sig p0) k H8).
apply H5.
rewrite H9.
apply H6.
move=> H8.
rewrite (Fmul_O_r (RCfield K)).
reflexivity.
move=> H7.
reflexivity.
move=> p0.
unfold RankNormalForm.
rewrite - (proj2 (AddConnectNature M N) p0).
elim (Nat.eq_dec (M + proj1_sig p0) (proj1_sig q)).
move=> H7.
elim (lt_irrefl M).
apply (le_trans (S M) (S (M + proj1_sig p0)) M).
apply (le_n_S M (M + proj1_sig p0) (le_plus_l M (proj1_sig p0))).
rewrite H7.
apply (proj2_sig q).
move=> H7.
reflexivity.
apply.
move=> H4.
rewrite - (RankNormalFormRank (RCfield K) (M + N) M k).
suff: (RankNormalForm (RCfield K) (M + N) M k = Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))) (MO (RCfield K) N M)) (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (/ proj1_sig (SingularValueRCHSig K M N A) m)
  | right _ => RCI K
end))).
move=> H5.
rewrite H5.
rewrite (RankElementaryTransformableR (RCfield K) (M + N) M).
reflexivity.
apply (proj2 (ElementaryTransformableRegular (RCfield K) M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (/ proj1_sig (SingularValueRCHSig K M N A) m)
  | right _ => RCI K
end)))).
apply (proj2 (RegularInvRExistRelation (RCfield K) M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (/ proj1_sig (SingularValueRCHSig K M N A) m)
  | right _ => RCI K
end)))).
exists (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m)
  | right _ => RCI K
end)).
rewrite MDiagMult.
apply functional_extensionality.
move=> p.
apply functional_extensionality.
move=> q.
unfold MDiag.
unfold MI.
elim (Nat.eq_dec (proj1_sig p) (proj1_sig q)).
move=> H6.
elim (excluded_middle_informative (proj1_sig p < k)%nat).
move=> H7.
simpl.
rewrite - (IRRCmult K).
rewrite Rinv_l.
elim K.
reflexivity.
reflexivity.
move=> H8.
apply (Rgt_not_eq (SingularValueRCH K M N A p) 0 (proj1 (H4 p) H7) H8).
move=> H7.
apply (Fmul_I_l (RCfield K)).
move=> H6.
reflexivity.
rewrite MBlockHMult.
rewrite MDiagMult.
apply functional_extensionality.
move=> p.
apply functional_extensionality.
move=> q.
unfold MBlockH.
rewrite - {1} (proj2 (AddConnectInvRelation M N) p).
elim (AddConnectInv M N p).
move=> p0.
unfold RankNormalForm.
unfold MDiag.
rewrite - (proj1 (AddConnectNature M N) p0).
elim (Nat.eq_dec (proj1_sig p0) (proj1_sig q)).
move=> H5.
elim (excluded_middle_informative (proj1_sig p0 < k)%nat).
move=> H6.
simpl.
rewrite - (IRRCmult K).
rewrite Rinv_r.
elim K.
reflexivity.
reflexivity.
apply (Rgt_not_eq (SingularValueRCH K M N A p0) 0 (proj1 (H4 p0) H6)).
move=> H6.
suff: (proj1_sig (SingularValueRCHSig K M N A) p0 = SingularValueRCH K M N A p0).
move=> H7.
rewrite H7.
rewrite (proj2 (H4 p0)).
rewrite (Fmul_I_r (RCfield K)).
elim K.
reflexivity.
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H8.
rewrite H8.
simpl.
unfold IRC.
rewrite (CmakeRe 0 0).
reflexivity.
move=> H8.
rewrite H8.
simpl.
unfold IRC.
rewrite (CmakeIm 0 0).
reflexivity.
elim (le_or_lt k (proj1_sig p0)).
apply.
move=> H8.
elim (H6 H8).
reflexivity.
move=> H5.
reflexivity.
move=> p0.
unfold RankNormalForm.
rewrite (Mmult_O_l (RCfield K) N M M).
rewrite - (proj2 (AddConnectNature M N) p0).
elim (Nat.eq_dec (M + proj1_sig p0) (proj1_sig q)).
move=> H5.
elim (excluded_middle_informative (M + proj1_sig p0 < k)%nat).
move=> H6.
elim (lt_irrefl k).
apply (le_trans (S k) (S M) k).
apply (le_n_S k M H1).
apply (le_trans (S M) (S (M + proj1_sig p0)) k).
apply (le_n_S M (M + proj1_sig p0) (le_plus_l M (proj1_sig p0))).
apply H6.
move=> H6.
reflexivity.
move=> H5.
reflexivity.
apply (le_trans k M (M + N) H1 (le_plus_l M N)).
apply H1.
rewrite {3} (proj2 (proj2 H2)).
rewrite (RankElementaryTransformableL (RCfield K) (M + N) M).
rewrite (RankElementaryTransformableR (RCfield K) (M + N) M).
reflexivity.
apply (proj2 (ElementaryTransformableRegular (RCfield K) M (AdjointMatrixRC K M M V))).
apply (proj2 (RegularInvRExistRelation (RCfield K) M (AdjointMatrixRC K M M V))).
exists V.
apply (proj1 (proj2 H2)).
apply (proj2 (ElementaryTransformableRegular (RCfield K) (M + N) U)).
apply (proj2 (RegularInvLExistRelation (RCfield K) (M + N) U)).
exists (AdjointMatrixRC K (M + N) (M + N) U).
apply (proj1 H2).
Qed.

Lemma SingularValueRCHApproximateFrobeniusNorm_exists : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M) (U : Matrix (RCfield K) (M + N) (M + N)) (V : Matrix (RCfield K) M M), UnitaryMatrixRC K (M + N) U -> UnitaryMatrixRC K M V -> A = Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun m : {n : nat | (n < M)%nat} => IRRC K (SingularValueRCH K M N A m))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)) -> forall (k : nat), (k <= M)%nat -> exists (H : MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n) >= 0), RCFrobeniusNorm K (M + N) M (Mplus (RCfield K) (M + N) M A (Mopp (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun m : {n : nat | (n < M)%nat} => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right _ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))))) = MySqrt (exist (fun (r : R) => r >= 0) (MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n)) H).
Proof.
move=> K M N A U V H1 H2 H3 k H4.
suff: (MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n) >= 0).
move=> H5.
exists H5.
apply (SingularValueRCHApproximateFrobeniusNorm K M N A U V H1 H2 H3 k H4).
apply MySumF2Induction.
apply conj.
right.
reflexivity.
move=> cm u H5 H6.
rewrite - (Rplus_0_l 0).
apply (Rplus_ge_compat cm 0 (SingularValueRCH K M N A u * SingularValueRCH K M N A u) 0 H6).
apply Formula_1_3.
Qed.

Lemma UnitaryMarixRCComplementExists : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M), Mmult (RCfield K) M (M + N) M (AdjointMatrixRC K (M + N) M A) A = MI (RCfield K) M -> exists (B : Matrix (RCfield K) (M + N) N), UnitaryMatrixRC K (M + N) (MBlockW (RCfield K) (M + N) M N A B).
Proof.
move=> K M N A H1.
suff: (SubspaceVS (RCfield K) (FnVS (RCfield K) (M + N)) (fun (x : RCn K (M + N)) => forall (m : Count M), RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) x = RCO K)).
move=> H2.
elim (Proposition_5_9_1_1 (RCfield K) (FnVS (RCfield K) (M + N)) (FnVSFiniteDimension (RCfield K) (M + N)) (fun (x : RCn K (M + N)) => forall (m : Count M), RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) x = RCO K) H2).
move=> L H3.
suff: (L = N).
move=> H4.
elim H3.
rewrite H4.
move=> F H5.
elim (GramSchmidtLinearlyIndepententRC K (FnVS (RCfield K) (M + N)) (RCnInner_Product_Space K (M + N)) N (fun (m : Count N) => proj1_sig (F m))).
move=> G H6.
suff: (forall (m : Count M) (n : Count N), RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) (G n) = RCO K).
move=> H7.
exists (MTranspose (RCfield K) N (M + N) G).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite - (proj2 (AddConnectInvRelation M N) x).
rewrite - (proj2 (AddConnectInvRelation M N) y).
elim (AddConnectInv M N x).
move=> x0.
elim (AddConnectInv M N y).
move=> y0.
unfold Mmult.
suff: (MI (RCfield K) (M + N) (AddConnect M N (inl x0)) (AddConnect M N (inl y0)) = MI (RCfield K) M x0 y0).
move=> H8.
rewrite H8.
rewrite - H1.
apply MySumF2Same.
move=> u H9.
unfold MBlockW.
unfold AdjointMatrixRC.
rewrite (proj1 (AddConnectInvRelation M N) (inl x0)).
rewrite (proj1 (AddConnectInvRelation M N) (inl y0)).
reflexivity.
unfold MI.
rewrite - (proj1 (AddConnectNature M N) x0).
rewrite - (proj1 (AddConnectNature M N) y0).
reflexivity.
move=> y0.
unfold MI.
rewrite - (proj1 (AddConnectNature M N) x0).
rewrite - (proj2 (AddConnectNature M N) y0).
elim (Nat.eq_dec (proj1_sig x0) (M + proj1_sig y0)).
move=> H8.
elim (lt_irrefl (proj1_sig x0)).
rewrite {2} H8.
apply (le_trans (S (proj1_sig x0)) M (M + proj1_sig y0) (proj2_sig x0) (le_plus_l M (proj1_sig y0))).
move=> H8.
simpl.
rewrite - (ConjugateRCO K).
rewrite - (H7 x0 y0).
unfold RCnInnerProduct.
unfold Mmult.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < M + N)%nat} (exist (Finite {n : nat | (n < M + N)%nat}) (Full_set {n : nat | (n < M + N)%nat}) (CountFinite (M + N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite (ConjugateRCO K).
reflexivity.
move=> B b H9 H10 H11 H12.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H12.
unfold MBlockW.
unfold AdjointMatrixRC.
rewrite (proj1 (AddConnectInvRelation M N) (inl x0)).
rewrite (proj1 (AddConnectInvRelation M N) (inr y0)).
simpl.
rewrite (Proposition_4_8_1_1_RC K).
rewrite (Proposition_4_8_2_RC K).
rewrite (ConjugateRCInvolutive K).
reflexivity.
apply H11.
apply H11.
move=> x0.
elim (AddConnectInv M N y).
move=> y0.
unfold MI.
rewrite - (proj2 (AddConnectNature M N) x0).
rewrite - (proj1 (AddConnectNature M N) y0).
elim (Nat.eq_dec (M + proj1_sig x0) (proj1_sig y0)).
move=> H8.
elim (lt_irrefl (M + proj1_sig x0)).
rewrite {1} H8.
apply (le_trans (S (proj1_sig y0)) M (M + proj1_sig x0) (proj2_sig y0) (le_plus_l M (proj1_sig x0))).
move=> H8.
simpl.
rewrite - (H7 y0 x0).
apply (MySumF2Same (Count (M + N)) (exist (Finite (Count (M + N))) (Full_set (Count (M + N))) (CountFinite (M + N))) (RCPCM K)).
move=> u H9.
unfold MBlockW.
unfold AdjointMatrixRC.
rewrite (proj1 (AddConnectInvRelation M N) (inr x0)).
rewrite (proj1 (AddConnectInvRelation M N) (inl y0)).
rewrite (RCmult_comm K).
reflexivity.
move=> y0.
unfold MI.
rewrite - (proj2 (AddConnectNature M N) x0).
rewrite - (proj2 (AddConnectNature M N) y0).
elim (Nat.eq_dec (M + proj1_sig x0) (M + proj1_sig y0)).
move=> H8.
suff: (x0 = y0).
move=> H9.
rewrite H9.
simpl.
rewrite - (proj1 (proj1 H6) y0).
apply (MySumF2Same (Count (M + N)) (exist (Finite (Count (M + N))) (Full_set (Count (M + N))) (CountFinite (M + N))) (RCPCM K)).
move=> u H10.
unfold MBlockW.
unfold AdjointMatrixRC.
rewrite (proj1 (AddConnectInvRelation M N) (inr y0)).
rewrite (RCmult_comm K (G y0 u) (ConjugateRC K (G y0 u))).
reflexivity.
apply sig_map.
apply (plus_reg_l (proj1_sig x0) (proj1_sig y0) M H8).
move=> H8.
simpl.
rewrite - (proj2 (proj1 H6) y0 x0).
apply (MySumF2Same (Count (M + N)) (exist (Finite (Count (M + N))) (Full_set (Count (M + N))) (CountFinite (M + N))) (RCPCM K)).
move=> u H9.
unfold MBlockW.
unfold AdjointMatrixRC.
rewrite (proj1 (AddConnectInvRelation M N) (inr x0)).
rewrite (proj1 (AddConnectInvRelation M N) (inr y0)).
rewrite (RCmult_comm K (G y0 u) (ConjugateRC K (G x0 u))).
reflexivity.
move=> H9.
apply H8.
rewrite H9.
reflexivity.
move=> m n.
suff: (In (RCn K (M + N)) (fun (x : RCn K (M + N)) => forall (m : Count M), RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) x = RCO K) (G n)).
move=> H7.
apply (H7 m).
suff: (In (RCn K (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count N) (fun (m : Count N) => proj1_sig (F m))) (G n)).
elim.
move=> x H7.
rewrite H7.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (fun (t : Count N) => proj1_sig x t <> FO (RCfield K)) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 H2)).
move=> B b H8 H9 H10 H11.
rewrite MySumF2Add.
apply (proj1 H2).
apply H11.
apply (proj1 (proj2 H2)).
apply (proj2_sig (F b)).
apply H10.
rewrite (proj2 H6).
apply (SpanContainSelfVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count N) G n).
apply (SubspaceBasisLinearlyIndependentVS (RCfield K) (FnVS (RCfield K) (M + N)) (fun (x : RCn K (M + N)) => forall (m : Count M), RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) x = RCO K) H2 (Count N) (fun (m : Count N) => proj1_sig (F m))).
exists (fun (m : Count N) => proj2_sig (F m)).
apply H5.
apply (plus_reg_l L N M).
elim H3.
move=> F H4.
elim (DimensionVSNature2 (RCfield K) (FnVS (RCfield K) (M + N)) (FnVSFiniteDimension (RCfield K) (M + N)) (M + L) (fun (m : Count (M + L)) => match AddConnectInv M L m with
  | inl m0 => MTranspose (RCfield K) (M + N) M A m0
  | inr m0 => proj1_sig (F m0)
end)).
elim (FnVSDimension (RCfield K) (M + N)).
move=> H5.
suff: (H5 = FnVSFiniteDimension (RCfield K) (M + N)).
move=> H6.
rewrite H6.
apply.
apply proof_irrelevance.
apply (proj2 (BasisLIGeVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (M + L)) (fun (m : Count (M + L)) => match AddConnectInv M L m with
  | inl m0 => MTranspose (RCfield K) (M + N) M A m0
  | inr m0 => proj1_sig (F m0)
end))).
apply conj.
apply (proj2 (FiniteLinearlyIndependentVS (RCfield K) (FnVS (RCfield K) (M + N)) (M + L) (fun (m : Count (M + L)) => match AddConnectInv M L m with
  | inl m0 => MTranspose (RCfield K) (M + N) M A m0
  | inr m0 => proj1_sig (F m0)
end))).
move=> a.
rewrite (MySumF2Included (Count (M + L)) (FiniteIm (Count M) (Count (M + L)) (fun (m : Count M) => AddConnect M L (inl m)) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2Included (Count (M + L)) (FiniteIm (Count L) (Count (M + L)) (fun (m : Count L) => AddConnect M L (inr m)) (exist (Finite (Count L)) (Full_set (Count L)) (CountFinite L)))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count (M + L))).
rewrite CM_O_r.
move=> H5.
suff: (forall (m : Count M), a (AddConnect M L (inl m)) = RCO K).
move=> H6 m.
rewrite - (proj2 (AddConnectInvRelation M L) m).
elim (AddConnectInv M L m).
apply H6.
move=> m0.
suff: (LinearlyIndependentVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count L) (fun (m : Count L) => proj1_sig (F m))).
move=> H7.
apply (proj1 (FiniteLinearlyIndependentVS (RCfield K) (FnVS (RCfield K) (M + N)) L (fun (m : Count L) => proj1_sig (F m))) H7 (fun (m : Count L) => a (AddConnect M L (inr m)))).
suff: (CMc (VSPCM (RCfield K) (FnVS (RCfield K) (M + N))) (MySumF2 (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (VSPCM (RCfield K) (FnVS (RCfield K) (M + N))) (Basics.compose (fun (n : Count (M + L)) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) (a n) match AddConnectInv M L n with
  | inl m0 => MTranspose (RCfield K) (M + N) M A m0
  | inr m0 => proj1_sig (F m0)
end) (fun (m : Count M) => AddConnect M L (inl m)))) (MySumF2 (Count L) (exist (Finite (Count L)) (Full_set (Count L)) (CountFinite L)) (VSPCM (RCfield K) (FnVS (RCfield K) (M + N))) (Basics.compose (fun (n : Count (M + L)) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) (a n) match AddConnectInv M L n with
  | inl m0 => MTranspose (RCfield K) (M + N) M A m0
  | inr m0 => proj1_sig (F m0)
end) (fun (m : Count L) => AddConnect M L (inr m)))) = VO (RCfield K) (FnVS (RCfield K) (M + N))).
rewrite (MySumF2O (Count M)).
rewrite CM_comm.
rewrite CM_O_r.
suff: ((Basics.compose (fun (n : Count (M + L)) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) (a n) match AddConnectInv M L n with
  | inl m1 => MTranspose (RCfield K) (M + N) M A m1
  | inr m1 => proj1_sig (F m1)
end) (fun (m1 : Count L) => AddConnect M L (inr m1))) = (fun (n : Count L) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) (a (AddConnect M L (inr n))) (proj1_sig (F n)))).
move=> H8.
rewrite H8.
apply.
apply functional_extensionality.
move=> k.
unfold Basics.compose.
rewrite (proj1 (AddConnectInvRelation M L) (inr k)).
reflexivity.
move=> u H8.
unfold Basics.compose.
rewrite (proj1 (AddConnectInvRelation M L) (inl u)).
apply functional_extensionality.
move=> x.
rewrite (H6 u).
apply (Fmul_O_l (RCfield K)).
apply H5.
apply (SubspaceBasisLinearlyIndependentVS (RCfield K) (FnVS (RCfield K) (M + N)) (fun (x : RCn K (M + N)) => forall (m : Count M), RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) x = RCO K) H2 (Count L) (fun (m : Count L) => proj1_sig (F m))).
exists (fun (m : Count L) => proj2_sig (F m)).
apply H4.
move=> m.
suff: (RCO K = RCnInnerProduct K (M + N) (VO (RCfield K) (FnVS (RCfield K) (M + N))) (MTranspose (RCfield K) (M + N) M A m)).
move=> H6.
rewrite H6.
rewrite - H5.
simpl.
rewrite (Proposition_4_2_1_1 K).
rewrite - (Fadd_O_r (RCfield K) (a (AddConnect M L (inl m)))).
suff: (a (AddConnect M L (inl m)) = RCnInnerProduct K (M + N) (MySumF2 (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (VSPCM (RCfield K) (FnVS (RCfield K) (M + N))) (Basics.compose (fun (n : Count (M + L)) => Fnmul (RCfield K) (M + N) (a n) match AddConnectInv M L n with
  | inl m0 => MTranspose (RCfield K) (M + N) M A m0
  | inr m0 => proj1_sig (F m0)
end) (fun (m0 : Count M) => AddConnect M L (inl m0)))) (MTranspose (RCfield K) (M + N) M A m)).
move=> H7.
rewrite H7.
apply (Fadd_eq_compat_l (RCfield K)).
apply (FiniteSetInduction (Count L) (exist (Finite (Count L)) (Full_set (Count L)) (CountFinite L))).
apply conj.
rewrite MySumF2Empty.
suff: (RCnInnerProduct K (M + N) (CMe (VSPCM (RCfield K) (FnVS (RCfield K) (M + N)))) (MTranspose (RCfield K) (M + N) M A m) = FO (RCfield K)).
move=> H8.
rewrite H8.
reflexivity.
apply (RCip_mult_0_l K (FnVS (RCfield K) (M + N)) (RCnInner_Product_Space K (M + N))).
move=> B b H8 H9 H10 H11.
rewrite MySumF2Add.
rewrite (Proposition_4_2_1_1 K).
rewrite - H11.
unfold Basics.compose.
rewrite (proj1 (AddConnectInvRelation M L) (inr b)).
rewrite (Proposition_4_2_2_1 K).
rewrite (Proposition_4_2_3 K).
rewrite (proj2_sig (F b) m).
rewrite (ConjugateRCO K).
suff: (RCmult K (a (AddConnect M L (inr b))) (RCO K) = RCO K).
move=> H12.
rewrite H12.
simpl.
rewrite (RCplus_0_l K).
reflexivity.
apply (Fmul_O_r (RCfield K) (a (AddConnect M L (inr b)))).
apply H10.
rewrite - (Fadd_O_r (RCfield K) (a (AddConnect M L (inl m)))).
rewrite (MySumF2Included (Count M) (FiniteSingleton (Count M) m)).
rewrite (Proposition_4_2_1_1 K).
rewrite MySumF2Singleton.
unfold Basics.compose.
rewrite (proj1 (AddConnectInvRelation M L) (inl m)).
rewrite (Proposition_4_2_2_1 K).
suff: (forall (k l : Count M), RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A k) (MTranspose (RCfield K) (M + N) M A l) = ConjugateRC K (Mmult (RCfield K) M (M + N) M (AdjointMatrixRC K (M + N) M A) A k l)).
move=> H7.
rewrite (H7 m m).
rewrite H1.
unfold MI.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H8.
simpl.
rewrite (ConjugateRCI K).
rewrite (RCmult_comm K (a (AddConnect M L (inl m)))).
rewrite (RCmult_1_l K (a (AddConnect M L (inl m)))).
apply (Fadd_eq_compat_l (RCfield K)).
apply (FiniteSetInduction (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (Complement (Count M) (Singleton (Count M) m)))).
apply conj.
rewrite MySumF2Empty.
suff: (RCnInnerProduct K (M + N) (CMe (VSPCM (RCfield K) (FnVS (RCfield K) (M + N)))) (MTranspose (RCfield K) (M + N) M A m) = RCO K).
move=> H9.
rewrite H9.
reflexivity.
apply (RCip_mult_0_l K (FnVS (RCfield K) (M + N)) (RCnInner_Product_Space K (M + N))).
move=> B b H9 H10 H11 H12.
rewrite MySumF2Add.
rewrite (Proposition_4_2_1_1 K).
rewrite - H12.
rewrite (Proposition_4_2_2_1 K).
rewrite (proj1 (AddConnectInvRelation M L) (inl b)).
rewrite (H7 b m).
rewrite H1.
unfold MI.
elim (Nat.eq_dec (proj1_sig b) (proj1_sig m)).
elim H10.
move=> b0 H13 H14 H15.
elim H13.
suff: (b0 = m).
move=> H16.
rewrite H16.
apply (In_singleton (Count M) m).
apply sig_map.
apply H15.
move=> H13.
simpl.
rewrite (ConjugateRCO K).
suff: (RCmult K (a (AddConnect M L (inl b))) (RCO K) = RCO K).
move=> H14.
rewrite H14.
rewrite (RCplus_0_l K).
reflexivity.
apply (Fmul_O_r (RCfield K) (a (AddConnect M L (inl b)))).
apply H11.
elim.
reflexivity.
move=> k l.
apply (RCnInnerProductMatrix K (M + N)).
move=> u H7.
apply (Full_intro (Count M) u).
suff: (RCnInnerProduct K (M + N) (VO (RCfield K) (FnVS (RCfield K) (M + N))) (MTranspose (RCfield K) (M + N) M A m) = RCO K).
move=> H6.
rewrite H6.
reflexivity.
apply (RCip_mult_0_l K (FnVS (RCfield K) (M + N)) (RCnInner_Product_Space K (M + N))).
move=> u.
elim.
move=> u0 H5 H6.
suff: (In (Count (M + L)) (Complement (Count (M + L)) (proj1_sig (FiniteIm (Count L) (Count (M + L)) (fun (m : Count L) => AddConnect M L (inr m)) (exist (Finite (Count L)) (Full_set (Count L)) (CountFinite L))))) u0).
elim H6.
move=> u1.
rewrite - (proj2 (AddConnectInvRelation M L) u1).
elim (AddConnectInv M L u1).
move=> u2.
elim.
apply (Im_intro (Count M) (Count (M + L)) (Full_set (Count M)) (fun (m : Count M) => AddConnect M L (inl m)) u2).
apply (Full_intro (Count M) u2).
reflexivity.
move=> u2 H7 H8.
elim.
apply (Im_intro (Count L) (Count (M + L)) (Full_set (Count L)) (fun (m : Count L) => AddConnect M L (inr m)) u2).
apply (Full_intro (Count L) u2).
reflexivity.
apply H5.
move=> u1 u2 H5 H6 H7.
suff: (u1 = match AddConnectInv M L (AddConnect M L (inr u1)) with
  | inl _ => u1
  | inr u => u
end).
move=> H8.
rewrite H8.
rewrite H7.
rewrite (proj1 (AddConnectInvRelation M L) (inr u2)).
reflexivity.
rewrite (proj1 (AddConnectInvRelation M L) (inr u1)).
reflexivity.
move=> u.
elim.
move=> x H5 y H6.
apply (Intersection_intro (Count (M + L))).
move=> H7.
suff: (y = AddConnect M L (inr x)).
elim H7.
move=> z H8 w H9 H10.
suff: (match AddConnectInv M L w with
  | inl _ => False
  | inr _ => True
end).
rewrite H9.
rewrite (proj1 (AddConnectInvRelation M L) (inl z)).
apply.
rewrite H10.
rewrite (proj1 (AddConnectInvRelation M L) (inr x)).
apply I.
apply H6.
apply (Full_intro (Count (M + L)) y).
move=> u1 u2 H5 H6 H7.
suff: (u1 = match AddConnectInv M L (AddConnect M L (inl u1)) with
  | inl u => u
  | inr _ => u1
end).
move=> H8.
rewrite H8.
rewrite H7.
rewrite (proj1 (AddConnectInvRelation M L) (inl u2)).
reflexivity.
rewrite (proj1 (AddConnectInvRelation M L) (inl u1)).
reflexivity.
move=> u H5.
apply (Full_intro (Count (M + L)) u).
apply Extensionality_Ensembles.
apply conj.
move=> v H5.
suff: (exists (g : Count L -> RCT K), Vadd (RCfield K) (FnVS (RCfield K) (M + N)) (Vopp (RCfield K) (FnVS (RCfield K) (M + N)) (MySumF2 (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (VSPCM (RCfield K) (FnVS (RCfield K) (M + N))) (fun (m : Count M) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) (ConjugateRC K (RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) v)) (MTranspose (RCfield K) (M + N) M A m)))) v = MySumF2 (Count L) (exist (Finite (Count L)) (Full_set (Count L)) (CountFinite L)) (VSPCM (RCfield K) (FnVS (RCfield K) (M + N))) (fun (m : Count L) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) (g m) (proj1_sig (F m)))).
elim.
move=> g H6.
rewrite (FiniteSpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (M + L)).
exists (fun (m : Count (M + L)) => match AddConnectInv M L m with
  | inl m0 => ConjugateRC K (RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m0) v)
  | inr m0 => g m0
end).
rewrite (MySumF2Included (Count (M + L)) (FiniteIm (Count M) (Count (M + L)) (fun (m : Count M) => AddConnect M L (inl m)) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2Included (Count (M + L)) (FiniteIm (Count L) (Count (M + L)) (fun (m : Count L) => AddConnect M L (inr m)) (exist (Finite (Count L)) (Full_set (Count L)) (CountFinite L)))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count (M + L))).
rewrite CM_O_r.
unfold Basics.compose.
suff: ((fun (x : Count L) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) match AddConnectInv M L (AddConnect M L (inr x)) with
  | inl m0 => ConjugateRC K (RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m0) v)
  | inr m0 => g m0
end match AddConnectInv M L (AddConnect M L (inr x)) with
  | inl m0 => MTranspose (RCfield K) (M + N) M A m0
  | inr m0 => proj1_sig (F m0)
end) = (fun (m : Count L) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) (g m) (proj1_sig (F m)))).
move=> H7.
rewrite H7.
rewrite - H6.
suff: ((fun (x : Count M) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) match AddConnectInv M L (AddConnect M L (inl x)) with
  | inl m0 => ConjugateRC K (RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m0) v)
  | inr m0 => g m0
end match AddConnectInv M L (AddConnect M L (inl x)) with
  | inl m0 => MTranspose (RCfield K) (M + N) M A m0
  | inr m0 => proj1_sig (F m0)
end) = (fun (m : Count M) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) (ConjugateRC K (RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) v)) (MTranspose (RCfield K) (M + N) M A m))).
move=> H8.
rewrite H8.
simpl.
rewrite - (Fnadd_assoc (RCfield K) (M + N)).
rewrite (Fnadd_opp_r (RCfield K) (M + N)).
rewrite (Fnadd_O_l (RCfield K) (M + N)).
reflexivity.
apply functional_extensionality.
move=> m.
rewrite (proj1 (AddConnectInvRelation M L) (inl m)).
reflexivity.
apply functional_extensionality.
move=> m.
rewrite (proj1 (AddConnectInvRelation M L) (inr m)).
reflexivity.
move=> u.
elim.
move=> u0 H7 H8.
suff: (In (Count (M + L)) (Complement (Count (M + L)) (proj1_sig (FiniteIm (Count L) (Count (M + L)) (fun (m : Count L) => AddConnect M L (inr m)) (exist (Finite (Count L)) (Full_set (Count L)) (CountFinite L))))) u0).
elim H8.
move=> u1.
rewrite - (proj2 (AddConnectInvRelation M L) u1).
elim (AddConnectInv M L u1).
move=> u2.
elim.
apply (Im_intro (Count M) (Count (M + L)) (Full_set (Count M)) (fun (m : Count M) => AddConnect M L (inl m)) u2).
apply (Full_intro (Count M) u2).
reflexivity.
move=> u2 H9 H10.
elim.
apply (Im_intro (Count L) (Count (M + L)) (Full_set (Count L)) (fun (m : Count L) => AddConnect M L (inr m)) u2).
apply (Full_intro (Count L) u2).
reflexivity.
apply H7.
move=> u1 u2 H7 H8 H9.
suff: (u1 = match AddConnectInv M L (AddConnect M L (inr u1)) with
  | inl _ => u1
  | inr u => u
end).
move=> H10.
rewrite H10.
rewrite H9.
rewrite (proj1 (AddConnectInvRelation M L) (inr u2)).
reflexivity.
rewrite (proj1 (AddConnectInvRelation M L) (inr u1)).
reflexivity.
move=> u.
elim.
move=> x H7 y H8.
apply (Intersection_intro (Count (M + L))).
move=> H9.
suff: (y = AddConnect M L (inr x)).
elim H9.
move=> z H10 w H11 H12.
suff: (match AddConnectInv M L w with
  | inl _ => False
  | inr _ => True
end).
rewrite H11.
rewrite (proj1 (AddConnectInvRelation M L) (inl z)).
apply.
rewrite H12.
rewrite (proj1 (AddConnectInvRelation M L) (inr x)).
apply I.
apply H8.
apply (Full_intro (Count (M + L)) y).
move=> u1 u2 H7 H8 H9.
suff: (u1 = match AddConnectInv M L (AddConnect M L (inl u1)) with
  | inl u => u
  | inr _ => u1
end).
move=> H10.
rewrite H10.
rewrite H9.
rewrite (proj1 (AddConnectInvRelation M L) (inl u2)).
reflexivity.
rewrite (proj1 (AddConnectInvRelation M L) (inl u1)).
reflexivity.
move=> u H7.
apply (Full_intro (Count (M + L)) u).
suff: (forall (m : Count M), RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) (Vadd (RCfield K) (FnVS (RCfield K) (M + N)) (Vopp (RCfield K) (FnVS (RCfield K) (M + N)) (MySumF2 (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (VSPCM (RCfield K) (FnVS (RCfield K) (M + N))) (fun (m : Count M) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) (ConjugateRC K (RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) v)) (MTranspose (RCfield K) (M + N) M A m)))) v) = RCO K).
move=> H6.
elim (proj1 (FiniteBasisVS (RCfield K) (SubspaceMakeVS (RCfield K) (FnVS (RCfield K) (M + N)) (fun (x : RCn K (M + N)) => forall (m : Count M), RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) x = RCO K) H2) L F) H4 (exist (fun (x : RCn K (M + N)) => forall (m : Count M), RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) x = RCO K) (Vadd (RCfield K) (FnVS (RCfield K) (M + N)) (Vopp (RCfield K) (FnVS (RCfield K) (M + N)) (MySumF2 (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (VSPCM (RCfield K) (FnVS (RCfield K) (M + N))) (fun (m : Count M) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) (ConjugateRC K (RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) v)) (MTranspose (RCfield K) (M + N) M A m)))) v) H6)).
move=> g H7.
exists g.
suff: (Vadd (RCfield K) (FnVS (RCfield K) (M + N)) (Vopp (RCfield K) (FnVS (RCfield K) (M + N)) (MySumF2 (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (VSPCM (RCfield K) (FnVS (RCfield K) (M + N))) (fun (m : Count M) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) (ConjugateRC K (RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) v)) (MTranspose (RCfield K) (M + N) M A m)))) v = proj1_sig (exist (fun (x : RCn K (M + N)) => forall (m : Count M), RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) x = RCO K) (Vadd (RCfield K) (FnVS (RCfield K) (M + N)) (Vopp (RCfield K) (FnVS (RCfield K) (M + N)) (MySumF2 (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (VSPCM (RCfield K) (FnVS (RCfield K) (M + N))) (fun (m : Count M) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) (ConjugateRC K (RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) v)) (MTranspose (RCfield K) (M + N) M A m)))) v) H6)).
move=> H8.
rewrite H8.
rewrite (proj1 H7).
apply (FiniteSetInduction (Count L) (exist (Finite (Count L)) (Full_set (Count L)) (CountFinite L))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H9 H10 H11 H12.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H12.
reflexivity.
apply H11.
apply H11.
reflexivity.
move=> m.
suff: (RCnInnerProduct K (M + N) = RCip K (FnVS (RCfield K) (M + N)) (RCnInner_Product_Space K (M + N))).
move=> H6.
rewrite {1} H6.
rewrite (RCip_linear_plus_r K).
rewrite (RCip_linear_opp_r K).
rewrite (MySumF2Included (Count M) (FiniteSingleton (Count M) m)).
rewrite (RCip_linear_plus_r K).
rewrite MySumF2Singleton.
rewrite (RCip_linear_mult_r K).
simpl.
rewrite (ConjugateRCInvolutive K).
rewrite (RCnInnerProductMatrix K (M + N) (MTranspose (RCfield K) (M + N) M A m) (MTranspose (RCfield K) (M + N) M A m)).
suff: (Mmult (RCfield K) 1 (M + N) 1 (AdjointMatrixRC K (M + N) 1 (MVectorToMatrix (RCfield K) (M + N) (MTranspose (RCfield K) (M + N) M A m))) (MVectorToMatrix (RCfield K) (M + N) (MTranspose (RCfield K) (M + N) M A m)) Single Single = Mmult (RCfield K) M (M + N) M (AdjointMatrixRC K (M + N) M A) A m m).
move=> H7.
rewrite H7.
rewrite H1.
unfold MI.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H8.
simpl.
rewrite (ConjugateRCI K).
rewrite (RCmult_comm K).
rewrite (RCmult_1_l K).
suff: (RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) (MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (Complement (Count M) (Singleton (Count M) m))) (VSPCM (RCfield K) (FnVS (RCfield K) (M + N))) (fun (k : Count M) => Fnmul (RCfield K) (M + N) (ConjugateRC K (RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A k) v)) (MTranspose (RCfield K) (M + N) M A k))) = RCO K).
move=> H9.
rewrite H9.
rewrite (RCplus_comm K (RCnInnerProduct K (M + N) (MTranspose (RCfield K) (M + N) M A m) v)).
rewrite (RCplus_0_l K).
apply (Fadd_opp_l (RCfield K)).
rewrite {1} H6.
apply (FiniteSetInduction (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (Complement (Count M) (Singleton (Count M) m)))).
apply conj.
rewrite MySumF2Empty.
apply (RCip_mult_0_r K (FnVS (RCfield K) (M + N)) (RCnInner_Product_Space K (M + N))).
move=> B b H9 H10 H11 H12.
rewrite MySumF2Add.
rewrite (RCip_linear_plus_r K (FnVS (RCfield K) (M + N)) (RCnInner_Product_Space K (M + N))).
rewrite H12.
rewrite (RCip_linear_mult_r K (FnVS (RCfield K) (M + N)) (RCnInner_Product_Space K (M + N))).
simpl.
rewrite (RCnInnerProductMatrix K (M + N) (MTranspose (RCfield K) (M + N) M A m) (MTranspose (RCfield K) (M + N) M A b)).
suff: (Mmult (RCfield K) 1 (M + N) 1 (AdjointMatrixRC K (M + N) 1 (MVectorToMatrix (RCfield K) (M + N) (MTranspose (RCfield K) (M + N) M A m))) (MVectorToMatrix (RCfield K) (M + N) (MTranspose (RCfield K) (M + N) M A b)) Single Single = Mmult (RCfield K) M (M + N) M (AdjointMatrixRC K (M + N) M A) A m b).
move=> H13.
rewrite H13.
rewrite H1.
unfold MI.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig b)).
elim H10.
move=> b0 H14 H15 H16.
elim H14.
suff: (m = b0).
move=> H17.
rewrite H17.
apply (In_singleton (Count M) b0).
apply sig_map.
apply H16.
move=> H14.
rewrite (RCplus_0_l K).
simpl.
rewrite (ConjugateRCO K).
apply (Fmul_O_r (RCfield K)).
reflexivity.
apply H11.
elim.
reflexivity.
reflexivity.
move=> u H7.
apply (Full_intro (Count M) u).
reflexivity.
move=> u H5.
apply (Full_intro (VT (RCfield K) (FnVS (RCfield K) (M + N))) u).
suff: (RCnInnerProduct K (M + N) = RCip K (FnVS (RCfield K) (M + N)) (RCnInner_Product_Space K (M + N))).
move=> H2.
apply conj.
move=> v1 v2 H3 H4 m.
rewrite H2.
rewrite (RCip_linear_plus_r K (FnVS (RCfield K) (M + N)) (RCnInner_Product_Space K (M + N))).
simpl.
rewrite (H3 m).
rewrite (H4 m).
apply (RCplus_0_l K (RCO K)).
apply conj.
move=> f v H3 m.
rewrite H2.
rewrite (RCip_linear_mult_r K (FnVS (RCfield K) (M + N)) (RCnInner_Product_Space K (M + N))).
simpl.
rewrite (H3 m).
apply (Fmul_O_r (RCfield K) (ConjugateRC K f)).
move=> m.
apply (RCip_mult_0_r K (FnVS (RCfield K) (M + N)) (RCnInner_Product_Space K (M + N))).
reflexivity.
Qed.

Lemma MBlockHRCFrobeniusNorm : forall (K : RC) (M N L : nat) (A : Matrix (RCfield K) M L) (B : Matrix (RCfield K) N L), RCFrobeniusNorm K M L A * RCFrobeniusNorm K M L A + RCFrobeniusNorm K N L B * RCFrobeniusNorm K N L B = RCFrobeniusNorm K (M + N) L (MBlockH (RCfield K) M N L A B) * RCFrobeniusNorm K (M + N) L (MBlockH (RCfield K) M N L A B).
Proof.
move=> K M N L A B.
unfold RCFrobeniusNorm.
rewrite - (proj2 (RCnNormNature K (M * L) (fun (m : Count (M * L)) => A (fst (MultConnectInv M L m)) (snd (MultConnectInv M L m))))).
rewrite - (proj2 (RCnNormNature K (N * L) (fun (m : Count (N * L)) => B (fst (MultConnectInv N L m)) (snd (MultConnectInv N L m))))).
rewrite - (proj2 (RCnNormNature K ((M + N) * L) (fun (m : Count ((M + N) * L)) => MBlockH (RCfield K) M N L A B (fst (MultConnectInv (M + N) L m)) (snd (MultConnectInv (M + N) L m))))).
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count ((M + N) * L)) (FiniteIm (Count (M * L)) (Count ((M + N) * L)) (fun (m : Count (M * L)) => MultConnect (M + N) L (AddConnect M N (inl (fst (MultConnectInv M L m))), snd (MultConnectInv M L m))) (exist (Finite (Count (M * L))) (Full_set (Count (M * L))) (CountFinite (M * L))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2Included (Count ((M + N) * L)) (FiniteIm (Count (N * L)) (Count ((M + N) * L)) (fun (m : Count (N * L)) => MultConnect (M + N) L (AddConnect M N (inr (fst (MultConnectInv N L m))), snd (MultConnectInv N L m))) (exist (Finite (Count (N * L))) (Full_set (Count (N * L))) (CountFinite (N * L))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count ((M + N) * L))).
rewrite (CM_O_r (RCPCM K)).
rewrite RCReplus.
rewrite (MySumF2Same (Count (M * L)) (exist (Finite (Count (M * L))) (Full_set (Count (M * L))) (CountFinite (M * L))) (RCPCM K) (fun (n : Count (M * L)) => RCmult K (A (fst (MultConnectInv M L n)) (snd (MultConnectInv M L n))) (ConjugateRC K (A (fst (MultConnectInv M L n)) (snd (MultConnectInv M L n))))) (Basics.compose (fun (n : Count ((M + N) * L)) => RCmult K (MBlockH (RCfield K) M N L A B (fst (MultConnectInv (M + N) L n)) (snd (MultConnectInv (M + N) L n))) (ConjugateRC K (MBlockH (RCfield K) M N L A B (fst (MultConnectInv (M + N) L n)) (snd (MultConnectInv (M + N) L n))))) (fun (m : Count (M * L)) => MultConnect (M + N) L (AddConnect M N (inl (fst (MultConnectInv M L m))), snd (MultConnectInv M L m))))).
rewrite (MySumF2Same (Count (N * L)) (exist (Finite (Count (N * L))) (Full_set (Count (N * L))) (CountFinite (N * L))) (RCPCM K) (fun (n : Count (N * L)) => RCmult K (B (fst (MultConnectInv N L n)) (snd (MultConnectInv N L n))) (ConjugateRC K (B (fst (MultConnectInv N L n)) (snd (MultConnectInv N L n))))) (Basics.compose (fun (n : Count ((M + N) * L)) => RCmult K (MBlockH (RCfield K) M N L A B (fst (MultConnectInv (M + N) L n)) (snd (MultConnectInv (M + N) L n))) (ConjugateRC K (MBlockH (RCfield K) M N L A B (fst (MultConnectInv (M + N) L n)) (snd (MultConnectInv (M + N) L n))))) (fun (m : Count (N * L)) => MultConnect (M + N) L (AddConnect M N (inr (fst (MultConnectInv N L m))), snd (MultConnectInv N L m))))).
reflexivity.
move=> u H1.
unfold Basics.compose.
unfold MBlockH.
rewrite (proj1 (MultConnectInvRelation (M + N) L)).
simpl.
rewrite (proj1 (AddConnectInvRelation M N)).
reflexivity.
move=> u H1.
unfold Basics.compose.
unfold MBlockH.
rewrite (proj1 (MultConnectInvRelation (M + N) L)).
simpl.
rewrite (proj1 (AddConnectInvRelation M N)).
reflexivity.
move=> u.
elim.
move=> u0 H1 H2.
suff: (In (Count ((M + N) * L)) (Complement (Count ((M + N) * L)) (proj1_sig (FiniteIm (Count (N * L)) (Count ((M + N) * L)) (fun m : Count (N * L) => MultConnect (M + N) L (AddConnect M N (inr (fst (MultConnectInv N L m))), snd (MultConnectInv N L m))) (exist (Finite (Count (N * L))) (Full_set (Count (N * L))) (CountFinite (N * L)))))) u0).
elim H2.
move=> u1 H3 H4 H5.
suff: (u1 = MultConnect (M + N) L (AddConnect M N (AddConnectInv M N (fst (MultConnectInv (M + N) L u1))), snd (MultConnectInv (M + N) L u1))).
elim (AddConnectInv M N (fst (MultConnectInv (M + N) L u1))).
move=> m H6.
elim H3.
apply (Im_intro (Count (M * L)) (Count ((M + N) * L)) (Full_set (Count (M * L))) (fun (l : Count (M * L)) => MultConnect (M + N) L (AddConnect M N (inl (fst (MultConnectInv M L l))), snd (MultConnectInv M L l))) (MultConnect M L (m, snd (MultConnectInv (M + N) L u1)))).
apply (Full_intro (Count (M * L))).
rewrite (proj1 (MultConnectInvRelation M L)).
apply H6.
move=> n H6.
elim H5.
apply (Im_intro (Count (N * L)) (Count ((M + N) * L)) (Full_set (Count (N * L))) (fun (l : Count (N * L)) => MultConnect (M + N) L (AddConnect M N (inr (fst (MultConnectInv N L l))), snd (MultConnectInv N L l))) (MultConnect N L (n, snd (MultConnectInv (M + N) L u1)))).
apply (Full_intro (Count (N * L))).
rewrite (proj1 (MultConnectInvRelation N L)).
apply H6.
rewrite (proj2 (AddConnectInvRelation M N)).
rewrite - {1} (proj2 (MultConnectInvRelation (M + N) L) u1).
rewrite - surjective_pairing.
reflexivity.
apply H1.
move=> u1 u2 H1 H2 H3.
suff: (u1 = MultConnect N L (match AddConnectInv M N (fst (MultConnectInv (M + N) L (MultConnect (M + N) L (AddConnect M N (inr (fst (MultConnectInv N L u1))), snd (MultConnectInv N L u1))))) with
  | inl m0 => fst (MultConnectInv N L u1)
  | inr m0 => m0
end, snd (MultConnectInv (M + N) L (MultConnect (M + N) L (AddConnect M N (inr (fst (MultConnectInv N L u1))), snd (MultConnectInv N L u1)))))).
move=> H4.
rewrite H4.
rewrite H3.
rewrite (proj1 (MultConnectInvRelation (M + N) L)).
simpl.
rewrite (proj1 (AddConnectInvRelation M N)).
rewrite - surjective_pairing.
apply (proj2 (MultConnectInvRelation N L)).
rewrite (proj1 (MultConnectInvRelation (M + N) L)).
simpl.
rewrite (proj1 (AddConnectInvRelation M N)).
rewrite - surjective_pairing.
rewrite (proj2 (MultConnectInvRelation N L)).
reflexivity.
move=> u.
elim.
move=> x H1 y H2.
apply (Intersection_intro (Count ((M + N) * L))).
move=> H3.
suff: (y = MultConnect (M + N) L (AddConnect M N (inr (fst (MultConnectInv N L x))), snd (MultConnectInv N L x) )).
elim H3.
move=> z H4 w H5 H6.
suff: (match AddConnectInv M N (fst (MultConnectInv (M + N) L w)) with
  | inl m => False
  | inr m => True
end).
rewrite H5.
rewrite (proj1 (MultConnectInvRelation (M + N) L)).
simpl.
rewrite (proj1 (AddConnectInvRelation M N)).
apply.
rewrite H6.
rewrite (proj1 (MultConnectInvRelation (M + N) L)).
simpl.
rewrite (proj1 (AddConnectInvRelation M N)).
apply I.
apply H2.
apply (Full_intro (Count ((M + N) * L)) y).
move=> u1 u2 H1 H2 H3.
suff: (u1 = MultConnect M L (match AddConnectInv M N (fst (MultConnectInv (M + N) L (MultConnect (M + N) L ( AddConnect M N (inl (fst (MultConnectInv M L u1))), snd (MultConnectInv M L u1))))) with
  | inl m0 => m0
  | inr m0 => fst (MultConnectInv M L u1)
end, snd (MultConnectInv (M + N) L (MultConnect (M + N) L ( AddConnect M N (inl (fst (MultConnectInv M L u1))), snd (MultConnectInv M L u1)))))).
move=> H4.
rewrite H4.
rewrite H3.
rewrite (proj1 (MultConnectInvRelation (M + N) L)).
simpl.
rewrite (proj1 (AddConnectInvRelation M N)).
rewrite - surjective_pairing.
apply (proj2 (MultConnectInvRelation M L)).
rewrite (proj1 (MultConnectInvRelation (M + N) L)).
simpl.
rewrite (proj1 (AddConnectInvRelation M N)).
rewrite - surjective_pairing.
rewrite (proj2 (MultConnectInvRelation M L)).
reflexivity.
move=> u H1.
apply (Full_intro (Count ((M + N) * L)) u).
Qed.

Lemma MBlockWRCFrobeniusNorm : forall (K : RC) (L M N : nat) (A : Matrix (RCfield K) L M) (B : Matrix (RCfield K) L N), RCFrobeniusNorm K L M A * RCFrobeniusNorm K L M A + RCFrobeniusNorm K L N B * RCFrobeniusNorm K L N B = RCFrobeniusNorm K L (M + N) (MBlockW (RCfield K) L M N A B) * RCFrobeniusNorm K L (M + N) (MBlockW (RCfield K) L M N A B).
Proof.
move=> K L M N A B.
unfold RCFrobeniusNorm.
rewrite - (proj2 (RCnNormNature K (L * M) (fun (m : Count (L * M)) => A (fst (MultConnectInv L M m)) (snd (MultConnectInv L M m))))).
rewrite - (proj2 (RCnNormNature K (L * N) (fun (m : Count (L * N)) => B (fst (MultConnectInv L N m)) (snd (MultConnectInv L N m))))).
rewrite - (proj2 (RCnNormNature K (L * (M + N)) (fun (m : Count (L * (M + N))) => MBlockW (RCfield K) L M N A B (fst (MultConnectInv L (M + N) m)) (snd (MultConnectInv L (M + N) m))))).
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count (L * (M + N))) (FiniteIm (Count (L * M)) (Count (L * (M + N))) (fun (m : Count (L * M)) => MultConnect L (M + N) (fst (MultConnectInv L M m), AddConnect M N (inl (snd (MultConnectInv L M m))))) (exist (Finite (Count (L * M))) (Full_set (Count (L * M))) (CountFinite (L * M))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2Included (Count (L * (M + N))) (FiniteIm (Count (L * N)) (Count (L * (M + N))) (fun (m : Count (L * N)) => MultConnect L (M + N) (fst (MultConnectInv L N m), AddConnect M N (inr (snd (MultConnectInv L N m))))) (exist (Finite (Count (L * N))) (Full_set (Count (L * N))) (CountFinite (L * N))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count (L * (M + N)))).
rewrite (CM_O_r (RCPCM K)).
rewrite RCReplus.
rewrite (MySumF2Same (Count (L * M)) (exist (Finite (Count (L * M))) (Full_set (Count (L * M))) (CountFinite (L * M))) (RCPCM K) (fun (n : Count (L * M)) => RCmult K (A (fst (MultConnectInv L M n)) (snd (MultConnectInv L M n))) (ConjugateRC K (A (fst (MultConnectInv L M n)) (snd (MultConnectInv L M n))))) (Basics.compose (fun (n : Count (L * (M + N))) => RCmult K (MBlockW (RCfield K) L M N A B (fst (MultConnectInv L (M + N) n)) (snd (MultConnectInv L (M + N) n))) (ConjugateRC K (MBlockW (RCfield K) L M N A B (fst (MultConnectInv L (M + N) n)) (snd (MultConnectInv L (M + N) n))))) (fun (m : Count (L * M)) => MultConnect L (M + N) (fst (MultConnectInv L M m), AddConnect M N (inl (snd (MultConnectInv L M m))))))).
rewrite (MySumF2Same (Count (L * N)) (exist (Finite (Count (L * N))) (Full_set (Count (L * N))) (CountFinite (L * N))) (RCPCM K) (fun (n : Count (L * N)) => RCmult K (B (fst (MultConnectInv L N n)) (snd (MultConnectInv L N n))) (ConjugateRC K (B (fst (MultConnectInv L N n)) (snd (MultConnectInv L N n))))) (Basics.compose (fun (n : Count (L * (M + N))) => RCmult K (MBlockW (RCfield K) L M N A B (fst (MultConnectInv L (M + N) n)) (snd (MultConnectInv L (M + N) n))) (ConjugateRC K (MBlockW (RCfield K) L M N A B (fst (MultConnectInv L (M + N) n)) (snd (MultConnectInv L (M + N) n))))) (fun (m : Count (L * N)) => MultConnect L (M + N) (fst (MultConnectInv L N m), AddConnect M N (inr (snd (MultConnectInv L N m))))))).
reflexivity.
move=> u H1.
unfold Basics.compose.
unfold MBlockW.
rewrite (proj1 (MultConnectInvRelation L (M + N))).
simpl.
rewrite (proj1 (AddConnectInvRelation M N)).
reflexivity.
move=> u H1.
unfold Basics.compose.
unfold MBlockW.
rewrite (proj1 (MultConnectInvRelation L (M + N))).
simpl.
rewrite (proj1 (AddConnectInvRelation M N)).
reflexivity.
move=> u.
elim.
move=> u0 H1 H2.
suff: (In (Count (L * (M + N))) (Complement (Count (L * (M + N))) (proj1_sig (FiniteIm (Count (L * N)) (Count (L * (M + N))) (fun (m : Count (L * N)) => MultConnect L (M + N) (fst (MultConnectInv L N m), AddConnect M N (inr (snd (MultConnectInv L N m))))) (exist (Finite (Count (L * N))) (Full_set (Count (L * N))) (CountFinite (L * N)))))) u0).
elim H2.
move=> u1 H3 H4 H5.
suff: (u1 = MultConnect L (M + N) (fst (MultConnectInv L (M + N) u1), AddConnect M N (AddConnectInv M N (snd (MultConnectInv L (M + N) u1))))).
elim (AddConnectInv M N (snd (MultConnectInv L (M + N) u1))).
move=> m H6.
elim H3.
apply (Im_intro (Count (L * M)) (Count (L * (M + N))) (Full_set (Count (L * M))) (fun (l : Count (L * M)) => MultConnect L (M + N) (fst (MultConnectInv L M l), AddConnect M N (inl (snd (MultConnectInv L M l))))) (MultConnect L M (fst (MultConnectInv L (M + N) u1), m))).
apply (Full_intro (Count (L * M))).
rewrite (proj1 (MultConnectInvRelation L M)).
apply H6.
move=> n H6.
elim H5.
apply (Im_intro (Count (L * N)) (Count (L * (M + N))) (Full_set (Count (L * N))) (fun (l : Count (L * N)) => MultConnect L (M + N) (fst (MultConnectInv L N l), AddConnect M N (inr (snd (MultConnectInv L N l))))) (MultConnect L N (fst (MultConnectInv L (M + N) u1), n))).
apply (Full_intro (Count (L * N))).
rewrite (proj1 (MultConnectInvRelation L N)).
apply H6.
rewrite (proj2 (AddConnectInvRelation M N)).
rewrite - {1} (proj2 (MultConnectInvRelation L (M + N)) u1).
rewrite - surjective_pairing.
reflexivity.
apply H1.
move=> u1 u2 H1 H2 H3.
rewrite - (proj2 (MultConnectInvRelation L N) u1).
rewrite - (proj2 (MultConnectInvRelation L N) u2).
suff: (u1 = MultConnect L N (fst (MultConnectInv L (M + N) (MultConnect L (M + N) (fst (MultConnectInv L N u1), AddConnect M N (inr (snd (MultConnectInv L N u1)))))), match AddConnectInv M N (snd (MultConnectInv L (M + N) (MultConnect L (M + N) (fst (MultConnectInv L N u1), AddConnect M N (inr (snd (MultConnectInv L N u1))))))) with
  | inl m0 => snd (MultConnectInv L N u1)
  | inr m0 => m0
end)).
move=> H4.
rewrite H4.
rewrite H3.
rewrite (proj1 (MultConnectInvRelation L (M + N))).
simpl.
rewrite (proj1 (MultConnectInvRelation L N)).
rewrite (proj1 (AddConnectInvRelation M N)).
rewrite - surjective_pairing.
reflexivity.
rewrite (proj1 (MultConnectInvRelation L (M + N))).
simpl.
rewrite (proj1 (AddConnectInvRelation M N)).
rewrite - surjective_pairing.
rewrite (proj2 (MultConnectInvRelation L N)).
reflexivity.
move=> u.
elim.
move=> x H1 y H2.
apply (Intersection_intro (Count (L * (M + N)))).
move=> H3.
suff: (y = MultConnect L (M + N) (fst (MultConnectInv L N x), AddConnect M N (inr (snd (MultConnectInv L N x))))).
elim H3.
move=> z H4 w H5 H6.
suff: (match AddConnectInv M N (snd (MultConnectInv L (M + N) w)) with
  | inl m => False
  | inr m => True
end).
rewrite H5.
rewrite (proj1 (MultConnectInvRelation L (M + N))).
simpl.
rewrite (proj1 (AddConnectInvRelation M N)).
apply.
rewrite H6.
rewrite (proj1 (MultConnectInvRelation L (M + N))).
simpl.
rewrite (proj1 (AddConnectInvRelation M N)).
apply I.
apply H2.
apply (Full_intro (Count (L * (M + N))) y).
move=> u1 u2 H1 H2 H3.
rewrite - (proj2 (MultConnectInvRelation L M) u1).
rewrite - (proj2 (MultConnectInvRelation L M) u2).
suff: (u1 = MultConnect L M (fst (MultConnectInv L (M + N) (MultConnect L (M + N) (fst (MultConnectInv L M u1), AddConnect M N (inl (snd (MultConnectInv L M u1)))))), match AddConnectInv M N (snd (MultConnectInv L (M + N) (MultConnect L (M + N) (fst (MultConnectInv L M u1), AddConnect M N (inl (snd (MultConnectInv L M u1))))))) with
  | inl m0 => m0
  | inr m0 => snd (MultConnectInv L M u1)
end)).
move=> H4.
rewrite H4.
rewrite H3.
rewrite (proj1 (MultConnectInvRelation L (M + N))).
simpl.
rewrite (proj1 (MultConnectInvRelation L M)).
rewrite (proj1 (AddConnectInvRelation M N)).
rewrite - surjective_pairing.
reflexivity.
rewrite (proj1 (MultConnectInvRelation L (M + N))).
simpl.
rewrite (proj1 (AddConnectInvRelation M N)).
rewrite - surjective_pairing.
rewrite (proj2 (MultConnectInvRelation L M)).
reflexivity.
move=> u H1.
apply (Full_intro (Count (L * (M + N))) u).
Qed.

Lemma SingularValueRCHBestApproximateFrobeniusNorm : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M) (k : nat), (k <= M)%nat -> forall (H : MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n) >= 0), is_min (fun (r : R) => exists (B : Matrix (RCfield K) (M + N) M), (Rank (RCfield K) (M + N) M B <= k)%nat /\ RCFrobeniusNorm K (M + N) M (Mplus (RCfield K) (M + N) M A (Mopp (RCfield K) (M + N) M B)) = r) (MySqrt (exist (fun (r : R) => r >= 0) (MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n)) H)).
Proof.
suff: (forall (K : RC) (M N : nat) (k : nat), (k <= M)%nat -> forall (A : Matrix (RCfield K) (M + N) M) (Q : Matrix (RCfield K) (M + N) k), Mmult (RCfield K) k (M + N) k (AdjointMatrixRC K (M + N) k Q) Q = MI (RCfield K) k -> forall (B : Matrix (RCfield K) k M), RCFrobeniusNorm K (M + N) M (Mplus (RCfield K) (M + N) M A (Mopp (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) k M Q B))) * RCFrobeniusNorm K (M + N) M (Mplus (RCfield K) (M + N) M A (Mopp (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) k M Q B))) >= RCFrobeniusNorm K (M + N) M A * RCFrobeniusNorm K (M + N) M A - RCFrobeniusNorm K k M (Mmult (RCfield K) k (M + N) M (AdjointMatrixRC K (M + N) k Q) A) * RCFrobeniusNorm K k M (Mmult (RCfield K) k (M + N) M (AdjointMatrixRC K (M + N) k Q) A)).
move=> H1.
suff: (forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M) (k : nat), (k <= M)%nat -> forall (Q : Matrix (RCfield K) (M + N) k), Mmult (RCfield K) k (M + N) k (AdjointMatrixRC K (M + N) k Q) Q = MI (RCfield K) k -> RCFrobeniusNorm K k M (Mmult (RCfield K) k (M + N) M (AdjointMatrixRC K (M + N) k Q) A) * RCFrobeniusNorm K k M (Mmult (RCfield K) k (M + N) M (AdjointMatrixRC K (M + N) k Q) A) <= MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n < k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n)).
move=> H2 K M N A k H3 H4.
apply conj.
elim (proj2 (proj2 (SingularValueRCHNature K M N A))).
move=> U.
elim.
move=> V H5.
exists (Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right_ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))).
apply conj.
apply (le_trans (Rank (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) (M + N) M U (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right_ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V)))) (Rank (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right_ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))) k).
apply (RankMultLeL (RCfield K)).
apply (le_trans (Rank (RCfield K) (M + N) M (Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right_ => RCO K
end)) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V))) (Rank (RCfield K) (M + N) M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right_ => RCO K
end)) (MO (RCfield K) N M))) k).
apply (RankMultLeR (RCfield K)).
suff: (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right_ => RCO K
end)) (MO (RCfield K) N M) = Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => IRRC K (SingularValueRCH K M N A m)
  | right_ => RCO K
end)) (MO (RCfield K) N M)) (RankNormalForm (RCfield K) M M k)).
move=> H6.
rewrite H6.
rewrite - {7} (RankNormalFormRank (RCfield K) M M k).
apply (RankMultLeL (RCfield K)).
apply H3.
apply H3.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < M)%nat} (FiniteSingleton {n : nat | (n < M)%nat} y) (exist (Finite (Count M)) (Full_set {n : nat | (n < M)%nat}) (CountFinite M))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
unfold MBlockH.
elim (AddConnectInv M N x).
move=> x0.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y)).
move=> H6.
elim (excluded_middle_informative (proj1_sig x0 < k)%nat).
move=> H7.
unfold RankNormalForm.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig y)).
move=> H8.
elim (excluded_middle_informative (proj1_sig y < k)%nat).
move=> H9.
rewrite (Fmul_I_r (RCfield K)).
reflexivity.
move=> H9.
elim H9.
rewrite - H6.
apply H7.
elim.
reflexivity.
move=> H7.
rewrite (Fmul_O_l (RCfield K)).
reflexivity.
move=> H6.
rewrite (Fmul_O_l (RCfield K)).
reflexivity.
move=> H6.
unfold MO.
rewrite (Fmul_O_l (RCfield K)).
reflexivity.
move=> u.
elim.
move=> u0 H6 H7.
unfold RankNormalForm.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig y)).
move=> H8.
elim H6.
suff: (u0 = y).
move=> H9.
rewrite H9.
apply (In_singleton {n : nat | (n < M)%nat} y).
apply sig_map.
apply H8.
move=> H8.
apply (Fmul_O_r (RCfield K)).
move=> u H6.
apply (Full_intro {n : nat | (n < M)%nat} u).
apply (SingularValueRCHApproximateFrobeniusNorm K M N A U V (proj1 H5) (proj1 (proj2 H5)) (proj2 (proj2 H5)) k H3).
move=> r.
elim.
move=> B H5.
suff: (exists (Q : Matrix (RCfield K) (M + N) k) (C : Matrix (RCfield K) k M), Mmult (RCfield K) k (M + N) k (AdjointMatrixRC K (M + N) k Q) Q = MI (RCfield K) k /\ B = Mmult (RCfield K) (M + N) k M Q C).
elim.
move=> Q.
elim.
move=> C H7.
rewrite - (proj2 H5).
suff: (forall (a b : R), a >= 0 -> b >= 0 -> a * a >= b * b -> a >= b).
move=> H8.
apply H8.
apply (RCnNormNature K ((M + N) * M)).
apply MySqrtNature.
rewrite - (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n)) H4))).
simpl.
apply Rle_ge.
apply (Rle_trans (MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun n : Count M => SingularValueRCH K M N A n * SingularValueRCH K M N A n)) (RCFrobeniusNorm K (M + N) M A * RCFrobeniusNorm K (M + N) M A - RCFrobeniusNorm K k M (Mmult (RCfield K) k (M + N) M (AdjointMatrixRC K (M + N) k Q) A) * RCFrobeniusNorm K k M (Mmult (RCfield K) k (M + N) M (AdjointMatrixRC K (M + N) k Q) A)) (RCFrobeniusNorm K (M + N) M (Mplus (RCfield K) (M + N) M A (Mopp (RCfield K) (M + N) M B)) * RCFrobeniusNorm K (M + N) M (Mplus (RCfield K) (M + N) M A (Mopp (RCfield K) (M + N) M B)))).
apply (Rplus_le_reg_r (MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n < k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n))).
suff: (MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n) + MySumF2 (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n < k)%nat)) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n) = RCFrobeniusNorm K (M + N) M A * RCFrobeniusNorm K (M + N) M A).
move=> H9.
rewrite H9.
unfold Rminus.
rewrite Rplus_assoc.
rewrite - {1} (Rplus_0_r (RCFrobeniusNorm K (M + N) M A * RCFrobeniusNorm K (M + N) M A)).
apply Rplus_le_compat_l.
apply Rge_le.
rewrite Rplus_comm.
apply Rge_minus.
apply Rle_ge.
apply (H2 K M N A k H3 Q).
apply (proj1 H7).
rewrite (SingularValueRCHFrobeniusNorm K M N A).
suff: ((fun (n : Count M) => (proj1_sig n < k)%nat) = Complement (Count M) (fun (n : Count M) => (proj1_sig n >= k)%nat)).
move=> H9.
rewrite H9.
rewrite (MySumF2Excluded (Count M) RPCM (fun (n : Count M) => SingularValueRCH K M N A n * SingularValueRCH K M N A n) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n >= k)%nat)).
reflexivity.
apply Extensionality_Ensembles.
apply conj.
move=> m H9.
apply (lt_not_le (proj1_sig m) k H9).
move=> m H9.
elim (le_or_lt k (proj1_sig m)).
move=> H10.
elim (H9 H10).
apply.
apply Rge_le.
rewrite (proj2 H7).
apply (H1 K M N k H3 A Q (proj1 H7) C).
move=> a b H8 H9 H10.
elim (Rge_or_gt a b).
apply.
move=> H11.
elim (Rge_not_gt (b * b) (a * a) H10).
apply (Rmult_le_0_lt_compat a b a b).
apply (Rge_le a 0 H8).
apply (Rge_le a 0 H8).
apply H11.
apply H11.
elim (proj2 (proj2 (SingularValueRCHNature K M N B))).
move=> U.
elim.
move=> V H6.
suff: (forall (n : Count k), (proj1_sig n < M + N)%nat).
move=> H7.
exists (fun (m : Count (M + N)) (n : Count k) => U m (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig n) (H7 n))).
exists (fun (m : Count k) (n : Count M) => Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (l : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N B) l))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V) (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m) (H7 m)) n).
apply conj.
apply functional_extensionality.
move=> p.
apply functional_extensionality.
move=> q.
suff: (Mmult (RCfield K) k (M + N) k (AdjointMatrixRC K (M + N) k (fun (m : Count (M + N)) (n : Count k) => U m (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig n) (H7 n)))) (fun (m : Count (M + N)) (n : Count k) => U m (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig n) (H7 n))) p q = Mmult (RCfield K) (M + N) (M + N) (M + N) (AdjointMatrixRC K (M + N) (M + N) U) U (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig p) (H7 p)) (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig q) (H7 q)) ).
move=> H8.
rewrite H8.
rewrite (proj1 H6).
reflexivity.
reflexivity.
rewrite {1} (proj2 (proj2 H6)).
suff: (forall (m : Count (M + N)) (n : Count M), (~ proj1_sig m < k)%nat -> Mmult (RCfield K) (M + N) M M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun (m : {n : nat | (n < M)%nat}) => IRRC K (proj1_sig (SingularValueRCHSig K M N B) m))) (MO (RCfield K) N M)) (AdjointMatrixRC K M M V) m n = RCO K).
move=> H8.
apply functional_extensionality.
move=> p.
apply functional_extensionality.
move=> q.
unfold Mmult at 5.
unfold Mmult at 1.
rewrite (MySumF2Included {n : nat | (n < M + N)%nat} (FiniteIm {n : nat | (n < k)%nat} {n : nat | (n < M + N)%nat} (fun (l : Count k) => (exist (fun (s : nat) => (s < M + N)%nat) (proj1_sig l) (H7 l))) (exist (Finite (Count k)) (Full_set {n : nat | (n < k)%nat}) (CountFinite k)))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O {n : nat | (n < M + N)%nat}).
apply (CM_O_r (FPCM (RCfield K))).
move=> u.
elim.
move=> u0 H9 H10.
rewrite (H8 u0 q).
apply (Fmul_O_r (RCfield K)).
move=> H11.
apply H9.
apply (Im_intro {n : nat | (n < k)%nat} {n : nat | (n < M + N)%nat} (Full_set {n : nat | (n < k)%nat}) (fun (l : Count k) => exist (fun s : nat => (s < M + N)%nat) (proj1_sig l) (H7 l)) (exist (fun (l : nat) => (l < k)%nat) (proj1_sig u0) H11)).
apply (Full_intro (Count k)).
apply sig_map.
reflexivity.
move=> u1 u2 H9 H10 H11.
apply sig_map.
suff: (proj1_sig u1 = proj1_sig (exist (fun (s : nat) => (s < M + N)%nat) (proj1_sig u1) (H7 u1))).
move=> H12.
rewrite H12.
rewrite H11.
reflexivity.
reflexivity.
move=> u H9.
apply (Full_intro (Count (M + N))).
suff: (forall (m : Count (M + N)) (n : Count M), ~ (proj1_sig m < k)%nat -> MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun m0 : {n0 : nat | (n0 < M)%nat} => IRRC K (proj1_sig (SingularValueRCHSig K M N B) m0))) (MO (RCfield K) N M) m n = RCO K).
move=> H8 m n H9.
apply MySumF2O.
move=> u H10.
rewrite (H8 m u H9).
apply (Fmul_O_l (RCfield K)).
suff: (forall (m : Count M), ~ (proj1_sig m < k)%nat -> proj1_sig (SingularValueRCHSig K M N B) m = 0).
move=> H8 m n.
unfold MBlockH.
rewrite - {1} (proj2 (AddConnectInvRelation M N) m).
elim (AddConnectInv M N m).
move=> u0.
rewrite - (proj1 (AddConnectNature M N) u0).
move=> H9.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig u0) (proj1_sig n)).
move=> H10.
rewrite (H8 u0 H9).
elim K.
reflexivity.
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H11.
rewrite H11.
apply (CmakeRe 0 0).
move=> H11.
rewrite H11.
apply (CmakeIm 0 0).
move=> H10.
reflexivity.
move=> u0 H9.
reflexivity.
move=> m H8.
apply (proj2 (proj1 (SingularValueRCHRankRelation K M N (Rank (RCfield K) (M + N) M B) (RankLeW (RCfield K) (M + N) M B) B) (eq_refl (Rank (RCfield K) (M + N) M B)) m)).
apply (le_trans (Rank (RCfield K) (M + N) M B) k (proj1_sig m) (proj1 H5)).
elim (le_or_lt k (proj1_sig m)).
apply.
move=> H9.
elim (H8 H9).
move=> m.
apply (le_trans (S (proj1_sig m)) k (M + N) (proj2_sig m)).
apply (le_trans k M (M + N) H3 (le_plus_l M N)).
move=> K M N A.
elim.
move=> H2 Q.
suff: (AdjointMatrixRC K (M + N) O Q = MO (RCfield K) O (M + N)).
move=> H3.
rewrite H3.
rewrite (Mmult_O_l (RCfield K) O (M + N) M).
unfold RCFrobeniusNorm.
rewrite - (proj2 (RCnNormNature K (0 * M) (fun (m : Count (0 * M)) => MO (RCfield K) 0 M (fst (MultConnectInv 0 M m)) (snd (MultConnectInv 0 M m))))).
unfold RCnInnerProduct.
rewrite MySumF2O.
rewrite MySumF2O.
right.
elim K.
reflexivity.
reflexivity.
move=> u.
elim.
move=> u0 H4 H5.
elim (le_not_lt O (proj1_sig u0) (le_0_n (proj1_sig u0)) H4).
move=> u H4.
apply (Fmul_O_l (RCfield K)).
apply functional_extensionality.
move=> p.
elim (le_not_lt O (proj1_sig p) (le_0_n (proj1_sig p)) (proj2_sig p)).
move=> k H2 H3 Q H4.
suff: (exists (U : Matrix (RCfield K) (S k) (S k)) (v : Count (M + N) -> RCT K), UnitaryMatrixRC K (S k) U /\ Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q) (exist (fun (l : nat) => (l < S k)%nat) O (le_n_S O k (le_0_n k))) = v /\ RCnNorm K M (MVmult (RCfield K) M (M + N) (MTranspose (RCfield K) (M + N) M A) v) <= SingularValueRCH K M N A (exist (fun (l : nat) => (l < M)%nat) k H3)).
elim.
move=> U.
elim.
move=> v H5.
rewrite - (UnitaryMatrixRCSaveRCFrobeniusNormL K (S k) M U (proj1 H5)).
rewrite - (Mmult_assoc (RCfield K) (S k) (S k) (M + N) M).
suff: (RCFrobeniusNorm K (S k) M (Mmult (RCfield K) (S k) (M + N) M (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q)) A) * RCFrobeniusNorm K (S k) M (Mmult (RCfield K) (S k) (M + N) M (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q)) A) = RCFrobeniusNorm K k M (fun (l : Count k) => Mmult (RCfield K) (S k) (M + N) M (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q)) A (AddConnect 1 k (inr l))) * RCFrobeniusNorm K k M (fun (l : Count k) => Mmult (RCfield K) (S k) (M + N) M (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q)) A (AddConnect 1 k (inr l))) + RCnNorm K M (MVmult (RCfield K) M (M + N) (MTranspose (RCfield K) (M + N) M A) v) * RCnNorm K M (MVmult (RCfield K) M (M + N) (MTranspose (RCfield K) (M + N) M A) v)).
move=> H6.
rewrite H6.
rewrite (MySumF2Included (Count M) (FiniteIntersection (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (fun (n : Count M) => (proj1_sig n < k)%nat))).
apply Rplus_le_compat.
suff: ((fun (l : Count k) => Mmult (RCfield K) (S k) (M + N) M (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q)) A (AddConnect 1 k (inr l))) = Mmult (RCfield K) k (M + N) M (AdjointMatrixRC K (M + N) k (AdjointMatrixRC K k (M + N) (Mmult (RCfield K) k (S k) (M + N) (fun (l : Count k) => U (AddConnect 1 k (inr l))) (AdjointMatrixRC K (M + N) (S k) Q)))) A).
move=> H7.
rewrite H7.
apply (H2 (le_trans k (S k) M (le_S k k (le_n k)) H3) (AdjointMatrixRC K k (M + N) (Mmult (RCfield K) k (S k) (M + N) (fun (l : Count k) => U (AddConnect 1 k (inr l))) (AdjointMatrixRC K (M + N) (S k) Q)))).
rewrite (AdjointMatrixRCInvolutive K k (M + N)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (Mmult (RCfield K) k (M + N) k (Mmult (RCfield K) k (S k) (M + N) (fun (l : Count k) => U (AddConnect 1 k (inr l))) (AdjointMatrixRC K (M + N) (S k) Q)) (AdjointMatrixRC K k (M + N) (Mmult (RCfield K) k (S k) (M + N) (fun (l : Count k) => U (AddConnect 1 k (inr l))) (AdjointMatrixRC K (M + N) (S k) Q))) x y = Mmult (RCfield K) (S k) (M + N) (S k) (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q)) (AdjointMatrixRC K (S k) (M + N) (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q))) (AddConnect 1 k (inr x)) (AddConnect 1 k (inr y))).
move=> H8.
rewrite H8.
rewrite (AdjointMatrixRCMult K (S k) (S k) (M + N)).
rewrite (Mmult_assoc (RCfield K) (S k) (S k) (M + N) (S k)).
rewrite - (Mmult_assoc (RCfield K) (S k) (M + N) (S k) (S k)).
rewrite (AdjointMatrixRCInvolutive K (M + N) (S k)).
rewrite H4.
rewrite (Mmult_I_l (RCfield K)).
rewrite (proj1 (MmultILRSame (RCfield K) (S k) (AdjointMatrixRC K (S k) (S k) U) U)).
unfold MI.
rewrite - (proj2 (AddConnectNature 1 k) x).
rewrite - (proj2 (AddConnectNature 1 k) y).
elim (Nat.eq_dec (1 + proj1_sig x) (1 + proj1_sig y)).
move=> H9.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H10.
reflexivity.
elim.
apply (plus_reg_l (proj1_sig x) (proj1_sig y) 1 H9).
move=> H9.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H10.
elim H9.
rewrite H10.
reflexivity.
move=> H10.
reflexivity.
apply (proj1 H5).
reflexivity.
rewrite (AdjointMatrixRCInvolutive K k (M + N)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
reflexivity.
rewrite (MySumF2Included (Count M) (FiniteSingleton (Count M) (exist (fun (l : nat) => (l < M)%nat) k H3))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (CM_O_r RPCM).
apply Rmult_le_compat.
apply Rge_le.
apply RCnNormNature.
apply Rge_le.
apply RCnNormNature.
apply (proj2 H5).
apply (proj2 H5).
move=> u.
elim.
move=> u0 H7 H8.
elim H7.
elim H8.
move=> u1 H9 H10.
elim (le_lt_or_eq (proj1_sig u1) k).
move=> H11.
elim H9.
apply (Intersection_intro (Count M)).
apply H11.
apply (Full_intro (Count M) u1).
move=> H11.
suff: (u1 = (exist (fun (l : nat) => (l < M)%nat) k H3)).
move=> H12.
rewrite H12.
apply (In_singleton (Count M) (exist (fun (l : nat) => (l < M)%nat) k H3)).
apply sig_map.
apply H11.
elim H10.
move=> u2 H11 H12.
apply (le_S_n (proj1_sig u2) k H11).
move=> u.
elim.
apply (Intersection_intro (Count M)).
move=> H7.
suff: (proj1_sig (exist (fun (l : nat) => (l < M)%nat) k H3) = k).
elim H7.
move=> u0 H8 H9 H10.
elim (lt_irrefl (proj1_sig u0)).
rewrite {2} H10.
apply H8.
reflexivity.
apply (Intersection_intro (Count M)).
apply (le_n (S k)).
apply (Full_intro (Count M)).
move=> u.
elim.
move=> u0 H7 H8.
apply (Intersection_intro (Count M)).
apply (le_trans (S (proj1_sig u0)) k (S k) H7 (le_S k k (le_n k))).
apply H8.
unfold RCFrobeniusNorm.
rewrite - (proj2 (RCnNormNature K (S k * M) (fun (m : Count (S k * M)) => Mmult (RCfield K) (S k) (M + N) M (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q)) A (fst (MultConnectInv (S k) M m)) (snd (MultConnectInv (S k) M m))))).
rewrite - (proj2 (RCnNormNature K (k * M) (fun (m : Count (k * M)) => Mmult (RCfield K) (S k) (M + N) M (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q)) A (AddConnect 1 k (inr (fst (MultConnectInv k M m)))) (snd (MultConnectInv k M m))))).
rewrite - (proj2 (RCnNormNature K M (MVmult (RCfield K) M (M + N) (MTranspose (RCfield K) (M + N) M A) v))).
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count (S k * M)) (FiniteIm (Count (k * M)) (Count (S k * M)) (fun (m : Count (k * M)) => MultConnect (S k) M (AddConnect 1 k (inr (fst (MultConnectInv k M m))), snd (MultConnectInv k M m))) (exist (Finite (Count (k * M))) (Full_set (Count (k * M))) (CountFinite (k * M))))).
rewrite - MySumF2BijectiveSame2.
rewrite (RCReplus K).
suff: (Basics.compose (fun (n : Count (S k * M)) => RCmult K (Mmult (RCfield K) (S k) (M + N) M (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q)) A (fst (MultConnectInv (S k) M n)) (snd (MultConnectInv (S k) M n))) (ConjugateRC K (Mmult (RCfield K) (S k) (M + N) M (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q)) A (fst (MultConnectInv (S k) M n)) (snd (MultConnectInv (S k) M n))))) (fun (m : Count (k * M)) => MultConnect (S k) M (AddConnect 1 k (inr (fst (MultConnectInv k M m))), snd (MultConnectInv k M m))) = (fun (n : Count (k * M)) => RCmult K (Mmult (RCfield K) (S k) (M + N) M (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q)) A (AddConnect 1 k (inr (fst (MultConnectInv k M n)))) (snd (MultConnectInv k M n))) (ConjugateRC K (Mmult (RCfield K) (S k) (M + N) M (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q)) A (AddConnect 1 k (inr (fst (MultConnectInv k M n)))) (snd (MultConnectInv k M n)))))).
move=> H6.
rewrite H6.
apply Rplus_eq_compat_l.
rewrite (MySumF2Included (Count (S k * M)) (FiniteIm (Count M) (Count (S k * M)) (fun (m : Count M) => MultConnect (S k) M (AddConnect 1 k (inl Single), m)) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count (S k * M))).
rewrite CM_O_r.
apply f_equal.
apply (MySumF2Same (Count M) (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) (RCPCM K)).
move=> u H7.
unfold Basics.compose.
rewrite (proj1 (MultConnectInvRelation (S k) M)).
rewrite - (proj1 (proj2 H5)).
suff: (Mmult (RCfield K) (S k) (M + N) M (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q)) A (fst (AddConnect 1 k (inl Single), u)) (snd (AddConnect 1 k (inl Single), u)) = MVmult (RCfield K) M (M + N) (MTranspose (RCfield K) (M + N) M A) (Mmult (RCfield K) (S k) (S k) (M + N) U (AdjointMatrixRC K (M + N) (S k) Q) (exist (fun l : nat => (l < S k)%nat) O (le_n_S 0 k (le_0_n k)))) u).
move=> H8.
rewrite H8.
reflexivity.
apply MySumF2Same.
move=> u0 H8.
suff: (fst (AddConnect 1 k (inl Single), u) = (exist (fun (l : nat) => (l < S k)%nat) O (le_n_S 0 k (le_0_n k)))).
move=> H9.
rewrite H9.
apply (Fmul_comm (RCfield K)).
apply sig_map.
simpl.
rewrite - (proj1 (AddConnectNature 1 k) Single).
reflexivity.
move=> u.
elim.
move=> u0 H7 H8.
elim H7.
elim H8.
move=> u1 H9 H10.
elim (le_lt_or_eq O (proj1_sig (fst (MultConnectInv (S k) M u1))) (le_0_n (proj1_sig (fst (MultConnectInv (S k) M u1))))).
move=> H11.
elim H9.
suff: (exists (m : Count k), proj1_sig (fst (MultConnectInv (S k) M u1)) = S (proj1_sig m)).
elim.
move=> m H12.
apply (Im_intro (Count (k * M)) (Count (S k * M)) (Full_set (Count (k * M))) (fun (l : Count (k * M)) => MultConnect (S k) M (AddConnect 1 k (inr (fst (MultConnectInv k M l))), snd (MultConnectInv k M l))) (MultConnect k M (m, snd (MultConnectInv (S k) M u1)))).
apply (Full_intro (Count (k * M))).
rewrite - {1} (proj2 (MultConnectInvRelation (S k) M) u1).
apply f_equal.
apply injective_projections.
rewrite (proj1 (MultConnectInvRelation k M)).
apply sig_map.
simpl.
rewrite - (proj2 (AddConnectNature 1 k) m).
apply H12.
rewrite (proj1 (MultConnectInvRelation k M)).
reflexivity.
suff: (0 < proj1_sig (fst (MultConnectInv (S k) M u1)))%nat.
suff: (proj1_sig (fst (MultConnectInv (S k) M u1)) < S k)%nat.
elim (proj1_sig (fst (MultConnectInv (S k) M u1))).
move=> H12 H13.
elim (lt_irrefl O H13).
move=> n H12 H13 H14.
exists (exist (fun (l : nat) => (l < k)%nat) n (lt_S_n n k H13)).
reflexivity.
apply (proj2_sig (fst (MultConnectInv (S k) M u1))).
apply H11.
move=> H11.
apply (Im_intro (Count M) (Count (S k * M)) (Full_set (Count M)) (fun (m : Count M) => MultConnect (S k) M (AddConnect 1 k (inl Single), m)) (snd (MultConnectInv (S k) M u1))).
apply (Full_intro (Count M)).
rewrite - {1} (proj2 (MultConnectInvRelation (S k) M) u1).
apply f_equal.
apply injective_projections.
apply sig_map.
rewrite - H11.
simpl.
rewrite - (proj1 (AddConnectNature 1 k) Single).
reflexivity.
reflexivity.
move=> u1 u2 H7 H8 H9.
suff: (u1 = snd (MultConnectInv (S k) M (MultConnect (S k) M (AddConnect 1 k (inl Single), u1)))).
move=> H10.
rewrite H10.
rewrite H9.
rewrite (proj1 (MultConnectInvRelation (S k) M)).
reflexivity.
rewrite (proj1 (MultConnectInvRelation (S k) M)).
reflexivity.
move=> u.
elim.
move=> x H7 y H8.
apply (Intersection_intro (Count (S k * M))).
move=> H9.
suff: (y = MultConnect (S k) M (AddConnect 1 k (inl Single), x)).
elim H9.
move=> z H10 w H11.
move=> H12.
suff: (match AddConnectInv 1 k (fst (MultConnectInv (S k) M w)) with
  | inl _ => True
  | inr _ => False
end).
rewrite H11.
rewrite (proj1 (MultConnectInvRelation (S k) M)).
rewrite (proj1 (AddConnectInvRelation 1 k)).
apply.
rewrite H12.
rewrite (proj1 (MultConnectInvRelation (S k) M)).
rewrite (proj1 (AddConnectInvRelation 1 k)).
apply I.
apply H8.
apply (Full_intro (Count (S k * M)) y).
apply functional_extensionality.
move=> m.
unfold Basics.compose.
rewrite (proj1 (MultConnectInvRelation (S k) M)).
reflexivity.
move=> u1 u2 H6 H7 H8.
rewrite - (proj2 (MultConnectInvRelation k M) u1).
rewrite - (proj2 (MultConnectInvRelation k M) u2).
apply f_equal.
apply injective_projections.
suff: (match AddConnectInv 1 k (fst (MultConnectInv (S k) M (MultConnect (S k) M (AddConnect 1 k (inr (fst (MultConnectInv k M u1))), snd (MultConnectInv k M u1))))) with
  | inl _ => False
  | inr l => l = fst (MultConnectInv k M u1)
end).
rewrite H8.
rewrite (proj1 (MultConnectInvRelation (S k) M)).
rewrite (proj1 (AddConnectInvRelation 1 k)).
move=> H9.
rewrite H9.
reflexivity.
rewrite (proj1 (MultConnectInvRelation (S k) M)).
rewrite (proj1 (AddConnectInvRelation 1 k)).
reflexivity.
suff: (snd (MultConnectInv k M u1) = snd (MultConnectInv (S k) M (MultConnect (S k) M (AddConnect 1 k (inr (fst (MultConnectInv k M u1))), snd (MultConnectInv k M u1))))).
move=> H9.
rewrite H9.
rewrite H8.
rewrite (proj1 (MultConnectInvRelation (S k) M)).
reflexivity.
rewrite (proj1 (MultConnectInvRelation (S k) M)).
reflexivity.
move=> u H6.
apply (Full_intro (Count (S k * M)) u).
elim (proj2 (proj2 (SingularValueRCHNature K M N A))).
move=> U.
elim.
move=> V H5.
suff: (forall (m : (Count (M + N - k))), (proj1_sig m + k < M + N)%nat).
move=> H6.
suff: (exists (v : Count (M + N) -> RCT K), RCnNorm K (M + N) v = 1 /\ SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (S k)) (AdjointMatrixRC K (M + N) (S k) Q) v /\ SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (M + N - k)) (fun (m : Count (M + N - k)) (n : Count (M + N)) => ConjugateRC K (U n (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m)))) v).
elim.
move=> v.
rewrite (FiniteSpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (S k)).
rewrite (FiniteSpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (M + N - k)).
move=> H7.
elim (proj1 (proj2 H7)).
move=> a H8.
suff: (RCnNorm K (S k) a = 1).
move=> H9.
elim (UnitaryMarixRCComplementExists K 1 k (fun (m : Count (S k)) (n : Count 1) => a m)).
move=> U0 H10.
exists (MTranspose (RCfield K) (S k) (S k) (MBlockW (RCfield K) (1 + k) 1 k (fun (m : Count (S k)) (n : Count 1) => a m) U0)).
exists v.
apply conj.
apply (proj1 (MmultILRSame (RCfield K) (S k) (MTranspose (RCfield K) (S k) (S k) (MBlockW (RCfield K) (1 + k) 1 k (fun (m : Count (S k)) (n : Count 1) => a m) U0)) (AdjointMatrixRC K (S k) (S k) (MTranspose (RCfield K) (S k) (S k) (MBlockW (RCfield K) (1 + k) 1 k (fun (m : Count (S k)) (n : Count 1) => a m) U0))))).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (Mmult (RCfield K) (S k) (S k) (S k) (MTranspose (RCfield K) (S k) (S k) (MBlockW (RCfield K) (1 + k) 1 k (fun (m : Count (S k)) (n : Count 1) => a m) U0)) (AdjointMatrixRC K (S k) (S k) (MTranspose (RCfield K) (S k) (S k) (MBlockW (RCfield K) (1 + k) 1 k (fun (m : Count (S k)) (n : Count 1) => a m) U0))) x y = ConjugateRC K (Mmult (RCfield K) (S k) (S k) (S k) (AdjointMatrixRC K (S k) (S k) (MBlockW (RCfield K) (1 + k) 1 k (fun (m : Count (S k)) (n : Count 1) => a m) U0)) (MBlockW (RCfield K) (1 + k) 1 k (fun (m : Count (S k)) (n : Count 1) => a m) U0) x y)).
move=> H11.
rewrite H11.
rewrite H10.
unfold MI.
simpl.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H12.
apply (ConjugateRCI K).
move=> H12.
apply (ConjugateRCO K).
unfold Mmult.
apply (FiniteSetInduction {n : nat | (n < S k)%nat} (exist (Finite (Count (S k))) (Full_set {n : nat | (n < S k)%nat}) (CountFinite (S k)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite (ConjugateRCO K).
reflexivity.
move=> B b H11 H12 H13 H14.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H14.
rewrite (Proposition_4_8_1_1_RC K).
rewrite (Proposition_4_8_2_RC K).
unfold AdjointMatrixRC.
rewrite (ConjugateRCInvolutive K).
reflexivity.
apply H13.
apply H13.
apply conj.
rewrite H8.
apply functional_extensionality.
move=> x.
unfold Mmult.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S k)%nat} (exist (Finite {n : nat | (n < S k)%nat}) (Full_set {n : nat | (n < S k)%nat}) (CountFinite (S k)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H11 H12 H13 H14.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H14.
suff: ((exist (fun (l : nat) => (l < S k)%nat) O (le_n_S 0 k (le_0_n k))) = AddConnect 1 k (inl Single)).
move=> H15.
rewrite H15.
unfold MTranspose.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 k) (inl Single)).
reflexivity.
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 k) Single).
reflexivity.
apply H13.
apply H13.
suff: (forall (x y : R), x >= 0 -> y >= 0 -> x * x <= y * y -> x <= y).
move=> H11.
apply H11.
apply (proj1 (RCnNormNature K M (MVmult (RCfield K) M (M + N) (MTranspose (RCfield K) (M + N) M A) v))).
apply (proj1 (SingularValueRCHNature K M N A) (exist (fun (l : nat) => (l < M)%nat) k H3)).
rewrite - (proj2 (RCnNormNature K M (MVmult (RCfield K) M (M + N) (MTranspose (RCfield K) (M + N) M A) v))).
elim (proj2 (proj2 H7)).
move=> b H12.
suff: (forall (m : Count (M + N)), ~ (proj1_sig m < k)%nat -> (proj1_sig m - k < M + N - k)%nat).
move=> H13.
suff: (v = MVmult (RCfield K) (M + N) (M + N) (fun (m n : Count (M + N)) => ConjugateRC K (U m n)) (fun (m : Count (M + N)) => match excluded_middle_informative (proj1_sig m < k)%nat with
  | left _ => RCO K
  | right H => b (exist (fun (l : nat) => (l < M + N - k)%nat) (proj1_sig m - k)%nat (H13 m H))
end)).
move=> H14.
suff: (RCRe K (RCnInnerProduct K (M + N - k) b b) = 1).
move=> H15.
rewrite H14.
unfold MVmult.
rewrite (RCnInnerProductMatrix K M).
rewrite (proj2 (MVectorMatrixRelation (RCfield K) (M + N))).
rewrite (proj2 (MVectorMatrixRelation (RCfield K) M)).
rewrite {2} (proj2 (proj2 H5)).
rewrite {1} (proj2 (proj2 H5)).
rewrite (MTransMult (RCfield K) (M + N) (M + N) M).
rewrite (Mmult_assoc (RCfield K) M (M + N) (M + N) 1).
rewrite - (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) 1).
suff: (Mmult (RCfield K) (M + N) (M + N) (M + N) (MTranspose (RCfield K) (M + N) (M + N) U) (fun (m n : Count (M + N)) => ConjugateRC K (U m n)) = MI (RCfield K) (M + N)).
move=> H16.
rewrite H16.
rewrite (Mmult_I_l (RCfield K) (M + N) 1).
rewrite (MTransMult (RCfield K) (M + N) M M).
rewrite (Mmult_assoc (RCfield K) M M (M + N) 1).
rewrite (AdjointMatrixRCMult K M M 1).
rewrite (Mmult_assoc (RCfield K) 1 M M 1).
rewrite - (Mmult_assoc (RCfield K) M M M 1).
suff: (Mmult (RCfield K) M M M (AdjointMatrixRC K M M (MTranspose (RCfield K) M M (AdjointMatrixRC K M M V))) (MTranspose (RCfield K) M M (AdjointMatrixRC K M M V)) = MI (RCfield K) M).
move=> H17.
rewrite H17.
rewrite (Mmult_I_l (RCfield K) M 1).
rewrite (AdjointMatrixRCMult K M (M + N) 1).
rewrite (Mmult_assoc (RCfield K) 1 (M + N) M 1).
rewrite - (Mmult_assoc (RCfield K) (M + N) M (M + N) 1).
suff: (AdjointMatrixRC K M (M + N) (MTranspose (RCfield K) (M + N) M (MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun m : {n : nat | (n < M)%nat} => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))) (MO (RCfield K) N M))) = MBlockH (RCfield K) M N M (MDiag (RCfield K) M (fun m : {n : nat | (n < M)%nat} => IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))) (MO (RCfield K) N M)).
move=> H18.
rewrite H18.
rewrite (MBlockHTranspose (RCfield K) M N M).
rewrite (MBlockHMult (RCfield K) M N M (M + N)).
rewrite (MBlockWMult (RCfield K) M M M N).
rewrite (MDiagTrans (RCfield K) M).
rewrite (MDiagMult (RCfield K) M).
rewrite (Mmult_O_l (RCfield K) N M (M + N)).
rewrite (MTransO (RCfield K) N M).
rewrite (Mmult_O_r (RCfield K) M M N).
unfold Mmult at 1.
rewrite (MySumF2Included {n : nat | (n < M + N)%nat} (FiniteIm (Count (M + N - k)) (Count (M + N)) (fun (m : Count (M + N - k)) => exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m)) (exist (Finite (Count (M + N - k))) (Full_set (Count (M + N - k))) (CountFinite (M + N - k))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O {n : nat | (n < M + N)%nat}).
rewrite CM_O_r.
rewrite - (Rmult_1_r (SingularValueRCH K M N A (exist (fun (l : nat) => (l < M)%nat) k H3) * SingularValueRCH K M N A (exist (fun (l : nat) => (l < M)%nat) k H3))).
rewrite - H15.
unfold RCnInnerProduct.
apply (FiniteSetInduction (Count (M + N - k)) (exist (Finite (Count (M + N - k))) (Full_set (Count (M + N - k))) (CountFinite (M + N - k)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite (ConjugateRCO K).
suff: (RCRe K (RCO K) = 0).
move=> H19.
rewrite H19.
rewrite Rmult_0_r.
right.
reflexivity.
elim K.
reflexivity.
reflexivity.
move=> C c H19 H20 H21 H22.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Proposition_4_8_1_1_RC K).
rewrite (RCReplus K).
rewrite (RCReplus K).
rewrite Rmult_plus_distr_l.
apply Rplus_le_compat.
apply H22.
unfold Basics.compose.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < M + N)%nat} (FiniteSingleton {n : nat | (n < M + N)%nat} (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig c + k)%nat (H6 c)))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
unfold MVectorToMatrix.
unfold AdjointMatrixRC.
simpl.
elim (excluded_middle_informative (proj1_sig c + k < k)%nat).
move=> H23.
elim (le_not_lt k (proj1_sig c + k) (le_plus_r (proj1_sig c) k) H23).
move=> H23.
suff: (exist (fun (l : nat) => (l < M + N - k)%nat) (proj1_sig c + k - k)%nat (H13 (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig c + k)%nat (H6 c)) H23) = c).
move=> H24.
rewrite H24.
unfold MBlockH.
unfold MBlockW.
suff: (proj1_sig (AddConnect M N (AddConnectInv M N (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig c + k)%nat (H6 c)))) >= k)%nat.
elim (AddConnectInv M N (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig c + k)%nat (H6 c))).
move=> m.
rewrite - (proj1 (AddConnectNature M N) m).
move=> H25.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H26.
suff: (forall (x : RCT K), RCRe K (ConjugateRC K x) = RCRe K x).
move=> H27.
rewrite H27.
rewrite (RCmult_comm K (ConjugateRC K (b c))).
rewrite (RCmult_assoc K).
rewrite - (IRRCmult K).
suff: (forall (r : R) (x : RCT K), RCRe K (RCmult K (IRRC K r) x) = r * (RCRe K x)).
move=> H28.
rewrite H28.
apply Rmult_le_compat_r.
suff: (forall (x : RCT K), 0 <= RCRe K (RCmult K x (ConjugateRC K x))).
move=> H29.
apply (H29 (b c)).
elim K.
move=> x.
apply Rge_le.
apply Formula_1_3.
move=> x.
simpl.
unfold Conjugate.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
unfold Rminus.
rewrite (Ropp_mult_distr_r (x CIm) (- x CIm)).
rewrite (Ropp_involutive (x CIm)).
apply Rplus_le_le_0_compat.
apply Rge_le.
apply Formula_1_3.
apply Rge_le.
apply Formula_1_3.
apply Rmult_le_compat.
apply Rge_le.
apply (proj1 (SingularValueRCHNature K M N A) m).
apply Rge_le.
apply (proj1 (SingularValueRCHNature K M N A) m).
apply Rge_le.
apply (proj1 (proj2 (SingularValueRCHNature K M N A))).
apply H25.
apply Rge_le.
apply (proj1 (proj2 (SingularValueRCHNature K M N A))).
apply H25.
elim K.
move=> r x.
reflexivity.
move=> r x.
simpl.
unfold Cmult.
rewrite CmakeRe.
unfold IRC.
rewrite (CmakeRe r 0).
rewrite (CmakeIm r 0).
rewrite (Rmult_0_l (x CIm)).
apply (Rminus_0_r (r * x CRe)).
elim K.
move=> x.
reflexivity.
move=> x.
apply (CmakeRe (x CRe) (- x CIm)).
elim.
reflexivity.
move=> m H25.
unfold MO.
suff: (RCmult K = Fmul (RCfield K)).
move=> H26.
rewrite H26.
rewrite (Fmul_O_l (RCfield K)).
rewrite (Fmul_O_r (RCfield K)).
suff: (RCRe K (ConjugateRC K (FO (RCfield K))) = 0).
move=> H27.
rewrite H27.
apply Rmult_le_pos.
apply Rge_le.
apply Formula_1_3.
suff: (forall (x : RCT K), 0 <= RCRe K (RCmult K x (ConjugateRC K x))).
move=> H28.
apply (H28 (b c)).
elim K.
move=> x.
apply Rge_le.
apply Formula_1_3.
move=> x.
simpl.
unfold Conjugate.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
unfold Rminus.
rewrite (Ropp_mult_distr_r (x CIm) (- x CIm)).
rewrite (Ropp_involutive (x CIm)).
apply Rplus_le_le_0_compat.
apply Rge_le.
apply Formula_1_3.
apply Rge_le.
apply Formula_1_3.
elim K.
reflexivity.
apply (CmakeRe 0 (- 0)).
reflexivity.
rewrite (proj2 (AddConnectInvRelation M N)).
apply (le_plus_r (proj1_sig c) k).
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig c) k).
apply (minus_plus k (proj1_sig c)).
move=> u.
elim.
move=> u0.
rewrite - {1} (proj2 (AddConnectInvRelation M N) (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig c + k)%nat (H6 c))).
unfold MBlockH.
unfold MBlockW.
unfold MDiag.
elim (AddConnectInv M N (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig c + k)%nat (H6 c))).
move=> m.
rewrite - {1} (proj2 (AddConnectInvRelation M N) u0).
elim (AddConnectInv M N u0).
move=> n H23 H24.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig n)).
move=> H25.
elim H23.
suff: (m = n).
move=> H26.
rewrite H26.
apply (In_singleton {n : nat | (n < M + N)%nat} (AddConnect M N (inl n))).
apply sig_map.
apply H25.
move=> H25.
apply (Fmul_O_l (RCfield K)).
move=> n H23 H24.
apply (Fmul_O_l (RCfield K)).
move=> n H23 H24.
apply (Fmul_O_l (RCfield K)).
move=> u H23.
apply (Full_intro {n : nat | (n < M + N)%nat} u).
apply H21.
apply H21.
move=> u.
elim.
move=> u0 H19 H20.
unfold AdjointMatrixRC.
unfold MVectorToMatrix.
elim (excluded_middle_informative (proj1_sig u0 < k)%nat).
move=> H21.
rewrite (ConjugateRCO K).
apply (Fmul_O_l (RCfield K)).
move=> H21.
elim (le_or_lt k (proj1_sig u0)).
move=> H22.
elim H19.
suff: (proj1_sig u0 - k < M + N - k)%nat.
move=> H23.
apply (Im_intro (Count (M + N - k)) (Count (M + N)) (Full_set (Count (M + N - k))) (fun (m : Count (M + N - k)) => exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m)) (exist (fun (l : nat) => (l < M + N - k)%nat) (proj1_sig u0 - k)%nat H23)).
apply (Full_intro (Count (M + N - k))).
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig u0 - k) k).
apply (le_plus_minus k (proj1_sig u0) H22).
apply (plus_lt_reg_l (proj1_sig u0 - k) (M + N - k) k).
rewrite (le_plus_minus_r k (proj1_sig u0) H22).
rewrite (le_plus_minus_r k (M + N)).
apply (proj2_sig u0).
apply (le_trans k (proj1_sig u0) (M + N) H22 (lt_le_weak (proj1_sig u0) (M + N) (proj2_sig u0))).
move=> H22.
elim (H21 H22).
move=> u1 u2 H19 H20 H21.
apply sig_map.
apply (plus_reg_l (proj1_sig u1) (proj1_sig u2) k).
rewrite (plus_comm k (proj1_sig u1)).
rewrite (plus_comm k (proj1_sig u2)).
suff: ((proj1_sig u1 + k)%nat = proj1_sig (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig u1 + k)%nat (H6 u1))).
move=> H22.
rewrite H22.
rewrite H21.
reflexivity.
reflexivity.
move=> u H19.
apply (Full_intro {n : nat | (n < M + N)%nat} u).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold AdjointMatrixRC.
unfold MTranspose.
unfold MBlockH.
unfold MDiag.
elim (AddConnectInv M N x).
move=> x0.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y)).
move=> H18.
suff: (forall (r : R), ConjugateRC K (IRRC K r) = IRRC K r).
move=> H19.
apply (H19 (SingularValueRCH K M N A x0)).
elim K.
move=> r.
reflexivity.
move=> r.
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H19.
rewrite H19.
apply (CmakeRe (IRRC CK r CRe)).
move=> H19.
rewrite H19.
simpl.
unfold IRC.
unfold Conjugate.
rewrite (CmakeIm (Cmake r 0 CRe) (- Cmake r 0 CIm)).
rewrite (CmakeIm r 0).
apply Ropp_0.
move=> H18.
apply (ConjugateRCO K).
move=> H18.
apply (ConjugateRCO K).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (ConjugateRC K (MI (RCfield K) M x y) = MI (RCfield K) M x y).
move=> H17.
rewrite - H17.
rewrite - (proj1 (proj2 H5)).
unfold Mmult.
apply (FiniteSetInduction {n : nat | (n < M)%nat} (exist (Finite (Count M)) (Full_set {n : nat | (n < M)%nat}) (CountFinite M))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (ConjugateRCO K).
reflexivity.
move=> C c H18 H19 H20 H21.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Proposition_4_8_1_1_RC K).
rewrite (Proposition_4_8_2_RC K).
rewrite H21.
reflexivity.
apply H20.
apply H20.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H17.
apply (ConjugateRCI K).
move=> H17.
apply (ConjugateRCO K).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (ConjugateRC K (MI (RCfield K) (M + N) x y) = MI (RCfield K) (M + N) x y).
move=> H16.
rewrite - H16.
rewrite - (proj1 H5).
unfold Mmult.
apply (FiniteSetInduction {n : nat | (n < M + N)%nat} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)%nat}) (CountFinite (M + N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (ConjugateRCO K).
reflexivity.
move=> C c H17 H18 H19 H20.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Proposition_4_8_1_1_RC K).
rewrite (Proposition_4_8_2_RC K).
rewrite H20.
unfold AdjointMatrixRC.
rewrite (ConjugateRCInvolutive K).
reflexivity.
apply H19.
apply H19.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H16.
apply (ConjugateRCI K).
move=> H16.
apply (ConjugateRCO K).
rewrite - (Rmult_1_l 1).
rewrite - (proj1 H7).
rewrite - (proj2 (RCnNormNature K (M + N) v)).
rewrite H14.
rewrite (RCnInnerProductMatrix K (M + N)).
unfold MVmult.
rewrite (proj2 (MVectorMatrixRelation (RCfield K) (M + N))).
rewrite (AdjointMatrixRCMult K (M + N) (M + N) 1).
rewrite (Mmult_assoc (RCfield K) 1 (M + N) (M + N) 1).
rewrite - (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) 1).
suff: (Mmult (RCfield K) (M + N) (M + N) (M + N) (AdjointMatrixRC K (M + N) (M + N) (fun (m n : Count (M + N)) => ConjugateRC K (U m n))) (fun (m n : Count (M + N)) => ConjugateRC K (U m n)) = MI (RCfield K) (M + N)).
move=> H15.
rewrite H15.
rewrite (Mmult_I_l (RCfield K) (M + N) 1).
rewrite - (RCnInnerProductMatrix K (M + N)).
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count (M + N)) (FiniteIm (Count (M + N - k)) (Count (M + N)) (fun (m : Count (M + N - k)) => exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m)) (exist (Finite (Count (M + N - k))) (Full_set (Count (M + N - k))) (CountFinite (M + N - k))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count (M + N))).
rewrite (CM_O_r (RCPCM K)).
apply f_equal.
apply (MySumF2Same (Count (M + N - k)) (exist (Finite (Count (M + N - k))) (Full_set (Count (M + N - k))) (CountFinite (M + N - k))) (RCPCM K)).
move=> u H16.
unfold Basics.compose.
simpl.
elim (excluded_middle_informative (proj1_sig u + k < k)%nat).
move=> H17.
elim (le_not_lt k (proj1_sig u + k) (le_plus_r (proj1_sig u) k) H17).
move=> H17.
suff: ((exist (fun (l : nat) => (l < M + N - k)%nat) (proj1_sig u + k - k)%nat (H13 (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig u + k)%nat (H6 u)) H17)) = u).
move=> H18.
rewrite H18.
reflexivity.
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig u) k).
apply (minus_plus k (proj1_sig u)).
move=> u.
elim.
move=> u0 H16 H17.
elim (excluded_middle_informative (proj1_sig u0 < k)%nat).
move=> H18.
apply (Fmul_O_l (RCfield K)).
move=> H18.
elim H16.
apply (Im_intro (Count (M + N - k)) (Count (M + N)) (Full_set (Count (M + N - k))) (fun (m : Count (M + N - k)) => exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m)) (exist (fun (l : nat) => (l < M + N - k)%nat) (proj1_sig u0 - k)%nat (H13 u0 H18))).
apply (Full_intro (Count (M + N - k))).
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig u0 - k) k).
apply (le_plus_minus k (proj1_sig u0)).
elim (le_or_lt k (proj1_sig u0)).
apply.
move=> H19.
elim (H18 H19).
move=> u1 u2 H16 H17 H18.
apply sig_map.
apply (plus_reg_l (proj1_sig u1) (proj1_sig u2) k).
rewrite (plus_comm k (proj1_sig u1)).
suff: ((proj1_sig u1 + k)%nat = proj1_sig (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig u1 + k)%nat (H6 u1))).
move=> H19.
rewrite H19.
rewrite H18.
apply (plus_comm (proj1_sig u2) k).
reflexivity.
move=> u H16.
apply (Full_intro (Count (M + N)) u).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (ConjugateRC K (MI (RCfield K) (M + N) x y) = MI (RCfield K) (M + N) x y).
move=> H15.
rewrite - H15.
rewrite - (proj1 H5).
unfold Mmult.
apply (FiniteSetInduction {n : nat | (n < M + N)%nat} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)%nat}) (CountFinite (M + N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (ConjugateRCO K).
reflexivity.
move=> C c H16 H17 H18 H19.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H19.
rewrite (Proposition_4_8_1_1_RC K).
rewrite (Proposition_4_8_2_RC K).
reflexivity.
apply H18.
apply H18.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H15.
apply (ConjugateRCI K).
move=> H15.
apply (ConjugateRCO K).
rewrite H12.
unfold MVmult.
unfold Mmult.
apply functional_extensionality.
move=> x.
unfold MMatrixToVector.
rewrite (MySumF2Included (Count (M + N)) (FiniteIm (Count (M + N - k)) (Count (M + N)) (fun (m : Count (M + N - k)) => exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m)) (exist (Finite (Count (M + N - k))) (Full_set (Count (M + N - k))) (CountFinite (M + N - k))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count (M + N))).
rewrite (CM_O_r (FPCM (RCfield K))).
apply (FiniteSetInduction (Count (M + N - k)) (exist (Finite (Count (M + N - k))) (Full_set (Count (M + N - k))) (CountFinite (M + N - k)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> C c H14 H15 H16 H17.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H17.
unfold Basics.compose.
unfold MVectorToMatrix.
simpl.
elim (excluded_middle_informative (proj1_sig c + k < k)%nat).
move=> H18.
elim (le_not_lt k (proj1_sig c + k) (le_plus_r (proj1_sig c) k) H18).
move=> H18.
suff: ((exist (fun (l : nat) => (l < M + N - k)%nat) (proj1_sig c + k - k)%nat (H13 (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig c + k)%nat (H6 c)) H18)) = c).
move=> H19.
rewrite H19.
rewrite (RCmult_comm K).
reflexivity.
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig c) k).
apply (minus_plus k (proj1_sig c)).
apply H16.
apply H16.
move=> u.
elim.
move=> u0 H14 H15.
unfold MVectorToMatrix.
elim (excluded_middle_informative (proj1_sig u0 < k)%nat).
move=> H16.
apply (Fmul_O_r (RCfield K)).
move=> H16.
elim H14.
apply (Im_intro (Count (M + N - k)) (Count (M + N)) (Full_set (Count (M + N - k))) (fun (m : Count (M + N - k)) => exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m)) (exist (fun (l : nat) => (l < M + N - k)%nat) (proj1_sig u0 - k)%nat (H13 u0 H16))).
apply (Full_intro (Count (M + N - k))).
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig u0 - k) k).
apply (le_plus_minus k (proj1_sig u0)).
elim (le_or_lt k (proj1_sig u0)).
apply.
move=> H17.
elim (H16 H17).
move=> u1 u2 H14 H15 H16.
apply sig_map.
apply (plus_reg_l (proj1_sig u1) (proj1_sig u2) k).
rewrite (plus_comm k (proj1_sig u1)).
suff: ((proj1_sig u1 + k)%nat = proj1_sig (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig u1 + k)%nat (H6 u1))).
move=> H17.
rewrite H17.
rewrite H16.
apply (plus_comm (proj1_sig u2) k).
reflexivity.
move=> u H14.
apply (Full_intro (Count (M + N)) u).
move=> m H13.
suff: (k <= proj1_sig m)%nat.
move=> H14.
apply (plus_lt_reg_l (proj1_sig m - k) (M + N - k) k).
rewrite (le_plus_minus_r k (proj1_sig m) H14).
rewrite (le_plus_minus_r k (M + N)).
apply (proj2_sig m).
apply (le_trans k (proj1_sig m) (M + N) H14 (lt_le_weak (proj1_sig m) (M + N) (proj2_sig m))).
elim (le_or_lt k (proj1_sig m)).
apply.
move=> H14.
elim (H13 H14).
move=> x y H11 H12 H13.
apply (Rnot_lt_le y x).
move=> H14.
apply (Rle_not_lt (y * y) (x * x) H13).
apply (Rmult_le_0_lt_compat y x y x).
apply (Rge_le y 0 H12).
apply (Rge_le y 0 H12).
apply H14.
apply H14.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite (SingleSame x).
rewrite (SingleSame y).
unfold Mmult.
unfold MI.
elim (Nat.eq_dec (proj1_sig Single) (proj1_sig Single)).
move=> H10.
simpl.
suff: (RCI K = IRRC K (RCRe K (RCnInnerProduct K (S k) a a))).
move=> H11.
rewrite H11.
unfold RCnInnerProduct.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S k)%nat} (exist (Finite {n : nat | (n < S k)%nat}) (Full_set {n : nat | (n < S k)%nat}) (CountFinite (S k)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
elim K.
reflexivity.
simpl.
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H12.
rewrite H12.
unfold IRC.
rewrite (CmakeRe 0 0).
reflexivity.
move=> H12.
rewrite H12.
unfold IRC.
rewrite (CmakeIm 0 0).
reflexivity.
move=> B b H12 H13 H14 H15.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H15.
rewrite (RCReplus K).
rewrite (IRRCplus K).
unfold AdjointMatrixRC.
suff: (forall (x : RCT K), RCmult K (ConjugateRC K x) x = IRRC K (RCRe K (RCmult K x (ConjugateRC K x)))).
move=> H16.
rewrite (H16 (a b)).
reflexivity.
elim K.
move=> w.
reflexivity.
move=> w.
simpl.
rewrite (Cmult_comm (Conjugate w) w).
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H16.
rewrite H16.
unfold IRC.
rewrite (CmakeRe (Cmult w (Conjugate w) CRe) 0).
reflexivity.
move=> H16.
rewrite H16.
unfold IRC.
rewrite (CmakeIm (Cmult w (Conjugate w) CRe) 0).
unfold Cmult.
rewrite (CmakeIm (w CRe * Conjugate w CRe - w CIm * Conjugate w CIm) (w CRe * Conjugate w CIm + w CIm * Conjugate w CRe)).
unfold Conjugate.
rewrite (CmakeRe (w CRe) (- w CIm)).
rewrite (CmakeIm (w CRe) (- w CIm)).
rewrite (Rmult_comm (w CRe) (- w CIm)).
rewrite - (Rmult_plus_distr_r (- w CIm) (w CIm) (w CRe)).
rewrite (Rplus_opp_l (w CIm)).
apply (Rmult_0_l (w CRe)).
apply H14.
apply H14.
rewrite (proj2 (RCnNormNature K (S k) a)).
rewrite H9.
rewrite (Rmult_1_l 1).
elim K.
reflexivity.
reflexivity.
elim.
reflexivity.
apply (RCnNormNature2 K (S k) a 1).
apply conj.
left.
apply Rlt_0_1.
rewrite - (proj1 H7).
rewrite - (proj2 (RCnNormNature K (M + N) v)).
suff: (v = MVmult (RCfield K) (M + N) (S k) (fun (m : Count (M + N)) (n : Count (S k)) => ConjugateRC K (Q m n)) a).
move=> H9.
rewrite H9.
unfold MVmult.
rewrite (RCnInnerProductMatrix K (M + N)).
rewrite (proj2 (MVectorMatrixRelation (RCfield K) (M + N))).
rewrite (AdjointMatrixRCMult K (M + N) (S k) 1).
rewrite (Mmult_assoc (RCfield K) 1 (S k) (M + N) 1).
rewrite - (Mmult_assoc (RCfield K) (S k) (M + N) (S k) 1).
suff: (Mmult (RCfield K) (S k) (M + N) (S k) (AdjointMatrixRC K (M + N) (S k) (fun (m : Count (M + N)) (n : Count (S k)) => ConjugateRC K (Q m n))) (fun (m : Count (M + N)) (n : Count (S k)) => ConjugateRC K (Q m n)) = MI (RCfield K) (S k)).
move=> H10.
rewrite H10.
rewrite (Mmult_I_l (RCfield K) (S k) 1).
rewrite (RCnInnerProductMatrix K (S k)).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (ConjugateRC K (MI (RCfield K) (S k) x y) = MI (RCfield K) (S k) x y).
move=> H10.
rewrite - H10.
rewrite - H4.
unfold Mmult.
apply (FiniteSetInduction {n : nat | (n < M + N)%nat} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)%nat}) (CountFinite (M + N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (ConjugateRCO K).
reflexivity.
move=> B b H11 H12 H13 H14.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H14.
rewrite (Proposition_4_8_1_1_RC K).
rewrite (Proposition_4_8_2_RC K).
reflexivity.
apply H13.
apply H13.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H10.
apply (ConjugateRCI K).
move=> H10.
apply (ConjugateRCO K).
rewrite H8.
apply functional_extensionality.
move=> x.
unfold MVmult.
unfold Mmult.
unfold MMatrixToVector.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S k)%nat} (exist (Finite {n : nat | (n < S k)%nat}) (Full_set {n : nat | (n < S k)%nat}) (CountFinite (S k)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H9 H10 H11 H12.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H12.
rewrite (RCmult_comm K (a b) (AdjointMatrixRC K (M + N) (S k) Q b x)).
reflexivity.
apply H11.
apply H11.
elim (classic (Intersection (Count (M + N) -> RCT K) (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (S k)) (AdjointMatrixRC K (M + N) (S k) Q)) (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (M + N - k)) (fun (m : Count (M + N - k)) (n : Count (M + N)) => ConjugateRC K (U n (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m))))) = Singleton (Count (M + N) -> RCT K) (VO (RCfield K) (FnVS (RCfield K) (M + N))))).
move=> H7.
elim (DimensionSumEnsembleVS2_exists (RCfield K) (FnVS (RCfield K) (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (S k)) (AdjointMatrixRC K (M + N) (S k) Q)) (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (M + N - k)) (fun (m : Count (M + N - k)) (n : Count (M + N)) => ConjugateRC K (U n (exist (fun l : nat => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m))))) (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (S k)) (AdjointMatrixRC K (M + N) (S k) Q)) (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (M + N - k)) (fun (m : Count (M + N - k)) (n : Count (M + N)) => ConjugateRC K (U n (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m)))))).
move=> H8 H9.
suff: (FiniteDimensionVS (RCfield K) (SubspaceMakeVS (RCfield K) (FnVS (RCfield K) (M + N)) (SumEnsembleVS (RCfield K) (FnVS (RCfield K) (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (S k)) (AdjointMatrixRC K (M + N) (S k) Q)) (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (M + N - k)) (fun (m : Count (M + N - k)) (n : Count (M + N)) => ConjugateRC K (U n (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m)))))) H8)).
move=> H10.
elim (H9 H10).
move=> H11.
elim.
move=> H12 H13.
elim (lt_irrefl (M + N)).
unfold lt.
suff: (S (M + N) = DimensionSubspaceVS (RCfield K) (FnVS (RCfield K) (M + N)) (SumEnsembleVS (RCfield K) (FnVS (RCfield K) (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (S k)) (AdjointMatrixRC K (M + N) (S k) Q)) (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (M + N - k)) (fun (m : Count (M + N - k)) (n : Count (M + N)) => ConjugateRC K (U n (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m)))))) H8 H10).
move=> H14.
rewrite H14.
elim (FnVSDimension (RCfield K) (M + N)).
move=> H15 H16.
rewrite - {11} H16.
apply (Proposition_5_9_1_2 (RCfield K) (FnVS (RCfield K) (M + N))).
rewrite (H13 H7).
suff: (DimensionSubspaceVS (RCfield K) (FnVS (RCfield K) (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (S k)) (AdjointMatrixRC K (M + N) (S k) Q)) (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (S k)) (AdjointMatrixRC K (M + N) (S k) Q)) H11 = S k).
move=> H14.
rewrite H14.
unfold DimensionSubspaceVS.
rewrite (DimensionVSNature2 (RCfield K) (SubspaceMakeVS (RCfield K) (FnVS (RCfield K) (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (M + N - k)) (fun (m : Count (M + N - k)) (n : Count (M + N)) => ConjugateRC K (U n (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m))))) (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (M + N - k)) (fun (m : Count (M + N - k)) (n : Count (M + N)) => ConjugateRC K (U n (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m)))))) H12 (M + N - k) (fun (m : Count (M + N - k)) => exist (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (M + N - k)) (fun (m : Count (M + N - k)) (n : Count (M + N)) => ConjugateRC K (U n (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m))))) (fun (n : Count (M + N)) => ConjugateRC K (U n (exist (fun l : nat => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m)))) (SpanContainSelfVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (M + N - k)) (fun (m : Count (M + N - k)) (n : Count (M + N)) => ConjugateRC K (U n (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m)))) m)) ).
rewrite {1} (le_plus_minus k (M + N)).
reflexivity.
apply (le_trans k M (M + N) (lt_le_weak k M H3) (le_plus_l M N)).
apply (proj2 (FiniteLinearlyIndependentVS (RCfield K) (FnVS (RCfield K) (M + N)) (M + N - k) (fun (m : Count (M + N - k)) (n : Count (M + N)) => ConjugateRC K (U n (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m)))))).
suff: (exists (f : Count (M + N) -> Count (k + (M + N - k))), Bijective f /\ forall (n : Count (M + N)), proj1_sig (f n) = proj1_sig n).
elim.
move=> f H15 a.
elim (proj1 H15).
move=> g H16.
suff: (MySumF2 (Count (M + N - k)) (exist (Finite (Count (M + N - k))) (Full_set (Count (M + N - k))) (CountFinite (M + N - k))) (VSPCM (RCfield K) (FnVS (RCfield K) (M + N))) (fun (n : Count (M + N - k)) => Vmul (RCfield K) (FnVS (RCfield K) (M + N)) (a n) (fun (n0 : Count (M + N)) => ConjugateRC K (U n0 (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig n + k)%nat (H6 n))))) = MVmult (RCfield K) (M + N) (M + N) (fun (m n : Count (M + N)) => ConjugateRC K (U m n)) (fun (m : Count (M + N)) => match AddConnectInv k (M + N - k) (f m) with
  | inl m0 => RCO K
  | inr m0 => a m0
end)).
move=> H17.
rewrite H17.
move=> H18 m.
suff: (a m = MVmult (RCfield K) (M + N) (M + N) (MI (RCfield K) (M + N)) (fun (l : Count (M + N)) => match AddConnectInv k (M + N - k) (f l) with
  | inl _ => RCO K
  | inr p => a p
end) (g (AddConnect k (M + N - k) (inr m)))).
move=> H19.
rewrite H19.
suff: (MI (RCfield K) (M + N) = Mmult (RCfield K) (M + N) (M + N) (M + N) (fun (m n : Count (M + N)) => U n m) (fun (m n : Count (M + N)) => ConjugateRC K (U m n))).
move=> H20.
rewrite H20.
unfold MVmult.
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) 1).
suff: (Mmult (RCfield K) (M + N) (M + N) 1 (fun (m n : Count (M + N)) => ConjugateRC K (U m n)) (MVectorToMatrix (RCfield K) (M + N) (fun l : Count (M + N) => match AddConnectInv k (M + N - k) (f l) with
  | inl _ => RCO K
  | inr p => a p
end)) = MVectorToMatrix (RCfield K) (M + N) (MVmult (RCfield K) (M + N) (M + N) (fun (m n : Count (M + N)) => ConjugateRC K (U m n)) (fun (m : Count (M + N)) => match AddConnectInv k (M + N - k) (f m) with
  | inl _ => RCO K
  | inr l => a l
end))).
move=> H21.
rewrite H21.
rewrite H18.
suff: (MVectorToMatrix (RCfield K) (M + N) (VO (RCfield K) (FnVS (RCfield K) (M + N))) = MO (RCfield K) (M + N) 1).
move=> H22.
rewrite H22.
rewrite (Mmult_O_r (RCfield K) (M + N) (M + N) 1).
reflexivity.
reflexivity.
reflexivity.
unfold MVmult.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (ConjugateRC K (MI (RCfield K) (M + N) x y) = MI (RCfield K) (M + N) x y).
move=> H20.
rewrite - H20.
rewrite - (proj1 H5).
unfold Mmult.
apply (FiniteSetInduction {n : nat | (n < M + N)%nat} (exist (Finite (Count (M + N))) (Full_set {n : nat | (n < M + N)%nat}) (CountFinite (M + N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (ConjugateRCO K).
move=> B b H21 H22 H23 H24.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Proposition_4_8_1_1_RC K).
rewrite (Proposition_4_8_2_RC K).
unfold AdjointMatrixRC.
rewrite (ConjugateRCInvolutive K (U b x)).
rewrite H24.
reflexivity.
apply H23.
apply H23.
unfold MI.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H20.
apply (ConjugateRCI K).
move=> H20.
apply (ConjugateRCO K).
unfold MVmult.
rewrite (Mmult_I_l (RCfield K) (M + N) 1).
rewrite (proj1 (MVectorMatrixRelation (RCfield K) (M + N))).
rewrite (proj2 H16 (AddConnect k (M + N - k) (inr m))).
rewrite (proj1 (AddConnectInvRelation k (M + N - k)) (inr m)).
reflexivity.
apply functional_extensionality.
move=> m.
unfold MVmult.
unfold MMatrixToVector.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < M + N)%nat} (FiniteIm (Count (M + N - k)) (Count (M + N)) (fun (m : Count (M + N - k)) => g (AddConnect k (M + N - k) (inr m))) (exist (Finite (Count (M + N - k))) (Full_set (Count (M + N - k))) (CountFinite (M + N - k))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O {n : nat | (n < M + N)%nat}).
rewrite CM_O_r.
apply (FiniteSetInduction (Count (M + N - k)) (exist (Finite (Count (M + N - k))) (Full_set (Count (M + N - k))) (CountFinite (M + N - k)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H17 H18 H19 H20.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H20.
unfold Basics.compose.
rewrite (RCmult_comm K (a b)).
unfold MVectorToMatrix.
rewrite (proj2 H16 (AddConnect k (M + N - k) (inr b))).
rewrite (proj1 (AddConnectInvRelation k (M + N - k)) (inr b)).
suff: ((exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig b + k)%nat (H6 b)) = g (AddConnect k (M + N - k) (inr b))).
move=> H21.
rewrite H21.
reflexivity.
rewrite - (proj1 H16 (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig b + k)%nat (H6 b))).
apply f_equal.
apply sig_map.
rewrite (proj2 H15).
simpl.
rewrite (plus_comm (proj1_sig b) k).
apply (proj2 (AddConnectNature k (M + N - k)) b).
apply H19.
apply H19.
move=> u.
elim.
move=> u0.
unfold MVectorToMatrix.
move=> H17 H18.
suff: (proj1_sig (AddConnect k (M + N - k) (AddConnectInv k (M + N - k) (f u0))) < k)%nat.
elim (AddConnectInv k (M + N - k) (f u0)).
move=> u1 H19.
apply (Fmul_O_r (RCfield K)).
move=> u1.
rewrite - (proj2 (AddConnectNature k (M + N - k)) u1).
move=> H19.
elim (le_not_lt k (k + proj1_sig u1) (le_plus_l k (proj1_sig u1)) H19).
rewrite (proj2 (AddConnectInvRelation k (M + N - k)) (f u0)).
elim (le_or_lt k (proj1_sig (f u0))).
move=> H19.
elim H17.
suff: (proj1_sig u0 - k < M + N - k)%nat.
move=> H20.
apply (Im_intro (Count (M + N - k)) (Count (M + N)) (Full_set (Count (M + N - k))) (fun (m0 : Count (M + N - k)) => g (AddConnect k (M + N - k) (inr m0))) (exist (fun (l : nat) => (l < M + N - k)%nat) (proj1_sig u0 - k)%nat H20)).
apply (Full_intro (Count (M + N - k))).
rewrite - {1} (proj1 H16 u0).
apply f_equal.
apply sig_map.
rewrite - (le_plus_minus_r k (proj1_sig (f u0)) H19).
rewrite (proj2 H15 u0).
apply (proj2 (AddConnectNature k (M + N - k)) (exist (fun (l : nat) => (l < M + N - k)%nat) (proj1_sig u0 - k)%nat H20)).
apply (plus_lt_reg_l (proj1_sig u0 - k) (M + N - k) k).
rewrite (le_plus_minus_r k (proj1_sig u0)).
rewrite (le_plus_minus_r k (M + N)).
apply (proj2_sig u0).
apply (le_trans k M (M + N) (lt_le_weak k M H3) (le_plus_l M N)).
rewrite - (proj2 H15 u0).
apply H19.
apply.
move=> u1 u2 H17 H18 H19.
suff: (u1 = match AddConnectInv k (M + N - k) (f (g (AddConnect k (M + N - k) (inr u1)))) with
  | inl u3 => u1
  | inr u3 => u3
end).
move=> H20.
rewrite H20.
rewrite H19.
rewrite (proj2 H16).
rewrite (proj1 (AddConnectInvRelation k (M + N - k)) (inr u2)).
reflexivity.
rewrite (proj2 H16).
rewrite (proj1 (AddConnectInvRelation k (M + N - k)) (inr u1)).
reflexivity.
move=> u H17.
apply (Full_intro {n : nat | (n < M + N)%nat} u).
suff: (M + N = k + (M + N - k))%nat.
move=> H15.
rewrite - H15.
exists (fun (m : Count (M + N)) => m).
apply conj.
exists (fun (m : Count (M + N)) => m).
apply conj.
move=> m.
reflexivity.
move=> m.
reflexivity.
move=> m.
reflexivity.
apply (le_plus_minus k (M + N)).
apply (le_trans k M (M + N) (lt_le_weak k M H3) (le_plus_l M N)).
suff: (H11 = (Proposition_5_9_1_1 (RCfield K) (FnVS (RCfield K) (M + N)) (FnVSFiniteDimension (RCfield K) (M + N)) (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (S k)) (AdjointMatrixRC K (M + N) (S k) Q)) (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (S k)) (AdjointMatrixRC K (M + N) (S k) Q)))).
move=> H14.
rewrite H14.
apply le_antisym.
apply (RankLeH (RCfield K) (S k) (M + N)).
rewrite - {1} (proj1 (RegularMatrixRank (RCfield K) (S k) (MI (RCfield K) (S k)))).
rewrite - H4.
apply (RankMultLeR (RCfield K)).
unfold RegularMatrix.
rewrite (DeterminantI (RCfield K) (S k)).
apply (FI_neq_FO (RCfield K)).
apply proof_irrelevance.
apply (Proposition_5_9_1_1 (RCfield K)).
apply (FnVSFiniteDimension (RCfield K) (M + N)).
move=> H7.
elim (classic (exists (v : Count (M + N) -> RCT K), Intersection (Count (M + N) -> RCT K) (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (S k)) (AdjointMatrixRC K (M + N) (S k) Q)) (SpanVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (M + N - k)) (fun (m : Count (M + N - k)) (n : Count (M + N)) => ConjugateRC K (U n (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m))))) v /\ v <> VO (RCfield K) (FnVS (RCfield K) (M + N)))).
elim.
move=> x H8.
exists (RCnmult K (M + N) (IRRC K (/ RCnNorm K (M + N) x)) x).
apply conj.
rewrite (Proposition_4_4_1 K (M + N)).
suff: (forall (a : R), a > 0 -> RCabs K (IRRC K (/ a)) * a = 1).
move=> H9.
apply (H9 (RCnNorm K (M + N) x)).
elim (proj1 (RCnNormNature K (M + N) x)).
apply.
move=> H10.
elim (proj2 H8).
apply (Proposition_4_4_3_2 K (M + N) x H10).
elim K.
move=> a H9.
simpl.
rewrite (Rabs_right (/ a)).
apply (Rinv_l a).
apply (Rgt_not_eq a 0 H9).
left.
apply (Rinv_0_lt_compat a H9).
move=> a H9.
simpl.
rewrite (CnormDefinition (IRC (/ a))).
rewrite (MySqrtNature2 (exist (fun (r : R) => r >= 0) (IRC (/ a) CRe * IRC (/ a) CRe + IRC (/ a) CIm * IRC (/ a) CIm) (CnormSqrtSub (IRC (/ a)))) (/ a)).
apply (Rinv_l a).
apply (Rgt_not_eq a 0 H9).
apply conj.
left.
apply (Rinv_0_lt_compat a H9).
simpl.
unfold IRC.
rewrite (CmakeRe (/ a) 0).
rewrite (CmakeIm (/ a) 0).
rewrite (Rmult_0_l 0).
apply (Rplus_0_r (/ a * / a)).
apply conj.
apply (proj1 (proj2 (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (S k)) (AdjointMatrixRC K (M + N) (S k) Q)))).
elim (proj1 H8).
move=> y H9 H10.
apply H9.
apply (proj1 (proj2 (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (M + N - k)) (fun (m : Count (M + N - k)) (n : Count (M + N)) => ConjugateRC K (U n (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m))))))).
elim (proj1 H8).
move=> y H9 H10.
apply H10.
move=> H8.
elim H7.
apply Extensionality_Ensembles.
apply conj.
move=> x H9.
elim (classic (x = VO (RCfield K) (FnVS (RCfield K) (M + N)))).
move=> H10.
rewrite H10.
apply (In_singleton (Count (M + N) -> RCT K)).
move=> H10.
elim H8.
exists x.
apply conj.
apply H9.
apply H10.
move=> u.
elim.
apply (Intersection_intro (Count (M + N) -> RCT K)).
apply (proj2 (proj2 (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (S k)) (AdjointMatrixRC K (M + N) (S k) Q)))).
apply (proj2 (proj2 (SpanSubspaceVS (RCfield K) (FnVS (RCfield K) (M + N)) (Count (M + N - k)) (fun (m : Count (M + N - k)) (n : Count (M + N)) => ConjugateRC K (U n (exist (fun (l : nat) => (l < M + N)%nat) (proj1_sig m + k)%nat (H6 m))))))).
move=> m.
rewrite {2} (le_plus_minus k (M + N)).
rewrite (plus_comm (proj1_sig m) k).
apply (plus_lt_compat_l (proj1_sig m) (M + N - k) k (proj2_sig m)).
apply (le_trans k M (M + N) (lt_le_weak k M H3) (le_plus_l M N)).
move=> K M N k H1.
suff: (M + N = k + (M + N - k))%nat.
move=> H2.
rewrite H2.
move=> A Q1 H3 B.
elim (UnitaryMarixRCComplementExists K k (M + N - k) Q1 H3).
move=> Q2 H4.
suff: (UnitaryMatrixRC K (k + (M + N - k)) (AdjointMatrixRC K (k + (M + N - k)) (k + (M + N - k)) (MBlockW (RCfield K) (k + (M + N - k)) k (M + N - k) Q1 Q2))).
move=> H5.
rewrite - (UnitaryMatrixRCSaveRCFrobeniusNormL K (k + (M + N - k)) M (AdjointMatrixRC K (k + (M + N - k)) (k + (M + N - k)) (MBlockW (RCfield K) (k + (M + N - k)) k (M + N - k) Q1 Q2)) H5 A).
rewrite (BlockWAdjointMatrixRC K (k + (M + N - k)) k (M + N - k) Q1 Q2).
rewrite (MBlockHMult (RCfield K) k (M + N - k) (k + (M + N - k))).
rewrite - (MBlockHRCFrobeniusNorm K k (M + N - k) M).
rewrite (Rplus_comm (RCFrobeniusNorm K k M (Mmult (RCfield K) k (k + (M + N - k)) M (AdjointMatrixRC K (k + (M + N - k)) k Q1) A) * RCFrobeniusNorm K k M (Mmult (RCfield K) k (k + (M + N - k)) M (AdjointMatrixRC K (k + (M + N - k)) k Q1) A))).
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
rewrite - (UnitaryMatrixRCSaveRCFrobeniusNormL K (k + (M + N - k)) M (AdjointMatrixRC K (k + (M + N - k)) (k + (M + N - k)) (MBlockW (RCfield K) (k + (M + N - k)) k (M + N - k) Q1 Q2)) H5 (Mplus (RCfield K) (k + (M + N - k)) M A (Mopp (RCfield K) (k + (M + N - k)) M (Mmult (RCfield K) (k + (M + N - k)) k M Q1 B)))).
rewrite (BlockWAdjointMatrixRC K (k + (M + N - k)) k (M + N - k) Q1 Q2).
rewrite (MBlockHMult (RCfield K) k (M + N - k) (k + (M + N - k))).
rewrite - (MBlockHRCFrobeniusNorm K k (M + N - k) M).
rewrite - (Rplus_0_l (RCFrobeniusNorm K (M + N - k) M (Mmult (RCfield K) (M + N - k) (k + (M + N - k)) M (AdjointMatrixRC K (k + (M + N - k)) (M + N - k) Q2) A) * RCFrobeniusNorm K (M + N - k) M (Mmult (RCfield K) (M + N - k) (k + (M + N - k)) M (AdjointMatrixRC K (k + (M + N - k)) (M + N - k) Q2) A))).
suff: (Mmult (RCfield K) (M + N - k) (k + (M + N - k)) M (AdjointMatrixRC K (k + (M + N - k)) (M + N - k) Q2) (Mplus (RCfield K) (k + (M + N - k)) M A (Mopp (RCfield K) (k + (M + N - k)) M (Mmult (RCfield K) (k + (M + N - k)) k M Q1 B))) = Mmult (RCfield K) (M + N - k) (k + (M + N - k)) M (AdjointMatrixRC K (k + (M + N - k)) (M + N - k) Q2) A).
move=> H6.
rewrite H6.
apply Rplus_ge_compat_r.
apply Formula_1_3.
rewrite (Mmult_plus_distr_l (RCfield K)).
suff: (Mopp (RCfield K) (k + (M + N - k)) M (Mmult (RCfield K) (k + (M + N - k)) k M Q1 B) = Mmult (RCfield K) (k + (M + N - k)) k M Q1 (Mopp (RCfield K) k M B)).
move=> H6.
rewrite H6.
rewrite - (Mmult_assoc (RCfield K)).
suff: (Mmult (RCfield K) (M + N - k) (k + (M + N - k)) k (AdjointMatrixRC K (k + (M + N - k)) (M + N - k) Q2) Q1 = MO (RCfield K) (M + N - k) k).
move=> H7.
rewrite H7.
rewrite (Mmult_O_l (RCfield K)).
rewrite (Mplus_comm (RCfield K)).
apply (Mplus_O_l (RCfield K)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (Mmult (RCfield K) (M + N - k) (k + (M + N - k)) k (AdjointMatrixRC K (k + (M + N - k)) (M + N - k) Q2) Q1 x y = MI (RCfield K) (k + (M + N - k)) (AddConnect k (M + N - k) (inr x)) (AddConnect k (M + N - k) (inl y))).
move=> H7.
rewrite H7.
unfold MI.
rewrite - (proj2 (AddConnectNature k (M + N - k)) x).
rewrite - (proj1 (AddConnectNature k (M + N - k)) y).
elim (Nat.eq_dec (k + proj1_sig x) (proj1_sig y)).
move=> H8.
elim (lt_irrefl k).
apply (le_trans (S k) (S (k + proj1_sig x)) k (le_n_S k (k + proj1_sig x) (le_plus_l k (proj1_sig x)))).
rewrite H8.
apply (proj2_sig y).
move=> H8.
reflexivity.
rewrite - H4.
rewrite (BlockWAdjointMatrixRC K (k + (M + N - k)) k (M + N - k) Q1 Q2).
rewrite (MBlockHMult (RCfield K) k (M + N - k) (k + (M + N - k)) (k + (M + N - k))).
rewrite (MBlockWMult (RCfield K) k (k + (M + N - k)) k (M + N - k)).
rewrite (MBlockWMult (RCfield K) (M + N - k) (k + (M + N - k)) k (M + N - k)).
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation k (M + N - k))).
rewrite (proj1 (AddConnectInvRelation k (M + N - k))).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold Mopp.
unfold Mmult.
apply (FiniteSetInduction {n : nat | (n < k)%nat} (exist (Finite (Count k)) (Full_set {n : nat | (n < k)%nat}) (CountFinite k))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Fopp_O (RCfield K)).
move=> C c H6 H7 H8 H9.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Fopp_add_distr (RCfield K)).
rewrite H9.
rewrite (Fopp_mul_distr_r (RCfield K)).
reflexivity.
apply H8.
apply H8.
unfold UnitaryMatrixRC.
rewrite (AdjointMatrixRCInvolutive K (k + (M + N - k)) (k + (M + N - k))).
apply (proj1 (MmultILRSame (RCfield K) (k + (M + N - k)) (AdjointMatrixRC K (k + (M + N - k)) (k + (M + N - k)) (MBlockW (RCfield K) (k + (M + N - k)) k (M + N - k) Q1 Q2)) (MBlockW (RCfield K) (k + (M + N - k)) k (M + N - k) Q1 Q2)) H4).
apply (le_plus_minus k (M + N)).
apply (le_trans k M (M + N) H1 (le_plus_l M N)).
Qed.

Lemma Proposition_1_sub : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) (M + N) M), exists ! (X : Matrix (RCfield K) M (M + N)), Mmult (RCfield K) (M + N) (M + N) M (Mmult (RCfield K) (M + N) M (M + N) A X) A = A /\ Mmult (RCfield K) M M (M + N) (Mmult (RCfield K) M (M + N) M X A) X = X /\ AdjointMatrixRC K (M + N) (M + N) (Mmult (RCfield K) (M + N) M (M + N) A X) = Mmult (RCfield K) (M + N) M (M + N) A X /\ AdjointMatrixRC K M M (Mmult (RCfield K) M (M + N) M X A) = Mmult (RCfield K) M (M + N) M X A.
Proof.
move=> K M N A.
apply (unique_existence (fun (X : Matrix (RCfield K) M (M + N)) => Mmult (RCfield K) (M + N) (M + N) M (Mmult (RCfield K) (M + N) M (M + N) A X) A = A /\ Mmult (RCfield K) M M (M + N) (Mmult (RCfield K) M (M + N) M X A) X = X /\ AdjointMatrixRC K (M + N) (M + N) (Mmult (RCfield K) (M + N) M (M + N) A X) = Mmult (RCfield K) (M + N) M (M + N) A X /\ AdjointMatrixRC K M M (Mmult (RCfield K) M (M + N) M X A) = Mmult (RCfield K) M (M + N) M X A)).
apply conj.
elim (proj2 (proj2 (SingularValueRCHNature K M N A))).
move=> U.
elim.
move=> V H1.
rewrite (proj2 (proj2 H1)).
exists (Mmult (RCfield K) M (M + N) (M + N) (Mmult (RCfield K) M M (M + N) V (MBlockW (RCfield K) M M N (MDiag (RCfield K) M
                (fun (m : {n : nat | (n < M)%nat}) => match excluded_middle_informative (SingularValueRCH K M N A m = 0) with 
  | left _ => RCO K
  | right _ => IRRC K (/ SingularValueRCH K M N A m)
end))
             (MO (RCfield K) M N))) (AdjointMatrixRC K (M + N) (M + N) U)).
apply conj.
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) M (M + N)).
rewrite (Mmult_assoc (RCfield K) (M + N) M M (M + N)).
rewrite (Mmult_assoc (RCfield K) M M (M + N) (M + N)).
rewrite - (Mmult_assoc (RCfield K) M M M (M + N)).
rewrite (proj1 (proj2 H1)).
rewrite (Mmult_I_l (RCfield K) M (M + N)).
rewrite - (Mmult_assoc (RCfield K) (M + N) M (M + N) (M + N)).
rewrite - (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) (M + N)).
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) M).
rewrite - (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) M (AdjointMatrixRC K (M + N) (M + N) U)).
rewrite (proj1 H1).
rewrite (Mmult_I_l (RCfield K) (M + N) M).
rewrite (MBlockHMult (RCfield K) M N M (M + N)).
rewrite (MBlockWMult (RCfield K) M M M N).
rewrite (MBlockWMult (RCfield K) N M M N).
rewrite (Mmult_O_r (RCfield K) M M N).
rewrite (Mmult_O_l (RCfield K) N M M).
rewrite (Mmult_O_l (RCfield K) N M N).
rewrite (MDiagMult (RCfield K) M).
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) M).
rewrite - (Mmult_assoc (RCfield K) (M + N) (M + N) M M).
rewrite (MBlockHWWHSame (RCfield K) M N M N).
rewrite (MBlockHWMult (RCfield K) (M + N) M N M).
rewrite (Mmult_O_r (RCfield K) (M + N) N M).
rewrite (Mplus_comm (RCfield K) (M + N) M).
rewrite (Mplus_O_l (RCfield K) (M + N) M).
rewrite (MBlockHMult (RCfield K) M N M M).
rewrite (Mmult_O_l (RCfield K) N M M).
rewrite (MDiagMult (RCfield K) M).
suff: ((fun (m : {n : nat | (n < M)%nat}) =>
            Fmul (RCfield K)
              (Fmul (RCfield K)
                 (IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))
                 (match
                   excluded_middle_informative (SingularValueRCH K M N A m = 0)
                  with | left _=>  RCO K
                  | right _ => IRRC K (/ SingularValueRCH K M N A m)
end))
              (IRRC K (proj1_sig (SingularValueRCHSig K M N A) m)))

= (fun (m : {n : nat | (n < M)%nat}) =>
                  IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))).
move=> H2.
rewrite H2.
reflexivity.
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (SingularValueRCH K M N A m = 0)).
unfold SingularValueRCH.
move=> H2.
rewrite H2.
suff: (IRRC K 0 = RCO K).
move=> H3.
rewrite H3.
apply (Fmul_O_r (RCfield K)).
elim K.
reflexivity.
apply functional_extensionality.
move=> z.
elim (CReorCIm z).
move=> H3.
rewrite H3.
apply (CmakeRe 0 0).
move=> H3.
rewrite H3.
apply (CmakeIm 0 0).
move=> H2.
simpl.
rewrite - (IRRCmult K).
rewrite - (IRRCmult K).
rewrite (Rinv_r (proj1_sig (SingularValueRCHSig K M N A) m) H2).
rewrite Rmult_1_l.
reflexivity.
apply conj.
rewrite (Mmult_assoc (RCfield K) M (M + N) (M + N) M).
rewrite - (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) M).
rewrite (proj1 H1).
rewrite (Mmult_I_l (RCfield K) (M + N) M).
rewrite - (Mmult_assoc (RCfield K) M (M + N) M M).
rewrite (Mmult_assoc (RCfield K) M M M (M + N)).
rewrite - (Mmult_assoc (RCfield K) M M (M + N) (M + N)).
rewrite - (Mmult_assoc (RCfield K) M M M (M + N)).
rewrite (proj1 (proj2 H1)).
rewrite (Mmult_I_l (RCfield K) M (M + N)).
rewrite (Mmult_assoc (RCfield K) M M (M + N) M).
rewrite (MBlockHWMult (RCfield K) M M N M).
rewrite (Mmult_O_l (RCfield K) M N M).
rewrite (MDiagMult (RCfield K) M).
rewrite (Mplus_comm (RCfield K) M M).
rewrite (Mplus_O_l (RCfield K) M M).
rewrite (Mmult_assoc (RCfield K) M M M (M + N)).
rewrite - (Mmult_assoc (RCfield K) M M (M + N) (M + N)).
rewrite (MBlockWMult (RCfield K) M M M N).
rewrite (Mmult_O_r (RCfield K) M M N).
rewrite (MDiagMult (RCfield K) M).
rewrite (Mmult_assoc (RCfield K) M M (M + N) (M + N)).
suff: ((fun (m : {n : nat | (n < M)%nat}) =>
            Fmul (RCfield K)
              (Fmul (RCfield K)
                 match excluded_middle_informative (SingularValueRCH K M N A m = 0)
               with | left _ => RCO K
               | right _ => IRRC K (/ SingularValueRCH K M N A m) end
                 (IRRC K (proj1_sig (SingularValueRCHSig K M N A) m)))
              match excluded_middle_informative (SingularValueRCH K M N A m = 0)
               with | left _ => RCO K
               | right _ => IRRC K (/ SingularValueRCH K M N A m) end)

= (fun (m : {n : nat | (n < M)%nat}) => 
              match excluded_middle_informative (SingularValueRCH K M N A m = 0)
               with | left _ => RCO K
               | right _ => IRRC K (/ SingularValueRCH K M N A m) end)).
move=> H2.
rewrite H2.
reflexivity.
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (SingularValueRCH K M N A m = 0)).
unfold SingularValueRCH.
move=> H2.
rewrite H2.
apply (Fmul_O_r (RCfield K)).
move=> H2.
simpl.
rewrite - (IRRCmult K).
rewrite - (IRRCmult K).
rewrite (Rinv_l (proj1_sig (SingularValueRCHSig K M N A) m) H2).
rewrite Rmult_1_l.
reflexivity.
apply conj.
rewrite - (Mmult_assoc (RCfield K) (M + N) (M + N) M M).
rewrite (Mmult_assoc (RCfield K) (M + N) M M (M + N)).
rewrite (Mmult_assoc (RCfield K) M M (M + N) (M + N)).
rewrite - (Mmult_assoc (RCfield K) M M M (M + N)).
rewrite (proj1 (proj2 H1)).
rewrite (Mmult_I_l (RCfield K) M (M + N)).
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) M (M + N)).
rewrite - (Mmult_assoc (RCfield K) (M + N) M (M + N) (M + N)).
rewrite (MBlockHMult (RCfield K) M N M (M + N)).
rewrite (MBlockWMult (RCfield K) M M M N).
rewrite (MBlockWMult (RCfield K) N M M N).
rewrite (Mmult_O_l (RCfield K) N M N).
rewrite (Mmult_O_l (RCfield K) N M M).
rewrite (Mmult_O_r (RCfield K) M M N).
rewrite (MDiagMult (RCfield K) M).
rewrite (AdjointMatrixRCMult K (M + N) (M + N) (M + N)).
rewrite (AdjointMatrixRCMult K (M + N) (M + N) (M + N)).
rewrite (BlockHAdjointMatrixRC K M N (M + N)).
rewrite (BlockWAdjointMatrixRC K M M N).
rewrite (BlockWAdjointMatrixRC K N M N).
rewrite (MBlockHWWHSame (RCfield K) M N M N).
rewrite (AdjointMatrixRCO K M N).
rewrite (AdjointMatrixRCO K N M).
rewrite (AdjointMatrixRCO K N N).
rewrite (AdjointMatrixRCInvolutive K (M + N) (M + N)).
suff: (AdjointMatrixRC K M M
              (MDiag (RCfield K) M
                 (fun m : {n : nat | (n < M)%nat} =>
                  Fmul (RCfield K)
                    (IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))
                    (match
                      excluded_middle_informative
                        (SingularValueRCH K M N A m = 0)
                     with | left _ => RCO K
                     | right _ => IRRC K (/ SingularValueRCH K M N A m) end)))
= MDiag (RCfield K) M
              (fun m : {n : nat | (n < M)%nat} =>
               Fmul (RCfield K)
                 (IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))
                 (match
                   excluded_middle_informative (SingularValueRCH K M N A m = 0)
                  with | left _ => RCO K
                  | right _ => IRRC K (/ SingularValueRCH K M N A m) end))).
move=> H2.
rewrite H2.
rewrite (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) (M + N)).
reflexivity.
unfold AdjointMatrixRC.
unfold MDiag.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig x)).
move=> H2.
suff: (y = x).
move=> H3.
rewrite H3.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig x)).
move=> H4.
elim (excluded_middle_informative (SingularValueRCH K M N A x = 0)).
move=> H5.
rewrite (Fmul_O_r (RCfield K)).
apply (ConjugateRCO K).
move=> H5.
simpl.
rewrite - (IRRCmult K).
rewrite (Rinv_r (proj1_sig (SingularValueRCHSig K M N A) x) H5).
suff: (IRRC K 1 = RCI K).
move=> H6.
rewrite H6.
apply (ConjugateRCI K).
elim K.
reflexivity.
reflexivity.
elim.
reflexivity.
apply sig_map.
apply H2.
move=> H2.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H3.
elim H2.
rewrite H3.
reflexivity.
move=> H3.
apply (ConjugateRCO K).
rewrite (Mmult_assoc (RCfield K) M (M + N) (M + N) M).
rewrite - (Mmult_assoc (RCfield K) (M + N) (M + N) (M + N) M).
rewrite (proj1 H1).
rewrite (Mmult_I_l (RCfield K) (M + N) M).
rewrite (Mmult_assoc (RCfield K) M M (M + N) M).
rewrite - (Mmult_assoc (RCfield K) M (M + N) M M).
rewrite (MBlockHWMult (RCfield K) M M N M).
rewrite (MDiagMult (RCfield K) M).
rewrite (Mmult_O_l (RCfield K) M N M).
rewrite (Mplus_comm (RCfield K) M M).
rewrite (Mplus_O_l (RCfield K) M M).
rewrite (AdjointMatrixRCMult K M M M).
rewrite (AdjointMatrixRCMult K M M M).
rewrite (AdjointMatrixRCInvolutive K M M).
suff: (AdjointMatrixRC K M M
              (MDiag (RCfield K) M
                 (fun m : {n : nat | (n < M)%nat} =>
                  Fmul (RCfield K)
                    (match
                      excluded_middle_informative
                        (SingularValueRCH K M N A m = 0)
                     with | left _ => RCO K
                     | right _ => IRRC K (/ SingularValueRCH K M N A m) end) (IRRC K (proj1_sig (SingularValueRCHSig K M N A) m))))
= MDiag (RCfield K) M
              (fun m : {n : nat | (n < M)%nat} =>
               Fmul (RCfield K)
                 (match
                   excluded_middle_informative (SingularValueRCH K M N A m = 0)
                  with | left _ => RCO K
                  | right _ => IRRC K (/ SingularValueRCH K M N A m) end) 
                 (IRRC K (proj1_sig (SingularValueRCHSig K M N A) m)))).
move=> H2.
rewrite H2.
rewrite (Mmult_assoc (RCfield K) M M M M).
reflexivity.
unfold AdjointMatrixRC.
unfold MDiag.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig x)).
move=> H2.
suff: (y = x).
move=> H3.
rewrite H3.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig x)).
move=> H4.
elim (excluded_middle_informative (SingularValueRCH K M N A x = 0)).
move=> H5.
rewrite (Fmul_O_l (RCfield K)).
apply (ConjugateRCO K).
move=> H5.
simpl.
rewrite - (IRRCmult K).
rewrite (Rinv_l (proj1_sig (SingularValueRCHSig K M N A) x) H5).
suff: (IRRC K 1 = RCI K).
move=> H6.
rewrite H6.
apply (ConjugateRCI K).
elim K.
reflexivity.
reflexivity.
elim.
reflexivity.
apply sig_map.
apply H2.
move=> H2.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H3.
elim H2.
rewrite H3.
reflexivity.
move=> H3.
apply (ConjugateRCO K).
move=> X Y H1 H2.
rewrite - (proj1 (proj2 H1)).
rewrite - (proj2 (proj2 (proj2 H1))).
rewrite (AdjointMatrixRCMult K M (M + N) M X A).
rewrite - (proj1 H2).
rewrite (Mmult_assoc (RCfield K) (M + N) M (M + N) M A Y A).
rewrite (AdjointMatrixRCMult K (M + N) M M A (Mmult (RCfield K) M (M + N) M Y A)).
rewrite (Mmult_assoc (RCfield K) M M (M + N) M).
rewrite - (AdjointMatrixRCMult K M (M + N) M X A).
rewrite (proj2 (proj2 (proj2 H1))).
rewrite (proj2 (proj2 (proj2 H2))).
rewrite (Mmult_assoc (RCfield K) M M M (M + N)).
rewrite (Mmult_assoc (RCfield K) M (M + N) M (M + N) X A X).
rewrite - (proj1 (proj2 (proj2 H1))).
rewrite (AdjointMatrixRCMult K (M + N) M (M + N) A X).
rewrite - {2} (proj1 H2).
rewrite (AdjointMatrixRCMult K (M + N) (M + N) M).
rewrite (proj1 (proj2 (proj2 H2))).
rewrite - (Mmult_assoc (RCfield K) (M + N) M (M + N) (M + N)).
rewrite - (AdjointMatrixRCMult K (M + N) M (M + N) A X).
rewrite (proj1 (proj2 (proj2 H1))).
rewrite - (Mmult_assoc (RCfield K) M (M + N) (M + N) (M + N)).
rewrite - (Mmult_assoc (RCfield K) M (M + N) M (M + N) X A X).
rewrite (proj1 (proj2 H1)).
rewrite (Mmult_assoc (RCfield K) M (M + N) M (M + N)).
rewrite - (Mmult_assoc (RCfield K) (M + N) M (M + N) (M + N)).
rewrite - (Mmult_assoc (RCfield K) (M + N) (M + N) M (M + N)).
rewrite (proj1 H1).
rewrite - (Mmult_assoc (RCfield K) M (M + N) M (M + N) Y A Y).
apply (proj1 (proj2 H2)).
Qed.

Lemma Proposition_1 : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M N), exists ! (X : Matrix (RCfield K) N M), Mmult (RCfield K) M M N (Mmult (RCfield K) M N M A X) A = A /\ Mmult (RCfield K) N N M (Mmult (RCfield K) N M N X A) X = X /\ AdjointMatrixRC K M M (Mmult (RCfield K) M N M A X) = Mmult (RCfield K) M N M A X /\ AdjointMatrixRC K N N (Mmult (RCfield K) N M N X A) = Mmult (RCfield K) N M N X A.
Proof.
move=> K M N.
elim (le_or_lt M N).
move=> H1.
suff: (N = M + (N - M))%nat.
move=> H2.
rewrite H2.
move=> A.
elim (Proposition_1_sub K M (N - M) (AdjointMatrixRC K M (M + (N - M)) A)).
move=> X H3.
exists (AdjointMatrixRC K M (M + (N - M)) X).
apply conj.
apply conj.
rewrite - {3} (AdjointMatrixRCInvolutive K M (M + (N - M)) A).
rewrite - (proj1 (proj1 H3)).
rewrite (AdjointMatrixRCMult K (M + (N - M)) (M + (N - M)) M).
rewrite (AdjointMatrixRCMult K (M + (N - M)) M (M + (N - M))).
rewrite (AdjointMatrixRCInvolutive K M (M + (N - M)) A).
rewrite (Mmult_assoc (RCfield K) M (M + (N - M)) M (M + (N - M))).
reflexivity.
apply conj.
rewrite - {3} (proj1 (proj2 (proj1 H3))).
rewrite (AdjointMatrixRCMult K M M (M + (N - M))).
rewrite (AdjointMatrixRCMult K M (M + (N - M)) M).
rewrite (AdjointMatrixRCInvolutive K M (M + (N - M)) A).
apply (Mmult_assoc (RCfield K) (M + (N - M)) M (M + (N - M)) M).
apply conj.
rewrite (AdjointMatrixRCMult K M (M + (N - M)) M).
rewrite (AdjointMatrixRCInvolutive K M (M + (N - M)) X).
rewrite - (proj2 (proj2 (proj2 (proj1 H3)))).
rewrite (AdjointMatrixRCMult K M (M + (N - M)) M X).
rewrite (AdjointMatrixRCInvolutive K M (M + (N - M)) A).
reflexivity.
rewrite (AdjointMatrixRCMult K (M + (N - M)) M (M + (N - M))).
rewrite (AdjointMatrixRCInvolutive K M (M + (N - M)) X).
rewrite - (proj1 (proj2 (proj2 (proj1 H3)))).
rewrite (AdjointMatrixRCMult K (M + (N - M)) M (M + (N - M))).
rewrite (AdjointMatrixRCInvolutive K M (M + (N - M)) A).
reflexivity.
move=> Y H4.
rewrite (proj2 H3 (AdjointMatrixRC K (M + (N - M)) M Y)).
apply (AdjointMatrixRCInvolutive K (M + (N - M)) M Y).
apply conj.
rewrite - {3} (proj1 H4).
rewrite (AdjointMatrixRCMult K M M (M + (N - M))).
rewrite (AdjointMatrixRCMult K M (M + (N - M)) M A Y).
apply (Mmult_assoc (RCfield K) (M + (N - M)) M (M + (N - M)) M).
apply conj.
rewrite - {3} (proj1 (proj2 H4)).
rewrite (AdjointMatrixRCMult K (M + (N - M)) (M + (N - M)) M).
rewrite (AdjointMatrixRCMult K (M + (N - M)) M (M + (N - M)) Y A).
apply (Mmult_assoc (RCfield K) M (M + (N - M)) M (M + (N - M))).
apply conj.
rewrite (AdjointMatrixRCMult K (M + (N - M)) M (M + (N - M))).
rewrite (AdjointMatrixRCInvolutive K (M + (N - M)) M Y).
rewrite (AdjointMatrixRCInvolutive K M (M + (N - M)) A).
rewrite - (proj2 (proj2 (proj2 H4))).
apply (AdjointMatrixRCMult K (M + (N - M)) M (M + (N - M)) Y A).
rewrite (AdjointMatrixRCMult K M (M + (N - M)) M).
rewrite (AdjointMatrixRCInvolutive K M (M + (N - M)) A).
rewrite (AdjointMatrixRCInvolutive K (M + (N - M)) M Y).
rewrite - (proj1 (proj2 (proj2 H4))).
apply (AdjointMatrixRCMult K M (M + (N - M)) M A Y).
apply (le_plus_minus M N H1).
move=> H1.
suff: (M = N + (M - N))%nat.
move=> H2.
rewrite H2.
apply (Proposition_1_sub K N (M - N)).
apply (le_plus_minus N M (lt_le_weak N M H1)).
Qed.

Lemma GeneralizedInverseMatrixRCSig : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M N), {X : Matrix (RCfield K) N M | Mmult (RCfield K) M M N (Mmult (RCfield K) M N M A X) A = A /\ Mmult (RCfield K) N N M (Mmult (RCfield K) N M N X A) X = X /\ AdjointMatrixRC K M M (Mmult (RCfield K) M N M A X) = Mmult (RCfield K) M N M A X /\ AdjointMatrixRC K N N (Mmult (RCfield K) N M N X A) = Mmult (RCfield K) N M N X A}.
Proof.
move=> K M N A.
apply constructive_definite_description.
apply (Proposition_1 K M N A).
Qed.

Definition GeneralizedInverseMatrixRC (K : RC) (M N : nat) (A : Matrix (RCfield K) M N) := proj1_sig (GeneralizedInverseMatrixRCSig K M N A).

Definition GeneralizedInverseMatrixRCNature (K : RC) (M N : nat) (A : Matrix (RCfield K) M N) : Mmult (RCfield K) M M N (Mmult (RCfield K) M N M A (GeneralizedInverseMatrixRC K M N A)) A = A /\ Mmult (RCfield K) N N M (Mmult (RCfield K) N M N (GeneralizedInverseMatrixRC K M N A) A) (GeneralizedInverseMatrixRC K M N A) = GeneralizedInverseMatrixRC K M N A /\ AdjointMatrixRC K M M (Mmult (RCfield K) M N M A (GeneralizedInverseMatrixRC K M N A)) = Mmult (RCfield K) M N M A (GeneralizedInverseMatrixRC K M N A) /\ AdjointMatrixRC K N N (Mmult (RCfield K) N M N (GeneralizedInverseMatrixRC K M N A) A) = Mmult (RCfield K) N M N (GeneralizedInverseMatrixRC K M N A) A := proj2_sig (GeneralizedInverseMatrixRCSig K M N A).

Lemma GeneralizedInverseMatrixRCNature2 : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M N) (X : Matrix (RCfield K) N M), (Mmult (RCfield K) M M N (Mmult (RCfield K) M N M A X) A = A /\ Mmult (RCfield K) N N M (Mmult (RCfield K) N M N X A) X = X /\ AdjointMatrixRC K M M (Mmult (RCfield K) M N M A X) = Mmult (RCfield K) M N M A X /\ AdjointMatrixRC K N N (Mmult (RCfield K) N M N X A) = Mmult (RCfield K) N M N X A) -> GeneralizedInverseMatrixRC K M N A = X.
Proof.
move=> K M N A X.
apply (proj2 (proj2 (unique_existence (fun (X : Matrix (RCfield K) N M) => Mmult (RCfield K) M M N (Mmult (RCfield K) M N M A X) A = A /\
Mmult (RCfield K) N N M (Mmult (RCfield K) N M N X A) X = X /\
AdjointMatrixRC K M M (Mmult (RCfield K) M N M A X) =
Mmult (RCfield K) M N M A X /\
AdjointMatrixRC K N N (Mmult (RCfield K) N M N X A) =
Mmult (RCfield K) N M N X A)) (Proposition_1 K M N A)) (GeneralizedInverseMatrixRC K M N A) X (GeneralizedInverseMatrixRCNature K M N A)).
Qed.

Definition ResiRC (K : RC) (M N L : nat) (A : Matrix (RCfield K) M N) (B : Matrix (RCfield K) M L) := Mplus (RCfield K) M L B (Mopp (RCfield K) M L (Mmult (RCfield K) M M L (Mmult (RCfield K) M N M A (GeneralizedInverseMatrixRC K M N A)) B)).

Lemma Lemma1 : forall (K : RC) (M N L : nat) (A : Matrix (RCfield K) M N) (B : Matrix (RCfield K) M L) (X : Matrix (RCfield K) N L), (Mmult (RCfield K) N M L (AdjointMatrixRC K M N A) (Mminus (RCfield K) M L B (Mmult (RCfield K) M N L A X))) = MO (RCfield K) N L <-> ResiRC K M N L A B = Mplus (RCfield K) M L B (Mopp (RCfield K) M L (Mmult (RCfield K) M N L A X)).
Proof.
move=> K M N L A B X.
rewrite (Mmult_plus_distr_l (RCfield K) N M L (AdjointMatrixRC K M N A)).
rewrite (Mopp_mult_distr_r_reverse (RCfield K) N M L (AdjointMatrixRC K M N A) (Mmult (RCfield K) M N L A X)).
apply conj.
move=> H1.
apply (f_equal (fun (Y : Matrix (RCfield K) M L) => Mplus (RCfield K) M L B
  (Mopp (RCfield K) M L
     Y))).
rewrite - (Mplus_O_l (RCfield K) M L B).
rewrite - (Mplus_opp_r (RCfield K) M L (Mmult (RCfield K) M N L A X)).
rewrite (Mplus_assoc (RCfield K) M L).
rewrite (Mmult_plus_distr_l (RCfield K) M M L).
rewrite - (Mmult_assoc (RCfield K) M M N L).
rewrite (proj1 (GeneralizedInverseMatrixRCNature K M N A)).
rewrite - (proj1 (proj2 (proj2 (GeneralizedInverseMatrixRCNature K M N A)))).
rewrite (AdjointMatrixRCMult K M N M A (GeneralizedInverseMatrixRC K M N A)).
rewrite (Mmult_assoc (RCfield K) M N M L).
rewrite (Mmult_plus_distr_l (RCfield K) N M L).
suff: (Mplus (RCfield K) N L
        (Mmult (RCfield K) N M L (AdjointMatrixRC K M N A)
           (Mopp (RCfield K) M L (Mmult (RCfield K) M N L A X)))
        (Mmult (RCfield K) N M L (AdjointMatrixRC K M N A) B)
= Mplus (RCfield K) N L (Mmult (RCfield K) N M L (AdjointMatrixRC K M N A) B)
       (Mopp (RCfield K) N L
          (Mmult (RCfield K) N M L (AdjointMatrixRC K M N A)
          (Mmult (RCfield K) M N L A X)))).
move=> H2.
rewrite H2.
rewrite H1.
rewrite (Mmult_O_r (RCfield K) M N L).
apply (Mplus_O_r (RCfield K) M L (Mmult (RCfield K) M N L A X)).
rewrite (Mplus_comm (RCfield K) N L).
rewrite (Mopp_mult_distr_r (RCfield K) N M L).
reflexivity.
move=> H1.
rewrite (Mopp_mult_distr_r (RCfield K) N M L (AdjointMatrixRC K M N A)
        (Mmult (RCfield K) M N L A X)).
rewrite - (Mmult_plus_distr_l (RCfield K) N M L (AdjointMatrixRC K M N A) B
        (Mopp (RCfield K) M L (Mmult (RCfield K) M N L A X))).
rewrite - H1.
rewrite (Mmult_plus_distr_l (RCfield K) N M L).
rewrite - (Mopp_mult_distr_r (RCfield K) N M L (AdjointMatrixRC K M N A)).
rewrite - (proj1 (proj2 (proj2 (GeneralizedInverseMatrixRCNature K M N A)))).
rewrite - (Mmult_assoc (RCfield K) N M M L).
rewrite - (AdjointMatrixRCMult K M M N).
rewrite (proj1 (GeneralizedInverseMatrixRCNature K M N A)).
apply (Mplus_opp_r (RCfield K) N L (Mmult (RCfield K) N M L (AdjointMatrixRC K M N A) B)).
Qed.

Definition ResiVRC (K : RC) (M N : nat) (A : Matrix (RCfield K) M N) (b : RCn K M) := MMatrixToVector (RCfield K) M (ResiRC K M N 1 A (MVectorToMatrix (RCfield K) M b)).

Lemma Lemma1V : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M N) (b : RCn K M) (x : RCn K N), MVmult (RCfield K) N M (AdjointMatrixRC K M N A) (RCnminus K M b (MVmult (RCfield K) M N A x)) = RCnO K N <-> ResiVRC K M N A b = RCnplus K M b (RCnopp K M (MVmult (RCfield K) M N A x)).
Proof.
move=> K M N A b x.
suff: (RCnplus K M b (RCnopp K M (MVmult (RCfield K) M N A x)) = MMatrixToVector (RCfield K) M (Mplus (RCfield K) M 1 (MVectorToMatrix (RCfield K) M b)
         (Mopp (RCfield K) M 1
            (Mmult (RCfield K) M N 1 A (MVectorToMatrix (RCfield K) N x))))).
move=> H1.
suff: (MVmult (RCfield K) N M (AdjointMatrixRC K M N A)
  (RCnminus K M b (MVmult (RCfield K) M N A x))
= MMatrixToVector (RCfield K) N (Mmult (RCfield K) N M 1 (AdjointMatrixRC K M N A)
        (Mminus (RCfield K) M 1 (MVectorToMatrix (RCfield K) M b)
           (Mmult (RCfield K) M N 1 A (MVectorToMatrix (RCfield K) N x))
           ))).
move=> H2.
apply conj.
move=> H3.
rewrite H1.
apply (f_equal (MMatrixToVector (RCfield K) M)).
apply (proj1 (Lemma1 K M N 1 A (MVectorToMatrix (RCfield K) M b) (MVectorToMatrix (RCfield K) N x))).
rewrite - (proj2 (MVectorMatrixRelation (RCfield K) N) (Mmult (RCfield K) N M 1 (AdjointMatrixRC K M N A)
  (Mminus (RCfield K) M 1 (MVectorToMatrix (RCfield K) M b)
     (Mmult (RCfield K) M N 1 A (MVectorToMatrix (RCfield K) N x))
     ))).
rewrite - H2.
rewrite H3.
reflexivity.
unfold ResiVRC.
move=> H3.
rewrite H2.
rewrite (proj2 (Lemma1 K M N 1 A (MVectorToMatrix (RCfield K) M b) (MVectorToMatrix (RCfield K) N x))).
reflexivity.
rewrite - (proj2 (MVectorMatrixRelation (RCfield K) M) (ResiRC K M N 1 A (MVectorToMatrix (RCfield K) M b))).
rewrite H3.
rewrite H1.
apply (proj2 (MVectorMatrixRelation (RCfield K) M) (Mplus (RCfield K) M 1 (MVectorToMatrix (RCfield K) M b)
        (Mopp (RCfield K) M 1
           (Mmult (RCfield K) M N 1 A (MVectorToMatrix (RCfield K) N x))))).
reflexivity.
reflexivity.
Qed.

Lemma Lemma2 : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M N) (b : RCn K M) (x : RCn K N), (forall (y : RCn K N), RCnNorm K M (RCnminus K M b (MVmult (RCfield K) M N A x)) <= RCnNorm K M (RCnminus K M b (MVmult (RCfield K) M N A y))) <-> MVmult (RCfield K) N M (AdjointMatrixRC K M N A) (RCnminus K M b (MVmult (RCfield K) M N A x)) = RCnO K N.
Proof.
suff: (forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M N) (b : RCn K M), (forall (y : RCn K N), RCnNorm K M b <= RCnNorm K M (RCnminus K M b (MVmult (RCfield K) M N A y))) <-> MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b = RCnO K N).
move=> H1 K M N A b x.
suff: (forall (y : RCn K N), RCnminus K M b (MVmult (RCfield K) M N A y) = RCnminus K M (RCnminus K M b (MVmult (RCfield K) M N A x)) (MVmult (RCfield K) M N A (RCnminus K N y x))).
move=> H2.
apply conj.
move=> H3.
apply (proj1 (H1 K M N A (RCnminus K M b (MVmult (RCfield K) M N A x)))).
move=> y.
suff: (y = RCnminus K N (RCnplus K N y x) x).
move=> H4.
rewrite H4.
rewrite - (H2 (RCnplus K N y x)).
apply (H3 (RCnplus K N y x)).
unfold RCnminus.
unfold Fnminus.
unfold RCnplus.
rewrite (Fnadd_assoc (RCfield K) N y x (Fnopp (RCfield K) N x)).
rewrite (Fnadd_opp_r (RCfield K) N x).
rewrite (Fnadd_comm (RCfield K) N y (FnO (RCfield K) N)).
rewrite (Fnadd_O_l (RCfield K) N y).
reflexivity.
move=> H3 y.
rewrite (H2 y).
apply (proj2 (H1 K M N A (RCnminus K M b (MVmult (RCfield K) M N A x))) H3 (RCnminus K N y x)).
move=> y.
suff: (MVmult (RCfield K) M N A (RCnminus K N y x) = RCnminus K M (MVmult (RCfield K) M N A y) (MVmult (RCfield K) M N A x)).
move=> H2.
rewrite H2.
apply functional_extensionality.
move=> m.
unfold RCnminus.
unfold Fnminus.
unfold RCnplus.
unfold Fnadd.
unfold Fnopp.
rewrite (Fopp_minus_distr (RCfield K) (MVmult (RCfield K) M N A y m) (MVmult (RCfield K) M N A x m)).
rewrite (Fadd_assoc (RCfield K) (b m) (Fopp (RCfield K) (MVmult (RCfield K) M N A x m))).
rewrite - (Fadd_assoc (RCfield K) (Fopp (RCfield K) (MVmult (RCfield K) M N A x m)) (MVmult (RCfield K) M N A x m)).
rewrite (Fadd_opp_l (RCfield K) (MVmult (RCfield K) M N A x m)).
rewrite (Fadd_O_l (RCfield K) (Fopp (RCfield K) (MVmult (RCfield K) M N A y m))).
reflexivity.
unfold MVmult.
suff: (MVectorToMatrix (RCfield K) N (RCnminus K N y x) = Mminus (RCfield K) N 1 (MVectorToMatrix (RCfield K) N y) (MVectorToMatrix (RCfield K) N x)).
move=> H2.
rewrite H2.
rewrite (Mmult_minus_distr_l (RCfield K) M N 1 A).
reflexivity.
apply functional_extensionality.
move=> m.
apply functional_extensionality.
move=> n.
reflexivity.
suff: (forall (K : RC) (M : nat) (x y : RCn K M), RCnNorm K M x <= RCnNorm K M y <-> RCnNorm K M x * RCnNorm K M x <= RCnNorm K M y * RCnNorm K M y).
move=> H1.
suff: (forall (K : RC) (M : nat) (x y : RCn K M), RCnNorm K M x < RCnNorm K M y <-> RCnNorm K M x * RCnNorm K M x < RCnNorm K M y * RCnNorm K M y).
move=> H2 K M N A b.
apply conj.
move=> H3.
elim (proj1 (RCnNormNature K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b))).
move=> H4.
suff: (forall (c : R), c >= 0 -> RCRe K (RCnInnerProduct K M b (MVmult (RCfield K) M N A (RCnmult K N (IRRC K c) (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)))) = c * (RCnNorm K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b) * RCnNorm K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b))).
move=> H5.
suff: (forall (c : R), c >= 0 -> RCnNorm K M (MVmult (RCfield K) M N A
             (RCnmult K N (IRRC K c)
                (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b))) * RCnNorm K M (MVmult (RCfield K) M N A
             (RCnmult K N (IRRC K c)
                (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)))
= c * c * (RCnNorm K M (MVmult (RCfield K) M N A
             (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)) * RCnNorm K M (MVmult (RCfield K) M N A
             (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)))).
move=> H6.
suff: (exists (c : R), c >= 0 /\ 2 * c * (RCnNorm K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b) *
      RCnNorm K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)) > c * c *
     (RCnNorm K M
        (MVmult (RCfield K) M N A
           (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)) *
      RCnNorm K M
        (MVmult (RCfield K) M N A
           (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)))).
elim.
move=> c H7.
elim (Rle_not_lt (RCnNorm K M (RCnminus K M b (MVmult (RCfield K) M N A (RCnmult K N (IRRC K c) (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b))))) (RCnNorm K M b) (H3 (RCnmult K N (IRRC K c) (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)))).
apply (proj2 (H2 K M (RCnminus K M b
     (MVmult (RCfield K) M N A
        (RCnmult K N (IRRC K c)
           (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)))) b)).
rewrite - (Rplus_0_r (RCnNorm K M b * RCnNorm K M b)).
rewrite (Formula_4_15_2 K M b (MVmult (RCfield K) M N A
        (RCnmult K N (IRRC K c)
           (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)))).
unfold Rminus.
rewrite (Rplus_assoc (RCnNorm K M b * RCnNorm K M b)).
apply (Rplus_lt_compat_l (RCnNorm K M b * RCnNorm K M b)).
rewrite (H5 c (proj1 H7)).
rewrite (H6 c (proj1 H7)).
rewrite Rplus_comm.
apply Rlt_minus.
rewrite - (Rmult_assoc 2 c).
apply (proj2 H7).
elim (Formula_1_3 (RCnNorm K M
     (MVmult (RCfield K) M N A
        (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)))).
move=> H7.
elim (Proposition_1_1 0 (2 * (RCnNorm K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b) *
   RCnNorm K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)) / (RCnNorm K M
     (MVmult (RCfield K) M N A
        (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)) *
   RCnNorm K M
     (MVmult (RCfield K) M N A
        (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b))))
).
move=> c H8.
exists c.
apply conj.
left.
apply (proj1 H8).
rewrite (Rmult_comm 2 c).
rewrite (Rmult_assoc c 2).
rewrite (Rmult_assoc c c).
apply (Rmult_gt_compat_l c).
apply (proj1 H8).
rewrite - (Rmult_1_r (2 *
(RCnNorm K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b) *
 RCnNorm K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)))).
rewrite - (Rinv_l (RCnNorm K M
        (MVmult (RCfield K) M N A
           (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)) *
      RCnNorm K M
        (MVmult (RCfield K) M N A
           (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)))).
rewrite - (Rmult_assoc (2 *
(RCnNorm K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b) *
 RCnNorm K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)))).
apply Rmult_lt_compat_r.
apply H7.
apply (proj2 H8).
apply (Rgt_not_eq (RCnNorm K M
       (MVmult (RCfield K) M N A
          (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)) *
     RCnNorm K M
       (MVmult (RCfield K) M N A
          (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b))) 0 H7).
apply Rmult_gt_0_compat.
apply Rmult_gt_0_compat.
apply Two_Gt_Zero.
apply (Rmult_gt_0_compat (RCnNorm K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)) (RCnNorm K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)) H4 H4).
apply Rinv_0_lt_compat.
apply H7.
move=> H7.
rewrite H7.
exists 1.
apply conj.
left.
apply Rlt_0_1.
rewrite (Rmult_1_r 2).
rewrite (Rmult_0_r (1 * 1)).
apply Rmult_gt_0_compat.
apply Two_Gt_Zero.
apply (Rmult_gt_0_compat (RCnNorm K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)) (RCnNorm K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)) H4 H4).
move=> c H6.
suff: (MVmult (RCfield K) M N A
     (RCnmult K N (IRRC K c)
        (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b))
= RCnmult K M (IRRC K c) (MVmult (RCfield K) M N A
      (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b))).
move=> H7.
rewrite H7.
rewrite (Proposition_4_4_1 K M (IRRC K c) (MVmult (RCfield K) M N A
        (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b))).
rewrite (Rmult_assoc c c).
rewrite (Rmult_comm c).
rewrite - (Rmult_assoc c).
rewrite (Rmult_assoc (c *
RCnNorm K M
  (MVmult (RCfield K) M N A (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)))).
rewrite (Rmult_comm (RCnNorm K M
   (MVmult (RCfield K) M N A
      (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)))).
suff: (RCabs K (IRRC K c) = c).
move=> H8.
rewrite H8.
reflexivity.
unfold RCabs.
unfold IRRC.
elim K.
apply (Rabs_pos_eq c (Rge_le c 0 H6)).
rewrite (CnormDefinition (IRC c)).
apply MySqrtNature2.
apply conj.
apply H6.
simpl.
unfold IRC.
rewrite (CmakeRe c 0).
rewrite (CmakeIm c 0).
rewrite (Rmult_0_l 0).
apply (Rplus_0_r (c * c)).
apply functional_extensionality.
move=> m.
unfold MVmult.
unfold RCnmult.
unfold Fnmul.
unfold MMatrixToVector.
unfold MVectorToMatrix.
unfold Mmult at 3.
unfold Mmult at 1.
apply (FiniteSetInduction {n : nat | (n < N)%nat} (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (Fmul_O_r (RCfield K) (IRRC K c)).
reflexivity.
move=> D d H7 H8 H9 H10.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H10.
rewrite (Fmul_add_distr_l (RCfield K)).
rewrite - (Fmul_assoc (RCfield K) (A m d)).
rewrite - (Fmul_assoc (RCfield K) (IRRC K c)).
rewrite (Fmul_comm (RCfield K) (A m d)).
reflexivity.
apply H9.
apply H9.
move=> c H5.
rewrite (RCnInnerProductMatrix K M b).
unfold MVmult.
rewrite (proj2 (MVectorMatrixRelation (RCfield K) M)).
rewrite - (Mmult_assoc (RCfield K) 1 M N 1 (AdjointMatrixRC K M 1 (MVectorToMatrix (RCfield K) M b)) A).
rewrite - (proj2 (RCnNormNature K N
   (MMatrixToVector (RCfield K) N
      (Mmult (RCfield K) N M 1 (AdjointMatrixRC K M N A)
         (MVectorToMatrix (RCfield K) M b))))).
suff: (forall (x : RCT K), c * RCRe K x = RCRe K (RCmult K (ConjugateRC K (IRRC K c)) x)).
move=> H6.
rewrite H6.
rewrite - (Proposition_4_2_2_2 K N (IRRC K c)).
rewrite (RCnInnerProductMatrix K N).
rewrite (proj2 (MVectorMatrixRelation (RCfield K) N)).
rewrite (AdjointMatrixRCMult K N M 1 (AdjointMatrixRC K M N A)
              (MVectorToMatrix (RCfield K) M b)).
rewrite (AdjointMatrixRCInvolutive K M N A).
reflexivity.
elim K.
move=> x.
reflexivity.
move=> x.
simpl.
unfold Conjugate.
unfold IRC.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite Ropp_0.
rewrite (Rmult_0_l (x CIm)).
rewrite (Rminus_0_r (c * x CRe)).
reflexivity.
apply (Proposition_4_4_3_2 K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b)).
move=> H3 y.
apply (proj2 (H1 K M b (RCnminus K M b (MVmult (RCfield K) M N A y)))).
rewrite - (Rplus_0_r (RCnNorm K M b * RCnNorm K M b)).
rewrite (Formula_4_15_2 K M b (MVmult (RCfield K) M N A y)).
suff: (RCnInnerProduct K M b (MVmult (RCfield K) M N A y) = RCnInnerProduct K N (MVmult (RCfield K) N M (AdjointMatrixRC K M N A) b) y).
move=> H4.
rewrite H4.
rewrite H3.
suff: (RCnInnerProduct K N (RCnO K N) y = RCO K).
move=> H5.
rewrite H5.
suff: (2 * RCRe K (RCO K) = 0).
move=> H6.
rewrite H6.
rewrite (Rminus_0_r (RCnNorm K M b * RCnNorm K M b)).
apply (Rplus_le_compat_l (RCnNorm K M b * RCnNorm K M b) 0).
apply Rge_le.
apply Formula_1_3.
elim K.
apply (Rmult_0_r 2).
apply (Rmult_0_r 2).
apply (RCip_mult_0_l K (FnVS (RCfield K) N) (RCnInner_Product_Space K N) y).
rewrite (RCnInnerProductMatrix K M).
rewrite (RCnInnerProductMatrix K N).
rewrite (AdjointMatrixRCMult K N M 1 (AdjointMatrixRC K M N A)
              (MVectorToMatrix (RCfield K) M b)).
rewrite (AdjointMatrixRCInvolutive K M N A).
unfold MVmult.
rewrite (proj2 (MVectorMatrixRelation (RCfield K) M)).
rewrite (Mmult_assoc (RCfield K) 1 M N 1 (AdjointMatrixRC K M 1 (MVectorToMatrix (RCfield K) M b)) A (MVectorToMatrix (RCfield K) N y)).
reflexivity.
move=> K M x y.
apply conj.
move=> H2.
elim (Rle_or_lt (RCnNorm K M y * RCnNorm K M y) (RCnNorm K M x * RCnNorm K M x)).
move=> H3.
elim (Rle_not_lt (RCnNorm K M x) (RCnNorm K M y) (proj2 (H1 K M y x) H3) H2).
apply.
move=> H2.
elim (Rle_or_lt (RCnNorm K M y) (RCnNorm K M x)).
move=> H3.
elim (Rle_not_lt (RCnNorm K M x * RCnNorm K M x) (RCnNorm K M y * RCnNorm K M y) (proj1 (H1 K M y x) H3) H2).
apply.
move=> K M x y.
apply conj.
move=> H1.
apply (Rmult_le_compat (RCnNorm K M x) (RCnNorm K M y) (RCnNorm K M x) (RCnNorm K M y)).
apply Rge_le.
apply (proj1 (RCnNormNature K M x)).
apply Rge_le.
apply (proj1 (RCnNormNature K M x)).
apply H1.
apply H1.
move=> H1.
elim (Rle_or_lt (RCnNorm K M x) (RCnNorm K M y)).
apply.
move=> H2.
elim (Rle_not_lt (RCnNorm K M y * RCnNorm K M y) (RCnNorm K M x * RCnNorm K M x) H1).
apply (Rmult_le_0_lt_compat (RCnNorm K M y) (RCnNorm K M x) (RCnNorm K M y) (RCnNorm K M x)).
apply Rge_le.
apply (proj1 (RCnNormNature K M y)).
apply Rge_le.
apply (proj1 (RCnNormNature K M y)).
apply H2.
apply H2.
Qed.

Lemma Lemma3 : forall (K : RC) (M N : nat) (A : Matrix (RCfield K) M N) (b : RCn K M) (x : RCn K N),
       (forall (y : RCn K N),
        RCnNorm K M (RCnminus K M b (MVmult (RCfield K) M N A x)) <=
        RCnNorm K M (RCnminus K M b (MVmult (RCfield K) M N A y))) <->
       RCnminus K M b (MVmult (RCfield K) M N A x) = ResiVRC K M N A b.
Proof.
move=> K M N A b x.
apply conj.
move=> H1.
rewrite (proj1 (Lemma1V K M N A b x)).
reflexivity.
apply (proj1 (Lemma2 K M N A b x) H1).
move=> H1.
apply (proj2 (Lemma2 K M N A b x)).
apply (proj2 (Lemma1V K M N A b x)).
rewrite - H1.
reflexivity.
Qed.

Lemma Lemma4 : forall (K : RC) (M N P Q : nat) (A1 : Matrix (RCfield K) M P) (A2 : Matrix (RCfield K) M Q) (B : Matrix (RCfield K) M N),
       ResiRC K M (P + Q) N (MBlockW (RCfield K) M P Q A1 A2) B = ResiRC K M Q N (ResiRC K M P Q A1 A2) (ResiRC K M P N A1 B).
Proof.
move=> K M N P Q A1 A2 B.
suff: (let X := Mmult (RCfield K) P M Q (GeneralizedInverseMatrixRC K M P A1) A2 in ResiRC K M (P + Q) N (MBlockW (RCfield K) M P Q A1 A2) B =
ResiRC K M Q N (ResiRC K M P Q A1 A2) (ResiRC K M P N A1 B)).
apply.
move=> X.
suff: (let Y := Mmult (RCfield K) P M N (GeneralizedInverseMatrixRC K M P A1) B in ResiRC K M (P + Q) N (MBlockW (RCfield K) M P Q A1 A2) B =
ResiRC K M Q N (ResiRC K M P Q A1 A2) (ResiRC K M P N A1 B)).
apply.
move=> Y.
suff: (let Z := Mmult (RCfield K) Q M N (GeneralizedInverseMatrixRC K M Q (ResiRC K M P Q A1 A2)) (ResiRC K M P N A1 B) in ResiRC K M (P + Q) N (MBlockW (RCfield K) M P Q A1 A2) B =
ResiRC K M Q N (ResiRC K M P Q A1 A2) (ResiRC K M P N A1 B)).
apply.
move=> Z.
suff: (ResiRC K M Q N (ResiRC K M P Q A1 A2) (ResiRC K M P N A1 B) = Mminus (RCfield K) M N B (Mmult (RCfield K) M (P + Q) N (MBlockW (RCfield K) M P Q A1 A2) (MBlockH (RCfield K) P Q N (Mminus (RCfield K) P N Y (Mmult (RCfield K) P Q N X Z)) Z))).
move=> H1.
rewrite H1.
apply (proj1 (Lemma1 K M (P + Q) N (MBlockW (RCfield K) M P Q A1 A2) B (MBlockH (RCfield K) P Q N
        (Mminus (RCfield K) P N Y (Mmult (RCfield K) P Q N X Z)) Z))).
suff: (Mmult (RCfield K) P M N
  (AdjointMatrixRC K M P A1)
  (Mminus (RCfield K) M N B
     (Mmult (RCfield K) M (P + Q) N (MBlockW (RCfield K) M P Q A1 A2)
        (MBlockH (RCfield K) P Q N
           (Mminus (RCfield K) P N Y (Mmult (RCfield K) P Q N X Z)) Z))) =
MO (RCfield K) P N).
move=> H2.
suff: (Mmult (RCfield K) Q M N
  (AdjointMatrixRC K M Q A2)
  (Mminus (RCfield K) M N B
     (Mmult (RCfield K) M (P + Q) N (MBlockW (RCfield K) M P Q A1 A2)
        (MBlockH (RCfield K) P Q N
           (Mminus (RCfield K) P N Y (Mmult (RCfield K) P Q N X Z)) Z))) =
MO (RCfield K) Q N).
move=> H3.
rewrite (BlockWAdjointMatrixRC K M P Q A1 A2).
rewrite (MBlockHMult (RCfield K) P Q M N (AdjointMatrixRC K M P A1)
     (AdjointMatrixRC K M Q A2)).
rewrite H2.
rewrite H3.
apply functional_extensionality.
move=> m.
unfold MBlockH.
elim (AddConnectInv P Q m).
move=> H4.
reflexivity.
move=> H4.
reflexivity.
rewrite - (Mminus_O_r (RCfield K) Q N (Mmult (RCfield K) Q M N (AdjointMatrixRC K M Q A2)
  (Mminus (RCfield K) M N B
     (Mmult (RCfield K) M (P + Q) N (MBlockW (RCfield K) M P Q A1 A2)
        (MBlockH (RCfield K) P Q N
           (Mminus (RCfield K) P N Y (Mmult (RCfield K) P Q N X Z)) Z))))).
rewrite - {1} (Mmult_O_r (RCfield K) Q P N (AdjointMatrixRC K P Q X)).
rewrite - H2.
rewrite - (Mmult_assoc (RCfield K) Q P M N (AdjointMatrixRC K P Q X) (AdjointMatrixRC K M P A1)).
rewrite - (AdjointMatrixRCMult K M P Q A1 X).
unfold Mminus at 1.
rewrite (Mopp_mult_distr_l (RCfield K) Q M N).
rewrite - (Mmult_plus_distr_r (RCfield K) Q M N).
rewrite - H1.
suff: (Mplus (RCfield K) Q M (AdjointMatrixRC K M Q A2)
     (Mopp (RCfield K) Q M
        (AdjointMatrixRC K M Q (Mmult (RCfield K) M P Q A1 X)))
= AdjointMatrixRC K M Q (ResiRC K M P Q A1 A2)).
move=> H3.
rewrite H3.
rewrite - (proj2 (Lemma1 K M Q N (ResiRC K M P Q A1 A2) (ResiRC K M P N A1 B) Z)).
unfold ResiRC at 2.
rewrite (Mmult_assoc (RCfield K) M Q M N (ResiRC K M P Q A1 A2)
              (GeneralizedInverseMatrixRC K M Q (ResiRC K M P Q A1 A2)) (ResiRC K M P N A1 B)).
reflexivity.
unfold ResiRC at 1.
rewrite (Mmult_assoc (RCfield K) M Q M N (ResiRC K M P Q A1 A2) (GeneralizedInverseMatrixRC K M Q (ResiRC K M P Q A1 A2)) (ResiRC K M P N A1 B)).
reflexivity.
unfold ResiRC.
rewrite (AdjointMatrixRCPlus K M Q A2).
rewrite (AdjointMatrixRCOpp K M Q).
rewrite (Mmult_assoc (RCfield K) M P M Q A1 (GeneralizedInverseMatrixRC K M P A1) A2).
reflexivity.
rewrite (MBlockHWMult (RCfield K) M P Q N).
rewrite (Mmult_minus_distr_l (RCfield K) M P N A1).
unfold Mminus.
rewrite (Mopp_plus_distr (RCfield K) M N).
rewrite (Mopp_plus_distr (RCfield K) M N).
rewrite (Mopp_involutive (RCfield K) M N).
rewrite (Mplus_assoc (RCfield K) M N (Mopp (RCfield K) M N (Mmult (RCfield K) M P N A1 Y))).
rewrite - (Mplus_assoc (RCfield K) M N B).
rewrite (Mmult_plus_distr_l (RCfield K) P M N).
rewrite (proj2 (Lemma1 K M P N A1 B Y)).
rewrite (Mopp_mult_distr_l (RCfield K) M Q N A2 Z).
rewrite - (Mmult_assoc (RCfield K) M P Q N A1 X Z).
rewrite - (Mmult_plus_distr_r (RCfield K) M Q N).
rewrite - (Mmult_assoc (RCfield K) P M Q N).
rewrite - (Mmult_opp_opp (RCfield K) P M Q).
rewrite (Mopp_plus_distr (RCfield K) M Q).
rewrite (Mopp_involutive (RCfield K) M Q).
rewrite (Mopp_mult_distr_l_reverse (RCfield K) P M Q).
rewrite (Mplus_comm (RCfield K) M Q).
rewrite (proj2 (Lemma1 K M P Q A1 A2 X)).
rewrite (Mopp_O (RCfield K) P Q).
rewrite (Mmult_O_l (RCfield K) P Q N Z).
apply (Mplus_O_l (RCfield K) P N (MO (RCfield K) P N)).
unfold ResiRC.
rewrite (Mmult_assoc (RCfield K) M P M Q).
reflexivity.
unfold ResiRC.
rewrite (Mmult_assoc (RCfield K) M P M N).
reflexivity.
rewrite (MBlockHWMult (RCfield K) M P Q N).
unfold Mminus.
rewrite (Mopp_plus_distr (RCfield K) M N).
rewrite (Mmult_plus_distr_l (RCfield K) M P N).
rewrite (Mopp_plus_distr (RCfield K) M N).
rewrite (Mopp_mult_distr_r_reverse (RCfield K) M P N).
rewrite (Mopp_involutive (RCfield K) M N).
rewrite (Mplus_assoc (RCfield K) M N).
rewrite - (Mopp_involutive (RCfield K) M N (Mmult (RCfield K) M P N A1 (Mmult (RCfield K) P Q N X Z))).
rewrite - (Mopp_plus_distr (RCfield K) M N).
rewrite - (Mplus_assoc (RCfield K) M N B).
rewrite - (Mmult_assoc (RCfield K) M P Q N A1).
rewrite (Mopp_mult_distr_l (RCfield K) M Q N).
rewrite - (Mmult_plus_distr_r (RCfield K) M Q N).
unfold Z.
unfold X.
unfold Y.
unfold ResiRC.
rewrite (Mmult_assoc (RCfield K) M Q M N).
rewrite (Mmult_assoc (RCfield K) M P M N A1).
rewrite (Mmult_assoc (RCfield K) M P M Q A1).
rewrite (Mplus_comm (RCfield K) M Q (Mopp (RCfield K) M Q
              (Mmult (RCfield K) M P Q A1
                 (Mmult (RCfield K) P M Q (GeneralizedInverseMatrixRC K M P A1)
                    A2))) A2).
reflexivity.
Qed.

Lemma Lemma5 : forall (K : RC) (M N1 N2 : nat) (A1 : Matrix (RCfield K) M N1) (A2 : Matrix (RCfield K) M N2) (Q1 : Matrix (RCfield K) M N1) (Q2 : Matrix (RCfield K) M N2) (R1 : Matrix (RCfield K) N1 N1) (R2 : Matrix (RCfield K) N1 N2) (R3 : Matrix (RCfield K) N2 N2), Mmult (RCfield K) (N1 + N2) M (N1 + N2) (AdjointMatrixRC K M (N1 + N2) (MBlockW (RCfield K) M N1 N2 Q1 Q2)) (MBlockW (RCfield K) M N1 N2 Q1 Q2) = MI (RCfield K) (N1 + N2) -> Rank (RCfield K) M N1 A1 = N1 -> MBlockW (RCfield K) M N1 N2 A1 A2 = Mmult (RCfield K) M (N1 + N2) (N1 + N2) (MBlockW (RCfield K) M N1 N2 Q1 Q2) (MBlockH (RCfield K) N1 N2 (N1 + N2) (MBlockW (RCfield K) N1 N1 N2 R1 R2) (MBlockW (RCfield K) N2 N1 N2 (MO (RCfield K) N2 N1) R3)) -> ResiRC K M N1 N2 A1 A2 = Mmult (RCfield K) M N2 N2 Q2 R3.
Proof.
move=> K M N1 N2 A1 A2 Q1 Q2 R1 R2 R3 H1 H2 H3.
suff: (A1 = Mmult (RCfield K) M N1 N1 Q1 R1).
move=> H4.
suff: (A2 = Mplus (RCfield K) M N2 (Mmult (RCfield K) M N1 N2 Q1 R2) (Mmult (RCfield K) M N2 N2 Q2 R3)).
move=> H5.
suff: (RegularMatrix (RCfield K) N1 R1).
move=> H6.
suff: (Mmult (RCfield K) M N2 N2 Q2 R3 = Mminus (RCfield K) M N2 A2 (Mmult (RCfield K) M N1 N2 A1 (Mmult (RCfield K) N1 N1 N2 (InvMatrix (RCfield K) N1 R1) R2))).
move=> H7.
rewrite H7.
apply (proj1 (Lemma1 K M N1 N2 A1 A2 (Mmult (RCfield K) N1 N1 N2 (InvMatrix (RCfield K) N1 R1) R2))).
rewrite - H7.
rewrite H4.
rewrite (AdjointMatrixRCMult K M N1 N1 Q1 R1).
rewrite (Mmult_assoc (RCfield K) N1 N1 M N2).
rewrite - (Mmult_assoc (RCfield K) N1 M N2 N2).
suff: (Mmult (RCfield K) N1 M N2 (AdjointMatrixRC K M N1 Q1) Q2 = MO (RCfield K) N1 N2).
move=> H8.
rewrite H8.
rewrite (Mmult_O_l (RCfield K) N1 N2 N2 R3).
apply (Mmult_O_r (RCfield K) N1 N1 N2 (AdjointMatrixRC K N1 N1 R1)).
suff: (Mmult (RCfield K) N1 M N2 (AdjointMatrixRC K M N1 Q1) Q2
=
(fun (m : Count N1) (n : Count N2) => Mmult (RCfield K) (N1 + N2) M (N1 + N2)
       (AdjointMatrixRC K M (N1 + N2) (MBlockW (RCfield K) M N1 N2 Q1 Q2))
       (MBlockW (RCfield K) M N1 N2 Q1 Q2) (AddConnect N1 N2 (inl m)) (AddConnect N1 N2 (inr n)))).
move=> H8.
rewrite H8.
rewrite H1.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MI.
rewrite - (proj1 (AddConnectNature N1 N2) x).
rewrite - (proj2 (AddConnectNature N1 N2) y).
elim (Nat.eq_dec (proj1_sig x) (N1 + proj1_sig y)).
move=> H9.
elim (le_not_lt N1 (proj1_sig x)).
rewrite H9.
apply (le_plus_l N1 (proj1_sig y)).
apply (proj2_sig x).
move=> H9.
reflexivity.
rewrite (BlockWAdjointMatrixRC K M N1 N2 Q1 Q2).
rewrite (MBlockWMult (RCfield K) (N1 + N2) M N1 N2).
rewrite (MBlockHMult (RCfield K) N1 N2 M N2).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation N1 N2) (inr y)).
rewrite (proj1 (AddConnectInvRelation N1 N2) (inl x)).
reflexivity.
rewrite - (Mplus_O_r (RCfield K) M N2 (Mmult (RCfield K) M N2 N2 Q2 R3)).
rewrite H5.
unfold Mminus.
rewrite (Mplus_comm (RCfield K) M N2 (Mmult (RCfield K) M N1 N2 Q1 R2)).
rewrite (Mplus_assoc (RCfield K) M N2 (Mmult (RCfield K) M N2 N2 Q2 R3)).
apply (f_equal (Mplus (RCfield K) M N2 (Mmult (RCfield K) M N2 N2 Q2 R3))).
rewrite - (Mmult_assoc (RCfield K) M N1 N1 N2 A1 (InvMatrix (RCfield K) N1 R1) R2).
rewrite H4.
rewrite (Mmult_assoc (RCfield K) M N1 N1 N1 Q1 R1 (InvMatrix (RCfield K) N1 R1)).
rewrite (InvMatrixMultR (RCfield K) N1 R1 H6).
rewrite (Mmult_I_r (RCfield K) M N1 Q1).
rewrite (Mplus_opp_r (RCfield K) M N2 (Mmult (RCfield K) M N1 N2 Q1 R2)).
reflexivity.
elim (proj1 (RankInvLExistRelation (RCfield K) M N1 A1) H2).
move=> X H6.
apply (proj2 (RegularInvLExistRelation (RCfield K) N1 R1)).
exists (Mmult (RCfield K) N1 M N1 X Q1).
rewrite (Mmult_assoc (RCfield K) N1 M N1 N1 X Q1 R1).
rewrite - H4.
apply H6.
suff: (A2 = (fun (m : Count M) (n : Count N2) => MBlockW (RCfield K) M N1 N2 A1 A2 m (AddConnect N1 N2 (inr n)))).
move=> H5.
rewrite H5.
rewrite H3.
rewrite (MBlockHWMult (RCfield K) M N1 N2 (N1 + N2)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite (MBlockWMult (RCfield K) M N1 N1 N2 Q1 R1 R2).
rewrite (MBlockWMult (RCfield K) M N2 N1 N2 Q2 (MO (RCfield K) N2 N1) R3).
unfold Mplus.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation N1 N2) (inr y)).
reflexivity.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation N1 N2) (inr y)).
reflexivity.
suff: (A1 = (fun (m : Count M) (n : Count N1) => MBlockW (RCfield K) M N1 N2 A1 A2 m (AddConnect N1 N2 (inl n)))).
move=> H4.
rewrite H4.
rewrite H3.
rewrite (MBlockHWMult (RCfield K) M N1 N2 (N1 + N2)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
rewrite (MBlockWMult (RCfield K) M N1 N1 N2 Q1 R1 R2).
rewrite (MBlockWMult (RCfield K) M N2 N1 N2 Q2 (MO (RCfield K) N2 N1) R3).
unfold Mplus.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation N1 N2) (inl y)).
rewrite (Mmult_O_r (RCfield K) M N2 N1 Q2).
apply (Fadd_O_r (RCfield K) (Mmult (RCfield K) M N1 N1 Q1 R1 x y)).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation N1 N2) (inl y)).
reflexivity.
Qed.

Lemma MatrixJMeqExtensionality : forall (f : Field) (M1 M2 N1 N2 : nat), (M1 = M2) -> (N1 = N2) -> forall (X : Matrix f M1 N1) (Y : Matrix f M2 N2), (forall (m1 : Count M1) (m2 : Count M2) (n1 : Count N1) (n2 : Count N2), proj1_sig m1 = proj1_sig m2 -> proj1_sig n1 = proj1_sig n2 -> X m1 n1 = Y m2 n2) -> JMeq X Y.
Proof.
move=> f M1 M2 N1 N2 H1 H2.
rewrite H1.
rewrite H2.
move=> X Y H3.
rewrite (functional_extensionality X Y).
apply (JMeq_refl Y).
move=> m.
apply functional_extensionality.
move=> n.
apply (H3 m m n n eq_refl eq_refl).
Qed.

Lemma Formula_P763_1 : forall (K : RC) (M N L : nat), (M >= N)%nat -> forall (H : (N >= L)%nat) (A Q : Matrix (RCfield K) M N) (R : Matrix (RCfield K) N N), Rank (RCfield K) M L (fun (m : Count M) (n : Count L) => A m (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) L N (proj2_sig n) H))) = L -> Mmult (RCfield K) N M N (AdjointMatrixRC K M N Q) Q = MI (RCfield K) N -> UpperTriangularMatrix (RCfield K) N N R -> A = Mmult (RCfield K) M N N Q R -> forall (p q : Count N), (proj1_sig p < L)%nat -> (proj1_sig q >= proj1_sig p)%nat -> MySumF2 (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun (k : Count N) => (proj1_sig p <= proj1_sig k <= proj1_sig q)%nat)) RPCM ((fun (n : Count N) => RCabs K (R n q) * RCabs K (R n q))) <= RCabs K (R p p) * RCabs K (R p p) <-> RCnNorm K M (ResiVRC K M (proj1_sig p) (fun (m : Count M) (n : Count (proj1_sig p)) => A m (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (proj1_sig p) N (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p))))) (fun (m : Count M) => A m q)) <= RCnNorm K M (ResiVRC K M (proj1_sig p) (fun (m : Count M) (n : Count (proj1_sig p)) => A m (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n) (le_trans (S (proj1_sig n)) (proj1_sig p) N (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p))))) (fun (m : Count M) => A m p)).
Proof.
move=> K M N L H1 H2 A Q R H3 H4 H5 H6 p q H7 H8.
suff: (forall (r : Count N), (proj1_sig r >= proj1_sig p)%nat -> MySumF2 (Count N)
  (FiniteIntersection (Count N)
     (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))
     (fun (k : Count N) => (proj1_sig p <= proj1_sig k <= proj1_sig r)%nat)) RPCM
  (fun (n : Count N) => RCabs K (R n r) * RCabs K (R n r)) = RCRe K (RCnInnerProduct K M (ResiVRC K M (proj1_sig p)
     (fun (m : Count M) (n : Count (proj1_sig p)) =>
      A m
        (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
           (le_trans (S (proj1_sig n)) (proj1_sig p) N 
              (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p)))))
     (fun (m : Count M) => A m r)) (ResiVRC K M (proj1_sig p)
     (fun (m : Count M) (n : Count (proj1_sig p)) =>
      A m
        (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
           (le_trans (S (proj1_sig n)) (proj1_sig p) N 
              (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p)))))
     (fun (m : Count M) => A m r)))).
move=> H9.
suff: (RCabs K (R p p) * RCabs K (R p p) = MySumF2 (Count N)
       (FiniteIntersection (Count N)
          (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))
          (fun (k : Count N) => (proj1_sig p <= proj1_sig k <= proj1_sig p)%nat))
       RPCM (fun (n : Count N) => RCabs K (R n p) * RCabs K (R n p))).
move=> H10.
rewrite (H9 q H8).
rewrite H10.
rewrite (H9 p (le_n (proj1_sig p))).
suff: (forall (x y : RbaseSymbolsImpl.R), x >= 0 -> y >= 0 -> x * x <= y * y <-> x <= y).
move=> H11.
rewrite (proj2 (RCnNormNature K M (ResiVRC K M (proj1_sig p)
        (fun (m : Count M) (n : Count (proj1_sig p)) =>
         A m
           (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
              (le_trans (S (proj1_sig n)) (proj1_sig p) N 
                 (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p)))))
        (fun (m : Count M) => A m q)))).
rewrite (proj2 (RCnNormNature K M (ResiVRC K M (proj1_sig p)
        (fun (m : Count M) (n : Count (proj1_sig p)) =>
         A m
           (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
              (le_trans (S (proj1_sig n)) (proj1_sig p) N 
                 (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p)))))
        (fun (m : Count M) => A m p)))).
apply H11.
apply (RCnNormNature K M).
apply (RCnNormNature K M).
move=> x y H11 H12.
apply conj.
move=> H13.
apply (Rnot_lt_le y x).
move=> H14.
apply (Rle_not_lt (y * y) (x * x) H13).
apply (Rmult_le_0_lt_compat y x y x).
apply (Rge_le y 0 H12).
apply (Rge_le y 0 H12).
apply H14.
apply H14.
move=> H13.
apply (Rmult_le_compat x y x y).
apply (Rge_le x 0 H11).
apply (Rge_le x 0 H11).
apply H13.
apply H13.
rewrite (MySumF2Included (Count N) (FiniteSingleton (Count N) p)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
reflexivity.
move=> u.
elim.
move=> u0 H10 H11.
elim H10.
elim H11.
move=> u1 H12 H13.
suff: (p = u1).
move=> H14.
rewrite H14.
apply (In_singleton (Count N) u1).
apply sig_map.
apply (le_antisym (proj1_sig p) (proj1_sig u1) (proj1 H12) (proj2 H12)).
move=> u.
elim.
apply (Intersection_intro (Count N)).
apply (conj (le_n (proj1_sig p)) (le_n (proj1_sig p))).
apply (Full_intro (Count N) p).
move=> r H9.
suff: (forall (m : Count (N - proj1_sig p)%nat), (proj1_sig m + proj1_sig p < N)%nat).
move=> H10.
suff: (ResiRC K M (proj1_sig p) (N - proj1_sig p) (fun (m : Count M) (n : Count (proj1_sig p)) =>
      A m
        (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
           (le_trans (S (proj1_sig n)) (proj1_sig p) N 
              (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p))))) (fun (m : Count M) (n : Count (N - proj1_sig p)%nat) =>
      A m
        (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n + proj1_sig p)%nat
           (H10 n))) = Mmult (RCfield K) M (N - proj1_sig p) (N - proj1_sig p) (fun (m : Count M) (n : Count (N - proj1_sig p)%nat) => Q m (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n + proj1_sig p)%nat
           (H10 n))) (fun (m : Count (N - proj1_sig p)%nat) (n : Count (N - proj1_sig p)%nat) => R (exist (fun (k : nat) => (k < N)%nat) (proj1_sig m + proj1_sig p)%nat
           (H10 m)) (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n + proj1_sig p)%nat
           (H10 n)))).
move=> H11.
suff: (proj1_sig r - proj1_sig p < N - proj1_sig p)%nat.
move=> H12.
suff: (ResiVRC K M (proj1_sig p)
     (fun (m : Count M) (n : Count (proj1_sig p)) =>
      A m
        (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
           (le_trans (S (proj1_sig n)) (proj1_sig p) N 
              (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p)))))
     (fun (m : Count M) => A m r) = (fun (l : Count M) => ResiRC K M (proj1_sig p) (N - proj1_sig p) (fun (m : Count M) (n : Count (proj1_sig p)) =>
      A m
        (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
           (le_trans (S (proj1_sig n)) (proj1_sig p) N 
              (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p))))) (fun (m : Count M) (n : Count (N - proj1_sig p)%nat) =>
      A m
        (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n + proj1_sig p)%nat
           (H10 n))) l (exist (fun (s : nat) => (s < N - proj1_sig p)%nat) (proj1_sig r - proj1_sig p)%nat H12))).
move=> H13.
rewrite H13.
rewrite H11.
rewrite RCnInnerProductMatrix.
suff: ((fun (l : Count M) =>
               Mmult (RCfield K) M (N - proj1_sig p) 
                 (N - proj1_sig p)
                 (fun (m : Count M) (n : Count (N - proj1_sig p)) =>
                  Q m
                    (exist (fun (k : nat) => (k < N)%nat)
                       (proj1_sig n + proj1_sig p)%nat 
                       (H10 n)))
                 (fun (m n : Count (N - proj1_sig p)) =>
                  R
                    (exist (fun (k : nat) => (k < N)%nat)
                       (proj1_sig m + proj1_sig p)%nat 
                       (H10 m))
                    (exist (fun (k : nat) => (k < N)%nat)
                       (proj1_sig n + proj1_sig p)%nat 
                       (H10 n))) l
                 (exist (fun (s : nat) => (s < N - proj1_sig p)%nat)
                    (proj1_sig r - proj1_sig p)%nat H12))
= MMatrixToVector (RCfield K) M (Mmult (RCfield K) M (N - proj1_sig p) 
                 1 (fun (m : Count M) (n : Count (N - proj1_sig p)) =>
                  Q m
                    (exist (fun (k : nat) => (k < N)%nat)
                       (proj1_sig n + proj1_sig p)%nat 
                       (H10 n))) (fun (m : Count (N - proj1_sig p)) (n : Count 1) =>
                  R
                    (exist (fun (k : nat) => (k < N)%nat)
                       (proj1_sig m + proj1_sig p)%nat 
                       (H10 m))
                    r))).
move=> H14.
rewrite H14.
rewrite (proj2 (MVectorMatrixRelation (RCfield K) M)).
rewrite (AdjointMatrixRCMult K M (N - proj1_sig p) 1).
rewrite (Mmult_assoc (RCfield K) 1 (N - proj1_sig p) M 1).
rewrite - (Mmult_assoc (RCfield K) (N - proj1_sig p) M (N - proj1_sig p) 1).
suff: (Mmult (RCfield K) (N - proj1_sig p) M (N - proj1_sig p)
              (AdjointMatrixRC K M (N - proj1_sig p)
                 (fun (m : Count M) (n : Count (N - proj1_sig p)) =>
                  Q m
                    (exist (fun (k : nat) => (k < N)%nat)
                       (proj1_sig n + proj1_sig p)%nat 
                       (H10 n))))
              (fun (m : Count M) (n : Count (N - proj1_sig p)) =>
               Q m
                 (exist (fun (k : nat) => (k < N)%nat)
                    (proj1_sig n + proj1_sig p)%nat 
                    (H10 n))) = (fun (m n : Count (N - proj1_sig p)) => Mmult (RCfield K) N M N (AdjointMatrixRC K M N Q) Q (exist (fun (k : nat) => (k < N)%nat)
                       (proj1_sig m + proj1_sig p)%nat 
                       (H10 m)) (exist (fun (k : nat) => (k < N)%nat)
                       (proj1_sig n + proj1_sig p)%nat 
                       (H10 n)))).
move=> H15.
rewrite H15.
rewrite H4.
suff: ((fun (m n : Count (N - proj1_sig p)) =>
            MI (RCfield K) N
              (exist (fun k : nat => (k < N)%nat)
                 (proj1_sig m + proj1_sig p)%nat (H10 m))
              (exist (fun k : nat => (k < N)%nat)
                 (proj1_sig n + proj1_sig p)%nat (H10 n))) = MI (RCfield K) (N - proj1_sig p)).
move=> H16.
rewrite H16.
rewrite (Mmult_I_l (RCfield K) (N - proj1_sig p) 1).
unfold Mmult.
suff: (MySumF2 (Count N)
  (FiniteIntersection (Count N)
     (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))
     (fun (k : Count N) => (proj1_sig p <= proj1_sig k <= proj1_sig r)%nat)) RPCM
  (fun (n : Count N) => RCabs K (R n r) * RCabs K (R n r)) = MySumF2 (Count N)
  (FiniteIntersection (Count N)
     (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))
     (fun (k : Count N) => (proj1_sig p <= proj1_sig k)%nat)) RPCM
  (fun (n : Count N) => RCabs K (R n r) * RCabs K (R n r))).
move=> H17.
rewrite H17.
rewrite (MySumF2Included (Count N) (FiniteIm (Count (N - proj1_sig p)) (Count N) (fun (n : Count (N - proj1_sig p)) => (exist (fun (k : nat) => (k < N)%nat)
                 (proj1_sig n + proj1_sig p)%nat (H10 n))) (exist (Finite (Count (N - proj1_sig p)))
           (Full_set {n : nat | (n < N - proj1_sig p)%nat})
           (CountFinite (N - proj1_sig p))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count N)).
rewrite CM_O_r.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < N - proj1_sig p)%nat}
  (exist (Finite {n : nat | (n < N - proj1_sig p)%nat})
     (Full_set {n : nat | (n < N - proj1_sig p)%nat})
     (CountFinite (N - proj1_sig p)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (ConjugateRCO K).
elim K.
reflexivity.
reflexivity.
move=> B b H18 H19 H20 H21.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Proposition_4_8_1_1_RC K).
rewrite (RCReplus K).
rewrite H21.
apply Rplus_eq_compat_l.
suff: (forall (x : RCT K), RCabs K x * RCabs K x = RCRe K (ConjugateRC K (RCmult K (ConjugateRC K x) x))).
move=> H22.
apply H22.
move=> x.
rewrite (Proposition_4_8_2_RC K).
rewrite (ConjugateRCInvolutive K x).
rewrite - (Proposition_4_8_3_RC K x).
suff: (forall (K : RC) (y : RbaseSymbolsImpl.R), y = RCRe K (IRRC K y)).
move=> H22.
apply (H22 K (RCabs K x * RCabs K x)).
elim.
move=> y.
reflexivity.
move=> y.
simpl.
unfold IRC.
rewrite (CmakeRe y 0).
reflexivity.
apply H20.
apply H20.
move=> u.
elim.
move=> u0 H18 H19.
elim H18.
elim H19.
move=> u1 H20 H21.
suff: (proj1_sig u1 - proj1_sig p < N - proj1_sig p)%nat.
move=> H22.
apply (Im_intro (Count (N - proj1_sig p)) (Count N) (Full_set {n : nat | (n < N - proj1_sig p)%nat}) (fun (n : Count (N - proj1_sig p)) =>
         exist (fun (k : nat) => (k < N)%nat) (proj1_sig n + proj1_sig p)%nat
           (H10 n))
         (exist (fun (k : nat) => (k < N - proj1_sig p)%nat) (proj1_sig u1 - proj1_sig p)%nat H22)).
apply (Full_intro (Count (N - proj1_sig p))).
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig u1 - proj1_sig p) (proj1_sig p)).
apply (le_plus_minus (proj1_sig p) (proj1_sig u1) H20).
apply (plus_lt_reg_l (proj1_sig u1 - proj1_sig p) (N - proj1_sig p) (proj1_sig p)).
rewrite (le_plus_minus_r (proj1_sig p) N (lt_le_weak (proj1_sig p) N (proj2_sig p))).
rewrite (le_plus_minus_r (proj1_sig p) (proj1_sig u1) H20).
apply (proj2_sig u1).
move=> u1 u2 H18 H19 H20.
apply sig_map.
apply (plus_reg_l (proj1_sig u1) (proj1_sig u2) (proj1_sig p)).
suff: ((proj1_sig p + proj1_sig u1)%nat = proj1_sig (exist (fun (k : nat) => (k < N)%nat) (proj1_sig u1 + proj1_sig p)%nat
        (H10 u1))).
move=> H21.
rewrite H21.
rewrite H20.
apply (plus_comm (proj1_sig u2) (proj1_sig p)).
apply (plus_comm (proj1_sig p) (proj1_sig u1)).
move=> u0.
elim.
move=> u1 H18 y H19.
rewrite H19.
apply (Intersection_intro (Count N)).
apply (le_plus_r (proj1_sig u1) (proj1_sig p)).
apply (Full_intro (Count N)).
rewrite (MySumF2Included (Count N)
  (FiniteIntersection (Count N)
     (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))
     (fun (k : Count N) => (proj1_sig p <= proj1_sig k <= proj1_sig r)%nat)) (FiniteIntersection (Count N)
     (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))
     (fun (k : Count N) => (proj1_sig p <= proj1_sig k)%nat))).
rewrite - {1} (Rplus_0_r (MySumF2 (Count N)
  (FiniteIntersection (Count N)
     (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))
     (fun (k : Count N) => (proj1_sig p <= proj1_sig k <= proj1_sig r)%nat)) RPCM
  (fun (n : Count N) => RCabs K (R n r) * RCabs K (R n r)))).
apply Rplus_eq_compat_l.
rewrite MySumF2O.
reflexivity.
move=> u.
elim.
move=> u0 H17 H18.
rewrite (H5 u0 r).
rewrite (RCabs_RCO K).
apply (Rmult_0_l 0).
elim (le_or_lt (proj1_sig u0) (proj1_sig r)).
move=> H19.
elim H17.
apply (Intersection_intro (Count N)).
apply conj.
elim H18.
move=> u1 H20 H21.
apply H20.
apply H19.
apply (Full_intro (Count N) u0).
move=> H19.
apply H19.
move=> u.
elim.
move=> u0 H17 H18.
apply (Intersection_intro (Count N)).
apply (proj1 H17).
apply H18.
apply functional_extensionality.
move=> m.
apply functional_extensionality.
move=> n.
unfold MI.
simpl.
elim (Nat.eq_dec (proj1_sig m + proj1_sig p) (proj1_sig n + proj1_sig p)).
move=> H16.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig n)).
move=> H17.
reflexivity.
elim.
apply (plus_reg_l (proj1_sig m) (proj1_sig n) (proj1_sig p)).
rewrite (plus_comm (proj1_sig p) (proj1_sig m)).
rewrite H16.
apply (plus_comm (proj1_sig n) (proj1_sig p)).
move=> H16.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig n)).
move=> H17.
elim H16.
rewrite H17.
reflexivity.
move=> H17.
reflexivity.
reflexivity.
apply functional_extensionality.
move=> m.
unfold MMatrixToVector.
unfold Mmult.
simpl.
suff: ((exist (fun (k : nat) => (k < N)%nat)
           (proj1_sig r - proj1_sig p + proj1_sig p)%nat
           (H10
              (exist (fun (s : nat) => (s < N - proj1_sig p)%nat)
                 (proj1_sig r - proj1_sig p)%nat H12))) = r).
move=> H14.
rewrite H14.
reflexivity.
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig r - proj1_sig p) (proj1_sig p)).
apply (le_plus_minus_r (proj1_sig p) (proj1_sig r) H9).
apply functional_extensionality.
move=> m.
unfold ResiVRC.
suff: ((fun (n : Count M) => A n r) = (fun (n : Count M) => A n (exist (fun (k : nat) => (k < N)%nat) (proj1_sig (exist (fun (s : nat) => (s < N - proj1_sig p)%nat)
     (proj1_sig r - proj1_sig p)%nat H12) + proj1_sig p)%nat (H10 (exist (fun (s : nat) => (s < N - proj1_sig p)%nat)
     (proj1_sig r - proj1_sig p)%nat H12))))).
move=> H13.
rewrite H13.
reflexivity.
suff: ((exist (fun (k : nat) => (k < N)%nat)
      (proj1_sig
         (exist (fun (s : nat) => s < N - proj1_sig p) 
            (proj1_sig r - proj1_sig p) H12) + proj1_sig p)%nat
      (H10
         (exist (fun (s : nat) => (s < N - proj1_sig p)%nat)
            (proj1_sig r - proj1_sig p)%nat H12))) = r).
move=> H13.
rewrite H13.
reflexivity.
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig r - proj1_sig p) (proj1_sig p)).
apply (le_plus_minus_r (proj1_sig p) (proj1_sig r) H9).
apply (plus_lt_reg_l (proj1_sig r - proj1_sig p) (N - proj1_sig p) (proj1_sig p)).
rewrite (le_plus_minus_r (proj1_sig p) (proj1_sig r) H9).
rewrite (le_plus_minus_r (proj1_sig p) N (lt_le_weak (proj1_sig p) N (proj2_sig p))).
apply (proj2_sig r).
apply (Lemma5 K M (proj1_sig p) (N - proj1_sig p) (fun (m : Count M) (n : Count (proj1_sig p)) =>
   A m
     (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
        (le_trans (S (proj1_sig n)) (proj1_sig p) N 
           (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p)))))
  (fun (m : Count M) (n : Count (N - proj1_sig p)) =>
   A m
     (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n + proj1_sig p)%nat (H10 n))) (fun (m : Count M) (n : Count (proj1_sig p)) =>
   Q m
     (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
        (le_trans (S (proj1_sig n)) (proj1_sig p) N 
           (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p)))))
(fun (m : Count M) (n : Count (N - proj1_sig p)) =>
   Q m
     (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n + proj1_sig p)%nat (H10 n)))
(fun (m n : Count (proj1_sig p)) =>
   R (exist (fun (k : nat) => (k < N)%nat) (proj1_sig m)
        (le_trans (S (proj1_sig m)) (proj1_sig p) N 
           (proj2_sig m) (lt_le_weak (proj1_sig p) N (proj2_sig p))))
     (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
        (le_trans (S (proj1_sig n)) (proj1_sig p) N 
           (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p)))))
(fun (m : Count (proj1_sig p)) (n : Count (N - proj1_sig p)) =>
   R (exist (fun (k : nat) => (k < N)%nat) (proj1_sig m)
        (le_trans (S (proj1_sig m)) (proj1_sig p) N 
           (proj2_sig m) (lt_le_weak (proj1_sig p) N (proj2_sig p))))
     (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n + proj1_sig p)%nat (H10 n)))
  (fun (m n : Count (N - proj1_sig p)) =>
   R (exist (fun (k : nat) => (k < N)%nat) (proj1_sig m + proj1_sig p)%nat (H10 m))
     (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n + proj1_sig p)%nat (H10 n)))
).
suff: (Matrix (RCfield K) M N = Matrix (RCfield K) M (proj1_sig p + (N - proj1_sig p)))%nat.
move=> H11.
apply JMeq_eq.
suff: (JMeq (Mmult (RCfield K) (proj1_sig p + (N - proj1_sig p)) M
     (proj1_sig p + (N - proj1_sig p))
     (AdjointMatrixRC K M (proj1_sig p + (N - proj1_sig p))
        (MBlockW (RCfield K) M (proj1_sig p) (N - proj1_sig p)
           (fun (m : Count M) (n : Count (proj1_sig p)) =>
            Q m
              (exist (fun k : nat => (k < N)%nat) (proj1_sig n)
                 (Nat.le_trans (S (proj1_sig n)) (proj1_sig p) N 
                    (proj2_sig n) (Nat.lt_le_incl (proj1_sig p) N (proj2_sig p)))))
           (fun (m : Count M) (n : Count (N - proj1_sig p)) =>
            Q m
              (exist (fun k : nat => (k < N)%nat)
                 (proj1_sig n + proj1_sig p)%nat (H10 n)))))
     (MBlockW (RCfield K) M (proj1_sig p) (N - proj1_sig p)
        (fun (m : Count M) (n : Count (proj1_sig p)) =>
         Q m
           (exist (fun k : nat => (k < N)%nat) (proj1_sig n)
              (Nat.le_trans (S (proj1_sig n)) (proj1_sig p) N 
                 (proj2_sig n) (Nat.lt_le_incl (proj1_sig p) N (proj2_sig p)))))
        (fun (m : Count M) (n : Count (N - proj1_sig p)) =>
         Q m
           (exist (fun k : nat => (k < N)%nat) (proj1_sig n + proj1_sig p)%nat
              (H10 n))))) (Mmult (RCfield K) N M N (AdjointMatrixRC K M N Q) Q)).
move=> H12.
apply (JMeq_trans H12).
rewrite H4.
suff: (N = proj1_sig p + (N - proj1_sig p))%nat.
move=> H13.
suff: (forall (n1 n2 : nat), n1 = n2 -> JMeq (MI (RCfield K) n1) (MI (RCfield K) n2)).
move=> H14.
apply H14.
apply H13.
move=> n1 n2 H14.
rewrite H14.
apply JMeq_refl.
apply (le_plus_minus (proj1_sig p) N (lt_le_weak (proj1_sig p) N (proj2_sig p))).
suff: (forall (n1 n2 : nat) (H : n1 = n2) (Q1 : Matrix (RCfield K) M n1) (Q2 : Matrix (RCfield K) M n2), JMeq Q1 Q2 -> JMeq (Mmult (RCfield K) n1 M n1 (AdjointMatrixRC K M n1 Q1) Q1) (Mmult (RCfield K) n2 M n2 (AdjointMatrixRC K M n2 Q2) Q2)).
move=> H12.
apply (H12 (proj1_sig p + (N - proj1_sig p))%nat N (le_plus_minus_r (proj1_sig p) N (lt_le_weak (proj1_sig p) N (proj2_sig p)))).
apply MatrixJMeqExtensionality.
reflexivity.
apply (le_plus_minus_r (proj1_sig p) N (lt_le_weak (proj1_sig p) N (proj2_sig p))).
move=> m1 m2 n1 n2 H13.
suff: (m1 = m2).
move=> H14.
rewrite H14.
rewrite - {1} (proj2 (AddConnectInvRelation (proj1_sig p) (N - proj1_sig p)) n1).
unfold MBlockW.
elim (AddConnectInv (proj1_sig p) (N - proj1_sig p) n1).
move=> n11.
rewrite - (proj1 (AddConnectNature (proj1_sig p) (N - proj1_sig p)) n11).
move=> H15.
suff: ((exist (fun (k : nat) => (k < N)%nat) (proj1_sig n11)
     (le_trans (S (proj1_sig n11)) (proj1_sig p) N 
        (proj2_sig n11) (lt_le_weak (proj1_sig p) N (proj2_sig p)))) = n2).
move=> H16.
rewrite H16.
reflexivity.
apply sig_map.
apply H15.
move=> n12.
rewrite - (proj2 (AddConnectNature (proj1_sig p) (N - proj1_sig p)) n12).
move=> H15.
suff: ((exist (fun (k : nat) => (k < N)%nat) (proj1_sig n12 + proj1_sig p)%nat
     (H10 n12)) = n2).
move=> H16.
rewrite H16.
reflexivity.
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig n12) (proj1_sig p)).
apply H15.
apply sig_map.
apply H13.
move=> n1 n2 H12.
rewrite H12.
move=> Q1 Q2.
elim.
apply (JMeq_refl (Mmult (RCfield K) n2 M n2 (AdjointMatrixRC K M n2 Q1) Q1)).
rewrite (le_plus_minus_r (proj1_sig p) N (lt_le_weak (proj1_sig p) N (proj2_sig p))).
reflexivity.
apply (proj2 (RankInvLExistRelation (RCfield K) M (proj1_sig p) (fun (m : Count M) (n : Count (proj1_sig p)) =>
   A m
     (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
        (le_trans (S (proj1_sig n)) (proj1_sig p) N 
           (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p))))))).
elim (proj1 (RankInvLExistRelation (RCfield K) M L (fun (m : Count M) (n : Count L) =>
   A m
     (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
        (le_trans (S (proj1_sig n)) L N 
           (proj2_sig n) H2)))) H3).
move=> B H11.
exists (fun (m : Count (proj1_sig p)) (n : Count M) => B (exist (fun (k : nat) => (k < L)%nat) (proj1_sig m) (le_trans (S (proj1_sig m)) (proj1_sig p) L (proj2_sig m) (lt_le_weak (proj1_sig p) L H7))) n).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
suff: (Mmult (RCfield K) (proj1_sig p) M (proj1_sig p)
  (fun (m : Count (proj1_sig p)) (n : Count M) =>
   B
     (exist (fun (k : nat) => (k < L)%nat) (proj1_sig m)
        (le_trans (S (proj1_sig m)) (proj1_sig p) L 
           (proj2_sig m) (lt_le_weak (proj1_sig p) L H7))) n)
  (fun (m : Count M) (n : Count (proj1_sig p)) =>
   A m
     (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
        (le_trans (S (proj1_sig n)) (proj1_sig p) N 
           (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p))))) x y
= Mmult (RCfield K) L M L B
        (fun (m : Count M) (n : Count L) =>
         A m
           (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
              (le_trans (S (proj1_sig n)) L N (proj2_sig n) H2))) 
 (exist (fun (k : nat) => (k < L)%nat) (proj1_sig x)
        (le_trans (S (proj1_sig x)) (proj1_sig p) L 
           (proj2_sig x) (lt_le_weak (proj1_sig p) L H7)))
 (exist (fun (k : nat) => (k < L)%nat) (proj1_sig y)
        (le_trans (S (proj1_sig y)) (proj1_sig p) L 
           (proj2_sig y) (lt_le_weak (proj1_sig p) L H7)))).
move=> H12.
rewrite H12.
rewrite H11.
reflexivity.
unfold Mmult.
suff: ((le_trans (S (proj1_sig y)) (proj1_sig p) N 
              (proj2_sig y) (lt_le_weak (proj1_sig p) N (proj2_sig p)))
= (le_trans (S (proj1_sig y)) L N
              (le_trans (S (proj1_sig y)) (proj1_sig p) L 
                 (proj2_sig y) (lt_le_weak (proj1_sig p) L H7)) H2)).
move=> H12.
rewrite H12.
reflexivity.
apply proof_irrelevance.
apply JMeq_eq.
suff: (JMeq (MBlockW (RCfield K) M (proj1_sig p) (N - proj1_sig p)
     (fun (m : Count M) (n : Count (proj1_sig p)) =>
      A m
        (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n)
           (le_trans (S (proj1_sig n)) (proj1_sig p) N 
              (proj2_sig n) (lt_le_weak (proj1_sig p) N (proj2_sig p)))))
     (fun (m : Count M) (n : Count (N - proj1_sig p)) =>
      A m
        (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n + proj1_sig p)%nat
           (H10 n)))) A).
move=> H11.
apply (JMeq_trans H11).
rewrite H6.
suff: (forall (M1 N1 L1 M2 N2 L2 : nat), M1 = M2 -> N1 = N2 -> L1 = L2 -> forall (X1 : Matrix (RCfield K) M1 N1) (X2 : Matrix (RCfield K) M2 N2) (Y1 : Matrix (RCfield K) N1 L1) (Y2 : Matrix (RCfield K) N2 L2), JMeq X1 X2 -> JMeq Y1 Y2 -> JMeq (Mmult (RCfield K) M1 N1 L1 X1 Y1) (Mmult (RCfield K) M2 N2 L2 X2 Y2)).
move=> H12.
apply H12.
reflexivity.
apply (le_plus_minus (proj1_sig p) N (lt_le_weak (proj1_sig p) N (proj2_sig p))).
apply (le_plus_minus (proj1_sig p) N (lt_le_weak (proj1_sig p) N (proj2_sig p))).
apply MatrixJMeqExtensionality.
reflexivity.
apply (le_plus_minus (proj1_sig p) N (lt_le_weak (proj1_sig p) N (proj2_sig p))).
move=> m1 m2 n1 n2 H13.
suff: (m1 = m2).
move=> H14.
rewrite H14.
rewrite - {1} (proj2 (AddConnectInvRelation (proj1_sig p) (N - proj1_sig p)) n2).
unfold MBlockW.
elim (AddConnectInv (proj1_sig p) (N - proj1_sig p) n2).
move=> n21.
rewrite - (proj1 (AddConnectNature (proj1_sig p) (N - proj1_sig p)) n21).
move=> H15.
suff: (n1 = (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n21)
     (le_trans (S (proj1_sig n21)) (proj1_sig p) N 
        (proj2_sig n21) (lt_le_weak (proj1_sig p) N (proj2_sig p))))).
move=> H16.
rewrite H16.
reflexivity.
apply sig_map.
apply H15.
move=> n22.
rewrite - (proj2 (AddConnectNature (proj1_sig p) (N - proj1_sig p)) n22).
move=> H15.
suff: (n1 = (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n22 + proj1_sig p)%nat
     (H10 n22))).
move=> H16.
rewrite H16.
reflexivity.
apply sig_map.
rewrite H15.
apply (plus_comm (proj1_sig p) (proj1_sig n22)).
apply sig_map.
apply H13.
apply MatrixJMeqExtensionality.
apply (le_plus_minus (proj1_sig p) N (lt_le_weak (proj1_sig p) N (proj2_sig p))).
apply (le_plus_minus (proj1_sig p) N (lt_le_weak (proj1_sig p) N (proj2_sig p))).
move=> m1 m2 n1 n2.
rewrite - {1} (proj2 (AddConnectInvRelation (proj1_sig p) (N - proj1_sig p)) m2).
rewrite - {1} (proj2 (AddConnectInvRelation (proj1_sig p) (N - proj1_sig p)) n2).
unfold MBlockH.
unfold MBlockW.
elim (AddConnectInv (proj1_sig p) (N - proj1_sig p) m2).
move=> m21.
rewrite - (proj1 (AddConnectNature (proj1_sig p) (N - proj1_sig p)) m21).
move=> H13.
elim (AddConnectInv (proj1_sig p) (N - proj1_sig p) n2).
move=> n21.
rewrite - (proj1 (AddConnectNature (proj1_sig p) (N - proj1_sig p)) n21).
move=> H14.
suff: (m1 = (exist (fun (k : nat) => (k < N)%nat) (proj1_sig m21)
     (le_trans (S (proj1_sig m21)) (proj1_sig p) N 
        (proj2_sig m21) (lt_le_weak (proj1_sig p) N (proj2_sig p))))).
move=> H15.
suff: (n1 = (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n21)
     (le_trans (S (proj1_sig n21)) (proj1_sig p) N 
        (proj2_sig n21) (lt_le_weak (proj1_sig p) N (proj2_sig p))))).
move=> H16.
rewrite H15.
rewrite H16.
reflexivity.
apply sig_map.
apply H14.
apply sig_map.
apply H13.
move=> n22.
rewrite - (proj2 (AddConnectNature (proj1_sig p) (N - proj1_sig p)) n22).
move=> H14.
suff: (m1 = (exist (fun (k : nat) => (k < N)%nat) (proj1_sig m21)
     (le_trans (S (proj1_sig m21)) (proj1_sig p) N 
        (proj2_sig m21) (lt_le_weak (proj1_sig p) N (proj2_sig p))))).
move=> H15.
suff: (n1 = (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n22 + proj1_sig p)%nat
     (H10 n22))).
move=> H16.
rewrite H15.
rewrite H16.
reflexivity.
apply sig_map.
rewrite H14.
apply (plus_comm (proj1_sig p) (proj1_sig n22)).
apply sig_map.
apply H13.
move=> m22.
rewrite - (proj2 (AddConnectNature (proj1_sig p) (N - proj1_sig p)) m22).
move=> H13.
elim (AddConnectInv (proj1_sig p) (N - proj1_sig p) n2).
move=> n21.
rewrite - (proj1 (AddConnectNature (proj1_sig p) (N - proj1_sig p)) n21).
move=> H14.
apply (H5 m1 n1).
rewrite H13.
rewrite H14.
apply (le_trans (S (proj1_sig n21)) (proj1_sig p) (proj1_sig p + proj1_sig m22) (proj2_sig n21) (le_plus_l (proj1_sig p) (proj1_sig m22))).
move=> n22.
rewrite - (proj2 (AddConnectNature (proj1_sig p) (N - proj1_sig p)) n22).
move=> H14.
suff: (m1 = (exist (fun (k : nat) => (k < N)%nat) (proj1_sig m22 + proj1_sig p)%nat
     (H10 m22))).
move=> H15.
suff: (n1 = (exist (fun (k : nat) => (k < N)%nat) (proj1_sig n22 + proj1_sig p)%nat
     (H10 n22))).
move=> H16.
rewrite H15.
rewrite H16.
reflexivity.
apply sig_map.
rewrite H14.
apply (plus_comm (proj1_sig p) (proj1_sig n22)).
apply sig_map.
rewrite H13.
apply (plus_comm (proj1_sig p) (proj1_sig m22)).
move=> M1 N1 L1 M2 N2 L2 H12 H13 H14.
rewrite H12.
rewrite H13.
rewrite H14.
move=> X1 X2 Y1 Y2.
elim.
elim.
apply (JMeq_refl (Mmult (RCfield K) M2 N2 L2 X1 Y1)).
apply MatrixJMeqExtensionality.
reflexivity.
apply (le_plus_minus_r (proj1_sig p) N (lt_le_weak (proj1_sig p) N (proj2_sig p))).
move=> m1 m2 n1 n2 H11.
suff: (m1 = m2).
move=> H12.
rewrite H12.
rewrite - {1} (proj2 (AddConnectInvRelation (proj1_sig p) (N - proj1_sig p)) n1).
unfold MBlockW.
elim (AddConnectInv (proj1_sig p) (N - proj1_sig p) n1).
move=> n11.
rewrite - (proj1 (AddConnectNature (proj1_sig p) (N - proj1_sig p)) n11).
move=> H13.
suff: ((exist (fun (k : nat) => (k < N)%nat) (proj1_sig n11)
     (le_trans (S (proj1_sig n11)) (proj1_sig p) N 
        (proj2_sig n11) (lt_le_weak (proj1_sig p) N (proj2_sig p)))) = n2).
move=> H14.
rewrite H14.
reflexivity.
apply sig_map.
apply H13.
move=> n12.
rewrite - (proj2 (AddConnectNature (proj1_sig p) (N - proj1_sig p)) n12).
move=> H13.
suff: ((exist (fun (k : nat) => (k < N)%nat) (proj1_sig n12 + proj1_sig p)%nat
     (H10 n12)) = n2).
move=> H14.
rewrite H14.
reflexivity.
apply sig_map.
simpl.
rewrite (plus_comm (proj1_sig n12) (proj1_sig p)).
apply H13.
apply sig_map.
apply H11.
move=> m.
rewrite {4} (le_plus_minus (proj1_sig p) N (lt_le_weak (proj1_sig p) N (proj2_sig p))).
rewrite (plus_comm (proj1_sig m) (proj1_sig p)).
apply (plus_lt_compat_l (proj1_sig m) (N - proj1_sig p) (proj1_sig p) (proj2_sig m)).
Qed.

Lemma MBlockWMORCTwoNorm : forall (K : RC) (M N1 N2 : nat) (A : Matrix (RCfield K) M N1), RCTwoNorm K M (N1 + N2) (MBlockW (RCfield K) M N1 N2 A (MO (RCfield K) M N2)) = RCTwoNorm K M N1 A.
Proof.
move=> K M.
elim.
elim.
move=> A.
reflexivity.
move=> N H1 A.
elim (proj1 (RCTwoNormNature K M N
  (MBlockW (RCfield K) M 0 (S N) A (MO (RCfield K) M (S N))))).
move=> x H2.
rewrite - (proj2 H2).
apply (RCnNormNature2 K M).
apply conj.
right.
reflexivity.
unfold RCnInnerProduct.
rewrite MySumF2O.
simpl.
rewrite (Rmult_0_l 0).
elim K.
reflexivity.
reflexivity.
move=> u H3.
unfold MVmult.
unfold MBlockW.
unfold MMatrixToVector.
unfold Mmult.
rewrite MySumF2O.
apply (Fmul_O_l (RCfield K)).
move=> u0 H4.
elim (AddConnectInv 0 (S N) u0).
move=> u1.
elim (le_not_lt O (proj1_sig u1) (le_0_n (proj1_sig u1)) (proj2_sig u1)).
move=> u1.
apply (Fmul_O_l (RCfield K) (MVectorToMatrix (RCfield K) (S N) x u0 Single)).
move=> N1 H1 N2 A.
apply Rle_antisym.
elim (proj1 (RCTwoNormNature K M (N1 + N2)
  (MBlockW (RCfield K) M (S N1) N2 A (MO (RCfield K) M N2)))).
move=> x H2.
rewrite - (proj2 H2).
elim (proj1 (RCnNormNature K (S N1) (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m))))).
move=> H3.
apply (Rle_trans (RCnNorm K M
  (MVmult (RCfield K) M (S (N1 + N2))
     (MBlockW (RCfield K) M (S N1) N2 A (MO (RCfield K) M N2)) x))
(RCnNorm K M
  (MVmult (RCfield K) M (S N1)
     A (RCnmult K (S N1) (IRRC K (1 / RCnNorm K (S N1) (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m))))) (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m))))))).
suff: (MVmult (RCfield K) M (S N1) A
     (RCnmult K (S N1)
        (IRRC K
           (1 /
            RCnNorm K (S N1)
              (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m)))))
        (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m))))
= RCnmult K M (IRRC K
           (1 /
            RCnNorm K (S N1)
              (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m)))))
(MVmult (RCfield K) M (S N1) A (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m))))).
move=> H4.
rewrite H4.
rewrite (Proposition_4_4_1 K M).
rewrite - (Rmult_1_l (RCnNorm K M
  (MVmult (RCfield K) M (S (N1 + N2))
     (MBlockW (RCfield K) M (S N1) N2 A (MO (RCfield K) M N2)) x))).
suff: (MVmult (RCfield K) M (S (N1 + N2))
     (MBlockW (RCfield K) M (S N1) N2 A (MO (RCfield K) M N2)) x
= MVmult (RCfield K) M (S N1) A
     (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m)))).
move=> H5.
rewrite H5.
apply Rmult_le_compat_r.
apply Rge_le.
apply (RCnNormNature K M).
suff: (forall (r : R), r >= 0 -> RCabs K (IRRC K r) = r).
move=> H6.
rewrite H6.
rewrite - {1} (Rinv_r (RCnNorm K (S N1) (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m))))).
apply Rmult_le_compat_r.
left.
apply Rinv_0_lt_compat.
apply H3.
rewrite - (proj1 H2).
suff: (forall (r1 r2 : R), r1 >= 0 -> r2 >= 0 -> r1 * r1 <= r2 * r2 -> r1 <= r2).
move=> H7.
apply H7.
apply (RCnNormNature K (S N1)).
apply (RCnNormNature K (S (N1 + N2)) x).
rewrite - (proj2 (RCnNormNature K (S N1) (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m))))).
rewrite - (proj2 (RCnNormNature K (S (N1 + N2)) x)).
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count (S (N1 + N2)))
     (FiniteIm (Count (S N1)) (Count (S (N1 + N2))) (fun (n : Count (S N1)) => AddConnect (S N1) N2 (inl n)) (exist (Finite (Count (S N1))) (Full_set (Count (S N1)))
        (CountFinite (S N1))))
).
rewrite - (Rplus_0_r (RCRe K
  (MySumF2 (Count (S N1))
     (exist (Finite (Count (S N1))) (Full_set (Count (S N1)))
        (CountFinite (S N1))) (RCPCM K)
     (fun (n : Count (S N1)) =>
      RCmult K (x (AddConnect (S N1) N2 (inl n)))
        (ConjugateRC K (x (AddConnect (S N1) N2 (inl n)))))))).
rewrite - (MySumF2BijectiveSame2 (Count (S N1)) (Count (S (N1 + N2)))
(exist (Finite (Count (S N1))) (Full_set (Count (S N1)))
              (CountFinite (S N1)))
(fun (n : Count (S N1)) => AddConnect (S N1) N2 (inl n))).
rewrite RCReplus.
apply Rplus_le_compat_l.
apply (MySumF2Induction (Count (S (N1 + N2)))).
apply conj.
right.
elim K.
reflexivity.
reflexivity.
move=> cm u H8 H9.
rewrite RCReplus.
rewrite - (Rplus_0_l 0).
apply Rplus_le_compat.
apply H9.
rewrite - (Proposition_4_8_3_RC K (x u)).
suff: (forall (r : R), RCRe K (IRRC K r) = r).
move=> H10.
rewrite H10.
apply Rge_le.
apply Formula_1_3.
move=> r.
elim K.
reflexivity.
apply (CmakeRe r 0).
move=> u1 u2 H8 H9 H10.
apply sig_map.
rewrite (proj1 (AddConnectNature (S N1) N2) u1).
rewrite (proj1 (AddConnectNature (S N1) N2) u2).
rewrite H10.
reflexivity.
move=> u H8.
apply (Full_intro (Count (S (N1 + N2))) u).
move=> r1 r2 H7 H8 H9.
apply (Rnot_lt_le r2 r1).
move=> H10.
apply (Rle_not_lt (r2 * r2) (r1 * r1) H9).
apply (Rmult_le_0_lt_compat r2 r1 r2 r1).
apply (Rge_le r2 0 H8).
apply (Rge_le r2 0 H8).
apply H10.
apply H10.
apply (Rgt_not_eq (RCnNorm K (S N1) (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m)))) 0 H3).
left.
unfold Rdiv.
rewrite Rmult_1_l.
apply Rinv_0_lt_compat.
apply H3.
move=> r H6.
elim K.
apply (Rabs_pos_eq r (Rge_le r 0 H6)).
simpl.
rewrite (CnormDefinition (IRC r)).
apply MySqrtNature2.
apply conj.
apply H6.
simpl.
unfold IRC.
rewrite (CmakeRe r 0).
rewrite (CmakeIm r 0).
rewrite (Rmult_0_l 0).
apply (Rplus_0_r (r * r)).
apply functional_extensionality.
move=> m.
unfold MVmult.
unfold MMatrixToVector.
unfold Mmult.
rewrite (MySumF2Included {n : nat | (n < S (N1 + N2))%nat}
(FiniteIm {n : nat | (n < S N1)%nat} {n : nat | (n < S (N1 + N2))%nat}
(fun (n : Count (S N1)) => AddConnect (S N1) N2 (inl n)) (exist (Finite (Count (S N1))) (Full_set {n : nat | (n < S N1)%nat})
     (CountFinite (S N1))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O {n : nat | (n < S (N1 + N2))%nat}).
rewrite (CM_O_r (FPCM (RCfield K))).
apply (MySumF2Same {n : nat | (n < S N1)%nat}
  (exist (Finite (Count (S N1))) (Full_set {n : nat | (n < S N1)%nat})
     (CountFinite (S N1))) (FPCM (RCfield K))).
move=> u H5.
unfold Basics.compose.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation (S N1) N2) (inl u)).
reflexivity.
move=> u.
unfold MBlockW.
rewrite - {1} (proj2 (AddConnectInvRelation (S N1) N2) u).
elim (AddConnectInv (S N1) N2 u).
move=> u0 H5.
suff: (Im {n : nat | (n < S N1)%nat}
                   {n : nat | (n < S (N1 + N2))%nat} (Full_set {n : nat | (n < S N1)%nat})
(fun (n : Count (S N1)) => AddConnect (S N1) N2 (inl n)) (AddConnect (S N1) N2 (inl u0))).
elim H5.
move=> u1 H6 H7 H8.
elim H6.
apply H8.
apply (Im_intro {n : nat | (n < S N1)%nat} {n : nat | (n < S (N1 + N2))%nat}
  (Full_set {n : nat | (n < S N1)%nat})
  (fun (n : Count (S N1)) => AddConnect (S N1) N2 (inl n)) u0 (Full_intro {n : nat | (n < S N1)%nat} u0)).
reflexivity.
move=> u0 H5.
apply (Fmul_O_l (RCfield K)).
move=> u1 u2 H5 H6 H7.
apply sig_map.
rewrite (proj1 (AddConnectNature (S N1) N2) u1).
rewrite H7.
rewrite (proj1 (AddConnectNature (S N1) N2) u2).
reflexivity.
move=> u H5.
apply (Full_intro {n : nat | (n < S (N1 + N2))%nat} u).
apply functional_extensionality.
move=> m.
unfold MVmult.
unfold RCnmult.
unfold Fnmul.
unfold MMatrixToVector.
unfold MVectorToMatrix.
unfold Mmult.
apply (FiniteSetInduction {n : nat | (n < S N1)%nat}
     (exist (Finite (Count (S N1))) (Full_set {n : nat | (n < S N1)%nat})
        (CountFinite (S N1)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (Fmul_O_r (RCfield K)).
reflexivity.
move=> B b H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H7.
rewrite (Fmul_add_distr_l (RCfield K)).
rewrite - (Fmul_assoc (RCfield K) (A m b)).
rewrite (Fmul_comm (RCfield K) (A m b)).
rewrite (Fmul_assoc (RCfield K)).
reflexivity.
apply H6.
apply H6.
apply (proj2 (RCTwoNormNature K M N1 A)).
exists (RCnmult K (S N1)
           (IRRC K
              (1 /
               RCnNorm K (S N1)
                 (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m)))))
           (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m)))).
apply conj.
rewrite (Proposition_4_4_1 K (S N1)).
suff: (forall (r : R), r >= 0 -> RCabs K (IRRC K r) = r).
move=> H6.
rewrite H6.
unfold Rdiv.
rewrite Rmult_1_l.
apply Rinv_l.
apply (Rgt_not_eq (RCnNorm K (S N1) (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m)))) 0 H3).
left.
unfold Rdiv.
rewrite Rmult_1_l.
apply Rinv_0_lt_compat.
apply H3.
move=> r H4.
elim K.
apply (Rabs_pos_eq r (Rge_le r 0 H4)).
simpl.
rewrite (CnormDefinition (IRC r)).
apply MySqrtNature2.
apply conj.
apply H4.
simpl.
unfold IRC.
rewrite (CmakeRe r 0).
rewrite (CmakeIm r 0).
rewrite (Rmult_0_l 0).
apply (Rplus_0_r (r * r)).
reflexivity.
move=> H3.
rewrite (RCnNormNature2 K M (MVmult (RCfield K) M (S (N1 + N2))
     (MBlockW (RCfield K) M (S N1) N2 A (MO (RCfield K) M N2)) x) 0).
elim (proj1 (RCTwoNormNature K M N1 A)).
move=> y H4.
rewrite - (proj2 H4).
apply (Rge_le (RCnNorm K M (MVmult (RCfield K) M (S N1) A y)) 0 (proj1 (RCnNormNature K M (MVmult (RCfield K) M (S N1) A y)))).
apply conj.
right.
reflexivity.
unfold RCnInnerProduct.
rewrite MySumF2O.
rewrite (Rmult_0_l 0).
elim K.
reflexivity.
reflexivity.
move=> u H4.
unfold MVmult.
unfold MMatrixToVector.
unfold Mmult.
rewrite MySumF2O.
apply (Fmul_O_l (RCfield K)).
move=> u0 H5.
unfold MBlockW.
rewrite - {2} (proj2 (AddConnectInvRelation (S N1) N2) u0).
elim (AddConnectInv (S N1) N2 u0).
move=> u1.
unfold MVectorToMatrix.
suff: (let temp := (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m))) in
Fmul (RCfield K) (A u u1) (temp u1) = CMe (FPCM (RCfield K))).
apply.
rewrite (Proposition_4_4_3_2 K (S N1) (fun (m : Count (S N1)) => x (AddConnect (S N1) N2 (inl m))) H3).
apply (Fmul_O_r (RCfield K)).
move=> u2.
apply (Fmul_O_l (RCfield K)).
elim (proj1 (RCTwoNormNature K M N1 A)).
move=> x H2.
rewrite - (proj2 H2).
apply (proj2 (RCTwoNormNature K M (N1 + N2)
  (MBlockW (RCfield K) M (S N1) N2 A (MO (RCfield K) M N2)))).
exists (fun (m : Count (S N1 + N2)) => match AddConnectInv (S N1) N2 m with
  | inl m0 => x m0
  | inr m0 => RCO K
end).
apply conj.
rewrite - (proj1 H2).
apply (RCnNormNature2 K (S (N1 + N2))).
apply conj.
apply (proj1 (RCnNormNature K (S N1) x)).
rewrite - (proj2 (RCnNormNature K (S N1) x)).
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count (S (N1 + N2))) (FiniteIm (Count (S N1)) (Count (S (N1 + N2))) (fun (n : Count (S N1)) => AddConnect (S N1) N2 (inl n)) (exist (Finite (Count (S N1))) (Full_set (Count (S N1)))
        (CountFinite (S N1))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count (S (N1 + N2)))).
rewrite CM_O_r.
apply f_equal.
apply (MySumF2Same (Count (S N1))
     (exist (Finite (Count (S N1))) (Full_set (Count (S N1)))
        (CountFinite (S N1))) (RCPCM K)).
move=> u H3.
unfold Basics.compose.
rewrite (proj1 (AddConnectInvRelation (S N1) N2) (inl u)).
reflexivity.
move=> u.
rewrite - {1} (proj2 (AddConnectInvRelation (S N1) N2) u).
elim (AddConnectInv (S N1) N2 u).
move=> u0 H3.
suff: (Im (Count (S N1)) (Count (S (N1 + N2))) (Full_set (Count (S N1))) (fun (n : Count (S N1)) => AddConnect (S N1) N2 (inl n)) (AddConnect (S N1) N2 (inl u0))).
elim H3.
move=> u1 H4 H5 H6.
elim (H4 H6).
apply (Im_intro (Count (S N1)) (Count (S (N1 + N2))) (Full_set (Count (S N1)))
  (fun (n : Count (S N1)) => AddConnect (S N1) N2 (inl n)) u0 (Full_intro (Count (S N1)) u0)).
reflexivity.
move=> u0 H3.
apply (Fmul_O_l (RCfield K)).
move=> u1 u2 H3 H4 H5.
apply sig_map.
rewrite (proj1 (AddConnectNature (S N1) N2) u1).
rewrite H5.
rewrite (proj1 (AddConnectNature (S N1) N2) u2).
reflexivity.
move=> u H3.
apply (Full_intro (Count (S (N1 + N2))) u).
apply f_equal.
apply functional_extensionality.
move=> m.
unfold MVmult.
unfold MMatrixToVector.
unfold Mmult.
rewrite (MySumF2Included (Count (S (N1 + N2))) (FiniteIm (Count (S N1)) (Count (S (N1 + N2))) (fun (n : Count (S N1)) => AddConnect (S N1) N2 (inl n)) (exist (Finite (Count (S N1))) (Full_set (Count (S N1)))
        (CountFinite (S N1))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count (S (N1 + N2)))).
rewrite CM_O_r.
apply (MySumF2Same (Count (S N1))
     (exist (Finite (Count (S N1))) (Full_set (Count (S N1)))
        (CountFinite (S N1))) (RCPCM K)).
move=> u H3.
unfold Basics.compose.
unfold MBlockW.
unfold MVectorToMatrix.
rewrite (proj1 (AddConnectInvRelation (S N1) N2) (inl u)).
reflexivity.
move=> u.
rewrite - {1} (proj2 (AddConnectInvRelation (S N1) N2) u).
unfold MBlockW.
elim (AddConnectInv (S N1) N2 u).
move=> u0 H3.
suff: (Im (Count (S N1)) (Count (S (N1 + N2))) (Full_set (Count (S N1))) (fun (n : Count (S N1)) => AddConnect (S N1) N2 (inl n)) (AddConnect (S N1) N2 (inl u0))).
elim H3.
move=> u1 H4 H5 H6.
elim (H4 H6).
apply (Im_intro (Count (S N1)) (Count (S (N1 + N2))) (Full_set (Count (S N1)))
  (fun (n : Count (S N1)) => AddConnect (S N1) N2 (inl n)) u0 (Full_intro (Count (S N1)) u0)).
reflexivity.
move=> u0 H3.
apply (Fmul_O_l (RCfield K)).
move=> u1 u2 H3 H4 H5.
apply sig_map.
rewrite (proj1 (AddConnectNature (S N1) N2) u1).
rewrite H5.
rewrite (proj1 (AddConnectNature (S N1) N2) u2).
reflexivity.
move=> u H3.
apply (Full_intro (Count (S (N1 + N2))) u).
Qed.

Lemma MBlockWRCTwoNormSame : forall (K : RC) (M N1 N2 : nat) (A1 : Matrix (RCfield K) M N1) (A2 : Matrix (RCfield K) M N2), RCTwoNorm K M (N1 + N2) (MBlockW (RCfield K) M N1 N2 A1 A2) = RCTwoNorm K M (N2 + N1) (MBlockW (RCfield K) M N2 N1 A2 A1).
Proof.
suff: (forall (K : RC) (M N1 N2 : nat) (A1 : Matrix (RCfield K) M N1)
  (A2 : Matrix (RCfield K) M N2),
RCTwoNorm K M (N1 + N2) (MBlockW (RCfield K) M N1 N2 A1 A2) >=
RCTwoNorm K M (N2 + N1) (MBlockW (RCfield K) M N2 N1 A2 A1)).
move=> H1 K M N1 N2 A1 A2.
apply Rge_antisym.
apply (H1 K M N1 N2 A1 A2).
apply (H1 K M N2 N1 A2 A1).
suff: (forall (K : RC) (M N : nat), (exists (n : nat), S n = N) -> forall (A : Matrix (RCfield K) M N),
       is_max
         (fun (l : R) =>
          exists (x : RCn K N),
            RCnNorm K N x = 1 /\
            RCnNorm K M (MVmult (RCfield K) M N A x) = l)
         (RCTwoNorm K M N A)).
move=> H1.
suff: (forall (K : RC) (M N1 N2 : nat) (A1 : Matrix (RCfield K) M N1)
  (A2 : Matrix (RCfield K) M N2) (r1 r2 : R), is_max
         (fun (l : R) =>
          exists (x : RCn K (N1 + N2)),
            RCnNorm K (N1 + N2) x = 1 /\
            RCnNorm K M (MVmult (RCfield K) M (N1 + N2) (MBlockW (RCfield K) M N1 N2 A1 A2) x) = l) r1
-> is_max
         (fun (l : R) =>
          exists (x : RCn K (N2 + N1)),
            RCnNorm K (N2 + N1) x = 1 /\
            RCnNorm K M (MVmult (RCfield K) M (N2 + N1) (MBlockW (RCfield K) M N2 N1 A2 A1) x) = l) r2 -> r1 >= r2).
move=> H2 K M.
elim.
elim.
move=> A1 A2.
right.
reflexivity.
move=> N1 H3 A1 A2.
apply (H2 K M O (S N1) A1 A2).
apply (RCTwoNormNature K M N1 (MBlockW (RCfield K) M 0 (S N1) A1 A2)).
apply (H1 K M (S N1 + 0)%nat).
exists N1.
rewrite (plus_comm (S N1) O).
reflexivity.
move=> N1 H3 N2 A1 A2.
apply (H2 K M (S N1) N2 A1 A2).
apply (H1 K M (S N1 + N2)%nat).
exists (N1 + N2)%nat.
reflexivity.
apply (H1 K M (N2 + S N1)%nat).
exists (N2 + N1)%nat.
rewrite (plus_comm N2 N1).
rewrite (plus_comm N2 (S N1)).
reflexivity.
move=> K M N1 N2 A1 A2 r1 r2 H2 H3.
apply (Rle_ge r2 r1).
apply (proj2 H2 r2).
elim (proj1 H3).
move=> x H4.
exists (fun (m : Count (N1 + N2)) => match AddConnectInv N1 N2 m with
  | inl m0 => x (AddConnect N2 N1 (inr m0)) 
  | inr m0 => x (AddConnect N2 N1 (inl m0))
end).
apply conj.
rewrite - (proj1 H4).
apply RCnNormNature2.
apply conj.
apply (proj1 (RCnNormNature K (N2 + N1) x)).
rewrite - (proj2 (RCnNormNature K (N2 + N1) x)).
unfold RCnInnerProduct.
rewrite (MySumF2Included (Count (N2 + N1)) (FiniteIm (Count (N1 + N2)) (Count (N2 + N1)) (fun (m : Count (N1 + N2)) => match AddConnectInv N1 N2 m with
  | inl m0 => AddConnect N2 N1 (inr m0) 
  | inr m0 => AddConnect N2 N1 (inl m0)
end) (exist (Finite (Count (N1 + N2))) (Full_set (Count (N1 + N2)))
        (CountFinite (N1 + N2))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count (N2 + N1))).
rewrite CM_O_r.
apply f_equal.
apply (MySumF2Same (Count (N1 + N2))
  (exist (Finite (Count (N1 + N2))) (Full_set (Count (N1 + N2)))
     (CountFinite (N1 + N2))) (RCPCM K)).
move=> u H5.
unfold Basics.compose.
elim (AddConnectInv N1 N2 u).
move=> u0.
reflexivity.
move=> u0.
reflexivity.
move=> u.
elim.
move=> u0.
elim.
apply (Im_intro (Count (N1 + N2)) (Count (N2 + N1)) (Full_set (Count (N1 + N2))) (fun (m : Count (N1 + N2)) =>
         match AddConnectInv N1 N2 m with
         | inl m0 => AddConnect N2 N1 (inr m0)
         | inr m0 => AddConnect N2 N1 (inl m0)
         end) match AddConnectInv N2 N1 u0 with
         | inl u1 => AddConnect N1 N2 (inr u1)
         | inr u1 => AddConnect N1 N2 (inl u1)
         end).
apply (Full_intro (Count (N1 + N2))).
rewrite - {1} (proj2 (AddConnectInvRelation N2 N1) u0).
elim (AddConnectInv N2 N1 u0).
move=> u1.
rewrite (proj1 (AddConnectInvRelation N1 N2) (inr u1)).
reflexivity.
move=> u1.
rewrite (proj1 (AddConnectInvRelation N1 N2) (inl u1)).
reflexivity.
move=> u1 u2 H5 H6.
rewrite - {2} (proj2 (AddConnectInvRelation N1 N2) u1).
rewrite - {2} (proj2 (AddConnectInvRelation N1 N2) u2).
elim (AddConnectInv N1 N2 u1).
move=> u10.
elim (AddConnectInv N1 N2 u2).
move=> u20 H7.
suff: (AddConnect N1 N2 (inl u10) = let temp := AddConnect N2 N1 (inr u10) in match AddConnectInv N2 N1 temp with
  | inl t => AddConnect N1 N2 (inl u10)
  | inr t => AddConnect N1 N2 (inl t)
end).
move=> H8.
rewrite H8.
rewrite H7.
simpl.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inr u20)).
reflexivity.
simpl.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inr u10)).
reflexivity.
move=> u20 H7.
suff: (match AddConnectInv N2 N1 (AddConnect N2 N1 (inr u10)) with
  | inl u11 => True
  | inr u11 => False
end).
rewrite (proj1 (AddConnectInvRelation N2 N1) (inr u10)).
elim.
rewrite H7.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inl u20)).
apply I.
move=> u10.
elim (AddConnectInv N1 N2 u2).
move=> u20 H7.
suff: (match AddConnectInv N2 N1 (AddConnect N2 N1 (inl u10)) with
  | inl u11 => True
  | inr u11 => False
end).
rewrite H7.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inr u20)).
elim.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inl u10)).
apply I.
move=> u20 H7.
suff: (AddConnect N1 N2 (inr u10) = let temp := AddConnect N2 N1 (inl u10) in match AddConnectInv N2 N1 temp with
  | inl t => AddConnect N1 N2 (inr t)
  | inr t => AddConnect N1 N2 (inr u10)
end).
move=> H8.
rewrite H8.
rewrite H7.
simpl.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inl u20)).
reflexivity.
simpl.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inl u10)).
reflexivity.
move=> u H5.
apply (Full_intro (Count (N2 + N1)) u).
rewrite - (proj2 H4).
apply RCnNormNature2.
apply conj.
apply (proj1 (RCnNormNature K M (MVmult (RCfield K) M (N2 + N1) (MBlockW (RCfield K) M N2 N1 A2 A1) x))).
rewrite - (proj2 (RCnNormNature K  M
  (MVmult (RCfield K) M (N2 + N1) (MBlockW (RCfield K) M N2 N1 A2 A1) x))).
unfold RCnInnerProduct.
apply f_equal.
apply (MySumF2Same (Count M)
  (exist (Finite (Count M)) (Full_set (Count M)) (CountFinite M)) 
  (RCPCM K)).
move=> v H5.
unfold MVmult.
unfold Mmult.
unfold MMatrixToVector.
rewrite (MySumF2Included (Count (N2 + N1)) (FiniteIm (Count (N1 + N2)) (Count (N2 + N1)) (fun (m : Count (N1 + N2)) => match AddConnectInv N1 N2 m with
  | inl m0 => AddConnect N2 N1 (inr m0) 
  | inr m0 => AddConnect N2 N1 (inl m0)
end) (exist (Finite (Count (N1 + N2))) (Full_set (Count (N1 + N2)))
        (CountFinite (N1 + N2))))).
rewrite - MySumF2BijectiveSame2.
rewrite (MySumF2O (Count (N2 + N1))).
rewrite CM_O_r.
suff: ((fun (n : Count (N1 + N2)) =>
      Fmul (RCfield K) (MBlockW (RCfield K) M N1 N2 A1 A2 v n)
        (MVectorToMatrix (RCfield K) (N1 + N2)
           (fun (m : Count (N1 + N2)) =>
            match AddConnectInv N1 N2 m with
            | inl m0 => x (AddConnect N2 N1 (inr m0))
            | inr m0 => x (AddConnect N2 N1 (inl m0))
            end) n Single)) =
(Basics.compose
        (fun (n : Count (N2 + N1)) =>
         Fmul (RCfield K) (MBlockW (RCfield K) M N2 N1 A2 A1 v n)
           (MVectorToMatrix (RCfield K) (N2 + N1) x n Single))
        (fun (m : Count (N1 + N2)) =>
         match AddConnectInv N1 N2 m with
         | inl m0 => AddConnect N2 N1 (inr m0)
         | inr m0 => AddConnect N2 N1 (inl m0)
         end))).
move=> H6.
rewrite H6.
reflexivity.
apply functional_extensionality.
move=> u.
unfold Basics.compose.
unfold MBlockW.
unfold MVectorToMatrix.
elim (AddConnectInv N1 N2 u).
move=> u0.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inr u0)).
reflexivity.
move=> u0.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inl u0)).
reflexivity.
move=> u.
elim.
move=> u0.
elim.
apply (Im_intro (Count (N1 + N2)) (Count (N2 + N1)) (Full_set (Count (N1 + N2))) (fun (m : Count (N1 + N2)) =>
         match AddConnectInv N1 N2 m with
         | inl m0 => AddConnect N2 N1 (inr m0)
         | inr m0 => AddConnect N2 N1 (inl m0)
         end) match AddConnectInv N2 N1 u0 with
         | inl u1 => AddConnect N1 N2 (inr u1)
         | inr u1 => AddConnect N1 N2 (inl u1)
         end).
apply (Full_intro (Count (N1 + N2))).
rewrite - {1} (proj2 (AddConnectInvRelation N2 N1) u0).
elim (AddConnectInv N2 N1 u0).
move=> u1.
rewrite (proj1 (AddConnectInvRelation N1 N2) (inr u1)).
reflexivity.
move=> u1.
rewrite (proj1 (AddConnectInvRelation N1 N2) (inl u1)).
reflexivity.
move=> u1 u2 H6 H7.
rewrite - {2} (proj2 (AddConnectInvRelation N1 N2) u1).
rewrite - {2} (proj2 (AddConnectInvRelation N1 N2) u2).
elim (AddConnectInv N1 N2 u1).
move=> u10.
elim (AddConnectInv N1 N2 u2).
move=> u20 H8.
suff: (AddConnect N1 N2 (inl u10) = let temp := AddConnect N2 N1 (inr u10) in match AddConnectInv N2 N1 temp with
  | inl t => AddConnect N1 N2 (inl u10)
  | inr t => AddConnect N1 N2 (inl t)
end).
move=> H9.
rewrite H9.
rewrite H8.
simpl.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inr u20)).
reflexivity.
simpl.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inr u10)).
reflexivity.
move=> u20 H8.
suff: (match AddConnectInv N2 N1 (AddConnect N2 N1 (inr u10)) with
  | inl u11 => True
  | inr u11 => False
end).
rewrite (proj1 (AddConnectInvRelation N2 N1) (inr u10)).
elim.
rewrite H8.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inl u20)).
apply I.
move=> u10.
elim (AddConnectInv N1 N2 u2).
move=> u20 H8.
suff: (match AddConnectInv N2 N1 (AddConnect N2 N1 (inl u10)) with
  | inl u11 => True
  | inr u11 => False
end).
rewrite H8.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inr u20)).
elim.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inl u10)).
apply I.
move=> u20 H8.
suff: (AddConnect N1 N2 (inr u10) = let temp := AddConnect N2 N1 (inl u10) in match AddConnectInv N2 N1 temp with
  | inl t => AddConnect N1 N2 (inr t)
  | inr t => AddConnect N1 N2 (inr u10)
end).
move=> H9.
rewrite H9.
rewrite H8.
simpl.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inl u20)).
reflexivity.
simpl.
rewrite (proj1 (AddConnectInvRelation N2 N1) (inl u10)).
reflexivity.
move=> u H6.
apply (Full_intro (Count (N2 + N1)) u).
move=> K M N.
elim.
move=> n H1.
rewrite - H1.
apply (RCTwoNormNature K M n).
Qed.

Lemma Formula_P763_2 : forall (K : RC) (M N1 N2 : nat) (A1 : Matrix (RCfield K) M N1)
         (A2 : Matrix (RCfield K) M N2) (Q1 : Matrix (RCfield K) M N1)
         (Q2 : Matrix (RCfield K) M N2) (R1 : Matrix (RCfield K) N1 N1)
         (R2 : Matrix (RCfield K) N1 N2) (R3 : Matrix (RCfield K) N2 N2),
       Mmult (RCfield K) (N1 + N2) M (N1 + N2)
         (AdjointMatrixRC K M (N1 + N2) (MBlockW (RCfield K) M N1 N2 Q1 Q2))
         (MBlockW (RCfield K) M N1 N2 Q1 Q2) = MI (RCfield K) (N1 + N2) ->
       Rank (RCfield K) M N1 A1 = N1 ->
       MBlockW (RCfield K) M N1 N2 A1 A2 =
       Mmult (RCfield K) M (N1 + N2) (N1 + N2)
         (MBlockW (RCfield K) M N1 N2 Q1 Q2)
         (MBlockH (RCfield K) N1 N2 (N1 + N2)
            (MBlockW (RCfield K) N1 N1 N2 R1 R2)
            (MBlockW (RCfield K) N2 N1 N2 (MO (RCfield K) N2 N1) R3)) -> RCTwoNorm K M (N1 + N2) (Mminus (RCfield K) M (N1 + N2) (MBlockW (RCfield K) M N1 N2 A1 A2) (Mmult (RCfield K) M N1 (N1 + N2) Q1 (MBlockW (RCfield K) N1 N1 N2 R1 R2))) = RCTwoNorm K M N2 (ResiRC K M N1 N2 A1 A2).
Proof.
move=> K M N1 N2 A1 A2 Q1 Q2 R1 R2 R3 H1 H2 H3.
rewrite (Lemma5 K M N1 N2 A1 A2 Q1 Q2 R1 R2 R3 H1 H2 H3).
rewrite H3.
rewrite (MBlockHWMult (RCfield K) M N1 N2 (N1 + N2)).
rewrite (Mplus_comm (RCfield K) M (N1 + N2)).
unfold Mminus.
rewrite (Mplus_assoc (RCfield K) M (N1 + N2)).
rewrite (Mplus_opp_r (RCfield K) M (N1 + N2)).
rewrite (Mplus_O_r (RCfield K) M (N1 + N2)).
rewrite (MBlockWMult (RCfield K) M N2 N1 N2 Q2 (MO (RCfield K) N2 N1) R3).
rewrite (MBlockWRCTwoNormSame K M N1 N2 (Mmult (RCfield K) M N2 N1 Q2 (MO (RCfield K) N2 N1))
     (Mmult (RCfield K) M N2 N2 Q2 R3)).
rewrite (Mmult_O_r (RCfield K) M N2 N1 Q2).
apply (MBlockWMORCTwoNorm K M N2 N1 (Mmult (RCfield K) M N2 N2 Q2 R3)).
Qed.


