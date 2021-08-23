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

Record CInner_Product_Space (V : VectorSpace Cfield) : Type := mkCInner_Product_Space {
  Cip : VT Cfield V -> VT Cfield V -> C;
  Cip_sym : forall (x y : VT Cfield V), Cip x y = Conjugate (Cip y x);
  Cip_linear_mult_l : forall (c : C) (x y : VT Cfield V), Cip (Vmul Cfield V c x) y = Cmult c (Cip x y);
  Cip_linear_plus_l : forall (x1 x2 y : VT Cfield V), Cip (Vadd Cfield V x1 x2) y = Cplus (Cip x1 y) (Cip x2 y);
  Cip_pos_re : forall (x : VT Cfield V), (Cip x x) CRe >= 0;
  Cip_refl : forall (x : VT Cfield V), Cip x x = CO <-> x = VO Cfield V
}.

Lemma Cip_pos_im : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x : VT Cfield V), (Cip V I x x) CIm = 0.
Proof.
move=> V I x.
suff: (Cip V I x x CIm = - Cip V I x x CIm).
move=> H1.
elim (Rmult_integral (Cip V I x x CIm) (1 + 1)).
apply.
move=> H2.
apply False_ind.
apply (Rlt_not_eq 0 (1 + 1)).
apply (Rlt_trans 0 1 (1 + 1) Rlt_0_1 (Rlt_plus_1 1)).
rewrite H2.
reflexivity.
rewrite (Rmult_plus_distr_l (Cip V I x x CIm) 1 1).
rewrite (Rmult_1_r (Cip V I x x CIm)).
rewrite {1} H1.
apply (Rplus_opp_l (Cip V I x x CIm)).
rewrite {1} (Cip_sym V I x x).
unfold Conjugate.
apply CmakeIm.
Qed.

Lemma Cip_linear_mult_r : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (c : C) (x y : VT Cfield V), Cip V I x (Vmul Cfield V c y) = Cmult (Conjugate c) (Cip V I x y).
Proof.
move=> V I c x y.
rewrite (Cip_sym V I x (Vmul Cfield V c y)).
rewrite (Cip_linear_mult_l V I c y x).
rewrite (Cip_sym V I x y).
apply (Proposition_4_8_2 c (Cip V I y x)).
Qed.

Lemma Cip_linear_plus_r : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x y1 y2 : VT Cfield V), Cip V I x (Vadd Cfield V y1 y2) = Cplus (Cip V I x y1) (Cip V I x y2).
Proof.
move=> V I x y1 y2.
rewrite (Cip_sym V I x (Vadd Cfield V y1 y2)).
rewrite (Cip_linear_plus_l V I y1 y2 x).
rewrite (Cip_sym V I x y1).
rewrite (Cip_sym V I x y2).
apply (Proposition_4_8_1_1 (Cip V I y1 x) (Cip V I y2 x)).
Qed.

Lemma Cip_mult_0_l : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x : VT Cfield V), Cip V I (VO Cfield V) x = CO.
Proof.
move=> V I x.
suff: (VO Cfield V = Vmul Cfield V CO (VO Cfield V)).
move=> H1.
rewrite H1.
rewrite (Cip_linear_mult_l V I CO).
apply (Fmul_O_l Cfield).
rewrite (Vmul_O_r Cfield V CO).
reflexivity.
Qed.

Lemma ConjugateCO : Conjugate CO = CO.
Proof.
apply functional_extensionality.
move=> m.
elim (CReorCIm m).
move=> H1.
rewrite H1.
apply (ConjugateRe CO).
move=> H1.
rewrite H1.
rewrite (ConjugateIm CO).
unfold CO.
unfold RnO.
apply Ropp_0.
Qed.

Lemma ConjugateCI : Conjugate CI = CI.
Proof.
apply functional_extensionality.
move=> m.
elim (CReorCIm m).
move=> H1.
rewrite H1.
apply (ConjugateRe CI).
move=> H1.
rewrite H1.
rewrite (ConjugateIm CI).
unfold CI.
rewrite CmakeIm.
apply Ropp_0.
Qed.

Lemma ConjugateInvolutive : forall (c : C), Conjugate (Conjugate c) = c.
Proof.
move=> c.
unfold Conjugate.
apply functional_extensionality.
move=> m.
elim (CReorCIm m).
move=> H1.
rewrite H1.
rewrite CmakeRe.
apply CmakeRe.
move=> H1.
rewrite H1.
rewrite CmakeIm.
rewrite CmakeIm.
apply (Ropp_involutive (c CIm)).
Qed.

Lemma Cip_mult_0_r : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x : VT Cfield V), Cip V I x (VO Cfield V) = CO.
Proof.
move=> V I x.
rewrite (Cip_sym V I x (VO Cfield V)).
rewrite (Cip_mult_0_l V I x).
apply ConjugateCO.
Qed.

Lemma Cip_linear_opp_l : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x y : VT Cfield V), Cip V I (Vopp Cfield V x) y = Copp (Cip V I x y).
Proof.
move=> V I x y.
apply (Fadd_opp_r_uniq Cfield (Cip V I x y) (Cip V I (Vopp Cfield V x) y)).
simpl.
rewrite - (Cip_linear_plus_l V I x (Vopp Cfield V x) y).
rewrite (Vadd_opp_r Cfield V x).
apply (Cip_mult_0_l V I y).
Qed.

Lemma Cip_linear_opp_r : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (x y : VT Cfield V), Cip V I x (Vopp Cfield V y) = Copp (Cip V I x y).
Proof.
move=> V I x y.
apply (Fadd_opp_r_uniq Cfield (Cip V I x y) (Cip V I x (Vopp Cfield V y))).
simpl.
rewrite - (Cip_linear_plus_r V I x y (Vopp Cfield V y)).
rewrite (Vadd_opp_r Cfield V y).
apply (Cip_mult_0_r V I x).
Qed.

Definition OrthonormalSystemC (V : VectorSpace Cfield) (I : CInner_Product_Space V) (T : Type) (W : T -> VT Cfield V) := (forall (t : T), Cip V I (W t) (W t) = CI) /\ (forall (t1 t2 : T), t1 <> t2 -> Cip V I (W t1) (W t2) = CO).

Lemma OrthonormalSystemLinearlyIndependentC : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (T : Type) (W : T -> VT Cfield V), OrthonormalSystemC V I T W -> LinearlyIndependentVS Cfield V T W.
Proof.
move=> V I T W H1.
apply (proj2 (LinearlyIndependentVSDef3 Cfield V T W)).
move=> a A H2 t H3.
suff: (a t = Cip V I (MySumF2 T A (VSPCM Cfield V)
       (fun (t : T) => Vmul Cfield V (a t) (W t))) (W t)).
move=> H4.
rewrite H4.
rewrite H2.
apply (Cip_mult_0_l V I (W t)).
suff: (Cip V I
  (MySumF2 T
      A (VSPCM Cfield V)
     (fun (t0 : T) => Vmul Cfield V (a t0) (W t0)))
  (W t) = MySumF2 T
     A (FPCM Cfield)
     (fun (t0 : T) => Cmult (a t0) (Cip V I (W t0) (W t)))).
move=> H4.
rewrite H4.
rewrite (MySumF2Included T (FiniteSingleton T t)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (proj1 H1 t).
suff: (Cmult (a t) CI = a t).
move=> H5.
rewrite H5.
rewrite (CM_O_r (FPCM Cfield) (a t)).
reflexivity.
apply (Fmul_I_r Cfield (a t)).
move=> u.
elim.
move=> u0 H5 H6.
rewrite (proj2 H1 u0 t).
apply (Fmul_O_r Cfield (a u0)).
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
apply (Cip_mult_0_l V I (W t)).
move=> B b H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Cip_linear_plus_l V I).
rewrite H7.
rewrite (Cip_linear_mult_l V I).
reflexivity.
apply H6.
apply H6.
Qed.

Lemma GramSchmidtLinearlyIndepententC_sub : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (N : nat) (W : Count N -> VT Cfield V), LinearlyIndependentVS Cfield V (Count N) W -> {Z : Count N -> VT Cfield V | OrthonormalSystemC V I (Count N) Z /\ forall (m : Count N), In (VT Cfield V) (SpanVS Cfield V {k : Count N | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))) (Z m)}.
Proof.
suff: (forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (N : nat) (W : Count N -> VT Cfield V), LinearlyIndependentVS Cfield V (Count N) W -> {Z : Count N -> VT Cfield V | LinearlyIndependentVS Cfield V (Count N) Z /\ (forall (t1 t2 : Count N), t1 <> t2 -> Cip V I (Z t1) (Z t2) = CO) /\ forall (m : Count N), In (VT Cfield V) (SpanVS Cfield V {k : Count N | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))) (Z m)}).
move=> H1 V I N W H2.
elim (H1 V I N W H2).
move=> Z H3.
exists (fun (m : Count N) => Vmul Cfield V (IRC (/ MySqrt (exist (fun (r : R) => r >= 0) (Cip V I (Z m) (Z m) CRe) (Cip_pos_re V I (Z m))))) (Z m)).
apply conj.
apply conj.
move=> t.
rewrite (Cip_linear_mult_l V I).
rewrite (Cip_linear_mult_r V I).
rewrite - Cmult_assoc.
suff: (Cip V I (Z t) (Z t) CRe <> 0).
move=> H4.
suff: (MySqrt
  (exist (fun (r : R) => r >= 0) (Cip V I (Z t) (Z t) CRe) (Cip_pos_re V I (Z t))) <> 0).
move=> H5.
unfold Conjugate.
unfold IRC.
rewrite CmakeRe.
rewrite CmakeIm.
unfold Cmult at 2.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite - (Rinv_mult_distr (MySqrt
  (exist (fun (r : R) => r >= 0) (Cip V I (Z t) (Z t) CRe) (Cip_pos_re V I (Z t)))) (MySqrt
  (exist (fun (r : R) => r >= 0) (Cip V I (Z t) (Z t) CRe) (Cip_pos_re V I (Z t)))) H5 H5).
rewrite - (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (Cip V I (Z t) (Z t) CRe) (Cip_pos_re V I (Z t))))).
rewrite Rmult_0_l.
rewrite Rmult_0_l.
rewrite Ropp_mult_distr_r_reverse.
rewrite Rmult_0_r.
rewrite Rplus_opp_l.
simpl.
rewrite Rminus_0_r.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite (Rinv_l (Cip V I (Z t) (Z t) CRe) H4).
rewrite Rmult_0_l.
rewrite Rmult_0_l.
rewrite (Cip_pos_im V I (Z t)).
rewrite Rmult_0_r.
rewrite Rminus_0_r.
rewrite Rplus_0_r.
reflexivity.
move=> H5.
apply H4.
suff: (Cip V I (Z t) (Z t) CRe = proj1_sig
       (exist (fun (r : R) => r >= 0) (Cip V I (Z t) (Z t) CRe) (Cip_pos_re V I (Z t)))).
move=> H6.
rewrite H6.
rewrite (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (Cip V I (Z t) (Z t) CRe) (Cip_pos_re V I (Z t))))).
rewrite H5.
apply (Rmult_0_r 0).
reflexivity.
move=> H4.
apply (LinearlyIndependentNotContainVOVS Cfield V (Count N) Z (proj1 H3) t).
apply (proj1 (Cip_refl V I (Z t))).
apply functional_extensionality.
move=> m.
elim (CReorCIm m).
move=> H5.
rewrite H5.
apply H4.
move=> H5.
rewrite H5.
apply (Cip_pos_im V I (Z t)).
move=> t1 t2 H4.
rewrite (Cip_linear_mult_l V I).
rewrite (Cip_linear_mult_r V I).
rewrite (proj1 (proj2 H3) t1 t2 H4).
suff: (Cmult
     (Conjugate
        (IRC
           (/
            MySqrt
              (exist (fun (r : R) => r >= 0) (Cip V I (Z t2) (Z t2) CRe)
                 (Cip_pos_re V I (Z t2)))))) CO = CO).
move=> H5.
rewrite H5.
apply (Fmul_O_r Cfield).
apply (Fmul_O_r Cfield).
move=> m.
apply (proj1 (proj2 (SpanSubspaceVS Cfield V
     {k : Count N | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x))))).
apply (proj2 (proj2 H3) m).
move=> V I.
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
elim (H1 (fun (m : Count N) =>
          W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m)))).
move=> W0 H5.
exists (fun (m : Count (S N)) => match excluded_middle_informative (proj1_sig m < N)%nat with
  | left H => W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig m) H)
  | right _ => Vadd Cfield V (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) (Vopp Cfield V (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM Cfield V) (fun (m : Count N) => Vmul Cfield V (Conjugate (Cmult (Cip V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) (Cinv (Cip V I (W0 m) (W0 m))))) (W0 m))))
end).
apply conj.
apply (Proposition_5_2 Cfield V N H3 H4).
apply conj.
suff: ((fun (m : Count N) =>
   match
     excluded_middle_informative
       (proj1_sig (exist (fun (n : nat) => n < S N) (proj1_sig m) (H3 m)) <
        N)%nat
   with
   | left H =>
       W0
         (exist (fun (k : nat) => (k < N)%nat)
            (proj1_sig
               (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m)))
            H)
   | right _ =>
       Vadd Cfield V
         (W (exist (fun (k : nat) => (k < S N)%nat) N H4))
         (Vopp Cfield V
            (MySumF2 (Count N)
               (exist (Finite (Count N)) (Full_set (Count N))
                  (CountFinite N)) (VSPCM Cfield V) (fun (m : Count N) => Vmul Cfield V (Conjugate (Cmult (Cip V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) (Cinv (Cip V I (W0 m) (W0 m))))) (W0 m))))
   end) = W0).
move=> H6.
rewrite H6.
apply (proj1 H5).
apply functional_extensionality.
move=> k.
elim (excluded_middle_informative
    (proj1_sig (exist (fun (n : nat) => n < S N) (proj1_sig k) (H3 k)) < N)%nat).
move=> H6.
suff: ((exist (fun (l : nat) => (l < N)%nat)
     (proj1_sig
        (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig k) (H3 k))) H6) = k).
move=> H7.
rewrite H7.
reflexivity.
apply sig_map.
reflexivity.
move=> H6.
elim (H6 (proj2_sig k)).
elim (excluded_middle_informative
      (proj1_sig (exist (fun (n : nat) => n < S N) N H4) < N)%nat).
move=> H6.
elim (lt_irrefl N H6).
move=> H6 H7.
apply (proj2 (proj1 (Proposition_5_2 Cfield V N H3 H4 W) H2)).
suff: (In (VT Cfield V)
       (SpanVS Cfield V (Count N)
          (fun (m : Count N) =>
           match
             excluded_middle_informative
               (proj1_sig
                  (exist (fun (n : nat) => n < S N) (proj1_sig m) (H3 m)) <
                N)%nat
           with
           | left H =>
               W0
                 (exist (fun (k : nat) => (k < N)%nat)
                    (proj1_sig
                       (exist (fun (n : nat) => (n < S N)%nat)
                          (proj1_sig m) (H3 m))) H)
           | right _ =>
               Vadd Cfield V
                 (W (exist (fun (k : nat) => (k < S N)%nat) N H4))
                 (Vopp Cfield V
                    (MySumF2 (Count N)
                       (exist (Finite (Count N)) 
                          (Full_set (Count N)) (CountFinite N))
                       (VSPCM Cfield V)
                       (fun (m0 : Count N) =>
                        Vmul Cfield V
                          (Conjugate (Cmult (Cip V I (W0 m0)
                             (W
                                (exist (fun (k : nat) => (k < S N)%nat) N
                                   H4))) (Cinv (Cip V I (W0 m0) (W0 m0)))))
                          (W0 m0))))
           end))
          (W (exist (fun (k : nat) => (k < S N)%nat) N H4))
          ).
elim.
move=> x H8.
rewrite H8.
apply (FiniteSetInduction (Count N)
     (exist (Finite (Count N))
        (fun (t : Count N) => proj1_sig x t <> FO Cfield) 
        (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS Cfield V (Count N)
     (fun (m : Count N) =>
      W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m)))))).
move=> B b H9 H10 H11 H12.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS Cfield V (Count N)
     (fun (m : Count N) =>
      W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))))).
apply H12.
apply (proj1 (proj2 (SpanSubspaceVS Cfield V (Count N)
     (fun (m : Count N) =>
      W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m)))))).
elim (excluded_middle_informative
      (proj1_sig (exist (fun (n : nat) => n < S N) (proj1_sig b) (H3 b)) <
       N)%nat).
move=> H13.
suff: ((exist (fun (k : nat) => (k < N)%nat)
        (proj1_sig
           (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig b) (H3 b)))
        H13) = b).
move=> H14.
rewrite H14.
elim (proj2 (proj2 H5) b).
move=> y H15.
rewrite H15.
apply (FiniteSetInduction {k : Count N | (proj1_sig k <= proj1_sig b)%nat}
     (exist (Finite {k : Count N | (proj1_sig k <= proj1_sig b)%nat})
        (fun (t : {k : Count N | (proj1_sig k <= proj1_sig b)%nat}) =>
         proj1_sig y t <> FO Cfield) (proj2_sig y))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS Cfield V (Count N)
     (fun (m : Count N) =>
      W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m)))))).
move=> D d H16 H17 H18 H19.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS Cfield V (Count N)
     (fun (m : Count N) =>
      W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))))).
apply H19.
apply (proj1 (proj2 (SpanSubspaceVS Cfield V (Count N)
     (fun (m : Count N) =>
      W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m)))))).
apply (SpanContainSelfVS Cfield V (Count N)
     (fun (m : Count N) =>
      W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))) (proj1_sig d)).
apply H18.
apply sig_map.
reflexivity.
move=> H13.
elim (H13 (proj2_sig b)).
apply H11.
rewrite - {3} (Vadd_O_r Cfield V (W (exist (fun (k : nat) => (k < S N)%nat) N H4))).
rewrite - (Vadd_opp_l Cfield V (MySumF2 (Count N)
                (exist (Finite (Count N)) (Full_set (Count N))
                   (CountFinite N)) (VSPCM Cfield V)
                (fun (m : Count N) =>
                 Vmul Cfield V
                   (Conjugate (Cmult (Cip V I (W0 m)
                      (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) 
                    (Cinv (Cip V I (W0 m) (W0 m))))) (W0 m)))).
rewrite - (Vadd_assoc Cfield V (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) (Vopp Cfield V (MySumF2 (Count N)
                (exist (Finite (Count N)) (Full_set (Count N))
                   (CountFinite N)) (VSPCM Cfield V)
                (fun (m : Count N) =>
                 Vmul Cfield V
                   (Conjugate (Cmult (Cip V I (W0 m)
                      (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) 
                    (Cinv (Cip V I (W0 m) (W0 m))))) (W0 m)))) (MySumF2 (Count N)
                (exist (Finite (Count N)) (Full_set (Count N))
                   (CountFinite N)) (VSPCM Cfield V)
                (fun (m : Count N) =>
                 Vmul Cfield V
                   (Conjugate (Cmult (Cip V I (W0 m)
                      (W (exist (fun (k : nat) => (k < S N)%nat) N H4)))
                    (Cinv (Cip V I (W0 m) (W0 m))))) (W0 m)))).
apply (SpanSubspaceVS Cfield V).
apply H7.
apply (FiniteSetInduction (Count N)
     (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun (P : {X : Ensemble (Count N) | Finite (Count N) X}) => In (VT Cfield V)
  (SpanVS Cfield V (Count N)
     (fun (m : Count N) =>
      match
        excluded_middle_informative
          (proj1_sig
             (exist (fun (n : nat) => n < S N) (proj1_sig m) (H3 m)) < N)%nat
      with
      | left H =>
          W0
            (exist (fun (k : nat) => (k < N)%nat)
               (proj1_sig
                  (exist (fun (n : nat) => (n < S N)%nat) 
                     (proj1_sig m) (H3 m))) H)
      | right _ =>
          Vadd Cfield V
            (W (exist (fun (k : nat) => (k < S N)%nat) N H4))
            (Vopp Cfield V
               (MySumF2 (Count N)
                  (exist (Finite (Count N)) (Full_set (Count N))
                     (CountFinite N)) (VSPCM Cfield V)
                  (fun (m0 : Count N) =>
                   Vmul Cfield V
                     (Conjugate (Cmult (Cip V I (W0 m0)
                        (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) 
                      (Cinv (Cip V I (W0 m0) (W0 m0))))) (W0 m0))))
      end))
  (MySumF2 (Count N)
     P
     (VSPCM Cfield V)
     (fun (m : Count N) =>
      Vmul Cfield V
        (Conjugate (Cmult (Cip V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4)))
         (Cinv (Cip V I (W0 m) (W0 m))))) (W0 m))))).
apply conj.
rewrite MySumF2Empty.
apply (SpanSubspaceVS Cfield V (Count N)).
move=> B b H8 H9 H10 H11.
rewrite MySumF2Add.
apply (SpanSubspaceVS Cfield V (Count N)).
apply H11.
apply (SpanSubspaceVS Cfield V (Count N)).
suff: ((fun (m : Count N) =>
      match
        excluded_middle_informative
          (proj1_sig
             (exist (fun (n : nat) => n < S N) (proj1_sig m) (H3 m)) < N)%nat
      with
      | left H =>
          W0
            (exist (fun (k : nat) => (k < N)%nat)
               (proj1_sig
                  (exist (fun (n : nat) => (n < S N)%nat) 
                     (proj1_sig m) (H3 m))) H)
      | right _ =>
          Vadd Cfield V
            (W (exist (fun (k : nat) => (k < S N)%nat) N H4))
            (Vopp Cfield V
               (MySumF2 (Count N)
                  (exist (Finite (Count N)) (Full_set (Count N))
                     (CountFinite N)) (VSPCM Cfield V)
                  (fun (m0 : Count N) =>
                   Vmul Cfield V
                     (Conjugate (Cmult (Cip V I (W0 m0)
                        (W (exist (fun k : nat => (k < S N)%nat) N H4)))
                      (Cinv (Cip V I (W0 m0) (W0 m0))))) (W0 m0))))
      end) = W0).
move=> H12.
rewrite H12.
apply (SpanContainSelfVS Cfield V (Count N) W0 b).
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative
    (proj1_sig (exist (fun (n : nat) => n < S N) (proj1_sig m) (H3 m)) < N)%nat).
move=> H12.
suff: ((exist (fun (k : nat) => (k < N)%nat)
     (proj1_sig
        (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))) H12) = m).
move=> H13.
rewrite H13.
reflexivity.
apply sig_map.
reflexivity.
move=> H12.
elim (H12 (proj2_sig m)).
apply H10.
apply conj.
suff: (forall (t1 t2 : Count (S N)),
(proj1_sig t1 < proj1_sig t2)%nat ->
Cip V I
  match excluded_middle_informative (proj1_sig t1 < N)%nat with
  | left H => W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H)
  | right _ =>
      Vadd Cfield V
        (W (exist (fun (k : nat) => (k < S N)%nat) N H4))
        (Vopp Cfield V
           (MySumF2 (Count N)
              (exist (Finite (Count N)) (Full_set (Count N))
                 (CountFinite N)) (VSPCM Cfield V)
              (fun (m : Count N) =>
               Vmul Cfield V
                 (Conjugate (Cmult
                    (Cip V I (W0 m)
                       (W (exist (fun (k : nat) => (k < S N)%nat) N H4)))
                    (Cinv (Cip V I (W0 m) (W0 m))))) 
                 (W0 m))))
  end
  match excluded_middle_informative (proj1_sig t2 < N)%nat with
  | left H => W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t2) H)
  | right _ =>
      Vadd Cfield V
        (W (exist (fun (k : nat) => (k < S N)%nat) N H4))
        (Vopp Cfield V
           (MySumF2 (Count N)
              (exist (Finite (Count N)) (Full_set (Count N))
                 (CountFinite N)) (VSPCM Cfield V)
              (fun (m : Count N) =>
               Vmul Cfield V
                 (Conjugate (Cmult
                    (Cip V I (W0 m)
                       (W (exist (fun (k : nat) => (k < S N)%nat) N H4)))
                    (Cinv (Cip V I (W0 m) (W0 m))))) 
                 (W0 m))))
  end = CO).
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
rewrite (Cip_sym V I).
rewrite (H6 t2 t1 H8).
apply ConjugateCO.
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
rewrite (Cip_linear_plus_r V I).
rewrite (Cip_linear_opp_r V I).
suff: (Cip V I (W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7))
  (MySumF2 (Count N)
     (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))
     (VSPCM Cfield V)
     (fun (m : Count N) =>
      Vmul Cfield V
        (Conjugate (Cmult (Cip V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4)))
         (Cinv (Cip V I (W0 m) (W0 m))))) (W0 m))) = MySumF2 (Count N)
     (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (FPCM Cfield) (fun (m : Count N) =>
      Cip V I (W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7)) (Vmul Cfield V
        (Conjugate (Cmult (Cip V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) 
         (Cinv (Cip V I (W0 m) (W0 m))))) (W0 m)))).
move=> H9.
rewrite H9.
rewrite (MySumF2Included (Count N) (FiniteSingleton (Count N) (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7)) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (Cip_linear_mult_r V I).
rewrite ConjugateInvolutive.
rewrite Cmult_assoc.
rewrite Cinv_l.
suff: (Cmult
           (Cip V I
              (W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7))
              (W (exist (fun (k : nat) => (k < S N)%nat) N H4))) CI = Cip V I
              (W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7))
              (W (exist (fun (k : nat) => (k < S N)%nat) N H4))).
move=> H10.
rewrite H10.
rewrite (CM_O_r (FPCM Cfield)).
apply Cplus_opp_r.
apply (Fmul_I_r Cfield).
move=> H10.
apply (LinearlyIndependentNotContainVOVS Cfield V (Count N) W0 (proj1 H5) (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7)).
apply (proj1 (Cip_refl V I (W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7))) H10).
move=> u.
elim.
move=> u0 H10 H11.
rewrite (Cip_linear_mult_r V I).
rewrite (proj1 (proj2 H5) (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7) u0).
apply (Fmul_O_r Cfield).
move=> H12.
apply H10.
rewrite H12.
apply (In_singleton (Count N) u0).
move=> m H10.
apply (Full_intro (Count N) m).
apply (FiniteSetInduction (Count N)
  (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Cip_mult_0_r V I).
move=> B b H9 H10 H11 H12.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Cip_linear_plus_r V I).
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
apply (FiniteSetInduction {k : Count N
     | (proj1_sig k <=
        proj1_sig (exist (fun (k0 : nat) => k0 < N) (proj1_sig m) H6))%nat} (exist
        (Finite
           {k : Count N
           | (proj1_sig k <=
              proj1_sig (exist (fun (k0 : nat) => k0 < N) (proj1_sig m) H6))%nat})
        (fun
           t : {k : Count N
               | (proj1_sig k <=
                  proj1_sig
                    (exist (fun (k0 : nat) => k0 < N) (proj1_sig m) H6))%nat}
         => proj1_sig x t <> FO Cfield) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
apply (SpanSubspaceVS Cfield V).
move=> B b H8 H9 H10 H11.
rewrite MySumF2Add.
apply (SpanSubspaceVS Cfield V).
apply H11.
apply (SpanSubspaceVS Cfield V).
suff: (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig b))
        (H3 (proj1_sig b)) = proj1_sig (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig b))
        (H3 (proj1_sig b))) (proj2_sig b))).
move=> H12.
rewrite H12.
apply (SpanContainSelfVS Cfield V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x0 : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x0)) (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig b))
        (H3 (proj1_sig b))) (proj2_sig b))).
reflexivity.
apply H10.
move=> H6.
apply (SpanSubspaceVS Cfield V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x))).
suff: (proj1_sig (exist (fun (k : nat) => (k < S N)%nat) N H4) <= proj1_sig m)%nat.
move=> H7.
suff: (exist (fun (k : nat) => (k < S N)%nat) N H4 = proj1_sig (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (k : nat) => (k < S N)%nat) N H4) H7)).
move=> H8.
rewrite H8.
apply (SpanContainSelfVS Cfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x)) (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (k : nat) => (k < S N)%nat) N H4) H7)).
reflexivity.
elim (le_or_lt N (proj1_sig m)).
apply.
move=> H7.
elim (H6 H7).
apply (SubspaceMakeVSVoppSub Cfield V (SpanVS Cfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x))) (SpanSubspaceVS Cfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x)))).
apply (FiniteSetInduction (Count N)
     (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS Cfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x))))).
move=> B b H7 H8 H9 H10.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS Cfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x)))).
apply H10.
apply (proj1 (proj2 (SpanSubspaceVS Cfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x))))).
elim (proj2 (proj2 H5) b).
move=> x H11.
rewrite H11.
apply (FiniteSetInduction {k : Count N | (proj1_sig k <= proj1_sig b)%nat}
     (exist (Finite {k : Count N | (proj1_sig k <= proj1_sig b)%nat})
        (fun (t : {k : Count N | (proj1_sig k <= proj1_sig b)%nat}) =>
         proj1_sig x t <> FO Cfield) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS Cfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x))))).
move=> D d H12 H13 H14 H15.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS Cfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x)))).
apply H15.
apply (proj1 (proj2 (SpanSubspaceVS Cfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x))))).
suff: (proj1_sig (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig d))
        (H3 (proj1_sig d))) <= proj1_sig m)%nat.
move=> H16.
suff: (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig d))
        (H3 (proj1_sig d)) = proj1_sig (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig d))
        (H3 (proj1_sig d))) H16)).
move=> H17.
rewrite H17.
apply (SpanContainSelfVS Cfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat} (fun (y : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig y)) (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig d))
        (H3 (proj1_sig d))) H16)).
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
apply (proj1 (proj1 (Proposition_5_2 Cfield V N H3 H4 W) H2)).
elim (Proposition_5_2_exists Cfield V N).
move=> H4.
elim.
move=> H5 H6.
apply H5.
elim (Proposition_5_2_exists Cfield V N).
move=> H4 H5.
apply H4.
Qed.

Lemma GramSchmidtLinearlyIndepententC : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (N : nat) (W : Count N -> VT Cfield V), LinearlyIndependentVS Cfield V (Count N) W -> {Z : Count N -> VT Cfield V | OrthonormalSystemC V I (Count N) Z /\ SpanVS Cfield V (Count N) W = SpanVS Cfield V (Count N) Z}.
Proof.
move=> V I N W H1.
elim (GramSchmidtLinearlyIndepententC_sub V I N W H1).
move=> Z H2.
exists Z.
suff: (forall (U : Count N -> VT Cfield V), LinearlyIndependentVS Cfield V (Count N) U -> FiniteDimensionVS Cfield (SubspaceMakeVS Cfield V (SpanVS Cfield V (Count N) U) (SpanSubspaceVS Cfield V (Count N) U))).
move=> H3.
suff: (forall (U : Count N -> VT Cfield V) (H : LinearlyIndependentVS Cfield V (Count N) U), DimensionSubspaceVS Cfield V
  (SpanVS Cfield V (Count N) U)
  (SpanSubspaceVS Cfield V (Count N) U) 
  (H3 U H) = N).
move=> H4.
apply conj.
apply (proj1 H2).
suff: (Included (VT Cfield V) (SpanVS Cfield V (Count N) Z) (SpanVS Cfield V (Count N) W)).
move=> H5.
rewrite (proj1 (Proposition_5_9_1_3_subspace Cfield V (SpanVS Cfield V (Count N) Z) (SpanVS Cfield V (Count N) W) (SpanSubspaceVS Cfield V (Count N) Z) (SpanSubspaceVS Cfield V (Count N) W) H5 (H3 W H1) (H3 Z (OrthonormalSystemLinearlyIndependentC V I (Count N) Z (proj1 H2))))).
reflexivity.
rewrite (H4 W H1).
apply (H4 Z (OrthonormalSystemLinearlyIndependentC V I (Count N) Z (proj1 H2))).
move=> v.
elim.
move=> x H5.
rewrite H5.
apply (FiniteSetInduction (Count N)
     (exist (Finite (Count N))
        (fun (t : Count N) => proj1_sig x t <> FO Cfield) 
        (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS Cfield V (Count N) W))).
move=> B b H6 H7 H8 H9.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS Cfield V (Count N) W)).
apply H9.
apply (proj1 (proj2 (SpanSubspaceVS Cfield V (Count N) W))).
elim (proj2 H2 b).
move=> y H10.
rewrite H10.
apply (FiniteSetInduction {k : Count N | (proj1_sig k <= proj1_sig b)%nat}
     (exist (Finite {k : Count N | (proj1_sig k <= proj1_sig b)%nat})
        (fun (t : {k : Count N | (proj1_sig k <= proj1_sig b)%nat}) =>
         proj1_sig y t <> FO Cfield) (proj2_sig y))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS Cfield V (Count N) W))).
move=> D d H11 H12 H13 H14.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS Cfield V (Count N) W)).
apply H14.
apply (proj1 (proj2 (SpanSubspaceVS Cfield V (Count N) W))).
apply (SpanContainSelfVS Cfield V (Count N) W (proj1_sig d)).
apply H13.
apply H8.
move=> U H4.
apply (DimensionVSNature2 Cfield (SubspaceMakeVS Cfield V
     (SpanVS Cfield V (Count N) U)
     (SpanSubspaceVS Cfield V (Count N) U)) (H3 U H4) N (fun (m : Count N) => exist (SpanVS Cfield V (Count N) U) (U m) (SpanContainSelfVS Cfield V (Count N) U m)) H4).
move=> U H3.
exists N.
exists (fun (m : Count N) => exist (SpanVS Cfield V (Count N) U) (U m) (SpanContainSelfVS Cfield V (Count N) U m)).
apply H3.
Qed.

Lemma GramSchmidtBasisC : forall (V : VectorSpace Cfield) (I : CInner_Product_Space V) (N : nat) (W : Count N -> VT Cfield V), BasisVS Cfield V (Count N) W -> {Z : Count N -> VT Cfield V | OrthonormalSystemC V I (Count N) Z /\ BasisVS Cfield V (Count N) Z /\ forall (m : Count N), In (VT Cfield V) (SpanVS Cfield V {k : Count N | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))) (Z m)}.
Proof.
move=> V I N W H1.
elim (GramSchmidtLinearlyIndepententC_sub V I N W).
move=> Z H2.
exists Z.
apply conj.
apply (proj1 H2).
apply conj.
suff: (FiniteDimensionVS Cfield V).
move=> H3.
apply (Corollary_5_8_2_3 Cfield V N Z H3).
apply conj.
apply (OrthonormalSystemLinearlyIndependentC V I (Count N) Z (proj1 H2)).
apply (DimensionVSNature2 Cfield V H3 N W H1).
exists N.
exists W.
apply H1.
apply (proj2 H2).
apply (proj1 (proj1 (BasisLIGeVS Cfield V (Count N) W) H1)).
Qed.

Definition AdjointMatrix (M N : nat) (A : Matrix Cfield M N) := (fun (x : {n : nat | (n < N)%nat}) (y : {n : nat | (n < M)%nat}) => Conjugate (A y x)).

Lemma AdjointMatrixMult : forall (M N K : nat) (A : Matrix Cfield M N) (B : Matrix Cfield N K), AdjointMatrix M K (Mmult Cfield M N K A B) = Mmult Cfield K N M (AdjointMatrix N K B) (AdjointMatrix M N A).
Proof.
move=> M N K A B.
unfold AdjointMatrix.
unfold Mmult.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply (FiniteSetInduction {n : nat | (n < N)%nat}
     (exist (Finite (Count N)) (Full_set {n : nat | (n < N)%nat})
        (CountFinite N))).
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

Definition HermitianMatrix (N : nat) (A : Matrix Cfield N N) := AdjointMatrix N N A = A.

Definition UnitaryMatrix (N : nat) (A : Matrix Cfield N N) := Mmult Cfield N N N (AdjointMatrix N N A) A = MI Cfield N.

Definition MDiag (f : Field) (N : nat) (a : {n : nat | (n < N)%nat} -> FT f) := fun (x y : {n : nat | (n < N)%nat}) => match Nat.eq_dec (proj1_sig x) (proj1_sig y) with
  | left _ => a x
  | right _ => FO f
end.

Definition MVectorToMatrix (f : Field) (N : nat) (v : {n : nat | (n < N)%nat} -> FT f) := fun (x : {n : nat | (n < N)%nat}) (y : {n : nat | (n < 1)%nat}) => v x.

Definition MMatrixToVector (f : Field) (N : nat) (A : Matrix f N 1) := fun (x : {n : nat | (n < N)%nat}) => A x (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1)).

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
suff: (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1) = y).
move=> H1.
rewrite H1.
reflexivity.
apply sig_map.
elim (le_lt_or_eq O (proj1_sig y) (le_0_n (proj1_sig y))).
move=> H1.
elim (le_not_lt (proj1_sig y) O (le_S_n (proj1_sig y) O (proj2_sig y)) H1).
apply.
Qed.

Definition MVmult (f : Field) (M N : nat) (A : Matrix f M N) (v : {n : nat | (n < N)%nat} -> FT f) := MMatrixToVector f M (Mmult f M N 1 A (MVectorToMatrix f N v)).

Lemma UnitaryMatrixChain : forall (N : nat) (A B : Matrix Cfield N N), UnitaryMatrix N A -> UnitaryMatrix N B -> UnitaryMatrix N (Mmult Cfield N N N A B).
Proof.
move=> N A B H1 H2.
unfold UnitaryMatrix.
rewrite (AdjointMatrixMult N N N A B).
rewrite (Mmult_assoc Cfield N N N N (AdjointMatrix N N B) (AdjointMatrix N N A) (Mmult Cfield N N N A B)).
rewrite - (Mmult_assoc Cfield N N N N (AdjointMatrix N N A) A B).
rewrite H1.
rewrite (Mmult_I_l Cfield N N B).
apply H2.
Qed.

Definition Cn (N : nat) := Count N -> C.

Definition CnInnerProduct (N : nat) (x y : Cn N) := MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (FPCM Cfield) (fun (n : Count N) => Cmult (x n) (Conjugate (y n))).

Lemma Cnip_sym : forall (N : nat) (x y : Cn N), CnInnerProduct N x y = Conjugate (CnInnerProduct N y x).
Proof.
move=> N x y.
unfold CnInnerProduct.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite ConjugateCO.
reflexivity.
move=> B b H1 H2 H3 H4.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite Proposition_4_8_1_1.
rewrite Proposition_4_8_2.
rewrite ConjugateInvolutive.
rewrite Cmult_comm.
rewrite H4.
reflexivity.
apply H3.
apply H3.
Qed.

Lemma Cnip_linear_mult_l : forall (N : nat) (c : C) (x y : Cn N), CnInnerProduct N (Vmul Cfield (FnVS Cfield N) c x) y = Cmult c (CnInnerProduct N x y).
Proof.
move=> N c x y.
unfold CnInnerProduct.
apply (FiniteSetInduction (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
suff: (Cmult c CO = Fmul Cfield c (FO Cfield)).
move=> H1.
rewrite H1.
rewrite (Fmul_O_r Cfield c).
reflexivity.
reflexivity.
move=> B b H1 H2 H3 H4.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite Cmult_plus_distr_l.
rewrite Cmult_assoc.
rewrite H4.
reflexivity.
apply H3.
apply H3.
Qed.

Lemma Cnip_linear_plus_l : forall (N : nat) (x1 x2 y : Cn N), CnInnerProduct N (Vadd Cfield (FnVS Cfield N) x1 x2) y = Cplus (CnInnerProduct N x1 y) (CnInnerProduct N x2 y).
Proof.
move=> N x1 x2 y.
unfold CnInnerProduct.
apply MySumF2Distr.
move=> u H1.
simpl.
apply (Fmul_add_distr_r Cfield (x1 u) (x2 u) (Conjugate (y u))).
Qed.

Lemma Cnip_pos_re : forall (N : nat) (x : Cn N), CnInnerProduct N x x CRe >= 0.
Proof.
move=> N x.
unfold CnInnerProduct.
apply MySumF2Induction.
apply conj.
right.
reflexivity.
move=> cm u H1 H2.
simpl.
unfold Cplus.
unfold Rnplus.
apply Rle_ge.
apply (Rplus_le_le_0_compat (cm CRe) (Cmult (x u) (Conjugate (x u)) CRe)).
apply Rge_le.
apply H2.
unfold Cmult.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
unfold Rminus.
apply (Rplus_le_le_0_compat (x u CRe * x u CRe) (- (x u CIm * - x u CIm))).
apply Rge_le.
apply Formula_1_3.
rewrite Ropp_mult_distr_l.
apply Rge_le.
apply Formula_1_3.
Qed.

Lemma Cnip_refl : forall (N : nat) (x : Cn N), CnInnerProduct N x x = CO <-> x = VO Cfield (FnVS Cfield N).
Proof.
move=> N x.
apply conj.
move=> H1.
apply functional_extensionality.
move=> m.
suff: (Cmult (x m) (Conjugate (x m)) CRe = 0).
unfold Cmult.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
unfold Rminus.
rewrite Ropp_mult_distr_l.
move=> H2.
apply functional_extensionality.
move=> n.
elim (CReorCIm n).
move=> H3.
rewrite H3.
suff: (x m CRe * x m CRe = 0).
move=> H4.
elim (Rle_or_lt (x m CRe) 0).
elim.
move=> H5.
elim (Rlt_not_eq 0 (x m CRe * x m CRe)).
rewrite - (Rmult_0_r (x m CRe)).
apply (Rmult_lt_gt_compat_neg_l (x m CRe) (x m CRe) 0 H5 H5).
rewrite H4.
reflexivity.
apply.
move=> H5.
elim (Rlt_not_eq 0 (x m CRe * x m CRe)).
apply (Rmult_lt_0_compat (x m CRe) (x m CRe) H5 H5).
rewrite H4.
reflexivity.
elim (Formula_1_3 (x m CRe)).
move=> H4.
elim (Rgt_not_eq (x m CRe * x m CRe + - x m CIm * - x m CIm) 0).
apply Rplus_lt_le_0_compat.
apply H4.
apply Rge_le.
apply (Formula_1_3 (- x m CIm)).
apply H2.
apply.
move=> H3.
rewrite H3.
suff: (- x m CIm * - x m CIm = 0).
move=> H4.
elim (Rle_or_lt (x m CIm) 0).
elim.
move=> H5.
elim (Rgt_not_eq (- x m CIm * - x m CIm) 0).
apply (Rmult_lt_0_compat (- x m CIm) (- x m CIm)).
apply (Ropp_0_gt_lt_contravar (x m CIm) H5).
apply (Ropp_0_gt_lt_contravar (x m CIm) H5).
apply H4.
apply.
move=> H5.
elim (Rgt_not_eq (- x m CIm * - x m CIm) 0).
rewrite - (Rmult_0_r (- x m CIm)).
apply (Rmult_lt_gt_compat_neg_l (- x m CIm) (- x m CIm) 0).
apply (Ropp_lt_gt_0_contravar (x m CIm) H5).
apply (Ropp_lt_gt_0_contravar (x m CIm) H5).
apply H4.
elim (Formula_1_3 (- x m CIm)).
move=> H4.
elim (Rgt_not_eq (x m CRe * x m CRe + - x m CIm * - x m CIm) 0).
apply Rplus_le_lt_0_compat.
apply Rge_le.
apply (Formula_1_3 (x m CRe)).
apply H4.
apply H2.
apply.
suff: (CnInnerProduct N x x CRe = 0).
unfold CnInnerProduct.
rewrite (MySumF2Included (Count N) (FiniteSingleton (Count N) m)).
rewrite MySumF2Singleton.
simpl.
unfold Cplus.
unfold Rnplus.
move=> H2.
suff: (forall (n : Count N), 0 <= Cmult (x n) (Conjugate (x n)) CRe).
move=> H3.
elim (H3 m).
move=> H4.
elim (Rgt_not_eq (Cmult (x m) (Conjugate (x m)) CRe +
     MySumF2 (Count N)
       (FiniteIntersection (Count N)
          (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))
          (Complement (Count N) (Singleton (Count N) m))) 
       (FPCM Cfield) (fun (n : Count N) => Cmult (x n) (Conjugate (x n))) CRe) 0).
apply Rplus_lt_le_0_compat.
apply H4.
apply MySumF2Induction.
apply conj.
right.
reflexivity.
move=> cm u H5 H6.
apply Rplus_le_le_0_compat.
apply H6.
apply (H3 u).
apply H2.
move=> H4.
rewrite H4.
reflexivity.
move=> n.
unfold Cmult.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
apply (Rplus_le_le_0_compat (x n CRe * x n CRe) (- (x n CIm * - x n CIm))).
apply Rge_le.
apply (Formula_1_3 (x n CRe)).
rewrite (Ropp_mult_distr_l (x n CIm) (- x n CIm)).
apply Rge_le.
apply (Formula_1_3 (- x n CIm)).
move=> n H2.
apply (Full_intro (Count N) n).
rewrite H1.
reflexivity.
move=> H1.
rewrite H1.
apply MySumF2O.
move=> u H2.
unfold Cmult.
apply functional_extensionality.
move=> n.
elim (CReorCIm n).
move=> H3.
rewrite H3.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
simpl.
unfold CO.
unfold RnO.
rewrite (Rmult_0_l 0).
rewrite (Rmult_0_l (- 0)).
apply (Rplus_opp_r 0).
move=> H3.
rewrite H3.
unfold Conjugate.
rewrite CmakeIm.
rewrite CmakeRe.
rewrite CmakeIm.
simpl.
unfold CO.
unfold RnO.
rewrite (Rmult_0_l 0).
rewrite (Rmult_0_l (- 0)).
apply (Rplus_0_r 0).
Qed.

Definition CnInner_Product_Space (N : nat) := mkCInner_Product_Space (FnVS Cfield N) (CnInnerProduct N) (Cnip_sym N) (Cnip_linear_mult_l N) (Cnip_linear_plus_l N) (Cnip_pos_re N) (Cnip_refl N).

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

Lemma AdjointMatrixO : forall (M N : nat), AdjointMatrix M N (MO Cfield M N) = MO Cfield N M.
Proof.
move=> M N.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
apply ConjugateCO.
Qed.

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
suff: (exists (V : Matrix Cfield (S N) (S N)), UnitaryMatrix (S N) V /\ forall (m : {n : nat | (n < S N)%nat}), (proj1_sig m > O)%nat -> Mmult Cfield (S N) (S N) (S N) (AdjointMatrix (S N) (S N) V)
    (Mmult Cfield (S N) (S N) (S N) A V) m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = CO).
elim.
move=> V H3.
suff: (exists (B : Matrix Cfield N N) (la : C), HermitianMatrix N B /\ Mmult Cfield (S N) (S N) (S N) (AdjointMatrix (S N) (S N) V)
        (Mmult Cfield (S N) (S N) (S N) A V) = MBlockH Cfield 1 N (S N) (MBlockW Cfield 1 1 N (fun (_ _ : {n : nat | (n < 1)%nat}) => la) (MO Cfield 1 N)) (MBlockW Cfield N 1 N (MO Cfield N 1) B)).
elim.
move=> B.
elim.
move=> la H4.
elim (H1 B (proj1 H4)).
move=> W.
elim.
move=> D H5.
exists (Mmult Cfield (S N) (S N) (S N) V (MBlockH Cfield 1 N (S N)
       (MBlockW Cfield 1 1 N (fun _ _ : {n : nat | (n < 1)%nat} => CI)
          (MO Cfield 1 N)) (MBlockW Cfield N 1 N (MO Cfield N 1) W))).
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
suff: (exist (Finite (Count 1)) (Full_set {n : nat | (n < 1)%nat})
     (CountFinite 1) = FiniteSingleton {n : nat | (n < 1)%nat} (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1))).
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
suff: (exist (Finite (Count 1)) (Full_set {n : nat | (n < 1)%nat})
     (CountFinite 1) = FiniteSingleton {n : nat | (n < 1)%nat} (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1))).
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
exists (fun (x y : {n : nat | (n < N)%nat}) => Mmult Cfield (S N) (S N) (S N) (AdjointMatrix (S N) (S N) V)
    (Mmult Cfield (S N) (S N) (S N) A V) (AddConnect 1 N (inr x)) (AddConnect 1 N (inr y))).
exists (Mmult Cfield (S N) (S N) (S N) (AdjointMatrix (S N) (S N) V)
    (Mmult Cfield (S N) (S N) (S N) A V) (AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat
           (le_n 1)))) (AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat
           (le_n 1))))).
suff: (HermitianMatrix (S N) (Mmult Cfield (S N) (S N) (S N)
  (fun (x0 y0 : {n : nat | (n < S N)%nat}) => Conjugate (V y0 x0))
  (Mmult Cfield (S N) (S N) (S N) A V))).
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
suff: (y = (exist (fun (n : nat) => (n < S N)%nat) 0%nat
           (le_n_S 0 N (le_0_n N)))).
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
suff: (x = (exist (fun (n : nat) => (n < S N)%nat) 0%nat
           (le_n_S 0 N (le_0_n N)))).
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
suff: (let Aform := fun (u : {n : nat | (n < S N)%nat} -> C) => CnInnerProduct (S N) u (MVmult Cfield (S N) (S N) A u) CRe in exists (V : Matrix Cfield (S N) (S N)),
  UnitaryMatrix (S N) V /\
  (forall (m : {n : nat | (n < S N)%nat}),
   (proj1_sig m > 0)%nat ->
   Mmult Cfield (S N) (S N) (S N) (AdjointMatrix (S N) (S N) V)
     (Mmult Cfield (S N) (S N) (S N) A V) m
     (exist (fun (n : nat) => (n < S N)%nat) 0%nat
        (le_n_S 0 N (Nat.le_0_l N))) = CO)).
apply.
move=> Aform.
suff: (exists (v : {n : nat | (n < S N)%nat} -> C), CnInnerProduct (S N) v v = CI /\ forall (w : {n : nat | (n < S N)%nat} -> C), CnInnerProduct (S N) w w = CI -> Aform w <= Aform v).
elim.
move=> v H3.
suff: (exists (V : Matrix Cfield (S N) (S N)),
  UnitaryMatrix (S N) V /\ V (exist (fun (n : nat) => (n < S N)%nat) 0%nat
           (le_n_S 0 N (le_0_n N))) = (fun (m : Count (S N)) => Conjugate (v m))).
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
suff: (Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) (exist (fun (n : nat) => (n < S N)%nat) O
           (le_n_S 0 N (le_0_n N))) (exist (fun (n : nat) => (n < S N)%nat) O
           (le_n_S 0 N (le_0_n N))) CRe = Aform v).
move=> H9.
suff: (forall (r1 r2 : R), (forall (eps : R), Aform v + (1 + 1) * eps * r1 + eps * eps * r2 <= (1 + eps * eps) * Aform v) -> r1 = 0).
move=> H10.
apply functional_extensionality.
move=> n.
elim (CReorCIm n).
move=> H11.
rewrite H11.
apply (H10 (Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m
  (exist (fun (n0 : nat) => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) CRe) (Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m m CRe)).
move=> eps.
suff: (Aform v +
(1 + 1) * eps *
Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m
  (exist (fun n0 : nat => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N)))
  CRe +
eps * eps *
Mmult Cfield (S N) (S N) (S N) V
     (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m m CRe) = Aform (MMatrixToVector Cfield (S N) (Mmult Cfield (S N) (S N) 1 (AdjointMatrix (S N) (S N) V) (MVectorToMatrix Cfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
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
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat
          (le_n_S 0 N (le_0_n N))))).
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
unfold Rnplus.
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
rewrite Rmult_0_l.
rewrite Rminus_0_r.
rewrite Rplus_0_r.
reflexivity.
elim.
reflexivity.
move=> u.
elim.
move=> u0 H15 H16.
suff: (In (Count (S N))
        (Complement (Count (S N))
           (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H16.
move=> u1 H17 H18 H19.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H20.
elim H17.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat
        (le_n_S 0 N (le_0_n N)))).
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
suff: (Mmult Cfield (S N) (S N) 1 (AdjointMatrix (S N) (S N) V)
              (MVectorToMatrix Cfield (S N)
                 (fun (l : Count (S N)) =>
                  match excluded_middle_informative (proj1_sig l = 0%nat) with
                  | left _ => CI
                  | right _ => match excluded_middle_informative (l = m)
                   with | left _ => Cmake eps 0
                   | right _ => CO
end
end)) = MVectorToMatrix Cfield (S N) (MVmult Cfield (S N) (S N) (AdjointMatrix (S N) (S N) V) (fun (l : Count (S N)) =>
                  match excluded_middle_informative (proj1_sig l = 0%nat) with
                  | left _ => CI
                  | right _ => match excluded_middle_informative (l = m)
                   with | left _ => Cmake eps 0
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
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat
          (le_n_S 0 N (le_0_n N))))).
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
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat
          (le_n_S 0 N (le_0_n N))))).
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat
          (le_n_S 0 N (le_0_n N)))) (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat})
     (CountFinite (S N)))).
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m)).
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m) (FiniteIntersection (Count (S N))
        (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat})
           (CountFinite (S N)))
        (Complement (Count (S N))
           (proj1_sig
              (FiniteSingleton (Count (S N))
                 (exist (fun (n : nat) => (n < S N)%nat) O
                    (le_n_S 0 N (le_0_n N)))))))).
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
rewrite (Cmult_comm (Mmult Cfield (S N) (S N) (S N) V
                 (Mmult Cfield (S N) (S N) (S N) A
                    (AdjointMatrix (S N) (S N) V)) m
                 (exist (fun (n0 : nat) => (n0 < S N)%nat) 0%nat
                    (le_n_S 0 N (Nat.le_0_l N))))).
rewrite Cmult_1_l.
unfold Cplus.
unfold Rnplus.
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
rewrite (Rmult_comm (Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V))
  (exist (fun (n0 : nat) => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N)))
  m CRe) eps).
rewrite (Rmult_comm (Mmult Cfield (S N) (S N) (S N) V
    (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m m
    CRe) eps).
unfold CO.
unfold RnO.
rewrite Rplus_0_r.
rewrite - Rmult_assoc.
rewrite - Rplus_assoc.
rewrite - Rplus_assoc.
suff: (Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V))
  (exist (fun n0 : nat => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N)))
  m CRe = Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V))
  m (exist (fun n0 : nat => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N)))
  CRe).
move=> H19.
rewrite H19.
reflexivity.
suff: (Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V))
   = AdjointMatrix (S N) (S N) (Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)))).
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
suff: (In (Count (S N))
        (Complement (Count (S N))
           (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H17.
move=> u1 H18 H19 H20.
unfold MVectorToMatrix.
unfold AdjointMatrix.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H21.
elim H18.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat
           (le_n_S 0 N (le_0_n N)))).
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
suff: (In (Count (S N))
        (Complement (Count (S N))
           (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H17.
move=> u1 H18 H19 H20.
unfold MVectorToMatrix.
unfold AdjointMatrix.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H21.
elim H18.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat
           (le_n_S 0 N (le_0_n N)))).
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
suff: (In (Count (S N))
        (Complement (Count (S N))
           (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H14.
move=> u1 H15 H16 H17.
unfold MVectorToMatrix.
unfold AdjointMatrix.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H18.
elim H15.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat
           (le_n_S 0 N (le_0_n N)))).
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
apply (H10 (Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m
  (exist (fun (n0 : nat) => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) CIm) (Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m m CRe)).
move=> eps.
suff: (Aform v +
(1 + 1) * eps *
Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m
  (exist (fun n0 : nat => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N)))
  CIm +
eps * eps *
Mmult Cfield (S N) (S N) (S N) V
     (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m m CRe) = Aform (MMatrixToVector Cfield (S N) (Mmult Cfield (S N) (S N) 1 (AdjointMatrix (S N) (S N) V) (MVectorToMatrix Cfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
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
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat
          (le_n_S 0 N (le_0_n N))))).
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
unfold Rnplus.
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
suff: (In (Count (S N))
        (Complement (Count (S N))
           (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H16.
move=> u1 H17 H18 H19.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H20.
elim H17.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat
        (le_n_S 0 N (le_0_n N)))).
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
suff: (Mmult Cfield (S N) (S N) 1 (AdjointMatrix (S N) (S N) V)
              (MVectorToMatrix Cfield (S N)
                 (fun (l : Count (S N)) =>
                  match excluded_middle_informative (proj1_sig l = 0%nat) with
                  | left _ => CI
                  | right _ => match excluded_middle_informative (l = m)
                   with | left _ => Cmake 0 eps
                   | right _ => CO
end
end)) = MVectorToMatrix Cfield (S N) (MVmult Cfield (S N) (S N) (AdjointMatrix (S N) (S N) V) (fun (l : Count (S N)) =>
                  match excluded_middle_informative (proj1_sig l = 0%nat) with
                  | left _ => CI
                  | right _ => match excluded_middle_informative (l = m)
                   with | left _ => Cmake 0 eps
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
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat
          (le_n_S 0 N (le_0_n N))))).
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
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat
          (le_n_S 0 N (le_0_n N))))).
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat
          (le_n_S 0 N (le_0_n N)))) (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat})
     (CountFinite (S N)))).
rewrite MySumF2Singleton.
rewrite MySumF2Singleton.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m)).
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) m) (FiniteIntersection (Count (S N))
        (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat})
           (CountFinite (S N)))
        (Complement (Count (S N))
           (proj1_sig
              (FiniteSingleton (Count (S N))
                 (exist (fun (n : nat) => (n < S N)%nat) O
                    (le_n_S 0 N (le_0_n N)))))))).
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
rewrite (Cmult_comm (Mmult Cfield (S N) (S N) (S N) V
                 (Mmult Cfield (S N) (S N) (S N) A
                    (AdjointMatrix (S N) (S N) V)) m
                 (exist (fun (n0 : nat) => (n0 < S N)%nat) 0%nat
                    (le_n_S 0 N (Nat.le_0_l N))))).
rewrite Cmult_1_l.
unfold Cplus.
unfold Rnplus.
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
rewrite (Rmult_comm (- Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V))
  (exist (fun (n0 : nat) => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N)))
  m CIm) eps).
rewrite (Rmult_comm (Mmult Cfield (S N) (S N) (S N) V
    (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)) m m
    CRe) eps).
rewrite - Rmult_assoc.
rewrite - Rplus_assoc.
rewrite - Rplus_assoc.
suff: (- Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V))
  (exist (fun n0 : nat => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N)))
  m CIm = Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V))
  m (exist (fun n0 : nat => (n0 < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N)))
  CIm).
move=> H19.
rewrite H19.
reflexivity.
suff: (Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V))
   = AdjointMatrix (S N) (S N) (Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V)))).
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
suff: (In (Count (S N))
        (Complement (Count (S N))
           (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H17.
move=> u1 H18 H19 H20.
unfold MVectorToMatrix.
unfold AdjointMatrix.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H21.
elim H18.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat
           (le_n_S 0 N (le_0_n N)))).
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
suff: (In (Count (S N))
        (Complement (Count (S N))
           (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H17.
move=> u1 H18 H19 H20.
unfold MVectorToMatrix.
unfold AdjointMatrix.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H21.
elim H18.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat
           (le_n_S 0 N (le_0_n N)))).
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
suff: (In (Count (S N))
        (Complement (Count (S N))
           (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H14.
move=> u1 H15 H16 H17.
unfold MVectorToMatrix.
unfold AdjointMatrix.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H18.
elim H15.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat
           (le_n_S 0 N (le_0_n N)))).
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
suff: (Mmult Cfield (S N) (S N) (S N) V
  (Mmult Cfield (S N) (S N) (S N) A (AdjointMatrix (S N) (S N) V))
  (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N)))
  (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N))) = Conjugate (CnInnerProduct (S N) v (MVmult Cfield (S N) (S N) A v))).
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
apply (MySumF2Same
 {n : nat | (n < S N)%nat}
  (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat})
     (CountFinite (S N))) (FPCM Cfield)
  (fun (n : Count (S N)) =>
   Fmul Cfield (A u0 n) (Conjugate (Conjugate (v n))))
(fun (n : Count (S N)) => Fmul Cfield (A u0 n) (v n))).
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
elim (Cnip_pos_re (S N) w).
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
suff: (MVmult Cfield (S N) (S N) A
        (Vmul Cfield (FnVS Cfield (S N))
           (Cmake
              (MySqrt
                 (exist (fun (r : R) => r >= 0)
                    (/ CnInnerProduct (S N) w w CRe) H8)) 0) w) = Vmul Cfield (FnVS Cfield (S N)) (Cmake
              (MySqrt
                 (exist (fun r : R => r >= 0)
                    (/ CnInnerProduct (S N) w w CRe) H8)) 0) (MVmult Cfield (S N) (S N) A w)).
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
apply (FiniteSetInduction {n : nat | (n < S N)%nat}
  (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat})
     (CountFinite (S N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
suff: (CMe (FPCM Cfield) = FO Cfield).
move=> H10.
rewrite {1} H10.
rewrite - (Fmul_O_r Cfield (Cmake
     (MySqrt
        (exist (fun (r : R) => r >= 0) (/ CnInnerProduct (S N) w w CRe) H8))
     0)).
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
elim (Cnip_pos_re (S N) w).
apply.
move=> H8.
elim (H7 H8).
apply H7.
move=> H7.
apply H6.
move=> m.
rewrite (proj1 (Cnip_refl (S N) w)).
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
apply (FiniteSetInduction {n : nat | (n < S N)%nat}
  (exist (Finite {n : nat | (n < S N)%nat})
     (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
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
suff: (AdjointMatrix (S N) (S N)
     (fun (m : Count (S N)) => match AddConnectInv 1 N m with
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
suff: ((AdjointMatrix (S N) (S N)
     (AdjointMatrix (S N) (S N)
        (fun (m : Count (S N)) =>
         match AddConnectInv 1 N m with
         | inl _ => (fun (m : Count (S N)) => Conjugate (v m))
         | inr n => W n
         end))) = (fun (m : Count (S N)) =>
         match AddConnectInv 1 N m with
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
suff: ((AdjointMatrix (S N) (S N)
     (AdjointMatrix (S N) (S N)
        (fun (m : Count (S N)) =>
         match AddConnectInv 1 N m with
         | inl _ => (fun (m : Count (S N)) => Conjugate (v m))
         | inr n => W n
         end))) = (fun (m : Count (S N)) =>
         match AddConnectInv 1 N m with
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
apply (FiniteSetInduction {n : nat | (n < S N)%nat}
  (exist (Finite {n : nat | (n < S N)%nat})
     (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
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
apply (MySumF2Same {n : nat | (n < S N)%nat}
  (exist (Finite {n : nat | (n < S N)%nat})
     (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))
  (FPCM Cfield) (fun (n : {n : nat | (n < S N)%nat}) =>
   Cmult (Conjugate (Conjugate (W m n))) (Conjugate (W m n))) (fun (n : {n : nat | (n < S N)%nat}) => Cmult (W m n) (Conjugate (W m n)))).
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
apply (MySumF2Same {n : nat | (n < S N)%nat}
  (exist (Finite {n : nat | (n < S N)%nat})
     (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))
  (FPCM Cfield)).
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
apply (FiniteSetInduction {n : nat | (n < S N)%nat}
  (exist (Finite {n : nat | (n < S N)%nat})
     (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
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
apply (MySumF2Same {n : nat | (n < S N)%nat}
  (exist (Finite {n : nat | (n < S N)%nat})
     (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))
  (FPCM Cfield)).
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
apply (FiniteSetInduction (Count N) (exist (Finite (Count N))
        (fun (t0 : Count N) => proj1_sig a t0 <> FO Cfield) 
        (proj2_sig a))).
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
apply (SubspaceBasisLinearlyIndependentVS Cfield (FnVS Cfield (S N))
       (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 
       (Count N) B H6).
suff: (DimensionSubspaceVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 H5 = N).
move=> H6.
suff: (exists (B : Count (DimensionSubspaceVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 H5) -> Cn (S N)),
  BasisSubspaceVS Cfield (FnVS Cfield (S N))
    (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 
    (Count (DimensionSubspaceVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 H5)) B).
rewrite H6.
apply.
apply (DimensionSubspaceVSNature Cfield (FnVS Cfield (S N))
       (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 H5).
suff: (SubspaceVS Cfield (FnVS Cfield (S N))
         (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m)))).
move=> H6.
elim (DimensionSumEnsembleVS2_exists Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H6 H4).
move=> H7 H8.
suff: (FiniteDimensionVS Cfield
              (SubspaceMakeVS Cfield (FnVS Cfield (S N))
                 (SumEnsembleVS Cfield (FnVS Cfield (S N))
                    (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m)))
                    (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) H7)).
move=> H9.
elim (H8 H9).
move=> H10.
elim.
move=> H11 H12.
apply (plus_reg_l (DimensionSubspaceVS Cfield (FnVS Cfield (S N))
  (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H4 H5) N 1).
suff: ((1 + N)%nat = DimensionSubspaceVS Cfield (FnVS Cfield (S N))
        (SumEnsembleVS Cfield (FnVS Cfield (S N))
           (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m)))
           (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) H7 H9).
move=> H13.
rewrite H13.
suff: (1%nat = DimensionSubspaceVS Cfield (FnVS Cfield (S N))
         (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) H6 H10).
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
suff: ((Cip (FnVS Cfield (S N)) (CnInner_Product_Space (S N))
     (fun (m : Count (S N)) => Conjugate (v m))
     (fun (m : Count (S N)) => Conjugate (v m))) = CI).
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
apply (MySumF2Same (Count (S N))
  (exist (Finite (Count (S N))) (Full_set (Count (S N)))
     (CountFinite (S N))) (FPCM Cfield)).
move=> u1 H19.
rewrite ConjugateInvolutive.
apply Cmult_comm.
reflexivity.
apply H16.
move=> u.
elim.
apply (proj2 (proj2 (IntersectionSubspaceVS Cfield (FnVS Cfield (S N)) (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m)))
     (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO) H6 H4))).
rewrite (DimensionSubspaceVSNature2 Cfield (FnVS Cfield (S N))
  (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) H6 H10 1 (fun (m : Count 1) => (fun (m : Count (S N)) => Conjugate (v m)))).
reflexivity.
suff: (exists (f : C), (fun (m : Count (S N)) => Conjugate (v m)) = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))).
move=> H14.
exists (fun (m : Count 1) => H14).
apply (proj2 (BasisLIGeVS Cfield
  (SubspaceMakeVS Cfield (FnVS Cfield (S N))
     (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) H6) 
  (Count 1)
  (fun (m : Count 1) =>
   exist (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) (fun (m : Count (S N)) => Conjugate (v m)) H14))).
apply conj.
apply FiniteLinearlyIndependentVS.
move=> a H15 m.
suff: (MySumF2 (Count 1)
        (exist (Finite (Count 1)) (Full_set (Count 1)) (CountFinite 1))
        (VSPCM Cfield
           (SubspaceMakeVS Cfield (FnVS Cfield (S N))
              (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) H6))
        (fun (n : Count 1) =>
         Vmul Cfield
           (SubspaceMakeVS Cfield (FnVS Cfield (S N))
              (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) H6)
           (a n)
           (exist (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m)))
              (fun (m : Count (S N)) => Conjugate (v m)) H14)) =
      VO Cfield
        (SubspaceMakeVS Cfield (FnVS Cfield (S N))
           (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m))) H6)).
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
apply (Cnip_refl (S N)).
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
suff: (Fnmul Cfield (S N) (a m) (fun (m0 : Count (S N)) => Conjugate (v m0)) = proj1_sig (Vmul Cfield
        (SubspaceMakeVS Cfield (FnVS Cfield (S N))
           (fun w : Cn (S N) =>
            exists f : C,
              w =
              Fnmul Cfield (S N) f (fun m : Count (S N) => Conjugate (v m)))
           H6) (a m)
        (exist
           (fun w : Cn (S N) =>
            exists f : C,
              w =
              Fnmul Cfield (S N) f (fun m : Count (S N) => Conjugate (v m)))
           (fun m : Count (S N) => Conjugate (v m)) H14))).
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
suff: (forall (z : Cn (S N)), In (Cn (S N)) (SumEnsembleVS Cfield (FnVS Cfield (S N))
        (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m)))
        (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) z).
move=> H16.
rewrite (DimensionVSNature2 Cfield
  (SubspaceMakeVS Cfield (FnVS Cfield (S N))
     (SumEnsembleVS Cfield (FnVS Cfield (S N))
        (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m)))
        (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) H7) H9 (S N) (fun (m : Count (S N)) => exist (SumEnsembleVS Cfield (FnVS Cfield (S N))
        (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m)))
        (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) (a m) (H16 (a m)))).
reflexivity.
apply (IsomorphicSaveBasisVS Cfield (FnVS Cfield (S N)) (SubspaceMakeVS Cfield (FnVS Cfield (S N))
     (SumEnsembleVS Cfield (FnVS Cfield (S N))
        (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m)))
        (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) H7) (Count (S N)) a (fun (z : Cn (S N)) =>
   exist
     (SumEnsembleVS Cfield (FnVS Cfield (S N))
        (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m)))
        (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) 
     z (H16 z))).
apply conj.
exists (fun (m : (SubspaceMakeVST Cfield (FnVS Cfield (S N))
     (SumEnsembleVS Cfield (FnVS Cfield (S N))
        (fun (w : Cn (S N)) => exists (f : C), w = Fnmul Cfield (S N) f (fun (m : Count (S N)) => Conjugate (v m)))
        (fun (w : Cn (S N)) => CnInnerProduct (S N) (fun (m : Count (S N)) => Conjugate (v m)) w = CO)) H7)) => proj1_sig m).
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
suff: ((Cip (FnVS Cfield (S N)) (CnInner_Product_Space (S N))
           (fun (m : Count (S N)) => Conjugate (v m))
           (fun (m : Count (S N)) => Conjugate (v m))) = CI).
move=> H21.
rewrite H21.
rewrite Cmult_comm.
rewrite Cmult_1_l.
rewrite ConjugateInvolutive.
apply Cplus_opp_r.
rewrite - (proj1 H3).
simpl.
unfold CnInnerProduct.
apply (MySumF2Same (Count (S N))
  (exist (Finite (Count (S N))) (Full_set (Count (S N)))
     (CountFinite (S N))) (FPCM Cfield)).
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
elim (CountMult (S N) 2).
move=> F.
elim.
move=> G H3.
elim (Theorem_7_3_2_1 (Rn_met (S N * 2)) (fun (x : Rn (S N * 2)) => Aform (fun (m : Count (S N)) => Cmake (x (F (m, CRe))) (x (F (m, CIm))))) (fun (x : Rn (S N * 2)) => RnInnerProduct (S N * 2) x x = 1)).
move=> z H4.
suff: (forall (y : R),
       In R
         (Im (Base (Rn_met (S N * 2))) R
            (fun (x : Rn (S N * 2)) => RnInnerProduct (S N * 2) x x = 1)
          (fun (x : Rn (S N * 2)) =>
           Aform
             (fun m : Count (S N) =>
              Cmake (x (F (m, CRe))) (x (F (m, CIm)))))) y ->
       y <= z).
elim (proj1 H4).
move=> x H5 y H6 H7.
exists (fun (m : Count (S N)) =>
              Cmake (x (F (m, CRe))) (x (F (m, CIm)))).
suff: (forall (v : Count (S N) -> C), CnInnerProduct (S N) v v = CI <-> RnInnerProduct (S N * 2) (fun (m : Count (S N * 2)) => v (fst (G m)) (snd (G m))) (fun (m : Count (S N * 2)) => v (fst (G m)) (snd (G m))) = 1).
move=> H8.
apply conj.
apply H8.
suff: ((fun (m : Count (S N * 2)) =>
   Cmake (x (F (fst (G m), CRe))) (x (F (fst (G m), CIm))) (snd (G m))) = x).
move=> H9.
rewrite H9.
apply H5.
apply functional_extensionality.
move=> m.
elim (CReorCIm (snd (G m))).
move=> H9.
rewrite H9.
rewrite CmakeRe.
suff: ((fst (G m), CRe) = G m).
move=> H10.
rewrite H10.
rewrite (proj2 H3 m).
reflexivity.
apply injective_projections.
reflexivity.
rewrite H9.
reflexivity.
move=> H9.
rewrite H9.
rewrite CmakeIm.
suff: ((fst (G m), CIm) = G m).
move=> H10.
rewrite H10.
rewrite (proj2 H3 m).
reflexivity.
apply injective_projections.
reflexivity.
rewrite H9.
reflexivity.
move=> w H9.
rewrite - H6.
apply H7.
apply (Im_intro (Base (Rn_met (S N * 2))) R
     (fun (x0 : Rn (S N * 2)) => RnInnerProduct (S N * 2) x0 x0 = 1)
     (fun (x0 : Rn (S N * 2)) =>
      Aform
        (fun m : Count (S N) => Cmake (x0 (F (m, CRe))) (x0 (F (m, CIm))))) (fun (m : Count (S N * 2)) => w (fst (G m)) (snd (G m)))).
apply H8.
apply H9.
suff: ((fun (m : Count (S N)) =>
   Cmake (w (fst (G (F (m, CRe)))) (snd (G (F (m, CRe)))))
     (w (fst (G (F (m, CIm)))) (snd (G (F (m, CIm)))))) = w).
move=> H10.
rewrite H10.
reflexivity.
apply functional_extensionality.
move=> m.
apply functional_extensionality.
move=> n.
elim (CReorCIm n).
move=> H10.
rewrite H10.
rewrite CmakeRe.
rewrite (proj1 H3).
reflexivity.
move=> H10.
rewrite H10.
rewrite CmakeIm.
rewrite (proj1 H3).
reflexivity.
suff: (forall (v : Count (S N) -> C), CnInnerProduct (S N) v v CRe = RnInnerProduct (S N * 2)
  (fun (m : Count (S N * 2)) => v (fst (G m)) (snd (G m)))
  (fun (m : Count (S N * 2)) => v (fst (G m)) (snd (G m)))).
move=> H8 v.
apply conj.
move=> H9.
rewrite - (H8 v).
rewrite H9.
apply CmakeRe.
move=> H9.
apply functional_extensionality.
move=> n.
elim (CReorCIm n).
move=> H10.
rewrite H10.
rewrite (H8 v).
unfold CI.
rewrite CmakeRe.
apply H9.
move=> H10.
rewrite H10.
unfold CI.
rewrite CmakeIm.
apply (Cip_pos_im (FnVS Cfield (S N)) (CnInner_Product_Space (S N))).
move=> v.
rewrite RnInnerProductDefinition.
suff: ((exist (Finite (Count (S N * 2))) (Full_set (Count (S N * 2)))
     (CountFinite (S N * 2))) = (FiniteIm (Count (S N) * Count 2) (Count (S N * 2)) F
            (FinitePair (Count (S N)) (Count 2)
               (exist (Finite (Count (S N))) (Full_set (Count (S N)))
                  (CountFinite (S N)))
               (exist (Finite (Count 2)) (Full_set (Count 2))
                  (CountFinite 2))))).
move=> H8.
rewrite H8.
rewrite - (MySumF2BijectiveSame2 (Count (S N) * Count 2) (Count (S N * 2)) (FinitePair (Count (S N)) (Count 2) (exist (Finite (Count (S N))) (Full_set (Count (S N)))
     (CountFinite (S N))) (exist (Finite (Count 2)) (Full_set (Count 2))
     (CountFinite 2))) F).
unfold Basics.compose.
suff: ((fun (x0 : Count (S N) * Count 2) =>
   v (fst (G (F x0))) (snd (G (F x0))) *
   v (fst (G (F x0))) (snd (G (F x0)))) = (fun (x0 : Count (S N) * Count 2) =>
   v (fst x0) (snd x0) *
   v (fst x0) (snd x0))).
move=> H9.
rewrite H9.
rewrite (MySumF2Pair (Count (S N)) (Count 2) (exist (Finite (Count (S N))) (Full_set (Count (S N)))
        (CountFinite (S N))) (exist (Finite (Count 2)) (Full_set (Count 2))
        (CountFinite 2)) RPCM (fun (x : Count (S N)) (y : Count 2) => v x y * v x y)).
unfold CnInnerProduct.
apply (FiniteSetInduction (Count (S N))
  (exist (Finite (Count (S N))) (Full_set (Count (S N)))
     (CountFinite (S N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H10 H11 H12 H13.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
unfold Cplus.
unfold Rnplus.
rewrite H13.
apply Rplus_eq_compat_l.
rewrite (MySumF2Included (Count 2) (FiniteSingleton (Count 2) CRe)).
rewrite MySumF2Singleton.
rewrite (MySumF2Included (Count 2) (FiniteSingleton (Count 2) CIm)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
unfold Cmult.
unfold Conjugate.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
simpl.
rewrite Rplus_0_r.
unfold Rminus.
rewrite (Ropp_mult_distr_r (v b CIm) (- v b CIm)).
rewrite (Ropp_involutive (v b CIm)).
reflexivity.
move=> u.
elim.
move=> u0 H14 H15.
suff: (In (Count 2)
        (Complement (Count 2) (proj1_sig (FiniteSingleton (Count 2) CIm)))
        u0).
elim H15.
move=> u1 H16 H17 H18.
elim (CReorCIm u1).
move=> H19.
elim H16.
rewrite H19.
apply In_singleton.
move=> H19.
elim H18.
rewrite H19.
apply In_singleton.
apply H14.
move=> u.
elim.
apply Intersection_intro.
move=> H14.
elim (lt_irrefl O).
unfold lt.
suff: (S O = proj1_sig CIm).
move=> H15.
rewrite H15.
elim H14.
apply (le_n O).
reflexivity.
apply Full_intro.
move=> u H14.
apply Full_intro.
apply H12.
apply H12.
apply functional_extensionality.
move=> u.
rewrite (proj1 H3).
reflexivity.
move=> u1 u2 H9 H10 H11.
rewrite - (proj1 H3 u1).
rewrite - (proj1 H3 u2).
rewrite H11.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> u H8.
apply (Im_intro (Count (S N) * Count 2) (Count (S N * 2)) (proj1_sig (FinitePair (Count (S N)) (Count 2)
           (exist (Finite (Count (S N))) (Full_set (Count (S N)))
              (CountFinite (S N)))
           (exist (Finite (Count 2)) (Full_set (Count 2)) (CountFinite 2)))) F (G u)).
apply conj.
apply Full_intro.
apply Full_intro.
rewrite (proj2 H3 u).
reflexivity.
move=> u H8.
apply Full_intro.
apply H4.
suff: (O < S N * 2)%nat.
move=> H4.
apply (Inhabited_intro (Base (Rn_met (S N * 2)))
  (fun (x : Rn (S N * 2)) => RnInnerProduct (S N * 2) x x = 1) (fun (m : Count (S N * 2)) => match excluded_middle_informative (m = exist (fun (k : nat) => (k < S N * 2)%nat) O H4) with
  | left _ => 1
  | right _ => 0
end)).
unfold In.
rewrite RnInnerProductDefinition.
rewrite (MySumF2Included (Count (S N * 2)) (FiniteSingleton (Count (S N * 2)) (exist (fun (k : nat) => (k < S N * 2)%nat) O H4))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
elim (excluded_middle_informative
       (@eq (Count (S N * 2)) (exist (fun (k : nat) => (k < S N * 2)%nat) O
          H4)
        (exist (fun (k : nat) => (k < S N * 2)%nat) O
          H4))).
move=> H5.
rewrite (Rmult_1_r 1).
apply (CM_O_r RPCM 1).
elim.
reflexivity.
move=> u.
elim.
move=> u0 H5 H6.
elim (excluded_middle_informative
       (@eq (Count (S N * 2)) u0
        (exist (fun (k : nat) => (k < S N * 2)%nat) O
          H4))).
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
apply (FiniteSetInduction (Count (S N))
     (exist (Finite (Count (S N))) (Full_set (Count (S N)))
        (CountFinite (S N)))).
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
suff: ((fun (x0 : Rn (S N * 2)) =>
   MySumF2 (Count (S N)) (FiniteAdd (Count (S N)) B b) 
     (FPCM Cfield)
     (fun n : Count (S N) =>
      Cmult (Cmake (x0 (F (n, CRe))) (x0 (F (n, CIm))))
        (Conjugate
           (MVmult Cfield (S N) (S N) A
              (fun m : Count (S N) =>
               Cmake (x0 (F (m, CRe))) (x0 (F (m, CIm)))) n))) CRe) =
(fun (x0 : Rn (S N * 2)) =>
   (MySumF2 (Count (S N)) B 
     (FPCM Cfield)
     (fun n : Count (S N) =>
      Cmult (Cmake (x0 (F (n, CRe))) (x0 (F (n, CIm))))
        (Conjugate
           (MVmult Cfield (S N) (S N) A
              (fun m : Count (S N) =>
               Cmake (x0 (F (m, CRe))) (x0 (F (m, CIm)))) n))) CRe) + (Cmult (Cmake (x0 (F (b, CRe))) (x0 (F (b, CIm))))
        (Conjugate
           (MVmult Cfield (S N) (S N) A
              (fun m : Count (S N) =>
               Cmake (x0 (F (m, CRe))) (x0 (F (m, CIm)))) b)) CRe))).
move=> H10.
rewrite H10.
apply Theorem_6_6_3_1_R.
apply H9.
apply (Theorem_6_8_2 (Rn_met (S N * 2)) 2 (fun r : Base (Rn_met (S N * 2)) =>
   Cmult (Cmake (r (F (b, CRe))) (r (F (b, CIm))))
     (Conjugate
        (MVmult Cfield (S N) (S N) A
           (fun m : Count (S N) => Cmake (r (F (m, CRe))) (r (F (m, CIm))))
           b))) (Full_set (Base (Rn_met (S N * 2)))) x).
apply Theorem_6_6_3_5_C.
apply Theorem_6_8_2.
move=> n.
elim (CReorCIm n).
move=> H11.
rewrite H11.
suff: ((fun r : Base (Rn_met (S N * 2)) =>
   Cmake (r (F (b, CRe))) (r (F (b, CIm))) CRe) = (fun r : Base (Rn_met (S N * 2)) =>
  (r (F (b, CRe))))).
move=> H12.
rewrite H12.
apply H4.
apply functional_extensionality.
move=> r.
apply CmakeRe.
move=> H11.
rewrite H11.
suff: ((fun r : Base (Rn_met (S N * 2)) =>
   Cmake (r (F (b, CRe))) (r (F (b, CIm))) CIm) = (fun r : Base (Rn_met (S N * 2)) =>
  (r (F (b, CIm))))).
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
apply (FiniteSetInduction {n : nat | (n < S N)%nat}
     (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat})
        (CountFinite (S N)))).
apply conj.
move=> eps H11.
exists 1.
apply conj.
apply Rlt_0_1.
move=> y H12.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (proj2 (dist_refl (Rn_met 2) (Conjugate (CMe (FPCM Cfield)))
  (Conjugate (CMe (FPCM Cfield))))).
apply H11.
reflexivity.
move=> D d H11 H12 H13 H14  .
suff: ((fun r : Base (Rn_met (S N * 2)) =>
   Conjugate
     (MySumF2 {n : nat | (n < S N)%nat}
        (FiniteAdd {n : nat | (n < S N)%nat} D d) 
        (FPCM Cfield)
        (fun n : Count (S N) =>
         Fmul Cfield (A b n) (Cmake (r (F (n, CRe))) (r (F (n, CIm))))))) = (fun r : Base (Rn_met (S N * 2)) =>
   Cplus (Conjugate
     (MySumF2 {n : nat | (n < S N)%nat}
        D 
        (FPCM Cfield)
        (fun n : Count (S N) =>
         Fmul Cfield (A b n) (Cmake (r (F (n, CRe))) (r (F (n, CIm))))))) (Conjugate (Fmul Cfield (A b d) (Cmake (r (F (d, CRe))) (r (F (d, CIm)))))))).
move=> H15.
rewrite H15.
apply Theorem_6_6_3_1_Rn.
apply H14.
suff: (ContinuousMet (Rn_met (S N * 2)) (Rn_met 2)
  (fun r : Base (Rn_met (S N * 2)) =>
   Fmul Cfield (A b d) (Cmake (r (F (d, CRe))) (r (F (d, CIm)))))
  (Full_set (Base (Rn_met (S N * 2)))) x).
move=> H16.
apply Theorem_6_8_2.
move=> n.
elim (CReorCIm n).
move=> H17.
rewrite H17.
suff: ((fun r : Base (Rn_met (S N * 2)) =>
   Conjugate
     (Fmul Cfield (A b d) (Cmake (r (F (d, CRe))) (r (F (d, CIm))))) CRe) = (fun r : Base (Rn_met (S N * 2)) =>
  Fmul Cfield (A b d) (Cmake (r (F (d, CRe))) (r (F (d, CIm)))) CRe)).
move=> H18.
rewrite H18.
apply (Theorem_6_8_2 (Rn_met (S N * 2)) 2 (fun r : Base (Rn_met (S N * 2)) =>
         Fmul Cfield (A b d) (Cmake (r (F (d, CRe))) (r (F (d, CIm)))))).
apply H16.
apply functional_extensionality.
move=> r.
apply CmakeRe.
move=> H17.
rewrite H17.
suff: ((fun r : Base (Rn_met (S N * 2)) =>
   Conjugate
     (Fmul Cfield (A b d) (Cmake (r (F (d, CRe))) (r (F (d, CIm))))) CIm) = (fun r : Base (Rn_met (S N * 2)) =>
  - Fmul Cfield (A b d) (Cmake (r (F (d, CRe))) (r (F (d, CIm)))) CIm)).
move=> H18.
rewrite H18.
apply Theorem_6_6_3_4_R.
apply (Theorem_6_8_2 (Rn_met (S N * 2)) 2 (fun r : Base (Rn_met (S N * 2)) =>
         Fmul Cfield (A b d) (Cmake (r (F (d, CRe))) (r (F (d, CIm)))))).
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
suff: ((fun r : Base (Rn_met (S N * 2)) =>
   Cmake (r (F (d, CRe))) (r (F (d, CIm))) CRe) = (fun r : Base (Rn_met (S N * 2)) =>
   (r (F (d, CRe))))).
move=> H17.
rewrite H17.
apply H4.
apply functional_extensionality.
move=> r.
apply CmakeRe.
move=> H16.
rewrite H16.
suff: ((fun r : Base (Rn_met (S N * 2)) =>
   Cmake (r (F (d, CRe))) (r (F (d, CIm))) CIm) = (fun r : Base (Rn_met (S N * 2)) =>
   (r (F (d, CIm))))).
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
rewrite RnInnerProductDefinition.
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



