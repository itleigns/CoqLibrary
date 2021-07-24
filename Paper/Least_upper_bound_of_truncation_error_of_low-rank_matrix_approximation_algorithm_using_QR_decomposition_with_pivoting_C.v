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
Require Import MyAlgebraicStructure.MyVectorSpace.
Require Import MyAlgebraicStructure.MyField.
Require Import Analysis.KaisekiNyuumonn.KaisekiNyuumonn1.
Require Import LinearAlgebra.Matrix.
Require Import LinearAlgebra.SenkeiDaisuunoSekai.SenkeiDaisuunoSekai1.
Require Import Tools.MySum.
Local Open Scope R_scope.

Record CInner_Product_Space (V : VectorSpace Cfield) : Type := {
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