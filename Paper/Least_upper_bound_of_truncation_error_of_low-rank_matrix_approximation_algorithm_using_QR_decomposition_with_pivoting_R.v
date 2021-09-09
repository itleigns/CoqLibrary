Add LoadPath "Analysis/KaisekiNyuumonn" as Analysis.KaisekiNyuumonn.
Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "BasicProperty" as BasicProperty.
Add LoadPath "BasicNotation" as BasicNotation.
Add LoadPath "Tools" as Tools.
Add LoadPath "LibraryExtension" as LibraryExtension.
Add LoadPath "LinearAlgebra/SenkeiDaisuunoSekai" as LinearAlgebra.SenkeiDaisuunoSekai.
Add LoadPath "LinearAlgebra" as LinearAlgebra.


From mathcomp Require Import ssreflect.
Require Import Reals.
Require Import Classical.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Image.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import MyAlgebraicStructure.MyVectorSpace.
Require Import MyAlgebraicStructure.MyField.
Require Import Analysis.KaisekiNyuumonn.KaisekiNyuumonn1.
Require Import LinearAlgebra.SenkeiDaisuunoSekai.SenkeiDaisuunoSekai1.
Require Import LinearAlgebra.Matrix.
Require Import Tools.MySum.
Require Import BasicProperty.MappingProperty.
Local Open Scope R_scope.

Record RInner_Product_Space (V : VectorSpace Rfield) : Type := mkRInner_Product_Space {
  Rip : VT Rfield V -> VT Rfield V -> R;
  Rip_sym : forall (x y : VT Rfield V), Rip x y = Rip y x;
  Rip_linear_mult_l : forall (c : R) (x y : VT Rfield V), Rip (Vmul Rfield V c x) y = c * (Rip x y);
  Rip_linear_plus_l : forall (x1 x2 y : VT Rfield V), Rip (Vadd Rfield V x1 x2) y = (Rip x1 y) + (Rip x2 y);
  Rip_pos : forall (x : VT Rfield V), Rip x x >= 0;
  Rip_refl : forall (x : VT Rfield V), Rip x x = 0 <-> x = VO Rfield V
}.

Lemma Rip_linear_mult_r : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (c : R) (x y : VT Rfield V), Rip V I x (Vmul Rfield V c y) = c * (Rip V I x y).
Proof.
move=> V I c x y.
rewrite (Rip_sym V I x (Vmul Rfield V c y)).
rewrite (Rip_linear_mult_l V I c y x).
rewrite (Rip_sym V I x y).
reflexivity.
Qed.

Lemma Rip_linear_plus_r : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (x y1 y2 : VT Rfield V), Rip V I x (Vadd Rfield V y1 y2) = (Rip V I x y1) + (Rip V I x y2).
Proof.
move=> V I x y1 y2.
rewrite (Rip_sym V I x (Vadd Rfield V y1 y2)).
rewrite (Rip_sym V I x y1).
rewrite (Rip_sym V I x y2).
apply (Rip_linear_plus_l V I y1 y2 x).
Qed.

Lemma Rip_mult_0_l : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (x : VT Rfield V), Rip V I (VO Rfield V) x = 0.
Proof.
move=> V I x.
suff: (VO Rfield V = Vmul Rfield V 0 (VO Rfield V)).
move=> H1.
rewrite H1.
rewrite (Rip_linear_mult_l V I 0).
apply Rmult_0_l.
rewrite (Vmul_O_r Rfield V 0).
reflexivity.
Qed.

Lemma Rip_mult_0_r : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (x : VT Rfield V), Rip V I x (VO Rfield V) = 0.
Proof.
move=> V I x.
rewrite (Rip_sym V I x (VO Rfield V)).
apply (Rip_mult_0_l V I x).
Qed.

Lemma Rip_linear_opp_l : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (x y : VT Rfield V), Rip V I (Vopp Rfield V x) y = - (Rip V I x y).
Proof.
move=> V I x y.
apply (Rplus_opp_r_uniq (Rip V I x y) (Rip V I (Vopp Rfield V x) y)).
rewrite - (Rip_linear_plus_l V I x (Vopp Rfield V x) y).
rewrite (Vadd_opp_r Rfield V x).
apply (Rip_mult_0_l V I y).
Qed.

Lemma Rip_linear_opp_r : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (x y : VT Rfield V), Rip V I x (Vopp Rfield V y) = - (Rip V I x y).
Proof.
move=> V I x y.
rewrite (Rip_sym V I x (Vopp Rfield V y)).
rewrite (Rip_linear_opp_l V I y x).
rewrite (Rip_sym V I x y).
reflexivity.
Qed.

Definition OrthonormalSystemR (V : VectorSpace Rfield) (I : RInner_Product_Space V) (T : Type) (W : T -> VT Rfield V) := (forall (t : T), Rip V I (W t) (W t) = 1) /\ (forall (t1 t2 : T), t1 <> t2 -> Rip V I (W t1) (W t2) = 0).

Lemma OrthonormalSystemLinearlyIndependentR : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (T : Type) (W : T -> VT Rfield V), OrthonormalSystemR V I T W -> LinearlyIndependentVS Rfield V T W.
Proof.
move=> V I T W H1.
apply (proj2 (LinearlyIndependentVSDef3 Rfield V T W)).
move=> a A H2 t H3.
suff: (a t = Rip V I (MySumF2 T A (VSPCM Rfield V)
       (fun (t : T) => Vmul Rfield V (a t) (W t))) (W t)).
move=> H4.
rewrite H4.
rewrite H2.
apply (Rip_mult_0_l V I (W t)).
suff: (Rip V I
  (MySumF2 T
      A (VSPCM Rfield V)
     (fun (t0 : T) => Vmul Rfield V (a t0) (W t0)))
  (W t) = MySumF2 T
     A RPCM
     (fun (t0 : T) => (a t0) * (Rip V I (W t0) (W t)))).
move=> H4.
rewrite H4.
rewrite (MySumF2Included T (FiniteSingleton T t)).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (proj1 H1 t).
rewrite (Rmult_1_r (a t)).
rewrite (CM_O_r RPCM (a t)).
reflexivity.
move=> u.
elim.
move=> u0 H5 H6.
rewrite (proj2 H1 u0 t).
apply (Rmult_0_r (a u0)).
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
apply (Rip_mult_0_l V I (W t)).
move=> B b H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Rip_linear_plus_l V I).
rewrite H7.
rewrite (Rip_linear_mult_l V I).
reflexivity.
apply H6.
apply H6.
Qed.

Lemma GramSchmidtLinearlyIndepententR_sub : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (N : nat) (W : Count N -> VT Rfield V), LinearlyIndependentVS Rfield V (Count N) W -> {Z : Count N -> VT Rfield V | OrthonormalSystemR V I (Count N) Z /\ forall (m : Count N), In (VT Rfield V) (SpanVS Rfield V {k : Count N | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))) (Z m)}.
Proof.
suff: (forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (N : nat) (W : Count N -> VT Rfield V), LinearlyIndependentVS Rfield V (Count N) W -> {Z : Count N -> VT Rfield V | LinearlyIndependentVS Rfield V (Count N) Z /\ (forall (t1 t2 : Count N), t1 <> t2 -> Rip V I (Z t1) (Z t2) = 0) /\ forall (m : Count N), In (VT Rfield V) (SpanVS Rfield V {k : Count N | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))) (Z m)}).
move=> H1 V I N W H2.
elim (H1 V I N W H2).
move=> Z H3.
exists (fun (m : Count N) => Vmul Rfield V (/ MySqrt (exist (fun (r : R) => r >= 0) (Rip V I (Z m) (Z m)) (Rip_pos V I (Z m)))) (Z m)).
apply conj.
apply conj.
move=> t.
rewrite (Rip_linear_mult_l V I).
rewrite (Rip_linear_mult_r V I).
rewrite - Rmult_assoc.
suff: (Rip V I (Z t) (Z t) <> 0).
move=> H4.
suff: (MySqrt
  (exist (fun (r : R) => r >= 0) (Rip V I (Z t) (Z t)) (Rip_pos V I (Z t))) <> 0).
move=> H5.
rewrite - (Rinv_mult_distr (MySqrt
  (exist (fun (r : R) => r >= 0) (Rip V I (Z t) (Z t)) (Rip_pos V I (Z t)))) (MySqrt
  (exist (fun (r : R) => r >= 0) (Rip V I (Z t) (Z t)) (Rip_pos V I (Z t)))) H5 H5).
rewrite - (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (Rip V I (Z t) (Z t)) (Rip_pos V I (Z t))))).
apply (Rinv_l (Rip V I (Z t) (Z t)) H4).
move=> H5.
apply H4.
suff: (Rip V I (Z t) (Z t) = proj1_sig
       (exist (fun (r : R) => r >= 0) (Rip V I (Z t) (Z t)) (Rip_pos V I (Z t)))).
move=> H6.
rewrite H6.
rewrite (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (Rip V I (Z t) (Z t)) (Rip_pos V I (Z t))))).
rewrite H5.
apply (Rmult_0_r 0).
reflexivity.
move=> H4.
apply (LinearlyIndependentNotContainVOVS Rfield V (Count N) Z (proj1 H3) t).
apply (proj1 (Rip_refl V I (Z t)) H4).
move=> t1 t2 H4.
rewrite (Rip_linear_mult_l V I).
rewrite (Rip_linear_mult_r V I).
rewrite (proj1 (proj2 H3) t1 t2 H4).
rewrite Rmult_0_r.
apply Rmult_0_r.
move=> m.
apply (proj1 (proj2 (SpanSubspaceVS Rfield V
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
  | right _ => Vadd Rfield V (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) (Vopp Rfield V (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (VSPCM Rfield V) (fun (m : Count N) => Vmul Rfield V (Rip V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) / Rip V I (W0 m) (W0 m)) (W0 m))))
end).
apply conj.
apply (Proposition_5_2 Rfield V N H3 H4).
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
       Vadd Rfield V
         (W (exist (fun (k : nat) => (k < S N)%nat) N H4))
         (Vopp Rfield V
            (MySumF2 (Count N)
               (exist (Finite (Count N)) (Full_set (Count N))
                  (CountFinite N)) (VSPCM Rfield V) (fun (m : Count N) => Vmul Rfield V (Rip V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) / Rip V I (W0 m) (W0 m)) (W0 m))))
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
apply (proj2 (proj1 (Proposition_5_2 Rfield V N H3 H4 W) H2)).
suff: (In (VT Rfield V)
       (SpanVS Rfield V (Count N)
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
               Vadd Rfield V
                 (W (exist (fun (k : nat) => (k < S N)%nat) N H4))
                 (Vopp Rfield V
                    (MySumF2 (Count N)
                       (exist (Finite (Count N)) 
                          (Full_set (Count N)) (CountFinite N))
                       (VSPCM Rfield V)
                       (fun (m0 : Count N) =>
                        Vmul Rfield V
                          (Rip V I (W0 m0)
                             (W
                                (exist (fun k : nat => (k < S N)%nat) N
                                   H4)) / Rip V I (W0 m0) (W0 m0)) 
                          (W0 m0))))
           end))
          (W (exist (fun (k : nat) => (k < S N)%nat) N H4))
          ).
elim.
move=> x H8.
rewrite H8.
apply (FiniteSetInduction (Count N)
     (exist (Finite (Count N))
        (fun (t : Count N) => proj1_sig x t <> FO Rfield) 
        (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS Rfield V (Count N)
     (fun (m : Count N) =>
      W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m)))))).
move=> B b H9 H10 H11 H12.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS Rfield V (Count N)
     (fun (m : Count N) =>
      W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))))).
apply H12.
apply (proj1 (proj2 (SpanSubspaceVS Rfield V (Count N)
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
         proj1_sig y t <> FO Rfield) (proj2_sig y))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS Rfield V (Count N)
     (fun (m : Count N) =>
      W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m)))))).
move=> C c H16 H17 H18 H19.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS Rfield V (Count N)
     (fun (m : Count N) =>
      W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))))).
apply H19.
apply (proj1 (proj2 (SpanSubspaceVS Rfield V (Count N)
     (fun (m : Count N) =>
      W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m)))))).
apply (SpanContainSelfVS Rfield V (Count N)
     (fun (m : Count N) =>
      W (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig m) (H3 m))) (proj1_sig c)).
apply H18.
apply sig_map.
reflexivity.
move=> H13.
elim (H13 (proj2_sig b)).
apply H11.
rewrite - {3} (Vadd_O_r Rfield V (W (exist (fun (k : nat) => (k < S N)%nat) N H4))).
rewrite - (Vadd_opp_l Rfield V (MySumF2 (Count N)
                (exist (Finite (Count N)) (Full_set (Count N))
                   (CountFinite N)) (VSPCM Rfield V)
                (fun (m : Count N) =>
                 Vmul Rfield V
                   (Rip V I (W0 m)
                      (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) /
                    Rip V I (W0 m) (W0 m)) (W0 m)))).
rewrite - (Vadd_assoc Rfield V (W (exist (fun k : nat => (k < S N)%nat) N H4)) (Vopp Rfield V (MySumF2 (Count N)
                (exist (Finite (Count N)) (Full_set (Count N))
                   (CountFinite N)) (VSPCM Rfield V)
                (fun (m : Count N) =>
                 Vmul Rfield V
                   (Rip V I (W0 m)
                      (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) /
                    Rip V I (W0 m) (W0 m)) (W0 m)))) (MySumF2 (Count N)
                (exist (Finite (Count N)) (Full_set (Count N))
                   (CountFinite N)) (VSPCM Rfield V)
                (fun (m : Count N) =>
                 Vmul Rfield V
                   (Rip V I (W0 m)
                      (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) /
                    Rip V I (W0 m) (W0 m)) (W0 m)))).
apply (SpanSubspaceVS Rfield V).
apply H7.
apply (FiniteSetInduction (Count N)
     (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun (P : {X : Ensemble (Count N) | Finite (Count N) X}) => In (VT Rfield V)
  (SpanVS Rfield V (Count N)
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
          Vadd Rfield V
            (W (exist (fun (k : nat) => (k < S N)%nat) N H4))
            (Vopp Rfield V
               (MySumF2 (Count N)
                  (exist (Finite (Count N)) (Full_set (Count N))
                     (CountFinite N)) (VSPCM Rfield V)
                  (fun (m0 : Count N) =>
                   Vmul Rfield V
                     (Rip V I (W0 m0)
                        (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) /
                      Rip V I (W0 m0) (W0 m0)) (W0 m0))))
      end))
  (MySumF2 (Count N)
     P
     (VSPCM Rfield V)
     (fun m : Count N =>
      Vmul Rfield V
        (Rip V I (W0 m) (W (exist (fun k : nat => (k < S N)%nat) N H4)) /
         Rip V I (W0 m) (W0 m)) (W0 m))))).
apply conj.
rewrite MySumF2Empty.
apply (SpanSubspaceVS Rfield V (Count N)).
move=> B b H8 H9 H10 H11.
rewrite MySumF2Add.
apply (SpanSubspaceVS Rfield V (Count N)).
apply H11.
apply (SpanSubspaceVS Rfield V (Count N)).
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
          Vadd Rfield V
            (W (exist (fun (k : nat) => (k < S N)%nat) N H4))
            (Vopp Rfield V
               (MySumF2 (Count N)
                  (exist (Finite (Count N)) (Full_set (Count N))
                     (CountFinite N)) (VSPCM Rfield V)
                  (fun (m0 : Count N) =>
                   Vmul Rfield V
                     (Rip V I (W0 m0)
                        (W (exist (fun k : nat => (k < S N)%nat) N H4)) /
                      Rip V I (W0 m0) (W0 m0)) (W0 m0))))
      end) = W0).
move=> H12.
rewrite H12.
apply (SpanContainSelfVS Rfield V (Count N) W0 b).
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
Rip V I
  match excluded_middle_informative (proj1_sig t1 < N)%nat with
  | left H => W0 (exist (fun k : nat => (k < N)%nat) (proj1_sig t1) H)
  | right _ =>
      Vadd Rfield V
        (W (exist (fun k : nat => (k < S N)%nat) N H4))
        (Vopp Rfield V
           (MySumF2 (Count N)
              (exist (Finite (Count N)) (Full_set (Count N))
                 (CountFinite N)) (VSPCM Rfield V)
              (fun m : Count N =>
               Vmul Rfield V
                 (Rip V I (W0 m)
                    (W (exist (fun k : nat => (k < S N)%nat) N H4)) /
                  Rip V I (W0 m) (W0 m)) (W0 m))))
  end
  match excluded_middle_informative (proj1_sig t2 < N)%nat with
  | left H => W0 (exist (fun k : nat => (k < N)%nat) (proj1_sig t2) H)
  | right _ =>
      Vadd Rfield V
        (W (exist (fun k : nat => (k < S N)%nat) N H4))
        (Vopp Rfield V
           (MySumF2 (Count N)
              (exist (Finite (Count N)) (Full_set (Count N))
                 (CountFinite N)) (VSPCM Rfield V)
              (fun m : Count N =>
               Vmul Rfield V
                 (Rip V I (W0 m)
                    (W (exist (fun k : nat => (k < S N)%nat) N H4)) /
                  Rip V I (W0 m) (W0 m)) (W0 m))))
  end = 0).
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
rewrite (Rip_sym V I).
apply (H6 t2 t1 H8).
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
rewrite (Rip_linear_plus_r V I).
rewrite (Rip_linear_opp_r V I).
suff: (Rip V I (W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7))
  (MySumF2 (Count N)
     (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))
     (VSPCM Rfield V)
     (fun (m : Count N) =>
      Vmul Rfield V
        (Rip V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) /
         Rip V I (W0 m) (W0 m)) (W0 m))) = MySumF2 (Count N)
     (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) RPCM (fun (m : Count N) =>
      Rip V I (W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7)) (Vmul Rfield V
        (Rip V I (W0 m) (W (exist (fun (k : nat) => (k < S N)%nat) N H4)) /
         Rip V I (W0 m) (W0 m)) (W0 m)))).
move=> H9.
rewrite H9.
rewrite (MySumF2Included (Count N) (FiniteSingleton (Count N) (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7)) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite (Rip_linear_mult_r V I).
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite (CM_O_r RPCM).
apply Rplus_opp_r.
move=> H10.
apply (LinearlyIndependentNotContainVOVS Rfield V (Count N) W0 (proj1 H5) (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7)).
apply (proj1 (Rip_refl V I (W0 (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7))) H10).
move=> u.
elim.
move=> u0 H10 H11.
rewrite (Rip_linear_mult_r V I).
rewrite (proj1 (proj2 H5) (exist (fun (k : nat) => (k < N)%nat) (proj1_sig t1) H7) u0).
apply Rmult_0_r.
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
apply (Rip_mult_0_r V I).
move=> B b H9 H10 H11 H12.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Rip_linear_plus_r V I).
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
         => proj1_sig x t <> FO Rfield) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
apply (SpanSubspaceVS Rfield V).
move=> B b H8 H9 H10 H11.
rewrite MySumF2Add.
apply (SpanSubspaceVS Rfield V).
apply H11.
apply (SpanSubspaceVS Rfield V).
suff: (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig b))
        (H3 (proj1_sig b)) = proj1_sig (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig b))
        (H3 (proj1_sig b))) (proj2_sig b))).
move=> H12.
rewrite H12.
apply (SpanContainSelfVS Rfield V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x0 : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x0)) (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig b))
        (H3 (proj1_sig b))) (proj2_sig b))).
reflexivity.
apply H10.
move=> H6.
apply (SpanSubspaceVS Rfield V {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x))).
suff: (proj1_sig (exist (fun (k : nat) => (k < S N)%nat) N H4) <= proj1_sig m)%nat.
move=> H7.
suff: (exist (fun (k : nat) => (k < S N)%nat) N H4 = proj1_sig (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (k : nat) => (k < S N)%nat) N H4) H7)).
move=> H8.
rewrite H8.
apply (SpanContainSelfVS Rfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x)) (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (k : nat) => (k < S N)%nat) N H4) H7)).
reflexivity.
elim (le_or_lt N (proj1_sig m)).
apply.
move=> H7.
elim (H6 H7).
apply (SubspaceMakeVSVoppSub Rfield V (SpanVS Rfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x))) (SpanSubspaceVS Rfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x)))).
apply (FiniteSetInduction (Count N)
     (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS Rfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x))))).
move=> B b H7 H8 H9 H10.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS Rfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x)))).
apply H10.
apply (proj1 (proj2 (SpanSubspaceVS Rfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x))))).
elim (proj2 (proj2 H5) b).
move=> x H11.
rewrite H11.
apply (FiniteSetInduction {k : Count N | (proj1_sig k <= proj1_sig b)%nat}
     (exist (Finite {k : Count N | (proj1_sig k <= proj1_sig b)%nat})
        (fun (t : {k : Count N | (proj1_sig k <= proj1_sig b)%nat}) =>
         proj1_sig x t <> FO Rfield) (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS Rfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x))))).
move=> C c H12 H13 H14 H15.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS Rfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x)))).
apply H15.
apply (proj1 (proj2 (SpanSubspaceVS Rfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}
     (fun (x : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig x))))).
suff: (proj1_sig (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig c))
        (H3 (proj1_sig c))) <= proj1_sig m)%nat.
move=> H16.
suff: (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig c))
        (H3 (proj1_sig c)) = proj1_sig (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig c))
        (H3 (proj1_sig c))) H16)).
move=> H17.
rewrite H17.
apply (SpanContainSelfVS Rfield V
     {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat} (fun (y : {k : Count (S N) | (proj1_sig k <= proj1_sig m)%nat}) =>
      W (proj1_sig y)) (exist (fun (k : Count (S N)) => (proj1_sig k <= proj1_sig m)%nat) (exist (fun (n : nat) => (n < S N)%nat) (proj1_sig (proj1_sig c))
        (H3 (proj1_sig c))) H16)).
reflexivity.
apply (le_trans (proj1_sig (proj1_sig c)) (proj1_sig b) (proj1_sig m) (proj2_sig c)).
apply (le_S_n (proj1_sig b) (proj1_sig m)).
apply (le_trans (S (proj1_sig b)) N (S (proj1_sig m)) (proj2_sig b)).
apply (le_S N (proj1_sig m)).
elim (le_or_lt N (proj1_sig m)).
apply.
move=> H16.
elim (H6 H16).
apply H14.
apply H9.
apply (proj1 (proj1 (Proposition_5_2 Rfield V N H3 H4 W) H2)).
elim (Proposition_5_2_exists Rfield V N).
move=> H4.
elim.
move=> H5 H6.
apply H5.
elim (Proposition_5_2_exists Rfield V N).
move=> H4 H5.
apply H4.
Qed.

Lemma GramSchmidtLinearlyIndepententR : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (N : nat) (W : Count N -> VT Rfield V), LinearlyIndependentVS Rfield V (Count N) W -> {Z : Count N -> VT Rfield V | OrthonormalSystemR V I (Count N) Z /\ SpanVS Rfield V (Count N) W = SpanVS Rfield V (Count N) Z}.
Proof.
move=> V I N W H1.
elim (GramSchmidtLinearlyIndepententR_sub V I N W H1).
move=> Z H2.
exists Z.
suff: (forall (U : Count N -> VT Rfield V), LinearlyIndependentVS Rfield V (Count N) U -> FiniteDimensionVS Rfield (SubspaceMakeVS Rfield V (SpanVS Rfield V (Count N) U) (SpanSubspaceVS Rfield V (Count N) U))).
move=> H3.
suff: (forall (U : Count N -> VT Rfield V) (H : LinearlyIndependentVS Rfield V (Count N) U), DimensionSubspaceVS Rfield V
  (SpanVS Rfield V (Count N) U)
  (SpanSubspaceVS Rfield V (Count N) U) 
  (H3 U H) = N).
move=> H4.
apply conj.
apply (proj1 H2).
suff: (Included (VT Rfield V) (SpanVS Rfield V (Count N) Z) (SpanVS Rfield V (Count N) W)).
move=> H5.
rewrite (proj1 (Proposition_5_9_1_3_subspace Rfield V (SpanVS Rfield V (Count N) Z) (SpanVS Rfield V (Count N) W) (SpanSubspaceVS Rfield V (Count N) Z) (SpanSubspaceVS Rfield V (Count N) W) H5 (H3 W H1) (H3 Z (OrthonormalSystemLinearlyIndependentR V I (Count N) Z (proj1 H2))))).
reflexivity.
rewrite (H4 W H1).
apply (H4 Z (OrthonormalSystemLinearlyIndependentR V I (Count N) Z (proj1 H2))).
move=> v.
elim.
move=> x H5.
rewrite H5.
apply (FiniteSetInduction (Count N)
     (exist (Finite (Count N))
        (fun (t : Count N) => proj1_sig x t <> FO Rfield) 
        (proj2_sig x))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS Rfield V (Count N) W))).
move=> B b H6 H7 H8 H9.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS Rfield V (Count N) W)).
apply H9.
apply (proj1 (proj2 (SpanSubspaceVS Rfield V (Count N) W))).
elim (proj2 H2 b).
move=> y H10.
rewrite H10.
apply (FiniteSetInduction {k : Count N | (proj1_sig k <= proj1_sig b)%nat}
     (exist (Finite {k : Count N | (proj1_sig k <= proj1_sig b)%nat})
        (fun (t : {k : Count N | (proj1_sig k <= proj1_sig b)%nat}) =>
         proj1_sig y t <> FO Rfield) (proj2_sig y))).
apply conj.
rewrite MySumF2Empty.
apply (proj2 (proj2 (SpanSubspaceVS Rfield V (Count N) W))).
move=> C c H11 H12 H13 H14.
rewrite MySumF2Add.
apply (proj1 (SpanSubspaceVS Rfield V (Count N) W)).
apply H14.
apply (proj1 (proj2 (SpanSubspaceVS Rfield V (Count N) W))).
apply (SpanContainSelfVS Rfield V (Count N) W (proj1_sig c)).
apply H13.
apply H8.
move=> U H4.
apply (DimensionVSNature2 Rfield (SubspaceMakeVS Rfield V
     (SpanVS Rfield V (Count N) U)
     (SpanSubspaceVS Rfield V (Count N) U)) (H3 U H4) N (fun (m : Count N) => exist (SpanVS Rfield V (Count N) U) (U m) (SpanContainSelfVS Rfield V (Count N) U m)) H4).
move=> U H3.
exists N.
exists (fun (m : Count N) => exist (SpanVS Rfield V (Count N) U) (U m) (SpanContainSelfVS Rfield V (Count N) U m)).
apply H3.
Qed.

Lemma GramSchmidtBasisR : forall (V : VectorSpace Rfield) (I : RInner_Product_Space V) (N : nat) (W : Count N -> VT Rfield V), BasisVS Rfield V (Count N) W -> {Z : Count N -> VT Rfield V | OrthonormalSystemR V I (Count N) Z /\ BasisVS Rfield V (Count N) Z /\ forall (m : Count N), In (VT Rfield V) (SpanVS Rfield V {k : Count N | (proj1_sig k <= proj1_sig m)%nat} (fun (x : {k : Count N | (proj1_sig k <= proj1_sig m)%nat}) => W (proj1_sig x))) (Z m)}.
Proof.
move=> V I N W H1.
elim (GramSchmidtLinearlyIndepententR_sub V I N W).
move=> Z H2.
exists Z.
apply conj.
apply (proj1 H2).
apply conj.
suff: (FiniteDimensionVS Rfield V).
move=> H3.
apply (Corollary_5_8_2_3 Rfield V N Z H3).
apply conj.
apply (OrthonormalSystemLinearlyIndependentR V I (Count N) Z (proj1 H2)).
apply (DimensionVSNature2 Rfield V H3 N W H1).
exists N.
exists W.
apply H1.
apply (proj2 H2).
apply (proj1 (proj1 (BasisLIGeVS Rfield V (Count N) W) H1)).
Qed.

Definition MSymmetric (f : Field) (N : nat) (A : Matrix f N N) := MTranspose f N N A = A.

Definition OrthogonalMatrix (N : nat) (A : Matrix Rfield N N) := Mmult Rfield N N N (MTranspose Rfield N N A) A = MI Rfield N.

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

Lemma OrthogonalMatrixChain : forall (N : nat) (A B : Matrix Rfield N N), OrthogonalMatrix N A -> OrthogonalMatrix N B -> OrthogonalMatrix N (Mmult Rfield N N N A B).
Proof.
move=> N A B H1 H2.
unfold OrthogonalMatrix.
rewrite (MTransMult Rfield N N N A B).
rewrite (Mmult_assoc Rfield N N N N (MTranspose Rfield N N B) (MTranspose Rfield N N A) (Mmult Rfield N N N A B)).
rewrite - (Mmult_assoc Rfield N N N N (MTranspose Rfield N N A) A B).
rewrite H1.
rewrite (Mmult_I_l Rfield N N B).
apply H2.
Qed.

Definition RnInner_Product_Space (N : nat) := mkRInner_Product_Space (RnVS N) (RnInnerProduct N) (Proposition_4_2_3 N) (Proposition_4_2_2_1 N) (Proposition_4_2_1_1 N) (Proposition_4_2_4_1 N) (fun (x : Rn N) => conj (Proposition_4_2_4_2 N x) (Proposition_4_2_4_3 N x)).

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
suff: (exists (V : Matrix Rfield (S N) (S N)), OrthogonalMatrix (S N) V /\ forall (m : {n : nat | (n < S N)%nat}), (proj1_sig m > O)%nat -> Mmult Rfield (S N) (S N) (S N) (MTranspose Rfield (S N) (S N) V)
    (Mmult Rfield (S N) (S N) (S N) A V) m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = 0).
elim.
move=> V H3.
suff: (exists (B : Matrix Rfield N N) (la : R), MSymmetric Rfield N B /\ Mmult Rfield (S N) (S N) (S N) (MTranspose Rfield (S N) (S N) V)
        (Mmult Rfield (S N) (S N) (S N) A V) = MBlockH Rfield 1 N (S N) (MBlockW Rfield 1 1 N (fun (_ _ : {n : nat | (n < 1)%nat}) => la) (MO Rfield 1 N)) (MBlockW Rfield N 1 N (MO Rfield N 1) B)).
elim.
move=> B.
elim.
move=> la H4.
elim (H1 B (proj1 H4)).
move=> W.
elim.
move=> D H5.
exists (Mmult Rfield (S N) (S N) (S N) V (MBlockH Rfield 1 N (S N)
       (MBlockW Rfield 1 1 N (fun _ _ : {n : nat | (n < 1)%nat} => 1)
          (MO Rfield 1 N)) (MBlockW Rfield N 1 N (MO Rfield N 1) W))).
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
suff: (exist (Finite (Count 1)) (Full_set {n : nat | (n < 1)%nat})
     (CountFinite 1) = FiniteSingleton {n : nat | (n < 1)%nat} (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1))).
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
suff: (exist (Finite (Count 1)) (Full_set {n : nat | (n < 1)%nat})
     (CountFinite 1) = FiniteSingleton {n : nat | (n < 1)%nat} (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1))).
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
exists (fun (x y : {n : nat | (n < N)%nat}) => Mmult Rfield (S N) (S N) (S N) (MTranspose Rfield (S N) (S N) V)
    (Mmult Rfield (S N) (S N) (S N) A V) (AddConnect 1 N (inr x)) (AddConnect 1 N (inr y))).
exists (Mmult Rfield (S N) (S N) (S N) (MTranspose Rfield (S N) (S N) V)
    (Mmult Rfield (S N) (S N) (S N) A V) (AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat
           (le_n 1)))) (AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat
           (le_n 1))))).
suff: (MSymmetric Rfield (S N) (Mmult Rfield (S N) (S N) (S N)
  (fun (x0 y0 : {n : nat | (n < S N)%nat}) => V y0 x0)
  (Mmult Rfield (S N) (S N) (S N) A V))).
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
suff: (let Aform := fun (u : {n : nat | (n < S N)%nat} -> R) => RnInnerProduct (S N) u (MVmult Rfield (S N) (S N) A u) in exists (V : Matrix Rfield (S N) (S N)),
  OrthogonalMatrix (S N) V /\
  (forall (m : {n : nat | (n < S N)%nat}),
   (proj1_sig m > 0)%nat ->
   Mmult Rfield (S N) (S N) (S N) (MTranspose Rfield (S N) (S N) V)
     (Mmult Rfield (S N) (S N) (S N) A V) m
     (exist (fun (n : nat) => (n < S N)%nat) O
        (le_n_S 0 N (le_0_n N))) = 0)).
apply.
move=> Aform.
suff: (exists (v : {n : nat | (n < S N)%nat} -> R), RnNorm (S N) v = 1 /\ forall (w : {n : nat | (n < S N)%nat} -> R), RnNorm (S N) w = 1 -> Aform w <= Aform v).
elim.
move=> v H3.
suff: (exists (V : Matrix Rfield (S N) (S N)),
  OrthogonalMatrix (S N) V /\ V (exist (fun (n : nat) => (n < S N)%nat) 0%nat
           (le_n_S 0 N (le_0_n N))) = v).
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
suff: (Mmult Rfield (S N) (S N) (S N) V
  (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) (exist (fun (n : nat) => (n < S N)%nat) O
           (le_n_S 0 N (le_0_n N))) (exist (fun (n : nat) => (n < S N)%nat) O
           (le_n_S 0 N (le_0_n N))) = Aform v).
move=> H8.
suff: (forall (eps : R), Aform v + (1 + 1) * eps * (Mmult Rfield (S N) (S N) (S N) V
  (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m
  (exist (fun (n : nat) => (n < S N)%nat) 0%nat (le_n_S 0 N (Nat.le_0_l N)))) + eps * eps * (Mmult Rfield (S N) (S N) (S N) V
  (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m) <= (1 + eps * eps) * Aform v).
move=> H9.
suff: (forall (eps : R), eps * ((1 + 1) * Mmult Rfield (S N) (S N) (S N) V
       (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
       m
       (exist (fun (n : nat) => (n < S N)%nat) 0%nat
          (le_n_S 0 N (le_0_n N))) + eps * (Mmult Rfield (S N) (S N) (S N) V
       (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
       m m - Aform v)) <= 0).
move=> H10.
elim (Rmult_integral (1 + 1) (Mmult Rfield (S N) (S N) (S N) V
       (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
       m
       (exist (fun (n : nat) => (n < S N)%nat) 0%nat
          (le_n_S 0 N (le_0_n N))))).
move=> H11.
apply False_ind.
apply (Rle_not_lt 0 (1 + 1)).
rewrite H11.
right.
reflexivity.
apply (Rlt_trans 0 1 (1 + 1) Rlt_0_1 (Rlt_plus_1 1)).
apply.
elim (Rle_or_lt ((1 + 1) * (Mmult Rfield (S N) (S N) (S N) V
       (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
       m
       (exist (fun (n : nat) => (n < S N)%nat) 0%nat
          (le_n_S 0 N (le_0_n N))))) 0).
elim.
move=> H11.
apply False_ind.
elim (Rle_or_lt 0 (Mmult Rfield (S N) (S N) (S N) V
          (Mmult Rfield (S N) (S N) (S N) A
             (MTranspose Rfield (S N) (S N) V)) m m - 
        Aform v)).
move=> H12.
apply (Rle_not_lt 0 (- 1 * ((1 + 1) *
       Mmult Rfield (S N) (S N) (S N) V
         (Mmult Rfield (S N) (S N) (S N) A
            (MTranspose Rfield (S N) (S N) V)) m
         (exist (fun n : nat => (n < S N)%nat) 0%nat
            (le_n_S 0 N (Nat.le_0_l N))) +
       (- 1) *
       (Mmult Rfield (S N) (S N) (S N) V
          (Mmult Rfield (S N) (S N) (S N) A
             (MTranspose Rfield (S N) (S N) V)) m m - 
        Aform v))) (H10 (- 1))).
rewrite - Rmult_opp_opp.
apply Rmult_lt_0_compat.
rewrite (Ropp_involutive 1).
apply Rlt_0_1.
apply Ropp_gt_lt_0_contravar.
rewrite - (Rplus_0_r 0).
apply Rplus_lt_le_compat.
apply H11.
rewrite - (Rmult_0_l (Mmult Rfield (S N) (S N) (S N) V
   (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m -
 Aform v)).
apply Rmult_le_compat_r.
apply H12.
apply Rge_le.
apply Ropp_0_le_ge_contravar.
left.
apply Rlt_0_1.
move=> H12.
elim (Proposition_1_1 ((1 + 1) *
      Mmult Rfield (S N) (S N) (S N) V
        (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
        m
        (exist (fun (n : nat) => (n < S N)%nat) 0%nat
           (le_n_S 0 N (le_0_n N)))) 0).
move=> x H13.
apply (Rle_not_lt 0 ((- x / (Mmult Rfield (S N) (S N) (S N) V
          (Mmult Rfield (S N) (S N) (S N) A
             (MTranspose Rfield (S N) (S N) V)) m m - 
        Aform v)) * ((1 + 1) *
       Mmult Rfield (S N) (S N) (S N) V
         (Mmult Rfield (S N) (S N) (S N) A
            (MTranspose Rfield (S N) (S N) V)) m
         (exist (fun n : nat => (n < S N)%nat) 0%nat
            (le_n_S 0 N (Nat.le_0_l N))) +
       (- x / (Mmult Rfield (S N) (S N) (S N) V
          (Mmult Rfield (S N) (S N) (S N) A
             (MTranspose Rfield (S N) (S N) V)) m m - 
        Aform v)) *
       (Mmult Rfield (S N) (S N) (S N) V
          (Mmult Rfield (S N) (S N) (S N) A
             (MTranspose Rfield (S N) (S N) V)) m m - 
        Aform v))) (H10 (- x / (Mmult Rfield (S N) (S N) (S N) V
          (Mmult Rfield (S N) (S N) (S N) A
             (MTranspose Rfield (S N) (S N) V)) m m - 
        Aform v)))).
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
elim (Rle_or_lt 0 (Mmult Rfield (S N) (S N) (S N) V
          (Mmult Rfield (S N) (S N) (S N) A
             (MTranspose Rfield (S N) (S N) V)) m m - 
        Aform v)).
move=> H12.
apply (Rle_not_lt 0 (1 * ((1 + 1) *
       Mmult Rfield (S N) (S N) (S N) V
         (Mmult Rfield (S N) (S N) (S N) A
            (MTranspose Rfield (S N) (S N) V)) m
         (exist (fun n : nat => (n < S N)%nat) 0%nat
            (le_n_S 0 N (Nat.le_0_l N))) +
       1 *
       (Mmult Rfield (S N) (S N) (S N) V
          (Mmult Rfield (S N) (S N) (S N) A
             (MTranspose Rfield (S N) (S N) V)) m m - 
        Aform v))) (H10 1)).
rewrite Rmult_1_l.
rewrite Rmult_1_l.
apply Rplus_lt_le_0_compat.
apply H11.
apply H12.
move=> H12.
elim (Proposition_1_1 0 ((1 + 1) *
      Mmult Rfield (S N) (S N) (S N) V
        (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
        m
        (exist (fun (n : nat) => (n < S N)%nat) 0%nat
           (le_n_S 0 N (le_0_n N)))) H11).
move=> x H13.
apply (Rle_not_lt 0 ((x / (- (Mmult Rfield (S N) (S N) (S N) V
        (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
        m m - Aform v))) * ((1 + 1) *
       Mmult Rfield (S N) (S N) (S N) V
         (Mmult Rfield (S N) (S N) (S N) A
            (MTranspose Rfield (S N) (S N) V)) m
         (exist (fun (n : nat) => (n < S N)%nat) 0%nat
            (le_n_S 0 N (le_0_n N))) +
       (x / (- (Mmult Rfield (S N) (S N) (S N) V
        (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
        m m - Aform v))) *
       (Mmult Rfield (S N) (S N) (S N) V
          (Mmult Rfield (S N) (S N) (S N) A
             (MTranspose Rfield (S N) (S N) V)) m m - 
        Aform v))) (H10 (x / (- (Mmult Rfield (S N) (S N) (S N) V
        (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
        m m - Aform v))))).
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
rewrite - (Rplus_assoc (eps *
  ((1 + 1) *
   Mmult Rfield (S N) (S N) (S N) V
     (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m
     (exist (fun (n : nat) => (n < S N)%nat) O
        (le_n_S 0 N (le_0_n N)))))).
rewrite (Rplus_comm (eps *
  ((1 + 1) *
   Mmult Rfield (S N) (S N) (S N) V
     (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m
     (exist (fun (n : nat) => (n < S N)%nat) O
        (le_n_S 0 N (le_0_n N)))) +
  eps * eps *
  Mmult Rfield (S N) (S N) (S N) V
    (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m
    m)).
rewrite - (Rplus_assoc (eps * eps * Aform v)).
rewrite Rplus_opp_r.
rewrite Rplus_0_l.
rewrite - (Rmult_assoc eps).
rewrite (Rmult_comm eps (1 + 1)).
rewrite - Rplus_assoc.
apply (H9 eps).
move=> eps.
suff: (Aform v +
(1 + 1) * eps *
Mmult Rfield (S N) (S N) (S N) V
  (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m
  (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N))) +
eps * eps *
Mmult Rfield (S N) (S N) (S N) V
  (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) m m =
Aform (MMatrixToVector Rfield (S N) (Mmult Rfield (S N) (S N) 1 (MTranspose Rfield (S N) (S N) V) (MVectorToMatrix Rfield (S N) (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
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
rewrite RnInnerProductDefinition.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat
          (le_n_S 0 N (le_0_n N))))).
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
suff: (In (Count (S N))
        (Complement (Count (S N))
           (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H13.
move=> u1 H14 H15 H16.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H17.
elim H14.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat
        (le_n_S 0 N (le_0_n N)))).
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
suff: (MVectorToMatrix Rfield (S N)
     (MVmult Rfield (S N) (S N) A
        (MMatrixToVector Rfield (S N)
           (Mmult Rfield (S N) (S N) 1 (MTranspose Rfield (S N) (S N) V)
              (MVectorToMatrix Rfield (S N)
                 (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
  | left _ => 1
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => eps
    | right _ => 0
  end
end)))))
= Mmult Rfield (S N) (S N) 1 A (Mmult Rfield (S N) (S N) 1 (MTranspose Rfield (S N) (S N) V)
              (MVectorToMatrix Rfield (S N)
                 (fun (l : Count (S N)) => match excluded_middle_informative (proj1_sig l = O) with
  | left _ => 1
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => eps
    | right _ => 0
  end
end)))
).
move=> H9.
rewrite H9.
rewrite (Mmult_assoc Rfield 1 (S N) (S N) 1).
rewrite - (Mmult_assoc Rfield (S N) (S N) (S N) 1).
rewrite - (Mmult_assoc Rfield (S N) (S N) (S N) 1 (Mmult Rfield (S N) (S N) (S N) V A)).
unfold Mmult at 5.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (n : nat) => (n < S N)%nat) 0%nat
          (le_n_S 0 N (le_0_n N))))).
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
rewrite (Rplus_assoc (Mmult Rfield (S N) (S N) (S N) V
  (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
  (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))
  (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))) (Mmult Rfield (S N) (S N) (S N) V
  (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
  (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))
  m * eps)).
rewrite (Rmult_comm (Mmult Rfield (S N) (S N) (S N) V
  (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
  (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))
  m) eps).
rewrite (Rmult_comm (Mmult Rfield (S N) (S N) (S N) V
  (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
  m m) eps).
rewrite (Rmult_plus_distr_l eps).
rewrite - (Rmult_assoc eps eps).
rewrite - (Rplus_assoc (eps *
 Mmult Rfield (S N) (S N) (S N) V
   (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
   (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))
   m)).
suff: (Mmult Rfield (S N) (S N) (S N) V
   (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
   (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))
   m = Mmult Rfield (S N) (S N) (S N) V
   (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V))
   m (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S 0 N (le_0_n N)))
   ).
move=> H17.
rewrite H17.
rewrite Rplus_assoc.
reflexivity.
suff: (Mmult Rfield (S N) (S N) (S N) V
  (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)) = MTranspose Rfield (S N) (S N) (Mmult Rfield (S N) (S N) (S N) V
  (Mmult Rfield (S N) (S N) (S N) A (MTranspose Rfield (S N) (S N) V)))).
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
suff: (In (Count (S N))
        (Complement (Count (S N))
           (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H14.
move=> u1 H15 H16 H17.
unfold MVectorToMatrix.
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
apply Rmult_0_r.
apply H13.
move=> u.
elim.
move=> u0 H13 H14.
suff: (In (Count (S N))
        (Complement (Count (S N))
           (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H14.
move=> u1 H15 H16 H17.
unfold MVectorToMatrix.
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
suff: (In (Count (S N))
        (Complement (Count (S N))
           (proj1_sig (FiniteSingleton (Count (S N)) m))) u0).
elim H11.
move=> u1 H12 H13 H14.
unfold MVectorToMatrix.
unfold MTranspose.
elim (excluded_middle_informative (proj1_sig u1 = O)).
move=> H15.
elim H12.
suff: (u1 = (exist (fun (n : nat) => (n < S N)%nat) 0%nat
           (le_n_S 0 N (le_0_n N)))).
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
rewrite (Proposition_4_2_4_3 (S N) (RnO (S N))).
rewrite Rmult_0_r.
unfold Aform.
rewrite RnInnerProductDefinition.
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
apply Proposition_4_2_4_1.
suff: (Aform w * / RnInnerProduct (S N) w w = Aform (Rnmult (S N) (/ RnNorm (S N) w) w)).
move=> H7.
rewrite H7.
apply H3.
rewrite Proposition_4_4_1.
rewrite Rabs_right.
apply Rinv_l.
move=> H8.
apply H6.
apply (Proposition_4_4_3_2 (S N) w H8).
left.
apply Rinv_0_lt_compat.
elim (Proposition_4_4_3_1 (S N) w).
apply.
move=> H8.
apply False_ind.
apply H6.
apply (Proposition_4_4_3_2 (S N) w H8).
rewrite (proj2 (RnNormNature (S N) w)).
unfold Aform.
rewrite RnInnerProductDefinition.
rewrite RnInnerProductDefinition.
apply (FiniteSetInduction (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N)))
     (CountFinite (S N)))).
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
apply (Proposition_4_4_3_2 (S N) w H11).
move=> H11.
apply H6.
apply (Proposition_4_4_3_2 (S N) w H11).
apply H9.
apply H9.
move=> H7.
apply H6.
apply (Proposition_4_2_4_2 (S N) w H7).
move=> x y.
rewrite RnInnerProductDefinition.
unfold MVectorToMatrix.
unfold MTranspose.
unfold Mmult.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S N)%nat}
  (exist (Finite {n : nat | (n < S N)%nat})
     (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
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
suff: (MTranspose Rfield (S N) (S N)
     (fun (m : Count (S N)) => match AddConnectInv 1 N m with
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
rewrite RnInnerProductDefinition.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S N)%nat}
  (exist (Finite {n : nat | (n < S N)%nat})
     (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> C c H12 H13 H14 H15.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H15.
reflexivity.
apply H14.
apply H14.
rewrite (proj2 (RnNormNature (S N) v)).
rewrite (proj1 H3).
rewrite (Rmult_1_r 1).
reflexivity.
move=> m.
simpl.
rewrite - (proj1 (proj1 H7) m).
simpl.
rewrite RnInnerProductDefinition.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S N)%nat}
  (exist (Finite {n : nat | (n < S N)%nat})
     (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> C c H10 H11 H12 H13.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H13.
reflexivity.
apply H12.
apply H12.
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
simpl.
rewrite RnInnerProductDefinition.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S N)%nat}
  (exist (Finite {n : nat | (n < S N)%nat})
     (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> C c H14 H15 H16 H17.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H17.
reflexivity.
apply H16.
apply H16.
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
rewrite RnInnerProductDefinition.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S N)%nat}
  (exist (Finite {n : nat | (n < S N)%nat})
     (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> C c H14 H15 H16 H17.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H17.
rewrite (Rmult_comm (W x0 c) (v c)).
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
rewrite RnInnerProductDefinition.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < S N)%nat}
  (exist (Finite {n : nat | (n < S N)%nat})
     (Full_set {n : nat | (n < S N)%nat}) (CountFinite (S N)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> C c H14 H15 H16 H17.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H17.
reflexivity.
apply H16.
apply H16.
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
apply (FiniteSetInduction (Count N) (exist (Finite (Count N))
        (fun (t0 : Count N) => proj1_sig a t0 <> FO Rfield) 
        (proj2_sig a))).
apply conj.
rewrite MySumF2Empty.
apply (Rip_mult_0_r (RnVS (S N)) (RnInner_Product_Space (S N)) v).
move=> C c H12 H13 H14 H15.
rewrite MySumF2Add.
simpl.
rewrite (Proposition_4_2_1_2 (S N) v).
rewrite H15.
rewrite - (Proposition_4_2_2_2 (S N)).
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
apply (SubspaceBasisLinearlyIndependentVS Rfield (RnVS (S N))
       (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 
       (Count N) B H6).
suff: (DimensionSubspaceVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 H5 = N).
move=> H6.
suff: (exists (B : Count (DimensionSubspaceVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 H5) -> Rn (S N)),
  BasisSubspaceVS Rfield (RnVS (S N))
    (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 
    (Count (DimensionSubspaceVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 H5)) B).
rewrite H6.
apply.
apply (DimensionSubspaceVSNature Rfield (RnVS (S N))
       (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 H5).
suff: (SubspaceVS Rfield (RnVS (S N))
         (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v)).
move=> H6.
elim (DimensionSumEnsembleVS2_exists Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H6 H4).
move=> H7 H8.
suff: (FiniteDimensionVS Rfield
              (SubspaceMakeVS Rfield (RnVS (S N))
                 (SumEnsembleVS Rfield (RnVS (S N))
                    (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v)
                    (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) H7)).
move=> H9.
elim (H8 H9).
move=> H10.
elim.
move=> H11 H12.
apply (plus_reg_l (DimensionSubspaceVS Rfield (RnVS (S N))
  (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H4 H5) N 1).
suff: ((1 + N)%nat = DimensionSubspaceVS Rfield (RnVS (S N))
        (SumEnsembleVS Rfield (RnVS (S N))
           (fun (w : Rn (S N)) => exists f : R, w = Rnmult (S N) f v)
           (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) H7 H9).
move=> H13.
rewrite H13.
suff: (1%nat = DimensionSubspaceVS Rfield (RnVS (S N))
         (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) H6 H10).
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
rewrite - (Proposition_4_2_2_2 (S N) c v v).
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
apply (proj2 (proj2 (IntersectionSubspaceVS Rfield (RnVS (S N)) (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v)
     (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0) H6 H4))).
rewrite (DimensionSubspaceVSNature2 Rfield (RnVS (S N))
  (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) H6 H10 1 (fun (m : Count 1) => v)).
reflexivity.
suff: (exists (f : R), v = Rnmult (S N) f v).
move=> H14.
exists (fun (m : Count 1) => H14).
apply (proj2 (BasisLIGeVS Rfield
  (SubspaceMakeVS Rfield (RnVS (S N))
     (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) H6) 
  (Count 1)
  (fun (m : Count 1) =>
   exist (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) v H14))).
apply conj.
apply FiniteLinearlyIndependentVS.
move=> a H15 m.
suff: (MySumF2 (Count 1)
        (exist (Finite (Count 1)) (Full_set (Count 1)) (CountFinite 1))
        (VSPCM Rfield
           (SubspaceMakeVS Rfield (RnVS (S N))
              (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) H6))
        (fun (n : Count 1) =>
         Vmul Rfield
           (SubspaceMakeVS Rfield (RnVS (S N))
              (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) H6)
           (a n)
           (exist (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v)
              v H14)) =
      VO Rfield
        (SubspaceMakeVS Rfield (RnVS (S N))
           (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) H6)).
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
apply (Proposition_4_4_3_3 (S N) v H19).
suff: (Rnmult (S N) (a m) v = proj1_sig (Vmul Rfield
        (SubspaceMakeVS Rfield (RnVS (S N))
           (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) H6)
        (a m)
        (exist (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v) v
           H14))).
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
rewrite (Rnmult_I_l (S N) v).
reflexivity.
suff: (FiniteDimensionVS Rfield (RnVS (S N))).
move=> H13.
suff: (DimensionVS Rfield (RnVS (S N)) H13 = S N).
move=> H14.
elim (DimensionVSNature Rfield (RnVS (S N)) H13).
rewrite H14.
move=> a H15.
unfold DimensionSubspaceVS.
suff: (forall (z : Rn (S N)), In (Rn (S N)) (SumEnsembleVS Rfield (RnVS (S N))
        (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v)
        (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) z).
move=> H16.
rewrite (DimensionVSNature2 Rfield
  (SubspaceMakeVS Rfield (RnVS (S N))
     (SumEnsembleVS Rfield (RnVS (S N))
        (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v)
        (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) H7) H9 (S N) (fun (m : Count (S N)) => exist (SumEnsembleVS Rfield (RnVS (S N))
        (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v)
        (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) (a m) (H16 (a m)))).
reflexivity.
apply (IsomorphicSaveBasisVS Rfield (FnVS Rfield (S N)) (SubspaceMakeVS Rfield (RnVS (S N))
     (SumEnsembleVS Rfield (RnVS (S N))
        (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v)
        (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) H7) (Count (S N)) a (fun (z : Rn (S N)) =>
   exist
     (SumEnsembleVS Rfield (RnVS (S N))
        (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v)
        (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) 
     z (H16 z))).
apply conj.
exists (fun (m : (SubspaceMakeVST Rfield (RnVS (S N))
     (SumEnsembleVS Rfield (RnVS (S N))
        (fun (w : Rn (S N)) => exists (f : R), w = Rnmult (S N) f v)
        (fun (w : Rn (S N)) => RnInnerProduct (S N) v w = 0)) H7)) => proj1_sig m).
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
rewrite (Proposition_4_2_1_2 (S N)).
suff: (RnInnerProduct (S N) v (Rnopp (S N) (Rnmult (S N) (RnInnerProduct (S N) v z) v)) = Rip (RnVS (S N)) (RnInner_Product_Space (S N)) v (Vopp Rfield (RnVS (S N)) (Rnmult (S N) (RnInnerProduct (S N) v z) v))).
move=> H17.
rewrite H17.
rewrite (Rip_linear_opp_r (RnVS (S N)) (RnInner_Product_Space (S N))).
simpl.
rewrite - (Proposition_4_2_2_2 (S N)).
rewrite (proj2 (RnNormNature (S N) v)).
rewrite (proj1 H3).
rewrite (Rmult_1_l 1).
rewrite Rmult_1_r.
apply Rplus_opp_r.
reflexivity.
unfold Rnminus.
rewrite (Rnplus_comm (S N) z).
rewrite - (Rnplus_assoc (S N)).
rewrite (Rnplus_opp_r (S N)).
rewrite (Rnplus_O_l (S N) z).
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
rewrite (Proposition_4_2_1_2 (S N) v x y).
rewrite H4.
rewrite H5.
apply (Rplus_0_r 0).
apply conj.
move=> f x H4.
unfold In.
rewrite - (Proposition_4_2_2_2 (S N) f v x).
rewrite H4.
apply (Rmult_0_r f).
apply (Rip_mult_0_r (RnVS (S N)) (RnInner_Product_Space (S N)) v).
elim (Theorem_7_3_2_1 (Rn_met (S N)) Aform (fun (x : Rn (S N)) => RnInnerProduct (S N) x x = 1)).
move=> z H3.
suff: (forall (y : R),
       In R
         (Im (Base (Rn_met (S N))) R
            (fun (x : Rn (S N)) => RnInnerProduct (S N) x x = 1) Aform) y ->
       y <= z).
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
apply (Im_intro (Base (Rn_met (S N))) R
     (fun (x0 : Rn (S N)) => RnInnerProduct (S N) x0 x0 = 1) Aform w).
unfold In.
rewrite (proj2 (RnNormNature (S N) w)).
rewrite H7.
apply (Rmult_1_r 1).
reflexivity.
apply (proj2 H3).
apply (Inhabited_intro (Base (Rn_met (S N)))
  (fun (x : Rn (S N)) => RnInnerProduct (S N) x x = 1) (fun (m : Count (S N)) => match excluded_middle_informative (m = exist (fun (k : nat) => (k < S N)%nat) O (le_n_S O N (le_0_n N))) with
  | left _ => 1
  | right _ => 0
end)).
unfold In.
rewrite RnInnerProductDefinition.
rewrite (MySumF2Included (Count (S N)) (FiniteSingleton (Count (S N)) (exist (fun (k : nat) => (k < S N)%nat) O (le_n_S O N (le_0_n N))))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
elim (excluded_middle_informative
       (@eq (Count (S N)) (exist (fun (k : nat) => (k < S N)%nat) O
          (le_n_S 0 N (le_0_n N)))
        (exist (fun (k : nat) => (k < S N)%nat) O
          (le_n_S 0 N (le_0_n N))))).
move=> H3.
rewrite (Rmult_1_r 1).
apply (CM_O_r RPCM 1).
elim.
reflexivity.
move=> u.
elim.
move=> u0 H3 H4.
elim (excluded_middle_informative
       (@eq (Count (S N)) u0
        (exist (fun (k : nat) => (k < S N)%nat) O
          (le_n_S 0 N (le_0_n N))))).
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
suff: (forall (k : nat), (k <= S N)%nat -> ContinuousMet (Rn_met (S N)) R_met
  (fun (u : {n : nat | (n < S N)%nat} -> R) =>
   my_sum_f_R
     (fun (n : nat) =>
      UnwrapRn (S N) u n * UnwrapRn (S N) (MVmult Rfield (S N) (S N) A u) n)
     k) (Full_set (Base (Rn_met (S N)))) x).
move=> H5.
apply (H5 (S N) (le_n (S N))).
elim.
move=> H5 eps H6.
exists 1.
apply conj.
apply Rlt_0_1.
move=> y H7.
unfold my_sum_f_R.
rewrite (proj2 (dist_refl R_met 0 0)).
apply H6.
reflexivity.
move=> k H5 H6.
simpl.
apply Theorem_6_6_3_1_R.
apply (H5 (le_trans k (S k) (S N) (le_S k k (le_n k)) H6)).
unfold UnwrapRn.
elim (excluded_middle_informative (k < S N)%nat).
move=> H7.
apply Theorem_6_6_3_5_R.
apply H3.
unfold MVmult.
unfold MMatrixToVector.
unfold MVectorToMatrix.
unfold Mmult.
apply (FiniteSetInduction {n : nat | (n < S N)%nat}
     (exist (Finite (Count (S N))) (Full_set {n : nat | (n < S N)%nat})
        (CountFinite (S N)))).
apply conj.
move=> eps H8.
exists 1.
apply conj.
apply Rlt_0_1.
move=> y H9.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (proj2 (dist_refl R_met 0 0)).
apply H8.
reflexivity.
move=> B b H8 H9 H10 H11.
suff: ((fun (r : Base (Rn_met (S N))) =>
   MySumF2 {n : nat | (n < S N)%nat}
     (FiniteAdd {n : nat | (n < S N)%nat} B b) (FPCM Rfield)
     (fun (n : Count (S N)) =>
      Fmul Rfield (A (exist (fun (n0 : nat) => (n0 < S N)%nat) k H7) n) (r n))) = (fun (r : Base (Rn_met (S N))) =>
   MySumF2 {n : nat | (n < S N)%nat}
     B (FPCM Rfield)
     (fun (n : Count (S N)) =>
      Fmul Rfield (A (exist (fun (n0 : nat) => (n0 < S N)%nat) k H7) n) (r n)) + Fmul Rfield (A (exist (fun (n0 : nat) => (n0 < S N)%nat) k H7) b) (r b))).
move=> H12.
rewrite H12.
apply Theorem_6_6_3_1_R.
apply H11.
apply Theorem_6_6_3_3_R.
apply H3.
apply functional_extensionality.
move=> r.
apply MySumF2Add.
apply H10.
move=> H7.
elim (H7 H6).
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
rewrite RnInnerProductDefinition.
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

Definition UpperTriangularNormalFormR (M N : nat) (A : Matrix Rfield M N) := UpperTriangularMatrixStrong Rfield M N A /\ forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}), (forall (z : {n : nat | (n < N)%nat}), (proj1_sig y > proj1_sig z)%nat -> A x z = 0) -> A x y >= 0.

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
suff: (forall (D : Matrix Rfield (S M) (S N)), (forall (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < 1)%nat}),
     D m (AddConnect 1 N (inl k)) = 0) -> Mmult Rfield N (S M) N
  (MTranspose Rfield (S M) N
     (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) =>
      D m (AddConnect 1 N (inr k))))
  (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) =>
   D m (AddConnect 1 N (inr k))) = (fun (x y : {n : nat | (n < N)%nat}) => Mmult Rfield (S N) (S M) (S N) (MTranspose Rfield (S M) (S N) D) D (AddConnect 1 N (inr x)) (AddConnect 1 N (inr y)))).
move=> H10.
rewrite (H10 A H8).
rewrite (H10 B H9).
rewrite H5.
reflexivity.
move=> D H10.
suff: (D = MBlockW Rfield (S M) 1 N (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < 1)%nat}) =>
      D m (AddConnect 1 N (inl k))) (fun (m : {n : nat | (n < S M)%nat}) (k : {n : nat | (n < N)%nat}) =>
      D m (AddConnect 1 N (inr k)))).
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
suff: (forall (D : Matrix Rfield (S M) (S N)), (forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < 1)%nat}),
     D (AddConnect 1 M (inr x)) (AddConnect 1 N (inl y)) = 0) -> Mmult Rfield N M N
  (MTranspose Rfield M N
     (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) =>
      D (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y))))
  (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) =>
   D (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y))) = (fun (x y : {n : nat | (n < N)%nat}) => Mmult Rfield (S N) M (S N) (MTranspose Rfield M (S N)
     (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) =>
      D (AddConnect 1 M (inr x)) y))
  (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) =>
   D (AddConnect 1 M (inr x)) y) (AddConnect 1 N (inr x)) (AddConnect 1 N (inr y)))).
move=> H10.
rewrite (H10 A H7).
rewrite (H10 B H8).
suff: (Mmult Rfield (S N) M (S N)
   (MTranspose Rfield M (S N)
      (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat})
       => A (AddConnect 1 M (inr x)) y))
   (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) =>
    A (AddConnect 1 M (inr x)) y) = Mmult Rfield (S N) M (S N)
   (MTranspose Rfield M (S N)
      (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat})
       => B (AddConnect 1 M (inr x)) y))
   (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) =>
    B (AddConnect 1 M (inr x)) y)).
move=> H11.
rewrite H11.
reflexivity.
rewrite - (Mplus_O_l Rfield (S N) (S N) (Mmult Rfield (S N) M (S N)
  (MTranspose Rfield M (S N)
     (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) =>
      A (AddConnect 1 M (inr x)) y))
  (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) =>
   A (AddConnect 1 M (inr x)) y))).
rewrite - (Mplus_O_l Rfield (S N) (S N) (Mmult Rfield (S N) M (S N)
  (MTranspose Rfield M (S N)
     (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) =>
      B (AddConnect 1 M (inr x)) y))
  (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) =>
   B (AddConnect 1 M (inr x)) y))).
rewrite - (Mplus_opp_r Rfield (S N) (S N) (Mmult Rfield (S N) 1 (S N)
     (MTranspose Rfield 1 (S N)
        (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat})
         => A (AddConnect 1 M (inl x)) y))
     (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) =>
      A (AddConnect 1 M (inl x)) y))).
rewrite (Mplus_comm Rfield (S N) (S N) (Mmult Rfield (S N) 1 (S N)
     (MTranspose Rfield 1 (S N)
        (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat})
         => A (AddConnect 1 M (inl x)) y))
     (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) =>
      A (AddConnect 1 M (inl x)) y))).
rewrite Mplus_assoc.
rewrite Mplus_assoc.
suff: (Mplus Rfield (S N) (S N)
     (Mmult Rfield (S N) 1 (S N)
        (MTranspose Rfield 1 (S N)
           (fun (x : {n : nat | (n < 1)%nat})
              (y : {n : nat | (n < S N)%nat}) =>
            A (AddConnect 1 M (inl x)) y))
        (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat})
         => A (AddConnect 1 M (inl x)) y))
     (Mmult Rfield (S N) M (S N)
        (MTranspose Rfield M (S N)
           (fun (x : {n : nat | (n < M)%nat})
              (y : {n : nat | (n < S N)%nat}) =>
            A (AddConnect 1 M (inr x)) y))
        (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat})
         => A (AddConnect 1 M (inr x)) y)) = Mplus Rfield (S N) (S N)
     (Mmult Rfield (S N) 1 (S N)
        (MTranspose Rfield 1 (S N)
           (fun (x : {n : nat | (n < 1)%nat})
              (y : {n : nat | (n < S N)%nat}) =>
            A (AddConnect 1 M (inl x)) y))
        (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat})
         => A (AddConnect 1 M (inl x)) y))
     (Mmult Rfield (S N) M (S N)
        (MTranspose Rfield M (S N)
           (fun (x : {n : nat | (n < M)%nat})
              (y : {n : nat | (n < S N)%nat}) =>
            B (AddConnect 1 M (inr x)) y))
        (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat})
         => B (AddConnect 1 M (inr x)) y))).
move=> H11.
rewrite H11.
reflexivity.
suff: ((fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat})
         => A (AddConnect 1 M (inl x)) y) = (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat})
         => B (AddConnect 1 M (inl x)) y)).
move=> H12.
rewrite {3} H12.
rewrite {3} H12.
suff: (forall (D : Matrix Rfield (S M) (S N)), Mplus Rfield (S N) (S N)
  (Mmult Rfield (S N) 1 (S N)
     (MTranspose Rfield 1 (S N)
        (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat})
         => D (AddConnect 1 M (inl x)) y))
     (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat}) =>
      D (AddConnect 1 M (inl x)) y))
  (Mmult Rfield (S N) M (S N)
     (MTranspose Rfield M (S N)
        (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat})
         => D (AddConnect 1 M (inr x)) y))
     (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) =>
      D (AddConnect 1 M (inr x)) y)) = Mmult Rfield (S N) (S M) (S N) (MTranspose Rfield (S M) (S N) D) D).
move=> H13.
rewrite (H13 A).
rewrite (H13 B).
apply H5.
move=> D.
suff: (D = MBlockH Rfield 1 M (S N) (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < S N)%nat})
         => D (AddConnect 1 M (inl x)) y) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat})
         => D (AddConnect 1 M (inr x)) y)).
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
suff: ((fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < S N)%nat}) =>
    D (AddConnect 1 M (inr x)) y) = MBlockW Rfield M 1 N (MO Rfield M 1) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) =>
      D (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y)))).
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
suff: (forall (D : Matrix Rfield (S M) (S N)), UpperTriangularNormalFormR (S M) (S N) D -> (forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < 1)%nat}),
     D (AddConnect 1 M (inr x)) (AddConnect 1 N (inl y)) = 0) -> forall (x y : {n : nat | (n < 1)%nat}), D (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) * D (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) = Mmult Rfield (S N) (S M) (S N) (MTranspose Rfield (S M) (S N) D) D (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N)))).
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
suff: (forall (D : Matrix Rfield (S M) (S N)), (D (exist (fun n : nat => (n < S M)%nat) 0%nat
           (le_n_S 0 M (le_0_n M))) (exist (fun n : nat => (n < S N)%nat) 0%nat
           (le_n_S 0 N (le_0_n N))) > 0) -> (forall (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < 1)%nat}),
     D (AddConnect 1 M (inr x)) (AddConnect 1 N (inl y)) = 0) -> D (AddConnect 1 M (inl x))
  (exist (fun n : nat => (n < S N)%nat) 0%nat (le_n_S 0 N (le_0_n N))) *
D (AddConnect 1 M (inl x)) (AddConnect 1 N (inr y0)) = Mmult Rfield (S N) (S M) (S N) (MTranspose Rfield (S M) (S N) D) D (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) (AddConnect 1 N (inr y0))).
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
suff: (A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) *
A (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) =
B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y)) *
B (AddConnect 1 M (inl x)) (AddConnect 1 N (inl y))).
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
suff: (AddConnect 1 N (inl y) = (exist (fun (n : nat) => (n < S N)%nat) 0%nat
        (le_n_S 0 N (le_0_n N)))).
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
suff: ((exist (fun (n : nat) => (n < S N)%nat) 0%nat
        (le_n_S 0 N (le_0_n N))) = (AddConnect 1 N (inl (exist (fun (n : nat) => (n < 1)%nat) 0%nat
        (le_n 1))))).
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

Lemma HouseholderRSig : forall (N : nat) (x y : {n : nat | (n < N)%nat} -> R), RnNorm N x = RnNorm N y -> {Q : Matrix Rfield N N | OrthogonalMatrix N Q /\ Mmult Rfield N N 1 Q (MVectorToMatrix Rfield N x) = MVectorToMatrix Rfield N y /\ Mmult Rfield N N 1 Q (MVectorToMatrix Rfield N y) = MVectorToMatrix Rfield N x}.
Proof.
suff: (forall (N : nat) (x y : {n : nat | (n < N)%nat} -> R),
RnInnerProduct N x y = 0 ->
{Q : Matrix Rfield N N
| OrthogonalMatrix N Q /\
  Mmult Rfield N N 1 Q (MVectorToMatrix Rfield N x) =
  MVectorToMatrix Rfield N x /\
  Mmult Rfield N N 1 Q (MVectorToMatrix Rfield N y) =
  Mopp Rfield N 1 (MVectorToMatrix Rfield N y)}).
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
rewrite (Proposition_4_2_1_1 N).
rewrite (Proposition_4_2_1_2 N).
rewrite (Proposition_4_2_1_2 N).
rewrite - Rplus_assoc.
rewrite (Rplus_assoc (RnInnerProduct N x x)).
rewrite (Proposition_4_2_3 N y x).
rewrite - (Proposition_4_2_1_2 N x).
rewrite (Rnplus_comm N (Rnopp N y)).
rewrite (Rnplus_opp_r N y).
rewrite (RnInnerProductDefinition N x (RnO N)).
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
rewrite - (Mplus_assoc Rfield N N (VMmult Rfield N N (- (2 / RnInnerProduct N y y))
        (Mmult Rfield N 1 N (MVectorToMatrix Rfield N y)
           (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y))))).
rewrite - (VMmult_plus_distr_r Rfield N N (- (2 / RnInnerProduct N y y)) (- (2 / RnInnerProduct N y y))).
suff: (Mmult Rfield N N N
        (VMmult Rfield N N (- (2 / RnInnerProduct N y y))
           (Mmult Rfield N 1 N (MVectorToMatrix Rfield N y)
              (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y))))
        (VMmult Rfield N N (- (2 / RnInnerProduct N y y))
           (Mmult Rfield N 1 N (MVectorToMatrix Rfield N y)
              (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y)))) = Mopp Rfield N N (VMmult Rfield N N
        (Fadd Rfield (- (2 / RnInnerProduct N y y))
           (- (2 / RnInnerProduct N y y)))
        (Mmult Rfield N 1 N (MVectorToMatrix Rfield N y)
           (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y))))).
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
suff: (Mmult Rfield 1 1 N
        (Mmult Rfield 1 N 1
           (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y))
           (MVectorToMatrix Rfield N y))
        (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y)) = VMmult Rfield 1 N (RnInnerProduct N y y)
        (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y))).
move=> H3.
rewrite H3.
rewrite (VMmult_assoc_r Rfield N 1 N (RnInnerProduct N y y)).
rewrite (VMmult_assoc_reverse Rfield N N).
suff: (Fmul Rfield
     (Fmul Rfield (- (2 / RnInnerProduct N y y))
        (- (2 / RnInnerProduct N y y))) (RnInnerProduct N y y) = - (Fadd Rfield (- (2 / RnInnerProduct N y y))
        (- (2 / RnInnerProduct N y y)))).
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
apply (Proposition_4_2_4_2 N y H4).
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> w.
unfold Mmult at 1.
suff: (exist (Finite (Count 1)) (Full_set {n : nat | (n < 1)%nat})
     (CountFinite 1) = FiniteSingleton (Count 1) h).
move=> H3.
rewrite H3.
rewrite MySumF2Singleton.
apply Rmult_eq_compat_r.
unfold Mmult.
rewrite RnInnerProductDefinition.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < N)%nat}
  (exist (Finite {n : nat | (n < N)%nat}) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H7.
reflexivity.
apply H6.
apply H6.
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
suff: (Mmult Rfield 1 N 1
           (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y))
           (MVectorToMatrix Rfield N x) = MO Rfield 1 1).
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
rewrite RnInnerProductDefinition.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < N)%nat}
  (exist (Finite {n : nat | (n < N)%nat}) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H3 H4 H5 H6.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H6.
rewrite Rmult_comm.
reflexivity.
apply H5.
apply H5.
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
suff: (exist (Finite (Count 1)) (Full_set {n : nat | (n < 1)%nat})
     (CountFinite 1) = FiniteSingleton (Count 1) w).
move=> H3.
rewrite H3.
rewrite MySumF2Singleton.
suff: (Mmult Rfield 1 N 1
           (MTranspose Rfield N 1 (MVectorToMatrix Rfield N y))
           (MVectorToMatrix Rfield N y) w w = RnInnerProduct N y y).
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
apply (H2 (Proposition_4_2_4_2 N y H5)).
unfold Mmult.
rewrite RnInnerProductDefinition.
unfold Count.
apply (FiniteSetInduction {n : nat | (n < N)%nat}
  (exist (Finite {n : nat | (n < N)%nat}) (Full_set {n : nat | (n < N)%nat}) (CountFinite N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H7.
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

Definition HouseholderR (N : nat) (x y : {n : nat | (n < N)%nat} -> R) (H : RnNorm N x = RnNorm N y) := proj1_sig (HouseholderRSig N x y H).

Lemma MmultILRSame : forall (f : Field) (N : nat) (A B : Matrix f N N), Mmult f N N N A B = MI f N <-> Mmult f N N N B A = MI f N .
Proof.
suff: (forall (f : Field) (N : nat) (A B : Matrix f N N),
Mmult f N N N A B = MI f N -> Mmult f N N N B A = MI f N).
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

Lemma QRStrong1 : forall (M N : nat) (A : Matrix Rfield M N), exists (Q : Matrix Rfield M M), (OrthogonalMatrix M Q) /\ exists (U : Matrix Rfield M N), UpperTriangularNormalFormR M N U /\ A = Mmult Rfield M M N Q U.
Proof.
suff: (forall (M N : nat) (A : Matrix Rfield M N),
exists (Q : Matrix Rfield M M),
  OrthogonalMatrix M Q /\
     UpperTriangularNormalFormR M N (Mmult Rfield M M N Q A)).
move=> H1 M N A.
elim (H1 M N A).
move=> Q H2.
exists (MTranspose Rfield M M Q).
apply conj.
unfold OrthogonalMatrix.
rewrite (MTransTrans Rfield M M Q).
suff: (MTranspose Rfield M M Q = InvMatrix Rfield M Q).
move=> H4.
rewrite H4.
apply (InvMatrixMultR Rfield M Q).
apply (proj2 (RegularInvLExistRelation Rfield M Q)).
exists (MTranspose Rfield M M Q).
apply (proj1 H2).
apply (InvMatrixMultUniqueLStrong Rfield M Q (MTranspose Rfield M M Q) (proj1 H2)).
exists (Mmult Rfield M M N Q A).
apply conj.
apply (proj2 H2).
rewrite - (Mmult_assoc Rfield M M M N).
rewrite (proj1 H2).
rewrite (Mmult_I_l Rfield M N A).
reflexivity.
elim.
move=> N A.
exists (MI Rfield O).
apply conj.
unfold OrthogonalMatrix.
rewrite (MTransI Rfield O).
apply (Mmult_I_r Rfield O O (MI Rfield O)).
apply conj.
move=> x.
elim (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) (proj2_sig x)).
move=> x.
elim (le_not_lt O (proj1_sig x) (le_0_n (proj1_sig x)) (proj2_sig x)).
move=> M H1.
elim.
move=> A.
exists (MI Rfield (S M)).
apply conj.
unfold OrthogonalMatrix.
rewrite (MTransI Rfield (S M)).
apply (Mmult_I_r Rfield (S M) (S M) (MI Rfield (S M))).
apply conj.
move=> x y.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) (proj2_sig y)).
move=> x y.
elim (le_not_lt O (proj1_sig y) (le_0_n (proj1_sig y)) (proj2_sig y)).
move=> N H2 A.
elim (classic (MTranspose Rfield (S M) (S N) A (exist (fun (n : nat) => (n < S N)%nat) O (le_n_S O N (le_0_n N))) = RnO (S M))).
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
apply (MySumF2O {n : nat | (n < S M)%nat} (exist (Finite (Count (S M))) (Full_set {n : nat | (n < S M)%nat})
     (CountFinite (S M))) (FPCM Rfield)).
move=> u H5.
suff: (A u (AddConnect 1 N (inl y0)) = MTranspose Rfield (S M) (S N) A
       (exist (fun (n : nat) => (n < S N)%nat) O
          (le_n_S 0 N (le_0_n N))) u).
move=> H6.
rewrite H6.
rewrite H3.
apply (Rmult_0_r (Q x u)).
suff: ((exist (fun (n : nat) => (n < S N)%nat) O
          (le_n_S 0 N (le_0_n N))) = AddConnect 1 N (inl y0)).
move=> H6.
rewrite H6.
reflexivity.
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
right.
apply (MySumF2O {n : nat | (n < S M)%nat} (exist (Finite (Count (S M))) (Full_set {n : nat | (n < S M)%nat})
     (CountFinite (S M))) (FPCM Rfield)).
move=> u H6.
suff: (A u (AddConnect 1 N (inl y0)) = MTranspose Rfield (S M) (S N) A
       (exist (fun (n : nat) => (n < S N)%nat) O
          (le_n_S 0 N (le_0_n N))) u).
move=> H7.
rewrite H7.
rewrite H3.
apply (Rmult_0_r (Q x u)).
suff: ((exist (fun (n : nat) => (n < S N)%nat) O
          (le_n_S 0 N (le_0_n N))) = AddConnect 1 N (inl y0)).
move=> H7.
rewrite H7.
reflexivity.
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
elim (HouseholderRSig (S M) (MTranspose Rfield (S M) (S N) A
       (exist (fun (n : nat) => (n < S N)%nat) O
          (le_n_S 0 N (le_0_n N)))) (fun (m : Count (S M)) => match AddConnectInv 1 M m with 
  | inl _ => RnNorm (S M) (MTranspose Rfield (S M) (S N) A
       (exist (fun (n : nat) => (n < S N)%nat) O
          (le_n_S 0 N (le_0_n N))))
  | inr _ => 0
end)).
move=> Q1 H4.
elim (H1 N (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat}) => Mmult Rfield (S M) (S M) (S N) Q1 A (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y)))).
move=> Q2 H5.
exists (Mmult Rfield (S M) (S M) (S M) (MBlockH Rfield 1 M (S M) (MBlockW Rfield 1 1 M (MI Rfield 1) (MO Rfield 1 M)) (MBlockW Rfield M 1 M (MO Rfield M 1) Q2)) Q1).
apply conj.
apply (OrthogonalMatrixChain (S M)).
unfold OrthogonalMatrix.
rewrite (MBlockHTranspose Rfield 1 M (S M)).
rewrite (MBlockWTranspose Rfield 1 1 M).
rewrite (MBlockWTranspose Rfield M 1 M).
rewrite (MBlockHWMult Rfield (S M) 1 M (S M)).
rewrite (MTransI Rfield 1).
rewrite (MTransO Rfield 1 M).
rewrite (MBlockHMult Rfield 1 M 1 (S M)).
rewrite (MBlockHMult Rfield 1 M M (S M)).
rewrite (MBlockWMult Rfield 1 1 1 M).
rewrite (MBlockWMult Rfield M 1 1 M).
rewrite (MBlockWMult Rfield 1 M 1 M).
rewrite (MBlockWMult Rfield M M 1 M).
rewrite (Mmult_I_l Rfield 1 1 (MI Rfield 1)).
rewrite (Mmult_I_l Rfield 1 M (MO Rfield 1 M)).
rewrite (Mmult_I_r Rfield M 1 (MO Rfield M 1)).
rewrite (Mmult_O_r Rfield M 1 M (MO Rfield M 1)).
rewrite (Mmult_O_r Rfield 1 M 1).
rewrite (MTransO Rfield M 1).
rewrite (Mmult_O_l Rfield 1 M M Q2).
rewrite (Mmult_O_r Rfield M M 1 (MTranspose Rfield M M Q2)).
rewrite (proj1 H5).
rewrite (MBlockHPlus Rfield 1 M (S M)).
rewrite (MBlockWPlus Rfield 1 1 M).
rewrite (MBlockWPlus Rfield M 1 M).
rewrite (Mplus_O_l Rfield 1 M (MO Rfield 1 M)).
rewrite (Mplus_O_l Rfield M 1 (MO Rfield M 1)).
rewrite (Mplus_O_l Rfield M M (MI Rfield M)).
rewrite (Mplus_comm Rfield 1 1).
rewrite (Mplus_O_l Rfield 1 1 (MI Rfield 1)).
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
move=> H6.
elim (lt_irrefl (proj1_sig x0)).
apply (le_trans (S (proj1_sig x0)) 1 (proj1_sig x0)).
apply (proj2_sig x0).
rewrite H6.
apply (le_plus_l 1 (proj1_sig y0)).
move=> H6.
reflexivity.
move=> x0.
elim (AddConnectInv 1 M y).
move=> y0.
unfold MI.
rewrite - (proj2 (AddConnectNature 1 M) x0).
rewrite - (proj1 (AddConnectNature 1 M) y0).
elim (Nat.eq_dec (1 + proj1_sig x0) (proj1_sig y0)).
move=> H6.
elim (lt_irrefl (1 + proj1_sig x0)).
apply (le_trans (S (1 + proj1_sig x0)) 1 (1 + proj1_sig x0)).
rewrite H6.
apply (proj2_sig y0).
apply (le_plus_l 1 (proj1_sig x0)).
move=> H6.
reflexivity.
move=> y0.
unfold MI.
rewrite - (proj2 (AddConnectNature 1 M) x0).
rewrite - (proj2 (AddConnectNature 1 M) y0).
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y0)).
move=> H6.
elim (Nat.eq_dec (1 + proj1_sig x0) (1 + proj1_sig y0)).
move=> H7.
reflexivity.
elim.
rewrite H6.
reflexivity.
move=> H6.
elim (Nat.eq_dec (1 + proj1_sig x0) (1 + proj1_sig y0)).
move=> H7.
elim H6.
apply (plus_reg_l (proj1_sig x0) (proj1_sig y0) 1 H7).
move=> H7.
reflexivity.
apply (proj1 H4).
rewrite (Mmult_assoc Rfield (S M) (S M) (S M) (S N)).
suff: (exists (r : R), r > 0 /\ exists (a : Matrix Rfield 1 N), Mmult Rfield (S M) (S M) (S N) Q1 A = MBlockH Rfield 1 M (S N) (MBlockW Rfield 1 1 N (fun (x y : {n : nat | (n < 1)%nat}) => r) a) (MBlockW Rfield M 1 N (MO Rfield M 1) (fun (x : {n : nat | (n < M)%nat}) (y : {n : nat | (n < N)%nat})
           =>
           Mmult Rfield (S M) (S M) (S N) Q1 A (AddConnect 1 M (inr x))
             (AddConnect 1 N (inr y))))).
elim.
move=> r H6.
elim (proj2 H6).
move=> a H7.
rewrite H7.
rewrite (MBlockHWWHSame Rfield 1 M 1 M).
rewrite (MBlockHWMult Rfield (S M) 1 M (S N)).
rewrite (MBlockHMult Rfield 1 M 1 (S N)).
rewrite (MBlockHMult Rfield 1 M M (S N)).
rewrite (MBlockWMult Rfield 1 1 1 N).
rewrite (MBlockWMult Rfield 1 M 1 N).
rewrite (MBlockWMult Rfield M 1 1 N).
rewrite (MBlockWMult Rfield M M 1 N).
rewrite (MBlockHPlus Rfield 1 M (S N)).
rewrite (MBlockWPlus Rfield 1 1 N).
rewrite (MBlockWPlus Rfield M 1 N).
rewrite (Mmult_I_l Rfield 1 1).
rewrite (Mmult_O_l Rfield 1 M 1 (MO Rfield M 1)).
rewrite (Mmult_I_l Rfield 1 N a).
rewrite (Mmult_O_l Rfield 1 M N).
rewrite (Mmult_O_l Rfield M 1 1).
rewrite (Mmult_O_r Rfield M M 1 Q2).
rewrite (Mmult_O_l Rfield M 1 N a).
rewrite (Mplus_O_l Rfield M 1 (MO Rfield M 1)).
rewrite (Mplus_O_l Rfield M N).
rewrite (Mplus_comm Rfield 1 1).
rewrite (Mplus_O_l Rfield 1 1).
rewrite (Mplus_comm Rfield 1 N a (MO Rfield 1 N)).
rewrite (Mplus_O_l Rfield 1 N a).
apply conj.
move=> x.
rewrite - (proj2 (AddConnectInvRelation 1 M) x).
elim (AddConnectInv 1 M x).
move=> x0 y H8 z.
rewrite - (proj1 (AddConnectNature 1 M) x0).
suff: (proj1_sig x0 = O).
move=> H9.
rewrite H9.
move=> H10.
elim (le_not_lt O (proj1_sig z) (le_0_n (proj1_sig z)) H10).
elim (le_lt_or_eq (proj1_sig x0) O (le_S_n (proj1_sig x0) O (proj2_sig x0))).
move=> H9.
elim (le_not_lt O (proj1_sig x0) (le_0_n (proj1_sig x0)) H9).
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
move=> H8 z.
rewrite - (proj2 (AddConnectInvRelation 1 M) z).
elim (AddConnectInv 1 M z).
move=> z0 H9.
exists (AddConnect 1 N (inl z0)).
apply conj.
rewrite - (proj1 (AddConnectNature 1 N) z0).
rewrite - (proj2 (AddConnectNature 1 N) y0).
apply (le_trans (S (proj1_sig z0)) 1 (1 + proj1_sig y0) (proj2_sig z0) (le_plus_l 1 (proj1_sig y0))).
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 M) (inl z0)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inl z0)).
apply (Rgt_not_eq r 0 (proj1 H6)).
move=> z0.
rewrite - (proj2 (AddConnectNature 1 M) x0).
rewrite - (proj2 (AddConnectNature 1 N) y0).
rewrite - (proj2 (AddConnectNature 1 M) z0).
move=> H9.
elim (proj1 (proj2 H5) x0 y0 H8 z0 (plus_lt_reg_l (proj1_sig z0) (proj1_sig x0) 1 H9)).
move=> w0 H10.
exists (AddConnect 1 N (inr w0)).
apply conj.
rewrite - (proj2 (AddConnectNature 1 N) w0).
apply (plus_lt_compat_l (proj1_sig w0) (proj1_sig y0) 1 (proj1 H10)).
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 M) (inr z0)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inr w0)).
apply (proj2 H10).
move=> x.
rewrite - (proj2 (AddConnectInvRelation 1 M) x).
elim (AddConnectInv 1 M x).
move=> x0 y.
rewrite - (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0 H8.
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 M) (inl x0)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inl y0)).
left.
apply (proj1 H6).
move=> y0.
unfold MBlockH at 1.
rewrite (proj1 (AddConnectInvRelation 1 M) (inl x0)).
unfold MBlockW at 1.
move=> H8.
apply False_ind.
apply (Rgt_not_eq r 0 (proj1 H6)).
suff: (match AddConnectInv 1 N (AddConnect 1 N (inl x0)) with
  | inl _ => r
  | inr y0 => a x0 y0
end = 0).
rewrite (proj1 (AddConnectInvRelation 1 N) (inl x0)).
apply.
apply (H8 (AddConnect 1 N (inl x0))).
rewrite - (proj1 (AddConnectNature 1 N) x0).
rewrite - (proj2 (AddConnectNature 1 N) y0).
apply (le_trans (S (proj1_sig x0)) 1 (1 + proj1_sig y0) (proj2_sig x0) (le_plus_l 1 (proj1_sig y0))).
move=> x0 y.
rewrite - (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0 H8.
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 M) (inr x0)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inl y0)).
right.
reflexivity.
move=> y0 H8.
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 M) (inr x0)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inr y0)).
apply (proj2 (proj2 H5) x0 y0).
move=> z0 H9.
suff: (MBlockH Rfield 1 M (S N)
       (MBlockW Rfield 1 1 N (fun (x y : {n : nat | (n < 1)%nat}) => r) a)
       (MBlockW Rfield M 1 N (MO Rfield M 1)
          (Mmult Rfield M M N Q2
             (fun (x : {n : nat | (n < M)%nat})
                (y : {n : nat | (n < N)%nat}) =>
              Mmult Rfield (S M) (S M) (S N) Q1 A 
                (AddConnect 1 M (inr x)) (AddConnect 1 N (inr y)))))
       (AddConnect 1 M (inr x0)) (AddConnect 1 N (inr z0)) = 0).
unfold MBlockH.
unfold MBlockW.
rewrite (proj1 (AddConnectInvRelation 1 M) (inr x0)).
rewrite (proj1 (AddConnectInvRelation 1 N) (inr z0)).
apply.
apply (H8 (AddConnect 1 N (inr z0))).
rewrite - (proj2 (AddConnectNature 1 N) y0).
rewrite - (proj2 (AddConnectNature 1 N) z0).
apply (plus_lt_compat_l (proj1_sig z0) (proj1_sig y0) 1 H9).
exists (RnNorm (S M)
              (MTranspose Rfield (S M) (S N) A
                 (exist (fun (n : nat) => (n < S N)%nat) O
                    (le_n_S 0 N (le_0_n N))))).
apply conj.
elim (proj1 (RnNormNature (S M) (MTranspose Rfield (S M) (S N) A
                 (exist (fun (n : nat) => (n < S N)%nat) O
                    (le_n_S 0 N (le_0_n N)))))).
apply.
move=> H6.
elim H3.
apply (Proposition_4_4_3_2 (S M) (MTranspose Rfield (S M) (S N) A
                 (exist (fun (n : nat) => (n < S N)%nat) O
                    (le_n_S 0 N (le_0_n N)))) H6).
exists (fun (x : {n : nat | (n < 1)%nat}) (y : {n : nat | (n < N)%nat}) =>
        Mmult Rfield (S M) (S M) (S N) Q1 A (AddConnect 1 M (inl x))
          (AddConnect 1 N (inr y))).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
unfold MBlockH.
unfold MBlockW.
rewrite - {1} (proj2 (AddConnectInvRelation 1 N) y).
elim (AddConnectInv 1 N y).
move=> y0.
suff: (Mmult Rfield (S M) (S M) (S N) Q1 A x (AddConnect 1 N (inl y0)) = let temp := (fun (m : Count (S M)) =>
match AddConnectInv 1 M m with
| inl _ =>
    RnNorm (S M)
      (MTranspose Rfield (S M) (S N) A
         (exist (fun (n : nat) => (n < S N)%nat) 0%nat
            (le_n_S 0 N (le_0_n N))))
| inr x0 => MO Rfield M 1 x0 y0
end) in temp x).
apply.
rewrite - (proj1 (MVectorMatrixRelation Rfield (S M)) (fun (m : Count (S M)) =>
match AddConnectInv 1 M m with
| inl _ =>
    RnNorm (S M)
      (MTranspose Rfield (S M) (S N) A
         (exist (fun (n : nat) => (n < S N)%nat) 0%nat
            (le_n_S 0 N (le_0_n N))))
| inr x0 => MO Rfield M 1 x0 y0
end)).
rewrite - (proj1 (proj2 H4)).
simpl.
suff: (AddConnect 1 N (inl y0) = (exist (fun (n : nat) => (n < S N)%nat) 0%nat
            (le_n_S 0 N (le_0_n N)))).
move=> H6.
rewrite H6.
reflexivity.
apply sig_map.
rewrite - (proj1 (AddConnectNature 1 N) y0).
elim (le_lt_or_eq (proj1_sig y0) O (le_S_n (proj1_sig y0) O (proj2_sig y0))).
move=> H6.
elim (le_not_lt O (proj1_sig y0) (le_0_n (proj1_sig y0)) H6).
apply.
move=> y0.
rewrite - {1} (proj2 (AddConnectInvRelation 1 M) x).
elim (AddConnectInv 1 M x).
move=> H6.
reflexivity.
move=> H6.
reflexivity.
apply (RnNormNature2 (S M)).
apply conj.
apply (RnNormNature (S M)).
rewrite - (proj2 (RnNormNature (S M) (fun (m : Count (S M)) =>
   match AddConnectInv 1 M m with
   | inl _ =>
       RnNorm (S M)
         (MTranspose Rfield (S M) (S N) A
            (exist (fun (n : nat) => (n < S N)%nat) O
               (le_n_S 0 N (le_0_n N))))
   | inr _ => 0
   end))).
rewrite (RnInnerProductDefinition (S M) (fun (m : Count (S M)) =>
   match AddConnectInv 1 M m with
   | inl _ =>
       RnNorm (S M)
         (MTranspose Rfield (S M) (S N) A
            (exist (fun (n : nat) => (n < S N)%nat) O
               (le_n_S 0 N (le_0_n N))))
   | inr _ => 0
   end)).
rewrite (MySumF2Included (Count (S M)) (FiniteSingleton (Count (S M)) (exist (fun (n : nat) => (n < S M)%nat) O
               (le_n_S 0 M (le_0_n M))))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
suff: (exist (fun (n : nat) => (n < S M)%nat) O
               (le_n_S 0 M (le_0_n M)) = AddConnect 1 M (inl (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1)))).
move=> H4.
rewrite H4.
rewrite (proj1 (AddConnectInvRelation 1 M)).
apply (proj2 (RnNormNature (S M) (MTranspose Rfield (S M) (S N) A
     (exist (fun (n : nat) => (n < S N)%nat) O
        (le_n_S 0 N (le_0_n N)))))).
apply sig_map.
apply (proj1 (AddConnectNature 1 M) (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1))).
move=> u.
elim.
move=> u0.
rewrite - (proj2 (AddConnectInvRelation 1 M) u0).
elim (AddConnectInv 1 M u0).
move=> u1 H4 H5.
elim H4.
suff: (exist (fun (n : nat) => (n < S M)%nat) O
               (le_n_S 0 M (le_0_n M)) = AddConnect 1 M (inl u1)).
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
move=> u H4.
apply (Full_intro (Count (S M)) u).
Qed.

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

Lemma SingularDecompositionH : forall (M N : nat) (A : Matrix Rfield (M + N) M), exists (U : Matrix Rfield (M + N)%nat (M + N)%nat), (OrthogonalMatrix (M + N)%nat U) /\ exists (V : Matrix Rfield M M), (OrthogonalMatrix M V) /\ exists (sigma : {n : nat | (n < M)%nat} -> R), ((forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\ (forall (m1 m2 : {n : nat | (n < M)%nat}), (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) /\ A = Mmult Rfield (M + N)%nat (M + N)%nat M U (Mmult Rfield (M + N)%nat M M (MBlockH Rfield M N M (MDiag Rfield M sigma) (MO Rfield N M)) (MTranspose Rfield M M V))).
Proof.
suff: (forall (M N : nat) (A : Matrix Rfield (M + N) M),
exists (U : Matrix Rfield (M + N) (M + N)),
  OrthogonalMatrix (M + N) U /\
  (exists (V : Matrix Rfield M M),
     OrthogonalMatrix M V /\
     (exists (sigma : {n : nat | (n < M)%nat} -> R),
        (forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\
        A =
        Mmult Rfield (M + N) (M + N) M U
          (Mmult Rfield (M + N) M M
             (MBlockH Rfield M N M (MDiag Rfield M sigma) (MO Rfield N M))
             (MTranspose Rfield M M V))))).
move=> H1 M N A.
suff: (forall (k : nat), (k <= M)%nat -> exists (U : Matrix Rfield (M + N) (M + N)),
  OrthogonalMatrix (M + N) U /\ (exists (V : Matrix Rfield M M),
  OrthogonalMatrix M V /\
  (exists (sigma : {n : nat | (n < M)%nat} -> R),
     (forall (m : {n : nat | (n < M)%nat}), sigma m >= 0) /\
     (forall (m1 m2 : {n : nat | (n < M)%nat}),
      (proj1_sig m2 < k)%nat -> (proj1_sig m1 <= proj1_sig m2)%nat -> sigma m1 >= sigma m2) /\
(forall (m1 m2 : {n : nat | (n < M)%nat}),
      (proj1_sig m1 < k)%nat -> (proj1_sig m2 >= k)%nat -> sigma m1 >= sigma m2) /\
     A =
     Mmult Rfield (M + N) (M + N) M U
       (Mmult Rfield (M + N) M M
          (MBlockH Rfield M N M (MDiag Rfield M sigma) (MO Rfield N M))
          (MTranspose Rfield M M V))))).
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
exists (Mmult Rfield (M + N) (M + N) (M + N) U (ElementaryMatrixSwap Rfield (M + N) (AddConnect M N (inl (exist (fun (n : nat) => (n < M)%nat) k H3))) (AddConnect M N (inl m)))).
apply conj.
apply (OrthogonalMatrixChain (M + N)).
apply (proj1 H4).
unfold OrthogonalMatrix.
rewrite (ElementaryMatrixSwapTrans Rfield (M + N)).
rewrite - {1} (InvMatrixElementaryMatrixSwap Rfield (M + N)).
apply (InvMatrixMultL Rfield (M + N)).
elim (classic (k = proj1_sig m)).
move=> H8.
suff: (ElementaryMatrixSwap Rfield (M + N)
     (AddConnect M N (inl (exist (fun (n : nat) => (n < M)%nat) k H3)))
     (AddConnect M N (inl m)) = MI Rfield (M + N)).
move=> H9.
rewrite H9.
unfold RegularMatrix.
rewrite (DeterminantI Rfield (M + N)).
apply R1_neq_R0.
suff: (exist (fun (n : nat) => (n < M)%nat) k H3 = m).
move=> H9.
rewrite H9.
unfold ElementaryMatrixSwap.
unfold MI.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H10.
rewrite H10.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect M N (inl m)))).
move=> H11.
reflexivity.
move=> H11.
reflexivity.
move=> H10.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig (AddConnect M N (inl m)))).
move=> H11.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig (AddConnect M N (inl m)))).
move=> H12.
elim H10.
rewrite H12.
apply H11.
move=> H12.
reflexivity.
move=> H11.
reflexivity.
apply sig_map.
apply H8.
move=> H8.
unfold RegularMatrix.
rewrite (DeterminantElementaryMatrixSwap Rfield (M + N)).
simpl.
move=> H9.
apply R1_neq_R0.
rewrite - (Ropp_involutive 1).
rewrite H9.
apply Ropp_0.
rewrite - (proj1 (AddConnectNature M N)).
rewrite - (proj1 (AddConnectNature M N)).
apply H8.
exists (Mmult Rfield M M M V (ElementaryMatrixSwap Rfield M (exist (fun (n : nat) => (n < M)%nat) k H3) m)).
apply conj.
apply (OrthogonalMatrixChain M).
apply (proj1 H5).
unfold OrthogonalMatrix.
rewrite (ElementaryMatrixSwapTrans Rfield M).
rewrite - {1} (InvMatrixElementaryMatrixSwap Rfield M).
apply (InvMatrixMultL Rfield M).
elim (classic (k = proj1_sig m)).
move=> H8.
suff: (ElementaryMatrixSwap Rfield M
     (exist (fun (n : nat) => (n < M)%nat) k H3)
     m = MI Rfield M).
move=> H9.
rewrite H9.
unfold RegularMatrix.
rewrite (DeterminantI Rfield M).
apply R1_neq_R0.
suff: (exist (fun (n : nat) => (n < M)%nat) k H3 = m).
move=> H9.
rewrite H9.
unfold ElementaryMatrixSwap.
unfold MI.
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> y.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig y)).
move=> H10.
rewrite H10.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig m)).
move=> H11.
reflexivity.
move=> H11.
reflexivity.
move=> H10.
elim (Nat.eq_dec (proj1_sig x) (proj1_sig m)).
move=> H11.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig m)).
move=> H12.
elim H10.
rewrite H12.
apply H11.
move=> H12.
reflexivity.
move=> H11.
reflexivity.
apply sig_map.
apply H8.
move=> H8.
unfold RegularMatrix.
rewrite (DeterminantElementaryMatrixSwap Rfield M).
simpl.
move=> H9.
apply R1_neq_R0.
rewrite - (Ropp_involutive 1).
rewrite H9.
apply Ropp_0.
apply H8.
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
elim (excluded_middle_informative
    (m1 = exist (fun (n : nat) => (n < M)%nat) k H3)).
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
elim (excluded_middle_informative
    (m2 = exist (fun (n : nat) => (n < M)%nat) k H3)).
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
elim (excluded_middle_informative
    (m2 = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H11.
elim (excluded_middle_informative
    (m1 = exist (fun (n : nat) => (n < M)%nat) k H3)).
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
elim (excluded_middle_informative
    (m1 = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H10.
elim (excluded_middle_informative
    (m2 = exist (fun (n : nat) => (n < M)%nat) k H3)).
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
elim (excluded_middle_informative
    (m2 = exist (fun (n : nat) => (n < M)%nat) k H3)).
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
rewrite (MTransMult Rfield M M M V).
rewrite - (Mmult_assoc Rfield (M + N) M M M).
rewrite - (Mmult_assoc Rfield (M + N) (M + N) M M).
rewrite (Mmult_assoc Rfield (M + N) (M + N) (M + N) M).
rewrite (Mmult_assoc Rfield (M + N) (M + N) M M).
rewrite (proj2 (proj2 (proj2 H6))).
suff: (MBlockH Rfield M N M (MDiag Rfield M sigma) (MO Rfield N M) = Mmult Rfield (M + N) (M + N) M
        (ElementaryMatrixSwap Rfield (M + N)
           (AddConnect M N (inl (exist (fun (n : nat) => (n < M)%nat) k H3)))
           (AddConnect M N (inl m)))
        (Mmult Rfield (M + N) M M
           (MBlockH Rfield M N M
              (MDiag Rfield M
                 (fun (l : {n : nat | (n < M)%nat}) => match excluded_middle_informative (l = exist (fun (n : nat) => (n < M)%nat) k H3) with
  | left _ => sigma m
  | right _ => match excluded_middle_informative (l = m) with
    | left _ => sigma (exist (fun (n : nat) => (n < M)%nat) k H3)
    | right _ => sigma l
  end
end)) (MO Rfield N M))
           (MTranspose Rfield M M
              (ElementaryMatrixSwap Rfield M
                 (exist (fun (n : nat) => (n < M)%nat) k H3) m)))).
move=> H8.
rewrite H8.
reflexivity.
rewrite (ElementaryMatrixSwapTrans Rfield M).
rewrite (MBlockHMult Rfield M N M M).
rewrite (Mmult_O_l Rfield N M M).
rewrite (ElementaryMatrixSwapNatureR Rfield M M).
rewrite (ElementaryMatrixSwapNatureL Rfield (M + N) M).
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
move=> H8.
suff: (x0 = y).
move=> H9.
rewrite H9.
rewrite - (proj1 (AddConnectNature M N) y).
rewrite - (proj1 (AddConnectNature M N) (exist (fun (n : nat) => (n < M)%nat) k H3)).
elim (Nat.eq_dec (proj1_sig y)
    (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H10.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H11.
elim (excluded_middle_informative (m = m)).
move=> H12.
elim (excluded_middle_informative (m = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H13.
suff: (y = m).
move=> H14.
rewrite H14.
reflexivity.
rewrite H13.
apply sig_map.
apply H10.
move=> H13.
suff: (y = exist (fun (n : nat) => (n < M)%nat) k H3).
move=> H14.
rewrite H14.
reflexivity.
apply sig_map.
apply H10.
elim.
reflexivity.
elim.
reflexivity.
rewrite (proj1 (AddConnectInvRelation M N) (inl (exist (fun (n : nat) => (n < M)%nat) k H3))).
rewrite - (proj1 (AddConnectNature M N) m).
move=> H10.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig m)).
move=> H11.
elim (Nat.eq_dec (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))
    (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H12.
elim (excluded_middle_informative
    (exist (fun (n : nat) => (n < M)%nat) k H3 =
     exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H13.
suff: (y = m).
move=> H14.
rewrite H14.
reflexivity.
apply sig_map.
apply H11.
elim.
reflexivity.
elim.
reflexivity.
move=> H11.
rewrite (proj1 (AddConnectInvRelation M N) (inl y)).
elim (Nat.eq_dec (proj1_sig y) (proj1_sig y)).
move=> H12.
elim (excluded_middle_informative (y = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H13.
elim H10.
rewrite H13.
reflexivity.
move=> H13.
elim (excluded_middle_informative (y = m)).
move=> H14.
elim H11.
rewrite H14.
reflexivity.
move=> H14.
reflexivity.
elim.
reflexivity.
apply sig_map.
apply H8.
move=> H8.
rewrite - (proj1 (AddConnectNature M N) x0).
rewrite - (proj1 (AddConnectNature M N) (exist (fun (n : nat) => (n < M)%nat) k H3)).
elim (Nat.eq_dec (proj1_sig x0)
    (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H9.
elim (Nat.eq_dec (proj1_sig y)
    (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H10.
elim H8.
rewrite H10.
apply H9.
move=> H10.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig m)).
move=> H11.
elim (Nat.eq_dec (proj1_sig m)
    (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H12.
elim H10.
rewrite H11.
apply H12.
move=> H12.
reflexivity.
move=> H11.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig y)).
move=> H12.
elim H11.
rewrite H12.
reflexivity.
move=> H12.
reflexivity.
move=> H9.
rewrite (proj1 (AddConnectInvRelation M N) (inl (exist (fun (n : nat) => (n < M)%nat) k H3))).
rewrite - (proj1 (AddConnectNature M N) m).
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig m)).
move=> H10.
elim (Nat.eq_dec (proj1_sig y)
    (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H11.
elim (Nat.eq_dec (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))
    (proj1_sig m)).
move=> H12.
elim H9.
rewrite H10.
rewrite H12.
reflexivity.
move=> H12.
reflexivity.
move=> H11.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig m)).
move=> H12.
elim H8.
rewrite H12.
apply H10.
move=> H12.
elim (Nat.eq_dec (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))
    (proj1_sig y)).
move=> H13.
elim H11.
rewrite H13.
reflexivity.
move=> H13.
reflexivity.
move=> H10.
rewrite (proj1 (AddConnectInvRelation M N) (inl x0)).
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig m)).
move=> H11.
elim (H10 H11).
move=> H11.
elim (excluded_middle_informative
       (x0 = exist (fun (n : nat) => (n < M)%nat) k H3)).
move=> H12.
elim H9.
rewrite H12.
reflexivity.
move=> H12.
elim (Nat.eq_dec (proj1_sig x0)
      (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
move=> H13.
elim H12.
apply sig_map.
apply H13.
move=> H13.
elim (Nat.eq_dec (proj1_sig y)
    (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
reflexivity.
move=> H14.
elim (Nat.eq_dec (proj1_sig y) (proj1_sig m)).
move=> H15.
reflexivity.
move=> H15.
elim (Nat.eq_dec (proj1_sig x0) (proj1_sig y)).
move=> H16.
elim (H8 H16).
move=> H16.
reflexivity.
move=> x0.
rewrite - (proj1 (AddConnectNature M N) (exist (fun (n : nat) => (n < M)%nat) k H3)).
rewrite - (proj2 (AddConnectNature M N) x0).
elim (Nat.eq_dec (M + proj1_sig x0)
    (proj1_sig (exist (fun (n : nat) => (n < M)%nat) k H3))).
simpl.
move=> H8.
elim (le_not_lt M k).
rewrite - H8.
apply (le_plus_l M (proj1_sig x0)).
apply H3.
move=> H8.
rewrite - (proj1 (AddConnectNature M N) m).
elim (Nat.eq_dec (M + proj1_sig m)
    (proj1_sig m)).
simpl.
move=> H9.
elim (le_not_lt M (proj1_sig m)).
rewrite - H9.
apply (le_plus_l M (proj1_sig m)).
apply (proj2_sig m).
move=> H9.
elim (Nat.eq_dec (M + proj1_sig x0) (proj1_sig m)).
move=> H10.
elim (le_not_lt M (proj1_sig m)).
rewrite - H10.
apply (le_plus_l M (proj1_sig x0)).
apply (proj2_sig m).
move=> H10.
rewrite (proj1 (AddConnectInvRelation M N) (inr x0)).
reflexivity.
suff: (forall (k : nat), (k > O)%nat -> (k <= M)%nat -> exists (m : {n : nat | (n < M)%nat}),
  (proj1_sig m >= M - k)%nat /\
  (forall (l : {n : nat | (n < M)%nat}),
   (proj1_sig l >= M - k)%nat -> sigma m >= sigma l)).
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
elim (SymmetricTransformableToDiag M (Mmult Rfield M (M + N) M (MTranspose Rfield (M + N) M A) A)).
move=> V.
elim.
move=> sigma H1.
suff: (forall (m : {n : nat | (n < M)%nat}), sigma m >= 0).
move=> H2.
suff: (exists (U : Matrix Rfield (M + N) (M + N)), OrthogonalMatrix (M + N) U /\ A = Mmult Rfield (M + N) (M + N) M U (Mmult Rfield (M + N) M M (MBlockH Rfield M N M (MDiag Rfield M (fun (m : {n : nat | (n < M)%nat}) => MySqrt (exist (fun (r : R) => r >= 0) (sigma m) (H2 m)))) (MO Rfield N M)) (MTranspose Rfield M M V))).
elim.
move=> U H3.
exists U.
apply conj.
apply (proj1 H3).
exists V.
apply conj.
apply (proj1 H1).
exists (fun (m : {n : nat | (n < M)%nat}) =>
                 MySqrt (exist (fun (r : R) => r >= 0) (sigma m) (H2 m))).
apply conj.
move=> m.
apply (proj1 (MySqrtNature (exist (fun (r : R) => r >= 0) (sigma m) (H2 m)))).
apply (proj2 H3).
elim (QRStrong1 (M + N) M A).
move=> Q1.
elim.
move=> H3.
elim.
move=> U1 H4.
elim (QRStrong1 (M + N) M (Mmult Rfield (M + N) M M (MBlockH Rfield M N M (MDiag Rfield M (fun (m : {n : nat | (n < M)%nat}) => MySqrt (exist (fun (r : R) => r >= 0) (sigma m) (H2 m)))) (MO Rfield N M)) (MTranspose Rfield M M V))).
move=> Q2.
elim.
move=> H5.
elim.
move=> U2 H6.
exists (Mmult Rfield (M + N) (M + N) (M + N) Q1 (MTranspose Rfield (M + N) (M + N) Q2)).
apply conj.
apply (OrthogonalMatrixChain (M + N) Q1 (MTranspose Rfield (M + N) (M + N) Q2)).
apply H3.
apply (proj1 (MmultILRSame Rfield (M + N) (MTranspose Rfield (M + N) (M + N) Q2) Q2) H5).
rewrite (proj2 H6).
rewrite (Mmult_assoc Rfield (M + N) (M + N) (M + N) M Q1 (MTranspose Rfield (M + N) (M + N) Q2) (Mmult Rfield (M + N) (M + N) M Q2 U2)).
rewrite - (Mmult_assoc Rfield (M + N) (M + N) (M + N) M (MTranspose Rfield (M + N) (M + N) Q2) Q2 U2).
rewrite H5.
suff: (U2 = U1).
move=> H7.
rewrite H7.
rewrite (Mmult_I_l Rfield (M + N) M U1).
apply (proj2 H4).
apply (UpperTriangularNormalFormCholeskyR (M + N) M U2 U1 (proj1 H6) (proj1 H4)).
rewrite - {2} (Mmult_I_l Rfield (M + N) M U2).
rewrite - H5.
rewrite (Mmult_assoc Rfield (M + N) (M + N) (M + N) M
        (MTranspose Rfield (M + N) (M + N) Q2) Q2 U2).
rewrite - (Mmult_assoc Rfield M (M + N) (M + N) M).
rewrite - (MTransMult Rfield (M + N) (M + N) M Q2 U2).
rewrite - (proj2 H6).
rewrite (MTransMult Rfield (M + N) M M).
rewrite (MTransTrans Rfield M M V).
rewrite (Mmult_assoc Rfield M M (M + N) M).
rewrite - (Mmult_assoc Rfield M (M + N) M M).
suff: (Mmult Rfield M (M + N) M
        (MTranspose Rfield (M + N) M
           (MBlockH Rfield M N M
              (MDiag Rfield M
                 (fun (m : {n : nat | (n < M)%nat}) =>
                  MySqrt (exist (fun (r : R) => r >= 0) (sigma m) (H2 m))))
              (MO Rfield N M)))
        (MBlockH Rfield M N M
           (MDiag Rfield M
              (fun (m : {n : nat | (n < M)%nat}) =>
               MySqrt (exist (fun (r : R) => r >= 0) (sigma m) (H2 m))))
           (MO Rfield N M)) = MDiag Rfield M sigma).
move=> H7.
rewrite H7.
rewrite (proj2 H1).
rewrite - (Mmult_assoc Rfield M M M M V).
rewrite - (Mmult_assoc Rfield M M M M V).
rewrite (proj1 (MmultILRSame Rfield M (MTranspose Rfield M M V) V) (proj1 H1)).
rewrite (Mmult_I_l Rfield M M).
rewrite (Mmult_assoc Rfield M M M M).
rewrite (proj1 (MmultILRSame Rfield M (MTranspose Rfield M M V) V) (proj1 H1)).
rewrite (Mmult_I_r Rfield M M).
rewrite (proj2 H4).
rewrite (MTransMult Rfield (M + N) (M + N) M Q1 U1).
rewrite (Mmult_assoc Rfield M (M + N) (M + N) M).
rewrite - (Mmult_assoc Rfield (M + N) (M + N) (M + N) M).
rewrite H3.
rewrite (Mmult_I_l Rfield (M + N) M U1).
reflexivity.
rewrite (MBlockHTranspose Rfield M N M).
rewrite (MBlockHWMult Rfield M M N M).
rewrite (Mmult_O_r Rfield M N M).
rewrite (Mplus_comm Rfield M M).
rewrite (Mplus_O_l Rfield M M).
rewrite (MDiagTrans Rfield M).
rewrite (MDiagMult Rfield M).
suff: ((fun (m : {n : nat | (n < M)%nat}) =>
   Fmul Rfield (MySqrt (exist (fun (r : R) => r >= 0) (sigma m) (H2 m)))
     (MySqrt (exist (fun (r : R) => r >= 0) (sigma m) (H2 m)))) = sigma).
move=> H7.
rewrite H7.
reflexivity.
apply functional_extensionality.
move=> m.
simpl.
rewrite - (proj2 (MySqrtNature (exist (fun (r : R) => r >= 0) (sigma m) (H2 m)))).
reflexivity.
move=> m.
suff: (sigma m = MDiag Rfield M sigma m m).
move=> H2.
rewrite H2.
rewrite (proj2 H1).
rewrite (Mmult_assoc Rfield M (M + N) M M).
rewrite - (Mmult_assoc Rfield M M (M + N) M).
rewrite - (MTransMult Rfield (M + N) M M).
unfold Mmult at 1.
apply MySumF2Induction.
apply conj.
right.
reflexivity.
move=> cm u H3 H4.
rewrite - (Rplus_0_r 0).
apply (Rplus_ge_compat cm 0).
apply H4.
apply Formula_1_3.
unfold MDiag.
elim (Nat.eq_dec (proj1_sig m) (proj1_sig m)).
move=> H2.
reflexivity.
elim.
reflexivity.
unfold MSymmetric.
rewrite (MTransMult Rfield M (M + N) M).
rewrite (MTransTrans Rfield (M + N) M A).
reflexivity.
Qed.


