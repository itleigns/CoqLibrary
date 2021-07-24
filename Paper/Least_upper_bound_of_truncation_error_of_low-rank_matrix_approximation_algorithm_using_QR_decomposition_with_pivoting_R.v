Add LoadPath "Analysis/KaisekiNyuumonn" as Analysis.KaisekiNyuumonn.
Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "BasicProperty" as BasicProperty.
Add LoadPath "Tools" as Tools.
Add LoadPath "LibraryExtension" as LibraryExtension.
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
Require Import LinearAlgebra.SenkeiDaisuunoSekai.SenkeiDaisuunoSekai1.
Require Import Tools.MySum.
Local Open Scope R_scope.

Record RInner_Product_Space (V : VectorSpace Rfield) : Type := {
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


