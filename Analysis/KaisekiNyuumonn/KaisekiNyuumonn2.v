Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "Tools" as Tools.
Add LoadPath "BasicProperty" as BasicProperty.
Add LoadPath "Analysis/KaisekiNyuumonn" as Analysis.KaisekiNyuumonn.

From mathcomp Require Import ssreflect.
Require Import Reals.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Image.
Require Export QArith_base.
Require Export Rdefinitions.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import BasicProperty.MappingProperty.
Require Import MyAlgebraicStructure.MyField.
Require Import MyAlgebraicStructure.MyVectorSpace.
Require Import Tools.MySum.
Require Import Analysis.KaisekiNyuumonn.KaisekiNyuumonn1_1.
Require Import Analysis.KaisekiNyuumonn.KaisekiNyuumonn1_2.
Local Open Scope R_scope.

Definition DifferentiableR_R (A : Ensemble R) (f : R -> R) (r : R) := exists (c : R), limit_in R_met R_met (fun (h : R) => / h * (f (r + h) - f r)) (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 c.

Definition DifferentiableR_Rn (N : nat) (A : Ensemble R) (f : R -> Rn N) (r : R) := exists (c : Rn N), limit_in R_met (Rn_met N) (fun (h : R) => Rnmult N (/ h) (Rnminus N (f (r + h)) (f r))) (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 c.

Definition DifferentiableR_RRn (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (r : R) := exists (c : RRnT K), limit_in R_met (RRn_met K) (fun (h : R) => RRnmult K (/ h) (RRnminus K (f (r + h)) (f r))) (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 c.

Lemma DifferentialR_RRn_sub : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (r : R), ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r -> DifferentiableR_RRn K A f r -> {c : RRnT K | limit_in R_met (RRn_met K) (fun (h : R) => RRnmult K (/ h) (RRnminus K (f (r + h)) (f r))) (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 c}.
Proof.
move=> K A f r H1 H2.
apply constructive_definite_description.
apply (unique_existence (fun (x : RRnT K) => limit_in R_met (RRn_met K)
    (fun (h : R) => RRnmult K (/ h) (RRnminus K (f (r + h)) (f r)))
    (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 x)).
apply conj.
apply H2.
move=> x1 x2 H3 H4.
apply (Proposition_6_3 R_met (RRn_met K) (fun (h : R) => RRnmult K (/ h) (RRnminus K (f (r + h)) (f r)))
       (fun (h : R) => h <> 0 /\ In R A (r + h)) 0).
move=> eps H5.
elim (H1 eps H5).
move=> x H6.
exists (x - r).
apply conj.
unfold NeighborhoodMet.
unfold dist.
simpl.
unfold R_dist.
rewrite (Rminus_0_r (x - r)).
apply (proj1 H6).
apply conj.
apply (Rminus_eq_contra x r (proj1 (proj2 H6))).
rewrite (Rplus_comm r (x - r)).
rewrite (Rplus_assoc x (- r) r).
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_r x).
apply (proj2 (proj2 H6)).
apply H3.
apply H4.
Qed.

Definition DifferentialR_RRn (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_RRn K A f r) := proj1_sig (DifferentialR_RRn_sub K A f r H1 H2).

Definition DifferentialR_R : forall (A : Ensemble R) (f : R -> R) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_R A f r), R := DifferentialR_RRn R1K.

Definition DifferentialR_Rn (N : nat) : forall (A : Ensemble R) (f : R -> Rn N) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_Rn N A f r), Rn N := DifferentialR_RRn (RnK N).

Definition DifferentialR_RRnNature (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_RRn K A f r) : limit_in R_met (RRn_met K) (fun (h : R) => RRnmult K (/ h) (RRnminus K (f (r + h)) (f r))) (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 (DifferentialR_RRn K A f r H1 H2) := proj2_sig (DifferentialR_RRn_sub K A f r H1 H2).

Definition DifferentialR_RNature (A : Ensemble R) (f : R -> R) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_R A f r) : limit_in R_met R_met (fun (h : R) => / h * (f (r + h) - f r)) (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 (DifferentialR_R A f r H1 H2) := DifferentialR_RRnNature R1K A f r H1 H2.

Definition DifferentialR_RnNature (N : nat) (A : Ensemble R) (f : R -> Rn N) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_Rn N A f r) : limit_in R_met (Rn_met N) (fun (h : R) => Rnmult N (/ h) (Rnminus N (f (r + h)) (f r))) (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 (DifferentialR_Rn N A f r H1 H2) := DifferentialR_RRnNature (RnK N) A f r H1 H2.

Lemma DifferentialR_RRnNature2 : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_RRn K A f r) (c : RRnT K), limit_in R_met (RRn_met K) (fun (h : R) => RRnmult K (/ h) (RRnminus K (f (r + h)) (f r))) (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 c -> DifferentialR_RRn K A f r H1 H2 = c.
Proof.
move=> K A f r H1 H2 c H3.
apply (Proposition_6_3 R_met (RRn_met K) (fun (h : R) => RRnmult K (/ h) (RRnminus K (f (r + h)) (f r)))
       (fun (h : R) => h <> 0 /\ In R A (r + h)) 0).
move=> eps H4.
elim (H1 eps H4).
move=> x H5.
exists (x - r).
apply conj.
unfold NeighborhoodMet.
unfold dist.
simpl.
unfold R_dist.
rewrite (Rminus_0_r (x - r)).
apply (proj1 H5).
apply conj.
apply (Rminus_eq_contra x r (proj1 (proj2 H5))).
rewrite (Rplus_comm r (x - r)).
rewrite (Rplus_assoc x (- r) r).
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_r x).
apply (proj2 (proj2 H5)).
apply (DifferentialR_RRnNature K A f r H1 H2).
apply H3.
Qed.

Definition DifferentialR_RNature2 (A : Ensemble R) (f : R -> R) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_R A f r) : forall (c : R), limit_in R_met R_met (fun (h : R) => / h * (f (r + h) - f r)) (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 c -> (DifferentialR_R A f r H1 H2) = c := DifferentialR_RRnNature2 R1K A f r H1 H2.

Definition DifferentialR_RnNature2 (N : nat) (A : Ensemble R) (f : R -> Rn N) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_Rn N A f r) : forall (c : Rn N), limit_in R_met (Rn_met N) (fun (h : R) => Rnmult N (/ h) (Rnminus N (f (r + h)) (f r))) (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 c -> (DifferentialR_Rn N A f r H1 H2) = c := DifferentialR_RRnNature2 (RnK N) A f r H1 H2.

Lemma Proposition_1_1_1 : forall (N : nat) (A : Ensemble R) (f : R -> Rn N) (r : R), DifferentiableR_Rn N A f r <-> (forall (m : Count N), DifferentiableR_R A (fun (r : R) => f r m) r).
Proof.
move=> N A f r.
apply conj.
elim.
move=> c H1 m.
exists (c m).
apply (proj1 (Theorem_6_8_1 R_met N (fun (h : R) => Rnmult N (/ h) (Rnminus N (f (r + h)) (f r)))
       (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 c) H1 m).
move=> H1.
suff: (forall (n : nat), (n <= N)%nat ->
     exists (c : Rn N), forall (m : Count N), (proj1_sig m < n)%nat ->
       limit_in R_met R_met (fun h : R => / h * (f (r + h) m - f r m))
         (fun h : R => h <> 0 /\ In R A (r + h)) 0 (c m)).
move=> H2.
elim (H2 N (le_n N)).
move=> c H3.
exists c.
apply (proj2 (Theorem_6_8_1 R_met N (fun (h : R) => Rnmult N (/ h) (Rnminus N (f (r + h)) (f r)))
       (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 c)).
move=> n.
apply (H3 n (proj2_sig n)).
elim.
move=> H2.
exists (RnO N).
move=> m H3.
elim (le_not_lt O (proj1_sig m) (le_0_n (proj1_sig m)) H3).
move=> n H2 H3.
elim H2.
move=> x H4.
elim (H1 (exist (fun (m : nat) => (m < N)%nat) n H3)).
move=> y H5.
exists (fun (m : Count N) => match excluded_middle_informative (proj1_sig m = n) with
  | left _ => y
  | right _ => x m
end).
move=> m H6.
elim (le_lt_or_eq (proj1_sig m) n (le_S_n (proj1_sig m) n H6)).
move=> H7.
elim (excluded_middle_informative (proj1_sig m = n)).
move=> H8.
elim (lt_irrefl (proj1_sig m)).
rewrite {2} H8.
apply H7.
move=> H8.
apply (H4 m H7).
move=> H7.
elim (excluded_middle_informative (proj1_sig m = n)).
move=> H8.
suff: (m = (exist (fun (m : nat) => (m < N)%nat) n H3)).
move=> H9.
rewrite H9.
apply H5.
apply sig_map.
apply H7.
move=> H8.
apply (H4 m).
elim (le_lt_or_eq (proj1_sig m) n (le_S_n (proj1_sig m) n H6)).
move=> H9.
apply H9.
move=> H9.
elim (H8 H9).
apply (le_trans n (S n) N (le_S n n (le_n n)) H3).
Qed.

Lemma Proposition_1_1_2 : forall (N : nat) (A : Ensemble R) (f : R -> Rn N) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_Rn N A f r) (H3 : forall (m : Count N), DifferentiableR_R A (fun (r : R) => f r m) r), DifferentialR_Rn N A f r H1 H2 = (fun (m : Count N) => DifferentialR_R A (fun (r : R) => f r m) r H1 (H3 m)).
Proof.
move=> N A f r H1 H2 H3.
apply (DifferentialR_RnNature2 N A f r H1 H2).
apply (proj2 (Theorem_6_8_1 R_met N (fun (h : R) => Rnmult N (/ h) (Rnminus N (f (r + h)) (f r)))
       (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 (fun (m : Count N) => DifferentialR_R A (fun (r0 : R) => f r0 m) r H1 (H3 m)))).
move=> n.
apply (DifferentialR_RNature A (fun (x : R) => f x n) r H1 (H3 n)).
Qed.

Lemma Proposition_1_2 : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (r : R), DifferentiableR_RRn K A f r -> ContinuousMet R_met (RRn_met K) f A r.
Proof.
move=> K A f r.
elim.
move=> c H1 eps H2.
elim (H1 1 Rlt_0_1).
move=> dlt H3.
exists (Rmin dlt (/ (RRnNorm K c + 1) * eps * / (1 + 1))).
apply conj.
unfold Rmin.
elim (Rle_dec dlt (/ (RRnNorm K c + 1) * eps * / (1 + 1))).
move=> H4.
apply (proj1 H3).
move=> H4.
apply (Rmult_gt_0_compat (/ (RRnNorm K c + 1) * eps) (/ (1 + 1))).
apply (Rmult_gt_0_compat (/ (RRnNorm K c + 1)) eps).
apply (Rinv_0_lt_compat (RRnNorm K c + 1)).
apply (Rle_lt_trans 0 (RRnNorm K c) (RRnNorm K c + 1)).
apply (RRnNorm_pos K c).
apply (Rlt_plus_1 (RRnNorm K c)).
apply H2.
apply (Rinv_0_lt_compat (1 + 1)).
apply (Rlt_trans 0 1 (1 + 1) Rlt_0_1 (Rlt_plus_1 1)).
move=> x H4.
elim (classic (x = r)).
move=> H5.
rewrite (proj2 (dist_refl (RRn_met K) (f x) (f r))).
apply H2.
rewrite H5.
reflexivity.
move=> H5.
simpl.
apply (Rle_lt_trans (RRnNorm K (RRnminus K (f x) (f r))) ((RRnNorm K (RRnminus K (RRnminus K (f x) (f r)) (RRnmult K (x - r) c))) + RRnNorm K (RRnmult K (x - r) c))).
rewrite - {1} (RRnplus_0_l K (RRnminus K (f x) (f r))).
rewrite (RRnplus_comm K (RRnO K) (RRnminus K (f x) (f r))).
rewrite - (RRnplus_opp_r K (RRnmult K (x - r) c)).
rewrite (RRnplus_comm K (RRnmult K (x - r) c)).
rewrite - (RRnplus_assoc K (RRnminus K (f x) (f r))).
apply ((fun (K : RRn) => match K with
  | R1K => Rabs_triang
  | RnK N => Proposition_4_4_2_1_R N
end) : forall (K : RRn) (x y : RRnT K), RRnNorm K (RRnplus K x y) <= RRnNorm K x + RRnNorm K y).
rewrite ((fun (K : RRn) => match K with
  | R1K => Rabs_mult
  | RnK N => Proposition_4_4_1_R N
end) : forall (K : RRn) (r : R) (x : RRnT K), RRnNorm K (RRnmult K r x) = Rabs r * RRnNorm K x).
rewrite - (eps2 eps).
apply Rplus_lt_compat.
suff: (RRnminus K (RRnminus K (f x) (f r)) (RRnmult K (x - r) c)
=
RRnmult K (x - r) (RRnminus K (RRnmult K (/ (x - r)) (RRnminus K (f (r + (x - r))) (f r))) c)).
move=> H6.
rewrite H6.
rewrite ((fun (K : RRn) => match K with
  | R1K => Rabs_mult
  | RnK N => Proposition_4_4_1_R N
end) : forall (K : RRn) (r : R) (x : RRnT K), RRnNorm K (RRnmult K r x) = Rabs r * RRnNorm K x).
rewrite - (Rmult_1_l (eps * / 2)).
rewrite - (Rinv_r (Rabs (x - r))).
rewrite (Rmult_assoc (Rabs (x - r))).
apply (Rmult_lt_compat_l (Rabs (x - r))).
apply (Rabs_pos_lt (x - r)).
apply (Rminus_eq_contra x r H5).
apply (Rlt_trans (RRnNorm K
  (RRnminus K (RRnmult K (/ (x - r)) (RRnminus K (f (r + (x - r))) (f r))) c)) 1).
apply (proj2 H3 (x - r)).
apply conj.
apply conj.
apply (Rminus_eq_contra x r H5).
rewrite (Rplus_comm r (x - r)).
unfold Rminus.
rewrite (Rplus_assoc x (- r) r).
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_r x).
apply (proj1 H4).
unfold dist.
simpl.
unfold R_dist.
rewrite (Rminus_0_r (x - r)).
apply (Rlt_le_trans (Rabs (x - r)) (Rmin dlt (/ (RRnNorm K c + 1) * eps * / (1 + 1))) dlt).
apply (proj2 H4).
apply Rmin_l.
rewrite - (Rinv_l (Rabs (x - r))).
apply (Rmult_lt_compat_l (/ Rabs (x - r))).
apply Rinv_0_lt_compat.
apply (Rabs_pos_lt (x - r)).
apply (Rminus_eq_contra x r H5).
apply (Rlt_le_trans (Rabs (x - r)) (Rmin dlt (/ (RRnNorm K c + 1) * eps * / (1 + 1)))).
apply (proj2 H4).
apply (Rle_trans (Rmin dlt (/ (RRnNorm K c + 1) * eps * / (1 + 1))) (/ (RRnNorm K c + 1) * eps * / (1 + 1))).
apply Rmin_r.
rewrite - (Rmult_1_l (eps * / 2)).
rewrite Rmult_assoc.
apply Rmult_le_compat_r.
left.
apply (eps2_Rgt_R0 eps H2).
apply (Rmult_le_reg_l (RRnNorm K c + 1)).
apply (Rle_lt_trans 0 (RRnNorm K c)).
apply Rge_le.
apply ((fun (K : RRn) => match K with
  | R1K => fun (x : R) => (Rle_ge 0 (Rabs x) (Rabs_pos x))
  | RnK N => fun (x : Rn N) => (proj1 (RnNormNature N x))
end) : forall (K : RRn) (x : RRnT K), RRnNorm K x >= 0).
apply Rlt_plus_1.
rewrite (Rinv_r (RRnNorm K c + 1)).
rewrite (Rmult_1_r (RRnNorm K c + 1)).
rewrite - {1} (Rplus_0_l 1).
apply (Rplus_le_compat_r 1).
apply Rge_le.
apply ((fun (K : RRn) => match K with
  | R1K => fun (x : R) => (Rle_ge 0 (Rabs x) (Rabs_pos x))
  | RnK N => fun (x : Rn N) => (proj1 (RnNormNature N x))
end) : forall (K : RRn) (x : RRnT K), RRnNorm K x >= 0).
apply Rgt_not_eq.
apply (Rle_lt_trans 0 (RRnNorm K c)).
apply Rge_le.
apply ((fun (K : RRn) => match K with
  | R1K => fun (x : R) => (Rle_ge 0 (Rabs x) (Rabs_pos x))
  | RnK N => fun (x : Rn N) => (proj1 (RnNormNature N x))
end) : forall (K : RRn) (x : RRnT K), RRnNorm K x >= 0).
apply Rlt_plus_1.
apply Rabs_no_R0.
apply (Rminus_eq_contra x r H5).
apply Rabs_no_R0.
apply (Rminus_eq_contra x r H5).
rewrite (Rplus_comm r (x - r)).
unfold Rminus.
rewrite (Rplus_assoc x (- r) r).
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_r x).
rewrite (RRnmult_plus_distr_l K (x + - r)).
rewrite (RRnmult_assoc K (x + - r)).
rewrite (Rinv_r (x - r)).
rewrite (RRnmult_1_l K (RRnminus K (f x) (f r))).
suff: (RRnmult K (x + - r) (RRnopp K c) = RRnopp K (RRnmult K (x + - r) c)).
move=> H6.
rewrite H6.
reflexivity.
apply (Vopp_mul_distr_r_reverse Rfield (RRnVS K)).
apply (Rminus_eq_contra x r H5).
apply (Rle_lt_trans (Rabs (x - r) * RRnNorm K c) (Rabs (x - r) * (RRnNorm K c + 1))).
apply (Rmult_le_compat_l (Rabs (x - r))).
apply (Rabs_pos (x - r)).
left.
apply (Rlt_plus_1 (RRnNorm K c)).
rewrite - (Rmult_1_r (eps * / 2)).
rewrite - {2} (Rinv_l (RRnNorm K c + 1)).
rewrite - (Rmult_assoc (eps * / 2)).
apply Rmult_lt_compat_r.
apply (Rle_lt_trans 0 (RRnNorm K c)).
apply Rge_le.
apply ((fun (K : RRn) => match K with
  | R1K => fun (x : R) => (Rle_ge 0 (Rabs x) (Rabs_pos x))
  | RnK N => fun (x : Rn N) => (proj1 (RnNormNature N x))
end) : forall (K : RRn) (x : RRnT K), RRnNorm K x >= 0).
apply Rlt_plus_1.
apply (Rlt_le_trans (Rabs (x - r)) (Rmin dlt (/ (RRnNorm K c + 1) * eps * / (1 + 1)))).
apply (proj2 H4).
rewrite (Rmult_comm (eps * / 2)).
rewrite (Rmult_assoc (/ (RRnNorm K c + 1)) eps).
apply Rmin_r.
apply Rgt_not_eq.
apply (Rle_lt_trans 0 (RRnNorm K c)).
apply Rge_le.
apply ((fun (K : RRn) => match K with
  | R1K => fun (x : R) => (Rle_ge 0 (Rabs x) (Rabs_pos x))
  | RnK N => fun (x : Rn N) => (proj1 (RnNormNature N x))
end) : forall (K : RRn) (x : RRnT K), RRnNorm K x >= 0).
apply Rlt_plus_1.
Qed.

Lemma Proposition_1_3_1_plus_differentiable : forall (K : RRn) (A : Ensemble R) (f g : R -> RRnT K) (r : R), DifferentiableR_RRn K A f r -> DifferentiableR_RRn K A g r -> DifferentiableR_RRn K A (fun (x : R) => RRnplus K (f x) (g x)) r.
Proof.
move=> K A f g r.
elim.
move=> c1 H1.
elim.
move=> c2 H2.
exists (RRnplus K c1 c2).
suff: ((fun (h : R) =>
   RRnmult K (/ h)
     (RRnminus K (RRnplus K (f (r + h)) (g (r + h))) (RRnplus K (f r) (g r))))
= (fun (h : R) => RRnplus K (RRnmult K (/ h) (RRnminus K (f (r + h)) (f r))) (RRnmult K (/ h) (RRnminus K (g (r + h)) (g r)))
)).
move=> H3.
rewrite H3.
apply Theorem_6_6_1_1.
apply H1.
apply H2.
apply functional_extensionality.
unfold RRnminus.
suff: (forall (r : R) (a b c d : RRnT K), Vmul Rfield (RRnVS K) r (Vadd Rfield (RRnVS K) (Vadd Rfield (RRnVS K) a b) (Vopp Rfield (RRnVS K) (Vadd Rfield (RRnVS K) c d)))
= Vadd Rfield (RRnVS K) (Vmul Rfield (RRnVS K) r (Vadd Rfield (RRnVS K) a (Vopp Rfield (RRnVS K) c))) (Vmul Rfield (RRnVS K) r (Vadd Rfield (RRnVS K) b (Vopp Rfield (RRnVS K) d)))).
move=> H3 x.
apply (H3 (/ x)).
move=> x a b c d.
rewrite (Vopp_add_distr Rfield (RRnVS K) c d).
rewrite (Vadd_assoc Rfield (RRnVS K) a b).
rewrite - (Vadd_assoc Rfield (RRnVS K) b (Vopp Rfield (RRnVS K) c)).
rewrite (Vadd_comm Rfield (RRnVS K) b (Vopp Rfield (RRnVS K) c)).
rewrite (Vadd_assoc Rfield (RRnVS K) (Vopp Rfield (RRnVS K) c) b).
rewrite - (Vadd_assoc Rfield (RRnVS K) a).
apply (Vmul_add_distr_l Rfield (RRnVS K)).
Qed.

Lemma Proposition_1_3_1_plus : forall (K : RRn) (A : Ensemble R) (f g : R -> RRnT K) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_RRn K A f r) (H3 : DifferentiableR_RRn K A g r) (H4 : DifferentiableR_RRn K A (fun (x : R) => RRnplus K (f x) (g x)) r), DifferentialR_RRn K A (fun (x : R) => RRnplus K (f x) (g x)) r H1 H4 = RRnplus K (DifferentialR_RRn K A f r H1 H2) (DifferentialR_RRn K A g r H1 H3).
Proof.
move=> K A f g r H1 H2 H3 H4.
apply DifferentialR_RRnNature2.
suff: ((fun (h : R) =>
   RRnmult K (/ h)
     (RRnminus K (RRnplus K (f (r + h)) (g (r + h))) (RRnplus K (f r) (g r))))
= (fun (h : R) => RRnplus K (RRnmult K (/ h) (RRnminus K (f (r + h)) (f r))) (RRnmult K (/ h) (RRnminus K (g (r + h)) (g r)))
)).
move=> H5.
rewrite H5.
apply Theorem_6_6_1_1.
apply DifferentialR_RRnNature.
apply DifferentialR_RRnNature.
apply functional_extensionality.
unfold RRnminus.
suff: (forall (r : R) (a b c d : RRnT K), Vmul Rfield (RRnVS K) r (Vadd Rfield (RRnVS K) (Vadd Rfield (RRnVS K) a b) (Vopp Rfield (RRnVS K) (Vadd Rfield (RRnVS K) c d)))
= Vadd Rfield (RRnVS K) (Vmul Rfield (RRnVS K) r (Vadd Rfield (RRnVS K) a (Vopp Rfield (RRnVS K) c))) (Vmul Rfield (RRnVS K) r (Vadd Rfield (RRnVS K) b (Vopp Rfield (RRnVS K) d)))).
move=> H5 x.
apply (H5 (/ x)).
move=> x a b c d.
rewrite (Vopp_add_distr Rfield (RRnVS K) c d).
rewrite (Vadd_assoc Rfield (RRnVS K) a b).
rewrite - (Vadd_assoc Rfield (RRnVS K) b (Vopp Rfield (RRnVS K) c)).
rewrite (Vadd_comm Rfield (RRnVS K) b (Vopp Rfield (RRnVS K) c)).
rewrite (Vadd_assoc Rfield (RRnVS K) (Vopp Rfield (RRnVS K) c) b).
rewrite - (Vadd_assoc Rfield (RRnVS K) a).
apply (Vmul_add_distr_l Rfield (RRnVS K)).
Qed.

Lemma Proposition_1_3_1_opp_differentiable : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (r : R), DifferentiableR_RRn K A f r -> DifferentiableR_RRn K A (fun (x : R) => RRnopp K (f x)) r.
Proof.
move=> K A f r.
elim.
move=> c H1.
exists (RRnopp K c).
suff: ((fun (h : R) =>
   RRnmult K (/ h) (RRnminus K (RRnopp K (f (r + h))) (RRnopp K (f r))))
= (fun (h : R) => RRnopp K (RRnmult K (/ h) (RRnminus K (f (r + h)) (f r)))
)).
move=> H2.
rewrite H2.
apply Theorem_6_6_1_4.
apply H1.
apply functional_extensionality.
suff: (forall (r : R) (a b : RRnT K), Vmul Rfield (RRnVS K) r (Vadd Rfield (RRnVS K) (Vopp Rfield (RRnVS K) a) (Vopp Rfield (RRnVS K) (Vopp Rfield (RRnVS K) b)))
= Vopp Rfield (RRnVS K) (Vmul Rfield (RRnVS K) r (Vadd Rfield (RRnVS K) a (Vopp Rfield (RRnVS K) b)))).
move=> H2 x.
apply (H2 (/ x)).
move=> x a b.
rewrite (Vopp_mul_distr_r Rfield (RRnVS K)).
rewrite (Vopp_add_distr Rfield (RRnVS K)).
reflexivity.
Qed.

Lemma Proposition_1_3_1_opp : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_RRn K A f r) (H3 : DifferentiableR_RRn K A (fun (x : R) => RRnopp K (f x)) r), DifferentialR_RRn K A (fun (x : R) => RRnopp K (f x)) r H1 H3 = RRnopp K (DifferentialR_RRn K A f r H1 H2).
Proof.
move=> K A f r H1 H2 H3.
apply DifferentialR_RRnNature2.
suff: ((fun (h : R) =>
   RRnmult K (/ h)
     (RRnminus K (RRnopp K (f (r + h))) (RRnopp K (f r))))
= (fun (h : R) => RRnopp K (RRnmult K (/ h) (RRnminus K (f (r + h)) (f r)))
)).
move=> H4.
rewrite H4.
apply Theorem_6_6_1_4.
apply DifferentialR_RRnNature.
apply functional_extensionality.
suff: (forall (r : R) (a b : RRnT K), Vmul Rfield (RRnVS K) r (Vadd Rfield (RRnVS K) (Vopp Rfield (RRnVS K) a) (Vopp Rfield (RRnVS K) (Vopp Rfield (RRnVS K) b)))
= Vopp Rfield (RRnVS K) (Vmul Rfield (RRnVS K) r (Vadd Rfield (RRnVS K) a (Vopp Rfield (RRnVS K) b)))).
move=> H4 x.
apply (H4 (/ x)).
move=> x a b.
rewrite (Vopp_mul_distr_r Rfield (RRnVS K)).
rewrite (Vopp_add_distr Rfield (RRnVS K)).
reflexivity.
Qed.

Lemma Proposition_1_3_1_minus_differentiable : forall (K : RRn) (A : Ensemble R) (f g : R -> RRnT K) (r : R), DifferentiableR_RRn K A f r -> DifferentiableR_RRn K A g r -> DifferentiableR_RRn K A (fun (x : R) => RRnminus K (f x) (g x)) r.
Proof.
move=> K A f g r H1 H2.
apply Proposition_1_3_1_plus_differentiable.
apply H1.
apply Proposition_1_3_1_opp_differentiable.
apply H2.
Qed.

Lemma Proposition_1_3_1_minus : forall (K : RRn) (A : Ensemble R) (f g : R -> RRnT K) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_RRn K A f r) (H3 : DifferentiableR_RRn K A g r) (H4 : DifferentiableR_RRn K A (fun (x : R) => RRnminus K (f x) (g x)) r), DifferentialR_RRn K A (fun (x : R) => RRnminus K (f x) (g x)) r H1 H4 = RRnminus K (DifferentialR_RRn K A f r H1 H2) (DifferentialR_RRn K A g r H1 H3).
Proof.
move=> K A f g r H1 H2 H3 H4.
unfold RRnminus.
rewrite - (Proposition_1_3_1_opp K A g r H1 H3 (Proposition_1_3_1_opp_differentiable K A g r H3)).
apply (Proposition_1_3_1_plus K A f (fun (x : R) => RRnopp K (g x)) r H1 H2 (Proposition_1_3_1_opp_differentiable K A g r H3) H4).
Qed.

Lemma Proposition_1_3_1_MySumF2_differentiable : forall (U : Type) (S : {X : Ensemble U | Finite_sets.Finite U X}) (K : RRn) (A : Ensemble R) (f : U -> R -> RRnT K) (r : R), (forall (u : U), (In U (proj1_sig S) u) -> DifferentiableR_RRn K A (f u) r) -> DifferentiableR_RRn K A (fun (x : R) => MySumF2 U S (RRnPCM K) (fun (u : U) => f u x)) r.
Proof.
move=> U S K A f r H1.
apply (FiniteSetInduction U S).
apply conj.
exists (RRnO K).
move=> eps H2.
exists 1.
apply conj.
apply Rlt_0_1.
move=> x H3.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
suff: (RRnminus K (CMe (RRnPCM K)) (CMe (RRnPCM K)) = RRnO K).
move=> H4.
rewrite H4.
suff: (RRnmult K (/ x) (RRnO K) = RRnO K).
move=> H5.
rewrite H5.
rewrite (proj2 (dist_refl (RRn_met K) (RRnO K) (RRnO K))).
apply H2.
reflexivity.
apply (Vmul_O_r Rfield (RRnVS K)).
apply (RRnplus_opp_r K).
move=> B b H2 H3 H4 H5.
suff: ((fun (x : R) => MySumF2 U (FiniteAdd U B b) (RRnPCM K) (fun (u : U) => f u x)) = (fun (x : R) => RRnplus K (MySumF2 U B (RRnPCM K) (fun (u : U) => f u x)) (f b x))).
move=> H6.
rewrite H6.
apply (Proposition_1_3_1_plus_differentiable K A).
apply H5.
apply (H1 b H3).
apply functional_extensionality.
move=> x.
rewrite MySumF2Add.
reflexivity.
apply H4.
Qed.

Definition Proposition_1_3_1_MySumF2_R_differentiable (U : Type) (S : {X : Ensemble U | Finite U X}) : forall (A : Ensemble R) (f : U -> R -> R) (r : R), (forall (u : U), (In U (proj1_sig S) u) -> DifferentiableR_R A (f u) r) -> DifferentiableR_R A (fun (x : R) => MySumF2 U S RPCM (fun (u : U) => f u x)) r := Proposition_1_3_1_MySumF2_differentiable U S R1K.

Lemma Proposition_1_3_1_MySumF2 : forall (U : Type) (S : {X : Ensemble U | Finite_sets.Finite U X}) (K : RRn) (A : Ensemble R) (f : U -> R -> RRnT K) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : forall (u : U), DifferentiableR_RRn K A (f u) r) (H3 : DifferentiableR_RRn K A (fun (x : R) => MySumF2 U S (RRnPCM K) (fun (u : U) => f u x)) r), 
DifferentialR_RRn K A (fun (x : R) => MySumF2 U S (RRnPCM K) (fun (u : U) => f u x)) r H1 H3 = MySumF2 U S (RRnPCM K) (fun (u : U) => DifferentialR_RRn K A (f u) r H1 (H2 u)).
Proof.
move=> U S K A f r H1 H2.
apply (FiniteSetInduction U S).
apply conj.
move=> H3.
apply (DifferentialR_RRnNature2 K).
move=> eps H4.
exists 1.
apply conj.
apply Rlt_0_1.
move=> x H5.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
suff: (RRnminus K (CMe (RRnPCM K)) (CMe (RRnPCM K)) = RRnO K).
move=> H6.
rewrite H6.
suff: (RRnmult K (/ x) (RRnO K) = RRnO K).
move=> H7.
rewrite H7.
rewrite (proj2 (dist_refl (RRn_met K) (RRnO K) (RRnO K))).
apply H4.
reflexivity.
apply (Vmul_O_r Rfield (RRnVS K)).
apply (RRnplus_opp_r K).
move=> B b H3 H4 H5 H6.
suff: ((fun (x : R) => MySumF2 U (FiniteAdd U B b) (RRnPCM K) (fun (u : U) => f u x)) = (fun (x : R) => RRnplus K (MySumF2 U B (RRnPCM K) (fun (u : U) => f u x)) (f b x))).
move=> H7.
rewrite H7.
move=> H8.
rewrite MySumF2Add.
rewrite - (H6 (Proposition_1_3_1_MySumF2_differentiable U B K A f r (fun (u : U) (H : In U (proj1_sig B) u) => H2 u))).
apply (Proposition_1_3_1_plus K A).
apply H5.
apply functional_extensionality.
move=> x.
apply MySumF2Add.
apply H5.
Qed.

Definition Proposition_1_3_1_MySumF2_R (U : Type) (S : {X : Ensemble U | Finite_sets.Finite U X}) : forall (A : Ensemble R) (f : U -> R -> R) 
         (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r)
         (H2 : forall (u : U), DifferentiableR_R A (f u) r)
         (H3 : DifferentiableR_R A
                 (fun (x : R) => MySumF2 U S RPCM (fun (u : U) => f u x)) r),
       DifferentialR_R A
         (fun (x : R) => MySumF2 U S RPCM (fun (u : U) => f u x)) r H1 H3 =
       MySumF2 U S RPCM
         (fun (u : U) => DifferentialR_R A (f u) r H1 (H2 u)) := Proposition_1_3_1_MySumF2 U S R1K.

Lemma Proposition_1_3_3_mult_R_differentiable : forall (A : Ensemble R) (f g : R -> R) (r : R), DifferentiableR_R A f r -> DifferentiableR_R A g r -> DifferentiableR_R A (fun (x : R) => (f x) * (g x)) r.
Proof.
move=> A f g r.
elim.
move=> c1 H1 H2.
elim H2.
move=> c2 H3.
exists (c1 * (g r) + (f r) * c2).
suff: ((fun (h : R) => / h * (f (r + h) * g (r + h) - f r * g r))
=
(fun (h : R) => / h * (f (r + h) - f r) * g (r + h) + / h * (f r) * (g (r + h) - g r))).
move=> H4.
rewrite H4.
apply Theorem_6_6_1_1_R.
apply Theorem_6_6_2_1_R.
apply H1.
move=> eps H5.
elim (Proposition_1_2 R1K A g r H2 eps H5).
move=> dlt H6.
exists dlt.
apply conj.
apply (proj1 H6).
move=> x H7.
apply (proj2 H6 (r + x)).
apply conj.
apply (proj2 (proj1 H7)).
unfold dist.
simpl.
unfold R_dist.
unfold Rminus.
rewrite (Rplus_comm (r + x) (- r)).
rewrite - (Rplus_assoc (- r) r x).
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_l x).
rewrite - (Rminus_0_r x).
apply (proj2 H7).
suff: ((fun (h : Base R_met) => / h * f r * (g (r + h) - g r))
= (fun (h : Base R_met) =>  f r * (/ h * (g (r + h) - g r)))).
move=> H5.
rewrite H5.
apply Theorem_6_6_1_3_R.
apply H3.
apply functional_extensionality.
move=> h.
rewrite (Rmult_comm (/ h) (f r)).
apply (Rmult_assoc (f r) (/ h) (g (r + h) - g r)).
apply functional_extensionality.
move=> h.
rewrite (Rmult_assoc (/ h) ((f (r + h) - f r))).
rewrite (Rmult_assoc (/ h) (f r)).
rewrite - (Rmult_plus_distr_l (/ h)).
unfold Rminus.
rewrite (Rmult_plus_distr_r (f (r + h))).
rewrite (Rmult_plus_distr_l (f r)).
rewrite (Rplus_assoc (f (r + h) * g (r + h)) (- f r * g (r + h))).
rewrite - (Rplus_assoc (- f r * g (r + h))).
rewrite - (Rmult_plus_distr_r (- f r)).
rewrite (Rplus_opp_l (f r)).
rewrite (Rmult_0_l (g (r + h))).
rewrite (Rplus_0_l (f r * - g r)).
rewrite (Ropp_mult_distr_r (f r) (g r)).
reflexivity.
Qed.

Lemma Proposition_1_3_3_mult_R : forall (A : Ensemble R) (f g : R -> R) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_R A f r) (H3 : DifferentiableR_R A g r) (H4 : DifferentiableR_R A (fun (x : R) => (f x) * (g x)) r), DifferentialR_R A (fun (x : R) => (f x) * (g x)) r H1 H4 = DifferentialR_R A f r H1 H2 * (g r) + (f r) * DifferentialR_R A g r H1 H3.
Proof.
move=> A f g r H1 H2 H3 H4.
apply (DifferentialR_RNature2 A).
suff: ((fun (h : R) => / h * (f (r + h) * g (r + h) - f r * g r))
=
(fun (h : R) => / h * (f (r + h) - f r) * g (r + h) + / h * (f r) * (g (r + h) - g r))).
move=> H5.
rewrite H5.
apply Theorem_6_6_1_1_R.
apply Theorem_6_6_2_1_R.
apply (DifferentialR_RNature A f r H1 H2).
move=> eps H6.
elim (Proposition_1_2 R1K A g r H3 eps H6).
move=> dlt H7.
exists dlt.
apply conj.
apply (proj1 H7).
move=> x H8.
apply (proj2 H7 (r + x)).
apply conj.
apply (proj2 (proj1 H8)).
unfold dist.
simpl.
unfold R_dist.
unfold Rminus.
rewrite (Rplus_comm (r + x) (- r)).
rewrite - (Rplus_assoc (- r) r x).
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_l x).
rewrite - (Rminus_0_r x).
apply (proj2 H8).
suff: ((fun (h : Base R_met) => / h * f r * (g (r + h) - g r))
= (fun (h : Base R_met) =>  f r * (/ h * (g (r + h) - g r)))).
move=> H6.
rewrite H6.
apply Theorem_6_6_1_3_R.
apply (DifferentialR_RNature A g r H1 H3).
apply functional_extensionality.
move=> h.
rewrite (Rmult_comm (/ h) (f r)).
apply (Rmult_assoc (f r) (/ h) (g (r + h) - g r)).
apply functional_extensionality.
move=> h.
rewrite (Rmult_assoc (/ h) ((f (r + h) - f r))).
rewrite (Rmult_assoc (/ h) (f r)).
rewrite - (Rmult_plus_distr_l (/ h)).
unfold Rminus.
rewrite (Rmult_plus_distr_r (f (r + h))).
rewrite (Rmult_plus_distr_l (f r)).
rewrite (Rplus_assoc (f (r + h) * g (r + h)) (- f r * g (r + h))).
rewrite - (Rplus_assoc (- f r * g (r + h))).
rewrite - (Rmult_plus_distr_r (- f r)).
rewrite (Rplus_opp_l (f r)).
rewrite (Rmult_0_l (g (r + h))).
rewrite (Rplus_0_l (f r * - g r)).
rewrite (Ropp_mult_distr_r (f r) (g r)).
reflexivity.
Qed.

Lemma Proposition_1_3_3_mult_C_differentiable : forall (A : Ensemble R) (f g : R -> C) (r : R), DifferentiableR_Rn 2 A f r -> DifferentiableR_Rn 2 A g r -> DifferentiableR_Rn 2 A (fun (x : R) => Cmult (f x) (g x)) r.
Proof.
move=> A f g r.
elim.
move=> c1 H1 H2.
elim H2.
move=> c2 H3.
exists (Cplus (Cmult c1 (g r)) (Cmult (f r) c2)).
suff: ((fun (h : R) =>
   Rnmult 2 (/ h)
     (Rnminus 2 (Cmult (f (r + h)) (g (r + h))) (Cmult (f r) (g r))))
=
(fun (h : R) => Cplus (Rnmult 2 (/ h) (Cmult (Cminus (f (r + h)) (f r)) (g (r + h)))) (Rnmult 2 (/ h) (Cmult (f r) (Cminus (g (r + h)) (g r)))))).
move=> H4.
rewrite H4.
apply (Theorem_6_6_1_1_Rn R_met 2).
suff: ((fun (h : Base R_met) =>
   Rnmult 2 (/ h) (Cmult (Cminus (f (r + h)) (f r)) (g (r + h))))
= (fun (h : Base R_met) =>
   (Cmult (Rnmult 2 (/ h) (Cminus (f (r + h)) (f r))) (g (r + h))))).
move=> H5.
rewrite H5.
apply (Theorem_6_6_2_1_C R_met).
apply H1.
move=> eps H6.
elim (Proposition_1_2 (RnK 2) A g r H2 eps H6).
move=> dlt H7.
exists dlt.
apply conj.
apply (proj1 H7).
move=> x H8.
apply (proj2 H7 (r + x)).
apply conj.
apply (proj2 (proj1 H8)).
unfold dist.
simpl.
unfold R_dist.
unfold Rminus.
rewrite (Rplus_comm (r + x) (- r)).
rewrite - (Rplus_assoc (- r) r x).
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_l x).
rewrite - (Rminus_0_r x).
apply (proj2 H8).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> m.
elim (CReorCIm m).
move=> H5.
rewrite H5.
unfold Rnmult.
unfold Fnmul.
simpl.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
apply (Rmult_minus_distr_l (/ x) (Cminus (f (r + x)) (f r) CRe * g (r + x) CRe) (Cminus (f (r + x)) (f r) CIm * g (r + x) CIm)).
move=> H5.
rewrite H5.
unfold Rnmult.
unfold Fnmul.
simpl.
unfold Cmult.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
apply (Rmult_plus_distr_l (/ x)).
suff: ((fun (h : Base R_met) => Rnmult 2 (/ h) (Cmult (f r) (Cminus (g (r + h)) (g r))))
= (fun (h : Base R_met) => Cmult (f r) (Rnmult 2 (/ h) (Cminus (g (r + h)) (g r))))).
move=> H5.
rewrite H5.
apply Theorem_6_6_2_1_C.
move=> eps H6.
exists 1.
apply conj.
apply Rlt_0_1.
move=> h H7.
rewrite (proj2 (dist_refl C_met (f r) (f r))).
apply H6.
reflexivity.
apply H3.
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> m.
elim (CReorCIm m).
move=> H5.
rewrite H5.
unfold Rnmult.
unfold Fnmul.
simpl.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite - Rmult_assoc.
rewrite - Rmult_assoc.
rewrite (Rmult_comm (f r CRe) (/ h)).
rewrite (Rmult_comm (f r CIm) (/ h)).
rewrite (Rmult_minus_distr_l (/ h)).
rewrite Rmult_assoc.
rewrite Rmult_assoc.
reflexivity.
move=> H5.
rewrite H5.
unfold Rnmult.
unfold Fnmul.
simpl.
unfold Cmult.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite - Rmult_assoc.
rewrite - Rmult_assoc.
rewrite (Rmult_comm (f r CRe) (/ h)).
rewrite (Rmult_comm (f r CIm) (/ h)).
rewrite (Rmult_plus_distr_l (/ h)).
rewrite Rmult_assoc.
rewrite Rmult_assoc.
reflexivity.
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> m.
unfold Rnmult.
unfold Fnmul.
unfold Rnminus.
unfold Fnminus.
unfold Cplus.
unfold Fnadd.
simpl.
rewrite - (Rmult_plus_distr_l (/ h)).
rewrite (Cmult_comm (Cminus (f (r + h)) (f r))).
rewrite Cmult_plus_distr_l.
rewrite Cmult_plus_distr_l.
unfold Cplus.
simpl.
rewrite (Rplus_assoc (Cmult (g (r + h)) (f (r + h)) m)).
rewrite - (Rplus_assoc (Cmult (g (r + h)) (Fnopp Rfield 2 (f r)) m)).
rewrite (Cmult_comm (f r) (g (r + h))).
suff: (Cmult (g (r + h)) (Fnopp Rfield 2 (f r)) m + Cmult (g (r + h)) (f r) m
= Cplus (Cmult (g (r + h)) (Fnopp Rfield 2 (f r))) (Cmult (g (r + h)) (f r)) m).
move=> H4.
rewrite H4.
rewrite - Cmult_plus_distr_l.
rewrite (Cplus_comm (Fnopp Rfield 2 (f r)) (f r)).
rewrite (Cplus_opp_r (f r)).
suff: (Cmult = Fmul Cfield).
move=> H5.
rewrite H5.
rewrite (Fmul_O_r Cfield (g (r + h))).
rewrite (Rplus_0_l (Fmul Cfield (f r) (Fnopp Rfield 2 (g r)) m)).
rewrite - (Fopp_mul_distr_r Cfield (f r)).
rewrite (Fmul_comm Cfield (g (r + h))).
reflexivity.
reflexivity.
reflexivity.
Qed.

Lemma Proposition_1_3_3_mult_C : forall (A : Ensemble R) (f g : R -> C) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_Rn 2 A f r) (H3 : DifferentiableR_Rn 2 A g r) (H4 : DifferentiableR_Rn 2 A (fun (x : R) => Cmult (f x) (g x)) r), DifferentialR_Rn 2 A (fun (x : R) => Cmult (f x) (g x)) r H1 H4 = Cplus (Cmult (DifferentialR_Rn 2 A f r H1 H2) (g r)) (Cmult (f r) (DifferentialR_Rn 2 A g r H1 H3)).
Proof.
move=> A f g r H1 H2 H3 H4.
apply (DifferentialR_RnNature2 2 A).
suff: ((fun (h : R) =>
   Rnmult 2 (/ h)
     (Rnminus 2 (Cmult (f (r + h)) (g (r + h))) (Cmult (f r) (g r))))
=
(fun (h : R) => Cplus (Rnmult 2 (/ h) (Cmult (Cminus (f (r + h)) (f r)) (g (r + h)))) (Rnmult 2 (/ h) (Cmult (f r) (Cminus (g (r + h)) (g r)))))).
move=> H5.
rewrite H5.
apply (Theorem_6_6_1_1_Rn R_met 2).
suff: ((fun (h : Base R_met) =>
   Rnmult 2 (/ h) (Cmult (Cminus (f (r + h)) (f r)) (g (r + h))))
= (fun (h : Base R_met) =>
   (Cmult (Rnmult 2 (/ h) (Cminus (f (r + h)) (f r))) (g (r + h))))).
move=> H6.
rewrite H6.
apply (Theorem_6_6_2_1_C R_met).
apply (DifferentialR_RnNature 2 A f r H1 H2).
move=> eps H7.
elim (Proposition_1_2 (RnK 2) A g r H3 eps H7).
move=> dlt H8.
exists dlt.
apply conj.
apply (proj1 H8).
move=> x H9.
apply (proj2 H8 (r + x)).
apply conj.
apply (proj2 (proj1 H9)).
unfold dist.
simpl.
unfold R_dist.
unfold Rminus.
rewrite (Rplus_comm (r + x) (- r)).
rewrite - (Rplus_assoc (- r) r x).
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_l x).
rewrite - (Rminus_0_r x).
apply (proj2 H9).
apply functional_extensionality.
move=> x.
apply functional_extensionality.
move=> m.
elim (CReorCIm m).
move=> H6.
rewrite H6.
unfold Rnmult.
unfold Fnmul.
simpl.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
apply (Rmult_minus_distr_l (/ x) (Cminus (f (r + x)) (f r) CRe * g (r + x) CRe) (Cminus (f (r + x)) (f r) CIm * g (r + x) CIm)).
move=> H6.
rewrite H6.
unfold Rnmult.
unfold Fnmul.
simpl.
unfold Cmult.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
apply (Rmult_plus_distr_l (/ x)).
suff: ((fun (h : Base R_met) => Rnmult 2 (/ h) (Cmult (f r) (Cminus (g (r + h)) (g r))))
= (fun (h : Base R_met) => Cmult (f r) (Rnmult 2 (/ h) (Cminus (g (r + h)) (g r))))).
move=> H6.
rewrite H6.
apply Theorem_6_6_2_1_C.
move=> eps H7.
exists 1.
apply conj.
apply Rlt_0_1.
move=> h H8.
rewrite (proj2 (dist_refl C_met (f r) (f r))).
apply H7.
reflexivity.
apply (DifferentialR_RnNature 2 A g r H1 H3).
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> m.
elim (CReorCIm m).
move=> H6.
rewrite H6.
unfold Rnmult.
unfold Fnmul.
simpl.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite - Rmult_assoc.
rewrite - Rmult_assoc.
rewrite (Rmult_comm (f r CRe) (/ h)).
rewrite (Rmult_comm (f r CIm) (/ h)).
rewrite (Rmult_minus_distr_l (/ h)).
rewrite Rmult_assoc.
rewrite Rmult_assoc.
reflexivity.
move=> H6.
rewrite H6.
unfold Rnmult.
unfold Fnmul.
simpl.
unfold Cmult.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite - Rmult_assoc.
rewrite - Rmult_assoc.
rewrite (Rmult_comm (f r CRe) (/ h)).
rewrite (Rmult_comm (f r CIm) (/ h)).
rewrite (Rmult_plus_distr_l (/ h)).
rewrite Rmult_assoc.
rewrite Rmult_assoc.
reflexivity.
apply functional_extensionality.
move=> h.
apply functional_extensionality.
move=> m.
unfold Rnmult.
unfold Fnmul.
unfold Rnminus.
unfold Fnminus.
unfold Cplus.
unfold Fnadd.
simpl.
rewrite - (Rmult_plus_distr_l (/ h)).
rewrite (Cmult_comm (Cminus (f (r + h)) (f r))).
rewrite Cmult_plus_distr_l.
rewrite Cmult_plus_distr_l.
unfold Cplus.
simpl.
rewrite (Rplus_assoc (Cmult (g (r + h)) (f (r + h)) m)).
rewrite - (Rplus_assoc (Cmult (g (r + h)) (Fnopp Rfield 2 (f r)) m)).
rewrite (Cmult_comm (f r) (g (r + h))).
suff: (Cmult (g (r + h)) (Fnopp Rfield 2 (f r)) m + Cmult (g (r + h)) (f r) m
= Cplus (Cmult (g (r + h)) (Fnopp Rfield 2 (f r))) (Cmult (g (r + h)) (f r)) m).
move=> H5.
rewrite H5.
rewrite - Cmult_plus_distr_l.
rewrite (Cplus_comm (Fnopp Rfield 2 (f r)) (f r)).
rewrite (Cplus_opp_r (f r)).
suff: (Cmult = Fmul Cfield).
move=> H6.
rewrite H6.
rewrite (Fmul_O_r Cfield (g (r + h))).
rewrite (Rplus_0_l (Fmul Cfield (f r) (Fnopp Rfield 2 (g r)) m)).
rewrite - (Fopp_mul_distr_r Cfield (f r)).
rewrite (Fmul_comm Cfield (g (r + h))).
reflexivity.
reflexivity.
reflexivity.
Qed.

Lemma Proposition_1_3_3_inv_R_differentiable : forall (A : Ensemble R) (f : R -> R) (r : R), DifferentiableR_R A f r -> f r <> 0 -> DifferentiableR_R A (fun (x : R) => / (f x)) r.
Proof.
move=> A f r H1 H2.
elim H1.
move=> c H3.
exists (- (c / (f r * f r))).
suff: (exists (dlt : R), dlt > 0 /\ forall (h : R), h <> 0 -> In R A (r + h) -> Rabs (h - 0) < dlt -> / h * (/ f (r + h) - / f r) = / h * (f (r + h) - f r) * - / (f r * f (r + h))).
move=> H4.
suff: (limit_in R_met R_met (fun (h : R) => / h * (f (r + h) - f r) * - / (f r * f (r + h))))
  (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 (- (c / (f r * f r))).
move=> H5 eps H6.
elim (H5 eps H6).
move=> dlt1 H7.
elim H4.
move=> dlt2 H8.
exists (Rmin dlt1 dlt2).
apply conj.
apply (Rmin_pos dlt1 dlt2 (proj1 H7) (proj1 H8)).
move=> x H9.
rewrite (proj2 H8 x (proj1 (proj1 H9))).
apply (proj2 H7 x).
apply conj.
apply (proj1 H9).
apply (Rlt_le_trans (dist R_met x 0) (Rmin dlt1 dlt2) dlt1 (proj2 H9) (Rmin_l dlt1 dlt2)).
apply (proj2 (proj1 H9)).
apply (Rlt_le_trans (dist R_met x 0) (Rmin dlt1 dlt2) dlt2 (proj2 H9) (Rmin_r dlt1 dlt2)).
unfold Rdiv.
rewrite Ropp_mult_distr_r.
apply Theorem_6_6_2_1_R.
apply H3.
apply Theorem_6_6_1_4_R.
apply Theorem_6_6_2_3_R.
apply (Rmult_integral_contrapositive_currified (f r) (f r) H2 H2).
apply Theorem_6_6_1_3_R.
move=> eps H5.
elim (Proposition_1_2 R1K A f r H1 eps H5).
move=> dlt H6.
exists dlt.
apply conj.
apply (proj1 H6).
move=> x H7.
apply (proj2 H6).
apply conj.
apply (proj2 (proj1 H7)).
unfold dist.
simpl.
unfold R_dist.
unfold Rminus.
rewrite (Rplus_comm (r + x) (- r)).
rewrite - (Rplus_assoc (- r) r x).
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_l x).
rewrite - (Rminus_0_r x).
apply (proj2 H7).
elim (Proposition_1_2 R1K A f r H1 (Rabs (f r))).
move=> dlt H4.
exists dlt.
apply conj.
apply (proj1 H4).
move=> h H5 H6 H7.
suff: (f (r + h) <> 0).
move=> H8.
rewrite Rmult_assoc.
rewrite - (Ropp_minus_distr (f r) (f (r + h))).
rewrite Rmult_opp_opp.
rewrite Rmult_plus_distr_r.
rewrite (Rinv_mult_distr (f r) (f (r + h)) H2 H8).
rewrite - (Rmult_assoc (f r) (/ f r)).
rewrite (Rinv_r (f r) H2).
rewrite (Rmult_1_l (/ f (r + h))).
rewrite (Rmult_comm (/ f r) (/ f (r + h))).
rewrite - (Rmult_assoc (- f (r + h)) (/ f (r + h))).
rewrite Ropp_mult_distr_l_reverse.
rewrite Ropp_mult_distr_l_reverse.
rewrite (Rinv_r (f (r + h)) H8).
rewrite (Rmult_1_l (/ f r)).
reflexivity.
move=> H8.
apply (Rlt_irrefl (Rabs (f r))).
suff: (Rabs (f r) = (dist (RRn_met R1K) (f (r + h)) (f r))).
move=> H9.
rewrite {1} H9.
apply (proj2 H4 (r + h)).
apply conj.
apply H6.
unfold dist.
simpl.
unfold R_dist.
rewrite (Rplus_comm r h).
unfold Rminus.
rewrite (Rplus_assoc h r (- r)).
rewrite (Rplus_opp_r r).
rewrite - Ropp_0.
apply H7.
rewrite H8.
rewrite - {1} (Rminus_0_r (f r)).
apply (Rabs_minus_sym (f r) 0).
apply (Rabs_pos_lt (f r) H2).
Qed.

Lemma Proposition_1_3_3_inv_R : forall (A : Ensemble R) (f : R -> R) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_R A f r) (H3 : f r <> 0) (H4 : DifferentiableR_R A (fun (x : R) => / (f x)) r), DifferentialR_R A (fun (x : R) => / (f x)) r H1 H4 = - (DifferentialR_R A f r H1 H2 / ((f r) * (f r))).
Proof.
move=> A f r H1 H2 H3 H4.
suff: (exists (dlt : R), dlt > 0 /\ forall (h : R), h <> 0 -> In R A (r + h) -> Rabs (h - 0) < dlt -> / h * (/ f (r + h) - / f r) = / h * (f (r + h) - f r) * - / (f r * f (r + h))).
move=> H5.
suff: (limit_in R_met R_met (fun (h : R) => / h * (f (r + h) - f r) * - / (f r * f (r + h))))
  (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 (- (DifferentialR_R A f r H1 H2 / (f r * f r))).
move=> H6.
apply (DifferentialR_RNature2 A (fun (x : R) => / f x) r H1 H4).
move=> eps H7.
elim (H6 eps H7).
move=> dlt1 H8.
elim H5.
move=> dlt2 H9.
exists (Rmin dlt1 dlt2).
apply conj.
apply (Rmin_pos dlt1 dlt2 (proj1 H8) (proj1 H9)).
move=> x H10.
rewrite (proj2 H9 x (proj1 (proj1 H10))).
apply (proj2 H8 x).
apply conj.
apply (proj1 H10).
apply (Rlt_le_trans (dist R_met x 0) (Rmin dlt1 dlt2) dlt1 (proj2 H10) (Rmin_l dlt1 dlt2)).
apply (proj2 (proj1 H10)).
apply (Rlt_le_trans (dist R_met x 0) (Rmin dlt1 dlt2) dlt2 (proj2 H10) (Rmin_r dlt1 dlt2)).
unfold Rdiv.
rewrite Ropp_mult_distr_r.
apply Theorem_6_6_2_1_R.
apply (DifferentialR_RNature A f r H1 H2).
apply Theorem_6_6_1_4_R.
apply Theorem_6_6_2_3_R.
apply (Rmult_integral_contrapositive_currified (f r) (f r) H3 H3).
apply Theorem_6_6_1_3_R.
move=> eps H6.
elim (Proposition_1_2 R1K A f r H2 eps H6).
move=> dlt H7.
exists dlt.
apply conj.
apply (proj1 H7).
move=> x H8.
apply (proj2 H7).
apply conj.
apply (proj2 (proj1 H8)).
unfold dist.
simpl.
unfold R_dist.
unfold Rminus.
rewrite (Rplus_comm (r + x) (- r)).
rewrite - (Rplus_assoc (- r) r x).
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_l x).
rewrite - (Rminus_0_r x).
apply (proj2 H8).
elim (Proposition_1_2 R1K A f r H2 (Rabs (f r))).
move=> dlt H5.
exists dlt.
apply conj.
apply (proj1 H5).
move=> h H6 H7 H8.
suff: (f (r + h) <> 0).
move=> H9.
rewrite Rmult_assoc.
rewrite - (Ropp_minus_distr (f r) (f (r + h))).
rewrite Rmult_opp_opp.
rewrite Rmult_plus_distr_r.
rewrite (Rinv_mult_distr (f r) (f (r + h)) H3 H9).
rewrite - (Rmult_assoc (f r) (/ f r)).
rewrite (Rinv_r (f r) H3).
rewrite (Rmult_1_l (/ f (r + h))).
rewrite (Rmult_comm (/ f r) (/ f (r + h))).
rewrite - (Rmult_assoc (- f (r + h)) (/ f (r + h))).
rewrite Ropp_mult_distr_l_reverse.
rewrite Ropp_mult_distr_l_reverse.
rewrite (Rinv_r (f (r + h)) H9).
rewrite (Rmult_1_l (/ f r)).
reflexivity.
move=> H9.
apply (Rlt_irrefl (Rabs (f r))).
suff: (Rabs (f r) = (dist (RRn_met R1K) (f (r + h)) (f r))).
move=> H10.
rewrite {1} H10.
apply (proj2 H5 (r + h)).
apply conj.
apply H7.
unfold dist.
simpl.
unfold R_dist.
rewrite (Rplus_comm r h).
unfold Rminus.
rewrite (Rplus_assoc h r (- r)).
rewrite (Rplus_opp_r r).
rewrite - Ropp_0.
apply H8.
rewrite H9.
rewrite - {1} (Rminus_0_r (f r)).
apply (Rabs_minus_sym (f r) 0).
apply (Rabs_pos_lt (f r) H3).
Qed.

Lemma Proposition_1_3_3_inv_C_differentiable : forall (A : Ensemble R) (f : R -> C) (r : R), DifferentiableR_Rn 2 A f r -> f r <> CO -> DifferentiableR_Rn 2 A (fun (x : R) => Cinv (f x)) r.
Proof.
move=> A f r H1 H2.
elim H1.
move=> c H3.
exists (Copp (Cmult c (Cinv (Cmult (f r) (f r))))).
suff: (exists (dlt : R), dlt > 0 /\ forall (h : R), h <> 0 -> In R A (r + h) -> Rabs (h - 0) < dlt -> Rnmult 2 (/ h) (Rnminus 2 (Cinv (f (r + h))) (Cinv (f r))) = Cmult (Rnmult 2 (/ h) (Cminus (f (r + h)) (f r))) (Copp (Cinv (Cmult (f r) (f (r + h)))))).
move=> H4.
suff: (limit_in R_met C_met (fun (h : R) => Cmult (Rnmult 2 (/ h) (Cminus (f (r + h)) (f r))) (Copp (Cinv (Cmult (f r) (f (r + h))))))
  (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 (Copp (Cmult c (Cinv (Cmult (f r) (f r)))))).
move=> H5 eps H6.
elim (H5 eps H6).
move=> dlt1 H7.
elim H4.
move=> dlt2 H8.
exists (Rmin dlt1 dlt2).
apply conj.
apply (Rmin_pos dlt1 dlt2 (proj1 H7) (proj1 H8)).
move=> x H9.
rewrite (proj2 H8 x (proj1 (proj1 H9))).
apply (proj2 H7 x).
apply conj.
apply (proj1 H9).
apply (Rlt_le_trans (dist R_met x 0) (Rmin dlt1 dlt2) dlt1 (proj2 H9) (Rmin_l dlt1 dlt2)).
apply (proj2 (proj1 H9)).
apply (Rlt_le_trans (dist R_met x 0) (Rmin dlt1 dlt2) dlt2 (proj2 H9) (Rmin_r dlt1 dlt2)).
unfold Rdiv.
rewrite (Fopp_mul_distr_r Cfield c (Cinv (Cmult (f r) (f r))) : Copp (Cmult c (Cinv (Cmult (f r) (f r)))) = Cmult c (Copp (Cinv (Cmult (f r) (f r))))).
apply Theorem_6_6_2_1_C.
apply H3.
apply (Theorem_6_6_1_4_Rn R_met 2).
apply Theorem_6_6_2_3_C.
apply (Fmul_integral_contrapositive_currified Cfield (f r) (f r) H2 H2 : Cmult (f r) (f r) <> CO).
apply Theorem_6_6_2_1_C.
move=> eps H5.
exists 1.
apply conj.
apply Rlt_0_1.
move=> x H6.
rewrite (proj2 (dist_refl C_met (f r) (f r))).
apply H5.
reflexivity.
move=> eps H5.
elim (Proposition_1_2 (RnK 2) A f r H1 eps H5).
move=> dlt H6.
exists dlt.
apply conj.
apply (proj1 H6).
move=> x H7.
apply (proj2 H6).
apply conj.
apply (proj2 (proj1 H7)).
unfold dist.
simpl.
unfold R_dist.
unfold Rminus.
rewrite (Rplus_comm (r + x) (- r)).
rewrite - (Rplus_assoc (- r) r x).
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_l x).
rewrite - (Rminus_0_r x).
apply (proj2 H7).
elim (Proposition_1_2 (RnK 2) A f r H1 (RnNorm 2 (f r))).
move=> dlt H4.
exists dlt.
apply conj.
apply (proj1 H4).
move=> h H5 H6 H7.
suff: (f (r + h) <> CO).
move=> H8.
suff: (forall (x : R) (c1 c2 : C), Cmult (Rnmult 2 x c1) c2 = Rnmult 2 x (Cmult c1 c2)).
move=> H9.
rewrite (H9 (/ h)).
rewrite - (Fopp_minus_distr Cfield (f r) (f (r + h)) : Copp (Cminus (f r) (f (r + h))) = Cminus (f (r + h)) (f r)).
rewrite (Fmul_opp_opp Cfield : forall (c1 c2 : C), Cmult (Copp c1) (Copp c2) = Cmult c1 c2).
rewrite (Fmul_add_distr_r Cfield : forall (c1 c2 c3 : C), Cmult (Cplus c1 c2) c3 = Cplus (Cmult c1 c3) (Cmult c2 c3)).
rewrite (Finv_mul_distr Cfield (f r) (f (r + h)) H2 H8 : Cinv (Cmult (f r) (f (r + h))) = Cmult (Cinv (f r)) (Cinv (f (r + h)))).
rewrite - (Cmult_assoc (f r) (Cinv (f r))).
rewrite (Finv_r Cfield (f r) H2 : Cmult (f r) (Cinv (f r)) = CI).
rewrite (Cmult_1_l (Cinv (f (r + h)))).
rewrite (Cmult_comm (Cinv (f r)) (Cinv (f (r + h)))).
rewrite - (Cmult_assoc (Copp (f (r + h))) (Cinv (f (r + h)))).
rewrite - (Fopp_mul_distr_l Cfield (f (r + h)) (Cinv (f (r + h))) : Copp (Cmult (f (r + h)) (Cinv (f (r + h)))) = Cmult (Copp (f (r + h))) (Cinv (f (r + h)))).
rewrite (Finv_r Cfield (f (r + h)) H8 : Cmult (f (r + h)) (Cinv (f (r + h))) = CI).
rewrite - (Fopp_mul_distr_l Cfield CI (Cinv (f r)) : Copp (Cmult CI (Cinv (f r))) = Cmult (Copp CI) (Cinv (f r))).
rewrite (Cmult_1_l (Cinv (f r))).
reflexivity.
move=> x c1 c2.
apply functional_extensionality.
move=> m.
elim (CReorCIm m).
move=> H9.
rewrite H9.
unfold Cmult.
unfold Rnmult.
unfold Fnmul.
rewrite CmakeRe.
rewrite CmakeRe.
simpl.
unfold Rminus.
rewrite Rmult_plus_distr_l.
rewrite - (Rmult_assoc x (c1 CRe) (c2 CRe)).
rewrite (Ropp_mult_distr_r_reverse x (c1 CIm * c2 CIm)).
rewrite - (Rmult_assoc x (c1 CIm) (c2 CIm)).
reflexivity.
move=> H9.
rewrite H9.
unfold Cmult.
unfold Rnmult.
unfold Fnmul.
rewrite CmakeIm.
rewrite CmakeIm.
simpl.
unfold Rminus.
rewrite Rmult_plus_distr_l.
rewrite - (Rmult_assoc x (c1 CRe) (c2 CIm)).
rewrite - (Rmult_assoc x (c1 CIm) (c2 CRe)).
reflexivity.
move=> H8.
apply (Rlt_irrefl (RnNorm 2 (f r))).
suff: (RnNorm 2 (f r) = dist C_met (f (r + h)) (f r)).
move=> H9.
rewrite {1} H9.
apply (proj2 H4 (r + h)).
apply conj.
apply H6.
unfold dist.
simpl.
unfold R_dist.
rewrite (Rplus_comm r h).
unfold Rminus.
rewrite (Rplus_assoc h r (- r)).
rewrite (Rplus_opp_r r).
rewrite - Ropp_0.
apply H7.
rewrite H8.
rewrite - {1} (Fminus_O_r Cfield (f r)).
apply (dist_sym C_met).
apply (RRnNorm_pos_lt (RnK 2) (f r) H2).
Qed.

Lemma Proposition_1_3_3_inv_C : forall (A : Ensemble R) (f : R -> C) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_Rn 2 A f r) (H3 : f r <> CO) (H4 : DifferentiableR_Rn 2 A (fun (x : R) => Cinv (f x)) r), DifferentialR_Rn 2 A (fun (x : R) => Cinv (f x)) r H1 H4 = Copp (Cmult (DifferentialR_Rn 2 A f r H1 H2) (Cinv (Cmult (f r) (f r)))).
Proof.
move=> A f r H1 H2 H3 H4.
suff: (exists (dlt : R), dlt > 0 /\ forall (h : R), h <> 0 -> In R A (r + h) -> Rabs (h - 0) < dlt -> Rnmult 2 (/ h) (Rnminus 2 (Cinv (f (r + h))) (Cinv (f r))) = Cmult (Rnmult 2 (/ h) (Cminus (f (r + h)) (f r))) (Copp (Cinv (Cmult (f r) (f (r + h)))))).
move=> H5.
suff: (limit_in R_met C_met (fun (h : R) => Cmult (Rnmult 2 (/ h) (Cminus (f (r + h)) (f r))) (Copp (Cinv (Cmult (f r) (f (r + h))))))
  (fun (h : R) => h <> 0 /\ In R A (r + h)) 0 (Copp (Cmult (DifferentialR_Rn 2 A f r H1 H2) (Cinv (Cmult (f r) (f r)))))).
move=> H6.
apply (DifferentialR_RnNature2 2).
move=> eps H7.
elim (H6 eps H7).
move=> dlt1 H8.
elim H5.
move=> dlt2 H9.
exists (Rmin dlt1 dlt2).
apply conj.
apply (Rmin_pos dlt1 dlt2 (proj1 H8) (proj1 H9)).
move=> x H10.
rewrite (proj2 H9 x (proj1 (proj1 H10))).
apply (proj2 H8 x).
apply conj.
apply (proj1 H10).
apply (Rlt_le_trans (dist R_met x 0) (Rmin dlt1 dlt2) dlt1 (proj2 H10) (Rmin_l dlt1 dlt2)).
apply (proj2 (proj1 H10)).
apply (Rlt_le_trans (dist R_met x 0) (Rmin dlt1 dlt2) dlt2 (proj2 H10) (Rmin_r dlt1 dlt2)).
unfold Rdiv.
rewrite (Fopp_mul_distr_r Cfield (DifferentialR_Rn 2 A f r H1 H2) (Cinv (Cmult (f r) (f r))) : Copp (Cmult (DifferentialR_Rn 2 A f r H1 H2) (Cinv (Cmult (f r) (f r)))) = Cmult (DifferentialR_Rn 2 A f r H1 H2) (Copp (Cinv (Cmult (f r) (f r))))).
apply Theorem_6_6_2_1_C.
apply (DifferentialR_RnNature 2 A f r H1 H2).
apply (Theorem_6_6_1_4_Rn R_met 2).
apply Theorem_6_6_2_3_C.
apply (Fmul_integral_contrapositive_currified Cfield (f r) (f r) H3 H3 : Cmult (f r) (f r) <> CO).
apply Theorem_6_6_2_1_C.
move=> eps H6.
exists 1.
apply conj.
apply Rlt_0_1.
move=> x H7.
rewrite (proj2 (dist_refl C_met (f r) (f r))).
apply H6.
reflexivity.
move=> eps H6.
elim (Proposition_1_2 (RnK 2) A f r H2 eps H6).
move=> dlt H7.
exists dlt.
apply conj.
apply (proj1 H7).
move=> x H8.
apply (proj2 H7).
apply conj.
apply (proj2 (proj1 H8)).
unfold dist.
simpl.
unfold R_dist.
unfold Rminus.
rewrite (Rplus_comm (r + x) (- r)).
rewrite - (Rplus_assoc (- r) r x).
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_l x).
rewrite - (Rminus_0_r x).
apply (proj2 H8).
elim (Proposition_1_2 (RnK 2) A f r H2 (RnNorm 2 (f r))).
move=> dlt H5.
exists dlt.
apply conj.
apply (proj1 H5).
move=> h H6 H7 H8.
suff: (f (r + h) <> CO).
move=> H9.
suff: (forall (x : R) (c1 c2 : C), Cmult (Rnmult 2 x c1) c2 = Rnmult 2 x (Cmult c1 c2)).
move=> H10.
rewrite (H10 (/ h)).
rewrite - (Fopp_minus_distr Cfield (f r) (f (r + h)) : Copp (Cminus (f r) (f (r + h))) = Cminus (f (r + h)) (f r)).
rewrite (Fmul_opp_opp Cfield : forall (c1 c2 : C), Cmult (Copp c1) (Copp c2) = Cmult c1 c2).
rewrite (Fmul_add_distr_r Cfield : forall (c1 c2 c3 : C), Cmult (Cplus c1 c2) c3 = Cplus (Cmult c1 c3) (Cmult c2 c3)).
rewrite (Finv_mul_distr Cfield (f r) (f (r + h)) H3 H9 : Cinv (Cmult (f r) (f (r + h))) = Cmult (Cinv (f r)) (Cinv (f (r + h)))).
rewrite - (Cmult_assoc (f r) (Cinv (f r))).
rewrite (Finv_r Cfield (f r) H3 : Cmult (f r) (Cinv (f r)) = CI).
rewrite (Cmult_1_l (Cinv (f (r + h)))).
rewrite (Cmult_comm (Cinv (f r)) (Cinv (f (r + h)))).
rewrite - (Cmult_assoc (Copp (f (r + h))) (Cinv (f (r + h)))).
rewrite - (Fopp_mul_distr_l Cfield (f (r + h)) (Cinv (f (r + h))) : Copp (Cmult (f (r + h)) (Cinv (f (r + h)))) = Cmult (Copp (f (r + h))) (Cinv (f (r + h)))).
rewrite (Finv_r Cfield (f (r + h)) H9 : Cmult (f (r + h)) (Cinv (f (r + h))) = CI).
rewrite - (Fopp_mul_distr_l Cfield CI (Cinv (f r)) : Copp (Cmult CI (Cinv (f r))) = Cmult (Copp CI) (Cinv (f r))).
rewrite (Cmult_1_l (Cinv (f r))).
reflexivity.
move=> x c1 c2.
apply functional_extensionality.
move=> m.
elim (CReorCIm m).
move=> H10.
rewrite H10.
unfold Cmult.
unfold Rnmult.
unfold Fnmul.
rewrite CmakeRe.
rewrite CmakeRe.
simpl.
unfold Rminus.
rewrite Rmult_plus_distr_l.
rewrite - (Rmult_assoc x (c1 CRe) (c2 CRe)).
rewrite (Ropp_mult_distr_r_reverse x (c1 CIm * c2 CIm)).
rewrite - (Rmult_assoc x (c1 CIm) (c2 CIm)).
reflexivity.
move=> H10.
rewrite H10.
unfold Cmult.
unfold Rnmult.
unfold Fnmul.
rewrite CmakeIm.
rewrite CmakeIm.
simpl.
unfold Rminus.
rewrite Rmult_plus_distr_l.
rewrite - (Rmult_assoc x (c1 CRe) (c2 CIm)).
rewrite - (Rmult_assoc x (c1 CIm) (c2 CRe)).
reflexivity.
move=> H9.
apply (Rlt_irrefl (RnNorm 2 (f r))).
suff: (RnNorm 2 (f r) = dist C_met (f (r + h)) (f r)).
move=> H10.
rewrite {1} H10.
apply (proj2 H5 (r + h)).
apply conj.
apply H7.
unfold dist.
simpl.
unfold R_dist.
rewrite (Rplus_comm r h).
unfold Rminus.
rewrite (Rplus_assoc h r (- r)).
rewrite (Rplus_opp_r r).
rewrite - Ropp_0.
apply H8.
rewrite H9.
rewrite - {1} (Fminus_O_r Cfield (f r)).
apply (dist_sym C_met).
apply (RRnNorm_pos_lt (RnK 2) (f r) H3).
Qed.

Lemma Proposition_1_3_3_div_R_differentiable : forall (A : Ensemble R) (f g : R -> R) (r : R), DifferentiableR_R A f r -> DifferentiableR_R A g r -> g r <> 0 -> DifferentiableR_R A (fun (x : R) => (f x) / (g x)) r.
Proof.
move=> A f g r H1 H2 H3.
apply (Proposition_1_3_3_mult_R_differentiable A).
apply H1.
apply (Proposition_1_3_3_inv_R_differentiable A).
apply H2.
apply H3.
Qed.

Lemma Proposition_1_3_3_div_R : forall (A : Ensemble R) (f g : R -> R) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_R A f r) (H3 : DifferentiableR_R A g r) (H4 : g r <> 0) (H5 : DifferentiableR_R A (fun (x : R) => (f x) / (g x)) r), DifferentialR_R A (fun (x : R) => (f x) / (g x)) r H1 H5 = (DifferentialR_R A f r H1 H2 * (g r) - (f r) * DifferentialR_R A g r H1 H3) / (g r * g r).
Proof.
move=> A f g r H1 H2 H3 H4 H5.
suff: (DifferentiableR_R A (fun (x : R) => / g x) r).
move=> H6.
rewrite (Proposition_1_3_3_mult_R A f (fun (x : R) => / g x) r H1 H2 H6 H5).
rewrite (Proposition_1_3_3_inv_R A g r H1 H3 H4 H6).
unfold Rdiv.
rewrite Rmult_plus_distr_r.
rewrite {2} (Rinv_mult_distr (g r) (g r) H4 H4).
rewrite (Rmult_assoc (DifferentialR_R A f r H1 H2) (g r)).
rewrite - (Rmult_assoc (g r) (/ g r) (/ g r)).
rewrite (Rinv_r (g r) H4).
rewrite (Rmult_1_l (/ g r)).
rewrite (Ropp_mult_distr_r (f r)).
rewrite Rmult_assoc.
rewrite Ropp_mult_distr_l.
reflexivity.
apply (Proposition_1_3_3_inv_R_differentiable A).
apply H3.
apply H4.
Qed.

Lemma Proposition_1_3_3_div_C_differentiable : forall (A : Ensemble R) (f g : R -> C) (r : R), DifferentiableR_Rn 2 A f r -> DifferentiableR_Rn 2 A g r -> g r <> CO -> DifferentiableR_Rn 2 A (fun (x : R) => Cmult (f x) (Cinv (g x))) r.
Proof.
move=> A f g r H1 H2 H3.
apply (Proposition_1_3_3_mult_C_differentiable A).
apply H1.
apply (Proposition_1_3_3_inv_C_differentiable A).
apply H2.
apply H3.
Qed.

Lemma Proposition_1_3_3_div_C : forall (A : Ensemble R) (f g : R -> C) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_Rn 2 A f r) (H3 : DifferentiableR_Rn 2 A g r) (H4 : g r <> CO) (H5 : DifferentiableR_Rn 2 A (fun (x : R) => Cmult (f x) (Cinv (g x))) r), DifferentialR_Rn 2 A (fun (x : R) => Cmult (f x) (Cinv (g x))) r H1 H5 = Cmult (Cplus (Cmult (DifferentialR_Rn 2 A f r H1 H2) (g r)) (Copp (Cmult (f r) (DifferentialR_Rn 2 A g r H1 H3)))) (Cinv (Cmult (g r) (g r))).
Proof.
move=> A f g r H1 H2 H3 H4 H5.
suff: (DifferentiableR_Rn 2 A (fun (x : R) => Cinv (g x)) r).
move=> H6.
rewrite (Proposition_1_3_3_mult_C A f (fun (x : R) => Cinv (g x)) r H1 H2 H6 H5).
rewrite (Proposition_1_3_3_inv_C A g r H1 H3 H4 H6).
rewrite (Fmul_add_distr_r Cfield : forall (c1 c2 c3 : C), Cmult (Cplus c1 c2) c3 = Cplus (Cmult c1 c3) (Cmult c2 c3)).
rewrite {2} (Finv_mul_distr Cfield (g r) (g r) H4 H4 : Cinv (Cmult (g r) (g r)) = Cmult (Cinv (g r)) (Cinv (g r))).
rewrite (Cmult_assoc (DifferentialR_Rn 2 A f r H1 H2) (g r)).
rewrite - (Cmult_assoc (g r) (Cinv (g r)) (Cinv (g r))).
rewrite (Finv_r Cfield (g r) H4 : Cmult (g r) (Cinv (g r)) = CI).
rewrite (Cmult_1_l (Cinv (g r))).
rewrite (Fopp_mul_distr_r Cfield (f r) (DifferentialR_Rn 2 A g r H1 H3) : Copp (Cmult (f r) (DifferentialR_Rn 2 A g r H1 H3)) = Cmult (f r) (Copp (DifferentialR_Rn 2 A g r H1 H3))).
rewrite Cmult_assoc.
rewrite (Fopp_mul_distr_l Cfield (DifferentialR_Rn 2 A g r H1 H3) (Cinv (Cmult (g r) (g r))) : Copp (Cmult (DifferentialR_Rn 2 A g r H1 H3) (Cinv (Cmult (g r) (g r)))) = Cmult (Copp (DifferentialR_Rn 2 A g r H1 H3)) (Cinv (Cmult (g r) (g r)))).
reflexivity.
apply (Proposition_1_3_3_inv_C_differentiable A).
apply H3.
apply H4.
Qed.

Lemma Proposition_1_3_2_R_differentiable : forall (A : Ensemble R) (N : nat) (f g : R -> Rn N) (r : R), DifferentiableR_Rn N A f r -> DifferentiableR_Rn N A g r -> DifferentiableR_R A (fun (x : R) => RnInnerProduct N (f x) (g x)) r.
Proof.
move=> A N f g r H1 H2.
apply Proposition_1_3_1_MySumF2_R_differentiable.
move=> u H3.
apply Proposition_1_3_3_mult_R_differentiable.
apply (proj1 (Proposition_1_1_1 N A f r) H1 u).
apply (proj1 (Proposition_1_1_1 N A g r) H2 u).
Qed.

Lemma Proposition_1_3_2_R : forall (A : Ensemble R) (N : nat) (f g : R -> Rn N) (r : R) (H1 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H2 : DifferentiableR_Rn N A f r) (H3 : DifferentiableR_Rn N A g r) (H4 : DifferentiableR_R A (fun (x : R) => RnInnerProduct N (f x) (g x)) r), DifferentialR_R A (fun (x : R) => RnInnerProduct N (f x) (g x)) r H1 H4 = RnInnerProduct N (DifferentialR_Rn N A f r H1 H2) (g r) + RnInnerProduct N (f r) (DifferentialR_Rn N A g r H1 H3).
Proof.
move=> A N f g r H1 H2 H3 H4.
suff: (forall (u : Count N), DifferentiableR_R A (fun (x : R) => f x u) r).
move=> H5.
suff: (forall (u : Count N), DifferentiableR_R A (fun (x : R) => g x u) r).
move=> H6.
suff: (forall (u : Count N), DifferentiableR_R A (fun (x : R) => f x u * g x u) r).
move=> H7.
rewrite Proposition_1_3_1_MySumF2_R.
rewrite (MySumF2Distr (Count N) RPCM
  (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N))
(fun (u : Count N) => (DifferentialR_R A (fun (x : R) => f x u) r H1 (H5 u)) * g r u)
(fun (u : Count N) => f r u * DifferentialR_R A (fun (x : R) => g x u) r H1 (H6 u))
(fun (u : Count N) => DifferentialR_R A (fun (x : R) => f x u * g x u) r H1 (H7 u))).
suff: (forall (r1 r2 r3 r4 : R), r1 = r2 -> r3 = r4 -> r1 + r3 = r2 + r4).
move=> H8.
apply H8.
apply (MySumF2Same (Count N)
  (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) RPCM).
move=> u H9.
rewrite (Proposition_1_1_2 N A f r H1 H2 H5).
reflexivity.
apply (MySumF2Same (Count N)
  (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) RPCM).
move=> u H9.
rewrite (Proposition_1_1_2 N A g r H1 H3 H6).
reflexivity.
move=> r1 r2 r3 r4 H8 H9.
rewrite H8.
rewrite H9.
reflexivity.
move=> u H8.
apply Proposition_1_3_3_mult_R.
move=> u.
apply Proposition_1_3_3_mult_R_differentiable.
apply (H5 u).
apply (H6 u).
apply (proj1 (Proposition_1_1_1 N A g r) H3).
apply (proj1 (Proposition_1_1_1 N A f r) H2).
Qed.

Lemma FullNotIsolated : forall (r : R), ClosureMet R_met (fun (x : R) => x <> r /\ In R (Full_set R) x) r.
Proof.
move=> r eps H1.
exists (r + eps / 2).
apply conj.
unfold NeighborhoodMet.
simpl.
unfold R_dist.
unfold Rminus.
rewrite (Rplus_comm (r + eps / 2) (- r)).
rewrite - (Rplus_assoc (- r) r (eps / 2)).
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_l (eps / 2)).
rewrite Rabs_pos_eq.
apply (Rlt_eps2_eps eps H1).
left.
apply (eps2_Rgt_R0 eps H1).
apply conj.
rewrite - {2} (Rplus_0_r r).
move=> H2.
apply (Rgt_not_eq (eps / 2) 0 (eps2_Rgt_R0 eps H1)).
apply (Rplus_eq_reg_l r (eps / 2) 0 H2).
apply (Full_intro R (r + eps / 2)).
Qed.

Definition DifferentialR_RRn_Full (K : RRn) (f : R -> RRnT K) (r : R) := DifferentialR_RRn K (Full_set R) f r (FullNotIsolated r).

Definition DifferentialR_Rn_Full (N : nat) (f : R -> Rn N) (r : R) := DifferentialR_Rn N (Full_set R) f r (FullNotIsolated r).

Definition DifferentialR_R_Full (f : R -> R) (r : R) := DifferentialR_R (Full_set R) f r (FullNotIsolated r).

Definition TangentVector (K : RRn) (f : R -> RRnT K) (r : R) (H : DifferentiableR_RRn K (Full_set R) f r) (t : R) := RRnplus K (f r) (RRnmult K (t - r) (DifferentialR_RRn_Full K f r H)).

Definition TangentLine (f : R -> R) (r : R) (H : DifferentiableR_R (Full_set R) f r) (t : R) := (f r) + (t - r) * (DifferentialR_R_Full f r H).

Definition TangentPlane (N : nat) (f : R -> Rn N) (r : R) (H : DifferentiableR_Rn N (Full_set R) f r) (t : R) := Rnplus N (f r) (Rnmult N (t - r) (DifferentialR_Rn_Full N f r H)).

Lemma Proposition_1_4 : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (a b : R), a < b -> (forall (r : R), a <= r <= b -> ClosureMet R_met (fun (x : R) => x <> r /\ In R A x /\ a <= x <= b) r) -> (forall (r : R), a <= r <= b -> DifferentiableR_RRn K (fun (x : R) => In R A x /\ a <= x <= b) f r) <-> (exists (g : R -> RRnT K), (forall (r : R), a <= r <= b -> f r = g r) /\ forall (r : R), DifferentiableR_RRn K A g r).
Proof.
move=> K A f a b H1 H2.
apply conj.
move=> H3.
suff: (a <= a <= b).
move=> H4.
suff: (a <= b <= b).
move=> H5.
suff: (forall (r : R), a <= r <= b -> ClosureMet R_met
    (fun (x : R) => x <> r /\ In R A x /\ a <= x <= b) r).
move=> H6.
exists (fun (r : R) => match Rle_lt_dec a r with
  | left _ => match Rle_lt_dec r b with
    | left _ => f r
    | right _ => RRnplus K (f b) (RRnmult K (r - b) (DifferentialR_RRn K (fun (x : R) => In R A x /\ a <= x <= b) f b (H6 b H5) (H3 b H5)))
  end
  | right _ => RRnplus K (f a) (RRnmult K (r - a) (DifferentialR_RRn K (fun (x : R) => In R A x /\ a <= x <= b) f a (H6 a H4) (H3 a H4)))
end).
apply conj.
move=> r H7.
elim (Rle_lt_dec a r).
move=> H8.
elim (Rle_lt_dec r b).
move=> H9.
reflexivity.
move=> H9.
elim (Rle_not_lt b r (proj2 H7) H9).
move=> H8.
elim (Rle_not_lt r a (proj1 H7) H8).
suff: ((forall (x : R) (r : RRnT K), x <> 0 -> RRnmult K (/ x) (RRnmult K x r) = r) /\ (forall (x : R) (r : RRnT K), RRnopp K (RRnmult K x r) = RRnmult K (- x) r) /\ forall (r1 r2 r3 : RRnT K), RRnminus K (RRnplus K r1 r2) (RRnplus K r1 r3) = RRnminus K r2 r3).
move=> H7 r.
elim (Rle_or_lt r a).
elim.
move=> H8.
exists (DifferentialR_RRn K (fun (x : R) => In R A x /\ a <= x <= b) f a (H6 a H4) (H3 a H4)).
move=> eps H9.
exists (a - r).
apply conj.
apply (Rlt_Rminus r a H8).
move=> x H10.
elim (Rle_lt_dec a r).
move=> H11.
elim (Rle_not_lt r a H11 H8).
move=> H11.
elim (Rle_lt_dec a (r + x)).
move=> H12.
elim (Rle_not_lt (r + x) a H12).
apply (Rle_lt_trans (r + x) (r + Rabs (x - 0)) a).
apply Rplus_le_compat_l.
rewrite (Rminus_0_r x).
apply (Rle_abs x).
apply (Rplus_lt_reg_l (- r)).
rewrite - Rplus_assoc.
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_l (Rabs (x - 0))).
rewrite (Rplus_comm (- r) a).
apply (proj2 H10).
move=> H12.
rewrite (proj2 (proj2 H7)).
unfold RRnminus.
rewrite (proj1 (proj2 H7)).
rewrite - RRnmult_plus_distr_r.
rewrite (Rplus_comm r x).
unfold Rminus.
rewrite (Rplus_assoc x r (- a)).
rewrite (Rplus_assoc x (r + - a)).
rewrite (Rplus_opp_r (r + - a)).
rewrite (Rplus_0_r x).
rewrite (proj1 H7 x).
rewrite (proj2 (dist_refl (RRn_met K) (DifferentialR_RRn K (fun (x0 : R) => In R A x0 /\ a <= x0 <= b) f a 
     (H6 a H4) (H3 a H4)) (DifferentialR_RRn K (fun (x0 : R) => In R A x0 /\ a <= x0 <= b) f a 
     (H6 a H4) (H3 a H4)))).
apply H9.
reflexivity.
apply (proj1 (proj1 H10)).
move=> H8.
exists (DifferentialR_RRn K (fun (x : R) => In R A x /\ a <= x <= b) f a (H6 a H4) (H3 a H4)).
move=> eps H9.
elim (DifferentialR_RRnNature K (fun (x : R) => In R A x /\ a <= x <= b) f a (H6 a H4) (H3 a H4) eps H9).
move=> dlt H10.
exists (Rmin dlt (b - a)).
apply conj.
apply Rmin_pos.
apply (proj1 H10).
apply (Rlt_Rminus a b H1).
rewrite H8.
move=> x H11.
elim (Rle_lt_dec a a).
move=> H12.
elim (Rle_lt_dec a b).
move=> H13.
elim (Rle_lt_dec a (a + x)).
move=> H14.
elim (Rle_lt_dec (a + x) b).
move=> H15.
apply (proj2 H10 x).
apply conj.
apply conj.
apply (proj1 (proj1 H11)).
apply conj.
apply (proj2 (proj1 H11)).
apply (conj H14 H15).
apply (Rlt_le_trans (dist R_met x 0) (Rmin dlt (b - a)) dlt (proj2 H11) (Rmin_l dlt (b - a))).
move=> H15.
elim (Rle_not_lt b (a + x)).
apply (Rle_trans (a + x) (a + Rabs x) b).
apply (Rplus_le_compat_l a x (Rabs x) (Rle_abs x)).
apply (Rplus_le_reg_l (- a)).
rewrite - Rplus_assoc.
rewrite (Rplus_opp_l a).
rewrite (Rplus_0_l (Rabs x)).
rewrite (Rplus_comm (- a) b).
rewrite - (Rminus_0_r x).
left.
apply (Rlt_le_trans (Rabs (x - 0)) (Rmin dlt (b - a)) (b - a) (proj2 H11) (Rmin_r dlt (b - a))).
apply H15.
move=> H14.
rewrite - {2} (RRnplus_0_r K (f a)).
rewrite (proj2 (proj2 H7)).
unfold RRnminus.
suff: (RRnopp K (RRnO K) = RRnO K).
move=> H15.
rewrite H15.
rewrite (RRnplus_0_r K).
unfold Rminus.
rewrite (Rplus_comm (a + x) (- a)).
rewrite - (Rplus_assoc (- a) a x).
rewrite (Rplus_opp_l a).
rewrite (Rplus_0_l x).
rewrite (proj1 H7).
rewrite (proj2 (dist_refl (RRn_met K) (DifferentialR_RRn K (fun (x0 : R) => In R A x0 /\ a <= x0 <= b) f a 
     (H6 a H4) (H3 a H4)) (DifferentialR_RRn K (fun (x0 : R) => In R A x0 /\ a <= x0 <= b) f a 
     (H6 a H4) (H3 a H4)))).
apply H9.
reflexivity.
apply (proj1 (proj1 H11)).
apply (Vopp_O Rfield (RRnVS K)).
move=> H13.
elim (Rle_not_lt a b).
left.
apply H13.
apply H1.
move=> H12.
elim (Rlt_irrefl a H12).
move=> H8.
elim (Rle_or_lt b r).
elim.
move=> H9.
exists (DifferentialR_RRn K (fun (x : R) => In R A x /\ a <= x <= b) f b (H6 b H5) (H3 b H5)).
move=> eps H10.
exists (r - b).
apply conj.
apply (Rlt_Rminus b r H9).
move=> x H11.
elim (Rle_lt_dec r b).
move=> H12.
elim (Rle_not_lt b r H12 H9).
move=> H12.
elim (Rle_lt_dec (r + x) b).
move=> H13.
elim (Rle_not_lt b (r + x) H13).
apply (Rlt_le_trans b (r - Rabs (x - 0)) (r + x)).
apply (Rplus_lt_reg_l (- b)).
rewrite (Rplus_opp_l b).
unfold Rminus.
rewrite - Rplus_assoc.
apply (Rplus_lt_reg_r (Rabs (x + - 0))).
rewrite (Rplus_0_l (Rabs (x + - 0))).
rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite (Rplus_0_r (- b + r)).
rewrite (Rplus_comm (- b) r).
apply (proj2 H11).
apply Rplus_le_compat_l.
rewrite (Rminus_0_r x).
rewrite - (Ropp_involutive x).
rewrite (Rabs_Ropp (- x)).
apply Ropp_le_contravar.
apply Rle_abs.
move=> H13.
elim (Rle_lt_dec a r).
move=> H14.
elim (Rle_lt_dec a (r + x)).
move=> H15.
rewrite (proj2 (proj2 H7)).
unfold RRnminus.
rewrite (proj1 (proj2 H7)).
rewrite - RRnmult_plus_distr_r.
rewrite (Rplus_comm r x).
unfold Rminus.
rewrite (Rplus_assoc x r (- b)).
rewrite (Rplus_assoc x (r + - b)).
rewrite (Rplus_opp_r (r + - b)).
rewrite (Rplus_0_r x).
rewrite (proj1 H7 x).
rewrite (proj2 (dist_refl (RRn_met K) (DifferentialR_RRn K (fun (x0 : R) => In R A x0 /\ a <= x0 <= b) f b 
     (H6 b H5) (H3 b H5)) (DifferentialR_RRn K (fun (x0 : R) => In R A x0 /\ a <= x0 <= b) f b
     (H6 b H5) (H3 b H5)))).
apply H10.
reflexivity.
apply (proj1 (proj1 H11)).
move=> H15.
elim (Rlt_irrefl a).
apply (Rlt_trans a b a H1 (Rlt_trans b (r + x) a H13 H15)).
move=> H14.
elim (Rlt_irrefl a).
apply (Rlt_trans a b a H1 (Rlt_trans b r a H12 H14)).
move=> H9.
rewrite - H9.
exists (DifferentialR_RRn K (fun (x : R) => In R A x /\ a <= x <= b) f b (H6 b H5) (H3 b H5)).
move=> eps H10.
elim (DifferentialR_RRnNature K (fun (x : R) => In R A x /\ a <= x <= b) f b (H6 b H5) (H3 b H5) eps H10).
move=> dlt H11.
exists (Rmin dlt (b - a)).
apply conj.
apply Rmin_pos.
apply (proj1 H11).
apply (Rlt_Rminus a b H1).
move=> x H12.
elim (Rle_lt_dec a b).
move=> H13.
elim (Rle_lt_dec b b).
move=> H14.
elim (Rle_lt_dec a (b + x)).
move=> H15.
elim (Rle_lt_dec (b + x) b).
move=> H16.
apply (proj2 H11 x).
apply conj.
apply conj.
apply (proj1 (proj1 H12)).
apply conj.
apply (proj2 (proj1 H12)).
apply (conj H15 H16).
apply (Rlt_le_trans (dist R_met x 0) (Rmin dlt (b - a)) dlt (proj2 H12) (Rmin_l dlt (b - a))).
move=> H16.
rewrite - {2} (RRnplus_0_r K (f b)).
rewrite (proj2 (proj2 H7)).
unfold RRnminus.
suff: (RRnopp K (RRnO K) = RRnO K).
move=> H17.
rewrite H17.
rewrite (RRnplus_0_r K).
unfold Rminus.
rewrite (Rplus_comm (b + x) (- b)).
rewrite - (Rplus_assoc (- b) b x).
rewrite (Rplus_opp_l b).
rewrite (Rplus_0_l x).
rewrite (proj1 H7).
rewrite (proj2 (dist_refl (RRn_met K) (DifferentialR_RRn K (fun (x0 : R) => In R A x0 /\ a <= x0 <= b) f b
     (H6 b H5) (H3 b H5)) (DifferentialR_RRn K (fun (x0 : R) => In R A x0 /\ a <= x0 <= b) f b 
     (H6 b H5) (H3 b H5)))).
apply H10.
reflexivity.
apply (proj1 (proj1 H12)).
apply (Vopp_O Rfield (RRnVS K)).
move=> H15.
elim (Rle_not_lt (b + x) a).
left.
apply (Rplus_lt_reg_r (- x)).
rewrite Rplus_assoc.
rewrite (Rplus_opp_r x).
rewrite (Rplus_0_r b).
apply (Rplus_lt_reg_l (- a)).
rewrite - Rplus_assoc.
rewrite (Rplus_opp_l a).
rewrite (Rplus_0_l (- x)).
apply (Rle_lt_trans (- x) (Rabs x) (- a + b)).
rewrite - Rabs_Ropp.
apply Rle_abs.
rewrite - (Rminus_0_r x).
rewrite (Rplus_comm (- a) b).
apply (Rlt_le_trans (Rabs (x - 0)) (Rmin dlt (b - a)) (b - a) (proj2 H12) (Rmin_r dlt (b - a))).
apply H15.
move=> H14.
elim (Rlt_irrefl b H14).
move=> H13.
elim (Rlt_irrefl a (Rlt_trans a b a H1 H13)).
move=> H9.
suff: (a <= r <= b).
move=> H10.
exists (DifferentialR_RRn K (fun (x : R) => In R A x /\ a <= x <= b) f r (H6 r H10) (H3 r H10)).
move=> eps H11.
elim (DifferentialR_RRnNature K (fun (x : R) => In R A x /\ a <= x <= b) f r (H6 r H10) (H3 r H10) eps H11).
move=> dlt H12.
exists (Rmin dlt (Rmin (b - r) (r - a))).
apply conj.
apply Rmin_pos.
apply (proj1 H12).
apply Rmin_pos.
apply (Rlt_Rminus r b H9).
apply (Rlt_Rminus a r H8).
move=> x H13.
elim (Rle_lt_dec a r).
move=> H14.
elim (Rle_lt_dec r b).
move=> H15.
elim (Rle_lt_dec a (r + x)).
move=> H16.
elim (Rle_lt_dec (r + x) b).
move=> H17.
apply (proj2 H12 x).
apply conj.
apply conj.
apply (proj1 (proj1 H13)).
apply conj.
apply (proj2 (proj1 H13)).
apply (conj H16 H17).
apply (Rlt_le_trans (dist R_met x 0) (Rmin dlt (Rmin (b - r) (r - a)))).
apply (proj2 H13).
apply (Rmin_l dlt (Rmin (b - r) (r - a))).
move=> H17.
elim (Rle_not_lt b (r + x)).
apply (Rle_trans (r + x) (r + Rabs (x - 0)) b).
apply Rplus_le_compat_l.
rewrite (Rminus_0_r x).
apply (Rle_abs x).
apply (Rplus_le_reg_l (- r)).
rewrite - Rplus_assoc.
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_l (Rabs (x - 0))).
apply (Rle_trans (Rabs (x - 0)) (Rmin dlt (Rmin (b - r) (r - a))) (- r + b)).
left.
apply (proj2 H13).
rewrite (Rplus_comm (- r) b).
apply (Rle_trans (Rmin dlt (Rmin (b - r) (r - a))) (Rmin (b - r) (r - a))).
apply Rmin_r.
apply Rmin_l.
apply H17.
move=> H16.
elim (Rle_not_lt (r + x) a).
apply (Rle_trans a (r - Rabs (x - 0)) (r + x)).
apply (Rplus_le_reg_l (- r)).
rewrite - Rplus_assoc.
rewrite (Rplus_opp_l r).
rewrite (Rplus_0_l (- Rabs (x - 0))).
rewrite (Rplus_comm (- r) a).
rewrite - (Ropp_minus_distr r a : - (r - a) = a + - r).
apply Ropp_le_contravar.
apply (Rle_trans (Rabs (x - 0)) (Rmin dlt (Rmin (b - r) (r - a))) (r - a)).
left.
apply (proj2 H13).
apply (Rle_trans (Rmin dlt (Rmin (b - r) (r - a))) (Rmin (b - r) (r - a)) (r - a)).
apply Rmin_r.
apply Rmin_r.
apply Rplus_le_compat_l.
rewrite (Rminus_0_r x).
rewrite - (Ropp_involutive x).
rewrite Rabs_Ropp.
apply Ropp_le_contravar.
apply Rle_abs.
apply H16.
move=> H15.
elim (Rlt_irrefl b (Rlt_trans b r b H15 H9)).
move=> H14.
elim (Rlt_irrefl a (Rlt_trans a r a H8 H14)).
apply conj.
left.
apply H8.
left.
apply H9.
apply conj.
move=> x r H7.
rewrite (RRnmult_assoc K).
rewrite (Rinv_l x H7).
apply (RRnmult_1_l K r).
apply conj.
move=> x r.
apply (Vopp_mul_distr_l Rfield (RRnVS K)).
move=> r1 r2 r3.
unfold RRnminus.
rewrite (Vopp_add_distr Rfield (RRnVS K) r1 r3 : RRnopp K (RRnplus K r1 r3) = RRnplus K (RRnopp K r1) (RRnopp K r3)).
rewrite - (RRnplus_assoc K (RRnplus K r1 r2)).
rewrite (RRnplus_comm K r1 r2).
rewrite (RRnplus_assoc K r2 r1).
rewrite (RRnplus_opp_r K r1).
rewrite (RRnplus_0_r K r2).
reflexivity.
apply H2.
apply conj.
left.
apply H1.
right.
reflexivity.
apply conj.
right.
reflexivity.
left.
apply H1.
elim.
move=> g H3 r H4.
suff: (ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r).
move=> H5.
exists (DifferentialR_RRn K A g r H5 (proj2 H3 r)).
move=> eps H6.
elim (DifferentialR_RRnNature K A g r H5 (proj2 H3 r) eps H6).
move=> dlt H7.
exists dlt.
apply conj.
apply (proj1 H7).
move=> x H8.
rewrite (proj1 H3 (r + x) (proj2 (proj2 (proj1 H8)))).
rewrite (proj1 H3 r H4).
apply (proj2 H7 x).
apply conj.
apply conj.
apply (proj1 (proj1 H8)).
apply (proj1 (proj2 (proj1 H8))).
apply (proj2 H8).
move=> eps H5.
elim (H2 r H4 eps H5).
move=> x H6.
exists x.
apply conj.
apply (proj1 H6).
apply conj.
apply (proj1 (proj2 H6)).
apply (proj1 (proj2 (proj2 H6))).
Qed.

Lemma NeighborhoodOpenSetMet : forall (M : Metric_Space) (x : Base M) (eps : R), OpenSetMet M (NeighborhoodMet M x eps).
Proof.
move=> M x d y H1.
exists (d - dist M x y).
apply conj.
rewrite (dist_sym M x y).
apply (Rlt_Rminus (dist M y x) d H1).
move=> z H2.
unfold In.
unfold NeighborhoodMet.
apply (Rle_lt_trans (dist M z x) (dist M z y + dist M x y) d).
rewrite (dist_sym M x y).
apply (dist_tri M z x y).
apply (Rplus_lt_reg_r (- dist M x y)).
rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
apply H2.
Qed.

Lemma OpenSetNotIsolatedR : forall (A : Ensemble R), OpenSetMet R_met A -> forall (r : R), In R A r -> ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r.
Proof.
move=> A H1 r H2 eps H3.
elim (H1 r H2).
move=> dlt H4.
exists (r + Rmin dlt eps  / 2).
apply conj.
unfold NeighborhoodMet.
unfold dist.
simpl.
unfold R_dist.
rewrite (Rplus_comm r (Rmin dlt eps / 2)).
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
rewrite Rabs_pos_eq.
apply (Rlt_le_trans (Rmin dlt eps / 2) (Rmin dlt eps) eps).
apply Rlt_eps2_eps.
apply Rmin_pos.
apply (proj1 H4).
apply H3.
apply (Rmin_r dlt eps).
left.
apply eps2_Rgt_R0.
apply Rmin_pos.
apply (proj1 H4).
apply H3.
apply conj.
apply Rgt_not_eq.
rewrite - {2} (Rplus_0_r r).
apply Rplus_lt_compat_l.
apply eps2_Rgt_R0.
apply Rmin_pos.
apply (proj1 H4).
apply H3.
apply (proj2 H4).
unfold In.
unfold NeighborhoodMet.
unfold dist.
simpl.
unfold R_dist.
rewrite (Rplus_comm r (Rmin dlt eps / 2)).
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
rewrite Rabs_pos_eq.
apply (Rlt_le_trans (Rmin dlt eps / 2) (Rmin dlt eps) dlt).
apply Rlt_eps2_eps.
apply Rmin_pos.
apply (proj1 H4).
apply H3.
apply (Rmin_l dlt eps).
left.
apply eps2_Rgt_R0.
apply Rmin_pos.
apply (proj1 H4).
apply H3.
Qed.

Lemma OpenSetNotIsolatedR_Intersection : forall (A : Ensemble R) (B : Ensemble R), OpenSetMet R_met B -> forall (r : R), In R B r -> ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r -> ClosureMet R_met (fun (x : R) => x <> r /\ In R (Intersection R A B) x) r.
Proof.
move=> A B H1 r H2 H3 eps H4.
elim (H1 r H2).
move=> dlt H5.
elim (H3 (Rmin dlt eps)).
move=> x H6.
exists x.
apply conj.
apply (Rlt_le_trans (R_dist x r) (Rmin dlt eps) eps (proj1 H6) (Rmin_r dlt eps)).
apply conj.
apply (proj1 (proj2 H6)).
apply (Intersection_intro R A B x).
apply (proj2 (proj2 H6)).
apply (proj2 H5).
apply (Rlt_le_trans (R_dist x r) (Rmin dlt eps) dlt (proj1 H6) (Rmin_l dlt eps)).
apply Rmin_pos.
apply (proj1 H5).
apply H4.
Qed.

Definition DifferentiableR_RRn_OpenSet (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H : OpenSetMet R_met B) := forall (r : R), In R B r -> DifferentiableR_RRn K (Intersection R A B) f r.

Definition DifferentiableR_Rn_OpenSet (N : nat) (A : Ensemble R) (f : R -> Rn N) (B : Ensemble R) (H : OpenSetMet R_met B) := forall (r : R), In R B r -> DifferentiableR_Rn N (Intersection R A B) f r.

Definition DifferentiableR_R_OpenSet (A : Ensemble R) (f : R -> R) (B : Ensemble R) (H : OpenSetMet R_met B) := forall (r : R), In R B r -> DifferentiableR_R (Intersection R A B) f r.

Lemma DifferentialR_RRn_OpenSet_Sig : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_RRn_OpenSet K A f B H1), {g : R -> RRnT K | (forall (r : R), ~ (ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) \/ ~ (In R B r) -> g r = RRnO K) /\ forall (r : R) (H3 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H4 : In R B r), g r = DifferentialR_RRn K (Intersection R A B) f r (OpenSetNotIsolatedR_Intersection A B H1 r H4 H3) (H2 r H4)}.
Proof.
move=> K A f B H1 H2.
exists (fun (r : R) => match excluded_middle_informative (ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) with
  | left H3 => match excluded_middle_informative (In R B r) with
    | left H4 => DifferentialR_RRn K (Intersection R A B) f r (OpenSetNotIsolatedR_Intersection A B H1 r H4 H3) (H2 r H4)
    | right _ => RRnO K
  end
  | right _ => RRnO K
end).
apply conj.
move=> r.
elim.
move=> H3.
elim (excluded_middle_informative
    (ClosureMet R_met (fun x : R => x <> r /\ In R A x) r)).
move=> H4.
elim (H3 H4).
move=> H4.
reflexivity.
move=> H3.
elim (excluded_middle_informative
    (ClosureMet R_met (fun x : R => x <> r /\ In R A x) r)).
move=> H4.
elim (excluded_middle_informative (In R B r)).
move=> H5.
elim (H3 H5).
move=> H5.
reflexivity.
move=> H4.
reflexivity.
move=> r H3 H4.
elim (excluded_middle_informative (ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r)).
move=> H5.
elim (excluded_middle_informative (In R B r)).
move=> H6.
suff: (H5 = H3).
move=> H7.
rewrite H7.
suff: (H6 = H4).
move=> H8.
rewrite H8.
reflexivity.
apply proof_irrelevance.
apply proof_irrelevance.
move=> H6.
elim (H6 H4).
move=> H5.
elim (H5 H3).
Qed.

Definition DifferentialR_RRn_OpenSet (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_RRn_OpenSet K A f B H1) := proj1_sig (DifferentialR_RRn_OpenSet_Sig K A f B H1 H2).

Definition DifferentialR_Rn_OpenSet (N : nat) (A : Ensemble R) (f : R -> Rn N) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_Rn_OpenSet N A f B H1) := proj1_sig (DifferentialR_RRn_OpenSet_Sig (RnK N) A f B H1 H2).

Definition DifferentialR_R_OpenSet (A : Ensemble R) (f : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_R_OpenSet A f B H1) := proj1_sig (DifferentialR_RRn_OpenSet_Sig R1K A f B H1 H2).

Definition DifferentialR_RRn_OpenSet_Nature (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_RRn_OpenSet K A f B H1) : (forall (r : R), ~ (ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) \/ ~ (In R B r) -> DifferentialR_RRn_OpenSet K A f B H1 H2 r = RRnO K) /\ forall (r : R) (H3 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H4 : In R B r), DifferentialR_RRn_OpenSet K A f B H1 H2 r = DifferentialR_RRn K (Intersection R A B) f r (OpenSetNotIsolatedR_Intersection A B H1 r H4 H3) (H2 r H4) := proj2_sig (DifferentialR_RRn_OpenSet_Sig K A f B H1 H2).

Definition DifferentialR_Rn_OpenSet_Nature (N : nat) (A : Ensemble R) (f : R -> Rn N) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_Rn_OpenSet N A f B H1) : (forall (r : R), ~ (ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) \/ ~ (In R B r) -> DifferentialR_Rn_OpenSet N A f B H1 H2 r = RnO N) /\ forall (r : R) (H3 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H4 : In R B r), DifferentialR_Rn_OpenSet N A f B H1 H2 r = DifferentialR_Rn N (Intersection R A B) f r (OpenSetNotIsolatedR_Intersection A B H1 r H4 H3) (H2 r H4) := proj2_sig (DifferentialR_RRn_OpenSet_Sig (RnK N) A f B H1 H2).

Definition DifferentialR_R_OpenSet_Nature (A : Ensemble R) (f : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_R_OpenSet A f B H1) : (forall (r : R), ~ (ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) \/ ~ (In R B r) -> DifferentialR_R_OpenSet A f B H1 H2 r = 0) /\ forall (r : R) (H3 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H4 : In R B r), DifferentialR_R_OpenSet A f B H1 H2 r = DifferentialR_R (Intersection R A B) f r (OpenSetNotIsolatedR_Intersection A B H1 r H4 H3) (H2 r H4) := proj2_sig (DifferentialR_RRn_OpenSet_Sig R1K A f B H1 H2).

Lemma DifferentialR_RRn_OpenSet_Nature2 : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_RRn_OpenSet K A f B H1) (g : R -> RRnT K), ((forall (r : R), ~ (ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) \/ ~ (In R B r) -> g r = RRnO K) /\ forall (r : R) (H3 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H4 : In R B r), g r = DifferentialR_RRn K (Intersection R A B) f r (OpenSetNotIsolatedR_Intersection A B H1 r H4 H3) (H2 r H4)) -> DifferentialR_RRn_OpenSet K A f B H1 H2 = g.
Proof.
move=> K A f B H1 H2 g H3.
apply functional_extensionality.
move=> r.
elim (classic (ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r)).
move=> H4.
elim (classic (In R B r)).
move=> H5.
rewrite (proj2 (DifferentialR_RRn_OpenSet_Nature K A f B H1 H2) r H4 H5).
rewrite (proj2 H3 r H4 H5).
reflexivity.
move=> H5.
rewrite (proj1 H3 r).
apply (proj1 (DifferentialR_RRn_OpenSet_Nature K A f B H1 H2) r).
right.
apply H5.
right.
apply H5.
move=> H4.
rewrite (proj1 H3 r).
apply (proj1 (DifferentialR_RRn_OpenSet_Nature K A f B H1 H2) r).
left.
apply H4.
left.
apply H4.
Qed.

Definition DifferentialR_Rn_OpenSet_Nature2 (N : nat) : forall (A : Ensemble R) (f : R -> Rn N) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_Rn_OpenSet N A f B H1) (g : R -> Rn N), ((forall (r : R), ~ (ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) \/ ~ (In R B r) -> g r = RnO N) /\ forall (r : R) (H3 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H4 : In R B r), g r = DifferentialR_Rn N (Intersection R A B) f r (OpenSetNotIsolatedR_Intersection A B H1 r H4 H3) (H2 r H4)) -> DifferentialR_Rn_OpenSet N A f B H1 H2 = g := DifferentialR_RRn_OpenSet_Nature2 (RnK N).

Definition DifferentialR_R_OpenSet_Nature2 : forall (A : Ensemble R) (f : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_R_OpenSet A f B H1) (g : R -> R), ((forall (r : R), ~ (ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) \/ ~ (In R B r) -> g r = 0) /\ forall (r : R) (H3 : ClosureMet R_met (fun (x : R) => x <> r /\ In R A x) r) (H4 : In R B r), g r = DifferentialR_R (Intersection R A B) f r (OpenSetNotIsolatedR_Intersection A B H1 r H4 H3) (H2 r H4)) -> DifferentialR_R_OpenSet A f B H1 H2 = g := DifferentialR_RRn_OpenSet_Nature2 R1K.

Fixpoint repeat (T : Type) (f : T -> T) (n : nat) : T -> T := match n with
  | O => Datatypes.id
  | S m => compose f (repeat T f m)
end.

Lemma repeat_add : forall (T : Type) (f : T -> T) (n m : nat), repeat T f (n + m) = compose (repeat T f n) (repeat T f m).
Proof.
move=> T f.
elim.
move=> m.
reflexivity.
move=> n H1 m.
simpl.
rewrite H1.
reflexivity.
Qed.

Lemma repeat_def2 : forall (T : Type) (f : T -> T), repeat T f = fix rep (n : nat) : T -> T := match n with
  | O => Datatypes.id
  | S m => compose f (repeat T f m)
end.
Proof.
move=> T f.
apply functional_extensionality.
elim.
reflexivity.
move=> n H1.
apply (repeat_add T f 1 n).
Qed.

Definition DifferentialR_RRn_OpenSet_option (K : RRn) (A : Ensemble R) (B : Ensemble R) (H1 : OpenSetMet R_met B) := (fun (g : option (R -> RRnT K)) => match g with
  | None => None
  | Some h => match excluded_middle_informative (DifferentiableR_RRn_OpenSet K A h B H1) with
    | left H => Some (DifferentialR_RRn_OpenSet K A h B H1 H)
    | right _ => None
  end
end).

Definition DifferentialR_RRn_OpenSet_N_sub (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) := repeat (option (R -> RRnT K)) (DifferentialR_RRn_OpenSet_option K A B H1) n (Some f).

Definition DifferentiableR_RRn_OpenSet_N (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) := match DifferentialR_RRn_OpenSet_N_sub K A f B H1 n with
  | None => False
  | Some _ => True
end.

Definition DifferentiableR_Rn_OpenSet_N (N : nat) (A : Ensemble R) (f : R -> Rn N) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) := match DifferentialR_RRn_OpenSet_N_sub (RnK N) A f B H1 n with
  | None => False
  | Some _ => True
end.

Definition DifferentiableR_R_OpenSet_N (A : Ensemble R) (f : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) := match DifferentialR_RRn_OpenSet_N_sub R1K A f B H1 n with
  | None => False
  | Some _ => True
end.

Definition DifferentialR_RRn_OpenSet_N (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R)
  (H1 : OpenSetMet R_met B) (n : nat) : DifferentiableR_RRn_OpenSet_N K A f B H1 n -> R -> RRnT K := option_rec
  (fun (o : option (R -> RRnT K)) =>
   match o with
   | Some _ => True
   | None => False
   end -> R -> RRnT K) (fun (g : R -> RRnT K) (_ : True) => g)
  (fun (H2 : False) => match H2 return (R -> RRnT K) with
                     end : R -> RRnT K)
  (DifferentialR_RRn_OpenSet_N_sub K A f B H1 n).

Definition DifferentialR_Rn_OpenSet_N (N : nat) (A : Ensemble R) (f : R -> Rn N) (B : Ensemble R)
  (H1 : OpenSetMet R_met B) (n : nat) : DifferentiableR_Rn_OpenSet_N N A f B H1 n -> R -> Rn N := DifferentialR_RRn_OpenSet_N (RnK N) A f B H1 n.

Definition DifferentialR_R_OpenSet_N (A : Ensemble R) (f : R -> R) (B : Ensemble R)
  (H1 : OpenSetMet R_met B) (n : nat) : DifferentiableR_R_OpenSet_N A f B H1 n -> R -> R := DifferentialR_RRn_OpenSet_N R1K A f B H1 n.

Lemma DifferentialR_RRn_OpenSet_N_Nature1 : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) (H2 : DifferentiableR_RRn_OpenSet_N K A f B H1 n) (H3 : DifferentiableR_RRn_OpenSet_N K A f B H1 (S n)) (H4 : DifferentiableR_RRn_OpenSet K A (DifferentialR_RRn_OpenSet_N K A f B H1 n H2) B H1), DifferentialR_RRn_OpenSet_N K A f B H1 (S n) H3 = DifferentialR_RRn_OpenSet K A (DifferentialR_RRn_OpenSet_N K A f B H1 n H2) B H1 H4.
Proof.
move=> K A f B H1 n.
unfold DifferentialR_RRn_OpenSet_N.
unfold DifferentiableR_RRn_OpenSet_N.
unfold DifferentialR_RRn_OpenSet_N_sub.
simpl.
unfold compose.
elim (repeat (option (R -> RRnT K))
            (DifferentialR_RRn_OpenSet_option K A B H1) n (Some f)).
move=> g H2.
unfold DifferentialR_RRn_OpenSet_option.
elim (excluded_middle_informative (DifferentiableR_RRn_OpenSet K A g B H1)).
simpl.
move=> H3 H4 H5.
suff: (H3 = H5).
move=> H6.
rewrite H6.
reflexivity.
apply proof_irrelevance.
move=> H3.
elim.
elim.
Qed.

Definition DifferentialR_Rn_OpenSet_N_Nature1 (N : nat) : forall (A : Ensemble R) (f : R -> Rn N) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) (H2 : DifferentiableR_Rn_OpenSet_N N A f B H1 n) (H3 : DifferentiableR_Rn_OpenSet_N N A f B H1 (S n)) (H4 : DifferentiableR_Rn_OpenSet N A (DifferentialR_Rn_OpenSet_N N A f B H1 n H2) B H1), DifferentialR_Rn_OpenSet_N N A f B H1 (S n) H3 = DifferentialR_Rn_OpenSet N A (DifferentialR_Rn_OpenSet_N N A f B H1 n H2) B H1 H4 := DifferentialR_RRn_OpenSet_N_Nature1 (RnK N).

Definition DifferentialR_R_OpenSet_N_Nature1 : forall (A : Ensemble R) (f : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) (H2 : DifferentiableR_R_OpenSet_N A f B H1 n) (H3 : DifferentiableR_R_OpenSet_N A f B H1 (S n)) (H4 : DifferentiableR_R_OpenSet A (DifferentialR_R_OpenSet_N A f B H1 n H2) B H1), DifferentialR_R_OpenSet_N A f B H1 (S n) H3 = DifferentialR_R_OpenSet A (DifferentialR_R_OpenSet_N A f B H1 n H2) B H1 H4 := DifferentialR_RRn_OpenSet_N_Nature1 R1K.

Lemma DifferentialR_RRn_OpenSet_N_Nature2 : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) (H2 : DifferentiableR_RRn_OpenSet K A f B H1) (H3 : DifferentiableR_RRn_OpenSet_N K A f B H1 (S n)) (H4 : DifferentiableR_RRn_OpenSet_N K A (DifferentialR_RRn_OpenSet K A f B H1 H2) B H1 n), DifferentialR_RRn_OpenSet_N K A f B H1 (S n) H3 = DifferentialR_RRn_OpenSet_N K A (DifferentialR_RRn_OpenSet K A f B H1 H2) B H1 n H4.
Proof.
move=> K A f B H1 n.
unfold DifferentialR_RRn_OpenSet_N.
unfold DifferentiableR_RRn_OpenSet_N.
unfold DifferentialR_RRn_OpenSet_N_sub.
suff: (S n = n + 1)%nat.
move=> H2.
rewrite H2.
rewrite repeat_add.
simpl.
rewrite compose_id_right.
unfold DifferentialR_RRn_OpenSet_option at 2.
unfold DifferentialR_RRn_OpenSet_option at 4.
unfold compose.
simpl.
elim (excluded_middle_informative
                (DifferentiableR_RRn_OpenSet K A f B H1)).
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
move=> H3 H4.
elim (H3 H4).
apply (plus_comm 1 n).
Qed.

Definition DifferentialR_Rn_OpenSet_N_Nature2 (N : nat) : forall (A : Ensemble R) (f : R -> Rn N) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) (H2 : DifferentiableR_Rn_OpenSet N A f B H1) (H3 : DifferentiableR_Rn_OpenSet_N N A f B H1 (S n)) (H4 : DifferentiableR_Rn_OpenSet_N N A (DifferentialR_Rn_OpenSet N A f B H1 H2) B H1 n), DifferentialR_Rn_OpenSet_N N A f B H1 (S n) H3 = DifferentialR_Rn_OpenSet_N N A (DifferentialR_Rn_OpenSet N A f B H1 H2) B H1 n H4 := DifferentialR_RRn_OpenSet_N_Nature2 (RnK N).

Definition DifferentialR_R_OpenSet_N_Nature2 : forall (A : Ensemble R) (f : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) (H2 : DifferentiableR_R_OpenSet A f B H1) (H3 : DifferentiableR_R_OpenSet_N A f B H1 (S n)) (H4 : DifferentiableR_R_OpenSet_N A (DifferentialR_R_OpenSet A f B H1 H2) B H1 n), DifferentialR_R_OpenSet_N A f B H1 (S n) H3 = DifferentialR_R_OpenSet_N A (DifferentialR_R_OpenSet A f B H1 H2) B H1 n H4 := DifferentialR_RRn_OpenSet_N_Nature2 R1K.

Lemma DifferentialR_RRn_OpenSet_N_Nature3 : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_RRn_OpenSet_N K A f B H1 O), DifferentialR_RRn_OpenSet_N K A f B H1 O H2 = f.
Proof.
move=> K A f B H1 H2.
reflexivity.
Qed.

Definition DifferentialR_Rn_OpenSet_N_Nature3 (N : nat) : forall (A : Ensemble R) (f : R -> Rn N) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_Rn_OpenSet_N N A f B H1 O), DifferentialR_Rn_OpenSet_N N A f B H1 O H2 = f := DifferentialR_RRn_OpenSet_N_Nature3 (RnK N).

Definition DifferentialR_R_OpenSet_N_Nature3 : forall (A : Ensemble R) (f : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_R_OpenSet_N A f B H1 O), DifferentialR_R_OpenSet_N A f B H1 O H2 = f := DifferentialR_RRn_OpenSet_N_Nature3 R1K.

Lemma DifferentiableR_RRn_OpenSet_N_Nature1 : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) (H2 : DifferentiableR_RRn_OpenSet_N K A f B H1 n), DifferentiableR_RRn_OpenSet_N K A f B H1 (S n) <-> DifferentiableR_RRn_OpenSet K A (DifferentialR_RRn_OpenSet_N K A f B H1 n H2) B H1.
Proof.
move=> K A f B H1 n.
unfold DifferentiableR_RRn_OpenSet_N.
unfold DifferentialR_RRn_OpenSet_N.
unfold DifferentialR_RRn_OpenSet_N_sub.
simpl.
unfold compose.
elim (repeat (option (R -> RRnT K))
            (DifferentialR_RRn_OpenSet_option K A B H1) n (Some f)).
move=> g H2.
unfold DifferentialR_RRn_OpenSet_option.
elim (excluded_middle_informative (DifferentiableR_RRn_OpenSet K A g B H1)).
move=> H3.
apply conj.
move=> H4.
apply H3.
move=> H4.
apply I.
move=> H3.
apply conj.
elim.
move=> H4.
elim (H3 H4).
elim.
Qed.

Definition DifferentiableR_Rn_OpenSet_N_Nature1 (N : nat) : forall (A : Ensemble R) (f : R -> Rn N) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) (H2 : DifferentiableR_Rn_OpenSet_N N A f B H1 n), DifferentiableR_Rn_OpenSet_N N A f B H1 (S n) <-> DifferentiableR_Rn_OpenSet N A (DifferentialR_Rn_OpenSet_N N A f B H1 n H2) B H1 := DifferentiableR_RRn_OpenSet_N_Nature1 (RnK N).

Definition DifferentiableR_R_OpenSet_N_Nature1 : forall (A : Ensemble R) (f : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) (H2 : DifferentiableR_R_OpenSet_N A f B H1 n), DifferentiableR_R_OpenSet_N A f B H1 (S n) <-> DifferentiableR_R_OpenSet A (DifferentialR_R_OpenSet_N A f B H1 n H2) B H1 := DifferentiableR_RRn_OpenSet_N_Nature1 R1K.

Lemma DifferentiableR_RRn_OpenSet_N_Nature2 : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) (H2 : DifferentiableR_RRn_OpenSet K A f B H1), DifferentiableR_RRn_OpenSet_N K A f B H1 (S n) <-> DifferentiableR_RRn_OpenSet_N K A (DifferentialR_RRn_OpenSet K A f B H1 H2) B H1 n.
Proof.
move=> K A f B H1 n.
unfold DifferentiableR_RRn_OpenSet_N.
unfold DifferentialR_RRn_OpenSet_N.
unfold DifferentialR_RRn_OpenSet_N_sub.
suff: (S n = n + 1)%nat.
move=> H2.
rewrite H2.
rewrite repeat_add.
simpl.
rewrite compose_id_right.
simpl.
unfold compose.
unfold DifferentialR_RRn_OpenSet_option.
elim (excluded_middle_informative (DifferentiableR_RRn_OpenSet K A f B H1)).
move=> H3 H4.
suff: (H3 = H4).
move=> H5.
rewrite H5.
apply conj.
move=> H6.
apply H6.
move=> H6.
apply H6.
apply proof_irrelevance.
move=> H3 H4.
elim (H3 H4).
apply (plus_comm 1 n).
Qed.

Definition DifferentiableR_Rn_OpenSet_N_Nature2 (N : nat) : forall (A : Ensemble R) (f : R -> Rn N) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) (H2 : DifferentiableR_Rn_OpenSet N A f B H1), DifferentiableR_Rn_OpenSet_N N A f B H1 (S n) <-> DifferentiableR_Rn_OpenSet_N N A (DifferentialR_Rn_OpenSet N A f B H1 H2) B H1 n := DifferentiableR_RRn_OpenSet_N_Nature2 (RnK N).

Definition DifferentiableR_R_OpenSet_N_Nature2 : forall (A : Ensemble R) (f : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) (H2 : DifferentiableR_R_OpenSet A f B H1), DifferentiableR_R_OpenSet_N A f B H1 (S n) <-> DifferentiableR_R_OpenSet_N A (DifferentialR_R_OpenSet A f B H1 H2) B H1 n := DifferentiableR_RRn_OpenSet_N_Nature2 R1K.

Lemma DifferentiableR_RRn_OpenSet_N_Nature3 : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B), DifferentiableR_RRn_OpenSet_N K A f B H1 O.
Proof.
move=> K A f B H1.
apply I.
Qed.

Definition DifferentiableR_Rn_OpenSet_N_Nature3 (N : nat) : forall (A : Ensemble R) (f : R -> Rn N) (B : Ensemble R) (H1 : OpenSetMet R_met B), DifferentiableR_Rn_OpenSet_N N A f B H1 O := DifferentiableR_RRn_OpenSet_N_Nature3 (RnK N).

Definition DifferentiableR_R_OpenSet_N_Nature3 : forall (A : Ensemble R) (f : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B), DifferentiableR_R_OpenSet_N A f B H1 O := DifferentiableR_RRn_OpenSet_N_Nature3 R1K.

Lemma DifferentiableR_RRn_OpenSet_N_le : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n m : nat), (n <= m)%nat -> DifferentiableR_RRn_OpenSet_N K A f B H1 m -> DifferentiableR_RRn_OpenSet_N K A f B H1 n.
Proof.
move=> K A f B H1 n m.
elim.
apply.
move=> k H2.
unfold DifferentiableR_RRn_OpenSet_N at 3.
unfold DifferentiableR_RRn_OpenSet_N at 1.
unfold DifferentialR_RRn_OpenSet_N_sub.
simpl.
unfold compose.
elim (repeat (option (R -> RRnT K))
      (DifferentialR_RRn_OpenSet_option K A B H1) k (Some f)).
move=> g H3 H4.
apply (H3 I).
move=> H3.
elim.
Qed.

Lemma DifferentiableR_RRn_OpenSet_N_1 : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B), DifferentiableR_RRn_OpenSet_N K A f B H1 1 <-> DifferentiableR_RRn_OpenSet K A f B H1.
Proof.
move=> K A f B H1.
unfold DifferentiableR_RRn_OpenSet_N.
unfold DifferentialR_RRn_OpenSet_N_sub.
simpl.
unfold compose.
simpl.
elim (excluded_middle_informative (DifferentiableR_RRn_OpenSet K A f B H1)).
move=> H2.
apply conj.
move=> H3.
apply H2.
move=> H3.
apply I.
move=> H2.
apply conj.
elim.
move=> H3.
apply (H2 H3).
Qed.

Lemma DifferentialR_RRn_OpenSet_N_1 : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_RRn_OpenSet_N K A f B H1 1) (H3 : DifferentiableR_RRn_OpenSet K A f B H1), DifferentialR_RRn_OpenSet_N K A f B H1 1 H2 = DifferentialR_RRn_OpenSet K A f B H1 H3.
Proof.
move=> K A f B H1.
unfold DifferentialR_RRn_OpenSet_N.
unfold DifferentiableR_RRn_OpenSet_N.
unfold DifferentialR_RRn_OpenSet_N_sub.
simpl.
unfold compose.
simpl.
elim (excluded_middle_informative (DifferentiableR_RRn_OpenSet K A f B H1)).
move=> H2 H3 H4.
suff: (H2 = H4).
move=> H5.
rewrite H5.
reflexivity.
apply proof_irrelevance.
move=> H2.
elim.
Qed.

Lemma DifferentiableR_RRn_OpenSet_N_add : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n m : nat) (H2 : DifferentiableR_RRn_OpenSet_N K A f B H1 n), DifferentiableR_RRn_OpenSet_N K A f B H1 (n + m) <-> DifferentiableR_RRn_OpenSet_N K A (DifferentialR_RRn_OpenSet_N K A f B H1 n H2) B H1 m.
Proof.
move=> K A f B H1 n m.
unfold DifferentiableR_RRn_OpenSet_N.
unfold DifferentialR_RRn_OpenSet_N.
unfold DifferentialR_RRn_OpenSet_N_sub.
rewrite (plus_comm n m).
rewrite (repeat_add (option (R -> RRnT K))
    (fun (g : option (R -> RRnT K)) =>
     match g with
     | Some h =>
         match
           excluded_middle_informative (DifferentiableR_RRn_OpenSet K A h B H1)
         with
         | left H => Some (DifferentialR_RRn_OpenSet K A h B H1 H)
         | right _ => None
         end
     | None => None
     end) m n).
unfold compose.
unfold DifferentialR_RRn_OpenSet_option.
elim (repeat (option (R -> RRnT K))
           (fun (g : option (R -> RRnT K)) =>
            match g with
            | Some h =>
                match
                  excluded_middle_informative
                    (DifferentiableR_RRn_OpenSet K A h B H1)
                with
                | left H => Some (DifferentialR_RRn_OpenSet K A h B H1 H)
                | right _ => None
                end
            | None => None
            end) n (Some f)).
move=> g H2.
apply conj.
move=> H3.
apply H3.
move=> H3.
apply H3.
elim.
Qed.

Lemma DifferentialR_RRn_OpenSet_N_add : forall (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n m : nat) (H2 : DifferentiableR_RRn_OpenSet_N K A f B H1 n) (H3 : DifferentiableR_RRn_OpenSet_N K A f B H1 (n + m)) (H4 : DifferentiableR_RRn_OpenSet_N K A (DifferentialR_RRn_OpenSet_N K A f B H1 n H2) B H1 m), DifferentialR_RRn_OpenSet_N K A f B H1 (n + m) H3 = DifferentialR_RRn_OpenSet_N K A (DifferentialR_RRn_OpenSet_N K A f B H1 n H2) B H1 m H4.
Proof.
move=> K A f B H1 n m.
unfold DifferentiableR_RRn_OpenSet_N.
unfold DifferentialR_RRn_OpenSet_N.
unfold DifferentialR_RRn_OpenSet_N_sub.
rewrite (plus_comm n m).
rewrite (repeat_add (option (R -> RRnT K))
    (DifferentialR_RRn_OpenSet_option K A B H1) m n).
unfold compose.
unfold DifferentialR_RRn_OpenSet_option.
elim (repeat (option (R -> RRnT K))
           (fun (g : option (R -> RRnT K)) =>
            match g with
            | Some h =>
                match
                  excluded_middle_informative
                    (DifferentiableR_RRn_OpenSet K A h B H1)
                with
                | left H => Some (DifferentialR_RRn_OpenSet K A h B H1 H)
                | right _ => None
                end
            | None => None
            end) n (Some f)).
move=> g H2 H3 H4.
suff: (H3 = H4).
move=> H5.
rewrite H5.
reflexivity.
apply proof_irrelevance.
elim.
Qed.

Lemma DifferentialR_RRn_OpenSet_N_plus : forall (K : RRn) (A : Ensemble R) (f g : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat), DifferentiableR_RRn_OpenSet_N K A f B H1 n -> DifferentiableR_RRn_OpenSet_N K A g B H1 n -> DifferentiableR_RRn_OpenSet_N K A (fun (r : R) => RRnplus K (f r) (g r)) B H1 n.
Proof.
suff: (forall (n : nat) (K : RRn) (A : Ensemble R) (f g : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B), DifferentiableR_RRn_OpenSet_N K A f B H1 n -> DifferentiableR_RRn_OpenSet_N K A g B H1 n -> DifferentiableR_RRn_OpenSet_N K A (fun (r : R) => RRnplus K (f r) (g r)) B H1 n).
move=> H1 K A f g B H2 n. 
apply (H1 n K A f g B H2).
elim.
move=> K A f g B H1 H2 H3.
apply I.
move=> n H1 K A f g B H2 H3 H4.
suff: (DifferentiableR_RRn_OpenSet K A f B H2).
move=> H5.
suff: (DifferentiableR_RRn_OpenSet K A g B H2).
move=> H6.
suff: (DifferentiableR_RRn_OpenSet K A (fun (r : R) => RRnplus K (f r) (g r)) B H2).
move=> H7.
apply (proj2 (DifferentiableR_RRn_OpenSet_N_Nature2 K A (fun (r : R) => RRnplus K (f r) (g r)) B H2 n H7)).
suff: (DifferentialR_RRn_OpenSet K A (fun r : R => RRnplus K (f r) (g r)) B H2 H7
= (fun (r : R) => RRnplus K (DifferentialR_RRn_OpenSet K A f B H2 H5 r) (DifferentialR_RRn_OpenSet K A g B H2 H6 r))).
move=> H8.
rewrite H8.
apply H1.
apply (proj1 (DifferentiableR_RRn_OpenSet_N_Nature2 K A f B H2 n H5) H3).
apply (proj1 (DifferentiableR_RRn_OpenSet_N_Nature2 K A g B H2 n H6) H4).
apply DifferentialR_RRn_OpenSet_Nature2.
apply conj.
move=> r H8.
rewrite (proj1 (DifferentialR_RRn_OpenSet_Nature K A f B H2 H5) r H8).
rewrite (proj1 (DifferentialR_RRn_OpenSet_Nature K A g B H2 H6) r H8).
apply (RRnplus_0_l K (RRnO K)).
move=> r H8 H9.
rewrite (Proposition_1_3_1_plus K (Intersection R A B) f g r (OpenSetNotIsolatedR_Intersection A B H2 r H9 H8) (H5 r H9) (H6 r H9)).
rewrite (proj2 (DifferentialR_RRn_OpenSet_Nature K A f B H2 H5) r H8 H9).
rewrite (proj2 (DifferentialR_RRn_OpenSet_Nature K A g B H2 H6) r H8 H9).
reflexivity.
move=> r H7.
apply (Proposition_1_3_1_plus_differentiable K (Intersection R A B) f g r).
apply (H5 r H7).
apply (H6 r H7).
apply DifferentiableR_RRn_OpenSet_N_1.
apply (DifferentiableR_RRn_OpenSet_N_le K A g B H2 1 (S n)).
apply (le_n_S O n (le_0_n n)).
apply H4.
apply DifferentiableR_RRn_OpenSet_N_1.
apply (DifferentiableR_RRn_OpenSet_N_le K A f B H2 1 (S n)).
apply (le_n_S O n (le_0_n n)).
apply H3.
Qed.

Lemma DifferentiableR_RRn_OpenSet_N_plus : forall (K : RRn) (A : Ensemble R) (f g : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) (H2 : DifferentiableR_RRn_OpenSet_N K A f B H1 n) (H3 : DifferentiableR_RRn_OpenSet_N K A g B H1 n) (H4 : DifferentiableR_RRn_OpenSet_N K A (fun (r : R) => RRnplus K (f r) (g r)) B H1 n), DifferentialR_RRn_OpenSet_N K A (fun (r : R) => RRnplus K (f r) (g r)) B H1 n H4 = (fun (r : R) => RRnplus K (DifferentialR_RRn_OpenSet_N K A f B H1 n H2 r) (DifferentialR_RRn_OpenSet_N K A g B H1 n H3 r)).
Proof.
suff: (forall (n : nat) (K : RRn) (A : Ensemble R) (f g : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (H2 : DifferentiableR_RRn_OpenSet_N K A f B H1 n) (H3 : DifferentiableR_RRn_OpenSet_N K A g B H1 n) (H4 : DifferentiableR_RRn_OpenSet_N K A (fun (r : R) => RRnplus K (f r) (g r)) B H1 n), DifferentialR_RRn_OpenSet_N K A (fun (r : R) => RRnplus K (f r) (g r)) B H1 n H4 = (fun (r : R) => RRnplus K (DifferentialR_RRn_OpenSet_N K A f B H1 n H2 r) (DifferentialR_RRn_OpenSet_N K A g B H1 n H3 r))).
move=> H1 K A f g B H2 n H3 H4 H5.
apply (H1 n K A f g B H2 H3 H4 H5).
elim.
move=> K A f g B H1 H2 H3 H4.
reflexivity.
move=> n H1 K A f g B H2 H3 H4 H5.
suff: (DifferentiableR_RRn_OpenSet K A f B H2).
move=> H6.
suff: (DifferentiableR_RRn_OpenSet K A g B H2).
move=> H7.
suff: (DifferentiableR_RRn_OpenSet K A (fun (r : R) => RRnplus K (f r) (g r)) B H2).
move=> H8.
rewrite (DifferentialR_RRn_OpenSet_N_Nature2 K A (fun (r : R) => RRnplus K (f r) (g r)) B H2 n H8).
apply (proj1 (DifferentiableR_RRn_OpenSet_N_Nature2 K A (fun (r : R) => RRnplus K (f r) (g r)) B H2 n H8) H5).
suff: (DifferentialR_RRn_OpenSet K A (fun r : R => RRnplus K (f r) (g r)) B H2 H8
= (fun (r : R) => RRnplus K (DifferentialR_RRn_OpenSet K A f B H2 H6 r) (DifferentialR_RRn_OpenSet K A g B H2 H7 r))).
move=> H9.
rewrite H9.
move=> H10.
rewrite H1.
apply (proj1 (DifferentiableR_RRn_OpenSet_N_Nature2 K A f B H2 n H6) H3).
apply (proj1 (DifferentiableR_RRn_OpenSet_N_Nature2 K A g B H2 n H7) H4).
move=> H11 H12.
apply functional_extensionality.
move=> r.
rewrite (DifferentialR_RRn_OpenSet_N_Nature2 K A f B H2 n H6 H3).
rewrite (DifferentialR_RRn_OpenSet_N_Nature2 K A g B H2 n H7 H4).
reflexivity.
apply DifferentialR_RRn_OpenSet_Nature2.
apply conj.
move=> r H9.
rewrite (proj1 (DifferentialR_RRn_OpenSet_Nature K A f B H2 H6) r H9).
rewrite (proj1 (DifferentialR_RRn_OpenSet_Nature K A g B H2 H7) r H9).
apply (RRnplus_0_l K (RRnO K)).
move=> r H9 H10.
rewrite Proposition_1_3_1_plus.
apply (H6 r H10).
apply (H7 r H10).
move=> H11 H12.
rewrite (proj2 (DifferentialR_RRn_OpenSet_Nature K A f B H2 H6) r H9 H10).
rewrite (proj2 (DifferentialR_RRn_OpenSet_Nature K A g B H2 H7) r H9 H10).
suff: (H6 r H10 = H11).
move=> H13.
suff: (H7 r H10 = H12).
move=> H14.
rewrite H13.
rewrite H14.
reflexivity.
apply proof_irrelevance.
apply proof_irrelevance.
apply DifferentiableR_RRn_OpenSet_N_1.
apply (DifferentiableR_RRn_OpenSet_N_le K A (fun (r : R) => RRnplus K (f r) (g r)) B H2 1 (S n)).
apply (le_n_S O n (le_0_n n)).
apply H5.
apply DifferentiableR_RRn_OpenSet_N_1.
apply (DifferentiableR_RRn_OpenSet_N_le K A g B H2 1 (S n)).
apply (le_n_S O n (le_0_n n)).
apply H4.
apply DifferentiableR_RRn_OpenSet_N_1.
apply (DifferentiableR_RRn_OpenSet_N_le K A f B H2 1 (S n)).
apply (le_n_S O n (le_0_n n)).
apply H3.
Qed.

Lemma Proposition_1_5_R_differentiable : forall (A : Ensemble R) (f g : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat), DifferentiableR_R_OpenSet_N A f B H1 n -> DifferentiableR_R_OpenSet_N A g B H1 n -> DifferentiableR_R_OpenSet_N A (fun (r : R) => f r * g r) B H1 n.
Proof.
suff: (forall (n : nat) (A : Ensemble R) (f g : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B), DifferentiableR_R_OpenSet_N A f B H1 n -> DifferentiableR_R_OpenSet_N A g B H1 n -> DifferentiableR_R_OpenSet_N A (fun (r : R) => f r * g r) B H1 n).
move=> H1 A f g B H2 n H3 H4.
apply (H1 n A f g B H2 H3 H4).
elim.
move=> A f g B H1 H2 H3.
apply I.
move=> n H1 A f g B H2 H3 H4.
suff: (DifferentiableR_R_OpenSet_N A (fun (r : R) => f r * g r) B H2 1).
move=> H5.
suff: (DifferentiableR_R_OpenSet A (fun (r : R) => f r * g r) B H2).
move=> H6.
apply (proj2 (DifferentiableR_RRn_OpenSet_N_add R1K A (fun (r : R) => f r * g r) B H2 1 n H5)).
rewrite (DifferentialR_RRn_OpenSet_N_1 R1K A (fun (r : R) => f r * g r) B H2 H5 H6).
suff: (DifferentiableR_R_OpenSet A f B H2).
move=> H7.
suff: (DifferentiableR_R_OpenSet A g B H2).
move=> H8.
rewrite (DifferentialR_RRn_OpenSet_Nature2 R1K A (fun (r : R) => f r * g r) B H2 H6 (fun (r : R) => DifferentialR_R_OpenSet A f B H2 H7 r * g r + f r * DifferentialR_R_OpenSet A g B H2 H8 r)).
apply (DifferentialR_RRn_OpenSet_N_plus R1K).
apply (H1 A).
apply (proj1 (DifferentiableR_R_OpenSet_N_Nature2 A f B H2 n H7) H3).
apply (DifferentiableR_RRn_OpenSet_N_le R1K A g B H2 n (S n) (le_S n n (le_n n)) H4).
apply (H1 A).
apply (DifferentiableR_RRn_OpenSet_N_le R1K A f B H2 n (S n) (le_S n n (le_n n)) H3).
apply (proj1 (DifferentiableR_R_OpenSet_N_Nature2 A g B H2 n H8) H4).
apply conj.
move=> r H9.
rewrite (proj1 (DifferentialR_R_OpenSet_Nature A f B H2 H7) r H9).
rewrite (proj1 (DifferentialR_R_OpenSet_Nature A g B H2 H8) r H9).
rewrite (Rmult_0_l (g r)).
rewrite (Rmult_0_r (f r)).
apply (Rplus_0_l 0).
move=> r H9 H10.
suff: (DifferentialR_RRn R1K = DifferentialR_R).
move=> H11.
rewrite H11.
rewrite (Proposition_1_3_3_mult_R (Intersection R A B) f g r (OpenSetNotIsolatedR_Intersection A B H2 r H10 H9) 
  (H7 r H10) (H8 r H10) (H6 r H10)).
rewrite (proj2 (DifferentialR_R_OpenSet_Nature A f B H2 H7) r H9 H10).
rewrite (proj2 (DifferentialR_R_OpenSet_Nature A g B H2 H8) r H9 H10).
reflexivity.
reflexivity.
apply (DifferentiableR_RRn_OpenSet_N_1 R1K).
apply (DifferentiableR_RRn_OpenSet_N_le R1K A g B H2 1 (S n)).
apply (le_n_S O n (le_0_n n)).
apply H4.
apply (DifferentiableR_RRn_OpenSet_N_1 R1K).
apply (DifferentiableR_RRn_OpenSet_N_le R1K A f B H2 1 (S n)).
apply (le_n_S O n (le_0_n n)).
apply H3.
apply (DifferentiableR_RRn_OpenSet_N_1 R1K).
apply H5.
apply (DifferentiableR_RRn_OpenSet_N_1 R1K).
move=> r H5.
apply Proposition_1_3_3_mult_R_differentiable.
suff: (DifferentiableR_R_OpenSet A f B H2).
move=> H6.
apply (H6 r H5).
apply (DifferentiableR_RRn_OpenSet_N_1 R1K).
apply (DifferentiableR_RRn_OpenSet_N_le R1K A f B H2 1 (S n)).
apply (le_n_S O n (le_0_n n)).
apply H3.
suff: (DifferentiableR_R_OpenSet A g B H2).
move=> H6.
apply (H6 r H5).
apply (DifferentiableR_RRn_OpenSet_N_1 R1K).
apply (DifferentiableR_RRn_OpenSet_N_le R1K A g B H2 1 (S n)).
apply (le_n_S O n (le_0_n n)).
apply H4.
Qed.

Lemma Proposition_1_5_R : forall (A : Ensemble R) (f g : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat), DifferentiableR_R_OpenSet_N A f B H1 n -> DifferentiableR_R_OpenSet_N A g B H1 n -> forall (H2 : DifferentiableR_R_OpenSet_N A (fun (r : R) => f r * g r) B H1 n) (H3 : forall (m : Count (S n)), DifferentiableR_R_OpenSet_N A f B H1 (proj1_sig m)) (H4 : forall (m : Count (S n)), DifferentiableR_R_OpenSet_N A g B H1 (n - proj1_sig m)%nat), DifferentialR_R_OpenSet_N A (fun (r : R) => f r * g r) B H1 n H2 = (fun (r : R) => MySumF2 (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n))) RPCM (fun (u : Count (S n)) => INR (conv n (proj1_sig u)) * (DifferentialR_R_OpenSet_N A f B H1 (proj1_sig u) (H3 u) r * DifferentialR_R_OpenSet_N A g B H1 (n - proj1_sig u) (H4 u) r))).
Proof.
suff: (forall (n : nat) (A : Ensemble R) (f g : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B), DifferentiableR_R_OpenSet_N A f B H1 n -> DifferentiableR_R_OpenSet_N A g B H1 n -> forall (H2 : DifferentiableR_R_OpenSet_N A (fun (r : R) => f r * g r) B H1 n) (H3 : forall (m : Count (S n)), DifferentiableR_R_OpenSet_N A f B H1 (proj1_sig m)) (H4 : forall (m : Count (S n)), DifferentiableR_R_OpenSet_N A g B H1 (n - proj1_sig m)%nat), DifferentialR_R_OpenSet_N A (fun (r : R) => f r * g r) B H1 n H2 = (fun (r : R) => MySumF2 (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n))) RPCM (fun (u : Count (S n)) => INR (conv n (proj1_sig u)) * (DifferentialR_R_OpenSet_N A f B H1 (proj1_sig u) (H3 u) r * DifferentialR_R_OpenSet_N A g B H1 (n - proj1_sig u) (H4 u) r)))).
move=> H1 A f g B H2 n.
apply (H1 n A f g B H2).
elim.
move=> A f g B H1 H2 H3 H4 H5 H6.
apply functional_extensionality.
move=> r.
rewrite (MySumF2Included (Count 1) (FiniteSingleton (Count 1) (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1)))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
rewrite Rmult_1_l.
reflexivity.
move=> u.
elim.
move=> u0.
elim.
suff: (u0 = (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1))).
move=> H7.
rewrite H7.
apply In_singleton.
apply sig_map.
simpl.
elim (le_lt_or_eq (proj1_sig u0) O (le_S_n (proj1_sig u0) O (proj2_sig u0))).
move=> H7.
elim (le_not_lt O (proj1_sig u0) (le_0_n (proj1_sig u0)) H7).
move=> H7.
apply H7.
move=> u H7.
apply Full_intro.
move=> n H1 A f g B H2 H3 H4 H5 H6 H7.
suff: (DifferentiableR_R_OpenSet A (fun (r : R) => f r * g r) B H2).
move=> H8.
suff: (DifferentiableR_RRn_OpenSet_N R1K A
                (DifferentialR_RRn_OpenSet R1K A (fun r : R => f r * g r) B
                   H2 H8) B H2 n).
move=> H9.
suff: (DifferentialR_R_OpenSet_N = DifferentialR_RRn_OpenSet_N R1K).
move=> H10.
suff: (DifferentiableR_R_OpenSet A f B H2).
move=> H11.
suff: (DifferentiableR_R_OpenSet A g B H2).
move=> H12.
rewrite H10.
rewrite (DifferentialR_RRn_OpenSet_N_Nature2 R1K A (fun (r : R) => f r * g r) B H2 n H8 H5 H9).
move: H9.
rewrite (DifferentialR_RRn_OpenSet_Nature2 R1K A (fun (r : R) => f r * g r) B H2 H8 (fun (r : R) => DifferentialR_R_OpenSet A f B H2 H11 r * g r + f r * DifferentialR_R_OpenSet A g B H2 H12 r)).
move=> H9.
rewrite (DifferentiableR_RRn_OpenSet_N_plus R1K).
apply Proposition_1_5_R_differentiable.
apply (proj1 (DifferentiableR_R_OpenSet_N_Nature2 A f B H2 n H11) H3).
apply (DifferentiableR_RRn_OpenSet_N_le R1K A g B H2 n (S n) (le_S n n (le_n n)) H4).
apply Proposition_1_5_R_differentiable.
apply (DifferentiableR_RRn_OpenSet_N_le R1K A f B H2 n (S n) (le_S n n (le_n n)) H3).
apply (proj1 (DifferentiableR_R_OpenSet_N_Nature2 A g B H2 n H12) H4).
move=> H13 H14.
apply functional_extensionality.
move=> r.
rewrite - H10.
rewrite (H1 A (fun (r : R) => DifferentialR_R_OpenSet A f B H2 H11 r) g B H2).
move=> m.
apply (DifferentiableR_RRn_OpenSet_N_le R1K A (fun (r : R) => DifferentialR_R_OpenSet A f B H2 H11 r) B H2 (proj1_sig m) n (le_S_n (proj1_sig m) n (proj2_sig m))).
apply (proj1 (DifferentiableR_R_OpenSet_N_Nature2 A f B H2 n H11) H3).
move=> m.
apply (DifferentiableR_RRn_OpenSet_N_le R1K A g B H2 (n - proj1_sig m) (S n)).
apply (le_S (n - proj1_sig m) n).
apply (plus_le_reg_l (n - proj1_sig m) n (proj1_sig m)).
rewrite (le_plus_minus_r (proj1_sig m) n (le_S_n (proj1_sig m) n (proj2_sig m))).
apply (le_plus_r (proj1_sig m) n).
apply H4.
move=> H15 H16.
rewrite (H1 A f (fun (r : R) => DifferentialR_R_OpenSet A g B H2 H12 r) B H2).
move=> m.
apply (DifferentiableR_RRn_OpenSet_N_le R1K A f B H2 (proj1_sig m) (S n) (le_S (proj1_sig m) n (le_S_n (proj1_sig m) n (proj2_sig m)))).
apply H3.
move=> m.
apply (DifferentiableR_RRn_OpenSet_N_le R1K A (fun (r : R) => DifferentialR_R_OpenSet A g B H2 H12 r) B H2 (n - proj1_sig m) n).
apply (plus_le_reg_l (n - proj1_sig m) n (proj1_sig m)).
rewrite (le_plus_minus_r (proj1_sig m) n (le_S_n (proj1_sig m) n (proj2_sig m))).
apply (le_plus_r (proj1_sig m) n).
apply (proj1 (DifferentiableR_R_OpenSet_N_Nature2 A g B H2 n H12) H4).
move=> H17 H18.
elim (MySumF2Sn2_exists (S n)).
move=> H19.
elim.
move=> H20 H21.
suff: (forall (m : Count (S (S n))), proj1_sig m <> O -> pred (proj1_sig m) < S n)%nat.
move=> H22.
rewrite - (Rplus_0_r (MySumF2 (Count (S n))
     (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n)))
     RPCM
     (fun (u : Count (S n)) =>
      INR (conv n (proj1_sig u)) *
      (DifferentialR_R_OpenSet_N A
         (fun (r : R) => DifferentialR_R_OpenSet A f B H2 H11 r) B H2
         (proj1_sig u) (H15 u) r *
       DifferentialR_R_OpenSet_N A g B H2 (n - proj1_sig u) (H16 u) r)))).
suff: (MySumF2 (Count (S (S n)))
(exist (Finite (Count (S (S n)))) (Full_set (Count (S (S n))))
              (CountFinite (S (S n))))
RPCM (fun (m : (Count (S (S n)))) => match excluded_middle_informative (proj1_sig m = O) with
  | left _ => 0  
  | right H => INR (conv n (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H)))) *
      (DifferentialR_R_OpenSet_N A
         (fun (r : R) => DifferentialR_R_OpenSet A f B H2 H11 r) B H2
         (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) (H15 (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) r *
       DifferentialR_R_OpenSet_N A g B H2 (n - proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) (H16 (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) r)
end)
=
MySumF2 (Count (S n))
     (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n)))
     RPCM
     (fun (u : Count (S n)) =>
      INR (conv n (proj1_sig u)) *
      (DifferentialR_R_OpenSet_N A
         (fun r0 : R => DifferentialR_R_OpenSet A f B H2 H11 r0) B H2
         (proj1_sig u) (H15 u) r *
       DifferentialR_R_OpenSet_N A g B H2 (n - proj1_sig u) (H16 u) r)) + 0).
move=> H23.
rewrite - H23.
rewrite - (Rplus_0_r (MySumF2 (Count (S n))
     (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n)))
     RPCM
     (fun (u : Count (S n)) =>
      INR (conv n (proj1_sig u)) *
      (DifferentialR_R_OpenSet_N A f B H2 (proj1_sig u) (H17 u) r *
       DifferentialR_R_OpenSet_N A
         (fun (r : R) => DifferentialR_R_OpenSet A g B H2 H12 r) B H2
         (n - proj1_sig u) (H18 u) r)))).
suff: (MySumF2 (Count (S (S n)))
(exist (Finite (Count (S (S n)))) (Full_set (Count (S (S n))))
              (CountFinite (S (S n))))
RPCM (fun (m : (Count (S (S n)))) => match excluded_middle_informative (proj1_sig m < S n)%nat with
  | left H => INR (conv n (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H))) *
(DifferentialR_R_OpenSet_N A f B H2 (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) (H17 (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) r *
       DifferentialR_R_OpenSet_N A
         (fun (r : R) => DifferentialR_R_OpenSet A g B H2 H12 r) B H2
         (n - proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) (H18 (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) r)      
  | right _ => 0
end)
= MySumF2 (Count (S n))
        (exist (Finite (Count (S n))) (Full_set (Count (S n)))
           (CountFinite (S n))) RPCM
        (fun (u : Count (S n)) =>
      INR (conv n (proj1_sig u)) *
      (DifferentialR_R_OpenSet_N A f B H2 (proj1_sig u) (H17 u) r *
       DifferentialR_R_OpenSet_N A
         (fun (r : R) => DifferentialR_R_OpenSet A g B H2 H12 r) B H2
         (n - proj1_sig u) (H18 u) r)) + 0).
move=> H24.
rewrite - H24.
suff: (RRnplus R1K = CMc RPCM).
move=> H25.
rewrite H25.
rewrite - (MySumF2Distr (Count (S (S n))) RPCM (exist (Finite (Count (S (S n)))) (Full_set (Count (S (S n))))
     (CountFinite (S (S n)))) (fun (m : (Count (S (S n)))) => match excluded_middle_informative (proj1_sig m = O) with
  | left _ => 0  
  | right H => INR (conv n (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H)))) *
      (DifferentialR_R_OpenSet_N A
         (fun (r : R) => DifferentialR_R_OpenSet A f B H2 H11 r) B H2
         (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) (H15 (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) r *
       DifferentialR_R_OpenSet_N A g B H2 (n - proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) (H16 (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) r)
end)
(fun (m : (Count (S (S n)))) => match excluded_middle_informative (proj1_sig m < S n)%nat with
  | left H => INR (conv n (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H))) *
(DifferentialR_R_OpenSet_N A f B H2 (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) (H17 (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) r *
       DifferentialR_R_OpenSet_N A
         (fun (r : R) => DifferentialR_R_OpenSet A g B H2 H12 r) B H2
         (n - proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) (H18 (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) r)      
  | right _ => 0
end)
(fun (u : Count (S (S n))) =>
   INR (conv (S n) (proj1_sig u)) *
   (DifferentialR_R_OpenSet_N A f B H2 (proj1_sig u) (H6 u) r *
    DifferentialR_R_OpenSet_N A g B H2 (S n - proj1_sig u) (H7 u) r))).
reflexivity.
move=> u H26.
elim (excluded_middle_informative (proj1_sig u < S n)%nat).
move=> H27.
elim (excluded_middle_informative (proj1_sig u = O)).
move=> H28.
simpl.
rewrite {1} H28.
rewrite {3} H28.
suff: (conv n 0 = 1%nat).
move=> H29.
rewrite H29.
simpl.
rewrite Rplus_0_l.
suff: (H6 u = H17 (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig u) H27)).
move=> H30.
rewrite H30.
rewrite - (DifferentialR_R_OpenSet_N_Nature2 A g B H2 (n - proj1_sig u) H12).
rewrite minus_Sn_m.
apply (H7 u).
apply (le_S_n (proj1_sig u) n H27).
rewrite minus_Sn_m.
move=> H31.
suff: (H31 = H7 u).
move=> H32.
rewrite H32.
reflexivity.
apply proof_irrelevance.
apply (le_S_n (proj1_sig u) n H27).
apply proof_irrelevance.
elim n.
reflexivity.
move=> k H29.
reflexivity.
move=> H28.
simpl.
rewrite - (DifferentialR_R_OpenSet_N_Nature2 A f B H2 (pred (proj1_sig u)) H11).
suff: (proj1_sig u <> O).
suff: (proj1_sig u < S n)%nat.
elim (proj1_sig u).
move=> H29.
elim.
reflexivity.
move=> m H29 H30 H31.
apply (DifferentiableR_RRn_OpenSet_N_le R1K A f B H2 (S m) (S n)).
apply (lt_le_weak (S m) (S n) H30).
apply H3.
apply H27.
apply H28.
suff: (S (pred (proj1_sig u)) = proj1_sig u).
move=> H29.
rewrite H29.
move=> H30.
rewrite - DifferentialR_R_OpenSet_N_Nature2.
apply (DifferentiableR_RRn_OpenSet_N_le R1K A g B H2 (S (n - proj1_sig u)) (S n)).
apply le_n_S.
apply (plus_le_reg_l (n - proj1_sig u) n (proj1_sig u)).
rewrite (le_plus_minus_r (proj1_sig u) n).
apply le_plus_r.
apply (le_S_n (proj1_sig u) n H27).
apply H4.
suff: (S (n - proj1_sig u) = n - pred (proj1_sig u))%nat.
move=> H31.
rewrite H31.
move=> H32.
suff: (H30 = H17 (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig u) H27)).
move=> H33.
rewrite H33.
suff: (H16
      (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig u))
         (H22 u H28)) = H32).
move=> H34.
rewrite H34.
rewrite - Rmult_plus_distr_r.
suff: (INR match proj1_sig u with
    | O => 1
    | S k => conv n k + conv n (S k)
    end = INR (conv n (pred (proj1_sig u))) + INR (conv n (proj1_sig u))).
move=> H35.
rewrite H35.
apply Rmult_eq_compat_l.
simpl.
suff: (H6 u = H17 (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig u) H27)).
move=> H36.
rewrite H36.
apply Rmult_eq_compat_l.
suff: (forall (n m : nat), n = m -> forall (H37 : DifferentiableR_R_OpenSet_N A g B H2 n) (H38 : DifferentiableR_R_OpenSet_N A g B H2 m), DifferentialR_R_OpenSet_N A g B H2 n H37 r = DifferentialR_R_OpenSet_N A g B H2 m H38 r).
move=> H37.
apply H37.
suff: (proj1_sig u <> O).
elim (proj1_sig u).
elim.
reflexivity.
move=> m H38 H39.
reflexivity.
apply H28.
move=> m k H37.
rewrite H37.
move=> H38 H39.
suff: (H38 = H39).
move=> H40.
rewrite H40.
reflexivity.
apply proof_irrelevance.
apply proof_irrelevance.
suff: (proj1_sig u <> O).
elim (proj1_sig u).
elim.
reflexivity.
move=> m H35 H36.
apply plus_INR.
apply H28.
apply proof_irrelevance.
apply proof_irrelevance.
suff: (proj1_sig u < S n)%nat.
suff: (proj1_sig u <> O).
elim (proj1_sig u).
elim.
reflexivity.
move=> m H31 H32 H33.
apply minus_Sn_m.
apply (le_S_n (S m) n H33).
apply H28.
apply H27.
suff: (proj1_sig u <> O).
elim (proj1_sig u).
elim.
reflexivity.
move=> m H29 H30.
reflexivity.
apply H28.
move=> H27.
elim (excluded_middle_informative (proj1_sig u = O)).
move=> H28.
elim H27.
rewrite H28.
apply (le_n_S O n (le_0_n n)).
move=> H28.
simpl.
rewrite Rplus_0_r.
suff: (S (pred (proj1_sig u)) = proj1_sig u).
move=> H29.
rewrite - DifferentialR_R_OpenSet_N_Nature2.
rewrite H29.
apply (H6 u).
rewrite H29.
move=> H30.
suff: (H6 u = H30).
move=> H31.
rewrite H31.
suff: (INR match proj1_sig u with
    | O => 1
    | S k => conv n k + conv n (S k)
    end = INR (conv n (pred (proj1_sig u)))).
move=> H32.
rewrite H32.
suff: (DifferentialR_R_OpenSet_N A g B H2
   match proj1_sig u with
   | O => S n
   | S l => n - l
   end (H7 u) r = DifferentialR_R_OpenSet_N A g B H2 (n - pred (proj1_sig u))
   (H16
      (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig u))
         (H22 u H28))) r).
move=> H33.
rewrite H33.
reflexivity.
suff: (forall (n m : nat), n = m -> forall (H33 : DifferentiableR_R_OpenSet_N A g B H2 n) (H34 : DifferentiableR_R_OpenSet_N A g B H2 m), DifferentialR_R_OpenSet_N A g B H2 n H33 r = DifferentialR_R_OpenSet_N A g B H2 m H34 r).
move=> H33.
apply H33.
suff: (proj1_sig u <> O).
elim (proj1_sig u).
elim.
reflexivity.
move=> m H34 H35.
reflexivity.
apply H28.
move=> m k H33.
rewrite H33.
move=> H34 H35.
suff: (H34 = H35).
move=> H36.
rewrite H36.
reflexivity.
apply proof_irrelevance.
suff: (proj1_sig u = S n).
move=> H32.
rewrite H32.
rewrite (proj2 (conv_fact n) (S n) (le_n (S n))).
rewrite plus_comm.
reflexivity.
elim (le_lt_or_eq (proj1_sig u) (S n)).
move=> H32.
elim (H27 H32).
move=> H32.
apply H32.
apply (le_S_n (proj1_sig u) (S n) (proj2_sig u)).
apply proof_irrelevance.
suff: (proj1_sig u <> O).
elim (proj1_sig u).
elim.
reflexivity.
move=> m H29 H30.
reflexivity.
apply H28.
reflexivity.
rewrite (H21 RPCM).
simpl.
elim (excluded_middle_informative (S n < S n)%nat).
move=> H24.
elim (lt_irrefl (S n) H24).
move=> H24.
apply Rplus_eq_compat_r.
apply f_equal.
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (proj1_sig m < S n)%nat).
move=> H25.
suff: (H17 (exist (fun k : nat => (k < S n)%nat) (proj1_sig m) H25) = H17 m).
move=> H26.
suff: (H18 (exist (fun k : nat => (k < S n)%nat) (proj1_sig m) H25) = H18 m).
move=> H27.
rewrite H26.
rewrite H27.
reflexivity.
apply proof_irrelevance.
apply proof_irrelevance.
move=> H25.
elim (H25 (proj2_sig m)).
rewrite (MySumF2Included (Count (S (S n))) (FiniteIm (Count (S (S n))) (Count (S (S n)))
(fun (m : Count (S (S n))) => match excluded_middle_informative (proj1_sig m < S n)%nat with
  | left H => exist (fun (k : nat) => (k < S (S n))%nat) (S (proj1_sig m)) (le_n_S (S (proj1_sig m)) (S n) H)
  | right _ => exist (fun (k : nat) => (k < S (S n))%nat) O (le_n_S O (S n) (le_0_n (S n)))
end)
(exist (Finite (Count (S (S n)))) (Full_set (Count (S (S n))))
     (CountFinite (S (S n)))))
  (exist (Finite (Count (S (S n)))) (Full_set (Count (S (S n))))
     (CountFinite (S (S n)))) RPCM).
rewrite - MySumF2BijectiveSame2.
rewrite (H21 RPCM).
rewrite (MySumF2O (Count (S (S n)))).
rewrite CM_O_r.
unfold compose.
simpl.
elim (excluded_middle_informative (S n < S n)%nat).
move=> H23.
elim (lt_irrefl (S n) H23).
move=> H23.
simpl.
elim (excluded_middle_informative (O = O)).
move=> H24.
apply Rplus_eq_compat_r.
apply f_equal.
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (proj1_sig m < S n)%nat).
move=> H25.
simpl.
elim (excluded_middle_informative (S (proj1_sig m) = O)).
move=> H26.
elim (lt_irrefl (S (proj1_sig m))).
rewrite {1} H26.
apply (le_n_S O (proj1_sig m) (le_0_n (proj1_sig m))).
move=> H26.
suff: (H15 (exist (fun k : nat => (k < S n)%nat) (proj1_sig m)
         (H22
            (exist (fun (k : nat) => (k < S (S n))%nat) 
               (S (proj1_sig m)) (le_n_S (S (proj1_sig m)) (S n) H25)) H26)) = H15 m).
move=> H27.
rewrite H27.
suff: (H16 (exist (fun k : nat => (k < S n)%nat) (proj1_sig m)
         (H22
            (exist (fun (k : nat) => (k < S (S n))%nat) 
               (S (proj1_sig m)) (le_n_S (S (proj1_sig m)) (S n) H25)) H26)) = H16 m).
move=> H28.
rewrite H28.
reflexivity.
apply proof_irrelevance.
apply proof_irrelevance.
move=> H25.
elim (H25 (proj2_sig m)).
elim.
reflexivity.
move=> u.
elim.
move=> u0 H23 H24.
elim H23.
elim u0.
elim.
move=> H25.
apply (Im_intro (Count (S (S n))) (Count (S (S n))) (Full_set (Count (S (S n)))) (fun (m : Count (S (S n))) =>
         match excluded_middle_informative (proj1_sig m < S n)%nat with
         | left H =>
             exist (fun (k : nat) => (k < S (S n))%nat) 
               (S (proj1_sig m)) (le_n_S (S (proj1_sig m)) (S n) H)
         | right _ =>
             exist (fun (k : nat) => (k < S (S n))%nat) 0%nat
               (le_n_S 0 (S n) (le_0_n (S n)))
         end) (exist (fun (k : nat) => (k < S (S n))%nat) (S n) (le_n (S (S n))))).
apply (Full_intro (Count (S (S n)))).
simpl.
elim (excluded_middle_informative (S n < S n)%nat).
move=> H26.
elim (lt_irrefl (S n) H26).
move=> H26.
apply sig_map.
reflexivity.
move=> m H25 H26.
apply (Im_intro (Count (S (S n))) (Count (S (S n))) (Full_set (Count (S (S n)))) (fun (m : Count (S (S n))) =>
         match excluded_middle_informative (proj1_sig m < S n)%nat with
         | left H =>
             exist (fun (k : nat) => (k < S (S n))%nat) 
               (S (proj1_sig m)) (le_n_S (S (proj1_sig m)) (S n) H)
         | right _ =>
             exist (fun (k : nat) => (k < S (S n))%nat) 0%nat
               (le_n_S 0 (S n) (le_0_n (S n)))
         end) (exist (fun (k : nat) => (k < S (S n))%nat) m (le_trans (S m) (S (S m)) (S (S n)) (le_S (S m) (S m) (le_n (S m))) H26))).
apply (Full_intro (Count (S (S n)))).
simpl.
elim (excluded_middle_informative (m < S n)%nat).
move=> H27.
apply sig_map.
reflexivity.
move=> H27.
elim (H27 (le_S_n (S m) (S n) H26)).
move=> u1 u2 H23 H24 .
elim (excluded_middle_informative (proj1_sig u1 < S n)%nat).
move=> H25.
elim (excluded_middle_informative (proj1_sig u2 < S n)%nat).
move=> H26 H27.
apply sig_map.
suff: (proj1_sig u1 = pred (proj1_sig (exist (fun (k : nat) => (k < S (S n))%nat) (S (proj1_sig u1))
        (le_n_S (S (proj1_sig u1)) (S n) H25)))).
move=> H28.
rewrite H28.
rewrite H27.
reflexivity.
reflexivity.
move=> H26 H27.
elim (lt_irrefl (proj1_sig (exist (fun (k : nat) => (k < S (S n))%nat) (S (proj1_sig u1))
  (le_n_S (S (proj1_sig u1)) (S n) H25)))).
rewrite {1} H27.
apply (le_n_S O (proj1_sig u1) (le_0_n (proj1_sig u1))).
move=> H25.
elim (excluded_middle_informative (proj1_sig u2 < S n)%nat).
move=> H26 H27.
elim (lt_irrefl (proj1_sig (exist (fun (k : nat) => (k < S (S n))%nat) O
  (le_n_S 0 (S n) (le_0_n (S n)))))).
rewrite {2} H27.
apply (le_n_S O (proj1_sig u2) (le_0_n (proj1_sig u2))).
move=> H26 H27.
apply sig_map.
elim (le_lt_or_eq (proj1_sig u1) (S n)).
move=> H28.
elim (H25 H28).
elim (le_lt_or_eq (proj1_sig u2) (S n)).
move=> H29.
elim (H26 H29).
move=> H28 H29.
rewrite H28.
apply H29.
apply (le_S_n (proj1_sig u2) (S n) (proj2_sig u2)).
apply (le_S_n (proj1_sig u1) (S n) (proj2_sig u1)).
move=> u H23.
apply (Full_intro (Count (S (S n))) u).
move=> m.
suff: (proj1_sig m < S (S n))%nat.
elim (proj1_sig m).
move=> H22.
elim.
reflexivity.
move=> k H22 H23 H24.
apply (le_S_n (S k) (S n) H23).
apply (proj2_sig m).
apply (DifferentiableR_RRn_OpenSet_N_le R1K A f B H2 n (S n) (le_S n n (le_n n)) H3).
apply (proj1 (DifferentiableR_RRn_OpenSet_N_Nature2 R1K A g B H2 n H12) H4).
apply (proj1 (DifferentiableR_RRn_OpenSet_N_Nature2 R1K A f B H2 n H11) H3).
apply (DifferentiableR_RRn_OpenSet_N_le R1K A g B H2 n (S n) (le_S n n (le_n n)) H4).
apply conj.
move=> r H13.
rewrite (proj1 (DifferentialR_R_OpenSet_Nature A f B H2 H11) r H13).
rewrite (proj1 (DifferentialR_R_OpenSet_Nature A g B H2 H12) r H13).
rewrite (Rmult_0_l (g r)).
rewrite (Rmult_0_r (f r)).
apply (Rplus_0_l 0).
move=> r H13 H14.
rewrite (proj2 (DifferentialR_R_OpenSet_Nature A f B H2 H11) r H13 H14).
rewrite (proj2 (DifferentialR_R_OpenSet_Nature A g B H2 H12) r H13 H14).
rewrite - (Proposition_1_3_3_mult_R (Intersection R A B) f g r (OpenSetNotIsolatedR_Intersection A B H2 r H14 H13) 
  (H11 r H14) (H12 r H14) (H8 r H14)).
reflexivity.
apply (DifferentiableR_RRn_OpenSet_N_1 R1K A g B H2).
apply (DifferentiableR_RRn_OpenSet_N_le R1K A g B H2 1 (S n) (le_n_S O n (le_0_n n)) H4).
apply (DifferentiableR_RRn_OpenSet_N_1 R1K A f B H2).
apply (DifferentiableR_RRn_OpenSet_N_le R1K A f B H2 1 (S n) (le_n_S O n (le_0_n n)) H3).
reflexivity.
apply (proj1 (DifferentiableR_RRn_OpenSet_N_Nature2 R1K A (fun (r : R) => f r * g r) B H2 n H8) H5).
apply (DifferentiableR_RRn_OpenSet_N_1 R1K A (fun (r : R) => f r * g r) B H2).
apply (DifferentiableR_RRn_OpenSet_N_le R1K A (fun (r : R) => f r * g r) B H2 1 (S n) (le_n_S O n (le_0_n n)) H5).
Qed.

Lemma Proposition_1_5_R_exists : forall (A : Ensemble R) (f g : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat), DifferentiableR_R_OpenSet_N A f B H1 n -> DifferentiableR_R_OpenSet_N A g B H1 n -> exists (H2 : DifferentiableR_R_OpenSet_N A (fun (r : R) => f r * g r) B H1 n) (H3 : forall (m : Count (S n)), DifferentiableR_R_OpenSet_N A f B H1 (proj1_sig m)) (H4 : forall (m : Count (S n)), DifferentiableR_R_OpenSet_N A g B H1 (n - proj1_sig m)%nat), DifferentialR_R_OpenSet_N A (fun (r : R) => f r * g r) B H1 n H2 = (fun (r : R) => MySumF2 (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n))) RPCM (fun (u : Count (S n)) => INR (conv n (proj1_sig u)) * (DifferentialR_R_OpenSet_N A f B H1 (proj1_sig u) (H3 u) r * DifferentialR_R_OpenSet_N A g B H1 (n - proj1_sig u) (H4 u) r))).
Proof.
move=> A f g B H1 n H2 H3.
suff: (DifferentiableR_R_OpenSet_N A (fun (r : R) => f r * g r) B H1 n).
move=> H4.
suff: (forall (m : Count (S n)),
      DifferentiableR_R_OpenSet_N A f B H1 (proj1_sig m)).
move=> H5.
suff: (forall (m : Count (S n)),
      DifferentiableR_R_OpenSet_N A g B H1 (n - proj1_sig m)).
move=> H6.
exists H4.
exists H5.
exists H6.
apply (Proposition_1_5_R A f g B H1 n H2 H3 H4 H5 H6).
move=> m.
apply (DifferentiableR_RRn_OpenSet_N_le R1K A g B H1 (n - proj1_sig m) n).
apply (plus_le_reg_l (n - proj1_sig m) n (proj1_sig m)).
rewrite (le_plus_minus_r (proj1_sig m) n).
apply (le_plus_r (proj1_sig m) n).
apply (le_S_n (proj1_sig m) n (proj2_sig m)).
apply H3.
move=> m.
apply (DifferentiableR_RRn_OpenSet_N_le R1K A f B H1 (proj1_sig m) n).
apply (le_S_n (proj1_sig m) n (proj2_sig m)).
apply H2.
apply Proposition_1_5_R_differentiable.
apply H2.
apply H3.
Qed.

Lemma Proposition_1_5_C_differentiable : forall (A : Ensemble R) (f g : R -> C) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat), DifferentiableR_Rn_OpenSet_N 2 A f B H1 n -> DifferentiableR_Rn_OpenSet_N 2 A g B H1 n -> DifferentiableR_Rn_OpenSet_N 2 A (fun (r : R) => Cmult (f r) (g r)) B H1 n.
Proof.
suff: (forall (n : nat) (A : Ensemble R) (f g : R -> C) (B : Ensemble R) (H1 : OpenSetMet R_met B), DifferentiableR_Rn_OpenSet_N 2 A f B H1 n -> DifferentiableR_Rn_OpenSet_N 2 A g B H1 n -> DifferentiableR_Rn_OpenSet_N 2 A (fun (r : R) => Cmult (f r) (g r)) B H1 n).
move=> H1 A f g B H2 n H3 H4.
apply (H1 n A f g B H2 H3 H4).
elim.
move=> A f g B H1 H2 H3.
apply I.
move=> n H1 A f g B H2 H3 H4.
suff: (DifferentiableR_Rn_OpenSet_N 2 A (fun (r : R) => Cmult (f r) (g r)) B H2 1).
move=> H5.
suff: (DifferentiableR_Rn_OpenSet 2 A (fun (r : R) => Cmult (f r) (g r)) B H2).
move=> H6.
apply (proj2 (DifferentiableR_RRn_OpenSet_N_add (RnK 2) A (fun (r : R) => Cmult (f r) (g r)) B H2 1 n H5)).
rewrite (DifferentialR_RRn_OpenSet_N_1 (RnK 2) A (fun (r : R) => Cmult (f r) (g r)) B H2 H5 H6).
suff: (DifferentiableR_Rn_OpenSet 2 A f B H2).
move=> H7.
suff: (DifferentiableR_Rn_OpenSet 2 A g B H2).
move=> H8.
rewrite (DifferentialR_RRn_OpenSet_Nature2 (RnK 2) A (fun (r : R) => Cmult (f r) (g r)) B H2 H6 (fun (r : R) => Cplus (Cmult (DifferentialR_Rn_OpenSet 2 A f B H2 H7 r) (g r)) (Cmult (f r) (DifferentialR_Rn_OpenSet 2 A g B H2 H8 r)))).
apply (DifferentialR_RRn_OpenSet_N_plus (RnK 2)).
apply (H1 A).
apply (proj1 (DifferentiableR_Rn_OpenSet_N_Nature2 2 A f B H2 n H7) H3).
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A g B H2 n (S n) (le_S n n (le_n n)) H4).
apply (H1 A).
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A f B H2 n (S n) (le_S n n (le_n n)) H3).
apply (proj1 (DifferentiableR_Rn_OpenSet_N_Nature2 2 A g B H2 n H8) H4).
apply conj.
move=> r H9.
rewrite (proj1 (DifferentialR_Rn_OpenSet_Nature 2 A f B H2 H7) r H9).
rewrite (proj1 (DifferentialR_Rn_OpenSet_Nature 2 A g B H2 H8) r H9).
rewrite (Fmul_O_l Cfield (g r) : Cmult (RnO 2) (g r) = CO).
rewrite (Fmul_O_r Cfield (f r) : Cmult (f r) (RnO 2) = CO).
apply (Cplus_0_l CO).
move=> r H9 H10.
suff: (DifferentialR_RRn (RnK 2) = DifferentialR_Rn 2).
move=> H11.
rewrite H11.
rewrite (Proposition_1_3_3_mult_C (Intersection R A B) f g r (OpenSetNotIsolatedR_Intersection A B H2 r H10 H9) 
  (H7 r H10) (H8 r H10) (H6 r H10)).
rewrite (proj2 (DifferentialR_Rn_OpenSet_Nature 2 A f B H2 H7) r H9 H10).
rewrite (proj2 (DifferentialR_Rn_OpenSet_Nature 2 A g B H2 H8) r H9 H10).
reflexivity.
reflexivity.
apply (DifferentiableR_RRn_OpenSet_N_1 (RnK 2) A g B H2).
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A g B H2 1 (S n)).
apply (le_n_S O n (le_0_n n)).
apply H4.
apply (DifferentiableR_RRn_OpenSet_N_1 (RnK 2) A f B H2).
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A f B H2 1 (S n)).
apply (le_n_S O n (le_0_n n)).
apply H3.
apply (DifferentiableR_RRn_OpenSet_N_1 (RnK 2) A (fun (r : R) => Cmult (f r) (g r)) B H2).
apply H5.
apply (DifferentiableR_RRn_OpenSet_N_1 (RnK 2) A (fun (r : R) => Cmult (f r) (g r)) B H2).
move=> r H5.
apply Proposition_1_3_3_mult_C_differentiable.
suff: (DifferentiableR_Rn_OpenSet 2 A f B H2).
move=> H6.
apply (H6 r H5).
apply (DifferentiableR_RRn_OpenSet_N_1 (RnK 2) A f B H2).
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A f B H2 1 (S n)).
apply (le_n_S O n (le_0_n n)).
apply H3.
suff: (DifferentiableR_Rn_OpenSet 2 A g B H2).
move=> H6.
apply (H6 r H5).
apply (DifferentiableR_RRn_OpenSet_N_1 (RnK 2) A g B H2).
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A g B H2 1 (S n)).
apply (le_n_S O n (le_0_n n)).
apply H4.
Qed.

Lemma Proposition_1_5_C : forall (A : Ensemble R) (f g : R -> C) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat), DifferentiableR_Rn_OpenSet_N 2 A f B H1 n -> DifferentiableR_Rn_OpenSet_N 2 A g B H1 n -> forall (H2 : DifferentiableR_Rn_OpenSet_N 2 A (fun (r : R) => Cmult (f r) (g r)) B H1 n) (H3 : forall (m : Count (S n)), DifferentiableR_Rn_OpenSet_N 2 A f B H1 (proj1_sig m)) (H4 : forall (m : Count (S n)), DifferentiableR_Rn_OpenSet_N 2 A g B H1 (n - proj1_sig m)%nat), DifferentialR_Rn_OpenSet_N 2 A (fun (r : R) => Cmult (f r) (g r)) B H1 n H2 = (fun (r : R) => MySumF2 (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n))) CPCM (fun (u : Count (S n)) => Cmult (IRC (INR (conv n (proj1_sig u)))) (Cmult (DifferentialR_Rn_OpenSet_N 2 A f B H1 (proj1_sig u) (H3 u) r) (DifferentialR_Rn_OpenSet_N 2 A g B H1 (n - proj1_sig u) (H4 u) r)))).
Proof.
suff: (forall (n : nat) (A : Ensemble R) (f g : R -> C) (B : Ensemble R) (H1 : OpenSetMet R_met B), DifferentiableR_Rn_OpenSet_N 2 A f B H1 n -> DifferentiableR_Rn_OpenSet_N 2 A g B H1 n -> forall (H2 : DifferentiableR_Rn_OpenSet_N 2 A (fun (r : R) => Cmult (f r) (g r)) B H1 n) (H3 : forall (m : Count (S n)), DifferentiableR_Rn_OpenSet_N 2 A f B H1 (proj1_sig m)) (H4 : forall (m : Count (S n)), DifferentiableR_Rn_OpenSet_N 2 A g B H1 (n - proj1_sig m)%nat), DifferentialR_Rn_OpenSet_N 2 A (fun (r : R) => Cmult (f r) (g r)) B H1 n H2 = (fun (r : R) => MySumF2 (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n))) CPCM (fun (u : Count (S n)) => Cmult (IRC (INR (conv n (proj1_sig u)))) (Cmult (DifferentialR_Rn_OpenSet_N 2 A f B H1 (proj1_sig u) (H3 u) r) (DifferentialR_Rn_OpenSet_N 2 A g B H1 (n - proj1_sig u) (H4 u) r))))).
move=> H1 A f g B H2 n.
apply (H1 n A f g B H2).
elim.
move=> A f g B H1 H2 H3 H4 H5 H6.
apply functional_extensionality.
move=> r.
rewrite (MySumF2Included (Count 1) (FiniteSingleton (Count 1) (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1)))).
rewrite MySumF2Singleton.
rewrite MySumF2O.
rewrite CM_O_r.
rewrite Cmult_1_l.
reflexivity.
move=> u.
elim.
move=> u0.
elim.
suff: (u0 = (exist (fun (n : nat) => (n < 1)%nat) 0%nat (le_n 1))).
move=> H7.
rewrite H7.
apply In_singleton.
apply sig_map.
simpl.
elim (le_lt_or_eq (proj1_sig u0) O (le_S_n (proj1_sig u0) O (proj2_sig u0))).
move=> H7.
elim (le_not_lt O (proj1_sig u0) (le_0_n (proj1_sig u0)) H7).
move=> H7.
apply H7.
move=> u H7.
apply Full_intro.
move=> n H1 A f g B H2 H3 H4 H5 H6 H7.
suff: (DifferentiableR_Rn_OpenSet 2 A (fun (r : R) => Cmult (f r) (g r)) B H2).
move=> H8.
suff: (DifferentiableR_RRn_OpenSet_N (RnK 2) A
                (DifferentialR_RRn_OpenSet (RnK 2) A (fun (r : R) => Cmult (f r) (g r)) B
                   H2 H8) B H2 n).
move=> H9.
suff: (DifferentialR_Rn_OpenSet_N 2 = DifferentialR_RRn_OpenSet_N (RnK 2)).
move=> H10.
suff: (DifferentiableR_Rn_OpenSet 2 A f B H2).
move=> H11.
suff: (DifferentiableR_Rn_OpenSet 2 A g B H2).
move=> H12.
rewrite H10.
rewrite (DifferentialR_RRn_OpenSet_N_Nature2 (RnK 2) A (fun (r : R) => Cmult (f r) (g r)) B H2 n H8 H5 H9).
move: H9.
rewrite (DifferentialR_RRn_OpenSet_Nature2 (RnK 2) A (fun (r : R) => Cmult (f r) (g r)) B H2 H8 (fun (r : R) => Cplus (Cmult (DifferentialR_Rn_OpenSet 2 A f B H2 H11 r) (g r)) (Cmult (f r) (DifferentialR_Rn_OpenSet 2 A g B H2 H12 r)))).
move=> H9.
rewrite (DifferentiableR_RRn_OpenSet_N_plus (RnK 2)).
apply Proposition_1_5_C_differentiable.
apply (proj1 (DifferentiableR_Rn_OpenSet_N_Nature2 2 A f B H2 n H11) H3).
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A g B H2 n (S n) (le_S n n (le_n n)) H4).
apply Proposition_1_5_C_differentiable.
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A f B H2 n (S n) (le_S n n (le_n n)) H3).
apply (proj1 (DifferentiableR_Rn_OpenSet_N_Nature2 2 A g B H2 n H12) H4).
move=> H13 H14.
apply functional_extensionality.
move=> r.
rewrite - H10.
rewrite (H1 A (fun (r : R) => DifferentialR_Rn_OpenSet 2 A f B H2 H11 r) g B H2).
move=> m.
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A (fun (r : R) => DifferentialR_Rn_OpenSet 2 A f B H2 H11 r) B H2 (proj1_sig m) n (le_S_n (proj1_sig m) n (proj2_sig m))).
apply (proj1 (DifferentiableR_Rn_OpenSet_N_Nature2 2 A f B H2 n H11) H3).
move=> m.
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A g B H2 (n - proj1_sig m) (S n)).
apply (le_S (n - proj1_sig m) n).
apply (plus_le_reg_l (n - proj1_sig m) n (proj1_sig m)).
rewrite (le_plus_minus_r (proj1_sig m) n (le_S_n (proj1_sig m) n (proj2_sig m))).
apply (le_plus_r (proj1_sig m) n).
apply H4.
move=> H15 H16.
rewrite (H1 A f (fun (r : R) => DifferentialR_Rn_OpenSet 2 A g B H2 H12 r) B H2).
move=> m.
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A f B H2 (proj1_sig m) (S n) (le_S (proj1_sig m) n (le_S_n (proj1_sig m) n (proj2_sig m)))).
apply H3.
move=> m.
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A (fun (r : R) => DifferentialR_Rn_OpenSet 2 A g B H2 H12 r) B H2 (n - proj1_sig m) n).
apply (plus_le_reg_l (n - proj1_sig m) n (proj1_sig m)).
rewrite (le_plus_minus_r (proj1_sig m) n (le_S_n (proj1_sig m) n (proj2_sig m))).
apply (le_plus_r (proj1_sig m) n).
apply (proj1 (DifferentiableR_Rn_OpenSet_N_Nature2 2 A g B H2 n H12) H4).
move=> H17 H18.
elim (MySumF2Sn2_exists (S n)).
move=> H19.
elim.
move=> H20 H21.
suff: (forall (m : Count (S (S n))), proj1_sig m <> O -> pred (proj1_sig m) < S n)%nat.
move=> H22.
rewrite - (Cplus_0_l (MySumF2 (Count (S n))
     (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n)))
     CPCM
     (fun (u : Count (S n)) =>
      Cmult (IRC (INR (conv n (proj1_sig u))))
        (Cmult
           (DifferentialR_Rn_OpenSet_N 2 A
              (fun (r0 : R) => DifferentialR_Rn_OpenSet 2 A f B H2 H11 r0) B H2
              (proj1_sig u) (H15 u) r)
           (DifferentialR_Rn_OpenSet_N 2 A g B H2 (n - proj1_sig u) (H16 u) r))))).
rewrite (Cplus_comm CO).
suff: (MySumF2 (Count (S (S n)))
(exist (Finite (Count (S (S n)))) (Full_set (Count (S (S n))))
              (CountFinite (S (S n))))
CPCM (fun (m : (Count (S (S n)))) => match excluded_middle_informative (proj1_sig m = O) with
  | left _ => CO
  | right H => Cmult (IRC (INR (conv n (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))))))
      (Cmult (DifferentialR_Rn_OpenSet_N 2 A
         (fun (r : R) => DifferentialR_Rn_OpenSet 2 A f B H2 H11 r) B H2
         (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) (H15 (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) r)
       (DifferentialR_Rn_OpenSet_N 2 A g B H2 (n - proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) (H16 (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) r))
end)
=
Cplus (MySumF2 (Count (S n))
     (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n)))
     CPCM
     (fun (u : Count (S n)) =>
      Cmult (IRC (INR (conv n (proj1_sig u))))
      (Cmult (DifferentialR_Rn_OpenSet_N 2 A
         (fun (r0 : R) => DifferentialR_Rn_OpenSet 2 A f B H2 H11 r0) B H2
         (proj1_sig u) (H15 u) r)
       (DifferentialR_Rn_OpenSet_N 2 A g B H2 (n - proj1_sig u) (H16 u) r)))) CO).
move=> H23.
rewrite - H23.
rewrite - (Cplus_0_l (MySumF2 (Count (S n))
     (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n)))
     CPCM
     (fun (u : Count (S n)) =>
      Cmult (IRC (INR (conv n (proj1_sig u))))
      (Cmult (DifferentialR_Rn_OpenSet_N 2 A f B H2 (proj1_sig u) (H17 u) r)
       (DifferentialR_Rn_OpenSet_N 2 A
         (fun (r : R) => DifferentialR_Rn_OpenSet 2 A g B H2 H12 r) B H2
         (n - proj1_sig u) (H18 u) r))))).
rewrite (Cplus_comm CO).
suff: (MySumF2 (Count (S (S n)))
(exist (Finite (Count (S (S n)))) (Full_set (Count (S (S n))))
              (CountFinite (S (S n))))
CPCM (fun (m : (Count (S (S n)))) => match excluded_middle_informative (proj1_sig m < S n)%nat with
  | left H => Cmult (IRC (INR (conv n (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)))))
(Cmult (DifferentialR_Rn_OpenSet_N 2 A f B H2 (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) (H17 (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) r)
       (DifferentialR_Rn_OpenSet_N 2 A
         (fun (r : R) => DifferentialR_Rn_OpenSet 2 A g B H2 H12 r) B H2
         (n - proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) (H18 (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) r))
  | right _ => CO
end)
= Cplus (MySumF2 (Count (S n))
        (exist (Finite (Count (S n))) (Full_set (Count (S n)))
           (CountFinite (S n))) CPCM
        (fun (u : Count (S n)) =>
      Cmult (IRC (INR (conv n (proj1_sig u))))
      (Cmult (DifferentialR_Rn_OpenSet_N 2 A f B H2 (proj1_sig u) (H17 u) r)
       (DifferentialR_Rn_OpenSet_N 2 A
         (fun (r : R) => DifferentialR_Rn_OpenSet 2 A g B H2 H12 r) B H2
         (n - proj1_sig u) (H18 u) r)))) CO).
move=> H24.
rewrite - H24.
suff: (RRnplus (RnK 2) = CMc CPCM).
move=> H25.
rewrite H25.
rewrite - (MySumF2Distr (Count (S (S n))) CPCM (exist (Finite (Count (S (S n)))) (Full_set (Count (S (S n))))
     (CountFinite (S (S n)))) (fun (m : (Count (S (S n)))) => match excluded_middle_informative (proj1_sig m = O) with
  | left _ => CO
  | right H => Cmult (IRC (INR (conv n (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))))))
      (Cmult (DifferentialR_Rn_OpenSet_N 2 A
         (fun (r : R) => DifferentialR_Rn_OpenSet 2 A f B H2 H11 r) B H2
         (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) (H15 (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) r)
       (DifferentialR_Rn_OpenSet_N 2 A g B H2 (n - proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) (H16 (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H22 m H))) r))
end)
(fun (m : (Count (S (S n)))) => match excluded_middle_informative (proj1_sig m < S n)%nat with
  | left H => Cmult (IRC (INR (conv n (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)))))
(Cmult (DifferentialR_Rn_OpenSet_N 2 A f B H2 (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) (H17 (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) r)
       (DifferentialR_Rn_OpenSet_N 2 A
         (fun (r : R) => DifferentialR_Rn_OpenSet 2 A g B H2 H12 r) B H2
         (n - proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) (H18 (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) r))
  | right _ => CO
end)
(fun (u : Count (S (S n))) =>
   Cmult (IRC (INR (conv (S n) (proj1_sig u))))
   (Cmult (DifferentialR_Rn_OpenSet_N 2 A f B H2 (proj1_sig u) (H6 u) r)
    (DifferentialR_Rn_OpenSet_N 2 A g B H2 (S n - proj1_sig u) (H7 u) r)))).
reflexivity.
move=> u H26.
elim (excluded_middle_informative (proj1_sig u < S n)%nat).
move=> H27.
elim (excluded_middle_informative (proj1_sig u = O)).
move=> H28.
simpl.
rewrite {1} H28.
rewrite {3} H28.
suff: (conv n 0 = 1%nat).
move=> H29.
rewrite H29.
simpl.
rewrite Cplus_0_l.
suff: (H6 u = H17 (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig u) H27)).
move=> H30.
rewrite H30.
rewrite - (DifferentialR_Rn_OpenSet_N_Nature2 2 A g B H2 (n - proj1_sig u) H12).
rewrite minus_Sn_m.
apply (H7 u).
apply (le_S_n (proj1_sig u) n H27).
rewrite minus_Sn_m.
move=> H31.
suff: (H31 = H7 u).
move=> H32.
rewrite H32.
reflexivity.
apply proof_irrelevance.
apply (le_S_n (proj1_sig u) n H27).
apply proof_irrelevance.
elim n.
reflexivity.
move=> k H29.
reflexivity.
move=> H28.
simpl.
rewrite - (DifferentialR_Rn_OpenSet_N_Nature2 2 A f B H2 (pred (proj1_sig u)) H11).
suff: (proj1_sig u <> O).
suff: (proj1_sig u < S n)%nat.
elim (proj1_sig u).
move=> H29.
elim.
reflexivity.
move=> m H29 H30 H31.
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A f B H2 (S m) (S n)).
apply (lt_le_weak (S m) (S n) H30).
apply H3.
apply H27.
apply H28.
suff: (S (pred (proj1_sig u)) = proj1_sig u).
move=> H29.
rewrite H29.
move=> H30.
rewrite - DifferentialR_Rn_OpenSet_N_Nature2.
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A g B H2 (S (n - proj1_sig u)) (S n)).
apply le_n_S.
apply (plus_le_reg_l (n - proj1_sig u) n (proj1_sig u)).
rewrite (le_plus_minus_r (proj1_sig u) n).
apply le_plus_r.
apply (le_S_n (proj1_sig u) n H27).
apply H4.
suff: (S (n - proj1_sig u) = n - pred (proj1_sig u))%nat.
move=> H31.
rewrite H31.
move=> H32.
suff: (H30 = H17 (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig u) H27)).
move=> H33.
rewrite H33.
suff: (H16
      (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig u))
         (H22 u H28)) = H32).
move=> H34.
rewrite H34.
rewrite - (Fmul_add_distr_r Cfield : forall (x y z : C), Cmult (Cplus x y) z = Cplus (Cmult x z) (Cmult y z)).
suff: (IRC (INR match proj1_sig u with
    | O => 1
    | S k => conv n k + conv n (S k)
    end) = Cplus (IRC (INR (conv n (pred (proj1_sig u))))) (IRC (INR (conv n (proj1_sig u))))).
move=> H35.
rewrite H35.
apply (Fmul_eq_compat_l Cfield : forall (x y z : C), y = z -> Cmult x y = Cmult x z).
simpl.
suff: (H6 u = H17 (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig u) H27)).
move=> H36.
rewrite H36.
apply (Fmul_eq_compat_l Cfield : forall (x y z : C), y = z -> Cmult x y = Cmult x z).
suff: (forall (n m : nat), n = m -> forall (H37 : DifferentiableR_Rn_OpenSet_N 2 A g B H2 n) (H38 : DifferentiableR_Rn_OpenSet_N 2 A g B H2 m), DifferentialR_Rn_OpenSet_N 2 A g B H2 n H37 r = DifferentialR_Rn_OpenSet_N 2 A g B H2 m H38 r).
move=> H37.
apply H37.
suff: (proj1_sig u <> O).
elim (proj1_sig u).
elim.
reflexivity.
move=> m H38 H39.
reflexivity.
apply H28.
move=> m k H37.
rewrite H37.
move=> H38 H39.
suff: (H38 = H39).
move=> H40.
rewrite H40.
reflexivity.
apply proof_irrelevance.
apply proof_irrelevance.
suff: (proj1_sig u <> O).
elim (proj1_sig u).
elim.
reflexivity.
move=> m H35 H36.
rewrite plus_INR.
rewrite IRCplus.
reflexivity.
apply H28.
apply proof_irrelevance.
apply proof_irrelevance.
suff: (proj1_sig u < S n)%nat.
suff: (proj1_sig u <> O).
elim (proj1_sig u).
elim.
reflexivity.
move=> m H31 H32 H33.
apply minus_Sn_m.
apply (le_S_n (S m) n H33).
apply H28.
apply H27.
suff: (proj1_sig u <> O).
elim (proj1_sig u).
elim.
reflexivity.
move=> m H29 H30.
reflexivity.
apply H28.
move=> H27.
elim (excluded_middle_informative (proj1_sig u = O)).
move=> H28.
elim H27.
rewrite H28.
apply (le_n_S O n (le_0_n n)).
move=> H28.
simpl.
rewrite (Fadd_O_r Cfield : forall (x : C), Cplus x CO = x).
suff: (S (pred (proj1_sig u)) = proj1_sig u).
move=> H29.
rewrite - DifferentialR_Rn_OpenSet_N_Nature2.
rewrite H29.
apply (H6 u).
rewrite H29.
move=> H30.
suff: (H6 u = H30).
move=> H31.
rewrite H31.
suff: (INR match proj1_sig u with
    | O => 1
    | S k => conv n k + conv n (S k)
    end = INR (conv n (pred (proj1_sig u)))).
move=> H32.
rewrite H32.
suff: (DifferentialR_Rn_OpenSet_N 2 A g B H2
   match proj1_sig u with
   | O => S n
   | S l => n - l
   end (H7 u) r = DifferentialR_Rn_OpenSet_N 2 A g B H2 (n - pred (proj1_sig u))
   (H16
      (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig u))
         (H22 u H28))) r).
move=> H33.
rewrite H33.
reflexivity.
suff: (forall (n m : nat), n = m -> forall (H33 : DifferentiableR_Rn_OpenSet_N 2 A g B H2 n) (H34 : DifferentiableR_Rn_OpenSet_N 2 A g B H2 m), DifferentialR_Rn_OpenSet_N 2 A g B H2 n H33 r = DifferentialR_Rn_OpenSet_N 2 A g B H2 m H34 r).
move=> H33.
apply H33.
suff: (proj1_sig u <> O).
elim (proj1_sig u).
elim.
reflexivity.
move=> m H34 H35.
reflexivity.
apply H28.
move=> m k H33.
rewrite H33.
move=> H34 H35.
suff: (H34 = H35).
move=> H36.
rewrite H36.
reflexivity.
apply proof_irrelevance.
suff: (proj1_sig u = S n).
move=> H32.
rewrite H32.
rewrite (proj2 (conv_fact n) (S n) (le_n (S n))).
rewrite plus_comm.
reflexivity.
elim (le_lt_or_eq (proj1_sig u) (S n)).
move=> H32.
elim (H27 H32).
move=> H32.
apply H32.
apply (le_S_n (proj1_sig u) (S n) (proj2_sig u)).
apply proof_irrelevance.
suff: (proj1_sig u <> O).
elim (proj1_sig u).
elim.
reflexivity.
move=> m H29 H30.
reflexivity.
apply H28.
reflexivity.
rewrite (H21 CPCM).
simpl.
elim (excluded_middle_informative (S n < S n)%nat).
move=> H24.
elim (lt_irrefl (S n) H24).
move=> H24.
apply (Fadd_eq_compat_r Cfield : forall (x y z : C), y = z -> Cplus y x = Cplus z x).
apply f_equal.
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (proj1_sig m < S n)%nat).
move=> H25.
suff: (H17 (exist (fun k : nat => (k < S n)%nat) (proj1_sig m) H25) = H17 m).
move=> H26.
suff: (H18 (exist (fun k : nat => (k < S n)%nat) (proj1_sig m) H25) = H18 m).
move=> H27.
rewrite H26.
rewrite H27.
reflexivity.
apply proof_irrelevance.
apply proof_irrelevance.
move=> H25.
elim (H25 (proj2_sig m)).
rewrite (MySumF2Included (Count (S (S n))) (FiniteIm (Count (S (S n))) (Count (S (S n)))
(fun (m : Count (S (S n))) => match excluded_middle_informative (proj1_sig m < S n)%nat with
  | left H => exist (fun (k : nat) => (k < S (S n))%nat) (S (proj1_sig m)) (le_n_S (S (proj1_sig m)) (S n) H)
  | right _ => exist (fun (k : nat) => (k < S (S n))%nat) O (le_n_S O (S n) (le_0_n (S n)))
end)
(exist (Finite (Count (S (S n)))) (Full_set (Count (S (S n))))
     (CountFinite (S (S n)))))
  (exist (Finite (Count (S (S n)))) (Full_set (Count (S (S n))))
     (CountFinite (S (S n)))) CPCM).
rewrite - MySumF2BijectiveSame2.
rewrite (H21 CPCM).
rewrite (MySumF2O (Count (S (S n)))).
rewrite CM_O_r.
unfold compose.
simpl.
elim (excluded_middle_informative (S n < S n)%nat).
move=> H23.
elim (lt_irrefl (S n) H23).
move=> H23.
simpl.
elim (excluded_middle_informative (O = O)).
move=> H24.
apply (Fadd_eq_compat_r Cfield : forall (x y z : C), y = z -> Cplus y x = Cplus z x).
apply f_equal.
apply functional_extensionality.
move=> m.
elim (excluded_middle_informative (proj1_sig m < S n)%nat).
move=> H25.
simpl.
elim (excluded_middle_informative (S (proj1_sig m) = O)).
move=> H26.
elim (lt_irrefl (S (proj1_sig m))).
rewrite {1} H26.
apply (le_n_S O (proj1_sig m) (le_0_n (proj1_sig m))).
move=> H26.
suff: (H15 (exist (fun k : nat => (k < S n)%nat) (proj1_sig m)
         (H22
            (exist (fun (k : nat) => (k < S (S n))%nat) 
               (S (proj1_sig m)) (le_n_S (S (proj1_sig m)) (S n) H25)) H26)) = H15 m).
move=> H27.
rewrite H27.
suff: (H16 (exist (fun k : nat => (k < S n)%nat) (proj1_sig m)
         (H22
            (exist (fun (k : nat) => (k < S (S n))%nat) 
               (S (proj1_sig m)) (le_n_S (S (proj1_sig m)) (S n) H25)) H26)) = H16 m).
move=> H28.
rewrite H28.
reflexivity.
apply proof_irrelevance.
apply proof_irrelevance.
move=> H25.
elim (H25 (proj2_sig m)).
elim.
reflexivity.
move=> u.
elim.
move=> u0 H23 H24.
elim H23.
elim u0.
elim.
move=> H25.
apply (Im_intro (Count (S (S n))) (Count (S (S n))) (Full_set (Count (S (S n)))) (fun (m : Count (S (S n))) =>
         match excluded_middle_informative (proj1_sig m < S n)%nat with
         | left H =>
             exist (fun (k : nat) => (k < S (S n))%nat) 
               (S (proj1_sig m)) (le_n_S (S (proj1_sig m)) (S n) H)
         | right _ =>
             exist (fun (k : nat) => (k < S (S n))%nat) 0%nat
               (le_n_S 0 (S n) (le_0_n (S n)))
         end) (exist (fun (k : nat) => (k < S (S n))%nat) (S n) (le_n (S (S n))))).
apply (Full_intro (Count (S (S n)))).
simpl.
elim (excluded_middle_informative (S n < S n)%nat).
move=> H26.
elim (lt_irrefl (S n) H26).
move=> H26.
apply sig_map.
reflexivity.
move=> m H25 H26.
apply (Im_intro (Count (S (S n))) (Count (S (S n))) (Full_set (Count (S (S n)))) (fun (m : Count (S (S n))) =>
         match excluded_middle_informative (proj1_sig m < S n)%nat with
         | left H =>
             exist (fun (k : nat) => (k < S (S n))%nat) 
               (S (proj1_sig m)) (le_n_S (S (proj1_sig m)) (S n) H)
         | right _ =>
             exist (fun (k : nat) => (k < S (S n))%nat) 0%nat
               (le_n_S 0 (S n) (le_0_n (S n)))
         end) (exist (fun (k : nat) => (k < S (S n))%nat) m (le_trans (S m) (S (S m)) (S (S n)) (le_S (S m) (S m) (le_n (S m))) H26))).
apply (Full_intro (Count (S (S n)))).
simpl.
elim (excluded_middle_informative (m < S n)%nat).
move=> H27.
apply sig_map.
reflexivity.
move=> H27.
elim (H27 (le_S_n (S m) (S n) H26)).
move=> u1 u2 H23 H24 .
elim (excluded_middle_informative (proj1_sig u1 < S n)%nat).
move=> H25.
elim (excluded_middle_informative (proj1_sig u2 < S n)%nat).
move=> H26 H27.
apply sig_map.
suff: (proj1_sig u1 = pred (proj1_sig (exist (fun (k : nat) => (k < S (S n))%nat) (S (proj1_sig u1))
        (le_n_S (S (proj1_sig u1)) (S n) H25)))).
move=> H28.
rewrite H28.
rewrite H27.
reflexivity.
reflexivity.
move=> H26 H27.
elim (lt_irrefl (proj1_sig (exist (fun (k : nat) => (k < S (S n))%nat) (S (proj1_sig u1))
  (le_n_S (S (proj1_sig u1)) (S n) H25)))).
rewrite {1} H27.
apply (le_n_S O (proj1_sig u1) (le_0_n (proj1_sig u1))).
move=> H25.
elim (excluded_middle_informative (proj1_sig u2 < S n)%nat).
move=> H26 H27.
elim (lt_irrefl (proj1_sig (exist (fun (k : nat) => (k < S (S n))%nat) O
  (le_n_S 0 (S n) (le_0_n (S n)))))).
rewrite {2} H27.
apply (le_n_S O (proj1_sig u2) (le_0_n (proj1_sig u2))).
move=> H26 H27.
apply sig_map.
elim (le_lt_or_eq (proj1_sig u1) (S n)).
move=> H28.
elim (H25 H28).
elim (le_lt_or_eq (proj1_sig u2) (S n)).
move=> H29.
elim (H26 H29).
move=> H28 H29.
rewrite H28.
apply H29.
apply (le_S_n (proj1_sig u2) (S n) (proj2_sig u2)).
apply (le_S_n (proj1_sig u1) (S n) (proj2_sig u1)).
move=> u H23.
apply (Full_intro (Count (S (S n))) u).
move=> m.
suff: (proj1_sig m < S (S n))%nat.
elim (proj1_sig m).
move=> H22.
elim.
reflexivity.
move=> k H22 H23 H24.
apply (le_S_n (S k) (S n) H23).
apply (proj2_sig m).
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A f B H2 n (S n) (le_S n n (le_n n)) H3).
apply (proj1 (DifferentiableR_RRn_OpenSet_N_Nature2 (RnK 2) A g B H2 n H12) H4).
apply (proj1 (DifferentiableR_RRn_OpenSet_N_Nature2 (RnK 2) A f B H2 n H11) H3).
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A g B H2 n (S n) (le_S n n (le_n n)) H4).
apply conj.
move=> r H13.
rewrite (proj1 (DifferentialR_Rn_OpenSet_Nature 2 A f B H2 H11) r H13).
rewrite (proj1 (DifferentialR_Rn_OpenSet_Nature 2 A g B H2 H12) r H13).
rewrite (Fmul_O_l Cfield (g r) : Cmult CO (g r) = CO).
rewrite (Fmul_O_r Cfield (f r) : Cmult (f r) CO = CO).
apply (Cplus_0_l CO).
move=> r H13 H14.
rewrite (proj2 (DifferentialR_Rn_OpenSet_Nature 2 A f B H2 H11) r H13 H14).
rewrite (proj2 (DifferentialR_Rn_OpenSet_Nature 2 A g B H2 H12) r H13 H14).
rewrite - (Proposition_1_3_3_mult_C (Intersection R A B) f g r (OpenSetNotIsolatedR_Intersection A B H2 r H14 H13) 
  (H11 r H14) (H12 r H14) (H8 r H14)).
reflexivity.
apply (DifferentiableR_RRn_OpenSet_N_1 (RnK 2) A g B H2).
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A g B H2 1 (S n) (le_n_S O n (le_0_n n)) H4).
apply (DifferentiableR_RRn_OpenSet_N_1 (RnK 2) A f B H2).
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A f B H2 1 (S n) (le_n_S O n (le_0_n n)) H3).
reflexivity.
apply (proj1 (DifferentiableR_RRn_OpenSet_N_Nature2 (RnK 2) A (fun (r : R) => Cmult (f r) (g r)) B H2 n H8) H5).
apply (DifferentiableR_RRn_OpenSet_N_1 (RnK 2) A (fun (r : R) => Cmult (f r) (g r)) B H2).
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A (fun (r : R) => Cmult (f r) (g r)) B H2 1 (S n) (le_n_S O n (le_0_n n)) H5).
Qed.

Lemma Proposition_1_5_C_exists : forall (A : Ensemble R) (f g : R -> C) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat), DifferentiableR_Rn_OpenSet_N 2 A f B H1 n -> DifferentiableR_Rn_OpenSet_N 2 A g B H1 n -> exists (H2 : DifferentiableR_Rn_OpenSet_N 2 A (fun (r : R) => Cmult (f r) (g r)) B H1 n) (H3 : forall (m : Count (S n)), DifferentiableR_Rn_OpenSet_N 2 A f B H1 (proj1_sig m)) (H4 : forall (m : Count (S n)), DifferentiableR_Rn_OpenSet_N 2 A g B H1 (n - proj1_sig m)%nat), DifferentialR_Rn_OpenSet_N 2 A (fun (r : R) => Cmult (f r) (g r)) B H1 n H2 = (fun (r : R) => MySumF2 (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n))) CPCM (fun (u : Count (S n)) => Cmult (IRC (INR (conv n (proj1_sig u)))) (Cmult (DifferentialR_Rn_OpenSet_N 2 A f B H1 (proj1_sig u) (H3 u) r) (DifferentialR_Rn_OpenSet_N 2 A g B H1 (n - proj1_sig u) (H4 u) r)))).
Proof.
move=> A f g B H1 n H2 H3.
suff: (DifferentiableR_Rn_OpenSet_N 2 A (fun (r : R) => Cmult (f r) (g r)) B H1 n).
move=> H4.
suff: (forall (m : Count (S n)),
      DifferentiableR_Rn_OpenSet_N 2 A f B H1 (proj1_sig m)).
move=> H5.
suff: (forall (m : Count (S n)),
      DifferentiableR_Rn_OpenSet_N 2 A g B H1 (n - proj1_sig m)).
move=> H6.
exists H4.
exists H5.
exists H6.
apply (Proposition_1_5_C A f g B H1 n H2 H3 H4 H5 H6).
move=> m.
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A g B H1 (n - proj1_sig m) n).
apply (plus_le_reg_l (n - proj1_sig m) n (proj1_sig m)).
rewrite (le_plus_minus_r (proj1_sig m) n).
apply (le_plus_r (proj1_sig m) n).
apply (le_S_n (proj1_sig m) n (proj2_sig m)).
apply H3.
move=> m.
apply (DifferentiableR_RRn_OpenSet_N_le (RnK 2) A f B H1 (proj1_sig m) n).
apply (le_S_n (proj1_sig m) n (proj2_sig m)).
apply H2.
apply Proposition_1_5_C_differentiable.
apply H2.
apply H3.
Qed.

Definition DifferentiableR_RRn_OpenSet_N_continuously (K : RRn) (A : Ensemble R) (f : R -> RRnT K) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) := DifferentiableR_RRn_OpenSet_N K A f B H1 n /\ forall (H : DifferentiableR_RRn_OpenSet_N K A f B H1 n) (r : R), In R A r -> ContinuousMet R_met (RRn_met K) (DifferentialR_RRn_OpenSet_N K A f B H1 n H) (Intersection R A B) r.

Definition DifferentiableR_Rn_OpenSet_N_continuously (N : nat) (A : Ensemble R) (f : R -> Rn N) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) := DifferentiableR_Rn_OpenSet_N N A f B H1 n /\ forall (H : DifferentiableR_Rn_OpenSet_N N A f B H1 n) (r : R), In R A r -> ContinuousMet R_met (Rn_met N) (DifferentialR_Rn_OpenSet_N N A f B H1 n H) (Intersection R A B) r.

Definition DifferentiableR_R_OpenSet_N_continuously (A : Ensemble R) (f : R -> R) (B : Ensemble R) (H1 : OpenSetMet R_met B) (n : nat) := DifferentiableR_R_OpenSet_N A f B H1 n /\ forall (H : DifferentiableR_R_OpenSet_N A f B H1 n) (r : R), In R A r -> ContinuousMet R_met R_met (DifferentialR_R_OpenSet_N A f B H1 n H) (Intersection R A B) r.
