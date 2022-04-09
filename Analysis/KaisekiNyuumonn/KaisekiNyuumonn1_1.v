From mathcomp Require Import ssreflect.
Require Import Reals.
Require Import Coq.Sets.Ensembles.
Require Export QArith_base.
Local Open Scope R_scope.
Require Export Rdefinitions.
Require Import Classical.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Image.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Arith.Even.
Require Import Coq.Arith.Div2.

Lemma sig_map : forall {T : Type} (P : T -> Prop) (x : {x : T | P x}) (y : {x : T | P x}), proj1_sig x = proj1_sig y -> x = y.
Proof.
move=> A P x y.
case x.
move=> xv xp.
case y.
move=> yv yp .
simpl.
move=> H1.
subst xv.
rewrite (proof_irrelevance (P yv) yp xp).
by [].
Qed.

Lemma Problem_1_1_1_1 : forall r1 : R, ((forall r2 : R, (r1 + r2) = r2) -> r1 = 0).
Proof.
move=> r1 H.
rewrite - (H 0).
rewrite - {1}(Rplus_0_l r1).
apply (Rplus_comm 0 r1).
Qed.

Lemma Problem_1_1_1_1_improved : forall r1 : R, ((exists r2 : R, (r1 + r2) = r2) -> r1 = 0).
Proof.
move=> r1 H1.
case H1.
move=> r2.
move=> H2.
rewrite - (Rplus_0_l r1).
rewrite (Rplus_comm 0 r1).
rewrite - (Rplus_opp_r r2).
rewrite - (Rplus_assoc r1 r2 (- r2)).
rewrite H2.
by [].
Qed.

Lemma Problem_1_1_1_2 : forall r1 : R, (forall r2 : R, (r1 + r2 = 0 -> r2 = - r1)).
Proof.
move=> r1 r2.
move=> H.
rewrite - (Rplus_0_l r2).
rewrite - (Rplus_opp_r r1).
rewrite (Rplus_comm r1 (- r1)).
rewrite (Rplus_assoc (- r1) r1 r2).
rewrite H.
rewrite (Rplus_comm (- r1) 0).
apply (Rplus_0_l (- r1)).
Qed.

Lemma Problem_1_1_1_3 : forall r : R, - (- r) = r.
Proof.
move=> r.
symmetry.
apply (Problem_1_1_1_2 (- r) r).
rewrite (Rplus_comm (- r) r).
apply (Rplus_opp_r r).
Qed.

Lemma Problem_1_1_1_4 : forall r : R, 0 * r = 0.
Proof.
move=> r.
apply (Problem_1_1_1_1_improved (0 * r)).
exists (0 * r).
rewrite (Rmult_comm 0 r).
rewrite - (Rmult_plus_distr_l r 0 0).
rewrite (Rplus_0_l 0).
by [].
Qed.

Lemma Problem_1_1_1_5 : forall r : R, (- 1) * r = - r.
Proof.
move=> r.
apply (Problem_1_1_1_2 r ((- 1) * r)).
rewrite - {1}(Rmult_1_l r).
rewrite (Rmult_comm 1 r).
rewrite (Rmult_comm (- 1) r).
rewrite - (Rmult_plus_distr_l r 1 (- 1)).
rewrite (Rplus_opp_r 1).
rewrite (Rmult_comm r 0).
apply (Problem_1_1_1_4 r).
Qed.

Lemma Problem_1_1_1_6 : (- 1) * (- 1) = 1.
Proof.
rewrite (Problem_1_1_1_5 (- 1)).
apply (Problem_1_1_1_3 1).
Qed.

Lemma Problem_1_1_1_7_l : forall r1 r2 : R, r1 * (- r2) = - (r1 * r2).
Proof.
move=> r1 r2.
apply (Problem_1_1_1_2 (r1 * r2) (r1 * (- r2))).
rewrite - (Rmult_plus_distr_l r1 r2 (- r2)).
rewrite (Rplus_opp_r r2).
rewrite (Rmult_comm r1 0).
apply (Problem_1_1_1_4 r1).
Qed.

Lemma Problem_1_1_1_7_r : forall r1 r2 : R, - (r1 * r2) = (- r1) * r2.
Proof.
move=> r1 r2.
symmetry.
apply (Problem_1_1_1_2 (r1 * r2) (- r1 * r2)).
rewrite (Rmult_comm r1 r2).
rewrite (Rmult_comm (- r1) r2).
rewrite - (Rmult_plus_distr_l r2 r1 (- r1)).
rewrite (Rplus_opp_r r1).
rewrite (Rmult_comm r2 0).
apply (Problem_1_1_1_4 r2).
Qed.

Lemma Problem_1_1_1_8 : forall r1 r2 : R, (- r1) * (- r2) = r1 * r2.
Proof.
move=> r1 r2.
rewrite - (Problem_1_1_1_3 (r1 * r2)).
rewrite (Problem_1_1_1_7_l (- r1) r2).
f_equal.
symmetry.
apply (Problem_1_1_1_7_r r1 r2).
Qed.

Lemma Problem_1_1_1_9 : forall r1 r2 : R, r1 * r2 = 0 -> {r1 = 0} + {r2 = 0}.
Proof.
move=> r1 r2.
move=> H1.
elim: (total_order_T r1 0).
elim.
move=> H2.
right.
suff: r1 <> 0.
move=> H3.
rewrite - (Rmult_1_l r2).
rewrite - ((Rinv_l r1) H3).
rewrite (Rmult_assoc (/ r1) r1 r2).
rewrite H1.
rewrite (Rmult_comm (/ r1) 0).
apply (Problem_1_1_1_4 (/ r1)).
move=> H3.
apply (Rlt_asym r1 0).
apply H2.
rewrite H3.
rewrite - {1}H3.
apply H2.
move=> H3.
left.
apply H3.
move=> H2.
right.
suff: r1 <> 0.
move=> H3.
rewrite - (Rmult_1_l r2).
rewrite - ((Rinv_l r1) H3).
rewrite (Rmult_assoc (/ r1) r1 r2).
rewrite H1.
rewrite (Rmult_comm (/ r1) 0).
apply (Problem_1_1_1_4 (/ r1)).
move=> H3.
apply (Rlt_asym r1 0).
rewrite H3.
rewrite - {2}H3.
apply H2.
apply H2.
Qed.

Lemma Problem_1_1_1_sub : forall r1 r2 : R, r1 * r2 = 1 -> r2 = (/ r1).
Proof.
move=> r1 r2.
move=> H1.
suff: {r1 = 0} + {r1 <> 0}.
case.
move=> H2.
apply False_ind.
elim H1.
apply R1_neq_R0.
rewrite - H1.
rewrite H2.
apply (Problem_1_1_1_4 r2).
move=> H2.
rewrite - (Rmult_1_l r2).
rewrite - ((Rinv_l r1) H2).
rewrite (Rmult_assoc (/ r1)).
rewrite H1.
rewrite (Rmult_comm (/ r1) 1).
apply (Rmult_1_l (/ r1)).
elim: (total_order_T r1 0).
elim.
move=> H2.
right.
move=> H3.
apply (Rlt_asym r1 0).
apply H2.
rewrite H3.
rewrite - {1}H3.
apply H2.
apply left.
move=> H2.
right.
move=> H3.
apply (Rlt_asym r1 0).
rewrite H3.
rewrite - {2}H3.
apply H2.
apply H2.
Qed.

Lemma Problem_1_1_1_10 : forall r : R, (r <> 0) -> / (- r) = - (/ r).
Proof.
move=> r.
move=> H1.
symmetry.
apply (Problem_1_1_1_sub (- r) (- / r)).
rewrite (Problem_1_1_1_8 r (/ r)).
rewrite (Rmult_comm r (/ r)).
apply ((Rinv_l r) H1).
Qed.

Lemma Problem_1_1_1_11 : forall r1 r2 : R, ((r1 <> 0) /\ (r2 <> 0)) -> / (r1 * r2) = (/ r2) * (/ r1).
Proof.
move=> r1 r2.
case.
move=> H1 H2.
symmetry.
apply (Problem_1_1_1_sub (r1 * r2) ((/ r2) * (/ r1))).
rewrite (Rmult_assoc r1 r2 (/ r2 * / r1)).
rewrite - (Rmult_assoc r2 (/ r2) (/ r1)).
rewrite (Rmult_comm r2 (/ r2)).
rewrite ((Rinv_l r2) H2).
rewrite (Rmult_1_l (/ r1)).
rewrite (Rmult_comm r1 (/ r1)).
apply ((Rinv_l r1) H1).
Qed.

Lemma Formula_1_2 : forall r : R, (r > 0) \/ (r = 0) <-> ( - r < 0) \/ (r = 0).
Proof.
rewrite /iff.
move=> r.
apply conj.
elim.
left.
rewrite - (Rplus_0_r (- r)).
rewrite - {2}(Rplus_opp_l r).
apply (Rplus_lt_compat_l (- r) 0 r).
apply H.
right.
apply H.
elim.
left.
rewrite - (Rplus_0_r r).
rewrite - {2}(Rplus_opp_l (- r)).
rewrite (Problem_1_1_1_3 r).
apply ((Rplus_lt_compat_l r (- r) 0) H).
right.
apply H.
Qed.

Lemma Formula_1_3 : forall r : R, (r * r > 0) \/ (r * r = 0).
Proof.
suff: forall r : R, r > 0 -> r * r > 0.
move => H1 r.
elim (total_order_T r 0).
elim.
move=> H3.
left.
rewrite - (Problem_1_1_1_8 r r).
suff: - r > 0.
apply (H1 (- r)).
rewrite /Rgt.
rewrite - (Rplus_0_r (- r)).
rewrite - {1}(Rplus_opp_l r).
apply (Rplus_lt_compat_l (- r) r 0).
apply H3.
move=> H2.
right.
rewrite H2.
apply (Problem_1_1_1_4 0).
move=> H3.
left.
apply ((H1 r) H3).
move=> r H1.
rewrite - (Problem_1_1_1_4 r).
rewrite (Rmult_comm 0 r).
apply ((Rmult_lt_compat_l r 0 r) H1 H1).
Qed.

Lemma Formula_1_3_2 : forall r : R, r * r >= 0.
Proof.
apply Formula_1_3.
Qed.

Lemma Formula_1_3_3 : forall r : R, r <> 0 -> r * r > 0.
Proof.
move=> r H1.
elim (Formula_1_3 r).
apply.
move=> H2.
apply False_ind.
apply H1.
rewrite - (Rmult_1_l r).
rewrite - (Rinv_l r H1).
rewrite (Rmult_assoc (/ r) r r).
rewrite H2.
apply (Rmult_0_r (/ r)).
Qed.

Lemma Formula_1_4 : 1 > 0.
Proof.
elim (total_order_T 1 0).
case.
move=> H1.
apply False_ind.
apply (Rlt_asym 0 1).
rewrite - (Rmult_1_l 1).
elim (Formula_1_3 1).
apply.
move=> H2.
apply False_ind.
rewrite (Rmult_1_l 1) in H2.
apply (R1_neq_R0 H2).
apply H1.
move=> H2.
apply False_ind.
apply (R1_neq_R0 H2).
apply.
Qed.

Lemma Problem_1_1_2_1 : forall r1 r2 : R, r1 <= r2 <-> 0 <= r2 - r1.
Proof.
move=> r1 r2.
rewrite /iff.
apply conj.
move=> H1.
elim H1.
move=> H2.
left.
rewrite - (Rplus_opp_r r1).
rewrite (Rplus_comm r1 (- r1)).
rewrite /Rminus.
rewrite (Rplus_comm r2 (- r1)).
apply (Rplus_lt_compat_l (- r1) r1 r2 H2).
move=> H2.
right.
rewrite /Rminus.
rewrite H2.
rewrite (Rplus_opp_r r2).
by [].
move=> H1.
elim H1.
move=> H2.
left.
rewrite - (Rplus_0_l r1).
rewrite (Rplus_comm 0 r1).
rewrite - (Rplus_0_l r2).
rewrite - {2}(Rplus_opp_r r1).
rewrite (Rplus_assoc r1 (- r1) r2).
rewrite (Rplus_comm (- r1) r2).
apply (Rplus_lt_compat_l r1 0 (r2 + - r1) H2).
move=> H2.
right.
rewrite - (Rplus_0_l r1).
rewrite - (Rplus_0_l r2).
rewrite (Rplus_comm 0 r2).
rewrite - {2}(Rplus_opp_r r1).
rewrite (Rplus_comm r1 (- r1)).
rewrite - (Rplus_assoc r2 (- r1) r1).
f_equal.
apply H2.
Qed.

Lemma Problem_1_1_2_2_sub : forall r1 r2 : R, r1 <= r2 <-> r2 >= r1.
Proof.
move=> r1 r2.
rewrite /iff.
apply conj.
move=> H1.
elim H1.
by [left].
by [right].
move=> H1.
elim H1.
by [left].
by [right].
Qed.

Lemma Problem_1_1_2_2 : forall r1 r2 : R, r1 <= r2 <-> - r1 >= -r2.
Proof.
move=> r1 r2.
apply conj.
move=> H1.
apply (proj1 (Problem_1_1_2_2_sub (- r2) (- r1))).
apply (proj2 (Problem_1_1_2_1 (- r2) (- r1))).
rewrite /Rminus.
rewrite (Problem_1_1_1_3 r2).
rewrite (Rplus_comm (- r1) r2).
apply (proj1 (Problem_1_1_2_1 r1 r2) H1).
move=> H1.
apply (proj2 (Problem_1_1_2_1 r1 r2)).
rewrite /Rminus.
rewrite (Rplus_comm r2 (- r1)).
rewrite - (Problem_1_1_1_3 r2).
apply (proj1 (Problem_1_1_2_1 (- r2) (- r1))).
apply (proj2 (Problem_1_1_2_2_sub (- r2) (- r1)) H1).
Qed.

Lemma Problem_1_1_2_3 : forall r1 r2 r3 : R, r1 <= r2 /\ r3 <= 0 -> r1 * r3 >= r2 * r3.
Proof.
move=> r1 r2 r3.
case.
move=> H1 H2.
elim H2.
move=> H3.
elim H1.
move=> H4.
apply (proj1 (Problem_1_1_2_2_sub (r2 * r3) (r1 * r3))).
apply (proj2 (Problem_1_1_2_2 (r2 * r3) (r1 * r3))).
rewrite - (Problem_1_1_1_7_l r1 r3).
rewrite - (Problem_1_1_1_7_l r2 r3).
rewrite (Rmult_comm r2 (- r3)).
rewrite (Rmult_comm r1 (- r3)).
left.
apply (Rmult_lt_compat_l (- r3) r1 r2).
rewrite - (Rplus_opp_r r3).
rewrite - {2}(Rplus_0_l (-r3)).
rewrite (Rplus_comm r3 (- r3)).
rewrite (Rplus_comm 0 (- r3)).
apply (Rplus_lt_compat_l (- r3) r3 0 H3).
apply H4.
right.
f_equal.
apply H.
right.
rewrite (Rmult_comm r1 r3).
rewrite (Rmult_comm r2 r3).
rewrite H.
rewrite (Problem_1_1_1_4 r1).
rewrite (Problem_1_1_1_4 r2).
by [].
Qed.

Lemma Problem_1_1_2_4 : forall r: R, r > 0 -> /r > 0.
Proof.
move=> r.
elim (total_order_T (/ r) 0).
case.
move=> H1 H2.
apply False_ind.
apply (Rlt_asym 0 1 Formula_1_4).
rewrite - (Rinv_l r).
rewrite - (Problem_1_1_1_4 r).
rewrite (Rmult_comm 0 r).
rewrite (Rmult_comm (/ r) r).
apply (Rmult_lt_compat_l r (/ r) 0 H2 H1).
move=> H3.
rewrite H3 in H2.
apply (Rlt_asym 0 0).
apply H2.
apply H2.
move=> H1 H2.
apply False_ind.
apply R1_neq_R0.
rewrite - (Rinv_l r).
rewrite H1.
apply (Problem_1_1_1_4 r).
move=> H3.
rewrite H3 in H2.
apply (Rlt_asym 0 0).
apply H2.
apply H2.
move=> H1 H2.
apply H1.
Qed.

Lemma Problem_1_1_2_5 : forall r1 r2 r3 r4 : R, r1 <= r2 /\ r3 <= r4 -> r1 + r3 <= r2 + r4.
Proof.
move=> r1 r2 r3 r4.
case.
move=> H1 H2.
elim H1.
elim H2.
move=> H3 H4.
left.
apply (Rlt_trans (r1 + r3) (r2 + r3) (r2 + r4)).
rewrite (Rplus_comm r1 r3).
rewrite (Rplus_comm r2 r3).
apply (Rplus_lt_compat_l r3 r1 r2 H4).
apply (Rplus_lt_compat_l r2 r3 r4 H3).
move=> H3 H4.
rewrite H3.
rewrite (Rplus_comm r1 r4).
rewrite (Rplus_comm r2 r4).
left.
apply (Rplus_lt_compat_l r4 r1 r2 H4).
elim H2.
move=> H3 H4.
rewrite H4.
left.
apply (Rplus_lt_compat_l r2 r3 r4 H3).
move=> H3 H4.
rewrite H3.
rewrite H4.
right.
by [].
Qed.

Lemma Problem_1_1_2_6 : forall r1 r2 r3 r4 : R, r1 <= r2 /\ r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
move=> r1 r2 r3 r4.
case.
move=> H1 H2.
elim H1.
move=> H3.
apply (Rlt_trans (r1 + r3) (r2 + r3) (r2 + r4)).
rewrite (Rplus_comm r1 r3).
rewrite (Rplus_comm r2 r3).
apply (Rplus_lt_compat_l r3 r1 r2 H3).
apply (Rplus_lt_compat_l r2 r3 r4 H2).
move=> H3.
rewrite H3.
apply (Rplus_lt_compat_l r2 r3 r4 H2).
Qed.

Lemma Rlt_to_Rneq : forall r1 r2 : R, r1 < r2 -> r1 <> r2.
Proof.
move=> r1 r2.
move=> H1 H2.
rewrite H2 in H1.
apply (Rlt_asym r2 r2).
apply H1.
apply H1.
Qed.

Lemma Req_to_nRlt : forall r1 r2 : R, r1 = r2 -> ~ r1 < r2.
Proof.
move=> r1 r2.
move=> H1 H2.
rewrite H1 in H2.
apply (Rlt_asym r2 r2).
apply H2.
apply H2.
Qed.

Lemma Rgt_to_Rneq : forall r1 r2 : R, r1 > r2 -> r1 <> r2.
Proof.
move=> r1 r2.
move=> H1 H2.
rewrite H2 in H1.
apply (Rlt_asym r2 r2).
apply H1.
apply H1.
Qed.

Lemma Req_to_nRgt : forall r1 r2 : R, r1 = r2 -> ~ r1 > r2.
Proof.
move=> r1 r2.
move=> H1 H2.
rewrite H1 in H2.
apply (Rlt_asym r2 r2).
apply H2.
apply H2.
Qed.

Lemma Proposition_1_1 : forall r1 r2 : R, r1 < r2 -> (exists r3 : R, (r1 < r3) /\ (r3 < r2)).
Proof.
move=> r1 r2.
move=> H3.
exists ((r1 + r2) / (1 + 1)).
suff: (1 + 1) > 0.
suff: (1 + 1) <> 0.
move=> H1 H2.
apply conj.
rewrite /Rdiv.
rewrite (Rmult_comm (r1 + r2) (/ (1 + 1))).
rewrite - {1}(Rmult_1_l r1).
rewrite - {1}(Rinv_l (1 + 1) H1).
rewrite (Rmult_assoc (/ (1 + 1)) (1 + 1) r1).
apply (Rmult_lt_compat_l (/ (1 + 1)) ((1 + 1) * r1) (r1 + r2)).
apply (Problem_1_1_2_4 (1 + 1) H2).
rewrite (Rmult_comm (1 + 1) r1).
rewrite (Rmult_plus_distr_l r1 1 1).
rewrite (Rmult_1_r r1).
apply (Rplus_lt_compat_l r1 r1 r2 H3).
rewrite /Rdiv.
rewrite (Rmult_comm (r1 + r2) (/ (1 + 1))).
rewrite - {2}(Rmult_1_l r2).
rewrite - {3}(Rinv_l (1 + 1) H1).
rewrite (Rmult_assoc (/ (1 + 1)) (1 + 1) r2).
apply (Rmult_lt_compat_l (/ (1 + 1)) (r1 + r2) ((1 + 1) * r2)).
apply (Problem_1_1_2_4 (1 + 1) H2).
rewrite (Rmult_comm (1 + 1) r2).
rewrite (Rmult_plus_distr_l r2 1 1).
rewrite (Rmult_1_r r2).
apply (Rplus_lt_compat_r r2 r1 r2 H3).
suff: 1 + 1 > 0.
apply (Rgt_to_Rneq (1 + 1) 0).
apply (Rlt_trans 0 1 (1+1)).
apply Formula_1_4.
rewrite - {1}(Rplus_0_r 1).
apply (Rplus_lt_compat_l 1 0 1 Formula_1_4).
apply (Rlt_trans 0 1 (1+1)).
apply Formula_1_4.
rewrite - {1}(Rplus_0_r 1).
apply (Rplus_lt_compat_l 1 0 1 Formula_1_4).
Qed.

Lemma Formula_1_5 : forall r : R, (r >= 0) /\ (forall epsilon : R, (epsilon > 0) -> (epsilon > r)) -> r = 0.
Proof.
move=> r.
case.
move=> H1 H2.
elim H1.
move=> H3.
apply False_ind.
elim (Proposition_1_1 0 r H3).
move=> epsilon H5.
apply (Rlt_asym epsilon r).
apply (proj2 H5).
apply (H2 epsilon (proj1 H5)).
apply.
Qed.

Definition is_max := fun (E : (Ensemble R)) (m : R) => (In R E m) /\ forall x : R, (In R E x) -> x <= m.

Definition is_min := fun (E : (Ensemble R)) (m : R) => (In R E m) /\ forall x : R, (In R E x) -> x >= m.

Definition my_lower_bound : Ensemble R -> Ensemble R := fun (E : (Ensemble R)) => (fun (m : R) => forall x : R, (In R E x) -> x >= m).

Definition my_lower_bounded : Ensemble R -> Prop := fun x => (Inhabited R (my_lower_bound x)).

Definition my_upper_bound : Ensemble R -> Ensemble R := fun (E : (Ensemble R)) => (fun (m : R) => forall x : R, (In R E x) -> x <= m).

Definition my_upper_bounded : Ensemble R -> Prop := fun x => (Inhabited R (my_upper_bound x)).

Definition my_bounded : Ensemble R -> Prop := fun x => (Inhabited R (my_upper_bound x)) /\ (Inhabited R (my_lower_bound x)).

Lemma bounded_abs : forall A : Ensemble R , (my_bounded A) <-> (my_upper_bounded (Image.Im R R A Rabs)).
Proof.
move=> A.
apply conj.
move=> H1.
elim (proj1 H1).
move=> ma H2.
elim (proj2 H1).
move=> mi H3.
exists (Rmax (Rabs ma) (Rabs mi)).
move=> y H4.
elim H4.
move=> z.
rewrite {1}/Rabs.
elim (Rcase_abs z).
move=> H5 H6.
move=> y0 H7.
apply (Rle_trans y0 (Rabs mi) (Rmax (Rabs ma) (Rabs mi))).
rewrite /Rabs.
elim (Rcase_abs mi).
move=> H8.
rewrite H7.
apply (Ropp_ge_le_contravar z mi).
apply (H3 z H6).
move=> H8.
apply False_ind.
apply (Rge_not_lt mi 0 H8).
apply (Rle_lt_trans mi z 0).
apply (Rge_le z mi).
apply (H3 z H6).
apply H5.
apply (Rmax_r (Rabs ma) (Rabs mi)).
move=> H5 H6.
move=> y0 H7.
apply (Rle_trans y0 (Rabs ma) (Rmax (Rabs ma) (Rabs mi))).
rewrite /Rabs.
elim (Rcase_abs ma).
move=> H8.
apply False_ind.
apply (Rlt_not_ge ma 0 H8).
apply (Rge_trans ma z 0).
apply (Rle_ge z ma).
apply (H2 z H6).
apply H5.
move=> H8.
rewrite H7.
apply (H2 z H6).
apply (Rmax_l (Rabs ma) (Rabs mi)).
move=> H1.
elim H1.
move=> ma H2.
apply conj.
exists ma.
move=> z H4.
apply (Rle_trans z (Rabs z) ma).
apply (Rle_abs z).
apply (H2 (Rabs z)).
exists z.
apply H4.
by [].
exists (- ma).
move=> z H4.
apply (Rge_trans z (- (Rabs z)) (- ma)).
rewrite - {1}(Ropp_involutive z).
apply (Ropp_le_ge_contravar (- z) (Rabs z)).
rewrite - (Rabs_Ropp z).
apply (Rle_abs (- z)).
apply (Ropp_le_ge_contravar (Rabs z) ma).
apply (H2 (Rabs z)).
exists z.
apply H4.
by [].
Qed.

Lemma Formula_1_6 : (~(exists x : R , is_max (Full_set R) x)) /\ (~(exists x : R , is_min (Full_set R) x)).
Proof.
apply conj.
move=> H1.
elim H1.
move=> x.
move=> H2.
elim ((proj2 H2) (x + 1)).
move=> H3.
apply (Rlt_asym x (x + 1)).
rewrite - {1}(Rplus_0_r x).
apply (Rplus_lt_compat_l x 0 1).
apply (Formula_1_4).
apply H3.
move=> H3.
apply (R1_neq_R0).
rewrite - {2}(Rplus_0_r x) in H3.
apply (Rplus_eq_reg_l x 1 0 H3).
apply (Full_intro R (x + 1)).
move=> H1.
elim H1.
move=> x.
move=> H2.
elim ((proj2 H2) (x + - 1)).
move=> H3.
rewrite - {2}(Rplus_0_r x) in H3.
apply (Rlt_asym (x + 0) (x + -1)).
apply H3.
apply (Rplus_lt_compat_l x (- 1) 0).
rewrite - Ropp_0.
apply (Ropp_gt_lt_contravar 1 0).
apply (Formula_1_4).
move=> H3.
apply (R1_neq_R0).
rewrite - {2}(Rplus_0_r x) in H3.
rewrite - (Ropp_involutive 1).
rewrite - (Ropp_involutive 0).
apply (Ropp_eq_compat (- 1) (- 0)).
rewrite Ropp_0.
apply (Rplus_eq_reg_l x (- 1) 0 H3).
apply (Full_intro R (x + -1)).
Qed.

Lemma R_R_exist_max : forall r1 r2 : R, {x : R | is_max (Couple R r1 r2) x}.
Proof.
move=> r1 r2.
elim (Rlt_le_dec r1 r2).
move=> H1.
exists r2.
apply conj.
apply (Couple_r R r1 r2).
move=> x.
move=> H2.
elim H2.
apply (Rlt_le r1 r2 H1).
apply (Rle_refl r2).
move=> H1.
exists r1.
apply conj.
apply (Couple_l R r1 r2).
move=> x.
move=> H2.
elim H2.
apply (Rle_refl r1).
apply H1.
Qed.

Lemma R_R_exist_min : forall r1 r2 : R, {x : R | is_min (Couple R r1 r2) x}.
Proof.
move=> r1 r2.
elim (Rgt_ge_dec r1 r2).
move=> H1.
exists r2.
apply conj.
apply (Couple_r R r1 r2).
move=> x.
move=> H2.
elim H2.
apply (Rgt_ge r1 r2 H1).
apply (Rge_refl r2).
move=> H1.
exists r1.
apply conj.
apply (Couple_l R r1 r2).
move=> x.
move=> H2.
elim H2.
apply (Rge_refl r1).
apply H1.
Qed.

Definition my_abs (r : R) : R := let (a,_) := R_R_exist_max r (- r) in a.

Lemma Formula_1_7 : (forall r : R, (r >= 0 -> my_abs(r) = r)) /\ (forall r : R, (r <= 0 -> my_abs(r) = -r)).
Proof.
apply conj.
move=> r.
move=> H1.
rewrite /my_abs.
elim (R_R_exist_max r (- r)).
move=> x.
case.
move=> H2.
elim H2.
by [].
move=> H3.
apply (Rle_antisym (- r) r).
apply (Rle_trans (- r) 0 r).
rewrite - (Ropp_0).
apply (Ropp_ge_le_contravar r 0 H1).
apply (Rge_le r 0 H1).
apply (H3 r (Couple_l R r (- r))).
move=> r.
move=> H1.
rewrite /my_abs.
elim (R_R_exist_max r (- r)).
move=> x.
case.
move=> H2.
elim H2.
move=> H3.
apply (Rle_antisym r (- r)).
apply (Rle_trans r 0 (- r)).
apply H1.
rewrite - (Ropp_0).
apply (Ropp_le_contravar 0 r H1).
apply (H3 (- r) (Couple_r R r (- r))).
by [].
Qed.

Lemma Formula_1_8 : (forall r : R, (my_abs(- r) = my_abs(r))).
Proof.
move=> r.
elim (Rge_gt_dec r 0).
move=> H1.
rewrite ((proj1 Formula_1_7) r H1).
rewrite ((proj2 Formula_1_7) (- r)).
apply (Ropp_involutive r).
rewrite - Ropp_0.
apply (Ropp_ge_le_contravar r 0 H1).
move=> H1.
rewrite ((proj2 Formula_1_7) r (Rge_le 0 r (Rgt_ge 0 r H1))).
rewrite ((proj1 Formula_1_7) (- r)).
by [].
rewrite - Ropp_0.
apply (Ropp_ge_contravar r 0 (Rgt_ge 0 r H1)).
Qed.

Lemma Formula_1_9 : (forall r : R, -my_abs(r) <= r <= my_abs(r)).
Proof.
move=> r.
apply conj.
unfold my_abs.
elim (R_R_exist_max r (- r)).
move=> x.
move=> H1.
rewrite - (Ropp_involutive r).
apply (Ropp_le_contravar x (- r)).
apply (proj2 H1 (- r) (Couple_r R r (- r))).
unfold my_abs.
elim (R_R_exist_max r (- r)).
move=> x.
move=> H1.
apply (proj2 H1 r (Couple_l R r (- r))).
Qed.

Lemma Proposition_1_2_1 : (forall r : R, my_abs(r) >= 0) /\ (forall r : R, (my_abs(r) = 0) -> (r = 0)).
Proof.
apply conj.
move=> r.
elim (Rge_gt_dec r 0).
move=> H.
rewrite (proj1 Formula_1_7 r H).
apply H.
move=> H.
rewrite (proj2 Formula_1_7 r (Rge_le 0 r (Rgt_ge 0 r H))).
rewrite - Ropp_0.
apply (Ropp_ge_contravar r 0 ((Rgt_ge 0 r H))).
move=> r.
move=> H.
apply (Rle_antisym r 0).
rewrite - H.
apply (proj2 (Formula_1_9 r)).
rewrite - Ropp_0.
rewrite - H.
apply (proj1 (Formula_1_9 r)).
Qed.

Lemma Proposition_1_2_2 : (forall r1 r2 : R, my_abs(r1 * r2) = my_abs(r1) * my_abs(r2)).
Proof.
move=> r1 r2.
elim (Rge_gt_dec r1 0).
elim (Rge_gt_dec r2 0).
move=> H2 H1.
rewrite (proj1 Formula_1_7 r1 H1).
rewrite (proj1 Formula_1_7 r2 H2).
apply (proj1 Formula_1_7 (r1 * r2) ((Rle_ge 0 (r1 * r2) (Rmult_le_pos r1 r2 (Rge_le r1 0 H1) (Rge_le r2 0 H2))))).
move=> H2 H1.
rewrite (proj1 Formula_1_7 r1 H1).
rewrite (proj2 Formula_1_7 r2 (Rge_le 0 r2 (Rgt_ge 0 r2 H2))).
rewrite (proj2 Formula_1_7 (r1 * r2)).
apply (Ropp_mult_distr_r r1 r2).
apply (Ropp_le_cancel (r1 * r2) 0).
rewrite Ropp_0.
rewrite (Ropp_mult_distr_r r1 r2).
apply (Rmult_le_pos r1 (- r2)).
apply (Rge_le r1 0 H1).
apply (Ropp_0_ge_le_contravar r2).
apply (Rgt_ge 0 r2 H2).
elim (Rge_gt_dec r2 0).
move=> H2 H1.
rewrite (proj1 Formula_1_7 r2 H2).
rewrite (proj2 Formula_1_7 r1).
rewrite (proj2 Formula_1_7 (r1 * r2)).
apply (Ropp_mult_distr_l r1 r2).
apply (Ropp_le_cancel (r1 * r2) 0).
rewrite Ropp_0.
rewrite (Ropp_mult_distr_l r1 r2).
apply (Rmult_le_pos (- r1) r2).
apply (Ropp_0_ge_le_contravar r1).
apply (Rgt_ge 0 r1 H1).
apply (Rge_le r2 0 H2).
apply (Rge_le 0 r1).
apply (Rgt_ge 0 r1 H1).
move=> H2 H1.
rewrite (proj2 Formula_1_7 r2).
rewrite (proj2 Formula_1_7 r1).
rewrite (proj1 Formula_1_7 (r1 * r2)).
rewrite (Rmult_opp_opp r1 r2).
by [].
rewrite - (Rmult_opp_opp r1 r2).
apply (Rle_ge 0 (- r1 * - r2)).
apply (Rmult_le_pos (- r1) (- r2)).
apply (Ropp_0_ge_le_contravar r1).
apply (Rgt_ge 0 r1 H1).
apply (Ropp_0_ge_le_contravar r2).
apply (Rgt_ge 0 r2 H2).
apply (Rge_le 0 r1).
apply (Rgt_ge 0 r1 H1).
apply (Rge_le 0 r2).
apply (Rgt_ge 0 r2 H2).
Qed.

Lemma Proposition_1_2_3 : (forall r1 r2 : R, my_abs(r1 + r2) <= my_abs(r1) + my_abs(r2)).
Proof.
move=> r1 r2.
rewrite {1}/my_abs.
elim (R_R_exist_max (r1 + r2) (- (r1 + r2))).
move=> x.
move=> H1.
elim (proj1 H1).
apply (Rplus_le_compat r1 (my_abs r1) r2 (my_abs r2)).
apply (proj2 (Formula_1_9 r1)).
apply (proj2 (Formula_1_9 r2)).
apply (Ropp_le_cancel (- (r1 + r2)) (my_abs r1 + my_abs r2)).
rewrite (Ropp_involutive (r1 + r2)).
rewrite (Ropp_plus_distr (my_abs r1) (my_abs r2)).
apply (Rplus_le_compat (- (my_abs r1)) r1 (- (my_abs r2)) r2).
apply (proj1 (Formula_1_9 r1)).
apply (proj1 (Formula_1_9 r2)).
Qed.

Lemma Proposition_1_2_4 : (forall r1 r2 : R, my_abs(r1) - my_abs(r2) <= my_abs(r1 + r2)).
Proof.
move=> r1 r2.
apply (Rplus_le_reg_r (my_abs r2) (my_abs r1 - my_abs r2) (my_abs (r1 + r2))).
rewrite (Rplus_assoc (my_abs r1) (- my_abs r2) (my_abs r2)).
rewrite (Rplus_opp_l (my_abs r2)).
rewrite (Rplus_0_r (my_abs r1)).
rewrite - (Formula_1_8 r2).
suff: (r1 + r2) + - r2 = r1.
move=> H.
rewrite - {1}H.
apply (Proposition_1_2_3 (r1 + r2) (- r2)).
rewrite (Rplus_assoc r1 r2 (- r2)).
rewrite (Rplus_opp_r r2).
apply (Rplus_0_r r1).
Qed.

Lemma myabs_eq_abs : (forall r : R, my_abs(r) = Rabs(r)).
Proof.
move=> r.
rewrite /Rabs.
case (Rcase_abs r).
move=> H1.
apply ((proj2 Formula_1_7) r (Rlt_le r 0 H1)).
apply ((proj1 Formula_1_7) r).
Qed.

Lemma Formula_1_10 : (forall A : (Ensemble R) ,forall r1 r2 : R, (In R (my_upper_bound A) r1) -> (r1 <= r2) -> (In R (my_upper_bound A) r2)) /\ (forall A : (Ensemble R) ,forall r1 r2 : R, (In R (my_lower_bound A) r1) -> (r2 <= r1) -> (In R (my_lower_bound A) r2)).
Proof.
apply conj.
move=> A r1 r2.
unfold my_upper_bound.
unfold In.
move=> H1 H2.
move=> x.
move=> H3.
apply (Rle_trans x r1 r2).
apply ((H1 x) H3).
apply H2.
move=> A r1 r2.
unfold my_lower_bound.
unfold In.
move=> H1 H2.
move=> x.
move=> H3.
apply (Rge_trans x r1 r2).
apply ((H1 x) H3).
apply (Rle_ge r2 r1 H2).
Qed.

Definition is_greatest_lower_bound := fun (E : (Ensemble R)) (m : R) => (is_max (my_lower_bound E) m).

Definition is_least_upper_bound := fun (E : (Ensemble R)) (m : R) => (is_min (my_upper_bound E) m).

Lemma Proposition_1_3 : (forall (A : (Ensemble R)) (m : R),((forall (a : R), (In R A a) -> a <= m) /\ (forall (x : R), x < m -> (exists (a : R), (In R A a) /\ x < a)) <-> (is_least_upper_bound A m))) /\ (forall (A : (Ensemble R)) (m : R),((forall (a : R), (In R A a) -> a >= m) /\ (forall (x : R), x > m -> (exists (a : R), (In R A a) /\ x > a)) <-> (is_greatest_lower_bound A m))).
Proof.
apply conj.
move=> A m.
apply conj.
case.
move=> H1 H2.
rewrite /is_least_upper_bound.
rewrite /my_upper_bound.
rewrite /is_min.
rewrite /In.
apply conj.
move=> x H3.
apply (H1 x H3).
move=> x.
move=> H3.
elim (Rge_gt_dec x m).
apply.
move=> H4.
apply False_ind.
elim (H2 x H4).
move=> x0 H5.
apply (Rlt_not_le x0 x (proj2 H5)).
apply (H3 x0 (proj1 H5)).
move=> H1.
apply conj.
apply (proj1 H1).
move=> x H2.
rewrite /In in H1.
rewrite /my_upper_bound in H1.
apply (NNPP (exists a : R, In R A a /\ x < a)).
move=> H3.
apply (Rlt_not_ge x m H2).
rewrite /is_least_upper_bound in H1.
rewrite /is_min in H1.
apply ((proj2 H1) x).
move=> y.
move=> H4.
apply (Rnot_lt_le x y).
move=> H5.
apply H3.
exists y.
apply conj.
apply H4.
apply H5.
move=> A m.
apply conj.
case.
move=> H1 H2.
rewrite /is_greatest_lower_bound.
rewrite /my_lower_bound.
rewrite /is_max.
rewrite /In.
apply conj.
move=> x H3.
apply (H1 x H3).
move=> x.
move=> H3.
elim (Rlt_le_dec m x).
move=> H4.
apply False_ind.
elim (H2 x H4).
move=> x0 H5.
apply (Rlt_not_ge x0 x (proj2 H5)).
apply (H3 x0 (proj1 H5)).
apply.
move=> H1.
apply conj.
apply (proj1 H1).
move=> x H2.
apply (NNPP (exists a : R, In R A a /\ x > a)).
move=> H3.
apply (Rgt_not_le x m H2).
rewrite /is_greatest_lower_bound in H1.
rewrite /is_max in H1.
apply ((proj2 H1) x).
move=> y.
move=> H4.
apply (Rnot_gt_ge x y).
move=> H5.
apply H3.
exists y.
apply conj.
apply H4.
apply H5.
Qed.

Lemma max_unique : (forall (A : (Ensemble R)) (m1 m2 : R), ((is_max A m1) /\ (is_max A m2)) -> m1 = m2).
Proof.
move=> A m1 m2.
case.
move=> H1 H2.
apply (Rle_antisym m1 m2).
apply (proj2 H2 m1 (proj1 H1)).
apply (proj2 H1 m2 (proj1 H2)).
Qed.

Lemma min_unique : (forall (A : (Ensemble R)) (m1 m2 : R), ((is_min A m1) /\ (is_min A m2)) -> m1 = m2).
Proof.
move=> A m1 m2.
case.
move=> H1 H2.
apply (Rge_antisym m1 m2).
apply (proj2 H2 m1 (proj1 H1)).
apply (proj2 H1 m2 (proj1 H2)).
Qed.

Lemma greatest_lower_bound_unique : (forall (A : (Ensemble R)) (m1 m2 : R), ((is_greatest_lower_bound A m1) /\ (is_greatest_lower_bound A m2)) -> m1 = m2).
Proof.
move=> A.
apply (max_unique (my_lower_bound A)).
Qed.

Lemma least_upper_bound_unique : (forall (A : (Ensemble R)) (m1 m2 : R), ((is_least_upper_bound A m1) /\ (is_least_upper_bound A m2)) -> m1 = m2).
Proof.
move=> A.
apply (min_unique (my_upper_bound A)).
Qed.

Lemma Proposition_1_3_corollary_1 : (forall (A : (Ensemble R)) (m : R), (is_max A m) -> (is_least_upper_bound A m)) /\ (forall (A : (Ensemble R)) (m1 m2 : R), (is_max A m1) -> (is_least_upper_bound A m2) -> m1 = m2).
Proof.
suff: (forall (A : Ensemble R) (m : R), is_max A m -> is_least_upper_bound A m).
move=> H1.
apply conj.
apply H1.
move=> A m1 m2 H2 H3.
apply (least_upper_bound_unique A m1 m2).
apply conj.
apply (H1 A m1 H2).
apply H3.
move=> A M H1.
apply conj.
rewrite /is_max in H1.
rewrite /In.
rewrite /my_upper_bound.
apply (proj2 H1).
move=> x H2.
apply (Rle_ge M x).
apply (H2 M (proj1 H1)).
Qed.

Lemma Proposition_1_3_corollary_2 : (forall (A : (Ensemble R)) (m : R), (is_min A m) -> (is_greatest_lower_bound A m)) /\ (forall (A : (Ensemble R)) (m1 m2 : R), (is_min A m1) -> (is_greatest_lower_bound A m2) -> m1 = m2).
Proof.
suff: (forall (A : Ensemble R) (m : R), is_min A m -> is_greatest_lower_bound A m).
move=> H1.
apply conj.
apply H1.
move=> A m1 m2 H2 H3.
apply (greatest_lower_bound_unique A m1 m2).
apply conj.
apply (H1 A m1 H2).
apply H3.
move=> A m H1.
apply conj.
rewrite /is_min in H1.
rewrite /In.
rewrite /my_lower_bound.
apply (proj2 H1).
move=> x H2.
apply (Rge_le m x).
apply (H2 m (proj1 H1)).
Qed.

Lemma My_completeness_of_upper : (forall (A : (Ensemble R)), (Inhabited R A) /\ (my_upper_bounded A) -> {x : R | is_least_upper_bound A x}).
Proof.
move=> A.
case.
move=> H1 H2.
suff : {x : R | is_lub A x}.
move=> H3.
elim H3.
move=> x H4.
exists x.
apply conj.
apply (proj1 H4).
move=> x0.
move=> H5.
apply (Rle_ge x x0).
apply (proj2 H4 x0).
apply H5.
apply (completeness A).
elim H2.
move=> x H3.
rewrite /bound.
elim H2.
move=> x0.
move=> H4.
exists x0.
apply H4.
elim H1.
move=> x H3.
exists x.
apply H3.
Qed.

Definition MinusER : Ensemble R -> Ensemble R := fun (E : (Ensemble R)) => (fun (x : R) => (In R E (- x))).

Lemma My_completeness_of_lower : (forall (A : (Ensemble R)), (Inhabited R A) /\ (my_lower_bounded A) -> ({x : R | is_greatest_lower_bound A x})).
Proof.
move=> A.
case.
move=> H1 H2.
suff: {x : R | is_least_upper_bound (MinusER A) x}.
case.
move=> x.
move=> H3.
exists (- x).
apply conj.
move=> a.
move=> H4.
rewrite - (Ropp_involutive a).
apply (Ropp_le_ge_contravar (- a) x).
apply (proj1 H3).
rewrite - (Ropp_involutive a) in H4.
apply H4.
move=> x0 H4.
rewrite /is_least_upper_bound in H3.
rewrite /is_min in H3.
rewrite - (Ropp_involutive x0).
apply (Ropp_ge_le_contravar (- x0) x).
apply (proj2 H3 (- x0)).
move=> y.
move=> H5.
rewrite - (Ropp_involutive y).
apply (Ropp_ge_le_contravar (- y) x0).
apply (H4 (- y)).
apply H5.
apply (My_completeness_of_upper (MinusER A)).
apply conj.
elim H1.
move=> x H3.
exists (- x).
rewrite - (Ropp_involutive x) in H3.
apply H3.
elim H2.
move=> x H3.
exists (- x).
move=> x0.
move=> H4.
rewrite - (Ropp_involutive x0).
apply (Ropp_ge_le_contravar (- x0) x).
apply (H3 (- x0)).
apply H4.
Qed.

Lemma SqrtChoose : forall (x : R), (x >= 0) -> {r : R | r >= 0 /\ x = r * r}.
Proof.
move=> x H1.
elim (Rle_lt_or_eq_dec 0 x).
move=> H2.
elim (My_completeness_of_upper (fun (r : R) => r >= 0 /\ r * r <= x)).
move=> r H3.
exists r.
apply conj.
apply (Rle_ge 0 r).
apply ((proj1 H3) 0).
apply conj.
apply (Req_ge 0 0).
reflexivity.
rewrite (Rmult_0_r 0).
apply (Rge_le x 0 H1).
apply NNPP.
move=> H4.
elim (Rdichotomy x (r * r) H4).
move=> H5.
suff: (let eps := (Rmin r ((r * r - x) / (3 * r))) in False).
move=> H6.
apply H6.
move=> eps.
apply (Rle_not_lt (r - eps) r).
apply Rge_le.
apply ((proj2 H3) (r - eps)).
move=> x0 H6.
elim (proj1 H6).
move=> H7.
suff: (x0 * x0 <= (r - eps) * (r - eps)).
move=> H8.
apply (Rminus_le x0 (r - eps)).
apply (Rmult_le_reg_r (x0 + (r - eps)) (x0 - (r - eps)) 0).
apply (Rlt_le_trans 0 x0 (x0 + (r - eps))).
apply H7.
rewrite -{1} (Rplus_0_r x0).
apply (Rplus_le_compat_l x0 0 (r - eps)).
apply (Rge_le (r - eps) 0).
apply Rge_minus.
apply Rle_ge.
apply (Rmin_l r ((r * r - x) / (3 * r))).
rewrite (Rmult_0_l (x0 + (r - eps))).
rewrite (Rmult_plus_distr_r x0 (- (r - eps)) (x0 + (r - eps))).
rewrite (Rmult_plus_distr_l x0 x0 (r - eps)).
rewrite (Rmult_plus_distr_l (- (r - eps)) x0 (r - eps)).
rewrite - (Rplus_assoc (x0 * x0 + x0 * (r - eps)) (- (r - eps) * x0) (- (r - eps) * (r - eps))).
rewrite (Rplus_assoc (x0 * x0) (x0 * (r - eps)) (- (r - eps) * x0)).
rewrite (Rmult_comm x0 (r - eps)).
rewrite - (Rmult_plus_distr_r (r - eps) (- (r - eps)) x0).
rewrite (Rplus_opp_r (r - eps)).
rewrite (Rmult_0_l x0).
rewrite (Rplus_0_r (x0 * x0)).
rewrite (Ropp_mult_distr_l_reverse (r - eps) (r - eps)).
apply (Rle_minus (x0 * x0) ((r - eps) * (r - eps))).
apply H8.
apply (Rle_trans (x0 * x0) x ((r - eps) * (r - eps))).
apply (proj2 H6).
rewrite (Rmult_plus_distr_r r (- eps) (r - eps)).
rewrite (Rmult_plus_distr_l r r (- eps)).
rewrite (Rmult_plus_distr_l (- eps) r (- eps)).
apply (Rle_trans x (r * r - 3 * r * eps) (r * r + r * - eps + (- eps * r + - eps * - eps))).
apply (Rplus_le_reg_l (- x) x (r * r - 3 * r * eps)).
rewrite (Rplus_opp_l x).
apply (Rplus_le_reg_l (3 * r * eps) 0 (- x + (r * r - 3 * r * eps))).
rewrite (Rplus_0_r (3 * r * eps)).
rewrite - (Rplus_assoc (- x) (r * r) (- (3 * r * eps))).
rewrite (Rplus_comm (- x + r * r) (- (3 * r * eps))).
rewrite - (Rplus_assoc (3 * r * eps) (- (3 * r * eps)) (- x + r * r)).
rewrite (Rplus_opp_r (3 * r * eps)).
rewrite (Rplus_0_l (- x + r * r)).
suff: (3 * r > 0).
move=> H8.
apply (Rmult_le_reg_l (/ (3 * r)) (3 * r * eps) (- x + r * r)).
apply (Rinv_0_lt_compat (3 * r) H8).
rewrite - (Rmult_assoc (/ (3 * r)) (3 * r) eps).
rewrite (Rinv_l (3 * r)).
rewrite (Rmult_1_l eps).
rewrite (Rmult_comm (/ (3 * r)) (- x + r * r)).
rewrite (Rplus_comm (- x) (r * r)).
apply (Rmin_r r ((r * r - x) / (3 * r))).
apply (Rgt_not_eq (3 * r) 0).
apply H8.
apply (Rmult_lt_0_compat 3 r).
rewrite /3.
rewrite - (INR_IPR 3).
simpl.
apply (Rlt_trans 0 (1 + 1) (1 + 1 + 1)).
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
suff: (0 <= r).
move=> H8.
elim H8.
apply.
move=> H9.
apply False_ind.
apply (Rle_not_lt x (r * r)).
rewrite - H9.
rewrite (Rmult_0_r 0).
apply (Rge_le x 0 H1).
apply H5.
apply ((proj1 H3) 0).
apply conj.
apply (Req_ge 0 0).
reflexivity.
rewrite (Rmult_0_r 0).
apply (Rge_le x 0 H1).
rewrite (Rplus_assoc (r * r) (r * - eps) (- eps * r + - eps * - eps)).
apply (Rplus_le_compat_l (r * r) (- (3 * r * eps)) (r * - eps + (- eps * r + - eps * - eps))).
rewrite (Ropp_mult_distr_r (3 * r) eps).
rewrite /3.
rewrite - (INR_IPR 3).
simpl.
rewrite (Rmult_assoc (1 + 1 + 1) r (- eps)).
rewrite (Rmult_plus_distr_r (1 + 1) 1 (r * - eps)).
rewrite (Rmult_plus_distr_r 1 1 (r * - eps)).
rewrite (Rmult_1_l (r * - eps)).
rewrite (Rplus_assoc (r * - eps) (r * - eps) (r * - eps)).
apply (Rplus_le_compat_l (r * - eps) (r * - eps + r * - eps) (- eps * r + - eps * - eps)).
rewrite (Rmult_comm (- eps) r).
apply (Rplus_le_compat_l (r * - eps) (r * - eps) (- eps * - eps)).
rewrite (Rmult_opp_opp eps eps).
rewrite - (Ropp_mult_distr_r r eps).
rewrite (Ropp_mult_distr_l r eps).
suff: (0 <= eps).
move=> H8.
apply (Rmult_le_compat_r eps (- r) eps).
apply H8.
apply (Rle_trans (- r) 0 eps).
rewrite - Ropp_0.
apply (Ropp_le_contravar r 0).
apply (proj1 H3 0).
apply conj.
apply (Req_ge 0 0).
reflexivity.
rewrite (Rmult_0_r 0).
apply (Rge_le x 0 H1).
apply H8.
unfold eps.
unfold Rmin.
elim (Rle_dec r ((r * r - x) / (3 * r))).
move=> H8.
apply (proj1 H3 0).
apply conj.
apply (Req_ge 0 0).
reflexivity.
rewrite (Rmult_0_r 0).
apply (Rge_le x 0 H1).
move=> H8.
rewrite - (Rmult_0_r (r * r - x)).
apply (Rmult_le_compat_l (r * r - x) 0 (/ (3 * r))).
apply Rge_le.
apply (Rge_minus (r * r) x).
apply (Rle_ge x (r * r)).
apply (Rlt_le x (r * r) H5).
apply (Rlt_le 0 (/ (3 * r))).
apply (Rinv_0_lt_compat (3 * r)).
apply (Rmult_lt_0_compat 3 r).
rewrite /3.
rewrite - (INR_IPR 3).
simpl.
apply (Rlt_trans 0 (1 + 1) (1 + 1 + 1)).
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
suff: (0 <= r).
move=> H9.
elim H9.
apply.
move=> H10.
apply False_ind.
apply (Rle_not_lt x (r * r)).
rewrite - H10.
rewrite (Rmult_0_r 0).
apply (Rge_le x 0 H1).
apply H5.
apply ((proj1 H3) 0).
apply conj.
apply (Req_ge 0 0).
reflexivity.
rewrite (Rmult_0_r 0).
apply (Rge_le x 0 H1).
move=> H7.
rewrite H7.
apply Rge_le.
apply (Rge_minus r eps).
apply Rle_ge.
apply (Rmin_l r ((r * r - x) / (3 * r))).
rewrite -{2} (Rplus_0_r r).
apply (Rplus_lt_compat_l r (- eps) 0).
rewrite - Ropp_0.
apply (Ropp_lt_contravar eps 0).
suff: (0 < r).
move=> H6.
unfold eps.
unfold Rmin.
elim (Rle_dec r ((r * r - x) / (3 * r))).
move=> H7.
apply H6.
move=> H7.
apply (Rmult_lt_0_compat (r * r - x) (/ (3 * r))).
apply (Rgt_minus (r * r) x).
apply H5.
apply (Rinv_0_lt_compat (3 * r)).
apply (Rmult_lt_0_compat 3 r).
rewrite /3.
rewrite - (INR_IPR 3).
simpl.
apply (Rlt_trans 0 (1 + 1) (1 + 1 + 1)).
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
apply H6.
suff: (0 <= r).
move=> H7.
elim H7.
apply.
move=> H8.
apply False_ind.
apply (Rle_not_lt x (r * r)).
rewrite - H8.
rewrite (Rmult_0_r 0).
apply (Rge_le x 0 H1).
apply H5.
apply ((proj1 H3) 0).
apply conj.
apply (Req_ge 0 0).
reflexivity.
rewrite (Rmult_0_r 0).
apply (Rge_le x 0 H1).
move=> H5.
suff: (let eps := (Rmin r ((x - r * r) / (3 * r))) in False).
apply.
move=> eps.
apply (Rlt_not_le (r + eps) r).
rewrite -{1} (Rplus_0_r r).
apply (Rplus_lt_compat_l r 0 eps).
suff: (0 < r).
move=> H6.
unfold eps.
unfold Rmin.
elim (Rle_dec r ((x - r * r) / (3 * r))).
move=> H7.
apply H6.
move=> H7.
apply (Rmult_lt_0_compat (x - r * r) (/ (3 * r))).
apply (Rgt_minus x (r * r)).
apply H5.
apply (Rinv_0_lt_compat (3 * r)).
apply (Rmult_lt_0_compat 3 r).
rewrite /3.
rewrite - (INR_IPR 3).
simpl.
apply (Rlt_trans 0 (1 + 1) (1 + 1 + 1)).
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
apply H6.
elim (Rle_dec x 1).
move=> H6.
apply (Rlt_le_trans 0 x r).
apply H2.
apply (proj1 H3 x).
apply conj.
apply H1.
rewrite -{3} (Rmult_1_l x).
apply (Rmult_le_compat_r x x 1).
apply (Rlt_le 0 x H2).
apply H6.
move=> H6.
apply (Rlt_le_trans 0 1 r).
apply Rlt_0_1.
apply (proj1 H3 1).
apply conj.
apply (Rgt_ge 1 0 Rlt_0_1).
rewrite (Rmult_1_r 1).
apply (Rlt_le 1 x).
apply (Rnot_le_lt x 1 H6).
apply (proj1 H3 (r + eps)).
apply conj.
apply (Rge_trans (r + eps) eps 0).
rewrite -{2} (Rplus_0_l eps).
apply (Rplus_ge_compat_r eps r 0).
apply (Rle_ge 0 r).
apply ((proj1 H3) 0).
apply conj.
apply (Req_ge 0 0).
reflexivity.
rewrite (Rmult_0_r 0).
apply (Rge_le x 0 H1).
unfold eps.
unfold Rmin.
elim (Rle_dec r ((x - r * r) / (3 * r))).
move=> H6.
apply (Rle_ge 0 r).
apply ((proj1 H3) 0).
apply conj.
apply (Req_ge 0 0).
reflexivity.
rewrite (Rmult_0_r 0).
apply (Rge_le x 0 H1).
move=> H6.
rewrite - (Rmult_0_r (x - r * r)).
apply (Rmult_ge_compat_l (x - r * r) (/ (3 * r)) 0).
apply (Rge_minus x (r * r)).
apply (Rle_ge (r * r) x).
apply (Rlt_le (r * r) x H5).
apply (Rgt_ge (/ (3 * r)) 0).
apply (Rinv_0_lt_compat (3 * r)).
apply (Rmult_lt_0_compat 3 r).
rewrite /3.
rewrite - (INR_IPR 3).
simpl.
apply (Rlt_trans 0 (1 + 1) (1 + 1 + 1)).
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
elim (Rle_dec x 1).
move=> H7.
apply (Rlt_le_trans 0 x r).
apply H2.
apply (proj1 H3 x).
apply conj.
apply H1.
rewrite -{3} (Rmult_1_l x).
apply (Rmult_le_compat_r x x 1).
apply (Rlt_le 0 x H2).
apply H7.
move=> H7.
apply (Rlt_le_trans 0 1 r).
apply Rlt_0_1.
apply (proj1 H3 1).
apply conj.
apply (Rgt_ge 1 0 Rlt_0_1).
rewrite (Rmult_1_r 1).
apply (Rlt_le 1 x).
apply (Rnot_le_lt x 1 H7).
suff: (0 < r).
move=> H6.
rewrite (Rmult_plus_distr_r r eps (r + eps)).
rewrite (Rmult_plus_distr_l r r eps).
rewrite (Rmult_plus_distr_l eps r eps).
apply (Rle_trans (r * r + r * eps + (eps * r + eps * eps)) (r * r + 3 * r * eps) x).
rewrite /3.
rewrite - (INR_IPR 3).
simpl.
rewrite (Rmult_assoc (1 + 1 + 1) r eps).
rewrite (Rmult_plus_distr_r (1 + 1) 1 (r * eps)).
rewrite (Rmult_plus_distr_r 1 1 (r * eps)).
rewrite (Rmult_1_l (r * eps)).
rewrite (Rplus_assoc (r * eps) (r * eps) (r * eps)).
rewrite - (Rplus_assoc (r * r) (r * eps) (r * eps + r * eps)).
apply (Rplus_le_compat_l (r * r + r * eps) (eps * r + eps * eps) (r * eps + r * eps)).
rewrite (Rmult_comm eps r).
apply (Rplus_le_compat_l (r * eps) (eps * eps) (r * eps)).
apply (Rmult_le_compat_r eps eps r).
unfold eps.
unfold Rmin.
elim (Rle_dec r ((x - r * r) / (3 * r))).
move=> H7.
apply (Rlt_le 0 r H6).
move=> H7.
rewrite - (Rmult_0_r (x - r * r)).
apply (Rmult_le_compat_l (x - r * r) 0 (/ (3 * r))).
apply Rge_le.
apply (Rge_minus x (r * r)).
apply (Rgt_ge x (r * r) H5).
apply (Rlt_le 0 (/ (3 * r))).
apply (Rinv_0_lt_compat (3 * r)).
apply (Rmult_lt_0_compat 3 r).
rewrite /3.
rewrite - (INR_IPR 3).
simpl.
apply (Rlt_trans 0 (1 + 1) (1 + 1 + 1)).
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
apply H6.
apply (Rmin_l r ((x - r * r) / (3 * r))).
apply (Rplus_le_reg_l (- x) (r * r + 3 * r * eps) x).
rewrite (Rplus_opp_l x).
rewrite - (Rplus_assoc (- x) (r * r) (3 * r * eps)).
rewrite - (Rplus_opp_r (- x + r * r)).
apply (Rplus_le_compat_l (- x + r * r) (3 * r * eps) (- (- x + r * r))).
rewrite (Rplus_comm (- x) (r * r)).
rewrite (Ropp_minus_distr (r * r) x).
suff: (3 * r > 0).
move=> H7.
apply (Rmult_le_reg_l (/ (3 * r)) (3 * r * eps) (x - r * r)).
apply (Rinv_0_lt_compat (3 * r) H7).
rewrite - (Rmult_assoc (/ (3 * r)) (3 * r) eps).
rewrite (Rinv_l (3 * r)).
rewrite (Rmult_1_l eps).
rewrite (Rmult_comm (/ (3 * r)) (x - r * r)).
apply (Rmin_r r ((x - r * r) / (3 * r))).
apply (Rgt_not_eq (3 * r) 0).
apply H7.
apply (Rmult_lt_0_compat 3 r).
rewrite /3.
rewrite - (INR_IPR 3).
simpl.
apply (Rlt_trans 0 (1 + 1) (1 + 1 + 1)).
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
apply H6.
elim (Rle_dec x 1).
move=> H7.
apply (Rlt_le_trans 0 x r).
apply H2.
apply (proj1 H3 x).
apply conj.
apply H1.
rewrite -{3} (Rmult_1_l x).
apply (Rmult_le_compat_r x x 1).
apply (Rlt_le 0 x H2).
apply H7.
move=> H7.
apply (Rlt_le_trans 0 1 r).
apply Rlt_0_1.
apply (proj1 H3 1).
apply conj.
apply (Rgt_ge 1 0 Rlt_0_1).
rewrite (Rmult_1_r 1).
apply (Rlt_le 1 x).
apply (Rnot_le_lt x 1 H7).
apply conj.
apply (Inhabited_intro R (fun r : R => r >= 0 /\ r * r <= x) 0).
apply conj.
apply (Req_ge 0 0).
reflexivity.
rewrite (Rmult_0_l 0).
apply (Rge_le x 0 H1).
elim (Rle_dec 1 x).
move=> H3.
exists x.
move=> y.
move=> H4.
apply (Rnot_lt_le x y).
move=> H5.
apply (Rlt_not_le (y * y) y).
rewrite -{1} (Rmult_1_r y).
apply (Rmult_lt_compat_l y 1 y).
apply (Rlt_trans 0 x y H2 H5).
apply (Rle_lt_trans 1 x y H3 H5).
apply (Rlt_le (y * y) y).
apply (Rle_lt_trans (y * y) x y (proj2 H4) H5).
move=> H3.
exists 1.
move=> y.
move=> H4.
apply (Rnot_lt_le 1 y).
move=> H5.
apply (Rlt_not_le (y * y) y).
rewrite -{1} (Rmult_1_r y).
apply (Rmult_lt_compat_l y 1 y).
apply (Rlt_trans 0 1 y Rlt_0_1 H5).
apply H5.
apply (Rle_trans (y * y) x y).
apply (proj2 H4).
apply (Rlt_le x y).
apply (Rlt_trans x 1 y).
apply (Rnot_le_lt 1 x H3).
apply H5.
move=> H2.
exists 0.
apply conj.
apply (Req_ge 0 0).
reflexivity.
rewrite - H2.
rewrite (Rmult_0_l 0).
reflexivity.
apply (Rge_le x 0 H1).
Qed.

Definition MySqrt := fun (r : {x : R | x >= 0}) => proj1_sig (SqrtChoose (proj1_sig r) (proj2_sig r)).

Lemma MySqrtNature : forall (r : {x : R | x >= 0}), (MySqrt r) >= 0 /\ (proj1_sig r) = (MySqrt r) * (MySqrt r).
Proof.
move=> r.
apply (proj2_sig (SqrtChoose (proj1_sig r) (proj2_sig r))).
Qed.

Lemma SqrtUnique : forall (r : {x : R | x >= 0}) (y z : R), (y >= 0 /\ (proj1_sig r) = y * y) -> (z >= 0 /\ (proj1_sig r) = z * z) -> y = z.
Proof.
move=> r y z H1 H2.
suff: (y + z > 0 -> y = z).
move=> H3.
elim (proj1 H1).
move=> H4.
apply H3.
apply (Rge_gt_trans (y + z) y 0).
rewrite -{2} (Rplus_0_r y).
apply (Rplus_ge_compat_l y z 0).
apply (proj1 H2).
apply H4.
move=> H4.
elim (proj1 H2).
move=> H5.
apply H3.
apply (Rgt_ge_trans (y + z) y 0).
rewrite -{2} (Rplus_0_r y).
apply (Rplus_gt_compat_l y z 0).
apply H5.
apply (proj1 H1).
move=> H5.
rewrite H5.
apply H4.
move=> H3.
apply (Rminus_diag_uniq y z).
apply (Rmult_eq_reg_l (y + z) (y - z) 0).
rewrite (Rmult_0_r (y + z)).
rewrite (Rmult_plus_distr_r y z (y - z)).
rewrite (Rmult_plus_distr_l y y (- z)).
rewrite (Rmult_plus_distr_l z y (- z)).
rewrite - (Rplus_assoc (y * y + y * - z) (z * y) (z * - z)).
rewrite (Rplus_assoc (y * y) (y * - z) (z * y)).
rewrite (Rmult_comm z y).
rewrite - (Rmult_plus_distr_l y (- z) z).
rewrite (Rplus_opp_l z).
rewrite (Rmult_0_r y).
rewrite (Rplus_0_r (y * y)).
rewrite (Ropp_mult_distr_r_reverse z z).
rewrite - (proj2 H1).
rewrite - (proj2 H2).
apply (Rplus_opp_r (proj1_sig r)).
apply (Rgt_not_eq (y + z) 0 H3).
Qed.

Lemma MySqrtNature2 : forall (r : {x : R | x >= 0}) (y : R), (y >= 0 /\ (proj1_sig r) = y * y) -> (MySqrt r) = y.
Proof.
move=> r y H1.
have: (MySqrt r) >= 0 /\ (proj1_sig r) = (MySqrt r) * (MySqrt r).
apply (proj2_sig (SqrtChoose (proj1_sig r) (proj2_sig r))).
move=> H2.
apply (SqrtUnique r (MySqrt r) y H2 H1).
Qed.

(* Prop 1 4 の前半はMy_completeness_of_lowerに含まれている。*)
Lemma Proposition_1_4 : forall (A : Ensemble R) (x : R),is_greatest_lower_bound A x <-> is_least_upper_bound (MinusER A) (- x).
Proof.
move=> A x.
apply conj.
move=> H1.
apply conj.
move=> a.
move=> H2.
rewrite - (Ropp_involutive a).
apply (Ropp_ge_le_contravar (- a) x).
apply (proj1 H1).
apply H2.
move=> x0 H2.
rewrite /is_greatest_lower_bound in H1.
rewrite /is_max in H1.
rewrite - (Ropp_involutive x0).
apply (Ropp_le_ge_contravar (- x0) x).
apply (proj2 H1 (- x0)).
move=> y.
move=> H3.
rewrite - (Ropp_involutive y).
apply (Ropp_le_ge_contravar (- y) x0).
apply (H2 (- y)).
rewrite - (Ropp_involutive y) in H3.
apply H3.
move=> H1.
apply conj.
move=> a.
move=> H2.
apply (Ropp_ge_cancel a x).
apply (Rle_ge (- a) (- x)).
apply (proj1 H1 (- a)).
rewrite - (Ropp_involutive a) in H2.
apply H2.
move=> x0 H2.
rewrite /is_least_upper_bound in H1.
rewrite /is_min in H1.
apply (Rge_le x x0).
apply (Ropp_ge_cancel x x0).
apply (proj2 H1 (- x0)).
move=> y.
move=> H3.
rewrite - (Ropp_involutive y).
apply (Ropp_ge_le_contravar (- y) x0).
apply (H2 (- y)).
apply H3.
Qed.

Lemma Formula_1_11 : forall (A B : Ensemble R), (Included R A B) -> (Included R (my_upper_bound B) (my_upper_bound A)).
Proof.
move=> A B.
move=> H1.
move=> x.
move=> H2.
move=> y.
move=> H3.
apply H2.
apply (H1 y).
apply H3.
Qed.

Lemma Formula_1_12 : forall (A B : Ensemble R), (Included R A B) -> (Included R (my_upper_bound B) (my_upper_bound A)).
Proof.
move=> A B.
move=> H1.
move=> x.
move=> H2.
move=> y.
move=> H3.
apply H2.
apply (H1 y).
apply H3.
Qed.

Lemma Proposition_1_5_1 : forall (A B : Ensemble R), (Included R A B) -> (my_upper_bounded B) -> (my_upper_bounded A).
Proof.
move=> A B.
move=> H1 H2.
elim H2.
move=> x.
move=> H3.
exists x.
move=> y.
move=> H4.
apply (H3 y).
apply (H1 y H4).
Qed.

Lemma Proposition_1_5_2 : forall (A B : Ensemble R), (Included R A B) -> (my_lower_bounded B) -> (my_lower_bounded A).
Proof.
move=> A B.
move=> H1 H2.
elim H2.
move=> x.
move=> H3.
exists x.
move=> y.
move=> H4.
apply (H3 y).
apply (H1 y H4).
Qed.

Lemma Proposition_1_5_3 : forall (A B : Ensemble R) (x y : R), (Included R A B) -> (is_least_upper_bound A x) -> (is_least_upper_bound B y) -> x <= y.
Proof.
move=> A B x y.
move=> H1 H2 H3.
apply (Rge_le y x).
apply (proj2 H2 y).
move=> z.
move=> H4.
apply (proj1 H3 z).
apply (H1 z H4).
Qed.

Lemma Proposition_1_5_4 : forall (A B : Ensemble R) (x y : R), (Included R A B) -> (is_greatest_lower_bound A x) -> (is_greatest_lower_bound B y) -> x >= y.
Proof.
move=> A B x y.
move=> H1 H2 H3.
apply (Rle_ge y x).
apply (proj2 H2 y).
move=> z.
move=> H4.
apply (proj1 H3 z).
apply (H1 z H4).
Qed.

Definition PlusER : Ensemble R -> Ensemble R -> Ensemble R := fun (A B : (Ensemble R)) => (fun (x : R) => (exists (a b : R), (In R A a) /\ (In R B b) /\ x = a + b)).

Definition MultER : Ensemble R -> Ensemble R -> Ensemble R := fun (A B : (Ensemble R)) => (fun (x : R) => (exists (a b : R), (In R A a) /\ (In R B b) /\ x = a * b)).

Lemma Formula_1_13_1 : forall (A B : Ensemble R), (forall (a b : R), (is_least_upper_bound A a) -> (is_least_upper_bound B b) -> (is_least_upper_bound (PlusER A B) (a+b))).
Proof.
move=> A B.
move=> a b H3 H4.
suff: Inhabited R A.
move=> H1.
suff: Inhabited R B.
move=> H2.
apply conj.
move=> x H5.
elim H5.
move=> ax.
elim.
move=> bx.
case.
move=> H6.
case.
move=> H7.
move=> H8.
rewrite H8.
apply (Rplus_le_compat ax a bx b).
apply (proj1 H3 ax H6).
apply (proj1 H4 bx H7).
move=> x H5.
apply (Rnot_lt_ge x (a + b)).
move=> H6.
elim (proj2 (proj2 (proj1 Proposition_1_3 A a) H3) (a - (a + b - x) / 2)).
move=> a0.
case.
move=> H7 H8.
elim (proj2 (proj2 (proj1 Proposition_1_3 B b) H4) (b - (a + b - x) / 2)).
move=> b0.
case.
move=> H9 H10.
apply (Rlt_not_ge x (a0 + b0)).
suff: x = (a - (a + b - x)/2) + (b - (a + b - x)/2).
move=> H11.
rewrite H11.
apply (Rplus_lt_compat (a - (a + b - x)/2) a0 (b - (a + b - x)/2) b0).
apply H8.
apply H10.
rewrite /Rminus.
rewrite (Rplus_comm b (- ((a + b + - x) / 2))).
rewrite - (Rplus_assoc (a + - ((a + b + - x) / 2)) (- ((a + b + - x) / 2)) b).
rewrite (Rplus_assoc a (- ((a + b + - x) / 2)) (- ((a + b + - x) / 2))).
rewrite - (Ropp_plus_distr ((a + b + - x) / 2) ((a + b + - x) / 2)).
rewrite (eps2 (a + b + - x)).
rewrite (Ropp_plus_distr (a + b) (- x)).
rewrite (Ropp_plus_distr a b).
rewrite - (Rplus_assoc a (- a + - b) (- - x)).
rewrite - (Rplus_assoc a (- a) (- b)).
rewrite (Rplus_opp_r a).
rewrite (Rplus_0_l (- b)).
rewrite (Rplus_comm (- b) (- - x)).
rewrite (Rplus_assoc (- - x) (- b) b).
rewrite (Rplus_opp_l b).
rewrite (Rplus_0_r (- - x)).
rewrite (Ropp_involutive x).
by [].
apply (Rle_ge (a0 + b0) x).
apply (H5 (a0 + b0)).
exists a0.
exists b0.
apply conj.
apply H7.
apply conj.
apply H9.
by [].
rewrite - {3}(Rplus_0_r b).
rewrite {1}/Rminus.
apply (Rplus_lt_compat_l b (- ((a + b - x) / 2)) 0).
apply (Ropp_lt_gt_0_contravar ((a + b - x) / 2)).
apply (Rdiv_lt_0_compat (a + b - x) 2).
apply (Rgt_minus (a + b) x).
apply H6.
rewrite - (Rmult_1_r 2).
rewrite (RIneq.double 1).
apply (Rplus_lt_0_compat 1 1).
apply Rlt_0_1.
apply Rlt_0_1.
rewrite - {3}(Rplus_0_r a).
rewrite {1}/Rminus.
apply (Rplus_lt_compat_l a (- ((a + b - x) / 2)) 0).
apply (Ropp_lt_gt_0_contravar ((a + b - x) / 2)).
apply (Rdiv_lt_0_compat (a + b - x) 2).
apply (Rgt_minus (a + b) x).
apply H6.
rewrite - (Rmult_1_r 2).
rewrite (RIneq.double 1).
apply (Rplus_lt_0_compat 1 1).
apply Rlt_0_1.
apply Rlt_0_1.
elim (proj2 (proj2 (proj1 Proposition_1_3 B b) H4) (b - 1)).
move=> bx.
case.
move=> H5 H6.
apply (Inhabited_intro R B bx H5).
rewrite - {2}(Rplus_0_r b).
apply (Rplus_gt_compat_l b 0 (- 1)).
apply (Ropp_0_lt_gt_contravar 1).
apply (Rlt_0_1).
elim (proj2 (proj2 (proj1 Proposition_1_3 A a) H3) (a - 1)).
move=> ax.
case.
move=> H5 H6.
apply (Inhabited_intro R A ax H5).
rewrite - {2}(Rplus_0_r a).
apply (Rplus_gt_compat_l a 0 (- 1)).
apply (Ropp_0_lt_gt_contravar 1).
apply (Rlt_0_1).
Qed.

Lemma Formula_1_13_2 : forall (A B : Ensemble R), (forall (a b : R), (is_greatest_lower_bound A a) -> (is_greatest_lower_bound B b) -> (is_greatest_lower_bound (PlusER A B) (a+b))).
Proof.
move=> A B.
move=> a b H3 H4.
suff: Inhabited R A.
move=> H1.
suff: Inhabited R B.
move=> H2.
apply conj.
move=> x H5.
elim H5.
move=> ax.
elim.
move=> bx.
case.
move=> H6.
case.
move=> H7.
move=> H8.
rewrite H8.
apply (Rplus_ge_compat ax a bx b).
apply (proj1 H3 ax H6).
apply (proj1 H4 bx H7).
move=> x H5.
apply (Rnot_gt_le x (a + b)).
move=> H6.
elim (proj2 (proj2 (proj2 Proposition_1_3 A a) H3) (a + (x - (a + b)) / 2)).
move=> a0.
case.
move=> H7 H8.
elim (proj2 (proj2 (proj2 Proposition_1_3 B b) H4) (b + (x - (a + b)) / 2)).
move=> b0.
case.
move=> H9 H10.
apply (Rgt_not_le x (a0 + b0)).
suff: x = (a + (x - (a + b))/2) + (b + (x - (a + b))/2).
move=> H11.
rewrite H11.
apply (Rplus_gt_compat (a + (x - (a + b))/2) a0 (b + (x - (a + b))/2) b0).
apply H8.
apply H10.
rewrite (Rplus_comm b ((x - (a+b)) / 2)).
rewrite - (Rplus_assoc (a + ((x - (a+b)) / 2)) ((x - (a + b)) / 2) b).
rewrite (Rplus_assoc a ((x - (a + b)) / 2) ((x - (a + b)) / 2)).
rewrite (eps2 (x - (a + b))).
rewrite /Rminus.
rewrite (Ropp_plus_distr a b).
rewrite - (Rplus_assoc x (- a) (- b)).
rewrite (Rplus_comm x (- a)).
rewrite (Rplus_assoc (- a) x (- b)).
rewrite - (Rplus_assoc a (- a) (x + - b)).
rewrite (Rplus_opp_r a).
rewrite (Rplus_0_l (x + - b)).
rewrite (Rplus_assoc x (- b) b).
rewrite (Rplus_opp_l b).
rewrite (Rplus_0_r x).
by [].
apply (Rge_le (a0 + b0) x).
apply (H5 (a0 + b0)).
exists a0.
exists b0.
apply conj.
apply H7.
apply conj.
apply H9.
by [].
rewrite - {3}(Rplus_0_r b).
apply (Rplus_gt_compat_l b ((x - (a + b)) / 2) 0).
apply (Rdiv_lt_0_compat (x - (a + b)) 2).
apply (Rgt_minus x (a + b)).
apply H6.
rewrite - (Rmult_1_r 2).
rewrite (RIneq.double 1).
apply (Rplus_lt_0_compat 1 1).
apply Rlt_0_1.
apply Rlt_0_1.
rewrite - {3}(Rplus_0_r a).
apply (Rplus_gt_compat_l a ((x - (a + b)) / 2) 0).
apply (Rdiv_lt_0_compat (x - (a + b)) 2).
apply (Rgt_minus x (a + b)).
apply H6.
rewrite - (Rmult_1_r 2).
rewrite (RIneq.double 1).
apply (Rplus_lt_0_compat 1 1).
apply Rlt_0_1.
apply Rlt_0_1.
elim (proj2 (proj2 (proj2 Proposition_1_3 B b) H4) (b + 1)).
move=> bx.
case.
move=> H5 H6.
apply (Inhabited_intro R B bx H5).
rewrite - {2}(Rplus_0_r b).
apply (Rplus_gt_compat_l b 1 0).
apply (Rlt_0_1).
elim (proj2 (proj2 (proj2 Proposition_1_3 A a) H3) (a + 1)).
move=> ax.
case.
move=> H5 H6.
apply (Inhabited_intro R A ax H5).
rewrite - {2}(Rplus_0_r a).
apply (Rplus_gt_compat_l a 1 0).
apply (Rlt_0_1).
Qed.

Lemma Formula_1_13_3 : forall (A B : Ensemble R), ((Included R A (fun x : R => x >= 0)) /\ (Included R B (fun x : R => x >= 0))) -> (forall (a b : R), (is_least_upper_bound A a) -> (is_least_upper_bound B b) -> (is_least_upper_bound (MultER A B) (a*b))).
Proof.
move=> A B.
case.
move=> H5 H6.
move=> a b H7 H8.
suff: Inhabited R A.
move=> H1.
suff: Inhabited R B.
move=> H2.
elim (total_order_T a 0).
elim.
move=> H9.
apply False_ind.
apply (Rlt_not_ge a 0 H9).
elim H1.
move=> ax H10.
apply (Rge_trans a ax 0).
apply (Rle_ge ax a).
apply ((proj1 H7) ax H10).
apply (H5 ax H10).
move=> H9.
suff: forall ax : R, (In R A ax) -> ax = 0.
move=> H10.
rewrite H9.
rewrite (Rmult_0_l b).
apply ((proj1 Proposition_1_3_corollary_1) (MultER A B)).
apply conj.
elim H1.
move=> ax H11.
elim H2.
move=> bx H12.
exists ax.
exists bx.
apply conj.
apply H11.
apply conj.
apply H12.
rewrite (H10 ax).
rewrite (Rmult_0_l bx).
by [].
apply H11.
move=> ab.
move=> H12.
elim H12.
move=> ax.
move=> H13.
elim H13.
move=> bx.
case.
move=> H14.
case.
move=> H15 H16.
rewrite H16.
apply (Req_le_sym (ax * bx) 0).
rewrite (H10 ax H14).
rewrite (Rmult_0_l bx).
by [].
move=> ax H10.
apply (Rge_antisym ax 0).
apply (H5 ax H10).
rewrite - H9.
apply (Rle_ge ax a).
apply (proj1 H7 ax H10).
move=> H9.
elim (total_order_T b 0).
elim.
move=> H10.
apply False_ind.
apply (Rlt_not_ge b 0 H10).
elim H2.
move=> bx H11.
apply (Rge_trans b bx 0).
apply (Rle_ge bx b).
apply ((proj1 H8) bx H11).
apply (H6 bx H11).
move=> H10.
suff: forall bx : R, (In R B bx) -> bx = 0.
move=> H11.
rewrite H10.
rewrite (Rmult_0_r a).
apply ((proj1 Proposition_1_3_corollary_1) (MultER A B)).
apply conj.
elim H1.
move=> ax H12.
elim H2.
move=> bx H13.
exists ax.
exists bx.
apply conj.
apply H12.
apply conj.
apply H13.
rewrite (H11 bx).
rewrite (Rmult_0_r ax).
by [].
apply H13.
move=> ab.
move=> H12.
elim H12.
move=> ax.
move=> H13.
elim H13.
move=> bx.
case.
move=> H14.
case.
move=> H15 H16.
rewrite H16.
apply (Req_le_sym (ax * bx) 0).
rewrite (H11 bx H15).
rewrite (Rmult_0_r ax).
by [].
move=> bx H11.
apply (Rge_antisym bx 0).
apply (H6 bx H11).
rewrite - H10.
apply (Rle_ge bx b).
apply (proj1 H8 bx H11).
move=> H10.
apply conj.
move=> ab H11.
elim H11.
move=> ax H12.
elim H12.
move=> bx.
case.
move=> H13.
case.
move=> H14 H15.
rewrite H15.
apply (Rge_le (a * b) (ax * bx)).
apply (Rmult_ge_compat a ax b bx).
apply (H5 ax H13).
apply (H6 bx H14).
apply (Rle_ge ax a).
apply (proj1 H7 ax H13).
apply (Rle_ge bx b).
apply (proj1 H8 bx H14).
move=> ab H11.
apply (Rnot_gt_ge (a * b) ab).
move=> H12.
elim (Rge_gt_dec ab 0).
move=> H13.
elim (Proposition_1_1 ab (a * b) H12).
move=> cen H14.
elim (proj2 (proj2 (proj1 Proposition_1_3 A a) H7) (a * cen / (a * b))).
move=> ax.
case.
move=> H15 H16.
elim (proj2 (proj2 (proj1 Proposition_1_3 B b) H8) (b * ab / cen)).
move=> bx.
case.
move=> H17 H18.
apply (Rlt_not_le (ax * bx) ab).
suff: (a * cen / (a * b)) * (b * ab / cen) = ab.
move=> H19.
rewrite - H19.
suff: b * ab / cen >= 0.
move=> H20.
apply (Rmult_ge_0_gt_0_lt_compat (a * cen / (a * b)) ax (b * ab / cen) bx).
apply H20.
apply (Rgt_ge_trans ax (a * cen / (a * b)) 0).
apply H16.
apply (Rgt_ge (a * cen / (a * b)) 0).
apply (Rdiv_lt_0_compat (a * cen) (a * b)).
apply (Rmult_lt_0_compat a cen).
apply H9.
apply (Rgt_ge_trans cen ab 0).
apply (proj1 H14).
apply H13.
apply (Rmult_lt_0_compat a b).
apply H9.
apply H10.
apply H16.
apply H18.
rewrite /Rdiv.
rewrite - (Rmult_0_l (/ cen)).
apply (Rmult_ge_compat_r (/ cen) (b * ab) 0).
apply (Rgt_ge (/ cen) 0).
apply (Rinv_0_lt_compat cen).
apply (Rgt_ge_trans cen ab 0).
apply (proj1 H14).
apply H13.
rewrite - (Rmult_0_r b).
apply (Rmult_ge_compat_l b ab 0).
apply (Rgt_ge b 0 H10).
apply H13.
rewrite /Rdiv.
rewrite (Rinv_mult_distr a b (Rgt_not_eq a 0 H9) (Rgt_not_eq b 0 H10)).
rewrite - (Rmult_assoc (a * cen) (/ a) (/ b)).
rewrite (Rmult_comm a cen).
rewrite (Rmult_assoc cen a (/ a)).
rewrite (Rinv_r a (Rgt_not_eq a 0 H9)).
rewrite (Rmult_1_r cen).
rewrite - (Rmult_assoc (cen * / b) (b * ab) (/ cen)).
rewrite - (Rmult_assoc (cen * / b) b ab).
rewrite (Rmult_assoc cen (/ b) b).
rewrite (Rinv_l b (Rgt_not_eq b 0 H10)).
rewrite (Rmult_1_r cen).
rewrite (Rmult_comm cen ab).
rewrite (Rmult_assoc ab cen (/ cen)).
rewrite (Rinv_r cen).
apply (Rmult_1_r ab).
apply (Rgt_not_eq cen 0).
apply (Rgt_ge_trans cen ab 0).
apply H14.
apply H13.
apply (H11 (ax * bx)).
exists ax.
exists bx.
apply conj.
apply H15.
apply conj.
apply H17.
by [].
rewrite - {2}(Rmult_1_r b).
rewrite - (Rinv_r cen).
rewrite - (Rmult_assoc b cen (/ cen)).
rewrite /Rdiv.
apply (Rmult_lt_compat_r (/ cen) (b * ab) (b * cen)).
apply (Rinv_0_lt_compat cen).
apply (Rgt_ge_trans cen ab 0).
apply H14.
apply H13.
apply (Rmult_lt_compat_l b ab cen).
apply H10.
apply (proj1 H14).
apply (Rgt_not_eq cen 0).
apply (Rgt_ge_trans cen ab 0).
apply H14.
apply H13.
rewrite /Rdiv.
rewrite (Rinv_mult_distr a b (Rgt_not_eq a 0 H9) (Rgt_not_eq b 0 H10)).
rewrite - (Rmult_assoc (a * cen) (/ a) (/ b)).
rewrite (Rmult_comm a cen).
rewrite (Rmult_assoc cen a (/ a)).
rewrite (Rinv_r a (Rgt_not_eq a 0 H9)).
rewrite (Rmult_1_r cen).
rewrite - (Rmult_1_r a).
rewrite - (Rinv_r b (Rgt_not_eq b 0 H10)).
rewrite - (Rmult_assoc a b (/ b)).
apply (Rmult_lt_compat_r (/ b) cen (a * b)).
apply (Rinv_0_lt_compat b H10).
apply (proj2 H14).
move=> H13.
apply (Rlt_not_ge ab 0 H13).
elim H1.
move=> ax H15.
elim H2.
move=> bx H16.
apply (Rge_trans ab (ax * bx) 0).
apply (Rle_ge (ax * bx) ab).
apply (H11 (ax * bx)).
exists ax.
exists bx.
apply conj.
apply H15.
apply conj.
apply H16.
by [].
rewrite - (Rmult_0_r ax).
apply (Rmult_ge_compat_l ax bx 0).
apply (H5 ax H15).
apply (H6 bx H16).
elim (proj2 (proj2 (proj1 Proposition_1_3 B b) H8) (b - 1)).
move=> bx.
case.
move=> H9 H10.
apply (Inhabited_intro R B bx H9).
rewrite - {2}(Rplus_0_r b).
apply (Rplus_gt_compat_l b 0 (- 1)).
apply (Ropp_0_lt_gt_contravar 1).
apply (Rlt_0_1).
elim (proj2 (proj2 (proj1 Proposition_1_3 A a) H7) (a - 1)).
move=> ax.
case.
move=> H9 H10.
apply (Inhabited_intro R A ax H9).
rewrite - {2}(Rplus_0_r a).
apply (Rplus_gt_compat_l a 0 (- 1)).
apply (Ropp_0_lt_gt_contravar 1).
apply (Rlt_0_1).
Qed.

Lemma Formula_1_13_4 : forall (A B : Ensemble R), ((Included R A (fun x : R => x >= 0)) /\ (Included R B (fun x : R => x >= 0))) -> (forall (a b : R), (is_greatest_lower_bound A a) -> (is_greatest_lower_bound B b) -> (is_greatest_lower_bound (MultER A B) (a*b))).
Proof.
move=> A B.
case.
move=> H3 H4 a b H5 H6.
suff: Inhabited R A.
suff: Inhabited R B.
move=> H2 H1.
elim (total_order_T a 0).
elim.
move=> H9.
apply False_ind.
apply (Rlt_not_ge a 0 H9).
apply (Rle_ge 0 a).
apply (proj2 H5 0).
move=> ax H10.
apply (H3 ax H10).
move=> H7.
rewrite H7.
rewrite (Rmult_0_l b).
apply conj.
move=> ab H8.
elim H8.
move=> ax H9.
elim H9.
move=> bx.
case.
move=> H10.
case.
move=> H11 H12.
rewrite H12.
rewrite - (Rmult_0_r ax).
apply (Rmult_ge_compat_l ax bx 0).
apply (H3 ax H10).
apply (H4 bx H11).
move=> x H8.
apply (Rnot_gt_le x 0).
move=> H9.
elim H2.
move=> bx H10.
elim (total_order_T bx 0).
elim.
apply (Rge_not_lt bx 0 (H4 bx H10)).
move=> H11.
apply (Rgt_not_ge 0 x H9).
apply (H8 0).
elim H1.
move=> ax H12.
exists ax.
exists bx.
apply conj.
apply H12.
apply conj.
apply H10.
rewrite H11.
rewrite (Rmult_0_r ax).
by [].
move=> H11.
elim (proj2 (proj2 (proj2 Proposition_1_3 A a) H5) (x * / bx)).
move=> ax.
case.
move=> H12 H13.
apply (Rge_not_gt x (ax * bx)).
apply (H8 (ax * bx)).
exists ax.
exists bx.
apply conj.
apply H12.
apply conj.
apply H10.
by [].
rewrite - (Rmult_1_r x).
rewrite - (Rinv_l bx ((Rgt_not_eq bx 0 H11))).
rewrite - (Rmult_assoc x (/ bx) bx).
apply (Rmult_gt_compat_r bx (x * / bx) ax H11 H13).
rewrite H7.
apply (Rmult_gt_0_compat x (/ bx) H9 (Rinv_0_lt_compat bx H11)).
move=> H7.
elim (total_order_T b 0).
elim.
move=> H8.
apply False_ind.
apply (Rlt_not_ge b 0 H8).
apply (Rle_ge 0 b).
apply (proj2 H6 0).
move=> bx H9.
apply (H4 bx H9).
move=> H8.
rewrite H8.
rewrite (Rmult_0_r a).
apply conj.
move=> ab H9.
elim H9.
move=> ax H10.
elim H10.
move=> bx.
case.
move=> H11.
case.
move=> H12 H13.
rewrite H13.
rewrite - (Rmult_0_r ax).
apply (Rmult_ge_compat_l ax bx 0).
apply (H3 ax H11).
apply (H4 bx H12).
move=> x H9.
apply (Rnot_gt_le x 0).
move=> H10.
elim H1.
move=> ax H11.
elim (proj2 (proj2 (proj2 Proposition_1_3 B b) H6) (/ ax * x)).
move=> bx.
case.
move=> H12 H13.
apply (Rge_not_gt x (ax * bx)).
apply (H9 (ax * bx)).
exists ax.
exists bx.
apply conj.
apply H11.
apply conj.
apply H12.
by [].
rewrite - (Rmult_1_l x).
rewrite - (Rinv_r ax).
rewrite (Rmult_assoc ax (/ ax) x).
apply (Rmult_gt_compat_l ax (/ ax * x) bx).
apply (Rge_gt_trans ax a 0).
apply (proj1 H5 ax H11).
apply H7.
apply H13.
apply (Rgt_not_eq ax 0).
apply (Rge_gt_trans ax a 0).
apply (proj1 H5 ax H11).
apply H7.
rewrite H8.
apply (Rmult_gt_0_compat (/ ax) x).
apply ((Rinv_0_lt_compat ax)).
apply (Rge_gt_trans ax a 0).
apply (proj1 H5 ax H11).
apply H7.
apply H10.
move=> H8.
apply conj.
move=> ab.
move=> H9.
elim H9.
move=> ax.
move=> H10.
elim H10.
move=> bx.
case.
move=> H11.
case.
move=> H12 H13.
rewrite H13.
apply (Rmult_ge_compat ax a bx b).
apply (Rgt_ge a 0 H7).
apply (Rgt_ge b 0 H8).
apply (proj1 H5 ax H11).
apply (proj1 H6 bx H12).
move=> ab H9.
apply (Rnot_lt_le (a * b) ab).
move=> H10.
elim (Rge_gt_dec ab 0).
move=> H11.
elim (Proposition_1_1 (a * b) ab H10).
move=> cen H12.
elim (proj2 (proj2 (proj2 Proposition_1_3 A a) H5) (a * cen / (a * b))).
move=> ax.
case.
move=> H13 H14.
elim (proj2 (proj2 (proj2 Proposition_1_3 B b) H6) (b * ab / cen)).
move=> bx.
case.
move=> H15 H16.
apply (Rgt_not_ge (ax * bx) ab).
suff: (a * cen / (a * b)) * (b * ab / cen) = ab.
move=> H17.
rewrite - H17.
apply (Rmult_ge_0_gt_0_lt_compat ax (a * cen / (a * b)) bx (b * ab / cen)).
apply (H4 bx H15).
apply (Rgt_ge_trans (a * cen / (a * b)) ax 0).
apply H14.
apply (H3 ax H13).
apply H14.
apply H16.
rewrite /Rdiv.
rewrite (Rinv_mult_distr a b (Rgt_not_eq a 0 H7) (Rgt_not_eq b 0 H8)).
rewrite - (Rmult_assoc (a * cen) (/ a) (/ b)).
rewrite (Rmult_comm a cen).
rewrite (Rmult_assoc cen a (/ a)).
rewrite (Rinv_r a (Rgt_not_eq a 0 H7)).
rewrite (Rmult_1_r cen).
rewrite - (Rmult_assoc (cen * / b) (b * ab) (/ cen)).
rewrite - (Rmult_assoc (cen * / b) b ab).
rewrite (Rmult_assoc cen (/ b) b).
rewrite (Rinv_l b (Rgt_not_eq b 0 H8)).
rewrite (Rmult_1_r cen).
rewrite (Rmult_comm cen ab).
rewrite (Rmult_assoc ab cen (/ cen)).
rewrite (Rinv_r cen).
apply (Rmult_1_r ab).
apply (Rgt_not_eq cen 0).
apply (Rgt_ge_trans cen (a * b) 0).
apply (proj1 H12).
apply (Rgt_ge (a * b) 0).
apply (Rmult_gt_0_compat a b H7 H8).
apply (H9 (ax * bx)).
exists ax.
exists bx.
apply conj.
apply H13.
apply conj.
apply H15.
by [].
rewrite - {2}(Rmult_1_r b).
rewrite - (Rinv_r cen).
rewrite - (Rmult_assoc b cen (/ cen)).
rewrite /Rdiv.
apply (Rmult_gt_compat_r (/ cen) (b * ab) (b * cen)).
apply (Rinv_0_lt_compat cen).
apply (Rgt_ge_trans cen (a * b) 0).
apply (proj1 H12).
apply (Rgt_ge (a * b) 0).
apply (Rmult_gt_0_compat a b H7 H8).
apply (Rmult_gt_compat_l b ab cen).
apply H8.
apply (proj2 H12).
apply (Rgt_not_eq cen 0).
apply (Rgt_ge_trans cen (a * b) 0).
apply (proj1 H12).
apply (Rgt_ge (a * b) 0).
apply (Rmult_gt_0_compat a b H7 H8).
rewrite /Rdiv.
rewrite (Rinv_mult_distr a b (Rgt_not_eq a 0 H7) (Rgt_not_eq b 0 H8)).
rewrite - (Rmult_assoc (a * cen) (/ a) (/ b)).
rewrite (Rmult_comm a cen).
rewrite (Rmult_assoc cen a (/ a)).
rewrite (Rinv_r a (Rgt_not_eq a 0 H7)).
rewrite (Rmult_1_r cen).
rewrite - (Rmult_1_r a).
rewrite - (Rinv_r b (Rgt_not_eq b 0 H8)).
rewrite - (Rmult_assoc a b (/ b)).
apply (Rmult_gt_compat_r (/ b) cen (a * b)).
apply (Rinv_0_lt_compat b H8).
apply (proj1 H12).
move=> H11.
apply (Rlt_not_ge ab 0 H11).
apply (Rge_trans ab (a * b) 0).
apply (Rgt_ge ab (a * b) H10).
apply (Rgt_ge (a * b) 0).
apply (Rmult_gt_0_compat a b H7 H8).
elim (proj2 (proj2 (proj2 Proposition_1_3 B b) H6) (b + 1)).
move=> bx.
case.
move=> H7 H8.
apply (Inhabited_intro R B bx H7).
rewrite - {2}(Rplus_0_r b).
apply (Rplus_gt_compat_l b 1 0).
apply (Rlt_0_1).
elim (proj2 (proj2 (proj2 Proposition_1_3 A a) H5) (a + 1)).
move=> ax.
case.
move=> H7 H8.
apply (Inhabited_intro R A ax H7).
rewrite - {2}(Rplus_0_r a).
apply (Rplus_gt_compat_l a 1 0).
apply (Rlt_0_1).
Qed.

Definition RN : (Ensemble R) := (fun x:R => exists n:nat, INR n = x).

Fixpoint conv (n k:nat) : nat := match k with
  | O => 1%nat
  | S k => (match n with
    | O => 0%nat
    | S n => (conv n k) + (conv n (S k))%nat
  end)
end.

Lemma conv_fact : forall (n:nat), (forall (k:nat),(n >= k)%nat -> ((conv n k) * (fact k) * (fact (n - k)) = (fact n))%nat) /\ forall (k:nat),(n < k)%nat -> ((conv n k) = 0%nat).
Proof.
move=> n.
elim: n.
apply conj.
move=> k H1.
suff: 0%nat = k.
move=> H2.
rewrite - H2.
simpl.
by [].
apply (le_n_0_eq k H1).
move=> k.
case k.
move=> H1.
apply False_ind.
apply (lt_0_neq 0 H1).
by [].
move=> n0 H1.
simpl.
by [].
move=> n.
move=> H1.
apply conj.
move=> k.
case k.
move=> H2.
simpl conv.
simpl fact.
rewrite (mult_1_l 1).
rewrite (mult_1_l (fact n + n * fact n)).
by [].
move=> k0.
move=> H2.
simpl.
rewrite - {1}(mult_1_l (fact k0)).
rewrite - (mult_plus_distr_r 1 k0 (fact k0)).
rewrite (mult_assoc_reverse (conv n k0 + conv n (S k0)) ((1 + k0) * fact k0) (fact (n - k0)))%nat.
rewrite (mult_plus_distr_r (conv n k0) (conv n (S k0)) ((1 + k0) * fact k0 * fact (n - k0))).
rewrite - (mult_assoc_reverse (conv n k0) ((1 + k0) * fact k0) (fact (n - k0)))%nat.
rewrite - (mult_assoc_reverse (conv n k0) (1 + k0) (fact k0))%nat.
rewrite (mult_comm (conv n k0) (1 + k0)).
rewrite (mult_assoc_reverse ((1 + k0) * conv n k0) (fact k0) (fact (n - k0)))%nat.
rewrite (mult_assoc_reverse (1 + k0) (conv n k0) (fact k0 * fact (n - k0)))%nat.
rewrite - (mult_assoc_reverse (conv n k0) (fact k0) (fact (n - k0)))%nat.
rewrite (proj1 H1 k0 (le_S_n k0 n H2)).
move: H1.
case (le_S_n k0 n H2).
move=> H1.
rewrite (proj2 H1 (S k0)).
simpl.
by [].
by [].
move=> m H3 H4.
suff: fact (S k0) = ((1 + k0)%nat * (fact k0))%nat.
move=> H5.
rewrite - H5.
rewrite - (minus_Sn_m m k0 H3).
suff: fact (S (m - k0)) = ((S (m - k0)%nat) * fact (S m - S k0))%nat.
move=> H6.
rewrite H6.
rewrite (mult_comm (S (m - k0)) (fact (S m - S k0))).
rewrite - (mult_assoc_reverse (fact (S k0)) (fact (S m - S k0)) (S (m - k0))).
rewrite - (mult_assoc_reverse (conv (S m) (S k0)) (fact (S k0) * fact (S m - S k0)) (S (m - k0))).
rewrite - (mult_assoc_reverse (conv (S m) (S k0)) (fact (S k0)) (fact (S m - S k0))).
rewrite (proj1 H4 (S k0)).
suff: (S (m - k0) = m - k0 + 1)%nat.
move=> H7.
rewrite H7.
simpl.
rewrite (mult_comm (fact m + m * fact m) (m - k0 + 1)).
rewrite - (plus_assoc (fact m + m * fact m) (k0 * (fact m + m * fact m)) ((m - k0 + 1) * (fact m + m * fact m))).
rewrite - (mult_plus_distr_r k0 (m - k0 + 1) (fact m + m * fact m)).
suff: (k0 + (m - k0 + 1))%nat = (1 + m)%nat.
move=> H8.
rewrite H8.
rewrite (mult_plus_distr_r 1 m (fact m + m * fact m)).
rewrite (mult_1_l (fact m + m * fact m)).
by [].
rewrite (plus_assoc k0 (m - k0) 1).
rewrite (le_plus_minus_r k0 m H3).
apply (plus_comm m 1).
elim (m - k0)%nat.
by [].
move=> n0 H7.
rewrite {1}H7.
by [].
apply (le_n_S k0 m H3).
by [].
by [].
move=> k.
elim k.
move=> H2.
apply False_ind.
apply (lt_not_le (S n) 0 H2).
elim n.
apply (le_Sn_le 0 1).
by [].
move=> n0.
move=> H3.
apply (le_Sn_le 0 (S (S n0))).
apply (le_n_S 0 (S n0) H3).
move=> n0 H2 H3.
simpl.
rewrite (proj2 H1 n0).
rewrite (proj2 H1 (S n0)).
by [].
apply (le_Sn_le (S n) (S n0) H3).
apply (le_S_n (S n) n0 H3).
Qed.

Lemma sigma_translation : forall (f : nat-> R) (n low high : nat),(high >= low /\ low >= n)%nat -> (sigma f low high) = (sigma (fun k:nat => f (k+n))%nat (low-n) (high-n)).
Proof.
move=> f.
suff: forall n low high : nat, (high >= low)%nat /\ (low >= n)%nat -> (high - n - (low - n) = high - low)%nat.
move=> H2.
move=> n low high H1.
rewrite /sigma.
rewrite (H2 n low high H1).
elim (high-low)%nat.
rewrite /sum_f_R0.
rewrite (plus_0_r (low - n)).
rewrite (plus_0_r low).
rewrite (plus_comm (low - n) n).
rewrite - (le_plus_minus n low (proj2 H1)).
by [].
move=> n0 H3.
simpl.
rewrite H3.
rewrite (plus_comm (low - n) (S n0)).
rewrite - (plus_assoc (S n0) (low - n) n).
rewrite (plus_comm (low - n) n).
rewrite - (le_plus_minus n low (proj2 H1)).
rewrite (plus_comm (S n0) low).
by [].
move=> n.
elim n.
move=> low high H1.
simpl.
rewrite - (minus_n_O low).
rewrite - (minus_n_O high).
by [].
move=> n0.
move=> H1.
move=> low high.
elim low.
case.
move=> H2 H3.
apply False_ind.
apply (le_not_gt (S n0) 0 H3).
apply (gt_Sn_O n0).
move=> low0.
elim high.
move=> H2.
case.
move=> H3 H4.
apply False_ind.
apply (le_not_gt (S low0) 0 H3).
apply (gt_Sn_O low0).
move=> high0.
move=> H2 H3 H4.
simpl.
apply (H1 low0 high0).
apply conj.
apply (le_S_n low0 high0 (proj1 H4)).
apply (le_S_n n0 low0 (proj2 H4)).
Qed.

Definition Rsequence := nat -> R.

Definition RSequencePlus (f g : Rsequence) : Rsequence := (fun n => (f n) + (g n)).

Definition RSequenceMultR (r : R) (f : Rsequence) : Rsequence := (fun n => r * (f n)).

Definition RSequenceOpp (f : Rsequence) : Rsequence := (fun n => - (f n)).

Definition RSequenceMinus (f g : Rsequence) : Rsequence := (fun n => (f n) - (g n)).

Definition RSequenceMult (f g : Rsequence) : Rsequence := (fun n => (f n) * (g n)).

Definition RSequenceInv (f : Rsequence) : Rsequence := (fun n => 1 / (f n)).

Definition RSequenceDiv (f g : Rsequence) : Rsequence := (fun n => (f n) / (g n)).

Lemma Sigma_Same : forall (f g : Rsequence) (low high : nat), (low <= high)%nat -> (forall k:nat, (low <= k <= high)%nat -> (f k) = (g k)) -> (sigma f low high) = (sigma g low high).
Proof.
move=> f g low high.
elim high.
move=> H1 H2.
rewrite /sigma.
simpl.
rewrite - (plus_n_O low).
apply (H2 low).
by [].
move=> high0 H1 H2 H3.
elim (le_lt_or_eq low (S high0) H2).
move=> H4.
rewrite ((sigma_last f) low (S high0)).
rewrite ((sigma_last g) low (S high0)).
simpl.
rewrite H1.
rewrite (H3 (S high0)).
by [].
by [].
apply (le_S_n low high0 H4).
move=> k H5.
apply H3.
apply conj.
apply (proj1 H5).
apply le_S.
apply (proj2 H5).
apply H4.
apply H4.
move=> H4.
rewrite - H4.
rewrite (sigma_eq_arg f low).
rewrite (sigma_eq_arg g low).
apply (H3 low).
by [].
Qed.

Lemma Sigma_Plus : forall (f g : Rsequence) (low high : nat),(sigma (RSequencePlus f g) low high) = (sigma f low high) + (sigma g low high).
Proof.
move=> f g low high.
rewrite /sigma.
elim (high-low)%nat.
rewrite /RSequencePlus.
simpl.
by [].
move=> n H1.
simpl.
rewrite H1.
rewrite /RSequencePlus.
rewrite - (Rplus_assoc (sum_f_R0 (fun k : nat => f (low + k)%nat) n + f (low + S n)%nat) (sum_f_R0 (fun k : nat => g (low + k)%nat) n) (g (low + S n)%nat)).
rewrite (Rplus_assoc (sum_f_R0 (fun k : nat => f (low + k)%nat) n) (f (low + S n)%nat) (sum_f_R0 (fun k : nat => g (low + k)%nat) n)).
rewrite (Rplus_comm (f (low + S n)%nat) (sum_f_R0 (fun k : nat => g (low + k)%nat) n)).
rewrite - (Rplus_assoc (sum_f_R0 (fun k : nat => f (low + k)%nat) n) (sum_f_R0 (fun k : nat => g (low + k)%nat) n) (f (low + S n)%nat)).
rewrite (Rplus_assoc (sum_f_R0 (fun k : nat => f (low + k)%nat) n + sum_f_R0 (fun k : nat => g (low + k)%nat) n) (f (low + S n)%nat) (g (low + S n)%nat)).
by [].
Qed.

Lemma Sigma_Mult : forall (r : R) (f : Rsequence) (low high : nat),(sigma (RSequenceMultR r f) low high) = r * (sigma f low high).
Proof.
move=> r f low high.
rewrite /sigma.
elim (high-low)%nat.
rewrite /RSequenceMultR.
simpl.
by [].
move=> n H1.
simpl.
rewrite H1.
rewrite /RSequenceMultR.
rewrite (Rmult_plus_distr_l r (sum_f_R0 (fun k : nat => f (low + k)%nat) n) (f (low + S n)%nat)).
by [].
Qed.

Theorem Binomial_Theorem : forall (n : nat) (x y : R), (pow (x + y) n) = (sigma (fun k => (INR (conv n k)) * (pow x k) * (pow y (n - k))) 0 n).
Proof.
move=> n x y.
elim n.
rewrite /sigma.
rewrite /sum_f_R0.
simpl.
rewrite (Rmult_1_l 1).
rewrite (Rmult_1_l 1).
by [].
move=> n0 H1.
suff: ((x + y) ^ S n0) = ((x + y) * (x + y) ^ n0).
move=> H2.
rewrite H2.
rewrite H1.
rewrite - (Sigma_Mult (x + y) (fun k : nat => INR (conv n0 k) * x ^ k * y ^ (n0 - k)) 0 n0).
rewrite /RSequenceMultR.
suff: (sigma (fun k : nat => (x + y) * (INR (conv n0 k) * x ^ k * y ^ (n0 - k))) 0 n0) = (sigma (fun k : nat => (INR (conv n0 k) * x ^ (S k) * y ^ (n0 - k))) 0 n0) + (sigma (fun k : nat => (INR (conv n0 k) * x ^ k * y ^ (S n0 - k))) 0 n0).
move=> H3.
rewrite H3.
suff: sigma (fun k : nat => INR (conv n0 k) * x ^ S k * y ^ (n0 - k)) 0 n0 = sigma (fun k : nat => INR (conv n0 (k - 1)) * x ^ k * y ^ ((S n0 - k))) (S 0) (S n0).
move=> H4.
rewrite H4.
suff: sigma (fun k : nat => INR (conv n0 (k - 1)) * x ^ k * y ^ (S n0 - k)) 1 (S n0) = sigma (fun k : nat => match k with
  | O => 0
  | S k => INR (conv n0 k) * x ^ (S k) * y ^ (n0 - k)
end) 0 (S n0).
move=> H5.
rewrite H5.
suff: sigma (fun k : nat => INR (conv n0 k) * x ^ k * y ^ (S n0 - k)) 0 n0 = sigma (fun k : nat => INR (conv n0 k) * x ^ k * y ^ S (n0 - k)) 0 (S n0).
move=> H6.
rewrite H6.
rewrite - (Sigma_Plus (fun k : nat => match k with
  | 0%nat => 0
  | S k0 => INR (conv n0 k0) * x ^ S k0 * y ^ (n0 - k0)
end) (fun k : nat => INR (conv n0 k) * x ^ k * y ^ S (n0 - k)) 0 (S n0)).
suff: forall k:nat, (k <= (S n0))%nat -> ((RSequencePlus (fun k : nat => match k with
  | 0%nat => 0
  | S k0 => INR (conv n0 k0) * x ^ S k0 * y ^ (n0 - k0)
end) (fun k : nat => INR (conv n0 k) * x ^ k * y ^ S (n0 - k))) k) = ((fun k : nat => INR (conv (S n0) k) * x ^ k * y ^ (S n0 - k)) k).
move=> H7.
apply (Sigma_Same (RSequencePlus (fun k : nat => match k with
  | 0%nat => 0
  | S k0 => INR (conv n0 k0) * x ^ S k0 * y ^ (n0 - k0)
end) (fun k : nat => INR (conv n0 k) * x ^ k * y ^ S (n0 - k))) (fun k : nat => INR (conv (S n0) k) * x ^ k * y ^ (S n0 - k)) 0 (S n0) ).
apply (le_0_n (S n0)).
rewrite /RSequencePlus.
move=> k H8.
elim k.
elim n0.
simpl.
apply (Rplus_0_l (1 * 1 * (y * 1))).
move=> n1 H9.
simpl.
apply (Rplus_0_l (1 * 1 * (y * (y * y ^ n1)))).
move=> k0 H9.
elim (le_or_lt (S k0) n0).
move=> H10.
rewrite (minus_Sn_m n0 (S k0) H10).
simpl.
rewrite (plus_INR (conv n0 k0) (conv n0 (S k0))).
rewrite (Rmult_plus_distr_r (INR (conv n0 k0)) (INR (conv n0 (S k0))) (x * x ^ k0)).
rewrite (Rmult_plus_distr_r (INR (conv n0 k0) * (x * x ^ k0)) (INR (conv n0 (S k0)) * (x * x ^ k0)) (y ^ (n0 - k0))).
by [].
move=> H10.
simpl.
rewrite (proj2 (conv_fact n0) (S k0) H10).
simpl.
rewrite (Rmult_0_l (x * x ^ k0)).
rewrite (Rmult_0_l (y * y ^ (n0 - S k0))).
rewrite (Rplus_0_r (INR (conv n0 k0) * (x * x ^ k0) * y ^ (n0 - k0))).
rewrite - (plus_n_O (conv n0 k0)).
by [].
move=> k H7.
rewrite /RSequencePlus.
elim k.
elim n0.
simpl.
apply (Rplus_0_l (1 * 1 * (y * 1))).
move=> n1 H8.
simpl.
apply (Rplus_0_l (1 * 1 * (y * (y * y ^ n1)))).
move=> k0 H8.
elim (le_or_lt (S k0) n0).
move=> H9.
rewrite (minus_Sn_m n0 (S k0) H9).
simpl.
rewrite (plus_INR (conv n0 k0) (conv n0 (S k0))).
rewrite (Rmult_plus_distr_r (INR (conv n0 k0)) (INR (conv n0 (S k0))) (x * x ^ k0)).
rewrite (Rmult_plus_distr_r (INR (conv n0 k0) * (x * x ^ k0)) (INR (conv n0 (S k0)) * (x * x ^ k0)) (y ^ (n0 - k0))).
by [].
move=> H10.
simpl.
rewrite (proj2 (conv_fact n0) (S k0) H10).
simpl.
rewrite (Rmult_0_l (x * x ^ k0)).
rewrite (Rmult_0_l (y * y ^ (n0 - S k0))).
rewrite (Rplus_0_r (INR (conv n0 k0) * (x * x ^ k0) * y ^ (n0 - k0))).
rewrite - (plus_n_O (conv n0 k0)).
by [].
rewrite ((sigma_last (fun k : nat => INR (conv n0 k) * x ^ k * y ^ S (n0 - k))) 0%nat (S n0)).
rewrite (proj2 (conv_fact n0) (S n0)).
simpl.
rewrite (Rmult_0_l (x * x ^ n0)).
rewrite (Rmult_0_l (y * y ^ (n0 - S n0))).
rewrite (Rplus_0_l (sigma (fun k : nat => INR (conv n0 k) * x ^ k * (y * y ^ (n0 - k))) 0 n0)).
rewrite (Sigma_Same (fun k : nat => INR (conv n0 k) * x ^ k * y ^ match k with
  | O => S n0
  | S l => n0 - l
end) (fun k : nat => INR (conv n0 k) * x ^ k * (y * y ^ (n0 - k))) 0 n0).
by [].
apply (le_O_n n0).
move=> k.
elim k.
move=> H6.
simpl.
rewrite - (minus_n_O n0).
by [].
move=> n1 H6 H7.
suff: y ^ S (n0 - S n1) = y * y ^ (n0 - S n1).
move=> H8.
rewrite - H8.
rewrite (minus_Sn_m n0 (S n1)).
simpl.
by [].
apply (proj2 H7).
by [].
by [].
apply (le_n_S 0 n0).
apply (le_O_n n0).
rewrite ((sigma_first (fun k : nat => match k with
  | 0%nat => 0
  | S k0 => INR (conv n0 k0) * x ^ S k0 * y ^ (n0 - k0)
end)) 0%nat (S n0)).
rewrite (Rplus_0_l (sigma (fun k : nat => match k with
  | 0%nat => 0
  | S k0 => INR (conv n0 k0) * x ^ S k0 * y ^ (n0 - k0)
end) 1 (S n0))).
by [].
apply (le_n_S 0 n0).
apply (le_O_n n0).
rewrite (sigma_translation (fun k : nat => INR (conv n0 (k - 1)) * x ^ k * y ^ (S n0 - k)) 1 1 (S n0)).
simpl Nat.sub.
rewrite - (minus_n_O n0).
apply (Sigma_Same (fun k : nat => INR (conv n0 k) * x ^ S k * y ^ (n0 - k)) (fun k : nat => INR (conv n0 (k + 1 - 1)) * x ^ (k + 1) * y ^ match (k + 1)%nat with
  | O => S n0
  | S l => n0 - l
end) 0 n0).
apply (le_O_n n0).
move=> k H4.
rewrite - (plus_Snm_nSm k 0).
rewrite - (plus_n_O (S k)).
simpl Nat.sub.
rewrite - (minus_n_O k).
by [].
apply conj.
apply (le_n_S 0 n0).
apply (le_0_n n0).
by [].
rewrite - (Sigma_Plus (fun k : nat => INR (conv n0 k) * x ^ S k * y ^ (n0 - k)) (fun k : nat => INR (conv n0 k) * x ^ k * y ^ (S n0 - k)) 0 n0).
apply (Sigma_Same (fun k : nat => (x + y) * (INR (conv n0 k) * x ^ k * y ^ (n0 - k))) (RSequencePlus (fun k : nat => INR (conv n0 k) * x ^ S k * y ^ (n0 - k)) (fun k : nat => INR (conv n0 k) * x ^ k * y ^ (S n0 - k))) 0 n0).
apply (le_0_n n0).
move=> k H3.
rewrite /RSequencePlus.
rewrite (Rmult_plus_distr_r x y (INR (conv n0 k) * x ^ k * y ^ (n0 - k))).
rewrite - (Rmult_assoc x (INR (conv n0 k) * x ^ k) (y ^ (n0 - k))).
rewrite - (Rmult_assoc x (INR (conv n0 k)) (x ^ k)).
rewrite (Rmult_comm x (INR (conv n0 k))).
rewrite - (Rmult_assoc y (INR (conv n0 k) * x ^ k) (y ^ (n0 - k))).
rewrite - (Rmult_assoc y (INR (conv n0 k)) (x ^ k)).
rewrite (Rmult_comm y (INR (conv n0 k))).
rewrite (Rmult_assoc (INR (conv n0 k)) y (x ^ k)).
rewrite (Rmult_comm y (x ^ k)).
rewrite - (Rmult_assoc (INR (conv n0 k)) (x ^ k) y).
rewrite (Rmult_assoc (INR (conv n0 k) * x ^ k) y (y ^ (n0 - k))).
rewrite - (minus_Sn_m n0 k).
simpl.
rewrite (Rmult_assoc (INR (conv n0 k)) x (x ^ k)).
by [].
apply (proj2 H3).
by [].
Qed.

Definition is_max_nat := fun (E : (Ensemble nat)) (m : nat) => (In nat E m) /\ forall x : nat, (In nat E x) -> (x <= m)%nat.

Definition is_min_nat := fun (E : (Ensemble nat)) (m : nat) => (In nat E m) /\ forall x : nat, (In nat E x) -> (x >= m)%nat.

Lemma Finite_max_R : forall (U : Ensemble R), (Finite R U) -> (Inhabited R U) -> exists m : R, (is_max U m).
Proof.
move=> U H1.
elim H1.
move=> H2.
apply False_ind.
elim H2.
move=> x H3.
elim H3.
move=> A H2 H3 x H4 H5.
move: H3.
elim H2.
exists x.
apply conj.
apply (Union_intror R (Empty_set R) (Singleton R x) x).
apply (In_singleton R x).
move=> x0.
elim.
move=> x1.
elim.
move=> x1.
elim.
apply (Req_le x x).
by [].
move=> A0 H6 H7 x0 H8.
elim.
move=> x1.
move=> H9.
elim (R_R_exist_max x x1).
move=> m H10.
exists m.
apply conj.
elim (proj1 H10).
apply (Union_intror R (Add R A0 x0) (Singleton R x) x).
apply (In_singleton R x).
apply (Union_introl R (Add R A0 x0) (Singleton R x) x1).
apply H9.
move=> x2.
elim.
move=> x3 H11.
apply (Rle_trans x3 x1 m).
apply (proj2 H9 x3 H11).
apply (proj2 H10 x1).
apply (Couple_r R x x1).
move=> x3.
elim.
apply (proj2 H10 x).
apply (Couple_l R x x1).
exists x0.
apply (Union_intror R A0 (Singleton R x0) x0).
apply (In_singleton R x0).
Qed.

Lemma Finite_min_R : forall (U : Ensemble R), (Finite R U) -> (Inhabited R U) -> exists m : R, (is_min U m).
Proof.
move=> U H1.
elim H1.
move=> H2.
apply False_ind.
elim H2.
move=> x H3.
elim H3.
move=> A H2 H3 x H4 H5.
move: H3.
elim H2.
exists x.
apply conj.
apply (Union_intror R (Empty_set R) (Singleton R x) x).
apply (In_singleton R x).
move=> x0.
elim.
move=> x1.
elim.
move=> x1.
elim.
apply (Req_ge x x).
by [].
move=> A0 H6 H7 x0 H8.
elim.
move=> x1.
move=> H9.
elim (R_R_exist_min x x1).
move=> m H10.
exists m.
apply conj.
elim (proj1 H10).
apply (Union_intror R (Add R A0 x0) (Singleton R x) x).
apply (In_singleton R x).
apply (Union_introl R (Add R A0 x0) (Singleton R x) x1).
apply H9.
move=> x2.
elim.
move=> x3 H11.
apply (Rge_trans x3 x1 m).
apply (proj2 H9 x3 H11).
apply (proj2 H10 x1).
apply (Couple_r R x x1).
move=> x3.
elim.
apply (proj2 H10 x).
apply (Couple_l R x x1).
exists x0.
apply (Union_intror R A0 (Singleton R x0) x0).
apply (In_singleton R x0).
Qed.

Lemma Finite_max_nat : forall (U : Ensemble nat), (Finite nat U) -> (Inhabited nat U) -> exists m : nat, (is_max_nat U m).
Proof.
move=> U H1.
elim H1.
move=> H2.
apply False_ind.
elim H2.
move=> x H3.
elim H3.
move=> A H2 H3 x H4 H5.
move: H3.
elim H2.
exists x.
apply conj.
apply (Union_intror nat (Empty_set nat) (Singleton nat x) x).
apply (In_singleton nat x).
move=> x0.
elim.
move=> x1.
elim.
move=> x1.
elim.
by [].
move=> A0 H6 H7 x0 H8.
elim.
move=> x1.
move=> H9.
exists (max x x1).
apply conj.
apply (Nat.max_case_strong x x1).
move=> H10.
apply (Union_intror nat (Add nat A0 x0) (Singleton nat x) x).
apply (In_singleton nat x).
move=> H10.
apply (Union_introl nat (Add nat A0 x0) (Singleton nat x) x1).
apply (proj1 H9).
move=> x2.
elim.
move=> x3 H10.
apply (le_trans x3 x1 (Init.Nat.max x x1)).
apply (proj2 H9 x3 H10).
apply (Nat.le_max_r x x1).
move=> x3.
elim.
apply (Nat.le_max_l x x1).
exists x0.
apply (Union_intror nat A0 (Singleton nat x0) x0).
apply (In_singleton nat x0).
Qed.

Lemma Finite_min_nat : forall (U : Ensemble nat), (Finite nat U) -> (Inhabited nat U) -> exists m : nat, (is_min_nat U m).
Proof.
move=> U H1.
elim H1.
move=> H2.
apply False_ind.
elim H2.
move=> x H3.
elim H3.
move=> A H2 H3 x H4 H5.
move: H3.
elim H2.
exists x.
apply conj.
apply (Union_intror nat (Empty_set nat) (Singleton nat x) x).
apply (In_singleton nat x).
move=> x0.
elim.
move=> x1.
elim.
move=> x1.
elim.
by [].
move=> A0 H6 H7 x0 H8.
elim.
move=> x1.
move=> H9.
exists (min x x1).
apply conj.
apply (Nat.min_case_strong x x1).
move=> H10.
apply (Union_intror nat (Add nat A0 x0) (Singleton nat x) x).
apply (In_singleton nat x).
move=> H10.
apply (Union_introl nat (Add nat A0 x0) (Singleton nat x) x1).
apply (proj1 H9).
move=> x2.
elim.
move=> x3 H10.
apply (le_trans (Init.Nat.min x x1) x1 x3).
apply (Nat.le_min_r x x1).
apply (proj2 H9 x3 H10).
move=> x3.
elim.
apply (Nat.le_min_l x x1).
exists x0.
apply (Union_intror nat A0 (Singleton nat x0) x0).
apply (In_singleton nat x0).
Qed.

Lemma Finite_Set_Included : forall (U : Type) (A B : Ensemble U), (Finite U B) -> (Included U A B) -> (Finite U A).
Proof.
suff: forall (U : Type) (B : Ensemble U), (Finite U B) -> forall (A : Ensemble U), (Included U A B) -> (Finite U A).
move=> H1 U A B H2 H3.
apply (H1 U B H2 A H3).
move=> U B.
elim.
move=> A H1.
suff: A = (Empty_set U).
move=> H2.
rewrite H2.
apply (Empty_is_finite U).
apply (Extensionality_Ensembles U A (Empty_set U)).
apply conj.
move=> x H2.
elim (H1 x H2).
move=> x H2.
elim H2.
move=> B0 H1 H2.
move=> x H3 A H4.
elim (classic (In U A x)).
move=> H5.
suff: Included U (Subtract U A x) B0.
move=> H6.
suff: A = (Add U (Subtract U A x) x).
move=> H7.
rewrite H7.
apply (Union_is_finite U (Subtract U A x) (H2 (Subtract U A x) H6) x).
move=> H8.
apply (proj2 H8).
by [].
apply (Extensionality_Ensembles U A (Add U (Subtract U A x) x)).
apply conj.
move=> y H7.
elim (classic (x = y)).
move=> H8.
apply (Union_intror U (Subtract U A x) (Singleton U x)).
rewrite H8.
by [].
move=> H8.
apply (Union_introl U (Subtract U A x) (Singleton U x)).
apply conj.
apply H7.
move=> H9.
apply H8.
elim H9.
by [].
move=> y.
elim.
move=> y0 H7.
apply (proj1 H7).
move=> y0 H7.
elim H7.
apply H5.
move=> y H6.
move : (proj2 H6).
elim (H4 y (proj1 H6)).
move=> y0.
move=> H7 H8.
apply H7.
move=> y0 H7 H8.
apply False_ind.
apply (H8 H7).
move=> H5.
apply (H2 A).
move=> y H6.
suff: In U A y.
elim (H4 y).
move=> y0.
move=> H7 H8.
apply H7.
move=> y0 H7 H8.
apply False_ind.
apply H5.
rewrite H7.
apply H8.
apply H6.
apply H6.
Qed.

Lemma Finite_Set_And_l : forall (U : Type) (A B : Ensemble U), (Finite U A) -> (Finite U (Intersection U A B)).
Proof.
move=> U A B H1.
apply (Finite_Set_Included U (Intersection U A B) A).
apply H1.
move=> x H2.
elim H2.
move=> y H3 H4.
apply H3.
Qed.

Lemma Finite_Set_And_r : forall (U : Type) (A B : Ensemble U), (Finite U B) -> (Finite U (Intersection U A B)).
Proof.
move=> U A B H1.
apply (Finite_Set_Included U (Intersection U A B) B).
apply H1.
move=> x H2.
elim H2.
move=> y H3.
apply.
Qed.

Lemma Finite_Set_Or : forall (U : Type) (A B : Ensemble U), (Finite U A) -> (Finite U B) -> (Finite U (Union U A B)).
Proof.
move=> U A B H1.
elim.
suff: A = (Union U A (Empty_set U)).
move=> H2.
rewrite - H2.
apply H1.
apply (Extensionality_Ensembles U A (Union U A (Empty_set U))).
apply conj.
move=> x H2.
apply (Union_introl U A (Empty_set U) x H2).
move=> x.
elim.
move=> x0.
apply.
move=> x0.
elim.
move=> B0 H2 H3.
move=> x H4.
elim (classic (In U A x)).
move=> H5.
suff: (Union U A B0) = (Union U A (Add U B0 x)).
move=> H6.
rewrite - H6.
apply H3.
apply (Extensionality_Ensembles U (Union U A B0) (Union U A (Add U B0 x))).
apply conj.
move=> y.
elim.
move=> y0 H6.
apply (Union_introl U A (Add U B0 x) y0 H6).
move=> y0 H6.
apply (Union_intror U A (Add U B0 x) y0).
apply (Union_introl U B0 (Singleton U x) y0 H6).
move=> y.
elim.
move=> y0 H6.
apply (Union_introl U A B0 y0 H6).
move=> y0.
elim.
move=> y1 H6.
apply (Union_intror U A B0 y1 H6).
move=> y1 H6.
apply (Union_introl U A B0 y1).
rewrite - H6.
apply H5.
move=> H5.
suff: (Union U A (Add U B0 x)) = (Add U (Union U A B0) x).
move=> H6.
rewrite H6.
apply (Union_is_finite U (Union U A B0) H3 x).
move=> H7.
move: H7 H4 H5.
elim.
move=> x0 H7 H8 H9.
apply (H9 H7).
move=> x0 H7 H8 H9.
apply (H8 H7).
apply (Extensionality_Ensembles U (Union U A (Add U B0 x)) (Add U (Union U A B0) x)).
apply conj.
move=> y.
elim.
move=> y0 H6.
apply (Union_introl U (Union U A B0) (Singleton U x) y0).
apply (Union_introl U A B0 y0 H6).
move=> y0.
elim.
move=> y1 H6.
apply (Union_introl U (Union U A B0) (Singleton U x) y1).
apply (Union_intror U A B0 y1 H6).
move=> y1 H6.
apply (Union_intror U (Union U A B0) (Singleton U x) y1 H6).
move=> y0.
elim.
move=> y1.
elim.
move=> y2 H6.
apply (Union_introl U A (Add U B0 x) y2 H6).
move=> y2 H6.
apply (Union_intror U A (Add U B0 x) y2).
apply (Union_introl U B0 (Singleton U x) y2 H6).
move=> y2 H6.
apply (Union_intror U A (Add U B0 x) y2).
apply (Union_intror U B0 (Singleton U x) y2 H6).
Qed.

Lemma nat_cardinal : forall (n : nat) , cardinal nat (fun x : nat => (x < n)%nat) n.
Proof.
move=> n.
elim n.
suff: (fun x : nat => (x < 0)%nat) = (Empty_set nat).
move=> H1.
rewrite H1.
apply (card_empty nat).
apply (Extensionality_Ensembles nat (fun x : nat => (x < 0)%nat) (Empty_set nat)).
apply conj.
move=> m H1.
apply False_ind.
apply (le_not_lt 0 m).
apply (le_O_n m).
apply H1.
move=> m.
elim.
move=> n0 H1.
suff: (Add nat (fun x : nat => (x < n0)%nat) n0) = (fun x : nat => (x < S n0)%nat).
move=> H2.
rewrite - H2.
apply (card_add nat (fun x : nat => (x < n0)%nat) n0 H1 n0).
move=> H3.
apply (le_Sn_n n0 H3).
apply (Extensionality_Ensembles nat (Add nat (fun x : nat => (x < n0)%nat) n0) (fun x : nat => (x < S n0)%nat)).
apply conj.
move=> x.
elim.
move=> x0 H2.
apply (lt_trans x0 n0 (S n0)).
apply H2.
by [].
move=> x0 H2.
rewrite H2.
by [].
move=> x H2.
elim (le_lt_or_eq (S x) (S n0)).
move=> H3.
apply (Union_introl nat (fun x0 : nat => (x0 < n0)%nat) (Singleton nat n0) x).
apply (lt_S_n x n0 H3).
move=> H3.
apply (Union_intror nat (fun x0 : nat => (x0 < n0)%nat) (Singleton nat n0) x).
rewrite - (Nat.pred_succ n0).
rewrite - (Nat.pred_succ x).
rewrite H3.
by [].
apply H2.
Qed.

Lemma Exist_min_nat : forall (U : Ensemble nat), (Inhabited nat U) -> exists m : nat, (is_min_nat U m).
Proof.
move=> U.
elim.
move=> n H1.
elim (classic (Inhabited nat (Intersection nat U (fun x:nat => (x < n)%nat)))).
move=> H2.
elim (Finite_min_nat (Intersection nat U (fun x : nat => (x < n)%nat))).
move=> x H3.
exists x.
apply conj.
elim (proj1 H3).
move=> y H4 H5.
apply H4.
move=> y.
elim (le_or_lt n y).
move=> H4 H5.
apply (le_trans x n y).
apply (le_trans x (S x) n).
apply (le_S x).
apply (le_n x).
elim (proj1 H3).
move=> y0 H6.
apply.
apply H4.
move=> H4 H5.
apply ((proj2 H3) y).
apply (Intersection_intro nat U (fun x0 : nat => (x0 < n)%nat) y H5).
apply H4.
apply (Finite_Set_And_r nat U (fun x : nat => (x < n)%nat)).
apply (cardinal_finite nat (fun x : nat => (x < n)%nat) n (nat_cardinal n)).
apply H2.
move=> H2.
exists n.
apply conj.
apply H1.
move=> x.
move=> H3.
elim (le_or_lt n x).
apply.
move=> H4.
apply False_ind.
apply H2.
apply (Inhabited_intro nat (Intersection nat U (fun x0 : nat => (x0 < n)%nat)) x).
apply (Intersection_intro nat U (fun x0 : nat => (x0 < n)%nat) x H3 H4).
Qed.

Definition UR := fun (a eps : R) => (fun (x : R) => R_dist x a < eps).

Lemma Formula_2_5 : forall (An : nat -> R) (x : R), (Un_cv An x) <-> forall (eps : R), (eps > 0) -> (Finite nat (fun (n : nat) => ~(In R (UR x eps) (An n)))).
Proof.
move=> An x.
apply conj.
move=> H1 eps H2.
elim (H1 eps H2).
move=> n H3.
apply (Finite_Set_Included nat (fun n0 : nat => ~ In R (UR x eps) (An n0)) (fun x : nat => (x < n)%nat)).
apply (cardinal_finite nat (fun x : nat => (x < n)%nat) n (nat_cardinal n)).
move=> n0 H4.
elim (le_or_lt n n0).
move=> H5.
apply False_ind.
apply H4.
apply (H3 n0 H5).
apply.
move=> H1 eps H2.
elim (classic (Inhabited nat (fun n : nat => ~ In R (UR x eps) (An n)))).
move=> H8.
elim (Finite_max_nat (fun n : nat => ~ In R (UR x eps) (An n)) (H1 eps H2)).
move=> n.
move=> H3.
exists (S n).
move=> n0 H5.
apply (Rnot_ge_lt (R_dist (An n0) x) eps).
move=> H6.
apply (le_not_gt (S n) n0 H5).
apply (le_n_S n0 n).
apply (proj2 H3 n0).
move=> H7.
apply (Rlt_not_ge (R_dist (An n0) x) eps H7 H6).
apply H8.
move=> H3.
exists O.
move=> n H4.
apply (Rnot_ge_lt (R_dist (An n) x) eps).
move=> H5.
apply H3.
apply (Inhabited_intro nat (fun n0 : nat => ~ In R (UR x eps) (An n0)) n).
apply (Rge_not_lt (R_dist (An n) x) eps H5).
Qed.

Lemma Formula_2_6 : forall (An Bn : nat -> R), (Finite nat (fun n : nat => (An n) <> (Bn n))) -> forall (x : R), (Un_cv An x) <-> (Un_cv Bn x).
Proof.
suff: forall (An Bn : nat -> R), (Finite nat (fun n : nat => (An n) <> (Bn n))) -> forall (x : R), (Un_cv An x) -> (Un_cv Bn x).
move=> H1.
move=> An Bn H2 x.
apply conj.
apply (H1 An Bn H2 x).
suff: (fun n : nat => An n <> Bn n) = (fun n : nat => Bn n <> An n).
move=> H3.
rewrite H3 in H2.
apply (H1 Bn An H2 x).
apply (Extensionality_Ensembles nat (fun n : nat => An n <> Bn n) (fun n : nat => Bn n <> An n)).
apply conj.
move=> n H3.
move=> H4.
apply H3.
rewrite H4.
by [].
move=> n H3.
move=> H4.
apply H3.
rewrite H4.
by [].
move=> An Bn H1.
elim (classic (Inhabited nat (fun n : nat => An n <> Bn n))).
move=> H2.
elim (Finite_max_nat (fun n : nat => An n <> Bn n) H1).
move=> n.
move=> H3 x H4.
move=> eps H5.
elim (H4 eps).
move=> m H6.
exists (max (S n) m).
move=> k H7.
elim (classic ((An k) = (Bn k))).
move=> H8.
rewrite - H8.
apply (H6 k).
apply (le_trans m (Init.Nat.max (S n) m) k).
apply (Nat.le_max_r (S n) m).
apply H7.
move=> H8.
apply False_ind.
apply (le_not_gt (Init.Nat.max (S n) m) k H7).
apply (le_trans (S k) (S n) (Init.Nat.max (S n) m)).
apply (le_n_S k n).
apply (proj2 H3 k).
apply H8.
apply (Nat.le_max_l (S n) m).
apply H5.
apply H2.
move=> H2 x H3.
move=> eps H4.
elim (H3 eps).
move=> n H5.
exists n.
move=> n0 H6.
suff: (An n0) = (Bn n0).
move=> H7.
rewrite - H7.
apply (H5 n0 H6).
apply (NNPP (An n0 = Bn n0)).
move=> H7.
apply H2.
apply (Inhabited_intro nat (fun n1 : nat => An n1 <> Bn n1) n0 H7).
apply H4.
Qed.

Lemma Proposition_2_3 : forall (An : nat -> R),forall (x y: R), (Un_cv An x) -> (Un_cv An y) -> x = y.
Proof.
move=> An x y H1 H2.
elim (total_order_T (R_dist x y) 0).
elim.
move=> H3.
apply False_ind.
apply (Rlt_not_ge (R_dist x y) 0).
apply H3.
apply (R_dist_pos x y).
apply (proj1 (R_dist_refl x y)).
move=> H3.
apply False_ind.
elim (H1 ((R_dist x y) * / 2)).
move=> n1 H4.
elim (H2 ((R_dist x y) * / 2)).
move=> n2 H5.
apply (Rlt_irrefl (R_dist x y)).
rewrite - {2}(eps2 (R_dist x y)).
apply (Rle_lt_trans (R_dist x y) ((R_dist (An (Init.Nat.max n1 n2)) x) + (R_dist (An (Init.Nat.max n1 n2)) y)) (R_dist x y * / 2 + R_dist x y * / 2)).
rewrite (R_dist_sym (An (Init.Nat.max n1 n2)) x).
apply (R_dist_tri x y (An (Init.Nat.max n1 n2))).
apply (Rplus_lt_compat (R_dist (An (Init.Nat.max n1 n2)) x) (R_dist x y * / 2) (R_dist (An (Init.Nat.max n1 n2)) y) (R_dist x y * / 2)).
apply H4.
apply (Nat.le_max_l n1 n2).
apply H5.
apply (Nat.le_max_r n1 n2).
apply (eps2_Rgt_R0 (R_dist x y) H3).
apply (eps2_Rgt_R0 (R_dist x y) H3).
Qed.

Lemma Proposition_2_4 : forall (An : nat -> R), (exists (x : R), (Un_cv An x)) -> (my_bounded (fun x => exists (n : nat), (An n) = x)).
Proof.
move=> An H1.
elim H1.
move=> a H2.
elim (H2 1).
move=> n H3.
suff: (Finite R (fun x => exists (n0 : nat), (An n0) = x /\ (n0 <= n)%nat)).
move=> H4.
apply conj.
elim (Finite_max_R (fun x : R => exists n0 : nat, An n0 = x /\ (n0 <= n)%nat) H4).
move=> ma H5.
exists (Rmax ma (a + 1)).
move=> x H6.
elim H6.
move=> nx H7.
elim (le_or_lt n nx).
move=> H8.
apply (Rle_trans x (a + 1) (Rmax ma (a + 1))).
rewrite (Rplus_comm a 1).
rewrite - (Rplus_0_r x).
rewrite - (Rplus_opp_l a).
rewrite - (Rplus_assoc x (- a) a).
apply (Rplus_le_compat_r a (x + - a) 1).
rewrite - H7.
apply (Rlt_le (An nx + - a) 1).
apply (Rle_lt_trans (An nx + - a) (Rabs (An nx + - a)) 1).
apply (Rle_abs (An nx + - a)).
apply (H3 nx).
apply H8.
apply (Rmax_r ma (a + 1)).
move=> H8.
apply (Rle_trans x ma (Rmax ma (a + 1))).
apply ((proj2 H5) x).
exists nx.
apply conj.
apply H7.
apply (le_Sn_le nx n H8).
apply (Rmax_l ma (a + 1)).
exists (An n).
exists n.
apply conj.
by [].
by [].
elim (Finite_min_R (fun x : R => exists n0 : nat, An n0 = x /\ (n0 <= n)%nat) H4).
move=> mi H5.
exists (Rmin mi (a - 1)).
move=> x H6.
elim H6.
move=> nx H7.
elim (le_or_lt n nx).
move=> H8.
apply (Rge_trans x (a - 1) (Rmin mi (a - 1))).
rewrite /Rminus.
rewrite (Rplus_comm a (- 1)).
rewrite - (Rplus_0_r x).
rewrite - (Rplus_opp_l a).
rewrite - (Rplus_assoc x (- a) a).
apply (Rplus_ge_compat_r a (x + - a) (- 1)).
rewrite - H7.
apply (Rgt_ge (An nx + - a) (- 1)).
apply (Ropp_gt_cancel (An nx + - a) (- 1)).
rewrite (Ropp_involutive 1).
apply (Rgt_ge_trans 1 (Rabs (- (An nx + - a))) (- (An nx + - a))).
rewrite (Rabs_Ropp (An nx + - a)).
apply (H3 nx H8).
apply (Rle_ge (- (An nx + - a)) (Rabs (- (An nx + - a)))).
apply (Rle_abs (-(An nx + - a))).
apply (Rle_ge (Rmin mi (a - 1)) (a - 1)).
apply (Rmin_r mi (a - 1)).
move=> H8.
apply (Rge_trans x mi (Rmin mi (a - 1))).
apply ((proj2 H5) x).
exists nx.
apply conj.
apply H7.
apply (le_Sn_le nx n H8).
apply (Rle_ge (Rmin mi (a - 1)) mi).
apply (Rmin_l mi (a - 1)).
exists (An n).
exists n.
apply conj.
by [].
by [].
suff: (fun x : R => exists n0 : nat, An n0 = x /\ (n0 <= n)%nat) = (Image.Im nat R (fun x : nat => (x <= n)%nat) An).
move=> H4.
rewrite H4.
apply (finite_image nat R (fun x : nat => (x <= n)%nat) An).
suff: (fun x : nat => (x <= n)%nat) = (fun x : nat => (x < (S n))%nat).
move=> H5.
rewrite H5.
apply (cardinal_finite nat (fun x : nat => (x < S n)%nat) (S n)).
apply (nat_cardinal (S n)).
apply (Extensionality_Ensembles nat (fun x : nat => (x <= n)%nat) (fun x : nat => (x < S n)%nat)).
apply conj.
move=> m.
apply (le_n_S m n).
move=> m.
apply (le_S_n m n).
apply (Extensionality_Ensembles R (fun x : R => exists n0 : nat, An n0 = x /\ (n0 <= n)%nat) (Im nat R (fun x : nat => (x <= n)%nat) An)).
apply conj.
move=> x.
elim.
move=> n0 H4.
apply (Im_intro nat R (fun x : nat => (x <= n)%nat) An n0).
apply (proj2 H4).
rewrite (proj1 H4).
by [].
move=> n0.
elim.
move=> n1 H4.
move=> x H5.
exists n1.
apply conj.
rewrite H5.
by [].
apply H4.
apply (Rlt_0_1).
Qed.

Lemma Same_Sequence_cv : forall (An Bn : nat -> R), (forall (n : nat), (An n) = (Bn n)) -> forall (x : R), (Un_cv An x) <-> (Un_cv Bn x).
Proof.
move=> An Bn H1 x.
apply conj.
move=> H2.
move=> eps H3.
elim (H2 eps).
move=> n H4.
exists n.
move=> n0 H5.
rewrite - (H1 n0).
apply (H4 n0 H5).
apply H3.
move=> H2.
move=> eps H3.
elim (H2 eps).
move=> n H4.
exists n.
move=> n0 H5.
rewrite (H1 n0).
apply (H4 n0 H5).
apply H3.
Qed.

Lemma Theorem_2_5_1_plus : forall (An Bn : nat -> R) (x y : R), (Un_cv An x) -> (Un_cv Bn y) -> (Un_cv (RSequencePlus An Bn) (x + y)).
Proof.
move=> An Bn x y H1 H2.
move=> eps H3.
elim (H1 (eps * / 2)).
move=> n1 H4.
elim (H2 (eps * / 2)).
move=> n2 H5.
exists (Nat.max n1 n2).
move=> n H6.
rewrite /RSequencePlus.
rewrite /R_dist.
rewrite /Rminus.
rewrite (Ropp_plus_distr x y).
rewrite - (Rplus_assoc (An n + Bn n) (- x) (- y)).
rewrite (Rplus_assoc (An n) (Bn n) (- x)).
rewrite (Rplus_comm (Bn n) (- x)).
rewrite - (Rplus_assoc (An n) (- x) (Bn n)).
rewrite (Rplus_assoc (An n + - x) (Bn n) (- y)).
apply (Rle_lt_trans (Rabs (An n + - x + (Bn n + - y))) (Rabs (An n + - x) + Rabs (Bn n + - y)) eps).
apply (Rabs_triang (An n + - x) (Bn n + - y)).
rewrite - (eps2 eps).
apply (Rplus_lt_compat (Rabs (An n + - x)) (eps * / 2) (Rabs (Bn n + - y)) (eps * / 2)).
apply (H4 n).
apply (le_trans n1 (Nat.max n1 n2) n).
apply (Nat.le_max_l n1 n2).
apply H6.
apply (H5 n).
apply (le_trans n2 (Nat.max n1 n2) n).
apply (Nat.le_max_r n1 n2).
apply H6.
apply (eps2_Rgt_R0 eps H3).
apply (eps2_Rgt_R0 eps H3).
Qed.

Lemma Theorem_2_5_1_opp : forall (An : nat -> R) (x : R), (Un_cv An x) -> (Un_cv (RSequenceOpp An) (- x)).
Proof.
move=> An x H1.
move=> eps H3.
elim (H1 eps).
move=> n H4.
exists n.
move=> n0 H5.
rewrite /RSequenceOpp.
rewrite /R_dist.
rewrite /Rminus.
rewrite - (Ropp_plus_distr (An n0) (- x)).
rewrite (Rabs_Ropp (An n0 + - x)).
apply (H4 n0).
apply H5.
apply H3.
Qed.

Lemma Theorem_2_5_1_minus : forall (An Bn : nat -> R) (x y : R), (Un_cv An x) -> (Un_cv Bn y) -> (Un_cv (RSequenceMinus An Bn) (x - y)).
Proof.
move=> An Bn x y H1 H2.
suff: forall n : nat, ((RSequenceMinus An Bn) n) = ((RSequencePlus An (RSequenceOpp Bn)) n).
move=> H3.
suff: Un_cv ((RSequencePlus An (RSequenceOpp Bn))) (x - y).
apply (proj2 (Same_Sequence_cv (RSequenceMinus An Bn) (RSequencePlus An (RSequenceOpp Bn)) H3 (x - y))).
suff: Un_cv (RSequenceOpp Bn) (- y).
apply (Theorem_2_5_1_plus An (RSequenceOpp Bn) x (- y) H1).
apply (Theorem_2_5_1_opp Bn y H2).
move=> n0.
by [].
Qed.

Lemma Theorem_2_5_1_mult : forall (An Bn : nat -> R) (x y : R), (Un_cv An x) -> (Un_cv Bn y) -> (Un_cv (RSequenceMult An Bn) (x * y)).
Proof.
move=> An Bn a b H1 H2.
elim ((proj1 (bounded_abs (fun x => exists (n : nat), (Bn n) = x)))).
move=> ma H3.
move=> eps H4.
elim (H1 (eps * / 2 * / (ma + 1))).
move=> n1 H5.
elim (H2 (eps * / 2 * / ((Rabs a) + 1))).
move=> n2 H6.
exists (Nat.max n1 n2).
move=> n H7.
rewrite /RSequenceMult.
rewrite /R_dist.
rewrite - (Rplus_0_r (An n * Bn n - a * b)).
rewrite - (Rplus_opp_l (a * (Bn n))).
rewrite - (Rplus_assoc (An n * Bn n - a * b) (- (a * Bn n)) (a * Bn n)).
rewrite (Rplus_assoc (An n * Bn n) (- (a * b)) (- (a * Bn n))).
rewrite (Rplus_comm (- (a * b)) (- (a * Bn n))).
rewrite - (Rplus_assoc (An n * Bn n) (- (a * Bn n)) (- (a * b))).
rewrite (Rplus_assoc (An n * Bn n + - (a * Bn n)) (- (a * b)) (a * Bn n)).
apply (Rle_lt_trans (Rabs (An n * Bn n + - (a * Bn n) + (- (a * b) + a * Bn n))) (Rabs (An n * Bn n + - (a * Bn n)) + Rabs (- (a * b) + a * Bn n)) eps).
apply (Rabs_triang (An n * Bn n + - (a * Bn n)) (- (a * b) + a * Bn n)).
rewrite - (eps2 eps).
apply (Rplus_lt_compat (Rabs (An n * Bn n + - (a * Bn n))) (eps * / 2) (Rabs (- (a * b) + a * Bn n)) (eps * / 2)).
rewrite (Ropp_mult_distr_l a (Bn n)).
rewrite - (Rmult_plus_distr_r (An n) (- a) (Bn n)).
rewrite (Rabs_mult (An n + - a) (Bn n)).
apply (Rle_lt_trans (Rabs (An n + - a) * Rabs (Bn n)) (Rabs (An n + - a) * (ma + 1)) (eps * / 2)).
apply (Rmult_le_compat_l (Rabs (An n + - a)) (Rabs (Bn n)) (ma + 1)).
apply (Rabs_pos (An n + - a)).
apply (Rle_trans (Rabs (Bn n)) ma (ma + 1)).
apply (H3 (Rabs (Bn n))).
exists (Bn n).
exists n.
by [].
by [].
apply (Rlt_le ma (ma + 1)).
apply (Rlt_plus_1 ma).
apply (Rmult_lt_reg_r (/ (ma + 1)) (Rabs (An n + - a) * (ma + 1)) (eps * / 2)).
apply (Rinv_0_lt_compat (ma + 1)).
apply (Rle_lt_trans 0 ma (ma + 1)).
apply (Rle_trans 0 (Rabs (Bn O)) ma).
apply (Rabs_pos (Bn O)).
apply (H3 (Rabs (Bn O))).
exists (Bn O).
exists O.
by [].
by [].
apply (Rlt_plus_1 ma).
rewrite (Rmult_assoc (Rabs (An n + - a)) (ma + 1) (/ (ma + 1))).
rewrite (Rinv_r (ma + 1)).
rewrite (Rmult_1_r (Rabs (An n + - a))).
apply (H5 n).
apply (le_trans n1 (Nat.max n1 n2) n).
apply (Nat.le_max_l n1 n2).
apply H7.
apply (Rgt_not_eq (ma + 1) 0).
apply (Rle_lt_trans 0 ma (ma + 1)).
apply (Rle_trans 0 (Rabs (Bn O)) ma).
apply (Rabs_pos (Bn O)).
apply (H3 (Rabs (Bn O))).
exists (Bn O).
exists O.
by [].
by [].
apply (Rlt_plus_1 ma).
rewrite (Ropp_mult_distr_r a b).
rewrite - (Rmult_plus_distr_l a (- b) (Bn n)).
rewrite (Rmult_comm a (- b + Bn n)).
rewrite (Rabs_mult (- b + Bn n) a).
apply (Rle_lt_trans (Rabs (- b + Bn n) * Rabs a) (Rabs (- b + Bn n) * (Rabs a + 1)) (eps * / 2)).
apply (Rmult_le_compat_l (Rabs (- b + Bn n)) (Rabs a) (Rabs a + 1)).
apply (Rabs_pos (- b + Bn n)).
apply (Rlt_le (Rabs a) (Rabs a + 1)).
apply (Rlt_plus_1 (Rabs a)).
rewrite (Rplus_comm (- b) (Bn n)).
apply (Rmult_lt_reg_r (/ (Rabs a + 1)) (Rabs (Bn n + - b) * (Rabs a + 1)) (eps * / 2)).
apply (Rinv_0_lt_compat (Rabs a + 1)).
apply (Rle_lt_trans 0 (Rabs a) (Rabs a + 1)).
apply (Rabs_pos a).
apply (Rlt_plus_1 (Rabs a)).
rewrite (Rmult_assoc (Rabs (Bn n + - b)) (Rabs a + 1) (/ (Rabs a + 1))).
rewrite (Rinv_r (Rabs a + 1)).
rewrite (Rmult_1_r (Rabs (Bn n + - b))).
apply (H6 n).
apply (le_trans n2 (Nat.max n1 n2) n).
apply (Nat.le_max_r n1 n2).
apply H7.
apply (Rgt_not_eq (Rabs a + 1) 0).
apply (Rle_lt_trans 0 (Rabs a) (Rabs a + 1)).
apply (Rabs_pos a).
apply (Rlt_plus_1 (Rabs a)).
apply (Rmult_gt_0_compat (eps * / 2) (/ (Rabs a + 1))).
apply (eps2_Rgt_R0 eps H4).
apply (Rinv_0_lt_compat (Rabs a + 1)).
apply (Rle_lt_trans 0 (Rabs a) (Rabs a + 1)).
apply (Rabs_pos a).
apply (Rlt_plus_1 (Rabs a)).
apply (Rmult_gt_0_compat (eps * / 2) (/ (ma + 1))).
apply (eps2_Rgt_R0 eps H4).
apply (Rinv_0_lt_compat (ma + 1)).
apply (Rle_lt_trans 0 ma (ma + 1)).
apply (Rle_trans 0 (Rabs (Bn O)) ma).
apply (Rabs_pos (Bn O)).
apply (H3 (Rabs (Bn O))).
exists (Bn O).
exists O.
by [].
by [].
apply (Rlt_plus_1 ma).
apply (Proposition_2_4 Bn).
exists b.
apply H2.
Qed.

Lemma Theorem_2_5_1_inv : forall (An : nat -> R) (x : R), (Un_cv An x) -> (x <> 0) -> (Un_cv (RSequenceInv An) (1 / x)).
Proof.
move=> An a H1 H2.
elim (H1 ((Rabs a) * / 2)).
move=> n1 H3.
suff: forall (n : nat), (n >= n1)%nat -> Rabs (An n) > (Rabs a) * / 2.
move=> H4.
move=> eps H5.
elim (H1 ((Rabs a) * (Rabs a) * eps * / 2)).
move=> n2 H6.
exists (Nat.max n1 n2).
move=> n H7.
apply (Rle_lt_trans (R_dist (RSequenceInv An n) (1 / a)) (2 * (R_dist (An n) a) * / (Rabs a) * / (Rabs a)) eps).
rewrite {1}/R_dist.
rewrite /RSequenceInv.
rewrite /Rdiv.
rewrite (Rmult_1_l (/ An n)).
rewrite (Rmult_1_l (/ a)).
rewrite - (Rinv_r_simpl_m a (/ An n)).
rewrite - {2}(Rinv_r_simpl_r (An n) (/ a)).
rewrite (Rmult_assoc a (/ An n) (/ a)).
rewrite (Rmult_assoc (An n) (/ An n) (/ a)).
rewrite /Rminus.
rewrite (Ropp_mult_distr_l (An n) (/ An n * / a)).
rewrite - (Rmult_plus_distr_r a (- (An n)) (/ An n * / a)).
rewrite (Rabs_mult (a + - An n) (/ An n * / a)).
rewrite /R_dist.
rewrite (Rabs_minus_sym (An n) a).
rewrite /Rminus.
rewrite (Rmult_comm 2 (Rabs (a + - An n))).
rewrite (Rmult_assoc (Rabs (a + - An n)) 2 (/ Rabs a)).
rewrite (Rmult_assoc (Rabs (a + - An n)) (2 * / Rabs a) (/ Rabs a)).
apply (Rmult_le_compat_l (Rabs (a + - An n)) (Rabs (/ An n * / a)) (2 * / Rabs a * / Rabs a)).
apply (Rabs_pos (a + - An n)).
rewrite (Rabs_mult (/ An n) (/ a)).
rewrite (Rabs_Rinv a).
apply (Rmult_le_compat_r (/ Rabs a) (Rabs (/ An n)) (2 * / Rabs a)).
apply (Rlt_le 0 (/ Rabs a)).
apply (Rinv_0_lt_compat (Rabs a)).
apply (Rabs_pos_lt a H2).
rewrite (Rabs_Rinv (An n)).
apply (Rlt_le (/ Rabs (An n)) (2 * / Rabs a)).
rewrite - (Rinv_involutive 2).
rewrite - (Rinv_mult_distr (/ 2) (Rabs a)).
apply (Rinv_lt_contravar (/ 2 * Rabs a) (Rabs (An n))).
apply (Rmult_lt_0_compat (/ 2 * Rabs a) (Rabs (An n))).
apply (Rmult_lt_0_compat (/ 2) (Rabs a)).
apply (Rinv_0_lt_compat 2).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rabs_pos_lt a H2).
apply (Rlt_trans 0 (Rabs a * / 2) (Rabs (An n))).
apply (eps2_Rgt_R0 (Rabs a)).
apply (Rabs_pos_lt a H2).
apply (H4 n).
apply (le_trans n1 (Nat.max n1 n2) n).
apply (Nat.le_max_l n1 n2).
apply H7.
rewrite (Rmult_comm (/ 2) (Rabs a)).
apply (H4 n).
apply (le_trans n1 (Nat.max n1 n2) n).
apply (Nat.le_max_l n1 n2).
apply H7.
apply (Rgt_not_eq (/ 2) 0).
apply (Rinv_0_lt_compat 2).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rgt_not_eq (Rabs a) 0).
apply (Rabs_pos_lt a H2).
apply (Rgt_not_eq 2 0).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
move=> H8.
apply (Rgt_not_le (Rabs (An n)) (Rabs a * / 2)).
apply (H4 n).
apply (le_trans n1 (Nat.max n1 n2) n).
apply (Nat.le_max_l n1 n2).
apply H7.
rewrite H8.
rewrite Rabs_R0.
apply (Rlt_le 0 (Rabs a * / 2)).
apply (eps2_Rgt_R0 (Rabs a)).
apply (Rabs_pos_lt a H2).
apply H2.
move=> H8.
apply (Rgt_not_le (Rabs (An n)) (Rabs a * / 2)).
apply (H4 n).
apply (le_trans n1 (Nat.max n1 n2) n).
apply (Nat.le_max_l n1 n2).
apply H7.
rewrite H8.
rewrite Rabs_R0.
apply (Rlt_le 0 (Rabs a * / 2)).
apply (eps2_Rgt_R0 (Rabs a)).
apply (Rabs_pos_lt a H2).
apply H2.
rewrite - (Rmult_1_r eps).
rewrite - (Rinv_r (Rabs a)).
rewrite - (Rmult_assoc eps (Rabs a) (/ Rabs a)).
apply (Rmult_lt_compat_r (/ Rabs a) (2 * R_dist (An n) a * / Rabs a) (eps * Rabs a)).
apply (Rinv_0_lt_compat (Rabs a)).
apply (Rabs_pos_lt a H2).
rewrite - (Rmult_1_r (eps * Rabs a)).
rewrite - (Rinv_r (Rabs a)).
rewrite - (Rmult_assoc (eps * Rabs a) (Rabs a) (/ Rabs a)).
apply (Rmult_lt_compat_r (/ Rabs a) (2 * R_dist (An n) a) (eps * Rabs a * Rabs a)).
apply (Rinv_0_lt_compat (Rabs a)).
apply (Rabs_pos_lt a H2).
rewrite - (Rmult_1_l eps).
rewrite - (Rinv_r 2).
rewrite (Rmult_assoc (2 * / 2 * eps) (Rabs a) (Rabs a)).
rewrite (Rmult_assoc (2 * / 2) (eps) (Rabs a * Rabs a)).
rewrite (Rmult_assoc 2 (/ 2) (eps * (Rabs a * Rabs a))).
apply (Rmult_lt_compat_l 2 (R_dist (An n) a) (/ 2 * (eps * (Rabs a * Rabs a)))).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
rewrite (Rmult_comm (/ 2) (eps * (Rabs a * Rabs a))).
rewrite (Rmult_comm eps (Rabs a * Rabs a)).
apply (H6 n).
apply (le_trans n2 (Nat.max n1 n2) n).
apply (Nat.le_max_r n1 n2).
apply H7.
apply (Rgt_not_eq 2 0).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rgt_not_eq (Rabs a) 0).
apply (Rabs_pos_lt a H2).
apply (Rgt_not_eq (Rabs a) 0).
apply (Rabs_pos_lt a H2).
apply (Rmult_gt_0_compat (Rabs a * Rabs a * eps) (/ 2)).
apply (Rmult_gt_0_compat (Rabs a * Rabs a) eps).
apply (Rmult_gt_0_compat (Rabs a) (Rabs a)).
apply (Rabs_pos_lt a H2).
apply (Rabs_pos_lt a H2).
apply H5.
apply (Rinv_0_lt_compat 2).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
move=> n H4.
apply (Rplus_gt_reg_l (Rabs a * / 2) (Rabs (An n)) (Rabs a * / 2)).
rewrite (eps2 (Rabs a)).
apply (Rplus_lt_reg_r (- Rabs (An n)) (Rabs a) (Rabs a * / 2 + Rabs (An n))).
rewrite (Rplus_assoc (Rabs a * / 2) (Rabs (An n)) (- Rabs (An n))).
rewrite (Rplus_opp_r (Rabs (An n))).
rewrite (Rplus_0_r (Rabs a * / 2)).
apply (Rle_lt_trans (Rabs a + - Rabs (An n)) (Rabs (a + - (An n))) (Rabs a * / 2)).
apply (Rabs_triang_inv a (An n)).
rewrite (Rabs_minus_sym a (An n)).
apply (H3 n).
apply H4.
apply (eps2_Rgt_R0 (Rabs a)).
apply (Rabs_pos_lt a H2).
Qed.

Lemma Theorem_2_5_1_div : forall (An Bn : nat -> R) (x y : R), (Un_cv An x) -> (Un_cv Bn y) -> (y <> 0) -> (Un_cv (RSequenceDiv An Bn) (x / y)).
Proof.
move=> An Bn x y H1 H2 H3.
suff: Un_cv (RSequenceMult An (RSequenceInv Bn)) (x / y).
apply (Same_Sequence_cv (RSequenceMult An (RSequenceInv Bn)) (RSequenceDiv An Bn)).
move=> n.
rewrite /RSequenceInv.
rewrite /RSequenceMult.
rewrite /RSequenceDiv.
rewrite /Rdiv.
rewrite (Rmult_1_l (/ Bn n)).
by [].
rewrite /Rdiv.
rewrite - (Rmult_1_l (/ y)).
suff: Un_cv (RSequenceInv Bn) (1 * / y).
apply (Theorem_2_5_1_mult An (RSequenceInv Bn) x (1 * / y) H1).
apply (Theorem_2_5_1_inv Bn y H2 H3).
Qed.

Lemma Theorem_2_6 : forall (An Bn : nat -> R) (x y : R), (Un_cv An x) -> (Un_cv Bn y) -> (forall n : nat, (An n) <= (Bn n)) -> x <= y.
Proof.
move=> An Bn a b H1 H2 H3.
apply (Rnot_gt_le a b).
move=> H4.
elim (H1 ((a-b) * / 2)).
move=> n1 H5.
elim (H2 ((a-b) * / 2)).
move=> n2 H6.
apply (Rle_not_lt (Bn (Nat.max n1 n2)) (An (Nat.max n1 n2)) (H3 (Nat.max n1 n2))).
apply (Rlt_trans (Bn (Nat.max n1 n2)) ((a + b) * / 2) (An (Nat.max n1 n2))).
apply (Rplus_lt_reg_r (- b) (Bn (Nat.max n1 n2)) ((a + b) * / 2)).
rewrite - {2}(eps2 (- b)).
rewrite - (Rdiv_plus_distr (- b) (- b) 2).
rewrite - (Rdiv_plus_distr (a + b) (- b + - b) 2).
rewrite (Rplus_assoc a b (- b + - b)).
rewrite - (Rplus_assoc b (- b) (- b)).
rewrite (Rplus_opp_r b).
rewrite (Rplus_0_l (- b)).
apply (Rle_lt_trans (Bn (Nat.max n1 n2) + - b) (Rabs (Bn (Nat.max n1 n2) + - b)) ((a + - b) / 2)).
apply (Rle_abs (Bn (Nat.max n1 n2) + - b)).
apply (H6 (Nat.max n1 n2)).
apply (Nat.le_max_r n1 n2).
apply (Rplus_lt_reg_l (- a) ((a + b) * / 2) (An (Nat.max n1 n2))).
rewrite - {1}(eps2 (- a)).
rewrite - (Rdiv_plus_distr (- a) (- a) 2).
rewrite - (Rdiv_plus_distr (- a + - a) (a + b) 2).
rewrite (Rplus_assoc (- a) (- a) (a + b)).
rewrite - (Rplus_assoc (- a) a b).
rewrite (Rplus_opp_l a).
rewrite (Rplus_0_l b).
apply (Ropp_lt_cancel ((- a + b) / 2) (- a + An (Nat.max n1 n2))).
apply (Rle_lt_trans (- (- a + An (Nat.max n1 n2))) (Rabs (- (- a + An (Nat.max n1 n2)))) (- ((- a + b) / 2))).
apply (Rle_abs (- (- a + An (Nat.max n1 n2)))).
rewrite (Rabs_Ropp (- a + An (Nat.max n1 n2))).
rewrite (Rplus_comm (- a) (An (Nat.max n1 n2))).
rewrite (Ropp_mult_distr_l (- a + b) (/ 2)).
rewrite (Ropp_plus_distr (- a) b).
rewrite (Ropp_involutive a).
apply (H5 (Nat.max n1 n2)).
apply (Nat.le_max_l n1 n2).
apply (eps2_Rgt_R0 (a - b)).
apply (Rgt_minus a b H4).
apply (eps2_Rgt_R0 (a - b)).
apply (Rgt_minus a b H4).
Qed.

Lemma Theorem_2_6_2 : forall (An Bn : nat -> R) (x y : R), (Un_cv An x) -> (Un_cv Bn y) -> (exists (N : nat), forall n : nat, (n >= N)%nat -> (An n) <= (Bn n)) -> x <= y.
Proof.
move=> An Bn a b H1 H2.
elim.
move=> N H3.
suff: (Un_cv (fun (n : nat) => Bn (n + N)%nat) b).
suff: (Un_cv (fun (n : nat) => An (n + N)%nat) a).
move=> H4 H5.
apply (Theorem_2_6 (fun (n : nat) => An (n + N)%nat) (fun (n : nat) => Bn (n + N)%nat) a b H4 H5).
move=> n.
apply (H3 (n + N)%nat).
rewrite - {2} (plus_0_l N).
apply (plus_le_compat_r 0 n N).
apply (le_0_n n).
move=> eps H4.
elim (H1 eps H4).
move=> M H5.
exists M.
move=> n H6.
apply (H5 (n + N)%nat).
apply (le_trans M n (n + N)%nat).
apply H6.
rewrite - {1} (plus_0_r n).
apply (plus_le_compat_l 0 N n).
apply (le_0_n N).
move=> eps H4.
elim (H2 eps H4).
move=> M H5.
exists M.
move=> n H6.
apply (H5 (n + N)%nat).
apply (le_trans M n (n + N)%nat).
apply H6.
rewrite - {1} (plus_0_r n).
apply (plus_le_compat_l 0 N n).
apply (le_0_n N).
Qed.

Lemma ConstSequence_Cv : forall (x : R), (Un_cv (fun n : nat => x) x).
Proof.
move=> x.
move=> eps H1.
exists O.
move=> n H2.
rewrite (proj2 (R_dist_refl x x)).
apply H1.
by [].
Qed.

Lemma Theorem_2_6_Collorary_1 : forall (An : nat -> R) (a b : R), (Un_cv An a) -> (forall n : nat, (An n) <= b) -> a <= b.
Proof.
move=> An a b H1 H2.
apply (Theorem_2_6 An (fun n : nat => b) a b).
apply H1.
apply (ConstSequence_Cv b).
apply H2.
Qed.

Lemma Theorem_2_6_Collorary_2 : forall (An : nat -> R) (a b : R), (Un_cv An a) -> (forall n : nat, b <= (An n)) -> b <= a.
Proof.
move=> An a b H1 H2.
apply (Theorem_2_6 (fun n : nat => b) An b a).
apply (ConstSequence_Cv b).
apply H1.
apply H2.
Qed.

Lemma Proposition_2_7 : forall (An Bn: nat -> R) (x : R), (Un_cv An x) -> (Un_cv Bn x) -> (forall (Cn : nat -> R), (forall n : nat, (An n) <= (Cn n) <= (Bn n)) -> (Un_cv Cn x)).
Proof.
move=> An Bn x H1 H2 Cn H3.
move=> eps H4.
elim (H1 eps).
move=> n1 H5.
elim (H2 eps).
move=> n2 H6.
exists (Nat.max n1 n2).
move=> n H7.
apply (Rabs_def1 ((Cn n) - x) eps).
apply (Rle_lt_trans (Cn n - x) (Bn n - x) eps).
apply (Rplus_le_compat_r (- x) (Cn n) (Bn n)).
apply (proj2 (H3 n)).
apply (Rle_lt_trans (Bn n - x) (Rabs (Bn n - x)) eps).
apply (Rle_abs (Bn n - x)).
apply (H6 n).
apply (le_trans n2 (Nat.max n1 n2) n).
apply (Nat.le_max_r n1 n2).
apply H7.
apply (Rlt_le_trans (- eps) (An n - x) (Cn n - x)).
apply (Ropp_lt_cancel (- eps) (An n - x)).
rewrite (Ropp_involutive eps).
apply (Rle_lt_trans (- (An n - x)) (Rabs (An n - x)) eps).
rewrite - (Rabs_Ropp (An n - x)).
apply (Rle_abs (- (An n - x))).
apply (H5 n).
apply (le_trans n1 (Nat.max n1 n2) n).
apply (Nat.le_max_l n1 n2).
apply H7.
apply (Rplus_le_compat_r (- x) (An n) (Cn n)).
apply (proj1 (H3 n)).
apply H4.
apply H4.
Qed.

Lemma Proposition_2_7_2 : forall (An Bn: nat -> R) (x : R), (Un_cv An x) -> (Un_cv Bn x) -> (forall (Cn : nat -> R), (exists (N : nat), forall n : nat, (n >= N)%nat -> (An n) <= (Cn n) <= (Bn n)) -> (Un_cv Cn x)).
Proof.
move=> An Bn x H1 H2 Cn.
elim.
move=> N H3.
suff: (Un_cv (fun (n : nat) => Cn (n + N)%nat) x).
move=> H4 eps H5.
elim (H4 eps H5).
move=> M H6.
exists (M + N)%nat.
move=> n H7.
suff: (n = (n - N) + N)%nat.
move=> H8.
rewrite H8.
apply (H6 (n - N)%nat).
apply (plus_le_reg_l M (n - N) N)%nat.
rewrite (plus_comm N M).
rewrite - (le_plus_minus N n).
apply H7.
apply (le_trans N (M + N) n)%nat.
rewrite - {1} (plus_0_l N).
apply (plus_le_compat_r 0 M N (le_0_n M)).
apply H7.
rewrite (plus_comm (n - N) N)%nat.
rewrite - (le_plus_minus N n).
reflexivity.
apply (le_trans N (M + N) n)%nat.
rewrite - {1} (plus_0_l N).
apply (plus_le_compat_r 0 M N (le_0_n M)).
apply H7.
apply (Proposition_2_7 (fun n : nat => An (n + N)%nat) (fun n : nat => Bn (n + N)%nat) x).
move=> eps H4.
elim (H1 eps H4).
move=> M H5.
exists M.
move=> n H6.
apply (H5 (n + N)%nat).
apply (le_trans M n (n + N)%nat).
apply H6.
rewrite - {1} (plus_0_r n).
apply (plus_le_compat_l 0 N n).
apply (le_0_n N).
move=> eps H4.
elim (H2 eps H4).
move=> M H5.
exists M.
move=> n H6.
apply (H5 (n + N)%nat).
apply (le_trans M n (n + N)%nat).
apply H6.
rewrite - {1} (plus_0_r n).
apply (plus_le_compat_l 0 N n).
apply (le_0_n N).
move=> n.
apply (H3 (n + N)%nat).
rewrite - {2} (plus_0_l N).
apply (plus_le_compat_r 0 n N).
apply (le_0_n n).
Qed.

Definition Un_shrinking : ((nat -> R) -> Prop) := fun Un : (nat -> R) => forall n:nat, Un n >= Un (S n).

Lemma shrinking_prop : forall (An : (nat -> R)) (n m:nat), (Un_shrinking An) -> (n >= m)%nat -> An m >= An n.
Proof.
move=> An n m H1.
elim.
apply (Req_le (An m) (An m)).
by [].
move=> n0 H2 H3.
apply (Rge_trans (An m) (An n0) (An (S n0))).
apply H3.
apply (H1 n0).
Qed.

Lemma Theorem_3_1_1 : forall (An : (nat -> R)), (my_upper_bounded (Image.Im nat R (Full_set nat) An)) -> (Un_growing An) -> exists (s : R), (Un_cv An s) /\ (is_least_upper_bound (Image.Im nat R (Full_set nat) An) s).
Proof.
move=> An H1 H2.
elim (My_completeness_of_upper (Im nat R (Full_set nat) An)).
move=> s H3.
exists s.
apply conj.
move=> eps H4.
elim (proj2 (proj2 (proj1 Proposition_1_3 (Im nat R (Full_set nat) An) s) H3) (s - eps)).
move=> y.
case.
elim.
move=> n0 H5.
move=> y0 H6 H7.
exists n0.
move=> n H8.
apply (Rabs_def1 ((An n) - s) eps).
apply (Rle_lt_trans (An n - s) 0 eps).
apply (Rle_minus (An n) s).
apply (proj1 H3 (An n)).
apply (Im_intro nat R (Full_set nat) An n).
by [].
by [].
apply H4.
apply (Rplus_lt_reg_r s (- eps) (An n - s)).
rewrite (Rplus_assoc (An n) (- s) s).
rewrite (Rplus_opp_l s).
rewrite (Rplus_0_r (An n)).
rewrite (Rplus_comm (- eps) s).
apply (Rlt_le_trans (s + - eps) y0 (An n)).
apply H7.
rewrite H6.
apply (Rge_le (An n) (An n0)).
apply (growing_prop An n n0 H2 H8).
apply (tech_Rgt_minus s eps H4).
apply H3.
apply conj.
exists (An O).
apply (Im_intro nat R (Full_set nat) An O).
by [].
by [].
apply H1.
Qed.

Lemma Theorem_3_1_2 : forall (An : (nat -> R)), (my_lower_bounded (Image.Im nat R (Full_set nat) An)) -> (Un_shrinking An) -> exists (s : R), (Un_cv An s) /\ (is_greatest_lower_bound (Image.Im nat R (Full_set nat) An) s).
Proof.
move=> An H1 H2.
elim (My_completeness_of_lower (Im nat R (Full_set nat) An)).
move=> s H3.
exists s.
apply conj.
move=> eps H4.
elim (proj2 (proj2 (proj2 Proposition_1_3 (Im nat R (Full_set nat) An) s) H3) (s + eps)).
move=> y.
case.
elim.
move=> n0 H5.
move=> y0 H6 H7.
exists n0.
move=> n H8.
apply (Rabs_def1 ((An n) - s) eps).
apply (Rplus_lt_reg_r s (An n - s) eps).
rewrite (Rplus_assoc (An n) (- s) s).
rewrite (Rplus_opp_l s).
rewrite (Rplus_0_r (An n)).
rewrite (Rplus_comm eps s).
apply (Rle_lt_trans (An n) y0 (s + eps)).
rewrite H6.
apply (Rge_le (An n0) (An n)).
apply (shrinking_prop An n n0 H2 H8).
apply H7.
apply (Rlt_le_trans (- eps) 0 (An n - s)).
apply (Ropp_lt_gt_0_contravar eps H4).
apply (Rge_le (An n - s) 0).
apply (Rge_minus (An n) s).
apply (proj1 H3 (An n)).
apply (Im_intro nat R (Full_set nat) An n).
by [].
by [].
rewrite - {2}(Rplus_0_r s).
apply (Rplus_gt_compat_l s eps 0 H4).
apply H3.
apply conj.
exists (An O).
apply (Im_intro nat R (Full_set nat) An O).
by [].
by [].
apply H1.
Qed.

Definition Un_inf : ((nat -> R) -> Prop) := fun Un : (nat -> R) => forall M:R, exists N : nat, (forall n:nat, (n >= N)%nat -> (Un n) > M).

Definition Un_minf : ((nat -> R) -> Prop) := fun Un : (nat -> R) => forall M:R, exists N : nat, (forall n:nat, (n >= N)%nat -> (Un n) < M).

Lemma Same_Sequence_inf : forall (An Bn : nat -> R), (forall (n : nat), (An n) = (Bn n)) -> (Un_inf An) <-> (Un_inf Bn).
Proof.
move=> An Bn H1.
apply conj.
move=> H2.
move=> M.
elim (H2 M).
move=> n0 H3.
exists n0.
move=> n H4.
rewrite - (H1 n).
apply (H3 n H4).
move=> H2.
move=> M.
elim (H2 M).
move=> n0 H3.
exists n0.
move=> n H4.
rewrite (H1 n).
apply (H3 n H4).
Qed.

Lemma Same_Sequence_minf : forall (An Bn : nat -> R), (forall (n : nat), (An n) = (Bn n)) -> (Un_minf An) <-> (Un_minf Bn).
Proof.
move=> An Bn H1.
apply conj.
move=> H2.
move=> M.
elim (H2 M).
move=> n0 H3.
exists n0.
move=> n H4.
rewrite - (H1 n).
apply (H3 n H4).
move=> H2.
move=> M.
elim (H2 M).
move=> n0 H3.
exists n0.
move=> n H4.
rewrite (H1 n).
apply (H3 n H4).
Qed.

Lemma le_Sequence_inf : forall (An Bn : nat -> R), (forall (n : nat), (An n) <= (Bn n)) -> (Un_inf An) -> (Un_inf Bn).
Proof.
move=> An Bn H1.
move=> H2.
move=> M.
elim (H2 M).
move=> n0 H3.
exists n0.
move=> n H4.
apply (Rge_gt_trans (Bn n) (An n) M).
apply (Rle_ge (An n) (Bn n)).
apply (H1 n).
apply (H3 n H4).
Qed.

Lemma ge_Sequence_minf : forall (An Bn : nat -> R), (forall (n : nat), (An n) >= (Bn n)) -> (Un_minf An) -> (Un_minf Bn).
Proof.
move=> An Bn H1.
move=> H2.
move=> M.
elim (H2 M).
move=> n0 H3.
exists n0.
move=> n H4.
apply (Rle_lt_trans (Bn n) (An n) M).
apply (Rge_le (An n) (Bn n)).
apply (H1 n).
apply (H3 n H4).
Qed.

Lemma Formula_3_4_1 : forall (An : (nat -> R)), (Un_growing An) -> (~ (my_upper_bounded (Image.Im nat R (Full_set nat) An))) -> (Un_inf An).
Proof.
move=> An H1 H2.
move=> M.
apply (NNPP (exists N : nat, forall n : nat, (n >= N)%nat -> An n > M)).
move=> H3.
apply H2.
exists M.
move=> x.
elim.
move=> n H4.
move=> y H5.
rewrite H5.
apply (Rnot_gt_le (An n) M).
move=> H6.
apply H3.
exists n.
move=> n0 H7.
apply (Rge_gt_trans (An n0) (An n) M).
apply (growing_prop An n0 n H1 H7).
apply H6.
Qed.

Lemma Formula_3_4_2 : forall (An : (nat -> R)), (Un_shrinking An) -> (~ (my_lower_bounded (Image.Im nat R (Full_set nat) An))) -> (Un_minf An).
Proof.
move=> An H1 H2.
move=> M.
apply (NNPP (exists N : nat, forall n : nat, (n >= N)%nat -> An n < M)).
move=> H3.
apply H2.
exists M.
move=> x.
elim.
move=> n H4.
move=> y H5.
rewrite H5.
apply (Rnot_lt_ge (An n) M).
move=> H6.
apply H3.
exists n.
move=> n0 H7.
apply (Rle_lt_trans (An n0) (An n) M).
apply (Rge_le (An n) (An n0)).
apply (shrinking_prop An n0 n H1 H7).
apply H6.
Qed.

Lemma Theorem_3_2 : forall (a b : R), (a > 0) -> (b > 0) -> exists (n : nat), (INR n) * a > b.
Proof.
move=> a b H1 H2.
apply (NNPP (exists n : nat, INR n * a > b)).
move=> H3.
elim (My_completeness_of_upper (fun x : R => (exists n : nat, INR n = x))).
move=> M H4.
elim ((proj2 (proj1 Proposition_1_3 (fun x : R => exists n : nat, INR n = x) M) H4)).
move=> H5 H6.
elim (H6 (M-1)).
move=> x.
case.
move=> H7 H8.
elim H7.
move=> n H9.
apply (Rlt_not_le (x+1) M).
rewrite - (Rplus_0_r M).
rewrite - (Rplus_opp_l 1).
rewrite - (Rplus_assoc M (- 1) 1).
apply (Rplus_lt_compat_r 1 (M-1) x H8).
apply (H5 (x+1)).
exists (1 + n)%nat.
rewrite (S_O_plus_INR n).
rewrite H9.
rewrite (Rplus_comm x 1).
by [].
rewrite - {2}(Rplus_0_r M).
apply (Rplus_lt_compat_l M (- 1) 0).
rewrite - Ropp_0.
apply (Ropp_gt_lt_contravar 1 0).
apply (Rlt_0_1).
apply conj.
apply (Inhabited_intro R (fun x : R => exists n : nat, INR n = x) 0).
exists O.
by [].
exists (b/a).
move=> x H4.
elim H4.
move=> n H5.
apply (Rnot_lt_le (b / a) x).
move=> H6.
apply H3.
exists n.
rewrite H5.
rewrite - (Rmult_1_r b).
rewrite - (Rinv_l a).
rewrite - (Rmult_assoc b (/ a) a).
apply (Rmult_lt_compat_r a (b * /a) x).
apply H1.
apply H6.
apply (Rgt_not_eq a 0).
apply H1.
Qed.

Lemma Formula_3_6 : forall (a : R), (a > 0) -> (Un_inf (fun n : nat => a * (INR n))).
Proof.
move=> a H1.
move=> M.
elim (Rgt_ge_dec M 0).
move=> H2.
elim (Theorem_3_2 a M H1 H2).
move=> n H3.
exists n.
move=> n0 H4.
rewrite (Rmult_comm a (INR n0)).
apply (Rge_gt_trans (INR n0 * a) (INR n * a) M).
apply (Rmult_ge_compat_r a (INR n0) (INR n)).
apply (Rgt_ge a 0 H1).
apply (Rle_ge (INR n) (INR n0)).
apply (le_INR n n0 H4).
apply H3.
move=> H2.
exists 1%nat.
move=> n H3.
apply (Rgt_ge_trans (a * INR n) 0 M).
apply (Rmult_gt_0_compat a (INR n)).
apply H1.
apply (lt_0_INR n H3).
apply H2.
Qed.

Lemma Formula_3_7 : (Un_inf (fun n : nat => (INR n))).
Proof.
suff: forall n : nat, 1 * INR n = INR n.
move=> H1.
apply (proj1 (Same_Sequence_inf (fun n : nat => 1*(INR n)) (fun n : nat => (INR n)) H1)).
apply (Formula_3_6 1).
apply (Rlt_0_1).
move=> n.
apply (Rmult_1_l (INR n)).
Qed.

Lemma Formula_3_8 : (Un_cv (fun n : nat => 1 / (INR n)) 0).
Proof.
move=> eps H1.
elim (Theorem_3_2 eps 1).
move=> n H2.
exists (max n 1).
move=> n0 H3.
rewrite /R_dist.
rewrite /Rabs.
elim (Rcase_abs (1 / INR n0 - 0)).
move=> H4.
apply False_ind.
apply (Rlt_not_le 0 (1 / INR n0 - 0) H4).
rewrite /Rminus.
rewrite (Ropp_0).
rewrite (Rplus_0_r (1 / INR n0)).
apply (Rlt_le 0 (1 / INR n0)).
apply (Rmult_lt_0_compat 1 (/ INR n0)).
apply Rlt_0_1.
apply (Rinv_0_lt_compat (INR n0)).
apply (lt_0_INR n0).
apply (le_trans 1 (Init.Nat.max n 1) n0).
apply (Nat.le_max_r n 1).
apply H3.
move=> H4.
rewrite /Rminus.
rewrite (Ropp_0).
rewrite (Rplus_0_r (1 / INR n0)).
apply (Rmult_lt_reg_r (INR n0) (1 / INR n0) eps).
apply (lt_0_INR n0).
apply (le_trans 1 (Init.Nat.max n 1) n0).
apply (Nat.le_max_r n 1).
apply H3.
rewrite (Rmult_assoc 1 (/ INR n0) (INR n0)).
rewrite (Rinv_l (INR n0)).
rewrite (Rmult_1_r 1).
apply (Rlt_le_trans 1 (INR n * eps) (eps * INR n0)).
apply H2.
rewrite (Rmult_comm (INR n) eps).
apply (Rmult_le_compat_l eps (INR n) (INR n0)).
apply (Rlt_le 0 eps).
apply H1.
apply (le_INR n n0).
apply (le_trans n (Init.Nat.max n 1) n0).
apply (Nat.le_max_l n 1).
apply H3.
apply (Rgt_not_eq (INR n0) 0).
apply (lt_0_INR n0).
apply (le_trans 1 (Init.Nat.max n 1) n0).
apply (Nat.le_max_r n 1).
apply H3.
apply H1.
apply (Rlt_0_1).
Qed.

Lemma Formula_3_9_1 : (Un_inf (fun n : nat => (pow 2 n))).
Proof.
apply (le_Sequence_inf (fun n : nat => INR n) (fun n : nat => 2 ^ n)).
elim.
simpl.
apply (Rlt_le 0 1).
apply (Rlt_0_1).
move=> n H1.
apply (Rle_trans (INR (S n)) (2 ^ n + 1) (2 ^ S n)).
rewrite (S_INR n).
apply (Rplus_le_compat_r 1 (INR n) (2 ^ n) H1).
simpl.
rewrite {2}/2.
rewrite - (INR_IPR 2).
simpl.
rewrite (Rmult_plus_distr_r 1 1 (2 ^ n)).
rewrite (Rmult_1_l (2 ^ n)).
apply (Rplus_le_compat_l (2 ^ n) 1 (2 ^ n)).
move: H1.
elim n.
move=> H1.
simpl.
apply (Req_le 1 1).
by [].
move=> n0 H2 H3.
apply (Rle_trans 1 (INR (S n0)) (2 ^ S n0)).
rewrite (S_INR n0).
rewrite - {1}(Rplus_0_l 1).
apply (Rplus_le_compat_r 1 0 (INR n0)).
apply (pos_INR n0).
apply H3.
apply (Formula_3_7).
Qed.

Lemma Formula_3_9_2 : (Un_cv (fun n : nat => 1 / (pow 2 n)) 0).
Proof.
move=> eps H1.
elim (Formula_3_9_1 (1 / eps)).
move=> n0 H2.
exists n0.
move=> n H3.
apply (Rabs_def1 (1 / 2 ^ n - 0) eps).
rewrite (Rminus_0_r (1 / 2 ^ n)).
apply (Rmult_lt_reg_r (2 ^ n) (1 / 2 ^ n) eps).
elim n.
apply (Rlt_0_1).
move=> n1.
move=> H4.
simpl.
rewrite {1}/2.
rewrite - (INR_IPR 2).
simpl.
rewrite (Rmult_plus_distr_r 1 1 (2 ^ n1)).
rewrite (Rmult_1_l (2 ^ n1)).
apply (Rplus_lt_0_compat (2 ^ n1) (2 ^ n1) H4 H4).
rewrite (Rmult_assoc 1 (/ 2 ^ n) (2 ^ n)).
rewrite (Rinv_l (2 ^ n)).
rewrite - {2}(Rinv_l eps).
rewrite - (Rmult_assoc 1 (/ eps) eps).
rewrite (Rmult_comm eps (2 ^ n)).
apply (Rmult_lt_compat_r eps (1 * / eps) (2 ^ n)).
apply H1.
apply (H2 n H3).
apply (Rgt_not_eq eps 0 H1).
apply (Rgt_not_eq (2 ^ n) 0).
elim n.
apply (Rlt_0_1).
move=> n1.
move=> H4.
simpl.
rewrite {1}/2.
rewrite - (INR_IPR 2).
simpl.
rewrite (Rmult_plus_distr_r 1 1 (2 ^ n1)).
rewrite (Rmult_1_l (2 ^ n1)).
apply (Rplus_lt_0_compat (2 ^ n1) (2 ^ n1) H4 H4).
rewrite (Rminus_0_r (1 / 2 ^ n)).
apply (Rlt_trans (- eps) 0 (1 / 2 ^ n)).
apply (Ropp_lt_gt_0_contravar eps H1).
rewrite /Rdiv.
rewrite (Rmult_1_l (/ 2 ^ n)).
apply (Rinv_0_lt_compat (2 ^ n)).
elim n.
apply (Rlt_0_1).
move=> n1.
move=> H4.
simpl.
rewrite {1}/2.
rewrite - (INR_IPR 2).
simpl.
rewrite (Rmult_plus_distr_r 1 1 (2 ^ n1)).
rewrite (Rmult_1_l (2 ^ n1)).
apply (Rplus_lt_0_compat (2 ^ n1) (2 ^ n1) H4 H4).
Qed.

Inductive BoundedClosedSection (LR : {lr : (R * R) | (fst lr) <= (snd lr)}): Ensemble R := BoundedClosedSection_intro : forall x:R, (fst (proj1_sig LR)) <= x -> x <= (snd (proj1_sig LR)) -> In R (BoundedClosedSection LR) x.

Definition BoundedClosedSectionSet := {X : Ensemble R | exists LR : {lr : R * R | (fst lr) <= (snd lr)}, X = (BoundedClosedSection LR)}.

Lemma shrinking_prop_ER : forall (IN : (nat -> (Ensemble R))) (n m : nat), (forall k : nat, Included R (IN (S k)) (IN k)) -> (n >= m)%nat -> Included R (IN n) (IN m).
Proof.
move=> IN n m.
move=> H1.
elim.
by [].
move=> n0 H2 H3.
move=> x H4.
apply (H3 x).
apply (H1 n0 x).
apply H4.
Qed.

Lemma BoundedClosedSectionUniqueExistsPair : forall (A : BoundedClosedSectionSet), exists! LR : {lr : R * R | (fst lr) <= (snd lr)}, (proj1_sig A) = (BoundedClosedSection LR).
Proof.
move=> A.
elim (proj2_sig A).
move=> x H1.
exists x.
apply conj.
apply H1.
move=> y.
move=> H2.
apply (sig_map (fun lr : R * R => (fst lr <= snd lr)) x y).
apply (injective_projections (proj1_sig x) (proj1_sig y)).
apply (Rle_antisym (fst (proj1_sig x)) (fst (proj1_sig y))).
suff: In R (proj1_sig A) (fst (proj1_sig y)).
rewrite H1.
move=> H3.
case H3.
move=> x1 H4 H5.
apply H4.
rewrite H2.
apply (BoundedClosedSection_intro y).
apply (Req_le (fst (proj1_sig y))).
by [].
apply (proj2_sig y).
suff: In R (proj1_sig A) (fst (proj1_sig x)).
rewrite H2.
move=> H3.
case H3.
move=> x1 H4 H5.
apply H4.
rewrite H1.
apply (BoundedClosedSection_intro x).
apply (Req_le (fst (proj1_sig x))).
by [].
apply (proj2_sig x).
apply (Rle_antisym (snd (proj1_sig x)) (snd (proj1_sig y))).
suff: In R (proj1_sig A) (snd (proj1_sig x)).
rewrite H2.
move=> H3.
case H3.
move=> x1 H4 H5.
apply H5.
rewrite H1.
apply (BoundedClosedSection_intro x).
apply (proj2_sig x).
apply (Req_le (snd (proj1_sig x))).
by [].
suff: In R (proj1_sig A) (snd (proj1_sig y)).
rewrite H1.
move=> H3.
case H3.
move=> x1 H4 H5.
apply H5.
rewrite H2.
apply (BoundedClosedSection_intro y).
apply (proj2_sig y).
apply (Req_le (snd (proj1_sig y))).
by [].
Qed.

Definition BoundedClosedSectionToPair (A : BoundedClosedSectionSet) : ({lr : R * R | fst lr <= snd lr}) := proj1_sig (constructive_definite_description (fun X : {lr : R * R | fst lr <= snd lr} => (proj1_sig A) = (BoundedClosedSection X)) (BoundedClosedSectionUniqueExistsPair A)).

Definition BoundedClosedSectionToL (A : BoundedClosedSectionSet) : R := fst (proj1_sig (BoundedClosedSectionToPair A)).

Definition BoundedClosedSectionToR (A : BoundedClosedSectionSet) : R := snd (proj1_sig (BoundedClosedSectionToPair A)).

Definition BoundedClosedSectionToSize (A : BoundedClosedSectionSet) : R := (BoundedClosedSectionToR A) - (BoundedClosedSectionToL A).

Lemma BoundedClosedSectionEqual : forall A : BoundedClosedSectionSet, (proj1_sig A) = (BoundedClosedSection (BoundedClosedSectionToPair A)).
Proof.
move=> A.
rewrite /BoundedClosedSectionToPair.
elim (constructive_definite_description (fun X : {lr : R * R | fst lr <= snd lr} => proj1_sig A = BoundedClosedSection X) (BoundedClosedSectionUniqueExistsPair A)).
move=> x xp.
simpl.
apply xp.
Qed.

Lemma BoundedClosedSectionLleqR : forall A : BoundedClosedSectionSet, (BoundedClosedSectionToL A) <= (BoundedClosedSectionToR A).
Proof.
move=> A.
rewrite /BoundedClosedSectionToL.
rewrite /BoundedClosedSectionToR.
apply (proj2_sig (BoundedClosedSectionToPair A)).
Qed.

Lemma BoundedClosedSectionSetEqual : forall (LR : {lr : (R * R) | (fst lr) <= (snd lr)}), forall (P : (exists LR2 : {lr : (R * R) | (fst lr) <= (snd lr)}, (BoundedClosedSection LR) = (BoundedClosedSection LR2))), (BoundedClosedSectionToPair (exist (fun (A : Ensemble R) => (exists LR2 : {lr : R * R | (fst lr) <= (snd lr)}, A = (BoundedClosedSection LR2))) (BoundedClosedSection LR) P)) = LR.
Proof.
move=> LR H1.
rewrite /BoundedClosedSectionToPair.
elim (constructive_definite_description (fun X : {lr : R * R | fst lr <= snd lr} => proj1_sig (exist (fun A : Ensemble R => exists LR2 : {lr : R * R | fst lr <= snd lr}, A = BoundedClosedSection LR2) (BoundedClosedSection LR) H1) = BoundedClosedSection X) (BoundedClosedSectionUniqueExistsPair (exist (fun A : Ensemble R => exists LR2 : {lr : R * R | fst lr <= snd lr}, A = BoundedClosedSection LR2) (BoundedClosedSection LR) H1))).
move=> x xp.
simpl.
suff: LR = x.
move=> H2.
rewrite H2.
by [].
suff: BoundedClosedSection LR = BoundedClosedSection x.
move=> H2.
apply (let H3 := (BoundedClosedSectionUniqueExistsPair (exist (fun (A : Ensemble R) => exists LR2 : {lr : R * R | fst lr <= snd lr}, A = BoundedClosedSection LR2) (BoundedClosedSection LR) H1)) in (proj2 (proj2 (unique_existence (fun (LR0 : {lr : R * R | fst lr <= snd lr}) => proj1_sig (exist (fun A : Ensemble R => exists LR2 : {lr : R * R | fst lr <= snd lr}, A = BoundedClosedSection LR2) (BoundedClosedSection LR) H1) = BoundedClosedSection LR0)) H3))).
by [].
rewrite - H2.
by [].
apply xp.
Qed.

Lemma Theorem_3_3_1 : forall IN : (nat -> BoundedClosedSectionSet), (forall n : nat, Included R (proj1_sig (IN (S n))) (proj1_sig (IN n))) -> exists x : R, (forall n : nat, In R (proj1_sig (IN n)) x).
Proof.
move=> IN H1.
suff: Un_growing (fun n : nat => BoundedClosedSectionToL (IN n)).
move=> H2.
suff: (my_upper_bounded (Image.Im nat R (Full_set nat) (fun n : nat => BoundedClosedSectionToL (IN n)))).
move=> H3.
elim (Theorem_3_1_1 (fun n : nat => BoundedClosedSectionToL (IN n)) H3 H2).
move=> a.
case.
move=> H4 H5.
suff: Un_shrinking (fun n : nat => BoundedClosedSectionToR (IN n)).
move=> H6.
suff: (my_lower_bounded (Image.Im nat R (Full_set nat) (fun n : nat => BoundedClosedSectionToR (IN n)))).
move=> H7.
elim (Theorem_3_1_2 (fun n : nat => BoundedClosedSectionToR (IN n)) H7 H6).
move=> b.
case.
move=> H8 H9.
exists a.
suff: a <= b.
move=> H10.
move=> n.
rewrite (BoundedClosedSectionEqual (IN n)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN n))).
apply (proj1 H5 (fst (proj1_sig (BoundedClosedSectionToPair (IN n))))).
apply (Im_intro nat R (Full_set nat) (fun n0 : nat => BoundedClosedSectionToL (IN n0)) n).
by [].
by [].
apply (Rle_trans a b (snd (proj1_sig (BoundedClosedSectionToPair (IN n))))).
apply H10.
apply (Rge_le (snd (proj1_sig (BoundedClosedSectionToPair (IN n)))) b).
apply (proj1 H9 (snd (proj1_sig (BoundedClosedSectionToPair (IN n))))).
apply (Im_intro nat R (Full_set nat) (fun n0 : nat => BoundedClosedSectionToR (IN n0)) n).
by [].
by [].
apply (Theorem_2_6 (fun n : nat => BoundedClosedSectionToL (IN n)) (fun n : nat => BoundedClosedSectionToR (IN n)) a b H4 H8).
move=> n.
apply (BoundedClosedSectionLleqR (IN n)).
exists (BoundedClosedSectionToL (IN O)).
move=> x.
elim.
move=> n H7 y H8.
rewrite H8.
suff: In R (proj1_sig (IN O)) (BoundedClosedSectionToR (IN n)).
rewrite (BoundedClosedSectionEqual (IN O)).
move=> H9.
apply (Rle_ge (BoundedClosedSectionToL (IN O)) (BoundedClosedSectionToR (IN n))).
case H9.
move=> x0 H10 H11.
apply H10.
apply (shrinking_prop_ER (fun n0 : nat => proj1_sig (IN n0)) n 0 H1).
apply (le_0_n n).
rewrite (BoundedClosedSectionEqual (IN n)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN n))).
apply (proj2_sig (BoundedClosedSectionToPair (IN n))).
apply (Req_le (BoundedClosedSectionToR (IN n)) (snd (proj1_sig (BoundedClosedSectionToPair (IN n))))).
by [].
move=> n.
apply (Rle_ge (BoundedClosedSectionToR (IN (S n))) (BoundedClosedSectionToR (IN n))).
suff: (In R (proj1_sig (IN n)) (BoundedClosedSectionToR (IN (S n)))).
rewrite (BoundedClosedSectionEqual (IN n)).
case.
move=> x0 H6 H7.
apply H7.
apply (H1 n).
rewrite (BoundedClosedSectionEqual (IN (S n))).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN (S n)))).
apply (proj2_sig (BoundedClosedSectionToPair (IN (S n)))).
apply (Req_le (BoundedClosedSectionToR (IN (S n))) (snd (proj1_sig (BoundedClosedSectionToPair (IN (S n)))))).
by [].
exists (BoundedClosedSectionToR (IN O)).
move=> x.
elim.
move=> n H3 y H4.
rewrite H4.
suff: In R (proj1_sig (IN O)) (BoundedClosedSectionToL (IN n)).
rewrite (BoundedClosedSectionEqual (IN O)).
move=> H5.
case H5.
move=> x0 H6 H7.
apply H7.
apply (shrinking_prop_ER (fun n0 : nat => proj1_sig (IN n0)) n 0 H1).
apply (le_0_n n).
rewrite (BoundedClosedSectionEqual (IN n)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN n))).
apply (Req_le (fst (proj1_sig (BoundedClosedSectionToPair (IN n)))) (BoundedClosedSectionToL (IN n))).
by [].
apply (proj2_sig (BoundedClosedSectionToPair (IN n))).
move=> n.
suff: (In R (proj1_sig (IN n)) (BoundedClosedSectionToL (IN (S n)))).
rewrite (BoundedClosedSectionEqual (IN n)).
case.
move=> x0 H6 H7.
apply H6.
apply (H1 n).
rewrite (BoundedClosedSectionEqual (IN (S n))).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN (S n)))).
apply (Req_le (fst (proj1_sig (BoundedClosedSectionToPair (IN (S n))))) (BoundedClosedSectionToL (IN (S n)))).
by [].
apply (proj2_sig (BoundedClosedSectionToPair (IN (S n)))).
Qed.

Lemma Theorem_3_3_2 : forall (IN : (nat -> BoundedClosedSectionSet)), (forall n : nat, Included R (proj1_sig (IN (S n))) (proj1_sig (IN n))) -> (Un_cv (fun m : nat => (BoundedClosedSectionToR (IN m)) - (BoundedClosedSectionToL (IN m))) 0) -> (exists! x : R, (forall n : nat, In R (proj1_sig (IN n)) x)) /\ (forall x : R, (forall n : nat, In R (proj1_sig (IN n)) x) -> (Un_cv (fun m : nat => BoundedClosedSectionToL (IN m)) x) /\ (Un_cv (fun m : nat => BoundedClosedSectionToR (IN m)) x)).
Proof.
move=> IN H1 H2.
suff: Un_growing (fun n : nat => BoundedClosedSectionToL (IN n)).
move=> H3.
suff: (my_upper_bounded (Image.Im nat R (Full_set nat) (fun n : nat => BoundedClosedSectionToL (IN n)))).
move=> H4.
elim (Theorem_3_1_1 (fun n : nat => BoundedClosedSectionToL (IN n)) H4 H3).
move=> a.
case.
move=> H5 H6.
suff: Un_shrinking (fun n : nat => BoundedClosedSectionToR (IN n)).
move=> H7.
suff: (my_lower_bounded (Image.Im nat R (Full_set nat) (fun n : nat => BoundedClosedSectionToR (IN n)))).
move=> H8.
elim (Theorem_3_1_2 (fun n : nat => BoundedClosedSectionToR (IN n)) H8 H7).
move=> b.
case.
move=> H9 H10.
suff: a = b.
move=> H11.
suff: forall x : R,(forall n : nat, In R (proj1_sig (IN n)) x) -> a = x.
move=> H12.
apply conj.
exists a.
apply conj.
move=> n.
rewrite (BoundedClosedSectionEqual (IN n)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN n))).
apply (proj1 H6 (fst (proj1_sig (BoundedClosedSectionToPair (IN n))))).
apply (Im_intro nat R (Full_set nat) (fun n0 : nat => BoundedClosedSectionToL (IN n0)) n).
by [].
by [].
rewrite H11.
apply (Rge_le (snd (proj1_sig (BoundedClosedSectionToPair (IN n)))) b).
apply (proj1 H10 (snd (proj1_sig (BoundedClosedSectionToPair (IN n))))).
apply (Im_intro nat R (Full_set nat) (fun n0 : nat => BoundedClosedSectionToR (IN n0)) n).
by [].
by [].
apply H12.
move=> x H13.
apply conj.
rewrite - (H12 x H13).
apply H5.
rewrite - (H12 x H13).
rewrite H11.
apply H9.
move=> x H12.
apply (Rle_antisym a x).
apply (Rge_le x a).
apply (proj2 H6 x).
move=> y.
case.
move=> n H13 y0 H14.
rewrite H14.
suff: In R (BoundedClosedSection (BoundedClosedSectionToPair (IN n))) x.
case.
move=> x0 H15 H16.
apply H15.
rewrite - (BoundedClosedSectionEqual (IN n)).
apply (H12 n).
rewrite H11.
apply (proj2 H10 x).
move=> y.
case.
move=> n H14 y0 H15.
rewrite H15.
suff: In R (BoundedClosedSection (BoundedClosedSectionToPair (IN n))) x.
case.
move=> x0 H16 H17.
apply (Rle_ge x0 (BoundedClosedSectionToR (IN n))).
apply H17.
rewrite - (BoundedClosedSectionEqual (IN n)).
apply (H12 n).
apply (Rminus_diag_uniq_sym a b).
apply (Proposition_2_3 (fun m : nat => BoundedClosedSectionToR (IN m) - BoundedClosedSectionToL (IN m))).
suff: (fun m : nat => BoundedClosedSectionToR (IN m) - BoundedClosedSectionToL (IN m)) = (RSequencePlus (fun m : nat => BoundedClosedSectionToR (IN m)) (RSequenceOpp (fun m : nat => BoundedClosedSectionToL (IN m)))).
move=> H11.
rewrite H11.
apply (Theorem_2_5_1_plus (fun m : nat => BoundedClosedSectionToR (IN m)) (RSequenceOpp (fun m : nat => BoundedClosedSectionToL (IN m))) b (- a)).
apply H9.
apply (Theorem_2_5_1_opp (fun m : nat => BoundedClosedSectionToL (IN m)) a).
apply H5.
apply (functional_extensionality (fun m : nat => BoundedClosedSectionToR (IN m) - BoundedClosedSectionToL (IN m)) (RSequencePlus (fun m : nat => BoundedClosedSectionToR (IN m)) (RSequenceOpp (fun m : nat => BoundedClosedSectionToL (IN m))))).
move=> n.
rewrite /RSequencePlus.
rewrite /RSequenceOpp.
by [].
apply H2.
exists (BoundedClosedSectionToL (IN O)).
move=> x.
elim.
move=> n H8 y H9.
rewrite H9.
suff: In R (proj1_sig (IN O)) (BoundedClosedSectionToR (IN n)).
rewrite (BoundedClosedSectionEqual (IN O)).
move=> H10.
apply (Rle_ge (BoundedClosedSectionToL (IN O)) (BoundedClosedSectionToR (IN n))).
case H10.
move=> x0 H11 H12.
apply H11.
apply (shrinking_prop_ER (fun n0 : nat => proj1_sig (IN n0)) n 0 H1).
apply (le_0_n n).
rewrite (BoundedClosedSectionEqual (IN n)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN n))).
apply (proj2_sig (BoundedClosedSectionToPair (IN n))).
apply (Req_le (BoundedClosedSectionToR (IN n)) (snd (proj1_sig (BoundedClosedSectionToPair (IN n))))).
by [].
move=> n.
apply (Rle_ge (BoundedClosedSectionToR (IN (S n))) (BoundedClosedSectionToR (IN n))).
suff: (In R (proj1_sig (IN n)) (BoundedClosedSectionToR (IN (S n)))).
rewrite (BoundedClosedSectionEqual (IN n)).
case.
move=> x0 H7 H8.
apply H8.
apply (H1 n).
rewrite (BoundedClosedSectionEqual (IN (S n))).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN (S n)))).
apply (proj2_sig (BoundedClosedSectionToPair (IN (S n)))).
apply (Req_le (BoundedClosedSectionToR (IN (S n))) (snd (proj1_sig (BoundedClosedSectionToPair (IN (S n)))))).
by [].
exists (BoundedClosedSectionToR (IN O)).
move=> x.
elim.
move=> n H4 y H5.
rewrite H5.
suff: In R (proj1_sig (IN O)) (BoundedClosedSectionToL (IN n)).
rewrite (BoundedClosedSectionEqual (IN O)).
move=> H6.
case H6.
move=> x0 H7 H8.
apply H8.
apply (shrinking_prop_ER (fun n0 : nat => proj1_sig (IN n0)) n 0 H1).
apply (le_0_n n).
rewrite (BoundedClosedSectionEqual (IN n)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN n))).
apply (Req_le (fst (proj1_sig (BoundedClosedSectionToPair (IN n)))) (BoundedClosedSectionToL (IN n))).
by [].
apply (proj2_sig (BoundedClosedSectionToPair (IN n))).
move=> n.
suff: (In R (proj1_sig (IN n)) (BoundedClosedSectionToL (IN (S n)))).
rewrite (BoundedClosedSectionEqual (IN n)).
case.
move=> x0 H6 H7.
apply H6.
apply (H1 n).
rewrite (BoundedClosedSectionEqual (IN (S n))).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN (S n)))).
apply (Req_le (fst (proj1_sig (BoundedClosedSectionToPair (IN (S n))))) (BoundedClosedSectionToL (IN (S n)))).
by [].
apply (proj2_sig (BoundedClosedSectionToPair (IN (S n)))).
Qed.

Definition Subsequence (T : Type) (ABn An : nat -> T) : Prop := exists (Bn : nat -> nat), (forall (n : nat),(Bn n) < (Bn (S n)))%nat /\ (forall (n : nat),(ABn n) = (An (Bn n))).

Lemma Formula_3_17 : forall (An : nat -> nat), (forall (n : nat),(An n) < (An (S n)))%nat -> (forall (n : nat),(An n) >= n)%nat.
Proof.
move=> An H1.
elim.
apply (le_0_n (An O)).
move=> n H2.
apply (le_trans (S n) (S (An n)) (An (S n))).
apply (le_n_S n (An n)).
apply H2.
apply (H1 n).
Qed.

Lemma Formula_3_18 : forall (An Bn : nat -> R), (Subsequence R An Bn) -> forall (x : R), (Un_cv Bn x) -> (Un_cv An x).
Proof.
move=> An Bn H1 x H2.
elim H1.
move=> kn.
case.
move=> H3 H4.
move=> eps H5.
elim (H2 eps H5).
move=> n H6.
exists n.
move=> n0 H7.
rewrite (H4 n0).
apply (H6 (kn n0)).
apply (le_trans n n0 (kn n0)).
apply H7.
apply (Formula_3_17 kn H3 n0).
Qed.

Lemma Infinite_Set_Or : forall (U : Type) (A B : Ensemble U), (~ Finite U (Union U A B)) -> (~ Finite U A) \/ (~ Finite U B).
Proof.
move=> U A B H1.
apply (NNPP (~ Finite U A \/ ~ Finite U B)).
move=> H2.
apply H1.
apply (Finite_Set_Or U A B).
apply (NNPP (Finite U A)).
move=> H3.
apply H2.
left.
apply H3.
apply (NNPP (Finite U B)).
move=> H3.
apply H2.
right.
apply H3.
Qed.

Lemma Infinite_Or_Infinite : forall (U : Type), exists (f : ((Ensemble U) * (Ensemble U)) -> (Ensemble U)), forall (AB : ((Ensemble U) * (Ensemble U))), (~ Finite U (Union U (fst AB) (snd AB))) -> (~ Finite U (f AB)) /\ ((f AB) = (fst AB) \/ (f AB) = (snd AB)).
Proof.
move=> U.
exists (fun (AB : Ensemble U * Ensemble U) => match excluded_middle_informative (Finite U (fst AB)) with
  | left _ => snd AB
  | right _ => fst AB
end).
move=> AB H1.
elim (excluded_middle_informative (Finite U (fst AB))).
move=> H2.
elim (Infinite_Set_Or U (fst AB) (snd AB) H1).
move=> H3.
elim (H3 H2).
move=> H3.
apply conj.
apply H3.
right.
reflexivity.
move=> H2.
apply conj.
apply H2.
left.
reflexivity.
Qed.

Lemma Iminv_Infinite_Or_Infinite : forall (V U : Type), forall (F : V -> U), exists (f : ((Ensemble U) * (Ensemble U)) -> (Ensemble U)), forall (AB : ((Ensemble U) * (Ensemble U))), (~ Finite V (fun v : V => (In U (Union U (fst AB) (snd AB)) (F v))) -> (~ Finite V (fun v : V => In U (f AB) (F v)))) /\ ((f AB) = (fst AB) \/ (f AB) = (snd AB)).
Proof.
move=> V U F.
exists (fun (AB : Ensemble U * Ensemble U) => match excluded_middle_informative (Finite V (fun (v : V) => In U (fst AB) (F v))) with
  | left _ => snd AB
  | right _ => fst AB
end).
move=> AB.
apply conj.
elim (excluded_middle_informative (Finite V (fun (v : V) => In U (fst AB) (F v)))).
suff: ((fun (v : V) => In U (Union U (fst AB) (snd AB)) (F v))) = Union V (fun (v : V) => In U (fst AB) (F v)) (fun (v : V) => In U (snd AB) (F v)).
move=> H1.
rewrite H1.
move=> H2 H3.
elim (Infinite_Set_Or V (fun (v : V) => In U (fst AB) (F v)) (fun (v : V) => In U (snd AB) (F v)) H3).
move=> H4.
elim (H4 H2).
apply.
apply (Extensionality_Ensembles V (fun (v : V) => In U (Union U (fst AB) (snd AB)) (F v)) (Union V (fun (v : V) => In U (fst AB) (F v)) (fun (v : V) => In U (snd AB) (F v)))).
apply conj.
move=> y H1.
suff: ((fun (v : V) => In U (fst AB) (F v)) y) \/ ((fun (v : V) => In U (snd AB) (F v)) y).
case.
move=> H2.
apply (Union_introl V (fun (v : V) => In U (fst AB) (F v)) (fun (v : V) => In U (snd AB) (F v))).
apply H2.
move=> H2.
apply (Union_intror V (fun (v : V) => In U (fst AB) (F v)) (fun (v : V) => In U (snd AB) (F v))).
apply H2.
elim H1.
move=> z H2.
left.
apply H2.
move=> z H2.
right.
apply H2.
move=> y.
elim.
move=> z H1.
apply (Union_introl U (fst AB) (snd AB)).
apply H1.
move=> z H1.
apply (Union_intror U (fst AB) (snd AB)).
apply H1.
move=> H1 H2.
apply H1.
elim (excluded_middle_informative (Finite V (fun (v : V) => In U (fst AB) (F v)))).
move=> H1.
right.
reflexivity.
move=> H1.
left.
reflexivity.
Qed.

Lemma FullsetNatInfinite : (~ Finite nat (Full_set nat)).
Proof.
move=> H1.
elim (Finite_max_nat (Full_set nat)).
move=> ma H2.
apply (le_not_lt (S ma) ma).
apply (proj2 H2 (S ma)).
by [].
by [].
apply H1.
exists O.
by [].
Qed.

Lemma Two_Gt_Zero : 2 > 0.
Proof.
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
Qed.

Lemma Two_Neq_Zero : 2 <> 0.
Proof.
apply (Rgt_not_eq 2 0 Two_Gt_Zero).
Qed.

Lemma Two_Pow_Gt_Zero : forall n : nat, 2 ^ n > 0.
Proof.
elim.
simpl.
apply (Rlt_0_1).
move=> n H1.
simpl.
apply (Rmult_gt_0_compat 2 (2 ^ n)).
apply (Two_Gt_Zero).
apply H1.
Qed.

Lemma Two_Pow_Neq_Zero : forall n : nat, 2 ^ n <> 0.
Proof.
move=> n.
apply (Rgt_not_eq (2 ^ n) 0 (Two_Pow_Gt_Zero n)).
Qed.

Lemma Theorem_3_4 : forall (An : nat -> R), (my_bounded (Image.Im nat R (Full_set nat) An)) -> exists (Bn : nat -> R), ((Subsequence R Bn An) /\ (exists x : R, Un_cv Bn x)).
Proof.
move=> An H1.
elim (proj1 H1).
move=> b H2.
elim (proj2 H1).
move=> a H3.
suff: a <= b.
move=> H4.
elim (Iminv_Infinite_Or_Infinite nat R An).
move=> F H5.
suff: exists (IN : nat -> BoundedClosedSectionSet) , forall (n : nat),(BoundedClosedSectionToSize (IN n)) = (b - a) / (2 ^ n) /\ (~ Finite nat (fun m : nat => In R (proj1_sig (IN n)) (An m))) /\ (Included R (proj1_sig (IN (S n))) (proj1_sig (IN n))).
elim.
move=> IN.
move=> H6.
suff: exists (G : nat -> nat -> nat), forall (n m : nat), (is_min_nat (fun k : nat => (In R (proj1_sig (IN n)) (An k)) /\ (k >= m)%nat) (G n m)).
elim.
move=> G H7.
exists (fun (k : nat) => An ((fix Bn (n : nat) : nat := match n with
  | O => (G O O)
  | S n0 => (G (S n0) (S (Bn n0)))
end) k)).
apply conj.
exists (fix Bn (n : nat) : nat := match n with
  | O => (G O O)
  | S n0 => (G (S n0) (S (Bn n0)))
end).
apply conj.
elim.
apply (proj2 (proj1 (H7 1%nat (S (G O O))))).
move=> n0 H8.
apply (proj2 (proj1 (H7 (S (S n0)) (S (G (S n0) (S ((fix Bn (n : nat) : nat := match n with
  | 0 => G 0 0
  | S n1 => G (S n1) (S (Bn n1))
end) n0)))))%nat)).
by [].
suff: (exists! x : R, (forall n : nat, In R (proj1_sig (IN n)) x)) /\ (forall x : R, (forall n : nat, In R (proj1_sig (IN n)) x) -> (Un_cv (fun m : nat => BoundedClosedSectionToL (IN m)) x) /\ (Un_cv (fun m : nat => BoundedClosedSectionToR (IN m)) x)).
move=> H8.
suff: exists x : R, (forall n : nat, In R (proj1_sig (IN n)) x).
elim.
move=> x H9.
exists x.
apply (Proposition_2_7 (fun m : nat => BoundedClosedSectionToL (IN m)) (fun m : nat => BoundedClosedSectionToR (IN m)) x (proj1 (proj2 H8 x H9)) (proj2 (proj2 H8 x H9)) (fun k : nat => An ((fix Bn (n : nat) : nat := match n with
  | 0%nat => G 0%nat 0%nat
  | S n0 => G (S n0) (S (Bn n0))
end) k))).
move=> n.
suff: In R (BoundedClosedSection (BoundedClosedSectionToPair (IN n))) (An ((fix Bn (n0 : nat) : nat := match n0 with
  | 0%nat => G 0%nat 0%nat
  | S n1 => G (S n1) (S (Bn n1))
end) n)).
move=> H10.
case H10.
by [].
rewrite - (BoundedClosedSectionEqual (IN n)).
elim n.
apply (proj1 (proj1 (H7 O O))).
move=> n0 H12.
apply (proj1 (proj1 (H7 (S n0) (S ((fix Bn (n1 : nat) : nat := match n1 with
  | 0%nat => G 0%nat 0%nat
  | S n2 => G (S n2) (S (Bn n2))
end) n0))))).
apply (proj1 ((proj2 (unique_existence (fun x : R => forall n : nat, In R (proj1_sig (IN n)) x))) (proj1 H8))).
apply (Theorem_3_3_2 IN).
move=> n.
apply (proj2 (proj2 (H6 n))).
suff: (fun m : nat => BoundedClosedSectionToR (IN m) - BoundedClosedSectionToL (IN m)) = (fun n : nat => (b - a) / 2 ^ n).
move=> H8.
rewrite H8.
suff: (fun n : nat => (b - a) / 2 ^ n) = (RSequenceMult (fun n : nat => (b - a)) (fun n : nat => 1 / 2 ^ n)).
move=> H9.
rewrite H9.
rewrite - (Rmult_0_r (b - a)).
apply (Theorem_2_5_1_mult (fun _ : nat => b - a) (fun n : nat => 1 / 2 ^ n) (b - a) 0).
move=> eps H10.
exists O.
move=> n H11.
rewrite (R_dist_eq (b - a)).
apply H10.
apply Formula_3_9_2.
apply (functional_extensionality (fun n : nat => (b - a) / 2 ^ n) (RSequenceMult (fun _ : nat => b - a) (fun n : nat => 1 / 2 ^ n))).
move=> n.
rewrite /Rdiv.
rewrite - (Rmult_1_l (/ 2 ^ n)).
by [].
apply (functional_extensionality (fun m : nat => BoundedClosedSectionToR (IN m) - BoundedClosedSectionToL (IN m)) (fun n : nat => (b - a) / 2 ^ n)).
move=> n.
rewrite - (proj1 (H6 n)).
by [].
suff: forall (n m : nat), (exists ! x : nat, is_min_nat (fun k : nat => In R (proj1_sig (IN n)) (An k) /\ (k >= m)%nat) x).
move=> H7.
exists (fun (n m : nat) => proj1_sig (constructive_definite_description (fun (l : nat) => is_min_nat (fun k : nat => In R (proj1_sig (IN n)) (An k) /\ (k >= m)%nat) l) (H7 n m))).
move=> n m.
elim (constructive_definite_description (fun l : nat => is_min_nat (fun k : nat => In R (proj1_sig (IN n)) (An k) /\ (k >= m)%nat) l) (H7 n m)).
simpl.
by [].
move=> n m.
apply (unique_existence (fun x : nat => is_min_nat (fun k : nat => In R (proj1_sig (IN n)) (An k) /\ (k >= m)%nat) x)).
apply conj.
apply (Exist_min_nat (fun k : nat => In R (proj1_sig (IN n)) (An k) /\ (k >= m)%nat)).
apply (NNPP (Inhabited nat (fun k : nat => In R (proj1_sig (IN n)) (An k) /\ (k >= m)%nat))).
move=> H7.
apply (proj1 (proj2 (H6 n))).
apply (Finite_Set_Included nat (fun k : nat => In R (proj1_sig (IN n)) (An k)) (fun k : nat => (k < m)%nat)).
apply (cardinal_finite nat (fun k : nat => (k < m)%nat) m).
apply (nat_cardinal m).
move=> x H8.
elim (le_or_lt m x).
move=> H9.
apply False_ind.
apply H7.
exists x.
apply conj.
apply H8.
apply H9.
apply.
move=> k l H7 H8.
apply (le_antisym k l).
apply ((proj2 H7) l (proj1 H8)).
apply ((proj2 H8) k (proj1 H7)).
suff: forall (I : BoundedClosedSectionSet), (BoundedClosedSectionToL I) <= ((BoundedClosedSectionToL I) + (BoundedClosedSectionToR I)) / 2.
move=> H6.
suff: forall (I : BoundedClosedSectionSet), ((BoundedClosedSectionToL I) + (BoundedClosedSectionToR I)) / 2 <= (BoundedClosedSectionToR I).
move=> H7.
suff: forall (I : BoundedClosedSectionSet), exists LR : {lr : R * R | fst lr <= snd lr}, (F ( BoundedClosedSection (exist (fun x : R * R => (fst x) <= (snd x)) ((BoundedClosedSectionToL I) , ((BoundedClosedSectionToL I) + (BoundedClosedSectionToR I)) / 2) (H6 I)) ,BoundedClosedSection (exist (fun x : R * R => (fst x) <= (snd x)) (((BoundedClosedSectionToL I) + (BoundedClosedSectionToR I)) / 2, (BoundedClosedSectionToR I)) (H7 I)) )) = BoundedClosedSection LR.
move=> H8.
suff: forall (I : BoundedClosedSectionSet), Included R (F ( BoundedClosedSection (exist (fun x : R * R => (fst x) <= (snd x)) ((BoundedClosedSectionToL I) , ((BoundedClosedSectionToL I) + (BoundedClosedSectionToR I)) / 2) (H6 I)) ,BoundedClosedSection (exist (fun x : R * R => (fst x) <= (snd x)) (((BoundedClosedSectionToL I) + (BoundedClosedSectionToR I)) / 2, (BoundedClosedSectionToR I)) (H7 I)) )) (proj1_sig I).
move=> H9.
suff: exists LR : {lr : R * R | fst lr <= snd lr}, BoundedClosedSection (exist (fun lr : (R * R) => (fst lr) <= (snd lr)) (a,b) H4) = BoundedClosedSection LR.
move=> H10.
suff: (let IN := (fix IN (n : nat) : BoundedClosedSectionSet := match n with
  | O => exist (fun X : (Ensemble R) => exists LR : {lr : R * R | (fst lr) <= (snd lr)}, X = (BoundedClosedSection LR)) (BoundedClosedSection (exist (fun lr : (R * R) => (fst lr) <= (snd lr)) (a,b) H4)) H10
  | S n0 => exist (fun X : (Ensemble R) => exists LR : {lr : R * R | (fst lr) <= (snd lr)}, X = (BoundedClosedSection LR)) (F ( BoundedClosedSection (exist (fun x : R * R => (fst x) <= (snd x)) ((BoundedClosedSectionToL (IN n0)) , ((BoundedClosedSectionToL (IN n0)) + (BoundedClosedSectionToR (IN n0))) / 2) (H6 (IN n0))) ,BoundedClosedSection (exist (fun x : R * R => (fst x) <= (snd x)) (((BoundedClosedSectionToL (IN n0)) + (BoundedClosedSectionToR (IN n0))) / 2, (BoundedClosedSectionToR (IN n0))) (H7 (IN n0))) )) (H8 (IN n0))
end) in (exists IN : nat -> BoundedClosedSectionSet, forall n : nat, BoundedClosedSectionToSize (IN n) = (b - a) / 2 ^ n /\ ~ Finite nat (fun m : nat => In R (proj1_sig (IN n)) (An m)) /\ Included R (proj1_sig (IN (S n))) (proj1_sig (IN n)))).
by [].
move=> IN.
exists IN.
move=> n.
elim n.
apply conj.
rewrite /BoundedClosedSectionToSize.
rewrite /BoundedClosedSectionToR.
rewrite /BoundedClosedSectionToL.
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H4) H10).
simpl.
rewrite /Rdiv.
rewrite (Rinv_1).
rewrite (Rmult_1_r (b - a)).
by [].
apply conj.
move=> H11.
apply FullsetNatInfinite.
apply (Finite_Set_Included nat (Full_set nat) (fun m : nat => In R (proj1_sig (IN O)) (An m))).
apply H11.
move=> m.
move=> H12.
rewrite (BoundedClosedSectionEqual (IN O)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN 0%nat))).
rewrite /IN.
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H4) H10).
simpl.
apply (Rge_le (An m) a).
apply (H3 (An m)).
apply (Im_intro nat R (Full_set nat) An m).
by [].
by [].
rewrite /IN.
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H4) H10).
simpl.
apply (H2 (An m)).
apply (Im_intro nat R (Full_set nat) An m).
by [].
by [].
apply (H9 (IN O)).
move=> n0 H11.
simpl.
case (proj2 (H5 ( BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0))), BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0))) ))).
simpl.
move=> H12.
apply conj.
suff:exists LR : {lr : R * R | fst lr <= snd lr}, (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0)))) = BoundedClosedSection LR.
move=> H13.
rewrite (sig_map (fun X : Ensemble R => exists LR : {lr : R * R | fst lr <= snd lr}, X = BoundedClosedSection LR) (exist (fun X : Ensemble R => exists LR : {lr : R * R | fst lr <= snd lr}, X = BoundedClosedSection LR) (F (BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0))), BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0))))) (H8 (IN n0))) (exist (fun X : Ensemble R => exists LR : {lr : R * R | fst lr <= snd lr}, X = BoundedClosedSection LR) (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0)))) H13)).
rewrite /BoundedClosedSectionToSize.
rewrite /BoundedClosedSectionToR.
rewrite /BoundedClosedSectionToL.
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr) (BoundedClosedSectionToL (IN n0) , (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0))) H13).
simpl.
rewrite - {2}(eps2 (BoundedClosedSectionToL (IN n0))).
rewrite /Rdiv.
rewrite (Rmult_plus_distr_r (BoundedClosedSectionToL (IN n0)) (BoundedClosedSectionToR (IN n0)) (/ 2)).
rewrite (Rplus_comm (BoundedClosedSectionToL (IN n0) * / 2) (BoundedClosedSectionToR (IN n0) * / 2)).
rewrite /Rminus.
rewrite (Rplus_assoc (BoundedClosedSectionToR (IN n0) * / 2) (BoundedClosedSectionToL (IN n0) * / 2) (-(BoundedClosedSectionToL (IN n0) * / 2 + BoundedClosedSectionToL (IN n0) * / 2))).
rewrite (Ropp_plus_distr (BoundedClosedSectionToL (IN n0) * / 2) (BoundedClosedSectionToL (IN n0) * / 2)).
rewrite - (Rplus_assoc (BoundedClosedSectionToL (IN n0) * / 2) (- (BoundedClosedSectionToL (IN n0) * / 2)) (- (BoundedClosedSectionToL (IN n0) * / 2))).
rewrite (Rplus_opp_r (BoundedClosedSectionToL (IN n0) * / 2)).
rewrite (Rplus_0_l (- (BoundedClosedSectionToL (IN n0) * / 2))).
rewrite (Ropp_mult_distr_l (BoundedClosedSectionToL (IN n0) ) (/ 2)).
rewrite - (Rmult_plus_distr_r (BoundedClosedSectionToR (IN n0) ) (- BoundedClosedSectionToL (IN n0) ) (/ 2)).
rewrite /BoundedClosedSectionToSize in H11.
rewrite /Rminus in H11.
rewrite (proj1 H11).
rewrite (Rinv_mult_distr 2 (2 ^ n0)).
rewrite (Rmult_comm (/ 2) (/ 2 ^ n0)).
apply (Rmult_assoc (b + - a) (/ 2 ^ n0) (/ 2)).
apply Two_Neq_Zero.
apply (Two_Pow_Neq_Zero n0).
apply H12.
rewrite - H12.
apply (H8 (IN n0)).
apply conj.
move=> H13.
apply (proj1 (H5 (BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0))), BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0)))))).
simpl.
suff: (Union R (BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0)))) (BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0))))) = (proj1_sig (IN n0)).
move=> H14.
rewrite H14.
apply (proj1 (proj2 H11)).
apply (Extensionality_Ensembles R (Union R (BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0)))) (BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0))))) (proj1_sig (IN n0))).
apply conj.
move=> x.
case.
move=> x0.
case.
move=> x1.
simpl.
move=> H14 H15.
rewrite (BoundedClosedSectionEqual (IN n0)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN n0))).
apply H14.
apply (Rle_trans x1 ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (snd (proj1_sig (BoundedClosedSectionToPair (IN n0))))).
apply H15.
apply (H7 (IN n0)).
move=> x0.
case.
move=> x1.
simpl.
move=> H14 H15.
rewrite (BoundedClosedSectionEqual (IN n0)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN n0))).
apply (Rle_trans (fst (proj1_sig (BoundedClosedSectionToPair (IN n0)))) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) x1).
apply (H6 (IN n0)).
apply H14.
apply H15.
move=> x.
rewrite (BoundedClosedSectionEqual (IN n0)).
case.
move=> x0 H14 H15.
case (Rle_lt_dec x0 ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2)).
move=> H16.
apply (Union_introl R (BoundedClosedSection (exist (fun x1 : R * R => fst x1 <= snd x1) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0)))) (BoundedClosedSection (exist (fun x1 : R * R => fst x1 <= snd x1) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0))))).
apply (BoundedClosedSection_intro (exist (fun x1 : R * R => fst x1 <= snd x1) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0)))).
apply H14.
apply H16.
move=> H16.
apply (Union_intror R (BoundedClosedSection (exist (fun x1 : R * R => fst x1 <= snd x1) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0)))) (BoundedClosedSection (exist (fun x1 : R * R => fst x1 <= snd x1) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0))))).
apply (BoundedClosedSection_intro (exist (fun x1 : R * R => fst x1 <= snd x1) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0)))).
simpl.
apply (Rlt_le ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) x0 H16).
simpl.
apply H15.
apply H13.
simpl.
apply (H9 (IN (S n0))).
move=> H12.
apply conj.
suff:exists LR : {lr : R * R | fst lr <= snd lr}, (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0)))) = BoundedClosedSection LR.
move=> H13.
rewrite (sig_map (fun X : Ensemble R => exists LR : {lr : R * R | fst lr <= snd lr}, X = BoundedClosedSection LR) (exist (fun X : Ensemble R => exists LR : {lr : R * R | fst lr <= snd lr}, X = BoundedClosedSection LR) (F (BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0))), BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0))))) (H8 (IN n0))) (exist (fun X : Ensemble R => exists LR : {lr : R * R | fst lr <= snd lr}, X = BoundedClosedSection LR) (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0)))) H13)).
rewrite /BoundedClosedSectionToSize.
rewrite /BoundedClosedSectionToR.
rewrite /BoundedClosedSectionToL.
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0))) H13).
simpl.
rewrite - {1}(eps2 (BoundedClosedSectionToR (IN n0))).
rewrite /Rdiv.
rewrite (Rmult_plus_distr_r (BoundedClosedSectionToL (IN n0)) (BoundedClosedSectionToR (IN n0)) (/ 2)).
rewrite (Rplus_comm (BoundedClosedSectionToL (IN n0) * / 2) (BoundedClosedSectionToR (IN n0) * / 2)).
rewrite /Rminus.
rewrite (Rplus_assoc (BoundedClosedSectionToR (IN n0) * / 2) (BoundedClosedSectionToR (IN n0) * / 2) (-(BoundedClosedSectionToR (IN n0) * / 2 + BoundedClosedSectionToL (IN n0) * / 2))).
rewrite (Ropp_plus_distr (BoundedClosedSectionToR (IN n0) * / 2) (BoundedClosedSectionToL (IN n0) * / 2)).
rewrite - (Rplus_assoc (BoundedClosedSectionToR (IN n0) * / 2) (- (BoundedClosedSectionToR (IN n0) * / 2)) (- (BoundedClosedSectionToL (IN n0) * / 2))).
rewrite (Rplus_opp_r (BoundedClosedSectionToR (IN n0) * / 2)).
rewrite (Rplus_0_l (- (BoundedClosedSectionToL (IN n0) * / 2))).
rewrite (Ropp_mult_distr_l (BoundedClosedSectionToL (IN n0) ) (/ 2)).
rewrite - (Rmult_plus_distr_r (BoundedClosedSectionToR (IN n0) ) (- BoundedClosedSectionToL (IN n0) ) (/ 2)).
rewrite /BoundedClosedSectionToSize in H11.
rewrite /Rminus in H11.
rewrite (proj1 H11).
rewrite (Rinv_mult_distr 2 (2 ^ n0)).
rewrite (Rmult_comm (/ 2) (/ 2 ^ n0)).
apply (Rmult_assoc (b + - a) (/ 2 ^ n0) (/ 2)).
apply Two_Neq_Zero.
apply (Two_Pow_Neq_Zero n0).
apply H12.
simpl in H12.
rewrite - H12.
apply (H8 (IN n0)).
apply conj.
apply (proj1 (H5 (BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0))), BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0)))))).
simpl.
suff: (Union R (BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0)))) (BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0))))) = (proj1_sig (IN n0)).
move=> H14.
rewrite H14.
apply (proj1 (proj2 H11)).
apply (Extensionality_Ensembles R (Union R (BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0)))) (BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0))))) (proj1_sig (IN n0))).
apply conj.
move=> x.
case.
move=> x0.
case.
move=> x1.
simpl.
move=> H14 H15.
rewrite (BoundedClosedSectionEqual (IN n0)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN n0))).
apply H14.
apply (Rle_trans x1 ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (snd (proj1_sig (BoundedClosedSectionToPair (IN n0))))).
apply H15.
apply (H7 (IN n0)).
move=> x0.
case.
move=> x1.
simpl.
move=> H14 H15.
rewrite (BoundedClosedSectionEqual (IN n0)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN n0))).
apply (Rle_trans (fst (proj1_sig (BoundedClosedSectionToPair (IN n0)))) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) x1).
apply (H6 (IN n0)).
apply H14.
apply H15.
move=> x.
rewrite (BoundedClosedSectionEqual (IN n0)).
case.
move=> x0 H14 H15.
case (Rle_lt_dec x0 ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2)).
move=> H16.
apply (Union_introl R (BoundedClosedSection (exist (fun x1 : R * R => fst x1 <= snd x1) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0)))) (BoundedClosedSection (exist (fun x1 : R * R => fst x1 <= snd x1) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0))))).
apply (BoundedClosedSection_intro (exist (fun x1 : R * R => fst x1 <= snd x1) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0)))).
apply H14.
apply H16.
move=> H16.
apply (Union_intror R (BoundedClosedSection (exist (fun x1 : R * R => fst x1 <= snd x1) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0)))) (BoundedClosedSection (exist (fun x1 : R * R => fst x1 <= snd x1) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0))))).
apply (BoundedClosedSection_intro (exist (fun x1 : R * R => fst x1 <= snd x1) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0)))).
simpl.
apply (Rlt_le ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2) x0 H16).
simpl.
apply H15.
apply (H9 (IN (S n0))).
exists (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H4).
by [].
move=> I.
case (proj2 (H5 (BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) (BoundedClosedSectionToL I, (BoundedClosedSectionToL I + BoundedClosedSectionToR I) / 2) (H6 I)), BoundedClosedSection (exist (fun x : R * R => fst x <= snd x) ((BoundedClosedSectionToL I + BoundedClosedSectionToR I) / 2, BoundedClosedSectionToR I) (H7 I))))).
move=> H9.
rewrite H9.
simpl.
rewrite (BoundedClosedSectionEqual I).
move=> x.
case.
move=> x0 H10 H11.
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair I)).
apply H10.
apply (Rle_trans x0 (snd (proj1_sig (exist (fun x : R * R => fst x <= snd x) (BoundedClosedSectionToL I, (BoundedClosedSectionToL I + BoundedClosedSectionToR I) / 2) (H6 I)))) (snd (proj1_sig (BoundedClosedSectionToPair I)))).
apply H11.
apply (H7 I).
move=> H9.
rewrite H9.
simpl.
rewrite (BoundedClosedSectionEqual I).
move=> x.
case.
move=> x0 H10 H11.
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair I)).
apply (Rle_trans (fst (proj1_sig (BoundedClosedSectionToPair I))) ((BoundedClosedSectionToL I + BoundedClosedSectionToR I) / 2) x0).
apply (H6 I).
apply H10.
apply H11.
move=> x.
case (proj2 (H5 (BoundedClosedSection (exist (fun x0 : R * R => fst x0 <= snd x0) (BoundedClosedSectionToL x, (BoundedClosedSectionToL x + BoundedClosedSectionToR x) / 2) (H6 x)), BoundedClosedSection (exist (fun x0 : R * R => fst x0 <= snd x0) ((BoundedClosedSectionToL x + BoundedClosedSectionToR x) / 2, BoundedClosedSectionToR x) (H7 x))))).
move=> H8.
rewrite H8.
simpl.
exists (exist (fun x0 : R * R => fst x0 <= snd x0) (BoundedClosedSectionToL x, (BoundedClosedSectionToL x + BoundedClosedSectionToR x) / 2) (H6 x)).
by [].
move=> H8.
rewrite H8.
simpl.
exists (exist (fun x0 : R * R => fst x0 <= snd x0) ((BoundedClosedSectionToL x + BoundedClosedSectionToR x) / 2, BoundedClosedSectionToR x) (H7 x)).
by [].
move=> I.
rewrite - {2}(eps2 (BoundedClosedSectionToR I)).
rewrite /Rdiv.
rewrite (Rmult_plus_distr_r (BoundedClosedSectionToL I) (BoundedClosedSectionToR I) (/ 2)).
apply (Rplus_le_compat_r (BoundedClosedSectionToR I * / 2) (BoundedClosedSectionToL I * / 2) (BoundedClosedSectionToR I * / 2)).
apply (Rmult_le_compat_r (/ 2) (BoundedClosedSectionToL I) (BoundedClosedSectionToR I)).
apply (Rlt_le 0 (/ 2)).
apply (Rinv_0_lt_compat 2).
apply (Two_Gt_Zero).
apply (BoundedClosedSectionLleqR I).
move=> I.
rewrite - {1}(eps2 (BoundedClosedSectionToL I)).
rewrite /Rdiv.
rewrite (Rmult_plus_distr_r (BoundedClosedSectionToL I) (BoundedClosedSectionToR I) (/ 2)).
apply (Rplus_le_compat_l (BoundedClosedSectionToL I * / 2) (BoundedClosedSectionToL I * / 2) (BoundedClosedSectionToR I * / 2)).
apply (Rmult_le_compat_r (/ 2) (BoundedClosedSectionToL I) (BoundedClosedSectionToR I)).
apply (Rlt_le 0 (/ 2)).
apply (Rinv_0_lt_compat 2).
apply (Two_Gt_Zero).
apply (BoundedClosedSectionLleqR I).
apply (Rle_trans a (An O) b).
apply (Rge_le (An O) a).
apply (H3 (An O)).
apply (Im_intro nat R (Full_set nat) An O).
by [].
by [].
apply (H2 (An O)).
apply (Im_intro nat R (Full_set nat) An O).
by [].
by [].
Qed.

Lemma Proposition_3_5_1 : forall An : (nat -> R), (Cauchy_crit An) -> (my_bounded (fun x:R => (EUn An x))).
Proof.
move=> An H1.
elim (H1 1 Rlt_0_1).
move => N H2.
suff: (Finite R (fun x => exists (n0 : nat), (Rabs (An n0)) = x /\ (n0 <= N)%nat)).
move=> H3.
apply (proj2 (bounded_abs (fun x : R => EUn An x))).
elim (Finite_max_R (fun x : R => exists n0 : nat, (Rabs (An n0)) = x /\ (n0 <= N)%nat) H3).
move=> ma H4.
exists (Rmax ma ((Rabs (An N)) + 1)).
move=> x H5.
elim H5.
move=> x0 H6 y H7.
rewrite H7.
elim H6.
move=> n H8.
rewrite H8.
elim (le_or_lt N n).
move=> H9.
apply (Rle_trans (Rabs (An n)) ((Rabs (An N)) + 1) (Rmax ma (Rabs (An N) + 1))).
apply (Rplus_le_reg_l (- (Rabs (An N))) (Rabs (An n)) (Rabs (An N) +1)).
rewrite - (Rplus_assoc (- Rabs (An N)) (Rabs (An N)) 1).
rewrite (Rplus_opp_l (Rabs (An N))).
rewrite (Rplus_0_l 1).
rewrite (Rplus_comm (- Rabs (An N)) (Rabs (An n))).
apply (Rle_trans (Rabs (An n) + - Rabs (An N)) (Rabs ((An n) - (An N))) 1).
apply (Rabs_triang_inv (An n) (An N)).
apply (Rlt_le (Rabs (An n - An N)) 1).
apply (H2 n N).
apply H9.
apply (le_n N).
apply (Rmax_r ma (Rabs (An N) + 1)).
move=> H9.
apply (Rle_trans (Rabs (An n)) ma (Rmax ma (Rabs (An N) + 1))).
apply ((proj2 H4) (Rabs (An n))).
exists n.
apply conj.
by [].
apply (le_trans n (S n) N).
apply (le_S n n).
apply (le_n n).
apply H9.
apply (Rmax_l ma (Rabs (An N) + 1)).
apply (Inhabited_intro R (fun x : R => exists n0 : nat, Rabs (An n0) = x /\ (n0 <= N)%nat) (Rabs (An N))).
exists N.
by [].
suff: (Im nat R (fun x : nat => (x < (S N))%nat) (fun n : nat => (Rabs (An n)))) = (fun x : R => exists n0 : nat, Rabs (An n0) = x /\ (n0 <= N)%nat).
move=> H3.
rewrite - H3.
apply (finite_image nat R (fun x : nat => (x < (S N))%nat) (fun n : nat => (Rabs (An n)))).
apply (cardinal_finite nat (fun x : nat => (x < S N)%nat) (S N)).
apply (nat_cardinal (S N)).
apply (Extensionality_Ensembles R (Im nat R (fun x : nat => (x < S N)%nat) (fun n : nat => (Rabs (An n)))) (fun x : R => exists n0 : nat, Rabs (An n0) = x /\ (n0 <= N)%nat)).
apply conj.
move=> x.
elim.
move=> n0 H3.
move=> y H4.
rewrite H4.
exists n0.
apply conj.
by [].
apply (le_S_n n0 N).
apply H3.
move=> x.
elim.
move=> n0 H3.
apply (Im_intro nat R (fun x : nat => (x < S N)%nat) (fun n : nat => Rabs (An n)) n0).
apply (le_n_S n0 N).
apply (proj2 H3).
rewrite (proj1 H3).
by [].
Qed.

Lemma Proposition_3_5_2 : forall An : (nat -> R), (Cauchy_crit An) -> forall (Bn : nat -> R), ((Subsequence R Bn An) -> (forall a : R, (Un_cv Bn a) -> (Un_cv An a))).
Proof.
move=> An H1 Bn H2 a H3.
elim H2.
move=> F H4.
move=> eps H5.
suff: eps * / 2 > 0.
move=> H6.
elim (H1 (eps * / 2) H6).
move=> N H7.
elim (H3 (eps * / 2) H6).
move=> M H8.
exists (max N M).
move=> n H9.
apply (Rle_lt_trans (R_dist (An n) a) ((R_dist (An n) (Bn n)) + (R_dist (Bn n) a)) eps).
apply (R_dist_tri (An n) a (Bn n)).
rewrite - (eps2 eps).
apply (Rplus_lt_compat (R_dist (An n) (Bn n)) (eps * / 2) (R_dist (Bn n) a) (eps * / 2)).
rewrite (proj2 H4 n).
apply H7.
apply (le_trans N (max N M) n).
apply (Nat.le_max_l N M).
apply H9.
apply (le_trans N n (F n)).
apply (le_trans N (max N M) n).
apply (Nat.le_max_l N M).
apply H9.
apply (Formula_3_17 F (proj1 H4) n).
apply (H8 n).
apply (le_trans M (max N M) n).
apply (Nat.le_max_r N M).
apply H9.
apply (eps2_Rgt_R0 eps H5).
Qed.

Lemma Theorem_3_6 : forall (An : nat -> R), (exists a : R, Un_cv An a) <-> (Cauchy_crit An).
Proof.
move=> An.
apply conj.
elim.
move=> a H1.
move=> eps H2.
elim (H1 (eps * / 2)).
move=> N H3.
exists N.
move=> n m H4 H5.
apply (Rle_lt_trans (R_dist (An n) (An m)) ((R_dist (An n) a) + (R_dist (An m) a)) eps).
rewrite (R_dist_sym (An m) a).
apply (R_dist_tri (An n) (An m) a).
rewrite - (eps2 eps).
apply (Rplus_lt_compat (R_dist (An n) a) (eps * / 2) (R_dist (An m) a) (eps * / 2)).
apply (H3 n H4).
apply (H3 m H5).
apply (eps2_Rgt_R0 eps H2).
move=> H1.
suff: exists (Bn : nat -> R), ((Subsequence R Bn An) /\ (exists x : R, Un_cv Bn x)).
elim.
move=> Bn H2.
elim (proj2 H2).
move=> a H3.
exists a.
apply (Proposition_3_5_2 An H1 Bn (proj1 H2) a H3).
apply (Theorem_3_4 An).
suff: (Im nat R (Full_set nat) An) = (fun x:R => (EUn An x)).
move=> H2.
rewrite H2.
apply (Proposition_3_5_1 An H1).
apply (Extensionality_Ensembles R (Im nat R (Full_set nat) An) (fun x : R => EUn An x)).
apply conj.
move=> x H2.
elim H2.
move=> n H3 y H4.
exists n.
apply H4.
move=> x H2.
elim H2.
move=> n H3.
apply (Im_intro nat R (Full_set nat) An n).
apply (Full_intro nat n).
apply H3.
Qed.

Lemma Theorem_3_7 : forall r : R, exists! n:Z , (IZR n) <= r < (IZR (n+1)%Z).
Proof.
suff: forall r : R, r > 0 -> exists n:nat, INR n <= r < INR (n+1).
move=> H1 r.
apply (proj1 (unique_existence (fun (n:Z) => IZR n <= r < IZR (n + 1)))).
apply conj.
elim (Formula_3_7 (-r)).
move=> a H2.
suff: INR a + r > 0.
move=> H3.
elim (H1 (INR a + r) H3).
move => n H4.
exists (Z.of_nat n - Z.of_nat a)%Z.
rewrite (plus_IZR (Z.of_nat n - Z.of_nat a) 1).
rewrite (minus_IZR (Z.of_nat n) (Z.of_nat a)).
rewrite - (INR_IZR_INZ n).
rewrite - (INR_IZR_INZ a).
apply conj.
rewrite - (Rplus_0_r r).
rewrite - (Rplus_opp_r (INR a)).
rewrite - (Rplus_assoc r (INR a) (- INR a)).
apply (Rplus_le_compat_r (- INR a) (INR n) (r + INR a)).
rewrite (Rplus_comm r (INR a)).
apply (proj1 H4).
rewrite (Rplus_assoc (INR n) (- INR a) 1).
rewrite (Rplus_comm (- INR a) 1).
rewrite - (Rplus_assoc (INR n) 1 (- INR a)).
rewrite - (Rplus_0_r r).
rewrite - (Rplus_opp_r (INR a)).
rewrite - (Rplus_assoc r (INR a) (- INR a)).
apply (Rplus_lt_compat_r (- INR a) (r + INR a) (INR n + 1)).
rewrite (Rplus_comm r (INR a)).
suff: INR n + 1 = INR (n + 1).
move=> H5.
rewrite H5.
apply (proj2 H4).
suff: (S n) = (n + 1)%nat.
move=> H5.
rewrite - H5.
rewrite (S_INR n).
by [].
rewrite - (plus_Snm_nSm n 0).
by [].
rewrite - (Rplus_opp_l r).
apply (Rplus_gt_compat_r r (INR a) (- r)).
apply (H2 a).
by [].
move => n m H2 H3.
apply (Z.le_antisymm n m).
apply (Zlt_succ_le n m).
apply (lt_IZR n (Z.succ m)).
apply (Rle_lt_trans (IZR n) r (IZR (Z.succ m))).
apply (proj1 H2).
apply (proj2 H3).
apply (Zlt_succ_le m n).
apply (lt_IZR m (Z.succ n)).
apply (Rle_lt_trans (IZR m) r (IZR (Z.succ n))).
apply (proj1 H3).
apply (proj2 H2).
move=> r H1.
elim (Exist_min_nat (fun (n : nat) => r < INR n)).
move=> n.
elim.
elim n.
move=> H2 H3.
apply False_ind.
apply (Rle_not_lt 0 r).
apply (Rlt_le r 0).
apply H2.
apply H1.
move=> n0 H2 H3 H4.
exists n0.
apply conj.
apply (Rnot_lt_le r (INR n0)).
move=> H5.
apply (lt_not_le n0 (S n0)).
by [].
apply (H4 n0).
apply H5.
rewrite - (plus_Snm_nSm n0 0).
rewrite (Nat.add_0_r (S n0)).
apply H3.
elim (Formula_3_7 r).
move=> n H2.
apply (Inhabited_intro nat (fun n0 : nat => r < INR n0) n).
apply (H2 n).
by [].
Qed.

Definition Floor (r : R) := proj1_sig (constructive_definite_description (fun n : Z => (IZR n) <= r < (IZR (n+1)%Z)) (Theorem_3_7 r)).

Lemma Floor_inequality : forall (r : R), (IZR (Floor r)) <= r < (IZR ((Floor r)+1)%Z).
Proof.
move=> r.
apply (proj2_sig (constructive_definite_description (fun n : Z => (IZR n) <= r < (IZR (n+1)%Z)) (Theorem_3_7 r))).
Qed.

Lemma Floor_unique : forall (r : R), forall (n : Z), (IZR n) <= r < (IZR (n+1)%Z) -> n = (Floor r).
Proof.
move=> r n H1.
suff: uniqueness (fun (n:Z) => IZR n <= r < IZR (n + 1)).
move=> H2.
apply H2.
apply H1.
apply (Floor_inequality r).
apply (proj2 (proj2 (unique_existence (fun (n:Z) => IZR n <= r < IZR (n + 1))) (Theorem_3_7 r))).
Qed.

Lemma Floor_add_Z_r : forall (r : R), forall (n : Z), (Floor (r + IZR n)) = ((Floor r) + n)%Z.
Proof.
move=> r n.
suff: (Floor r + n)%Z = Floor (r + IZR n).
move=> H1.
rewrite H1.
by [].
apply (Floor_unique (r + IZR n) (Floor r + n)%Z).
apply conj.
rewrite (plus_IZR (Floor r) n).
apply (Rplus_le_compat_r (IZR n) (IZR (Floor r)) r).
apply (proj1 (Floor_inequality r)).
rewrite - (Z.add_assoc (Floor r) n 1).
rewrite (Z.add_comm n 1).
rewrite (Z.add_assoc (Floor r) 1 n).
rewrite (plus_IZR (Floor r + 1) n).
apply (Rplus_lt_compat_r (IZR n) r (IZR (Floor r + 1))).
apply (proj2 (Floor_inequality r)).
Qed.

Definition RQ : (Ensemble R) := (fun x:R => exists q:Q, QArith.Qreals.Q2R q = x).

Lemma Theorem_3_8 : forall (a b : R),(a < b)%R -> exists (x : Q), a < (QArith.Qreals.Q2R x) < b.
Proof.
move=> a b H1.
elim (Theorem_3_2 (b - a) 1).
elim.
move=> H2.
apply False_ind.
apply (Rgt_not_ge (INR O * (b - a)) 1).
rewrite (Rmult_0_l (b - a)).
apply Rlt_0_1.
apply (Rgt_ge (INR 0 * (b - a)) 1 H2).
move=> n H2.
move=> H3.
exists ((inject_Z (Floor (INR (S n) * a + 1))) / (inject_Z(Z.of_nat (S n))))%Q.
rewrite (Qreals.Q2R_div (inject_Z (Floor (INR (S n) * a + 1))) (inject_Z (Z.of_nat (S n)))).
suff: forall (m : Z), (Qreals.Q2R (inject_Z m)) = (IZR m).
move=> H4.
suff: (Qreals.Q2R (inject_Z (Z.of_nat (S n)))) = (INR (S n)).
move=> H5.
suff: Qreals.Q2R (inject_Z (Z.of_nat (S n))) > 0.
move=> H6.
apply conj.
rewrite - {1}(Rmult_1_r a).
rewrite - {1}(Rinv_r (Qreals.Q2R (inject_Z (Z.of_nat (S n))))).
rewrite - (Rmult_assoc a (Qreals.Q2R (inject_Z (Z.of_nat (S n)))) (/ Qreals.Q2R (inject_Z (Z.of_nat (S n))))).
apply (Rmult_lt_compat_r (/ Qreals.Q2R (inject_Z (Z.of_nat (S n)))) (a * Qreals.Q2R (inject_Z (Z.of_nat (S n)))) (Qreals.Q2R (inject_Z (Floor (INR (S n) * a + 1))))).
apply (Rinv_0_lt_compat (Qreals.Q2R (inject_Z (Z.of_nat (S n)))) H6).
rewrite H5.
rewrite (H4 (Floor (INR (S n) * a + 1))).
rewrite (Rmult_comm a (INR (S n))).
rewrite (Floor_add_Z_r (INR (S n) * a) 1).
apply (proj2 (Floor_inequality (INR (S n) * a))).
apply (Rgt_not_eq (Qreals.Q2R (inject_Z (Z.of_nat (S n)))) 0 H6).
rewrite - (Rmult_1_r b).
rewrite - {2}(Rinv_r (Qreals.Q2R (inject_Z (Z.of_nat (S n))))).
rewrite - (Rmult_assoc b (Qreals.Q2R (inject_Z (Z.of_nat (S n)))) (/ Qreals.Q2R (inject_Z (Z.of_nat (S n))))).
apply (Rmult_lt_compat_r (/ Qreals.Q2R (inject_Z (Z.of_nat (S n)))) (Qreals.Q2R (inject_Z (Floor (INR (S n) * a + 1)))) (b * Qreals.Q2R (inject_Z (Z.of_nat (S n))))).
apply (Rinv_0_lt_compat (Qreals.Q2R (inject_Z (Z.of_nat (S n)))) H6).
rewrite H5.
rewrite (H4 (Floor (INR (S n) * a + 1))).
apply (Rle_lt_trans (IZR (Floor (INR (S n) * a + 1))) (INR (S n) * a + 1) (b * INR (S n))).
apply (proj1 (Floor_inequality (INR (S n) * a + 1))).
rewrite (Rmult_comm b (INR (S n))).
rewrite - (Rplus_0_r ((INR (S n)) * b)).
rewrite (Rplus_comm (INR (S n) * a) 1).
rewrite - (Rplus_opp_l (INR (S n) * a)).
rewrite - (Rplus_assoc (INR (S n) * b) (- (INR (S n) * a)) (INR (S n) * a)).
apply (Rplus_lt_compat_r (INR (S n) * a) 1 (INR (S n) * b + - (INR (S n) * a))).
rewrite (Ropp_mult_distr_r (INR (S n)) a).
rewrite - (Rmult_plus_distr_l (INR (S n)) b (- a)).
apply H3.
apply (Rgt_not_eq (Qreals.Q2R (inject_Z (Z.of_nat (S n)))) 0 H6).
rewrite /inject_Z.
rewrite /Qreals.Q2R.
simpl.
apply (Rmult_gt_0_compat (IZR (Z.pos (Pos.of_succ_nat n))) (/ 1)).
simpl.
apply (IZR_lt 0 (Z.pos (Pos.of_succ_nat n))).
by [].
rewrite Rinv_1.
apply (Rlt_0_1).
rewrite /inject_Z.
rewrite /Qreals.Q2R.
rewrite /Qnum.
rewrite /Qden.
rewrite (INR_IZR_INZ (S n)).
rewrite Rinv_1.
apply (Rmult_1_r (IZR (Z.of_nat (S n)))).
move=> m.
rewrite /inject_Z.
rewrite /Qreals.Q2R.
rewrite /Qnum.
rewrite /Qden.
rewrite Rinv_1.
apply (Rmult_1_r (IZR m)).
by [].
apply (Rlt_Rminus a b H1).
apply Rlt_0_1.
Qed.

Lemma Theorem_3_9_sub : forall m : nat, (m > S O)%nat -> (forall x : R, exists (an : (nat -> {num : nat | (num < m) % nat})), let An := fun n : nat => (match n with
  | O => (IZR (Floor x))
  | S n1 => INR (proj1_sig (an n1)) / (pow (INR m) (S n1))
end) in (Un_cv (fun n : nat => (sum_f_R0 An n)) x)).
Proof.
move=> m H1 x.
suff: let Bn := fix Bn (n : nat) : (R * Z) := match n with
  | O => (x - IZR (Floor x) , 0%Z)
  | S n1 => (((fst (Bn n1)) * (INR m)) - IZR (Floor (((fst (Bn n1)) * (INR m)))) , Floor ((fst (Bn n1)) * (INR m)))
end in exists an : nat -> {num : nat | (num < m)%nat}, let An := fun n : nat => match n with
  | 0%nat => IZR (Floor x)
  | S n1 => INR (proj1_sig (an n1)) / INR m ^ S n1
end in Un_cv (fun n : nat => sum_f_R0 An n) x.
by [].
move=> Bn.
suff: forall n : nat, (0 <= (fst (Bn n)) < 1).
move=> H2.
suff: forall n : nat, (0%Z <= (snd (Bn n)))%Z.
move=> H3.
suff: forall n : nat, ((Z.to_nat (snd (Bn n))) < m)%nat.
move=> H4.
exists (fun n : nat => exist (fun num : nat => (num < m)%nat) (Z.to_nat (snd (Bn (S n)))) (H4 (S n))).
move=> An.
suff: forall n : nat, (x - (sum_f_R0 An n)) = (fst (Bn n)) / (pow (INR m) n).
move=> H5.
suff: forall n : nat, 0 <= x - (sum_f_R0 An n) < 1 / (pow (INR m) n).
move=> H6.
apply (Proposition_2_7 (fun n : nat => x - (1 / (pow 2 n))) (fun n : nat => x) x).
rewrite - {2}(Rplus_0_r x).
rewrite - Ropp_0.
apply (Theorem_2_5_1_minus (fun n : nat => x) (fun n : nat => 1 / 2 ^ n) x 0).
move=> eps H7.
exists O.
move=> n H8.
rewrite (R_dist_eq x).
apply H7.
apply Formula_3_9_2.
move=> eps H7.
exists O.
move=> n H8.
rewrite (R_dist_eq x).
apply H7.
suff: forall n : nat, (pow 2 n) <= (pow (INR m) n).
move => H7.
move=> n.
apply conj.
apply (Rle_trans (x - 1 / 2 ^ n) (x - 1 / (INR m) ^ n) (sum_f_R0 An n)).
apply (Rplus_le_compat_l x (- (1 / 2 ^ n)) (- (1 / INR m ^ n))).
apply (Ropp_ge_le_contravar (1 / (pow 2 n)) (1 / (pow (INR m) n))).
rewrite /Rdiv.
rewrite (Rmult_1_l (/ (pow 2 n))).
rewrite (Rmult_1_l (/ (pow (INR m) n))).
apply (Rle_ge (/ (pow (INR m) n)) (/ (pow 2 n))).
apply (Rinv_le_contravar (pow 2 n) (pow (INR m) n)).
apply (Two_Pow_Gt_Zero n).
elim n.
by [].
move=> n0 H8.
simpl.
apply (Rle_trans (2 * 2 ^ n0) (2 * INR m ^ n0) (INR m * INR m ^ n0)).
apply (Rmult_le_compat_l 2 (2 ^ n0) (INR m ^ n0)).
apply (Rlt_le 0 2).
apply Two_Gt_Zero.
apply H8.
apply (Rmult_le_compat_r (INR m ^ n0) 2 (INR m)).
apply (Rle_trans 0 (2 ^ n0) (INR m ^ n0)).
apply (Rlt_le 0 (2 ^ n0)).
apply (Two_Pow_Gt_Zero n0).
apply H8.
rewrite /2.
rewrite - (INR_IPR 2).
apply (le_INR (Pos.to_nat 2) m).
suff: (S 1) = (Pos.to_nat 2).
move=> H9.
rewrite - H9.
apply H1.
by [].
apply (Rlt_le (x - 1 / INR m ^ n) (sum_f_R0 An n)).
apply (Rplus_lt_reg_r (1 / INR m ^ n) (x - 1 / INR m ^ n) (sum_f_R0 An n)).
rewrite (Rplus_assoc x (- (1 / INR m ^ n)) (1 / INR m ^ n)).
rewrite (Rplus_opp_l (1 / INR m ^ n)).
rewrite (Rplus_0_r x).
apply (Rplus_lt_reg_l (- (sum_f_R0 An n)) x (sum_f_R0 An n + 1 / INR m ^ n)).
rewrite - (Rplus_assoc (- sum_f_R0 An n) (sum_f_R0 An n) (1 / INR m ^ n)).
rewrite (Rplus_opp_l (sum_f_R0 An n)).
rewrite (Rplus_0_l (1 / INR m ^ n)).
rewrite (Rplus_comm (- sum_f_R0 An n) x).
apply (proj2 (H6 n)).
apply (Rge_le x (sum_f_R0 An n)).
apply (Rminus_ge x (sum_f_R0 An n)).
apply (Rle_ge 0 (x - sum_f_R0 An n)).
apply (proj1 (H6 n)).
elim.
simpl.
apply (Req_le 1 1).
by [].
move=> n0 H7.
simpl.
apply (Rle_trans (2 * 2 ^ n0) (2 * INR m ^ n0) (INR m * INR m ^ n0)).
apply (Rmult_le_compat_l 2 (2 ^ n0) (INR m ^ n0)).
apply (Rlt_le 0 2).
apply Two_Gt_Zero.
apply H7.
apply (Rmult_le_compat_r (INR m ^ n0) 2 (INR m)).
apply (Rle_trans 0 (2 ^ n0) (INR m ^ n0)).
apply (Rlt_le 0 (2 ^ n0)).
apply (Two_Pow_Gt_Zero n0).
apply H7.
rewrite /2.
rewrite - (INR_IPR 2).
apply (le_INR (Pos.to_nat 2) m).
suff: (S 1) = (Pos.to_nat 2).
move=> H9.
rewrite - H9.
apply H1.
by [].
suff: forall n:nat, INR m ^ n > 0.
move=> H6.
move=> n.
rewrite (H5 n).
apply conj.
rewrite - (Rmult_0_r 0).
apply (Rmult_le_compat 0 (fst (Bn n)) 0 (/ INR m ^ n)).
apply (Req_le 0 0).
by [].
apply (Req_le 0 0).
by [].
apply (proj1 (H2 n)).
apply (Rlt_le 0 (/ INR m ^ n)).
apply (Rinv_0_lt_compat (INR m ^ n)).
apply (H6 n).
apply (Rmult_lt_compat_r (/ INR m ^ n) (fst (Bn n)) 1).
apply (Rinv_0_lt_compat (INR m ^ n)).
apply (H6 n).
apply (proj2 (H2 n)).
elim.
simpl.
apply (Rlt_0_1).
move=> n H6.
simpl.
apply (Rmult_gt_0_compat (INR m) (INR m ^ n)).
apply (lt_0_INR m).
apply (le_trans (S O) (S (S O)) m).
apply (le_S (S 0)).
apply (le_n (S 0)).
apply H1.
apply H6.
elim.
simpl.
rewrite /Rdiv.
rewrite Rinv_1.
rewrite (Rmult_1_r (x - IZR (Floor x))).
by [].
suff: forall n:nat, (INR m ^ n) <> 0.
move=> H5 n H6.
simpl.
rewrite /Rminus.
rewrite (Ropp_plus_distr (sum_f_R0 An n) (INR (Z.to_nat (snd (Bn (S n)))) / (INR m * INR m ^ n))).
rewrite - (Rplus_assoc x (- sum_f_R0 An n) (- (INR (Z.to_nat (snd (Bn (S n)))) / (INR m * INR m ^ n)))).
rewrite /Rminus in H6.
rewrite H6.
apply (Rmult_eq_reg_r (INR m * INR m ^ n) (fst (Bn n) / INR m ^ n + - (INR (Z.to_nat (snd (Bn (S n)))) / (INR m * INR m ^ n))) ((fst (Bn n) * INR m + - IZR (Floor (fst (Bn n) * INR m))) / (INR m * INR m ^ n))).
rewrite /Rdiv.
rewrite (Rmult_assoc ((fst (Bn n) * INR m + - IZR (Floor (fst (Bn n) * INR m)))) (/ (INR m * INR m ^ n)) (INR m * INR m ^ n)).
rewrite - (Rinv_l_sym (INR m * INR m ^ n)).
rewrite (Rmult_1_r (fst (Bn n) * INR m + - IZR (Floor (fst (Bn n) * INR m)))).
rewrite (Rmult_plus_distr_r (fst (Bn n) * / INR m ^ n) (- (INR (Z.to_nat (snd (Bn (S n)))) * / (INR m * INR m ^ n))) (INR m * INR m ^ n)).
rewrite (Ropp_mult_distr_l (INR (Z.to_nat (snd (Bn (S n))))) (/ (INR m * INR m ^ n))).
rewrite (Rmult_assoc ((- INR (Z.to_nat (snd (Bn (S n)))))) (/ (INR m * INR m ^ n)) (INR m * INR m ^ n)).
rewrite - (Rinv_l_sym (INR m * INR m ^ n)).
rewrite (Rmult_1_r (- INR (Z.to_nat (snd (Bn (S n)))))).
rewrite (Rmult_assoc (fst (Bn n)) (/ INR m ^ n) (INR m * INR m ^ n)).
rewrite (Rmult_comm (/ INR m ^ n) (INR m * INR m ^ n)).
rewrite (Rmult_assoc (INR m) (INR m ^ n) (/ INR m ^ n)).
rewrite - (Rinv_r_sym (INR m ^ n)).
rewrite (Rmult_1_r (INR m)).
rewrite (INR_IZR_INZ (Z.to_nat (snd (Bn (S n))))).
rewrite (Z2Nat.id (snd (Bn (S n)))).
by [].
apply (H3 (S n)).
apply (H5 n).
apply (H5 (S n)).
apply (H5 (S n)).
apply (H5 (S n)).
elim.
simpl.
apply (Rgt_not_eq 1 0).
apply (Rlt_0_1).
move=> n H5.
apply (Rmult_integral_contrapositive (INR m) (INR m ^ n)).
apply conj.
apply (Rgt_not_eq (INR m) 0).
apply (lt_0_INR m).
apply (le_trans (S O) (S (S O)) m).
apply (le_S (S 0)).
apply (le_n (S 0)).
apply H1.
apply H5.
elim.
simpl.
apply (le_trans 1 2 m).
apply (le_S (S 0)).
apply (le_n (S 0)).
apply H1.
move=> n H4.
apply (INR_lt (Z.to_nat (snd (Bn (S n)))) m).
rewrite (INR_IZR_INZ (Z.to_nat (snd (Bn (S n))))).
rewrite (Z2Nat.id (snd (Bn (S n)))).
apply (Rle_lt_trans (IZR (snd (Bn (S n)))) (fst (Bn n) * INR m) (INR m)).
apply (proj1 (Floor_inequality (fst (Bn n) * INR m))).
rewrite - {2}(Rmult_1_l (INR m)).
apply (Rmult_lt_compat_r (INR m) (fst (Bn n)) 1).
apply (lt_0_INR m).
apply (le_trans (S O) (S (S O)) m).
apply (le_S (S 0)).
apply (le_n (S 0)).
apply H1.
apply (proj2 (H2 n)).
apply (H3 (S n)).
elim.
by [].
move=> n H3.
apply (Znot_gt_le 0 (snd (Bn (S n)))).
move=> H4.
apply (Rle_not_lt (fst (Bn n)) 0).
apply (proj1 (H2 n)).
apply (Rmult_lt_reg_r (INR m) (fst (Bn n)) 0).
apply (lt_0_INR m).
apply (le_trans (S O) (S (S O)) m).
apply (le_S (S 0)).
apply (le_n (S 0)).
apply H1.
rewrite (Rmult_0_l (INR m)).
apply (Rlt_le_trans (fst (Bn n) * INR m) (IZR ((Floor (fst (Bn n) * INR m)) + 1)) 0).
apply (proj2 (Floor_inequality (fst (Bn n) * INR m))).
apply (IZR_le (Floor (fst (Bn n) * INR m) + 1) 0%Z).
apply (Zlt_le_succ (Floor (fst (Bn n) * INR m)) 0%Z).
apply (Z.gt_lt_iff 0%Z (Floor (fst (Bn n) * INR m))).
apply H4.
suff: forall y : R, 0 <= y - IZR (Floor y) < 1.
move=> H2.
elim.
apply (H2 x).
move=> n H3.
apply (H2 (fst (Bn n) * INR m)).
move=> y.
apply conj.
rewrite - (Rplus_opp_r (IZR (Floor y))).
apply (Rplus_le_compat_r (- IZR (Floor y)) (IZR (Floor y)) y).
apply (proj1 (Floor_inequality y)).
rewrite - (Rplus_0_r 1).
rewrite - (Rplus_opp_r (IZR (Floor y))).
rewrite - (Rplus_assoc 1 (IZR (Floor y)) (- IZR (Floor y))).
apply (Rplus_lt_compat_r (- IZR (Floor y)) y (1 + IZR (Floor y))).
rewrite (Rplus_comm 1 (IZR (Floor y))).
rewrite - (plus_IZR (Floor y) 1).
apply (proj2 (Floor_inequality y)).
Qed.

Lemma Theorem_3_9 : forall x : R, exists (an : (nat -> {num : nat | (num < 10) % nat})), let An := fun n : nat => (match n with
  | O => (IZR (Floor x))
  | S n1 => INR (proj1_sig (an n1)) / (pow 10 (S n1))
end) in (Un_cv (fun n : nat => (sum_f_R0 An n)) x).
Proof.
suff: 10 = (INR 10).
move=> H1.
rewrite H1.
apply (Theorem_3_9_sub 10%nat).
apply (le_S 2 9).
apply (le_S 2 8).
apply (le_S 2 7).
apply (le_S 2 6).
apply (le_S 2 5).
apply (le_S 2 4).
apply (le_S 2 3).
apply (le_S 2 2).
apply (le_n 2).
rewrite (INR_IZR_INZ 10).
by [].
Qed.

Lemma Q_Un_cv_R : forall x : R, exists (an : (nat -> {q : R | RQ q})), Un_cv (fun n : nat => proj1_sig (an n)) x.
Proof.
move=> x.
suff: ((S (S O)) > (S O))%nat.
move=> H1.
elim (Theorem_3_9_sub 2 H1 x).
move=> bn H2.
suff: let An := fun n : nat => match n with
  | 0%nat => IZR (Floor x)
  | S n1 => INR (proj1_sig (bn n1)) / INR 2 ^ S n1
end in exists an : nat -> {q : R | RQ q}, Un_cv (fun n : nat => proj1_sig (an n)) x.
by [].
move=> An.
suff: forall n:nat, (RQ (sum_f_R0 An n)).
move=> H3.
exists (fun n : nat => (exist RQ (sum_f_R0 An n) (H3 n))).
apply H2.
suff: forall (y z : R), (RQ y) -> (RQ z) -> (RQ (y + z)).
move=> H3.
suff: forall (y z : R), (RQ y) -> (RQ z) -> z <> 0 -> (RQ (y / z)).
move=> H4.
suff: forall (n : nat), IZR (Z.of_nat (2 ^ n)) = 2 ^ n.
move=> H5.
elim.
simpl.
(exists (inject_Z (Floor x))).
rewrite /Qreals.Q2R.
simpl.
rewrite (Rinv_1).
apply (Rmult_1_r (IZR (Floor x))).
move=> n H6.
apply (H3 (sum_f_R0 An n) (INR (proj1_sig (bn n)) / 2 ^ (S n))).
apply H6.
apply (H4 (INR (proj1_sig (bn n))) (2 ^ S n)).
exists ((inject_Z (Z.of_nat (proj1_sig (bn n))))).
rewrite (INR_IZR_INZ (proj1_sig (bn n))).
rewrite /Qreals.Q2R.
simpl.
rewrite (Rinv_1).
apply (Rmult_1_r (IZR (Z.of_nat (proj1_sig (bn n))))).
exists ((inject_Z (Z.of_nat (2 ^ S n)))).
rewrite /Qreals.Q2R.
rewrite (Rinv_1).
rewrite /inject_Z.
rewrite /Qnum.
rewrite (Rmult_1_r (IZR (Z.of_nat (2 ^ S n)))).
apply (H5 (S n)).
apply (Two_Pow_Neq_Zero (S n)).
elim.
by [].
move=> n H5.
simpl.
rewrite (plus_0_r (2 ^ n)).
rewrite (Nat2Z.inj_add (2 ^ n) (2 ^ n)).
rewrite (plus_IZR (Z.of_nat (2 ^ n)) (Z.of_nat (2 ^ n))).
rewrite (RIneq.double (2 ^ n)).
rewrite H5.
by [].
move=> y z H4 H5 H6.
elim H4.
move=> yq H7.
elim H5.
move=> zq H8.
exists (yq / zq)%Q.
rewrite (Qreals.Q2R_div yq zq).
rewrite H7.
rewrite H8.
by [].
simpl.
move=> H9.
apply H6.
rewrite - H8.
rewrite (Qreals.Qeq_eqR zq 0).
rewrite /Qreals.Q2R.
simpl.
apply (Rmult_0_l (/ 1)).
apply H9.
move=> y z H3 H4.
elim H3.
move=> yq H5.
elim H4.
move=> zq H6.
rewrite - H5.
rewrite - H6.
rewrite - (Qreals.Q2R_plus yq zq).
exists (yq + zq)%Q.
by [].
apply (le_n 2).
Qed.
