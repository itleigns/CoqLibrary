From mathcomp
Require Import ssreflect.
Require Import Reals.
Require Import Coq.Sets.Ensembles.
Local Open Scope R_scope.
Require Export Rdefinitions.
Require Import Classical.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Image.
Require Import ChoiceFacts.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Logic.ProofIrrelevanceFacts.

Lemma sig_map : forall {T : Type} (P : T -> Prop) (x : {x : T | P x}) (y : {x : T | P x}),
proj1_sig x = proj1_sig y -> x = y.
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

Section Kaisekinyuumonn.

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

Definition is_max :=
fun (E : (Ensemble R)) (m : R) => (In R E m) /\ forall x : R, (In R E x) -> x <= m.

Definition is_min :=
fun (E : (Ensemble R)) (m : R) => (In R E m) /\ forall x : R, (In R E x) -> x >= m.

Definition my_lower_bound : Ensemble R -> Ensemble R :=
fun (E : (Ensemble R)) => (fun (m : R) => forall x : R, (In R E x) -> x >= m).

Definition my_lower_bounded : Ensemble R -> Prop :=
fun x => (Inhabited R (my_lower_bound x)).

Definition my_upper_bound : Ensemble R -> Ensemble R :=
fun (E : (Ensemble R)) => (fun (m : R) => forall x : R, (In R E x) -> x <= m).

Definition my_upper_bounded : Ensemble R -> Prop :=
fun x => (Inhabited R (my_upper_bound x)).

Definition my_bounded : Ensemble R -> Prop :=
fun x => (Inhabited R (my_upper_bound x)) /\ (Inhabited R (my_lower_bound x)).

Lemma bounded_abs : forall A : Ensemble R , (my_bounded A) <-> (my_upper_bounded (Image.Im R R A Rabs)).
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

Definition my_abs (r : R) : R := 
  let (a,_) := R_R_exist_max r (- r) in a.

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
move=> r.
rewrite /Rabs.
case (Rcase_abs r).
move=> H1.
apply ((proj2 Formula_1_7) r (Rlt_le r 0 H1)).
apply ((proj1 Formula_1_7) r).
Qed.

Lemma Formula_1_10 : (forall A : (Ensemble R) ,forall  r1 r2 : R, (In R (my_upper_bound A) r1) -> (r1 <= r2) -> (In R (my_upper_bound A) r2))
 /\ (forall A : (Ensemble R) ,forall  r1 r2 : R, (In R (my_lower_bound A) r1) -> (r2 <= r1) -> (In R (my_lower_bound A) r2)).
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

Definition is_greatest_lower_bound := 
fun (E : (Ensemble R)) (m : R) => (is_max (my_lower_bound E) m). 

Definition is_least_upper_bound := 
fun (E : (Ensemble R)) (m : R) => (is_min (my_upper_bound E) m).

Lemma Proposition_1_3 : (forall (A : (Ensemble R)) (m : R),((forall (a : R), (In R A a) -> a <= m) /\ (forall (x : R), x < m ->  (exists (a : R), (In R A a) /\ x < a)) <-> (is_least_upper_bound A m)))
 /\ (forall (A : (Ensemble R)) (m : R),((forall (a : R), (In R A a) -> a >= m) /\ (forall (x : R), x > m ->  (exists (a : R), (In R A a) /\ x > a)) <-> (is_greatest_lower_bound A m))).
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

Lemma Proposition_1_3_corollary : (forall (A : (Ensemble R)) (m : R), (is_max A m) -> (is_least_upper_bound A m)) /\ (forall (A : (Ensemble R)) (m : R), (is_min A m) -> (is_greatest_lower_bound A m)).
Proof.
apply conj.
move=> A m.
move=> H1.
apply conj.
rewrite /is_max in H1.
rewrite /In.
rewrite /my_upper_bound.
apply (proj2 H1).
move=> x.
move=> H2.
apply (Rle_ge m x).
apply (H2 m (proj1 H1)).
move=> A m.
move=> H1.
apply conj.
rewrite /is_min in H1.
rewrite /In.
rewrite /my_lower_bound.
apply (proj2 H1).
move=> x.
move=> H2.
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

Definition MinusER : Ensemble R -> Ensemble R :=
fun (E : (Ensemble R)) => (fun (x : R) => (In R E (- x))).

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

(* Prop 1 4 の前半は1つ前のLemmaに含まれている。*)
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

Definition PlusER : Ensemble R -> Ensemble R -> Ensemble R :=
fun (A B : (Ensemble R)) => (fun (x : R) => (exists (a b : R), (In R A a) /\ (In R B b) /\ x = a + b)).

Definition MultER : Ensemble R -> Ensemble R -> Ensemble R :=
fun (A B : (Ensemble R)) => (fun (x : R) => (exists (a b : R), (In R A a) /\ (In R B b) /\ x = a * b)).

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
rewrite (double 1).
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
rewrite (double 1).
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
rewrite (double 1).
apply (Rplus_lt_0_compat 1 1).
apply Rlt_0_1.
apply Rlt_0_1.
rewrite - {3}(Rplus_0_r a).
apply (Rplus_gt_compat_l a ((x - (a + b)) / 2) 0).
apply (Rdiv_lt_0_compat (x - (a + b)) 2).
apply (Rgt_minus x (a + b)).
apply H6.
rewrite - (Rmult_1_r 2).
rewrite (double 1).
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
apply ((proj1 Proposition_1_3_corollary) (MultER A B)).
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
apply ((proj1 Proposition_1_3_corollary) (MultER A B)).
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

Definition RN : (Ensemble R) := 
  (fun x:R => exists n:nat, INR n = x).

Fixpoint conv (n k:nat) : nat :=
  match k with
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
rewrite - (mult_assoc_reverse  (conv (S m) (S k0)) (fact (S k0) * fact (S m - S k0)) (S (m - k0))).
rewrite - (mult_assoc_reverse  (conv (S m) (S k0)) (fact (S k0)) (fact (S m - S k0))).
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
suff: forall n low high : nat,
(high >= low)%nat /\ (low >= n)%nat -> (high - n - (low - n) = high - low)%nat.
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
suff: (sigma
  (fun k : nat => (x + y) * (INR (conv n0 k) * x ^ k * y ^ (n0 - k)))
  0 n0) = (sigma
  (fun k : nat => (INR (conv n0 k) * x ^ (S k) * y ^ (n0 - k)))
  0 n0) + (sigma
  (fun k : nat => (INR (conv n0 k) * x ^ k * y ^ (S n0 - k)))
  0 n0).
move=> H3.
rewrite H3.
suff: sigma (fun k : nat => INR (conv n0 k) * x ^ S k * y ^ (n0 - k)) 0 n0 = sigma (fun k : nat => INR (conv n0 (k - 1)) * x ^ k * y ^ ((S n0 - k))) (S 0) (S n0).
move=> H4.
rewrite H4.
suff: sigma (fun k : nat => INR (conv n0 (k - 1)) * x ^ k * y ^ (S n0 - k)) 1 (S n0) = 
sigma (fun k : nat => match k with | O => 0
| S k => INR (conv n0 k) * x ^ (S k) * y ^ (n0 - k) end) 0
  (S n0).
move=> H5.
rewrite H5.
suff: sigma (fun k : nat => INR (conv n0 k) * x ^ k * y ^ (S n0 - k)) 0 n0 = sigma (fun k : nat => INR (conv n0 k) * x ^ k * y ^ S (n0 - k)) 0 (S n0).
move=> H6.
rewrite H6.
rewrite - (Sigma_Plus (fun k : nat =>
   match k with
   | 0%nat => 0
   | S k0 => INR (conv n0 k0) * x ^ S k0 * y ^ (n0 - k0)
   end) (fun k : nat => INR (conv n0 k) * x ^ k * y ^ S (n0 - k)) 0 (S n0)).
suff: forall k:nat, (k <= (S n0))%nat -> ((RSequencePlus
     (fun k : nat =>
      match k with
      | 0%nat => 0
      | S k0 => INR (conv n0 k0) * x ^ S k0 * y ^ (n0 - k0)
      end) (fun k : nat => INR (conv n0 k) * x ^ k * y ^ S (n0 - k))) k) = ((fun k : nat => INR (conv (S n0) k) * x ^ k * y ^ (S n0 - k)) k).
move=> H7.
apply (Sigma_Same (RSequencePlus
     (fun k : nat =>
      match k with
      | 0%nat => 0
      | S k0 => INR (conv n0 k0) * x ^ S k0 * y ^ (n0 - k0)
      end) (fun k : nat => INR (conv n0 k) * x ^ k * y ^ S (n0 - k))) (fun k : nat => INR (conv (S n0) k) * x ^ k * y ^ (S n0 - k))
0 (S n0)
).
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
rewrite (Rplus_0_l (sigma (fun k : nat => INR (conv n0 k) * x ^ k * (y * y ^ (n0 - k))) 0
  n0)).
rewrite (Sigma_Same (fun k : nat =>
   INR (conv n0 k) * x ^ k * y ^ match k with
                                 | 0 => S n0
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
rewrite ((sigma_first (fun k : nat =>
   match k with
   | 0%nat => 0
   | S k0 => INR (conv n0 k0) * x ^ S k0 * y ^ (n0 - k0)
   end)) 0%nat (S n0)).
rewrite (Rplus_0_l (sigma
  (fun k : nat =>
   match k with
   | 0%nat => 0
   | S k0 => INR (conv n0 k0) * x ^ S k0 * y ^ (n0 - k0)
   end) 1 (S n0))).
by [].
apply (le_n_S 0 n0).
apply (le_O_n n0).
rewrite (sigma_translation (fun k : nat => INR (conv n0 (k - 1)) * x ^ k * y ^ (S n0 - k)) 1 1 (S n0)).
simpl Nat.sub.
rewrite - (minus_n_O n0).
apply (Sigma_Same (fun k : nat => INR (conv n0 k) * x ^ S k * y ^ (n0 - k)) (fun k : nat =>
   INR (conv n0 (k + 1 - 1)) * x ^ (k + 1) *
   y ^ match (k + 1)%nat with
       | 0 => S n0
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
apply (Sigma_Same (fun k : nat => (x + y) * (INR (conv n0 k) * x ^ k * y ^ (n0 - k))) (RSequencePlus (fun k : nat => INR (conv n0 k) * x ^ S k * y ^ (n0 - k))
     (fun k : nat => INR (conv n0 k) * x ^ k * y ^ (S n0 - k))) 0 n0).
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

Definition is_max_nat :=
fun (E : (Ensemble nat)) (m : nat) => (In nat E m) /\ forall x : nat, (In nat E x) -> (x <= m)%nat.

Definition is_min_nat :=
fun (E : (Ensemble nat)) (m : nat) => (In nat E m) /\ forall x : nat, (In nat E x) -> (x >= m)%nat.

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
apply (Rplus_lt_compat (R_dist (An (Init.Nat.max n1 n2)) x)
(R_dist x y * / 2)
(R_dist (An (Init.Nat.max n1 n2)) y)
(R_dist x y * / 2)).
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
elim (Finite_max_R (fun x : R =>
        exists n0 : nat, An n0 = x /\ (n0 <= n)%nat) H4).
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
elim (Finite_min_R (fun x : R =>
        exists n0 : nat, An n0 = x /\ (n0 <= n)%nat) H4).
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
elim (H2 (eps * / 2 * / ((Rabs a)  + 1))).
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

Definition Un_inf : ((nat -> R) -> Prop) := fun Un : (nat -> R) => forall M:R,
      exists N : nat, (forall n:nat, (n >= N)%nat -> (Un n) > M).

Definition Un_minf : ((nat -> R) -> Prop) := fun Un : (nat -> R) => forall M:R,
      exists N : nat, (forall n:nat, (n >= N)%nat -> (Un n) < M).

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

Definition BoundedClosedSection : Ensemble (Ensemble R) := (Image.Im (R * R) (Ensemble R) (fun (x : (R * R)) => (fst x) <= (snd x)) (fun (x : (R * R)) => (fun (y : R) => (fst x) <= y <= (snd x)))).

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

Lemma BoundedClosedsectionUniqueRpair : forall (A : Ensemble R), (In (Ensemble R) BoundedClosedSection A) -> (exists! (x : (R * R)) , (fst x) <= (snd x) /\ A = (fun (y : R) => (fst x) <= y <= (snd x))).
Proof.
move=> A H1.
apply (proj1 (unique_existence (fun (x : R * R) => (fst x) <= (snd x) /\ A = (fun y : R => fst x <= y <= snd x)))).
apply conj.
elim H1.
move=> x H2 A0 H3.
exists x.
apply conj.
apply H2.
apply H3.
move=> x y H2 H3.
apply (injective_projections x y).
apply (Rle_antisym (fst x) (fst y)).
suff: (In R A (fst y)).
rewrite (proj2 H2).
move=> H4.
apply (proj1 H4).
rewrite (proj2 H3).
apply conj.
apply (Req_le (fst y) (fst y)).
by [].
apply (proj1 H3).
suff: (In R A (fst x)).
rewrite (proj2 H3).
move=> H4.
apply (proj1 H4).
rewrite (proj2 H2).
apply conj.
apply (Req_le (fst x) (fst x)).
by [].
apply (proj1 H2).
apply (Rle_antisym (snd x) (snd y)).
suff: (In R A (snd x)).
rewrite (proj2 H3).
move=> H4.
apply (proj2 H4).
rewrite (proj2 H2).
apply conj.
apply (proj1 H2).
apply (Req_le (snd x) (snd x)).
by [].
suff: (In R A (snd y)).
rewrite (proj2 H2).
move=> H4.
apply (proj2 H4).
rewrite (proj2 H3).
apply conj.
apply (proj1 H3).
apply (Req_le (snd y) (snd y)).
by [].
Qed.

Definition BoundedClosedsectionToRpair (I : Ensemble R) (H : In (Ensemble R) BoundedClosedSection I) : (R * R) 
:= proj1_sig (constructive_definite_description (fun (x : R * R) => fst x <= snd x /\ I = (fun y : R => fst x <= y <= snd x)) (BoundedClosedsectionUniqueRpair I H)).

Lemma BoundedClosedsectionIsRpair : forall (I : Ensemble R) (H : In (Ensemble R) BoundedClosedSection I), 
I = (fun x : R => (fst (BoundedClosedsectionToRpair I H)) <= x <= (snd (BoundedClosedsectionToRpair I H))).
Proof.
move=> I H.
rewrite /BoundedClosedsectionToRpair.
elim (constructive_definite_description
         (fun x0 : R * R =>
          fst x0 <= snd x0 /\
          I = (fun y : R => fst x0 <= y <= snd x0))
         (BoundedClosedsectionUniqueRpair I H)).
simpl.
move=> x H1.
apply (proj2 H1).
Qed.

Definition BoundedClosedsectionL (I : Ensemble R) (H : In (Ensemble R) BoundedClosedSection I) : R 
:= (fst (BoundedClosedsectionToRpair I H)).

Definition BoundedClosedsectionR (I : Ensemble R) (H : In (Ensemble R) BoundedClosedSection I) : R 
:= (snd (BoundedClosedsectionToRpair I H)).

Definition BoundedClosedsectionSize (I : Ensemble R) (H : In (Ensemble R) BoundedClosedSection I) : R 
:= (BoundedClosedsectionR I H) - (BoundedClosedsectionL I H).

Lemma BoundedClosedsectionDef : forall (a b : R), (a <= b) -> (In (Ensemble R) BoundedClosedSection (fun x : R => a <= x <= b)).
Proof.
move=> a b H1.
apply (Im_intro (R * R) (Ensemble R) (fun x : R * R => fst x <= snd x)
     (fun (x : R * R) (y : R) => fst x <= y <= snd x) (a,b)).
apply H1.
by [].
Qed.

Lemma BoundedClosedsectionLCalc : forall (a b : R) (H : a <= b)  (H1 : In (Ensemble R) BoundedClosedSection (fun x : R => a <= x <= b)), (BoundedClosedsectionL (fun x : R => a <= x <= b) H1) = a.
Proof.
move=> a b H1 H2.
rewrite /BoundedClosedsectionL.
rewrite /BoundedClosedsectionToRpair.
suff: let y := (constructive_definite_description
        (fun x : R * R =>
         fst x <= snd x /\
         (fun x0 : R => a <= x0 <= b) =
         (fun y : R => fst x <= y <= snd x))
        (BoundedClosedsectionUniqueRpair
           (fun x : R => a <= x <= b) H2)) in fst
  (proj1_sig y) = a.
by [].
case (constructive_definite_description
    (fun x : R * R =>
     fst x <= snd x /\
     (fun x0 : R => a <= x0 <= b) =
     (fun y : R => fst x <= y <= snd x))
    (BoundedClosedsectionUniqueRpair
       (fun x : R => a <= x <= b) H2)).
simpl.
move=> x.
move=> H3.
apply (Rle_antisym (fst x) a).
suff: (In R (fun y : R => fst x <= y <= snd x) a).
move=> H4.
apply H4.
rewrite - (proj2 H3).
apply conj.
apply (Req_le a a).
by [].
apply H1.
suff: (In R (fun y : R => a <= y <= b) (fst x)).
move=> H4.
apply H4.
rewrite (proj2 H3).
apply conj.
apply (Req_le (fst x) (fst x)).
by [].
apply (proj1 H3).
Qed.

Lemma BoundedClosedsectionRCalc : forall (a b : R) (H : a <= b)  (H1 : In (Ensemble R) BoundedClosedSection (fun x : R => a <= x <= b)), (BoundedClosedsectionR (fun x : R => a <= x <= b) H1) = b.
Proof.
move=> a b H1 H2.
rewrite /BoundedClosedsectionR.
rewrite /BoundedClosedsectionToRpair.
suff: let y := (constructive_definite_description
        (fun x : R * R =>
         fst x <= snd x /\
         (fun x0 : R => a <= x0 <= b) =
         (fun y : R => fst x <= y <= snd x))
        (BoundedClosedsectionUniqueRpair
           (fun x : R => a <= x <= b) H2)) in snd
  (proj1_sig y) = b.
by [].
case (constructive_definite_description
    (fun x : R * R =>
     fst x <= snd x /\
     (fun x0 : R => a <= x0 <= b) =
     (fun y : R => fst x <= y <= snd x))
    (BoundedClosedsectionUniqueRpair
       (fun x : R => a <= x <= b) H2)).
simpl.
move=> x.
move=> H3.
apply (Rle_antisym (snd x) b).
suff: (In R (fun y : R => a <= y <= b) (snd x)).
move=> H4.
apply H4.
rewrite (proj2 H3).
apply conj.
apply (proj1 H3).
apply (Req_le (snd x) (snd x)).
by [].
suff: (In R (fun y : R => fst x <= y <= snd x) b).
move=> H4.
apply H4.
rewrite - (proj2 H3).
apply conj.
apply H1.
apply (Req_le b b).
by [].
Qed.

Lemma Theorem_3_3_1 : forall IN : (nat -> Ensemble R), (forall n : nat, (In (Ensemble R) BoundedClosedSection (IN n))) -> (forall n : nat, Included R (IN (S n)) (IN n)) -> exists x : R, (forall n : nat, In R (IN n) x).
Proof.
move=> IN H2 H3.
suff: Un_growing (fun n : nat => fst (BoundedClosedsectionToRpair (IN n) (H2 n))).
move=> H4.
suff: (my_upper_bounded (Image.Im nat R (Full_set nat) (fun n : nat => fst (BoundedClosedsectionToRpair (IN n) (H2 n))))).
move=> H5.
elim (Theorem_3_1_1 (fun n : nat => fst (BoundedClosedsectionToRpair (IN n) (H2 n))) H5 H4).
move=> a.
case.
move=> H6 H7.
suff: Un_shrinking (fun n : nat => snd (BoundedClosedsectionToRpair (IN n) (H2 n))).
move=> H8.
suff: (my_lower_bounded (Image.Im nat R (Full_set nat) (fun n : nat => snd (BoundedClosedsectionToRpair (IN n) (H2 n))))).
move=> H9.
elim (Theorem_3_1_2 (fun n : nat => snd (BoundedClosedsectionToRpair (IN n) (H2 n))) H9 H8).
move=> b.
case.
move=> H10 H11.
exists a.
suff: a <= b.
move=> H12.
move=> n.
suff: (IN n) = (fun y : R => fst (BoundedClosedsectionToRpair (IN n) (H2 n)) <= y <= snd (BoundedClosedsectionToRpair (IN n) (H2 n))).
move=> H13.
rewrite H13.
apply conj.
apply (proj1 H7 (fst (BoundedClosedsectionToRpair (IN n) (H2 n)))).
apply (Im_intro nat R (Full_set nat) (fun n0 : nat => fst (BoundedClosedsectionToRpair (IN n0) (H2 n0))) n).
by [].
by [].
apply (Rle_trans a b (snd (BoundedClosedsectionToRpair (IN n) (H2 n)))).
apply H12.
apply (Rge_le (snd (BoundedClosedsectionToRpair (IN n) (H2 n))) b).
apply (proj1 H11 (snd (BoundedClosedsectionToRpair (IN n) (H2 n)))).
apply (Im_intro nat R (Full_set nat) (fun n0 : nat => snd (BoundedClosedsectionToRpair (IN n0) (H2 n0))) n).
by [].
by [].
rewrite /BoundedClosedsectionToRpair.
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN n = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN n) (H2 n))).
simpl.
move=> x H13.
apply (proj2 H13).
apply (Theorem_2_6 (fun n : nat => fst (BoundedClosedsectionToRpair (IN n) (H2 n))) (fun n : nat => snd (BoundedClosedsectionToRpair (IN n) (H2 n))) a b).
apply H6.
apply H10.
move=> n.
rewrite /BoundedClosedsectionToRpair.
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN n = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN n) (H2 n))).
simpl.
move=> x H12.
apply (proj1 H12).
exists (fst (BoundedClosedsectionToRpair (IN O) (H2 O))).
move=> x.
elim.
move=> n H9 y H10.
rewrite H10.
rewrite /BoundedClosedsectionToRpair.
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN n = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN n) (H2 n))).
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN 0%nat = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN 0%nat) (H2 0%nat))).
simpl.
move=> i0 H11 iN H12.
apply (Rle_ge (fst i0) (snd iN)).
suff: In R (IN O) (snd iN).
rewrite (proj2 H11).
move=> H13.
apply (proj1 H13).
apply (shrinking_prop_ER IN n 0).
apply H3.
apply (le_0_n n).
rewrite (proj2 H12).
apply conj.
apply (proj1 H12).
apply (Req_le (snd iN) (snd iN)).
by [].
move=> n.
rewrite /BoundedClosedsectionToRpair.
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN n = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN n) (H2 n))).
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN (S n) = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN (S n)) (H2 (S n)))).
simpl.
move=> iSN H8 iN H9.
suff: (In R (IN n) (snd iSN)).
rewrite (proj2 H9).
move=> H10.
apply (Rle_ge (snd iSN) (snd iN)).
apply (proj2 H10).
apply (H3 n (snd iSN)).
rewrite (proj2 H8).
apply conj.
apply (proj1 H8).
apply (Req_le (snd iSN) (snd iSN)).
by [].
exists (snd (BoundedClosedsectionToRpair (IN O) (H2 O))).
move=> x.
elim.
move=> n H9 y H10.
rewrite H10.
rewrite /BoundedClosedsectionToRpair.
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN n = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN n) (H2 n))).
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN 0%nat = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN 0%nat) (H2 0%nat))).
simpl.
move=> i0 H11 iN H12.
suff: In R (IN O) (fst iN).
rewrite (proj2 H11).
move=> H13.
apply (proj2 H13).
apply (shrinking_prop_ER IN n 0).
apply H3.
apply (le_0_n n).
rewrite (proj2 H12).
apply conj.
apply (Req_le (fst iN) (fst iN)).
by [].
apply (proj1 H12).
move=> n.
rewrite /BoundedClosedsectionToRpair.
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN n = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN n) (H2 n))).
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN (S n) = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN (S n)) (H2 (S n)))).
simpl.
move=> iSN H8 iN H9.
suff: (In R (IN n) (fst iSN)).
rewrite (proj2 H9).
move=> H10.
apply (proj1 H10).
apply (H3 n (fst iSN)).
rewrite (proj2 H8).
apply conj.
apply (Req_le (fst iSN) (fst iSN)).
by [].
apply (proj1 H8).
Qed.

Lemma Theorem_3_3_2 : forall (IN : (nat -> Ensemble R)) (H : (forall n : nat, (In (Ensemble R) BoundedClosedSection (IN n)))), (forall n : nat, Included R (IN (S n)) (IN n)) -> (Un_cv (fun m : nat => (snd (BoundedClosedsectionToRpair (IN m) (H m)) - (fst (BoundedClosedsectionToRpair (IN m) (H m))))) 0) -> (exists! x : R, (forall n : nat, In R (IN n) x)) /\ (forall x : R, (forall n : nat, In R (IN n) x) -> (Un_cv (fun m : nat => fst (BoundedClosedsectionToRpair (IN m) (H m))) x) /\ (Un_cv (fun m : nat => snd (BoundedClosedsectionToRpair (IN m) (H m))) x)).
Proof.
move=> IN H2 H3 H1.
suff: Un_growing (fun n : nat => fst (BoundedClosedsectionToRpair (IN n) (H2 n))).
move=> H4.
suff: (my_upper_bounded (Image.Im nat R (Full_set nat) (fun n : nat => fst (BoundedClosedsectionToRpair (IN n) (H2 n))))).
move=> H5.
elim (Theorem_3_1_1 (fun n : nat => fst (BoundedClosedsectionToRpair (IN n) (H2 n))) H5 H4).
move=> a.
case.
move=> H6 H7.
suff: Un_shrinking (fun n : nat => snd (BoundedClosedsectionToRpair (IN n) (H2 n))).
move=> H8.
suff: (my_lower_bounded (Image.Im nat R (Full_set nat) (fun n : nat => snd (BoundedClosedsectionToRpair (IN n) (H2 n))))).
move=> H9.
elim (Theorem_3_1_2 (fun n : nat => snd (BoundedClosedsectionToRpair (IN n) (H2 n))) H9 H8).
move=> b.
case.
move=> H10 H11.
suff: a = b.
move=> H12.
suff: forall (z : R),(forall (n : nat), In R (IN n) z) -> z = a.
move=> H13.
apply conj.
apply (proj1 (unique_existence (fun (x : R) => forall n : nat, In R (IN n) x))).
apply conj.
exists a.
move=> n.
suff: (IN n) = (fun y : R => fst (BoundedClosedsectionToRpair (IN n) (H2 n)) <= y <= snd (BoundedClosedsectionToRpair (IN n) (H2 n))).
move=> H14.
rewrite H14.
apply conj.
apply (proj1 H7 (fst (BoundedClosedsectionToRpair (IN n) (H2 n)))).
apply (Im_intro nat R (Full_set nat) (fun n0 : nat => fst (BoundedClosedsectionToRpair (IN n0) (H2 n0))) n).
by [].
by [].
apply (Rle_trans a b (snd (BoundedClosedsectionToRpair (IN n) (H2 n)))).
apply (Req_le a b H12).
apply (Rge_le (snd (BoundedClosedsectionToRpair (IN n) (H2 n))) b).
apply (proj1 H11 (snd (BoundedClosedsectionToRpair (IN n) (H2 n)))).
apply (Im_intro nat R (Full_set nat) (fun n0 : nat => snd (BoundedClosedsectionToRpair (IN n0) (H2 n0))) n).
by [].
by [].
rewrite /BoundedClosedsectionToRpair.
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN n = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN n) (H2 n))).
simpl.
move=> x H14.
apply (proj2 H14).
move=> x y H14 H15.
rewrite (H13 x H14).
rewrite (H13 y H15).
by [].
move=> x H14.
apply conj.
rewrite (H13 x H14).
apply H6.
rewrite (H13 x H14).
rewrite H12.
apply H10.
move=> z H13.
apply (Rle_antisym z a).
rewrite H12.
apply (Rnot_gt_le z b).
move=> H14.
elim (proj2 (proj2 (proj2 Proposition_1_3 (Im nat R (Full_set nat)
           (fun n : nat =>
            snd
              (BoundedClosedsectionToRpair (IN n) (H2 n))))
        b) H11) z).
move => b0.
case.
elim.
move => n0 H15 y H16 H17.
apply (Rgt_not_le z y H17).
suff: (IN n0) = (fun w : R => (fst (BoundedClosedsectionToRpair (IN n0) (H2 n0))) <= w <= (snd (BoundedClosedsectionToRpair (IN n0) (H2 n0)))).
move=> H18.
suff: In R (fun w : R => (fst (BoundedClosedsectionToRpair (IN n0) (H2 n0))) <= w <= (snd (BoundedClosedsectionToRpair (IN n0) (H2 n0)))) z.
move=> H19.
rewrite H16.
apply (proj2 H19).
rewrite - H18.
apply (H13 n0).
rewrite /BoundedClosedsectionToRpair.
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN n0 = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN n0) (H2 n0))).
simpl.
move=> x H18.
apply (proj2 H18).
apply H14.
apply (Rnot_gt_le a z).
move=> H14.
elim (proj2 (proj2 (proj1 Proposition_1_3 (Im nat R (Full_set nat)
           (fun n : nat =>
            fst
              (BoundedClosedsectionToRpair (IN n) (H2 n))))
        a) H7) z).
move => b0.
case.
elim.
move => n0 H15 y H16 H17.
apply (Rlt_not_ge z y H17).
suff: (IN n0) = (fun w : R => (fst (BoundedClosedsectionToRpair (IN n0) (H2 n0))) <= w <= (snd (BoundedClosedsectionToRpair (IN n0) (H2 n0)))).
move=> H18.
suff: In R (fun w : R => (fst (BoundedClosedsectionToRpair (IN n0) (H2 n0))) <= w <= (snd (BoundedClosedsectionToRpair (IN n0) (H2 n0)))) z.
move=> H19.
rewrite H16.
apply (Rle_ge (fst (BoundedClosedsectionToRpair (IN n0) (H2 n0))) z).
apply (proj1 H19).
rewrite - H18.
apply (H13 n0).
rewrite /BoundedClosedsectionToRpair.
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN n0 = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN n0) (H2 n0))).
simpl.
move=> x H18.
apply (proj2 H18).
apply H14.
apply (Rminus_diag_uniq_sym a b).
apply (Proposition_2_3 (fun m : nat =>
        snd (BoundedClosedsectionToRpair (IN m) (H2 m)) -
        fst (BoundedClosedsectionToRpair (IN m) (H2 m))) (b - a) 0).
suff: (fun m : nat =>
   snd (BoundedClosedsectionToRpair (IN m) (H2 m)) -
   fst (BoundedClosedsectionToRpair (IN m) (H2 m))) = (RSequencePlus (fun m : nat =>
   snd (BoundedClosedsectionToRpair (IN m) (H2 m))) (RSequenceOpp (fun m : nat =>
   fst (BoundedClosedsectionToRpair (IN m) (H2 m))))).
move=> H12.
rewrite H12.
apply (Theorem_2_5_1_plus (fun m : nat =>
      snd (BoundedClosedsectionToRpair (IN m) (H2 m))) (RSequenceOpp
        (fun m : nat =>
         fst (BoundedClosedsectionToRpair (IN m) (H2 m)))) b (- a)).
apply H10.
apply (Theorem_2_5_1_opp (fun m : nat =>
      fst (BoundedClosedsectionToRpair (IN m) (H2 m))) a).
apply H6.
apply (functional_extensionality (fun m : nat =>
 snd (BoundedClosedsectionToRpair (IN m) (H2 m)) -
 fst (BoundedClosedsectionToRpair (IN m) (H2 m))) (RSequencePlus
  (fun m : nat =>
   snd (BoundedClosedsectionToRpair (IN m) (H2 m)))
  (RSequenceOpp
     (fun m : nat =>
      fst (BoundedClosedsectionToRpair (IN m) (H2 m)))))).
move=> n.
by [].
apply H1.
exists (fst (BoundedClosedsectionToRpair (IN O) (H2 O))).
move=> x.
elim.
move=> n H9 y H10.
rewrite H10.
rewrite /BoundedClosedsectionToRpair.
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN n = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN n) (H2 n))).
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN 0%nat = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN 0%nat) (H2 0%nat))).
simpl.
move=> i0 H11 iN H12.
apply (Rle_ge (fst i0) (snd iN)).
suff: In R (IN O) (snd iN).
rewrite (proj2 H11).
move=> H13.
apply (proj1 H13).
apply (shrinking_prop_ER IN n 0).
apply H3.
apply (le_0_n n).
rewrite (proj2 H12).
apply conj.
apply (proj1 H12).
apply (Req_le (snd iN) (snd iN)).
by [].
move=> n.
rewrite /BoundedClosedsectionToRpair.
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN n = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN n) (H2 n))).
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN (S n) = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN (S n)) (H2 (S n)))).
simpl.
move=> iSN H8 iN H9.
suff: (In R (IN n) (snd iSN)).
rewrite (proj2 H9).
move=> H10.
apply (Rle_ge (snd iSN) (snd iN)).
apply (proj2 H10).
apply (H3 n (snd iSN)).
rewrite (proj2 H8).
apply conj.
apply (proj1 H8).
apply (Req_le (snd iSN) (snd iSN)).
by [].
exists (snd (BoundedClosedsectionToRpair (IN O) (H2 O))).
move=> x.
elim.
move=> n H9 y H10.
rewrite H10.
rewrite /BoundedClosedsectionToRpair.
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN n = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN n) (H2 n))).
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN 0%nat = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN 0%nat) (H2 0%nat))).
simpl.
move=> i0 H11 iN H12.
suff: In R (IN O) (fst iN).
rewrite (proj2 H11).
move=> H13.
apply (proj2 H13).
apply (shrinking_prop_ER IN n 0).
apply H3.
apply (le_0_n n).
rewrite (proj2 H12).
apply conj.
apply (Req_le (fst iN) (fst iN)).
by [].
apply (proj1 H12).
move=> n.
rewrite /BoundedClosedsectionToRpair.
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN n = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN n) (H2 n))).
elim (constructive_definite_description
         (fun x : R * R =>
          fst x <= snd x /\ IN (S n) = (fun y0 : R => fst x <= y0 <= snd x))
         (BoundedClosedsectionUniqueRpair (IN (S n)) (H2 (S n)))).
simpl.
move=> iSN H8 iN H9.
suff: (In R (IN n) (fst iSN)).
rewrite (proj2 H9).
move=> H10.
apply (proj1 H10).
apply (H3 n (fst iSN)).
rewrite (proj2 H8).
apply conj.
apply (Req_le (fst iSN) (fst iSN)).
by [].
apply (proj1 H8).
Qed.

Definition Subsequence (ABn An : nat -> R) : Prop :=
exists (Bn : nat -> nat), (forall (n : nat),(Bn n) < (Bn (S n)))%nat /\ (forall (n : nat),(ABn n) = (An (Bn n))).

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

Lemma Formula_3_18 : forall (An Bn : nat -> R), (Subsequence An Bn) -> forall (x : R), (Un_cv Bn x) -> (Un_cv An x).
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
apply (functional_choice (fun (AB : ((Ensemble U) * (Ensemble U))) (X : Ensemble U) => (~ Finite U (Union U (fst AB) (snd AB))) -> (~ Finite U X) /\ (X = (fst AB) \/ X = (snd AB)))).
move=> x.
elim (classic (Finite U (Union U (fst x) (snd x)))).
move=> H1.
exists (Full_set U).
move=> H2.
apply False_ind.
apply (H2 H1).
move=> H1.
elim (Infinite_Set_Or U (fst x) (snd x) H1).
move=> H2.
exists (fst x).
move=> H3.
apply conj.
apply H2.
left.
by [].
move=> H2.
exists (snd x).
move=> H3.
apply conj.
apply H2.
right.
by [].
Qed.

Lemma  Iminv_Infinite_Or_Infinite : forall (V U : Type), forall (F : V -> U), exists (f : ((Ensemble U) * (Ensemble U)) -> (Ensemble U)), forall (AB : ((Ensemble U) * (Ensemble U))), (~ Finite V (fun v : V => (In U (Union U (fst AB) (snd AB)) (F v))) -> (~ Finite V (fun v : V => In U (f AB) (F v)))) /\ ((f AB) = (fst AB) \/ (f AB) = (snd AB)).
Proof.
move=> V U F.
apply (functional_choice (fun (AB : ((Ensemble U) * (Ensemble U))) (X : Ensemble U) =>  (~
   Finite V
     (fun v : V => In U (Union U (fst AB) (snd AB)) (F v)) ->
   ~ Finite V (fun v : V => In U X (F v))) /\
  (X = fst AB \/ X = snd AB)
)).
move=> x.
elim (classic (Finite V
    (fun v : V => In U (Union U (fst x) (snd x)) (F v)))).
move=> H1.
exists (fst x).
apply conj.
move=> H2.
apply False_ind.
apply (H2 H1).
left.
by [].
move=> H1.
suff: (fun v : V => In U (Union U (fst x) (snd x)) (F v)) = Union V (fun v : V => In U (fst x) (F v)) (fun v : V => In U (snd x) (F v)).
move=> H2.
elim (Infinite_Set_Or V (fun v : V => In U (fst x) (F v)) (fun v : V => In U (snd x) (F v))).
move=> H3.
exists (fst x).
apply conj.
move=> H4.
apply H3.
left.
by [].
move=> H3.
exists (snd x).
apply conj.
move=> H4.
apply H3.
right.
by [].
rewrite - H2.
apply H1.
apply (Extensionality_Ensembles V (fun v : V => In U (Union U (fst x) (snd x)) (F v))
(Union V (fun v : V => In U (fst x) (F v))
  (fun v : V => In U (snd x) (F v)))).
apply conj.
move=> y H2.
suff: ((fun v : V => In U (fst x) (F v)) y) \/
     ((fun v : V => In U (snd x) (F v)) y).
case.
move=> H3.
apply (Union_introl V (fun v : V => In U (fst x) (F v))
     (fun v : V => In U (snd x) (F v))).
apply H3.
move=> H3.
apply (Union_intror V (fun v : V => In U (fst x) (F v))
     (fun v : V => In U (snd x) (F v))).
apply H3.
elim H2.
move=> z.
left.
apply H.
move=> z.
right.
apply H.
move=> y.
elim.
move=> z H2.
apply (Union_introl U (fst x) (snd x)).
apply H2.
move=> z H2.
apply (Union_intror U (fst x) (snd x)).
apply H2.
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

Lemma Theorem_3_4 : forall (An : nat -> R) (H : my_bounded (Image.Im nat R (Full_set nat) An)), exists (Bn : nat -> R), (Subsequence Bn An).
Proof.
move=> An H1.
elim (proj1 H1).
move=> b H2.
elim (proj2 H1).
move=> a H3.
suff: a <= b.
move=> H10.
elim (Iminv_Infinite_Or_Infinite nat R An).
move=> F H4.
suff: exists (IN : nat -> (Ensemble R)) (H : (forall n : nat, (In (Ensemble R) BoundedClosedSection (IN n)))), forall (n : nat),(BoundedClosedsectionSize (IN n) (H n)) = (b - a) / (2 ^ n) /\ (~ Finite nat (fun m : nat => In R (IN n) (An m))) /\ (Included R (IN (S n)) (IN n)).
elim.
move=> IN.
elim.
move=> H5 H6.
suff: exists (G : nat -> nat -> nat), forall (n m : nat), (is_min_nat (fun k : nat => (In R (IN n) (An k)) /\ (k >= m)%nat) (G n m)).
elim.
move=> G H7.
exists (fun (k : nat) => An ((fix Bn (n : nat) : nat := 
match n with 
  | O => (G O O)
  | S n0 => (G (S n0) (S (Bn n0)))
end) k)).
exists (fix Bn (n : nat) : nat := 
match n with 
  | O => (G O O)
  | S n0 => (G (S n0) (S (Bn n0)))
end).
apply conj.
elim.
apply (proj2 (proj1 (H7 1%nat (S (G O O))))).
move=> n0 H8.
apply (proj2 (proj1 (H7 (S (S n0))
   (S
      (G (S n0)
         (S
            ((fix Bn (n : nat) : nat :=
                match n with
                | 0 => G 0 0
                | S n1 => G (S n1) (S (Bn n1))
                end) n0)))))%nat)).
by [].
suff: forall (n m : nat), (exists ! x : nat,
     is_min_nat
       (fun k : nat => In R (IN n) (An k) /\ (k >= m)%nat) x).
move=> H7.
exists (fun (n m : nat) => proj1_sig (constructive_definite_description (fun (l : nat) => is_min_nat
    (fun k : nat => In R (IN n) (An k) /\ (k >= m)%nat) l) (H7 n m))).
move=> n m.
elim (constructive_definite_description
        (fun l : nat =>
         is_min_nat
           (fun k : nat =>
            In R (IN n) (An k) /\ (k >= m)%nat) l)
        (H7 n m)).
simpl.
by [].
move=> n m.
apply (unique_existence (fun x : nat => is_min_nat
    (fun k : nat => In R (IN n) (An k) /\ (k >= m)%nat) x)).
apply conj.
apply (Exist_min_nat (fun k : nat => In R (IN n) (An k) /\ (k >= m)%nat)).
apply (NNPP (Inhabited nat
  (fun k : nat => In R (IN n) (An k) /\ (k >= m)%nat))).
move=> H7.
apply (proj1 (proj2 (H6 n))).
apply (Finite_Set_Included nat (fun k : nat => In R (IN n) (An k)) (fun k : nat => (k < m)%nat)).
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
suff: forall (I : Ensemble R) (H : (In (Ensemble R) BoundedClosedSection I)),
(In (Ensemble R) BoundedClosedSection (F ((fun x : R => (BoundedClosedsectionL I H) <= x <= ((BoundedClosedsectionL I H) + (BoundedClosedsectionR I H)) / 2),(fun x : R => ((BoundedClosedsectionL I H) + (BoundedClosedsectionR I H)) / 2 <= x <= (BoundedClosedsectionR I H))))).
move=> H6.
suff: (In (Ensemble R) BoundedClosedSection (fun x : R => a <= x <= b)).
move=> H7.
exists (fun n : nat => (proj1_sig ((fix IN (n : nat) : {I : (Ensemble R) | In (Ensemble R) BoundedClosedSection I} := 
match n with
  | O => exist (fun x : (Ensemble R) => In (Ensemble R) BoundedClosedSection x) (fun x : R => a <= x <= b) H7 
  | S n0 => exist (fun x : (Ensemble R) => In (Ensemble R) BoundedClosedSection x) (F ((fun x : R => (BoundedClosedsectionL (proj1_sig (IN n0)) (proj2_sig (IN n0))) <= x <= ((BoundedClosedsectionL (proj1_sig (IN n0)) (proj2_sig (IN n0))) + (BoundedClosedsectionR (proj1_sig (IN n0)) (proj2_sig (IN n0)))) / 2),(fun x : R => ((BoundedClosedsectionL (proj1_sig (IN n0)) (proj2_sig (IN n0))) + (BoundedClosedsectionR (proj1_sig (IN n0)) (proj2_sig (IN n0)))) / 2 <= x <= (BoundedClosedsectionR (proj1_sig (IN n0)) (proj2_sig (IN n0))))))
 (H6 (proj1_sig (IN n0)) (proj2_sig (IN n0)))
end) n))).
suff: forall n : nat,
      In (Ensemble R) BoundedClosedSection
        (proj1_sig
           ((fix IN (n0 : nat) :
               {I : Ensemble R |
               In (Ensemble R) BoundedClosedSection I} :=
               match n0 with
               | 0%nat =>
                   exist
                     (fun x : Ensemble R =>
                      In (Ensemble R) BoundedClosedSection
                        x) (fun x : R => a <= x <= b) H7
               | S n1 =>
                   exist
                     (fun x : Ensemble R =>
                      In (Ensemble R) BoundedClosedSection
                        x)
                     (F
                        (fun x : R =>
                         BoundedClosedsectionL
                           (proj1_sig (IN n1))
                           (proj2_sig (IN n1)) <= x <=
                         (BoundedClosedsectionL
                            (proj1_sig (IN n1))
                            (proj2_sig (IN n1)) +
                          BoundedClosedsectionR
                            (proj1_sig (IN n1))
                            (proj2_sig (IN n1))) / 2,
                        fun x : R =>
                        (BoundedClosedsectionL
                           (proj1_sig (IN n1))
                           (proj2_sig (IN n1)) +
                         BoundedClosedsectionR
                           (proj1_sig (IN n1))
                           (proj2_sig (IN n1))) / 2 <=
                        x <=
                        BoundedClosedsectionR
                          (proj1_sig (IN n1))
                          (proj2_sig (IN n1))))
                     (H6 (proj1_sig (IN n1))
                        (proj2_sig (IN n1)))
               end) n)).
move=> H8.
exists H8.
suff: let IN_sub := (fix IN (n : nat) : {I : (Ensemble R) | In (Ensemble R) BoundedClosedSection I} := 
match n with
  | O => exist (fun x : (Ensemble R) => In (Ensemble R) BoundedClosedSection x) (fun x : R => a <= x <= b) H7 
  | S n0 => exist (fun x : (Ensemble R) => In (Ensemble R) BoundedClosedSection x) (F ((fun x : R => (BoundedClosedsectionL (proj1_sig (IN n0)) (proj2_sig (IN n0))) <= x <= ((BoundedClosedsectionL (proj1_sig (IN n0)) (proj2_sig (IN n0))) + (BoundedClosedsectionR (proj1_sig (IN n0)) (proj2_sig (IN n0)))) / 2),(fun x : R => ((BoundedClosedsectionL (proj1_sig (IN n0)) (proj2_sig (IN n0))) + (BoundedClosedsectionR (proj1_sig (IN n0)) (proj2_sig (IN n0)))) / 2 <= x <= (BoundedClosedsectionR (proj1_sig (IN n0)) (proj2_sig (IN n0))))))
 (H6 (proj1_sig (IN n0)) (proj2_sig (IN n0)))
end) in let IN := (fun n : nat => (proj1_sig (IN_sub n))) in forall n : nat,
  BoundedClosedsectionSize (IN n) (H8 n) = (b - a) / 2 ^ n /\
  ~ Finite nat (fun m : nat => In R (IN n) (An m)) /\
  Included R (IN (S n)) (IN n).
by [].
move=> IN_sub IN.
elim.
apply conj.
rewrite /BoundedClosedsectionSize.
rewrite (BoundedClosedsectionRCalc a b H10).
rewrite (BoundedClosedsectionLCalc a b H10).
rewrite /Rdiv.
rewrite (Rinv_1).
rewrite (Rmult_1_r (b - a)).
by [].
apply conj.
move=> H9.
apply FullsetNatInfinite.
apply (Finite_Set_Included nat (Full_set nat) (fun m : nat => In R (IN 0%nat) (An m))).
apply H9.
move=> n.
move=> H11.
rewrite /IN.
simpl.
apply conj.
apply (Rge_le (An n) a).
apply (H3 (An n)).
apply (Im_intro nat R (Full_set nat) An n).
by [].
by [].
apply (H2 (An n)).
apply (Im_intro nat R (Full_set nat) An n).
by [].
by [].
rewrite /IN.
simpl.
rewrite (BoundedClosedsectionRCalc a b H10).
rewrite (BoundedClosedsectionLCalc a b H10).
suff: ~ Finite nat
                 (fun v : nat =>
                  In R
                    (Union R
                       (fst
                          (fun x : R => a <= x <= (a + b) / 2,
                          fun x : R => (a + b) / 2 <= x <= b))
                       (snd
                          (fun x : R => a <= x <= (a + b) / 2,
                          fun x : R => (a + b) / 2 <= x <= b)))
                    (An v)).
move=> H9.
elim (proj2 (H4 (fun x : R => a <= x <= (a + b) / 2,
     fun x : R => (a + b) / 2 <= x <= b))).
move=> H11.
rewrite H11.
simpl.
move=> x H12.
apply conj.
apply H12.
apply (Rle_trans x ((a + b) / 2) b).
apply H12.
rewrite /Rdiv.
rewrite - {2}(eps2 b).
rewrite (Rmult_plus_distr_r a b (/ 2)).
apply (Rplus_le_compat_r (b * / 2) (a * / 2) (b * / 2)).
apply (Rmult_le_compat_r (/ 2) a b).
apply (Rlt_le 0 (/ 2)).
apply (Rinv_0_lt_compat 2).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply H10.
move=> H11.
rewrite H11.
simpl.
move=> x H12.
apply conj.
apply (Rle_trans a ((a + b) / 2) x).
rewrite /Rdiv.
rewrite - {1}(eps2 a).
rewrite (Rmult_plus_distr_r a b (/ 2)).
apply (Rplus_le_compat_l (a * / 2) (a * / 2) (b * / 2)).
apply (Rmult_le_compat_r (/ 2) a b).
apply (Rlt_le 0 (/ 2)).
apply (Rinv_0_lt_compat 2).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply H10.
apply H12.
apply H12.
move=> H9.
apply FullsetNatInfinite.
apply (Finite_Set_Included nat (Full_set nat) (fun v : nat =>
        In R
          (Union R
             (fst
                (fun x : R => a <= x <= (a + b) / 2,
                fun x : R => (a + b) / 2 <= x <= b))
             (snd
                (fun x : R => a <= x <= (a + b) / 2,
                fun x : R => (a + b) / 2 <= x <= b)))
          (An v))).
apply H9.
move=> n.
move=> H11.
elim (Rlt_le_dec (An n) ((a + b) / 2)).
move=> H12.
left.
simpl.
apply conj.
apply (Rge_le (An n) a).
apply (H3 (An n)).
apply (Im_intro nat R (Full_set nat) An n).
by [].
by [].
apply (Rlt_le (An n) ((a + b) / 2) H12).
move=> H12.
right.
simpl.
apply conj.
apply H12.
apply (H2 (An n)).
apply (Im_intro nat R (Full_set nat) An n).
by [].
by [].
move=> n H9.
apply conj.
rewrite /BoundedClosedsectionSize.
rewrite /BoundedClosedsectionR.
rewrite /BoundedClosedsectionL.
rewrite /IN.
simpl.
suff: let ISN1 := (fun x : R =>
         BoundedClosedsectionL (proj1_sig (IN_sub n))
           (proj2_sig (IN_sub n)) <= x <=
         (BoundedClosedsectionL (proj1_sig (IN_sub n))
            (proj2_sig (IN_sub n)) +
          BoundedClosedsectionR (proj1_sig (IN_sub n))
            (proj2_sig (IN_sub n))) / 2) in
      let ISN2 := (fun x : R =>
        (BoundedClosedsectionL (proj1_sig (IN_sub n))
           (proj2_sig (IN_sub n)) +
         BoundedClosedsectionR (proj1_sig (IN_sub n))
           (proj2_sig (IN_sub n))) / 2 <= x <=
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) in
      (snd ( BoundedClosedsectionToRpair (F (ISN1,ISN2)) (H8 (S n))) 
    - fst ( BoundedClosedsectionToRpair (F (ISN1,ISN2)) (H8 (S n)))) = (b - a) / (2 * 2 ^ n).
by [].
move=> ISN1 ISN2.
suff: ~
     Finite nat
       (fun v : nat => In R (Union R (fst (ISN1, ISN2)) (snd (ISN1, ISN2))) (An v)).
move=> H11.
elim (H4 (ISN1, ISN2)).
move=> H12.
case.
move=> H13.
suff: forall (xv yv : Ensemble R),forall (xp : (In (Ensemble R) BoundedClosedSection xv)),forall (yp : (In (Ensemble R) BoundedClosedSection yv)),
xv = yv -> (BoundedClosedsectionToRpair xv xp) = (BoundedClosedsectionToRpair yv yp).
move=> H14.
suff: In (Ensemble R) BoundedClosedSection (fst (ISN1, ISN2)).
move=> H15.
rewrite (H14 (F (ISN1, ISN2)) (fst (ISN1, ISN2)) (H8 (S n)) H15 H13).
simpl.
rewrite /BoundedClosedsectionToRpair.
suff: let y := (constructive_definite_description
        (fun x : R * R =>
         fst x <= snd x /\
         ISN1 = (fun y : R => fst x <= y <= snd x))
        (BoundedClosedsectionUniqueRpair ISN1 H15)) in
snd (proj1_sig y) - fst (proj1_sig y) = (b - a) / (2 * 2 ^ n).
by [].
elim (constructive_definite_description
        (fun x : R * R =>
         fst x <= snd x /\
         ISN1 = (fun y : R => fst x <= y <= snd x))
        (BoundedClosedsectionUniqueRpair ISN1 H15)).
rewrite /ISN1.
move=> x H16.
simpl.
suff: BoundedClosedsectionL (proj1_sig (IN_sub n))
         (proj2_sig (IN_sub n)) = fst x.
move=> H17.
suff: (BoundedClosedsectionL (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n)) +
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) / 2 = snd x.
move=> H18.
rewrite - H17.
rewrite - H18.
rewrite /Rdiv.
suff: let x1 := (BoundedClosedsectionL (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) in
let x2 := (BoundedClosedsectionR (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) in
((x1 + x2) * / 2 - x1 = (b - a) * / (2 * 2 ^ n)).
by [].
move=> x1 x2.
rewrite - {2}(eps2 x1).
rewrite (Rmult_plus_distr_r x1 x2 (/ 2)).
rewrite (Rplus_comm (x1 * / 2) (x2 * / 2)).
rewrite /Rminus.
rewrite (Rplus_assoc (x2 * / 2) (x1 * / 2) (-(x1 * / 2 + x1 * / 2))).
rewrite (Ropp_plus_distr (x1 * / 2) (x1 * / 2)).
rewrite - (Rplus_assoc (x1 * / 2) (- (x1 * / 2)) (- (x1 * / 2))).
rewrite (Rplus_opp_r (x1 * / 2)).
rewrite (Rplus_0_l (- (x1 * / 2))).
rewrite (Ropp_mult_distr_l x1 (/ 2)).
rewrite - (Rmult_plus_distr_r x2 (- x1) (/ 2)).
rewrite /BoundedClosedsectionSize in H9.
rewrite /IN in H9.
rewrite /x1.
rewrite /x2.
rewrite (proof_irrelevance (In (Ensemble R) BoundedClosedSection (proj1_sig (IN_sub n))) (proj2_sig (IN_sub n)) (H8 n)).
rewrite /Rminus in H9.
rewrite (proj1 H9).
rewrite /Rdiv.
rewrite (Rmult_assoc (b + - a) (/ 2 ^ n) (/ 2)).
rewrite (Rinv_mult_distr 2 (2 ^ n)).
rewrite (Rmult_comm (/ 2) (/ 2 ^ n)).
by [].
apply (Rgt_not_eq 2 0).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rgt_trans (1 + 1) 1 0).
apply (Rlt_plus_1 1).
apply (Rlt_0_1).
apply (Rgt_not_eq (2 ^ n) 0).
elim n.
simpl.
rewrite /2.
apply Rlt_0_1.
move=> n0 H19.
simpl.
rewrite {1}/2.
rewrite - (INR_IPR 2).
simpl.
apply (Rmult_gt_0_compat (1 + 1) (2 ^ n0)).
apply (Rgt_trans (1 + 1) 1 0).
apply (Rlt_plus_1 1).
apply (Rlt_0_1).
apply H19.
suff: BoundedClosedsectionL (proj1_sig (IN_sub n))
         (proj2_sig (IN_sub n)) <=
       (BoundedClosedsectionL (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n)) +
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) / 2.
move=> H18.
apply (Rle_antisym ((BoundedClosedsectionL (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n)) +
 BoundedClosedsectionR (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) / 2) (snd x)).
suff: In R (fun y : R => fst x <= y <= snd x) ((BoundedClosedsectionL (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n)) +
 BoundedClosedsectionR (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) / 2).
move=> H19.
apply (proj2 H19).
rewrite - (proj2 H16).
apply conj.
apply H18.
apply (Req_le ((BoundedClosedsectionL (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n)) +
 BoundedClosedsectionR (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) / 2) ((BoundedClosedsectionL (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n)) +
 BoundedClosedsectionR (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) / 2)).
by [].
suff: In R (fun x : R =>
       BoundedClosedsectionL (proj1_sig (IN_sub n))
         (proj2_sig (IN_sub n)) <= x <=
       (BoundedClosedsectionL (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n)) +
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) / 2) (snd x).
move=> H19.
apply H19.
rewrite (proj2 H16).
apply conj.
apply (proj1 H16).
apply (Req_le (snd x) (snd x)).
by [].
suff: In R (fun x : R =>
       BoundedClosedsectionL (proj1_sig (IN_sub n))
         (proj2_sig (IN_sub n)) <= x <=
       (BoundedClosedsectionL (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n)) +
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) / 2) (snd x).
move=> H18.
apply (Rle_trans (BoundedClosedsectionL (proj1_sig (IN_sub n))
         (proj2_sig (IN_sub n))) (snd x) ((BoundedClosedsectionL (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n)) +
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) / 2)).
apply H18.
apply H18.
rewrite (proj2 H16).
apply conj.
apply (proj1 H16).
apply (Req_le (snd x) (snd x)).
by [].
apply (Rle_antisym (BoundedClosedsectionL (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n))) (fst x)).
suff: In R (fun x : R =>
       BoundedClosedsectionL (proj1_sig (IN_sub n))
         (proj2_sig (IN_sub n)) <= x <=
       (BoundedClosedsectionL (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n)) +
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) / 2) (fst x).
move=> H17.
apply H17.
rewrite (proj2 H16).
apply conj.
apply (Req_le (fst x) (fst x)).
by [].
apply (proj1 H16).
suff: In R (fun y : R => fst x <= y <= snd x) (BoundedClosedsectionL (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n))).
move=> H17.
apply H17.
rewrite - (proj2 H16).
apply conj.
apply (Req_le (BoundedClosedsectionL (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n))) (BoundedClosedsectionL (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n)))).
by [].
suff: In R (fun x : R =>
       BoundedClosedsectionL (proj1_sig (IN_sub n))
         (proj2_sig (IN_sub n)) <= x <=
       (BoundedClosedsectionL (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n)) +
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) / 2) (snd x).
move=> H18.
apply (Rle_trans (BoundedClosedsectionL (proj1_sig (IN_sub n))
         (proj2_sig (IN_sub n))) (snd x) ((BoundedClosedsectionL (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n)) +
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) / 2)).
apply H18.
apply H18.
rewrite (proj2 H16).
apply conj.
apply (proj1 H16).
apply (Req_le (snd x) (snd x)).
by [].
simpl.
rewrite /ISN1.
apply (Im_intro (R * R) (Ensemble R) (fun (x : (R * R)) => (fst x) <= (snd x)) (fun (x : (R * R)) => (fun (y : R) => (fst x) <= y <= (snd x)))
(BoundedClosedsectionL (proj1_sig (IN_sub n))
     (proj2_sig (IN_sub n)),
   (BoundedClosedsectionL (proj1_sig (IN_sub n))
    (proj2_sig (IN_sub n)) +
  BoundedClosedsectionR (proj1_sig (IN_sub n))
    (proj2_sig (IN_sub n))) / 2)).
simpl.
suff: (BoundedClosedsectionL (proj1_sig (IN_sub n))
     (proj2_sig (IN_sub n))) <=
  ((BoundedClosedsectionL (proj1_sig (IN_sub n))
     (proj2_sig (IN_sub n)) +
   BoundedClosedsectionR (proj1_sig (IN_sub n))
     (proj2_sig (IN_sub n))) / 2).
by [].
rewrite /Rdiv.
rewrite - {1}(eps2 (BoundedClosedsectionL (proj1_sig (IN_sub n))
     (proj2_sig (IN_sub n)))).
rewrite (Rmult_plus_distr_r (BoundedClosedsectionL (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) (BoundedClosedsectionR (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) (/ 2)).
apply (Rplus_le_compat_l (BoundedClosedsectionL (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n)) * / 2) (BoundedClosedsectionL (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n)) * / 2) (BoundedClosedsectionR (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n)) * / 2)).
apply (Rmult_le_compat_r (/ 2) (BoundedClosedsectionL (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n))) (BoundedClosedsectionR (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n)))).
apply (Rlt_le 0 (/ 2)).
apply (Rinv_0_lt_compat 2).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rgt_trans (1 + 1) 1 0).
apply (Rlt_plus_1 1).
apply (Rlt_0_1).
rewrite /BoundedClosedsectionL.
rewrite /BoundedClosedsectionR.
rewrite /BoundedClosedsectionToRpair.
suff: let y := (constructive_definite_description
        (fun x : R * R =>
         fst x <= snd x /\
         proj1_sig (IN_sub n) =
         (fun y : R => fst x <= y <= snd x))
        (BoundedClosedsectionUniqueRpair
           (proj1_sig (IN_sub n)) (proj2_sig (IN_sub n)))) in 
fst (proj1_sig y) <= snd (proj1_sig y).
by [].
elim (constructive_definite_description
    (fun x : R * R =>
     fst x <= snd x /\
     proj1_sig (IN_sub n) =
     (fun y : R => fst x <= y <= snd x))
    (BoundedClosedsectionUniqueRpair
       (proj1_sig (IN_sub n)) (proj2_sig (IN_sub n)))).
move=> x xp.
simpl.
apply (proj1 xp).
by [].
move=> xv yv xp yp H14.
subst xv.
rewrite (proof_irrelevance (In (Ensemble R) BoundedClosedSection yv) xp yp).
by [].
move=> H13.
suff: forall (xv yv : Ensemble R),forall (xp : (In (Ensemble R) BoundedClosedSection xv)),forall (yp : (In (Ensemble R) BoundedClosedSection yv)),
xv = yv -> (BoundedClosedsectionToRpair xv xp) = (BoundedClosedsectionToRpair yv yp).
move=> H14.
suff: In (Ensemble R) BoundedClosedSection (snd (ISN1, ISN2)).
move=> H15.
rewrite (H14 (F (ISN1, ISN2)) (snd (ISN1, ISN2)) (H8 (S n)) H15 H13).
simpl.
rewrite /BoundedClosedsectionToRpair.
suff: let y := (constructive_definite_description
        (fun x : R * R =>
         fst x <= snd x /\
         ISN2 = (fun y : R => fst x <= y <= snd x))
        (BoundedClosedsectionUniqueRpair ISN2 H15)) in
snd (proj1_sig y) - fst (proj1_sig y) = (b - a) / (2 * 2 ^ n).
by [].
elim (constructive_definite_description
        (fun x : R * R =>
         fst x <= snd x /\
         ISN2 = (fun y : R => fst x <= y <= snd x))
        (BoundedClosedsectionUniqueRpair ISN2 H15)).
rewrite /ISN2.
move=> x H16.
simpl.
suff: (BoundedClosedsectionL (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n)) +
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) / 2 = fst x.
move=> H17.
suff: (BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) = snd x.
move=> H18.
rewrite - H17.
rewrite - H18.
rewrite /Rdiv.
suff: let x1 := (BoundedClosedsectionL (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) in
let x2 := (BoundedClosedsectionR (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) in
(x2 - (x1 + x2) * / 2 = (b - a) * / (2 * 2 ^ n)).
by [].
move=> x1 x2.
rewrite - {1}(eps2 x2).
rewrite (Rmult_plus_distr_r x1 x2 (/ 2)).
rewrite (Rplus_comm (x1 * / 2) (x2 * / 2)).
rewrite /Rminus.
rewrite (Rplus_assoc (x2 * / 2) (x2 * / 2) (-(x2 * / 2 + x1 * / 2))).
rewrite (Ropp_plus_distr (x2 * / 2) (x1 * / 2)).
rewrite - (Rplus_assoc (x2 * / 2) (- (x2 * / 2)) (- (x1 * / 2))).
rewrite (Rplus_opp_r (x2 * / 2)).
rewrite (Rplus_0_l (- (x1 * / 2))).
rewrite (Ropp_mult_distr_l x1 (/ 2)).
rewrite - (Rmult_plus_distr_r x2 (- x1) (/ 2)).
rewrite /BoundedClosedsectionSize in H9.
rewrite /IN in H9.
rewrite /x1.
rewrite /x2.
rewrite (proof_irrelevance (In (Ensemble R) BoundedClosedSection (proj1_sig (IN_sub n))) (proj2_sig (IN_sub n)) (H8 n)).
rewrite /Rminus in H9.
rewrite (proj1 H9).
rewrite /Rdiv.
rewrite (Rmult_assoc (b + - a) (/ 2 ^ n) (/ 2)).
rewrite (Rinv_mult_distr 2 (2 ^ n)).
rewrite (Rmult_comm (/ 2) (/ 2 ^ n)).
by [].
apply (Rgt_not_eq 2 0).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rgt_trans (1 + 1) 1 0).
apply (Rlt_plus_1 1).
apply (Rlt_0_1).
apply (Rgt_not_eq (2 ^ n) 0).
elim n.
simpl.
rewrite /2.
apply Rlt_0_1.
move=> n0 H19.
simpl.
rewrite {1}/2.
rewrite - (INR_IPR 2).
simpl.
apply (Rmult_gt_0_compat (1 + 1) (2 ^ n0)).
apply (Rgt_trans (1 + 1) 1 0).
apply (Rlt_plus_1 1).
apply (Rlt_0_1).
apply H19.
suff: (BoundedClosedsectionL (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n)) +
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) / 2 <= BoundedClosedsectionR (proj1_sig (IN_sub n))
         (proj2_sig (IN_sub n)).
move=> H18.
apply (Rle_antisym (BoundedClosedsectionR (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n))) (snd x)).
suff: In R (fun y : R => fst x <= y <= snd x) (BoundedClosedsectionR (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n))).
move=> H19.
apply (proj2 H19).
rewrite - (proj2 H16).
apply conj.
apply H18.
apply (Req_le (BoundedClosedsectionR (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n))) (BoundedClosedsectionR (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n)))).
by [].
suff: In R (fun x : R =>
       (BoundedClosedsectionL (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n)) +
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) / 2 <= x <=
       BoundedClosedsectionR (proj1_sig (IN_sub n))
         (proj2_sig (IN_sub n)))
 (snd x).
move=> H19.
apply H19.
rewrite (proj2 H16).
apply conj.
apply (proj1 H16).
apply (Req_le (snd x) (snd x)).
by [].
suff: In R (fun x : R =>
       (BoundedClosedsectionL (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n)) +
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) / 2 <= x <=
       BoundedClosedsectionR (proj1_sig (IN_sub n))
         (proj2_sig (IN_sub n))) (fst x).
move=> H18.
apply (Rle_trans ((BoundedClosedsectionL (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n)) +
 BoundedClosedsectionR (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) / 2) (fst x) (BoundedClosedsectionR (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n)))).
apply H18.
apply H18.
rewrite (proj2 H16).
apply conj.
apply (Req_le (fst x) (fst x)).
by [].
apply (proj1 H16).
apply (Rle_antisym ((BoundedClosedsectionL (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n)) +
 BoundedClosedsectionR (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) / 2) (fst x)).
suff: In R (fun x : R =>
       (BoundedClosedsectionL (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n)) +
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) / 2 <= x <=
       BoundedClosedsectionR (proj1_sig (IN_sub n))
         (proj2_sig (IN_sub n))) (fst x).
move=> H18.
apply H18.
rewrite (proj2 H16).
apply conj.
apply (Req_le (fst x) (fst x)).
by [].
apply (proj1 H16).
suff: In R (fun y : R => fst x <= y <= snd x) ((BoundedClosedsectionL (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n)) +
 BoundedClosedsectionR (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) / 2).
move=> H17.
apply H17.
rewrite - (proj2 H16).
apply conj.
apply (Req_le ((BoundedClosedsectionL (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n)) +
 BoundedClosedsectionR (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) / 2) ((BoundedClosedsectionL (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n)) +
 BoundedClosedsectionR (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) / 2)).
by [].
suff: In R (fun x : R =>
       (BoundedClosedsectionL (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n)) +
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) / 2 <= x <=
       BoundedClosedsectionR (proj1_sig (IN_sub n))
         (proj2_sig (IN_sub n))) (fst x).
move=> H18.
apply (Rle_trans ((BoundedClosedsectionL (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n)) +
 BoundedClosedsectionR (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) / 2) (fst x) (BoundedClosedsectionR (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n)))).
apply H18.
apply H18.
rewrite (proj2 H16).
apply conj.
apply (Req_le (fst x) (fst x)).
by [].
apply (proj1 H16).
simpl.
rewrite /ISN2.
apply (Im_intro (R * R) (Ensemble R) (fun (x : (R * R)) => (fst x) <= (snd x)) (fun (x : (R * R)) => (fun (y : R) => (fst x) <= y <= (snd x)))
((BoundedClosedsectionL (proj1_sig (IN_sub n))
      (proj2_sig (IN_sub n)) +
    BoundedClosedsectionR (proj1_sig (IN_sub n))
      (proj2_sig (IN_sub n))) / 2 ,
   BoundedClosedsectionR (proj1_sig (IN_sub n))
     (proj2_sig (IN_sub n)))).
suff: (
  ((BoundedClosedsectionL (proj1_sig (IN_sub n))
     (proj2_sig (IN_sub n)) +
   BoundedClosedsectionR (proj1_sig (IN_sub n))
     (proj2_sig (IN_sub n))) / 2 <= BoundedClosedsectionR (proj1_sig (IN_sub n))
     (proj2_sig (IN_sub n)))).
by [].
rewrite /Rdiv.
rewrite - {2}(eps2 (BoundedClosedsectionR (proj1_sig (IN_sub n))
     (proj2_sig (IN_sub n)))).
rewrite (Rmult_plus_distr_r (BoundedClosedsectionL (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) (BoundedClosedsectionR (proj1_sig (IN_sub n))
   (proj2_sig (IN_sub n))) (/ 2)).
apply (Rplus_le_compat_r (BoundedClosedsectionR (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n)) * / 2) (BoundedClosedsectionL (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n)) * / 2) (BoundedClosedsectionR (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n)) * / 2)).
apply (Rmult_le_compat_r (/ 2) (BoundedClosedsectionL (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n))) (BoundedClosedsectionR (proj1_sig (IN_sub n))
  (proj2_sig (IN_sub n)))).
apply (Rlt_le 0 (/ 2)).
apply (Rinv_0_lt_compat 2).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rgt_trans (1 + 1) 1 0).
apply (Rlt_plus_1 1).
apply (Rlt_0_1).
rewrite /BoundedClosedsectionL.
rewrite /BoundedClosedsectionR.
rewrite /BoundedClosedsectionToRpair.
suff: let y := (constructive_definite_description
        (fun x : R * R =>
         fst x <= snd x /\
         proj1_sig (IN_sub n) =
         (fun y : R => fst x <= y <= snd x))
        (BoundedClosedsectionUniqueRpair
           (proj1_sig (IN_sub n)) (proj2_sig (IN_sub n)))) in 
fst (proj1_sig y) <= snd (proj1_sig y).
by [].
elim (constructive_definite_description
    (fun x : R * R =>
     fst x <= snd x /\
     proj1_sig (IN_sub n) =
     (fun y : R => fst x <= y <= snd x))
    (BoundedClosedsectionUniqueRpair
       (proj1_sig (IN_sub n)) (proj2_sig (IN_sub n)))).
move=> x xp.
simpl.
apply (proj1 xp).
by [].
move=> xv yv xp yp H14.
subst xv.
rewrite (proof_irrelevance (In (Ensemble R) BoundedClosedSection yv) xp yp).
by [].
move=> H12.
apply (proj1 (proj2 H9)).
apply (Finite_Set_Included nat (fun m : nat => In R (IN n) (An m)) (fun v : nat =>
         In R
           (Union R (fst (ISN1, ISN2)) (snd (ISN1, ISN2)))
           (An v))).
apply H12.
simpl.
move=> n0.
rewrite /IN.
rewrite /ISN1.
rewrite /ISN2.
rewrite /BoundedClosedsectionL.
rewrite /BoundedClosedsectionR.
rewrite /BoundedClosedsectionToRpair.
suff: let y := (constructive_definite_description
                 (fun x0 : R * R =>
                  fst x0 <= snd x0 /\
                  proj1_sig (IN_sub n) =
                  (fun y : R => fst x0 <= y <= snd x0))
                 (BoundedClosedsectionUniqueRpair
                    (proj1_sig (IN_sub n))
                    (proj2_sig (IN_sub n)))) in 
In nat (fun m : nat => In R (proj1_sig (IN_sub n)) (An m))
  n0 ->
In nat
  (fun v : nat =>
   In R
     (Union R
        (fun x : R =>
         fst
           (proj1_sig y) <= x <= (fst (proj1_sig y) + snd (proj1_sig y)) / 2)
         (fun x : R => (fst (proj1_sig y) + snd (proj1_sig y)) / 2 <= x <= 
snd (proj1_sig y))) (An v)) n0.
by [].
elim (constructive_definite_description
    (fun x0 : R * R =>
     fst x0 <= snd x0 /\
     proj1_sig (IN_sub n) =
     (fun y : R => fst x0 <= y <= snd x0))
    (BoundedClosedsectionUniqueRpair
       (proj1_sig (IN_sub n)) (proj2_sig (IN_sub n)))).
move=> x p.
simpl.
rewrite (proj2 p).
move=> H13.
elim (Rle_lt_dec (An n0) ((fst x + snd x) / 2)).
move=> H14.
apply (Union_introl R (fun x0 : R => fst x <= x0 <= (fst x + snd x) / 2)
        (fun x0 : R => (fst x + snd x) / 2 <= x0 <= snd x) (An n0)).
apply conj.
apply (proj1 H13).
apply H14.
move=> H14.
apply (Union_intror R (fun x0 : R => fst x <= x0 <= (fst x + snd x) / 2)
        (fun x0 : R => (fst x + snd x) / 2 <= x0 <= snd x) (An n0)).
apply conj.
apply (Rlt_le ((fst x + snd x) / 2) (An n0)).
apply H14.
apply (proj2 H13).
apply conj.
rewrite /IN.
simpl.
suff: let ISN1 := (fun x : R =>
         BoundedClosedsectionL (proj1_sig (IN_sub n))
           (proj2_sig (IN_sub n)) <= x <=
         (BoundedClosedsectionL (proj1_sig (IN_sub n))
            (proj2_sig (IN_sub n)) +
          BoundedClosedsectionR (proj1_sig (IN_sub n))
            (proj2_sig (IN_sub n))) / 2) in
let ISN2 := (fun x : R =>
        (BoundedClosedsectionL (proj1_sig (IN_sub n))
           (proj2_sig (IN_sub n)) +
         BoundedClosedsectionR (proj1_sig (IN_sub n))
           (proj2_sig (IN_sub n))) / 2 <= x <=
        BoundedClosedsectionR (proj1_sig (IN_sub n))
          (proj2_sig (IN_sub n))) in ~
Finite nat
  (fun m : nat =>
   In R
     (F (ISN1,ISN2)) (An m)).
by [].
move=> ISN1 ISN2.
suff:  ~
     Finite nat
       (fun v : nat =>
        In R (Union R (fst (ISN1,ISN2)) (snd (ISN1,ISN2))) (An v)).
move=> H11.
apply (H4 (ISN1,ISN2)).
move=> H12.
apply (proj1 (proj2 H9)).
apply (Finite_Set_Included nat (fun m : nat => In R (IN n) (An m)) (fun v : nat =>
         In R
           (Union R (fst (ISN1, ISN2)) (snd (ISN1, ISN2)))
           (An v))).
apply H12.
simpl.
move=> n0.
rewrite /IN.
rewrite /ISN1.
rewrite /ISN2.
rewrite /BoundedClosedsectionL.
rewrite /BoundedClosedsectionR.
rewrite /BoundedClosedsectionToRpair.
suff: let y := (constructive_definite_description
                 (fun x0 : R * R =>
                  fst x0 <= snd x0 /\
                  proj1_sig (IN_sub n) =
                  (fun y : R => fst x0 <= y <= snd x0))
                 (BoundedClosedsectionUniqueRpair
                    (proj1_sig (IN_sub n))
                    (proj2_sig (IN_sub n)))) in 
In nat (fun m : nat => In R (proj1_sig (IN_sub n)) (An m))
  n0 ->
In nat
  (fun v : nat =>
   In R
     (Union R
        (fun x : R =>
         fst
           (proj1_sig y) <= x <= (fst (proj1_sig y) + snd (proj1_sig y)) / 2)
         (fun x : R => (fst (proj1_sig y) + snd (proj1_sig y)) / 2 <= x <= 
snd (proj1_sig y))) (An v)) n0.
by [].
elim (constructive_definite_description
    (fun x0 : R * R =>
     fst x0 <= snd x0 /\
     proj1_sig (IN_sub n) =
     (fun y : R => fst x0 <= y <= snd x0))
    (BoundedClosedsectionUniqueRpair
       (proj1_sig (IN_sub n)) (proj2_sig (IN_sub n)))).
move=> x p.
simpl.
rewrite (proj2 p).
move=> H13.
elim (Rle_lt_dec (An n0) ((fst x + snd x) / 2)).
move=> H14.
apply (Union_introl R (fun x0 : R => fst x <= x0 <= (fst x + snd x) / 2)
        (fun x0 : R => (fst x + snd x) / 2 <= x0 <= snd x) (An n0)).
apply conj.
apply (proj1 H13).
apply H14.
move=> H14.
apply (Union_intror R (fun x0 : R => fst x <= x0 <= (fst x + snd x) / 2)
        (fun x0 : R => (fst x + snd x) / 2 <= x0 <= snd x) (An n0)).
apply conj.
apply (Rlt_le ((fst x + snd x) / 2) (An n0)).
apply H14.
apply (proj2 H13).


move=> H20.
apply (proj1 (proj2 H9)).

apply (Finite_Set_Included nat (fun m : nat => In R (IN n) (An m)) (fun v : nat =>
         In R
           (Union R (fst (ISN1, ISN2)) (snd (ISN1, ISN2)))
           (An v))).
apply H20.
simpl.
move=> n1.
rewrite /IN.
rewrite /ISN1.
rewrite /ISN2.
rewrite /BoundedClosedsectionL.
rewrite /BoundedClosedsectionR.
rewrite /BoundedClosedsectionToRpair.
suff: let y := (constructive_definite_description
                 (fun x1 : R * R =>
                  fst x1 <= snd x1 /\
                  proj1_sig (IN_sub n) =
                  (fun y : R => fst x1 <= y <= snd x1))
                 (BoundedClosedsectionUniqueRpair
                    (proj1_sig (IN_sub n))
                    (proj2_sig (IN_sub n)))) in 
In nat (fun m : nat => In R (proj1_sig (IN_sub n)) (An m))
  n1 ->
In nat
  (fun v : nat =>
   In R
     (Union R
        (fun x : R =>
         fst
           (proj1_sig y) <= x <= (fst (proj1_sig y) + snd (proj1_sig y)) / 2)
         (fun x : R => (fst (proj1_sig y) + snd (proj1_sig y)) / 2 <= x <= 
snd (proj1_sig y))) (An v)) n1.
by [].
elim (constructive_definite_description
                 (fun x1 : R * R =>
                  fst x1 <= snd x1 /\
                  proj1_sig (IN_sub n) =
                  (fun y : R => fst x1 <= y <= snd x1))
                 (BoundedClosedsectionUniqueRpair
                    (proj1_sig (IN_sub n))
                    (proj2_sig (IN_sub n)))).
move=> z zp.
simpl.
rewrite (proj2 zp).
move=> H13.
elim (Rle_lt_dec (An n1) ((fst z + snd z) / 2)).
move=> H14.
apply (Union_introl R (fun x0 : R => fst z <= x0 <= (fst z + snd z) / 2)
        (fun x0 : R => (fst z + snd z) / 2 <= x0 <= snd z) (An n1)).
apply conj.
apply (proj1 H13).
apply H14.
move=> H14.
apply (Union_intror R (fun x0 : R => fst z <= x0 <= (fst z + snd z) / 2)
        (fun x0 : R => (fst z + snd z) / 2 <= x0 <= snd z) (An n1)).
apply conj.
apply (Rlt_le ((fst z + snd z) / 2) (An n1)).
apply H14.
apply (proj2 H13).




suff: forall (n : nat), Included R (IN (S n)) (IN n).
move=> H11.
apply (H11 (S n)).

rewrite /IN.
simpl.
move=> n0 x.
rewrite /IN.
simpl.
suff:let ISN1 := (fun x0 : R =>
      BoundedClosedsectionL (proj1_sig (IN_sub n0))
        (proj2_sig (IN_sub n0)) <= x0 <=
      (BoundedClosedsectionL (proj1_sig (IN_sub n0))
         (proj2_sig (IN_sub n0)) +
       BoundedClosedsectionR (proj1_sig (IN_sub n0))
         (proj2_sig (IN_sub n0))) / 2) in
let ISN2 := (fun x0 : R =>
     (BoundedClosedsectionL (proj1_sig (IN_sub n0))
        (proj2_sig (IN_sub n0)) +
      BoundedClosedsectionR (proj1_sig (IN_sub n0))
        (proj2_sig (IN_sub n0))) / 2 <= x0 <=
     BoundedClosedsectionR (proj1_sig (IN_sub n0))
       (proj2_sig (IN_sub n0))) in
In R (F (ISN1 , ISN2)) x -> In R (proj1_sig (IN_sub n0)) x.
by [].
move=> ISN1 ISN2.
case (proj2 (H4 (ISN1,ISN2))).
move=> H12.
rewrite H12.
simpl.
rewrite /ISN1.
rewrite /BoundedClosedsectionL.
rewrite /BoundedClosedsectionR.
rewrite /BoundedClosedsectionToRpair.
suff: let y := (constructive_definite_description
           (fun x1 : R * R =>
            fst x1 <= snd x1 /\
            proj1_sig (IN_sub n0) =
            (fun y : R => fst x1 <= y <= snd x1))
           (BoundedClosedsectionUniqueRpair
              (proj1_sig (IN_sub n0))
              (proj2_sig (IN_sub n0)))) in 
In R (fun x0 : R => fst (proj1_sig y) <= x0 <= (fst (proj1_sig y) + snd (proj1_sig y)) / 2) x -> In R (proj1_sig (IN_sub n0)) x.
by [].
elim (constructive_definite_description
           (fun x1 : R * R =>
            fst x1 <= snd x1 /\
            proj1_sig (IN_sub n0) =
            (fun y : R => fst x1 <= y <= snd x1))
           (BoundedClosedsectionUniqueRpair
              (proj1_sig (IN_sub n0))
              (proj2_sig (IN_sub n0)))).
move=> z zp.
simpl.
rewrite (proj2 zp).
move=> H13.
apply conj.
apply (proj1 H13).
apply (Rle_trans x ((fst z + snd z) / 2) (snd z)).
apply (proj2 H13).
rewrite /Rdiv.
rewrite - {2}(eps2 (snd z)).
rewrite (Rmult_plus_distr_r (fst z) (snd z) (/ 2)).
apply (Rplus_le_compat_r (snd z * / 2) (fst z * / 2) (snd z * / 2)).
apply (Rmult_le_compat_r (/ 2) (fst z) (snd z)).
apply (Rlt_le 0 (/ 2)).
apply (Rinv_0_lt_compat 2).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rgt_trans (1 + 1) 1 0).
apply (Rlt_plus_1 1).
apply (Rlt_0_1).
apply (proj1 zp).
move=> H12.
rewrite H12.
simpl.
rewrite /ISN2.
rewrite /BoundedClosedsectionL.
rewrite /BoundedClosedsectionR.
rewrite /BoundedClosedsectionToRpair.
suff: let y := (constructive_definite_description
           (fun x1 : R * R =>
            fst x1 <= snd x1 /\
            proj1_sig (IN_sub n0) =
            (fun y : R => fst x1 <= y <= snd x1))
           (BoundedClosedsectionUniqueRpair
              (proj1_sig (IN_sub n0))
              (proj2_sig (IN_sub n0)))) in 
In R (fun x0 : R => (fst (proj1_sig y) + snd (proj1_sig y)) / 2 <= x0 <= snd (proj1_sig y)) x -> In R (proj1_sig (IN_sub n0)) x.
by [].
elim (constructive_definite_description
           (fun x1 : R * R =>
            fst x1 <= snd x1 /\
            proj1_sig (IN_sub n0) =
            (fun y : R => fst x1 <= y <= snd x1))
           (BoundedClosedsectionUniqueRpair
              (proj1_sig (IN_sub n0))
              (proj2_sig (IN_sub n0)))).
move=> z zp.
simpl.
rewrite (proj2 zp).
move=> H13.
apply conj.
apply (Rle_trans (fst z) ((fst z + snd z) / 2) x).
rewrite /Rdiv.
rewrite - {1}(eps2 (fst z)).
rewrite (Rmult_plus_distr_r (fst z) (snd z) (/ 2)).
apply (Rplus_le_compat_l (fst z * / 2) (fst z * / 2) (snd z * / 2)).
apply (Rmult_le_compat_r (/ 2) (fst z) (snd z)).
apply (Rlt_le 0 (/ 2)).
apply (Rinv_0_lt_compat 2).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rgt_trans (1 + 1) 1 0).
apply (Rlt_plus_1 1).
apply (Rlt_0_1).
apply (proj1 zp).
apply (proj1 H13).
apply (proj2 H13).
move=> n.
apply (proj2_sig ((fix IN (n0 : nat) :
         {I : Ensemble R |
         In (Ensemble R) BoundedClosedSection I} :=
         match n0 with
         | 0%nat =>
             exist
               (fun x : Ensemble R =>
                In (Ensemble R) BoundedClosedSection x)
               (fun x : R => a <= x <= b) H7
         | S n1 =>
             exist
               (fun x : Ensemble R =>
                In (Ensemble R) BoundedClosedSection x)
               (F
                  (fun x : R =>
                   BoundedClosedsectionL
                     (proj1_sig (IN n1))
                     (proj2_sig (IN n1)) <= x <=
                   (BoundedClosedsectionL
                      (proj1_sig (IN n1))
                      (proj2_sig (IN n1)) +
                    BoundedClosedsectionR
                      (proj1_sig (IN n1))
                      (proj2_sig (IN n1))) / 2,
                  fun x : R =>
                  (BoundedClosedsectionL
                     (proj1_sig (IN n1))
                     (proj2_sig (IN n1)) +
                   BoundedClosedsectionR
                     (proj1_sig (IN n1))
                     (proj2_sig (IN n1))) / 2 <= x <=
                  BoundedClosedsectionR
                    (proj1_sig (IN n1))
                    (proj2_sig (IN n1))))
               (H6 (proj1_sig (IN n1)) (proj2_sig (IN n1)))
         end) n)).
apply (BoundedClosedsectionDef a b H10).
move=> I H.
elim (proj2 (H4 (fun x : R =>
      BoundedClosedsectionL I H <= x <=
      (BoundedClosedsectionL I H +
       BoundedClosedsectionR I H) / 2,
     fun x : R =>
     (BoundedClosedsectionL I H +
      BoundedClosedsectionR I H) / 2 <= x <=
     BoundedClosedsectionR I H))).
move=> H6.
rewrite H6.
simpl.
apply (BoundedClosedsectionDef (BoundedClosedsectionL I H) ((BoundedClosedsectionL I H + BoundedClosedsectionR I H) /
   2)).
rewrite /Rdiv.
rewrite - {1}(eps2 (BoundedClosedsectionL I H)).
rewrite (Rmult_plus_distr_r (BoundedClosedsectionL I H) (BoundedClosedsectionR I H) (/ 2)).
apply (Rplus_le_compat_l (BoundedClosedsectionL I H * / 2) (BoundedClosedsectionL I H * / 2) (BoundedClosedsectionR I H * / 2)).
apply (Rmult_le_compat_r (/ 2) (BoundedClosedsectionL I H) (BoundedClosedsectionR I H)).
apply (Rlt_le 0 (/ 2)).
apply (Rinv_0_lt_compat 2).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
rewrite /BoundedClosedsectionL.
rewrite /BoundedClosedsectionR.
rewrite /BoundedClosedsectionToRpair.
suff: let y := constructive_definite_description
        (fun x : R * R =>
         fst x <= snd x /\
         I = (fun y : R => fst x <= y <= snd x))
        (BoundedClosedsectionUniqueRpair I H) in
fst (proj1_sig y) <= snd (proj1_sig y).
by [].
elim (constructive_definite_description
    (fun x : R * R =>
     fst x <= snd x /\
     I = (fun y : R => fst x <= y <= snd x))
    (BoundedClosedsectionUniqueRpair I H)).
move=> x xp.
simpl.
apply (proj1 xp).
move=> H6.
rewrite H6.
simpl.
apply (BoundedClosedsectionDef ((BoundedClosedsectionL I H + BoundedClosedsectionR I H) / 2) (BoundedClosedsectionR I H) ).
rewrite /Rdiv.
rewrite - {2}(eps2 (BoundedClosedsectionR I H)).
rewrite (Rmult_plus_distr_r (BoundedClosedsectionL I H) (BoundedClosedsectionR I H) (/ 2)).
apply (Rplus_le_compat_r (BoundedClosedsectionR I H * / 2) (BoundedClosedsectionL I H * / 2) (BoundedClosedsectionR I H * / 2)).
apply (Rmult_le_compat_r (/ 2) (BoundedClosedsectionL I H) (BoundedClosedsectionR I H)).
apply (Rlt_le 0 (/ 2)).
apply (Rinv_0_lt_compat 2).
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
rewrite /BoundedClosedsectionL.
rewrite /BoundedClosedsectionR.
rewrite /BoundedClosedsectionToRpair.
suff: let y := constructive_definite_description
        (fun x : R * R =>
         fst x <= snd x /\
         I = (fun y : R => fst x <= y <= snd x))
        (BoundedClosedsectionUniqueRpair I H) in
fst (proj1_sig y) <= snd (proj1_sig y).
by [].
elim (constructive_definite_description
    (fun x : R * R =>
     fst x <= snd x /\
     I = (fun y : R => fst x <= y <= snd x))
    (BoundedClosedsectionUniqueRpair I H)).
move=> x xp.
simpl.
apply (proj1 xp).
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