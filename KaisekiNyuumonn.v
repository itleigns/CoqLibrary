From mathcomp
Require Import ssreflect.
Require Import Reals.
Require Import Coq.Sets.Ensembles.
Local Open Scope R_scope.
Require Export Rdefinitions.
Require Import Classical.

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

