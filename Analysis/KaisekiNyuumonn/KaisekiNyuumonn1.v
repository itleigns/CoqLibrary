Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "Tools" as Tools.
Add LoadPath "BasicProperty" as BasicProperty.

From mathcomp
Require Import ssreflect.
Require Import Reals.
Require Import Coq.Sets.Ensembles.
Require Export QArith_base.
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
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Arith.Even.
Require Import Coq.Arith.Div2.
Require Import MyAlgebraicStructure.MyField.
Require Import MyAlgebraicStructure.MyVectorSpace.
Require Import Tools.MySum.

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

Section Kaisekinyuumonn1.

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

Inductive BoundedClosedSection (LR : {lr : (R * R) | (fst lr) <= (snd lr)}): Ensemble R := 
 BoundedClosedSection_intro : forall x:R, (fst (proj1_sig LR)) <= x -> x <= (snd (proj1_sig LR)) -> In R (BoundedClosedSection LR) x.

Definition BoundedClosedSectionSet := {X : Ensemble R | 
  exists LR : {lr : R * R | (fst lr) <= (snd lr)}, 
  X = (BoundedClosedSection LR)}.

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

Lemma BoundedClosedSectionUniqueExistsPair : 
forall (A : BoundedClosedSectionSet), exists! LR : {lr : R * R | (fst lr) <= (snd lr)}, (proj1_sig A) = (BoundedClosedSection LR).
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

Definition BoundedClosedSectionToPair (A : BoundedClosedSectionSet) : ({lr : R * R | fst lr <= snd lr})
:= proj1_sig (constructive_definite_description (fun X : {lr : R * R | fst lr <= snd lr} 
=> (proj1_sig A) = (BoundedClosedSection X)) (BoundedClosedSectionUniqueExistsPair A)).

Definition BoundedClosedSectionToL (A : BoundedClosedSectionSet) : R
:= fst (proj1_sig (BoundedClosedSectionToPair A)).

Definition BoundedClosedSectionToR (A : BoundedClosedSectionSet) : R
:= snd (proj1_sig (BoundedClosedSectionToPair A)).

Definition BoundedClosedSectionToSize (A : BoundedClosedSectionSet) : R
:= (BoundedClosedSectionToR A) - (BoundedClosedSectionToL A).

Lemma BoundedClosedSectionEqual : forall A : BoundedClosedSectionSet, (proj1_sig A) = (BoundedClosedSection (BoundedClosedSectionToPair A)).
Proof.
move=> A.
rewrite /BoundedClosedSectionToPair.
elim (constructive_definite_description
        (fun X : {lr : R * R | fst lr <= snd lr} => proj1_sig A = BoundedClosedSection X)
        (BoundedClosedSectionUniqueExistsPair A)).
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

Lemma BoundedClosedSectionSetEqual : forall (LR : {lr : (R * R) | (fst lr) <= (snd lr)}), forall (P : (exists LR2 : {lr : (R * R) | (fst lr) <= (snd lr)}, (BoundedClosedSection LR) = (BoundedClosedSection LR2))),
(BoundedClosedSectionToPair (exist (fun (A : Ensemble R) => (exists LR2 : {lr : R * R | (fst lr) <= (snd lr)}, A = (BoundedClosedSection LR2))) (BoundedClosedSection LR) P)) = LR.
Proof.
move=> LR H1.
rewrite /BoundedClosedSectionToPair.
elim (constructive_definite_description
     (fun X : {lr : R * R | fst lr <= snd lr} =>
      proj1_sig
        (exist
           (fun A : Ensemble R =>
            exists LR2 : {lr : R * R | fst lr <= snd lr},
              A = BoundedClosedSection LR2)
           (BoundedClosedSection LR) H1) =
      BoundedClosedSection X)
     (BoundedClosedSectionUniqueExistsPair
        (exist
           (fun A : Ensemble R =>
            exists LR2 : {lr : R * R | fst lr <= snd lr},
              A = BoundedClosedSection LR2)
           (BoundedClosedSection LR) H1))).
move=> x xp.
simpl.
suff: LR = x.
move=> H2.
rewrite H2.
by [].
suff: BoundedClosedSection LR = BoundedClosedSection x.
move=> H2.
apply (let H3 := (BoundedClosedSectionUniqueExistsPair (exist 
(fun (A : Ensemble R) => exists LR2 : {lr : R * R | fst lr <= snd lr},
       A = BoundedClosedSection LR2) (BoundedClosedSection LR) H1)) in
(proj2 (proj2 (unique_existence (fun (LR0 : {lr : R * R | fst lr <= snd lr}) =>
    proj1_sig
      (exist
         (fun A : Ensemble R =>
          exists LR2 : {lr : R * R | fst lr <= snd lr},
            A = BoundedClosedSection LR2)
         (BoundedClosedSection LR) H1) =
    BoundedClosedSection LR0)) H3))).
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
suff: (fun m : nat =>
   BoundedClosedSectionToR (IN m) - BoundedClosedSectionToL (IN m)) 
   = (RSequencePlus (fun m : nat => BoundedClosedSectionToR (IN m)) (RSequenceOpp (fun m : nat => BoundedClosedSectionToL (IN m)))).
move=> H11.
rewrite H11.
apply (Theorem_2_5_1_plus (fun m : nat => BoundedClosedSectionToR (IN m)) (RSequenceOpp
        (fun m : nat => BoundedClosedSectionToL (IN m))) b (- a)).
apply H9.
apply (Theorem_2_5_1_opp (fun m : nat => BoundedClosedSectionToL (IN m)) a).
apply H5.
apply (functional_extensionality (fun m : nat => BoundedClosedSectionToR (IN m) - BoundedClosedSectionToL (IN m)) 
(RSequencePlus (fun m : nat => BoundedClosedSectionToR (IN m)) (RSequenceOpp (fun m : nat => BoundedClosedSectionToL (IN m))))).
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

Definition Subsequence (T : Type) (ABn An : nat -> T) : Prop :=
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

Lemma Two_Gt_Zero : 2 > 0.
rewrite /2.
rewrite - (INR_IPR 2).
simpl.
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
Qed.

Lemma Two_Neq_Zero : 2 <> 0.
apply (Rgt_not_eq 2 0 Two_Gt_Zero).
Qed.

Lemma Two_Pow_Gt_Zero : forall n : nat, 2 ^ n > 0.
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
exists (fun (k : nat) => An ((fix Bn (n : nat) : nat := 
match n with 
  | O => (G O O)
  | S n0 => (G (S n0) (S (Bn n0)))
end) k)).
apply conj.
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
suff: (exists! x : R, (forall n : nat, In R (proj1_sig (IN n)) x)) /\ (forall x : R, (forall n : nat, In R (proj1_sig (IN n)) x) -> (Un_cv (fun m : nat => BoundedClosedSectionToL (IN m)) x) /\ (Un_cv (fun m : nat => BoundedClosedSectionToR (IN m)) x)).
move=> H8.
suff: exists x : R, (forall n : nat, In R (proj1_sig (IN n)) x).
elim.
move=> x H9.
exists x.
apply (Proposition_2_7 (fun m : nat => BoundedClosedSectionToL (IN m)) (fun m : nat => BoundedClosedSectionToR (IN m)) x (proj1 (proj2 H8 x H9)) (proj2 (proj2 H8 x H9)) (fun k : nat =>
   An
     ((fix Bn (n : nat) : nat :=
         match n with
         | 0%nat => G 0%nat 0%nat
         | S n0 => G (S n0) (S (Bn n0))
         end) k))).
move=> n.
suff: In R (BoundedClosedSection (BoundedClosedSectionToPair (IN n))) (An
  ((fix Bn (n0 : nat) : nat :=
      match n0 with
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
apply (proj1 (proj1 (H7 (S n0)
        (S
           ((fix Bn (n1 : nat) : nat :=
               match n1 with
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
apply (functional_extensionality (fun n : nat => (b - a) / 2 ^ n) (RSequenceMult (fun _ : nat => b - a)
  (fun n : nat => 1 / 2 ^ n))).
move=> n.
rewrite /Rdiv.
rewrite - (Rmult_1_l (/ 2 ^ n)).
by [].
apply (functional_extensionality (fun m : nat => BoundedClosedSectionToR (IN m) - BoundedClosedSectionToL (IN m)) (fun n : nat => (b - a) / 2 ^ n)).
move=> n.
rewrite - (proj1 (H6 n)).
by [].
suff: forall (n m : nat), (exists ! x : nat,
     is_min_nat
       (fun k : nat => In R (proj1_sig (IN n)) (An k) /\ (k >= m)%nat) x).
move=> H7.
exists (fun (n m : nat) => proj1_sig (constructive_definite_description (fun (l : nat) => is_min_nat
    (fun k : nat => In R (proj1_sig (IN n)) (An k) /\ (k >= m)%nat) l) (H7 n m))).
move=> n m.
elim (constructive_definite_description
        (fun l : nat =>
         is_min_nat
           (fun k : nat =>
            In R (proj1_sig (IN n)) (An k) /\ (k >= m)%nat) l)
        (H7 n m)).
simpl.
by [].
move=> n m.
apply (unique_existence (fun x : nat => is_min_nat
    (fun k : nat => In R (proj1_sig (IN n)) (An k) /\ (k >= m)%nat) x)).
apply conj.
apply (Exist_min_nat (fun k : nat => In R (proj1_sig (IN n)) (An k) /\ (k >= m)%nat)).
apply (NNPP (Inhabited nat
  (fun k : nat => In R (proj1_sig (IN n)) (An k) /\ (k >= m)%nat))).
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
suff: forall (I : BoundedClosedSectionSet), exists LR : {lr : R * R | fst lr <= snd lr}, 
(F (
BoundedClosedSection (exist (fun x : R * R => (fst x) <= (snd x)) ((BoundedClosedSectionToL I) , ((BoundedClosedSectionToL I) + (BoundedClosedSectionToR I)) / 2) (H6 I))
,BoundedClosedSection (exist (fun x : R * R => (fst x) <= (snd x)) (((BoundedClosedSectionToL I) + (BoundedClosedSectionToR I)) / 2, (BoundedClosedSectionToR I)) (H7 I))
)) = BoundedClosedSection LR.
move=> H8.
suff: forall (I : BoundedClosedSectionSet),
Included R (F (
BoundedClosedSection (exist (fun x : R * R => (fst x) <= (snd x)) ((BoundedClosedSectionToL I) , ((BoundedClosedSectionToL I) + (BoundedClosedSectionToR I)) / 2) (H6 I))
,BoundedClosedSection (exist (fun x : R * R => (fst x) <= (snd x)) (((BoundedClosedSectionToL I) + (BoundedClosedSectionToR I)) / 2, (BoundedClosedSectionToR I)) (H7 I))
)) (proj1_sig I).
move=> H9.
suff: exists LR : {lr : R * R | fst lr <= snd lr}, BoundedClosedSection (exist (fun lr : (R * R) => (fst lr) <= (snd lr)) (a,b) H4) = BoundedClosedSection LR.
move=> H10.
suff: (let IN := (fix IN (n : nat) : BoundedClosedSectionSet := 
match n with
  | O => exist (fun X : (Ensemble R) => exists LR : {lr : R * R | (fst lr) <= (snd lr)}, 
  X = (BoundedClosedSection LR)) (BoundedClosedSection (exist (fun lr : (R * R) => (fst lr) <= (snd lr)) (a,b) H4)) H10
  | S n0 => exist (fun X : (Ensemble R) => exists LR : {lr : R * R | (fst lr) <= (snd lr)}, 
  X = (BoundedClosedSection LR)) (F (
BoundedClosedSection (exist (fun x : R * R => (fst x) <= (snd x)) ((BoundedClosedSectionToL (IN n0)) , ((BoundedClosedSectionToL (IN n0)) + (BoundedClosedSectionToR (IN n0))) / 2) (H6 (IN n0)))
,BoundedClosedSection (exist (fun x : R * R => (fst x) <= (snd x)) (((BoundedClosedSectionToL (IN n0)) + (BoundedClosedSectionToR (IN n0))) / 2, (BoundedClosedSectionToR (IN n0))) (H7 (IN n0)))
))
 (H8 (IN n0))
end) in (exists IN : nat -> BoundedClosedSectionSet,
  forall n : nat,
  BoundedClosedSectionToSize (IN n) = (b - a) / 2 ^ n /\
  ~
  Finite nat
    (fun m : nat => In R (proj1_sig (IN n)) (An m)) /\
  Included R (proj1_sig (IN (S n))) (proj1_sig (IN n)))).
by [].
move=> IN.
exists IN.
move=> n.
elim n.
apply conj.
rewrite /BoundedClosedSectionToSize.
rewrite /BoundedClosedSectionToR.
rewrite /BoundedClosedSectionToL.
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr)
                 (a, b) H4) H10).
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
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr)
                 (a, b) H4) H10).
simpl.
apply (Rge_le (An m) a).
apply (H3 (An m)).
apply (Im_intro nat R (Full_set nat) An m).
by [].
by [].
rewrite /IN.
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr)
                 (a, b) H4) H10).
simpl.
apply (H2 (An m)).
apply (Im_intro nat R (Full_set nat) An m).
by [].
by [].
apply (H9 (IN O)).
move=> n0 H11.
simpl.
case (proj2 (H5 (
BoundedClosedSection
         (exist (fun (lr : R * R) => fst lr <= snd lr) (BoundedClosedSectionToL (IN n0),
         (BoundedClosedSectionToL (IN n0) +
          BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0))),
BoundedClosedSection
        (exist (fun (lr : R * R) => fst lr <= snd lr) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2,
        BoundedClosedSectionToR (IN n0)) (H7 (IN n0)))
))).
simpl.
move=> H12.
apply conj.
suff:exists LR : {lr : R * R | fst lr <= snd lr}, 
 (BoundedClosedSection
        (exist (fun lr : R * R => fst lr <= snd lr)
           (BoundedClosedSectionToL (IN n0),
           (BoundedClosedSectionToL (IN n0) +
            BoundedClosedSectionToR (IN n0)) / 2)
           (H6 (IN n0)))) = BoundedClosedSection LR.
move=> H13.
rewrite (sig_map (fun X : Ensemble R =>
      exists LR : {lr : R * R | fst lr <= snd lr},
        X = BoundedClosedSection LR) 
(exist
     (fun X : Ensemble R =>
      exists LR : {lr : R * R | fst lr <= snd lr},
        X = BoundedClosedSection LR)
     (F
        (BoundedClosedSection
           (exist (fun x : R * R => fst x <= snd x)
              (BoundedClosedSectionToL (IN n0),
              (BoundedClosedSectionToL (IN n0) +
               BoundedClosedSectionToR (IN n0)) / 2)
              (H6 (IN n0))),
        BoundedClosedSection
          (exist (fun x : R * R => fst x <= snd x)
             ((BoundedClosedSectionToL (IN n0) +
               BoundedClosedSectionToR (IN n0)) / 2,
             BoundedClosedSectionToR (IN n0)) 
             (H7 (IN n0)))))
     (H8 (IN n0)))
(exist (fun X : Ensemble R =>
      exists LR : {lr : R * R | fst lr <= snd lr},
        X = BoundedClosedSection LR)
(BoundedClosedSection
        (exist (fun lr : R * R => fst lr <= snd lr)
           (BoundedClosedSectionToL (IN n0),
           (BoundedClosedSectionToL (IN n0) +
            BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0))))
H13)).
rewrite /BoundedClosedSectionToSize.
rewrite /BoundedClosedSectionToR.
rewrite /BoundedClosedSectionToL.
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr)
                 (BoundedClosedSectionToL (IN n0) , (BoundedClosedSectionToL (IN n0) +
          BoundedClosedSectionToR (IN n0)) / 2) (H6 (IN n0))) H13).
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
apply (proj1 (H5 (BoundedClosedSection
           (exist (fun x : R * R => fst x <= snd x)
              (BoundedClosedSectionToL (IN n0),
              (BoundedClosedSectionToL (IN n0) +
               BoundedClosedSectionToR (IN n0)) / 2)
              (H6 (IN n0))),
        BoundedClosedSection
          (exist (fun x : R * R => fst x <= snd x)
             ((BoundedClosedSectionToL (IN n0) +
               BoundedClosedSectionToR (IN n0)) / 2,
             BoundedClosedSectionToR (IN n0)) 
             (H7 (IN n0)))))).
simpl.
suff: (Union R
        (BoundedClosedSection
           (exist (fun x : R * R => fst x <= snd x)
              (BoundedClosedSectionToL (IN n0),
              (BoundedClosedSectionToL (IN n0) +
               BoundedClosedSectionToR (IN n0)) / 2)
              (H6 (IN n0))))
        (BoundedClosedSection
           (exist (fun x : R * R => fst x <= snd x)
              ((BoundedClosedSectionToL (IN n0) +
                BoundedClosedSectionToR (IN n0)) / 2,
              BoundedClosedSectionToR (IN n0))
              (H7 (IN n0))))) = (proj1_sig (IN n0)).
move=> H14.
rewrite H14.
apply (proj1 (proj2 H11)).
apply (Extensionality_Ensembles R (Union R
  (BoundedClosedSection
     (exist (fun x : R * R => fst x <= snd x)
        (BoundedClosedSectionToL (IN n0),
        (BoundedClosedSectionToL (IN n0) +
         BoundedClosedSectionToR (IN n0)) / 2)
        (H6 (IN n0))))
  (BoundedClosedSection
     (exist (fun x : R * R => fst x <= snd x)
        ((BoundedClosedSectionToL (IN n0) +
          BoundedClosedSectionToR (IN n0)) / 2,
        BoundedClosedSectionToR (IN n0)) 
        (H7 (IN n0))))) (proj1_sig (IN n0))).
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
apply (Rle_trans (fst (proj1_sig (BoundedClosedSectionToPair (IN n0)))) ((BoundedClosedSectionToL (IN n0) +
       BoundedClosedSectionToR (IN n0)) / 2) x1).
apply (H6 (IN n0)).
apply H14.
apply H15.
move=> x.
rewrite (BoundedClosedSectionEqual (IN n0)).
case.
move=> x0 H14 H15.
case (Rle_lt_dec x0 ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2)).
move=> H16.
apply (Union_introl R
     (BoundedClosedSection
        (exist (fun x1 : R * R => fst x1 <= snd x1)
           (BoundedClosedSectionToL (IN n0),
           (BoundedClosedSectionToL (IN n0) +
            BoundedClosedSectionToR (IN n0)) / 2)
           (H6 (IN n0))))
     (BoundedClosedSection
        (exist (fun x1 : R * R => fst x1 <= snd x1)
           ((BoundedClosedSectionToL (IN n0) +
             BoundedClosedSectionToR (IN n0)) / 2,
           BoundedClosedSectionToR (IN n0)) 
           (H7 (IN n0))))).
apply (BoundedClosedSection_intro (exist (fun x1 : R * R => fst x1 <= snd x1)
        (BoundedClosedSectionToL (IN n0),
        (BoundedClosedSectionToL (IN n0) +
         BoundedClosedSectionToR (IN n0)) / 2)
        (H6 (IN n0)))).
apply H14.
apply H16.
move=> H16.
apply (Union_intror R
     (BoundedClosedSection
        (exist (fun x1 : R * R => fst x1 <= snd x1)
           (BoundedClosedSectionToL (IN n0),
           (BoundedClosedSectionToL (IN n0) +
            BoundedClosedSectionToR (IN n0)) / 2)
           (H6 (IN n0))))
     (BoundedClosedSection
        (exist (fun x1 : R * R => fst x1 <= snd x1)
           ((BoundedClosedSectionToL (IN n0) +
             BoundedClosedSectionToR (IN n0)) / 2,
           BoundedClosedSectionToR (IN n0)) 
           (H7 (IN n0))))).
apply (BoundedClosedSection_intro (exist (fun x1 : R * R => fst x1 <= snd x1)
        ((BoundedClosedSectionToL (IN n0) +
          BoundedClosedSectionToR (IN n0)) / 2,
        BoundedClosedSectionToR (IN n0)) 
        (H7 (IN n0)))).
simpl.
apply (Rlt_le ((BoundedClosedSectionToL (IN n0) +
       BoundedClosedSectionToR (IN n0)) / 2) x0 H16).
simpl.
apply H15.
apply H13.
simpl.
apply (H9 (IN (S n0))).
move=> H12.
apply conj.
suff:exists LR : {lr : R * R | fst lr <= snd lr}, 
 (BoundedClosedSection
        (exist (fun lr : R * R => fst lr <= snd lr)
           ((BoundedClosedSectionToL (IN n0) +
            BoundedClosedSectionToR (IN n0)) / 2,
            BoundedClosedSectionToR (IN n0))
           (H7 (IN n0)))) = BoundedClosedSection LR.
move=> H13.
rewrite (sig_map (fun X : Ensemble R =>
      exists LR : {lr : R * R | fst lr <= snd lr},
        X = BoundedClosedSection LR) 
(exist
     (fun X : Ensemble R =>
      exists LR : {lr : R * R | fst lr <= snd lr},
        X = BoundedClosedSection LR)
     (F
        (BoundedClosedSection
           (exist (fun x : R * R => fst x <= snd x)
              (BoundedClosedSectionToL (IN n0),
              (BoundedClosedSectionToL (IN n0) +
               BoundedClosedSectionToR (IN n0)) / 2)
              (H6 (IN n0))),
        BoundedClosedSection
          (exist (fun x : R * R => fst x <= snd x)
             ((BoundedClosedSectionToL (IN n0) +
               BoundedClosedSectionToR (IN n0)) / 2,
             BoundedClosedSectionToR (IN n0)) 
             (H7 (IN n0)))))
     (H8 (IN n0)))
(exist (fun X : Ensemble R =>
      exists LR : {lr : R * R | fst lr <= snd lr},
        X = BoundedClosedSection LR)
(BoundedClosedSection
        (exist (fun lr : R * R => fst lr <= snd lr)
           ((BoundedClosedSectionToL (IN n0) +
            BoundedClosedSectionToR (IN n0)) / 2,
            BoundedClosedSectionToR (IN n0)) (H7 (IN n0))))
H13)).
rewrite /BoundedClosedSectionToSize.
rewrite /BoundedClosedSectionToR.
rewrite /BoundedClosedSectionToL.
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr)
                 ((BoundedClosedSectionToL (IN n0) +
          BoundedClosedSectionToR (IN n0)) / 2, BoundedClosedSectionToR (IN n0)) (H7 (IN n0))) H13).
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
apply (proj1 (H5 (BoundedClosedSection
           (exist (fun x : R * R => fst x <= snd x)
              (BoundedClosedSectionToL (IN n0),
              (BoundedClosedSectionToL (IN n0) +
               BoundedClosedSectionToR (IN n0)) / 2)
              (H6 (IN n0))),
        BoundedClosedSection
          (exist (fun x : R * R => fst x <= snd x)
             ((BoundedClosedSectionToL (IN n0) +
               BoundedClosedSectionToR (IN n0)) / 2,
             BoundedClosedSectionToR (IN n0)) 
             (H7 (IN n0)))))).
simpl.
suff: (Union R
        (BoundedClosedSection
           (exist (fun x : R * R => fst x <= snd x)
              (BoundedClosedSectionToL (IN n0),
              (BoundedClosedSectionToL (IN n0) +
               BoundedClosedSectionToR (IN n0)) / 2)
              (H6 (IN n0))))
        (BoundedClosedSection
           (exist (fun x : R * R => fst x <= snd x)
              ((BoundedClosedSectionToL (IN n0) +
                BoundedClosedSectionToR (IN n0)) / 2,
              BoundedClosedSectionToR (IN n0))
              (H7 (IN n0))))) = (proj1_sig (IN n0)).
move=> H14.
rewrite H14.
apply (proj1 (proj2 H11)).
apply (Extensionality_Ensembles R (Union R
  (BoundedClosedSection
     (exist (fun x : R * R => fst x <= snd x)
        (BoundedClosedSectionToL (IN n0),
        (BoundedClosedSectionToL (IN n0) +
         BoundedClosedSectionToR (IN n0)) / 2)
        (H6 (IN n0))))
  (BoundedClosedSection
     (exist (fun x : R * R => fst x <= snd x)
        ((BoundedClosedSectionToL (IN n0) +
          BoundedClosedSectionToR (IN n0)) / 2,
        BoundedClosedSectionToR (IN n0)) 
        (H7 (IN n0))))) (proj1_sig (IN n0))).
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
apply (Rle_trans (fst (proj1_sig (BoundedClosedSectionToPair (IN n0)))) ((BoundedClosedSectionToL (IN n0) +
       BoundedClosedSectionToR (IN n0)) / 2) x1).
apply (H6 (IN n0)).
apply H14.
apply H15.
move=> x.
rewrite (BoundedClosedSectionEqual (IN n0)).
case.
move=> x0 H14 H15.
case (Rle_lt_dec x0 ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2)).
move=> H16.
apply (Union_introl R
     (BoundedClosedSection
        (exist (fun x1 : R * R => fst x1 <= snd x1)
           (BoundedClosedSectionToL (IN n0),
           (BoundedClosedSectionToL (IN n0) +
            BoundedClosedSectionToR (IN n0)) / 2)
           (H6 (IN n0))))
     (BoundedClosedSection
        (exist (fun x1 : R * R => fst x1 <= snd x1)
           ((BoundedClosedSectionToL (IN n0) +
             BoundedClosedSectionToR (IN n0)) / 2,
           BoundedClosedSectionToR (IN n0)) 
           (H7 (IN n0))))).
apply (BoundedClosedSection_intro (exist (fun x1 : R * R => fst x1 <= snd x1)
        (BoundedClosedSectionToL (IN n0),
        (BoundedClosedSectionToL (IN n0) +
         BoundedClosedSectionToR (IN n0)) / 2)
        (H6 (IN n0)))).
apply H14.
apply H16.
move=> H16.
apply (Union_intror R
     (BoundedClosedSection
        (exist (fun x1 : R * R => fst x1 <= snd x1)
           (BoundedClosedSectionToL (IN n0),
           (BoundedClosedSectionToL (IN n0) +
            BoundedClosedSectionToR (IN n0)) / 2)
           (H6 (IN n0))))
     (BoundedClosedSection
        (exist (fun x1 : R * R => fst x1 <= snd x1)
           ((BoundedClosedSectionToL (IN n0) +
             BoundedClosedSectionToR (IN n0)) / 2,
           BoundedClosedSectionToR (IN n0)) 
           (H7 (IN n0))))).
apply (BoundedClosedSection_intro (exist (fun x1 : R * R => fst x1 <= snd x1)
        ((BoundedClosedSectionToL (IN n0) +
          BoundedClosedSectionToR (IN n0)) / 2,
        BoundedClosedSectionToR (IN n0)) 
        (H7 (IN n0)))).
simpl.
apply (Rlt_le ((BoundedClosedSectionToL (IN n0) +
       BoundedClosedSectionToR (IN n0)) / 2) x0 H16).
simpl.
apply H15.
apply (H9 (IN (S n0))).
exists (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H4).
by [].
move=> I.
case (proj2 (H5 (BoundedClosedSection
        (exist (fun x : R * R => fst x <= snd x)
           (BoundedClosedSectionToL I,
           (BoundedClosedSectionToL I +
            BoundedClosedSectionToR I) / 2) 
           (H6 I)),
     BoundedClosedSection
       (exist (fun x : R * R => fst x <= snd x)
          ((BoundedClosedSectionToL I +
            BoundedClosedSectionToR I) / 2,
          BoundedClosedSectionToR I) (H7 I))))).
move=> H9.
rewrite H9.
simpl.
rewrite (BoundedClosedSectionEqual I).
move=> x.
case.
move=> x0 H10 H11.
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair I)).
apply H10.
apply (Rle_trans x0 (snd
        (proj1_sig
           (exist (fun x : R * R => fst x <= snd x)
              (BoundedClosedSectionToL I,
              (BoundedClosedSectionToL I +
               BoundedClosedSectionToR I) / 2) 
              (H6 I)))) (snd (proj1_sig (BoundedClosedSectionToPair I)))).
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
apply (Rle_trans (fst (proj1_sig (BoundedClosedSectionToPair I))) ((BoundedClosedSectionToL I +
               BoundedClosedSectionToR I) / 2) x0).
apply (H6 I).
apply H10.
apply H11.
move=> x.
case (proj2 (H5 (BoundedClosedSection
       (exist (fun x0 : R * R => fst x0 <= snd x0)
          (BoundedClosedSectionToL x,
          (BoundedClosedSectionToL x +
           BoundedClosedSectionToR x) / 2) 
          (H6 x)),
    BoundedClosedSection
      (exist (fun x0 : R * R => fst x0 <= snd x0)
         ((BoundedClosedSectionToL x +
           BoundedClosedSectionToR x) / 2,
         BoundedClosedSectionToR x) (H7 x))))).
move=> H8.
rewrite H8.
simpl.
exists (exist (fun x0 : R * R => fst x0 <= snd x0)
       (BoundedClosedSectionToL x,
       (BoundedClosedSectionToL x +
        BoundedClosedSectionToR x) / 2) 
       (H6 x)).
by [].
move=> H8.
rewrite H8.
simpl.
exists (exist (fun x0 : R * R => fst x0 <= snd x0)
       ((BoundedClosedSectionToL x +
         BoundedClosedSectionToR x) / 2,
       BoundedClosedSectionToR x) (H7 x)).
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
move=> An H1.
elim (H1 1 Rlt_0_1).
move => N H2.
suff: (Finite R (fun x => exists (n0 : nat), (Rabs (An n0)) = x /\ (n0 <= N)%nat)).
move=> H3.
apply (proj2 (bounded_abs (fun x : R => EUn An x))).
elim (Finite_max_R (fun x : R =>
        exists n0 : nat, (Rabs (An n0)) = x /\ (n0 <= N)%nat) H3).
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
apply (Inhabited_intro R (fun x : R =>
   exists n0 : nat, Rabs (An n0) = x /\ (n0 <= N)%nat) (Rabs (An N))).
exists N.
by [].
suff: (Im nat R (fun x : nat => (x < (S N))%nat) (fun n : nat => (Rabs (An n)))) = (fun x : R =>
   exists n0 : nat, Rabs (An n0) = x /\ (n0 <= N)%nat).
move=> H3.
rewrite - H3.
apply (finite_image nat R (fun x : nat => (x < (S N))%nat) (fun n : nat => (Rabs (An n)))).
apply (cardinal_finite nat (fun x : nat => (x < S N)%nat) (S N)).
apply (nat_cardinal (S N)).
apply (Extensionality_Ensembles R (Im nat R (fun x : nat => (x < S N)%nat) (fun n : nat => (Rabs (An n)))) (fun x : R =>
 exists n0 : nat, Rabs (An n0) = x /\ (n0 <= N)%nat)).
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

Definition Floor (r : R) := proj1_sig (constructive_definite_description
        (fun n : Z => (IZR n) <= r < (IZR (n+1)%Z))
        (Theorem_3_7 r)).

Lemma Floor_inequality : forall (r : R), (IZR (Floor r)) <= r < (IZR ((Floor r)+1)%Z).
Proof.
move=> r.
apply (proj2_sig (constructive_definite_description
        (fun n : Z => (IZR n) <= r < (IZR (n+1)%Z))
        (Theorem_3_7 r))).
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

Definition RQ : (Ensemble R) := 
  (fun x:R => exists q:Q, QArith.Qreals.Q2R q = x).

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

Lemma Theorem_3_9_sub : forall m : nat, (m > S O)%nat -> (forall x : R, exists (an : (nat -> {num : nat | (num < m) % nat})), 
let An := fun n : nat => (match n with
| O => (IZR (Floor x))
| S n1 => INR (proj1_sig (an n1)) / (pow (INR m) (S n1))
end) in (Un_cv (fun n : nat => (sum_f_R0 An n)) x)).
Proof.
move=> m H1 x.
suff: let Bn := fix Bn (n : nat) : (R * Z) :=
match n with
| O => (x - IZR (Floor x) , 0%Z)
| S n1 => (((fst (Bn n1)) * (INR m)) - IZR (Floor (((fst (Bn n1)) * (INR m)))) , Floor ((fst (Bn n1)) * (INR m)))
end in exists an : nat -> {num : nat | (num < m)%nat},
  let An :=
    fun n : nat =>
    match n with
    | 0%nat => IZR (Floor x)
    | S n1 => INR (proj1_sig (an n1)) / INR m ^ S n1
    end in
  Un_cv (fun n : nat => sum_f_R0 An n) x.
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
apply (Rmult_eq_reg_r (INR m * INR m ^ n) (fst (Bn n) / INR m ^ n +
- (INR (Z.to_nat (snd (Bn (S n)))) / (INR m * INR m ^ n))) ((fst (Bn n) * INR m + - IZR (Floor (fst (Bn n) * INR m))) /
(INR m * INR m ^ n))).
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

Lemma Theorem_3_9 : forall x : R, exists (an : (nat -> {num : nat | (num < 10) % nat})), 
let An := fun n : nat => (match n with
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
suff: let An :=
       fun n : nat =>
       match n with
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

Definition Rn (N : nat) := ({n : nat| (n < N)%nat } -> R).

Definition Rnplus (N : nat) := fun (a b : (Rn N)) => (fun (x : {n : nat| (n < N)%nat }) => (a x) + (b x)).

Definition Rnmult (N : nat) := fun (c : R) (a : (Rn N)) => (fun (x : {n : nat| (n < N)%nat }) => c * (a x)).

Definition Rnopp (N : nat) := fun (a : (Rn N)) => (fun (x : {n : nat| (n < N)%nat }) => - (a x)).

Definition Rnminus (N : nat) := fun (a b : (Rn N)) => (Rnplus N a (Rnopp N b)).

Definition Rfield := mkField R 0 1 Rplus Rmult Ropp Rinv Rplus_assoc Rmult_assoc Rplus_comm Rmult_comm Rplus_0_l Rmult_1_l Rplus_opp_r Rinv_l Rmult_plus_distr_l R1_neq_R0.

Definition RnO (N : nat) := (fun (x : {n : nat| (n < N)%nat }) => 0).

Definition UnwrapRn (N : nat) := fun (f : (Rn N)) (n : nat) => match (excluded_middle_informative (n < N)%nat) with | left a => (f (exist (fun (n0 : nat) => (n0 < N)%nat) n a)) | right _ => 0 end.

Lemma Rnplus_comm : forall (N : nat) (x y : Rn N), (Rnplus N x y) = (Rnplus N y x).
Proof.
move=> N x y.
apply functional_extensionality.
move=> n.
apply Rplus_comm.
Qed.

Lemma Rnplus_assoc : forall (N : nat) (x y z : Rn N), (Rnplus N (Rnplus N x y) z) = (Rnplus N x (Rnplus N y z)).
Proof.
move=> N x y z.
apply functional_extensionality.
move=> n.
apply Rplus_assoc.
Qed.

Lemma Rnplus_O_l : forall (N : nat) (x : Rn N), (Rnplus N (RnO N) x) = x.
Proof.
move=> N x.
apply functional_extensionality.
move=> n.
apply Rplus_0_l.
Qed.

Lemma Rnplus_opp_r : forall (N : nat) (x : Rn N), (Rnplus N x (Rnopp N x)) = (RnO N).
Proof.
move=> N x.
apply functional_extensionality.
move=> n.
apply Rplus_opp_r.
Qed.

Lemma Rnmult_plus_distr_l : forall (N : nat) (x : R) (y z : Rn N), (Rnmult N x (Rnplus N y z)) = (Rnplus N (Rnmult N x y) (Rnmult N x z)).
Proof.
move=> N x y z.
apply functional_extensionality.
move=> n.
apply Rmult_plus_distr_l.
Qed.

Lemma Rnmult_plus_distr_r : forall (N : nat) (x y : R) (z : Rn N), (Rnmult N (Rplus x y) z) = (Rnplus N (Rnmult N x z) (Rnmult N y z)).
Proof.
move=> N x y z.
apply functional_extensionality.
move=> n.
apply Rmult_plus_distr_r.
Qed.

Lemma Rnmult_assoc : forall (N : nat) (x y : R) (z : Rn N), (Rnmult N x (Rnmult N y z)) = (Rnmult N (x * y) z).
Proof.
move=> N x y z.
apply functional_extensionality.
move=> n.
unfold Rnmult.
rewrite (Rmult_assoc x y (z n)).
reflexivity.
Qed.

Lemma Rnmult_I_l : forall (N : nat) (x : Rn N), (Rnmult N 1 x) = x.
Proof.
move=> N x.
apply functional_extensionality.
move=> n.
apply Rmult_1_l.
Qed.

Definition RnVS (N : nat) := mkVectorSpace Rfield (Rn N) (RnO N) (Rnplus N) (Rnmult N) (Rnopp N) (Rnplus_comm N) (Rnplus_assoc N) (Rnplus_O_l N) (Rnplus_opp_r N) (Rnmult_plus_distr_l N) (Rnmult_plus_distr_r N) (Rnmult_assoc N) (Rnmult_I_l N).

Definition my_sum_f_R := 
fix my_sum_f_R (f : nat -> R) (N : nat) {struct N} : R :=
  match N with
  | 0%nat => 0
  | S i => (my_sum_f_R f i) + (f i)
  end.

Definition RnInnerProduct (N : nat) := fun (a b : Rn N) => (my_sum_f_R (fun (n : nat) => ((UnwrapRn N a) n) * ((UnwrapRn N b) n)) N).

Lemma Proposition_4_2_1_1 : forall (N : nat) (x y z : Rn N),(RnInnerProduct N (Rnplus N x y) z) = (RnInnerProduct N x z) + (RnInnerProduct N y z).
Proof.
move=> N x y z.
unfold RnInnerProduct.
suff: (forall (N0:nat), (N0 <= N)%nat -> my_sum_f_R (fun n : nat => UnwrapRn N (Rnplus N x y) n * UnwrapRn N z n) N0 = my_sum_f_R (fun n : nat => UnwrapRn N x n * UnwrapRn N z n) N0 + my_sum_f_R (fun n : nat => UnwrapRn N y n * UnwrapRn N z n)  N0).
move=> H1.
apply (H1 N).
apply (le_n N).
elim.
move=> H1.
simpl.
rewrite (Rplus_0_r 0).
reflexivity.
move=> n H1 H2.
simpl.
rewrite H1.
rewrite - (Rplus_assoc (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N z n0) n + UnwrapRn N x n * UnwrapRn N z n) (my_sum_f_R (fun n0 : nat => UnwrapRn N y n0 * UnwrapRn N z n0) n) (UnwrapRn N y n * UnwrapRn N z n)).
rewrite (Rplus_assoc (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N z n0) n) (UnwrapRn N x n * UnwrapRn N z n) (my_sum_f_R (fun n0 : nat => UnwrapRn N y n0 * UnwrapRn N z n0) n)).
rewrite (Rplus_comm (UnwrapRn N x n * UnwrapRn N z n) (my_sum_f_R (fun n0 : nat => UnwrapRn N y n0 * UnwrapRn N z n0) n)).
rewrite - (Rplus_assoc (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N z n0) n) (my_sum_f_R (fun n0 : nat => UnwrapRn N y n0 * UnwrapRn N z n0) n) (UnwrapRn N x n * UnwrapRn N z n)).
rewrite (Rplus_assoc (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N z n0) n + my_sum_f_R (fun n0 : nat => UnwrapRn N y n0 * UnwrapRn N z n0) n) (UnwrapRn N x n * UnwrapRn N z n) (UnwrapRn N y n * UnwrapRn N z n)).
apply (Rplus_eq_compat_l (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N z n0) n + my_sum_f_R (fun n0 : nat => UnwrapRn N y n0 * UnwrapRn N z n0) n) (UnwrapRn N (Rnplus N x y) n * UnwrapRn N z n) (UnwrapRn N x n * UnwrapRn N z n + UnwrapRn N y n * UnwrapRn N z n)).
unfold Rnplus.
unfold UnwrapRn.
elim (excluded_middle_informative (n < N)%nat).
move=> a.
apply Rmult_plus_distr_r.
move=> H3.
apply False_ind.
apply (H3 H2).
apply (le_trans n (S n) N).
apply (le_S n n).
apply (le_n n).
apply H2.
Qed.

Lemma Proposition_4_2_1_2 : forall (N : nat) (x y z : Rn N),(RnInnerProduct N x (Rnplus N y z)) = (RnInnerProduct N x y) + (RnInnerProduct N x z).
Proof.
move=> N x y z.
unfold RnInnerProduct.
suff: (forall (N0:nat), (N0 <= N)%nat -> my_sum_f_R (fun n : nat => UnwrapRn N x n * UnwrapRn N (Rnplus N y z) n) N0 = my_sum_f_R (fun n : nat => UnwrapRn N x n * UnwrapRn N y n) N0 + my_sum_f_R (fun n : nat => UnwrapRn N x n * UnwrapRn N z n)  N0).
move=> H1.
apply (H1 N).
apply (le_n N).
elim.
move=> H1.
simpl.
rewrite (Rplus_0_r 0).
reflexivity.
move=> n H1 H2.
simpl.
rewrite H1.
rewrite - (Rplus_assoc (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N y n0) n + UnwrapRn N x n * UnwrapRn N y n) (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N z n0) n) (UnwrapRn N x n * UnwrapRn N z n)).
rewrite (Rplus_assoc (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N y n0) n) (UnwrapRn N x n * UnwrapRn N y n) (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N z n0) n)).
rewrite (Rplus_comm (UnwrapRn N x n * UnwrapRn N y n) (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N z n0) n)).
rewrite - (Rplus_assoc (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N y n0) n) (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N z n0) n) (UnwrapRn N x n * UnwrapRn N y n)).
rewrite (Rplus_assoc (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N y n0) n + my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N z n0) n) (UnwrapRn N x n * UnwrapRn N y n) (UnwrapRn N x n * UnwrapRn N z n)).
apply (Rplus_eq_compat_l (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N y n0) n + my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N z n0) n) (UnwrapRn N x n * UnwrapRn N (Rnplus N y z) n) (UnwrapRn N x n * UnwrapRn N y n + UnwrapRn N x n * UnwrapRn N z n)).
unfold Rnplus.
unfold UnwrapRn.
elim (excluded_middle_informative (n < N)%nat).
move=> a.
apply Rmult_plus_distr_l.
move=> H3.
apply False_ind.
apply (H3 H2).
apply (le_trans n (S n) N).
apply (le_S n n).
apply (le_n n).
apply H2.
Qed.

Lemma Proposition_4_2_2_1 : forall (N : nat) (a : R) (x y : Rn N),(RnInnerProduct N (Rnmult N a x) y) = a * (RnInnerProduct N x y).
Proof.
move=> N a x y.
unfold RnInnerProduct.
suff: (forall (N0:nat), (N0 <= N)%nat -> my_sum_f_R (fun n : nat => UnwrapRn N (Rnmult N a x) n * UnwrapRn N y n) N0 = a * my_sum_f_R (fun n : nat => UnwrapRn N x n * UnwrapRn N y n) N0).
move=> H1.
apply (H1 N).
apply (le_n N).
elim.
move=> H1.
simpl.
rewrite (Rmult_0_r a).
reflexivity.
move=> n H1 H2.
simpl.
rewrite H1.
unfold Rnmult.
unfold UnwrapRn at 3.
elim (excluded_middle_informative (n < N)%nat).
move=> b.
rewrite (Rmult_plus_distr_l a (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N y n0) n) (UnwrapRn N x n * UnwrapRn N y n)).
apply (Rplus_eq_compat_l (a * my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N y n0) n) (a * x (exist (fun n0 : nat => (n0 < N)%nat) n b) * UnwrapRn N y n) (a * (UnwrapRn N x n * UnwrapRn N y n))).
unfold UnwrapRn at 2.
elim (excluded_middle_informative (n < N)%nat).
move=> c.
suff: (exist (fun n0 : nat => (n0 < N)%nat) n b) = (exist (fun n0 : nat => (n0 < N)%nat) n c).
move=> H3.
rewrite H3.
apply Rmult_assoc.
apply sig_map.
simpl.
reflexivity.
move=> H3.
apply False_ind.
apply (H3 b).
move=> H3.
apply False_ind.
apply (H3 H2).
apply (le_trans n (S n) N).
apply (le_S n n).
apply (le_n n).
apply H2.
Qed.

Lemma Proposition_4_2_2_2 : forall (N : nat) (a : R) (x y : Rn N), a * (RnInnerProduct N x y) = (RnInnerProduct N x (Rnmult N a y)).
Proof.
move=> N a x y.
unfold RnInnerProduct.
suff: (forall (N0:nat), (N0 <= N)%nat -> a * my_sum_f_R (fun n : nat => UnwrapRn N x n * UnwrapRn N y n) N0 = my_sum_f_R (fun n : nat => UnwrapRn N x n * UnwrapRn N (Rnmult N a y) n) N0).
move=> H1.
apply (H1 N).
apply (le_n N).
elim.
move=> H1.
simpl.
apply (Rmult_0_r a).
move=> n H1 H2.
simpl.
rewrite<- H1.
unfold Rnmult.
unfold UnwrapRn at 8.
elim (excluded_middle_informative (n < N)%nat).
move=> b.
rewrite (Rmult_plus_distr_l a (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N y n0) n) (UnwrapRn N x n * UnwrapRn N y n)).
apply (Rplus_eq_compat_l (a * my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N y n0) n) (a * (UnwrapRn N x n * UnwrapRn N y n)) (UnwrapRn N x n * (a * y (exist (fun n0 : nat => (n0 < N)%nat) n b)))).
unfold UnwrapRn at 2.
elim (excluded_middle_informative (n < N)%nat).
move=> c.
suff: (exist (fun n0 : nat => (n0 < N)%nat) n b) = (exist (fun n0 : nat => (n0 < N)%nat) n c).
move=> H3.
rewrite H3.
rewrite - (Rmult_assoc a (UnwrapRn N x n) (y (exist (fun n0 : nat => (n0 < N)%nat) n c))).
rewrite (Rmult_comm a (UnwrapRn N x n)).
apply Rmult_assoc.
apply sig_map.
simpl.
reflexivity.
move=> H3.
apply False_ind.
apply (H3 b).
move=> H3.
apply False_ind.
apply (H3 H2).
apply (le_trans n (S n) N).
apply (le_S n n).
apply (le_n n).
apply H2.
Qed.

Lemma Proposition_4_2_3 : forall (N : nat) (x y : Rn N), (RnInnerProduct N x y) = (RnInnerProduct N y x).
Proof.
move=> N x y.
unfold RnInnerProduct.
suff: (forall (N0:nat), (N0 <= N)%nat -> my_sum_f_R (fun n : nat => UnwrapRn N x n * UnwrapRn N y n) N0 = my_sum_f_R (fun n : nat => UnwrapRn N y n * UnwrapRn N x n) N0).
move=> H1.
apply (H1 N).
apply (le_n N).
elim.
move=> H1.
simpl.
reflexivity.
move=> n H1 H2.
simpl.
rewrite H1.
apply (Rplus_eq_compat_l (my_sum_f_R (fun n0 : nat => UnwrapRn N y n0 * UnwrapRn N x n0) n) (UnwrapRn N x n * UnwrapRn N y n) (UnwrapRn N y n * UnwrapRn N x n)).
apply Rmult_comm.
apply (le_trans n (S n) N).
apply (le_S n n).
apply (le_n n).
apply H2.
Qed.

Lemma Proposition_4_2_4_1 : forall (N : nat) (x : Rn N), (RnInnerProduct N x x) >= 0.
Proof.
move=> N x.
unfold RnInnerProduct.
suff: (forall (N0:nat), (N0 <= N)%nat -> my_sum_f_R (fun n : nat => UnwrapRn N x n * UnwrapRn N x n) N0 >= 0).
move=> H1.
apply (H1 N).
apply (le_n N).
elim.
move=> H1.
simpl.
apply (Req_ge 0 0).
reflexivity.
move=> n H1 H2.
simpl.
apply (Rge_trans (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n + UnwrapRn N x n * UnwrapRn N x n) (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n) 0).
rewrite -{2} (Rplus_0_r (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n)).
apply (Rplus_ge_compat_l (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n) (UnwrapRn N x n * UnwrapRn N x n) 0).
apply (Formula_1_3_2 (UnwrapRn N x n)).
apply H1.
apply (le_trans n (S n) N).
apply (le_S n n).
apply (le_n n).
apply H2.
Qed.

Lemma Proposition_4_2_4_2 : forall (N : nat) (x : Rn N), (RnInnerProduct N x x) = 0 -> x = (RnO N).
Proof.
move=> N x H1.
elim (classic (x = (RnO N))).
apply.
move=> H2.
apply False_ind.
apply (Rgt_not_eq (RnInnerProduct N x x) 0).
suff: (exists n:{n : nat | (n < N)%nat},x n <> 0).
move=> H3.
elim H3.
move=> n0 H4.
suff: (forall (N0:nat), (N0 <= N)%nat -> (my_sum_f_R (fun n : nat => UnwrapRn N x n * UnwrapRn N x n) N0 >= 0 /\ ((N0 > (proj1_sig n0))%nat -> my_sum_f_R (fun n : nat => UnwrapRn N x n * UnwrapRn N x n) N0 > 0))).
move=> H5.
apply H5.
apply (le_n N).
apply (proj2_sig n0).
elim.
move=> H5.
apply conj.
simpl.
apply (Req_ge 0 0).
reflexivity.
move=> H6.
apply False_ind.
apply (lt_not_le (proj1_sig n0) O).
apply H6.
apply (le_0_n (proj1_sig n0)).
move=> n H5 H6.
apply conj.
simpl.
apply (Rge_trans (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n + UnwrapRn N x n * UnwrapRn N x n) (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n) 0).
rewrite -{2} (Rplus_0_r (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n)).
apply (Rplus_ge_compat_l (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n) (UnwrapRn N x n * UnwrapRn N x n) 0).
apply (Formula_1_3_2 (UnwrapRn N x n)).
apply H5.
apply (le_trans n (S n) N).
apply (le_S n n).
apply (le_n n).
apply H6.
move=> H7.
simpl.
elim (classic (n = proj1_sig n0)).
move=> H8.
apply (Rgt_ge_trans (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n + UnwrapRn N x n * UnwrapRn N x n) (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n) 0).
rewrite -{2} (Rplus_0_r (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n)).
apply (Rplus_gt_compat_l (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n) (UnwrapRn N x n * UnwrapRn N x n) 0).
apply (Formula_1_3_3 (UnwrapRn N x n)).
rewrite H8.
unfold UnwrapRn.
elim (excluded_middle_informative (proj1_sig n0 < N)%nat).
move=> a.
suff: ((exist (fun n1 : nat => (n1 < N)%nat) (proj1_sig n0) a) = n0).
move=> H9.
rewrite H9.
apply H4.
apply sig_map.
simpl.
reflexivity.
move=> H9.
apply False_ind.
apply (H9 (proj2_sig n0)).
apply H5.
apply (le_trans n (S n) N).
apply (le_S n n).
apply (le_n n).
apply H6.
move=> H8.
apply (Rge_gt_trans (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n + UnwrapRn N x n * UnwrapRn N x n) (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n) 0).
rewrite -{2} (Rplus_0_r (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n)).
apply (Rplus_ge_compat_l (my_sum_f_R (fun n0 : nat => UnwrapRn N x n0 * UnwrapRn N x n0) n) (UnwrapRn N x n * UnwrapRn N x n) 0).
apply (Formula_1_3_2 (UnwrapRn N x n)).
apply H5.
apply (le_trans n (S n) N).
apply (le_S n n).
apply (le_n n).
apply H6.
elim (le_lt_or_eq (proj1_sig n0) n).
apply.
move=> H9.
apply False_ind.
apply H8.
rewrite H9.
reflexivity.
apply (le_S_n (proj1_sig n0) n H7).
apply NNPP.
move=> H3.
apply H2.
apply functional_extensionality.
move=> n.
apply NNPP.
move=> H4.
apply H3.
exists n.
unfold RnO in H4.
apply H4.
apply H1.
Qed.

Lemma Proposition_4_2_4_3 : forall (N : nat) (x : Rn N), x = (RnO N) -> (RnInnerProduct N x x) = 0.
Proof.
move=> N x H1.
rewrite H1.
have: Rnmult N 0 (RnO N) = (Vmul Rfield (RnVS N) 0 (RnO N)).
simpl.
reflexivity.
move=> H2.
suff: RnO N = Rnmult N 0 (RnO N).
move=> H3.
rewrite {2} H3.
rewrite - (Proposition_4_2_2_2 N 0 (RnO N) (RnO N)).
apply (Rmult_0_l (RnInnerProduct N (RnO N) (RnO N))).
rewrite H2.
rewrite (Vmul_O_l Rfield (RnVS N) (RnO N)).
reflexivity.
Qed.

Definition RnNorm (N : nat) := fun (x : Rn N) => (MySqrt (exist (fun (r : R) => r >= 0) (RnInnerProduct N x x) (Proposition_4_2_4_1 N x))).

Lemma RnNormNature : forall (N : nat) (x : Rn N), (RnNorm N x) >= 0 /\ (RnInnerProduct N x x) = (RnNorm N x) * (RnNorm N x).
Proof.
move=> N x.
apply (MySqrtNature (exist (fun (r : R) => r >= 0) (RnInnerProduct N x x) (Proposition_4_2_4_1 N x))).
Qed.

Lemma RnNormNature2 : forall (N : nat) (x : Rn N) (y : R), y >= 0 /\ (RnInnerProduct N x x) = y * y -> (RnNorm N x) = y.
Proof.
move=> N x y H1.
apply (MySqrtNature2 (exist (fun (r : R) => r >= 0) (RnInnerProduct N x x) (Proposition_4_2_4_1 N x)) y H1).
Qed.

Lemma Formula_4_15_1 : forall (N : nat) (x y : Rn N), (RnNorm N (Rnplus N x y)) * (RnNorm N (Rnplus N x y)) = (RnNorm N x) * (RnNorm N x) + 2 * (RnInnerProduct N x y) + (RnNorm N y) * (RnNorm N y).
Proof.
move=> N x y.
rewrite - (proj2 (RnNormNature N (Rnplus N x y))).
rewrite - (proj2 (RnNormNature N x)).
rewrite - (proj2 (RnNormNature N y)).
rewrite (Proposition_4_2_1_1 N x y (Rnplus N x y)).
rewrite (Proposition_4_2_1_2 N x x y).
rewrite (Proposition_4_2_1_2 N y x y).
rewrite (Rplus_assoc (RnInnerProduct N x x) (RnInnerProduct N x y) (RnInnerProduct N y x + RnInnerProduct N y y)).
rewrite (Rplus_assoc (RnInnerProduct N x x) (2 * RnInnerProduct N x y) (RnInnerProduct N y y)).
apply (Rplus_eq_compat_l (RnInnerProduct N x x) (RnInnerProduct N x y + (RnInnerProduct N y x + RnInnerProduct N y y)) (2 * RnInnerProduct N x y + RnInnerProduct N y y)).
rewrite /2.
rewrite - INR_IPR.
simpl.
rewrite (Rmult_plus_distr_r 1 1 (RnInnerProduct N x y)).
rewrite (Rmult_1_l (RnInnerProduct N x y)).
rewrite (Rplus_assoc (RnInnerProduct N x y) (RnInnerProduct N x y) (RnInnerProduct N y y)).
apply (Rplus_eq_compat_l (RnInnerProduct N x y) (RnInnerProduct N y x + RnInnerProduct N y y) (RnInnerProduct N x y + RnInnerProduct N y y)).
apply (Rplus_eq_compat_r (RnInnerProduct N y y) (RnInnerProduct N y x) (RnInnerProduct N x y)).
apply (Proposition_4_2_3 N y x).
Qed.

Lemma Formula_4_15_2 : forall (N : nat) (x y : Rn N), (RnNorm N (Rnminus N x y)) * (RnNorm N (Rnminus N x y)) = (RnNorm N x) * (RnNorm N x) - 2 * (RnInnerProduct N x y) + (RnNorm N y) * (RnNorm N y).
Proof.
move=> N x y.
rewrite - (proj2 (RnNormNature N (Rnminus N x y))).
rewrite - (proj2 (RnNormNature N x)).
rewrite - (proj2 (RnNormNature N y)).
rewrite (Proposition_4_2_1_1 N x (Rnopp N y) (Rnminus N x y)).
rewrite (Proposition_4_2_1_2 N x x (Rnopp N y)).
rewrite (Proposition_4_2_1_2 N (Rnopp N y) x (Rnopp N y)).
rewrite (Rplus_assoc (RnInnerProduct N x x) (RnInnerProduct N x (Rnopp N y)) (RnInnerProduct N (Rnopp N y) x + RnInnerProduct N (Rnopp N y) (Rnopp N y))).
rewrite (Rplus_assoc (RnInnerProduct N x x) (- (2 * RnInnerProduct N x y)) (RnInnerProduct N y y)).
apply (Rplus_eq_compat_l (RnInnerProduct N x x) (RnInnerProduct N x (Rnopp N y) + (RnInnerProduct N (Rnopp N y) x + RnInnerProduct N (Rnopp N y) (Rnopp N y))) (- (2 * RnInnerProduct N x y) + RnInnerProduct N y y)).
rewrite - (Vmul_I_l Rfield (RnVS N) (Rnopp N y)).
simpl.
have: ((Rnmult N 1 (Rnopp N y)) = (Vmul Rfield (RnVS N) 1 (Vopp Rfield (RnVS N) y))).
simpl.
reflexivity.
move=> H1.
rewrite H1.
rewrite - (Vopp_mul_distr_r Rfield (RnVS N) 1 y).
rewrite (Vopp_mul_distr_l Rfield (RnVS N) 1 y).
have: ((Rnmult N (- 1) y) = (Vmul Rfield (RnVS N) (Fopp Rfield 1) y)).
simpl.
reflexivity.
move=> H2.
rewrite - H2.
rewrite /2.
rewrite - INR_IPR.
simpl.
rewrite (Rmult_plus_distr_r 1 1 (RnInnerProduct N x y)).
rewrite (Rmult_1_l (RnInnerProduct N x y)).
rewrite (Ropp_plus_distr (RnInnerProduct N x y) (RnInnerProduct N x y)).
rewrite (Proposition_4_2_3 N (Rnmult N (-1) y) x).
rewrite - (Proposition_4_2_2_2 N (- 1) x y).
rewrite (Ropp_mult_distr_l_reverse 1 (RnInnerProduct N x y)).
rewrite (Rmult_1_l (RnInnerProduct N x y)).
rewrite (Rplus_assoc (- RnInnerProduct N x y) (- RnInnerProduct N x y) (RnInnerProduct N y y)).
apply (Rplus_eq_compat_l (- RnInnerProduct N x y) (- RnInnerProduct N x y + RnInnerProduct N (Rnmult N (-1) y) (Rnmult N (-1) y)) (- RnInnerProduct N x y + RnInnerProduct N y y)).
apply (Rplus_eq_compat_l (- RnInnerProduct N x y) (RnInnerProduct N (Rnmult N (-1) y) (Rnmult N (-1) y)) (RnInnerProduct N y y)).
rewrite - (Proposition_4_2_2_2 N (- 1) (Rnmult N (-1) y) y).
rewrite (Proposition_4_2_2_1 N (- 1) y y).
rewrite (Ropp_mult_distr_l_reverse 1 (RnInnerProduct N y y)).
rewrite (Rmult_1_l (RnInnerProduct N y y)).
rewrite (Ropp_mult_distr_l_reverse 1 (- RnInnerProduct N y y)).
rewrite (Rmult_1_l (- RnInnerProduct N y y)).
apply (Ropp_involutive (RnInnerProduct N y y)).
Qed.

Lemma Order_2_Discriminant_gt : forall (a b : R), (forall (x : R), (x * x + a * x + b) > 0) <-> a * a - 4 * b < 0.
Proof.
move=> a b.
apply conj.
move=> H1.
apply (Ropp_lt_cancel (a * a - 4 * b) 0).
rewrite Ropp_0.
rewrite (Ropp_minus_distr (a * a) (4 * b)).
suff: (4 * b - a * a = 4 * ((- a / 2) * (- a / 2) + a * (- a / 2) + b)).
move=> H2.
rewrite H2.
apply (Rmult_lt_0_compat 4 ((- a / 2) * (- a / 2) + a * (- a / 2) + b)).
rewrite /4.
rewrite - INR_IPR.
simpl.
apply (Rlt_trans 0 (1 + 1 + 1) (1 + 1 + 1 + 1)).
apply (Rlt_trans 0 (1 + 1) (1 + 1 + 1)).
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 (1 + 1) (1 + 1 + 1)).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
apply (H1 (- a / 2)).
have: 4 = 2 * 2.
rewrite /4.
rewrite /2.
rewrite - INR_IPR.
rewrite - INR_IPR.
simpl.
rewrite (Rmult_plus_distr_l (1 + 1) 1 1).
rewrite (Rmult_1_r (1 + 1)).
apply (Rplus_assoc (1 + 1) 1 1).
move=> H2.
rewrite (Rmult_plus_distr_l 4 (- a / 2 * (- a / 2) + a * (- a / 2)) b).
unfold Rminus.
rewrite (Rplus_comm (4 * b) (- (a * a))).
apply (Rplus_eq_compat_r (4 * b) (- (a * a)) (4 * (- a / 2 * (- a / 2) + a * (- a / 2)))).
rewrite (Rmult_plus_distr_l 4 (- a / 2 * (- a / 2)) (a * (- a / 2))).
rewrite H2.
rewrite - (Rmult_assoc (2 * 2) (- a / 2) (- a / 2)).
rewrite (Rmult_assoc 2 2 (- a / 2)).
rewrite (Rmult_comm 2 (- a / 2)).
rewrite (Rmult_assoc (- a) (/ 2) 2).
rewrite (Rinv_l 2).
rewrite (Rmult_1_r (- a)).
rewrite (Rmult_comm (2 * - a) (- a / 2)).
rewrite - (Rmult_assoc (- a / 2) 2 (- a)).
rewrite (Rmult_assoc (- a) (/ 2) 2).
rewrite (Rinv_l 2).
rewrite (Rmult_1_r (- a)).
rewrite (Rmult_comm a (- a / 2)).
rewrite - (Rmult_assoc (2 * 2) (- a / 2) a).
rewrite (Rmult_assoc 2 2 (- a / 2)).
rewrite (Rmult_comm 2 (- a / 2)).
rewrite (Rmult_assoc (- a) (/ 2) 2).
rewrite (Rinv_l 2).
rewrite (Rmult_1_r (- a)).
rewrite (Rmult_opp_opp a a).
rewrite (Ropp_mult_distr_r_reverse 2 a).
rewrite - (Ropp_mult_distr_l_reverse 2 a).
rewrite -{2} (Rmult_1_l (a * a)).
rewrite (Rmult_assoc (- 2) a a).
rewrite - (Rmult_plus_distr_r 1 (- 2) (a * a)).
rewrite /(-2).
rewrite - INR_IPR.
simpl.
rewrite (Ropp_plus_distr 1 1).
rewrite - (Rplus_assoc 1 (- 1) (- 1)).
rewrite (Rplus_opp_r 1).
rewrite (Rplus_0_l (- 1)).
rewrite (Ropp_mult_distr_l_reverse 1 (a * a)).
rewrite (Rmult_1_l (a * a)).
reflexivity.
apply Two_Neq_Zero.
apply Two_Neq_Zero.
apply Two_Neq_Zero.
move=> H1.
move=> x.
suff: (x * x + a * x + b = (x + (a / 2)) * (x + (a / 2)) + - (a * a - 4 * b) / 4).
move=> H2.
rewrite H2.
apply (Rgt_ge_trans ((x + a / 2) * (x + a / 2) + - (a * a - 4 * b) / 4) ((x + a / 2) * (x + a / 2)) 0).
rewrite -{2} (Rplus_0_r ((x + a / 2) * (x + a / 2))).
apply (Rplus_gt_compat_l ((x + a / 2) * (x + a / 2)) (- (a * a - 4 * b) / 4) 0).
apply (Rmult_gt_0_compat (- (a * a - 4 * b)) (/ 4)).
rewrite - Ropp_0.
apply (Ropp_lt_gt_contravar (a * a - 4 * b) 0).
apply H1.
apply (Rinv_0_lt_compat 4).
rewrite /4.
rewrite - INR_IPR.
simpl.
apply (Rlt_trans 0 (1 + 1 + 1) (1 + 1 + 1 + 1)).
apply (Rlt_trans 0 (1 + 1) (1 + 1 + 1)).
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 (1 + 1) (1 + 1 + 1)).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
apply (Formula_1_3_2 (x + a / 2)).
have: 4 = 2 * 2.
rewrite /4.
rewrite /2.
rewrite - INR_IPR.
rewrite - INR_IPR.
simpl.
rewrite (Rmult_plus_distr_l (1 + 1) 1 1).
rewrite (Rmult_1_r (1 + 1)).
apply (Rplus_assoc (1 + 1) 1 1).
move=> H2.
rewrite (Rmult_plus_distr_r x (a / 2) (x + a / 2)).
rewrite (Rmult_plus_distr_l x x (a / 2)).
rewrite (Rmult_plus_distr_l (a / 2) x (a / 2)).
rewrite (Rplus_assoc (x * x) (x * (a / 2)) (a / 2 * x + a / 2 * (a / 2))).
rewrite (Rplus_assoc (x * x) (x * (a / 2) + (a / 2 * x + a / 2 * (a / 2))) (- (a * a - 4 * b) / 4)).
rewrite (Rplus_assoc (x * x) (a * x) b).
apply (Rplus_eq_compat_l (x * x) (a * x + b) (x * (a / 2) + (a / 2 * x + a / 2 * (a / 2)) + - (a * a - 4 * b) / 4)).
rewrite - (Rplus_assoc (x * (a / 2)) (a / 2 * x) (a / 2 * (a / 2))).
rewrite (Rmult_comm x (a / 2)).
rewrite - (Rmult_plus_distr_r (a / 2) (a / 2) x).
rewrite - (Rmult_plus_distr_l a (/ 2) (/ 2)).
rewrite - (Rmult_1_l (/ 2)).
rewrite - (Rmult_plus_distr_r 1 1 (/ 2)).
rewrite {1}/2.
rewrite - INR_IPR.
simpl.
rewrite (Rinv_r (1 + 1)).
rewrite (Rmult_1_r a).
rewrite (Rplus_assoc (a * x) (a / 2 * (a / 2)) (- (a * a - 4 * b) / 4)).
apply (Rplus_eq_compat_l (a * x) b (a / 2 * (a / 2) + - (a * a - 4 * b) / 4)).
rewrite (Ropp_minus_distr (a * a) (4 * b)).
unfold Rminus.
unfold Rdiv.
rewrite (Rmult_plus_distr_r (4 * b) (- (a * a)) (/ 4)).
rewrite (Rplus_comm (4 * b * / 4) (- (a * a) * / 4)).
rewrite (Rmult_comm 4 b).
rewrite (Rmult_assoc b 4 (/ 4)).
rewrite (Rinv_r 4).
rewrite (Rmult_1_r b).
rewrite - (Rplus_assoc (a * / 2 * (a * / 2)) (- (a * a) * / 4) b).
rewrite -{1} (Rplus_0_l b).
apply (Rplus_eq_compat_r b 0 (a * / 2 * (a * / 2) + - (a * a) * / 4)).
rewrite (Ropp_mult_distr_l_reverse (a * a) (/ 4)).
rewrite H2.
rewrite (Rinv_mult_distr 2 2).
rewrite - (Rmult_assoc (a * a) (/ 2) (/ 2)).
rewrite (Rmult_assoc a a (/ 2)).
rewrite{3} (Rmult_comm a (/ 2)).
rewrite - (Rmult_assoc a (/ 2) a).
rewrite (Rmult_assoc (a * / 2) a (/ 2)).
rewrite (Rplus_opp_r (a * / 2 * (a * / 2))).
reflexivity.
apply Two_Neq_Zero.
apply Two_Neq_Zero.
rewrite H2.
apply (Rmult_integral_contrapositive 2 2).
apply conj.
apply Two_Neq_Zero.
apply Two_Neq_Zero.
apply Two_Neq_Zero.
Qed.

Lemma Order_2_Discriminant_ge : forall (a b : R), (forall (x : R), (x * x + a * x + b) >= 0) <-> a * a - 4 * b <= 0.
Proof.
move=> a b.
apply conj.
move=> H1.
apply (Ropp_le_cancel (a * a - 4 * b) 0).
rewrite Ropp_0.
rewrite (Ropp_minus_distr (a * a) (4 * b)).
suff: (4 * b - a * a = 4 * ((- a / 2) * (- a / 2) + a * (- a / 2) + b)).
move=> H2.
rewrite H2.
rewrite - (Rmult_0_r 4).
apply (Rmult_le_compat_l 4 0 ((- a / 2) * (- a / 2) + a * (- a / 2) + b)).
apply (Rlt_le 0 4).
rewrite /4.
rewrite - INR_IPR.
simpl.
apply (Rlt_trans 0 (1 + 1 + 1) (1 + 1 + 1 + 1)).
apply (Rlt_trans 0 (1 + 1) (1 + 1 + 1)).
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 (1 + 1) (1 + 1 + 1)).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
apply (Rge_le (- a / 2 * (- a / 2) + a * (- a / 2) + b) 0).
apply (H1 (- a / 2)).
have: 4 = 2 * 2.
rewrite /4.
rewrite /2.
rewrite - INR_IPR.
rewrite - INR_IPR.
simpl.
rewrite (Rmult_plus_distr_l (1 + 1) 1 1).
rewrite (Rmult_1_r (1 + 1)).
apply (Rplus_assoc (1 + 1) 1 1).
move=> H2.
rewrite (Rmult_plus_distr_l 4 (- a / 2 * (- a / 2) + a * (- a / 2)) b).
unfold Rminus.
rewrite (Rplus_comm (4 * b) (- (a * a))).
apply (Rplus_eq_compat_r (4 * b) (- (a * a)) (4 * (- a / 2 * (- a / 2) + a * (- a / 2)))).
rewrite (Rmult_plus_distr_l 4 (- a / 2 * (- a / 2)) (a * (- a / 2))).
rewrite H2.
rewrite - (Rmult_assoc (2 * 2) (- a / 2) (- a / 2)).
rewrite (Rmult_assoc 2 2 (- a / 2)).
rewrite (Rmult_comm 2 (- a / 2)).
rewrite (Rmult_assoc (- a) (/ 2) 2).
rewrite (Rinv_l 2).
rewrite (Rmult_1_r (- a)).
rewrite (Rmult_comm (2 * - a) (- a / 2)).
rewrite - (Rmult_assoc (- a / 2) 2 (- a)).
rewrite (Rmult_assoc (- a) (/ 2) 2).
rewrite (Rinv_l 2).
rewrite (Rmult_1_r (- a)).
rewrite (Rmult_comm a (- a / 2)).
rewrite - (Rmult_assoc (2 * 2) (- a / 2) a).
rewrite (Rmult_assoc 2 2 (- a / 2)).
rewrite (Rmult_comm 2 (- a / 2)).
rewrite (Rmult_assoc (- a) (/ 2) 2).
rewrite (Rinv_l 2).
rewrite (Rmult_1_r (- a)).
rewrite (Rmult_opp_opp a a).
rewrite (Ropp_mult_distr_r_reverse 2 a).
rewrite - (Ropp_mult_distr_l_reverse 2 a).
rewrite -{2} (Rmult_1_l (a * a)).
rewrite (Rmult_assoc (- 2) a a).
rewrite - (Rmult_plus_distr_r 1 (- 2) (a * a)).
rewrite /(-2).
rewrite - INR_IPR.
simpl.
rewrite (Ropp_plus_distr 1 1).
rewrite - (Rplus_assoc 1 (- 1) (- 1)).
rewrite (Rplus_opp_r 1).
rewrite (Rplus_0_l (- 1)).
rewrite (Ropp_mult_distr_l_reverse 1 (a * a)).
rewrite (Rmult_1_l (a * a)).
reflexivity.
apply Two_Neq_Zero.
apply Two_Neq_Zero.
apply Two_Neq_Zero.
move=> H1.
move=> x.
suff: (x * x + a * x + b = (x + (a / 2)) * (x + (a / 2)) + - (a * a - 4 * b) / 4).
move=> H2.
rewrite H2.
apply (Rge_trans ((x + a / 2) * (x + a / 2) + - (a * a - 4 * b) / 4) ((x + a / 2) * (x + a / 2)) 0).
rewrite -{2} (Rplus_0_r ((x + a / 2) * (x + a / 2))).
apply (Rplus_ge_compat_l ((x + a / 2) * (x + a / 2)) (- (a * a - 4 * b) / 4) 0).
rewrite - (Rmult_0_l (/ 4)).
apply (Rmult_ge_compat_r (/ 4) (- (a * a - 4 * b)) 0).
apply (Rgt_ge (/ 4) 0).
apply (Rinv_0_lt_compat 4).
rewrite /4.
rewrite - INR_IPR.
simpl.
apply (Rlt_trans 0 (1 + 1 + 1) (1 + 1 + 1 + 1)).
apply (Rlt_trans 0 (1 + 1) (1 + 1 + 1)).
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 (1 + 1) (1 + 1 + 1)).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
rewrite - Ropp_0.
apply (Ropp_le_ge_contravar (a * a - 4 * b) 0).
apply H1.
apply (Formula_1_3_2 (x + a / 2)).
have: 4 = 2 * 2.
rewrite /4.
rewrite /2.
rewrite - INR_IPR.
rewrite - INR_IPR.
simpl.
rewrite (Rmult_plus_distr_l (1 + 1) 1 1).
rewrite (Rmult_1_r (1 + 1)).
apply (Rplus_assoc (1 + 1) 1 1).
move=> H2.
rewrite (Rmult_plus_distr_r x (a / 2) (x + a / 2)).
rewrite (Rmult_plus_distr_l x x (a / 2)).
rewrite (Rmult_plus_distr_l (a / 2) x (a / 2)).
rewrite (Rplus_assoc (x * x) (x * (a / 2)) (a / 2 * x + a / 2 * (a / 2))).
rewrite (Rplus_assoc (x * x) (x * (a / 2) + (a / 2 * x + a / 2 * (a / 2))) (- (a * a - 4 * b) / 4)).
rewrite (Rplus_assoc (x * x) (a * x) b).
apply (Rplus_eq_compat_l (x * x) (a * x + b) (x * (a / 2) + (a / 2 * x + a / 2 * (a / 2)) + - (a * a - 4 * b) / 4)).
rewrite - (Rplus_assoc (x * (a / 2)) (a / 2 * x) (a / 2 * (a / 2))).
rewrite (Rmult_comm x (a / 2)).
rewrite - (Rmult_plus_distr_r (a / 2) (a / 2) x).
rewrite - (Rmult_plus_distr_l a (/ 2) (/ 2)).
rewrite - (Rmult_1_l (/ 2)).
rewrite - (Rmult_plus_distr_r 1 1 (/ 2)).
rewrite {1}/2.
rewrite - INR_IPR.
simpl.
rewrite (Rinv_r (1 + 1)).
rewrite (Rmult_1_r a).
rewrite (Rplus_assoc (a * x) (a / 2 * (a / 2)) (- (a * a - 4 * b) / 4)).
apply (Rplus_eq_compat_l (a * x) b (a / 2 * (a / 2) + - (a * a - 4 * b) / 4)).
rewrite (Ropp_minus_distr (a * a) (4 * b)).
unfold Rminus.
unfold Rdiv.
rewrite (Rmult_plus_distr_r (4 * b) (- (a * a)) (/ 4)).
rewrite (Rplus_comm (4 * b * / 4) (- (a * a) * / 4)).
rewrite (Rmult_comm 4 b).
rewrite (Rmult_assoc b 4 (/ 4)).
rewrite (Rinv_r 4).
rewrite (Rmult_1_r b).
rewrite - (Rplus_assoc (a * / 2 * (a * / 2)) (- (a * a) * / 4) b).
rewrite -{1} (Rplus_0_l b).
apply (Rplus_eq_compat_r b 0 (a * / 2 * (a * / 2) + - (a * a) * / 4)).
rewrite (Ropp_mult_distr_l_reverse (a * a) (/ 4)).
rewrite H2.
rewrite (Rinv_mult_distr 2 2).
rewrite - (Rmult_assoc (a * a) (/ 2) (/ 2)).
rewrite (Rmult_assoc a a (/ 2)).
rewrite{3} (Rmult_comm a (/ 2)).
rewrite - (Rmult_assoc a (/ 2) a).
rewrite (Rmult_assoc (a * / 2) a (/ 2)).
rewrite (Rplus_opp_r (a * / 2 * (a * / 2))).
reflexivity.
apply Two_Neq_Zero.
apply Two_Neq_Zero.
rewrite H2.
apply (Rmult_integral_contrapositive 2 2).
apply conj.
apply Two_Neq_Zero.
apply Two_Neq_Zero.
apply Two_Neq_Zero.
Qed.

Lemma Proposition_4_3_1 : forall (N : nat) (x y : Rn N), Rabs (RnInnerProduct
 N x y) <= (RnNorm N x) * (RnNorm N y).
Proof.
move=> N x y.
elim (classic ((RnInnerProduct N x x) = 0)).
move=> H1.
rewrite (Proposition_4_2_4_2 N x H1).
suff: (RnO N) = (Rnmult N 0 (RnO N)).
move=> H2.
suff: (RnInnerProduct N (RnO N) y) = 0.
move=> H3.
suff: (RnNorm N (RnO N)) = 0.
move=> H4.
rewrite H3.
rewrite H4.
rewrite (Rmult_0_l (RnNorm N y)).
rewrite Rabs_R0.
apply (Req_le 0 0).
reflexivity.
unfold RnNorm.
rewrite (MySqrtNature2 (exist (fun r : R => r >= 0) (RnInnerProduct N (RnO N) (RnO N)) (Proposition_4_2_4_1 N (RnO N))) 0).
reflexivity.
apply conj.
apply (Req_ge 0 0).
reflexivity.
unfold proj1_sig.
rewrite{2} H2.
rewrite - (Proposition_4_2_2_2 N 0 (RnO N) (RnO N)).
rewrite (Rmult_0_r 0).
apply (Rmult_0_l (RnInnerProduct N (RnO N) (RnO N))).
rewrite H2.
rewrite (Proposition_4_2_2_1 N 0 (RnO N) y).
apply (Rmult_0_l (RnInnerProduct N (RnO N) y)).
have: Rnmult N 0 (RnO N) = (Vmul Rfield (RnVS N) 0 (RnO N)).
simpl.
reflexivity.
move=> H2.
rewrite H2.
rewrite (Vmul_O_l Rfield (RnVS N) (RnO N)).
simpl.
reflexivity.
move=> H2.
suff: Rabs (RnInnerProduct N x y) * Rabs (RnInnerProduct N x y) <= RnNorm N x * RnNorm N x * RnNorm N y * RnNorm N y.
move=> H3.
apply (Rnot_lt_le (RnNorm N x * RnNorm N y) (Rabs (RnInnerProduct N x y))).
move=> H4.
apply (Rle_not_lt (RnNorm N x * RnNorm N x * RnNorm N y * RnNorm N y) (Rabs (RnInnerProduct N x y) * Rabs (RnInnerProduct N x y)) H3).
rewrite (Rmult_assoc (RnNorm N x) (RnNorm N x) (RnNorm N y)).
rewrite (Rmult_comm (RnNorm N x) (RnNorm N y)).
rewrite - (Rmult_assoc (RnNorm N x) (RnNorm N y) (RnNorm N x)).
rewrite (Rmult_assoc (RnNorm N x * RnNorm N y) (RnNorm N x) (RnNorm N y)).
apply (Rmult_le_0_lt_compat (RnNorm N x * RnNorm N y) (Rabs (RnInnerProduct N x y)) (RnNorm N x * RnNorm N y) (Rabs (RnInnerProduct N x y))).
rewrite - (Rmult_0_l (RnNorm N y)).
apply (Rmult_le_compat_r (RnNorm N y) 0 (RnNorm N x)).
apply (Rge_le (RnNorm N y) 0).
apply (proj1 (RnNormNature N y)).
apply (Rge_le (RnNorm N x) 0).
apply (proj1 (RnNormNature N x)).
rewrite - (Rmult_0_l (RnNorm N y)).
apply (Rmult_le_compat_r (RnNorm N y) 0 (RnNorm N x)).
apply (Rge_le (RnNorm N y) 0).
apply (proj1 (RnNormNature N y)).
apply (Rge_le (RnNorm N x) 0).
apply (proj1 (RnNormNature N x)).
apply H4.
apply H4.
suff: ((- (2 * (RnInnerProduct N x y) / (RnNorm N x * RnNorm N x))) * (- (2 * (RnInnerProduct N x y) / (RnNorm N x * RnNorm N x))) - 4 * (RnNorm N y * RnNorm N y) / (RnNorm N x * RnNorm N x) <= 0).
move=> H3.
suff: Rabs (RnInnerProduct N x y) * Rabs (RnInnerProduct N x y) = (RnInnerProduct N x y) * (RnInnerProduct N x y).
move=> H4.
rewrite H4.
apply (Rmult_le_reg_r (/ (RnNorm N x * RnNorm N x) * / (RnNorm N x * RnNorm N x)) (RnInnerProduct N x y * RnInnerProduct N x y) (RnNorm N x * RnNorm N x * RnNorm N y * RnNorm N y)).
apply (Formula_1_3_3 (/ (RnNorm N x * RnNorm N x))).
apply (Rinv_neq_0_compat (RnNorm N x * RnNorm N x)).
rewrite - (proj2 (RnNormNature N x)).
apply H2.
rewrite (Rmult_assoc (RnNorm N x * RnNorm N x) (RnNorm N y) (RnNorm N y)).
rewrite (Rmult_comm (RnNorm N x * RnNorm N x) (RnNorm N y * RnNorm N y)).
rewrite - (Rmult_assoc (RnNorm N y * RnNorm N y * (RnNorm N x * RnNorm N x)) (/ (RnNorm N x * RnNorm N x)) (/ (RnNorm N x * RnNorm N x))).
rewrite (Rmult_assoc (RnNorm N y * RnNorm N y) (RnNorm N x * RnNorm N x) (/ (RnNorm N x * RnNorm N x))).
rewrite (Rinv_r (RnNorm N x * RnNorm N x)).
rewrite (Rmult_1_r (RnNorm N y * RnNorm N y)).
apply (Rmult_le_reg_l 4 (RnInnerProduct N x y * RnInnerProduct N x y * (/ (RnNorm N x * RnNorm N x) * / (RnNorm N x * RnNorm N x))) (RnNorm N y * RnNorm N y * / (RnNorm N x * RnNorm N x))).
rewrite /4.
rewrite -INR_IPR.
simpl.
apply (Rlt_trans 0 (1 + 1 + 1) (1 + 1 + 1 + 1)).
apply (Rlt_trans 0 (1 + 1) (1 + 1 + 1)).
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 (1 + 1) (1 + 1 + 1)).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
suff: 4 = 2 * 2.
move=> H5.
rewrite {1} H5.
rewrite - (Rmult_assoc (RnInnerProduct N x y * RnInnerProduct N x y) (/ (RnNorm N x * RnNorm N x)) (/ (RnNorm N x * RnNorm N x))).
rewrite (Rmult_assoc (RnInnerProduct N x y) (RnInnerProduct N x y) (/ (RnNorm N x * RnNorm N x))).
rewrite (Rmult_comm (RnInnerProduct N x y) (/ (RnNorm N x * RnNorm N x))).
rewrite - (Rmult_assoc (RnInnerProduct N x y) (/ (RnNorm N x * RnNorm N x)) (RnInnerProduct N x y)).
rewrite (Rmult_assoc (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x)) (RnInnerProduct N x y) (/ (RnNorm N x * RnNorm N x))).
rewrite (Rmult_assoc 2 2 (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x) * (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x)))).
rewrite - (Rmult_assoc 2 (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x)) (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x))).
rewrite - (Rmult_assoc 2 (2 * (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x))) (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x))).
rewrite (Rmult_comm 2 (2 * (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x)))).
rewrite (Rmult_assoc (2 * (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x))) 2 (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x))).
rewrite - (Rmult_assoc 2 (RnInnerProduct N x y) (/ (RnNorm N x * RnNorm N x))).
rewrite - (Rmult_assoc 4 (RnNorm N y * RnNorm N y) (/ (RnNorm N x * RnNorm N x))).
rewrite - (Rmult_opp_opp (2 * RnInnerProduct N x y * / (RnNorm N x * RnNorm N x)) (2 * RnInnerProduct N x y * / (RnNorm N x * RnNorm N x))).
apply (Rminus_le (- (2 * RnInnerProduct N x y * / (RnNorm N x * RnNorm N x)) * - (2 * RnInnerProduct N x y * / (RnNorm N x * RnNorm N x))) (4 * (RnNorm N y * RnNorm N y) * / (RnNorm N x * RnNorm N x)) H3).
rewrite /4.
rewrite /2.
rewrite - INR_IPR.
rewrite - INR_IPR.
simpl.
rewrite (Rmult_plus_distr_l (1 + 1) 1 1).
rewrite (Rmult_1_r (1 + 1)).
apply (Rplus_assoc (1 + 1) 1 1).
rewrite - (proj2 (RnNormNature N x)).
apply H2.
unfold Rabs.
elim (Rcase_abs (RnInnerProduct N x y)).
move=> H4.
apply (Rmult_opp_opp (RnInnerProduct N x y) (RnInnerProduct N x y)).
move=> H5.
reflexivity.
unfold Rdiv.
rewrite (Rmult_assoc 4 (RnNorm N y * RnNorm N y) (/ (RnNorm N x * RnNorm N x))).
apply (Order_2_Discriminant_ge (- (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x))) (RnNorm N y * RnNorm N y * / (RnNorm N x * RnNorm N x))).
move=> t.
apply (Rle_ge 0 (t * t + - (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x)) * t + RnNorm N y * RnNorm N y * / (RnNorm N x * RnNorm N x))).
apply (Rmult_le_reg_l (RnNorm N x * RnNorm N x) 0 (t * t + - (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x)) * t + RnNorm N y * RnNorm N y * / (RnNorm N x * RnNorm N x))).
elim (Formula_1_3_2 (RnNorm N x)).
apply (Rgt_lt (RnNorm N x * RnNorm N x) 0).
move=> H3.
apply False_ind.
apply H2.
rewrite (proj2 (RnNormNature N x)).
apply H3.
rewrite (Rmult_0_r (RnNorm N x * RnNorm N x)).
suff: (RnNorm N x * RnNorm N x * (t * t + - (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x)) * t + RnNorm N y * RnNorm N y * / (RnNorm N x * RnNorm N x)) = RnNorm N (Rnminus N (Rnmult N t x) y) * RnNorm N (Rnminus N (Rnmult N t x) y)).
move=> H3.
rewrite H3.
apply (Rge_le (RnNorm N (Rnminus N (Rnmult N t x) y) * RnNorm N (Rnminus N (Rnmult N t x) y)) 0).
apply (Formula_1_3_2 (RnNorm N (Rnminus N (Rnmult N t x) y))).
rewrite (Formula_4_15_2 N (Rnmult N t x) y).
rewrite - (proj2 (RnNormNature N (Rnmult N t x))).
rewrite (Proposition_4_2_2_1 N t x (Rnmult N t x)).
rewrite - (Proposition_4_2_2_2 N t x x).
rewrite (Proposition_4_2_2_1 N t x y).
rewrite (proj2 (RnNormNature N x)).
rewrite (Rmult_plus_distr_l (RnNorm N x * RnNorm N x) (t * t + - (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x)) * t) (RnNorm N y * RnNorm N y * / (RnNorm N x * RnNorm N x))).
rewrite (Rmult_comm (RnNorm N y * RnNorm N y) (/ (RnNorm N x * RnNorm N x))).
rewrite - (Rmult_assoc (RnNorm N x * RnNorm N x) (/ (RnNorm N x * RnNorm N x)) (RnNorm N y * RnNorm N y)).
rewrite (Rinv_r (RnNorm N x * RnNorm N x)).
rewrite (Rmult_1_l (RnNorm N y * RnNorm N y)).
apply (Rplus_eq_compat_r (RnNorm N y * RnNorm N y) (RnNorm N x * RnNorm N x * (t * t + - (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x)) * t)) (t * (t * (RnNorm N x * RnNorm N x)) - 2 * (t * RnInnerProduct N x y))).
rewrite (Rmult_plus_distr_l (RnNorm N x * RnNorm N x) (t * t) (- (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x)) * t)).
rewrite - (Rmult_assoc t t (RnNorm N x * RnNorm N x)).
rewrite (Rmult_comm (t * t) (RnNorm N x * RnNorm N x)).
apply (Rplus_eq_compat_l (RnNorm N x * RnNorm N x * (t * t)) (RnNorm N x * RnNorm N x * (- (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x)) * t)) (- (2 * (t * RnInnerProduct N x y)))).
unfold Rdiv.
rewrite (Rmult_comm (2 * RnInnerProduct N x y) (/ (RnNorm N x * RnNorm N x))).
rewrite (Ropp_mult_distr_r (/ (RnNorm N x * RnNorm N x)) (2 * RnInnerProduct N x y)).
rewrite (Rmult_assoc (/ (RnNorm N x * RnNorm N x)) (- (2 * RnInnerProduct N x y)) t).
rewrite - (Rmult_assoc (RnNorm N x * RnNorm N x) (/ (RnNorm N x * RnNorm N x)) (- (2 * RnInnerProduct N x y) * t)).
rewrite (Rinv_r (RnNorm N x * RnNorm N x)).
rewrite (Rmult_1_l (- (2 * RnInnerProduct N x y) * t)).
rewrite - (Ropp_mult_distr_l (2 * RnInnerProduct N x y) t).
rewrite (Rmult_assoc 2 (RnInnerProduct N x y) t).
rewrite (Rmult_comm (RnInnerProduct N x y) t).
reflexivity.
rewrite - (proj2 (RnNormNature N x)).
apply H2.
rewrite - (proj2 (RnNormNature N x)).
apply H2.
Qed.

Lemma Proposition_4_3_2 : forall (N : nat) (x y : Rn N), Rabs (RnInnerProduct
 N x y) = (RnNorm N x) * (RnNorm N y) -> (exists (k : R), x = (Rnmult N k y) \/ y = (Rnmult N k x)).
Proof.
move=> N x y H1.
elim (classic ((RnInnerProduct N x x) = 0)).
move=> H2.
exists 0.
left.
suff: ((Rnmult N 0 y) = (Vmul Rfield (RnVS N) (FO Rfield) y)).
move=> H3.
rewrite H3.
rewrite (Vmul_O_l Rfield (RnVS N) y).
simpl.
apply (Proposition_4_2_4_2 N x H2).
simpl.
reflexivity.
move=> H2.
apply NNPP.
move=> H3.
apply (Rlt_not_eq (Rabs (RnInnerProduct N x y)) (RnNorm N x * RnNorm N y)).
suff: Rabs (RnInnerProduct N x y) * Rabs (RnInnerProduct N x y) < RnNorm N x * RnNorm N x * RnNorm N y * RnNorm N y.
move=> H4.
apply (Rnot_le_lt (RnNorm N x * RnNorm N y) (Rabs (RnInnerProduct N x y))).
move=> H5.
apply (Rlt_not_le (RnNorm N x * RnNorm N x * RnNorm N y * RnNorm N y) (Rabs (RnInnerProduct N x y) * Rabs (RnInnerProduct N x y)) H4).
rewrite (Rmult_assoc (RnNorm N x) (RnNorm N x) (RnNorm N y)).
rewrite (Rmult_comm (RnNorm N x) (RnNorm N y)).
rewrite - (Rmult_assoc (RnNorm N x) (RnNorm N y) (RnNorm N x)).
rewrite (Rmult_assoc (RnNorm N x * RnNorm N y) (RnNorm N x) (RnNorm N y)).
apply (Rmult_le_compat (RnNorm N x * RnNorm N y) (Rabs (RnInnerProduct N x y)) (RnNorm N x * RnNorm N y) (Rabs (RnInnerProduct N x y))).
rewrite - (Rmult_0_l (RnNorm N y)).
apply (Rmult_le_compat_r (RnNorm N y) 0 (RnNorm N x)).
apply (Rge_le (RnNorm N y) 0).
apply (proj1 (RnNormNature N y)).
apply (Rge_le (RnNorm N x) 0).
apply (proj1 (RnNormNature N x)).
rewrite - (Rmult_0_l (RnNorm N y)).
apply (Rmult_le_compat_r (RnNorm N y) 0 (RnNorm N x)).
apply (Rge_le (RnNorm N y) 0).
apply (proj1 (RnNormNature N y)).
apply (Rge_le (RnNorm N x) 0).
apply (proj1 (RnNormNature N x)).
apply H5.
apply H5.
suff: ((- (2 * (RnInnerProduct N x y) / (RnNorm N x * RnNorm N x))) * (- (2 * (RnInnerProduct N x y) / (RnNorm N x * RnNorm N x))) - 4 * (RnNorm N y * RnNorm N y) / (RnNorm N x * RnNorm N x) < 0).
move=> H4.
suff: Rabs (RnInnerProduct N x y) * Rabs (RnInnerProduct N x y) = (RnInnerProduct N x y) * (RnInnerProduct N x y).
move=> H5.
rewrite H5.
apply (Rmult_lt_reg_r (/ (RnNorm N x * RnNorm N x) * / (RnNorm N x * RnNorm N x)) (RnInnerProduct N x y * RnInnerProduct N x y) (RnNorm N x * RnNorm N x * RnNorm N y * RnNorm N y)).
apply (Formula_1_3_3 (/ (RnNorm N x * RnNorm N x))).
apply (Rinv_neq_0_compat (RnNorm N x * RnNorm N x)).
rewrite - (proj2 (RnNormNature N x)).
apply H2.
rewrite (Rmult_assoc (RnNorm N x * RnNorm N x) (RnNorm N y) (RnNorm N y)).
rewrite (Rmult_comm (RnNorm N x * RnNorm N x) (RnNorm N y * RnNorm N y)).
rewrite - (Rmult_assoc (RnNorm N y * RnNorm N y * (RnNorm N x * RnNorm N x)) (/ (RnNorm N x * RnNorm N x)) (/ (RnNorm N x * RnNorm N x))).
rewrite (Rmult_assoc (RnNorm N y * RnNorm N y) (RnNorm N x * RnNorm N x) (/ (RnNorm N x * RnNorm N x))).
rewrite (Rinv_r (RnNorm N x * RnNorm N x)).
rewrite (Rmult_1_r (RnNorm N y * RnNorm N y)).
apply (Rmult_lt_reg_l 4 (RnInnerProduct N x y * RnInnerProduct N x y * (/ (RnNorm N x * RnNorm N x) * / (RnNorm N x * RnNorm N x))) (RnNorm N y * RnNorm N y * / (RnNorm N x * RnNorm N x))).
rewrite /4.
rewrite -INR_IPR.
simpl.
apply (Rlt_trans 0 (1 + 1 + 1) (1 + 1 + 1 + 1)).
apply (Rlt_trans 0 (1 + 1) (1 + 1 + 1)).
apply (Rlt_trans 0 1 (1 + 1)).
apply (Rlt_0_1).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
apply (Rplus_lt_compat_r 1 (1 + 1) (1 + 1 + 1)).
apply (Rplus_lt_compat_r 1 1 (1 + 1)).
apply (Rlt_plus_1 1).
suff: 4 = 2 * 2.
move=> H6.
rewrite {1} H6.
rewrite - (Rmult_assoc (RnInnerProduct N x y * RnInnerProduct N x y) (/ (RnNorm N x * RnNorm N x)) (/ (RnNorm N x * RnNorm N x))).
rewrite (Rmult_assoc (RnInnerProduct N x y) (RnInnerProduct N x y) (/ (RnNorm N x * RnNorm N x))).
rewrite (Rmult_comm (RnInnerProduct N x y) (/ (RnNorm N x * RnNorm N x))).
rewrite - (Rmult_assoc (RnInnerProduct N x y) (/ (RnNorm N x * RnNorm N x)) (RnInnerProduct N x y)).
rewrite (Rmult_assoc (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x)) (RnInnerProduct N x y) (/ (RnNorm N x * RnNorm N x))).
rewrite (Rmult_assoc 2 2 (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x) * (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x)))).
rewrite - (Rmult_assoc 2 (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x)) (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x))).
rewrite - (Rmult_assoc 2 (2 * (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x))) (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x))).
rewrite (Rmult_comm 2 (2 * (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x)))).
rewrite (Rmult_assoc (2 * (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x))) 2 (RnInnerProduct N x y * / (RnNorm N x * RnNorm N x))).
rewrite - (Rmult_assoc 2 (RnInnerProduct N x y) (/ (RnNorm N x * RnNorm N x))).
rewrite - (Rmult_assoc 4 (RnNorm N y * RnNorm N y) (/ (RnNorm N x * RnNorm N x))).
rewrite - (Rmult_opp_opp (2 * RnInnerProduct N x y * / (RnNorm N x * RnNorm N x)) (2 * RnInnerProduct N x y * / (RnNorm N x * RnNorm N x))).
apply (Rminus_lt (- (2 * RnInnerProduct N x y * / (RnNorm N x * RnNorm N x)) * - (2 * RnInnerProduct N x y * / (RnNorm N x * RnNorm N x))) (4 * (RnNorm N y * RnNorm N y) * / (RnNorm N x * RnNorm N x)) H4).
rewrite /4.
rewrite /2.
rewrite - INR_IPR.
rewrite - INR_IPR.
simpl.
rewrite (Rmult_plus_distr_l (1 + 1) 1 1).
rewrite (Rmult_1_r (1 + 1)).
apply (Rplus_assoc (1 + 1) 1 1).
rewrite - (proj2 (RnNormNature N x)).
apply H2.
unfold Rabs.
elim (Rcase_abs (RnInnerProduct N x y)).
move=> H5.
apply (Rmult_opp_opp (RnInnerProduct N x y) (RnInnerProduct N x y)).
move=> H5.
reflexivity.
unfold Rdiv.
rewrite (Rmult_assoc 4 (RnNorm N y * RnNorm N y) (/ (RnNorm N x * RnNorm N x))).
apply (Order_2_Discriminant_gt (- (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x))) (RnNorm N y * RnNorm N y * / (RnNorm N x * RnNorm N x))).
move=> t.
apply (Rlt_gt 0 (t * t + - (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x)) * t + RnNorm N y * RnNorm N y * / (RnNorm N x * RnNorm N x))).
apply (Rmult_lt_reg_l (RnNorm N x * RnNorm N x) 0 (t * t + - (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x)) * t + RnNorm N y * RnNorm N y * / (RnNorm N x * RnNorm N x))).
elim (Formula_1_3_2 (RnNorm N x)).
apply (Rgt_lt (RnNorm N x * RnNorm N x) 0).
move=> H4.
apply False_ind.
apply H2.
rewrite (proj2 (RnNormNature N x)).
apply H4.
rewrite (Rmult_0_r (RnNorm N x * RnNorm N x)).
suff: (RnNorm N x * RnNorm N x * (t * t + - (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x)) * t + RnNorm N y * RnNorm N y * / (RnNorm N x * RnNorm N x)) = RnNorm N (Rnminus N (Rnmult N t x) y) * RnNorm N (Rnminus N (Rnmult N t x) y)).
move=> H4.
rewrite H4.
apply (Rgt_lt (RnNorm N (Rnminus N (Rnmult N t x) y) * RnNorm N (Rnminus N (Rnmult N t x) y)) 0).
apply (Formula_1_3_3 (RnNorm N (Rnminus N (Rnmult N t x) y))).
move=> H5.
suff: (Rnminus N (Rnmult N t x) y) = (RnO N).
move=> H6.
apply H3.
exists t.
right.
apply (Vminus_diag_uniq_sym Rfield (RnVS N) y (Rnmult N t x)).
apply H6.
apply (Proposition_4_2_4_2 N (Rnminus N (Rnmult N t x) y)).
rewrite (proj2 (RnNormNature N (Rnminus N (Rnmult N t x) y))).
rewrite H5.
apply (Rmult_0_l 0).
rewrite (Formula_4_15_2 N (Rnmult N t x) y).
rewrite - (proj2 (RnNormNature N (Rnmult N t x))).
rewrite (Proposition_4_2_2_1 N t x (Rnmult N t x)).
rewrite - (Proposition_4_2_2_2 N t x x).
rewrite (Proposition_4_2_2_1 N t x y).
rewrite (proj2 (RnNormNature N x)).
rewrite (Rmult_plus_distr_l (RnNorm N x * RnNorm N x) (t * t + - (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x)) * t) (RnNorm N y * RnNorm N y * / (RnNorm N x * RnNorm N x))).
rewrite (Rmult_comm (RnNorm N y * RnNorm N y) (/ (RnNorm N x * RnNorm N x))).
rewrite - (Rmult_assoc (RnNorm N x * RnNorm N x) (/ (RnNorm N x * RnNorm N x)) (RnNorm N y * RnNorm N y)).
rewrite (Rinv_r (RnNorm N x * RnNorm N x)).
rewrite (Rmult_1_l (RnNorm N y * RnNorm N y)).
apply (Rplus_eq_compat_r (RnNorm N y * RnNorm N y) (RnNorm N x * RnNorm N x * (t * t + - (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x)) * t)) (t * (t * (RnNorm N x * RnNorm N x)) - 2 * (t * RnInnerProduct N x y))).
rewrite (Rmult_plus_distr_l (RnNorm N x * RnNorm N x) (t * t) (- (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x)) * t)).
rewrite - (Rmult_assoc t t (RnNorm N x * RnNorm N x)).
rewrite (Rmult_comm (t * t) (RnNorm N x * RnNorm N x)).
apply (Rplus_eq_compat_l (RnNorm N x * RnNorm N x * (t * t)) (RnNorm N x * RnNorm N x * (- (2 * RnInnerProduct N x y / (RnNorm N x * RnNorm N x)) * t)) (- (2 * (t * RnInnerProduct N x y)))).
unfold Rdiv.
rewrite (Rmult_comm (2 * RnInnerProduct N x y) (/ (RnNorm N x * RnNorm N x))).
rewrite (Ropp_mult_distr_r (/ (RnNorm N x * RnNorm N x)) (2 * RnInnerProduct N x y)).
rewrite (Rmult_assoc (/ (RnNorm N x * RnNorm N x)) (- (2 * RnInnerProduct N x y)) t).
rewrite - (Rmult_assoc (RnNorm N x * RnNorm N x) (/ (RnNorm N x * RnNorm N x)) (- (2 * RnInnerProduct N x y) * t)).
rewrite (Rinv_r (RnNorm N x * RnNorm N x)).
rewrite (Rmult_1_l (- (2 * RnInnerProduct N x y) * t)).
rewrite - (Ropp_mult_distr_l (2 * RnInnerProduct N x y) t).
rewrite (Rmult_assoc 2 (RnInnerProduct N x y) t).
rewrite (Rmult_comm (RnInnerProduct N x y) t).
reflexivity.
rewrite - (proj2 (RnNormNature N x)).
apply H2.
rewrite - (proj2 (RnNormNature N x)).
apply H2.
apply H1.
Qed.

Lemma Proposition_4_4_1 : forall (N : nat) (a : R) (x : Rn N), RnNorm N (Rnmult N a x) = Rabs a * RnNorm N x.
Proof.
move=> N a x.
apply (RnNormNature2 N (Rnmult N a x) (Rabs a * RnNorm N x)).
apply conj.
rewrite - (Rmult_0_r (Rabs a)).
apply (Rmult_ge_compat_l (Rabs a) (RnNorm N x) 0).
apply (Rle_ge 0 (Rabs a)).
apply (Rabs_pos a).
apply (proj1 (RnNormNature N x)).
rewrite (Proposition_4_2_2_1 N a x (Rnmult N a x)).
rewrite - (Proposition_4_2_2_2 N a x x).
rewrite - (Rmult_assoc a a (RnInnerProduct N x x)).
suff: (a * a = Rabs a * Rabs a).
move=> H1.
rewrite H1.
rewrite (proj2 (RnNormNature N x)).
rewrite - (Rmult_assoc (Rabs a * Rabs a) (RnNorm N x) (RnNorm N x)).
rewrite (Rmult_assoc (Rabs a) (Rabs a) (RnNorm N x)).
rewrite (Rmult_comm (Rabs a) (RnNorm N x)).
rewrite - (Rmult_assoc (Rabs a) (RnNorm N x) (Rabs a)).
rewrite (Rmult_assoc (Rabs a * RnNorm N x) (Rabs a) (RnNorm N x)).
rewrite (Rmult_comm (Rabs a) (RnNorm N x)).
reflexivity.
unfold Rabs.
elim (Rcase_abs a).
move=> H1.
rewrite (Rmult_opp_opp a a).
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma Proposition_4_4_2_1 : forall (N : nat) (x y : Rn N), (RnNorm N (Rnplus N x y)) <= RnNorm N x + RnNorm N y.
Proof.
move=> N x y.
suff: RnNorm N (Rnplus N x y) * RnNorm N (Rnplus N x y) <= (RnNorm N x + RnNorm N y) * (RnNorm N x + RnNorm N y).
move=> H1.
apply (Rnot_lt_le (RnNorm N x + RnNorm N y) (RnNorm N (Rnplus N x y))).
move=> H2.
apply (Rle_not_lt ((RnNorm N x + RnNorm N y) * (RnNorm N x + RnNorm N y)) (RnNorm N (Rnplus N x y) * RnNorm N (Rnplus N x y)) H1).
suff: (0 <= (RnNorm N x + RnNorm N y)).
move=> H3.
apply (Rmult_le_0_lt_compat (RnNorm N x + RnNorm N y) (RnNorm N (Rnplus N x y)) (RnNorm N x + RnNorm N y) (RnNorm N (Rnplus N x y))).
apply H3.
apply H3.
apply H2.
apply H2.
apply (Rplus_le_le_0_compat (RnNorm N x) (RnNorm N y)).
apply (Rge_le (RnNorm N x) 0).
apply (proj1 (RnNormNature N x)).
apply (Rge_le (RnNorm N y) 0).
apply (proj1 (RnNormNature N y)).
rewrite (Formula_4_15_1 N x y).
rewrite (Rmult_plus_distr_l (RnNorm N x + RnNorm N y) (RnNorm N x) (RnNorm N y)).
rewrite (Rmult_plus_distr_r (RnNorm N x) (RnNorm N y) (RnNorm N x)).
rewrite (Rmult_plus_distr_r (RnNorm N x) (RnNorm N y) (RnNorm N y)).
rewrite (Rplus_assoc (RnNorm N x * RnNorm N x) (2 * RnInnerProduct N x y) (RnNorm N y * RnNorm N y)).
rewrite (Rplus_assoc (RnNorm N x * RnNorm N x) (RnNorm N y * RnNorm N x) (RnNorm N x * RnNorm N y + RnNorm N y * RnNorm N y)).
apply (Rplus_le_compat_l (RnNorm N x * RnNorm N x) (2 * RnInnerProduct N x y + RnNorm N y * RnNorm N y) (RnNorm N y * RnNorm N x + (RnNorm N x * RnNorm N y + RnNorm N y * RnNorm N y))).
rewrite - (Rplus_assoc (RnNorm N y * RnNorm N x) (RnNorm N x * RnNorm N y) (RnNorm N y * RnNorm N y)).
apply (Rplus_le_compat_r (RnNorm N y * RnNorm N y) (2 * RnInnerProduct N x y) (RnNorm N y * RnNorm N x + RnNorm N x * RnNorm N y)).
rewrite (Rmult_comm (RnNorm N y) (RnNorm N x)).
rewrite - (Rmult_1_l (RnNorm N x * RnNorm N y)).
rewrite - (Rmult_plus_distr_r 1 1 (RnNorm N x * RnNorm N y)).
rewrite /2.
rewrite - INR_IPR.
simpl.
apply (Rmult_le_compat_l (1 + 1) (RnInnerProduct N x y) (RnNorm N x * RnNorm N y)).
apply (Rlt_le 0 (1 + 1)).
apply (Rlt_trans 0 1 (1 + 1)).
apply Rlt_0_1.
apply (Rlt_plus_1 1).
apply (Rle_trans (RnInnerProduct N x y) (Rabs (RnInnerProduct N x y)) (RnNorm N x * RnNorm N y)).
apply (Rle_abs (RnInnerProduct N x y)).
apply (Proposition_4_3_1 N x y).
Qed.

Lemma Proposition_4_3_3 : forall (N : nat) (x y : Rn N), (exists (k : R), x = (Rnmult N k y) \/ y = (Rnmult N k x)) -> Rabs (RnInnerProduct
 N x y) = (RnNorm N x) * (RnNorm N y).
Proof.
move=> N x y.
elim.
move=> k.
elim.
move=> H1.
rewrite H1.
rewrite (Proposition_4_2_2_1 N k y y).
rewrite (Rabs_mult k (RnInnerProduct N y y)).
rewrite (Proposition_4_4_1 N k y).
rewrite (Rabs_pos_eq (RnInnerProduct N y y)).
rewrite (proj2 (RnNormNature N y)).
rewrite (Rmult_assoc (Rabs k) (RnNorm N y) (RnNorm N y)).
reflexivity.
apply (Rge_le (RnInnerProduct N y y) 0).
apply (Proposition_4_2_4_1 N y).
move=> H1.
rewrite H1.
rewrite - (Proposition_4_2_2_2 N k x x).
rewrite (Rabs_mult k (RnInnerProduct N x x)).
rewrite (Proposition_4_4_1 N k x).
rewrite (Rmult_comm (RnNorm N x) (Rabs k * RnNorm N x)).
rewrite (Rabs_pos_eq (RnInnerProduct N x x)).
rewrite (proj2 (RnNormNature N x)).
rewrite (Rmult_assoc (Rabs k) (RnNorm N x) (RnNorm N x)).
reflexivity.
apply (Rge_le (RnInnerProduct N x x) 0).
apply (Proposition_4_2_4_1 N x).
Qed.

Lemma Proposition_4_4_2_2 : forall (N : nat) (x y : Rn N), (RnNorm N (Rnplus N x y)) = RnNorm N x + RnNorm N y -> ((exists (k : R), x = (Rnmult N k y) \/ y = (Rnmult N k x)) /\ (RnInnerProduct N x y >= 0)).
Proof.
move=> N x y H1.
apply NNPP.
move=> H2.
apply (Rlt_not_eq (RnNorm N (Rnplus N x y)) (RnNorm N x + RnNorm N y)).
suff: RnNorm N (Rnplus N x y) * RnNorm N (Rnplus N x y) < (RnNorm N x + RnNorm N y) * (RnNorm N x + RnNorm N y).
move=> H3.
apply (Rnot_le_lt (RnNorm N x + RnNorm N y) (RnNorm N (Rnplus N x y))).
move=> H4.
apply (Rlt_not_le ((RnNorm N x + RnNorm N y) * (RnNorm N x + RnNorm N y)) (RnNorm N (Rnplus N x y) * RnNorm N (Rnplus N x y)) H3).
suff: (0 <= (RnNorm N x + RnNorm N y)).
move=> H5.
apply (Rmult_le_compat (RnNorm N x + RnNorm N y) (RnNorm N (Rnplus N x y)) (RnNorm N x + RnNorm N y) (RnNorm N (Rnplus N x y))).
apply H5.
apply H5.
apply H4.
apply H4.
apply (Rplus_le_le_0_compat (RnNorm N x) (RnNorm N y)).
apply (Rge_le (RnNorm N x) 0).
apply (proj1 (RnNormNature N x)).
apply (Rge_le (RnNorm N y) 0).
apply (proj1 (RnNormNature N y)).
rewrite (Formula_4_15_1 N x y).
rewrite (Rmult_plus_distr_l (RnNorm N x + RnNorm N y) (RnNorm N x) (RnNorm N y)).
rewrite (Rmult_plus_distr_r (RnNorm N x) (RnNorm N y) (RnNorm N x)).
rewrite (Rmult_plus_distr_r (RnNorm N x) (RnNorm N y) (RnNorm N y)).
rewrite (Rplus_assoc (RnNorm N x * RnNorm N x) (2 * RnInnerProduct N x y) (RnNorm N y * RnNorm N y)).
rewrite (Rplus_assoc (RnNorm N x * RnNorm N x) (RnNorm N y * RnNorm N x) (RnNorm N x * RnNorm N y + RnNorm N y * RnNorm N y)).
apply (Rplus_lt_compat_l (RnNorm N x * RnNorm N x) (2 * RnInnerProduct N x y + RnNorm N y * RnNorm N y) (RnNorm N y * RnNorm N x + (RnNorm N x * RnNorm N y + RnNorm N y * RnNorm N y))).
rewrite - (Rplus_assoc (RnNorm N y * RnNorm N x) (RnNorm N x * RnNorm N y) (RnNorm N y * RnNorm N y)).
apply (Rplus_lt_compat_r (RnNorm N y * RnNorm N y) (2 * RnInnerProduct N x y) (RnNorm N y * RnNorm N x + RnNorm N x * RnNorm N y)).
rewrite (Rmult_comm (RnNorm N y) (RnNorm N x)).
rewrite - (Rmult_1_l (RnNorm N x * RnNorm N y)).
rewrite - (Rmult_plus_distr_r 1 1 (RnNorm N x * RnNorm N y)).
rewrite /2.
rewrite - INR_IPR.
simpl.
apply (Rmult_lt_compat_l (1 + 1) (RnInnerProduct N x y) (RnNorm N x * RnNorm N y)).
apply (Rlt_trans 0 1 (1 + 1)).
apply Rlt_0_1.
apply (Rlt_plus_1 1).
apply (Rnot_le_lt (RnNorm N x * RnNorm N y) (RnInnerProduct N x y)).
move=> H3.
apply H2.
apply conj.
apply (Proposition_4_3_2 N x y).
elim (Proposition_4_3_1 N x y).
move=> H4.
apply False_ind.
apply (Rlt_irrefl (RnNorm N x * RnNorm N y)).
apply (Rle_lt_trans (RnNorm N x * RnNorm N y) (RnInnerProduct N x y) (RnNorm N x * RnNorm N y)).
apply H3.
apply (Rle_lt_trans (RnInnerProduct N x y) (Rabs (RnInnerProduct N x y)) (RnNorm N x * RnNorm N y)).
apply (Rle_abs (RnInnerProduct N x y)).
apply H4.
apply.
apply (Rle_ge 0 (RnInnerProduct N x y)).
apply (Rle_trans 0 (RnNorm N x * RnNorm N y) (RnInnerProduct N x y)).
rewrite - (Rmult_0_r (RnNorm N x)).
apply (Rmult_le_compat_l (RnNorm N x) 0 (RnNorm N y)).
apply (Rge_le (RnNorm N x) 0).
apply (proj1 (RnNormNature N x)).
apply (Rge_le (RnNorm N y) 0).
apply (proj1 (RnNormNature N y)).
apply H3.
apply H1.
Qed.

Lemma Proposition_4_4_2_3 : forall (N : nat) (x y : Rn N), ((exists (k : R), x = (Rnmult N k y) \/ y = (Rnmult N k x)) /\ (RnInnerProduct N x y >= 0)) -> (RnNorm N (Rnplus N x y)) = RnNorm N x + RnNorm N y.
Proof.
move=> N.
suff: forall x y : Rn N, ((exists k : R, x = Rnmult N k y) /\ RnInnerProduct N x y >= 0) -> RnNorm N (Rnplus N x y) = RnNorm N x + RnNorm N y.
move=> H1.
move=> x y H2.
elim (proj1 H2).
move=> k.
elim.
move=> H3.
apply (H1 x y).
apply conj.
exists k.
apply H3.
apply (proj2 H2).
move=> H3.
rewrite (Rnplus_comm N x y).
rewrite (Rplus_comm (RnNorm N x) (RnNorm N y)).
apply (H1 y x).
apply conj.
exists k.
apply H3.
rewrite (Proposition_4_2_3 N y x).
apply (proj2 H2).
move=> x y H1.
elim (proj1 H1).
move=> k H2.
rewrite H2.
rewrite - {2} (Rnmult_I_l N y).
rewrite - (Rnmult_plus_distr_r N k 1 y).
rewrite (Proposition_4_4_1 N (k + 1) y).
rewrite (Proposition_4_4_1 N k y).
elim (classic (RnNorm N y = 0)).
move=> H3.
rewrite H3.
rewrite (Rmult_0_r (Rabs k)).
rewrite (Rmult_0_r (Rabs (k + 1))).
rewrite (Rplus_0_r 0).
reflexivity.
move=> H3.
rewrite - {3} (Rmult_1_l (RnNorm N y)).
rewrite - (Rmult_plus_distr_r (Rabs k) 1 (RnNorm N y)).
apply (Rmult_eq_compat_r (RnNorm N y) (Rabs (k + 1)) (Rabs k + 1)).
suff: 0 <= k.
move=> H4.
rewrite (Rabs_pos_eq (k + 1)).
rewrite (Rabs_pos_eq k).
reflexivity.
apply H4.
apply (Rle_trans 0 k (k + 1)).
apply H4.
rewrite - {1} (Rplus_0_r k).
apply (Rplus_le_compat_l k 0 1).
apply Rle_0_1.
apply (Rmult_le_reg_r (RnInnerProduct N y y)).
elim (Proposition_4_2_4_1 N y).
apply.
move=> H4.
apply False_ind.
apply H3.
elim (Rmult_integral (RnNorm N y) (RnNorm N y)).
apply.
apply.
rewrite - (proj2 (RnNormNature N y)).
apply H4.
rewrite (Rmult_0_l (RnInnerProduct N y y)).
apply (Rge_le (k * RnInnerProduct N y y) 0).
rewrite - (Proposition_4_2_2_1 N k y y).
rewrite - H2.
apply (proj2 H1).
Qed.

Lemma Proposition_4_4_3_1 : forall (N : nat) (x : Rn N), (RnNorm N x) >= 0.
Proof.
move=> N x.
apply (proj1 (RnNormNature N x)).
Qed.

Lemma Proposition_4_4_3_2 : forall (N : nat) (x : Rn N), (RnNorm N x) = 0 -> x = (RnO N).
Proof.
move=> N x H1.
apply (Proposition_4_2_4_2 N x).
rewrite (proj2 (RnNormNature N x)).
rewrite H1.
apply (Rmult_0_r 0).
Qed.

Lemma Proposition_4_4_3_3 : forall (N : nat) (x : Rn N), x = (RnO N) -> (RnNorm N x) = 0.
Proof.
move=> N x H1.
apply (RnNormNature2 N x).
apply conj.
right.
reflexivity.
rewrite (Proposition_4_2_4_3 N x).
rewrite (Rmult_0_r 0).
reflexivity.
apply H1.
Qed.

Definition Rn_dist (N : nat) := fun (x y : Rn N) => RnNorm N (Rnminus N x y).

Lemma Rn_dist_pos : forall (N : nat) (x y : Rn N), Rn_dist N x y >= 0.
Proof.
move=> N x y.
apply (Proposition_4_4_3_1 N (Rnminus N x y)).
Qed.

Lemma Rn_dist_sym : forall (N : nat) (x y : Rn N), Rn_dist N x y = Rn_dist N y x.
Proof.
move=> N x y.
have: (Rnminus N y x) = (Vadd Rfield (RnVS N) y (Vopp Rfield (RnVS N) x)).
reflexivity.
move=> H1.
unfold Rn_dist.
rewrite H1.
rewrite - (Vopp_minus_distr Rfield (RnVS N) x y).
rewrite - (Vmul_I_l Rfield (RnVS N) (Vadd Rfield (RnVS N) x (Vopp Rfield (RnVS N) y))).
rewrite (Vopp_mul_distr_l Rfield (RnVS N) (FI Rfield) (Vadd Rfield (RnVS N) x (Vopp Rfield (RnVS N) y))).
simpl.
rewrite (Proposition_4_4_1 N (- 1) (Rnplus N x (Rnopp N y))).
rewrite (Rabs_Ropp 1).
rewrite Rabs_R1.
rewrite (Rmult_1_l (RnNorm N (Rnplus N x (Rnopp N y)))).
reflexivity.
Qed.

Lemma Rn_dist_refl : forall (N : nat) (x y : Rn N), Rn_dist N x y = 0 <-> x = y.
Proof.
move=> N x y.
apply conj.
move=> H1.
apply (Vminus_diag_uniq Rfield (RnVS N) x y).
simpl.
apply (Proposition_4_4_3_2 N (Rnplus N x (Rnopp N y))).
apply H1.
move=> H1.
rewrite H1.
unfold Rn_dist.
unfold Rnminus.
rewrite (Rnplus_opp_r N y).
apply (Proposition_4_4_3_3 N (RnO N)).
reflexivity.
Qed.

Lemma Rn_dist_eq : forall (N : nat) (x : Rn N), Rn_dist N x x = 0.
Proof.
move=> N x.
unfold Rn_dist.
unfold Rnminus.
rewrite (Rnplus_opp_r N x).
apply (Proposition_4_4_3_3 N (RnO N)).
reflexivity.
Qed.

Lemma Rn_dist_tri : forall (N : nat) (x y z : Rn N), Rn_dist N x y <= Rn_dist N x z + Rn_dist N z y.
Proof.
move=> N x y z.
unfold Rn_dist.
have: Rnminus N x y = Rnplus N (Rnminus N x z) (Rnminus N z y).
unfold Rnminus.
rewrite - (Rnplus_assoc N (Rnplus N x (Rnopp N z)) z (Rnopp N y)).
rewrite (Rnplus_assoc N x (Rnopp N z) z).
have: Rnplus N (Rnopp N z) z = RnO N.
apply (Vadd_opp_l Rfield (RnVS N) z).
move=> H1.
rewrite H1.
have: (Rnplus N x (RnO N)) = x.
apply (Vadd_O_r Rfield (RnVS N) x).
move=> H2.
rewrite H2.
reflexivity.
move=> H1.
rewrite H1.
apply (Proposition_4_4_2_1 N (Rnminus N x z) (Rnminus N z y)).
Qed.

Definition Rn_met (N : nat) : Metric_Space := Build_Metric_Space (Rn N) (Rn_dist N) (Rn_dist_pos N) (Rn_dist_sym N) (Rn_dist_refl N) (Rn_dist_tri N).

Definition RPCM : CommutativeMonoid := mkCommutativeMonoid R 0 Rplus Rplus_comm Rplus_0_r Rplus_assoc.

Lemma CountFinite : forall (N : nat), Finite (Count N) (Full_set (Count N)).
Proof.
move=> N.
apply EnsembleSetFinite.
elim N.
suff: ((fun u : nat => (u < 0)%nat) = Empty_set nat).
move=> H1.
rewrite H1.
apply Empty_is_finite.
apply Extensionality_Ensembles.
apply conj.
move=> n H1.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r n H1).
move=> n.
elim.
move=> n H1.
suff: ((fun u : nat => (u < S n)%nat) = Add nat (fun u : nat => (u < n)%nat) n).
move=> H2.
rewrite H2.
apply (Union_is_finite nat (fun u : nat => (u < n)%nat) H1 n).
apply (lt_irrefl n).
apply Extensionality_Ensembles.
apply conj.
move=> m H2.
elim (classic (m = n)).
move=> H3.
right.
rewrite H3.
reflexivity.
intro H3.
left.
elim (le_lt_or_eq (S m) (S n) H2).
apply (lt_S_n m n).
move=> H4.
apply False_ind.
apply H3.
apply (PeanoNat.Nat.succ_inj m n H4).
move=> m.
elim.
move=> m1 H2.
apply (le_S (S m1) n).
apply H2.
move=> m1 H2.
rewrite H2.
apply (le_n (S m1)).
Qed.

Lemma RnInnerProductDefinition : forall (N : nat) (x y : Rn N), (RnInnerProduct N x y) = MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) RPCM (fun (n : Count N) => (x n) * (y n)).
Proof.
move=> N x y.
rewrite<- (MySumF2Nature2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) RPCM (fun (n : Count N) => (x n) * (y n)) N (fun (n : Count N) => n) (fun (n : Count N) => Full_intro (Count N) n)).
unfold RnInnerProduct.
unfold SumGF.
suff: (forall (n : nat), my_sum_f_R (fun n : nat => UnwrapRn N x n * UnwrapRn N y n) n = SumGFSub (Count N) RPCM N (fun n : Count N => n) (fun n : Count N => x n * y n) n).
move=> H1.
apply (H1 N).
elim.
simpl.
reflexivity.
move=> n H1.
simpl.
unfold UnwrapGF.
unfold UnwrapRn at 3.
unfold UnwrapRn at 3.
elim (excluded_middle_informative (n < N)%nat).
rewrite H1.
reflexivity.
move=> H2.
rewrite H1.
simpl.
rewrite (Rmult_0_r 0).
reflexivity.
simpl.
exists (fun (u : {u : Count N | Full_set (Count N) u}) => proj1_sig u).
apply conj.
move=> n.
reflexivity.
move=> n.
apply sig_map.
reflexivity.
Qed.

Definition Un_cv_met (met : Metric_Space) (Un : nat -> (Base met)) (m : (Base met)) := forall (eps : R), eps > 0 -> exists (N : nat), forall (n : nat), (n >= N)%nat -> (dist met) (Un n) m < eps.

Definition Cauchy_met (met : Metric_Space) (Un : nat -> (Base met)) := forall (eps : R), eps > 0 -> exists (N : nat), forall (n m : nat), (n >= N)%nat -> (m >= N)%nat -> (dist met) (Un n) (Un m) < eps.

Lemma Theorem_4_5_1 : forall (N : nat) (An : nat -> (Rn N)) (a : (Rn N)), (Un_cv_met (Rn_met N) An a) <-> (forall (n : Count N), Un_cv (fun (n0 : nat) => (An n0 n)) (a n)).
Proof.
move=> N An a.
apply conj.
move=> H1 n eps H2.
elim (H1 eps).
move=> K H3.
exists K.
move=> n0 H4.
suff: (dist (Rn_met N) (An n0) a < eps).
move=> H5.
suff: ((RnInnerProduct N (Rnminus N (An n0) a) (Rnminus N (An n0) a)) < eps * eps).
rewrite RnInnerProductDefinition.
move=> H6.
suff: (R_dist (An n0 n) (a n) * R_dist (An n0 n) (a n) < eps * eps).
move=> H7.
apply (Rnot_le_lt eps (R_dist (An n0 n) (a n))).
move=> H8.
apply (Rlt_not_le (eps * eps) (R_dist (An n0 n) (a n) * R_dist (An n0 n) (a n)) H7).
apply (Rmult_le_compat eps (R_dist (An n0 n) (a n)) eps (R_dist (An n0 n) (a n))).
apply (Rlt_le 0 eps H2).
apply (Rlt_le 0 eps H2).
apply H8.
apply H8.
apply (Rle_lt_trans (R_dist (An n0 n) (a n) * R_dist (An n0 n) (a n)) (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) RPCM (fun n : Count N => Rnminus N (An n0) a n * Rnminus N (An n0) a n)) (eps * eps)).
rewrite (MySumF2Excluded (Count N) RPCM (fun n1 : Count N => Rnminus N (An n0) a n1 * Rnminus N (An n0) a n1) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Singleton (Count N) n)).
simpl.
suff: ((FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Singleton (Count N) n)) = (exist (Finite (Count N)) (Singleton (Count N) n) (Singleton_is_finite (Count N) n))).
move=> H7.
rewrite H7.
rewrite MySumF2Singleton.
suff: (R_dist (An n0 n) (a n) * R_dist (An n0 n) (a n) = Rnminus N (An n0) a n * Rnminus N (An n0) a n).
move=> H8.
rewrite H8.
rewrite - {1} (Rplus_0_r (Rnminus N (An n0) a n * Rnminus N (An n0) a n)).
apply (Rplus_le_compat_l (Rnminus N (An n0) a n * Rnminus N (An n0) a n) 0 (MySumF2 (Count N) (exist (Finite (Count N)) (Intersection (Count N) (Ensembles.Complement (Count N) (Singleton (Count N) n)) (Full_set (Count N))) (Intersection_preserves_finite (Count N) (Full_set (Count N)) (CountFinite N) (Ensembles.Complement (Count N) (Singleton (Count N) n)))) RPCM (fun n1 : Count N => Rnminus N (An n0) a n1 * Rnminus N (An n0) a n1))).
apply MySumF2Induction.
apply conj.
apply (Req_le 0 0).
reflexivity.
move=> r1 r2 H9 H10.
simpl.
rewrite<- (Rplus_0_r 0).
apply (Rplus_le_compat 0 r1 0 (Rnminus N (An n0) a r2 * Rnminus N (An n0) a r2)).
apply H10.
apply Rge_le.
apply (Formula_1_3_2 (Rnminus N (An n0) a r2)).
unfold R_dist.
unfold Rnminus.
unfold Rnplus.
unfold Rnopp.
simpl.
unfold Rabs.
elim (Rcase_abs (An n0 n - a n)).
move=> H8.
apply Rmult_opp_opp.
move=> H8.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> n1.
elim.
move=> n2 H7 H8.
apply H7.
move=> n1 H7.
apply Intersection_intro.
apply H7.
apply Full_intro.
apply H6.
rewrite (proj2 (RnNormNature N (Rnminus N (An n0) a))).
apply (Rmult_ge_0_gt_0_lt_compat (RnNorm N (Rnminus N (An n0) a)) eps (RnNorm N (Rnminus N (An n0) a)) eps).
apply (proj1 (RnNormNature N (Rnminus N (An n0) a))).
apply H2.
apply H5.
apply H5.
apply (H3 n0 H4).
apply H2.
move=> H1.
suff: (forall (n0 : nat) (eps : R), eps > 0 -> exists (n1 : nat), forall (n2 : nat), (n2 >= n1)%nat -> (my_sum_f_R (fun n : nat => UnwrapRn N (Rnminus N (An n2) a) n * UnwrapRn N (Rnminus N (An n2) a) n) n0) < eps).
move=> H2 eps H3.
elim (H2 N (eps * eps) (Rmult_gt_0_compat eps eps H3 H3)).
move=> N1 H4.
exists N1.
move=> n H5.
suff: (dist (Rn_met N) (An n) a * dist (Rn_met N) (An n) a < eps * eps).
move=> H6.
apply (Rnot_le_lt eps (dist (Rn_met N) (An n) a)).
move=> H7.
apply (Rlt_not_le (eps * eps) (dist (Rn_met N) (An n) a * dist (Rn_met N) (An n) a) H6).
apply (Rmult_le_compat eps (dist (Rn_met N) (An n) a) eps (dist (Rn_met N) (An n) a)).
apply (Rlt_le 0 eps H3).
apply (Rlt_le 0 eps H3).
apply H7.
apply H7.
suff: (dist (Rn_met N) (An n) a * dist (Rn_met N) (An n) a = my_sum_f_R (fun n0 : nat => UnwrapRn N (Rnminus N (An n) a) n0 * UnwrapRn N (Rnminus N (An n) a) n0) N).
move=> H6.
rewrite H6.
apply (H4 n H5).
unfold Rn_met.
unfold dist.
unfold Rn_dist.
unfold RnNorm.
rewrite<- (proj2 (MySqrtNature (exist (fun r : R => r >= 0) (RnInnerProduct N (Rnminus N (An n) a) (Rnminus N (An n) a)) (Proposition_4_2_4_1 N (Rnminus N (An n) a))))).
reflexivity.
elim.
move=> eps H2.
exists O.
move=> n1 H3.
apply H2.
move=> n1 H2 eps H3.
elim (H2 (eps / 2) (eps2_Rgt_R0 eps H3)).
move=> N1 H4.
elim (classic (n1 < N)%nat).
move=> H5.
suff: (MySqrt (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3))) > 0).
move=> H6.
elim (H1 (exist (fun (m : nat) => (m < N)%nat) n1 H5) (MySqrt (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3)))) H6).
move=> N2 H7.
exists (max N1 N2).
move=> n2 H8.
simpl.
rewrite<- (eps2 eps).
apply (Rplus_lt_compat (my_sum_f_R (fun n : nat => UnwrapRn N (Rnminus N (An n2) a) n * UnwrapRn N (Rnminus N (An n2) a) n) n1) (eps * / 2) (UnwrapRn N (Rnminus N (An n2) a) n1 *
UnwrapRn N (Rnminus N (An n2) a) n1) (eps * / 2)).
apply (H4 n2).
apply (le_trans N1 (max N1 N2) n2).
apply (Nat.le_max_l N1 N2).
apply H8.
suff: (UnwrapRn N (Rnminus N (An n2) a) n1 * UnwrapRn N (Rnminus N (An n2) a) n1 = R_dist (An n2 (exist (fun m : nat => (m < N)%nat) n1 H5)) (a (exist (fun m : nat => (m < N)%nat) n1 H5)) * R_dist (An n2 (exist (fun m : nat => (m < N)%nat) n1 H5)) (a (exist (fun m : nat => (m < N)%nat) n1 H5))).
move=> H9.
rewrite H9.
suff: ((proj1_sig (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3)))) = eps * / 2).
move=> H10.
rewrite<- H10.
rewrite (proj2 (MySqrtNature (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3))))).
suff: (R_dist (An n2 (exist (fun m : nat => (m < N)%nat) n1 H5)) (a (exist (fun m : nat => (m < N)%nat) n1 H5)) < MySqrt (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3)))).
move=> H11.
apply (Rmult_le_0_lt_compat (R_dist (An n2 (exist (fun m : nat => (m < N)%nat) n1 H5)) (a (exist (fun m : nat => (m < N)%nat) n1 H5))) (MySqrt (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3)))) (R_dist (An n2 (exist (fun m : nat => (m < N)%nat) n1 H5)) (a (exist (fun m : nat => (m < N)%nat) n1 H5))) (MySqrt (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3))))).
apply Rge_le.
apply R_dist_pos.
apply Rge_le.
apply R_dist_pos.
apply H11.
apply H11.
apply (H7 n2).
apply (le_trans N2 (max N1 N2) n2).
apply (Nat.le_max_r N1 N2).
apply H8.
reflexivity.
unfold UnwrapRn.
unfold R_dist.
elim (excluded_middle_informative (n1 < N)%nat).
move=> H9.
unfold Rnminus.
unfold Rnplus.
unfold Rnopp.
suff: ((exist (fun n0 : nat => (n0 < N)%nat) n1 H9) = (exist (fun m : nat => (m < N)%nat) n1 H5)).
move=> H10.
rewrite H10.
unfold Rabs.
elim (Rcase_abs (An n2 (exist (fun m : nat => (m < N)%nat) n1 H5) - a (exist (fun m : nat => (m < N)%nat) n1 H5))).
move=> H11.
rewrite Rmult_opp_opp.
reflexivity.
move=> H11.
reflexivity.
apply sig_map.
reflexivity.
move=> H9.
apply False_ind.
apply (H9 H5).
elim (proj1 (MySqrtNature (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3))))).
apply.
move=> H6.
apply False_ind.
apply (Rlt_irrefl 0).
rewrite - {2} (Rmult_0_r 0).
rewrite - {2} H6.
rewrite - {4} H6.
rewrite<- (proj2 (MySqrtNature (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3))))).
apply (eps2_Rgt_R0 eps H3).
move=> H5.
exists N1.
move=> n2 H6.
simpl.
unfold UnwrapRn at 3.
unfold UnwrapRn at 3.
elim (excluded_middle_informative (n1 < N)%nat).
move=> H7.
apply False_ind.
apply (H5 H7).
move=> H7.
rewrite (Rmult_0_r 0).
rewrite (Rplus_0_r (my_sum_f_R (fun n : nat => UnwrapRn N (Rnminus N (An n2) a) n * UnwrapRn N (Rnminus N (An n2) a) n) n1)).
apply (Rlt_trans (my_sum_f_R (fun n : nat => UnwrapRn N (Rnminus N (An n2) a) n * UnwrapRn N (Rnminus N (An n2) a) n) n1) (eps * / 2) eps).
apply (H4 n2).
apply H6.
apply (Rlt_eps2_eps eps H3).
Qed.

Lemma Theorem_4_5_2 : forall (N : nat) (An : nat -> (Rn N)), (Cauchy_met (Rn_met N) An) <-> (forall (n : Count N), Cauchy_crit (fun (n0 : nat) => (An n0 n))).
Proof.
move=> N An.
apply conj.
move=> H1 n eps H2.
elim (H1 eps).
move=> K H3.
exists K.
move=> n0 m0 H4 H5.
suff: (dist (Rn_met N) (An n0) (An m0) < eps).
move=> H6.
suff: ((RnInnerProduct N (Rnminus N (An n0) (An m0)) (Rnminus N (An n0) (An m0))) < eps * eps).
rewrite RnInnerProductDefinition.
move=> H7.
suff: (R_dist (An n0 n) (An m0 n) * R_dist (An n0 n) (An m0 n) < eps * eps).
move=> H8.
apply (Rnot_le_lt eps (R_dist (An n0 n) (An m0 n))).
move=> H9.
apply (Rlt_not_le (eps * eps) (R_dist (An n0 n) (An m0 n) * R_dist (An n0 n) (An m0 n)) H8).
apply (Rmult_le_compat eps (R_dist (An n0 n) (An m0 n)) eps (R_dist (An n0 n) (An m0 n))).
apply (Rlt_le 0 eps H2).
apply (Rlt_le 0 eps H2).
apply H9.
apply H9.
apply (Rle_lt_trans (R_dist (An n0 n) (An m0 n) * R_dist (An n0 n) (An m0 n)) (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) RPCM (fun n : Count N => Rnminus N (An n0) (An m0) n * Rnminus N (An n0) (An m0) n)) (eps * eps)).
rewrite (MySumF2Excluded (Count N) RPCM (fun n1 : Count N => Rnminus N (An n0) (An m0) n1 * Rnminus N (An n0) (An m0) n1) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Singleton (Count N) n)).
simpl.
suff: ((FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Singleton (Count N) n)) = (exist (Finite (Count N)) (Singleton (Count N) n) (Singleton_is_finite (Count N) n))).
move=> H8.
rewrite H8.
rewrite MySumF2Singleton.
suff: (R_dist (An n0 n) (An m0 n) * R_dist (An n0 n) (An m0 n) = Rnminus N (An n0) (An m0) n * Rnminus N (An n0) (An m0) n).
move=> H9.
rewrite H9.
rewrite - {1} (Rplus_0_r (Rnminus N (An n0) (An m0) n * Rnminus N (An n0) (An m0) n)).
apply (Rplus_le_compat_l (Rnminus N (An n0) (An m0) n * Rnminus N (An n0) (An m0) n) 0 (MySumF2 (Count N) (exist (Finite (Count N)) (Intersection (Count N) (Ensembles.Complement (Count N) (Singleton (Count N) n)) (Full_set (Count N))) (Intersection_preserves_finite (Count N) (Full_set (Count N)) (CountFinite N) (Ensembles.Complement (Count N) (Singleton (Count N) n)))) RPCM (fun n1 : Count N => Rnminus N (An n0) (An m0) n1 * Rnminus N (An n0) (An m0) n1))).
apply MySumF2Induction.
apply conj.
apply (Req_le 0 0).
reflexivity.
move=> r1 u H10 H11.
simpl.
rewrite<- (Rplus_0_r 0).
apply (Rplus_le_compat 0 r1 0 (Rnminus N (An n0) (An m0) u * Rnminus N (An n0) (An m0) u)).
apply H11.
apply Rge_le.
apply (Formula_1_3_2 (Rnminus N (An n0) (An m0) u)).
unfold R_dist.
unfold Rnminus.
unfold Rnplus.
unfold Rnopp.
simpl.
unfold Rabs.
elim (Rcase_abs (An n0 n - An m0 n)).
move=> H9.
apply Rmult_opp_opp.
move=> H9.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> n1.
elim.
move=> n2 H8 H9.
apply H8.
move=> n1 H8.
apply Intersection_intro.
apply H8.
apply Full_intro.
apply H7.
rewrite (proj2 (RnNormNature N (Rnminus N (An n0) (An m0)))).
apply (Rmult_ge_0_gt_0_lt_compat (RnNorm N (Rnminus N (An n0) (An m0))) eps (RnNorm N (Rnminus N (An n0) (An m0))) eps).
apply (proj1 (RnNormNature N (Rnminus N (An n0) (An m0)))).
apply H2.
apply H6.
apply H6.
apply (H3 n0 m0 H4 H5).
apply H2.
move=> H1.
suff: (forall (n0 : nat) (eps : R), eps > 0 -> exists (n1 : nat), forall (n2 m2 : nat), (n2 >= n1)%nat -> (m2 >= n1)%nat -> (my_sum_f_R (fun n : nat => UnwrapRn N (Rnminus N (An n2) (An m2)) n * UnwrapRn N (Rnminus N (An n2) (An m2)) n) n0) < eps).
move=> H2 eps H3.
elim (H2 N (eps * eps) (Rmult_gt_0_compat eps eps H3 H3)).
move=> N1 H4.
exists N1.
move=> n m H5 H6.
suff: (dist (Rn_met N) (An n) (An m) * dist (Rn_met N) (An n) (An m) < eps * eps).
move=> H7.
apply (Rnot_le_lt eps (dist (Rn_met N) (An n) (An m))).
move=> H8.
apply (Rlt_not_le (eps * eps) (dist (Rn_met N) (An n) (An m) * dist (Rn_met N) (An n) (An m)) H7).
apply (Rmult_le_compat eps (dist (Rn_met N) (An n) (An m)) eps (dist (Rn_met N) (An n) (An m))).
apply (Rlt_le 0 eps H3).
apply (Rlt_le 0 eps H3).
apply H8.
apply H8.
suff: (dist (Rn_met N) (An n) (An m) * dist (Rn_met N) (An n) (An m) = my_sum_f_R (fun n0 : nat => UnwrapRn N (Rnminus N (An n) (An m)) n0 * UnwrapRn N (Rnminus N (An n) (An m)) n0) N).
move=> H7.
rewrite H7.
apply (H4 n m H5 H6).
unfold Rn_met.
unfold dist.
unfold Rn_dist.
unfold RnNorm.
rewrite<- (proj2 (MySqrtNature (exist (fun r : R => r >= 0) (RnInnerProduct N (Rnminus N (An n) (An m)) (Rnminus N (An n) (An m))) (Proposition_4_2_4_1 N (Rnminus N (An n) (An m)))))).
reflexivity.
elim.
move=> eps H2.
exists O.
move=> n1 m1 H3 H4.
apply H2.
move=> n1 H2 eps H3.
elim (H2 (eps / 2) (eps2_Rgt_R0 eps H3)).
move=> N1 H4.
elim (classic (n1 < N)%nat).
move=> H5.
suff: (MySqrt (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3))) > 0).
move=> H6.
elim (H1 (exist (fun (m : nat) => (m < N)%nat) n1 H5) (MySqrt (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3)))) H6).
move=> N2 H7.
exists (max N1 N2).
move=> n2 m2 H8 H9.
simpl.
rewrite<- (eps2 eps).
apply (Rplus_lt_compat (my_sum_f_R (fun n : nat => UnwrapRn N (Rnminus N (An n2) (An m2)) n * UnwrapRn N (Rnminus N (An n2) (An m2)) n) n1) (eps * / 2) (UnwrapRn N (Rnminus N (An n2) (An m2)) n1 * UnwrapRn N (Rnminus N (An n2) (An m2)) n1) (eps * / 2)).
apply (H4 n2).
apply (le_trans N1 (max N1 N2) n2).
apply (Nat.le_max_l N1 N2).
apply H8.
apply (le_trans N1 (max N1 N2) m2).
apply (Nat.le_max_l N1 N2).
apply H9.
suff: (UnwrapRn N (Rnminus N (An n2) (An m2)) n1 * UnwrapRn N (Rnminus N (An n2) (An m2)) n1 = R_dist (An n2 (exist (fun m : nat => (m < N)%nat) n1 H5)) (An m2 (exist (fun m : nat => (m < N)%nat) n1 H5)) * R_dist (An n2 (exist (fun m : nat => (m < N)%nat) n1 H5)) (An m2 (exist (fun m : nat => (m < N)%nat) n1 H5))).
move=> H10.
rewrite H10.
suff: ((proj1_sig (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3)))) = eps * / 2).
move=> H11.
rewrite<- H11.
rewrite (proj2 (MySqrtNature (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3))))).
suff: (R_dist (An n2 (exist (fun m : nat => (m < N)%nat) n1 H5)) (An m2 (exist (fun m : nat => (m < N)%nat) n1 H5)) < MySqrt (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3)))).
move=> H12.
apply (Rmult_le_0_lt_compat (R_dist (An n2 (exist (fun m : nat => (m < N)%nat) n1 H5)) (An m2 (exist (fun m : nat => (m < N)%nat) n1 H5))) (MySqrt (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3)))) (R_dist (An n2 (exist (fun m : nat => (m < N)%nat) n1 H5)) (An m2 (exist (fun m : nat => (m < N)%nat) n1 H5))) (MySqrt (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3))))).
apply Rge_le.
apply R_dist_pos.
apply Rge_le.
apply R_dist_pos.
apply H12.
apply H12.
apply (H7 n2).
apply (le_trans N2 (max N1 N2) n2).
apply (Nat.le_max_r N1 N2).
apply H8.
apply (le_trans N2 (max N1 N2) m2).
apply (Nat.le_max_r N1 N2).
apply H9.
reflexivity.
unfold UnwrapRn.
unfold R_dist.
elim (excluded_middle_informative (n1 < N)%nat).
move=> H10.
unfold Rnminus.
unfold Rnplus.
unfold Rnopp.
suff: ((exist (fun n0 : nat => (n0 < N)%nat) n1 H10) = (exist (fun m : nat => (m < N)%nat) n1 H5)).
move=> H11.
rewrite H11.
unfold Rabs.
elim (Rcase_abs (An n2 (exist (fun m : nat => (m < N)%nat) n1 H5) - An m2 (exist (fun m : nat => (m < N)%nat) n1 H5))).
move=> H12.
rewrite Rmult_opp_opp.
reflexivity.
move=> H12.
reflexivity.
apply sig_map.
reflexivity.
move=> H10.
apply False_ind.
apply (H10 H5).
elim (proj1 (MySqrtNature (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3))))).
apply.
move=> H6.
apply False_ind.
apply (Rlt_irrefl 0).
rewrite - {2} (Rmult_0_r 0).
rewrite - {2} H6.
rewrite - {4} H6.
rewrite<- (proj2 (MySqrtNature (exist (fun r : R => r >= 0) (eps * / 2) (Rgt_ge (eps * / 2) 0 (eps2_Rgt_R0 eps H3))))).
apply (eps2_Rgt_R0 eps H3).
move=> H5.
exists N1.
move=> n2 m2 H6 H7.
simpl.
unfold UnwrapRn at 3.
unfold UnwrapRn at 3.
elim (excluded_middle_informative (n1 < N)%nat).
move=> H8.
apply False_ind.
apply (H5 H8).
move=> H8.
rewrite (Rmult_0_r 0).
rewrite (Rplus_0_r (my_sum_f_R (fun n : nat => UnwrapRn N (Rnminus N (An n2) (An m2)) n * UnwrapRn N (Rnminus N (An n2) (An m2)) n) n1)).
apply (Rlt_trans (my_sum_f_R (fun n : nat => UnwrapRn N (Rnminus N (An n2) (An m2)) n * UnwrapRn N (Rnminus N (An n2) (An m2)) n) n1) (eps * / 2) eps).
apply (H4 n2).
apply H6.
apply H7.
apply (Rlt_eps2_eps eps H3).
Qed.

Lemma Theorem_4_5_3 : forall (N : nat) (An : nat -> (Rn N)), (exists (a : Rn N), Un_cv_met (Rn_met N) An a) <-> Cauchy_met (Rn_met N) An.
Proof.
move=> N An.
apply conj.
move=> H1.
elim H1.
move=> a H2.
apply Theorem_4_5_2.
move=> n.
apply Theorem_3_6.
exists (a n).
apply Theorem_4_5_1.
apply H2.
move=> H1.
suff: (forall (n : Count N), Cauchy_crit (fun (m : nat) => An m n)).
move=> H2.
suff: (forall (n : Count N), exists (an : R), Un_cv (fun (m : nat) => An m n) an).
move=> H3.
suff: (forall (n : Count N), {an : R | Un_cv (fun (m : nat) => An m n) an}).
move=> H4.
exists (fun (n : Count N) => (proj1_sig (H4 n))).
apply Theorem_4_5_1.
move=> n.
apply (proj2_sig (H4 n)).
move=> n.
apply constructive_definite_description.
apply (unique_existence (fun (x : R) => Un_cv (fun m : nat => An m n) x)).
apply conj.
apply (H3 n).
move=> r1 r2 H4 H5.
apply (Proposition_2_3 (fun m : nat => An m n) r1 r2 H4 H5).
move=> n.
apply Theorem_3_6.
apply (H2 n).
apply Theorem_4_5_2.
apply H1.
Qed.

Lemma Theorem_4_5_4 : forall (N : nat) (An Bn : nat -> Rn N), (Subsequence (Rn N) An Bn) -> forall (x : Rn N), (Un_cv_met (Rn_met N) Bn x) -> (Un_cv_met (Rn_met N) An x).
Proof.
move=> N An Bn H1 x H2.
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

Lemma Theorem_4_5_5 : forall (N : nat) (An : nat -> Rn N) (a : Rn N), (Un_cv_met (Rn_met N) An a) -> (exists (M : R), forall (n : nat), (RnNorm N (An n)) <= M).
Proof.
move=> N An a H1.
suff: (exists (M : R), forall (n : nat), (RnInnerProduct N (An n) (An n)) <= M).
move=> H2.
elim H2.
move=> M H3.
elim (classic (M >= 0)).
move=> H4.
exists (MySqrt (exist (fun (r : R) => r >= 0) M H4)).
move=> n.
apply (Rnot_lt_le (MySqrt (exist (fun r : R => r >= 0) M H4)) (RnNorm N (An n))).
move=> H5.
apply (Rle_not_lt M (RnInnerProduct N (An n) (An n)) (H3 n)).
suff: (M = (proj1_sig (exist (fun r : R => r >= 0) M H4))).
move=> H6.
rewrite H6.
rewrite (proj2 (MySqrtNature (exist (fun r : R => r >= 0) M H4))).
rewrite (proj2 (RnNormNature N (An n))).
apply (Rmult_le_0_lt_compat (MySqrt (exist (fun r : R => r >= 0) M H4)) (RnNorm N (An n)) (MySqrt (exist (fun r : R => r >= 0) M H4)) (RnNorm N (An n))).
apply Rge_le.
apply (proj1 (MySqrtNature (exist (fun r : R => r >= 0) M H4))).
apply Rge_le.
apply (proj1 (MySqrtNature (exist (fun r : R => r >= 0) M H4))).
apply H5.
apply H5.
reflexivity.
move=> H4.
apply False_ind.
apply H4.
apply (Rge_trans M (RnInnerProduct N (An O) (An O)) 0).
apply Rle_ge.
apply (H3 O).
apply ((Proposition_4_2_4_1 N (An O))).
suff: (forall (N1 : nat), (N1 <= N)%nat -> exists (M : R), forall (n : nat), my_sum_f_R (fun n2 : nat => UnwrapRn N (An n) n2 * UnwrapRn N (An n) n2) N1 <= M).
apply.
apply (le_n N).
elim.
move=> H2.
exists 0.
move=> n.
simpl.
apply (Req_le 0 0).
reflexivity.
move=> n H2 H3.
suff: (n < N)%nat.
move=> H4.
elim H2.
move=> M1 H5.
elim (proj1 (bounded_abs (fun x : R => exists n0 : nat, An n0 (exist (fun (n1 : nat) => (n1 < N)%nat) n H4) = x))).
move=> M2 H6.
exists (M1 + M2 * M2).
move=> n0.
simpl.
apply (Rplus_le_compat (my_sum_f_R (fun n2 : nat => UnwrapRn N (An n0) n2 * UnwrapRn N (An n0) n2) n) M1 (UnwrapRn N (An n0) n * UnwrapRn N (An n0) n) (M2 * M2)).
apply (H5 n0).
unfold UnwrapRn.
elim (excluded_middle_informative (n < N)%nat).
move=> H7.
suff: (An n0 (exist (fun n1 : nat => (n1 < N)%nat) n H7) * An n0 (exist (fun n1 : nat => (n1 < N)%nat) n H7) = Rabs (An n0 (exist (fun n1 : nat => (n1 < N)%nat) n H7)) * Rabs (An n0 (exist (fun n1 : nat => (n1 < N)%nat) n H7))).
move=> H8.
rewrite H8.
suff: (Rabs (An n0 (exist (fun n1 : nat => (n1 < N)%nat) n H7)) <= M2).
move=> H9.
apply (Rmult_le_compat (Rabs (An n0 (exist (fun n1 : nat => (n1 < N)%nat) n H7))) M2 (Rabs (An n0 (exist (fun n1 : nat => (n1 < N)%nat) n H7))) M2).
apply Rabs_pos.
apply Rabs_pos.
apply H9.
apply H9.
apply (H6 (Rabs (An n0 (exist (fun n1 : nat => (n1 < N)%nat) n H7)))).
apply (Im_intro R R (fun x : R => exists n1 : nat, An n1 (exist (fun n2 : nat => (n2 < N)%nat) n H4) = x) Rabs (An n0 (exist (fun n1 : nat => (n1 < N)%nat) n H7))).
exists n0.
suff: ((exist (fun n2 : nat => (n2 < N)%nat) n H4) = (exist (fun n1 : nat => (n1 < N)%nat) n H7)).
move=> H9.
rewrite H9.
reflexivity.
apply sig_map.
reflexivity.
reflexivity.
unfold Rabs.
elim (Rcase_abs (An n0 (exist (fun n1 : nat => (n1 < N)%nat) n H7))).
move=> H8.
rewrite Rmult_opp_opp.
reflexivity.
move=> H8.
reflexivity.
move=> H7.
apply False_ind.
apply (H7 H4).
apply Proposition_2_4.
apply Theorem_3_6.
apply Theorem_4_5_2.
apply Theorem_4_5_3.
exists a.
apply H1.
apply (lt_le_weak n N H4).
apply H3.
Qed.

Lemma Proposition_4_6_1 : forall (N : nat) (xn yn : nat -> Rn N) (x y : Rn N), (Un_cv_met (Rn_met N) xn x) -> (Un_cv_met (Rn_met N) yn y) -> (Un_cv_met (Rn_met N) (fun (n : nat) => Rnplus N (xn n) (yn n)) (Rnplus N x y)).
Proof.
move=> N xn yn x y H1 H2.
apply Theorem_4_5_1.
move=> n.
apply Theorem_2_5_1_plus.
apply Theorem_4_5_1.
apply H1.
apply Theorem_4_5_1.
apply H2.
Qed.

Lemma Proposition_4_6_2 : forall (N : nat) (xn yn : nat -> Rn N) (x y : Rn N), (Un_cv_met (Rn_met N) xn x) -> (Un_cv_met (Rn_met N) yn y) -> (Un_cv_met (Rn_met N) (fun (n : nat) => Rnminus N (xn n) (yn n)) (Rnminus N x y)).
Proof.
move=> N xn yn x y H1 H2.
apply Theorem_4_5_1.
move=> n.
apply Theorem_2_5_1_minus.
apply Theorem_4_5_1.
apply H1.
apply Theorem_4_5_1.
apply H2.
Qed.

Lemma Proposition_4_6_3 : forall (N : nat) (xn : nat -> Rn N) (x : Rn N) (a : R), (Un_cv_met (Rn_met N) xn x) -> (Un_cv_met (Rn_met N) (fun (n : nat) => Rnmult N a (xn n)) (Rnmult N a x)).
Proof.
move=> N xn x a H1.
apply Theorem_4_5_1.
move=> n.
apply Theorem_2_5_1_mult.
move=> eps H2.
exists O.
move=> n0 H3.
rewrite (R_dist_eq a).
apply H2.
apply Theorem_4_5_1.
apply H1.
Qed.

Lemma Proposition_4_6_4 : forall (N : nat) (xn : nat -> Rn N) (x : Rn N), (Un_cv_met (Rn_met N) xn x) -> (Un_cv_met (Rn_met N) (fun (n : nat) => Rnopp N (xn n)) (Rnopp N x)).
Proof.
move=> N xn x H1.
apply Theorem_4_5_1.
move=> n.
apply Theorem_2_5_1_opp.
apply Theorem_4_5_1.
apply H1.
Qed.

Definition C := (Rn 2).

Definition CRe := (exist (fun (n : nat) => (n < 2)%nat) O (le_S 1 1 (le_n 1))).

Definition CIm := (exist (fun (n : nat) => (n < 2)%nat) 1%nat (le_n 2)).

Lemma CReorCIm : forall (n : Count 2), {n = CRe} + {n = CIm}.
Proof.
move=> n.
elim (excluded_middle_informative (proj1_sig n = O)).
move=> H1.
left.
apply sig_map.
apply H1.
move=> H2.
right.
apply sig_map.
elim (le_lt_or_eq (proj1_sig n) 1).
move=> H3.
apply False_ind.
apply H2.
rewrite<- (le_n_0_eq (proj1_sig n)).
reflexivity.
apply (le_S_n (proj1_sig n) O H3).
apply.
apply le_S_n.
apply (proj2_sig n).
Qed.

Definition Cmake (r1 r2 : R) := fun (n : Count 2) => match CReorCIm n with
| left _ => r1
| right _ => r2
end.

Lemma CmakeRe : forall (r1 r2 : R), Cmake r1 r2 CRe = r1.
Proof.
move=> r1 r2.
unfold Cmake.
elim (CReorCIm CRe).
move=> H1.
reflexivity.
move=> H2.
apply False_ind.
suff: (O <> 1%nat).
move=> H3.
apply H3.
suff: (proj1_sig CRe = proj1_sig CIm).
apply.
rewrite H2.
reflexivity.
apply (n_Sn 0).
Qed.

Lemma CmakeIm : forall (r1 r2 : R), Cmake r1 r2 CIm = r2.
Proof.
move=> r1 r2.
unfold Cmake.
elim (CReorCIm CIm).
move=> H1.
apply False_ind.
suff: (1%nat <> O).
move=> H2.
apply H2.
suff: (proj1_sig CIm = proj1_sig CRe).
apply.
rewrite H1.
reflexivity.
move=> H2.
apply (n_Sn 0).
rewrite H2.
reflexivity.
move=> H1.
reflexivity.
Qed.

Definition Cmult := fun (c1 c2 : C) => Cmake ((c1 CRe) * (c2 CRe) - (c1 CIm) * (c2 CIm)) ((c1 CRe) * (c2 CIm) + (c1 CIm) * (c2 CRe)).

Definition Cinv := fun (c : C) => Cmake ((c CRe) / ((c CRe) * (c CRe) + (c CIm) * (c CIm))) (- (c CIm) / ((c CRe) * (c CRe) + (c CIm) * (c CIm))).

Definition Cplus := Rnplus 2.

Definition Cplus_assoc : forall (c1 c2 c3 : C), (Cplus (Cplus c1 c2) c3) = (Cplus c1 (Cplus c2 c3)) := (Rnplus_assoc 2).

Lemma Cmult_assoc : forall (c1 c2 c3 : C), (Cmult (Cmult c1 c2) c3) = (Cmult c1 (Cmult c2 c3)).
Proof.
move=> c1 c2 c3.
apply functional_extensionality.
move=> x.
unfold Cmult.
unfold Cmake at 1.
unfold Cmake at 5.
elim (CReorCIm x).
move=> H1.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite (Rmult_plus_distr_r (c1 CRe * c2 CRe) (- (c1 CIm * c2 CIm)) (c3 CRe)).
rewrite (Rmult_plus_distr_r (c1 CRe * c2 CIm) (c1 CIm * c2 CRe) (c3 CIm)).
rewrite (Rmult_plus_distr_l (c1 CRe) (c2 CRe * c3 CRe) (- (c2 CIm * c3 CIm))).
rewrite (Rmult_plus_distr_l (c1 CIm) (c2 CRe * c3 CIm) (c2 CIm * c3 CRe)).
rewrite (Rmult_assoc (c1 CRe) (c2 CRe) (c3 CRe)).
unfold Rminus.
rewrite (Rplus_assoc (c1 CRe * (c2 CRe * c3 CRe)) (- (c1 CIm * c2 CIm) * c3 CRe) (- (c1 CRe * c2 CIm * c3 CIm + c1 CIm * c2 CRe * c3 CIm))).
rewrite (Rplus_assoc (c1 CRe * (c2 CRe * c3 CRe)) (c1 CRe * - (c2 CIm * c3 CIm)) (- (c1 CIm * (c2 CRe * c3 CIm) + c1 CIm * (c2 CIm * c3 CRe)))).
apply Rplus_eq_compat_l.
rewrite Ropp_plus_distr.
rewrite Ropp_plus_distr.
rewrite (Rplus_comm (- (c1 CIm * c2 CIm) * c3 CRe) (- (c1 CRe * c2 CIm * c3 CIm) + - (c1 CIm * c2 CRe * c3 CIm))).
rewrite - Rplus_assoc.
rewrite - Ropp_mult_distr_l.
rewrite (Rmult_assoc (c1 CIm) (c2 CIm) (c3 CRe)).
apply Rplus_eq_compat_r.
rewrite<- Ropp_mult_distr_r.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
reflexivity.
move=> H1.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite (Rmult_plus_distr_r (c1 CRe * c2 CRe) (- (c1 CIm * c2 CIm)) (c3 CIm)).
rewrite (Rmult_plus_distr_r (c1 CRe * c2 CIm) (c1 CIm * c2 CRe) (c3 CRe)).
rewrite (Rmult_plus_distr_l (c1 CRe) (c2 CRe * c3 CIm) (c2 CIm * c3 CRe)).
rewrite (Rmult_plus_distr_l (c1 CIm) (c2 CRe * c3 CRe) (- (c2 CIm * c3 CIm))).
rewrite (Rmult_assoc (c1 CRe) (c2 CRe) (c3 CIm)).
rewrite (Rplus_assoc (c1 CRe * (c2 CRe * c3 CIm)) (- (c1 CIm * c2 CIm) * c3 CIm) (c1 CRe * c2 CIm * c3 CRe + c1 CIm * c2 CRe * c3 CRe)).
rewrite (Rplus_assoc (c1 CRe * (c2 CRe * c3 CIm)) (c1 CRe * (c2 CIm * c3 CRe)) (c1 CIm * (c2 CRe * c3 CRe) + c1 CIm * - (c2 CIm * c3 CIm))).
apply Rplus_eq_compat_l.
rewrite (Rplus_comm (- (c1 CIm * c2 CIm) * c3 CIm) (c1 CRe * c2 CIm * c3 CRe + c1 CIm * c2 CRe * c3 CRe)).
rewrite (Rplus_assoc (c1 CRe * c2 CIm * c3 CRe) (c1 CIm * c2 CRe * c3 CRe) (- (c1 CIm * c2 CIm) * c3 CIm)).
rewrite (Rmult_assoc (c1 CRe) (c2 CIm) (c3 CRe)).
rewrite Rmult_assoc.
rewrite - Ropp_mult_distr_l.
rewrite - Ropp_mult_distr_r.
rewrite (Rmult_assoc (c1 CIm) (c2 CIm) (c3 CIm)).
reflexivity.
Qed.

Definition Cplus_comm : forall (c1 c2 : C), (Cplus c1 c2) = (Cplus c2 c1) := (Rnplus_comm 2).

Lemma Cmult_comm : forall (c1 c2 : C), (Cmult c1 c2) = (Cmult c2 c1).
Proof.
move=> c1 c2.
apply functional_extensionality.
move=> x.
unfold Cmult.
unfold Cmake.
elim (CReorCIm x).
move=> H1.
rewrite (Rmult_comm (c1 CRe) (c2 CRe)).
rewrite (Rmult_comm (c1 CIm) (c2 CIm)).
reflexivity.
move=> H1.
rewrite (Rmult_comm (c1 CRe) (c2 CIm)).
rewrite (Rmult_comm (c1 CIm) (c2 CRe)).
apply Rplus_comm.
Qed.

Definition CO := RnO 2.

Definition CI := Cmake 1 0.

Definition Cplus_0_l : forall (c : C), Cplus CO c = c := Rnplus_O_l 2.

Lemma Cmult_1_l : forall (c : C), Cmult CI c = c.
Proof.
move=> c.
apply functional_extensionality.
move=> x.
unfold Cmult.
unfold Cmake.
elim (CReorCIm x).
unfold CI.
move=> H1.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite H1.
rewrite (Rmult_0_l (c CIm)).
rewrite (Rmult_1_l (c CRe)).
unfold Rminus.
rewrite Ropp_0.
apply (Rplus_0_r (c CRe)).
unfold CI.
move=> H1.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite H1.
rewrite (Rmult_0_l (c CRe)).
rewrite (Rmult_1_l (c CIm)).
apply (Rplus_0_r (c CIm)).
Qed.

Definition Copp := Rnopp 2.

Definition Cplus_opp_r : forall (c : C), Cplus c (Copp c) = CO := Rnplus_opp_r 2.

Lemma Cinv_l : forall (c : C), c <> CO -> Cmult (Cinv c) c = CI.
Proof.
move=> c H1.
rewrite Cmult_comm.
apply functional_extensionality.
move=> x.
unfold Cmult.
unfold Cinv.
rewrite CmakeRe.
rewrite CmakeIm.
unfold CI.
unfold Cmake.
elim (CReorCIm x).
move=> H2.
rewrite - Rmult_assoc.
rewrite - Rmult_assoc.
unfold Rminus.
rewrite Ropp_mult_distr_l.
rewrite - (Rmult_plus_distr_r (c CRe * c CRe) (- (c CIm * - c CIm)) (/ (c CRe * c CRe + c CIm * c CIm))).
rewrite - Ropp_mult_distr_r.
rewrite Ropp_involutive.
apply (Rinv_r (c CRe * c CRe + c CIm * c CIm)).
move=> H3.
apply H1.
apply functional_extensionality.
move=> y.
elim (CReorCIm y).
move=> H4.
rewrite H4.
apply NNPP.
move=> H5.
apply (Rlt_irrefl (c CRe * c CRe + c CIm * c CIm)).
rewrite {1} H3.
rewrite - (Rplus_0_r 0).
apply (Rplus_lt_le_compat 0 (c CRe * c CRe) 0 (c CIm * c CIm)).
apply (Formula_1_3_3 (c CRe)).
apply H5.
apply Rge_le.
apply (Formula_1_3_2 (c CIm)).
move=> H4.
rewrite H4.
apply NNPP.
move=> H5.
apply (Rlt_irrefl (c CRe * c CRe + c CIm * c CIm)).
rewrite {1} H3.
rewrite - (Rplus_0_r 0).
apply (Rplus_le_lt_compat 0 (c CRe * c CRe) 0 (c CIm * c CIm)).
apply Rge_le.
apply (Formula_1_3_2 (c CRe)).
apply (Formula_1_3_3 (c CIm)).
apply H5.
move=> H2.
rewrite - Rmult_assoc.
rewrite - Rmult_assoc.
rewrite - (Rmult_plus_distr_r (c CRe * - c CIm) (c CIm * c CRe) (/ (c CRe * c CRe + c CIm * c CIm))).
rewrite (Rmult_comm (c CRe) (- c CIm)).
rewrite - (Rmult_plus_distr_r (- c CIm) (c CIm) (c CRe)).
rewrite Rplus_opp_l.
rewrite Rmult_0_l.
apply Rmult_0_l.
Qed.


Lemma Cmult_plus_distr_l : forall (c1 c2 c3 : C), (Cmult c1 (Cplus c2 c3)) = (Cplus (Cmult c1 c2) (Cmult c1 c3)).
Proof.
move=> c1 c2 c3.
apply functional_extensionality.
move=> x.
elim (CReorCIm x).
move=> H1.
rewrite H1.
unfold Cmult.
unfold Cplus.
unfold Rnplus.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rplus_assoc.
unfold Rminus.
rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
rewrite Rplus_comm.
rewrite Ropp_plus_distr.
rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
apply Rplus_comm.
move=> H1.
rewrite H1.
unfold Cmult.
unfold Cplus.
unfold Rnplus.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rplus_assoc.
rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
rewrite Rplus_comm.
rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
apply Rplus_comm.
Qed.

Lemma CRe_neq_CIm : CRe <> CIm.
Proof.
move=> H1.
apply (n_Sn 0).
suff: (proj1_sig CRe = proj1_sig CIm).
apply.
rewrite H1.
reflexivity.
Qed.

Lemma CIm_neq_CRe : CIm <> CRe.
Proof.
move=> H1.
apply CRe_neq_CIm.
rewrite H1.
reflexivity.
Qed.

Lemma CI_neq_CO : CI <> CO.
Proof.
move=> H1.
apply R1_neq_R0.
suff: (1 = CI CRe).
move=> H2.
rewrite H2.
rewrite H1.
reflexivity.
unfold CI.
unfold Cmake.
elim (CReorCIm CRe).
move=> H2.
reflexivity.
move=> H2.
apply False_ind.
apply CRe_neq_CIm.
apply H2.
Qed.

Definition Cfield := mkField C CO CI Cplus Cmult Copp Cinv Cplus_assoc Cmult_assoc Cplus_comm Cmult_comm Cplus_0_l Cmult_1_l Cplus_opp_r Cinv_l Cmult_plus_distr_l CI_neq_CO.

Definition Conjugate (c : C) := Cmake (c CRe) (- c CIm).

Lemma ConjugateRe : forall (c : C), (Conjugate c CRe) = (c CRe).
Proof.
move=> c.
unfold Conjugate.
unfold Cmake.
elim (CReorCIm CRe).
simpl.
move=> H1.
reflexivity.
move=> H1.
apply False_ind.
apply (CRe_neq_CIm H1).
Qed.

Lemma ConjugateIm : forall (c : C), (Conjugate c CIm) = - (c CIm).
Proof.
move=> c.
unfold Conjugate.
unfold Cmake.
elim (CReorCIm CIm).
move=> H1.
apply False_ind.
apply (CIm_neq_CRe H1).
move=> H1.
reflexivity.
Qed.

Definition IRC (r : R) := Cmake r 0.

Definition Cminus := (Rnminus 2).

Lemma Proposition_4_8_1_1 : forall (c1 c2 : C), Conjugate (Cplus c1 c2) = (Cplus (Conjugate c1) (Conjugate c2)).
Proof.
move=> c1 c2.
apply functional_extensionality.
move=> x.
unfold Cplus.
unfold Rnplus.
elim (CReorCIm x).
move=> H1.
rewrite H1.
rewrite ConjugateRe.
rewrite ConjugateRe.
rewrite ConjugateRe.
reflexivity.
move=> H1.
rewrite H1.
rewrite ConjugateIm.
rewrite ConjugateIm.
rewrite ConjugateIm.
apply Ropp_plus_distr.
Qed.

Lemma Proposition_4_8_1_2 : forall (c1 c2 : C), Conjugate (Cminus c1 c2) = (Cminus (Conjugate c1) (Conjugate c2)).
Proof.
move=> c1 c2.
apply functional_extensionality.
move=> x.
unfold Cminus.
unfold Rnminus.
unfold Rnplus.
unfold Rnopp.
elim (CReorCIm x).
move=> H1.
rewrite H1.
rewrite ConjugateRe.
rewrite ConjugateRe.
rewrite ConjugateRe.
reflexivity.
move=> H1.
rewrite H1.
rewrite ConjugateIm.
rewrite ConjugateIm.
rewrite ConjugateIm.
apply Ropp_plus_distr.
Qed.

Lemma Proposition_4_8_2 : forall (c1 c2 : C), Conjugate (Cmult c1 c2) = (Cmult (Conjugate c1) (Conjugate c2)).
Proof.
move=> c1 c2.
apply functional_extensionality.
move=> x.
elim (CReorCIm x).
move=> H1.
rewrite H1.
unfold Cmult.
rewrite CmakeRe.
rewrite ConjugateRe.
rewrite ConjugateRe.
rewrite ConjugateRe.
rewrite CmakeRe.
rewrite ConjugateIm.
rewrite ConjugateIm.
rewrite Rmult_opp_opp.
reflexivity.
move=> H1.
rewrite H1.
unfold Cmult.
rewrite CmakeIm.
rewrite ConjugateIm.
rewrite ConjugateIm.
rewrite ConjugateIm.
rewrite CmakeIm.
rewrite ConjugateRe.
rewrite ConjugateRe.
rewrite Ropp_plus_distr.
rewrite Ropp_mult_distr_r.
rewrite Ropp_mult_distr_l.
reflexivity.
Qed.

Definition Cnorm := RnNorm 2.

Lemma CnormSqrtSub : forall (c : C), (c CRe) * (c CRe) + (c CIm) * (c CIm) >= 0.
Proof.
move=> c.
rewrite - (Rplus_0_r 0).
apply Rplus_ge_compat.
apply Formula_1_3_2.
apply Formula_1_3_2.
Qed.

Lemma CnormDefinition : forall (c : C), Cnorm c = MySqrt (exist (fun (r : R) => r >= 0) ((c CRe) * (c CRe) + (c CIm) * (c CIm)) (CnormSqrtSub c)).
Proof.
move=> c.
unfold Cnorm.
unfold RnNorm.
suff: ((exist (fun r : R => r >= 0) (RnInnerProduct 2 c c) (Proposition_4_2_4_1 2 c)) = (exist (fun r : R => r >= 0) (c CRe * c CRe + c CIm * c CIm) (CnormSqrtSub c))).
move=> H1.
rewrite H1.
reflexivity.
apply sig_map.
simpl.
unfold RnInnerProduct.
simpl.
unfold UnwrapRn.
elim (excluded_middle_informative (lt O (S (S O)))).
move=> H1.
elim (excluded_middle_informative (lt (S O) (S (S O)))).
move=> H2.
suff: ((exist (fun n0 : nat => (n0 < 2)%nat) 0%nat H1) = CRe).
move=> H3.
rewrite H3.
suff: ((exist (fun n0 : nat => (n0 < 2)%nat) 1%nat H2) = CIm).
move=> H4.
rewrite H4.
rewrite (Rplus_0_l (c CRe * c CRe)).
reflexivity.
apply sig_map.
reflexivity.
apply sig_map.
reflexivity.
move=> H2.
apply False_ind.
apply (H2 (proj2_sig CIm)).
move=> H1.
apply False_ind.
apply (H1 (proj2_sig CRe)).
Qed.

Lemma Proposition_4_8_3 : forall (c : C), IRC ((Cnorm c) * (Cnorm c)) = (Cmult c (Conjugate c)).
Proof.
move=> c.
rewrite CnormDefinition.
rewrite<- (proj2 (MySqrtNature (exist (fun r : R => r >= 0)
        (c CRe * c CRe + c CIm * c CIm) 
        (CnormSqrtSub c)))).
simpl.
unfold Cmult.
unfold IRC.
unfold Cmake.
rewrite ConjugateRe.
rewrite ConjugateIm.
apply functional_extensionality.
move=> x.
elim CReorCIm.
move=> H1.
unfold Rminus.
rewrite Ropp_mult_distr_r.
rewrite Ropp_involutive.
reflexivity.
move=> H1.
rewrite (Rmult_comm (c CRe) (- c CIm)).
rewrite - (Rmult_plus_distr_r (- c CIm) (c CIm) (c CRe)).
rewrite Rplus_opp_l.
rewrite Rmult_0_l.
reflexivity.
Qed.

Lemma Proposition_4_8_4 : forall (c1 c2 : C), (Cnorm c1) * (Cnorm c2) = (Cnorm (Cmult c1 c2)).
Proof.
move=> c1 c2.
suff: (Cnorm (Cmult c1 c2) = Cnorm c1 * Cnorm c2).
move=> H1.
rewrite H1.
reflexivity.
rewrite (CnormDefinition (Cmult c1 c2)).
apply MySqrtNature2.
apply conj.
apply Rle_ge.
apply Rmult_le_pos.
apply Rge_le.
apply MySqrtNature.
apply Rge_le.
apply MySqrtNature.
simpl.
rewrite - Rmult_assoc.
rewrite (Rmult_assoc (Cnorm c1) (Cnorm c2) (Cnorm c1)).
rewrite (Rmult_comm (Cnorm c2) (Cnorm c1)).
rewrite - (Rmult_assoc (Cnorm c1) (Cnorm c1) (Cnorm c2)).
rewrite Rmult_assoc.
suff: (Cmult c1 c2 CRe * Cmult c1 c2 CRe + Cmult c1 c2 CIm * Cmult c1 c2 CIm = (proj1_sig (exist (fun r : R => r >= 0) (Cmult c1 c2 CRe * Cmult c1 c2 CRe + Cmult c1 c2 CIm * Cmult c1 c2 CIm) (CnormSqrtSub (Cmult c1 c2))))).
move=> H1.
rewrite H1.
rewrite (proj2 (MySqrtNature (exist (fun r : R => r >= 0) (Cmult c1 c2 CRe * Cmult c1 c2 CRe + Cmult c1 c2 CIm * Cmult c1 c2 CIm) (CnormSqrtSub (Cmult c1 c2))))).
suff: (MySqrt (exist (fun r : R => r >= 0) (Cmult c1 c2 CRe * Cmult c1 c2 CRe + Cmult c1 c2 CIm * Cmult c1 c2 CIm) (CnormSqrtSub (Cmult c1 c2))) * MySqrt (exist (fun r : R => r >= 0) (Cmult c1 c2 CRe * Cmult c1 c2 CRe + Cmult c1 c2 CIm * Cmult c1 c2 CIm) (CnormSqrtSub (Cmult c1 c2))) = (Cnorm (Cmult c1 c2)) * (Cnorm (Cmult c1 c2))).
move=> H2.
rewrite H2.
suff: (IRC (Cnorm (Cmult c1 c2) * Cnorm (Cmult c1 c2)) = Cmult (IRC (Cnorm c1 * Cnorm c1)) (IRC (Cnorm c2 * Cnorm c2))).
move=> H3.
suff: (Cnorm (Cmult c1 c2) * Cnorm (Cmult c1 c2) = (IRC (Cnorm (Cmult c1 c2) * Cnorm (Cmult c1 c2))) CRe).
move=> H4.
rewrite H4.
suff: (Cnorm c1 * Cnorm c1 * (Cnorm c2 * Cnorm c2) = Cmult (IRC (Cnorm c1 * Cnorm c1)) (IRC (Cnorm c2 * Cnorm c2)) CRe).
move=> H5.
rewrite H5.
rewrite H3.
reflexivity.
unfold IRC.
unfold Cmult.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite Rmult_0_r.
unfold Rminus.
rewrite Ropp_0.
rewrite Rplus_0_r.
reflexivity.
unfold IRC.
rewrite CmakeRe.
reflexivity.
rewrite Proposition_4_8_3.
rewrite Proposition_4_8_3.
rewrite Proposition_4_8_3.
rewrite Cmult_assoc.
rewrite Proposition_4_8_2.
rewrite - (Cmult_assoc c2 (Conjugate c1) (Conjugate c2)).
rewrite (Cmult_comm c2 (Conjugate c1)).
rewrite (Cmult_assoc (Conjugate c1) c2 (Conjugate c2)).
rewrite Cmult_assoc.
reflexivity.
rewrite CnormDefinition.
reflexivity.
reflexivity.
Qed.

Lemma Proposition_4_9_mult : forall (an bn  : nat -> C) (a b : C), Un_cv_met (Rn_met 2) an a -> Un_cv_met (Rn_met 2) bn b -> Un_cv_met (Rn_met 2) (fun (n : nat) => Cmult (an n) (bn n)) (Cmult a b).
Proof.
move=> an bn a b H1 H2.
apply Theorem_4_5_1.
move=> n.
elim (CReorCIm n).
move=> H3.
rewrite H3.
unfold Cmult.
unfold Cmake.
elim (CReorCIm CRe).
move=> H4.
apply Theorem_2_5_1_minus.
apply Theorem_2_5_1_mult.
apply Theorem_4_5_1.
apply H1.
apply Theorem_4_5_1.
apply H2.
apply Theorem_2_5_1_mult.
apply Theorem_4_5_1.
apply H1.
apply Theorem_4_5_1.
apply H2.
move=> H4.
apply False_ind.
apply (CRe_neq_CIm H4).
move=> H3.
rewrite H3.
unfold Cmult.
unfold Cmake.
elim (CReorCIm CIm).
move=> H4.
apply False_ind.
apply (CIm_neq_CRe H4).
move=> H4.
apply Theorem_2_5_1_plus.
apply Theorem_2_5_1_mult.
apply Theorem_4_5_1.
apply H1.
apply Theorem_4_5_1.
apply H2.
apply Theorem_2_5_1_mult.
apply Theorem_4_5_1.
apply H1.
apply Theorem_4_5_1.
apply H2.
Qed.

Lemma Proposition_4_9_inv : forall (an  : nat -> C) (a : C), a <> CO -> Un_cv_met (Rn_met 2) an a -> Un_cv_met (Rn_met 2) (fun (n : nat) => Cinv (an n)) (Cinv a).
Proof.
move=> an a H1 H2.
suff: (a CRe * a CRe + a CIm * a CIm <> 0).
move=> H3.
apply Theorem_4_5_1.
move=> n.
elim (CReorCIm n).
move=> H4.
rewrite H4.
unfold Cinv.
rewrite CmakeRe.
suff: ((fun n0 : nat => Cmake (an n0 CRe / (an n0 CRe * an n0 CRe + an n0 CIm * an n0 CIm)) (- an n0 CIm / (an n0 CRe * an n0 CRe + an n0 CIm * an n0 CIm)) CRe) = (fun n0 : nat => (an n0 CRe / (an n0 CRe * an n0 CRe + an n0 CIm * an n0 CIm)))).
move=> H5.
rewrite H5.
apply Theorem_2_5_1_div.
apply Theorem_4_5_1.
apply H2.
apply Theorem_2_5_1_plus.
apply Theorem_2_5_1_mult.
apply Theorem_4_5_1.
apply H2.
apply Theorem_4_5_1.
apply H2.
apply Theorem_2_5_1_mult.
apply Theorem_4_5_1.
apply H2.
apply Theorem_4_5_1.
apply H2.
apply H3.
apply functional_extensionality.
move=> m.
rewrite CmakeRe.
reflexivity.
move=> H4.
rewrite H4.
unfold Cinv.
rewrite CmakeIm.
suff: ((fun n0 : nat => Cmake (an n0 CRe / (an n0 CRe * an n0 CRe + an n0 CIm * an n0 CIm)) (- an n0 CIm / (an n0 CRe * an n0 CRe + an n0 CIm * an n0 CIm)) CIm) = (fun n0 : nat => (- an n0 CIm / (an n0 CRe * an n0 CRe + an n0 CIm * an n0 CIm)))).
move=> H5.
rewrite H5.
apply Theorem_2_5_1_div.
apply Theorem_2_5_1_opp.
apply Theorem_4_5_1.
apply H2.
apply Theorem_2_5_1_plus.
apply Theorem_2_5_1_mult.
apply Theorem_4_5_1.
apply H2.
apply Theorem_4_5_1.
apply H2.
apply Theorem_2_5_1_mult.
apply Theorem_4_5_1.
apply H2.
apply Theorem_4_5_1.
apply H2.
apply H3.
apply functional_extensionality.
move=> m.
rewrite CmakeIm.
reflexivity.
move=> H3.
apply H1.
apply functional_extensionality.
move=> x.
elim (CReorCIm x).
move=> H4.
rewrite H4.
apply NNPP.
move=> H5.
apply (Rlt_irrefl (a CRe * a CRe + a CIm * a CIm)).
rewrite {1} H3.
rewrite - (Rplus_0_r 0).
apply (Rplus_lt_le_compat 0 (a CRe * a CRe) 0 (a CIm * a CIm)).
apply (Formula_1_3_3 (a CRe)).
apply H5.
apply Rge_le.
apply (Formula_1_3_2 (a CIm)).
move=> H4.
rewrite H4.
apply NNPP.
move=> H5.
apply (Rlt_irrefl (a CRe * a CRe + a CIm * a CIm)).
rewrite {1} H3.
rewrite - (Rplus_0_r 0).
apply (Rplus_le_lt_compat 0 (a CRe * a CRe) 0 (a CIm * a CIm)).
apply Rge_le.
apply (Formula_1_3_2 (a CRe)).
apply (Formula_1_3_3 (a CIm)).
apply H5.
Qed.

Lemma Proposition_4_9_div : forall (an bn  : nat -> C) (a b : C), b <> CO -> Un_cv_met (Rn_met 2) an a -> Un_cv_met (Rn_met 2) bn b -> Un_cv_met (Rn_met 2) (fun (n : nat) => Cmult (an n) (Cinv (bn n))) (Cmult a (Cinv b)).
Proof.
move=> an bn a b H1 H2 H3.
suff: (Un_cv_met (Rn_met 2) (fun n : nat => Cinv (bn n)) (Cinv b)).
move=> H4.
apply Proposition_4_9_mult.
apply H2.
apply H4.
apply Proposition_4_9_inv.
apply H1.
apply H3.
Qed.

Lemma R1NormEqDist : forall (r : R), RnNorm 1%nat (fun (n : Count 1) => r) = Rabs r.
Proof.
move=> r.
apply RnNormNature2.
apply conj.
apply Rle_ge.
apply Rabs_pos.
unfold RnInnerProduct.
simpl.
unfold UnwrapRn.
elim (excluded_middle_informative (0 < 1)%nat).
move=> H1.
rewrite (Rplus_0_l (r * r)).
unfold Rabs.
elim (Rcase_abs r).
move=> H2.
rewrite Rmult_opp_opp.
reflexivity.
reflexivity.
move=> H1.
apply False_ind.
apply H1.
apply (le_n 1).
Qed.

Lemma natSectionFinite : forall (a b : nat), Finite nat (fun (n : nat) => (a <= n)%nat /\ (n <= b)%nat).
Proof.
move=> a b.
suff: ((fun n : nat => (a <= n <= b)%nat) = Intersection nat (fun n : nat => (a <= n)%nat) (fun n : nat => (n <= b)%nat)).
move=> H1.
rewrite H1.
apply Intersection_preserves_finite.
elim b.
suff: ((fun n : nat => (n <= 0)%nat) = Add nat (Empty_set nat) O).
move=> H2.
rewrite H2.
apply Union_is_finite.
apply Empty_is_finite.
elim.
apply Extensionality_Ensembles.
apply conj.
move=> n H2.
right.
rewrite (le_n_0_eq n).
reflexivity.
apply H2.
move=> n H2.
elim H2.
move=> m.
elim.
move=> m H3.
rewrite H3.
apply (le_n m).
move=> n H2.
suff: ((fun n0 : nat => (n0 <= S n)%nat) = Add nat (fun n0 : nat => (n0 <= n)%nat) (S n)).
move=> H3.
rewrite H3.
apply Union_is_finite.
apply H2.
apply Nat.nle_succ_diag_l.
apply Extensionality_Ensembles.
apply conj.
move=> m H3.
elim (le_lt_or_eq m (S n)).
move=> H4.
left.
apply (le_S_n m n H4).
move=> H4.
rewrite H4.
right.
reflexivity.
apply H3.
move=> m.
elim.
move=> k.
apply le_S.
move=> k H3.
rewrite H3.
apply le_n.
apply Extensionality_Ensembles.
apply conj.
move=> n H1.
apply Intersection_intro.
apply H1.
apply H1.
move=> n.
elim.
move=> m H1 H2.
apply conj.
apply H1.
apply H2.
Qed.

Lemma MySumEqsum_f_R0 : forall (f : nat -> R) (N : nat), sum_f_R0 f N = MySumF2 nat (exist (Finite nat) (fun (m : nat) => (O <= m <= N)%nat) (natSectionFinite O N)) RPCM f.
Proof.
move=> f N.
suff: forall (n : (Count (S N))), proj1_sig (exist (Finite nat) (fun m : nat => (0 <= m <= N)%nat) (natSectionFinite 0 N)) ((fun (m : Count (S N)) => proj1_sig m) n).
move=> H1.
rewrite<- (MySumF2Nature2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= N)%nat) (natSectionFinite 0 N)) RPCM f (S N) (fun (n : Count (S N)) => proj1_sig n) H1).
unfold SumGF.
suff: (forall (n : nat), (n <= N)%nat -> sum_f_R0 f n = SumGFSub nat RPCM (S N) (fun n : Count (S N) => proj1_sig n) (fun n : nat => f n) (S n)).
move=> H2.
apply H2.
apply le_n.
elim.
move=> H2.
simpl.
unfold UnwrapGF.
elim (excluded_middle_informative (0 < S N)%nat).
move=> H3.
simpl.
rewrite Rplus_0_l.
reflexivity.
move=> H3.
apply False_ind.
apply H3.
apply (Nat.lt_0_succ N).
move=> n H2 H3.
simpl.
rewrite H2.
simpl.
apply Rplus_eq_compat_l.
unfold UnwrapGF.
elim (excluded_middle_informative (S n < S N)%nat).
move=> H4.
reflexivity.
move=> H4.
apply False_ind.
apply H4.
apply (le_n_S (S n) N H3).
apply le_S_n.
apply le_S.
apply H3.
simpl.
suff: (forall (n : {u : nat | (0 <= u <= N)%nat}), ((proj1_sig n) < (S N))%nat).
move=> H2.
exists (fun (n : {u : nat | (0 <= u <= N)%nat}) => exist (fun (m : nat) => (m < S N)%nat) (proj1_sig n) (H2 n)).
apply conj.
move=> n.
simpl.
apply sig_map.
reflexivity.
move=> n.
apply sig_map.
reflexivity.
move=> n.
apply le_n_S.
apply (proj2_sig n).
move=> n.
simpl.
apply conj.
apply Nat.le_0_l.
apply le_S_n.
apply (proj2_sig n).
Qed.

Lemma MySumEqsigma : forall (f : nat -> R) (a b : nat), (a <= b)%nat -> sigma f a b = MySumF2 nat (exist (Finite nat) (fun (m : nat) => (a <= m <= b)%nat) (natSectionFinite a b)) RPCM f.
Proof.
move=> f a b H1.
unfold sigma.
rewrite MySumEqsum_f_R0.
suff: forall (n : nat), proj1_sig (exist (Finite nat) (fun m : nat => (0 <= m <= b - a)%nat) (natSectionFinite 0 (b - a))) n -> proj1_sig (exist (Finite nat) (fun m : nat => (a <= m <= b)%nat) (natSectionFinite a b)) ((fun (m : nat) => (a + m)%nat) n).
move=> H2.
apply (MySumF2BijectiveSame nat (exist (Finite nat) (fun (m : nat) => (0 <= m <= b - a)%nat) (natSectionFinite 0 (b - a))) nat (exist (Finite nat) (fun (m : nat) => (a <= m <= b)%nat) (natSectionFinite a b)) RPCM (fun m : nat => f m) (fun m : nat => (a + m)%nat) H2).
simpl.
suff: (forall (n : {u : nat | (a <= u <= b)%nat}), (0 <= (proj1_sig n - a) <= b - a)%nat).
move=> H3.
exists (fun (n : {u : nat | (a <= u <= b)%nat}) => (exist (fun (u : nat) => (0 <= u <= b - a)%nat) (proj1_sig n - a)%nat (H3 n))).
apply conj.
move=> n.
apply sig_map.
simpl.
apply minus_plus.
move=> n.
apply sig_map.
simpl.
apply le_plus_minus_r.
apply (proj2_sig n).
move=> n.
apply conj.
rewrite (minus_diag_reverse a).
apply minus_le_compat_r.
apply (proj2_sig n).
apply minus_le_compat_r.
apply (proj2_sig n).
move=> n.
simpl.
move=> H2.
apply conj.
rewrite - {1} (plus_0_r a).
apply plus_le_compat_l.
apply H2.
rewrite - (le_plus_minus_r a b).
apply plus_le_compat_l.
apply H2.
apply H1.
Qed.

Fixpoint sum_f_Rn (N : nat) (f : nat -> Rn N) (n : nat) : Rn N := 
match n with 
| O => f 0%nat
| S n0 => Rnplus N (sum_f_Rn N f n0) (f (S n0))
end.

Definition sigma_Rn (N : nat) (f : nat -> Rn N) (a b : nat) : Rn N := sum_f_Rn N (fun (k : nat) => f (a + k)%nat) (b - a).

Lemma sum_f_Rn_component : forall (N : nat) (f : nat -> Rn N), (sum_f_Rn N f) = (fun (n : nat) (m : Count N) => (sum_f_R0 (fun (l : nat) => (f l m))) n).
Proof.
move=> N f.
apply functional_extensionality.
elim.
simpl.
apply functional_extensionality.
move=> n.
reflexivity.
move=> m H1.
simpl.
apply functional_extensionality.
move=> n.
unfold Rnplus.
rewrite H1.
reflexivity.
Qed.

Lemma sigma_Rn_component : forall (N : nat) (f : nat -> Rn N), (sigma_Rn N f) = (fun (a b : nat) (m : Count N) => (sigma (fun (l : nat) => (f l m)) a b)).
Proof.
move=> N f.
apply functional_extensionality.
move=> a.
apply functional_extensionality.
move=> b.
unfold sigma_Rn.
unfold sigma.
rewrite sum_f_Rn_component.
reflexivity.
Qed.

Definition RnPCM (N : nat) : CommutativeMonoid := mkCommutativeMonoid (Rn N) (RnO N) (Rnplus N) (Rnplus_comm N) (Vadd_O_r Rfield (RnVS N)) (Rnplus_assoc N).

Lemma MySumF2RPNCM_component : forall (N : nat) (U : Type) (A : {X : Ensemble U | Finite U X}) (f : U -> Rn N), MySumF2 U A (RnPCM N) f = (fun (m : Count N) => MySumF2 U A RPCM (fun (n : U) => f n m)).
Proof.
move=> N U A f.
apply (FiniteSetInduction U A).
apply conj.
apply functional_extensionality.
move=> n.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
reflexivity.
move=> B b H1 H2 H3 H4.
rewrite MySumF2Add.
apply functional_extensionality.
move=> n.
rewrite MySumF2Add.
rewrite H4.
reflexivity.
apply H3.
apply H3.
Qed.

Lemma MySumEqsum_f_Rn : forall (N : nat) (f : nat -> (Rn N)) (n : nat), sum_f_Rn N f n = MySumF2 nat (exist (Finite nat) (fun (m : nat) => (O <= m <= n)%nat) (natSectionFinite O n)) (RnPCM N) f.
Proof.
move=> N f n.
apply functional_extensionality.
move=> m.
rewrite sum_f_Rn_component.
rewrite MySumF2RPNCM_component.
apply MySumEqsum_f_R0.
Qed.

Lemma MySumEqsigma_Rn : forall (N : nat) (f : nat -> Rn N) (a b : nat), (a <= b)%nat -> sigma_Rn N f a b = MySumF2 nat (exist (Finite nat) (fun (m : nat) => (a <= m <= b)%nat) (natSectionFinite a b)) (RnPCM N) f.
Proof.
move=> N f a b H1.
apply functional_extensionality.
move=> m.
rewrite sigma_Rn_component.
rewrite MySumF2RPNCM_component.
apply MySumEqsigma.
apply H1.
Qed.

Lemma Un_cv_1_Un_cv_same : forall (an : nat -> R) (a : R), Un_cv an a <-> Un_cv_met (Rn_met 1) (fun (n : nat) (m : Count 1) => an n) (fun (m : Count 1) => a).
Proof.
move=> an a.
apply conj.
move=> H1.
move=> eps H2.
elim (H1 eps H2).
move=> N H3.
exists N.
move=> n H4.
unfold Rn_met.
unfold dist.
unfold Rn_dist.
unfold Rnminus.
unfold Rnplus.
unfold Rnopp.
rewrite R1NormEqDist.
apply H3.
apply H4.
move=> H1.
move=> eps H2.
unfold R_dist.
elim (H1 eps H2).
move=> N H3.
exists N.
move=> n H4.
rewrite - R1NormEqDist.
apply H3.
apply H4.
Qed.

Lemma Theorem_5_1 : forall (N : nat) (an : nat -> Rn N), (exists (a : Rn N), Un_cv_met (Rn_met N) (sum_f_Rn N an) a) <-> (forall (eps : R), eps > 0 -> exists (M : nat),forall (n m : nat), (n > m)%nat -> (m >= M)%nat -> RnNorm N (sigma_Rn N an (S m) n) < eps).
Proof.
suff: (forall (N : nat) (an : nat -> Rn N) (n m : nat), (n > m)%nat -> sigma_Rn N an (S m) n = Rnminus N (sum_f_Rn N an n) (sum_f_Rn N an m)).
move=> H1 N an.
apply conj.
move=> H2 eps H3.
elim (proj1 (Theorem_4_5_3 N (sum_f_Rn N an)) H2 eps H3).
move=> M H4.
exists M.
move=> n m H5 H6.
rewrite H1.
apply H4.
apply (le_trans M m n).
apply H6.
apply (lt_le_weak m n H5).
apply H6.
apply H5.
move=> H2.
apply (proj2 (Theorem_4_5_3 N (sum_f_Rn N an))).
move=> eps H3.
elim (H2 eps H3).
move=> M H4.
exists M.
move=> n m H5 H6.
elim (le_or_lt n m).
move=> H7.
elim (le_lt_or_eq n m).
move=> H8.
rewrite dist_sym.
unfold dist.
unfold Rn_met.
unfold Rn_dist.
rewrite - H1.
apply H4.
apply H8.
apply H5.
apply H8.
move=> H8.
rewrite H8.
rewrite (proj2 (dist_refl (Rn_met N) (sum_f_Rn N an m) (sum_f_Rn N an m))).
apply H3.
reflexivity.
apply H7.
move=> H8.
unfold dist.
unfold Rn_met.
unfold Rn_dist.
rewrite - H1.
apply H4.
apply H8.
apply H6.
apply H8.
move=> N an n m H1.
rewrite MySumEqsigma_Rn.
rewrite MySumEqsum_f_Rn.
rewrite MySumEqsum_f_Rn.
rewrite (MySumF2Excluded nat (RnPCM N) an (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= n)%nat) (natSectionFinite 0 n)) (fun m0 : nat => (S m <= m0 <= n)%nat)).
suff: ((FiniteIntersection nat (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= n)%nat) (natSectionFinite 0 n)) (fun m0 : nat => (S m <= m0 <= n)%nat)) = (exist (Finite nat) (fun m0 : nat => (S m <= m0 <= n)%nat) (natSectionFinite (S m) n))).
move=> H6.
rewrite - H6.
suff: ((FiniteIntersection nat (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= n)%nat) (natSectionFinite 0 n)) (Ensembles.Complement nat (fun m0 : nat => (S m <= m0 <= n)%nat))) = (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= m)%nat) (natSectionFinite 0 m))).
move=> H7.
rewrite H7.
simpl.
unfold Rnminus.
rewrite Rnplus_assoc.
rewrite Rnplus_opp_r.
rewrite Rnplus_comm.
rewrite Rnplus_O_l.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> k H7.
elim H7.
move=> l H8 H9.
apply conj.
apply H9.
elim (le_or_lt l m).
apply.
move=> H10.
apply False_ind.
apply H8.
apply conj.
apply H10.
apply H9.
move=> k H7.
apply Intersection_intro.
move=> H8.
apply (le_not_lt k m).
apply H7.
apply H8.
apply conj.
apply H7.
apply (le_trans k m n).
apply H7.
apply (lt_le_weak m n H1).
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> k H2.
elim H2.
move=> l H3 H4.
apply H3.
move=> k H2.
apply Intersection_intro.
apply H2.
apply conj.
apply le_0_n.
apply H2.
apply H1.
Qed.

Lemma Theorem_5_1_R : forall (an : nat -> R), (exists (a : R), Un_cv (sum_f_R0 an) a) <-> (forall (eps : R), eps > 0 -> exists (M : nat),forall (n m : nat), (n > m)%nat -> (m >= M)%nat -> Rabs (sigma an (S m) n) < eps).
Proof.
suff: (forall (an : nat -> R) (n m : nat), (n > m)%nat -> sigma an (S m) n = (sum_f_R0 an n) - (sum_f_R0 an m)).
move=> H1 an.
apply conj.
move=> H2 eps H3.
elim (proj1 (Theorem_3_6 (sum_f_R0 an)) H2 eps H3).
move=> M H4.
exists M.
move=> n m H5 H6.
rewrite H1.
apply H4.
apply (le_trans M m n).
apply H6.
apply (lt_le_weak m n H5).
apply H6.
apply H5.
move=> H2.
apply (proj2 (Theorem_3_6 (sum_f_R0 an))).
move=> eps H3.
elim (H2 eps H3).
move=> M H4.
exists M.
move=> n m H5 H6.
elim (le_or_lt n m).
move=> H7.
elim (le_lt_or_eq n m).
move=> H8.
rewrite R_dist_sym.
unfold R_dist.
rewrite - H1.
apply H4.
apply H8.
apply H5.
apply H8.
move=> H8.
rewrite H8.
rewrite (proj2 (R_dist_refl (sum_f_R0 an m) (sum_f_R0 an m))).
apply H3.
reflexivity.
apply H7.
move=> H8.
unfold R_dist.
rewrite - H1.
apply H4.
apply H8.
apply H6.
apply H8.
move=>an n m H1.
rewrite MySumEqsigma.
rewrite MySumEqsum_f_R0.
rewrite MySumEqsum_f_R0.
rewrite (MySumF2Excluded nat RPCM an (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= n)%nat) (natSectionFinite 0 n)) (fun m0 : nat => (S m <= m0 <= n)%nat)).
suff: ((exist (Finite nat) (fun m0 : nat => (S m <= m0 <= n)%nat) (natSectionFinite (S m) n)) = (FiniteIntersection nat (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= n)%nat) (natSectionFinite 0 n)) (fun m0 : nat => (S m <= m0 <= n)%nat))).
move=> H6.
rewrite - H6.
suff: ((FiniteIntersection nat (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= n)%nat) (natSectionFinite 0 n)) (Ensembles.Complement nat (fun m0 : nat => (S m <= m0 <= n)%nat))) = (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= m)%nat) (natSectionFinite 0 m))).
move=> H7.
rewrite H7.
simpl.
simpl.
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> k H7.
elim H7.
move=> l H8 H9.
apply conj.
apply H9.
elim (le_or_lt l m).
apply.
move=> H10.
apply False_ind.
apply H8.
apply conj.
apply H10.
apply H9.
move=> k H7.
apply Intersection_intro.
move=> H8.
apply (le_not_lt k m).
apply H7.
apply H8.
apply conj.
apply H7.
apply (le_trans k m n).
apply H7.
apply (lt_le_weak m n H1).
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> k H2.
apply Intersection_intro.
apply H2.
apply conj.
apply le_O_n.
apply H2.
move=> k H2.
elim H2.
move=> l H3 H4.
apply H3.
apply H1.
Qed.

Lemma Theorem_5_1_corollary : forall (N : nat) (an : nat -> Rn N), (exists (a : Rn N), Un_cv_met (Rn_met N) (sum_f_Rn N an) a) -> Un_cv_met (Rn_met N) an (RnO N).
Proof.
move=> N an H1.
move=> eps H2.
elim (proj1 (Theorem_5_1 N an) H1 eps H2).
move=> M H3.
exists (S M).
move=> n H4.
unfold dist.
unfold Rn_met.
unfold Rn_dist.
suff: (Rnminus N (an n) (RnO N) = Vadd Rfield (RnVS N) (an n) (Vopp Rfield (RnVS N) (VO Rfield (RnVS N)))).
move=> H5.
rewrite H5.
rewrite (Vminus_O_r Rfield (RnVS N) (an n)).
move: H4.
elim n.
move=> H6.
apply False_ind.
apply (le_not_lt (S M) O).
apply H6.
apply (le_n_S O M).
apply (le_O_n M).
move=> n0 H6 H7.
suff: (RnNorm N (an (S n0)) = RnNorm N (sigma_Rn N an (S n0) (S n0))).
move=> H8.
rewrite H8.
apply (H3 (S n0) n0).
apply le_n.
apply (le_S_n M n0 H7).
unfold sigma_Rn.
rewrite minus_diag.
simpl.
rewrite plus_0_r.
reflexivity.
simpl.
reflexivity.
Qed.

Lemma Theorem_5_1_corollary_R : forall (an : nat -> R), (exists (a : R), Un_cv (sum_f_R0 an) a) -> Un_cv an 0.
Proof.
move=> an H1.
move=> eps H2.
elim (proj1 (Theorem_5_1_R an) H1 eps H2).
move=> M H3.
exists (S M).
move=> n H4.
unfold R_dist.
rewrite (Rminus_0_r (an n)).
move: H4.
elim n.
move=> H6.
apply False_ind.
apply (le_not_lt (S M) O).
apply H6.
apply (le_n_S O M).
apply (le_O_n M).
move=> n0 H6 H7.
suff: (Rabs (an (S n0)) = Rabs (sigma an (S n0) (S n0))).
move=> H8.
rewrite H8.
apply (H3 (S n0) n0).
apply le_n.
apply (le_S_n M n0 H7).
unfold sigma.
rewrite minus_diag.
simpl.
rewrite plus_0_r.
reflexivity.
Qed.

Lemma MySumF2Rtriangle : forall (U : Type) (A : {X : Ensemble U | Finite U X}) (an : U -> R), Rabs (MySumF2 U A RPCM an) <= MySumF2 U A RPCM (fun (m : U) => Rabs (an m)).
Proof.
move=> U A.
apply (FiniteSetInduction U A).
apply conj.
move=> an.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite Rabs_R0.
apply Req_le.
reflexivity.
move=> B b H1 H2 H3 H4 an.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
apply (Rle_trans (Rabs (MySumF2 U B RPCM an + an b)) (Rabs (MySumF2 U B RPCM an) + Rabs (an b)) (MySumF2 U B RPCM (fun m : U => Rabs (an m)) + Rabs (an b))).
apply Rabs_triang.
apply Rplus_le_compat_r.
apply (H4 an).
apply H3.
apply H3.
Qed.

Lemma sum_f_R0_triangle : forall (an : nat -> R) (n : nat), Rabs (sum_f_R0 an n) <= sum_f_R0 (fun (m : nat) => Rabs (an m)) n.
Proof.
move=> an.
elim.
simpl.
apply Req_le.
reflexivity.
move=> n H1.
simpl.
apply (Rle_trans (Rabs (sum_f_R0 an n + an (S n))) (Rabs (sum_f_R0 an n) + Rabs (an (S n))) (sum_f_R0 (fun m : nat => Rabs (an m)) n + Rabs (an (S n)))).
apply Rabs_triang.
apply Rplus_le_compat_r.
apply H1.
Qed.

Lemma sigma_triangle : forall (an : nat -> R) (n m : nat), Rabs (sigma an n m) <= sigma (fun (k : nat) => Rabs (an k)) n m.
Proof.
move=> an n m.
apply sum_f_R0_triangle.
Qed.

Lemma MySumF2Rntriangle : forall (N : nat) (U : Type) (A : {X : Ensemble U | Finite U X}) (an : U -> Rn N), RnNorm N (MySumF2 U A (RnPCM N) an) <= MySumF2 U A RPCM (fun (m : U) => RnNorm N (an m)).
Proof.
move=> N U A.
apply (FiniteSetInduction U A).
apply conj.
move=> an.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
simpl.
rewrite Proposition_4_4_3_3.
apply Req_le.
reflexivity.
reflexivity.
move=> B b H1 H2 H3 H4 an.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
apply (Rle_trans (RnNorm N (Rnplus N (MySumF2 U B (RnPCM N) an) (an b))) (RnNorm N (MySumF2 U B (RnPCM N) an) + RnNorm N (an b)) (MySumF2 U B RPCM (fun m : U => RnNorm N (an m)) + RnNorm N (an b))).
apply Proposition_4_4_2_1.
apply Rplus_le_compat_r.
apply (H4 an).
apply H3.
apply H3.
Qed.

Lemma sum_f_Rn_triangle : forall (N : nat) (an : nat -> Rn N) (n : nat), RnNorm N (sum_f_Rn N an n) <= sum_f_R0 (fun (m : nat) => RnNorm N (an m)) n.
Proof.
move=> N an.
elim.
simpl.
apply Req_le.
reflexivity.
move=> n H1.
simpl.
apply (Rle_trans (RnNorm N (Rnplus N (sum_f_Rn N an n) (an (S n)))) (RnNorm N (sum_f_Rn N an n) + RnNorm N (an (S n))) (sum_f_R0 (fun m : nat => RnNorm N (an m)) n + RnNorm N (an (S n)))).
apply Proposition_4_4_2_1.
apply Rplus_le_compat_r.
apply H1.
Qed.

Lemma sigma_Rn_triangle : forall (N : nat) (an : nat -> Rn N) (n m : nat), RnNorm N (sigma_Rn N an n m) <= sigma (fun (k : nat) => RnNorm N (an k)) n m.
Proof.
move=> N an n m.
apply sum_f_Rn_triangle.
Qed.

Lemma Theorem_5_2 : forall (N : nat) (an : nat -> Rn N), (exists (s : R), (Un_cv (sum_f_R0 (fun (m : nat) => RnNorm N (an m))) s)) -> (exists (s : Rn N), Un_cv_met (Rn_met N) (sum_f_Rn N an) s).
Proof.
move=> N an H1.
apply Theorem_5_1.
move=> eps H2.
elim (proj1 (Theorem_5_1_R (fun m : nat => RnNorm N (an m))) H1 eps H2).
move=> M H3.
exists M.
move=> n m H4 H5.
apply (Rle_lt_trans (RnNorm N (sigma_Rn N an (S m) n)) (sigma (fun k : nat => RnNorm N (an k)) (S m) n) eps).
apply sigma_Rn_triangle.
apply (Rle_lt_trans (sigma (fun k : nat => RnNorm N (an k)) (S m) n) (Rabs (sigma (fun k : nat => RnNorm N (an k)) (S m) n)) eps).
apply Rle_abs.
apply H3.
apply H4.
apply H5.
Qed.

Lemma Theorem_5_2_R : forall (an : nat -> R), (exists (s : R), (Un_cv (sum_f_R0 (fun (m : nat) => Rabs (an m))) s)) -> (exists (s : R), Un_cv (sum_f_R0 an) s).
Proof.
move=> an H1.
apply Theorem_5_1_R.
move=> eps H2.
elim (proj1 (Theorem_5_1_R (fun m : nat => Rabs (an m))) H1 eps H2).
move=> M H3.
exists M.
move=> n m H4 H5.
apply (Rle_lt_trans (Rabs (sigma an (S m) n)) (sigma (fun m0 : nat => Rabs (an m0)) (S m) n) eps).
apply sigma_triangle.
apply (Rle_lt_trans (sigma (fun m0 : nat => Rabs (an m0)) (S m) n) (Rabs (sigma (fun m0 : nat => Rabs (an m0)) (S m) n)) eps).
apply Rle_abs.
apply H3.
apply H4.
apply H5.
Qed.

Lemma MySumF2Rn_plus : forall (N : nat) (U : Type) (A : {X : Ensemble U | Finite U X}) (an bn : U -> Rn N), MySumF2 U A (RnPCM N) (fun (n : U) => Rnplus N (an n) (bn n)) = Rnplus N (MySumF2 U A (RnPCM N) an) (MySumF2 U A (RnPCM N) bn).
Proof.
move=> N U A an bn.
apply (FiniteSetInduction U A).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (Rnplus_O_l N (RnO N)).
reflexivity.
move=> B b H1 H2 H3 H4.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H4.
rewrite Rnplus_assoc.
rewrite - (Rnplus_assoc N (MySumF2 U B (RnPCM N) bn) (an b) (bn b)).
rewrite (Rnplus_comm N (MySumF2 U B (RnPCM N) bn) (an b)).
rewrite (Rnplus_assoc N (an b) (MySumF2 U B (RnPCM N) bn) (bn b)).
rewrite Rnplus_assoc.
reflexivity.
apply H3.
apply H3.
apply H3.
Qed.

Lemma sum_f_Rn_plus : forall (N : nat) (an bn : nat -> Rn N) (n : nat), sum_f_Rn N (fun (m : nat) => Rnplus N (an m) (bn m)) n = Rnplus N (sum_f_Rn N an n) (sum_f_Rn N bn n).
Proof.
move=> N an bn n.
rewrite MySumEqsum_f_Rn.
rewrite MySumEqsum_f_Rn.
rewrite MySumEqsum_f_Rn.
apply MySumF2Rn_plus.
Qed.

Lemma Sigma_Rn_plus : forall (N : nat) (an bn : nat -> Rn N) (n m : nat), sigma_Rn N (fun (k : nat) => Rnplus N (an k) (bn k)) n m = Rnplus N (sigma_Rn N an n m) (sigma_Rn N bn n m).
Proof.
move=> N an bn a b.
unfold sigma_Rn.
apply sum_f_Rn_plus.
Qed.

Lemma MySumF2R_plus : forall (U : Type) (A : {X : Ensemble U | Finite U X}) (an bn : U -> R), MySumF2 U A RPCM (fun (n : U) => (an n) + (bn n)) = (MySumF2 U A RPCM an) + (MySumF2 U A RPCM bn).
Proof.
move=> U A an bn.
apply (FiniteSetInduction U A).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (Rplus_0_l 0).
reflexivity.
move=> B b H1 H2 H3 H4.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H4.
rewrite Rplus_assoc.
rewrite - (Rplus_assoc (MySumF2 U B RPCM bn) (an b) (bn b)).
rewrite (Rplus_comm (MySumF2 U B RPCM bn) (an b)).
rewrite (Rplus_assoc (an b) (MySumF2 U B RPCM bn) (bn b)).
rewrite Rplus_assoc.
reflexivity.
apply H3.
apply H3.
apply H3.
Qed.

Lemma sum_f_R0_plus : forall (an bn : nat -> R) (n : nat), sum_f_R0 (fun (m : nat) => (an m) + (bn m)) n = (sum_f_R0 an n) + (sum_f_R0 bn n).
Proof.
move=> an bn n.
rewrite MySumEqsum_f_R0.
rewrite MySumEqsum_f_R0.
rewrite MySumEqsum_f_R0.
apply MySumF2R_plus.
Qed.

Lemma Sigma_R0_plus : forall (an bn : nat -> R) (n m : nat), sigma (fun (k : nat) => (an k) + (bn k)) n m = (sigma an n m) + (sigma bn n m).
Proof.
move=> an bn a b.
unfold sigma.
apply sum_f_R0_plus.
Qed.

Lemma MySumF2Rn_mult : forall (N : nat) (U : Type) (A : {X : Ensemble U | Finite U X}) (c : R) (an : U -> Rn N), MySumF2 U A (RnPCM N) (fun (n : U) => Rnmult N c (an n)) = Rnmult N c (MySumF2 U A (RnPCM N) an).
Proof.
move=> N U A c an.
apply (FiniteSetInduction U A).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
suff: (Rnmult N c (CMe (RnPCM N)) = (Vmul Rfield (RnVS N) c (VO Rfield (RnVS N)))).
move=> H1.
rewrite H1.
rewrite (Vmul_O_r Rfield (RnVS N) c).
reflexivity.
reflexivity.
move=> B b H1 H2 H3 H4.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H4.
rewrite Rnmult_plus_distr_l.
reflexivity.
apply H3.
apply H3.
Qed.

Lemma sum_f_Rn_mult : forall (N : nat) (c : R) (an : nat -> Rn N) (n : nat), sum_f_Rn N (fun (m : nat) => Rnmult N c (an m)) n = Rnmult N c (sum_f_Rn N an n).
Proof.
move=> N an bn n.
rewrite MySumEqsum_f_Rn.
rewrite MySumEqsum_f_Rn.
apply MySumF2Rn_mult.
Qed.

Lemma Sigma_Rn_mult : forall (N : nat) (c : R) (an : nat -> Rn N) (n m : nat), sigma_Rn N (fun (k : nat) => Rnmult N c (an k)) n m = Rnmult N c (sigma_Rn N an n m).
Proof.
move=> N an bn a b.
unfold sigma_Rn.
apply sum_f_Rn_mult.
Qed.

Lemma MySumF2R_mult : forall (U : Type) (A : {X : Ensemble U | Finite U X}) (c : R) (an : U -> R), MySumF2 U A RPCM (fun (n : U) => c * (an n)) = c * (MySumF2 U A RPCM an).
Proof.
move=> U A c an.
apply (FiniteSetInduction U A).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (Rmult_0_r c).
reflexivity.
move=> B b H1 H2 H3 H4.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
rewrite H4.
rewrite Rmult_plus_distr_l.
reflexivity.
apply H3.
apply H3.
Qed.

Lemma sum_f_R0_mult : forall (c : R) (an : nat -> R) (n : nat), sum_f_R0 (fun (m : nat) => c * (an m)) n = c * (sum_f_R0 an n).
Proof.
move=> c an n.
rewrite MySumEqsum_f_R0.
rewrite MySumEqsum_f_R0.
apply MySumF2R_mult.
Qed.

Lemma Sigma_R0_mult : forall (c : R) (an : nat -> R) (n m : nat), sigma (fun (k : nat) => c * (an k)) n m = c * (sigma an n m).
Proof.
move=> c an n m.
unfold sigma.
apply sum_f_R0_mult.
Qed.

Lemma Proposition_5_3_1_1 : forall (N : nat) (an bn : nat -> Rn N) (s t : Rn N), (Un_cv_met (Rn_met N) (sum_f_Rn N an) s) -> (Un_cv_met (Rn_met N) (sum_f_Rn N bn) t) -> (Un_cv_met (Rn_met N) (sum_f_Rn N (fun (n : nat) => Rnplus N (an n) (bn n))) (Rnplus N s t)).
Proof.
move=> N an bn s t H1 H2.
suff: (Un_cv_met (Rn_met N) (fun (m : nat) => Rnplus N (sum_f_Rn N an m) (sum_f_Rn N bn m)) (Rnplus N s t)).
move=> H3.
move=> eps H4.
elim (H3 eps H4).
move=> M H5.
exists M.
move=> n H6.
rewrite (sum_f_Rn_plus N an bn).
apply (H5 n H6).
apply Proposition_4_6_1.
apply H1.
apply H2.
Qed.

Lemma Proposition_5_3_1_1_R : forall (an bn : nat -> R) (s t : R), (Un_cv (sum_f_R0 an) s) -> (Un_cv (sum_f_R0 bn) t) -> (Un_cv (sum_f_R0 (fun (n : nat) => (an n) + (bn n))) (s + t)).
Proof.
move=> an bn s t H1 H2.
suff: (Un_cv (fun (m : nat) => (sum_f_R0 an m) + (sum_f_R0 bn m)) (s + t)).
move=> H3.
move=> eps H4.
elim (H3 eps H4).
move=> M H5.
exists M.
move=> n H6.
rewrite (sum_f_R0_plus an bn).
apply (H5 n H6).
apply Theorem_2_5_1_plus.
apply H1.
apply H2.
Qed.

Lemma Proposition_5_3_1_2 : forall (N : nat) (c : R) (an : nat -> Rn N) (s : Rn N), (Un_cv_met (Rn_met N) (sum_f_Rn N an) s) -> (Un_cv_met (Rn_met N) (sum_f_Rn N (fun (n : nat) => Rnmult N c (an n))) (Rnmult N c s)).
Proof.
move=> N c an s H1.
suff: (Un_cv_met (Rn_met N) (fun (m : nat) => Rnmult N c (sum_f_Rn N an m)) (Rnmult N c s)).
move=> H3.
move=> eps H4.
elim (H3 eps H4).
move=> M H5.
exists M.
move=> n H6.
rewrite (sum_f_Rn_mult N c an).
apply (H5 n H6).
apply Proposition_4_6_3.
apply H1.
Qed.

Lemma Proposition_5_3_1_2_R : forall (c : R) (an : nat -> R) (s : R), (Un_cv (sum_f_R0 an) s) -> (Un_cv (sum_f_R0 (fun (n : nat) => c * (an n))) (c * s)).
Proof.
move=> c an s H1.
suff: (Un_cv (fun (m : nat) => c * (sum_f_R0 an m)) (c * s)).
move=> H3.
move=> eps H4.
elim (H3 eps H4).
move=> M H5.
exists M.
move=> n H6.
rewrite (sum_f_R0_mult c an).
apply (H5 n H6).
apply Theorem_2_5_1_mult.
move=> eps H2.
exists O.
move=> n H3.
rewrite R_dist_eq.
apply H2.
apply H1.
Qed.

Lemma Proposition_5_3_2 : forall (N : nat) (an : nat -> Rn N) (bn : nat -> nat) (s : Rn N), (forall (n : nat),(bn n) < (bn (S n)))%nat -> (Un_cv_met (Rn_met N) (sum_f_Rn N an) s) -> (Un_cv_met (Rn_met N) (sum_f_Rn N (fun (n : nat) => (match n with | O => sigma_Rn N an O (bn O) | S n0 => sigma_Rn N an (S (bn n0)) (bn (S n0)) end))) s).
Proof.
move=> N an bn s H1.
apply Theorem_4_5_4.
exists bn.
apply conj.
apply H1.
elim.
unfold sum_f_Rn at 1.
unfold sigma_Rn.
suff: ((fun k : nat => an (0 + k)%nat) = an).
move=> H2.
suff: ((bn 0%nat - 0)%nat = bn 0%nat).
move=> H3.
rewrite H2.
rewrite H3.
reflexivity.
rewrite {2} (minus_n_O (bn O)).
reflexivity.
apply functional_extensionality.
move=> n.
rewrite (plus_0_l n).
reflexivity.
move=> n H2.
simpl.
rewrite H2.
rewrite MySumEqsigma_Rn.
rewrite MySumEqsum_f_Rn.
rewrite MySumEqsum_f_Rn.
rewrite (MySumF2Excluded nat (RnPCM N) an (exist (Finite nat) (fun m : nat => (0 <= m <= bn (S n))%nat) (natSectionFinite 0 (bn (S n)))) (fun m : nat => (0 <= m <= bn n)%nat)).
suff: ((FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= bn (S n))%nat) (natSectionFinite 0 (bn (S n)))) (fun m : nat => (0 <= m <= bn n)%nat)) = (exist (Finite nat) (fun m : nat => (0 <= m <= bn n)%nat) (natSectionFinite 0 (bn n)))).
move=> H3.
rewrite - H3.
suff: ((exist (Finite nat) (fun m : nat => (S (bn n) <= m <= bn (S n))%nat) (natSectionFinite (S (bn n)) (bn (S n)))) = (FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= bn (S n))%nat) (natSectionFinite 0 (bn (S n)))) (Ensembles.Complement nat (fun m : nat => (0 <= m <= bn n)%nat)))).
move=> H4.
rewrite - H4.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> m H4.
apply Intersection_intro.
move=> H5.
apply (le_not_lt m (bn n)).
apply H5.
apply H4.
apply conj.
apply le_O_n.
apply H4.
move=> m H4.
elim H4.
move=> m0 H5 H6.
elim (le_or_lt m0 (bn n)).
move=> H7.
apply False_ind.
apply H5.
apply conj.
apply le_O_n.
apply H7.
move=> H7.
apply conj.
apply H7.
apply H6.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> m H3.
elim H3.
move=> m0 H4 H5.
apply H4.
move=> m H3.
apply Intersection_intro.
apply H3.
apply conj.
apply H3.
apply (le_trans m (bn n) (bn (S n))).
apply H3.
apply lt_le_weak.
apply H1.
apply H1.
Qed.

Lemma Proposition_5_3_2_R : forall (an : nat -> R) (bn : nat -> nat) (s : R), (forall (n : nat),(bn n) < (bn (S n)))%nat -> (Un_cv (sum_f_R0 an) s) -> (Un_cv (sum_f_R0 (fun (n : nat) => (match n with | O => sigma an O (bn O) | S n0 => sigma an (S (bn n0)) (bn (S n0)) end))) s).
Proof.
move=> an bn s H1.
apply Formula_3_18.
exists bn.
apply conj.
apply H1.
elim.
unfold sum_f_R0 at 1.
unfold sigma.
suff: ((fun k : nat => an (0 + k)%nat) = an).
move=> H2.
suff: ((bn 0%nat - 0)%nat = bn 0%nat).
move=> H3.
rewrite H2.
rewrite H3.
reflexivity.
rewrite {2} (minus_n_O (bn O)).
reflexivity.
apply functional_extensionality.
move=> n.
rewrite (plus_0_l n).
reflexivity.
move=> n H2.
simpl.
rewrite H2.
rewrite MySumEqsigma.
rewrite MySumEqsum_f_R0.
rewrite MySumEqsum_f_R0.
rewrite (MySumF2Excluded nat RPCM an (exist (Finite nat) (fun m : nat => (0 <= m <= bn (S n))%nat) (natSectionFinite 0 (bn (S n)))) (fun m : nat => (0 <= m <= bn n)%nat)).
suff: ((exist (Finite nat) (fun m : nat => (0 <= m <= bn n)%nat) (natSectionFinite 0 (bn n))) = (FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= bn (S n))%nat) (natSectionFinite 0 (bn (S n)))) (fun m : nat => (0 <= m <= bn n)%nat))).
move=> H3.
rewrite - H3.
suff: ((exist (Finite nat) (fun m : nat => (S (bn n) <= m <= bn (S n))%nat) (natSectionFinite (S (bn n)) (bn (S n)))) = (FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= bn (S n))%nat) (natSectionFinite 0 (bn (S n)))) (Ensembles.Complement nat (fun m : nat => (0 <= m <= bn n)%nat)))).
move=> H4.
rewrite - H4.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> m H4.
apply Intersection_intro.
move=> H5.
apply (le_not_lt m (bn n)).
apply H5.
apply H4.
apply conj.
apply le_O_n.
apply H4.
move=> m H4.
elim H4.
move=> m0 H5 H6.
elim (le_or_lt m0 (bn n)).
move=> H7.
apply False_ind.
apply H5.
apply conj.
apply le_O_n.
apply H7.
move=> H7.
apply conj.
apply H7.
apply H6.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> m H4.
apply Intersection_intro.
apply H4.
apply conj.
apply H4.
apply (le_trans m (bn n) (bn (S n))).
apply H4.
apply lt_le_weak.
apply H1.
move=> m H4.
elim H4.
move=> m0 H5 H6.
apply H5.
apply H1.
Qed.

Definition PositiveSequence (an : nat -> R) := forall (n : nat), an n >= 0.

Definition NarrowPositiveSequence (an : nat -> R) := forall (n : nat), an n > 0.

Lemma NarrowPositiveSequenceWeak : forall (an : nat -> R), (NarrowPositiveSequence an) -> (PositiveSequence an).
Proof.
move=> an H1 n.
apply Rgt_ge.
apply H1.
Qed.

Lemma Theorem_5_4 : forall (an : nat -> R), (PositiveSequence an) -> ((exists (s : R), Un_cv (sum_f_R0 an) s) <-> my_bounded (Im nat R (Full_set nat) (sum_f_R0 an))).
Proof.
move=> an H1.
apply conj.
move=> H2.
suff: ((fun x : R => exists n : nat, sum_f_R0 an n = x) = (Im nat R (Full_set nat) (sum_f_R0 an))).
move=> H3.
rewrite - H3.
apply (Proposition_2_4 (sum_f_R0 an)).
apply H2.
apply Extensionality_Ensembles.
apply conj.
move=> r H3.
elim H3.
move=> n H4.
apply (Im_intro nat R (Full_set nat) (sum_f_R0 an) n).
apply Full_intro.
rewrite H4.
reflexivity.
move=> r H3.
elim H3.
move=> n H4 y H5.
exists n.
rewrite H5.
reflexivity.
move=> H2.
elim (Theorem_3_1_1 (sum_f_R0 an)).
move=> s H3.
exists s.
apply H3.
apply H2.
move=> n.
rewrite - (Rplus_0_r (sum_f_R0 an n)).
simpl.
apply Rplus_le_compat_l.
apply Rge_le.
apply H1.
Qed.

Lemma Formula_2_6_Rn : forall (N : nat) (An Bn : nat -> Rn N), Finite nat (fun n : nat => An n <> Bn n) -> forall x : Rn N, Un_cv_met (Rn_met N) An x <-> Un_cv_met (Rn_met N) Bn x.
Proof.
move=> N An Bn H1 x.
elim (classic (Inhabited nat (fun n : nat => An n <> Bn n))).
move=> H9.
elim (Finite_max_nat (fun n : nat => An n <> Bn n) H1).
move=> M1 H2.
apply conj.
move=> H3 eps H4.
elim (H3 eps H4).
move=> M2 H5.
exists (max (S M1) M2).
move=> n H6.
suff: (Bn n) = (An n).
move=> H7.
rewrite H7.
apply (H5 n).
apply (le_trans M2 (max (S M1) M2) n).
apply (Nat.le_max_r (S M1) M2).
apply H6.
apply NNPP.
move=> H7.
apply (le_not_lt n M1).
apply H2.
move=> H8.
apply H7.
rewrite H8.
reflexivity.
apply (le_trans (S M1) (max (S M1) M2) n).
apply (Nat.le_max_l (S M1) M2).
apply H6.
move=> H3 eps H4.
elim (H3 eps H4).
move=> M2 H5.
exists (max (S M1) M2).
move=> n H6.
suff: (An n) = (Bn n).
move=> H7.
rewrite H7.
apply (H5 n).
apply (le_trans M2 (max (S M1) M2) n).
apply (Nat.le_max_r (S M1) M2).
apply H6.
apply NNPP.
move=> H7.
apply (le_not_lt n M1).
apply H2.
apply H7.
apply (le_trans (S M1) (max (S M1) M2) n).
apply (Nat.le_max_l (S M1) M2).
apply H6.
apply H9.
move=> H2.
suff: (An = Bn).
move=> H3.
rewrite H3.
apply conj.
apply.
apply.
apply functional_extensionality.
move=> n.
apply NNPP.
move=> H3.
apply H2.
apply (Inhabited_intro nat (fun n0 : nat => An n0 <> Bn n0) n).
apply H3.
Qed.

Lemma Formula_2_6_sum_f_R0 : forall (An Bn : nat -> R), (Finite nat (fun n : nat => (An n) <> (Bn n))) -> ((exists (x : R), Un_cv (sum_f_R0 An) x) <-> (exists (x : R), Un_cv (sum_f_R0 Bn) x)).
Proof.
suff: (forall (An Bn : nat -> R), (Finite nat (fun n : nat => (An n) <> (Bn n))) -> ((exists (x : R), Un_cv (sum_f_R0 An) x) -> (exists (x : R), Un_cv (sum_f_R0 Bn) x))).
move=> H1.
move=> An Bn H2.
apply conj.
apply H1.
apply H2.
apply H1.
suff: ((fun n : nat => Bn n <> An n) = (fun n : nat => An n <> Bn n)).
move=> H3.
rewrite H3.
apply H2.
apply Extensionality_Ensembles.
apply conj.
move=> n H3 H4.
apply H3.
rewrite H4.
reflexivity.
move=> n H3 H4.
apply H3.
rewrite H4.
reflexivity.
move=> An Bn H1.
elim (classic (Inhabited nat (fun n : nat => An n <> Bn n))).
move=> H2.
elim (Finite_max_nat (fun n : nat => An n <> Bn n) H1).
move=> M1 H3 H4.
suff: (forall (n : nat), sum_f_R0 Bn (M1 + n) = sum_f_R0 An (M1 + n) + sum_f_R0 Bn M1 - sum_f_R0 An M1).
move=> H5.
elim H4.
move=> a H6.
exists (a + sum_f_R0 Bn M1 - sum_f_R0 An M1).
move=> eps H7.
elim (H6 eps H7).
move=> M2 H8.
exists (max M1 M2).
move=> n H9.
unfold R_dist.
rewrite - {1} (le_plus_minus_r M1 n).
rewrite (H5 (n - M1)%nat).
rewrite (le_plus_minus_r M1 n).
unfold Rminus at 2.
unfold Rminus at 2.
rewrite Rplus_assoc.
rewrite Rplus_assoc.
rewrite (Rplus_comm a (sum_f_R0 Bn M1 + - sum_f_R0 An M1)).
unfold Rminus.
rewrite Rplus_assoc.
rewrite Ropp_plus_distr.
rewrite - (Rplus_assoc (sum_f_R0 Bn M1 + - sum_f_R0 An M1) (- (sum_f_R0 Bn M1 + - sum_f_R0 An M1)) (- a)).
rewrite Rplus_opp_r.
rewrite Rplus_0_l.
apply H8.
apply (le_trans M2 (Init.Nat.max M1 M2) n).
apply (Nat.le_max_r M1 M2).
apply H9.
apply (le_trans M1 (Init.Nat.max M1 M2) n).
apply (Nat.le_max_l M1 M2).
apply H9.
apply (le_trans M1 (Init.Nat.max M1 M2) n).
apply (Nat.le_max_l M1 M2).
apply H9.
elim.
rewrite (plus_0_r M1).
rewrite (Rplus_comm (sum_f_R0 An M1) (sum_f_R0 Bn M1)).
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
reflexivity.
move=> n H5.
rewrite Nat.add_succ_r.
simpl.
rewrite Rplus_assoc.
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_assoc.
rewrite (Rplus_comm (An (S (M1 + n))) (sum_f_R0 Bn M1 + - sum_f_R0 An M1)).
rewrite - Rplus_assoc.
rewrite - Rplus_assoc.
suff: (An (S (M1 + n)) = Bn (S (M1 + n))).
move=> H6.
rewrite H6.
rewrite H5.
reflexivity.
apply NNPP.
move=> H6.
apply (le_not_lt (S (M1 + n)) M1).
apply H3.
apply H6.
apply (le_n_S M1 (M1 + n)).
rewrite - {1} (plus_0_r M1).
apply (plus_le_compat_l).
apply le_0_n.
apply H2.
move=> H2.
suff: (An = Bn).
move=> H3.
rewrite H3.
apply.
apply functional_extensionality.
move=> n.
apply NNPP.
move=> H3.
apply H2.
apply (Inhabited_intro nat (fun n0 : nat => An n0 <> Bn n0) n).
apply H3.
Qed.

Lemma Formula_2_6_sum_f_Rn : forall (N : nat) (An Bn : nat -> Rn N), (Finite nat (fun n : nat => (An n) <> (Bn n))) -> ((exists (x : Rn N), Un_cv_met (Rn_met N) (sum_f_Rn N An) x) <-> (exists (x : Rn N), Un_cv_met (Rn_met N) (sum_f_Rn N Bn) x)).
Proof.
suff: (forall (N : nat) (An Bn : nat -> Rn N), (Finite nat (fun n : nat => (An n) <> (Bn n))) -> ((exists (x : Rn N), Un_cv_met (Rn_met N) (sum_f_Rn N An) x) -> (exists (x : Rn N), Un_cv_met (Rn_met N) (sum_f_Rn N Bn) x))).
move=> H1.
move=> N An Bn H2.
apply conj.
apply H1.
apply H2.
apply H1.
suff: ((fun n : nat => Bn n <> An n) = (fun n : nat => An n <> Bn n)).
move=> H3.
rewrite H3.
apply H2.
apply Extensionality_Ensembles.
apply conj.
move=> n H3 H4.
apply H3.
rewrite H4.
reflexivity.
move=> n H3 H4.
apply H3.
rewrite H4.
reflexivity.
move=> N An Bn H1.
elim (classic (Inhabited nat (fun n : nat => An n <> Bn n))).
move=> H2.
elim (Finite_max_nat (fun n : nat => An n <> Bn n) H1).
move=> M1 H3 H4.
suff: (forall (n : nat), sum_f_Rn N Bn (M1 + n) = (Rnminus N (Rnplus N (sum_f_Rn N An (M1 + n)) (sum_f_Rn N Bn M1)) (sum_f_Rn N An M1))).
move=> H5.
elim H4.
move=> a H6.
exists (Rnminus N (Rnplus N a (sum_f_Rn N Bn M1)) (sum_f_Rn N An M1)).
move=> eps H7.
elim (H6 eps H7).
move=> M2 H8.
exists (max M1 M2).
move=> n H9.
unfold dist.
unfold Rn_met.
unfold Rn_dist.
rewrite - {1} (le_plus_minus_r M1 n).
rewrite (H5 (n - M1)%nat).
rewrite (le_plus_minus_r M1 n).
unfold Rnminus at 2.
unfold Rnminus at 2.
rewrite Rnplus_assoc.
rewrite Rnplus_assoc.
rewrite (Rnplus_comm N a (Rnplus N (sum_f_Rn N Bn M1) (Rnopp N (sum_f_Rn N An M1)))).
unfold Rnminus.
rewrite Rnplus_assoc.
suff: (Rnopp N (Rnplus N (Rnplus N (sum_f_Rn N Bn M1) (Rnopp N (sum_f_Rn N An M1))) a) = Vopp Rfield (RnVS N) (Vadd Rfield (RnVS N) (Rnplus N (sum_f_Rn N Bn M1) (Rnopp N (sum_f_Rn N An M1))) a)).
move=> H10.
rewrite H10.
rewrite Vopp_add_distr.
simpl.
rewrite - (Rnplus_assoc N (Rnplus N (sum_f_Rn N Bn M1) (Rnopp N (sum_f_Rn N An M1))) (Rnopp N (Rnplus N (sum_f_Rn N Bn M1) (Rnopp N (sum_f_Rn N An M1)))) (Rnopp N a)).
rewrite Rnplus_opp_r.
rewrite Rnplus_O_l.
apply H8.
apply (le_trans M2 (Init.Nat.max M1 M2) n).
apply (Nat.le_max_r M1 M2).
apply H9.
simpl.
reflexivity.
apply (le_trans M1 (Init.Nat.max M1 M2) n).
apply (Nat.le_max_l M1 M2).
apply H9.
apply (le_trans M1 (Init.Nat.max M1 M2) n).
apply (Nat.le_max_l M1 M2).
apply H9.
elim.
rewrite (plus_0_r M1).
rewrite (Rnplus_comm N (sum_f_Rn N An M1) (sum_f_Rn N Bn M1)).
unfold Rnminus.
rewrite Rnplus_assoc.
rewrite Rnplus_opp_r.
rewrite Rnplus_comm.
rewrite Rnplus_O_l.
reflexivity.
move=> n H5.
rewrite Nat.add_succ_r.
simpl.
rewrite Rnplus_assoc.
unfold Rnminus.
rewrite Rnplus_assoc.
rewrite Rnplus_assoc.
rewrite (Rnplus_comm N (An (S (M1 + n))) (Rnplus N (sum_f_Rn N Bn M1) (Rnopp N (sum_f_Rn N An M1)))).
rewrite - Rnplus_assoc.
rewrite - Rnplus_assoc.
suff: (An (S (M1 + n)) = Bn (S (M1 + n))).
move=> H6.
rewrite H6.
rewrite H5.
reflexivity.
apply NNPP.
move=> H6.
apply (le_not_lt (S (M1 + n)) M1).
apply H3.
apply H6.
apply (le_n_S M1 (M1 + n)).
rewrite - {1} (plus_0_r M1).
apply (plus_le_compat_l).
apply le_0_n.
apply H2.
move=> H2.
suff: (An = Bn).
move=> H3.
rewrite H3.
apply.
apply functional_extensionality.
move=> n.
apply NNPP.
move=> H3.
apply H2.
apply (Inhabited_intro nat (fun n0 : nat => An n0 <> Bn n0) n).
apply H3.
Qed.

Lemma Theorem_5_5_1 : forall (an cn : nat -> R), (PositiveSequence an) -> (PositiveSequence cn) -> (forall (n : nat), (an n) <= (cn n)) -> (exists (s : R), Un_cv (sum_f_R0 cn) s) -> (exists (s : R), Un_cv (sum_f_R0 an) s).
Proof.
move=> an cn H1 H2 H3 H4.
apply Theorem_5_4.
apply H1.
elim (proj1 (bounded_abs (Im nat R (Full_set nat) (sum_f_R0 cn))) (proj1 (Theorem_5_4 cn H2) H4)).
move=> M H5.
apply bounded_abs.
exists M.
move=> r H6.
elim H6.
move=> x H7 y H8.
rewrite H8.
elim H7.
move=> y0 H9 z0 H10.
rewrite H10.
apply (Rle_trans (Rabs (sum_f_R0 an y0)) (Rabs (sum_f_R0 cn y0)) M).
rewrite (Rabs_right (sum_f_R0 an y0)).
rewrite (Rabs_right (sum_f_R0 cn y0)).
rewrite MySumEqsum_f_R0.
rewrite MySumEqsum_f_R0.
apply (FiniteSetInduction nat (exist (Finite nat) (fun m : nat => (0 <= m <= y0)%nat) (natSectionFinite 0 y0))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply Req_le.
reflexivity.
move=> B b H11 H12 H13 H14.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
apply Rplus_le_compat.
apply H14.
apply H3.
apply H13.
apply H13.
rewrite MySumEqsum_f_R0.
apply MySumF2Induction.
apply conj.
apply Req_ge.
reflexivity.
move=> cm n H11 H12.
apply Rle_ge.
apply Rplus_le_le_0_compat.
apply Rge_le.
apply H12.
apply Rge_le.
apply H2.
rewrite MySumEqsum_f_R0.
apply MySumF2Induction.
apply conj.
apply Req_ge.
reflexivity.
move=> cm n H11 H12.
apply Rle_ge.
apply Rplus_le_le_0_compat.
apply Rge_le.
apply H12.
apply Rge_le.
apply H1.
apply H5.
apply (Im_intro R R (Im nat R (Full_set nat) (sum_f_R0 cn)) Rabs (sum_f_R0 cn y0)).
apply (Im_intro nat R (Full_set nat) (sum_f_R0 cn) y0).
apply Full_intro.
reflexivity.
reflexivity.
Qed.

Lemma Theorem_5_5_2 : forall (an dn : nat -> R), (PositiveSequence an) -> (PositiveSequence dn) -> (forall (n : nat), (an n) >= (dn n)) -> (Un_inf (sum_f_R0 dn)) -> (Un_inf (sum_f_R0 an)).
Proof.
move=> an dn H1 H2 H3 H4.
apply (le_Sequence_inf (sum_f_R0 dn) (sum_f_R0 an)).
move=> n.
rewrite MySumEqsum_f_R0.
rewrite MySumEqsum_f_R0.
apply (FiniteSetInduction nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply Req_le.
reflexivity.
move=> B b H5 H6 H7 H8.
rewrite MySumF2Add.
rewrite MySumF2Add.
apply Rplus_le_compat.
apply H8.
apply Rge_le.
apply H3.
apply H7.
apply H7.
apply H4.
Qed.

Lemma Theorem_5_5_3 : forall (an cn : nat -> R), (NarrowPositiveSequence an) -> (NarrowPositiveSequence cn) -> (forall (n : nat), (an (S n)) / (an n) <= (cn (S n)) / (cn n)) -> (exists (s : R), Un_cv (sum_f_R0 cn) s) -> (exists (s : R), Un_cv (sum_f_R0 an) s).
Proof.
move=> an cn H1 H2 H3 H4.
suff: (forall (n : nat), an n <= (an O) / (cn O) * (cn n)).
move=> H5.
apply (Theorem_5_5_1 an (fun (n : nat) => (an O) / (cn O) * (cn n))).
apply NarrowPositiveSequenceWeak.
apply H1.
apply NarrowPositiveSequenceWeak.
move=> n.
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
apply H1.
apply Rinv_0_lt_compat.
apply H2.
apply H2.
suff: (forall n : nat, an n / cn n <= an 0%nat / cn 0%nat).
move=> H6 n.
rewrite - (Rmult_1_r (an n)).
rewrite - (Rinv_l (cn n)).
rewrite - Rmult_assoc.
apply Rmult_le_compat_r.
apply Rlt_le.
apply H2.
apply H6.
apply Rgt_not_eq.
apply H2.
elim.
apply Req_le.
reflexivity.
move=> n H6.
apply (Rle_trans (an (S n) / cn (S n)) (an n / cn n) (an 0%nat / cn 0%nat)).
apply (Rmult_le_reg_r (cn (S n))).
apply H2.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
apply (Rmult_le_reg_l (/ (an n))).
apply Rinv_0_lt_compat.
apply H1.
rewrite Rmult_assoc.
rewrite - Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_l.
rewrite Rmult_comm.
rewrite (Rmult_comm (/ cn n) (cn (S n))).
apply H3.
apply Rgt_not_eq.
apply H1.
apply Rgt_not_eq.
apply H2.
apply H6.
elim H4.
move=> s H6.
exists (an 0%nat / cn 0%nat * s).
apply Proposition_5_3_1_2_R.
apply H6.
suff: (forall (n : nat), an n / cn n <= an 0%nat / cn 0%nat).
move=> H5.
move=> n.
apply (Rmult_le_reg_r (/ (cn n))).
apply Rinv_0_lt_compat.
apply H2.
rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
apply H5.
apply Rgt_not_eq.
apply H2.
elim.
apply Req_le.
reflexivity.
move=> n H5.
apply (Rle_trans (an (S n) / cn (S n)) (an n / cn n) (an 0%nat / cn 0%nat)).
apply (Rmult_le_reg_r (cn (S n))).
apply H2.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
apply (Rmult_le_reg_l (/ (an n))).
apply Rinv_0_lt_compat.
apply H1.
rewrite Rmult_assoc.
rewrite - Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_l.
rewrite Rmult_comm.
rewrite (Rmult_comm (/ cn n) (cn (S n))).
apply H3.
apply Rgt_not_eq.
apply H1.
apply Rgt_not_eq.
apply H2.
apply H5.
Qed.

Lemma Un_inf_mult : forall (an : nat -> R) (c : R), (c > 0) -> (Un_inf an) -> (Un_inf (fun (n : nat) => c * (an n) )).
Proof.
move=> an c H1 H2.
move=> eps.
elim (H2 (/ c * eps)).
move=> M H3.
exists M.
move=> n H4.
apply (Rmult_lt_reg_l (/ c)).
apply Rinv_0_lt_compat.
apply H1.
rewrite - Rmult_assoc.
rewrite Rinv_l.
rewrite (Rmult_1_l (an n)).
apply (H3 n H4).
apply Rgt_not_eq.
apply H1.
Qed.

Lemma Theorem_5_5_4 : forall (an dn : nat -> R), (NarrowPositiveSequence an) -> (NarrowPositiveSequence dn) -> (forall (n : nat), (an (S n)) / (an n) >= (dn (S n)) / (dn n)) -> (Un_inf (sum_f_R0 dn)) -> (Un_inf (sum_f_R0 an)).
Proof.
move=> an dn H1 H2 H3 H4.
suff: (forall (n : nat), an n >= (an O) / (dn O) * (dn n)).
move=> H5.
apply (Theorem_5_5_2 an (fun (n : nat) => (an O) / (dn O) * (dn n))).
apply NarrowPositiveSequenceWeak.
apply H1.
apply NarrowPositiveSequenceWeak.
move=> n.
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
apply H1.
apply Rinv_0_lt_compat.
apply H2.
apply H2.
suff: (forall n : nat, an n / dn n >= an 0%nat / dn 0%nat).
move=> H6 n.
rewrite - (Rmult_1_r (an n)).
rewrite - (Rinv_l (dn n)).
rewrite - Rmult_assoc.
apply Rmult_ge_compat_r.
apply Rgt_ge.
apply H2.
apply H6.
apply Rgt_not_eq.
apply H2.
elim.
apply Req_ge.
reflexivity.
move=> n H6.
apply (Rge_trans (an (S n) / dn (S n)) (an n / dn n) (an 0%nat / dn 0%nat)).
apply Rle_ge.
apply (Rmult_le_reg_r (dn (S n))).
apply H2.
rewrite (Rmult_assoc (an (S n)) (/ dn (S n)) (dn (S n))).
rewrite Rinv_l.
rewrite Rmult_1_r.
apply (Rmult_le_reg_l (/ (an n))).
apply Rinv_0_lt_compat.
apply H1.
rewrite Rmult_assoc.
rewrite - Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_l.
rewrite Rmult_comm.
rewrite (Rmult_comm (/ an n) (an (S n))).
apply Rge_le.
apply H3.
apply Rgt_not_eq.
apply H1.
apply Rgt_not_eq.
apply H2.
apply H6.
suff: (sum_f_R0 (fun n : nat => an 0%nat / dn 0%nat * dn n) = (fun n : nat => an 0%nat / dn 0%nat * (sum_f_R0 dn n))).
move=> H7.
rewrite H7.
apply Un_inf_mult.
apply Rmult_gt_0_compat.
apply H1.
apply Rinv_0_lt_compat.
apply H2.
apply H4.
apply functional_extensionality.
move=> n.
apply sum_f_R0_mult.
suff: (forall (n : nat), an n / dn n >= an 0%nat / dn 0%nat).
move=> H5.
move=> n.
apply Rle_ge.
apply (Rmult_le_reg_r (/ (dn n))).
apply Rinv_0_lt_compat.
apply H2.
rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
apply Rge_le.
apply H5.
apply Rgt_not_eq.
apply H2.
elim.
apply Req_le.
reflexivity.
move=> n H5.
apply (Rge_trans (an (S n) / dn (S n)) (an n / dn n) (an 0%nat / dn 0%nat)).
apply Rle_ge.
apply (Rmult_le_reg_r (dn (S n))).
apply H2.
rewrite (Rmult_assoc (an (S n)) (/ dn (S n)) (dn (S n))).
rewrite Rinv_l.
rewrite Rmult_1_r.
apply (Rmult_le_reg_l (/ (an n))).
apply Rinv_0_lt_compat.
apply H1.
rewrite Rmult_assoc.
rewrite - Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_l.
rewrite Rmult_comm.
rewrite (Rmult_comm (/ an n) (an (S n))).
apply Rge_le.
apply H3.
apply Rgt_not_eq.
apply H1.
apply Rgt_not_eq.
apply H2.
apply H5.
Qed.

Lemma GeometricProgressionSumR : forall (k : R), (k <> 1) -> forall (n : nat), (sum_f_R0 (pow k) n) = (1 - (pow k (S n))) / (1 - k).
Proof.
move=> k H1.
suff: (1 - k <> 0).
move=> H2.
elim.
simpl.
rewrite Rmult_1_r.
unfold Rdiv.
rewrite Rinv_r.
reflexivity.
apply H2.
move=> n H3.
suff: (sum_f_R0 (pow k) (S n) = sum_f_R0 (pow k) n + k ^ S n).
move=> H4.
rewrite H4.
rewrite H3.
rewrite - {2} (Rmult_1_r (k ^ S n)).
rewrite - {3} (Rinv_r (1 - k)).
rewrite - Rmult_assoc.
unfold Rdiv.
rewrite - Rmult_plus_distr_r.
suff: ((1 - k ^ S n + k ^ S n * (1 - k)) = (1 - k ^ S (S n))).
move=> H5.
rewrite H5.
reflexivity.
rewrite Rmult_plus_distr_l.
rewrite - Rplus_assoc.
rewrite Rmult_1_r.
rewrite (Rplus_assoc 1 (- k ^ S n) (k ^ S n)).
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
rewrite Rmult_comm.
rewrite - Ropp_mult_distr_l.
reflexivity.
apply H2.
reflexivity.
apply Rminus_eq_contra.
move=> H2.
apply H1.
rewrite H2.
reflexivity.
Qed.

Lemma mult_S_eq_reg_l : forall n m p : nat, (S n * m)%nat = (S n * p)%nat -> m = p.
Proof.
move=> n m p H1.
apply le_antisym.
apply (mult_S_le_reg_l n).
rewrite H1.
apply (le_n (S n * p)).
apply (mult_S_le_reg_l n).
rewrite H1.
apply (le_n (S n * p)).
Qed.

Lemma Example_2_6 : forall (x : R), (0 <= x < 1) -> (Un_cv (pow x) 0).
Proof.
move=> x H1.
elim (classic (x = 0)).
move=> H2.
suff: (forall (n : nat), (n > O)%nat -> (pow x n) = 0).
move=> H3 eps H4.
exists 1%nat.
move=> n H5.
rewrite H3.
rewrite R_dist_eq.
apply H4.
apply H5.
elim.
move=> H3.
apply False_ind.
apply (le_not_lt 0 0).
apply le_n.
apply H3.
move=> n H3 H4.
simpl.
rewrite H2.
apply Rmult_0_l.
move=> H9.
suff: (/ x - 1 > 0).
move=> H2.
apply (Proposition_2_7 (fun _ => 0) (fun (n : nat) => match n with | O => 1 | S _ => (/ ((INR n) * (/ x - 1))) end)).
move=> eps H3.
exists O.
move=> n H4.
rewrite R_dist_eq.
apply H3.
move=> eps H3.
elim (Formula_3_8 (eps * (/ x - 1))).
move=> M H4.
exists (S M).
move=> n H5.
suff: (match n with
  | 0%nat => 1
  | S _ => / (INR n * (/ x - 1))
  end = / (INR n * (/ x - 1))).
move=> H10.
rewrite H10.
unfold R_dist.
apply (Rmult_lt_reg_r (Rabs (/ x - 1))).
apply Rabs_pos_lt.
apply Rgt_not_eq.
apply H2.
rewrite {2} (Rabs_pos_eq (/ x - 1)).
rewrite - Rabs_mult.
unfold Rminus at 1.
rewrite Ropp_0.
rewrite Rplus_0_r.
rewrite Rinv_mult_distr.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite - (Rplus_0_r (/ INR n)).
rewrite - Ropp_0.
rewrite - (Rmult_1_l (/ INR n)).
apply H4.
apply lt_le_weak.
apply H5.
apply Rgt_not_eq.
apply H2.
apply Rgt_not_eq.
suff: (0 = INR O).
move=> H6.
rewrite H6.
apply lt_INR.
apply (le_trans (S O) (S M) n).
apply (le_n_S O M (le_0_n M)).
apply H5.
reflexivity.
apply Rgt_not_eq.
apply H2.
apply Rlt_le.
apply H2.
move: H5.
elim n.
move=> H5.
apply False_ind.
apply (lt_not_le O (S M)).
apply (le_n_S O M (le_0_n M)).
apply H5.
reflexivity.
apply Rmult_gt_0_compat.
apply H3.
apply H2.
move=> n.
apply conj.
elim n.
apply Rlt_le.
apply Rlt_0_1.
move=> n0.
move=> H3.
rewrite - (Rmult_0_l 0).
apply (Rmult_le_compat 0 x 0 (x ^ n0)).
apply Req_le.
reflexivity.
apply Req_le.
reflexivity.
apply H1.
apply H3.
suff: forall (n : nat), (x ^ n =  / ((/ x) ^ n)).
move=> H3.
rewrite H3.
elim n.
apply Req_le.
simpl.
apply Rinv_1.
move=> n0 H4.
apply Rlt_le.
apply Rinv_lt_contravar.
apply Rmult_gt_0_compat.
apply Rmult_gt_0_compat.
suff: (0 = INR O).
move=> H5.
rewrite H5.
apply lt_INR.
apply (le_n_S O n0 (le_0_n n0)).
reflexivity.
apply H2.
suff: (forall (m : nat), (/ x) ^ m > 0).
move=> H5.
apply H5.
elim.
apply Rlt_0_1.
move=> n1 H5.
simpl.
apply Rmult_gt_0_compat.
apply Rinv_0_lt_compat.
elim (proj1 H1).
apply.
move=> H6.
apply False_ind.
apply H9.
rewrite H6.
reflexivity.
apply H5.
suff: (/ x = (/ x - 1) + 1).
move=> H5.
rewrite {2} H5.
rewrite Binomial_Theorem.
apply (Rlt_le_trans (INR (S n0) * (/ x - 1)) (sigma (fun k : nat => INR (conv (S n0) k) * (/ x - 1) ^ k * 1 ^ (S n0 - k)) 0 (S O)) (sigma (fun k : nat => INR (conv (S n0) k) * (/ x - 1) ^ k * 1 ^ (S n0 - k)) 0 (S n0))).
unfold sigma.
simpl.
rewrite Rmult_1_l.
rewrite Rmult_1_l.
rewrite Rmult_1_l.
rewrite Rmult_1_r.
suff: (forall (m : nat), 1 ^ m = 1).
move=> H6.
rewrite H6.
rewrite H6.
rewrite Rmult_1_r.
suff: ((conv n0 O + conv n0 1%nat)%nat = S n0).
move=> H7.
rewrite H7.
rewrite - {1} (Rplus_0_l (match n0 with
| 0%nat => 1
| S _ => INR n0 + 1 end * (/ x - 1))).
simpl.
apply Rplus_lt_compat_r.
apply Rlt_0_1.
suff: (forall (n : nat), exists (m : nat), S m = fact n).
move=> H7.
suff: (conv n0 0 = 1%nat).
move=> H8.
rewrite H8.
suff: (conv n0 1 = n0).
move=> H10.
rewrite H10.
auto.
elim (classic (n0 = O)).
move=> H10.
rewrite H10.
apply (proj2 (conv_fact 0) 1%nat).
apply le_n.
move=> H12.
elim (H7 1%nat).
move=> m1 H10.
apply (mult_S_eq_reg_l m1).
rewrite mult_comm.
rewrite H10.
elim (H7 (n0 - 1)%nat).
move=> m2 H11.
apply (mult_S_eq_reg_l m2).
rewrite mult_comm.
rewrite H11.
rewrite (proj1 (conv_fact n0) 1%nat).
unfold fact at 3.
rewrite mult_1_l.
rewrite mult_1_l.
rewrite mult_comm.
rewrite - pred_of_minus.
move: H12.
elim n0.
move=> H12.
apply False_ind.
apply H12.
reflexivity.
move=> n1 H12 H13.
rewrite Nat.pred_succ.
reflexivity.
apply neq_0_lt.
move=> H13.
apply H12.
rewrite H13.
reflexivity.
unfold conv.
elim n0.
reflexivity.
reflexivity.
suff: (forall n1 : nat, (fact n1 > O)%nat).
move=> H7 n1.
exists (pred (fact n1)).
rewrite - (S_pred (fact n1) O).
reflexivity.
apply H7.
elim.
apply le_n.
move=> n1 H7.
suff: (fact (S n1) = ((S n1) * (fact n1))%nat).
move=> H8.
rewrite H8.
rewrite - (mult_0_r (S n1)).
apply mult_lt_compat_l.
apply H7.
apply (le_n_S O n1 (le_0_n n1)).
reflexivity.
elim.
reflexivity.
move=> n1 H6.
simpl.
rewrite H6.
apply (Rmult_1_l 1).
suff: (forall (n1 : nat), sigma (fun k : nat => INR (conv (S n0) k) * (/ x - 1) ^ k * 1 ^ (S n0 - k)) 0 1 <= sigma (fun k : nat => INR (conv (S n0) k) * (/ x - 1) ^ k * 1 ^ (S n0 - k)) 0 (S n1)).
move=> H6.
apply H6.
elim.
apply Req_le.
reflexivity.
move=> n1 H6.
suff: (sigma (fun k : nat => INR (conv (S n0) k) * (/ x - 1) ^ k * 1 ^ (S n0 - k)) 0 (S (S n1)) = sigma (fun k : nat => INR (conv (S n0) k) * (/ x - 1) ^ k * 1 ^ (S n0 - k)) 0 (S n1) + INR (conv (S n0) (S (S n1))) * (/ x - 1) ^ (S (S n1)) * 1 ^ (S n0 - (S (S n1)))).
move=> H7.
apply (Rle_trans (sigma (fun k : nat => INR (conv (S n0) k) * (/ x - 1) ^ k * 1 ^ (S n0 - k)) 0 1) (sigma (fun k : nat => INR (conv (S n0) k) * (/ x - 1) ^ k * 1 ^ (S n0 - k)) 0 (S n1)) (sigma (fun k : nat => INR (conv (S n0) k) * (/ x - 1) ^ k * 1 ^ (S n0 - k)) 0 (S (S n1)))).
apply H6.
rewrite - (Rplus_0_r (sigma (fun k : nat => INR (conv (S n0) k) * (/ x - 1) ^ k * 1 ^ (S n0 - k)) 0 (S n1))).
rewrite H7.
apply Rplus_le_compat_l.
rewrite - (Rmult_0_r (INR (conv (S n0) (S (S n1))) * (/ x - 1) ^ S (S n1))).
apply Rmult_le_compat_l.
rewrite - (Rmult_0_r (INR (conv (S n0) (S (S n1))))).
apply Rmult_le_compat_l.
suff: (0 = INR O).
move=> H8.
rewrite H8.
apply le_INR.
apply le_0_n.
reflexivity.
apply Rlt_le.
suff: (forall (n2 : nat), 0 < (/ x - 1) ^ n2).
move=> H8.
apply H8.
elim.
apply Rlt_0_1.
move=> n2 H8.
simpl.
apply Rmult_gt_0_compat.
apply H2.
apply H8.
apply Rlt_le.
suff: (forall (n2 : nat), 0 < 1 ^ n2).
move=> H8.
apply H8.
elim.
apply Rlt_0_1.
move=> n2 H8.
apply Rmult_gt_0_compat.
apply Rlt_0_1.
apply H8.
reflexivity.
rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
reflexivity.
elim.
simpl.
rewrite Rinv_1.
reflexivity.
move=> n0 H3.
simpl.
rewrite Rinv_mult_distr.
rewrite Rinv_involutive.
rewrite H3.
reflexivity.
apply H9.
apply Rinv_neq_0_compat.
apply H9.
apply Rgt_not_eq.
elim n0.
apply Rlt_0_1.
move=> n1 H4.
simpl.
apply Rmult_gt_0_compat.
apply Rinv_0_lt_compat.
elim (proj1 H1).
apply.
move=> H5.
apply False_ind.
apply H9.
rewrite H5.
reflexivity.
apply H4.
apply Rgt_minus.
rewrite - Rinv_1.
apply Rinv_lt_contravar.
rewrite Rmult_1_r.
elim (proj1 H1).
apply.
move=> H2.
apply False_ind.
apply H9.
rewrite H2.
reflexivity.
apply H1.
Qed.


Lemma Example_5_2 : forall (k : R), (Rabs k) < 1 -> (Un_cv (sum_f_R0 (pow k)) (1 / (1 - k))).
Proof.
move=> k H1 eps H2.
suff: (0 <= Rabs k < 1).
move=> H3.
elim (Example_2_6 (Rabs k) H3 ((1 - k) * eps)).
move=> M H4.
exists M.
move=> n H5.
rewrite GeometricProgressionSumR.
unfold R_dist.
rewrite - Rdiv_minus_distr.
unfold Rminus.
rewrite (Rplus_comm 1 (- (k ^ S n))).
rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
apply (Rmult_lt_reg_r (Rabs (1 + - k))).
apply Rabs_pos_lt.
move=> H6.
apply (Rle_not_lt (Rabs k) 1).
right.
suff: (k = 1).
move=> H7.
rewrite H7.
rewrite Rabs_R1.
reflexivity.
rewrite - (Ropp_involutive k).
rewrite - (Ropp_involutive 1).
apply Ropp_eq_compat.
apply Rplus_opp_r_uniq.
apply H6.
apply H3.
suff: (1 + - k > 0).
move=> H6.
rewrite - Rabs_mult.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite Rabs_Ropp.
rewrite (Rabs_pos_eq (1 + - k)).
rewrite Rmult_comm.
rewrite - (Rplus_0_r (Rabs (k ^ S n))).
rewrite - Ropp_0.
apply (Rle_lt_trans (Rabs (k ^ S n) + - 0) (Rabs (Rabs (k ^ S n) + - 0)) ((1 + - k) * eps)).
apply Rle_abs.
suff: (Rabs (k ^ S n) = Rabs k ^ S n).
move=> H7.
rewrite H7.
apply (H4 (S n)).
apply le_S.
apply H5.
elim n.
simpl.
rewrite Rmult_1_r.
rewrite Rmult_1_r.
reflexivity.
move=> n0 H7.
rewrite (Rabs_mult k (k ^ S n0)).
rewrite H7.
reflexivity.
apply Rlt_le.
apply H6.
apply Rgt_not_eq.
apply H6.
apply Rgt_minus.
apply (Rle_lt_trans k (Rabs k) 1).
apply Rle_abs.
apply H1.
move=> H6.
apply (Rle_not_lt (Rabs k) 1).
right.
rewrite H6.
rewrite Rabs_R1.
reflexivity.
apply H1.
apply Rmult_gt_0_compat.
apply Rgt_minus.
apply (Rle_lt_trans k (Rabs k) 1).
apply Rle_abs.
apply H1.
apply H2.
apply conj.
apply Rabs_pos.
apply H1.
Qed.

Lemma SumShiftUnR : forall (an : nat -> R) (s : R) (k : nat), (Un_cv (sum_f_R0 an) s) <-> (Un_cv (sum_f_R0 (fun (n : nat) => an (n + (S k))%nat)) (s - (sum_f_R0 an k))).
Proof.
move=> an s k.
suff: (forall (m : nat), (sum_f_R0 an k) + (sum_f_R0 (fun n : nat => an (n + S k)%nat) m) = sum_f_R0 an (m + S k)).
move=> H1.
apply conj.
move=> H2 eps H3.
elim (H2 eps H3).
move=> M H4.
exists M.
move=> n H5.
unfold R_dist.
unfold Rminus.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
rewrite (Rplus_comm (- s) (sum_f_R0 an k)).
rewrite - Rplus_assoc.
rewrite (Rplus_comm (sum_f_R0 (fun n0 : nat => an (n0 + S k)%nat) n) (sum_f_R0 an k)).
rewrite (H1 n).
apply (H4 (n + S k)%nat).
apply (le_trans M n (n + S k)).
apply H5.
rewrite - {1} (plus_0_r n).
apply plus_le_compat_l.
apply le_0_n.
move=> H2 eps H3.
elim (H2 eps H3).
move=> M H4.
exists (M + S k)%nat.
move=> n H5.
suff: (n = n - (S k) + (S k))%nat.
move=> H6.
rewrite H6.
rewrite - H1.
unfold R_dist.
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_comm.
rewrite Rplus_assoc.
rewrite - (Ropp_involutive (sum_f_R0 an k)).
rewrite - Ropp_plus_distr.
apply H4.
rewrite H6 in H5.
apply (plus_le_reg_l M (n - S k)%nat (S k)).
rewrite plus_comm.
rewrite (plus_comm (S k) (n - S k)).
apply H5.
rewrite plus_comm.
rewrite le_plus_minus_r.
reflexivity.
apply (le_trans (S k) (M + S k) n).
rewrite - {1} (plus_0_l (S k)).
apply plus_le_compat_r.
apply le_0_n.
apply H5.
move=> m.
suff: (sum_f_R0 (fun n : nat => an (n + S k)%nat) m = sigma an (S k) (m + S k)).
move=> H1.
rewrite H1.
rewrite MySumEqsum_f_R0.
rewrite MySumEqsum_f_R0.
rewrite MySumEqsigma.
suff: (MySumF2 nat (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= k)%nat) (natSectionFinite 0 k)) RPCM an + MySumF2 nat (exist (Finite nat) (fun m0 : nat => (S k <= m0 <= m + S k)%nat) (natSectionFinite (S k) (m + S k))) RPCM an = CMc RPCM (MySumF2 nat (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= k)%nat) (natSectionFinite 0 k)) RPCM an) (MySumF2 nat (exist (Finite nat) (fun m0 : nat => (S k <= m0 <= m + S k)%nat) (natSectionFinite (S k) (m + S k))) RPCM an)).
move=> H2.
rewrite H2.
rewrite - MySumF2Union.
suff: ((FiniteUnion nat (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= k)%nat) (natSectionFinite 0 k)) (exist (Finite nat) (fun m0 : nat => (S k <= m0 <= m + S k)%nat) (natSectionFinite (S k) (m + S k)))) = (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= m + S k)%nat) (natSectionFinite 0 (m + S k)))).
move=> H3.
rewrite H3.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> n H3.
elim H3.
move=> n1 H4.
apply conj.
apply H4.
apply (le_trans n1 k (m + S k))%nat.
apply H4.
apply lt_le_weak.
rewrite /lt.
rewrite - {1} (plus_0_l (S k)).
apply plus_le_compat_r.
apply le_0_n.
move=> n1 H4.
apply conj.
apply le_0_n.
apply H4.
move=> n H3.
elim (le_or_lt n k).
move=> H4.
left.
apply conj.
apply le_0_n.
apply H4.
move=> H4.
right.
apply conj.
apply H4.
apply H3.
move=> n.
simpl.
move=> H3 H4.
apply (lt_not_le k n).
apply H3.
apply H4.
reflexivity.
rewrite - {1} (plus_0_l (S k)).
apply plus_le_compat_r.
apply le_0_n.
unfold sigma.
rewrite plus_comm.
rewrite minus_plus.
suff: ((fun n : nat => an (n + S k)%nat) = (fun n : nat => an (S k + n)%nat)).
move=> H1.
rewrite H1.
reflexivity.
apply functional_extensionality.
move=> n.
rewrite (plus_comm n (S k)).
reflexivity.
Qed.

Lemma SumShiftUnR2 : forall (an : nat -> R) (k : nat), (exists (s : R) , (Un_cv (sum_f_R0 an) s)) <-> (exists (s : R), (Un_cv (sum_f_R0 (fun (n : nat) => an (n + k)%nat)) s)).
Proof.
move=> an.
elim.
suff: (an = (fun n : nat => an (n + 0)%nat)).
move=> H1.
rewrite - H1.
apply conj.
apply.
apply.
apply functional_extensionality.
move=> n.
rewrite plus_0_r.
reflexivity.
move=> k H1.
apply conj.
elim.
move=> s H2.
exists (s - sum_f_R0 an k).
apply SumShiftUnR.
apply H2.
elim.
move=> s H2.
exists (s + sum_f_R0 an k).
apply (proj2 (SumShiftUnR an (s + sum_f_R0 an k) k)).
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
apply H2.
Qed.

Lemma SumShiftUnRn : forall (N : nat) (an : nat -> Rn N) (s : Rn N) (k : nat), (Un_cv_met (Rn_met N) (sum_f_Rn N an) s) <-> (Un_cv_met (Rn_met N) (sum_f_Rn N (fun (n : nat) => an (n + (S k))%nat)) (Rnminus N s (sum_f_Rn N an k))).
Proof.
move=> N an s k.
suff: (forall (m : nat), Rnplus N (sum_f_Rn N an k) (sum_f_Rn N (fun n : nat => an (n + S k)%nat) m) = sum_f_Rn N an (m + S k)).
move=> H1.
apply conj.
move=> H2 eps H3.
elim (H2 eps H3).
move=> M H4.
exists M.
move=> n H5.
unfold dist.
unfold Rn_met.
unfold Rn_dist.
unfold Rnminus.
suff: ((Rnopp N (Rnplus N s (Rnopp N (sum_f_Rn N an k)))) = Vopp Rfield (RnVS N) (Vadd Rfield (RnVS N) s (Rnopp N (sum_f_Rn N an k)))).
move=> H6.
rewrite H6.
rewrite Vopp_add_distr.
rewrite Vopp_involutive.
simpl.
rewrite (Rnplus_comm N (Rnopp N s) (sum_f_Rn N an k)).
rewrite - Rnplus_assoc.
rewrite (Rnplus_comm N (sum_f_Rn N (fun n0 : nat => an (n0 + S k)%nat) n) (sum_f_Rn N an k)).
rewrite (H1 n).
apply (H4 (n + S k)%nat).
apply (le_trans M n (n + S k)).
apply H5.
rewrite - {1} (plus_0_r n).
apply plus_le_compat_l.
apply le_0_n.
reflexivity.
move=> H2 eps H3.
elim (H2 eps H3).
move=> M H4.
exists (M + S k)%nat.
move=> n H5.
suff: (n = n - (S k) + (S k))%nat.
move=> H6.
rewrite H6.
rewrite - H1.
unfold dist.
unfold Rn_met.
unfold Rn_dist.
unfold Rnminus.
rewrite Rnplus_assoc.
rewrite Rnplus_comm.
rewrite Rnplus_assoc.
rewrite - (Vopp_involutive Rfield (RnVS N) (sum_f_Rn N an k)).
suff: ((Rnplus N (Rnopp N s) (Vopp Rfield (RnVS N) (Vopp Rfield (RnVS N) (sum_f_Rn N an k)))) = Vadd Rfield (RnVS N) (Vopp Rfield (RnVS N) s) (Vopp Rfield (RnVS N) (Vopp Rfield (RnVS N) (sum_f_Rn N an k)))).
move=> H7.
rewrite H7.
rewrite - Vopp_add_distr.
apply H4.
rewrite H6 in H5.
apply (plus_le_reg_l M (n - S k)%nat (S k)).
rewrite plus_comm.
rewrite (plus_comm (S k) (n - S k)).
apply H5.
reflexivity.
rewrite plus_comm.
rewrite le_plus_minus_r.
reflexivity.
apply (le_trans (S k) (M + S k) n).
rewrite - {1} (plus_0_l (S k)).
apply plus_le_compat_r.
apply le_0_n.
apply H5.
move=> m.
suff: (sum_f_Rn N (fun n : nat => an (n + S k)%nat) m = sigma_Rn N an (S k) (m + S k)).
move=> H1.
rewrite H1.
rewrite MySumEqsum_f_Rn.
rewrite MySumEqsum_f_Rn.
rewrite MySumEqsigma_Rn.
suff: (Rnplus N (MySumF2 nat (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= k)%nat) (natSectionFinite 0 k)) (RnPCM N) an) (MySumF2 nat (exist (Finite nat) (fun m0 : nat => (S k <= m0 <= m + S k)%nat) (natSectionFinite (S k) (m + S k))) (RnPCM N) an) = CMc (RnPCM N) (MySumF2 nat (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= k)%nat) (natSectionFinite 0 k)) (RnPCM N) an) (MySumF2 nat (exist (Finite nat) (fun m0 : nat => (S k <= m0 <= m + S k)%nat) (natSectionFinite (S k) (m + S k))) (RnPCM N) an)).
move=> H2.
rewrite H2.
rewrite - MySumF2Union.
suff: ((FiniteUnion nat (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= k)%nat) (natSectionFinite 0 k)) (exist (Finite nat) (fun m0 : nat => (S k <= m0 <= m + S k)%nat) (natSectionFinite (S k) (m + S k)))) = (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= m + S k)%nat) (natSectionFinite 0 (m + S k)))).
move=> H3.
rewrite H3.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> n H3.
elim H3.
move=> n1 H4.
apply conj.
apply H4.
apply (le_trans n1 k (m + S k))%nat.
apply H4.
apply lt_le_weak.
rewrite /lt.
rewrite - {1} (plus_0_l (S k)).
apply plus_le_compat_r.
apply le_0_n.
move=> n1 H4.
apply conj.
apply le_0_n.
apply H4.
move=> n H3.
elim (le_or_lt n k).
move=> H4.
left.
apply conj.
apply le_0_n.
apply H4.
move=> H4.
right.
apply conj.
apply H4.
apply H3.
move=> n.
simpl.
move=> H3 H4.
apply (lt_not_le k n).
apply H3.
apply H4.
reflexivity.
rewrite - {1} (plus_0_l (S k)).
apply plus_le_compat_r.
apply le_0_n.
unfold sigma_Rn.
rewrite plus_comm.
rewrite minus_plus.
suff: ((fun n : nat => an (n + S k)%nat) = (fun n : nat => an (S k + n)%nat)).
move=> H1.
rewrite H1.
reflexivity.
apply functional_extensionality.
move=> n.
rewrite (plus_comm n (S k)).
reflexivity.
Qed.

Lemma SumShiftUnRn2 : forall (N : nat) (an : nat -> Rn N) (k : nat), (exists (s : Rn N) , (Un_cv_met (Rn_met N) (sum_f_Rn N an) s)) <-> (exists (s : Rn N), (Un_cv_met (Rn_met N) (sum_f_Rn N (fun (n : nat) => an (n + k)%nat)) s)).
Proof.
move=> N an.
elim.
suff: (an = (fun n : nat => an (n + 0)%nat)).
move=> H1.
rewrite - H1.
apply conj.
apply.
apply.
apply functional_extensionality.
move=> n.
rewrite plus_0_r.
reflexivity.
move=> k H1.
apply conj.
elim.
move=> s H2.
exists (Rnminus N s (sum_f_Rn N an k)).
apply SumShiftUnRn.
apply H2.
elim.
move=> s H2.
exists (Rnplus N s (sum_f_Rn N an k)).
apply (proj2 (SumShiftUnRn N an (Rnplus N s (sum_f_Rn N an k)) k)).
unfold Rnminus.
rewrite Rnplus_assoc.
rewrite Rnplus_opp_r.
rewrite Rnplus_comm.
rewrite Rnplus_O_l.
apply H2.
Qed.

Lemma Theorem_5_6_1_1 : forall (an : nat -> R), (NarrowPositiveSequence an) -> (exists (k : R), 0 < k < 1 /\ (exists (n0 : nat),forall (n : nat), (n >= n0)%nat -> (an (S n)) / (an n) <= k)) -> (exists (s : R), Un_cv (sum_f_R0 an) s).
Proof.
move=> an H1 H2.
elim H2.
move=> k H3.
elim (proj2 H3).
move=> n0 H4.
apply (proj2 (SumShiftUnR2 an n0)).
apply (Theorem_5_5_3 (fun n : nat => an (n + n0)%nat) (pow k)).
move=> n.
apply H1.
elim.
apply Rlt_0_1.
move=> n H5.
apply Rmult_gt_0_compat.
apply H3.
apply H5.
move=> n.
simpl.
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
apply H4.
rewrite - {2} (plus_0_l n0).
apply plus_le_compat_r.
apply le_0_n.
apply Rgt_not_eq.
elim n.
apply Rlt_0_1.
move=> n1 H5.
apply Rmult_gt_0_compat.
apply H3.
apply H5.
exists (1 / (1 - k)).
apply Example_5_2.
rewrite Rabs_right.
apply H3.
apply Rgt_ge.
apply H3.
Qed.

Lemma GeometricProgressionSumRUnInf : forall (k : R), (k >= 1) -> Un_inf (sum_f_R0 (pow k)).
Proof.
move=> k H1.
apply (Theorem_5_5_2 (pow k) (fun (n : nat) => 1)).
apply NarrowPositiveSequenceWeak.
elim.
apply Rlt_0_1.
move=> n H2.
apply Rmult_gt_0_compat.
apply (Rlt_le_trans 0 1 k).
apply Rlt_0_1.
apply Rge_le.
apply H1.
apply H2.
move=> n.
apply Rgt_ge.
apply Rlt_0_1.
elim.
apply Req_ge.
reflexivity.
move=> n H2.
rewrite - (Rmult_1_l 1).
apply (Rmult_ge_compat k 1 (k ^ n) 1).
apply Rgt_ge.
apply Rlt_0_1.
apply Rgt_ge.
apply Rlt_0_1.
apply H1.
apply H2.
suff: (sum_f_R0 (fun _ : nat => 1) = (fun (n : nat) => INR (S n))).
move=> H2.
rewrite H2.
move=> M.
elim (Formula_3_7 M).
move=> K H3.
exists K.
move=> n H4.
apply (H3 (S n)).
apply le_S.
apply H4.
apply functional_extensionality.
elim.
reflexivity.
move=> n H2.
simpl.
rewrite H2.
reflexivity.
Qed.

Lemma SumShiftUninfR : forall (an : nat -> R) (k : nat), (Un_inf (sum_f_R0 an)) <-> (Un_inf (sum_f_R0 (fun (n : nat) => an (n + k)%nat))).
Proof.
move=> an.
elim.
suff: (an = (fun n : nat => an (n + 0)%nat)).
move=> H1.
rewrite - H1.
apply conj.
apply.
apply.
apply functional_extensionality.
move=> n.
rewrite plus_0_r.
reflexivity.
move=> k H11.
suff: (forall (m : nat), (sum_f_R0 an k) + (sum_f_R0 (fun n : nat => an (n + S k)%nat) m) = sum_f_R0 an (m + S k)).
move=> H1.
apply conj.
move=> H2 L.
elim (H2 (sum_f_R0 an k + L)).
move=> M H4.
exists M.
move=> n H5.
apply (Rplus_lt_reg_l (sum_f_R0 an k)).
rewrite (H1 n).
apply (H4 (n + S k)%nat).
apply (le_trans M n (n + S k)).
apply H5.
rewrite - {1} (plus_0_r n).
apply plus_le_compat_l.
apply le_0_n.
move=> H2 L.
elim (H2 (- sum_f_R0 an k + L)).
move=> M H4.
exists (M + S k)%nat.
move=> n H5.
suff: (n = n - (S k) + (S k))%nat.
move=> H6.
rewrite H6.
rewrite - H1.
apply (Rplus_lt_reg_l (- sum_f_R0 an k)).
rewrite - Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
apply H4.
rewrite H6 in H5.
apply (plus_le_reg_l M (n - S k)%nat (S k)).
rewrite plus_comm.
rewrite (plus_comm (S k) (n - S k)).
apply H5.
rewrite plus_comm.
rewrite le_plus_minus_r.
reflexivity.
apply (le_trans (S k) (M + S k) n).
rewrite - {1} (plus_0_l (S k)).
apply plus_le_compat_r.
apply le_0_n.
apply H5.
move=> m.
suff: (sum_f_R0 (fun n : nat => an (n + S k)%nat) m = sigma an (S k) (m + S k)).
move=> H1.
rewrite H1.
rewrite MySumEqsum_f_R0.
rewrite MySumEqsum_f_R0.
rewrite MySumEqsigma.
suff: (MySumF2 nat (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= k)%nat) (natSectionFinite 0 k)) RPCM an + MySumF2 nat (exist (Finite nat) (fun m0 : nat => (S k <= m0 <= m + S k)%nat) (natSectionFinite (S k) (m + S k))) RPCM an = CMc RPCM (MySumF2 nat (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= k)%nat) (natSectionFinite 0 k)) RPCM an) (MySumF2 nat (exist (Finite nat) (fun m0 : nat => (S k <= m0 <= m + S k)%nat) (natSectionFinite (S k) (m + S k))) RPCM an)).
move=> H2.
rewrite H2.
rewrite - MySumF2Union.
suff: ((FiniteUnion nat (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= k)%nat) (natSectionFinite 0 k)) (exist (Finite nat) (fun m0 : nat => (S k <= m0 <= m + S k)%nat) (natSectionFinite (S k) (m + S k)))) = (exist (Finite nat) (fun m0 : nat => (0 <= m0 <= m + S k)%nat) (natSectionFinite 0 (m + S k)))).
move=> H3.
rewrite H3.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> n H3.
elim H3.
move=> n1 H4.
apply conj.
apply H4.
apply (le_trans n1 k (m + S k))%nat.
apply H4.
apply lt_le_weak.
rewrite /lt.
rewrite - {1} (plus_0_l (S k)).
apply plus_le_compat_r.
apply le_0_n.
move=> n1 H4.
apply conj.
apply le_0_n.
apply H4.
move=> n H3.
elim (le_or_lt n k).
move=> H4.
left.
apply conj.
apply le_0_n.
apply H4.
move=> H4.
right.
apply conj.
apply H4.
apply H3.
move=> n.
simpl.
move=> H3 H4.
apply (lt_not_le k n).
apply H3.
apply H4.
reflexivity.
rewrite - {1} (plus_0_l (S k)).
apply plus_le_compat_r.
apply le_0_n.
unfold sigma.
rewrite plus_comm.
rewrite minus_plus.
suff: ((fun n : nat => an (n + S k)%nat) = (fun n : nat => an (S k + n)%nat)).
move=> H1.
rewrite H1.
reflexivity.
apply functional_extensionality.
move=> n.
rewrite (plus_comm n (S k)).
reflexivity.
Qed.

Lemma Theorem_5_6_2_1 : forall (an : nat -> R), (NarrowPositiveSequence an) -> (exists (k : R), k > 1 /\ (exists (n0 : nat),forall (n : nat), (n >= n0)%nat -> (an (S n)) / (an n) >= k)) -> (Un_inf (sum_f_R0 an)).
Proof.
move=> an H1 H2.
elim H2.
move=> k H3.
elim (proj2 H3).
move=> n0 H4.
apply (proj2 (SumShiftUninfR an n0)).
apply (Theorem_5_5_4 (fun n : nat => an (n + n0)%nat) (pow k)).
move=> n.
apply H1.
elim.
apply Rlt_0_1.
move=> n H5.
apply Rmult_gt_0_compat.
apply (Rlt_trans 0 1 k).
apply Rlt_0_1.
apply H3.
apply H5.
move=> n.
simpl.
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
apply H4.
rewrite - {2} (plus_0_l n0).
apply plus_le_compat_r.
apply le_0_n.
apply Rgt_not_eq.
elim n.
apply Rlt_0_1.
move=> n1 H5.
apply Rmult_gt_0_compat.
apply (Rlt_trans 0 1 k).
apply Rlt_0_1.
apply H3.
apply H5.
apply GeometricProgressionSumRUnInf.
apply Rgt_ge.
apply H3.
Qed.

Lemma Theorem_5_7_1 : forall (an : nat -> R), (NarrowPositiveSequence an) -> (exists (k : R), (k < 1) /\ (Un_cv (fun (n : nat) => an (S n) / an n) k)) -> (exists (s : R), Un_cv (sum_f_R0 an) s).
Proof.
move=> an H1 H2.
apply (Theorem_5_6_1_1 an).
apply H1.
elim H2.
move=> k H3.
exists (k + (1 - k) / 2).
apply conj.
apply conj.
apply (Rle_lt_trans 0 k (k + (1 - k) / 2)).
apply (Theorem_2_6 (fun (n : nat) => 0) (fun (n : nat) => an (S n) / an n) 0 k).
move=> eps H4.
exists O.
move=> n H5.
rewrite R_dist_eq.
apply H4.
apply H3.
move=> n.
apply Rlt_le.
apply Rmult_lt_0_compat.
apply H1.
apply Rinv_0_lt_compat.
apply H1.
rewrite - {1} (Rplus_0_r k).
apply Rplus_lt_compat_l.
apply eps2_Rgt_R0.
apply Rgt_minus.
apply H3.
rewrite - {2} (Rplus_0_l 1).
rewrite - (Rplus_opp_r k).
rewrite Rplus_assoc.
apply Rplus_lt_compat_l.
rewrite Rplus_comm.
rewrite - (Rplus_0_r ((1 - k) / 2)).
rewrite - (eps2 (1 + - k)).
apply Rplus_lt_compat_l.
apply eps2_Rgt_R0.
apply Rgt_minus.
apply H3.
elim (proj2 H3 ((1 - k) / 2)).
move=> M H4.
exists M.
move=> n H5.
apply (Rplus_le_reg_l (- k)).
rewrite - Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
rewrite Rplus_comm.
apply (Rle_trans (an (S n) / an n + - k) (Rabs (an (S n) / an n + - k)) ((1 - k) / 2)).
apply Rle_abs.
apply Rlt_le.
apply H4.
apply H5.
apply eps2_Rgt_R0.
apply Rgt_minus.
apply H3.
Qed.

Lemma Theorem_5_7_2 : forall (an : nat -> R), (NarrowPositiveSequence an) -> (exists (k : R), (k > 1) /\ (Un_cv (fun (n : nat) => an (S n) / an n) k)) -> (Un_inf (sum_f_R0 an)).
Proof.
move=> an H1 H2.
apply (Theorem_5_6_2_1 an).
apply H1.
elim H2.
move=> k H3.
exists (k - (k - 1) / 2).
apply conj.
rewrite - {2} (Rplus_0_l 1).
rewrite - (Rplus_opp_r k).
rewrite Rplus_assoc.
rewrite - {2} (Ropp_involutive 1).
rewrite - Ropp_plus_distr.
apply Rplus_lt_compat_l.
apply Ropp_lt_contravar.
rewrite - (Rplus_0_r ((k - 1) / 2)).
rewrite - (eps2 (k + - (1))).
apply Rplus_lt_compat_l.
apply eps2_Rgt_R0.
apply Rgt_minus.
apply H3.
elim (proj2 H3 ((k - 1) / 2)).
move=> M H4.
exists M.
move=> n H5.
apply (Rplus_ge_reg_l (- k)).
rewrite - Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
rewrite Rplus_comm.
rewrite - (Ropp_involutive (an (S n) / an n + - k)).
apply Ropp_ge_contravar.
apply (Rge_trans ((k - 1) / 2) (Rabs (an (S n) / an n + - k)) (- (an (S n) / an n + - k))).
apply Rgt_ge.
apply H4.
apply H5.
rewrite - Rabs_Ropp.
apply Rle_ge.
apply Rle_abs.
apply eps2_Rgt_R0.
apply Rgt_minus.
apply H3.
Qed.

Lemma Theorem_5_7_3 : forall (an : nat -> R), (NarrowPositiveSequence an) -> (Un_inf (fun (n : nat) => an (S n) / an n)) -> (Un_inf (sum_f_R0 an)).
Proof.
move=> an H1 H2.
apply (Theorem_5_6_2_1 an).
apply H1.
exists 2.
apply conj.
rewrite - (Rplus_0_r 1).
rewrite /2.
rewrite - INR_IPR.
simpl.
apply Rplus_lt_compat_l.
apply Rlt_0_1.
elim (H2 2).
move=> M H3.
exists M.
move=> n H4.
apply Rgt_ge.
apply (H3 n H4).
Qed.

Definition AbsoluteConvergenceR (an : nat -> R) := (exists (s : R), (Un_cv (sum_f_R0 (fun (m : nat) => Rabs (an m))) s)).

Definition AbsoluteConvergenceRn (N : nat) (an : nat -> Rn N) := (exists s : R, Un_cv (sum_f_R0 (fun m : nat => RnNorm N (an m))) s).

Lemma Theorem_5_8_1 : forall (an bn : nat -> R), (AbsoluteConvergenceR an) -> (AbsoluteConvergenceR bn) -> (AbsoluteConvergenceR (fun (n : nat) => sum_f_R0 (fun (m : nat) => an m * bn (n - m)%nat) n)).
Proof.
move=> an bn H1 H2.
suff: (PositiveSequence (fun m : nat => Rabs (an m))).
move=> H3.
suff: (PositiveSequence (fun m : nat => Rabs (bn m))).
move=> H4.
apply Theorem_5_4.
move=> m.
apply Rle_ge.
apply Rabs_pos.
elim (proj1 (bounded_abs (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (an m))))) (proj1 (Theorem_5_4 (fun (m : nat) => Rabs (an m)) H3) H1)).
move=> a H5.
elim (proj1 (bounded_abs (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (bn m))))) (proj1 (Theorem_5_4 (fun (m : nat) => Rabs (bn m)) H4) H2)).
move=> b H6.
apply bounded_abs.
exists (a * b).
move=> r0 H7.
elim H7.
move=> r1 H8 r2 H9.
rewrite H9.
elim H8.
move=> n H10 r3 H11.
rewrite H11.
rewrite MySumEqsum_f_R0.
rewrite Rabs_pos_eq.
suff: ((MySumF2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 * bn (m - m0)%nat) m))) <= (MySumF2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun m : nat => MySumF2 nat (exist (Finite nat) (fun k : nat => (0 <= k <= m)%nat) (natSectionFinite 0 m)) RPCM ((fun m m0 : nat => Rabs (an m0) * Rabs (bn (m - m0)%nat)) m)))).
move=> H12.
apply (Rle_trans (MySumF2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 * bn (m - m0)%nat) m))) (MySumF2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun m : nat => MySumF2 nat (exist (Finite nat) (fun k : nat => (0 <= k <= m)%nat) (natSectionFinite 0 m)) RPCM (fun m0 : nat => Rabs (an m0) * Rabs (bn (m - m0)%nat)))) (a * b)).
apply H12.
suff: (Finite (nat * nat) (fun (uv : (nat * nat)) => (fst uv + snd uv <= n)%nat)).
move=> H13.
suff: ((exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) = (FiniteIm (nat * nat) nat (fun (nm : (nat * nat)) => (fst nm + snd nm) % nat) (exist (Finite (nat * nat)) (fun (uv : (nat * nat)) => (fst uv + snd uv <= n)%nat) H13))).
move=> H14.
rewrite H14.
suff: (MySumF2 nat (FiniteIm (nat * nat) nat (fun nm : nat * nat => (fst nm + snd nm)%nat) (exist (Finite (nat * nat)) (fun uv : nat * nat => (fst uv + snd uv <= n)%nat) H13)) RPCM (fun m : nat => MySumF2 nat (exist (Finite nat) (fun k : nat => (0 <= k <= m)%nat) (natSectionFinite 0 m)) RPCM (fun m0 : nat => Rabs (an m0) * Rabs (bn (m - m0)%nat))) = MySumF2 nat (FiniteIm (nat * nat) nat (fun nm : nat * nat => (fst nm + snd nm)%nat) (exist (Finite (nat * nat)) (fun uv : nat * nat => (fst uv + snd uv <= n)%nat) H13)) RPCM (fun m : nat => MySumF2 (nat * nat) (FiniteIntersection (nat * nat) (exist (Finite (nat * nat)) (fun (uv : (nat * nat)) => (fst uv + snd uv <= n)%nat) H13) (fun u1 : (nat * nat) => (fst u1 + snd u1)%nat = m)) RPCM (fun m0 : (nat * nat) => Rabs (an (fst m0)) * Rabs (bn (snd m0))))).
move=> H15.
rewrite H15.
rewrite - MySumF2ImageSum.
apply (Rle_trans (MySumF2 (nat * nat) (exist (Finite (nat * nat)) (fun uv : nat * nat => (fst uv + snd uv <= n)%nat) H13) RPCM (fun m0 : nat * nat => Rabs (an (fst m0)) * Rabs (bn (snd m0)))) (MySumF2 (nat * nat) (FinitePair nat nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n))) RPCM (fun m0 : nat * nat => Rabs (an (fst m0)) * Rabs (bn (snd m0)))) (a * b)).
rewrite (MySumF2Excluded (nat * nat) RPCM (fun m0 : nat * nat => Rabs (an (fst m0)) * Rabs (bn (snd m0))) (FinitePair nat nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n))) (fun uv : nat * nat => (fst uv + snd uv <= n)%nat)).
rewrite - (Rplus_0_r (MySumF2 (nat * nat) (exist (Finite (nat * nat)) (fun uv : nat * nat => (fst uv + snd uv <= n)%nat) H13) RPCM (fun m0 : nat * nat => Rabs (an (fst m0)) * Rabs (bn (snd m0))))).
suff: ((FiniteIntersection (nat * nat) (FinitePair nat nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n))) (fun uv : nat * nat => (fst uv + snd uv <= n)%nat)) = (exist (Finite (nat * nat)) (fun uv : nat * nat => (fst uv + snd uv <= n)%nat) H13)).
move=> H16.
rewrite H16.
apply Rplus_le_compat_l.
apply MySumF2Induction.
apply conj.
apply Req_le.
reflexivity.
move=> cm u H17 H18.
rewrite - (Rplus_0_l 0).
apply Rplus_le_compat.
apply H18.
rewrite - (Rmult_0_l 0).
apply Rmult_le_compat.
apply Req_le.
reflexivity.
apply Req_le.
reflexivity.
apply Rabs_pos.
apply Rabs_pos.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> uv.
elim.
move=> uv1 H16 H17.
apply H16.
move=> uv H16.
apply Intersection_intro.
apply H16.
apply conj.
apply conj.
apply le_0_n.
apply (le_trans (fst uv) (fst uv + snd uv) n).
rewrite - {1} (plus_0_r (fst uv)).
apply plus_le_compat_l.
apply le_0_n.
apply H16.
apply conj.
apply le_0_n.
apply (le_trans (snd uv) (fst uv + snd uv) n).
rewrite - {1} (plus_0_l (snd uv)).
apply plus_le_compat_r.
apply le_0_n.
apply H16.
rewrite (MySumF2Pair nat nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun m1 m2 : nat => Rabs (an m1) * Rabs (bn m2))).
suff: ((fun u : nat => MySumF2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun m2 : nat => Rabs (an u) * Rabs (bn m2))) = (fun u : nat => MySumF2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun m2 : nat => Rabs (bn m2)) * Rabs (an u))).
move=> H16.
rewrite H16.
rewrite MySumF2R_mult.
rewrite Rmult_comm.
apply Rmult_le_compat.
apply MySumF2Induction.
apply conj.
apply Req_le.
reflexivity.
move=> cm u H17 H18.
rewrite - (Rplus_0_l 0).
apply Rplus_le_compat.
apply H18.
apply Rabs_pos.
apply MySumF2Induction.
apply conj.
apply Req_le.
reflexivity.
move=> cm u H17 H18.
rewrite - (Rplus_0_l 0).
apply Rplus_le_compat.
apply H18.
apply Rabs_pos.
rewrite - MySumEqsum_f_R0.
apply H5.
apply (Im_intro R R (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (an m)))) Rabs ((sum_f_R0 (fun n0 : nat => Rabs (an n0)) n))).
apply (Im_intro nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (an m))) n).
apply Full_intro.
reflexivity.
rewrite Rabs_pos_eq.
reflexivity.
rewrite MySumEqsum_f_R0.
apply MySumF2Induction.
apply conj.
apply Req_le.
reflexivity.
move=> cm u H17 H18.
rewrite - (Rplus_0_l 0).
apply Rplus_le_compat.
apply H18.
apply Rabs_pos.
rewrite - MySumEqsum_f_R0.
apply H6.
apply (Im_intro R R (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (bn m)))) Rabs ((sum_f_R0 (fun n0 : nat => Rabs (bn n0)) n))).
apply (Im_intro nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (bn m))) n).
apply Full_intro.
reflexivity.
rewrite Rabs_pos_eq.
reflexivity.
rewrite MySumEqsum_f_R0.
apply MySumF2Induction.
apply conj.
apply Req_le.
reflexivity.
move=> cm u H17 H18.
rewrite - (Rplus_0_l 0).
apply Rplus_le_compat.
apply H18.
apply Rabs_pos.
apply functional_extensionality.
move=> u.
rewrite Rmult_comm.
apply MySumF2R_mult.
apply MySumF2Same.
move=> u H20.
suff: (MySumF2 (nat * nat) (FiniteIntersection (nat * nat) (exist (Finite (nat * nat)) (fun uv : nat * nat => (fst uv + snd uv <= n)%nat) H13) (fun u1 : nat * nat => (fst u1 + snd u1)%nat = u)) RPCM (fun m0 : nat * nat => Rabs (an (fst m0)) * Rabs (bn (snd m0))) = MySumF2 (nat * nat) (FiniteIntersection (nat * nat) (exist (Finite (nat * nat)) (fun uv : nat * nat => (fst uv + snd uv <= n)%nat) H13) (fun u1 : nat * nat => (fst u1 + snd u1)%nat = u)) RPCM (fun m0 : nat * nat => Rabs (an (fst m0)) * Rabs (bn (u - fst m0)%nat))).
move=> H15.
rewrite H15.
suff: (forall (nm : (nat * nat)), proj1_sig (FiniteIntersection (nat * nat) (exist (Finite (nat * nat)) (fun uv : nat * nat => (fst uv + snd uv <= n)%nat) H13) (fun u1 : nat * nat => (fst u1 + snd u1)%nat = u)) nm -> proj1_sig (exist (Finite nat) (fun k : nat => (0 <= k <= u)%nat) (natSectionFinite 0 u)) (fst nm)).
move=> H16.
rewrite (MySumF2BijectiveSame (nat * nat) (FiniteIntersection (nat * nat) (exist (Finite (nat * nat)) (fun uv : nat * nat => (fst uv + snd uv <= n)%nat) H13) (fun u1 : nat * nat => (fst u1 + snd u1)%nat = u)) nat (exist (Finite nat) (fun k : nat => (0 <= k <= u)%nat) (natSectionFinite 0 u)) RPCM (fun m0 : nat => Rabs (an m0) * Rabs (bn (u - m0)%nat)) fst).
reflexivity.
simpl.
suff: (forall (m : {u0 : nat | (0 <= u0 <= u)%nat}), Intersection (nat * nat) (fun u1 : nat * nat => (fst u1 + snd u1)%nat = u) (fun uv : nat * nat => (fst uv + snd uv <= n)%nat) (proj1_sig m , (u - proj1_sig m)%nat)).
move=> H17.
exists (fun (m : {u0 : nat | (0 <= u0 <= u)%nat}) => exist (Intersection (nat * nat) (fun u1 : nat * nat => (fst u1 + snd u1)%nat = u) (fun uv : nat * nat => (fst uv + snd uv <= n)%nat)) (proj1_sig m , (u - proj1_sig m)%nat) (H17 m)).
apply conj.
move=> x.
apply sig_map.
simpl.
suff: ((u - fst (proj1_sig x))%nat = snd (proj1_sig x)).
move=> H18.
rewrite H18.
rewrite (surjective_pairing (proj1_sig x)).
reflexivity.
apply (plus_reg_l (u - fst (proj1_sig x))%nat (snd (proj1_sig x)) (fst (proj1_sig x))).
elim (proj2_sig x).
move=> nm H18 H19.
rewrite H18.
apply le_plus_minus_r.
rewrite - (plus_0_r (fst nm)).
rewrite - H18.
apply plus_le_compat_l.
apply le_0_n.
move=> m.
apply sig_map.
reflexivity.
move=> m.
apply Intersection_intro.
apply le_plus_minus_r.
apply (proj2_sig m).
simpl.
simpl in H20.
unfold In.
simpl.
rewrite le_plus_minus_r.
elim H20.
move=> nm H17 y H18.
rewrite H18.
apply H17.
apply (proj2_sig m).
move=> nm.
simpl.
move=> H16.
apply conj.
apply le_0_n.
elim H16.
move=> nm1 H17 H18.
rewrite - (plus_0_r (fst nm1)).
rewrite - H17.
apply plus_le_compat_l.
apply le_0_n.
apply MySumF2Same.
move=> nm.
simpl.
move=> H15.
elim H15.
move=> nm1 H16 H17.
rewrite - H16.
rewrite minus_plus.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> m H14.
apply (Im_intro (nat * nat) nat (fun uv : nat * nat => (fst uv + snd uv <= n)%nat) (fun nm : nat * nat => (fst nm + snd nm)%nat) (O , m)).
unfold In.
rewrite plus_0_l.
apply H14.
rewrite plus_0_l.
reflexivity.
move=> m.
elim.
move=> nm H14 y H15.
rewrite H15.
apply conj.
apply le_0_n.
apply H14.
apply (Finite_downward_closed (nat * nat) (fun uv : nat * nat => (0 <= fst uv <= n)%nat /\ (0 <= snd uv <= n)%nat)).
apply (FinitePairFinite nat nat (fun u : nat => (0 <= u <= n)%nat) (fun u : nat => (0 <= u <= n)%nat)).
apply natSectionFinite.
apply natSectionFinite.
move=> uv H13.
apply conj.
apply conj.
apply le_0_n.
apply (le_trans (fst uv) (fst uv + snd uv) n).
rewrite - {1} (plus_0_r (fst uv)).
apply plus_le_compat_l.
apply le_0_n.
apply H13.
apply conj.
apply le_0_n.
apply (le_trans (snd uv) (fst uv + snd uv) n).
rewrite - {1} (plus_0_l (snd uv)).
apply plus_le_compat_r.
apply le_0_n.
apply H13.
apply (FiniteSetInduction nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply Req_le.
reflexivity.
move=> B b0 H12 H13 H14 H15.
rewrite MySumF2Add.
rewrite MySumF2Add.
apply Rplus_le_compat.
apply H15.
rewrite MySumEqsum_f_R0.
suff: ((fun m0 : nat => Rabs (an m0) * Rabs (bn (b0 - m0)%nat)) = (fun m0 : nat => Rabs ((an m0) * (bn (b0 - m0)%nat)))).
move=> H16.
rewrite H16.
apply MySumF2Rtriangle.
apply functional_extensionality.
move=> m0.
rewrite Rabs_mult.
reflexivity.
apply H14.
apply H14.
apply MySumF2Induction.
apply conj.
apply Req_le.
reflexivity.
move=> cm u H12 H13.
rewrite - (Rplus_0_r 0).
apply Rplus_le_compat.
apply H13.
apply Rabs_pos.
move=> m.
apply Rle_ge.
apply Rabs_pos.
move=> m.
apply Rle_ge.
apply Rabs_pos.
Qed.

Lemma Theorem_5_8_2 : forall (an bn : nat -> R) (a b : R), (AbsoluteConvergenceR an) -> (AbsoluteConvergenceR bn) -> (Un_cv (sum_f_R0 an) a) -> (Un_cv (sum_f_R0 bn) b) -> (Un_cv (sum_f_R0 (fun (n : nat) => sum_f_R0 (fun (m : nat) => an m * bn (n - m)%nat) n)) (a * b)).
Proof.
move=> an bn a b H1 H2 H3 H4.
suff: (forall (eps : R), eps > 0 -> exists (M : nat),forall (n : nat), (n >= M)%nat -> (Rabs (((sum_f_R0 (fun n : nat => sum_f_R0 (fun m : nat => an m * bn (n - m)%nat) n)) (n + n)%nat) - ((sum_f_R0 an n) * (sum_f_R0 bn n))) < eps)).
move=> H5 eps H6.
elim (proj1 (Theorem_3_6 (sum_f_R0 (fun n : nat => sum_f_R0 (fun m : nat => an m * bn (n - m)%nat) n))) (Theorem_5_2_R (fun (n : nat) => sum_f_R0 (fun (m : nat) => an m * bn (n - m)%nat) n) (Theorem_5_8_1 an bn H1 H2)) (eps * / 2 * / 2)).
move=> M1 H7.
elim (H5 (eps * / 2 * / 2)).
move=> M2 H8.
elim (Theorem_2_5_1_mult (sum_f_R0 an) (sum_f_R0 bn) a b H3 H4 (eps * / 2)).
move=> M3 H9.
exists (max M1 (max M2 M3)).
move=> n H10.
unfold R_dist.
suff: ((sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) n - a * b) = (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) n - sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n)) + (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n) - sum_f_R0 an n * sum_f_R0 bn n) + (sum_f_R0 an n * sum_f_R0 bn n - a * b)).
move=> H11.
rewrite H11.
apply (Rle_lt_trans (Rabs (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) n - sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n) + (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n) - sum_f_R0 an n * sum_f_R0 bn n) + (sum_f_R0 an n * sum_f_R0 bn n - a * b))) (Rabs (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) n - sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n) + (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n) - sum_f_R0 an n * sum_f_R0 bn n)) + Rabs (sum_f_R0 an n * sum_f_R0 bn n - a * b)) eps).
apply Rabs_triang.
apply (Rle_lt_trans (Rabs (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) n - sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n) + (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n) - sum_f_R0 an n * sum_f_R0 bn n)) + Rabs (sum_f_R0 an n * sum_f_R0 bn n - a * b)) (Rabs (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) n - sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n)) + Rabs (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n) - sum_f_R0 an n * sum_f_R0 bn n) + Rabs (sum_f_R0 an n * sum_f_R0 bn n - a * b)) eps).
apply Rplus_le_compat_r.
apply Rabs_triang.
rewrite - (eps2 eps).
rewrite - {1} (eps2 (eps * / 2)).
apply Rplus_lt_compat.
apply Rplus_lt_compat.
apply (H7 n (n + n)%nat).
apply (le_trans M1 (max M1 (max M2 M3)) n).
apply Nat.le_max_l.
apply H10.
apply (le_trans M1 (max M1 (max M2 M3)) (n + n)%nat).
apply Nat.le_max_l.
apply (le_trans (max M1 (max M2 M3)) n (n + n)).
apply H10.
rewrite - {1} (plus_0_l n).
apply plus_le_compat_r.
apply le_0_n.
apply (H8 n).
apply (le_trans M2 (max M1 (max M2 M3)) n).
apply (le_trans M2 (max M2 M3) (max M1 (max M2 M3))).
apply Nat.le_max_l.
apply Nat.le_max_r.
apply H10.
apply (H9 n).
apply (le_trans M3 (max M1 (max M2 M3)) n).
apply (le_trans M3 (max M2 M3) (max M1 (max M2 M3))).
apply Nat.le_max_r.
apply Nat.le_max_r.
apply H10.
unfold Rminus.
rewrite - (Rplus_assoc (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) n - sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n)) (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n)) (- (sum_f_R0 an n * sum_f_R0 bn n))).
rewrite (Rplus_assoc (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) n) (- sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n)) (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n))).
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
rewrite - Rplus_assoc.
rewrite (Rplus_assoc (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) n) (- (sum_f_R0 an n * sum_f_R0 bn n)) (sum_f_R0 an n * sum_f_R0 bn n)).
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
reflexivity.
apply eps2_Rgt_R0.
apply H6.
apply eps2_Rgt_R0.
apply eps2_Rgt_R0.
apply H6.
apply eps2_Rgt_R0.
apply eps2_Rgt_R0.
apply H6.
suff: (forall (n : nat), Finite (nat * nat) (fun (nm : (nat * nat)) => (fst nm + snd nm <= n + n)%nat /\  (fst nm > n)%nat)).
move=> H5.
suff: (forall (n : nat), Finite (nat * nat) (fun (nm : (nat * nat)) => (fst nm + snd nm <= n + n)%nat /\  (snd nm > n)%nat)).
move=> H6.
suff: (forall (n : nat),(sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n) - sum_f_R0 an n * sum_f_R0 bn n) = MySumF2 (nat * nat) (FiniteUnion (nat * nat) (exist (Finite (nat * nat)) (fun (nm : (nat * nat)) => (fst nm + snd nm <= n + n)%nat /\  (fst nm > n)%nat) (H5 n)) (exist (Finite (nat * nat)) (fun (nm : (nat * nat)) => (fst nm + snd nm <= n + n)%nat /\  (snd nm > n)%nat) (H6 n))) RPCM (fun (nm : (nat * nat)) => an (fst nm) * bn (snd nm))).
move=> H7.
suff: (PositiveSequence (fun m : nat => Rabs (an m))).
move=> H8.
suff: (PositiveSequence (fun m : nat => Rabs (bn m))).
move=> H9.
elim (proj1 (bounded_abs (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (an m))))) (proj1 (Theorem_5_4 (fun m : nat => Rabs (an m)) H8) H1)).
move=> L1 H10.
elim (proj1 (bounded_abs (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (bn m))))) (proj1 (Theorem_5_4 (fun m : nat => Rabs (bn m)) H9) H2)).
move=> L2 H11.
move=> eps H12.
elim (proj1 (Theorem_5_1_R (fun m : nat => Rabs (an m))) H1 (eps * / 2 * / (1 + Rabs L2))).
move=> M1 H13.
elim (proj1 (Theorem_5_1_R (fun m : nat => Rabs (bn m))) H2 (eps * / 2 * / (1 + Rabs L1))).
move=> M2 H14.
exists (S (max M1 M2)).
move=> n H15.
rewrite (H7 n).
apply (Rle_lt_trans (Rabs (MySumF2 (nat * nat) (FiniteUnion (nat * nat) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (fst nm > n)%nat) (H5 n)) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (snd nm > n)%nat)  (H6 n))) RPCM (fun nm : nat * nat => an (fst nm) * bn (snd nm)))) (MySumF2 (nat * nat) (FiniteUnion (nat * nat) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (fst nm > n)%nat) (H5 n)) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (snd nm > n)%nat) (H6 n))) RPCM (fun nm : nat * nat => Rabs (an (fst nm) * bn (snd nm)))) eps).
apply MySumF2Rtriangle.
rewrite MySumF2Union.
rewrite - (eps2 eps).
apply Rplus_lt_compat.
apply (Rle_lt_trans (MySumF2 (nat * nat) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (fst nm > n)%nat) (H5 n)) RPCM (fun nm : nat * nat => Rabs (an (fst nm) * bn (snd nm)))) (MySumF2 (nat * nat) (FinitePair nat nat (exist (Finite nat) (fun m : nat => (S n <= m <= n + n)%nat) (natSectionFinite (S n) (n + n)%nat)) (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n))) RPCM (fun nm : nat * nat => Rabs (an (fst nm) * bn (snd nm)))) (eps * / 2)).
rewrite (MySumF2Excluded (nat * nat) RPCM (fun nm : nat * nat => Rabs (an (fst nm) * bn (snd nm))) (FinitePair nat nat (exist (Finite nat) (fun m : nat => (S n <= m <= n + n)%nat) (natSectionFinite (S n) (n + n)%nat)) (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n))) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (fst nm > n)%nat)).
rewrite - (Rplus_0_r (MySumF2 (nat * nat) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (fst nm > n)%nat) (H5 n)) RPCM (fun nm : nat * nat => Rabs (an (fst nm) * bn (snd nm))))).
suff: ((FiniteIntersection (nat * nat) (FinitePair nat nat (exist (Finite nat) (fun m : nat => (S n <= m <= n + n)%nat) (natSectionFinite (S n) (n + n)%nat)) (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n))) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (fst nm > n)%nat)) = (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (fst nm > n)%nat) (H5 n))).
move=> H16.
rewrite H16.
apply Rplus_le_compat_l.
apply MySumF2Induction.
apply conj.
apply Req_le.
reflexivity.
move=> cm u H17 H18.
apply Rplus_le_le_0_compat.
apply H18.
apply Rabs_pos.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> nm.
elim.
move=> nm1 H16 H17.
apply H16.
move=> nm H16.
apply Intersection_intro.
apply H16.
apply conj.
apply conj.
apply H16.
rewrite - (plus_0_r (fst nm)).
apply (le_trans (fst nm + 0) (fst nm + snd nm) (n + n))%nat.
apply plus_le_compat_l.
apply le_0_n.
apply H16.
apply conj.
apply le_0_n.
apply (plus_le_reg_l (snd nm) n (fst nm)).
apply (le_trans (fst nm + snd nm) (n + n) (fst nm + n))%nat.
apply H16.
apply plus_le_compat_r.
apply lt_le_weak.
apply H16.
suff: ((fun nm : nat * nat => Rabs (an (fst nm) * bn (snd nm))) = (fun nm : nat * nat => Rabs (an (fst nm)) * Rabs (bn (snd nm)))).
move=> H16.
rewrite H16.
rewrite (MySumF2Pair nat nat (exist (Finite nat) (fun m : nat => (S n <= m <= n + n)%nat) (natSectionFinite (S n) (n + n))) (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun m1 m2 : nat => Rabs (an m1) * Rabs (bn m2))).
suff: ((fun u : nat => MySumF2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun m2 : nat => Rabs (an u) * Rabs (bn m2))) = (fun u : nat => Rabs (an u) * MySumF2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun m2 : nat => Rabs (bn m2)))).
move=> H17.
rewrite H17.
suff: ((fun u : nat => Rabs (an u) * MySumF2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun m2 : nat => Rabs (bn m2))) = (fun u : nat => MySumF2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun m2 : nat => Rabs (bn m2)) * Rabs (an u))).
move=> H18.
rewrite H18.
rewrite MySumF2R_mult.
rewrite - MySumEqsum_f_R0.
rewrite - MySumEqsigma.
apply (Rle_lt_trans (sum_f_R0 (fun m2 : nat => Rabs (bn m2)) n * sigma (fun n0 : nat => Rabs (an n0)) (S n) (n + n)) (L2 * (eps * / 2 * / (1 + Rabs L2))) (eps * / 2)).
apply Rmult_le_compat.
elim n.
apply Rabs_pos.
move=> n0 H19.
simpl.
apply Rplus_le_le_0_compat.
apply H19.
apply Rabs_pos.
unfold sigma.
elim (n + n - S n)%nat.
apply Rabs_pos.
move=> n0 H19.
simpl.
apply Rplus_le_le_0_compat.
apply H19.
apply Rabs_pos.
apply H11.
apply (Im_intro R R (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (bn m)))) Rabs (sum_f_R0 (fun m2 : nat => Rabs (bn m2)) n)).
apply (Im_intro nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (bn m))) n).
apply Full_intro.
reflexivity.
rewrite Rabs_pos_eq.
reflexivity.
elim n.
apply Rabs_pos.
move=> n0 H19.
simpl.
apply Rplus_le_le_0_compat.
apply H19.
apply Rabs_pos.
apply (Rle_trans (sigma (fun n0 : nat => Rabs (an n0)) (S n) (n + n)) (Rabs (sigma (fun n0 : nat => Rabs (an n0)) (S n) (n + n))) (eps * / 2 * / (1 + Rabs L2))).
apply Rle_abs.
apply Rlt_le.
apply H13.
rewrite - {3} (plus_0_l n).
apply plus_lt_compat_r.
apply (le_trans (S 0) (S (max M1 M2)) n).
apply le_n_S.
apply le_0_n.
apply H15.
apply (le_trans M1 (S (max M1 M2)) n).
apply le_S.
apply Nat.le_max_l.
apply H15.
rewrite - Rmult_assoc.
apply (Rmult_lt_reg_r (1 + Rabs L2)).
apply (Rlt_le_trans 0 1 (1 + Rabs L2)).
apply Rlt_0_1.
rewrite - {1} (Rplus_0_r 1).
apply Rplus_le_compat_l.
apply Rabs_pos.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite Rmult_comm.
apply Rmult_gt_compat_l.
apply eps2_Rgt_R0.
apply H12.
apply (Rle_lt_trans L2 (Rabs L2) (1 + Rabs L2)).
apply Rle_abs.
rewrite - {1} (Rplus_0_l (Rabs L2)).
apply Rplus_lt_compat_r.
apply Rlt_0_1.
apply Rgt_not_eq.
apply (Rlt_le_trans 0 1 (1 + Rabs L2)).
apply Rlt_0_1.
rewrite - {1} (Rplus_0_r 1).
apply Rplus_le_compat_l.
apply Rabs_pos.
rewrite - {1} (plus_0_r n).
apply plus_lt_compat_l.
apply (le_trans (S 0) (S (max M1 M2)) n).
apply le_n_S.
apply le_0_n.
apply H15.
apply functional_extensionality.
move=> u.
apply Rmult_comm.
apply functional_extensionality.
move=> u.
apply MySumF2R_mult.
apply functional_extensionality.
move=> nm.
apply Rabs_mult.
apply (Rle_lt_trans (MySumF2 (nat * nat) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (snd nm > n)%nat) (H6 n)) RPCM (fun nm : nat * nat => Rabs (an (fst nm) * bn (snd nm)))) (MySumF2 (nat * nat) (FinitePair nat nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) (exist (Finite nat) (fun m : nat => (S n <= m <= n + n)%nat) (natSectionFinite (S n) (n + n)%nat))) RPCM (fun nm : nat * nat => Rabs (an (fst nm) * bn (snd nm)))) (eps * / 2)).
rewrite (MySumF2Excluded (nat * nat) RPCM (fun nm : nat * nat => Rabs (an (fst nm) * bn (snd nm))) (FinitePair nat nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) (exist (Finite nat) (fun m : nat => (S n <= m <= n + n)%nat) (natSectionFinite (S n) (n + n)%nat))) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (snd nm > n)%nat)).
rewrite - (Rplus_0_r (MySumF2 (nat * nat) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (snd nm > n)%nat) (H6 n)) RPCM (fun nm : nat * nat => Rabs (an (fst nm) * bn (snd nm))))).
suff: ((FiniteIntersection (nat * nat) (FinitePair nat nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) (exist (Finite nat) (fun m : nat => (S n <= m <= n + n)%nat) (natSectionFinite (S n) (n + n)%nat))) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (snd nm > n)%nat)) = (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (snd nm > n)%nat) (H6 n))).
move=> H16.
rewrite H16.
apply Rplus_le_compat_l.
apply MySumF2Induction.
apply conj.
apply Req_le.
reflexivity.
move=> cm u H17 H18.
apply Rplus_le_le_0_compat.
apply H18.
apply Rabs_pos.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> nm.
elim.
move=> nm1 H16 H17.
apply H16.
move=> nm H16.
apply Intersection_intro.
apply H16.
apply conj.
apply conj.
apply le_0_n.
apply (plus_le_reg_l (fst nm) n (snd nm)).
rewrite plus_comm.
apply (le_trans (fst nm + snd nm) (n + n) (snd nm + n))%nat.
apply H16.
apply plus_le_compat_r.
apply lt_le_weak.
apply H16.
apply conj.
apply H16.
rewrite - (plus_0_r (snd nm)).
apply (le_trans (snd nm + 0) (fst nm + snd nm) (n + n))%nat.
rewrite (plus_comm (fst nm) (snd nm)).
apply plus_le_compat_l.
apply le_0_n.
apply H16.
suff: ((fun nm : nat * nat => Rabs (an (fst nm) * bn (snd nm))) = (fun nm : nat * nat => Rabs (an (fst nm)) * Rabs (bn (snd nm)))).
move=> H16.
rewrite H16.
rewrite (MySumF2Pair nat nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) (exist (Finite nat) (fun m : nat => (S n <= m <= n + n)%nat) (natSectionFinite (S n) (n + n))) RPCM (fun m1 m2 : nat => Rabs (an m1) * Rabs (bn m2))).
suff: ((fun u : nat => MySumF2 nat (exist (Finite nat) (fun m : nat => (S n <= m <= n + n)%nat) (natSectionFinite (S n) (n + n)%nat)) RPCM (fun m2 : nat => Rabs (an u) * Rabs (bn m2))) = (fun u : nat => Rabs (an u) * MySumF2 nat (exist (Finite nat) (fun m : nat => (S n <= m <= n + n)%nat) (natSectionFinite (S n) (n + n)%nat)) RPCM (fun m2 : nat => Rabs (bn m2)))).
move=> H17.
rewrite H17.
suff: ((fun u : nat => Rabs (an u) * MySumF2 nat (exist (Finite nat) (fun m : nat => (S n <= m <= n + n)%nat) (natSectionFinite (S n) (n + n)%nat)) RPCM (fun m2 : nat => Rabs (bn m2))) = (fun u : nat => MySumF2 nat (exist (Finite nat) (fun m : nat => (S n <= m <= n + n)%nat) (natSectionFinite (S n) (n + n)%nat)) RPCM (fun m2 : nat => Rabs (bn m2)) * Rabs (an u))).
move=> H18.
rewrite H18.
rewrite MySumF2R_mult.
rewrite - MySumEqsum_f_R0.
rewrite - MySumEqsigma.
apply (Rle_lt_trans (sigma (fun m2 : nat => Rabs (bn m2)) (S n) (n + n) * sum_f_R0 (fun n0 : nat => Rabs (an n0)) n) (L1 * (eps * / 2 * / (1 + Rabs L1))) (eps * / 2)).
rewrite Rmult_comm.
apply Rmult_le_compat.
elim n.
apply Rabs_pos.
move=> n0 H19.
simpl.
apply Rplus_le_le_0_compat.
apply H19.
apply Rabs_pos.
unfold sigma.
elim (n + n - S n)%nat.
apply Rabs_pos.
move=> n0 H19.
simpl.
apply Rplus_le_le_0_compat.
apply H19.
apply Rabs_pos.
apply H10.
apply (Im_intro R R (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (an m)))) Rabs (sum_f_R0 (fun m2 : nat => Rabs (an m2)) n)).
apply (Im_intro nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (an m))) n).
apply Full_intro.
reflexivity.
rewrite Rabs_pos_eq.
reflexivity.
elim n.
apply Rabs_pos.
move=> n0 H19.
simpl.
apply Rplus_le_le_0_compat.
apply H19.
apply Rabs_pos.
apply (Rle_trans (sigma (fun m2 : nat => Rabs (bn m2)) (S n) (n + n)) (Rabs (sigma (fun m2 : nat => Rabs (bn m2)) (S n) (n + n))) (eps * / 2 * / (1 + Rabs L1))).
apply Rle_abs.
apply Rlt_le.
apply H14.
rewrite - {3} (plus_0_l n).
apply plus_lt_compat_r.
apply (le_trans (S 0) (S (max M1 M2)) n).
apply le_n_S.
apply le_0_n.
apply H15.
apply (le_trans M2 (S (max M1 M2)) n).
apply le_S.
apply Nat.le_max_r.
apply H15.
rewrite - Rmult_assoc.
apply (Rmult_lt_reg_r (1 + Rabs L1)).
apply (Rlt_le_trans 0 1 (1 + Rabs L1)).
apply Rlt_0_1.
rewrite - {1} (Rplus_0_r 1).
apply Rplus_le_compat_l.
apply Rabs_pos.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite Rmult_comm.
apply Rmult_gt_compat_l.
apply eps2_Rgt_R0.
apply H12.
apply (Rle_lt_trans L1 (Rabs L1) (1 + Rabs L1)).
apply Rle_abs.
rewrite - {1} (Rplus_0_l (Rabs L1)).
apply Rplus_lt_compat_r.
apply Rlt_0_1.
apply Rgt_not_eq.
apply (Rlt_le_trans 0 1 (1 + Rabs L1)).
apply Rlt_0_1.
rewrite - {1} (Rplus_0_r 1).
apply Rplus_le_compat_l.
apply Rabs_pos.
rewrite - {1} (plus_0_r n).
apply plus_lt_compat_l.
apply (le_trans (S 0) (S (max M1 M2)) n).
apply le_n_S.
apply le_0_n.
apply H15.
apply functional_extensionality.
move=> u.
apply Rmult_comm.
apply functional_extensionality.
move=> u.
apply MySumF2R_mult.
apply functional_extensionality.
move=> nm.
apply Rabs_mult.
move=> nm H16 H17.
apply (le_not_lt (fst nm + snd nm) (n + n))%nat.
apply H17.
apply plus_lt_compat.
apply H17.
apply H16.
apply Rmult_gt_0_compat.
apply eps2_Rgt_R0.
apply H12.
apply Rinv_0_lt_compat.
apply (Rlt_le_trans 0 1 (1 + Rabs L1)).
apply Rlt_0_1.
rewrite - {1} (Rplus_0_r 1).
apply Rplus_le_compat_l.
apply Rabs_pos.
apply Rmult_gt_0_compat.
apply eps2_Rgt_R0.
apply H12.
apply Rinv_0_lt_compat.
apply (Rlt_le_trans 0 1 (1 + Rabs L2)).
apply Rlt_0_1.
rewrite - {1} (Rplus_0_r 1).
apply Rplus_le_compat_l.
apply Rabs_pos.
move=> m.
apply Rle_ge.
apply Rabs_pos.
move=> m.
apply Rle_ge.
apply Rabs_pos.
move=> n.
suff: (Finite (nat * nat) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat)).
move=> H7.
suff: (sum_f_R0 (fun n0 : nat => sum_f_R0 (fun m : nat => an m * bn (n0 - m)%nat) n0) (n + n) = MySumF2 (nat * nat) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat) H7) RPCM (fun nm : nat * nat => an (fst nm) * bn (snd nm))).
move=> H8.
rewrite H8.
suff: ((FiniteUnion (nat * nat) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (fst nm > n)%nat) (H5 n)) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat /\ (snd nm > n)%nat) (H6 n))) = (FiniteIntersection (nat * nat) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat) H7) (fun (nm : nat * nat) => (fst nm > n)%nat \/ (snd nm > n)%nat))).
move=> H9.
rewrite H9.
rewrite (MySumF2Excluded (nat * nat) RPCM (fun nm : nat * nat => an (fst nm) * bn (snd nm)) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat) H7) (fun nm : nat * nat => (fst nm > n)%nat \/ (snd nm > n)%nat)).
unfold Rminus.
rewrite Rplus_assoc.
rewrite - {2} (Rplus_0_r (MySumF2 (nat * nat) (FiniteIntersection (nat * nat) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat) H7) (fun nm : nat * nat => (fst nm > n)%nat \/ (snd nm > n)%nat)) RPCM (fun nm : nat * nat => an (fst nm) * bn (snd nm)))).
apply Rplus_eq_compat_l.
apply Rminus_diag_eq.
suff: ((FiniteIntersection (nat * nat) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat) H7) (Ensembles.Complement (nat * nat) (fun nm : nat * nat => (fst nm > n)%nat \/ (snd nm > n)%nat))) = (FinitePair nat nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)))).
move=> H10.
rewrite H10.
rewrite (MySumF2Pair nat nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun (m1 m2 : nat) => an m1 * bn m2)).
suff: ((fun u : nat => MySumF2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun m2 : nat => an u * bn m2)) = (fun u : nat => MySumF2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= n)%nat) (natSectionFinite 0 n)) RPCM (fun m2 : nat => bn m2) * an u)).
move=> H11.
rewrite H11.
rewrite MySumF2R_mult.
rewrite MySumEqsum_f_R0.
rewrite MySumEqsum_f_R0.
apply Rmult_comm.
apply functional_extensionality.
move=> m.
rewrite Rmult_comm.
apply MySumF2R_mult.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> nm H10.
apply conj.
apply conj.
apply le_0_n.
elim (le_or_lt (fst nm) n).
apply.
elim H10.
move=> nm1 H11 H12 H13.
apply False_ind.
apply H11.
left.
apply H13.
apply conj.
apply le_0_n.
elim (le_or_lt (snd nm) n).
apply.
elim H10.
move=> nm1 H11 H12 H13.
apply False_ind.
apply H11.
right.
apply H13.
move=> nm H10.
apply Intersection_intro.
elim.
apply le_not_lt.
apply H10.
apply le_not_lt.
apply H10.
apply plus_le_compat.
apply H10.
apply H10.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> nm H9.
apply Intersection_intro.
elim H9.
move=> nm1 H10.
left.
apply H10.
move=> nm1 H10.
right.
apply H10.
elim H9.
move=> nm1 H10.
apply H10.
move=> nm1 H10.
apply H10.
move=> nm.
elim.
move=> nm1 H9 H10.
elim H9.
move=> H11.
left.
apply conj.
apply H10.
apply H11.
move=> H11.
right.
apply conj.
apply H10.
apply H11.
rewrite (MySumF2ImageSum (nat * nat) nat (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat) H7) RPCM (fun nm : nat * nat => an (fst nm) * bn (snd nm)) (fun nm : (nat * nat) => (fst nm + snd nm)%nat)).
suff: ((FiniteIm (nat * nat) nat (fun nm : nat * nat => (fst nm + snd nm)%nat) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat) H7)) = (exist (Finite nat) (fun m : nat => (0 <= m <= n + n)%nat) (natSectionFinite 0 (n + n)%nat))).
move=> H8.
rewrite H8.
rewrite MySumEqsum_f_R0.
apply (MySumF2Same nat (exist (Finite nat) (fun m : nat => (0 <= m <= n + n)%nat) (natSectionFinite 0 (n + n))) RPCM).
move=> n0 H15.
rewrite MySumEqsum_f_R0.
suff: (forall (k : nat), proj1_sig (exist (Finite nat) (fun m : nat => (0 <= m <= n0)%nat) (natSectionFinite 0 n0)) k -> proj1_sig (FiniteIntersection (nat * nat) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat) H7) (fun u1 : nat * nat => (fst u1 + snd u1)%nat = n0)) (k , n0 - k)%nat).
move=> H9.
apply (MySumF2BijectiveSame nat (exist (Finite nat) (fun m : nat => (0 <= m <= n0)%nat) (natSectionFinite 0 n0)) (nat * nat) (FiniteIntersection (nat * nat) (exist (Finite (nat * nat)) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat) H7) (fun u1 : nat * nat => (fst u1 + snd u1)%nat = n0)) RPCM (fun nm : nat * nat => an (fst nm) * bn (snd nm)) (fun (u : nat) => (u , n0 - u)%nat) H9).
simpl.
suff: (forall (u0 : {u : nat * nat | Intersection (nat * nat) (fun u1 : nat * nat => (fst u1 + snd u1)%nat = n0) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat) u}), (0 <= (fst (proj1_sig u0)) <= n0)%nat).
move=> H10.
exists (fun (u0 : {u : nat * nat | Intersection (nat * nat) (fun u1 : nat * nat => (fst u1 + snd u1)%nat = n0) (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat) u}) => (exist (fun (u : nat) => (0 <= u <= n0)%nat) (fst (proj1_sig u0)) (H10 u0))).
apply conj.
move=> x.
apply sig_map.
reflexivity.
move=> y.
apply sig_map.
simpl.
suff: ((n0 - fst (proj1_sig y))%nat = snd (proj1_sig y)).
move=> H11.
rewrite H11.
rewrite (surjective_pairing (proj1_sig y)).
reflexivity.
elim (proj2_sig y).
move=> z H11 H12.
rewrite - H11.
apply minus_plus.
move=> u0.
apply conj.
apply le_0_n.
elim (proj2_sig u0).
move=> u1 H10 H11.
rewrite - (plus_0_r (fst u1)).
rewrite - H10.
apply plus_le_compat_l.
apply le_0_n.
simpl.
move=> k H9.
apply Intersection_intro.
unfold In.
simpl.
apply le_plus_minus_r.
apply H9.
unfold In.
simpl.
rewrite le_plus_minus_r.
apply H15.
apply H9.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> m.
elim.
move=> nm H8 y H9.
rewrite H9.
apply conj.
apply le_0_n.
apply H8.
move=> m H8.
apply (Im_intro (nat * nat) nat (fun nm : nat * nat => (fst nm + snd nm <= n + n)%nat) (fun nm : nat * nat => (fst nm + snd nm)%nat) (m , O)).
unfold In.
simpl.
rewrite plus_0_r.
apply H8.
rewrite plus_0_r.
reflexivity.
apply (Finite_downward_closed (nat * nat) (fun nm : nat * nat => (0 <= fst nm <= n + n)%nat /\ (0 <= snd nm <= n + n)%nat)).
apply (FinitePairFinite nat nat (fun m : nat => (0 <= m <= n + n)%nat) (fun m : nat => (0 <= m <= n + n)%nat)).
apply (natSectionFinite 0 (n + n)%nat).
apply (natSectionFinite 0 (n + n)%nat).
move=> nm H7.
apply conj.
apply conj.
apply le_0_n.
rewrite - (plus_0_r (fst nm)).
apply (le_trans (fst nm + 0) (fst nm + snd nm) (n + n))%nat.
apply plus_le_compat_l.
apply le_0_n.
apply H7.
apply conj.
apply le_0_n.
rewrite - (plus_0_l (snd nm)).
apply (le_trans (0 + snd nm) (fst nm + snd nm) (n + n))%nat.
apply plus_le_compat_r.
apply le_0_n.
apply H7.
move=> n.
apply (Finite_downward_closed (nat * nat) (fun nm : nat * nat => (0 <= fst nm <= n + n)%nat /\ (0 <= snd nm <= n + n)%nat)).
apply (FinitePairFinite nat nat (fun m : nat => (0 <= m <= n + n)%nat) (fun m : nat => (0 <= m <= n + n)%nat)).
apply (natSectionFinite 0 (n + n)%nat).
apply (natSectionFinite 0 (n + n)%nat).
move=> nm H7.
apply conj.
apply conj.
apply le_0_n.
rewrite - (plus_0_r (fst nm)).
apply (le_trans (fst nm + 0) (fst nm + snd nm) (n + n))%nat.
apply plus_le_compat_l.
apply le_0_n.
apply H7.
apply conj.
apply le_0_n.
rewrite - (plus_0_l (snd nm)).
apply (le_trans (0 + snd nm) (fst nm + snd nm) (n + n))%nat.
apply plus_le_compat_r.
apply le_0_n.
apply H7.
move=> n.
apply (Finite_downward_closed (nat * nat) (fun nm : nat * nat => (0 <= fst nm <= n + n)%nat /\ (0 <= snd nm <= n + n)%nat)).
apply (FinitePairFinite nat nat (fun m : nat => (0 <= m <= n + n)%nat) (fun m : nat => (0 <= m <= n + n)%nat)).
apply (natSectionFinite 0 (n + n)%nat).
apply (natSectionFinite 0 (n + n)%nat).
move=> nm H7.
apply conj.
apply conj.
apply le_0_n.
rewrite - (plus_0_r (fst nm)).
apply (le_trans (fst nm + 0) (fst nm + snd nm) (n + n))%nat.
apply plus_le_compat_l.
apply le_0_n.
apply H7.
apply conj.
apply le_0_n.
rewrite - (plus_0_l (snd nm)).
apply (le_trans (0 + snd nm) (fst nm + snd nm) (n + n))%nat.
apply plus_le_compat_r.
apply le_0_n.
apply H7.
Qed.

Lemma Theorem_5_8_1_C : forall (an bn : nat -> C), (AbsoluteConvergenceRn 2 an) -> (AbsoluteConvergenceRn 2 bn) -> (AbsoluteConvergenceRn 2 (fun (n : nat) => sum_f_Rn 2 (fun (m : nat) => Cmult (an m) (bn (n - m)%nat)) n)).
Proof.
suff: (forall (a b : {x : R | x >= 0}), proj1_sig a <= proj1_sig b -> MySqrt a <= MySqrt b).
move=> H1.
suff: (forall (c : C), RnNorm 2 c <= Rabs (c CRe) + Rabs (c CIm)).
move=> H2.
suff: (forall (c : C) (n : Count 2), Rabs (c n) <= RnNorm 2 c).
move=> H3.
move=> an bn H4 H5.
apply Theorem_5_4.
move=> m.
apply RnNormNature.
suff: (AbsoluteConvergenceR (fun n : nat => an n CRe)).
move=> H6.
suff: (AbsoluteConvergenceR (fun n : nat => an n CIm)).
move=> H7.
suff: (AbsoluteConvergenceR (fun n : nat => bn n CRe)).
move=> H8.
suff: (AbsoluteConvergenceR (fun n : nat => bn n CIm)).
move=> H9.
suff: (PositiveSequence (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CRe) m))).
move=> H10.
elim (proj1 (bounded_abs (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CRe) m))))) (proj1 (Theorem_5_4 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CRe) m)) H10) (Theorem_5_8_1 (fun (n : nat) => an n CRe) (fun (n : nat) => bn n CRe) H6 H8))).
move=> L1 H11.
suff: (PositiveSequence (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CIm) m))).
move=> H12.
elim (proj1 (bounded_abs (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CIm) m))))) (proj1 (Theorem_5_4 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CIm) m)) H12) (Theorem_5_8_1 (fun (n : nat) => an n CRe) (fun (n : nat) => bn n CIm) H6 H9))).
move=> L2 H13.
suff: (PositiveSequence (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CRe) m))).
move=> H14.
elim (proj1 (bounded_abs (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CRe) m))))) (proj1 (Theorem_5_4 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CRe) m)) H14) (Theorem_5_8_1 (fun (n : nat) => an n CIm) (fun (n : nat) => bn n CRe) H7 H8))).
move=> L3 H15.
suff: (PositiveSequence (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CIm) m))).
move=> H16.
elim (proj1 (bounded_abs (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CIm) m))))) (proj1 (Theorem_5_4 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CIm) m)) H16) (Theorem_5_8_1 (fun (n : nat) => an n CIm) (fun (n : nat) => bn n CIm) H7 H9))).
move=> L4 H17.
apply bounded_abs.
exists (L1 + L2 + L3 + L4).
move=> x.
elim.
move=> r H18 r1 H19.
rewrite H19.
elim H18.
move=> n H20 y H21.
rewrite H21.
rewrite Rabs_pos_eq.
apply (Rle_trans (sum_f_R0 (fun m : nat => RnNorm 2 (sum_f_Rn 2 (fun m0 : nat => Cmult (an m0) (bn (m - m0)%nat)) m)) n) ((sum_f_R0 (fun (m : nat) => Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CRe) m)) n) + (sum_f_R0 (fun (m : nat) => Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CIm) m)) n) + (sum_f_R0 (fun (m : nat) => Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CRe) m)) n) + (sum_f_R0 (fun (m : nat) => Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CIm) m)) n)) (L1 + L2 + L3 + L4)).
rewrite - sum_f_R0_plus.
rewrite - sum_f_R0_plus.
rewrite - sum_f_R0_plus.
suff: (forall (m : nat), RnNorm 2 (sum_f_Rn 2 (fun m0 : nat => Cmult (an m0) (bn (m - m0)%nat)) m) <= Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CRe) m) + Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CIm) m) + Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CRe) m) + Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CIm) m)).
move=> H22.
elim n.
simpl.
apply (H22 O).
move=> n0 H23.
simpl.
apply Rplus_le_compat.
apply H23.
apply (H22 (S n0)).
move=> m.
apply (Rle_trans (RnNorm 2
  (sum_f_Rn 2
     (fun m0 : nat =>
      Cmult (an m0) (bn (m - m0)%nat)) m)) (Rabs ((sum_f_Rn 2
     (fun m0 : nat =>
      Cmult (an m0) (bn (m - m0)%nat)) m) CRe) + Rabs (((sum_f_Rn 2
     (fun m0 : nat =>
      Cmult (an m0) (bn (m - m0)%nat)) m)) CIm))).
apply H2.
rewrite sum_f_Rn_component.
rewrite (Rplus_comm (Rabs
  (sum_f_R0
     (fun m0 : nat =>
      an m0 CRe * bn (m - m0)%nat CRe) m) +
Rabs
  (sum_f_R0
     (fun m0 : nat =>
      an m0 CRe * bn (m - m0)%nat CIm) m) +
Rabs
  (sum_f_R0
     (fun m0 : nat =>
      an m0 CIm * bn (m - m0)%nat CRe) m)) (Rabs
  (sum_f_R0
     (fun m0 : nat =>
      an m0 CIm * bn (m - m0)%nat CIm) m)
)).
rewrite Rplus_assoc.
rewrite - Rplus_assoc.
apply Rplus_le_compat.
rewrite Rplus_comm.
suff: ((fun l : nat => Cmult (an l) (bn (m - l)%nat) CRe) = (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CRe - an m0 CIm * bn (m - m0)%nat CIm)).
move=> H22.
rewrite H22.
rewrite sum_f_R0_plus.
suff: (Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CIm) m) = Rabs (sum_f_R0 (fun m0 : nat => - (an m0 CIm * bn (m - m0)%nat CIm)) m)).
move=> H23.
rewrite H23.
apply Rabs_triang.
rewrite - Rabs_Ropp.
suff: ((- sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CIm) m) = (sum_f_R0 (fun m0 : nat => - (an m0 CIm * bn (m - m0)%nat CIm)) m)).
move=> H23.
rewrite H23.
reflexivity.
suff: (forall (k : nat), - sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CIm) k = sum_f_R0 (fun m0 : nat => - (an m0 CIm * bn (m - m0)%nat CIm)) k).
move=> H23.
apply (H23 m).
elim.
reflexivity.
move=> k H23.
simpl.
rewrite - H23.
apply Ropp_plus_distr.
apply functional_extensionality.
move=> k.
unfold Cmult.
apply CmakeRe.
suff: ((fun l : nat => Cmult (an l) (bn (m - l)%nat) CIm) = (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CIm + an m0 CIm * bn (m - m0)%nat CRe)).
move=> H22.
rewrite H22.
rewrite sum_f_R0_plus.
apply Rabs_triang.
apply functional_extensionality.
move=> k.
unfold Cmult.
apply CmakeIm.
apply Rplus_le_compat.
apply Rplus_le_compat.
apply Rplus_le_compat.
apply H11.
apply (Im_intro R R (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CRe) m)))) Rabs (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CRe) m)) n)).
apply (Im_intro nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CRe) m))) n).
apply Full_intro.
reflexivity.
rewrite Rabs_pos_eq.
reflexivity.
elim n.
apply Rabs_pos.
move=> n0 H22.
simpl.
apply Rplus_le_le_0_compat.
apply H22.
apply Rabs_pos.
apply H13.
apply (Im_intro R R (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CIm) m)))) Rabs (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CIm) m)) n)).
apply (Im_intro nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CRe * bn (m - m0)%nat CIm) m))) n).
apply Full_intro.
reflexivity.
rewrite Rabs_pos_eq.
reflexivity.
elim n.
apply Rabs_pos.
move=> n0 H22.
simpl.
apply Rplus_le_le_0_compat.
apply H22.
apply Rabs_pos.
apply H15.
apply (Im_intro R R (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CRe) m)))) Rabs (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CRe) m)) n)).
apply (Im_intro nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CRe) m))) n).
apply Full_intro.
reflexivity.
rewrite Rabs_pos_eq.
reflexivity.
elim n.
apply Rabs_pos.
move=> n0 H22.
simpl.
apply Rplus_le_le_0_compat.
apply H22.
apply Rabs_pos.
apply H17.
apply (Im_intro R R (Im nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CIm) m)))) Rabs (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CIm) m)) n)).
apply (Im_intro nat R (Full_set nat) (sum_f_R0 (fun m : nat => Rabs (sum_f_R0 (fun m0 : nat => an m0 CIm * bn (m - m0)%nat CIm) m))) n).
apply Full_intro.
reflexivity.
rewrite Rabs_pos_eq.
reflexivity.
elim n.
apply Rabs_pos.
move=> n0 H22.
simpl.
apply Rplus_le_le_0_compat.
apply H22.
apply Rabs_pos.
elim n.
apply Rge_le.
apply RnNormNature.
move=> n0 H22.
simpl.
apply Rplus_le_le_0_compat.
apply H22.
apply Rge_le.
apply RnNormNature.
move=> m.
apply Rle_ge.
apply Rabs_pos.
move=> m.
apply Rle_ge.
apply Rabs_pos.
move=> m.
apply Rle_ge.
apply Rabs_pos.
move=> m.
apply Rle_ge.
apply Rabs_pos.
apply (Theorem_5_5_1 (fun n : nat => Rabs (bn n CIm)) (fun n : nat => RnNorm 2 (bn n))).
move=> m.
apply Rle_ge.
apply Rabs_pos.
move=> m.
apply RnNormNature.
move=> n.
apply H3.
apply H5.
apply (Theorem_5_5_1 (fun n : nat => Rabs (bn n CRe)) (fun n : nat => RnNorm 2 (bn n))).
move=> m.
apply Rle_ge.
apply Rabs_pos.
move=> m.
apply RnNormNature.
move=> n.
apply H3.
apply H5.
apply (Theorem_5_5_1 (fun n : nat => Rabs (an n CIm)) (fun n : nat => RnNorm 2 (an n))).
move=> m.
apply Rle_ge.
apply Rabs_pos.
move=> m.
apply RnNormNature.
move=> n.
apply H3.
apply H4.
apply (Theorem_5_5_1 (fun n : nat => Rabs (an n CRe)) (fun n : nat => RnNorm 2 (an n))).
move=> m.
apply Rle_ge.
apply Rabs_pos.
move=> m.
apply RnNormNature.
move=> n.
apply H3.
apply H4.
move=> c n.
elim (CReorCIm n).
move=> H3.
rewrite H3.
suff: (RnNorm 2 = Cnorm).
move=> H4.
rewrite H4.
rewrite CnormDefinition.
suff: (Rabs (c CRe) * Rabs (c CRe) >= 0).
move=> H5.
rewrite - (MySqrtNature2 (exist (fun (x : R) => x >= 0) (Rabs (c CRe) * Rabs (c CRe)) H5) (Rabs (c CRe))).
apply H1.
simpl.
rewrite - (Rplus_0_r (Rabs (c CRe) * Rabs (c CRe))).
unfold Rabs.
elim (Rcase_abs (c CRe)).
move=> H6.
rewrite Rmult_opp_opp.
apply Rplus_le_compat_l.
apply Rge_le.
apply Formula_1_3.
move=> H6.
apply Rplus_le_compat_l.
apply Rge_le.
apply Formula_1_3.
apply conj.
apply Rle_ge.
apply Rabs_pos.
reflexivity.
rewrite - Rabs_mult.
apply Rle_ge.
apply Rabs_pos.
reflexivity.
move=> H3.
rewrite H3.
suff: (RnNorm 2 = Cnorm).
move=> H4.
rewrite H4.
rewrite CnormDefinition.
suff: (Rabs (c CIm) * Rabs (c CIm) >= 0).
move=> H5.
rewrite - (MySqrtNature2 (exist (fun (x : R) => x >= 0) (Rabs (c CIm) * Rabs (c CIm)) H5) (Rabs (c CIm))).
apply H1.
simpl.
rewrite - (Rplus_0_l (Rabs (c CIm) * Rabs (c CIm))).
unfold Rabs.
elim (Rcase_abs (c CIm)).
move=> H6.
rewrite Rmult_opp_opp.
apply Rplus_le_compat_r.
apply Rge_le.
apply Formula_1_3.
move=> H6.
apply Rplus_le_compat_r.
apply Rge_le.
apply Formula_1_3.
apply conj.
apply Rle_ge.
apply Rabs_pos.
reflexivity.
rewrite - Rabs_mult.
apply Rle_ge.
apply Rabs_pos.
reflexivity.
move=> c.
suff: (RnNorm 2 (Cmake (c CRe) 0) = Rabs (c CRe)).
move=> H2.
suff: (RnNorm 2 (Cmake 0 (c CIm)) = Rabs (c CIm)).
move=> H3.
suff: (c = Rnplus 2 (Cmake (c CRe) 0) (Cmake 0 (c CIm))).
move=> H4.
rewrite - H2.
rewrite - H3.
rewrite {1} H4.
apply Proposition_4_4_2_1.
unfold Rnplus.
apply functional_extensionality.
move=> n.
elim (CReorCIm n).
move=> H4.
rewrite H4.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite Rplus_0_r.
reflexivity.
move=> H4.
rewrite H4.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite Rplus_0_l.
reflexivity.
suff: (RnNorm 2 = Cnorm).
move=> H3.
rewrite H3.
rewrite CnormDefinition.
apply MySqrtNature2.
apply conj.
apply Rle_ge.
apply Rabs_pos.
simpl.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite Rmult_0_r.
rewrite Rplus_0_l.
unfold Rabs.
elim (Rcase_abs (c CIm)).
move=> H4.
rewrite Rmult_opp_opp.
reflexivity.
move=> H4.
reflexivity.
reflexivity.
suff: (RnNorm 2 = Cnorm).
move=> H2.
rewrite H2.
rewrite CnormDefinition.
apply MySqrtNature2.
apply conj.
apply Rle_ge.
apply Rabs_pos.
simpl.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite Rmult_0_r.
rewrite Rplus_0_r.
unfold Rabs.
elim (Rcase_abs (c CRe)).
move=> H3.
rewrite Rmult_opp_opp.
reflexivity.
move=> H3.
reflexivity.
reflexivity.
move=> a b H1.
apply Rnot_lt_le.
move=> H2.
apply (Rle_not_lt (proj1_sig b) (proj1_sig a) H1).
rewrite (proj2 (MySqrtNature a)).
rewrite (proj2 (MySqrtNature b)).
apply Rmult_le_0_lt_compat.
apply Rge_le.
apply (proj1 (MySqrtNature b)).
apply Rge_le.
apply (proj1 (MySqrtNature b)).
apply H2.
apply H2.
Qed.

Lemma Theorem_5_8_2_C : forall (an bn : nat -> C) (a b : C), (AbsoluteConvergenceRn 2 an) -> (AbsoluteConvergenceRn 2 bn) -> (Un_cv_met (Rn_met 2) (sum_f_Rn 2 an) a) -> (Un_cv_met (Rn_met 2) (sum_f_Rn 2 bn) b) -> (Un_cv_met (Rn_met 2) (sum_f_Rn 2 (fun (n : nat) => sum_f_Rn 2 (fun (m : nat) => Cmult (an m) (bn (n - m)%nat)) n)) (Cmult a b)).
Proof.
suff: (forall (a b : {x : R | x >= 0}), proj1_sig a <= proj1_sig b -> MySqrt a <= MySqrt b).
move=> H1.
suff: (forall (c : C), RnNorm 2 c <= Rabs (c CRe) + Rabs (c CIm)).
move=> H2.
suff: (forall (c : C) (n : Count 2), Rabs (c n) <= RnNorm 2 c).
move=> H3.
move=> an bn a b H4 H5 H6 H7.
apply Theorem_4_5_1.
suff: (AbsoluteConvergenceR (fun n : nat => an n CRe)).
move=> H8.
suff: (AbsoluteConvergenceR (fun n : nat => an n CIm)).
move=> H9.
suff: (AbsoluteConvergenceR (fun n : nat => bn n CRe)).
move=> H10.
suff: (AbsoluteConvergenceR (fun n : nat => bn n CIm)).
move=> H11.
move=> n.
elim (CReorCIm n).
move=> H12.
rewrite H12.
unfold Cmult at 2.
rewrite CmakeRe.
suff: ((fun n0 : nat => sum_f_Rn 2 (fun n1 : nat => sum_f_Rn 2 (fun m : nat => Cmult (an m) (bn (n1 - m)%nat)) n1) n0 CRe) = (fun n0 : nat => sum_f_R0 (fun (n1 : nat) => sum_f_R0 (fun m : nat => (an m CRe) * (bn (n1 - m)%nat CRe)) n1) n0 + - (fun (n1 : nat) => sum_f_R0 (fun n1 : nat => sum_f_R0 (fun m : nat => an m CIm * bn (n1 - m)%nat CIm) n1) n1) n0)).
move=> H13.
rewrite H13.
apply Theorem_2_5_1_plus.
apply (Theorem_5_8_2 (fun (n : nat) => an n CRe) (fun (n : nat) => bn n CRe) (a CRe) (b CRe) H8 H10).
suff: ((fun (n : nat) => (sum_f_Rn 2 an) n CRe) = (sum_f_R0 (fun n0 : nat => an n0 CRe))).
move=> H14.
rewrite - H14.
apply Theorem_4_5_1.
apply H6.
apply functional_extensionality.
move=> m.
rewrite sum_f_Rn_component.
reflexivity.
suff: ((fun (n : nat) => (sum_f_Rn 2 bn) n CRe) = (sum_f_R0 (fun n0 : nat => bn n0 CRe))).
move=> H14.
rewrite - H14.
apply Theorem_4_5_1.
apply H7.
apply functional_extensionality.
move=> m.
rewrite sum_f_Rn_component.
reflexivity.
apply Theorem_2_5_1_opp.
apply (Theorem_5_8_2 (fun (n : nat) => an n CIm) (fun (n : nat) => bn n CIm) (a CIm) (b CIm) H9 H11).
suff: ((fun (n : nat) => (sum_f_Rn 2 an) n CIm) = (sum_f_R0 (fun n0 : nat => an n0 CIm))).
move=> H14.
rewrite - H14.
apply Theorem_4_5_1.
apply H6.
apply functional_extensionality.
move=> m.
rewrite sum_f_Rn_component.
reflexivity.
suff: ((fun (n : nat) => (sum_f_Rn 2 bn) n CIm) = (sum_f_R0 (fun n0 : nat => bn n0 CIm))).
move=> H14.
rewrite - H14.
apply Theorem_4_5_1.
apply H7.
apply functional_extensionality.
move=> m.
rewrite sum_f_Rn_component.
reflexivity.
apply functional_extensionality.
suff: (forall (m : nat), - sum_f_R0 (fun n1 : nat => sum_f_R0 (fun m0 : nat => an m0 CIm * bn (n1 - m0)%nat CIm) n1) m = sum_f_R0 (fun n1 : nat => sum_f_R0 (fun m0 : nat => - an m0 CIm * bn (n1 - m0)%nat CIm) n1) m).
move=> H13 m.
rewrite (H13 m).
rewrite - sum_f_R0_plus.
rewrite sum_f_Rn_component.
suff: ((fun l : nat => sum_f_Rn 2 (fun m0 : nat => Cmult (an m0) (bn (l - m0)%nat)) l CRe) = (fun m0 : nat => sum_f_R0 (fun m1 : nat => an m1 CRe * bn (m0 - m1)%nat CRe) m0 + sum_f_R0 (fun m1 : nat => - an m1 CIm * bn (m0 - m1)%nat CIm) m0)).
move=> H14.
rewrite H14.
reflexivity.
apply functional_extensionality.
move=> m0.
rewrite sum_f_Rn_component.
rewrite - sum_f_R0_plus.
suff: ((fun l : nat => Cmult (an l) (bn (m0 - l)%nat) CRe) = (fun m1 : nat => an m1 CRe * bn (m0 - m1)%nat CRe + - an m1 CIm * bn (m0 - m1)%nat CIm)).
move=> H14.
rewrite H14.
reflexivity.
apply functional_extensionality.
move=> m1.
unfold Cmult.
rewrite CmakeRe.
rewrite - Ropp_mult_distr_l.
reflexivity.
suff: ((fun n1 : nat => sum_f_R0 (fun m0 : nat => - an m0 CIm * bn (n1 - m0)%nat CIm) n1) = (fun n1 : nat => - sum_f_R0 (fun m0 : nat => an m0 CIm * bn (n1 - m0)%nat CIm) n1)).
move=> H13.
rewrite H13.
elim.
simpl.
reflexivity.
move=> m H14.
simpl.
rewrite - H14.
apply Ropp_plus_distr.
apply functional_extensionality.
move=> n0.
suff: (forall (n1 : nat), sum_f_R0 (fun m0 : nat => - an m0 CIm * bn (n0 - m0)%nat CIm) n1 = - sum_f_R0 (fun m0 : nat => an m0 CIm * bn (n0 - m0)%nat CIm) n1).
move=> H13.
apply (H13 n0).
elim.
simpl.
rewrite Ropp_mult_distr_l.
reflexivity.
move=> m H13.
simpl.
rewrite H13.
rewrite Ropp_plus_distr.
rewrite - Ropp_mult_distr_l.
reflexivity.
move=> H12.
rewrite H12.
unfold Cmult at 2.
rewrite CmakeIm.
suff: ((fun n0 : nat => sum_f_Rn 2 (fun n1 : nat => sum_f_Rn 2 (fun m : nat => Cmult (an m) (bn (n1 - m)%nat)) n1) n0 CIm) = (fun n0 : nat => sum_f_R0 (fun (n1 : nat) => sum_f_R0 (fun m : nat => (an m CRe) * (bn (n1 - m)%nat CIm)) n1) n0 + (fun (n1 : nat) => sum_f_R0 (fun n1 : nat => sum_f_R0 (fun m : nat => an m CIm * bn (n1 - m)%nat CRe) n1) n1) n0)).
move=> H13.
rewrite H13.
apply Theorem_2_5_1_plus.
apply (Theorem_5_8_2 (fun (n : nat) => an n CRe) (fun (n : nat) => bn n CIm) (a CRe) (b CIm) H8 H11).
suff: ((fun (n : nat) => (sum_f_Rn 2 an) n CRe) = (sum_f_R0 (fun n0 : nat => an n0 CRe))).
move=> H14.
rewrite - H14.
apply Theorem_4_5_1.
apply H6.
apply functional_extensionality.
move=> m.
rewrite sum_f_Rn_component.
reflexivity.
suff: ((fun (n : nat) => (sum_f_Rn 2 bn) n CIm) = (sum_f_R0 (fun n0 : nat => bn n0 CIm))).
move=> H14.
rewrite - H14.
apply Theorem_4_5_1.
apply H7.
apply functional_extensionality.
move=> m.
rewrite sum_f_Rn_component.
reflexivity.
apply (Theorem_5_8_2 (fun (n : nat) => an n CIm) (fun (n : nat) => bn n CRe) (a CIm) (b CRe) H9 H10).
suff: ((fun (n : nat) => (sum_f_Rn 2 an) n CIm) = (sum_f_R0 (fun n0 : nat => an n0 CIm))).
move=> H14.
rewrite - H14.
apply Theorem_4_5_1.
apply H6.
apply functional_extensionality.
move=> m.
rewrite sum_f_Rn_component.
reflexivity.
suff: ((fun (n : nat) => (sum_f_Rn 2 bn) n CRe) = (sum_f_R0 (fun n0 : nat => bn n0 CRe))).
move=> H14.
rewrite - H14.
apply Theorem_4_5_1.
apply H7.
apply functional_extensionality.
move=> m.
rewrite sum_f_Rn_component.
reflexivity.
apply functional_extensionality.
move=> m.
rewrite - sum_f_R0_plus.
rewrite sum_f_Rn_component.
suff: ((fun l : nat => sum_f_Rn 2 (fun m0 : nat => Cmult (an m0) (bn (l - m0)%nat)) l CIm) = (fun m0 : nat => sum_f_R0 (fun m1 : nat => an m1 CRe * bn (m0 - m1)%nat CIm) m0 + sum_f_R0 (fun m1 : nat => an m1 CIm * bn (m0 - m1)%nat CRe) m0)).
move=> H13.
rewrite H13.
reflexivity.
apply functional_extensionality.
move=> k.
rewrite - sum_f_R0_plus.
rewrite sum_f_Rn_component.
suff: ((fun l : nat => Cmult (an l) (bn (k - l)%nat) CIm) = (fun m0 : nat => an m0 CRe * bn (k - m0)%nat CIm + an m0 CIm * bn (k - m0)%nat CRe)).
move=> H13.
rewrite H13.
reflexivity.
apply functional_extensionality.
move=> l.
unfold Cmult.
apply CmakeIm.
apply (Theorem_5_5_1 (fun n : nat => Rabs (bn n CIm)) (fun n : nat => RnNorm 2 (bn n))).
move=> m.
apply Rle_ge.
apply Rabs_pos.
move=> m.
apply RnNormNature.
move=> n.
apply H3.
apply H5.
apply (Theorem_5_5_1 (fun n : nat => Rabs (bn n CRe)) (fun n : nat => RnNorm 2 (bn n))).
move=> m.
apply Rle_ge.
apply Rabs_pos.
move=> m.
apply RnNormNature.
move=> n.
apply H3.
apply H5.
apply (Theorem_5_5_1 (fun n : nat => Rabs (an n CIm)) (fun n : nat => RnNorm 2 (an n))).
move=> m.
apply Rle_ge.
apply Rabs_pos.
move=> m.
apply RnNormNature.
move=> n.
apply H3.
apply H4.
apply (Theorem_5_5_1 (fun n : nat => Rabs (an n CRe)) (fun n : nat => RnNorm 2 (an n))).
move=> m.
apply Rle_ge.
apply Rabs_pos.
move=> m.
apply RnNormNature.
move=> n.
apply H3.
apply H4.
move=> c n.
elim (CReorCIm n).
move=> H3.
rewrite H3.
suff: (RnNorm 2 = Cnorm).
move=> H4.
rewrite H4.
rewrite CnormDefinition.
suff: (Rabs (c CRe) * Rabs (c CRe) >= 0).
move=> H5.
rewrite - (MySqrtNature2 (exist (fun (x : R) => x >= 0) (Rabs (c CRe) * Rabs (c CRe)) H5) (Rabs (c CRe))).
apply H1.
simpl.
rewrite - (Rplus_0_r (Rabs (c CRe) * Rabs (c CRe))).
unfold Rabs.
elim (Rcase_abs (c CRe)).
move=> H6.
rewrite Rmult_opp_opp.
apply Rplus_le_compat_l.
apply Rge_le.
apply Formula_1_3.
move=> H6.
apply Rplus_le_compat_l.
apply Rge_le.
apply Formula_1_3.
apply conj.
apply Rle_ge.
apply Rabs_pos.
reflexivity.
rewrite - Rabs_mult.
apply Rle_ge.
apply Rabs_pos.
reflexivity.
move=> H3.
rewrite H3.
suff: (RnNorm 2 = Cnorm).
move=> H4.
rewrite H4.
rewrite CnormDefinition.
suff: (Rabs (c CIm) * Rabs (c CIm) >= 0).
move=> H5.
rewrite - (MySqrtNature2 (exist (fun (x : R) => x >= 0) (Rabs (c CIm) * Rabs (c CIm)) H5) (Rabs (c CIm))).
apply H1.
simpl.
rewrite - (Rplus_0_l (Rabs (c CIm) * Rabs (c CIm))).
unfold Rabs.
elim (Rcase_abs (c CIm)).
move=> H6.
rewrite Rmult_opp_opp.
apply Rplus_le_compat_r.
apply Rge_le.
apply Formula_1_3.
move=> H6.
apply Rplus_le_compat_r.
apply Rge_le.
apply Formula_1_3.
apply conj.
apply Rle_ge.
apply Rabs_pos.
reflexivity.
rewrite - Rabs_mult.
apply Rle_ge.
apply Rabs_pos.
reflexivity.
move=> c.
suff: (RnNorm 2 (Cmake (c CRe) 0) = Rabs (c CRe)).
move=> H2.
suff: (RnNorm 2 (Cmake 0 (c CIm)) = Rabs (c CIm)).
move=> H3.
suff: (c = Rnplus 2 (Cmake (c CRe) 0) (Cmake 0 (c CIm))).
move=> H4.
rewrite - H2.
rewrite - H3.
rewrite {1} H4.
apply Proposition_4_4_2_1.
unfold Rnplus.
apply functional_extensionality.
move=> n.
elim (CReorCIm n).
move=> H4.
rewrite H4.
rewrite CmakeRe.
rewrite CmakeRe.
rewrite Rplus_0_r.
reflexivity.
move=> H4.
rewrite H4.
rewrite CmakeIm.
rewrite CmakeIm.
rewrite Rplus_0_l.
reflexivity.
suff: (RnNorm 2 = Cnorm).
move=> H3.
rewrite H3.
rewrite CnormDefinition.
apply MySqrtNature2.
apply conj.
apply Rle_ge.
apply Rabs_pos.
simpl.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite Rmult_0_r.
rewrite Rplus_0_l.
unfold Rabs.
elim (Rcase_abs (c CIm)).
move=> H4.
rewrite Rmult_opp_opp.
reflexivity.
move=> H4.
reflexivity.
reflexivity.
suff: (RnNorm 2 = Cnorm).
move=> H2.
rewrite H2.
rewrite CnormDefinition.
apply MySqrtNature2.
apply conj.
apply Rle_ge.
apply Rabs_pos.
simpl.
rewrite CmakeRe.
rewrite CmakeIm.
rewrite Rmult_0_r.
rewrite Rplus_0_r.
unfold Rabs.
elim (Rcase_abs (c CRe)).
move=> H3.
rewrite Rmult_opp_opp.
reflexivity.
move=> H3.
reflexivity.
reflexivity.
move=> a b H1.
apply Rnot_lt_le.
move=> H2.
apply (Rle_not_lt (proj1_sig b) (proj1_sig a) H1).
rewrite (proj2 (MySqrtNature a)).
rewrite (proj2 (MySqrtNature b)).
apply Rmult_le_0_lt_compat.
apply Rge_le.
apply (proj1 (MySqrtNature b)).
apply Rge_le.
apply (proj1 (MySqrtNature b)).
apply H2.
apply H2.
Qed.

Definition NeighborhoodMet (m : Metric_Space) (x : Base m) (eps : R) := (fun (y : Base m) => dist m y x < eps).

Definition ClosureMet (m : Metric_Space) (A : Ensemble (Base m)) := (fun (y : Base m) => forall (eps : R) ,eps > 0 -> (exists (z : Base m), NeighborhoodMet m y eps z /\ A z)).

Lemma Proposition_6_1_1 : forall (m : Metric_Space) (A : Ensemble (Base m)) (b : Base m), (ClosureMet m A b) <-> (exists (c : nat -> Base m), (forall (n : nat), A (c n)) /\ (Un_cv_met m c b)).
Proof.
move=> m a b.
apply conj.
move=> H1.
suff: (exists (c : nat -> Base m), forall (n : nat), a (c n) /\ dist m (c n) b < 1 / INR (S n)).
elim.
move=> c H2.
exists c.
apply conj.
move=> n.
apply (proj1 (H2 n)).
move=> eps H3.
elim (Formula_3_8 eps H3).
move=> n H4.
exists n.
move=> n0 H5.
apply (Rlt_trans (dist m (c n0) b) (1 / INR (S n0)) (eps)).
apply (proj2 (H2 n0)).
rewrite - (Rplus_0_r (1 / INR (S n0))).
rewrite - Ropp_0.
rewrite - (Rabs_right (1 / INR (S n0) + - 0)).
apply (H4 (S n0)).
apply (le_S n n0).
apply H5.
rewrite Ropp_0.
rewrite (Rplus_0_r (1 / INR (S n0))).
apply (Rgt_ge (1 / INR (S n0)) 0).
rewrite /Rdiv.
rewrite (Rmult_1_l (/ INR (S n0))).
apply Rinv_0_lt_compat.
suff: (0 = (INR 0)).
move=> H6.
rewrite H6.
apply (lt_INR O (S n0)).
apply (le_n_S 0 n0).
apply (le_0_n n0).
simpl.
reflexivity.
apply (functional_choice (fun (n : nat) (x : Base m) => a x /\ dist m x b < 1 / INR (S n))).
move=> n.
elim (H1 (1 / INR (S n))).
move=> y H2.
exists y.
apply conj.
apply (proj2 H2).
apply (proj1 H2).
rewrite /Rdiv.
rewrite (Rmult_1_l (/ INR (S n))).
apply Rinv_0_lt_compat.
suff: (0 = (INR 0)).
move=> H6.
rewrite H6.
apply (lt_INR O (S n)).
apply (le_n_S 0 n).
apply (le_0_n n).
simpl.
reflexivity.
move=> H1.
move=> eps H2.
elim H1.
move=> c H3.
elim (proj2 H3 eps H2).
move=> n H4.
exists (c n).
apply conj.
apply (H4 n).
apply (le_n n).
apply (proj1 H3 n).
Qed.

Lemma Proposition_6_1_2 : forall (m : Metric_Space) (A : Ensemble (Base m)), Included (Base m) A (ClosureMet m A).
Proof.
move=> m A a H1.
move=> eps H2.
exists a.
apply conj.
unfold NeighborhoodMet.
rewrite (proj2 (dist_refl m a a)).
apply H2.
reflexivity.
apply H1.
Qed.

Lemma Proposition_6_1_3 : forall (m : Metric_Space) (A B : Ensemble (Base m)), Included (Base m) A B -> Included (Base m) (ClosureMet m A) (ClosureMet m B).
Proof.
move=> m A B H1 x H2.
move=> eps H3.
elim (H2 eps H3).
move=> y H4.
exists y.
apply conj.
apply (proj1 H4).
apply (H1 y).
apply (proj2 H4).
Qed.

Lemma Proposition_6_1_4 : forall (m : Metric_Space) (A : Ensemble (Base m)), (ClosureMet m (ClosureMet m A)) = (ClosureMet m A).
Proof.
move=> m A.
apply Extensionality_Ensembles.
apply conj.
move=> x H1.
move=> eps H2.
elim (H1 (eps * / 2) (eps2_Rgt_R0 eps H2)).
move=> y H3.
elim (proj2 H3 (eps * / 2) (eps2_Rgt_R0 eps H2)).
move=> z H4.
exists z.
apply conj.
apply (Rle_lt_trans (dist m z x) (dist m z y + dist m y x) eps).
apply (dist_tri m z x y).
rewrite - (eps2 eps).
apply Rplus_lt_compat.
apply (proj1 H4).
apply (proj1 H3).
apply (proj2 H4).
apply (Proposition_6_1_2 m (ClosureMet m A)).
Qed.

Lemma InfiniteHasSequence : forall (A : Ensemble nat), (~ Finite nat A) -> (exists (a : nat -> nat), (forall (n : nat), (A (a n))) /\ (forall (n : nat), (a n < a (S n))%nat)).
Proof.
move=> A H1.
suff: (forall (n : nat), exists (m : nat), (m >= n)%nat /\ (A m)).
move=> H2.
suff: (forall (m : nat), {k : nat | is_min_nat (fun (n : nat) => (A n) /\ (m < n)%nat) k}).
move=> H3.
exists ((fix a (n : nat) : nat := 
match n with 
  | O => (proj1_sig (H3 O))
  | S n0 => (proj1_sig (H3 (a n0)))
end)).
apply conj.
elim.
apply (proj2_sig (H3 O)).
move=> n H4.
apply (proj2_sig (H3 ((fix a (n0 : nat) : nat :=
            match n0 with
            | 0%nat => proj1_sig (H3 0%nat)
            | S n1 => proj1_sig (H3 (a n1))
            end) n))).
move=> n.
apply (proj2 (proj1 (proj2_sig (H3
      ((fix a (n0 : nat) : nat :=
          match n0 with
          | O => proj1_sig (H3 O)
          | S n1 => proj1_sig (H3 (a n1))
          end) n))))).
move=> m.
apply constructive_definite_description.
apply (unique_existence (fun (x : nat) => is_min_nat (fun n : nat => A n /\ (m < n)%nat) x)).
apply conj.
apply (Exist_min_nat (fun n : nat => A n /\ (m < n)%nat)).
elim (H2 (S m)).
move=> k H3.
apply (Inhabited_intro nat (fun n : nat => A n /\ (m < n)%nat) k).
apply conj.
apply (proj2 H3).
apply (proj1 H3).
move=> m0 m1 H3 H4.
apply (le_antisym m0 m1).
apply (proj2 H3 m1).
apply (proj1 H4).
apply (proj2 H4 m0).
apply (proj1 H3).
move=> n.
apply NNPP.
move=> H2.
apply H1.
apply (Finite_Set_Included nat A (fun (k : nat) => (k < n)%nat)).
apply (cardinal_finite nat (fun k : nat => (k < n)%nat) n).
apply (nat_cardinal n).
move=> a H3.
elim (le_or_lt n a).
move=> H4.
apply False_ind.
apply H2.
exists a.
apply conj.
apply H4.
apply H3.
move=> H4.
apply H4.
Qed.

Lemma Proposition_6_1_5 : forall (m : Metric_Space) (A B : Ensemble (Base m)), (ClosureMet m (Union (Base m) A B)) = (Union (Base m) (ClosureMet m A) (ClosureMet m B)).
Proof.
move=> m1 A B.
apply Extensionality_Ensembles.
apply conj.
move=> x H1.
elim (proj1 (Proposition_6_1_1 m1 (Union (Base m1) A B) x)).
move=> c H2.
elim (classic (Finite nat (fun (n : nat) => A (c n)))).
move=> H3.
right.
suff: (exists (n : nat),forall (n0 : nat), (n0 >= n)%nat -> (B (c n0))).
elim.
move=> m H4.
apply Proposition_6_1_1.
exists (fun (n : nat) => c (n + m)%nat).
apply conj.
move=> n.
apply (H4 (n + m)%nat).
rewrite - {2} (plus_0_l m).
apply plus_le_compat_r.
apply le_0_n.
move=> eps H5.
elim (proj2 H2 eps H5).
move=> k H6.
exists k.
move=> n H7.
apply (H6 (n + m)%nat).
apply (le_trans k n (n + m)%nat).
apply H7.
rewrite - {1} (plus_0_r n).
apply plus_le_compat_l.
apply le_0_n.
elim (classic (Inhabited nat (fun n : nat => A (c n)))).
move=> H4.
elim (Finite_max_nat (fun n : nat => A (c n)) H3 H4).
move=> m H5.
exists (S m).
move=> n H6.
suff: (~ A (c n)).
elim (proj1 H2 n).
move=> y H7 H8.
apply False_ind.
apply (H8 H7).
move=> y H7 H8.
apply H7.
move=> H7.
apply (lt_not_le m n).
apply H6.
apply (proj2 H5 n).
apply H7.
move=> H4.
exists O.
move=> n H5.
suff: (~ A (c n)).
elim (proj1 H2 n).
move=> y H7 H8.
apply False_ind.
apply (H8 H7).
move=> y H7 H8.
apply H7.
move=> H6.
apply H4.
apply (Inhabited_intro nat (fun n0 : nat => A (c n0)) n).
apply H6.
move=> H3.
elim (InfiniteHasSequence (fun n : nat => A (c n))).
move=> s H4.
left.
apply Proposition_6_1_1.
exists (fun (n : nat) => (c (s n))).
apply conj.
apply (proj1 H4).
move=> eps H5.
elim (proj2 H2 eps H5).
move=> m H6.
exists m.
move=> n H7.
apply (H6 (s n)).
apply (le_trans m n (s n)).
apply H7.
apply (Formula_3_17 s (proj2 H4)).
apply H3.
apply H1.
move=> x.
elim.
move=> y H1.
apply (Proposition_6_1_3 m1 A (Union (Base m1) A B)).
move=> a H2.
left.
apply H2.
apply H1.
move=> y H1.
apply (Proposition_6_1_3 m1 B (Union (Base m1) A B)).
move=> b H2.
right.
apply H2.
apply H1.
Qed.

Lemma Theorem_6_2 : forall (M1 M2 : Metric_Space) (f : Base M1 -> Base M2) (B : Ensemble (Base M1)) (x : Base M1) (y : Base M2), (limit_in M1 M2 f B x y <-> (forall (xn : nat -> {x : Base M1 | B x}), (Un_cv_met M1 (fun (n : nat) => proj1_sig (xn n)) x) -> (Un_cv_met M2 (fun (n : nat) => (f (proj1_sig (xn n)))) y))).
Proof.
move=> M1 M2 f B x y.
apply conj.
move=> H2 xn H3 eps H4.
elim (H2 eps H4).
move=> del H5.
elim (H3 del (proj1 H5)).
move=> n0 H6.
exists n0.
move=> n H7.
apply (proj2 H5 (proj1_sig (xn n))).
apply conj.
apply (proj2_sig (xn n)).
apply (H6 n H7).
move=> H2.
apply NNPP.
move=> H3.
suff: (exists (eps : R), eps > 0 /\ ~ exists alp : R, (alp > 0 /\ (forall x0 : Base M1, B x0 /\ dist M1 x0 x < alp -> dist M2 (f x0) y < eps))).
elim.
move=> eps H4.
suff: (exists (xn : nat -> {x : Base M1 | B x}), forall (n : nat), (dist M1 (proj1_sig (xn n)) x < 1 / (INR (S n)) /\ dist M2 (f (proj1_sig (xn n))) y >= eps)).
elim.
move=> xn H5.
suff: (Un_cv_met M2 (fun n : nat => f (proj1_sig (xn n))) y).
move=> H6.
elim (H6 eps (proj1 H4)).
move=> n H7.
apply (Rlt_not_ge (dist M2 (f (proj1_sig (xn n))) y) eps).
apply (H7 n).
apply (le_n n).
apply (proj2 (H5 n)).
apply (H2 xn).
move=> eps2 H6.
elim (Formula_3_8 eps2 H6).
move=> n H7.
exists n.
move=> n0 H8.
apply (Rlt_trans (dist M1 (proj1_sig (xn n0)) x) (1 / INR (S n0)) eps2).
apply (proj1 (H5 n0)).
rewrite - (Rplus_0_r (1 / INR (S n0))).
rewrite - Ropp_0.
apply (Rle_lt_trans (1 / INR (S n0) + - 0) (Rabs (1 / INR (S n0) + - 0)) eps2).
apply (Rle_abs (1 / INR (S n0) + - 0)).
apply (H7 (S n0)).
apply (le_S n n0).
apply H8.
apply (functional_choice (fun (n : nat) (z : {x0 : Base M1 | B x0}) => dist M1 (proj1_sig z) x < 1 / INR (S n) /\ dist M2 (f (proj1_sig z)) y >= eps)).
move=> n.
apply NNPP.
move=> H5.
apply (proj2 H4).
exists (1 / INR (S n)).
rewrite /Rdiv.
apply conj.
rewrite (Rmult_1_l (/ (INR (S n)))).
apply (Rinv_0_lt_compat (INR (S n))).
suff: (0 = (INR 0)).
move=> H6.
rewrite H6.
apply (lt_INR O (S n)).
apply (le_n_S 0 n).
apply (le_0_n n).
simpl.
reflexivity.
move=> x0 H6.
apply (Rnot_ge_lt (dist M2 (f x0) y) eps).
move=> H7.
apply H5.
exists (exist B x0 (proj1 H6)).
apply conj.
apply (proj2 H6).
apply H7.
apply NNPP.
move=> H4.
apply H3.
move=> eps H5.
apply NNPP.
move=> H6.
apply H4.
exists eps.
apply conj.
apply H5.
apply H6.
Qed.

Lemma Theorem_6_2_corollary : forall (M1 M2 : Metric_Space) (f : Base M1 -> Base M2) (B : Ensemble (Base M1)) (x : Base M1), (exists (y : Base M2), limit_in M1 M2 f B x y) <-> ((forall (xn : nat -> {x : Base M1 | B x}), (Un_cv_met M1 (fun (n : nat) => proj1_sig (xn n)) x) -> (exists (y : Base M2), Un_cv_met M2 (fun (n : nat) => (f (proj1_sig (xn n)))) y))).
Proof.
move=> M1 M2 f B x.
apply conj.
elim.
move=> y H2 xn H3.
exists y.
suff: ((forall xn : nat -> {x0 : Base M1 | B x0}, Un_cv_met M1 (fun n : nat => proj1_sig (xn n)) x -> Un_cv_met M2 (fun n : nat => f (proj1_sig (xn n))) y)).
move=> H4.
apply (H4 xn H3).
apply Theorem_6_2.
apply H2.
move=> H2.
elim (classic (ClosureMet M1 B x)).
move=> H1.
elim (proj1 (Proposition_6_1_1 M1 B x) H1).
move=> xm H3.
elim (H2 (fun (n : nat) => exist B (xm n) (proj1 H3 n)) (proj2 H3)).
move=> y H4.
exists y.
apply Theorem_6_2.
move=> xn H5.
suff: (Un_cv_met M2 
(fun (n : nat) => match (even_odd_dec n) with 
| left a => f (proj1_sig (xn (proj1_sig (even_2n n a)))) 
| right a => f (proj1_sig (exist B (xm (proj1_sig (odd_S2n n a))) (proj1 H3 (proj1_sig (odd_S2n n a)))))
 end) y).
move=> H6.
move=> eps H7.
elim (H6 eps H7).
move=> k H8.
exists k.
move=> n H9. 
suff: ((f (proj1_sig (xn n))) = (match even_odd_dec (double n) with
       | left a => f (proj1_sig (xn (proj1_sig (even_2n (double n) a))))
       | right a => f (proj1_sig (exist B (xm (proj1_sig (odd_S2n (double n) a))) (proj1 H3 (proj1_sig (odd_S2n (double n) a))))) end)).
move=> H10.
rewrite H10.
apply (H8 (double n)).
apply (le_trans k n (double n)).
apply H9.
rewrite - {1} (plus_0_r n).
apply (plus_le_compat_l O n n).
apply (le_0_n n).
elim (even_odd_dec (double n)).
move=> H10.
suff: ((proj1_sig (even_2n (Nat.double n) H10)) = n).
move=> H11.
rewrite H11.
reflexivity.
suff: (forall (n m : nat), (double n) = (double m) -> n = m).
move=> H11.
apply H11.
rewrite - (proj2_sig (even_2n (Nat.double n) H10)).
reflexivity.
move=> m1 m2 H11.
elim (le_or_lt m1 m2).
move=> H12.
elim (le_lt_or_eq m1 m2 H12).
move=> H13.
apply False_ind.
apply (lt_not_le (double m1) (double m2)).
apply (lt_trans (double m1) (m1 + m2)%nat (double m2)).
apply (plus_lt_compat_l m1 m2 m1).
apply H13.
apply (plus_lt_compat_r m1 m2 m2).
apply H13.
rewrite H11.
apply (le_n (double m2)).
apply.
move=> H12.
apply False_ind.
apply (lt_not_le (double m2) (double m1)).
apply (lt_trans (double m2) (m2 + m1)%nat (double m1)).
apply (plus_lt_compat_l m2 m1 m2).
apply H12.
apply (plus_lt_compat_r m2 m1 m1).
apply H12.
rewrite H11.
apply (le_n (double m2)).
move=> H10.
apply False_ind.
apply (Nat.neq_succ_diag_l (div2 (double n))).
rewrite {2} (even_div2 (double n)).
rewrite (odd_div2 (double n)).
reflexivity.
apply H10.
apply (double_even (double n)).
rewrite {2} Nat.double_twice.
rewrite div2_double.
reflexivity.
suff: (exists (y : Base M2), Un_cv_met M2 (fun n : nat => match even_odd_dec n with
   | left a => f (proj1_sig (xn (proj1_sig (even_2n n a))))
   | right a => f (proj1_sig (exist B (xm (proj1_sig (odd_S2n n a))) (proj1 H3 (proj1_sig (odd_S2n n a))))) end) y).
elim.
move=> y0 H6.
suff: (y = y0).
move=> H7.
rewrite H7.
apply H6.
apply NNPP.
move=> H7.
suff: (dist M2 y y0 / 2 > 0).
move=> H8.
elim (H6 ((dist M2 y y0) / 2) H8).
move=> k1 H9.
elim (H4 ((dist M2 y y0) / 2) H8).
move=> k2 H10.
apply (Rlt_irrefl (dist M2 y y0)).
apply (Rle_lt_trans (dist M2 y y0) (dist M2 (f (proj1_sig (exist B (xm (max k1 k2)) (proj1 H3 (max k1 k2))))) y + dist M2 (f (proj1_sig (exist B (xm (max k1 k2)) (proj1 H3 (max k1 k2))))) y0) (dist M2 y y0)).
rewrite (dist_sym M2 (f (proj1_sig (exist B (xm (Init.Nat.max k1 k2)) (proj1 H3 (Init.Nat.max k1 k2))))) y).
apply (dist_tri M2 y y0 (f (proj1_sig (exist B (xm (Init.Nat.max k1 k2)) (proj1 H3 (Init.Nat.max k1 k2)))))).
rewrite - (eps2 (dist M2 y y0)).
apply Rplus_lt_compat.
apply (H10 (max k1 k2)).
apply (Nat.le_max_r k1 k2).
suff: ((f (proj1_sig (exist B (xm (max k1 k2)) (proj1 H3 (max k1 k2))))) = match even_odd_dec (S (double (max k1 k2))) with
        | left a => f (proj1_sig (xn (proj1_sig (even_2n (S (double (max k1 k2))) a))))
        | right a => f (proj1_sig (exist B (xm (proj1_sig (odd_S2n (S (double (max k1 k2))) a))) (proj1 H3 (proj1_sig (odd_S2n (S (double (max k1 k2))) a)))))
        end). 
move=> H11.
rewrite H11.
apply (H9 (S (double (max k1 k2)))).
apply le_S.
apply (le_trans k1 (double k1) (double (max k1 k2))).
rewrite - {1} (plus_0_r k1).
apply (plus_le_compat_l 0 k1 k1).
apply (le_0_n k1).
apply (le_trans (double k1) (k1 + (max k1 k2))%nat (double (max k1 k2))).
apply (plus_le_compat_l k1 (max k1 k2) k1).
apply (Nat.le_max_l k1 k2).
apply (plus_le_compat_r k1 (max k1 k2) (max k1 k2)).
apply (Nat.le_max_l k1 k2).
elim (even_odd_dec (S (Nat.double (Init.Nat.max k1 k2)))).
move=> H11.
apply False_ind.
apply (Nat.neq_succ_diag_l (div2 (S (double (max k1 k2))))).
rewrite {2} (even_div2 (S (Nat.double (Init.Nat.max k1 k2)))).
rewrite (odd_div2 (S (Nat.double (Init.Nat.max k1 k2)))).
reflexivity.
apply (double_odd (S (Nat.double (Init.Nat.max k1 k2)))).
rewrite {2} Nat.double_twice.
rewrite Nat.div2_succ_double.
reflexivity.
apply H11.
move=> H11.
suff: ((max k1 k2) = (proj1_sig (odd_S2n (S (Nat.double (Init.Nat.max k1 k2))) H11))).
move=> H12.
rewrite - H12.
reflexivity.
suff: (forall (n m : nat), S (double n) = S (double m) -> n = m).
move=> H12.
apply H12.
rewrite - (proj2_sig (odd_S2n (S (double (max k1 k2))) H11)).
reflexivity.
move=> m1 m2 H12.
elim (le_or_lt m1 m2).
move=> H13.
elim (le_lt_or_eq m1 m2 H13).
move=> H14.
apply False_ind.
apply (lt_not_le (double m1) (double m2)).
apply (lt_trans (double m1) (m1 + m2)%nat (double m2)).
apply (plus_lt_compat_l m1 m2 m1).
apply H14.
apply (plus_lt_compat_r m1 m2 m2).
apply H14.
rewrite (eq_add_S (double m1) (double m2) H12).
apply (le_n (double m2)).
apply.
move=> H13.
apply False_ind.
apply (lt_not_le (double m2) (double m1)).
apply (lt_trans (double m2) (m2 + m1)%nat (double m1)).
apply (plus_lt_compat_l m2 m1 m2).
apply H13.
apply (plus_lt_compat_r m2 m1 m1).
apply H13.
rewrite (eq_add_S (double m1) (double m2) H12).
apply (le_n (double m2)).
apply (eps2_Rgt_R0 (dist M2 y y0)).
elim (dist_pos M2 y y0).
apply.
move=> H8.
apply False_ind.
apply H7.
apply (proj1 (dist_refl M2 y y0) H8).
suff: ((fun n : nat => match even_odd_dec n with
     | left a => f (proj1_sig (xn (proj1_sig (even_2n n a))))
     | right a => f (proj1_sig (exist B (xm (proj1_sig (odd_S2n n a))) (proj1 H3 (proj1_sig (odd_S2n n a)))))
     end) = (fun n : nat => f (proj1_sig ((fun (m : nat) => match even_odd_dec m with
     | left a => xn (proj1_sig (even_2n m a))
     | right a => (exist B (xm (proj1_sig (odd_S2n m a))) (proj1 H3 (proj1_sig (odd_S2n m a)))) end) n)))).
move=> H6.
rewrite H6.
apply H2.
move=> eps H7.
elim (proj2 H3 eps H7).
move=> k1 H8.
elim (H5 eps H7).
move=> k2 H9.
exists (S (double (max k1 k2))).
move=> n H10.
elim (even_odd_dec n).
move=> H11.
apply (H9 (proj1_sig (even_2n n H11))).
elim (le_or_lt k2 (proj1_sig (even_2n n H11))).
apply.
move=> H12.
apply False_ind.
apply (le_not_lt (S (Nat.double (Init.Nat.max k1 k2))) n).
apply H10.
rewrite (proj2_sig (even_2n n H11)).
apply le_S.
suff: ((proj1_sig (even_2n n H11)) < max k1 k2)%nat.
move=> H13.
apply (lt_trans (double (proj1_sig (even_2n n H11))) ((proj1_sig (even_2n n H11)) + (max k1 k2))%nat (double (max k1 k2))).
apply (plus_lt_compat_l (proj1_sig (even_2n n H11)) (max k1 k2) (proj1_sig (even_2n n H11))).
apply H13.
apply (plus_lt_compat_r (proj1_sig (even_2n n H11)) (max k1 k2) (max k1 k2)).
apply H13.
apply (lt_le_trans (proj1_sig (even_2n n H11)) k2 (max k1 k2)).
apply H12.
apply (Nat.le_max_r k1 k2).
move=> H11.
apply (H8 (proj1_sig (odd_S2n n H11))).
elim (le_or_lt k1 (proj1_sig (odd_S2n n H11))).
apply.
move=> H12.
apply False_ind.
apply (le_not_lt (S (Nat.double (Init.Nat.max k1 k2))) n).
apply H10.
rewrite (proj2_sig (odd_S2n n H11)).
apply lt_n_S.
suff: ((proj1_sig (odd_S2n n H11)) < max k1 k2)%nat.
move=> H13.
apply (lt_trans (double (proj1_sig (odd_S2n n H11))) ((proj1_sig (odd_S2n n H11)) + (max k1 k2))%nat (double (max k1 k2))).
apply (plus_lt_compat_l (proj1_sig (odd_S2n n H11)) (max k1 k2) (proj1_sig (odd_S2n n H11))).
apply H13.
apply (plus_lt_compat_r (proj1_sig (odd_S2n n H11)) (max k1 k2) (max k1 k2)).
apply H13.
apply (lt_le_trans (proj1_sig (odd_S2n n H11)) k1 (max k1 k2)).
apply H12.
apply (Nat.le_max_l k1 k2).
apply functional_extensionality.
move=> n.
elim (even_odd_dec n).
move=> H6.
reflexivity.
move=> H6.
reflexivity.
move=> H1.
suff: (exists (dlt : R), dlt > 0 /\ forall (y : Base M1), (NeighborhoodMet M1 x dlt y) -> ~ In (Base M1) B y).
elim.
move=> dlt H3.
exists (f x).
move=> eps H4.
exists dlt.
apply conj.
apply (proj1 H3).
move=> x0 H5.
apply False_ind.
apply (proj2 H3 x0).
apply (proj2 H5).
apply (proj1 H5).
apply NNPP.
move=> H3.
apply H1.
move=> eps H4.
apply NNPP.
move=> H5.
apply H3.
exists eps.
apply conj.
apply H4.
move=> y H6 H7.
apply H5.
exists y.
apply conj.
apply H6.
apply H7.
Qed.

Lemma Proposition_6_3 : forall (M1 M2 : Metric_Space) (f : Base M1 -> Base M2) (B : Ensemble (Base M1)) (x : Base M1), (ClosureMet M1 B x) -> (forall (y1 y2 : Base M2), limit_in M1 M2 f B x y1 -> limit_in M1 M2 f B x y2 -> y1 = y2).
Proof.
move=> M1 M2 f B x H1 y1 y2 H2 H3.
apply NNPP.
move=> H4.
suff: (dist M2 y1 y2 / 2 > 0).
move=> H5.
elim (H2 ((dist M2 y1 y2) / 2) H5).
move=> dlt1 H6.
elim (H3 ((dist M2 y1 y2) / 2) H5).
move=> dlt2 H7.
elim (H1 (Rmin dlt1 dlt2)).
move=> x0 H8.
apply (Rlt_irrefl (dist M2 y1 y2)).
apply (Rle_lt_trans (dist M2 y1 y2) (dist M2 (f x0) y1 + dist M2 (f x0) y2) (dist M2 y1 y2)).
rewrite (dist_sym M2 (f x0) y1).
apply (dist_tri M2 y1 y2 (f x0)).
rewrite - (eps2 (dist M2 y1 y2)).
apply Rplus_lt_compat.
apply (proj2 H6 x0).
apply conj.
apply (proj2 H8).
apply (Rlt_le_trans (dist M1 x0 x) (Rmin dlt1 dlt2) dlt1).
apply (proj1 H8).
apply (Rmin_l dlt1 dlt2).
apply (proj2 H7 x0).
apply conj.
apply (proj2 H8).
apply (Rlt_le_trans (dist M1 x0 x) (Rmin dlt1 dlt2) dlt2).
apply (proj1 H8).
apply (Rmin_r dlt1 dlt2).
apply (Rmin_pos dlt1 dlt2 (proj1 H6) (proj1 H7)).
apply (eps2_Rgt_R0 (dist M2 y1 y2)).
elim (dist_pos M2 y1 y2).
apply.
move=> H5.
apply False_ind.
apply H4.
apply (proj1 (dist_refl M2 y1 y2) H5).
Qed.

Lemma Proposition_2_3_met : forall (M : Metric_Space) (an : nat -> Base M)  (x y : Base M), (Un_cv_met M an x) -> (Un_cv_met M an y) -> x = y.
Proof.
move=> M an a b H1 H2. 
apply NNPP.
move=> H3.
suff: (dist M a b / 2 > 0).
move=> H4.
elim (H1 ((dist M a b) / 2) H4).
move=> m1 H5.
elim (H2 ((dist M a b) / 2) H4).
move=> m2 H6.
apply (Rlt_irrefl (dist M a b)).
apply (Rle_lt_trans (dist M a b) (dist M (an (max m1 m2)) a + dist M (an (max m1 m2)) b) (dist M a b)).
rewrite (dist_sym M (an (max m1 m2)) a).
apply (dist_tri M a b (an (max m1 m2))).
rewrite - (eps2 (dist M a b)).
apply Rplus_lt_compat.
apply (H5 (max m1 m2)).
apply (Nat.le_max_l m1 m2).
apply (H6 (max m1 m2)).
apply (Nat.le_max_r m1 m2).
apply (eps2_Rgt_R0 (dist M a b)).
elim (dist_pos M a b).
apply.
move=> H4.
apply False_ind.
apply H3.
apply (proj1 (dist_refl M a b) H4).
Qed.


Definition BoundedMet (M : Metric_Space) (A : Ensemble (Base M)) := exists (x : Base M) (r : R), Included (Base M) A (NeighborhoodMet M x r).

Lemma BoundedMetDef2 : forall (M : Metric_Space) (A : Ensemble (Base M)), (BoundedMet M A) -> forall (x : Base M), exists (r : R), Included (Base M) A (NeighborhoodMet M x r).
Proof.
move=> M A H1 x.
elim H1.
move=> x1.
elim.
move=> r H2.
exists ((dist M x x1) + r).
move=> a H3.
unfold NeighborhoodMet.
apply (Rle_lt_trans (dist M a x) (dist M x x1 + dist M x1 a) ((dist M x x1) + r)).
rewrite (dist_sym M a x).
apply (dist_tri M x a x1).
apply Rplus_lt_compat_l.
rewrite (dist_sym M x1 a).
apply (H2 a H3).
Qed.

Lemma Proposition_6_4_1 : forall (M1 M2 : Metric_Space) (f : Base M1 -> Base M2) (B : Ensemble (Base M1)) (x : Base M1) (y : Base M2), (limit_in M1 M2 f B x y <-> (forall (eps : R), eps > 0 -> (exists (dlt : R), dlt > 0 /\ Included (Base M2) (Im (Base M1) (Base M2) (Intersection (Base M1) (NeighborhoodMet M1 x dlt) B) f) (NeighborhoodMet M2 y eps)))).
Proof.
move=> M1 M2 f B x y.
apply conj.
move=> H2 eps H3.
elim (H2 eps H3).
move=> dlt H4.
exists dlt.
apply conj.
apply (proj1 H4).
move=> y0.
elim.
move=> x0 H5.
move=> y1 H6.
rewrite H6.
apply (proj2 H4 x0).
elim H5.
move=> x1 H7 H8.
apply conj.
apply H8.
apply H7.
move=> H2 eps H3.
elim (H2 eps H3).
move=> dlt H4.
exists dlt.
apply conj.
apply (proj1 H4).
move=> x0 H5.
apply (proj2 H4 (f x0)).
apply (Im_intro (Base M1) (Base M2) (Intersection (Base M1) (NeighborhoodMet M1 x dlt) B) f x0).
apply (Intersection_intro (Base M1) (NeighborhoodMet M1 x dlt) B).
apply (proj2 H5).
apply (proj1 H5).
reflexivity.
Qed.

Lemma Proposition_6_4_2 : forall (M1 M2 : Metric_Space) (f : Base M1 -> Base M2) (B : Ensemble (Base M1)) (x : Base M1), ((exists (y : Base M2), limit_in M1 M2 f B x y) -> (exists (dlt : R), dlt > 0 /\ (BoundedMet M2 (Im (Base M1) (Base M2) (Intersection (Base M1) (NeighborhoodMet M1 x dlt) B) f)))).
Proof.
move=> M1 M2 f B x.
elim.
move=> y H2.
elim (proj1 (Proposition_6_4_1 M1 M2 f B x y) H2 1).
move=> dlt H3.
exists dlt.
apply conj.
apply (proj1 H3).
exists y.
exists 1.
apply (proj2 H3).
apply Rlt_0_1.
Qed.

Definition ContinuousMet (M1 M2 : Metric_Space) (f : Base M1 -> Base M2) (A : Ensemble (Base M1)) (x : Base M1) := limit_in M1 M2 f A x (f x).

Lemma Proposition_6_5_2 : forall (M1 M2 : Metric_Space) (f : Base M1 -> Base M2) (B : Ensemble (Base M1)) (x : Base M1), (limit_in M1 M2 f B x (f x) <-> (forall (eps : R), eps > 0 -> (exists (dlt : R), dlt > 0 /\ Included (Base M2) (Im (Base M1) (Base M2) (Intersection (Base M1) (NeighborhoodMet M1 x dlt) B) f) (NeighborhoodMet M2 (f x) eps)))).
Proof.
move=> M1 M2 f B x.
apply (Proposition_6_4_1 M1 M2 f B x (f x)).
Qed.

Lemma Proposition_6_5_3 : forall (M1 M2 : Metric_Space) (f : Base M1 -> Base M2) (B : Ensemble (Base M1)) (x : Base M1), (limit_in M1 M2 f B x (f x) <-> limit_in M1 M2 f (fun (z : Base M1) => B z /\ z <> x) x (f x)).
Proof.
move=> M1 M2 f B x.
apply conj.
move=> H2 eps H3.
elim (H2 eps H3).
move=> dlt H4.
exists dlt.
apply conj.
apply (proj1 H4).
move=> x0 H5.
apply (proj2 H4 x0).
apply conj.
apply (proj1 (proj1 H5)).
apply (proj2 H5).
move=> H2 eps H3.
elim (H2 eps H3).
move=> dlt H4.
exists dlt.
apply conj.
apply (proj1 H4).
move=> x0 H5.
elim (classic (x0 = x)).
move=> H6.
rewrite H6.
rewrite (proj2 (dist_refl M2 (f x) (f x))).
apply H3.
reflexivity.
move=> H6.
apply (proj2 H4 x0).
apply conj.
apply conj.
apply (proj1 H5).
apply H6.
apply (proj2 H5).
Qed.

Lemma Theorem_6_6_1_1_Rn : forall (M1 : Metric_Space) (N : nat) (f g : Base M1 -> Rn N) (B : Ensemble (Base M1)) (x : Base M1) (fx gx : Rn N), (limit_in M1 (Rn_met N) f B x fx) -> (limit_in M1 (Rn_met N) g B x gx) -> (limit_in M1 (Rn_met N) (fun (r : Base M1) => Rnplus N (f r) (g r)) B x (Rnplus N fx gx)).
Proof.
move=> M1 N f g B x fx gx H1 H2.
apply (proj2 (Theorem_6_2 M1 (Rn_met N) (fun r : Base M1 => Rnplus N (f r) (g r)) B x (Rnplus N fx gx))).
move=> xn H4.
apply (Proposition_4_6_1 N).
apply (proj1 (Theorem_6_2 M1 (Rn_met N) f B x fx) H1).
apply H4.
apply (proj1 (Theorem_6_2 M1 (Rn_met N) g B x gx) H2).
apply H4.
Qed.

Lemma Theorem_6_6_1_1_R : forall (M1 : Metric_Space) (f g : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1) (fx gx : R), (limit_in M1 R_met f B x fx) -> (limit_in M1 R_met g B x gx) -> (limit_in M1 R_met (fun (r : Base M1) => (f r) + (g r)) B x (fx + gx)).
Proof.
move=> M1 f g B x fx gx H1 H2.
apply (proj2 (Theorem_6_2 M1 R_met (fun r : Base M1 => (f r) + (g r)) B x (fx + gx))).
move=> xn H4.
apply Theorem_2_5_1_plus.
apply (proj1 (Theorem_6_2 M1 R_met f B x fx) H1).
apply H4.
apply (proj1 (Theorem_6_2 M1 R_met g B x gx) H2).
apply H4.
Qed.

Lemma Theorem_6_6_1_2_Rn : forall (M1 : Metric_Space) (N : nat) (f g : Base M1 -> Rn N) (B : Ensemble (Base M1)) (x : Base M1) (fx gx : Rn N), (limit_in M1 (Rn_met N) f B x fx) -> (limit_in M1 (Rn_met N) g B x gx) -> (limit_in M1 (Rn_met N) (fun (r : Base M1) => Rnminus N (f r) (g r)) B x (Rnminus N fx gx)).
Proof.
move=> M1 N f g B x fx gx H2 H3.
apply (proj2 (Theorem_6_2 M1 (Rn_met N) (fun r : Base M1 => Rnminus N (f r) (g r)) B x (Rnminus N fx gx))).
move=> xn H4.
apply (Proposition_4_6_2 N).
apply (proj1 (Theorem_6_2 M1 (Rn_met N) f B x fx) H2).
apply H4.
apply (proj1 (Theorem_6_2 M1 (Rn_met N) g B x gx) H3).
apply H4.
Qed.

Lemma Theorem_6_6_1_2_R : forall (M1 : Metric_Space) (f g : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1) (fx gx : R), (limit_in M1 R_met f B x fx) -> (limit_in M1 R_met g B x gx) -> (limit_in M1 R_met (fun (r : Base M1) => (f r) - (g r)) B x (fx - gx)).
Proof.
move=> M1 f g B x fx gx H2 H3.
apply (proj2 (Theorem_6_2 M1 R_met (fun r : Base M1 => (f r) - (g r)) B x (fx - gx))).
move=> xn H4.
apply Theorem_2_5_1_minus.
apply (proj1 (Theorem_6_2 M1 R_met f B x fx) H2).
apply H4.
apply (proj1 (Theorem_6_2 M1 R_met g B x gx) H3).
apply H4.
Qed.

Lemma Theorem_6_6_1_3_Rn : forall (M1 : Metric_Space) (N : nat) (f : Base M1 -> Rn N) (c : R) (B : Ensemble (Base M1)) (x : Base M1) (fx : Rn N), (limit_in M1 (Rn_met N) f B x fx) -> (limit_in M1 (Rn_met N) (fun (r : Base M1) => Rnmult N c (f r)) B x (Rnmult N c fx)).
Proof.
move=> M1 N f c B x fx H2.
apply (proj2 (Theorem_6_2 M1 (Rn_met N) (fun r : Base M1 => Rnmult N c (f r)) B x (Rnmult N c fx))).
move=> xn H3.
apply (Proposition_4_6_3 N).
apply (proj1 (Theorem_6_2 M1 (Rn_met N) f B x fx) H2).
apply H3.
Qed.

Lemma Theorem_6_6_1_3_R : forall (M1 : Metric_Space) (f : Base M1 -> R) (c : R) (B : Ensemble (Base M1)) (x : Base M1) (fx : R), (limit_in M1 R_met f B x fx) -> (limit_in M1 R_met (fun (r : Base M1) => c * (f r)) B x (c * fx)).
Proof.
move=> M1 f c B x fx H2.
apply (proj2 (Theorem_6_2 M1 R_met (fun r : Base M1 => c * (f r)) B x (c * fx))).
move=> xn H3.
apply Theorem_2_5_1_mult.
move=> eps H4.
exists O.
move=> n H5.
rewrite (proj2 (R_dist_refl c c)).
apply H4.
reflexivity.
apply (proj1 (Theorem_6_2 M1 R_met f B x fx) H2).
apply H3.
Qed.

Lemma Theorem_6_6_1_4_Rn : forall (M1 : Metric_Space) (N : nat) (f : Base M1 -> Rn N) (B : Ensemble (Base M1)) (x : Base M1) (fx : Rn N), (limit_in M1 (Rn_met N) f B x fx) -> (limit_in M1 (Rn_met N) (fun (r : Base M1) => Rnopp N (f r)) B x (Rnopp N fx)).
Proof.
move=> M1 N f B x fx H2.
apply (proj2 (Theorem_6_2 M1 (Rn_met N) (fun r : Base M1 => Rnopp N (f r)) B x (Rnopp N fx))).
move=> xn H3.
apply (Proposition_4_6_4 N).
apply (proj1 (Theorem_6_2 M1 (Rn_met N) f B x fx) H2).
apply H3.
Qed.

Lemma Theorem_6_6_1_4_R : forall (M1 : Metric_Space) (f : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1) (fx : R), (limit_in M1 R_met f B x fx) -> (limit_in M1 R_met (fun (r : Base M1) => - (f r)) B x (- fx)).
Proof.
move=> M1 f B x fx H2.
apply (proj2 (Theorem_6_2 M1 R_met (fun r : Base M1 => - (f r)) B x (- fx))).
move=> xn H3.
apply Theorem_2_5_1_opp.
apply (proj1 (Theorem_6_2 M1 R_met f B x fx) H2).
apply H3.
Qed.

Lemma Theorem_6_6_2_1_C : forall (M1 : Metric_Space) (f g : Base M1 -> C) (B : Ensemble (Base M1)) (x : Base M1) (fx gx : C), (limit_in M1 (Rn_met 2) f B x fx) -> (limit_in M1 (Rn_met 2) g B x gx) -> (limit_in M1 (Rn_met 2) (fun (r : Base M1) => Cmult (f r) (g r)) B x (Cmult fx gx)).
Proof.
move=> M1 f g B x fx gx H2 H3.
apply (proj2 (Theorem_6_2 M1 (Rn_met 2) (fun r : Base M1 => Cmult (f r) (g r)) B x (Cmult fx gx))).
move=> xn H4.
apply Proposition_4_9_mult.
apply (proj1 (Theorem_6_2 M1 (Rn_met 2) f B x fx) H2).
apply H4.
apply (proj1 (Theorem_6_2 M1 (Rn_met 2) g B x gx) H3).
apply H4.
Qed.

Lemma Theorem_6_6_2_1_R : forall (M1 : Metric_Space) (f g : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1) (fx gx : R), (limit_in M1 R_met f B x fx) -> (limit_in M1 R_met g B x gx) -> (limit_in M1 R_met (fun (r : Base M1) => (f r) * (g r)) B x (fx * gx)).
Proof.
move=> M1 f g B x fx gx H2 H3.
apply (proj2 (Theorem_6_2 M1 R_met (fun r : Base M1 => (f r) * (g r)) B x (fx * gx))).
move=> xn H4.
apply Theorem_2_5_1_mult.
apply (proj1 (Theorem_6_2 M1 R_met f B x fx) H2).
apply H4.
apply (proj1 (Theorem_6_2 M1 R_met g B x gx) H3).
apply H4.
Qed.

Lemma Theorem_6_6_2_2_C : forall (M1 : Metric_Space) (f g : Base M1 -> C) (B : Ensemble (Base M1)) (x : Base M1) (fx gx : C), (gx <> CO) -> (limit_in M1 (Rn_met 2) f B x fx) -> (limit_in M1 (Rn_met 2) g B x gx) -> (limit_in M1 (Rn_met 2) (fun (r : Base M1) => Cmult (f r) (Cinv (g r))) B x (Cmult fx (Cinv gx))).
Proof.
move=> M1 f g B x fx gx H2 H3 H4.
apply (proj2 (Theorem_6_2 M1 (Rn_met 2) (fun r : Base M1 => Cmult (f r) (Cinv (g r))) B x (Cmult fx (Cinv gx)))).
move=> xn H5.
apply Proposition_4_9_div.
apply H2.
apply (proj1 (Theorem_6_2 M1 (Rn_met 2) f B x fx) H3).
apply H5.
apply (proj1 (Theorem_6_2 M1 (Rn_met 2) g B x gx) H4).
apply H5.
Qed.

Lemma Theorem_6_6_2_2_R : forall (M1 : Metric_Space) (f g : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1) (fx gx : R), (gx <> 0) -> (limit_in M1 R_met f B x fx) -> (limit_in M1 R_met g B x gx) -> (limit_in M1 R_met (fun (r : Base M1) => (f r) / (g r)) B x (fx / gx)).
Proof.
move=> M1 f g B x fx gx H2 H3 H4.
apply (proj2 (Theorem_6_2 M1 R_met (fun r : Base M1 => (f r) / (g r)) B x (fx / gx))).
move=> xn H5.
apply Theorem_2_5_1_div.
apply (proj1 (Theorem_6_2 M1 R_met f B x fx) H3).
apply H5.
apply (proj1 (Theorem_6_2 M1 R_met g B x gx) H4).
apply H5.
apply H2.
Qed.

Lemma Theorem_6_6_2_3_C : forall (M1 : Metric_Space) (f : Base M1 -> C) (B : Ensemble (Base M1)) (x : Base M1) (fx : C), (fx <> CO) -> (limit_in M1 (Rn_met 2) f B x fx) -> (limit_in M1 (Rn_met 2) (fun (r : Base M1) => Cinv (f r)) B x (Cinv fx)).
Proof.
move=> M1 f B x fx H2 H3.
apply (proj2 (Theorem_6_2 M1 (Rn_met 2) (fun r : Base M1 => Cinv (f r)) B x (Cinv fx))).
move=> xn H4.
apply Proposition_4_9_inv.
apply H2.
apply (proj1 (Theorem_6_2 M1 (Rn_met 2) f B x fx) H3).
apply H4.
Qed.

Lemma Theorem_6_6_2_3_R : forall (M1 : Metric_Space) (f : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1) (fx : R), (fx <> 0) -> (limit_in M1 R_met f B x fx) -> (limit_in M1 R_met (fun (r : Base M1) => / (f r)) B x (/ fx)).
Proof.
move=> M1 f B x fx H2 H3.
suff: ((fun r : Base M1 => / f r) = (fun r : Base M1 => 1 / f r)).
move=> H4.
suff: (/ fx = 1 / fx).
move=> H5.
rewrite H4.
rewrite H5.
apply Theorem_6_6_2_2_R.
apply H2.
move=> eps H6.
exists 1.
apply conj.
apply Rlt_0_1.
move=> x0 H7.
rewrite (proj2 (dist_refl R_met 1 1)).
apply H6.
reflexivity.
apply H3.
unfold Rdiv.
rewrite (Rmult_1_l (/ fx)).
reflexivity.
apply functional_extensionality.
move=> r.
unfold Rdiv.
rewrite (Rmult_1_l (/ f r)).
reflexivity.
Qed.

Lemma Theorem_6_6_3_1_Rn : forall (M1 : Metric_Space) (N : nat) (f g : Base M1 -> Rn N) (B : Ensemble (Base M1)) (x : Base M1), (ContinuousMet M1 (Rn_met N) f B x) -> (ContinuousMet M1 (Rn_met N) g B x) -> (ContinuousMet M1 (Rn_met N) (fun (r : Base M1) => Rnplus N (f r) (g r)) B x).
Proof.
move=> M1 N f g B x H1 H2.
apply Theorem_6_6_1_1_Rn.
apply H1.
apply H2.
Qed.

Lemma Theorem_6_6_3_1_R : forall (M1 : Metric_Space) (f g : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1), (ContinuousMet M1 R_met f B x) -> (ContinuousMet M1 R_met g B x) -> (ContinuousMet M1 R_met (fun (r : Base M1) => (f r) + (g r)) B x).
Proof.
move=> M1 f g B x H1 H2.
apply Theorem_6_6_1_1_R.
apply H1.
apply H2.
Qed.

Lemma Theorem_6_6_3_2_Rn : forall (M1 : Metric_Space) (N : nat) (f g : Base M1 -> Rn N) (B : Ensemble (Base M1)) (x : Base M1), (ContinuousMet M1 (Rn_met N) f B x) -> (ContinuousMet M1 (Rn_met N) g B x) -> (ContinuousMet M1 (Rn_met N) (fun (r : Base M1) => Rnminus N (f r) (g r)) B x).
Proof.
move=> M1 N B f g x H1 H2.
apply Theorem_6_6_1_2_Rn.
apply H1.
apply H2.
Qed.

Lemma Theorem_6_6_3_2_R : forall (M1 : Metric_Space) (f g : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1), (ContinuousMet M1 R_met f B x) -> (ContinuousMet M1 R_met g B x) -> (ContinuousMet M1 R_met (fun (r : Base M1) => (f r) - (g r)) B x).
Proof.
move=> M1 B f g x H1 H2.
apply Theorem_6_6_1_2_R.
apply H1.
apply H2.
Qed.

Lemma Theorem_6_6_3_3_Rn : forall (M1 : Metric_Space) (N : nat) (f : Base M1 -> Rn N) (c : R) (B : Ensemble (Base M1)) (x : Base M1), (ContinuousMet M1 (Rn_met N) f B x) -> (ContinuousMet M1 (Rn_met N) (fun (r : Base M1) => Rnmult N c (f r)) B x).
Proof.
move=> M1 N f c B x H1.
apply Theorem_6_6_1_3_Rn.
apply H1.
Qed.

Lemma Theorem_6_6_3_3_R : forall (M1 : Metric_Space) (f : Base M1 -> R) (c : R) (B : Ensemble (Base M1)) (x : Base M1), (ContinuousMet M1 R_met f B x) -> (ContinuousMet M1 R_met (fun (r : Base M1) => c * (f r)) B x).
Proof.
move=> M1 f c B x H1.
apply Theorem_6_6_1_3_R.
apply H1.
Qed.

Lemma Theorem_6_6_3_4_Rn : forall (M1 : Metric_Space) (N : nat) (f : Base M1 -> Rn N) (B : Ensemble (Base M1)) (x : Base M1), (ContinuousMet M1 (Rn_met N) f B x) -> (ContinuousMet M1 (Rn_met N) (fun (r : Base M1) => Rnopp N (f r)) B x).
Proof.
move=> M1 N f B x H1.
apply Theorem_6_6_1_4_Rn.
apply H1.
Qed.

Lemma Theorem_6_6_3_4_R : forall (M1 : Metric_Space) (f : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1), (ContinuousMet M1 R_met f B x) -> (ContinuousMet M1 R_met (fun (r : Base M1) => - (f r)) B x).
Proof.
move=> M1 f B x H1.
apply Theorem_6_6_1_4_R.
apply H1.
Qed.

Lemma Theorem_6_6_3_5_C : forall (M1 : Metric_Space) (f g : Base M1 -> C) (B : Ensemble (Base M1)) (x : Base M1), (ContinuousMet M1 (Rn_met 2) f B x) -> (ContinuousMet M1 (Rn_met 2) g B x) -> (ContinuousMet M1 (Rn_met 2) (fun (r : Base M1) => Cmult (f r) (g r)) B x).
Proof.
move=> M1 f g B x H1 H2.
apply Theorem_6_6_2_1_C.
apply H1.
apply H2.
Qed.

Lemma Theorem_6_6_3_5_R : forall (M1 : Metric_Space) (f g : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1), (ContinuousMet M1 R_met f B x) -> (ContinuousMet M1 R_met g B x) -> (ContinuousMet M1 R_met (fun (r : Base M1) => (f r) * (g r)) B x).
Proof.
move=> M1 f g B x H1 H2.
apply Theorem_6_6_2_1_R.
apply H1.
apply H2.
Qed.

Lemma Theorem_6_6_3_6_C : forall (M1 : Metric_Space) (f g : Base M1 -> C) (B : Ensemble (Base M1)) (x : Base M1), (g x <> CO) -> (ContinuousMet M1 (Rn_met 2) f B x) -> (ContinuousMet M1 (Rn_met 2) g B x) -> (ContinuousMet M1 (Rn_met 2) (fun (r : Base M1) => Cmult (f r) (Cinv (g r))) B x).
Proof.
move=> M1 f g B x H1 H2 H3.
apply Theorem_6_6_2_2_C.
apply H1.
apply H2.
apply H3.
Qed.

Lemma Theorem_6_6_3_6_R : forall (M1 : Metric_Space) (f g : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1), (g x <> 0) -> (ContinuousMet M1 R_met f B x) -> (ContinuousMet M1 R_met g B x) -> (ContinuousMet M1 R_met (fun (r : Base M1) => (f r) / (g r)) B x).
Proof.
move=> M1 f g B x H1 H2 H3.
apply Theorem_6_6_2_2_R.
apply H1.
apply H2.
apply H3.
Qed.

Lemma Theorem_6_6_3_7_C : forall (M1 : Metric_Space) (f : Base M1 -> C) (B : Ensemble (Base M1)) (x : Base M1), (f x <> CO) -> (ContinuousMet M1 (Rn_met 2) f B x) -> (ContinuousMet M1 (Rn_met 2) (fun (r : Base M1) => Cinv (f r)) B x).
Proof.
move=> M1 f B x H1 H2.
apply Theorem_6_6_2_3_C.
apply H1.
apply H2.
Qed.

Lemma Theorem_6_6_3_7_R : forall (M1 : Metric_Space) (f : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1), (f x <> 0) -> (ContinuousMet M1 R_met f B x) -> (ContinuousMet M1 R_met (fun (r : Base M1) => / (f r)) B x).
Proof.
move=> M1 f B x H1 H2.
apply Theorem_6_6_2_3_R.
apply H1.
apply H2.
Qed.

Lemma Theorem_6_6_4 : forall (M1 : Metric_Space) (f g : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1) (fx gx : R), (ClosureMet M1 B x) -> (limit_in M1 R_met f B x fx) -> (limit_in M1 R_met g B x gx) -> (exists (eps : R), eps > 0 /\ forall (a : Base M1), In (Base M1) (Intersection (Base M1) (NeighborhoodMet M1 x eps) B) a -> f a <= g a) -> fx <= gx.
Proof.
move=> M1 f g B x fx gx H1 H2 H3.
elim.
move=> eps H4.
elim (proj1 (Proposition_6_1_1 M1 B x) H1).
move=> an H5. 
apply (Theorem_2_6_2 (fun (n : nat) => f (an n)) (fun (n : nat) => g (an n)) fx gx).
apply (proj1 (Theorem_6_2 M1 R_met f B x fx) H2 (fun (n : nat) => exist B (an n) (proj1 H5 n))).
suff: ((fun n : nat => proj1_sig (exist B (an n) (proj1 H5 n))) = an).
move=> H6.
rewrite H6.
apply (proj2 H5).
apply functional_extensionality.
move=> x0.
reflexivity.
apply (proj1 (Theorem_6_2 M1 R_met g B x gx) H3 (fun (n : nat) => exist B (an n) (proj1 H5 n))).
suff: ((fun n : nat => proj1_sig (exist B (an n) (proj1 H5 n))) = an).
move=> H6.
rewrite H6.
apply (proj2 H5).
apply functional_extensionality.
move=> x0.
reflexivity.
elim (proj2 H5 eps (proj1 H4)).
move=> N H6.
exists N.
move=> n H7.
apply (proj2 H4 (an n)).
apply Intersection_intro.
apply (H6 n H7).
apply (proj1 H5 n).
Qed.

Lemma Theorem_6_7_1 : forall (M1 M2 : Metric_Space) (f : Base M1 -> Base M2) (B : Ensemble (Base M1)) (x : Base M1) (y : Base M2), ClosureMet M1 B x -> limit_in M1 M2 f B x y -> ClosureMet M2 (Im (Base M1) (Base M2) B f) y.
Proof.
move=> M1 M2 f B x y H1 H2.
apply (proj2 (Proposition_6_1_1 M2 (Im (Base M1) (Base M2) B f) y)).
elim (proj1 (Proposition_6_1_1 M1 B x)).
move=> a H3.
exists (fun (n : nat) => f (a n)).
apply conj.
move=> n.
apply (Im_intro (Base M1) (Base M2) B f (a n)).
apply (proj1 H3 n).
reflexivity.
suff: ((fun n : nat => f (a n)) = (fun n : nat => f (proj1_sig (exist B (a n) (proj1 H3 n))))).
move=> H4.
rewrite H4.
apply (proj1 (Theorem_6_2 M1 M2 f B x y)).
apply H2.
suff: ((fun n : nat => proj1_sig (exist B (a n) (proj1 H3 n))) = a).
move=> H5.
rewrite H5.
apply (proj2 H3).
apply functional_extensionality.
move=> n.
reflexivity.
apply functional_extensionality.
move=> n.
reflexivity.
apply H1.
Qed.

Lemma Theorem_6_7_2 : forall (M1 M2 M3 : Metric_Space) (f : Base M1 -> Base M2) (g : Base M2 -> Base M3) (B : Ensemble (Base M1)) (C : Ensemble (Base M2)) (x : Base M1) (y : Base M2) (z : Base M3), (Included (Base M2) (Im (Base M1) (Base M2) B f) C) -> limit_in M1 M2 f B x y -> limit_in M2 M3 g C y z -> limit_in M1 M3 (fun (r : Base M1) => g (f r)) B x z.
Proof.
move=> M1 M2 M3 f g B C x y z H1 H3 H4.
move=> eps H5.
elim (H4 eps H5).
move=> dlt H6.
elim (H3 dlt (proj1 H6)).
move=> alp H7.
exists alp.
apply conj.
apply (proj1 H7).
move=> x0 H8.
apply (proj2 H6 (f x0)).
apply conj.
apply (H1 (f x0)).
apply (Im_intro (Base M1) (Base M2) B f x0).
apply (proj1 H8).
reflexivity.
apply (proj2 H7 x0).
apply H8.
Qed.

Lemma Theorem_6_7_3 : forall (M1 M2 M3 : Metric_Space) (f : Base M1 -> Base M2) (g : Base M2 -> Base M3) (B : Ensemble (Base M1)) (C : Ensemble (Base M2)) (x : Base M1), (Included (Base M2) (Im (Base M1) (Base M2) B f) C) -> ContinuousMet M1 M2 f B x -> ContinuousMet M2 M3 g C (f x) -> ContinuousMet M1 M3 (fun (r : Base M1) => g (f r)) B x.
Proof.
move=> M1 M2 M3 f g B C x H1 H3 H4.
apply (Theorem_6_7_2 M1 M2 M3 f g B C x (f x) (g (f x)) H1).
apply H3.
apply H4.
Qed.

Lemma Theorem_6_8_1 : forall (M1 : Metric_Space) (N : nat) (f : Base M1 -> Rn N) (B : Ensemble (Base M1)) (x : Base M1) (y : Rn N), (limit_in M1 (Rn_met N) f B x y <-> forall (n : Count N), limit_in M1 R_met (fun (r : Base M1) => (f r n)) B x (y n)).
Proof.
move=> M1 N f B x y.
apply conj.
move=> H2.
move=> n.
apply (proj2 (Theorem_6_2 M1 R_met (fun r : Base M1 => f r n) B x (y n))).
move=> xn H3.
apply (proj1 (Theorem_4_5_1 N (fun (n0 : nat) => f (proj1_sig (xn n0))) y)).
apply (proj1 (Theorem_6_2 M1 (Rn_met N) f B x y) H2).
apply H3.
move=> H2.
apply (proj2 (Theorem_6_2 M1 (Rn_met N) f B x y)).
move=> xn H3.
apply (proj2 (Theorem_4_5_1 N (fun (n0 : nat) => f (proj1_sig (xn n0))) y)).
move=> n.
apply (proj1 (Theorem_6_2 M1 R_met (fun r : Base M1 => f r n) B x (y n)) (H2 n)).
apply H3.
Qed.

Lemma Theorem_6_8_2 : forall (M1 : Metric_Space) (N : nat) (f : Base M1 -> Rn N) (B : Ensemble (Base M1)) (x : Base M1), (ContinuousMet M1 (Rn_met N) f B x <-> forall (n : Count N), ContinuousMet M1 R_met (fun (r : Base M1) => (f r n)) B x).
Proof.
move=> M1 N f B x.
apply (Theorem_6_8_1 M1 N f B x (f x)).
Qed.

Definition limit_inf_R (M : Metric_Space) (f : (Base M) -> R) (B : Ensemble (Base M)) (x : Base M) := forall (m : R), exists (alp : R), alp > 0 /\ (forall x0 : Base M, B x0 /\ dist M x0 x < alp -> (f x0) > m).

Definition limit_minf_R (M : Metric_Space) (f : (Base M) -> R) (B : Ensemble (Base M)) (x : Base M) := forall (m : R), exists (alp : R), alp > 0 /\ (forall x0 : Base M, B x0 /\ dist M x0 x < alp -> (f x0) < m).


Lemma Proposition_6_9_1 : forall (M1 : Metric_Space) (f g : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1), limit_inf_R M1 f B x -> (exists (c : R), forall (y : Base M1), In (Base M1) B y -> g y >= c) -> limit_inf_R M1 (fun (r : Base M1) => (f r) + (g r)) B x.
Proof.
move=> M1 f g B x H2.
elim.
move=> c H3.
move=> M.
elim (H2 (M - c)).
move=> alp H4.
exists alp.
apply conj.
apply (proj1 H4).
move=> x0 H5.
rewrite - (Rplus_0_r M).
rewrite - (Rplus_opp_l c).
rewrite - (Rplus_assoc M (- c) c).
apply (Rplus_lt_le_compat (M - c) (f x0) c (g x0)).
apply (proj2 H4 x0).
apply H5.
apply (Rge_le (g x0) c).
apply (H3 x0).
apply (proj1 H5).
Qed.

Lemma Proposition_6_9_2 : forall (M1 : Metric_Space) (f g : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1), limit_inf_R M1 f B x -> (exists (c : R), c > 0 /\ forall (y : Base M1), In (Base M1) B y -> g y >= c) -> limit_inf_R M1 (fun (r : Base M1) => (f r) * (g r)) B x.
Proof.
move=> M1 f g B x H2.
elim.
move=> c H3 M.
elim (Rlt_or_le M 0).
move=> H4.
elim (H2 0).
move=> alp H5.
exists alp.
apply conj.
apply (proj1 H5).
move=> x0 H6.
apply (Rgt_trans (f x0 * g x0) 0 M).
apply (Rmult_gt_0_compat (f x0) (g x0)).
apply (proj2 H5 x0 H6).
apply (Rge_gt_trans (g x0) c 0).
apply (proj2 H3 x0 (proj1 H6)).
apply (proj1 H3).
apply H4.
move=> H4.
elim (H2 (M / c)).
move=> alp H5.
exists alp.
apply conj.
apply (proj1 H5).
move=> x0 H6.
rewrite - (Rmult_1_r M).
rewrite - (Rinv_l c).
rewrite - (Rmult_assoc M (/ c) c).
apply (Rle_lt_trans (M * / c * c) (M * / c * g x0) (f x0 * g x0)).
apply (Rmult_le_compat_l (M * / c) c (g x0)).
elim H4.
move=> H7.
apply (Rlt_le 0 (M * / c)).
apply (Rmult_lt_0_compat M (/ c)).
apply H7.
apply (Rinv_0_lt_compat c (proj1 H3)).
move=> H7.
rewrite - H7.
rewrite (Rmult_0_l (/ c)).
apply (Rle_refl 0).
apply (Rge_le (g x0) c).
apply (proj2 H3 x0 (proj1 H6)).
apply (Rmult_gt_compat_r (g x0) (f x0) (M * / c)).
apply (Rlt_le_trans 0 c (g x0)).
apply (proj1 H3).
apply (Rge_le (g x0) c).
apply (proj2 H3 x0 (proj1 H6)).
apply (proj2 H5 x0 H6).
apply (Rgt_not_eq c 0 (proj1 H3)).
Qed.

Lemma Proposition_6_9_3 : forall (M1 : Metric_Space) (f : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1), limit_inf_R M1 (fun (r : Base M1) => Rabs (f r)) B x -> limit_in M1 R_met (fun (r : Base M1) => / (f r)) B x 0.
Proof.
move=> M1 f B x H2.
move=> eps H3.
elim (H2 (/ eps)).
move=> alp H4.
exists alp.
apply conj.
apply (proj1 H4).
move=> x0 H5.
unfold R_met.
unfold dist.
unfold R_dist.
rewrite (Rminus_0_r (/ f x0)).
rewrite (Rabs_Rinv (f x0)).
rewrite - (Rinv_involutive eps).
apply (Rinv_lt_contravar (/ eps) (Rabs (f x0))).
suff: (0 < / eps).
move=> H6.
apply (Rmult_lt_0_compat (/ eps) (Rabs (f x0))).
apply H6.
apply (Rlt_trans 0 (/ eps) (Rabs (f x0)) H6 (proj2 H4 x0 H5)).
apply (Rinv_0_lt_compat eps H3).
apply (proj2 H4 x0 H5).
apply (Rgt_not_eq eps 0 H3).
move=> H6.
apply (Rgt_not_ge (/ eps) (Rabs (f x0))).
apply (proj2 H4 x0 H5).
rewrite H6.
rewrite Rabs_R0.
apply (Rgt_ge (/ eps) 0).
apply (Rinv_0_lt_compat eps H3).
Qed.

Lemma Proposition_6_9_4 : forall (M1 : Metric_Space) (f : Base M1 -> R) (B : Ensemble (Base M1)) (x : Base M1), limit_in M1 R_met f B x 0 -> (forall (r : Base M1), In (Base M1) B r -> f r > 0) -> limit_inf_R M1 (fun (r : Base M1) => / (f r)) B x.
Proof.
move=> M1 f B x H2 H3.
suff: (forall (M : R), M > 0 -> exists alp : R, alp > 0 /\ (forall x0 : Base M1, B x0 /\ dist M1 x0 x < alp -> / f x0 > M)).
move=> H4.
move=> M.
elim (Rle_or_lt M 0).
move=> H5.
elim (H4 1 Rlt_0_1).
move=> alp H6.
exists alp.
apply conj.
apply (proj1 H6).
move=> x0 H7.
apply (Rgt_trans (/ f x0) 1 M).
apply (proj2 H6 x0 H7).
apply (Rgt_ge_trans 1 0 M).
apply Rlt_0_1.
apply (Rle_ge M 0).
apply H5.
apply H4.
move=> M H4.
elim (H2 (/ M)).
move=> alp H5.
exists alp.
apply conj.
apply (proj1 H5).
move=> x0 H6.
rewrite - (Rabs_right (/ f x0)).
rewrite (Rabs_Rinv (f x0)).
rewrite - (Rinv_involutive M).
apply (Rinv_lt_contravar (Rabs (f x0)) (/ M)).
apply (Rmult_lt_0_compat (Rabs (f x0)) (/ M)).
rewrite (Rabs_right (f x0)).
apply (H3 x0 (proj1 H6)).
apply (Rgt_ge (f x0) 0 (H3 x0 (proj1 H6))).
apply (Rinv_0_lt_compat M H4).
rewrite - (Rminus_0_r (f x0)).
apply (proj2 H5 x0 H6).
apply (Rgt_not_eq M 0 H4).
apply (Rgt_not_eq (f x0) 0 (H3 x0 (proj1 H6))).
apply (Rgt_ge (/ f x0) 0).
apply (Rinv_0_lt_compat (f x0) (H3 x0 (proj1 H6))).
apply (Rinv_0_lt_compat M H4).
Qed.

Definition Banach (M1 : Metric_Space) := forall (an : nat -> Base M1), (forall (eps : R), eps > 0 -> exists (N : nat), forall (n1 n2 : nat), (n1 >= N)%nat -> (n2 >= N)%nat -> (dist M1 (an n1) (an n2) < eps)) -> exists (y : Base M1), Un_cv_met M1 an y.

Lemma BanachR : Banach R_met.
Proof.
move=> an.
apply (proj2 (Theorem_3_6 an)).
Qed.

Lemma BanachRn : forall (N : nat), Banach (Rn_met N).
Proof.
move=> N an.
apply (proj2 (Theorem_4_5_3 N an)).
Qed.

Lemma Theorem_6_10_1 : forall (M1 M2 : Metric_Space) (f : Base M1 -> Base M2) (B : Ensemble (Base M1)) (x : Base M1), (Banach M2) -> ((exists (y : Base M2), limit_in M1 M2 f B x y) <-> (forall (eps : R), eps > 0 -> exists (dlt : R), (dlt > 0) /\ forall (z1 z2 : Base M1), (In (Base M1) (Intersection (Base M1) (NeighborhoodMet M1 x dlt) B) z1) -> (In (Base M1) (Intersection (Base M1) (NeighborhoodMet M1 x dlt) B) z2) -> dist M2 (f z1) (f z2) < eps)).
Proof.
move=> M1 M2 f B x H1.
apply conj.
elim.
move=> y H3 eps H4.
elim (H3 (eps / 2) (eps2_Rgt_R0 eps H4)).
move=> dlt H5.
exists dlt.
apply conj.
apply (proj1 H5).
move=> z1 z2 H6 H7.
apply (Rle_lt_trans (dist M2 (f z1) (f z2)) (dist M2 (f z1) y + dist M2 (f z2) y) eps).
rewrite (dist_sym M2 (f z2) y).
apply (dist_tri M2 (f z1) (f z2) y).
rewrite - (eps2 eps).
apply (Rplus_lt_compat (dist M2 (f z1) y) (eps * / 2) (dist M2 (f z2) y) (eps * / 2)).
apply (proj2 H5 z1).
elim H6.
move=> z3 H8 H9.
apply conj.
apply H9.
apply H8.
apply (proj2 H5 z2).
elim H7.
move=> z3 H8 H9.
apply conj.
apply H9.
apply H8.
move=> H3.
apply (proj2 (Theorem_6_2_corollary M1 M2 f B x)).
move=> xn H4.
apply (H1 (fun n : nat => f (proj1_sig (xn n)))).
move=> eps H5.
elim (H3 eps H5).
move=> dlt H6.
elim (H4 dlt (proj1 H6)).
move=> N H7.
exists N.
move=> n1 n2 H8 H9.
apply (proj2 H6 (proj1_sig (xn n1)) (proj1_sig (xn n2))).
apply (Intersection_intro (Base M1) (NeighborhoodMet M1 x dlt) B (proj1_sig (xn n1))).
apply (H7 n1 H8).
apply (proj2_sig (xn n1)).
apply (Intersection_intro (Base M1) (NeighborhoodMet M1 x dlt) B (proj1_sig (xn n2))).
apply (H7 n2 H9).
apply (proj2_sig (xn n2)).
Qed.

Definition limit_R_inf (M : Metric_Space) (f : R -> Base M) (B : Ensemble R) (x : Base M) := forall (eps : R), eps > 0 -> exists (m : R), forall (r : R), B r /\ r >= m -> dist M (f r) x < eps.

Definition limit_R_minf (M : Metric_Space) (f : R -> Base M) (B : Ensemble R) (x : Base M) := forall (eps : R), eps > 0 -> exists (m : R), forall (r : R), B r /\ r <= m -> dist M (f r) x < eps.

Lemma Rextendmetfunsub : {f : R -> R | (forall (x : R), - (1) < f x < 1) /\ (forall (x y : R), (x < y) -> (f x < f y)) /\ (forall (x : R), ContinuousMet R_met R_met f (Full_set R) x) /\ (forall (x : R) (eps : R), eps > 0 -> exists (dlt : R), dlt > 0 /\ (forall (x0 : R), dist R_met (f x0) (f x) < dlt -> dist R_met x0 x < eps)) /\ (limit_R_inf R_met f (Full_set R) 1) /\ (limit_R_minf R_met f (Full_set R) (- (1))) /\ (forall (x : R), - (1) < x < 1 -> exists (y : R), f y = x)}.
Proof.
exists (fun (r : R) => match (Rlt_le_dec 0 r) with 
| left _ => 1 - / (r + 1)
| right _ => - (1) - / (r - 1)
end).
have: (forall x : R, - (1) < ((fun (r : R) => match (Rlt_le_dec 0 r) with 
| left _ => 1 - / (r + 1)
| right _ => - (1) - / (r - 1)
end) x) < 1).
move=> x.
elim (Rlt_le_dec 0 x).
move=> H1.
apply conj.
suff: (/ (x + 1) < 1).
move=> H2.
apply (Rlt_trans (- (1)) (- (/ (x + 1))) (1 - / (x + 1))).
apply (Ropp_lt_contravar 1 (/ (x + 1)) H2).
rewrite - {1} (Rplus_0_l (- (/ (x + 1)))).
apply (Rplus_lt_compat_r (- (/ (x + 1))) 0 1 Rlt_0_1).
rewrite - {2} Rinv_1.
apply (Rinv_1_lt_contravar 1 (x + 1)).
apply (Req_le 1 1).
reflexivity.
rewrite - {1} (Rplus_0_l 1).
apply (Rplus_lt_compat_r 1 0 x H1).
rewrite - {3} (Rplus_0_r 1).
apply (Rplus_lt_compat_l 1 (- / (x + 1)) 0).
apply (Ropp_lt_gt_0_contravar (/ (x + 1))).
apply (Rinv_0_lt_compat (x + 1)).
apply (Rlt_trans 0 x (x + 1) H1).
rewrite - {1} (Rplus_0_r x).
apply (Rplus_lt_compat_l x 0 1 Rlt_0_1).
move=> H1.
apply conj.
rewrite - {1} (Rplus_0_r (- (1))).
apply (Rplus_lt_compat_l (- (1)) 0 (- / (x - 1))).
apply (Ropp_0_gt_lt_contravar (/ (x - 1))).
apply (Rinv_lt_0_compat (x - 1)).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
apply (Rplus_lt_compat_l x (- (1)) 0).
apply (Ropp_0_lt_gt_contravar 1 Rlt_0_1).
apply H1.
suff: (/ (x - 1) >= - (1)).
move=> H2.
apply (Rle_lt_trans (- (1) - / (x - 1)) 0 1).
rewrite - (Rplus_opp_l 1).
apply (Rplus_le_compat_l (- (1)) (- / (x - 1)) 1).
rewrite - {2} (Ropp_involutive 1).
apply (Ropp_ge_le_contravar (/ (x - 1)) (- (1)) H2).
apply Rlt_0_1.
rewrite - (Rmult_1_r (/ (x - 1))).
rewrite - {3} (Rinv_l (x - 1)).
rewrite (Ropp_mult_distr_r (/ (x - 1)) (x - 1)).
apply (Rmult_le_ge_compat_neg_l (/ (x - 1)) 1 (- (x - 1))).
apply (Rlt_le (/ (x - 1)) 0).
apply (Rinv_lt_0_compat (x - 1)).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
apply (Rplus_lt_compat_l x (- (1)) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply H1.
rewrite - {1} (Ropp_involutive 1).
apply (Ropp_le_contravar (- (1)) (x - 1)).
rewrite - (Rplus_0_l (- (1))).
apply (Rplus_le_compat_r (- (1)) x 0 H1).
apply (Rlt_not_eq (x - 1) 0).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
apply (Rplus_lt_compat_l x (- (1)) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply H1.
move=> H0.
apply conj.
apply H0.
apply conj.
move=> x y H1.
elim (Rlt_le_dec 0 x).
move=> H2.
elim (Rlt_le_dec 0 y).
move=> H3.
apply (Rplus_lt_compat_l 1 (- / (x + 1)) (- / (y + 1))).
apply (Ropp_lt_contravar (/ (x + 1)) (/ (y + 1))).
apply (Rinv_1_lt_contravar (x + 1) (y + 1)).
rewrite - {1} (Rplus_0_l 1).
apply (Rplus_le_compat_r 1 0 x).
apply (Rlt_le 0 x H2).
apply (Rplus_lt_compat_r 1 x y H1).
move=> H3.
apply False_ind.
apply (Rle_not_lt y x).
apply (Rlt_le x y H1).
apply (Rle_lt_trans y 0 x H3 H2).
move=> H2.
elim (Rlt_le_dec 0 y).
move=> H3.
apply (Rle_lt_trans (- (1) - / (x - 1)) 0 (1 - / (y + 1))).
rewrite - (Rplus_opp_l 1).
apply (Rplus_le_compat_l (- (1)) (- / (x - 1)) 1).
rewrite - (Rmult_1_r (/ (x - 1))).
rewrite (Ropp_mult_distr_r (/ (x - 1)) 1).
rewrite - {3} (Rinv_l (x - 1)).
apply (Rmult_le_compat_neg_l (/ (x - 1)) (x - 1) (- (1))).
apply (Rlt_le (/ (x - 1)) 0).
apply (Rinv_lt_0_compat (x - 1)).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
apply (Rplus_lt_compat_l x (- (1)) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply H2.
rewrite - (Rplus_0_l (- (1))).
apply (Rplus_le_compat_r (- (1)) x 0 H2).
apply (Rlt_not_eq (x - 1) 0).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
apply (Rplus_lt_compat_l x (- (1)) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply H2.
rewrite - (Rplus_opp_r 1).
apply (Rplus_lt_compat_l 1 (- (1)) (- / (y + 1))).
apply (Ropp_lt_contravar 1 (/ (y + 1))).
rewrite - {2} Rinv_1.
apply (Rinv_1_lt_contravar 1 (y + 1)).
apply (Rle_refl 1).
rewrite - {1} (Rplus_0_l 1).
apply (Rplus_lt_compat_r 1 0 y H3).
move=> H3.
apply (Rplus_lt_compat_l (- (1)) (- / (x - 1)) (- / (y - 1))).
apply (Ropp_lt_contravar (/ (x - 1)) (/ (y - 1))).
apply (Rinv_lt_contravar (x - 1) (y - 1)).
rewrite - (Rmult_opp_opp (x - 1) (y - 1)).
apply (Rmult_lt_0_compat (- (x - 1)) (- (y - 1))).
apply (Ropp_0_gt_lt_contravar (x - 1)).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
apply (Rplus_lt_compat_l x (- (1)) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply H2.
apply (Ropp_0_gt_lt_contravar (y - 1)).
apply (Rlt_le_trans (y - 1) y 0).
rewrite - {2} (Rplus_0_r y).
apply (Rplus_lt_compat_l y (- (1)) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply H3.
apply (Rplus_lt_compat_r (- (1)) x y H1).
apply conj.
suff: (forall (x : R), (x >= 0) -> ContinuousMet R_met R_met (fun r : R => 1 - / (r + 1)) (Full_set R) x).
move=> H1.
suff: (forall (x : R), (x <= 0) -> ContinuousMet R_met R_met (fun r : R => - (1) - / (r - 1)) (Full_set R) x).
move=> H2.
move=> x.
elim (Rtotal_order x 0).
move=> H3 eps H4.
elim (H2 x (Rlt_le x 0 H3) eps H4).
move=> dlt H5.
exists (Rmin (- x) dlt).
apply conj.
apply (Rmin_pos (- x) dlt).
apply (Ropp_0_gt_lt_contravar x H3).
apply (proj1 H5).
move=> x0 H6.
elim (Rlt_le_dec 0 x0).
move=> H7.
apply False_ind.
apply (Rlt_not_le (Rmin (- x) dlt) (dist R_met x0 x) (proj2 H6)).
apply (Rle_trans (Rmin (- x) dlt) (- x) (dist R_met x0 x)).
apply (Rmin_l (- x) dlt).
apply (Rle_trans (- x) (x0 - x) (dist R_met x0 x)).
rewrite - {1} (Rplus_0_l (- x)).
apply (Rplus_le_compat_r (- x) 0 x0 (Rlt_le 0 x0 H7)).
apply (Rle_abs (x0 - x)).
move=> H7.
elim (Rlt_le_dec 0 x).
move=> H8.
apply False_ind.
apply (Rlt_irrefl 0).
apply (Rlt_trans 0 x 0 H8 H3).
move=> H8.
apply (proj2 H5 x0).
apply conj.
apply (Full_intro R x0).
apply (Rlt_le_trans (dist R_met x0 x) (Rmin (- x) dlt) dlt).
apply (proj2 H6).
apply (Rmin_r (- x) dlt).
elim.
move=> H3.
move=> eps H4.
suff: (x >= 0).
move=> H5.
suff: (x <= 0).
move=> H6.
elim (H1 x H5 eps H4).
move=> dlt1 H7.
elim (H2 x H6 eps H4).
move=> dlt2 H8.
exists (Rmin dlt1 dlt2).
apply conj.
apply (Rmin_pos dlt1 dlt2).
apply (proj1 H7).
apply (proj1 H8).
move=> x0 H9.
elim (Rlt_le_dec 0 x).
move=> H10.
apply False_ind.
apply (Rlt_irrefl x).
rewrite {1} H3.
apply H10.
move=> H10.
elim (Rlt_le_dec 0 x0).
move=> H11.
suff: ((- (1) - / (x - 1)) = (1 - / (x + 1))).
move=> H12.
rewrite H12.
apply (proj2 H7 x0).
apply conj.
apply (Full_intro R x0).
apply (Rlt_le_trans (dist R_met x0 x) (Rmin dlt1 dlt2) dlt1).
apply (proj2 H9).
apply (Rmin_l dlt1 dlt2).
rewrite H3.
unfold Rminus.
rewrite (Rplus_0_l (- 1)).
rewrite (Rplus_0_l 1).
rewrite - (Ropp_inv_permute 1).
rewrite Rinv_1.
rewrite (Rplus_opp_r 1).
apply (Rplus_opp_r (- (1))).
apply (Rgt_not_eq 1 0 Rlt_0_1).
move=> H11.
apply (proj2 H8 x0).
apply conj.
apply (proj1 H9).
apply (Rlt_le_trans (dist R_met x0 x) (Rmin dlt1 dlt2) dlt2).
apply (proj2 H9).
apply (Rmin_r dlt1 dlt2).
apply (Req_le x 0 H3).
apply (Req_ge x 0 H3).
move=> H3 eps H4.
elim (H1 x (Rgt_ge x 0 H3) eps H4).
move=> dlt H5.
exists (Rmin x dlt).
apply conj.
apply (Rmin_pos x dlt).
apply H3.
apply (proj1 H5).
move=> x0 H6.
elim (Rlt_le_dec 0 x0).
move=> H7.
elim (Rlt_le_dec 0 x).
move=> H8.
apply (proj2 H5 x0).
apply conj.
apply (Full_intro R x0).
apply (Rlt_le_trans (dist R_met x0 x) (Rmin x dlt) dlt).
apply (proj2 H6).
apply (Rmin_r x dlt).
move=> H8.
apply False_ind.
apply (Rlt_irrefl 0).
apply (Rlt_le_trans 0 x 0 H3 H8).
move=> H7.
apply False_ind.
apply (Rlt_not_le (Rmin x dlt) (dist R_met x0 x) (proj2 H6)).
apply (Rle_trans (Rmin x dlt) x (dist R_met x0 x)).
apply (Rmin_l x dlt).
apply (Rle_trans x (x - x0) (dist R_met x0 x)).
rewrite - {1} (Rplus_0_r x).
apply (Rplus_le_compat_l x 0 (- x0)).
apply (Ropp_0_ge_le_contravar x0).
apply (Rle_ge x0 0 H7).
rewrite (dist_sym R_met x0 x).
apply (Rle_abs (x - x0)).
move=> x H2.
apply (Theorem_6_6_3_2_R R_met (fun (r : R) => - (1)) (fun (r : R) => / (r - 1)) (Full_set R) x).
move=> eps H3.
exists 1.
apply conj.
apply Rlt_0_1.
move=> x0 H4.
rewrite (proj2 (dist_refl R_met (- (1)) (- (1)))).
apply H3.
reflexivity.
apply (Theorem_6_6_3_7_R R_met (fun (r : R) => r - 1) (Full_set R) x).
apply (Rlt_not_eq (x - 1) 0).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
apply (Rplus_lt_compat_l x (- 1) 0).
apply (Ropp_lt_gt_0_contravar 1 Rlt_0_1).
apply H2.
move=> eps H3.
exists eps.
apply conj.
apply H3.
move=> x0 H4.
suff: (dist R_met (x0 - 1) (x - 1) = dist R_met x0 x).
move=> H5.
rewrite H5.
apply (proj2 H4).
unfold dist.
unfold R_met.
unfold R_dist.
unfold Rminus.
rewrite (Ropp_minus_distr x 1).
rewrite - (Rplus_assoc (x0 + - (1)) 1 (- x)).
rewrite (Rplus_assoc x0 (- (1)) 1).
rewrite (Rplus_opp_l 1).
rewrite (Rplus_0_r x0).
reflexivity.
move=> x H2.
apply (Theorem_6_6_3_2_R R_met (fun (r : R) => 1) (fun (r : R) => / (r + 1)) (Full_set R) x).
move=> eps H3.
exists 1.
apply conj.
apply Rlt_0_1.
move=> x0 H4.
rewrite (proj2 (dist_refl R_met 1 1)).
apply H3.
reflexivity.
apply (Theorem_6_6_3_7_R R_met (fun (r : R) => r + 1) (Full_set R) x).
apply (Rgt_not_eq (x + 1) 0).
apply (Rgt_ge_trans (x + 1) x 0).
rewrite - {2} (Rplus_0_r x).
apply (Rplus_gt_compat_l x 1 0).
apply Rlt_0_1.
apply H2.
move=> eps H3.
exists eps.
apply conj.
apply H3.
move=> x0 H4.
suff: (dist R_met (x0 + 1) (x + 1) = dist R_met x0 x).
move=> H5.
rewrite H5.
apply (proj2 H4).
unfold dist.
unfold R_met.
unfold R_dist.
unfold Rminus.
rewrite (Ropp_plus_distr x 1).
rewrite (Rplus_comm (- x) (- (1))).
rewrite - (Rplus_assoc (x0 + 1) (- (1)) (- x)).
rewrite (Rplus_assoc x0 1 (- (1))).
rewrite (Rplus_opp_r 1).
rewrite (Rplus_0_r x0).
reflexivity.
apply conj.
suff: (let g := fun (x : R) => match (Rlt_le_dec 0 x) with 
| left _ => / - (x - 1) - 1
| right _ => / - (x + 1) + 1
end in forall x eps : R,
eps > 0 ->
exists dlt : R,
  dlt > 0 /\
  (forall x0 : R,
   dist R_met
     ((fun (r : R) => match (Rlt_le_dec 0 r) with 
| left _ => 1 - / (r + 1)
| right _ => - (1) - / (r - 1)
end) x0)
     ((fun (r : R) => match (Rlt_le_dec 0 r) with 
| left _ => 1 - / (r + 1)
| right _ => - (1) - / (r - 1)
end) x) < dlt ->
   dist R_met x0 x < eps)).
apply.
move=> g.
suff: (forall (x : R), g ((fun (r : R) => match (Rlt_le_dec 0 r) with 
| left _ => 1 - / (r + 1)
| right _ => - (1) - / (r - 1)
end) x) = x).
move=> H1.
suff: (forall (x : R), (- (1) < x < 1) -> ContinuousMet R_met R_met g (Full_set R) x).
move=> H2 x eps H3.
elim (H2 ((fun (r : R) => match (Rlt_le_dec 0 r) with 
| left _ => 1 - / (r + 1)
| right _ => - (1) - / (r - 1)
end) x) (H0 x) eps H3).
move=> dlt H4.
exists dlt.
apply conj.
apply (proj1 H4).
move=> x0 H5.
rewrite - (H1 x).
rewrite - (H1 x0).
apply (proj2 H4).
apply conj.
apply (Full_intro R).
apply H5.
suff: (forall (x : R), (x > - (1)) -> ContinuousMet R_met R_met (fun r : R => / - (r + 1) + 1) (Full_set R) x).
move=> H2.
suff: (forall (x : R), (x < 1) -> ContinuousMet R_met R_met (fun r : R => / - (r - 1) - 1) (Full_set R) x).
move=> H3.
move=> x.
elim (Rtotal_order x 0).
move=> H4 H5 eps H6.
elim (H2 x (proj1 H5) eps H6).
move=> dlt H7.
exists (Rmin (- x) dlt).
apply conj.
apply (Rmin_pos (- x) dlt).
apply (Ropp_0_gt_lt_contravar x H4).
apply (proj1 H7).
move=> x0 H8.
unfold g.
elim (Rlt_le_dec 0 x0).
move=> H9.
apply False_ind.
apply (Rlt_not_le (Rmin (- x) dlt) (dist R_met x0 x) (proj2 H8)).
apply (Rle_trans (Rmin (- x) dlt) (- x) (dist R_met x0 x)).
apply (Rmin_l (- x) dlt).
apply (Rle_trans (- x) (x0 - x) (dist R_met x0 x)).
rewrite - {1} (Rplus_0_l (- x)).
apply (Rplus_le_compat_r (- x) 0 x0 (Rlt_le 0 x0 H9)).
apply (Rle_abs (x0 - x)).
move=> H9.
elim (Rlt_le_dec 0 x).
move=> H10.
apply False_ind.
apply (Rlt_irrefl 0).
apply (Rlt_trans 0 x 0 H10 H4).
move=> H10.
apply (proj2 H7 x0).
apply conj.
apply (Full_intro R x0).
apply (Rlt_le_trans (dist R_met x0 x) (Rmin (- x) dlt) dlt).
apply (proj2 H8).
apply (Rmin_r (- x) dlt).
elim.
move=> H4 H5 eps H6.
elim (H2 x (proj1 H5) eps H6).
move=> dlt1 H9.
elim (H3 x (proj2 H5) eps H6).
move=> dlt2 H10.
exists (Rmin dlt1 dlt2).
apply conj.
apply (Rmin_pos dlt1 dlt2).
apply (proj1 H9).
apply (proj1 H10).
move=> x0 H11.
unfold g.
elim (Rlt_le_dec 0 x).
move=> H12.
apply False_ind.
apply (Rlt_irrefl x).
rewrite {1} H4.
apply H12.
move=> H12.
elim (Rlt_le_dec 0 x0).
move=> H13.
suff: ((/ - (x - 1) - 1) = (/ - (x + 1) + 1)).
move=> H14.
rewrite - H14.
apply (proj2 H10 x0).
apply conj.
apply (Full_intro R x0).
apply (Rlt_le_trans (dist R_met x0 x) (Rmin dlt1 dlt2) dlt2).
apply (proj2 H11).
apply (Rmin_r dlt1 dlt2).
rewrite H4.
unfold Rminus.
rewrite (Rplus_0_l (- 1)).
rewrite (Rplus_0_l 1).
rewrite - (Ropp_inv_permute 1).
rewrite (Ropp_involutive 1).
rewrite Rinv_1.
rewrite (Rplus_opp_l 1).
apply (Rplus_opp_r 1).
apply (Rgt_not_eq 1 0 Rlt_0_1).
move=> H13.
apply (proj2 H9 x0).
apply conj.
apply (proj1 H11).
apply (Rlt_le_trans (dist R_met x0 x) (Rmin dlt1 dlt2) dlt1).
apply (proj2 H11).
apply (Rmin_l dlt1 dlt2).
move=> H4 H5 eps H6.
elim (H3 x (proj2 H5) eps H6).
move=> dlt H7.
exists (Rmin x dlt).
apply conj.
apply (Rmin_pos x dlt).
apply H4.
apply (proj1 H7).
move=> x0 H8.
unfold g.
elim (Rlt_le_dec 0 x0).
move=> H9.
elim (Rlt_le_dec 0 x).
move=> H10.
apply (proj2 H7 x0).
apply conj.
apply (Full_intro R x0).
apply (Rlt_le_trans (dist R_met x0 x) (Rmin x dlt) dlt).
apply (proj2 H8).
apply (Rmin_r x dlt).
move=> H10.
apply False_ind.
apply (Rlt_irrefl 0).
apply (Rlt_le_trans 0 x 0 H4 H10).
move=> H9.
apply False_ind.
apply (Rlt_not_le (Rmin x dlt) (dist R_met x0 x) (proj2 H8)).
apply (Rle_trans (Rmin x dlt) x (dist R_met x0 x)).
apply (Rmin_l x dlt).
apply (Rle_trans x (x - x0) (dist R_met x0 x)).
rewrite - {1} (Rplus_0_r x).
apply (Rplus_le_compat_l x 0 (- x0)).
apply (Ropp_0_ge_le_contravar x0).
apply (Rle_ge x0 0 H9).
rewrite (dist_sym R_met x0 x).
apply (Rle_abs (x - x0)).
move=> x H3.
apply (Theorem_6_6_3_2_R R_met (fun (r : R) => / - (r - 1)) (fun (r : R) => 1) (Full_set R) x).
apply (Theorem_6_6_3_7_R R_met (fun (r : R) => - (r - 1)) (Full_set R) x).
apply (Ropp_neq_0_compat (x - 1)).
apply (Rlt_not_eq (x - 1) 0).
apply (Rlt_minus x 1 H3).
move=> eps H4.
exists eps.
apply conj.
apply H4.
move=> x0 H5.
suff: (dist R_met (- (x0 - 1)) (- (x - 1)) = dist R_met x0 x).
move=> H6.
rewrite H6.
apply (proj2 H5).
unfold dist.
unfold R_met.
unfold R_dist.
unfold Rminus.
rewrite (Ropp_minus_distr x0 1).
rewrite (Ropp_involutive (x + - (1))).
rewrite (Rplus_comm (1 - x0) (x + - (1))).
rewrite - (Rplus_assoc (x + - (1)) 1 (- x0)).
rewrite (Rplus_assoc x (- (1)) 1).
rewrite (Rplus_opp_l 1).
rewrite (Rplus_0_r x).
apply (Rabs_minus_sym x x0).
move=> eps H4.
exists 1.
apply conj.
apply Rlt_0_1.
move=> x0 H5.
rewrite (proj2 (dist_refl R_met 1 1)).
apply H4.
reflexivity.
move=> x H2.
apply (Theorem_6_6_3_1_R R_met (fun (r : R) => / - (r + 1)) (fun (r : R) => 1) (Full_set R) x).
apply (Theorem_6_6_3_7_R R_met (fun (r : R) => - (r + 1)) (Full_set R) x).
apply (Ropp_neq_0_compat (x + 1)).
apply (Rgt_not_eq (x + 1) 0).
rewrite - (Ropp_involutive 1).
apply (Rgt_minus x (- (1))).
apply H2.
move=> eps H3.
exists eps.
apply conj.
apply H3.
move=> x0 H4.
suff: (dist R_met (- (x0 + 1)) (- (x + 1)) = dist R_met x0 x).
move=> H5.
rewrite H5.
apply (proj2 H4).
unfold dist.
unfold R_met.
unfold R_dist.
unfold Rminus.
rewrite (Ropp_plus_distr x0 1).
rewrite (Rplus_comm x 1).
rewrite (Ropp_involutive (1 + x)).
rewrite - (Rplus_assoc (- x0 + - (1)) 1 x).
rewrite (Rplus_assoc (- x0) (- (1)) 1).
rewrite (Rplus_opp_l 1).
rewrite (Rplus_0_r (- x0)).
rewrite (Rplus_comm (- x0) x).
apply (Rabs_minus_sym x x0).
move=> eps H3.
exists 1.
apply conj.
apply Rlt_0_1.
move=> x0 H4.
rewrite (proj2 (dist_refl R_met 1 1)).
apply H3.
reflexivity.
move=> x.
elim (Rlt_le_dec 0 x).
move=> H1.
unfold g.
elim (Rlt_le_dec 0 (1 - / (x + 1))).
move=> H2.
unfold Rminus.
rewrite (Rplus_comm 1 (- / (x + 1))).
rewrite (Rplus_assoc (- / (x + 1)) 1 (- (1))).
rewrite (Rplus_opp_r 1).
rewrite (Rplus_0_r (- / (x + 1))).
rewrite (Ropp_involutive (/ (x + 1))).
rewrite (Rinv_involutive (x + 1)).
rewrite (Rplus_assoc x 1 (- (1))).
rewrite (Rplus_opp_r 1).
apply (Rplus_0_r x).
apply (Rgt_not_eq (x + 1) 0).
apply (Rlt_trans 0 x (x + 1) H1 (Rlt_plus_1 x)).
move=> H2.
apply False_ind.
apply (Rle_not_lt 0 (1 - / (x + 1)) H2).
apply (Rgt_minus 1 (/ (x + 1))).
rewrite - {1} Rinv_1.
apply (Rinv_1_lt_contravar 1 (x + 1)).
apply (Req_le 1 1).
reflexivity.
rewrite - {1} (Rplus_0_l 1).
apply (Rplus_lt_compat_r 1 0 x H1).
move=> H1.
unfold g.
elim (Rlt_le_dec 0 (- (1) - / (x - 1))).
move=> H2.
apply False_ind.
apply (Rlt_not_le (- (1) - / (x - 1)) 0 H2).
apply (Rle_minus (- (1)) (/ (x - 1))).
rewrite - (Rmult_1_r (/ (x - 1))).
rewrite - {1} (Rinv_l (x - 1)).
rewrite (Ropp_mult_distr_r (/ (x - 1)) (x - 1)).
apply (Rmult_le_compat_neg_l (/ (x - 1)) 1 (- (x - 1))).
apply (Rlt_le (/ (x - 1)) 0).
apply (Rinv_lt_0_compat (x - 1)).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
rewrite - (Rplus_opp_l 1).
rewrite - (Rplus_assoc x (- (1)) 1).
apply (Rlt_plus_1 (x - 1)).
apply H1.
rewrite (Ropp_minus_distr x 1).
rewrite - {1} (Rplus_0_r 1).
apply (Rplus_le_compat_l 1 0 (- x)).
apply (Ropp_0_ge_le_contravar x).
apply (Rle_ge x 0 H1).
apply (Rlt_not_eq (x - 1) 0).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
rewrite - (Rplus_opp_l 1).
rewrite - (Rplus_assoc x (- (1)) 1).
apply (Rlt_plus_1 (x - 1)).
apply H1.
move=> H2.
unfold Rminus.
rewrite (Rplus_comm (- (1)) (- / (x - 1))).
rewrite (Rplus_assoc (- / (x - 1)) (- (1)) 1).
rewrite (Rplus_opp_l 1).
rewrite (Rplus_0_r (- / (x - 1))).
rewrite (Ropp_involutive (/ (x - 1))).
rewrite (Rinv_involutive (x - 1)).
rewrite (Rplus_assoc x (- (1)) 1).
rewrite (Rplus_opp_l 1).
apply (Rplus_0_r x).
apply (Rlt_not_eq (x - 1) 0).
apply (Rlt_le_trans (x - 1) x 0).
rewrite - {2} (Rplus_0_r x).
rewrite - (Rplus_opp_l 1).
rewrite - (Rplus_assoc x (- (1)) 1).
apply (Rlt_plus_1 (x - 1)).
apply H1.
apply conj.
move=> eps H1.
exists (/ eps).
move=> r H2.
elim (Rlt_le_dec 0 r).
move=> H3.
unfold dist.
unfold R_met.
unfold R_dist.
unfold Rminus.
rewrite (Rplus_comm 1 (- (/ (r + 1)))).
rewrite (Rplus_assoc (- / (r + 1)) 1 (- (1))).
rewrite (Rplus_opp_r 1).
rewrite (Rplus_0_r (- / (r + 1))).
rewrite (Rabs_left (- / (r + 1))).
rewrite (Ropp_involutive (/ (r + 1))).
rewrite - (Rinv_involutive eps).
suff: (/ eps < r + 1).
move=> H4.
apply (Rinv_lt_contravar (/ eps) (r + 1)).
suff: (/ eps > 0).
move=> H5.
apply (Rmult_lt_0_compat (/ eps) (r + 1)).
apply H5.
apply (Rlt_trans 0 (/ eps) (r + 1) H5 H4).
apply (Rinv_0_lt_compat eps H1).
apply H4.
apply (Rle_lt_trans (/ eps) r (r + 1) (Rge_le r (/ eps) (proj2 H2))).
rewrite - {1} (Rplus_0_r r).
apply (Rplus_lt_compat_l r 0 1 Rlt_0_1).
apply (Rgt_not_eq eps 0 H1).
apply (Ropp_lt_gt_0_contravar (/ (r + 1))).
apply (Rinv_0_lt_compat (r + 1)).
apply (Rlt_trans 0 r (r + 1) H3 (Rlt_plus_1 r)).
move=> H3.
apply False_ind.
apply (Rlt_irrefl 0).
apply (Rlt_le_trans 0 r 0).
apply (Rlt_le_trans 0 (/ eps) r).
apply (Rinv_0_lt_compat eps H1).
apply (Rge_le r (/ eps) (proj2 H2)).
apply H3.
apply conj.
move=> eps H1.
exists (- / eps).
move=> r H2.
elim (Rlt_le_dec 0 r).
move=> H3.
apply False_ind.
apply (Rlt_irrefl 0).
apply (Rlt_le_trans 0 r 0).
apply H3.
apply (Rle_trans r (- / eps) 0).
apply (proj2 H2).
apply (Rlt_le (- / eps) 0).
apply (Ropp_lt_gt_0_contravar (/ eps)).
apply (Rinv_0_lt_compat eps H1).
move=> H3.
unfold dist.
unfold R_met.
unfold R_dist.
unfold Rminus.
rewrite (Rplus_comm (- (1)) (- (/ (r + - (1))))).
rewrite (Rplus_assoc (- / (r + - (1))) (- (1)) (- - (1))).
rewrite (Rplus_opp_r (- (1))).
rewrite (Rplus_0_r (- / (r + (- (1))))).
rewrite (Rabs_right (- / (r + - (1)))).
rewrite - (Ropp_involutive eps).
apply (Ropp_lt_contravar (/ (r + - (1))) (- eps)).
rewrite - (Rinv_involutive (- eps)).
rewrite - (Ropp_inv_permute eps).
suff: (r + - (1) < - / eps).
move=> H4.
apply (Rinv_lt_contravar (r + - (1)) (- / eps)).
rewrite - (Rmult_opp_opp (r + - (1)) (- / eps)).
apply (Rmult_lt_0_compat (- (r + - (1))) (- - / eps)).
apply (Ropp_gt_lt_0_contravar (r + - (1))).
apply (Rlt_trans (r + - (1)) (- / eps) 0 H4).
apply (Ropp_lt_gt_0_contravar (/ eps)).
apply (Rinv_0_lt_compat eps H1).
rewrite (Ropp_involutive (/ eps)).
apply (Rinv_0_lt_compat eps H1).
apply H4.
apply (Rlt_le_trans (r + - (1)) r (- / eps)).
rewrite - {2} (Rplus_0_r r).
rewrite - (Rplus_opp_l 1).
rewrite - (Rplus_assoc r (- (1)) 1).
apply (Rlt_plus_1 (r + - (1))).
apply (proj2 H2).
apply (Rgt_not_eq eps 0 H1).
apply (Ropp_neq_0_compat eps (Rgt_not_eq eps 0 H1)).
apply (Rgt_ge (- / (r + - (1))) 0).
apply (Ropp_gt_lt_0_contravar (/ (r + - (1)))).
apply (Rinv_lt_0_compat (r + - (1))).
apply (Rlt_le_trans (r + - (1)) r 0).
rewrite - {2} (Rplus_0_r r).
rewrite - (Rplus_opp_l 1).
rewrite - (Rplus_assoc r (- (1)) 1).
apply (Rlt_plus_1 (r + - (1))).
apply H3.
move=> x H1.
elim (Rtotal_order 0 x).
move=> H2.
exists (/ - (x - 1) - 1).
elim (Rlt_le_dec 0 (/ - (x - 1) - 1)).
move=> H3.
rewrite (Rplus_assoc (/ - (x - 1)) (- (1)) 1).
rewrite (Rplus_opp_l 1).
rewrite (Rplus_0_r (/ - (x - 1))).
rewrite (Rinv_involutive (- (x - 1))).
unfold Rminus.
rewrite (Ropp_involutive (x - 1)).
rewrite (Rplus_comm 1 (x - 1)).
rewrite (Rplus_assoc x (- (1)) 1).
rewrite (Rplus_opp_l 1).
apply (Rplus_0_r x).
apply (Ropp_neq_0_compat (x - 1)).
apply (Rlt_not_eq (x - 1) 0).
apply (Rlt_minus x 1).
apply (proj2 H1).
move=> H3.
apply False_ind.
apply (Rle_not_lt 0 (/ - (x - 1) - 1) H3).
apply (Rgt_minus (/ - (x - 1)) 1).
rewrite - {2} (Rinv_1).
apply (Rinv_lt_contravar (- (x - 1)) 1).
rewrite (Rmult_1_r (- (x - 1))).
apply (Ropp_0_gt_lt_contravar (x - 1)).
apply (Rlt_minus x 1 (proj2 H1)).
rewrite - {2} (Ropp_involutive 1).
apply (Ropp_lt_contravar (x - 1) (- (1))).
rewrite - (Rplus_0_l (- (1))).
apply (Rplus_lt_compat_r (- (1)) 0 x H2).
elim.
move=> H2.
exists 0.
elim (Rlt_le_dec 0 0).
move=> H3.
apply False_ind.
apply (Rlt_irrefl 0 H3).
move=> H3.
unfold Rminus.
rewrite (Rplus_0_l (- (1))).
rewrite - (Ropp_inv_permute 1).
rewrite Rinv_1.
rewrite (Rplus_opp_r (- (1))).
apply H2.
apply (Rgt_not_eq 1 0 Rlt_0_1).
move=> H2.
exists (/ - (x + 1) + 1).
elim (Rlt_le_dec 0 (/ - (x + 1) + 1)).
move=> H3.
apply False_ind.
apply (Rlt_not_le (/ - (x + 1) + 1) 0 H3).
left.
rewrite - {2} (Ropp_involutive 1).
apply (Rlt_minus (/ - (x + 1)) (- (1))).
rewrite - (Ropp_inv_permute (x + 1)).
apply (Ropp_lt_contravar (/ (x + 1)) 1).
rewrite - {1} Rinv_1.
apply (Rinv_lt_contravar (x + 1) 1).
rewrite (Rmult_1_r (x + 1)).
rewrite - (Rplus_opp_l 1).
apply (Rplus_lt_compat_r 1 (- (1)) x (proj1 H1)).
rewrite - {2} (Rplus_0_l 1).
apply (Rplus_lt_compat_r 1 x 0 H2).
apply (Rgt_not_eq (x + 1) 0).
rewrite - (Rplus_opp_l 1).
apply (Rplus_lt_compat_r 1 (- (1)) x (proj1 H1)).
move=> H3.
unfold Rminus.
rewrite (Rplus_assoc (/ - (x + 1)) 1 (- (1))).
rewrite (Rplus_opp_r 1).
rewrite (Rplus_0_r (/ - (x + 1))).
rewrite (Rinv_involutive (- (x + 1))).
rewrite (Ropp_involutive (x + 1)).
rewrite (Rplus_comm x 1).
rewrite - (Rplus_assoc (- (1)) 1 x).
rewrite (Rplus_opp_l 1).
apply (Rplus_0_l x).
apply (Ropp_neq_0_compat (x + 1)).
apply (Rgt_not_eq (x + 1) 0).
rewrite - (Rplus_opp_l 1).
apply (Rplus_lt_compat_r 1 (- (1)) x (proj1 H1)).
Qed.

Inductive Rextend : Set := 
  | Rinf : Rextend
  | Rminf : Rextend
  | Rval : R -> Rextend.

Definition Rextendlt := (fun (r1 r2 : Rextend) => match r1 with
  | Rinf => False
  | Rminf => match r2 with 
               | Rinf => True
               | Rminf => False
               | Rval _ => True
             end
  | Rval v1 => match r2 with
                 | Rinf => True
                 | Rminf => False
                 | Rval v2 => v1 < v2
               end
end).

Definition Rextendmetfun := (fun (r : Rextend) => match r with
  | Rinf => 1
  | Rminf => -1
  | Rval v => proj1_sig (Rextendmetfunsub) v 
end).

Definition Rextendmetdist := fun (r1 r2 : Rextend) => R_dist (Rextendmetfun r1) (Rextendmetfun r2).

Lemma Rextenddist_pos : forall x y : Rextend, Rextendmetdist x y >= 0.
Proof.
move=> x y.
apply R_dist_pos.
Qed.

Lemma Rextenddist_sym : forall x y : Rextend, Rextendmetdist x y = Rextendmetdist y x.
Proof.
move=> x y.
apply R_dist_sym.
Qed.

Lemma Rextenddist_refl : forall x y : Rextend, Rextendmetdist x y = 0 <-> x = y.
Proof.
move=> x y.
apply conj.
unfold Rextendmetdist.
elim x.
elim y.
move=> H1.
reflexivity.
unfold Rextendmetfun.
move=> H1.
apply False_ind.
apply (Rgt_not_eq 1 (- (1))).
apply (Rlt_trans (- (1)) 0 1).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply Rlt_0_1.
apply (proj1 (R_dist_refl 1 (- (1))) H1).
move=> r H1.
apply False_ind.
apply (Rgt_not_eq (Rextendmetfun Rinf) (Rextendmetfun (Rval r))).
unfold Rextendmetfun.
apply (proj2 (proj1 (proj2_sig Rextendmetfunsub) r)).
apply (proj1 (R_dist_refl (Rextendmetfun Rinf) (Rextendmetfun (Rval r))) H1).
elim y.
unfold Rextendmetfun.
move=> H1.
apply False_ind.
apply (Rlt_not_eq (- (1)) 1).
apply (Rlt_trans (- (1)) 0 1).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply Rlt_0_1.
apply (proj1 (R_dist_refl (- (1)) 1) H1).
move=> H1.
reflexivity.
move=> r H1.
apply False_ind.
apply (Rlt_not_eq (Rextendmetfun Rminf) (Rextendmetfun (Rval r))).
unfold Rextendmetfun.
apply (proj1 (proj1 (proj2_sig Rextendmetfunsub) r)).
apply (proj1 (R_dist_refl (Rextendmetfun Rminf) (Rextendmetfun (Rval r))) H1).
move=> r1.
elim y.
move=> H1.
apply False_ind.
apply (Rlt_not_eq (Rextendmetfun (Rval r1)) (Rextendmetfun Rinf)).
unfold Rextendmetfun.
apply (proj2 (proj1 (proj2_sig Rextendmetfunsub) r1)).
apply (proj1 (R_dist_refl (Rextendmetfun (Rval r1)) (Rextendmetfun Rinf)) H1).
move=> H1.
apply False_ind.
apply (Rgt_not_eq (Rextendmetfun (Rval r1)) (Rextendmetfun Rminf)).
unfold Rextendmetfun.
apply (proj1 (proj1 (proj2_sig Rextendmetfunsub) r1)).
apply (proj1 (R_dist_refl (Rextendmetfun (Rval r1)) (Rextendmetfun Rminf)) H1).
move=> r2.
elim (Rtotal_order r1 r2).
move=> H1 H2.
apply False_ind.
apply (Rlt_not_eq (Rextendmetfun (Rval r1)) (Rextendmetfun (Rval r2))).
unfold Rextendmetfun.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) r1 r2 H1).
apply (proj1 (R_dist_refl (Rextendmetfun (Rval r1)) (Rextendmetfun (Rval r2))) H2).
elim.
move=> H1 H2.
rewrite H1.
reflexivity.
move=> H1 H2.
apply False_ind.
apply (Rgt_not_eq (Rextendmetfun (Rval r1)) (Rextendmetfun (Rval r2))).
unfold Rextendmetfun.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) r2 r1 H1).
apply (proj1 (R_dist_refl (Rextendmetfun (Rval r1)) (Rextendmetfun (Rval r2))) H2).
move=> H1.
rewrite H1.
apply R_dist_refl.
reflexivity.
Qed.

Lemma Rextenddist_tri : forall x y z : Rextend, Rextendmetdist x y <= Rextendmetdist x z + Rextendmetdist z y.
Proof.
move=> x y z.
apply R_dist_tri.
Qed.

Definition Rextend_met : Metric_Space := Build_Metric_Space Rextend Rextendmetdist Rextenddist_pos Rextenddist_sym Rextenddist_refl Rextenddist_tri.

Lemma limit_in_R_R_extend_same_1 : forall (M : Metric_Space) (f : R -> (Base M)) (F : Rextend -> (Base M)) (B : Ensemble R) (x : R) (y : Base M), (forall (r : R), f r = F (Rval r)) -> (limit_in R_met M f B x y <-> limit_in Rextend_met M F (fun (r : Rextend) => exists (l : R), In R B l /\ r = Rval l) (Rval x) y).
Proof.
move=> M f F B x y H1.
apply conj.
move=> H2.
move=> eps H3.
elim (H2 eps H3).
move=> dlt H4.
elim (proj1 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub)))) x dlt (proj1 H4)).
move=> alp H5.
exists alp.
apply conj.
apply (proj1 H5).
move=> x0 H6.
elim (proj1 H6).
move=> x1 H7.
rewrite (proj2 H7).
rewrite - (H1 x1).
apply (proj2 H4 x1).
apply conj.
apply (proj1 H7).
apply (proj2 H5 x1).
suff: (dist Rextend_met (Rval x1) (Rval x) < alp).
apply.
rewrite - (proj2 H7).
apply (proj2 H6).
move=> H2.
move=> eps H3.
elim (H2 eps H3).
move=> dlt H4.
elim (proj1 (proj2 (proj2 (proj2_sig Rextendmetfunsub))) x dlt (proj1 H4)).
move=> alp H5.
exists alp.
apply conj.
apply (proj1 H5).
move=> x0 H6.
rewrite (H1 x0).
apply (proj2 H4 (Rval x0)).
apply conj.
exists x0.
apply conj.
apply (proj1 H6).
reflexivity.
apply (proj2 H5 x0).
apply conj.
apply (Full_intro R x0).
apply (proj2 H6).
Qed.

Lemma limit_in_R_R_extend_same_2 : forall (M : Metric_Space) (f : (Base M) -> R) (B : Ensemble (Base M)) (x : Base M) (y : R), (limit_in M R_met f B x y <-> limit_in M Rextend_met (fun (r : Base M) => Rval (f r)) B x (Rval y)).
Proof.
move=> M f B x y.
apply conj.
move=> H1 eps H2.
elim (proj1 (proj2 (proj2 (proj2_sig Rextendmetfunsub))) y eps H2).
move=> dlt H3.
elim (H1 dlt (proj1 H3)).
move=> alp H4.
exists alp.
apply conj.
apply (proj1 H4).
move=> x0 H5.
apply (proj2 H3 (f x0)).
apply conj.
apply (Full_intro R (f x0)).
apply (proj2 H4 x0 H5).
move=> H1 eps H2.
elim (proj1 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub)))) y eps H2).
move=> dlt H3.
elim (H1 dlt (proj1 H3)).
move=> alp H4.
exists alp.
apply conj.
apply (proj1 H4).
move=> x0 H5.
apply (proj2 H3 (f x0)).
apply (proj2 H4 x0 H5).
Qed.

Lemma limit_inf_R_extend_same : forall (M : Metric_Space) (f : (Base M) -> R) (B : Ensemble (Base M)) (x : Base M), limit_inf_R M f B x <-> limit_in M Rextend_met (fun (r : Base M) => Rval (f r)) B x Rinf.
Proof.
move=> M f B x.
apply conj.
move=> H1 eps H2.
elim (proj1 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub))))) eps H2).
move=> dlt H3.
elim (H1 dlt).
move=> alp H4.
exists alp.
apply conj.
apply (proj1 H4).
move=> x0 H5.
apply (H3 (f x0)).
apply conj.
apply (Full_intro R (f x0)).
apply (Rgt_ge (f x0) dlt).
apply (proj2 H4 x0 H5).
move=> H1 eps.
elim (H1 (1 - (proj1_sig Rextendmetfunsub eps))).
move=> dlt H2.
exists dlt.
apply conj.
apply (proj1 H2).
move=> x0 H3.
apply (Rnot_ge_gt eps (f x0)).
move=> H4.
apply (Rlt_not_le (1 - proj1_sig Rextendmetfunsub eps) (dist Rextend_met (Rval (f x0)) Rinf)).
apply (proj2 H2 x0 H3).
unfold dist.
unfold Rextend_met.
unfold Rextendmetdist.
unfold R_dist.
apply (Rle_trans (1 - proj1_sig Rextendmetfunsub eps) (1 - proj1_sig Rextendmetfunsub (f x0)) (Rabs (Rextendmetfun (Rval (f x0)) - Rextendmetfun Rinf))).
apply (Rplus_le_compat_l 1 (- proj1_sig Rextendmetfunsub eps) (- proj1_sig Rextendmetfunsub (f x0))).
apply (Ropp_ge_le_contravar (proj1_sig Rextendmetfunsub eps) (proj1_sig Rextendmetfunsub (f x0))).
elim H4.
move=> H5.
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) (f x0) eps H5).
move=> H5.
rewrite H5.
right.
reflexivity.
rewrite (Rabs_minus_sym (Rextendmetfun (Rval (f x0))) (Rextendmetfun Rinf)).
apply (Rle_abs (1 - proj1_sig Rextendmetfunsub (f x0))).
apply (Rgt_minus 1 (proj1_sig Rextendmetfunsub eps)).
apply (proj2 (proj1 (proj2_sig Rextendmetfunsub) eps)).
Qed.

Lemma limit_minf_R_extend_same : forall (M : Metric_Space) (f : (Base M) -> R) (B : Ensemble (Base M)) (x : Base M), limit_minf_R M f B x <-> limit_in M Rextend_met (fun (r : Base M) => Rval (f r)) B x Rminf.
Proof.
move=> M f B x.
apply conj.
move=> H1 eps H2.
elim (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub)))))) eps H2).
move=> dlt H3.
elim (H1 dlt).
move=> alp H4.
exists alp.
apply conj.
apply (proj1 H4).
move=> x0 H5.
apply (H3 (f x0)).
apply conj.
apply (Full_intro R (f x0)).
apply (Rlt_le (f x0) dlt).
apply (proj2 H4 x0 H5).
move=> H1 eps.
elim (H1 ((proj1_sig Rextendmetfunsub eps) - (- (1)))).
move=> dlt H2.
exists dlt.
apply conj.
apply (proj1 H2).
move=> x0 H3.
apply (Rnot_le_lt eps (f x0)).
move=> H4.
apply (Rlt_not_le (proj1_sig Rextendmetfunsub eps - (- (1))) (dist Rextend_met (Rval (f x0)) Rminf)).
apply (proj2 H2 x0 H3).
unfold dist.
unfold Rextend_met.
unfold Rextendmetdist.
unfold R_dist.
apply (Rle_trans (proj1_sig Rextendmetfunsub eps - - (1)) (proj1_sig Rextendmetfunsub (f x0) - - (1)) (Rabs (Rextendmetfun (Rval (f x0)) - Rextendmetfun Rminf))).
apply (Rplus_le_compat_r (- - 1) (proj1_sig Rextendmetfunsub eps) (proj1_sig Rextendmetfunsub (f x0))).
elim H4.
move=> H5.
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) eps (f x0) H5).
move=> H5.
rewrite H5.
right.
reflexivity.
unfold Rextendmetfun.
apply (Rle_abs (proj1_sig Rextendmetfunsub (f x0) - -1)).
apply (Rgt_minus (proj1_sig Rextendmetfunsub eps) (- (1))).
apply (proj1 (proj1 (proj2_sig Rextendmetfunsub) eps)).
Qed.

Lemma limit_R_inf_extend_same : forall (M : Metric_Space) (f : R -> (Base M)) (F : Rextend -> (Base M)) (B : Ensemble R) (x : Base M), (forall (r : R), f r = F (Rval r)) -> (limit_R_inf M f B x <-> limit_in Rextend_met M F (fun (r : Rextend) => exists (l : R), In R B l /\ r = Rval l) Rinf x).
Proof.
move=> M f F B x H1.
apply conj.
move=> H2 eps H3.
elim (H2 eps H3).
move=> dlt H4.
exists (1 - (proj1_sig Rextendmetfunsub dlt)).
apply conj.
apply (Rgt_minus 1 (proj1_sig Rextendmetfunsub dlt)).
apply (proj2 (proj1 (proj2_sig Rextendmetfunsub) dlt)).
move=> x0 H5.
elim (proj1 H5).
move=> k H6.
rewrite (proj2 H6).
rewrite - (H1 k).
apply (H4 k).
apply conj.
apply (proj1 H6).
apply (Rnot_lt_ge k dlt).
move=> H7.
apply (Rlt_not_le (1 - proj1_sig Rextendmetfunsub dlt) (dist Rextend_met x0 Rinf)).
apply (proj2 H5).
apply (Rle_trans (1 - proj1_sig Rextendmetfunsub dlt) (1 - proj1_sig Rextendmetfunsub k) (dist Rextend_met x0 Rinf)).
apply (Rplus_le_compat_l 1 (- proj1_sig Rextendmetfunsub dlt) (- proj1_sig Rextendmetfunsub k)).
apply (Ropp_ge_le_contravar (proj1_sig Rextendmetfunsub dlt) (proj1_sig Rextendmetfunsub k)).
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) k dlt H7).
rewrite (proj2 H6).
unfold dist.
unfold Rextend_met.
unfold Rextendmetdist.
unfold R_dist.
rewrite (Rabs_minus_sym (Rextendmetfun (Rval k)) (Rextendmetfun Rinf)).
unfold Rextendmetfun.
apply (Rle_abs (1 - proj1_sig Rextendmetfunsub k)).
move=> H2 eps H3.
elim (H2 eps H3).
move=> dlt H4.
elim (proj1 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub))))) dlt (proj1 H4)).
move=> alp H5.
exists alp.
move=> r H6.
rewrite (H1 r).
apply (proj2 H4 (Rval r)).
apply conj.
exists r.
apply conj.
apply (proj1 H6).
reflexivity.
apply (H5 r).
apply conj.
apply (Full_intro R r).
apply (proj2 H6).
Qed.

Lemma limit_R_minf_extend_same : forall (M : Metric_Space) (f : R -> (Base M)) (F : Rextend -> (Base M)) (B : Ensemble R) (x : Base M), (forall (r : R), f r = F (Rval r)) -> (limit_R_minf M f B x <-> limit_in Rextend_met M F (fun (r : Rextend) => exists (l : R), In R B l /\ r = Rval l) Rminf x).
Proof.
move=> M f F B x H1.
apply conj.
move=> H2 eps H3.
elim (H2 eps H3).
move=> dlt H4.
exists ((proj1_sig Rextendmetfunsub dlt) - - (1)).
apply conj.
apply (Rgt_minus (proj1_sig Rextendmetfunsub dlt) (- (1))).
apply (proj1 (proj1 (proj2_sig Rextendmetfunsub) dlt)).
move=> x0 H5.
elim (proj1 H5).
move=> k H6.
rewrite (proj2 H6).
rewrite - (H1 k).
apply (H4 k).
apply conj.
apply (proj1 H6).
apply (Rnot_gt_le k dlt).
move=> H7.
apply (Rgt_not_ge (dist Rextend_met x0 Rminf) (proj1_sig Rextendmetfunsub dlt - - (1))).
apply (proj2 H5).
apply (Rge_trans (dist Rextend_met x0 Rminf) (proj1_sig Rextendmetfunsub k - - (1)) (proj1_sig Rextendmetfunsub dlt - - (1))).
unfold dist.
unfold Rextend_met.
unfold Rextendmetdist.
unfold R_dist.
rewrite (proj2 H6).
unfold Rextendmetfun.
apply (Rle_ge (proj1_sig Rextendmetfunsub k - - (1)) (Rabs (proj1_sig Rextendmetfunsub k - - 1))).
apply (Rle_abs (proj1_sig Rextendmetfunsub k - - 1)).
apply (Rplus_ge_compat_r (- - (1)) (proj1_sig Rextendmetfunsub k) (proj1_sig Rextendmetfunsub dlt)).
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) dlt k H7).
move=> H2 eps H3.
elim (H2 eps H3).
move=> dlt H4.
elim (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub)))))) dlt (proj1 H4)).
move=> alp H5.
exists alp.
move=> r H6.
rewrite (H1 r).
apply (proj2 H4 (Rval r)).
apply conj.
exists r.
apply conj.
apply (proj1 H6).
reflexivity.
apply (H5 r).
apply conj.
apply (Full_intro R r).
apply (proj2 H6).
Qed.

Definition limit_inf_inf (f : R -> R) (B : Ensemble R) := forall (M : R), exists (m : R), forall (r : R), B r /\ r >= m -> (f r) >= M.

Definition limit_inf_minf (f : R -> R) (B : Ensemble R) := forall (M : R), exists (m : R), forall (r : R), B r /\ r >= m -> (f r) <= M.

Definition limit_minf_inf (f : R -> R) (B : Ensemble R) := forall (M : R), exists (m : R), forall (r : R), B r /\ r <= m -> (f r) >= M.

Definition limit_minf_minf (f : R -> R) (B : Ensemble R) := forall (M : R), exists (m : R), forall (r : R), B r /\ r <= m -> (f r) <= M.

Lemma limit_inf_inf_extend_same : forall (f : R -> R) (F : Rextend -> Rextend) (B : Ensemble R), (forall (r : R), Rval (f r) = F (Rval r)) -> (limit_inf_inf f B <-> limit_in Rextend_met Rextend_met F (fun (r : Rextend) => exists (l : R), In R B l /\ r = Rval l) Rinf Rinf).
Proof.
move=> f F B H1.
apply conj.
move=> H2 eps H3.
elim (proj1 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub))))) eps H3).
move=> dlt H4.
elim (H2 dlt).
move=> alp H5.
exists (1 - (proj1_sig Rextendmetfunsub alp)).
apply conj. 
apply (Rgt_minus 1 (proj1_sig Rextendmetfunsub alp)).
apply (proj2 (proj1 (proj2_sig Rextendmetfunsub) alp)).
move=> x H6.
elim (proj1 H6).
move=> r H7.
rewrite (proj2 H7).
rewrite - (H1 r).
apply (H4 (f r)).
apply conj.
apply (Full_intro R (f r)).
apply (H5 r).
apply conj.
apply (proj1 H7).
apply (Rnot_lt_ge r alp).
move=> H8.
apply (Rlt_not_le (1 - proj1_sig Rextendmetfunsub alp) (dist Rextend_met x Rinf) (proj2 H6)).
apply (Rle_trans (1 - proj1_sig Rextendmetfunsub alp) (1 - proj1_sig Rextendmetfunsub r) (dist Rextend_met x Rinf)).
apply (Rplus_le_compat_l 1 (- proj1_sig Rextendmetfunsub alp) (- proj1_sig Rextendmetfunsub r)).
apply (Ropp_le_contravar (proj1_sig Rextendmetfunsub alp) (proj1_sig Rextendmetfunsub r)).
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) r alp H8).
rewrite (proj2 H7).
unfold dist.
unfold Rextend_met.
unfold Rextendmetdist.
unfold R_dist.
rewrite (Rabs_minus_sym (Rextendmetfun (Rval r)) (Rextendmetfun Rinf)).
apply (Rle_abs (1 - proj1_sig Rextendmetfunsub r)).
move=> H2 eps.
elim (H2 (1 - proj1_sig Rextendmetfunsub eps)).
move=> dlt H3.
elim (proj1 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub))))) dlt (proj1 H3)).
move=> alp H4.
exists alp.
move=> r H5.
apply (Rnot_lt_ge (f r) eps).
move=> H6.
apply (Rlt_not_le (1 - proj1_sig Rextendmetfunsub eps) (dist Rextend_met (Rval (f r)) Rinf)).
rewrite (H1 r).
apply (proj2 H3 (Rval r)).
apply conj.
exists r.
apply conj.
apply (proj1 H5).
reflexivity.
apply (H4 r).
apply conj.
apply (Full_intro R r).
apply (proj2 H5).
unfold dist.
unfold Rextend_met.
unfold Rextendmetdist.
unfold R_dist.
rewrite (Rabs_left (Rextendmetfun (Rval (f r)) - Rextendmetfun Rinf)).
rewrite (Ropp_minus_distr (Rextendmetfun (Rval (f r))) (Rextendmetfun Rinf)).
unfold Rextendmetfun.
apply (Rplus_le_compat_l 1 (- proj1_sig Rextendmetfunsub eps) (- proj1_sig Rextendmetfunsub (f r))).
apply (Ropp_le_contravar (proj1_sig Rextendmetfunsub eps) (proj1_sig Rextendmetfunsub (f r))).
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) (f r) eps H6).
apply (Rlt_minus (Rextendmetfun (Rval (f r))) (Rextendmetfun Rinf)).
apply (proj2 (proj1 (proj2_sig Rextendmetfunsub) (f r))).
apply (Rgt_minus 1 (proj1_sig Rextendmetfunsub eps)).
apply (proj2 (proj1 (proj2_sig Rextendmetfunsub) eps)).
Qed.

Lemma limit_inf_minf_extend_same : forall (f : R -> R) (F : Rextend -> Rextend) (B : Ensemble R), (forall (r : R), Rval (f r) = F (Rval r)) -> (limit_inf_minf f B <-> limit_in Rextend_met Rextend_met F (fun (r : Rextend) => exists (l : R), In R B l /\ r = Rval l) Rinf Rminf).
Proof.
move=> f F B H1.
apply conj.
move=> H2 eps H3.
elim (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub)))))) eps H3).
move=> dlt H4.
elim (H2 dlt).
move=> alp H5.
exists (1 - (proj1_sig Rextendmetfunsub alp)).
apply conj. 
apply (Rgt_minus 1 (proj1_sig Rextendmetfunsub alp)).
apply (proj2 (proj1 (proj2_sig Rextendmetfunsub) alp)).
move=> x H6.
elim (proj1 H6).
move=> r H7.
rewrite (proj2 H7).
rewrite - (H1 r).
apply (H4 (f r)).
apply conj.
apply (Full_intro R (f r)).
apply (H5 r).
apply conj.
apply (proj1 H7).
apply (Rnot_lt_ge r alp).
move=> H8.
apply (Rlt_not_le (1 - proj1_sig Rextendmetfunsub alp) (dist Rextend_met x Rinf) (proj2 H6)).
apply (Rle_trans (1 - proj1_sig Rextendmetfunsub alp) (1 - proj1_sig Rextendmetfunsub r) (dist Rextend_met x Rinf)).
apply (Rplus_le_compat_l 1 (- proj1_sig Rextendmetfunsub alp) (- proj1_sig Rextendmetfunsub r)).
apply (Ropp_le_contravar (proj1_sig Rextendmetfunsub alp) (proj1_sig Rextendmetfunsub r)).
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) r alp H8).
rewrite (proj2 H7).
unfold dist.
unfold Rextend_met.
unfold Rextendmetdist.
unfold R_dist.
rewrite (Rabs_minus_sym (Rextendmetfun (Rval r)) (Rextendmetfun Rinf)).
apply (Rle_abs (1 - proj1_sig Rextendmetfunsub r)).
move=> H2 eps.
elim (H2 (proj1_sig Rextendmetfunsub eps - - (1))).
move=> dlt H3.
elim (proj1 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub))))) dlt (proj1 H3)).
move=> alp H4.
exists alp.
move=> r H5.
apply (Rnot_gt_le (f r) eps).
move=> H6.
apply (Rlt_not_le (proj1_sig Rextendmetfunsub eps - - (1)) (dist Rextend_met (Rval (f r)) Rminf)).
rewrite (H1 r).
apply (proj2 H3 (Rval r)).
apply conj.
exists r.
apply conj.
apply (proj1 H5).
reflexivity.
apply (H4 r).
apply conj.
apply (Full_intro R r).
apply (proj2 H5).
unfold dist.
unfold Rextend_met.
unfold Rextendmetdist.
unfold R_dist.
apply (Rle_trans (proj1_sig Rextendmetfunsub eps - - (1)) (proj1_sig Rextendmetfunsub (f r) - - (1)) (Rabs (Rextendmetfun (Rval (f r)) - Rextendmetfun Rminf))).
apply (Rplus_le_compat_r (- - (1)) (proj1_sig Rextendmetfunsub eps) (proj1_sig Rextendmetfunsub (f r))).
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) eps (f r) H6).
apply (Rle_abs (Rextendmetfun (Rval (f r)) - Rextendmetfun Rminf)).
apply (Rgt_minus (proj1_sig Rextendmetfunsub eps) (- (1))).
apply (proj1 (proj1 (proj2_sig Rextendmetfunsub) eps)).
Qed.

Lemma limit_minf_inf_extend_same : forall (f : R -> R) (F : Rextend -> Rextend) (B : Ensemble R), (forall (r : R), Rval (f r) = F (Rval r)) -> (limit_minf_inf f B <-> limit_in Rextend_met Rextend_met F (fun (r : Rextend) => exists (l : R), In R B l /\ r = Rval l) Rminf Rinf).
Proof.
move=> f F B H1.
apply conj.
move=> H2 eps H3.
elim (proj1 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub))))) eps H3).
move=> dlt H4.
elim (H2 dlt).
move=> alp H5.
exists ((proj1_sig Rextendmetfunsub alp) - - (1)).
apply conj.
apply (Rgt_minus (proj1_sig Rextendmetfunsub alp) (- (1))).
apply (proj1 (proj1 (proj2_sig Rextendmetfunsub) alp)).
move=> x H6.
elim (proj1 H6).
move=> r H7.
rewrite (proj2 H7).
rewrite - (H1 r).
apply (H4 (f r)).
apply conj.
apply (Full_intro R (f r)).
apply (H5 r).
apply conj.
apply (proj1 H7).
apply (Rnot_gt_le r alp).
move=> H8.
apply (Rlt_not_le (proj1_sig Rextendmetfunsub alp - - (1)) (dist Rextend_met x Rminf) (proj2 H6)).
apply (Rle_trans (proj1_sig Rextendmetfunsub alp - - (1)) (proj1_sig Rextendmetfunsub r - - (1)) (dist Rextend_met x Rminf)).
apply (Rplus_le_compat_r (- - (1)) (proj1_sig Rextendmetfunsub alp) (proj1_sig Rextendmetfunsub r)).
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) alp r H8).
rewrite (proj2 H7).
unfold dist.
unfold Rextend_met.
unfold Rextendmetdist.
unfold R_dist.
apply (Rle_abs (proj1_sig Rextendmetfunsub r - - (1))).
move=> H2 eps.
elim (H2 (1 - proj1_sig Rextendmetfunsub eps)).
move=> dlt H3.
elim (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub)))))) dlt (proj1 H3)).
move=> alp H4.
exists alp.
move=> r H5.
apply (Rnot_lt_ge (f r) eps).
move=> H6.
apply (Rlt_not_le (1 - proj1_sig Rextendmetfunsub eps) (dist Rextend_met (Rval (f r)) Rinf)).
rewrite (H1 r).
apply (proj2 H3 (Rval r)).
apply conj.
exists r.
apply conj.
apply (proj1 H5).
reflexivity.
apply (H4 r).
apply conj.
apply (Full_intro R r).
apply (proj2 H5).
unfold dist.
unfold Rextend_met.
unfold Rextendmetdist.
unfold R_dist.
rewrite (Rabs_left (Rextendmetfun (Rval (f r)) - Rextendmetfun Rinf)).
rewrite (Ropp_minus_distr (Rextendmetfun (Rval (f r))) (Rextendmetfun Rinf)).
unfold Rextendmetfun.
apply (Rplus_le_compat_l 1 (- proj1_sig Rextendmetfunsub eps) (- proj1_sig Rextendmetfunsub (f r))).
apply (Ropp_le_contravar (proj1_sig Rextendmetfunsub eps) (proj1_sig Rextendmetfunsub (f r))).
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) (f r) eps H6).
apply (Rlt_minus (Rextendmetfun (Rval (f r))) (Rextendmetfun Rinf)).
apply (proj2 (proj1 (proj2_sig Rextendmetfunsub) (f r))).
apply (Rgt_minus 1 (proj1_sig Rextendmetfunsub eps)).
apply (proj2 (proj1 (proj2_sig Rextendmetfunsub) eps)).
Qed.

Lemma limit_minf_minf_extend_same : forall (f : R -> R) (F : Rextend -> Rextend) (B : Ensemble R), (forall (r : R), Rval (f r) = F (Rval r)) -> (limit_minf_minf f B <-> limit_in Rextend_met Rextend_met F (fun (r : Rextend) => exists (l : R), In R B l /\ r = Rval l) Rminf Rminf).
Proof.
move=> f F B H1.
apply conj.
move=> H2 eps H3.
elim (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub)))))) eps H3).
move=> dlt H4.
elim (H2 dlt).
move=> alp H5.
exists ((proj1_sig Rextendmetfunsub alp) - - (1)).
apply conj. 
apply (Rgt_minus (proj1_sig Rextendmetfunsub alp) (- (1))).
apply (proj1 (proj1 (proj2_sig Rextendmetfunsub) alp)).
move=> x H6.
elim (proj1 H6).
move=> r H7.
rewrite (proj2 H7).
rewrite - (H1 r).
apply (H4 (f r)).
apply conj.
apply (Full_intro R (f r)).
apply (H5 r).
apply conj.
apply (proj1 H7).
apply (Rnot_gt_le r alp).
move=> H8.
apply (Rlt_not_le (proj1_sig Rextendmetfunsub alp - - (1)) (dist Rextend_met x Rminf) (proj2 H6)).
apply (Rle_trans (proj1_sig Rextendmetfunsub alp - - (1)) (proj1_sig Rextendmetfunsub r - - (1)) (dist Rextend_met x Rminf)).
apply (Rplus_le_compat_r (- - (1)) (proj1_sig Rextendmetfunsub alp) (proj1_sig Rextendmetfunsub r)).
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) alp r H8).
rewrite (proj2 H7).
unfold dist.
unfold Rextend_met.
unfold Rextendmetdist.
unfold R_dist.
apply (Rle_abs (proj1_sig Rextendmetfunsub r - - (1))).
move=> H2 eps.
elim (H2 (proj1_sig Rextendmetfunsub eps - - (1))).
move=> dlt H3.
elim (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub)))))) dlt (proj1 H3)).
move=> alp H4.
exists alp.
move=> r H5.
apply (Rnot_gt_le (f r) eps).
move=> H6.
apply (Rlt_not_le (proj1_sig Rextendmetfunsub eps - - (1)) (dist Rextend_met (Rval (f r)) Rminf)).
rewrite (H1 r).
apply (proj2 H3 (Rval r)).
apply conj.
exists r.
apply conj.
apply (proj1 H5).
reflexivity.
apply (H4 r).
apply conj.
apply (Full_intro R r).
apply (proj2 H5).
unfold dist.
unfold Rextend_met.
unfold Rextendmetdist.
unfold R_dist.
apply (Rle_trans (proj1_sig Rextendmetfunsub eps - - (1)) (proj1_sig Rextendmetfunsub (f r) - - (1)) (Rabs (Rextendmetfun (Rval (f r)) - Rextendmetfun Rminf))).
apply (Rplus_le_compat_r (- - (1)) (proj1_sig Rextendmetfunsub eps) (proj1_sig Rextendmetfunsub (f r))).
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) eps (f r) H6).
apply (Rle_abs (Rextendmetfun (Rval (f r)) - Rextendmetfun Rminf)).
apply (Rgt_minus (proj1_sig Rextendmetfunsub eps) (- (1))).
apply (proj1 (proj1 (proj2_sig Rextendmetfunsub) eps)).
Qed.

Lemma Un_cv_extend_same : forall (an : nat -> R) (a : R), (Un_cv an a) <-> (Un_cv_met Rextend_met (fun (n : nat) => Rval (an n)) (Rval a)).
Proof.
move=> an a.
apply conj.
move=> H1 eps H2.
elim (proj1 (proj2 (proj2 (proj2_sig Rextendmetfunsub))) a eps H2).
move=> dlt H3.
elim (H1 dlt (proj1 H3)).
move=> N H4.
exists N.
move=> n H5.
apply (proj2 H3 (an n)).
apply conj.
apply (Full_intro R (an n)).
apply (H4 n H5).
move=> H1 eps H2.
elim (proj1 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub)))) a eps H2).
move=> dlt H3.
elim (H1 dlt (proj1 H3)).
move=> N H4.
exists N.
move=> n H5.
apply (proj2 H3 (an n)).
apply (H4 n H5).
Qed.

Lemma Un_inf_extend_same : forall (an : nat -> R), (Un_inf an) <-> (Un_cv_met Rextend_met (fun (n : nat) => Rval (an n)) Rinf).
Proof.
move=> an.
apply conj.
move=> H1 eps H2.
elim (proj1 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub))))) eps H2).
move=> dlt H3.
elim (H1 dlt).
move=> N H4.
exists N.
move=> n H5.
apply (H3 (an n)).
apply conj.
apply (Full_intro R (an n)).
apply (Rgt_ge (an n) dlt (H4 n H5)).
move=> H1 eps.
elim (H1 (1 - (proj1_sig Rextendmetfunsub eps))).
move=> N H2.
exists N.
move=> n H3.
apply (Rnot_ge_gt eps (an n)).
move=> H4.
apply (Rlt_not_le (1 - proj1_sig Rextendmetfunsub eps) (dist Rextend_met (Rval (an n)) Rinf)).
apply (H2 n H3).
apply (Rle_trans (1 - proj1_sig Rextendmetfunsub eps) (1 - proj1_sig Rextendmetfunsub (an n)) (dist Rextend_met (Rval (an n)) Rinf)).
apply (Rplus_le_compat_l 1 (- proj1_sig Rextendmetfunsub eps) (- proj1_sig Rextendmetfunsub (an n))).
apply (Ropp_le_contravar (proj1_sig Rextendmetfunsub eps) (proj1_sig Rextendmetfunsub (an n))).
elim H4.
move=> H5.
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) (an n) eps H5).
move=> H5.
rewrite H5.
right.
reflexivity.
unfold dist.
unfold Rextend_met.
unfold Rextendmetdist.
unfold R_dist.
unfold Rextendmetfun.
rewrite (Rabs_minus_sym (proj1_sig Rextendmetfunsub (an n)) 1).
apply (Rle_abs (1 - proj1_sig Rextendmetfunsub (an n))).
apply (Rgt_minus 1 (proj1_sig Rextendmetfunsub eps)).
apply (proj2 (proj1 (proj2_sig Rextendmetfunsub) eps)).
Qed.

Lemma Un_minf_extend_same : forall (an : nat -> R), (Un_minf an) <-> (Un_cv_met Rextend_met (fun (n : nat) => Rval (an n)) Rminf).
Proof.
move=> an.
apply conj.
move=> H1 eps H2.
elim (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub)))))) eps H2).
move=> dlt H3.
elim (H1 dlt).
move=> N H4.
exists N.
move=> n H5.
apply (H3 (an n)).
apply conj.
apply (Full_intro R (an n)).
apply (Rlt_le (an n) dlt (H4 n H5)).
move=> H1 eps.
elim (H1 ((proj1_sig Rextendmetfunsub eps) - - (1))).
move=> N H2.
exists N.
move=> n H3.
apply (Rnot_le_lt eps (an n)).
move=> H4.
apply (Rlt_not_le (proj1_sig Rextendmetfunsub eps - - (1)) (dist Rextend_met (Rval (an n)) Rminf)).
apply (H2 n H3).
apply (Rle_trans (proj1_sig Rextendmetfunsub eps - - (1)) (proj1_sig Rextendmetfunsub (an n) - - (1)) (dist Rextend_met (Rval (an n)) Rminf)).
apply (Rplus_le_compat_r (- - (1)) (proj1_sig Rextendmetfunsub eps) (proj1_sig Rextendmetfunsub (an n))).
elim H4.
move=> H5.
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) eps (an n) H5).
move=> H5.
rewrite H5.
right.
reflexivity.
unfold dist.
unfold Rextend_met.
unfold Rextendmetdist.
unfold R_dist.
apply (Rle_abs (proj1_sig Rextendmetfunsub (an n) - - (1))).
apply (Rgt_minus (proj1_sig Rextendmetfunsub eps) (- (1))).
apply (proj1 (proj1 (proj2_sig Rextendmetfunsub) eps)).
Qed.

Lemma BanachRextend : Banach Rextend_met.
Proof.
move=> an H1.
elim (proj2 (Theorem_3_6 (fun (n : nat) => Rextendmetfun (an n))) H1).
move=> A H2.
suff: (exists (a : Rextend), Rextendmetfun a = A).
elim.
move=> a H3.
exists a.
unfold Un_cv_met.
unfold Rextend_met.
unfold dist.
unfold Rextendmetdist.
rewrite H3.
apply H2.
suff: (- (1) <= A <= 1).
move=> H3.
elim (classic (A = 1)).
move=> H4.
rewrite H4.
exists Rinf.
reflexivity.
move=> H4.
elim (classic (A = - (1))).
move=> H5.
rewrite H5.
exists Rminf.
reflexivity.
move=> H5.
elim (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2_sig Rextendmetfunsub)))))) A).
move=> x H6.
exists (Rval x).
apply H6.
apply conj.
elim (proj1 H3).
apply.
move=> H6.
apply False_ind.
apply H5.
rewrite H6.
reflexivity.
elim (proj2 H3).
apply.
move=> H6.
apply False_ind.
apply H4.
rewrite H6.
reflexivity.
apply conj.
apply (Theorem_2_6_Collorary_2 (fun n : nat => Rextendmetfun (an n)) A (- (1)) H2).
move=> n.
elim (an n).
apply (Rlt_le (- (1)) 1).
apply (Rlt_trans (- (1)) 0 1).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply Rlt_0_1.
apply (Req_le (- (1)) (Rextendmetfun Rminf)).
reflexivity.
move=> r.
left.
apply (proj1 (proj1 (proj2_sig Rextendmetfunsub) r)).
apply (Theorem_2_6_Collorary_1 (fun n : nat => Rextendmetfun (an n)) A 1 H2).
move=> n.
elim (an n).
apply (Req_le (Rextendmetfun Rinf) 1).
reflexivity.
apply (Rlt_le (- (1)) 1).
apply (Rlt_trans (- (1)) 0 1).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply Rlt_0_1.
move=> r.
left.
apply (proj2 (proj1 (proj2_sig Rextendmetfunsub) r)).
Qed.

Lemma Theorem_6_10_2 : forall (M2 : Metric_Space) (f : R -> Base M2) (B : Ensemble R), (Banach M2) -> ((exists (y : Base M2), limit_R_inf M2 f B y) <-> (forall (eps : R), eps > 0 -> exists (dlt : R), forall (z1 z2 : R), (In R (Intersection R (fun (r : R) => r >= dlt) B) z1) -> (In R (Intersection R (fun (r : R) => r >= dlt) B) z2) -> dist M2 (f z1) (f z2) < eps)).
Proof.
move=> M2 f B H1.
apply conj.
elim.
move=> y H2 eps H3.
elim (H2 (eps / 2) (eps2_Rgt_R0 eps H3)).
move=> dlt H4.
exists dlt.
move=> z1 z2 H5 H6.
apply (Rle_lt_trans (dist M2 (f z1) (f z2)) (dist M2 (f z1) y + dist M2 (f z2) y) eps).
rewrite (dist_sym M2 (f z2) y).
apply (dist_tri M2 (f z1) (f z2) y).
rewrite - (eps2 eps).
apply (Rplus_lt_compat (dist M2 (f z1) y) (eps * / 2) (dist M2 (f z2) y) (eps * / 2)).
apply (H4 z1).
apply conj.
elim H5.
move=> x H7.
apply.
elim H5.
move=> x H7 H8.
apply H7. 
apply (H4 z2).
apply conj.
elim H6.
move=> x H7.
apply.
elim H6.
move=> x H7 H8.
apply H7.
move=> H2.
suff: (exists y : Base M2, limit_in Rextend_met M2 (fun (r : Rextend) => match r with 
| Rinf => (f 0)
| Rminf => (f 0)
| Rval r => (f r)
end) (fun r : Rextend => exists l : R, In R B l /\ r = Rval l) Rinf y).
elim.
move=> y H3.
exists y.
apply (limit_R_inf_extend_same M2 f (fun (r : Rextend) => match r with 
| Rinf => (f 0)
| Rminf => (f 0)
| Rval r => (f r)
end) B y).
move=> r.
reflexivity.
apply H3.
apply Theorem_6_10_1.
apply H1.
move=> eps H3.
elim (H2 eps H3).
move=> dlt H4.
exists (1 - (proj1_sig Rextendmetfunsub dlt)).
apply conj.
apply (Rgt_minus 1 (proj1_sig Rextendmetfunsub dlt)).
apply (proj2 (proj1 (proj2_sig Rextendmetfunsub) dlt)).
move=> z1 z2 H5 H6.
elim H5.
move=> z3 H7 H8.
elim H6.
move=> z4 H9 H10.
elim H8.
move=> l1 H11.
elim H10.
move=> l2 H12.
rewrite (proj2 H11).
rewrite (proj2 H12).
apply (H4 l1 l2).
apply Intersection_intro.
apply (Rnot_gt_ge dlt l1).
move=> H13.
apply (Rlt_not_le (1 - proj1_sig Rextendmetfunsub dlt) (dist Rextend_met Rinf z3)).
rewrite (dist_sym Rextend_met Rinf z3).
apply H7.
rewrite (proj2 H11).
unfold dist.
unfold Rextend_met.
apply (Rle_trans (1 - proj1_sig Rextendmetfunsub dlt) (1 - proj1_sig Rextendmetfunsub l1) (Rextendmetdist Rinf (Rval l1))).
apply (Rplus_le_compat_l 1 (- proj1_sig Rextendmetfunsub dlt) (- proj1_sig Rextendmetfunsub l1)).
apply (Ropp_le_contravar (proj1_sig Rextendmetfunsub dlt) (proj1_sig Rextendmetfunsub l1)).
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) l1 dlt H13).
apply Rle_abs.
apply (proj1 H11).
apply Intersection_intro.
apply (Rnot_gt_ge dlt l2).
move=> H13.
apply (Rlt_not_le (1 - proj1_sig Rextendmetfunsub dlt) (dist Rextend_met Rinf z4)).
rewrite (dist_sym Rextend_met Rinf z4).
apply H9.
rewrite (proj2 H12).
unfold dist.
unfold Rextend_met.
apply (Rle_trans (1 - proj1_sig Rextendmetfunsub dlt) (1 - proj1_sig Rextendmetfunsub l2) (Rextendmetdist Rinf (Rval l2))).
apply (Rplus_le_compat_l 1 (- proj1_sig Rextendmetfunsub dlt) (- proj1_sig Rextendmetfunsub l2)).
apply (Ropp_le_contravar (proj1_sig Rextendmetfunsub dlt) (proj1_sig Rextendmetfunsub l2)).
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) l2 dlt H13).
apply Rle_abs.
apply (proj1 H12).
Qed.

Lemma Theorem_6_10_3 : forall (M2 : Metric_Space) (f : R -> Base M2) (B : Ensemble R), (Banach M2) -> ((exists (y : Base M2), limit_R_minf M2 f B y) <-> (forall (eps : R), eps > 0 -> exists (dlt : R), forall (z1 z2 : R), (In R (Intersection R (fun (r : R) => r <= dlt) B) z1) -> (In R (Intersection R (fun (r : R) => r <= dlt) B) z2) -> dist M2 (f z1) (f z2) < eps)).
Proof.
move=> M2 f B H1.
apply conj.
elim.
move=> y H2 eps H3.
elim (H2 (eps / 2) (eps2_Rgt_R0 eps H3)).
move=> dlt H4.
exists dlt.
move=> z1 z2 H5 H6.
apply (Rle_lt_trans (dist M2 (f z1) (f z2)) (dist M2 (f z1) y + dist M2 (f z2) y) eps).
rewrite (dist_sym M2 (f z2) y).
apply (dist_tri M2 (f z1) (f z2) y).
rewrite - (eps2 eps).
apply (Rplus_lt_compat (dist M2 (f z1) y) (eps * / 2) (dist M2 (f z2) y) (eps * / 2)).
apply (H4 z1).
apply conj.
elim H5.
move=> x H7.
apply.
elim H5.
move=> x H7 H8.
apply H7. 
apply (H4 z2).
apply conj.
elim H6.
move=> x H7.
apply.
elim H6.
move=> x H7 H8.
apply H7.
move=> H2.
suff: (exists y : Base M2, limit_in Rextend_met M2 (fun (r : Rextend) => match r with 
| Rinf => (f 0)
| Rminf => (f 0)
| Rval r => (f r)
end) (fun r : Rextend => exists l : R, In R B l /\ r = Rval l) Rminf y).
elim.
move=> y H3.
exists y.
apply (limit_R_minf_extend_same M2 f (fun (r : Rextend) => match r with 
| Rinf => (f 0)
| Rminf => (f 0)
| Rval r => (f r)
end) B y).
move=> r.
reflexivity.
apply H3.
apply Theorem_6_10_1.
apply H1.
move=> eps H3.
elim (H2 eps H3).
move=> dlt H4.
exists ((proj1_sig Rextendmetfunsub dlt) - - (1)).
apply conj.
apply (Rgt_minus (proj1_sig Rextendmetfunsub dlt) (- (1))).
apply (proj1 (proj1 (proj2_sig Rextendmetfunsub) dlt)).
move=> z1 z2 H5 H6.
elim H5.
move=> z3 H7 H8.
elim H6.
move=> z4 H9 H10.
elim H8.
move=> l1 H11.
elim H10.
move=> l2 H12.
rewrite (proj2 H11).
rewrite (proj2 H12).
apply (H4 l1 l2).
apply Intersection_intro.
apply (Rnot_lt_le dlt l1).
move=> H13.
apply (Rlt_not_le (proj1_sig Rextendmetfunsub dlt - - (1)) (dist Rextend_met Rminf z3)).
rewrite (dist_sym Rextend_met Rminf z3).
apply H7.
rewrite (proj2 H11).
unfold dist.
unfold Rextend_met.
apply (Rle_trans (proj1_sig Rextendmetfunsub dlt - - (1)) (proj1_sig Rextendmetfunsub l1 - - (1)) (Rextendmetdist Rminf (Rval l1))).
apply (Rplus_le_compat_r (- - (1)) (proj1_sig Rextendmetfunsub dlt) (proj1_sig Rextendmetfunsub l1)).
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) dlt l1 H13).
rewrite Rextenddist_sym.
apply Rle_abs.
apply (proj1 H11).
apply Intersection_intro.
apply (Rnot_lt_le dlt l2).
move=> H13.
apply (Rlt_not_le (proj1_sig Rextendmetfunsub dlt - - (1)) (dist Rextend_met Rminf z4)).
rewrite (dist_sym Rextend_met Rminf z4).
apply H9.
rewrite (proj2 H12).
unfold dist.
unfold Rextend_met.
apply (Rle_trans (proj1_sig Rextendmetfunsub dlt - - (1)) (proj1_sig Rextendmetfunsub l2 - - (1)) (Rextendmetdist Rminf (Rval l2))).
apply (Rplus_le_compat_r (- - (1)) (proj1_sig Rextendmetfunsub dlt) (proj1_sig Rextendmetfunsub l2)).
left.
apply (proj1 (proj2 (proj2_sig Rextendmetfunsub)) dlt l2 H13).
rewrite Rextenddist_sym.
apply Rle_abs.
apply (proj1 H12).
Qed.

Definition RFplus (T : Type) (f g : T -> R) : (T -> R) := (fun (r : T) => (f r) + (g r)).

Lemma RFplus_comm : forall (T : Type) (f g : T -> R), (RFplus T f g) = (RFplus T g f).
Proof.
move=> T f g.
apply functional_extensionality.
move=> x.
apply Rplus_comm.
Qed.

Lemma RFplus_0_r : forall (T : Type) (f : T -> R), (RFplus T f (fun (r : T) => 0)) = f.
Proof.
move=> T f.
apply functional_extensionality.
move=> x.
apply Rplus_0_r.
Qed.

Lemma RFplus_assoc : forall (T : Type) (f g h : T -> R), (RFplus T (RFplus T f g) h) = (RFplus T f (RFplus T g h)).
Proof.
move=> T f g h.
apply functional_extensionality.
move=> x.
apply Rplus_assoc.
Qed.

Definition RFPCM (T : Type) : CommutativeMonoid := mkCommutativeMonoid (T -> R) (fun (r : T) => 0) (RFplus T) (RFplus_comm T) (RFplus_0_r T) (RFplus_assoc T).

Fixpoint sum_f_RF (T : Type) (f : nat -> (T -> R)) (n : nat) : (T -> R) := 
match n with 
| O => f O
| S n0 => RFplus T (sum_f_RF T f n0) (f (S n0))
end.

Lemma MySumEqsum_f_RF : forall (T : Type) (f : nat -> (T -> R)) (N : nat), sum_f_RF T f N = MySumF2 nat (exist (Finite nat) (fun (m : nat) => (O <= m <= N)%nat) (natSectionFinite O N)) (RFPCM T) f.
Proof.
move=> T f N.
suff: forall (n : (Count (S N))), proj1_sig (exist (Finite nat) (fun m : nat => (0 <= m <= N)%nat) (natSectionFinite 0 N)) ((fun (m : Count (S N)) => proj1_sig m) n).
move=> H1.
rewrite - (MySumF2Nature2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= N)%nat) (natSectionFinite 0 N)) (RFPCM T) f (S N) (fun (n : Count (S N)) => proj1_sig n) H1).
unfold SumGF.
suff: (forall (n : nat), (n <= N)%nat -> sum_f_RF T f n = SumGFSub nat (RFPCM T) (S N) (fun n : Count (S N) => proj1_sig n) (fun n : nat => f n) (S n)).
move=> H2.
apply H2.
apply le_n.
elim.
move=> H2.
simpl.
unfold UnwrapGF.
elim (excluded_middle_informative (0 < S N)%nat).
move=> H3.
simpl.
rewrite RFplus_comm.
rewrite RFplus_0_r.
reflexivity.
move=> H3.
apply False_ind.
apply H3.
apply (Nat.lt_0_succ N).
move=> n H2 H3.
simpl.
rewrite H2.
simpl.
suff: (f (S n) = UnwrapGF nat (RFPCM T) (S N) (fun n0 : Count (S N) => proj1_sig n0) (fun n0 : nat => f n0) (S n)).
move=> H4.
rewrite H4.
reflexivity.
unfold UnwrapGF.
elim (excluded_middle_informative (S n < S N)%nat).
move=> H4.
reflexivity.
move=> H4.
apply False_ind.
apply H4.
apply (le_n_S (S n) N H3).
apply le_S_n.
apply le_S.
apply H3.
simpl.
suff: (forall (n : {u : nat | (0 <= u <= N)%nat}), ((proj1_sig n) < (S N))%nat).
move=> H2.
exists (fun (n : {u : nat | (0 <= u <= N)%nat}) => exist (fun (m : nat) => (m < S N)%nat) (proj1_sig n) (H2 n)).
apply conj.
move=> n.
simpl.
apply sig_map.
reflexivity.
move=> n.
apply sig_map.
reflexivity.
move=> n.
apply le_n_S.
apply (proj2_sig n).
move=> n.
simpl.
apply conj.
apply Nat.le_0_l.
apply le_S_n.
apply (proj2_sig n).
Qed.

Definition RnFplus (T : Type) (N : nat) (f g : T -> Rn N) : (T -> Rn N) := (fun (r : T) => Rnplus N (f r) (g r)).

Lemma RnFplus_comm : forall (T : Type) (N : nat) (f g : T -> Rn N), (RnFplus T N f g) = (RnFplus T N g f).
Proof.
move=> T N f g.
apply functional_extensionality.
move=> x.
apply Rnplus_comm.
Qed.

Lemma RnFplus_0_r : forall (T : Type) (N : nat) (f : T -> Rn N), (RnFplus T N f (fun (r : T) => RnO N)) = f.
Proof.
move=> T N f.
apply functional_extensionality.
move=> x.
apply (Vadd_O_r Rfield (RnVS N)).
Qed.

Lemma RnFplus_assoc : forall (T : Type) (N : nat) (f g h : T -> Rn N), (RnFplus T N (RnFplus T N f g) h) = (RnFplus T N f (RnFplus T N g h)).
Proof.
move=> T N f g h.
apply functional_extensionality.
move=> x.
apply Rnplus_assoc.
Qed.

Definition RnFPCM (T : Type) (N : nat) : CommutativeMonoid := mkCommutativeMonoid (T -> Rn N) (fun (r : T) => RnO N) (RnFplus T N) (RnFplus_comm T N) (RnFplus_0_r T N) (RnFplus_assoc T N).

Fixpoint sum_f_RnF (T : Type) (N : nat) (f : nat -> (T -> Rn N)) (n : nat) : (T -> Rn N) := 
match n with 
| O => f O
| S n0 => RnFplus T N (sum_f_RnF T N f n0) (f (S n0))
end.

Lemma MySumEqsum_f_RnF : forall (T : Type) (d : nat) (f : nat -> (T -> Rn d)) (N : nat), sum_f_RnF T d f N = MySumF2 nat (exist (Finite nat) (fun (m : nat) => (O <= m <= N)%nat) (natSectionFinite O N)) (RnFPCM T d) f.
Proof.
move=> T d f N.
suff: forall (n : (Count (S N))), proj1_sig (exist (Finite nat) (fun m : nat => (0 <= m <= N)%nat) (natSectionFinite 0 N)) ((fun (m : Count (S N)) => proj1_sig m) n).
move=> H1.
rewrite - (MySumF2Nature2 nat (exist (Finite nat) (fun m : nat => (0 <= m <= N)%nat) (natSectionFinite 0 N)) (RnFPCM T d) f (S N) (fun (n : Count (S N)) => proj1_sig n) H1).
unfold SumGF.
suff: (forall (n : nat), (n <= N)%nat -> sum_f_RnF T d f n = SumGFSub nat (RnFPCM T d) (S N) (fun n : Count (S N) => proj1_sig n) (fun n : nat => f n) (S n)).
move=> H2.
apply H2.
apply le_n.
elim.
move=> H2.
simpl.
unfold UnwrapGF.
elim (excluded_middle_informative (0 < S N)%nat).
move=> H3.
simpl.
rewrite RnFplus_comm.
rewrite RnFplus_0_r.
reflexivity.
move=> H3.
apply False_ind.
apply H3.
apply (Nat.lt_0_succ N).
move=> n H2 H3.
simpl.
rewrite H2.
simpl.
suff: (f (S n) = UnwrapGF nat (RnFPCM T d) (S N) (fun n0 : Count (S N) => proj1_sig n0) (fun n0 : nat => f n0) (S n)).
move=> H4.
rewrite H4.
reflexivity.
unfold UnwrapGF.
elim (excluded_middle_informative (S n < S N)%nat).
move=> H4.
reflexivity.
move=> H4.
apply False_ind.
apply H4.
apply (le_n_S (S n) N H3).
apply le_S_n.
apply le_S.
apply H3.
simpl.
suff: (forall (n : {u : nat | (0 <= u <= N)%nat}), ((proj1_sig n) < (S N))%nat).
move=> H2.
exists (fun (n : {u : nat | (0 <= u <= N)%nat}) => exist (fun (m : nat) => (m < S N)%nat) (proj1_sig n) (H2 n)).
apply conj.
move=> n.
simpl.
apply sig_map.
reflexivity.
move=> n.
apply sig_map.
reflexivity.
move=> n.
apply le_n_S.
apply (proj2_sig n).
move=> n.
simpl.
apply conj.
apply Nat.le_0_l.
apply le_S_n.
apply (proj2_sig n).
Qed.

Lemma Theorem_6_11 : forall (M1 : Metric_Space) (N : nat) (f : nat -> Base M1 -> Rn N) (B C : Ensemble (Base M1)) (Mn : nat -> R), (Included (Base M1) C B) -> (forall (n : nat) (x : Base M1), (In (Base M1) B x) -> (ContinuousMet M1 (Rn_met N) (f n) C x)) -> (exists (Mm : R), Un_cv (sum_f_R0 Mn) Mm) -> (forall (n : nat) (x : Base M1), (In (Base M1) B x) -> RnNorm N (f n x) <= Mn n) -> {F : Base M1 -> Rn N | (forall (x : Base M1), In (Base M1) B x -> Un_cv_met (Rn_met N) (fun (n : nat) => sum_f_RnF (Base M1) N f n x) (F x)) /\ (forall (x : Base M1), (In (Base M1) B x) -> ContinuousMet M1 (Rn_met N) F C x)}.
Proof.
move=> M1 N f B C Mn H1 H2 H3 H4.
suff: (forall (x : Base M1), (In (Base M1) B x) -> {Fx : Rn N | Un_cv_met (Rn_met N) (fun n : nat => sum_f_RnF (Base M1) N f n x) Fx}).
move=> H6.
exists (fun (x : Base M1) => match (excluded_middle_informative (In (Base M1) B x)) with
| left a => proj1_sig (H6 x a)
| right _ => RnO N
end).
apply conj.
move=> x H7.
elim (excluded_middle_informative (In (Base M1) B x)).
move=> H8.
apply (proj2_sig (H6 x H8)).
move=> H8.
apply False_ind.
apply (H8 H7).
move=> x H7.
move=> eps H8.
suff: (forall (n : nat), ContinuousMet M1 (Rn_met N) (sum_f_RnF (Base M1) N f n) C x).
move=> H9.
elim (proj1 (Theorem_3_6 (sum_f_R0 Mn)) H3 (eps * / 2 * / 2 * / 2)).
move=> k1 H10.
elim (H9 k1 (eps / 2)).
move=> dlt H11.
exists dlt.
apply conj.
apply (proj1 H11).
move=> y H12.
elim (excluded_middle_informative (In (Base M1) B x)).
move=> H13.
elim (excluded_middle_informative (In (Base M1) B y)).
move=> H14.
suff: (forall (x0 : Base M1) (p : B x0), dist M1 x0 x < dlt -> dist (Rn_met N) (proj1_sig (H6 x0 p)) (sum_f_RnF (Base M1) N f k1 x0) < eps * / 2 * / 2).
move=> H15.
apply (Rle_lt_trans (dist (Rn_met N) (proj1_sig (H6 y H14)) (proj1_sig (H6 x H13))) (dist (Rn_met N) (proj1_sig (H6 y H14)) (sum_f_RnF (Base M1) N f k1 y) + dist (Rn_met N) (sum_f_RnF (Base M1) N f k1 y) (sum_f_RnF (Base M1) N f k1 x) + dist (Rn_met N) (sum_f_RnF (Base M1) N f k1 x) (proj1_sig (H6 x H13))) eps).
apply (Rle_trans (dist (Rn_met N) (proj1_sig (H6 y H14)) (proj1_sig (H6 x H13))) (dist (Rn_met N) (proj1_sig (H6 y H14)) (sum_f_RnF (Base M1) N f k1 y) + dist (Rn_met N) (sum_f_RnF (Base M1) N f k1 y) (proj1_sig (H6 x H13)))).
apply dist_tri.
rewrite Rplus_assoc.
apply Rplus_le_compat_l.
apply dist_tri.
rewrite (Rplus_comm (dist (Rn_met N) (proj1_sig (H6 y H14)) (sum_f_RnF (Base M1) N f k1 y)) (dist (Rn_met N) (sum_f_RnF (Base M1) N f k1 y) (sum_f_RnF (Base M1) N f k1 x))).
rewrite Rplus_assoc.
rewrite - (eps2 eps).
apply Rplus_lt_compat.
apply (proj2 H11 y).
apply H12.
rewrite - (eps2 (eps * / 2)).
apply Rplus_lt_compat.
apply (H15 y H14).
apply (proj2 H12).
rewrite dist_sym.
apply (H15 x H13).
rewrite (proj2 (dist_refl M1 x x)).
apply (proj1 H11).
reflexivity.
move=> z H15 H16.
elim (proj2_sig (H6 z H15) (eps * / 2 * / 2 * / 2)).
move=> k2 H17.
apply (Rle_lt_trans (dist (Rn_met N) (proj1_sig (H6 z H15)) (sum_f_RnF (Base M1) N f k1 z)) (dist (Rn_met N) (proj1_sig (H6 z H15)) (sum_f_RnF (Base M1) N f (max k1 k2) z) + dist (Rn_met N) (sum_f_RnF (Base M1) N f (max k1 k2) z) (sum_f_RnF (Base M1) N f k1 z)) (eps * / 2 * / 2)).
apply dist_tri.
rewrite - (eps2 (eps * / 2 * / 2)).
apply Rplus_lt_compat.
rewrite dist_sym.
apply (H17 (max k1 k2)).
apply (Nat.le_max_r k1 k2).
apply (Rle_lt_trans (dist (Rn_met N) (sum_f_RnF (Base M1) N f (max k1 k2) z) (sum_f_RnF (Base M1) N f k1 z)) (R_dist (sum_f_R0 Mn (max k1 k2)) (sum_f_R0 Mn k1)) (eps * / 2 * / 2 * / 2)).
suff: ((FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= Init.Nat.max k1 k2)%nat) (natSectionFinite 0 (Init.Nat.max k1 k2))) (fun m : nat => (0 <= m <= k1)%nat)) = (exist (Finite nat) (fun m : nat => (0 <= m <= k1)%nat) (natSectionFinite 0 k1))).
move=> H18.
rewrite (MySumEqsum_f_RnF (Base M1) N f (max k1 k2)).
rewrite (MySumF2Excluded nat (RnFPCM (Base M1) N) f (exist (Finite nat) (fun m : nat => (0 <= m <= Init.Nat.max k1 k2)%nat) (natSectionFinite 0 (Init.Nat.max k1 k2))) (fun m : nat => (0 <= m <= k1)%nat)).
rewrite (MySumEqsum_f_RnF (Base M1) N f k1).
simpl.
unfold RnFplus.
rewrite (Rnplus_comm N (MySumF2 nat (FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= Init.Nat.max k1 k2)%nat) (natSectionFinite 0 (Init.Nat.max k1 k2))) (fun m : nat => (0 <= m <= k1)%nat)) (RnFPCM (Base M1) N) f z) (MySumF2 nat (FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= Init.Nat.max k1 k2)%nat) (natSectionFinite 0 (Init.Nat.max k1 k2))) (Complement nat (fun m : nat => (0 <= m <= k1)%nat))) (RnFPCM (Base M1) N) f z)).
unfold Rn_dist.
unfold Rnminus.
rewrite Rnplus_assoc.
rewrite H18.
rewrite Rnplus_opp_r.
rewrite Rnplus_comm.
rewrite Rnplus_O_l.
rewrite (MySumEqsum_f_R0 Mn (max k1 k2)).
rewrite (MySumF2Excluded nat RPCM Mn (exist (Finite nat) (fun m : nat => (0 <= m <= Init.Nat.max k1 k2)%nat) (natSectionFinite 0 (Init.Nat.max k1 k2))) (fun m : nat => (0 <= m <= k1)%nat)).
rewrite (MySumEqsum_f_R0 Mn k1).
simpl.
rewrite (Rplus_comm (MySumF2 nat (FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= Init.Nat.max k1 k2)%nat) (natSectionFinite 0 (Init.Nat.max k1 k2))) (fun m : nat => (0 <= m <= k1)%nat)) RPCM Mn) (MySumF2 nat (FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= Init.Nat.max k1 k2)%nat) (natSectionFinite 0 (Init.Nat.max k1 k2))) (Complement nat (fun m : nat => (0 <= m <= k1)%nat))) RPCM Mn)).
unfold R_dist.
unfold Rminus.
rewrite Rplus_assoc.
rewrite H18.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
apply (Rle_trans (RnNorm N (MySumF2 nat (FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= Init.Nat.max k1 k2)%nat) (natSectionFinite 0 (Init.Nat.max k1 k2))) (Complement nat (fun m : nat => (0 <= m <= k1)%nat))) (RnFPCM (Base M1) N) f z)) (MySumF2 nat (FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= Init.Nat.max k1 k2)%nat) (natSectionFinite 0 (Init.Nat.max k1 k2))) (Complement nat (fun m : nat => (0 <= m <= k1)%nat))) RPCM Mn) (Rabs (MySumF2 nat (FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= Init.Nat.max k1 k2)%nat) (natSectionFinite 0 (Init.Nat.max k1 k2))) (Complement nat (fun m : nat => (0 <= m <= k1)%nat))) RPCM Mn))).
suff: (forall (A : {X : Ensemble nat | Finite nat X}), (MySumF2 nat A (RnFPCM (Base M1) N) f z) = (MySumF2 nat A (RnPCM N) (fun (n : nat) => f n z))).
move=> H19.
rewrite H19.
apply (Rle_trans (RnNorm N (MySumF2 nat (FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= Init.Nat.max k1 k2)%nat) (natSectionFinite 0 (Init.Nat.max k1 k2))) (Complement nat (fun m : nat => (0 <= m <= k1)%nat))) (RnPCM N) (fun n : nat => f n z))) (MySumF2 nat (FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= Init.Nat.max k1 k2)%nat) (natSectionFinite 0 (Init.Nat.max k1 k2))) (Complement nat (fun m : nat => (0 <= m <= k1)%nat))) RPCM (fun n : nat => RnNorm N (f n z))) (MySumF2 nat (FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= Init.Nat.max k1 k2)%nat) (natSectionFinite 0 (Init.Nat.max k1 k2))) (Complement nat (fun m : nat => (0 <= m <= k1)%nat))) RPCM Mn)).
apply MySumF2Rntriangle.
apply (FiniteSetInduction nat (FiniteIntersection nat (exist (Finite nat) (fun m : nat => (0 <= m <= Init.Nat.max k1 k2)%nat) (natSectionFinite 0 (Init.Nat.max k1 k2))) (Complement nat (fun m : nat => (0 <= m <= k1)%nat)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply Req_le.
reflexivity.
move=> A0 n H20 H21 H22 H23.
rewrite MySumF2Add.
rewrite MySumF2Add.
apply Rplus_le_compat.
apply H23.
apply H4.
apply H15.
apply H22.
apply H22.
move=> A.
apply (FiniteSetInduction nat A).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> A0 b H19 H20 H21 H22.
rewrite MySumF2Add.
rewrite MySumF2Add.
simpl.
unfold RnFplus.
rewrite H22.
reflexivity.
apply H21.
apply H21.
apply Rle_abs.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> k H18.
elim H18.
move=> kk H19 H20.
apply H19.
move=> k H18.
apply Intersection_intro.
apply H18.
apply conj.
apply (proj1 H18).
apply (le_trans k k1 (max k1 k2)).
apply (proj2 H18).
apply (Nat.le_max_l k1 k2).
apply (H10 (max k1 k2) k1).
apply (Nat.le_max_l k1 k2).
apply (le_n k1).
apply eps2_Rgt_R0.
apply eps2_Rgt_R0.
apply eps2_Rgt_R0.
apply H8.
move=> H14.
apply False_ind.
apply H14.
apply H1.
apply (proj1 H12).
move=> H13.
apply False_ind.
apply (H13 H7).
apply eps2_Rgt_R0.
apply H8.
apply eps2_Rgt_R0.
apply eps2_Rgt_R0.
apply eps2_Rgt_R0.
apply H8.
elim.
simpl.
apply (H2 O x H7).
move=> n H9.
apply Theorem_6_6_3_1_Rn.
apply H9.
apply (H2 (S n) x H7).
move=> x H5.
apply constructive_definite_description.
apply (unique_existence (fun (x0 : Rn N) => Un_cv_met (Rn_met N) (fun n : nat => sum_f_RnF (Base M1) N f n x) x0)).
apply conj.
suff: ((fun n : nat => sum_f_RnF (Base M1) N f n x) = (fun n : nat => sum_f_Rn N (fun (k : nat)=> f k x) n)).
move=> H6.
rewrite H6.
apply Theorem_5_2.
apply (Theorem_5_5_1 (fun m : nat => RnNorm N (f m x)) Mn).
move=> n.
apply (proj1 (RnNormNature N (f n x))).
move=> n.
apply (Rge_trans (Mn n) (RnNorm N (f n x)) 0).
apply (Rle_ge (RnNorm N (f n x)) (Mn n)).
apply (H4 n x H5).
apply (proj1 (RnNormNature N (f n x))).
move=> n.
apply (H4 n x H5).
apply H3.
apply functional_extensionality.
elim.
reflexivity.
move=> n H6.
simpl.
unfold RnFplus.
rewrite H6.
reflexivity.
move=> x0 x1 H6 H7.
apply NNPP.
move=> H8.
suff: ((Rn_dist N x0 x1) > 0).
move=> H9.
elim (H6 ((Rn_dist N x0 x1) / 2)).
move=> n0 H10.
elim (H7 ((Rn_dist N x0 x1) / 2)).
move=> n1 H11.
apply (Rlt_irrefl (Rn_dist N x0 x1)).
apply (Rle_lt_trans (Rn_dist N x0 x1) (dist (Rn_met N) (sum_f_RnF (Base M1) N f (max n0 n1) x) x0 + dist (Rn_met N) (sum_f_RnF (Base M1) N f (max n0 n1) x) x1) (Rn_dist N x0 x1)).
rewrite (dist_sym (Rn_met N) (sum_f_RnF (Base M1) N f (max n0 n1) x) x0).
apply Rn_dist_tri.
rewrite - (eps2 (Rn_dist N x0 x1)).
apply Rplus_lt_compat.
apply (H10 (max n0 n1) (Nat.le_max_l n0 n1)).
apply (H11 (max n0 n1) (Nat.le_max_r n0 n1)).
apply eps2_Rgt_R0.
apply H9.
apply eps2_Rgt_R0.
apply H9.
elim (Rn_dist_pos N x0 x1).
apply.
move=> H11.
apply False_ind.
apply H8.
apply (proj1 (Rn_dist_refl N x0 x1) H11).
Qed.

Definition SequentiallyCompactMet (M : Metric_Space) (A : Ensemble (Base M)) := forall (an : nat -> Base M), (forall (n : nat), A (an n)) -> exists (bn : nat -> Base M), (Subsequence (Base M) bn an /\ exists (b : Base M), (A b) /\ Un_cv_met M bn b).

Lemma SequentiallyCompactMetDef : forall (M : Metric_Space) (A : Ensemble (Base M)), (SequentiallyCompactMet M A) <-> ((forall (an : nat -> Base M), (forall (n : nat), A (an n)) -> exists (bn : nat -> Base M), (Subsequence (Base M) bn an /\ exists (b : Base M), Un_cv_met M bn b)) /\ (forall (an : nat -> Base M), (forall n : nat, A (an n)) -> forall (a : Base M), Un_cv_met M an a -> A a)).
Proof.
move=> M A.
apply conj.
move=> H1.
apply conj.
move=> an H2.
elim (H1 an H2).
move=> bn H3.
exists bn.
apply conj.
apply (proj1 H3).
elim (proj2 H3).
move=> b H4.
exists b.
apply (proj2 H4).
move=> an H2.
move=> a H3.
elim (H1 an H2).
move=> bn H4.
elim (proj2 H4).
move=> b H5.
suff: (a = b).
move=> H6.
rewrite H6.
apply (proj1 H5).
apply (Proposition_2_3_met M bn a b).
move=> eps H6.
elim (H3 eps H6).
move=> m1 H7.
exists m1.
move=> n H8.
elim (proj1 H4).
move=> cn H9.
rewrite (proj2 H9 n).
apply (H7 (cn n)).
apply (le_trans m1 n (cn n)).
apply H8.
apply (Formula_3_17 cn (proj1 H9) n).
apply (proj2 H5).
move=> H1.
move=> an H2.
elim (proj1 H1 an).
move=> bn H3.
exists bn.
apply conj.
apply (proj1 H3).
elim (proj2 H3).
move=> b H4.
exists b.
apply conj.
apply (proj2 H1 bn).
move=> n.
elim (proj1 H3).
move=> cn H5.
rewrite (proj2 H5 n).
apply (H2 (cn n)).
apply H4.
apply H4.
apply H2.
Qed.

Definition ClosedSetMet (M : Metric_Space) (A : Ensemble (Base M)) := A = (ClosureMet M A).

Definition OpenSetMet (M : Metric_Space) (A : Ensemble (Base M)) := forall (a : Base M), (In (Base M) A a) -> exists (eps : R), eps > 0 /\ (Included (Base M) (NeighborhoodMet M a eps) A).

Lemma Proposition_7_1_1 : forall (M : Metric_Space) (A : Ensemble (Base M)), (ClosedSetMet M A) <-> (forall (an : nat -> Base M) (a : Base M), (forall (n : nat), A (an n)) -> (Un_cv_met M an a) -> (A a)).
Proof.
move=> M A.
apply conj.
move=> H1 an a H2 H3.
rewrite H1.
apply (proj2 (Proposition_6_1_1 M A a)).
exists an.
apply conj.
apply H2.
apply H3.
move=> H1.
apply Extensionality_Ensembles.
apply conj.
apply (Proposition_6_1_2 M A).
move=> a H2.
elim (proj1 (Proposition_6_1_1 M A a) H2).
move=> an H3.
apply (H1 an a).
apply (proj1 H3).
apply (proj2 H3).
Qed.

Lemma Proposition_7_1_2 : forall (M : Metric_Space) (A : Ensemble (Base M)), (ClosedSetMet M A) <-> (OpenSetMet M (Ensembles.Complement (Base M) A)).
Proof.
move=> M A.
apply conj.
move=> H1 a H2.
apply NNPP.
move=> H3.
apply H2.
rewrite H1.
move=> eps H4.
apply NNPP.
move=> H5.
apply H3.
exists eps.
apply conj.
apply H4.
move=> z H6 H7.
apply H5.
exists z.
apply conj.
apply H6.
apply H7.
move=> H1.
apply Extensionality_Ensembles.
apply conj.
apply (Proposition_6_1_2 M A).
move=> a H2.
apply NNPP.
move=> H3.
elim (H1 a H3).
move=> eps H4.
elim (H2 eps (proj1 H4)).
move=> x H5.
apply (proj2 H4 x).
apply (proj1 H5).
apply (proj2 H5).
Qed.

Definition TotallyBoundedMet (M : Metric_Space) (A : Ensemble (Base M)) := (forall (an : nat -> Base M), (forall (n : nat), A (an n)) -> exists (bn : nat -> Base M), (Subsequence (Base M) bn an /\ exists (b : Base M), Un_cv_met M bn b)).

Lemma Theorem_7_2_1_1 : forall (M : Metric_Space) (A : Ensemble (Base M)) (m : Base M), (TotallyBoundedMet M A) -> (BoundedMet M A).
Proof.
move=> M A x H1.
exists x.
apply NNPP.
move=> H2.
suff: (exists (f : nat -> Base M), forall (n : nat), (In (Base M) A (f n)) /\ dist M x (f n) > INR n).
elim.
move=> an H3.
elim (H1 an).
move=> bn H4.
elim (proj2 H4).
move=> b H5.
elim (H5 1 Rlt_0_1).
move=> k1 H6.
elim (Formula_3_7 (dist M x b + 1)).
move=> k2 H7.
apply (Rlt_not_le 1 (dist M (bn (max k1 k2)) b) (H6 (max k1 k2) (Nat.le_max_l k1 k2))).
rewrite (dist_sym M (bn (max k1 k2)) b).
apply (Rplus_le_reg_l (dist M x b) 1 (dist M b (bn (max k1 k2)))).
apply (Rle_trans (dist M x b + 1) (dist M x (bn (max k1 k2))) (dist M x b + dist M b (bn (Init.Nat.max k1 k2)))).
elim (proj1 H4).
move=> cn H8.
apply (Rle_trans (dist M x b + 1) (INR (cn (max k1 k2)))).
apply (Rlt_le (dist M x b + 1) (INR (cn (max k1 k2)))).
apply (H7 (cn (max k1 k2))).
apply (le_trans k2 (max k1 k2) (cn (max k1 k2))).
apply (Nat.le_max_r k1 k2).
apply (Formula_3_17 cn (proj1 H8) (max k1 k2)).
apply (Rlt_le (INR (cn (max k1 k2))) (dist M x (bn (max k1 k2)))).
rewrite (proj2 H8 (max k1 k2)).
apply (proj2 (H3 (cn (max k1 k2)))).
apply (dist_tri M x (bn (Init.Nat.max k1 k2)) b).
move=> n.
apply (proj1 (H3 n)).
apply (functional_choice (fun (n : nat) (m : Base M) => In (Base M) A m /\ dist M x m > INR n)).
move=> n.
apply NNPP.
move=> H3.
apply H2.
exists (INR n + 1).
move=> y H4.
apply NNPP.
move=> H5.
apply H3.
exists y.
apply conj.
apply H4.
apply (Rlt_le_trans (INR n) (INR n + 1) (dist M x y)).
apply (Rlt_plus_1 (INR n)).
apply (Rnot_lt_le (dist M x y) (INR n + 1)).
move=> H6.
apply H5.
unfold NeighborhoodMet.
unfold In.
rewrite (dist_sym M y x).
apply H6.
Qed.

Lemma Theorem_7_2_1_2 : forall (N : nat) (A : Ensemble (Rn N)), (BoundedMet (Rn_met N) A) -> (TotallyBoundedMet (Rn_met N) A).
Proof.
move=> N A H1.
move=> an H2.
suff: (forall (n0 : {n : nat | (n < N)%nat}), my_bounded (Im nat R (Full_set nat) (fun (m : nat) => an m n0))).
move=> H3.
suff: (forall (k : nat), (k <= N)%nat -> exists (bn : nat -> Rn N), Subsequence (Base (Rn_met N)) bn an /\ (forall (n0 : {n : nat | (n < N)%nat}), (proj1_sig n0 < k)%nat -> (exists (b : R), Un_cv (fun (m : nat) => bn m n0) b))).
move=> H4.
elim (H4 N).
move=> bn H5.
exists bn.
apply conj.
apply (proj1 H5).
suff: (exists (b : {n : nat | (n < N)%nat} -> R), forall (n0 : {n : nat | (n < N)%nat}), Un_cv (fun m : nat => bn m n0) (b n0)).
elim.
move=> b H6.
exists b.
apply (proj2 (Theorem_4_5_1 N bn b)).
apply H6.
apply (functional_choice (fun (n0 : {n : nat | (n < N)%nat}) (b : R) => Un_cv (fun m : nat => bn m n0) b)).
move=> n0.
apply (proj2 H5 n0).
apply (proj2_sig n0).
apply (le_n N).
elim.
move=> H4.
exists an.
apply conj.
exists (fun (n : nat) => n).
apply conj.
move=> n.
apply (le_n (S n)).
move=> n.
reflexivity.
move=> n0 H5.
apply False_ind.
apply (lt_not_le (proj1_sig n0) 0).
apply H5.
apply (le_0_n (proj1_sig n0)).
move=> k H4 H5.
elim H4.
move=> bn H6.
suff: (k < N)%nat.
move=> H7.
elim (Theorem_3_4 (fun (n0 : nat) => bn n0 (exist (fun (n : nat) => (n < N)%nat) k H7))).
move=> bn2 H8.
elim H8.
move=> H9 H10.
elim H9.
move=> cn H11.
exists (fun (n : nat) => bn (cn n)).
apply conj.
elim (proj1 H6).
move=> dn H12.
exists (fun (n : nat) => (dn (cn n))).
apply conj.
suff: (forall (n m : nat), (n < m)%nat -> ((dn n) < (dn m))%nat).
move=> H13.
move=> n.
apply (H13 (cn n) (cn (S n))).
apply (proj1 H11).
move=> n m.
elim.
apply (proj1 H12 n).
move=> m0 H13 H14.
apply (lt_trans (dn n) (dn m0) (dn (S m0))).
apply H14.
apply (proj1 H12 m0).
move=> n.
apply (proj2 H12 (cn n)).
move=> n0 H12.
elim (classic (proj1_sig n0 < k)%nat).
move=> H13.
elim (proj2 H6 n0 H13).
move=> b H14.
exists b.
apply (Formula_3_18 (fun m : nat => bn (cn m) n0) (fun m : nat => bn m n0)).
exists cn.
apply conj.
apply (proj1 H11).
move=> n.
reflexivity.
apply H14.
move=> H13.
elim (le_lt_or_eq (proj1_sig n0) k).
move=> H14.
apply False_ind.
apply H13.
apply H14.
move=> H14.
elim (proj2 H8).
move=> b H15.
exists b.
suff: ((fun m : nat => bn (cn m) n0) = bn2).
move=> H16.
rewrite H16.
apply H15.
apply functional_extensionality.
move=> n.
suff: (n0 = (exist (fun n0 : nat => (n0 < N)%nat) k H7)).
move=> H16.
rewrite H16.
rewrite (proj2 H11 n).
reflexivity.
apply sig_map.
apply H14.
apply (le_S_n (proj1_sig n0) k H12).
elim (H3 (exist (fun n : nat => (n < N)%nat) k H7)).
move=> H8 H9.
elim (proj1 H6).
move=> cn H10.
apply conj.
elim H8.
move=> m H11.
exists m.
move=> x H12.
elim H12.
move=> n H13 y H14.
rewrite H14.
rewrite (proj2 H10 n).
apply (H11 (an (cn n) (exist (fun n0 : nat => (n0 < N)%nat) k H7))).
apply (Im_intro nat R (Full_set nat) (fun m0 : nat => an m0 (exist (fun n0 : nat => (n0 < N)%nat) k H7)) (cn n)).
apply (Full_intro nat (cn n)).
reflexivity.
elim H9.
move=> m H11.
exists m.
move=> x H12.
elim H12.
move=> n H13 y H14.
rewrite H14.
rewrite (proj2 H10 n).
apply (H11 (an (cn n) (exist (fun n0 : nat => (n0 < N)%nat) k H7))).
apply (Im_intro nat R (Full_set nat) (fun m0 : nat => an m0 (exist (fun n0 : nat => (n0 < N)%nat) k H7)) (cn n)).
apply (Full_intro nat (cn n)).
reflexivity.
apply H5.
apply (le_trans k (S k) N).
apply (le_S k k (le_n k)).
apply H5.
move=> n0.
elim (BoundedMetDef2 (Rn_met N) A H1 (RnO N)).
move=> M H3.
apply (proj2 (bounded_abs (Im nat R (Full_set nat) (fun m : nat => an m n0)))).
exists M.
move=> x H4.
elim H4.
move=> x0 H5 y H6.
rewrite H6.
elim H5.
move=> n H7 z H8.
rewrite H8.
apply (Rle_trans (Rabs (an n n0)) (RnNorm N (an n)) M).
apply (Rnot_lt_le (RnNorm N (an n)) (Rabs (an n n0))).
move=> H9.
apply (Rle_not_lt (RnInnerProduct N (an n) (an n)) (Rabs (an n n0) * Rabs (an n n0))).
rewrite (RnInnerProductDefinition N (an n) (an n)).
rewrite (MySumF2Excluded (Count N) RPCM (fun n1 : Count N => an n n1 * an n n1) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Singleton (Count N) n0)).
simpl.
suff: ((FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Singleton (Count N) n0)) = (exist (Finite (Count N)) (Singleton (Count N) n0) (Singleton_is_finite (Count N) n0))).
move=> H10.
rewrite H10.
rewrite MySumF2Singleton.
suff: (Rabs (an n n0) * Rabs (an n n0) = an n n0 * an n n0).
move=> H11.
rewrite - (Rplus_0_r (Rabs (an n n0) * Rabs (an n n0))).
rewrite H11.
apply (Rplus_le_compat_l (an n n0 * an n n0) 0).
apply MySumF2Induction.
apply conj.
apply (Req_le 0 0).
reflexivity.
move=> r1 r2 H12 H13.
simpl.
rewrite - (Rplus_0_r 0).
apply (Rplus_le_compat 0 r1 0 (an n r2 * an n r2)).
apply H13.
apply Rge_le.
apply (Formula_1_3_2 (an n r2)).
unfold Rabs.
elim (Rcase_abs (an n n0)).
move=> H11.
apply Rmult_opp_opp.
move=> H11.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> n1.
elim.
move=> n2 H10 H11.
apply H10.
move=> n1 H10.
apply Intersection_intro.
apply H10.
apply Full_intro.
rewrite (proj2 (RnNormNature N (an n))).
apply Rmult_le_0_lt_compat.
apply Rge_le.
apply (proj1 (RnNormNature N (an n))).
apply Rge_le.
apply (proj1 (RnNormNature N (an n))).
apply H9.
apply H9.
suff: (RnNorm N (an n) = Rn_dist N (an n) (RnO N)).
move=> H9.
rewrite H9.
apply Rlt_le.
apply (H3 (an n)).
apply (H2 n).
unfold Rn_dist.
unfold Rnminus.
suff: ((Rnopp N (RnO N)) = (Vopp Rfield (RnVS N) (VO Rfield (RnVS N)))).
move=> H9.
rewrite H9.
rewrite (Vopp_O Rfield (RnVS N)).
suff: ((Rnplus N (an n) (VO Rfield (RnVS N))) = (Vadd Rfield (RnVS N) (an n) (VO Rfield (RnVS N)))).
move=> H10.
rewrite H10.
rewrite (Vadd_O_r Rfield (RnVS N) (an n)).
reflexivity.
reflexivity.
reflexivity.
Qed.

Lemma Theorem_7_2_1_2_R : forall (A : Ensemble R), (BoundedMet R_met A) -> (TotallyBoundedMet R_met A).
Proof.
move=> A H1 an H2.
apply (Theorem_3_4 an).
elim (BoundedMetDef2 R_met A H1 0).
move=> M H3.
apply (proj2 (bounded_abs (Im nat R (Full_set nat) an))).
exists M.
move=> x.
elim.
move=> x0 H4 y H5.
rewrite H5.
elim H4.
move=> n H6 y0 H7.
rewrite H7.
rewrite - (Rplus_0_r (an n)).
rewrite - Ropp_0.
left.
apply (H3 (an n)).
apply (H2 n).
Qed.

Lemma Theorem_7_2_2_1 : forall (M : Metric_Space) (A : Ensemble (Base M)) (m : Base M), (SequentiallyCompactMet M A) -> (BoundedMet M A /\ ClosedSetMet M A).
Proof.
move=> M A m H1.
apply conj.
apply (Theorem_7_2_1_1 M A m).
unfold TotallyBoundedMet.
apply (proj1 (proj1 (SequentiallyCompactMetDef M A) H1)).
apply Extensionality_Ensembles.
apply conj.
apply (Proposition_6_1_2 M A).
move=> a H2.
elim (proj1 (Proposition_6_1_1 M A a) H2).
move=> an H3.
apply (proj2 (proj1 (SequentiallyCompactMetDef M A) H1) an (proj1 H3) a (proj2 H3)).
Qed.

Lemma Theorem_7_2_2_2 : forall (N : nat) (A : Ensemble (Rn N)), (BoundedMet (Rn_met N) A /\ ClosedSetMet (Rn_met N) A) -> (SequentiallyCompactMet (Rn_met N) A).
Proof.
move=> N A H1.
apply (proj2 (SequentiallyCompactMetDef (Rn_met N) A)).
apply conj.
apply (Theorem_7_2_1_2 N A (proj1 H1)).
move=> an H2 a H3.
rewrite (proj2 H1).
apply (proj2 (Proposition_6_1_1 (Rn_met N) A a)).
exists an.
apply conj.
apply H2.
apply H3.
Qed.

Lemma Theorem_7_2_2_2_R : forall (A : Ensemble R), (BoundedMet R_met A /\ ClosedSetMet R_met A) -> (SequentiallyCompactMet R_met A).
Proof.
move=> A H1.
apply (proj2 (SequentiallyCompactMetDef R_met A)).
apply conj.
apply (Theorem_7_2_1_2_R A (proj1 H1)).
move=> an H2 a H3.
rewrite (proj2 H1).
apply (proj2 (Proposition_6_1_1 R_met A a)).
exists an.
apply conj.
apply H2.
apply H3.
Qed.

Lemma Theorem_7_3_1_1 : forall (M1 M2 : Metric_Space) (f : Base M1 -> Base M2) (A : Ensemble (Base M1)), (forall (a : (Base M1)), (In (Base M1) A a) -> (ContinuousMet M1 M2 f (Full_set (Base M1)) a)) -> SequentiallyCompactMet M1 A -> SequentiallyCompactMet M2 (Im (Base M1) (Base M2) A f).
Proof.
move=> M1 M2 f A H1 H2.
move=> fan H3.
suff: (exists (an : nat -> Base M1), forall (n : nat), (In (Base M1) A (an n)) /\ (fan n) = f (an n)).
elim.
move=> an H4.
elim (H2 an).
move=> bn H5.
exists (fun (n : nat) => f (bn n)).
apply conj.
elim (proj1 H5).
move=> cn H6.
exists cn.
apply conj.
apply (proj1 H6).
move=> n.
rewrite (proj2 H6 n).
rewrite (proj2 (H4 (cn n))).
reflexivity.
elim (proj2 H5).
move=> b H6.
exists (f b).
apply conj.
apply (Im_intro (Base M1) (Base M2) A f b).
apply (proj1 H6).
reflexivity.
apply (proj1 (Theorem_6_2 M1 M2 f (Full_set (Base M1)) b (f b)) (H1 b (proj1 H6)) (fun (n : nat) => (exist (Full_set (Base M1)) (bn n) (Full_intro (Base M1) (bn n))))).
apply (proj2 H6).
move=> n.
apply (proj1 (H4 n)).
apply (functional_choice (fun (n : nat) (x : Base M1) => In (Base M1) A x /\ fan n = f x)).
move=> n.
elim (H3 n).
move=> m H4 y H5.
exists m.
apply conj.
apply H4.
apply H5.
Qed.

Lemma Theorem_7_3_1_2 : forall (M1 M2 : Metric_Space) (f : Base M1 -> Base M2) (A : Ensemble (Base M1)) (m : Base M2), (forall (a : (Base M1)), (In (Base M1) A a) -> (ContinuousMet M1 M2 f (Full_set (Base M1)) a)) -> SequentiallyCompactMet M1 A -> BoundedMet M2 (Im (Base M1) (Base M2) A f).
Proof.
move=> M1 M2 f A m H1 H2.
apply (Theorem_7_2_2_1 M2 (Im (Base M1) (Base M2) A f) m).
apply (Theorem_7_3_1_1 M1 M2 f A H1 H2).
Qed.

Lemma Theorem_7_3_2_1 : forall (M : Metric_Space) (f : Base M -> R) (A : Ensemble (Base M)), (Inhabited (Base M) A) -> (forall (a : (Base M)), (In (Base M) A a) -> (ContinuousMet M R_met f (Full_set (Base M)) a)) -> SequentiallyCompactMet M A -> exists (m : R), is_max (Im (Base M) R A f) m.
Proof.
move=> M f A H1 H2 H3.
suff: (BoundedMet R_met (Im (Base M) R A f) /\ ClosedSetMet R_met (Im (Base M) R A f)).
move=> H4.
elim (BoundedMetDef2 R_met (Im (Base M) R A f) (proj1 H4) 0).
move=> K H5.
elim (My_completeness_of_upper (Im (Base M) R A f)).
move=> m H6.
exists m.
apply conj.
rewrite (proj2 H4).
move=> eps H7.
elim (proj2 (proj2 ((proj1 Proposition_1_3) (Im (Base M) R A f) m) H6) (m - eps)).
move=> x H8.
exists x.
apply conj.
unfold NeighborhoodMet.
unfold R_met.
unfold dist.
unfold R_dist.
rewrite (Rabs_minus_sym x m).
rewrite (Rabs_right (m - x)).
apply (Rplus_lt_reg_r x (m - x) eps).
rewrite (Rplus_assoc m (- x) x).
rewrite (Rplus_opp_l x).
rewrite (Rplus_comm eps x).
rewrite - (Rplus_opp_l eps).
rewrite - (Rplus_assoc m (- eps) eps).
apply (Rplus_lt_compat_r eps (m - eps) x (proj2 H8)).
apply (Rge_minus m x).
apply (Rle_ge x m).
apply (proj1 H6 x (proj1 H8)).
apply (proj1 H8).
rewrite - {2} (Rplus_0_r m).
apply (Rplus_lt_compat_l m (- eps) 0).
apply (Ropp_lt_gt_0_contravar eps H7).
move=> x H7.
apply (proj1 H6 x H7).
apply conj.
elim H1.
move=> a H6.
exists (f a).
apply (Im_intro (Base M) R A f a H6).
reflexivity.
elim (proj1 H4).
move=> x.
elim.
move=> m H6.
exists (x + m).
move=> y H7.
rewrite - (Rplus_0_r y).
rewrite - (Rplus_opp_l x).
rewrite - (Rplus_assoc y (- x) x).
rewrite (Rplus_comm x m).
apply (Rplus_le_compat_r x (y - x) m).
apply (Rle_trans (y - x) (Rabs (y - x)) m).
apply (Rle_abs (y - x)).
apply (Rlt_le (Rabs (y - x)) m).
apply (H6 y H7).
apply (Theorem_7_2_2_1 R_met (Im (Base M) R A f)).
apply 0.
apply (Theorem_7_3_1_1 M R_met f A H2 H3).
Qed.

Lemma Theorem_7_3_2_2 : forall (M : Metric_Space) (f : Base M -> R) (A : Ensemble (Base M)), (Inhabited (Base M) A) -> (forall (a : (Base M)), (In (Base M) A a) -> (ContinuousMet M R_met f (Full_set (Base M)) a)) -> SequentiallyCompactMet M A -> exists (m : R), is_min (Im (Base M) R A f) m.
Proof.
move=> M f A H1 H2 H3.
suff: (exists m : R, is_max (Im (Base M) R A (fun (x : Base M) => - (f x))) m).
elim.
move=> m H4.
exists (- m).
apply conj.
elim (proj1 H4).
move=> x H5 y H6.
apply (Im_intro (Base M) R A f x).
apply H5.
rewrite H6.
apply (Ropp_involutive (f x)).
move=> y.
elim.
move=> x H5 z H6.
rewrite H6.
apply (Ropp_ge_cancel (f x) (- m)).
rewrite (Ropp_involutive m).
apply (Rle_ge (- f x) m).
apply (proj2 H4 (- f x)).
apply (Im_intro (Base M) R A (fun x0 : Base M => - f x0) x).
apply H5.
reflexivity.
apply (Theorem_7_3_2_1 M (fun x : Base M => - f x) A H1).
move=> a H4.
apply (Theorem_6_6_3_4_R M f (Full_set (Base M)) a).
apply (H2 a H4).
apply H3.
Qed.

Definition CompactMet (M : Metric_Space) (A : Ensemble (Base M)) := forall (T : Type) (Ai : T -> (Ensemble (Base M))), (forall (t : T), OpenSetMet M (Ai t)) -> (Included (Base M) A (fun (x : Base M) => exists (t : T), In (Base M) (Ai t) x)) -> exists (tt : Ensemble T), (Finite T tt) /\ (Included (Base M) A (fun (x : Base M) => exists (t : T), (In T tt t) /\ In (Base M) (Ai t) x)).

Lemma Theorem_7_4_1 : forall (M : Metric_Space) (A : Ensemble (Base M)) (x : Base M), (CompactMet M A) -> (BoundedMet M A /\ ClosedSetMet M A).
Proof.
move=> M A x H1.
apply conj.
elim (H1 nat (fun (n : nat) => NeighborhoodMet M x (INR (S n)))).
move=> ns H2.
elim (classic (Inhabited nat ns)).
move=> H3.
elim (Finite_max_nat ns).
move=> m H4.
exists x.
exists (INR (S m)).
move=> a H5.
elim (proj2 H2 a H5).
move=> n1 H6.
apply (Rlt_le_trans (dist M a x) (INR (S n1)) (INR (S m))).
apply (proj2 H6).
apply (le_INR (S n1) (S m)).
apply (le_n_S n1 m (proj2 H4 n1 (proj1 H6))).
apply (proj1 H2).
apply H3.
move=> H3.
exists x.
exists 1.
move=> a H4.
apply False_ind.
apply H3.
elim (proj2 H2 a H4).
move=> n H5.
apply (Inhabited_intro nat ns n (proj1 H5)).
move=> t m H2.
exists (INR (S t) - (dist M m x)).
apply conj.
apply (Rgt_minus (INR (S t)) (dist M m x)).
apply H2.
move=> m0 H3.
apply (Rle_lt_trans (dist M m0 x) (dist M m0 m + dist M m x) (INR (S t))).
apply (dist_tri M m0 x m).
apply (Rplus_lt_reg_r (- dist M m x) (dist M m0 m + dist M m x) (INR (S t))).
rewrite (Rplus_assoc (dist M m0 m) (dist M m x) (- dist M m x)).
rewrite (Rplus_opp_r (dist M m x)).
rewrite (Rplus_0_r (dist M m0 m)).
apply H3.
move=> a H2.
elim (Formula_3_7 (dist M a x)).
move=> n H3.
exists n.
apply (H3 (S n)).
apply (le_S n n (le_n n)).
apply Extensionality_Ensembles.
apply conj.
apply (Proposition_6_1_2 M A).
move=> a H2.
apply NNPP.
move=> H3.
elim (H1 nat (fun (n : nat) (x : Base M) => dist M x a > 1 / (INR (S n)))).
move=> ns H4.
elim (classic (Inhabited nat ns)).
move=> H5.
elim (Finite_max_nat ns).
move=> m H6.
elim (H2 (1 / (INR (S m)))).
move=> y H7.
elim (proj2 H4 y (proj2 H7)).
move=> n H8.
apply (Rlt_not_le (dist M y a) (1 / INR (S m))).
apply (Rle_lt_trans (1 / INR (S m)) (1 / INR (S n)) (dist M y a)).
elim (le_INR (S n) (S m) (le_n_S n m (proj2 H6 n (proj1 H8)))).
move=> H9.
left.
unfold Rdiv.
rewrite (Rmult_1_l (/ (INR (S m)))).
rewrite (Rmult_1_l (/ (INR (S n)))).
apply (Rinv_lt_contravar (INR (S n)) (INR (S m))).
apply (Rmult_lt_0_compat (INR (S n)) (INR (S m))).
apply (lt_0_INR (S n)).
apply (le_n_S O n (le_0_n n)).
apply (lt_0_INR (S m)).
apply (le_n_S O m (le_0_n m)).
apply H9.
move=> H9.
rewrite H9.
right.
reflexivity.
apply (proj2 H8).
apply (Rlt_le (dist M y a) (1 / INR (S m))).
apply (proj1 H7).
unfold Rdiv.
rewrite (Rmult_1_l (/ INR (S m))).
apply (Rinv_0_lt_compat (INR (S m))).
apply (lt_0_INR (S m)).
apply (le_n_S O m (le_0_n m)).
apply (proj1 H4).
apply H5.
move=> H5.
apply H5.
elim (H2 1 Rlt_0_1).
move=> a0 H6.
elim (proj2 H4 a0 (proj2 H6)).
move=> n H7.
apply (Inhabited_intro nat ns n (proj1 H7)).
move=> n m H4.
exists (dist M m a - (1 / INR (S n))).
apply conj.
apply (Rgt_minus (dist M m a) (1 / INR (S n))).
apply H4.
move=> y H5.
apply (Rlt_le_trans (1 / INR (S n)) (dist M m a - dist M m y) (dist M y a)).
apply (Rplus_lt_reg_r (dist M m y) (1 / INR (S n)) (dist M m a - dist M m y)).
rewrite (Rplus_assoc (dist M m a) (- dist M m y) (dist M m y)).
rewrite (Rplus_opp_l (dist M m y)).
rewrite (Rplus_comm (1 / INR (S n)) (dist M m y)).
rewrite - (Rplus_opp_l (1 / INR (S n))).
rewrite - (Rplus_assoc (dist M m a) (- (1 / INR (S n))) (1 / INR (S n))).
apply (Rplus_lt_compat_r (1 / INR (S n)) (dist M m y) (dist M m a + - (1 / INR (S n)))).
rewrite (dist_sym M m y).
apply H5.
apply (Rplus_le_reg_r (dist M m y) (dist M m a - dist M m y) (dist M y a)).
rewrite (Rplus_assoc (dist M m a) (- dist M m y) (dist M m y)).
rewrite (Rplus_opp_l (dist M m y)).
rewrite (Rplus_0_r (dist M m a)).
rewrite (Rplus_comm (dist M y a) (dist M m y)).
apply (dist_tri M m a y).
move=> a0 H4.
elim (dist_pos M a0 a).
move=> H5.
elim (Formula_3_8 (dist M a0 a) H5).
move=> n H6.
exists n.
suff: (1 / INR (S n) = R_dist (1 / INR (S n)) 0).
move=> H7.
rewrite H7.
apply (H6 (S n)).
apply (le_S n n (le_n n)).
unfold R_dist.
unfold Rminus.
rewrite Ropp_0.
rewrite (Rplus_0_r (1 / INR (S n))).
rewrite (Rabs_right (1 / INR (S n))).
reflexivity.
apply (Rgt_ge (1 / INR (S n)) 0).
unfold Rdiv.
rewrite (Rmult_1_l (/ INR (S n))).
apply (Rinv_0_lt_compat (INR (S n))).
apply (lt_0_INR (S n)).
apply (le_n_S O n (le_0_n n)).
move=> H5.
apply False_ind.
apply H3.
rewrite - (proj1 (dist_refl M a0 a) H5).
apply H4.
Qed.

Lemma Theorem_7_4_2 : forall (N : nat) (A : Ensemble (Rn N)), ((BoundedMet (Rn_met N) A) /\ (ClosedSetMet (Rn_met N) A)) -> (CompactMet (Rn_met N) A).
Proof.
move=> N A H1.
move=> T X H2 H3.
apply NNPP.
move=> H4.
suff: (let infiniteCoverTemp := (fun (A0 : (Ensemble (Rn N))) => ~ exists (tt : Ensemble T), Finite T tt /\ Included (Base (Rn_met N)) (Intersection (Rn N) A0 A) (fun x : Base (Rn_met N) => exists t : T, In T tt t /\ In (Base (Rn_met N)) (X t) x)) in False).
apply.
move=> infiniteCoverTemp.
suff: (exists (D : nat -> {n : nat | (n < N)%nat} -> BoundedClosedSectionSet), (forall (n : nat), infiniteCoverTemp (fun (x : Rn N) => forall (m : {n : nat | (n < N)%nat}), In R (proj1_sig (D n m)) (x m))) /\ (forall (m : {n : nat | (n < N)%nat}), Un_cv (fun (n : nat) => BoundedClosedSectionToR (D n m) - BoundedClosedSectionToL (D n m)) 0) /\ (forall (m : {n : nat | (n < N)%nat}) (n : nat), Included R (proj1_sig (D (S n) m)) (proj1_sig (D n m)))).
elim.
move=> D H5.
suff: (forall (m : {n : nat | (n < N)%nat}), {r : R | forall (n : nat), In R (proj1_sig (D n m)) r}).
move=> H6.
suff: (let x := (fun (m : {n : nat | (n < N)%nat}) => proj1_sig (H6 m)) in False).
apply.
move=> x.
suff: (forall (eps : R), eps > 0 -> exists (n : nat), Included (Rn N) (fun (x : Rn N) => forall (m : {n : nat | (n < N)%nat}), In R (proj1_sig (D n m)) (x m)) (NeighborhoodMet (Rn_met N) x eps)).
move=> H7.
suff: (In (Rn N) A x).
move=> H8.
elim (H3 x H8).
move=> t H9.
elim (H2 t x).
move=> eps H10.
elim (H7 eps (proj1 H10)).
move=> n H11.
apply (proj1 H5 n).
exists (Singleton T t).
apply conj.
apply (Singleton_is_finite T t).
move=> y H12.
exists t.
apply conj.
apply (Singleton_intro T t).
reflexivity.
apply (proj2 H10 y).
apply (H11 y).
elim H12.
move=> y0 H13 H14.
apply H13.
apply H9.
rewrite (proj2 H1).
move=> eps H8.
elim (H7 eps H8).
move=> n H9.
apply NNPP.
move=> H10.
apply (proj1 H5 n).
exists (Empty_set T).
apply conj.
apply (Empty_is_finite T).
move=> z H11.
apply False_ind.
apply H10.
exists z.
elim H11.
move=> z0 H12 H13.
apply conj.
apply (H9 z0 H12).
apply H13.
move=> eps H7.
suff: (forall (k : nat), (k <= N)%nat -> (forall (eps : R), eps > 0 -> exists (n1 : nat), forall (n : nat), (n >= n1)%nat -> (forall (y : Rn N), (In (Rn N) (fun x0 : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (D n m)) (x0 m)) y) -> (my_sum_f_R (fun n : nat => UnwrapRn N (Rnminus N y x) n * UnwrapRn N (Rnminus N y x) n) k) < eps))).
move=> H8.
elim (H8 N (le_n N) (eps * eps)).
move=> n1 H9.
exists n1.
move=> y H10.
apply (Rnot_le_lt eps (dist (Rn_met N) y x)).
move=> H11.
apply (Rlt_not_le (eps * eps) ((dist (Rn_met N) y x) * (dist (Rn_met N) y x))).
unfold Rn_met.
unfold dist.
unfold Rn_dist.
unfold RnNorm.
rewrite - (proj2 (MySqrtNature (exist (fun r : R => r >= 0) (RnInnerProduct N (Rnminus N y x) (Rnminus N y x)) (Proposition_4_2_4_1 N (Rnminus N y x))))).
apply (H9 n1).
apply (le_n n1).
apply H10.
apply (Rmult_le_compat eps (dist (Rn_met N) y x) eps (dist (Rn_met N) y x)).
apply (Rlt_le 0 eps H7).
apply (Rlt_le 0 eps H7).
apply H11.
apply H11.
apply (Rmult_gt_0_compat eps eps H7 H7).
elim.
move=> H8 eps0 H9.
exists O.
move=> n H10 y H11.
apply H9.
move=> n H8 H9 eps0 H10.
suff: (n <= N)%nat.
move=> H11.
elim (H8 H11 (eps0 / 2)).
move=> n0 H12.
elim (proj1 (proj2 H5) (exist (fun (m : nat) => (m < N)%nat) n H9) (Rmin (eps0 / 2) 1)).
move=> n1 H13.
exists (max n0 n1).
move=> n2 H14 y H15.
simpl.
rewrite - (eps2 eps0).
apply (Rplus_lt_compat (my_sum_f_R (fun n3 : nat => UnwrapRn N (Rnminus N y x) n3 * UnwrapRn N (Rnminus N y x) n3) n) (eps0 * / 2) (UnwrapRn N (Rnminus N y x) n * UnwrapRn N (Rnminus N y x) n) (eps0 * / 2)).
apply (H12 n2).
apply (le_trans n0 (max n0 n1) n2).
apply (Nat.le_max_l n0 n1).
apply H14.
apply H15.
unfold UnwrapRn.
elim (excluded_middle_informative (n < N)%nat).
move=> H16.
unfold Rnminus.
unfold Rnplus.
unfold Rnopp.
suff: (Rabs (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16)) < (Rmin (eps0 / 2) 1)).
move=> H17.
suff: ((y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16)) * (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16)) = Rabs (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16)) * Rabs (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16))).
move=> H18.
rewrite H18.
rewrite - (Rmult_1_r (eps0 * / 2)).
apply (Rmult_le_0_lt_compat (Rabs (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16))) (eps0 * / 2) (Rabs (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16))) 1).
apply (Rabs_pos (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16))).
apply (Rabs_pos (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16))).
apply (Rlt_le_trans (Rabs (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16))) (Rmin (eps0 */ 2) 1) (eps0 * / 2)).
apply H17.
apply (Rmin_l (eps0 * / 2) 1).
apply (Rlt_le_trans (Rabs (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16))) (Rmin (eps0 */ 2) 1) 1).
apply H17.
apply (Rmin_r (eps0 * / 2) 1).
unfold Rabs.
elim (Rcase_abs (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16))).
move=> H18.
rewrite (Rmult_opp_opp (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16)) (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16))).
reflexivity.
reflexivity.
suff: (forall (x y : Rn N), In (Rn N) (fun x0 : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (D n2 m)) (x0 m)) x -> In (Rn N) (fun x0 : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (D n2 m)) (x0 m)) y -> (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16)) < 
Rmin (eps0 / 2) 1).
move=> H17.
unfold Rabs.
elim (Rcase_abs (y (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x (exist (fun n3 : nat => (n3 < N)%nat) n H16))).
move=> H19.
rewrite (Ropp_minus_distr (y (exist (fun n3 : nat => (n3 < N)%nat) n H16)) (x (exist (fun n3 : nat => (n3 < N)%nat) n H16))).
apply (H17 y x).
apply H15.
move=> m.
apply (proj2_sig (H6 m)).
move=> H18.
apply (H17 x y).
move=> m.
apply (proj2_sig (H6 m)).
apply H15.
move=> x0 y0 H17 H18.
apply (Rle_lt_trans (y0 (exist (fun n3 : nat => (n3 < N)%nat) n H16) + - x0 (exist (fun n3 : nat => (n3 < N)%nat) n H16)) ((BoundedClosedSectionToR (D n2 (exist (fun m : nat => (m < N)%nat) n H9)) - BoundedClosedSectionToL (D n2 (exist (fun m : nat => (m < N)%nat) n H9)))) (Rmin (eps0 / 2) 1)).
apply (Rplus_le_compat (y0 (exist (fun n3 : nat => (n3 < N)%nat) n H16)) (BoundedClosedSectionToR (D n2 (exist (fun m : nat => (m < N)%nat) n H9))) (- x0 (exist (fun n3 : nat => (n3 < N)%nat) n H16)) (- BoundedClosedSectionToL (D n2 (exist (fun m : nat => (m < N)%nat) n H9)))).
suff: ((exist (fun m : nat => (m < N)%nat) n H9) = (exist (fun n3 : nat => (n3 < N)%nat) n H16)).
move=> H19.
rewrite H19.
suff: (In R (BoundedClosedSection (BoundedClosedSectionToPair (D n2 (exist (fun n3 : nat => (n3 < N)%nat) n H16)))) (y0 (exist (fun n3 : nat => (n3 < N)%nat) n H16))).
elim.
move=> y1 H20 H21.
apply H21.
rewrite - (BoundedClosedSectionEqual (D n2 (exist (fun n3 : nat => (n3 < N)%nat) n H16))).
apply (H18 (exist (fun n3 : nat => (n3 < N)%nat) n H16)).
apply sig_map.
reflexivity.
apply (Ropp_le_contravar (x0 (exist (fun n3 : nat => (n3 < N)%nat) n H16)) (BoundedClosedSectionToL (D n2 (exist (fun m : nat => (m < N)%nat) n H9)))).
suff: ((exist (fun m : nat => (m < N)%nat) n H9) = (exist (fun n3 : nat => (n3 < N)%nat) n H16)).
move=> H19.
rewrite H19.
suff: (In R (BoundedClosedSection (BoundedClosedSectionToPair (D n2 (exist (fun n3 : nat => (n3 < N)%nat) n H16)))) (x0 (exist (fun n3 : nat => (n3 < N)%nat) n H16))).
elim.
move=> x1 H20 H21.
apply H20.
rewrite - (BoundedClosedSectionEqual (D n2 (exist (fun n3 : nat => (n3 < N)%nat) n H16))).
apply (H17 (exist (fun n3 : nat => (n3 < N)%nat) n H16)).
apply sig_map.
reflexivity.
suff: (BoundedClosedSectionToR (D n2 (exist (fun m : nat => (m < N)%nat) n H9)) - BoundedClosedSectionToL (D n2 (exist (fun m : nat => (m < N)%nat) n H9)) >= 0).
move=> H19.
rewrite - (Rabs_right (BoundedClosedSectionToR (D n2 (exist (fun m : nat => (m < N)%nat) n H9)) - BoundedClosedSectionToL (D n2 (exist (fun m : nat => (m < N)%nat) n H9))) H19).
rewrite - (Rplus_0_r (BoundedClosedSectionToR (D n2 (exist (fun m : nat => (m < N)%nat) n H9)) - BoundedClosedSectionToL (D n2 (exist (fun m : nat => (m < N)%nat) n H9)))).
rewrite - Ropp_0.
apply (H13 n2).
apply (le_trans n1 (max n0 n1) n2).
apply (Nat.le_max_r n0 n1).
apply H14.
apply (Rge_minus (BoundedClosedSectionToR (D n2 (exist (fun m : nat => (m < N)%nat) n H9))) (BoundedClosedSectionToL (D n2 (exist (fun m : nat => (m < N)%nat) n H9)))).
apply (Rle_ge (BoundedClosedSectionToL (D n2 (exist (fun m : nat => (m < N)%nat) n H9))) (BoundedClosedSectionToR (D n2 (exist (fun m : nat => (m < N)%nat) n H9)))).
apply (BoundedClosedSectionLleqR (D n2 (exist (fun m : nat => (m < N)%nat) n H9))).
move=> H16.
apply False_ind.
apply H16.
apply H9.
unfold Rmin.
elim (Rle_dec (eps0 / 2) 1).
move=> H13.
apply (eps2_Rgt_R0 eps0).
apply H10.
move=> H13.
apply Rlt_0_1.
apply (eps2_Rgt_R0 eps0).
apply H10.
apply (le_trans n (S n) N (le_S n n (le_n n)) H9).
move=> m.
apply (constructive_definite_description (fun (r : R) => forall (n : nat), In R (proj1_sig (D n m)) r)).
apply (proj1 (Theorem_3_3_2 (fun (n : nat) => D n m) (proj2 (proj2 H5) m) (proj1 (proj2 H5) m))).
suff: (exists (F : ({n : nat | (n < N)%nat} -> BoundedClosedSectionSet) -> {n : nat | (n < N)%nat} -> BoundedClosedSectionSet), forall (d : {n : nat | (n < N)%nat} -> BoundedClosedSectionSet), ((infiniteCoverTemp (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (d m)) (x m))) -> (infiniteCoverTemp (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (F d m)) (x m)))) /\ (forall m : {n : nat | (n < N)%nat}, (BoundedClosedSectionToR (d m) - BoundedClosedSectionToL (d m)) * / 2 = (BoundedClosedSectionToR ((F d) m) - BoundedClosedSectionToL ((F d) m))) /\ (forall (m : {n : nat | (n < N)%nat}), Included R (proj1_sig (F d m)) (proj1_sig (d m)))).
elim.
move=> F H5.
suff: (exists (d0 : {n : nat | (n < N)%nat} -> BoundedClosedSectionSet), infiniteCoverTemp (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (d0 m)) (x m))).
elim.
move=> d0 H6.
suff: (let D := (fix D (n : nat) : ({n : nat | (n < N)%nat} -> BoundedClosedSectionSet) := 
match n with 
  | O => d0
  | S n0 => F (D n0)
end) in exists D : nat -> {n : nat | (n < N)%nat} -> BoundedClosedSectionSet, (forall n : nat, infiniteCoverTemp (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (D n m)) (x m))) /\ (forall m : {n : nat | (n < N)%nat}, Un_cv (fun n : nat => BoundedClosedSectionToR (D n m) - BoundedClosedSectionToL (D n m)) 0) /\ (forall (m : {n : nat | (n < N)%nat}) (n : nat), Included R (proj1_sig (D (S n) m)) (proj1_sig (D n m)))).
apply.
move=> D.
exists D.
apply conj.
elim.
apply H6.
move=> n.
apply (proj1 (H5 (D n))).
apply conj.
move=> m.
suff: ((fun n : nat => BoundedClosedSectionToR (D n m) - BoundedClosedSectionToL (D n m)) = (fun n : nat => (BoundedClosedSectionToR (d0 m) - BoundedClosedSectionToL (d0 m)) * (1 / (pow 2 n)))).
move=> H7.
rewrite H7.
rewrite - (Rmult_0_r (BoundedClosedSectionToR (d0 m) - BoundedClosedSectionToL (d0 m))).
suff: ((fun n : nat => (BoundedClosedSectionToR (d0 m) - BoundedClosedSectionToL (d0 m)) * (1 / 2 ^ n)) = (RSequenceMult (fun n : nat => BoundedClosedSectionToR (d0 m) - BoundedClosedSectionToL (d0 m)) (fun (n : nat) => 1 / pow 2 n))).
move=> H8.
rewrite H8.
apply (Theorem_2_5_1_mult (fun n : nat => (BoundedClosedSectionToR (d0 m) - BoundedClosedSectionToL (d0 m))) (fun (n : nat) => 1 / pow 2 n) (BoundedClosedSectionToR (d0 m) - BoundedClosedSectionToL (d0 m)) 0).
move=> eps H9.
exists O.
move=> n H10.
rewrite (proj2 (R_dist_refl (BoundedClosedSectionToR (d0 m) - BoundedClosedSectionToL (d0 m)) (BoundedClosedSectionToR (d0 m) - BoundedClosedSectionToL (d0 m)))).
apply H9.
reflexivity.
apply Formula_3_9_2.
apply functional_extensionality.
move=> n.
reflexivity.
apply functional_extensionality.
elim.
unfold pow.
unfold Rdiv.
rewrite (Rinv_r 1).
rewrite (Rmult_1_r (BoundedClosedSectionToR (d0 m) - BoundedClosedSectionToL (d0 m))).
reflexivity.
apply (Rgt_not_eq 1 0 Rlt_0_1).
move=> n H7.
rewrite - (proj1 (proj2 (H5 (D n)))).
rewrite H7.
rewrite (Rmult_assoc (BoundedClosedSectionToR (d0 m) - BoundedClosedSectionToL (d0 m)) (1 / 2 ^ n) (/ 2)).
suff: ((1 / 2 ^ n * / 2) = (1 / 2 ^ S n)).
move=> H8.
rewrite H8.
reflexivity.
unfold Rdiv.
rewrite (Rmult_1_l (/ (pow 2 n))).
rewrite (Rmult_1_l (/ (pow 2 (S n)))).
simpl.
rewrite (Rmult_comm 2 (pow 2 n)).
rewrite (Rinv_mult_distr (pow 2 n) 2).
reflexivity.
apply (Two_Pow_Neq_Zero n).
apply Two_Neq_Zero.
move=> m n.
apply (proj2 (proj2 (H5 (D n))) m).
elim (BoundedMetDef2 (Rn_met N) A (proj1 H1) (RnO N)).
move=> M H6.
suff: (- M <= M).
move=> H7.
suff: (exists (LR : ({lr : R * R | fst lr <= snd lr})), BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (- M, M) H7) = BoundedClosedSection LR).
move=> H8.
exists (fun (m : {n : nat | (n < N)%nat}) => exist (fun (X : Ensemble R) => exists LR : {lr : R * R | fst lr <= snd lr}, X = BoundedClosedSection LR) (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (- M, M) H7)) H8).
unfold infiniteCoverTemp.
unfold proj1_sig.
suff: ((Intersection (Rn N) (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (- M, M) H7)) (x m)) A) = A).
move=> H9.
rewrite H9.
apply H4.
apply Extensionality_Ensembles.
apply conj.
move=> a.
elim.
move=> a0 H9 H10.
apply H10.
move=> a H9.
apply (Intersection_intro (Rn N)).
move=> m.
suff: (Rabs (a m) <= M).
move=> H10.
apply BoundedClosedSection_intro.
simpl.
apply (Rle_trans (- M) (- Rabs (a m)) (a m)).
apply (Ropp_le_contravar M (Rabs (a m)) H10).
rewrite - {2} (Ropp_involutive (a m)).
apply (Ropp_le_contravar (Rabs (a m)) (- a m)).
rewrite - (Rabs_Ropp (a m)).
apply (Rle_abs (- a m)).
apply (Rle_trans (a m) (Rabs (a m)) M).
apply (Rle_abs (a m)).
apply H10.
apply (Rle_trans (Rabs (a m)) (Rn_dist N a (RnO N)) M).
unfold Rn_dist.
unfold Rnminus.
suff: ((Rnplus N a (Rnopp N (RnO N))) = a).
move=> H10.
rewrite H10.
apply (Rnot_lt_le (RnNorm N a) (Rabs (a m))).
move=> H11.
apply (Rle_not_lt (RnNorm N a * RnNorm N a) (Rabs (a m) * Rabs (a m))).
rewrite - (proj2 (RnNormNature N a)).
suff: (Rabs (a m) * Rabs (a m) = (a m) * (a m)).
move=> H12.
rewrite H12.
rewrite - (Rplus_0_r (a m * a m)).
rewrite (RnInnerProductDefinition N a a).
rewrite (MySumF2Excluded (Count N) RPCM (fun n1 : Count N =>  a n1 * a n1) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Singleton (Count N) m)).
simpl.
suff: ((FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Singleton (Count N) m)) = (exist (Finite (Count N)) (Singleton (Count N) m) (Singleton_is_finite (Count N) m))).
move=> H13.
rewrite H13.
rewrite MySumF2Singleton.
apply (Rplus_le_compat_l (a m * a m) 0).
apply MySumF2Induction.
apply conj.
apply (Req_le 0 0).
reflexivity.
move=> r1 r2 H14 H15.
simpl.
rewrite - (Rplus_0_r 0).
apply (Rplus_le_compat 0 r1 0 (a r2 * a r2)).
apply H15.
apply Rge_le.
apply (Formula_1_3_2 (a r2)).
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> n1.
elim.
move=> n2 H13 H14.
apply H13.
move=> n1 H13.
apply Intersection_intro.
apply H13.
apply Full_intro.
unfold Rabs.
elim (Rcase_abs (a m)).
move=> H12.
apply (Rmult_opp_opp (a m) (a m)).
move=> H12.
reflexivity.
apply (Rmult_le_0_lt_compat (RnNorm N a) (Rabs (a m)) (RnNorm N a) (Rabs (a m))).
apply (Rge_le (RnNorm N a) 0).
apply (proj1 (RnNormNature N a)).
apply (Rge_le (RnNorm N a) 0).
apply (proj1 (RnNormNature N a)).
apply H11.
apply H11.
suff: (Rnplus N a (Rnopp N (RnO N)) = Vadd Rfield (RnVS N) a (Vopp Rfield (RnVS N) (VO Rfield (RnVS N)))).
move=> H10.
rewrite H10.
rewrite (Vopp_O Rfield (RnVS N)).
apply (Vadd_O_r Rfield (RnVS N) a).
reflexivity.
apply (Rlt_le (Rn_dist N a (RnO N)) M).
apply (H6 a H9).
apply H9.
exists (exist (fun lr : R * R => fst lr <= snd lr) (- M, M) H7).
reflexivity.
suff: (0 <= M).
move=> H7.
apply (Rle_trans (- M) 0 M).
apply (Rge_le 0 (- M)).
apply (Ropp_0_le_ge_contravar M H7).
apply H7.
suff: (exists (a : Rn N), In (Rn N) A a).
elim.
move=> a H7.
apply (Rle_trans 0 (Rn_dist N a (RnO N)) M).
apply (Rge_le (Rn_dist N a (RnO N)) 0).
apply (Rn_dist_pos N a (RnO N)).
apply (Rlt_le (Rn_dist N a (RnO N)) M).
apply (H6 a H7).
apply NNPP.
move=> H7.
apply H4.
exists (Empty_set T).
apply conj.
apply (Empty_is_finite T).
move=> a H8.
apply False_ind.
apply H7.
exists a.
apply H8.
suff: (exists (G : ({n : nat | (n < N)%nat} -> BoundedClosedSectionSet) -> {n : nat | (n < N)%nat} -> {n : nat | (n < N)%nat} -> BoundedClosedSectionSet), forall (d : {n : nat | (n < N)%nat} -> BoundedClosedSectionSet) (k : {n : nat | (n < N)%nat}), ((infiniteCoverTemp (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (d m)) (x m)) -> infiniteCoverTemp (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (G d k m)) (x m)))) /\ (forall m : {n : nat | (n < N)%nat}, (m <> k) -> (BoundedClosedSectionToR (d m) - BoundedClosedSectionToL (d m)) = BoundedClosedSectionToR (G d k m) - BoundedClosedSectionToL (G d k m)) /\ ((BoundedClosedSectionToR (d k) - BoundedClosedSectionToL (d k)) * / 2 = BoundedClosedSectionToR (G d k k) - BoundedClosedSectionToL (G d k k)) /\ (forall m : {n : nat | (n < N)%nat}, Included R (proj1_sig (G d k m)) (proj1_sig (d m)))).
elim.
move=> G H5.
suff: (forall (k : nat), (k <= N)%nat -> exists (Fsub : ({n : nat | (n < N)%nat} -> BoundedClosedSectionSet) -> {n : nat | (n < N)%nat} -> BoundedClosedSectionSet), forall (d : {n : nat | (n < N)%nat} -> BoundedClosedSectionSet), (infiniteCoverTemp (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (d m)) (x m)) -> infiniteCoverTemp (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (Fsub d m)) (x m))) /\ (forall m : {n : nat | (n < N)%nat}, (proj1_sig m >= k)%nat -> (BoundedClosedSectionToR (d m) - BoundedClosedSectionToL (d m)) = BoundedClosedSectionToR (Fsub d m) - BoundedClosedSectionToL (Fsub d m)) /\ (forall m : {n : nat | (n < N)%nat}, (proj1_sig m < k)%nat -> (BoundedClosedSectionToR (d m) - BoundedClosedSectionToL (d m)) * / 2 = BoundedClosedSectionToR (Fsub d m) - BoundedClosedSectionToL (Fsub d m)) /\ (forall m : {n : nat | (n < N)%nat}, Included R (proj1_sig (Fsub d m)) (proj1_sig (d m)))).
move=> H6.
elim (H6 N).
move=> F H7.
exists F.
move=> d.
apply conj.
apply (proj1 (H7 d)).
apply conj.
move=> m.
apply (proj1 (proj2 (proj2 (H7 d))) m).
apply (proj2_sig m).
apply (proj2 (proj2 (proj2 (H7 d)))).
apply (le_n N).
elim.
move=> H6.
exists (fun (d : ({n : nat | (n < N)%nat} -> BoundedClosedSectionSet)) => d).
move=> d.
apply conj.
apply.
apply conj.
move=> m H7.
reflexivity.
apply conj.
move=> m H7.
apply False_ind.
apply (lt_not_le (proj1_sig m) 0 H7).
apply (le_0_n (proj1_sig m)).
move=> m x H7.
apply H7.
move=> k H6 H7.
elim H6.
move=> Fsub H8.
exists (fun (d : ({n : nat | (n < N)%nat} -> BoundedClosedSectionSet)) => (G (Fsub d) (exist (fun (n : nat) => (n < N)%nat) k H7))).
move=> d.
apply conj.
move=> H9.
apply (proj1 (H5 (Fsub d) (exist (fun (n : nat) => (n < N)%nat) k H7))).
apply (proj1 (H8 d) H9).
apply conj.
move=> m H9.
suff: (BoundedClosedSectionToR (d m) - BoundedClosedSectionToL (d m) = BoundedClosedSectionToR (Fsub d m) - BoundedClosedSectionToL (Fsub d m)).
move=> H10.
rewrite H10.
apply (proj1 (proj2 (H5 (Fsub d) (exist (fun (n : nat) => (n < N)%nat) k H7)))).
move=> H11.
apply (le_not_lt (S k) (proj1_sig m)).
apply H9.
rewrite H11.
apply (le_n (S k)).
apply (proj1 (proj2 (H8 d))).
apply (le_trans k (S k) (proj1_sig m) (le_S k k (le_n k)) H9).
apply conj.
move=> m H9.
elim (classic (proj1_sig m = k)).
move=> H10.
suff: ((BoundedClosedSectionToR (d m) - BoundedClosedSectionToL (d m)) = (BoundedClosedSectionToR (Fsub d m) - BoundedClosedSectionToL (Fsub d m))).
move=> H11.
rewrite H11.
suff: ((exist (fun n : nat => (n < N)%nat) k H7) = m).
move=> H12.
rewrite H12.
apply (proj1 (proj2 (proj2 (H5 (Fsub d) m)))).
apply sig_map.
rewrite H10.
reflexivity.
apply (proj1 (proj2 (H8 d)) m).
rewrite H10.
apply (le_n k).
move=> H10.
suff: ((BoundedClosedSectionToR (d m) - BoundedClosedSectionToL (d m)) * / 2= (BoundedClosedSectionToR (Fsub d m) - BoundedClosedSectionToL (Fsub d m))).
move=> H11.
rewrite H11.
apply (proj1 (proj2 (H5 (Fsub d) (exist (fun n : nat => (n < N)%nat) k H7))) m).
move=> H12.
apply H10.
rewrite H12.
reflexivity.
apply (proj1 (proj2 (proj2 (H8 d))) m).
elim (le_lt_or_eq (proj1_sig m) k).
apply.
move=> H11.
apply False_ind.
apply (H10 H11).
apply (le_S_n (proj1_sig m) k H9).
move=> m x H9.
apply (proj2 (proj2 (proj2 (H8 d))) m x).
apply (proj2 (proj2 (proj2 (H5 (Fsub d) (exist (fun n : nat => (n < N)%nat) k H7)))) m x H9).
apply (le_trans k (S k) N (le_S k k (le_n k)) H7).
suff: (forall (LR : BoundedClosedSectionSet), BoundedClosedSectionToL LR <= (BoundedClosedSectionToL LR + BoundedClosedSectionToR LR) * / 2).
move=> H5.
suff: (forall (LR : BoundedClosedSectionSet), (BoundedClosedSectionToL LR + BoundedClosedSectionToR LR) * / 2 <= BoundedClosedSectionToR LR).
move=> H6.
suff: (forall (LR : BoundedClosedSectionSet), exists (LR0 : {lr : R * R | fst lr <= snd lr}), BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (BoundedClosedSectionToL LR, (BoundedClosedSectionToL LR + BoundedClosedSectionToR LR) * / 2) (H5 LR)) = BoundedClosedSection LR0).
move=> H7.
suff: (forall (LR : BoundedClosedSectionSet), exists (LR0 : {lr : R * R | fst lr <= snd lr}), BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) ((BoundedClosedSectionToL LR + BoundedClosedSectionToR LR) * / 2, BoundedClosedSectionToR LR) (H6 LR)) = BoundedClosedSection LR0).
move=> H8.
suff: (let leftG := fun (G : ({n : nat | (n < N)%nat} -> BoundedClosedSectionSet)) (k : {n : nat | (n < N)%nat}) => (fun (m : {n : nat | (n < N)%nat}) => match (excluded_middle_informative (proj1_sig m = proj1_sig k)) with
| left _ => exist (fun (X : Ensemble R) => exists (LR : {lr : R * R | fst lr <= snd lr}), X = BoundedClosedSection LR) (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (BoundedClosedSectionToL (G m), (BoundedClosedSectionToL (G m) + BoundedClosedSectionToR (G m)) * / 2) (H5 (G m)))) (H7 (G m))
| right _ => G m
end) in (exists (G : ({n : nat | (n < N)%nat} -> BoundedClosedSectionSet) -> {n : nat | (n < N)%nat} -> {n : nat | (n < N)%nat} -> BoundedClosedSectionSet), forall (d : {n : nat | (n < N)%nat} -> BoundedClosedSectionSet) (k : {n : nat | (n < N)%nat}), (infiniteCoverTemp (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (d m)) (x m)) -> infiniteCoverTemp (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (G d k m)) (x m))) /\ (forall m : {n : nat | (n < N)%nat}, m <> k -> BoundedClosedSectionToR (d m) - BoundedClosedSectionToL (d m) = BoundedClosedSectionToR (G d k m) - BoundedClosedSectionToL (G d k m)) /\ (BoundedClosedSectionToR (d k) - BoundedClosedSectionToL (d k)) * / 2 = BoundedClosedSectionToR (G d k k) - BoundedClosedSectionToL (G d k k) /\ (forall m : {n : nat | (n < N)%nat}, Included R (proj1_sig (G d k m)) (proj1_sig (d m))))).
apply.
move=> leftG.
suff: (let rightG := fun (G : ({n : nat | (n < N)%nat} -> BoundedClosedSectionSet)) (k : {n : nat | (n < N)%nat}) => (fun (m : {n : nat | (n < N)%nat}) => match (excluded_middle_informative (proj1_sig m = proj1_sig k)) with
| left _ => exist (fun (X : Ensemble R) => exists (LR : {lr : R * R | fst lr <= snd lr}), X = BoundedClosedSection LR) (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) ((BoundedClosedSectionToL (G m) + BoundedClosedSectionToR (G m)) * / 2, BoundedClosedSectionToR (G m)) (H6 (G m)))) (H8 (G m))
| right _ => G m
end) in (exists (G : ({n : nat | (n < N)%nat} -> BoundedClosedSectionSet) -> {n : nat | (n < N)%nat} -> {n : nat | (n < N)%nat} -> BoundedClosedSectionSet), forall (d : {n : nat | (n < N)%nat} -> BoundedClosedSectionSet) (k : {n : nat | (n < N)%nat}), (infiniteCoverTemp (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (d m)) (x m)) -> infiniteCoverTemp (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (G d k m)) (x m))) /\ (forall m : {n : nat | (n < N)%nat}, m <> k -> BoundedClosedSectionToR (d m) - BoundedClosedSectionToL (d m) = BoundedClosedSectionToR (G d k m) - BoundedClosedSectionToL (G d k m)) /\ (BoundedClosedSectionToR (d k) - BoundedClosedSectionToL (d k)) * / 2 = BoundedClosedSectionToR (G d k k) - BoundedClosedSectionToL (G d k k) /\ (forall m : {n : nat | (n < N)%nat}, Included R (proj1_sig (G d k m)) (proj1_sig (d m))))).
apply.
move=> rightG.
exists (fun (d : ({n : nat | (n < N)%nat} -> BoundedClosedSectionSet)) (k : {n : nat | (n < N)%nat}) => match (excluded_middle_informative (infiniteCoverTemp (fun (x : Rn N) => forall (m : {n0 : nat | (n0 < N)%nat}), In R (proj1_sig (leftG d k m)) (x m)))) with 
|left _ => leftG d k 
|right _ => rightG d k
end).
move=> d k.
apply conj.
move=> H9.
elim (excluded_middle_informative (infiniteCoverTemp (fun x0 : Rn N => forall m0 : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (leftG d k m0)) (x0 m0)))).
apply.
move=> H10.
apply NNPP.
unfold infiniteCoverTemp.
move=> H11.
apply H9.
suff: (exists tt : Ensemble T, Finite T tt /\ Included (Base (Rn_met N)) (Intersection (Rn N) (fun x0 : Rn N => forall m0 : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (leftG d k m0)) (x0 m0)) A) (fun x : Base (Rn_met N) => exists t : T, In T tt t /\ In (Base (Rn_met N)) (X t) x)).
elim.
move=> ns1 H12.
suff: (exists tt : Ensemble T, Finite T tt /\ Included (Base (Rn_met N)) (Intersection (Rn N) (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (rightG d k m)) (x m)) A) (fun x : Base (Rn_met N) => exists t : T, In T tt t /\ In (Base (Rn_met N)) (X t) x)).
elim.
move=> ns2 H13.
exists (Union T ns1 ns2).
apply conj.
apply (Union_preserves_Finite T ns1 ns2 (proj1 H12) (proj1 H13)).
move=> a.
elim.
move=> a0 H14 H15.
elim (classic ((a0 k) <= (BoundedClosedSectionToL (d k) + BoundedClosedSectionToR (d k)) *  / 2)).
move=> H16.
elim (proj2 H12 a0).
move=> t H17.
exists t.
apply conj.
apply (Union_introl T ns1 ns2 t (proj1 H17)).
apply (proj2 H17).
apply (Intersection_intro (Rn N)).
move=> m.
unfold leftG.
elim (excluded_middle_informative (proj1_sig m = proj1_sig k)).
move=> H17.
apply BoundedClosedSection_intro.
simpl.
suff: (In R (BoundedClosedSection (BoundedClosedSectionToPair (d m))) (a0 m)).
elim.
move=> a1 H18 H19.
apply H18.
rewrite - (BoundedClosedSectionEqual (d m)).
apply (H14 m).
suff: (m = k).
move=> H18.
rewrite H18.
apply H16.
apply sig_map.
apply H17.
move=> H17.
apply (H14 m).
apply H15.
move=> H16.
elim (proj2 H13 a0).
move=> t H17.
exists t.
apply conj.
apply (Union_intror T ns1 ns2 t (proj1 H17)).
apply (proj2 H17).
apply (Intersection_intro (Rn N)).
move=> m.
unfold rightG.
elim (excluded_middle_informative (proj1_sig m = proj1_sig k)).
move=> H17.
apply BoundedClosedSection_intro.
simpl.
apply (Rnot_lt_le (a0 m) ((BoundedClosedSectionToL (d m) + BoundedClosedSectionToR (d m)) * / 2)).
move=> H18.
apply H16.
left.
suff: (m = k).
move=> H19.
rewrite - H19.
apply H18.
apply sig_map.
apply H17.
suff: (In R (BoundedClosedSection (BoundedClosedSectionToPair (d m))) (a0 m)).
elim.
move=> a1 H18 H19.
apply H19.
rewrite - (BoundedClosedSectionEqual (d m)).
apply (H14 m).
move=> H17.
apply (H14 m).
apply H15.
apply NNPP.
apply H11.
apply NNPP.
apply H10.
apply conj.
move=> m H9.
elim (excluded_middle_informative (infiniteCoverTemp (fun x : Rn N => forall m0 : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (leftG d k m0)) (x m0)))).
move=> H10.
unfold leftG.
elim (excluded_middle_informative (proj1_sig m = proj1_sig k)).
move=> H11.
apply False_ind.
apply H9.
apply sig_map.
apply H11.
move=> H11.
reflexivity.
unfold rightG.
elim (excluded_middle_informative (proj1_sig m = proj1_sig k)).
move=> H10.
apply False_ind.
apply H9.
apply sig_map.
apply H10.
move=> H10.
reflexivity.
apply conj.
elim (excluded_middle_informative (infiniteCoverTemp (fun x : Rn N => forall m : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (leftG d k m)) (x m)))).
move=> H9.
unfold leftG.
elim (excluded_middle_informative (proj1_sig k = proj1_sig k)).
move=> H10.
unfold BoundedClosedSectionToL.
unfold BoundedClosedSectionToR.
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr) (BoundedClosedSectionToL (d k), (BoundedClosedSectionToL (d k) + BoundedClosedSectionToR (d k)) * / 2) (H5 (d k)))).
simpl.
rewrite - {2} (eps2 (BoundedClosedSectionToL (d k))).
rewrite - (Rmult_plus_distr_r (BoundedClosedSectionToL (d k)) (BoundedClosedSectionToL (d k)) (/ 2)).
unfold Rminus.
rewrite (Ropp_mult_distr_l (BoundedClosedSectionToL (d k) + BoundedClosedSectionToL (d k)) (/ 2)).
rewrite - (Rmult_plus_distr_r (BoundedClosedSectionToL (d k) + BoundedClosedSectionToR (d k)) (- (BoundedClosedSectionToL (d k) + BoundedClosedSectionToL (d k)))).
rewrite (Ropp_plus_distr (BoundedClosedSectionToL (d k)) (BoundedClosedSectionToL (d k))).
rewrite (Rplus_comm (BoundedClosedSectionToL (d k)) (BoundedClosedSectionToR (d k))).
rewrite (Rplus_assoc (BoundedClosedSectionToR (d k)) (BoundedClosedSectionToL (d k)) (- BoundedClosedSectionToL (d k) + - BoundedClosedSectionToL (d k))).
rewrite - (Rplus_assoc (BoundedClosedSectionToL (d k)) (- BoundedClosedSectionToL (d k)) (- BoundedClosedSectionToL (d k))).
rewrite (Rplus_opp_r (BoundedClosedSectionToL (d k))).
rewrite (Rplus_0_l (- BoundedClosedSectionToL (d k))).
reflexivity.
move=> H10.
apply False_ind.
apply H10.
reflexivity.
move=> H9.
unfold rightG.
elim (excluded_middle_informative (proj1_sig k = proj1_sig k)).
move=> H10.
unfold BoundedClosedSectionToL.
unfold BoundedClosedSectionToR.
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr) ((BoundedClosedSectionToL (d k) + BoundedClosedSectionToR (d k)) * / 2, BoundedClosedSectionToR (d k)) (H6 (d k)))).
simpl.
rewrite - {1} (eps2 (BoundedClosedSectionToR (d k))).
rewrite - (Rmult_plus_distr_r (BoundedClosedSectionToR (d k)) (BoundedClosedSectionToR (d k)) (/ 2)).
unfold Rminus.
rewrite (Ropp_mult_distr_l (BoundedClosedSectionToL (d k) + BoundedClosedSectionToR (d k)) (/ 2)).
rewrite - (Rmult_plus_distr_r (BoundedClosedSectionToR (d k) + BoundedClosedSectionToR (d k)) (- (BoundedClosedSectionToL (d k) + BoundedClosedSectionToR (d k)))).
rewrite (Ropp_plus_distr (BoundedClosedSectionToL (d k)) (BoundedClosedSectionToR (d k))).
rewrite (Rplus_comm (- BoundedClosedSectionToL (d k)) (- BoundedClosedSectionToR (d k))).
rewrite (Rplus_assoc (BoundedClosedSectionToR (d k)) (BoundedClosedSectionToR (d k)) (- BoundedClosedSectionToR (d k) + - BoundedClosedSectionToL (d k))).
rewrite - (Rplus_assoc (BoundedClosedSectionToR (d k)) (- BoundedClosedSectionToR (d k)) (- BoundedClosedSectionToL (d k))).
rewrite (Rplus_opp_r (BoundedClosedSectionToR (d k))).
rewrite (Rplus_0_l (- BoundedClosedSectionToL (d k))).
reflexivity.
move=> H10.
apply False_ind.
apply H10.
reflexivity.
move=> m x.
elim (excluded_middle_informative (infiniteCoverTemp (fun x0 : Rn N => forall m0 : {n0 : nat | (n0 < N)%nat}, In R (proj1_sig (leftG d k m0)) (x0 m0)))).
move=> H9.
unfold leftG.
elim (excluded_middle_informative (proj1_sig m = proj1_sig k)).
move=> H11.
simpl.
elim.
move=> x0 H12 H13.
rewrite (BoundedClosedSectionEqual (d m)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (d m)) x0).
apply H12.
apply (Rle_trans x0 ((BoundedClosedSectionToL (d m) + BoundedClosedSectionToR (d m)) * / 2) (snd (proj1_sig (BoundedClosedSectionToPair (d m))))).
apply H13.
apply (H6 (d m)).
move=> H10.
apply.
move=> H9.
unfold rightG.
elim (excluded_middle_informative (proj1_sig m = proj1_sig k)).
move=> H11.
simpl.
elim.
move=> x0 H12 H13.
rewrite (BoundedClosedSectionEqual (d m)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (d m)) x0).
apply (Rle_trans (fst (proj1_sig (BoundedClosedSectionToPair (d m)))) ((BoundedClosedSectionToL (d m) + BoundedClosedSectionToR (d m)) * / 2) x0).
apply (H5 (d m)).
apply H12.
apply H13.
move=> H10.
apply.
move=> LR.
exists (exist (fun lr : R * R => fst lr <= snd lr) ((BoundedClosedSectionToL LR + BoundedClosedSectionToR LR) * / 2, BoundedClosedSectionToR LR) (H6 LR)).
reflexivity.
move=> LR.
exists (exist (fun lr : R * R => fst lr <= snd lr) (BoundedClosedSectionToL LR, (BoundedClosedSectionToL LR + BoundedClosedSectionToR LR) * / 2) (H5 LR)).
reflexivity.
move=> LR.
rewrite - {2} (eps2 (BoundedClosedSectionToR LR)).
rewrite - (Rmult_plus_distr_r (BoundedClosedSectionToR LR) (BoundedClosedSectionToR LR)).
apply (Rmult_le_compat_r (/ 2) (BoundedClosedSectionToL LR + BoundedClosedSectionToR LR) (BoundedClosedSectionToR LR + BoundedClosedSectionToR LR)).
apply (Rlt_le 0 (/ 2)).
apply (Rinv_0_lt_compat 2).
apply Two_Gt_Zero.
apply (Rplus_le_compat_r (BoundedClosedSectionToR LR) (BoundedClosedSectionToL LR) (BoundedClosedSectionToR LR)).
apply (BoundedClosedSectionLleqR LR).
move=> LR.
rewrite - {1} (eps2 (BoundedClosedSectionToL LR)).
rewrite - (Rmult_plus_distr_r (BoundedClosedSectionToL LR) (BoundedClosedSectionToL LR)).
apply (Rmult_le_compat_r (/ 2) (BoundedClosedSectionToL LR + BoundedClosedSectionToL LR) (BoundedClosedSectionToL LR + BoundedClosedSectionToR LR)).
apply (Rlt_le 0 (/ 2)).
apply (Rinv_0_lt_compat 2).
apply Two_Gt_Zero.
apply (Rplus_le_compat_l (BoundedClosedSectionToL LR) (BoundedClosedSectionToL LR) (BoundedClosedSectionToR LR)).
apply (BoundedClosedSectionLleqR LR).
Qed.

Lemma Theorem_7_4_2_R : forall (A : Ensemble R), (my_bounded A /\ (ClosedSetMet R_met A)) -> (CompactMet R_met A).
Proof.
move=> A H1.
suff: (CompactMet (Rn_met 1%nat) (fun (x : Rn 1%nat) => In R A (x (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1%nat))))).
move=> H2 T Ai H3 H4.
elim (H2 T (fun (t : T) => (fun (y : Rn 1%nat) => In R (Ai t) (y (exist (fun (n : nat) => (n < 1)%nat) O (le_n 1%nat)))))).
move=> tt H5.
exists tt.
apply conj.
apply (proj1 H5).
move=> a H6.
elim (proj2 H5 (fun (n : Count 1%nat) => a)).
move=> t H7.
exists t.
apply conj.
apply (proj1 H7).
apply (proj2 H7).
apply H6.
move=> t x H5.
elim (H3 t (x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)))).
move=> eps H6.
exists eps.
apply conj.
apply (proj1 H6).
move=> y H7.
apply (proj2 H6 (y (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)))).
unfold In.
unfold NeighborhoodMet.
unfold R_met.
simpl.
suff: (R_dist (y (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))) (x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))) = Rn_dist 1%nat y x).
move=> H8.
rewrite H8.
apply H7.
unfold R_dist.
unfold Rn_dist.
unfold RnNorm.
rewrite (MySqrtNature2 (exist (fun r : R => r >= 0) (RnInnerProduct 1 (Rnminus 1 y x) (Rnminus 1 y x)) (Proposition_4_2_4_1 1 (Rnminus 1 y x))) (Rabs (y (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)) - x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))))).
reflexivity.
apply conj.
apply (Rle_ge 0 (Rabs (y (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)) - x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))))).
apply (Rabs_pos (y (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)) - x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)))).
unfold proj1_sig.
unfold RnInnerProduct.
simpl.
unfold UnwrapRn.
elim (excluded_middle_informative (0 < 1)%nat).
move=> H8.
unfold Rnminus.
unfold Rnplus.
unfold Rnopp.
rewrite (Rplus_0_l ((y (exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H8) + - x (exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H8)) * (y (exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H8) + - x (exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H8)))).
suff: ((exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H8) = (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))).
move=> H9.
rewrite H9.
unfold Rabs.
elim (Rcase_abs (y (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)) - x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)))).
move=> H10.
rewrite (Rmult_opp_opp (y (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)) + - x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))) (y (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)) + - x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)))).
reflexivity.
move=> H10.
reflexivity.
apply sig_map.
reflexivity.
move=> H8.
apply False_ind.
apply H8.
apply (le_n 1).
apply H5.
move=> x H5.
elim (H4 (x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)))).
move=> t H6.
exists t.
apply H6.
apply H5.
apply (Theorem_7_4_2 1%nat (fun x : Rn 1 => In R A (x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))))).
apply conj.
elim (proj1 (bounded_abs A) (proj1 H1)).
move=> M H2.
exists (RnO 1%nat).
exists (M + 1).
move=> a H3.
apply (Rle_lt_trans (Rn_dist 1 a (RnO 1)) M (M + 1)).
apply (H2 (Rn_dist 1%nat a (RnO 1%nat))).
unfold Rn_dist.
apply (Im_intro R R A Rabs (a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)))).
apply H3.
unfold RnNorm.
apply (MySqrtNature2 (exist (fun r : R => r >= 0) (RnInnerProduct 1 (Rnminus 1 a (RnO 1)) (Rnminus 1 a (RnO 1))) (Proposition_4_2_4_1 1 (Rnminus 1 a (RnO 1)))) (Rabs (a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))))).
apply conj.
apply (Rle_ge 0 (Rabs (a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))))).
apply (Rabs_pos (a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)))).
unfold proj1_sig.
unfold RnInnerProduct.
simpl.
unfold UnwrapRn.
elim (excluded_middle_informative (0 < 1)%nat).
move=> H4.
unfold Rnminus.
unfold Rnplus.
unfold Rnopp.
rewrite (Rplus_0_l ((a (exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H4) + - RnO 1 (exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H4)) * (a (exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H4) + - RnO 1 (exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H4)))).
suff: ((exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H4) = (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))).
move=> H5.
rewrite H5.
unfold RnO.
rewrite Ropp_0.
rewrite (Rplus_0_r (a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)))).
unfold Rabs.
elim (Rcase_abs (a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)))).
move=> H6.
rewrite (Rmult_opp_opp (a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))) (a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)))).
reflexivity.
move=>H6.
reflexivity.
apply sig_map.
reflexivity.
move=> H4.
apply False_ind.
apply H4.
apply (le_n 1).
rewrite - {1} (Rplus_0_r M).
apply (Rplus_lt_compat_l M 0 1 Rlt_0_1).
apply Extensionality_Ensembles.
apply conj.
apply (Proposition_6_1_2 (Rn_met 1%nat) (fun x : Rn 1 => In R A (x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))))).
move=> a H2.
rewrite (proj2 H1).
move=> eps H3.
elim (H2 eps H3).
move=> x H4.
exists (x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))).
apply conj.
unfold In.
unfold NeighborhoodMet.
unfold R_met.
simpl.
suff: (R_dist (x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))) (a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))) = Rn_dist 1%nat x a).
move=> H5.
rewrite H5.
apply (proj1 H4).
unfold R_dist.
unfold Rn_dist.
unfold RnNorm.
rewrite (MySqrtNature2 (exist (fun r : R => r >= 0) (RnInnerProduct 1 (Rnminus 1 x a) (Rnminus 1 x a)) (Proposition_4_2_4_1 1 (Rnminus 1 x a))) (Rabs (x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)) - a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))))).
reflexivity.
apply conj.
apply (Rle_ge 0 (Rabs (x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)) - a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))))).
apply (Rabs_pos (x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)) - a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)))).
unfold proj1_sig.
unfold RnInnerProduct.
simpl.
unfold UnwrapRn.
elim (excluded_middle_informative (0 < 1)%nat).
move=> H5.
unfold Rnminus.
unfold Rnplus.
unfold Rnopp.
rewrite (Rplus_0_l ((x (exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H5) + - a (exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H5)) * (x (exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H5) + - a (exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H5)))).
suff: ((exist (fun n0 : nat => (n0 < 1)%nat) 0%nat H5) = (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))).
move=> H6.
rewrite H6.
unfold Rabs.
elim (Rcase_abs (x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)) - a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)))).
move=> H7.
rewrite (Rmult_opp_opp (x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)) + - a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1))) (x (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)) + - a (exist (fun n : nat => (n < 1)%nat) 0%nat (le_n 1)))).
reflexivity.
move=> H7.
reflexivity.
apply sig_map.
reflexivity.
move=> H5.
apply False_ind.
apply H5.
apply (le_n 1).
apply (proj2 H4).
Qed.

Lemma Theorem_8_1 : forall (f : R -> R) (a b : R) (H : a <= b), (forall (x : R), In R (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (a,b) H)) x -> ContinuousMet R_met R_met f (Full_set R) x) -> (forall (y : R), ((f a <= y /\ y <= f b) \/ (f b <= y /\ y <= f a)) -> exists (x : R), (In R (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (a,b) H)) x) /\ y = f x).
Proof.
suff: (forall (f : R -> R) (a b : R) (H : a <= b), (forall (x : R), In R (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (a,b) H)) x -> ContinuousMet R_met R_met f (Full_set R) x) -> (forall (y : R), (f a <= y /\ y <= f b) -> exists (x : R), (In R (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (a,b) H)) x) /\ y = f x)).
move=> H1 f a b H2 H3 y H4.
elim H4.
move=> H5.
apply (H1 f a b H2 H3 y H5).
move=> H5.
suff: (forall (x : R), In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H2)) x -> ContinuousMet R_met R_met (fun (x0 : R) => - f x0) (Full_set R) x).
move=> H6.
elim (H1 (fun (x : R) => - f x) a b H2 H6 (- y)).
move=> x H7.
exists x.
apply conj.
apply (proj1 H7).
rewrite - (Ropp_involutive y).
rewrite - (Ropp_involutive (f x)).
rewrite (proj2 H7).
reflexivity.
apply conj.
apply (Ropp_le_contravar (f a) y (proj2 H5)).
apply (Ropp_le_contravar y (f b) (proj1 H5)).
move=> x H6.
apply (Theorem_6_6_3_4_R R_met f (Full_set R) x (H3 x H6)).
move=> f a b H1 H2 y H3.
suff: (exists (IN : nat -> BoundedClosedSectionSet), (forall (n : nat), Included R (proj1_sig (IN (S n))) (proj1_sig (IN n))) /\ (Un_cv (fun (m : nat) => BoundedClosedSectionToR (IN m) - BoundedClosedSectionToL (IN m)) 0) /\ (forall (n : nat), f (BoundedClosedSectionToL (IN n)) <= y <= f (BoundedClosedSectionToR (IN n))) /\ (forall (n : nat), Included R (proj1_sig (IN n)) (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)))).
elim.
move=> IN H4.
elim (Theorem_3_3_2 IN).
elim.
move=> x.
elim.
move=> H5 H6 H7.
exists x.
suff: (In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)) x).
move=> H8.
apply conj.
apply H8.
apply (Rle_antisym y (f x)).
apply (Theorem_2_6 (fun (_ : nat) => y) (fun (n : nat) => f (BoundedClosedSectionToR (IN n))) y (f x)).
move=> eps H9.
exists O.
move=> n H10.
rewrite (proj2 (R_dist_refl y y)).
apply H9.
reflexivity.
apply (proj1 (Theorem_6_2 R_met R_met f (Full_set R) x (f x)) (H2 x H8) (fun (n : nat) => exist (Full_set R) (BoundedClosedSectionToR (IN n)) (Full_intro R (BoundedClosedSectionToR (IN n))))).
apply (proj2 (H7 x H5)).
move=> n.
apply (proj2 (proj1 (proj2 (proj2 H4)) n)).
apply (Theorem_2_6 (fun (n : nat) => f (BoundedClosedSectionToL (IN n))) (fun (_ : nat) => y) (f x) y).
apply (proj1 (Theorem_6_2 R_met R_met f (Full_set R) x (f x)) (H2 x H8) (fun (n : nat) => exist (Full_set R) (BoundedClosedSectionToL (IN n)) (Full_intro R (BoundedClosedSectionToL (IN n))))).
apply (proj1 (H7 x H5)).
move=> eps H9.
exists O.
move=> n H10.
rewrite (proj2 (R_dist_refl y y)).
apply H9.
reflexivity.
move=> n.
apply (proj1 (proj1 (proj2 (proj2 H4)) n)).
apply (proj2 (proj2 (proj2 H4)) O).
apply (H5 O).
apply (proj1 H4).
apply (proj1 (proj2 H4)).
suff: (exists LR : {lr : R * R | (fst lr) <= (snd lr)}, (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)) = (BoundedClosedSection LR)).
move=> H4.
suff: (forall (LR : BoundedClosedSectionSet), BoundedClosedSectionToL LR <= (BoundedClosedSectionToL LR + BoundedClosedSectionToR LR) * / 2).
move=> H5.
suff: (forall (LR : BoundedClosedSectionSet), (BoundedClosedSectionToL LR + BoundedClosedSectionToR LR) * / 2 <= BoundedClosedSectionToR LR).
move=> H6.
suff: (forall (LR : BoundedClosedSectionSet), exists (LR0 : {lr : R * R | fst lr <= snd lr}), BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (BoundedClosedSectionToL LR, (BoundedClosedSectionToL LR + BoundedClosedSectionToR LR) * / 2) (H5 LR)) = BoundedClosedSection LR0).
move=> H7.
suff: (forall (LR : BoundedClosedSectionSet), exists (LR0 : {lr : R * R | fst lr <= snd lr}), BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) ((BoundedClosedSectionToL LR + BoundedClosedSectionToR LR) * / 2, BoundedClosedSectionToR LR) (H6 LR)) = BoundedClosedSection LR0).
move=> H8.
suff: (let IN := fix IN (n : nat) : BoundedClosedSectionSet := match n with
| O => exist (fun (X : Ensemble R) => exists (LR : {lr : R * R | fst lr <= snd lr}),
    X = BoundedClosedSection LR) (BoundedClosedSection
        (exist (fun (lr : R * R) => fst lr <= snd lr) (a, b) H1)) H4
| S n0 => match (Rle_lt_dec (f (((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) / 2))) y) with
          | left a => exist (fun (X : Ensemble R) => exists (LR : {lr : R * R | fst lr <= snd lr}), X = BoundedClosedSection LR) (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) ((BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) * / 2, BoundedClosedSectionToR (IN n0)) (H6 (IN n0)))) (H8 (IN n0))
          | right b => exist (fun (X : Ensemble R) => exists (LR : {lr : R * R | fst lr <= snd lr}), X = BoundedClosedSection LR) (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (BoundedClosedSectionToL (IN n0), (BoundedClosedSectionToL (IN n0) + BoundedClosedSectionToR (IN n0)) * / 2) (H5 (IN n0)))) (H7 (IN n0))
end end in exists (IN : nat -> BoundedClosedSectionSet), (forall (n : nat), Included R (proj1_sig (IN (S n))) (proj1_sig (IN n))) /\ Un_cv (fun (m : nat) => BoundedClosedSectionToR (IN m) - BoundedClosedSectionToL (IN m)) 0 /\ (forall (n : nat), f (BoundedClosedSectionToL (IN n)) <= y <= f (BoundedClosedSectionToR (IN n))) /\ (forall (n : nat), Included R (proj1_sig (IN n)) (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (a, b) H1)))).
apply.
move=> IN.
exists IN.
suff: (forall n : nat, Included R (proj1_sig (IN (S n))) (proj1_sig (IN n))).
move=> H9.
apply conj.
apply H9.
apply conj.
suff: ((fun (m : nat) => BoundedClosedSectionToR (IN m) - BoundedClosedSectionToL (IN m)) = (fun (n : nat) => (BoundedClosedSectionToR (IN O) - BoundedClosedSectionToL (IN O)) * (1 / (pow 2 n)))).
move=> H10.
rewrite H10.
rewrite - (Rmult_0_r (BoundedClosedSectionToR (IN O) - BoundedClosedSectionToL (IN O))).
apply (Theorem_2_5_1_mult (fun n : nat => (BoundedClosedSectionToR (IN O) - BoundedClosedSectionToL (IN O))) (fun (n : nat) => 1 / pow 2 n) (BoundedClosedSectionToR (IN O) - BoundedClosedSectionToL (IN O)) 0).
move=> eps H11.
exists O.
move=> n H12.
rewrite (proj2 (R_dist_refl (BoundedClosedSectionToR (IN O) - BoundedClosedSectionToL (IN O)) (BoundedClosedSectionToR (IN O) - BoundedClosedSectionToL (IN O)))).
apply H11.
reflexivity.
apply Formula_3_9_2.
apply functional_extensionality.
elim.
unfold pow.
unfold Rdiv.
rewrite (Rinv_r 1).
rewrite (Rmult_1_r (BoundedClosedSectionToR (IN O) - BoundedClosedSectionToL (IN O))).
reflexivity.
apply (Rgt_not_eq 1 0 Rlt_0_1).
move=> n.
move=> H10.
suff: (BoundedClosedSectionToR (IN (S n)) -
BoundedClosedSectionToL (IN (S n)) = (BoundedClosedSectionToR (IN n) -
BoundedClosedSectionToL (IN n)) * / 2).
move=> H11.
rewrite H11.
rewrite H10.
unfold Rdiv.
rewrite (Rmult_1_l (/ (pow 2 n))).
rewrite (Rmult_1_l (/ (pow 2 (S n)))).
rewrite (Rinv_mult_distr 2 (pow 2 n)).
rewrite (Rmult_comm (/ 2) (/ (pow 2 n))).
apply (Rmult_assoc (BoundedClosedSectionToR (IN 0%nat) - BoundedClosedSectionToL (IN 0%nat)) (/ (pow 2 n)) (/ 2)).
apply Two_Neq_Zero.
apply (Two_Pow_Neq_Zero n).
simpl.
elim (Rle_lt_dec (f ((BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) / 2)) y).
move=> H11.
unfold BoundedClosedSectionToL at 2.
unfold BoundedClosedSectionToR at 1.
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr) ((BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) * / 2, BoundedClosedSectionToR (IN n)) (H6 (IN n)))).
simpl.
rewrite - {1} (eps2 (BoundedClosedSectionToR (IN n))).
rewrite - (Rmult_plus_distr_r (BoundedClosedSectionToR (IN n)) (BoundedClosedSectionToR (IN n)) (/ 2)).
unfold Rminus.
rewrite (Ropp_mult_distr_l (BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) (/ 2)).
rewrite - (Rmult_plus_distr_r (BoundedClosedSectionToR (IN n) + BoundedClosedSectionToR (IN n)) (- (BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)))).
rewrite (Ropp_plus_distr (BoundedClosedSectionToL (IN n)) (BoundedClosedSectionToR (IN n))).
rewrite (Rplus_comm (- BoundedClosedSectionToL (IN n)) (- BoundedClosedSectionToR (IN n))).
rewrite (Rplus_assoc (BoundedClosedSectionToR (IN n)) (BoundedClosedSectionToR (IN n)) (- BoundedClosedSectionToR (IN n) + - BoundedClosedSectionToL (IN n))).
rewrite - (Rplus_assoc (BoundedClosedSectionToR (IN n)) (- BoundedClosedSectionToR (IN n)) (- BoundedClosedSectionToL (IN n))).
rewrite (Rplus_opp_r (BoundedClosedSectionToR (IN n))).
rewrite (Rplus_0_l (- BoundedClosedSectionToL (IN n))).
reflexivity.
move=> H11.
unfold BoundedClosedSectionToL at 3.
unfold BoundedClosedSectionToR at 1.
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr) ((BoundedClosedSectionToL (IN n), (BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) * / 2)) (H5 (IN n)))).
simpl.
rewrite - {2} (eps2 (BoundedClosedSectionToL (IN n))).
rewrite - (Rmult_plus_distr_r (BoundedClosedSectionToL (IN n)) (BoundedClosedSectionToL (IN n)) (/ 2)).
unfold Rminus.
rewrite (Ropp_mult_distr_l (BoundedClosedSectionToL (IN n) + BoundedClosedSectionToL (IN n)) (/ 2)).
rewrite - (Rmult_plus_distr_r (BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) (- (BoundedClosedSectionToL (IN n) + BoundedClosedSectionToL (IN n)))).
rewrite (Ropp_plus_distr (BoundedClosedSectionToL (IN n)) (BoundedClosedSectionToL (IN n))).
rewrite (Rplus_comm (BoundedClosedSectionToL (IN n)) (BoundedClosedSectionToR (IN n))).
rewrite (Rplus_assoc (BoundedClosedSectionToR (IN n)) (BoundedClosedSectionToL (IN n)) (- BoundedClosedSectionToL (IN n) + - BoundedClosedSectionToL (IN n))).
rewrite - (Rplus_assoc (BoundedClosedSectionToL (IN n)) (- BoundedClosedSectionToL (IN n)) (- BoundedClosedSectionToL (IN n))).
rewrite (Rplus_opp_r (BoundedClosedSectionToL (IN n))).
rewrite (Rplus_0_l (- BoundedClosedSectionToL (IN n))).
reflexivity.
apply conj.
elim.
simpl.
unfold BoundedClosedSectionToL.
unfold BoundedClosedSectionToR.
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)).
simpl.
apply H3.
move=> n H10.
simpl.
elim (Rle_lt_dec (f ((BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) / 2)) y).
unfold Rdiv.
move=> H11.
unfold BoundedClosedSectionToL at 1.
unfold BoundedClosedSectionToR at 3.
rewrite (BoundedClosedSectionSetEqual (exist (fun (lr : R * R) => fst lr <= snd lr) ((BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) * / 2, BoundedClosedSectionToR (IN n)) (H6 (IN n)))).
simpl.
apply conj.
apply H11.
apply (proj2 H10).
move=> H11.
unfold BoundedClosedSectionToL at 1.
unfold BoundedClosedSectionToR at 2.
rewrite (BoundedClosedSectionSetEqual (exist (fun (lr : R * R) => fst lr <= snd lr) (BoundedClosedSectionToL (IN n), (BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) * / 2) (H5 (IN n)))).
simpl.
apply conj.
apply (proj1 H10).
left.
apply H11.
elim.
move=> x.
apply.
move=> n H10 x H11.
apply (H10 x).
apply (H9 n x H11).
move=> n.
simpl.
elim (Rle_lt_dec (f ((BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) / 2)) y).
move=> H9.
rewrite (BoundedClosedSectionEqual (exist (fun X : Ensemble R => exists LR : {lr : R * R | fst lr <= snd lr}, X = BoundedClosedSection LR) (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) ((BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) * / 2, BoundedClosedSectionToR (IN n)) (H6 (IN n)))) (H8 (IN n)))).
rewrite (BoundedClosedSectionSetEqual (exist (fun lr : R * R => fst lr <= snd lr) ((BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) * / 2, BoundedClosedSectionToR (IN n)) (H6 (IN n)))).
move=> x.
elim.
simpl.
move=> x0 H10 H11.
rewrite (BoundedClosedSectionEqual (IN n)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN n))).
apply (Rle_trans (BoundedClosedSectionToL (IN n)) ((BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) * / 2) x0).
apply (H5 (IN n)).
apply H10.
apply H11.
move=> H9.
rewrite (BoundedClosedSectionEqual (exist (fun (X : Ensemble R) => exists (LR : {lr : R * R | fst lr <= snd lr}), X = BoundedClosedSection LR) (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (BoundedClosedSectionToL (IN n), (BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) * / 2) (H5 (IN n)))) (H7 (IN n)))).
rewrite (BoundedClosedSectionSetEqual (exist (fun (lr : R * R) => fst lr <= snd lr) (BoundedClosedSectionToL (IN n), (BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) * / 2) (H5 (IN n)))).
move=> x.
elim.
simpl.
move=> x0 H10 H11.
rewrite (BoundedClosedSectionEqual (IN n)).
apply (BoundedClosedSection_intro (BoundedClosedSectionToPair (IN n))).
apply H10.
apply (Rle_trans x0 ((BoundedClosedSectionToL (IN n) + BoundedClosedSectionToR (IN n)) * / 2) (BoundedClosedSectionToR (IN n))).
apply H11.
apply (H6 (IN n)).
move=> LR.
exists (exist (fun lr : R * R => fst lr <= snd lr) ((BoundedClosedSectionToL LR + BoundedClosedSectionToR LR) * / 2, BoundedClosedSectionToR LR) (H6 LR)).
reflexivity.
move=> LR.
exists (exist (fun lr : R * R => fst lr <= snd lr) (BoundedClosedSectionToL LR, (BoundedClosedSectionToL LR + BoundedClosedSectionToR LR) * / 2) (H5 LR)).
reflexivity.
move=> LR.
rewrite - {2} (eps2 (BoundedClosedSectionToR LR)).
rewrite - (Rmult_plus_distr_r (BoundedClosedSectionToR LR) (BoundedClosedSectionToR LR)).
apply (Rmult_le_compat_r (/ 2) (BoundedClosedSectionToL LR + BoundedClosedSectionToR LR) (BoundedClosedSectionToR LR + BoundedClosedSectionToR LR)).
apply (Rlt_le 0 (/ 2)).
apply (Rinv_0_lt_compat 2).
apply Two_Gt_Zero.
apply (Rplus_le_compat_r (BoundedClosedSectionToR LR) (BoundedClosedSectionToL LR) (BoundedClosedSectionToR LR)).
apply (BoundedClosedSectionLleqR LR).
move=> LR.
rewrite - {1} (eps2 (BoundedClosedSectionToL LR)).
rewrite - (Rmult_plus_distr_r (BoundedClosedSectionToL LR) (BoundedClosedSectionToL LR)).
apply (Rmult_le_compat_r (/ 2) (BoundedClosedSectionToL LR + BoundedClosedSectionToL LR) (BoundedClosedSectionToL LR + BoundedClosedSectionToR LR)).
apply (Rlt_le 0 (/ 2)).
apply (Rinv_0_lt_compat 2).
apply Two_Gt_Zero.
apply (Rplus_le_compat_l (BoundedClosedSectionToL LR) (BoundedClosedSectionToL LR) (BoundedClosedSectionToR LR)).
apply (BoundedClosedSectionLleqR LR).
exists (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1).
reflexivity.
Qed.

Lemma BoundedClosedSectionBoundedClosed : forall (a b : R) (H : a <= b), (BoundedMet R_met (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (a, b) H))) /\ (ClosedSetMet R_met (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (a, b) H))).
Proof.
move=> a b H1.
apply conj.
exists 0.
exists (Rmax (Rabs a) (Rabs b) + 1).
move=> x1.
elim.
move=> x2 H2 H3.
unfold NeighborhoodMet.
unfold dist.
unfold R_met.
unfold R_dist.
unfold Rabs at 3.
simpl.
unfold In.
unfold Rminus.
rewrite Ropp_0.
rewrite (Rplus_0_r x2).
elim (Rcase_abs x2).
move=> H4.
apply (Rle_lt_trans (- x2) (Rmax (Rabs a) (Rabs b)) (Rmax (Rabs a) (Rabs b) + 1)).
apply (Rle_trans (- x2) (Rabs a) (Rmax (Rabs a) (Rabs b))).
apply (Rle_trans (- x2) (- a) (Rabs a)).
apply (Ropp_le_contravar x2 a H2).
rewrite - (Rabs_Ropp a).
apply (Rle_abs (- a)).
apply (Rmax_l (Rabs a) (Rabs b)).
apply (Rlt_plus_1 (Rmax (Rabs a) (Rabs b))).
move=> H4.
apply (Rle_lt_trans x2 (Rmax (Rabs a) (Rabs b)) (Rmax (Rabs a) (Rabs b) + 1)).
apply (Rle_trans x2 (Rabs b) (Rmax (Rabs a) (Rabs b))).
apply (Rle_trans x2 b (Rabs b)).
apply H3.
apply (Rle_abs b).
apply (Rmax_r (Rabs a) (Rabs b)).
apply (Rlt_plus_1 (Rmax (Rabs a) (Rabs b))).
apply Extensionality_Ensembles.
apply conj.
apply (Proposition_6_1_2 R_met (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1))).
move=> x H2.
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)).
apply (Rnot_lt_le x a).
move=> H3.
elim (H2 (a - x)).
move => x0 H4.
apply (Rlt_not_le a x0).
apply (Rplus_lt_reg_r (- x) x0 a).
rewrite - (Rabs_right (x0 + - x)).
apply (proj1 H4).
apply (Rge_trans (x0 + - x) (a + - x) 0).
apply (Rplus_ge_compat_r (- x) x0 a).
apply (Rle_ge a x0).
elim (proj2 H4).
move=> x1 H5 H6.
apply H5.
apply (Rge_minus a x).
left.
apply H3.
elim (proj2 H4).
move=> x1 H5 H6.
apply H5.
apply (Rgt_minus a x H3).
apply (Rnot_lt_le b x).
move=> H3.
elim (H2 (x - b)).
move=> x0 H4.
apply (Rlt_not_le x0 b).
apply (Ropp_lt_cancel b x0).
apply (Rplus_lt_reg_l x (- x0) (- b)).
apply (Rle_lt_trans (x + - x0) (R_dist x0 x) (x + - b)).
rewrite (R_dist_sym x0 x).
apply (Rle_abs (x + - x0)).
apply (proj1 H4).
elim (proj2 H4).
move=> x1 H5 H6.
apply H6.
apply (Rgt_minus x b H3).
Qed.

Lemma Theorem_8_1_corollary_2 : forall (f : R -> R) (a b : R) (H1 : a <= b), (forall (x : R), In R (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (a, b) H1)) x -> ContinuousMet R_met R_met f (Full_set R) x) -> forall (m M : R), is_greatest_lower_bound (Im R R (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (a, b) H1)) f) m -> is_least_upper_bound (Im R R (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (a, b) H1)) f) M -> forall (H2 : m <= M), Im R R (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (a, b) H1)) f = (BoundedClosedSection (exist (fun (lr : R * R) => fst lr <= snd lr) (m, M) H2)).
Proof.
move=> f a b H1 H2 m M H3 H4 H5.
apply Extensionality_Ensembles.
apply conj.
move=> x H6.
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (m, M) H5) x).
apply (Rge_le x m).
apply (proj1 H3 x H6).
apply (proj1 H4 x H6).
move=> x.
elim.
move=> x0.
simpl.
move=> H6 H7.
elim (Theorem_7_3_2_1 R_met f (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1))).
move=> M0 H8.
suff: (exists (Mx : R), In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)) Mx /\ M0 = f Mx).
elim.
move=> Mx H9.
elim (Theorem_7_3_2_2 R_met f (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1))).
move=> m0 H10.
suff: (exists (mx : R), In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)) mx /\ m0 = f mx).
elim.
move=> mx H11.
elim (Rle_or_lt mx Mx).
move=> H12.
suff: ((forall x : R, In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (mx, Mx) H12)) x -> ContinuousMet R_met R_met f (Full_set R) x)).
move=> H13.
elim (Theorem_8_1 f mx Mx H12 H13 x0).
move=> x1 H14.
apply (Im_intro R R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)) f x1).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1) x1).
apply (Rle_trans a mx x1).
elim (proj1 H11).
move=> x2 H15 H16.
apply H15.
elim (proj1 H14).
move=> x2 H15 H16.
apply H15.
apply (Rle_trans x1 Mx b).
elim (proj1 H14).
move=> x2 H15 H16.
apply H16.
elim (proj1 H9).
move=> x2 H15 H16.
apply H16.
apply (proj2 H14).
left.
rewrite - (proj2 H11).
rewrite - (proj2 H9).
rewrite (proj2 Proposition_1_3_corollary_1 (Im (Base R_met) R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)) f) M0 M H8 H4).
rewrite (proj2 Proposition_1_3_corollary_2 (Im (Base R_met) R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)) f) m0 m H10 H3).
apply conj.
apply H6.
apply H7.
move=> x1.
elim.
move=> x2 H13 H14.
apply (H2 x2).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1) x2).
apply (Rle_trans a mx x2).
elim (proj1 H11).
move=> x3 H15 H16.
apply H15.
apply H13.
apply (Rle_trans x2 Mx b).
apply H14.
elim (proj1 H9).
move=> x3 H15 H16.
apply H16.
move=> H12.
suff: ((forall x : R, In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (Mx, mx) (Rlt_le Mx mx H12))) x -> ContinuousMet R_met R_met f (Full_set R) x)).
move=> H13.
elim (Theorem_8_1 f Mx mx (Rlt_le Mx mx H12) H13 x0).
move=> x1 H14.
apply (Im_intro R R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)) f x1).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1) x1).
apply (Rle_trans a Mx x1).
elim (proj1 H9).
move=> x2 H15 H16.
apply H15.
elim (proj1 H14).
move=> x2 H15 H16.
apply H15.
apply (Rle_trans x1 mx b).
elim (proj1 H14).
move=> x2 H15 H16.
apply H16.
elim (proj1 H11).
move=> x2 H15 H16.
apply H16.
apply (proj2 H14).
right.
rewrite - (proj2 H11).
rewrite - (proj2 H9).
rewrite (proj2 Proposition_1_3_corollary_1 (Im (Base R_met) R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)) f) M0 M H8 H4).
rewrite (proj2 Proposition_1_3_corollary_2 (Im (Base R_met) R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)) f) m0 m H10 H3).
apply conj.
apply H6.
apply H7.
move=> x1.
elim.
move=> x2 H13 H14.
apply (H2 x2).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1) x2).
apply (Rle_trans a Mx x2).
elim (proj1 H9).
move=> x3 H15 H16.
apply H15.
apply H13.
apply (Rle_trans x2 mx b).
apply H14.
elim (proj1 H11).
move=> x3 H15 H16.
apply H16.
elim (proj1 H10).
move=> mx H11 y H12.
exists mx.
apply conj.
apply H11.
apply H12.
apply (Inhabited_intro R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)) a).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1) a).
right.
reflexivity.
apply H1.
apply H2.
apply (Theorem_7_2_2_2_R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1))).
apply (BoundedClosedSectionBoundedClosed a b H1).
elim (proj1 H8).
move=> x1 H9 y H10.
exists x1.
apply conj.
apply H9.
apply H10.
apply (Inhabited_intro R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1)) a).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1) a).
right.
reflexivity.
apply H1.
apply H2.
apply (Theorem_7_2_2_2_R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H1))).
apply (BoundedClosedSectionBoundedClosed a b H1).
Qed.

Definition RextendFunUnWrapRextend (f : R -> R) := fun (r : Rextend) => Rval (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => (f r)
end).

Lemma Theorem_8_1_corollary_3_sub : forall (f : R -> R) (a b : Rextend), (Rextendlt a b) -> (forall (x : R), (Rextendlt a (Rval x)) -> (Rextendlt (Rval x) b) -> ContinuousMet R_met R_met f (Full_set R) x) -> forall (m M : Rextend), limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun (r : Rextend) => Rextendlt a r) a m -> limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun (r : Rextend) => Rextendlt r b) b M -> forall (y : R), ((Rextendlt m (Rval y) /\ Rextendlt (Rval y) M) \/ (Rextendlt M (Rval y) /\ Rextendlt (Rval y) m)) -> exists (x : R), Rextendlt a (Rval x) /\ Rextendlt (Rval x) b /\ y = f x.
Proof.
suff: (forall (f : R -> R) (a b : Rextend), Rextendlt a b -> (forall (x : R), Rextendlt a (Rval x) -> Rextendlt (Rval x) b -> ContinuousMet R_met R_met f (Full_set R) x) -> forall (m M : Rextend), limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun r : Rextend => Rextendlt a r) a m -> limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun r : Rextend => Rextendlt r b) b M -> forall (y : R), Rextendlt m (Rval y) /\ Rextendlt (Rval y) M -> exists (x : R), Rextendlt a (Rval x) /\ Rextendlt (Rval x) b /\ y = f x).
move => H1.
suff: (forall (f : R -> R) (A : Ensemble Rextend) (x : Rextend) (y : Rextend), limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) A x y -> limit_in Rextend_met Rextend_met
  (RextendFunUnWrapRextend (fun r : R => - f r))
  A x match y with
  | Rinf => Rminf
  | Rminf => Rinf
  | Rval r => Rval (- r)
  end).
move=> H2 f a b H3 H4 m M H5 H6 y.
elim.
apply (H1 f a b H3 H4 m M H5 H6 y).
move=> H7.
suff: (limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend (fun (r : R) => - f r)) (fun r : Rextend => Rextendlt a r) a (match m with Rinf => Rminf | Rminf => Rinf | Rval r => Rval (- r) end)).
move=> H8.
suff: (limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend (fun (r : R) => - f r)) (fun r : Rextend => Rextendlt r b) b (match M with Rinf => Rminf | Rminf => Rinf | Rval r => Rval (- r) end)).
move=> H9.
suff: (forall x : R, Rextendlt a (Rval x) -> Rextendlt (Rval x) b -> ContinuousMet R_met R_met (fun r : R => - f r) (Full_set R) x).
move=> H10.
elim (H1 (fun (r : R) => - f r) a b H3 H10 (match m with Rinf => Rminf | Rminf => Rinf | Rval r => Rval (- r) end) (match M with Rinf => Rminf | Rminf => Rinf | Rval r => Rval (- r) end) H8 H9 (- y)).
move=> x H11.
exists x.
apply conj.
apply (proj1 H11).
apply conj.
apply (proj1 (proj2 H11)).
rewrite - (Ropp_involutive y).
rewrite - (Ropp_involutive (f x)).
rewrite (proj2 (proj2 H11)).
reflexivity.
suff: (Rextendlt M (Rval y) /\ Rextendlt (Rval y) m).
elim m.
elim M.
unfold Rextendlt.
move=> H11.
apply False_ind.
apply (proj1 H11).
unfold Rextendlt.
apply.
move=> r.
unfold Rextendlt.
move=> H11.
apply conj.
apply I.
apply (Ropp_lt_contravar y r (proj1 H11)).
elim M.
unfold Rextendlt.
apply.
unfold Rextendlt.
move=> H11.
apply conj.
apply (proj2 H11).
apply (proj1 H11).
move=> r H11.
apply False_ind.
apply (proj2 H11).
move=> r.
elim M.
unfold Rextendlt.
move=> H11.
apply False_ind.
apply (proj1 H11).
unfold Rextendlt.
move=> H11.
apply conj.
apply (Ropp_lt_contravar r y (proj2 H11)).
apply I.
move=> rr.
unfold Rextendlt.
move=> H11.
apply conj.
apply (Ropp_lt_contravar r y (proj2 H11)).
apply (Ropp_lt_contravar y rr (proj1 H11)).
apply H7.
move=> x H10 H11.
apply (Theorem_6_6_3_4_R R_met f (Full_set R) x (H4 x H10 H11)).
apply (H2 f (fun r : Rextend => Rextendlt r b) b M H6).
apply (H2 f (fun r : Rextend => Rextendlt a r) a m H5).
move=> f A x.
elim.
move=> H2.
apply (proj1 (limit_minf_R_extend_same Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => (- f r)
end)) A x)).
suff: (limit_inf_R Rextend_met (fun r : Rextend => match r with
  | Rval r0 => f r0
  | _ => 0
end) A x).
move=> H3 M.
elim (H3 (- M)).
move=> x0 H4.
exists x0.
apply conj.
apply (proj1 H4).
elim.
move=> H5.
apply (Ropp_lt_cancel 0 M).
rewrite Ropp_0.
apply (proj2 H4 Rinf H5).
move=> H5.
apply (Ropp_lt_cancel 0 M).
rewrite Ropp_0.
apply (proj2 H4 Rminf H5).
move=> r H5.
apply (Ropp_lt_cancel (- f r) M).
rewrite (Ropp_involutive (f r)).
apply (proj2 H4 (Rval r) H5).
apply (proj2 (limit_inf_R_extend_same Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) A x) H2).
move=> H2.
apply (proj1 (limit_inf_R_extend_same Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => (- f r)
end)) A x)).
suff: (limit_minf_R Rextend_met (fun r : Rextend => match r with
  | Rval r0 => f r0
  | _ => 0
end) A x).
move=> H3 M.
elim (H3 (- M)).
move=> x0 H4.
exists x0.
apply conj.
apply (proj1 H4).
elim.
move=> H5.
apply (Ropp_lt_cancel M 0).
rewrite Ropp_0.
apply (proj2 H4 Rinf H5).
move=> H5.
apply (Ropp_lt_cancel M 0).
rewrite Ropp_0.
apply (proj2 H4 Rminf H5).
move=> r H5.
apply (Ropp_lt_cancel M (- f r)).
rewrite (Ropp_involutive (f r)).
apply (proj2 H4 (Rval r) H5).
apply (proj2 (limit_minf_R_extend_same Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) A x) H2).
move=> r H2.
apply (proj1 (limit_in_R_R_extend_same_2 Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => - f r
end)) A x (- r))).
suff: ((fun (r0 : Rextend) => match r0 with
  | Rval r1 => - f r1
  | _ => 0
end) = (fun (r0 : Rextend) => - match r0 with
  | Rval r1 => f r1
  | _ => 0
end)).
move=> H3.
rewrite H3.
apply (Theorem_6_6_1_4_R Rextend_met (fun (r0 : Rextend) => match r0 with
  | Rval r1 => f r1
  | _ => 0
end) A x r).
apply (proj2 (limit_in_R_R_extend_same_2 Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) A x r)).
apply H2.
apply functional_extensionality.
elim.
rewrite Ropp_0.
reflexivity.
rewrite Ropp_0.
reflexivity.
move=> r0.
reflexivity.
move=> f a b H1 H2 m M H3 H4 y H5.
suff: (exists (m0 : R), Rextendlt a (Rval m0) /\ Rextendlt (Rval m0) b /\ f m0 < y).
elim.
move=> m0 H6.
suff: (exists (M0 : R), Rextendlt a (Rval M0) /\ Rextendlt (Rval M0) b /\ m0 <= M0 /\ y < f M0).
elim.
move=> M0 H7.
suff: (forall (x : R), In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (m0, M0) (proj1 (proj2 (proj2 H7))))) x -> ContinuousMet R_met R_met f (Full_set R) x).
move=> H8.
elim (Theorem_8_1 f m0 M0 (proj1 (proj2 (proj2 H7))) H8 y).
move=> x H9.
exists x.
apply conj.
suff: (Rextendlt a (Rval m0)).
unfold Rextendlt.
elim a.
apply.
apply.
move=> r H10.
apply (Rlt_le_trans r m0 x).
apply H10.
elim (proj1 H9).
move=> x0 H11 H12.
apply H11.
apply (proj1 H6).
apply conj.
suff: (Rextendlt (Rval M0) b).
unfold Rextendlt.
elim b.
apply.
apply.
move=> r H10.
apply (Rle_lt_trans x M0 r).
elim (proj1 H9).
move=> x0 H11 H12.
apply H12.
apply H10.
apply (proj1 (proj2 H7)).
apply (proj2 H9).
left.
apply conj.
left.
apply (proj2 (proj2 H6)).
left.
apply (proj2 (proj2 (proj2 H7))).
move=> x H8.
apply (H2 x).
suff: (Rextendlt a (Rval m0)).
unfold Rextendlt.
elim a.
apply.
apply.
move=> r H9.
apply (Rlt_le_trans r m0 x).
apply H9.
elim H8.
move=> x0 H10 H11.
apply H10.
apply (proj1 H6).
suff: (Rextendlt (Rval M0) b).
unfold Rextendlt.
elim b.
apply.
apply.
move=> r H9.
apply (Rle_lt_trans x M0 r).
elim H8.
move=> x0 H10 H11.
apply H11.
apply H9.
apply (proj1 (proj2 H7)).
suff: (limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun r : Rextend => Rextendlt r b) b M).
suff: (Rextendlt (Rval y) M).
suff: (Rextendlt (Rval m0) b).
elim M.
elim b.
move=> H7 H8 H9.
suff: ((forall r : R, Rval (f r) = (fun (r : Rextend) => Rval (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (Rval r))).
move=> H10.
suff: (limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun r : Rextend => exists l : R, In R (Full_set R) l /\ r = Rval l) Rinf Rinf).
move=> H11.
elim (proj2 (limit_inf_inf_extend_same f (fun (r : Rextend) => Rval (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (Full_set R) H10) H11 (y + 1)).
move=> br H12.
exists (Rmax m0 br).
apply conj.
suff: (Rextendlt a (Rval m0)).
elim a.
apply.
apply.
move=> r H13.
apply (Rlt_le_trans r m0 (Rmax m0 br)).
apply H13.
apply (Rmax_l m0 br).
apply (proj1 H6).
apply conj.
apply I.
apply conj.
apply (Rmax_l m0 br).
apply (Rlt_le_trans y (y + 1) (f (Rmax m0 br))).
apply (Rlt_plus_1 y).
apply (Rge_le (f (Rmax m0 br)) (y + 1)).
apply (H12 (Rmax m0 br)).
apply conj.
apply (Full_intro R (Rmax m0 br)).
apply (Rle_ge br (Rmax m0 br)).
apply (Rmax_r m0 br).
move=> eps H11.
elim (H9 eps H11).
move=> dlt H12.
exists dlt.
apply conj.
apply (proj1 H12).
move=> x H13.
apply (proj2 H12 x).
apply conj.
elim (proj1 H13).
move=> xr H14.
rewrite (proj2 H14).
apply I.
apply (proj2 H13).
move=> r.
reflexivity.
move=> H7.
apply False_ind.
apply H7.
move=> br H7 H8 H9.
suff: (limit_inf_R R_met f (fun (r : R) => r < br) br).
move=> H10.
elim (H10 y).
move=> dlt H11.
exists (Rmax m0 (br - dlt * / 2)).
apply conj.
suff: (Rextendlt a (Rval m0)).
elim a.
apply.
apply.
move=> r H12.
apply (Rlt_le_trans r m0 (Rmax m0 (br - dlt * / 2))).
apply H12.
apply (Rmax_l m0 (br - dlt * / 2)).
apply (proj1 H6).
apply conj.
unfold Rmax.
elim (Rle_dec m0 (br - dlt * / 2)).
move=> H12.
rewrite - {2} (Rplus_0_r br).
apply (Rplus_lt_compat_l br (- (dlt * / 2)) 0).
apply (Ropp_lt_gt_0_contravar (dlt * / 2)).
apply (eps2_Rgt_R0 dlt (proj1 H11)).
move=> H12.
apply H7.
apply conj.
apply (Rmax_l m0 (br - dlt * / 2)).
apply (proj2 H11 (Rmax m0 (br - dlt * / 2))).
apply conj.
unfold Rmax.
elim (Rle_dec m0 (br - dlt * / 2)).
move=> H12.
rewrite - {2} (Rplus_0_r br).
apply (Rplus_lt_compat_l br (- (dlt * / 2)) 0).
apply (Ropp_lt_gt_0_contravar (dlt * / 2)).
apply (eps2_Rgt_R0 dlt (proj1 H11)).
move=> H12.
apply H7.
unfold dist.
unfold R_met.
unfold R_dist.
rewrite (Rabs_minus_sym (Rmax m0 (br - dlt * / 2)) br).
rewrite (Rabs_right (br - Rmax m0 (br - dlt * / 2))).
apply (Rle_lt_trans (br - Rmax m0 (br - dlt * / 2)) (br - (br - dlt * / 2)) dlt).
apply (Rplus_le_compat_l br (- Rmax m0 (br - dlt * / 2)) (- (br - dlt * / 2))).
apply (Ropp_le_contravar (Rmax m0 (br - dlt * / 2)) (br - dlt * / 2)).
apply (Rmax_r m0 (br - dlt * / 2)).
unfold Rminus at 1.
rewrite (Ropp_minus_distr br (dlt * / 2)).
rewrite (Rplus_comm br (dlt * / 2 - br)).
rewrite (Rplus_assoc (dlt * / 2) (- br) br).
rewrite (Rplus_opp_l br).
rewrite - {2} (eps2 dlt).
apply (Rplus_lt_compat_l (dlt * / 2) 0 (dlt * / 2)).
apply (eps2_Rgt_R0 dlt (proj1 H11)).
unfold Rmax.
elim (Rle_dec m0 (br - dlt * / 2)).
move=> H12.
unfold Rminus at 1.
rewrite (Ropp_minus_distr br (dlt * / 2)).
rewrite (Rplus_comm br (dlt * / 2 - br)).
rewrite (Rplus_assoc (dlt * / 2) (- br) br).
rewrite (Rplus_opp_l br).
left.
rewrite (Rplus_0_r (dlt * / 2)).
apply (eps2_Rgt_R0 dlt (proj1 H11)).
move=> H12.
apply (Rge_minus br m0).
left.
apply H7.
apply (proj2 (limit_inf_R_extend_same R_met f (fun r : R => r < br) br)).
suff: ((forall r : R, Rval (f r) = (fun (r : Rextend) => Rval (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (Rval r))).
move=> H10.
suff: (limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun r : Rextend => exists l : R, In R (fun r0 : R => r0 < br) l /\ r = Rval l) (Rval br) Rinf).
move=> H11 eps H12.
elim (proj2 (limit_in_R_R_extend_same_1 Rextend_met (fun r : Base R_met => Rval (f r)) (RextendFunUnWrapRextend f) (fun r : R => r < br) br Rinf H10) H11 eps H12).
move=> dlt H13.
exists dlt.
apply conj.
apply H13.
apply (proj2 H13).
move=> eps H11.
elim (H9 eps H11).
move=> dlt H12.
exists dlt.
apply conj.
apply (proj1 H12).
move=> x H13.
apply (proj2 H12 x).
elim (proj1 H13).
move=> l H14.
apply conj.
rewrite (proj2 H14).
apply (proj1 H14).
apply (proj2 H13).
move=> r.
reflexivity.
move=> H7 H8.
apply False_ind.
apply H8.
move=> Mr.
elim b.
move=> H7 H8 H9.
suff: (limit_R_inf R_met f (Full_set R) Mr).
move=> H10.
elim (H10 (Mr - y)).
move=> M0 H11.
exists (Rmax m0 M0).
apply conj.
suff: (Rextendlt a (Rval m0)).
elim a.
apply.
apply.
move=> r H12.
apply (Rlt_le_trans r m0 (Rmax m0 M0)).
apply H12.
apply (Rmax_l m0 M0).
apply (proj1 H6).
apply conj.
apply I.
apply conj.
apply (Rmax_l m0 M0).
apply (Ropp_lt_cancel y (f (Rmax m0 M0))).
apply (Rplus_lt_reg_l Mr (- f (Rmax m0 M0)) (- y)).
apply (Rle_lt_trans (Mr + - f (Rmax m0 M0)) (dist R_met (f (Rmax m0 M0)) Mr) (Mr + - y)).
rewrite (dist_sym R_met (f (Rmax m0 M0)) Mr).
apply (Rle_abs (Mr + - f (Rmax m0 M0))).
apply (H11 (Rmax m0 M0)).
apply conj.
apply (Full_intro R (Rmax m0 M0)).
apply (Rle_ge M0 (Rmax m0 M0)).
apply (Rmax_r m0 M0).
apply (Rgt_minus Mr y).
apply H8.
suff: ((forall r : R, f r = (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (Rval r))).
move=> H10.
apply (proj2 (limit_R_inf_extend_same R_met f (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (Full_set R) Mr H10)).
apply (proj2 (limit_in_R_R_extend_same_2 Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (fun (r : Rextend) => exists l : R, In R (Full_set R) l /\ r = Rval l) Rinf Mr)).
move=> eps H11.
elim (H9 eps H11).
move=> dlt H12.
exists dlt.
apply conj.
apply (proj1 H12).
move=> x H13.
apply (proj2 H12 x).
apply conj.
elim (proj1 H13).
move=> l H14.
rewrite (proj2 H14).
apply I.
apply (proj2 H13).
move=> r.
reflexivity.
move=> H7.
apply False_ind.
apply H7.
move=> br H7 H8 H9.
suff: (limit_in R_met R_met f (fun (r : R) => r < br) br Mr).
move=> H10.
elim (H10 (Mr - y)).
move=> dlt H11.
exists (Rmax m0 (br - dlt * / 2)).
apply conj.
suff: (Rextendlt a (Rval m0)).
elim a.
apply.
apply.
move=> r H12.
apply (Rlt_le_trans r m0 (Rmax m0 (br - dlt * / 2))).
apply H12.
apply (Rmax_l m0 (br - dlt * / 2)).
apply (proj1 H6).
apply conj.
unfold Rmax.
elim (Rle_dec m0 (br - dlt * / 2)).
move=> H12.
rewrite - {2} (Rplus_0_r br).
apply (Rplus_lt_compat_l br (- (dlt * / 2)) 0).
apply (Ropp_lt_gt_0_contravar (dlt * / 2)).
apply (eps2_Rgt_R0 dlt (proj1 H11)).
move=> H12.
apply H7.
apply conj.
apply (Rmax_l m0 (br - dlt * / 2)).
apply (Ropp_lt_cancel y (f (Rmax m0 (br - dlt * / 2)))).
apply (Rplus_lt_reg_l Mr (- f (Rmax m0 (br - dlt * / 2))) (- y)).
apply (Rle_lt_trans (Mr + - f (Rmax m0 (br - dlt * / 2))) (dist R_met (f (Rmax m0 (br - dlt * / 2))) Mr) (Mr + - y)).
unfold dist.
unfold R_met.
unfold R_dist.
rewrite (Rabs_minus_sym (f (Rmax m0 (br - dlt * / 2))) Mr).
apply (Rle_abs (Mr + - f (Rmax m0 (br - dlt * / 2)))).
apply (proj2 H11 (Rmax m0 (br - dlt * / 2))).
apply  conj.
unfold Rmax.
elim (Rle_dec m0 (br - dlt * / 2)).
move=> H12.
rewrite - {2} (Rplus_0_r br).
apply (Rplus_lt_compat_l br (- (dlt * / 2)) 0).
apply (Ropp_lt_gt_0_contravar (dlt * / 2)).
apply (eps2_Rgt_R0 dlt (proj1 H11)).
move=> H12.
apply H7.
unfold dist.
unfold R_met.
unfold R_dist.
rewrite (Rabs_minus_sym (Rmax m0 (br - dlt * / 2)) br).
rewrite (Rabs_right (br - Rmax m0 (br - dlt * / 2))).
apply (Rle_lt_trans (br - Rmax m0 (br - dlt * / 2)) (br - (br - dlt * / 2)) dlt).
apply (Rplus_le_compat_l br (- Rmax m0 (br - dlt * / 2)) (- (br - dlt * / 2))).
apply (Ropp_le_contravar (Rmax m0 (br - dlt * / 2)) (br - dlt * / 2)).
apply (Rmax_r m0 (br - dlt * / 2)).
unfold Rminus at 1.
rewrite (Ropp_minus_distr br (dlt * / 2)).
rewrite (Rplus_comm br (dlt * / 2 - br)).
rewrite (Rplus_assoc (dlt * / 2) (- br) br).
rewrite (Rplus_opp_l br).
rewrite - {2} (eps2 dlt).
apply (Rplus_lt_compat_l (dlt * / 2) 0 (dlt * / 2)).
apply (eps2_Rgt_R0 dlt (proj1 H11)).
unfold Rmax.
elim (Rle_dec m0 (br - dlt * / 2)).
move=> H12.
unfold Rminus at 1.
rewrite (Ropp_minus_distr br (dlt * / 2)).
rewrite (Rplus_comm br (dlt * / 2 - br)).
rewrite (Rplus_assoc (dlt * / 2) (- br) br).
rewrite (Rplus_opp_l br).
rewrite (Rplus_0_r (dlt * / 2)).
left.
apply (eps2_Rgt_R0 dlt (proj1 H11)).
move=> H12.
left.
apply (Rgt_minus br m0).
apply H7.
apply (Rgt_minus Mr y).
apply H8.
apply (proj2 (limit_in_R_R_extend_same_2 R_met f (fun r : R => r < br) br Mr)).
suff: (forall (r : R), (fun (r : R) => Rval (f r)) r = (RextendFunUnWrapRextend f) (Rval r)).
move=> H10.
apply (proj2 (limit_in_R_R_extend_same_1 Rextend_met (fun (r : Base R_met) => Rval (f r)) (RextendFunUnWrapRextend f) (fun (r : R) => r < br) br (Rval Mr) H10)).
move=> eps H11.
elim (H9 eps H11).
move=> dlt H12.
exists dlt.
apply conj.
apply (proj1 H12).
move=> x H13.
apply (proj2 H12 x).
apply conj.
elim (proj1 H13).
move=> l H14.
rewrite (proj2 H14).
apply (proj1 H14).
apply (proj2 H13).
move=> r.
reflexivity.
apply (proj1 (proj2 H6)).
apply (proj2 H5).
apply H4.
suff: (Rextendlt a b).
suff: (limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun r : Rextend => Rextendlt a r) a m).
suff: (Rextendlt m (Rval y)).
elim a.
move=> H6 H7 H8.
apply False_ind.
apply H8.
elim b.
elim m.
move=> H6.
apply False_ind.
apply H6.
move=> H6 H7 H8.
suff: (limit_minf_minf f (Full_set R)).
move=> H9.
elim (H9 (y - 1)).
move=> m0 H10.
exists m0.
apply conj.
apply I.
apply conj.
apply I.
apply (Rle_lt_trans (f m0) (y - 1) y).
apply (H10 m0).
apply conj.
apply (Full_intro R m0).
right.
reflexivity.
rewrite - {2} (Rplus_0_r y).
apply (Rplus_lt_compat_l y (- 1) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
suff: (forall (r : R), Rval (f r) = (RextendFunUnWrapRextend f) (Rval r)).
move=> H9.
apply (proj2 (limit_minf_minf_extend_same f (RextendFunUnWrapRextend f) (Full_set R) H9)).
move=> eps H10.
elim (H7 eps H10).
move=> dlt H11.
exists dlt.
apply conj.
apply (proj1 H11).
move=> x H12.
apply (proj2 H11 x).
apply conj.
elim (proj1 H12).
move=> l H13.
rewrite (proj2 H13).
apply I.
apply (proj2 H12).
move=> r.
reflexivity.
move=> ar.
move=> H6 H7 H8.
suff: (limit_R_minf R_met f (Full_set R) ar).
move=> H9.
elim (H9 (y - ar)).
move=> m0 H10.
exists m0.
apply conj.
apply I.
apply conj.
apply I.
apply (Rplus_lt_reg_r (- ar) (f m0) y).
apply (Rle_lt_trans (f m0 - ar) (dist R_met (f m0) ar) (y - ar)).
apply (Rle_abs (f m0 - ar)).
apply (H10 m0).
apply conj.
apply (Full_intro R m0).
right.
reflexivity.
apply (Rgt_minus y ar).
apply H6.
suff: (forall (r : R), f r = (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (Rval r)).
move=> H9.
apply (proj2 (limit_R_minf_extend_same R_met f (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (Full_set R) ar H9)).
apply (proj2 (limit_in_R_R_extend_same_2 Rextend_met (fun r : Rextend => match r with
| Rval r0 => f r0
| _ => 0
end) (fun r : Rextend => exists l : R, In R (Full_set R) l /\ r = Rval l) Rminf ar)).
move=> eps H10.
elim (H7 eps H10).
move=> dlt H11.
exists dlt.
apply conj.
apply (proj1 H11).
move=> x H12.
apply (proj2 H11 x).
apply conj.
elim (proj1 H12).
move=> l H13.
rewrite (proj2 H13).
apply I.
apply (proj2 H12).
move=> r.
reflexivity.
move=> H6 H7 H8.
apply False_ind.
apply H8.
move=> br.
elim m.
move=> H6.
apply False_ind.
apply H6.
move=> H6 H7 H8.
suff: (limit_minf_minf f (Full_set R)).
move=> H9.
elim (H9 (y - 1)).
move=> m0 H10.
exists (Rmin (br - 1) m0).
apply conj.
apply I.
apply conj.
apply (Rle_lt_trans (Rmin (br - 1) m0) (br - 1) br).
apply (Rmin_l (br - 1) m0).
rewrite - {2} (Rplus_0_r br).
apply (Rplus_lt_compat_l br (- 1) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply (Rle_lt_trans (f (Rmin (br - 1) m0)) (y - 1) y).
apply (H10 (Rmin (br - 1) m0)).
apply conj.
apply (Full_intro R (Rmin (br - 1) m0)).
apply (Rmin_r (br - 1) m0).
rewrite - {2} (Rplus_0_r y).
apply (Rplus_lt_compat_l y (- 1) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
suff: (forall (r : R), Rval (f r) = (RextendFunUnWrapRextend f) (Rval r)).
move=> H9.
apply (proj2 (limit_minf_minf_extend_same f (RextendFunUnWrapRextend f) (Full_set R) H9)).
move=> eps H10.
elim (H7 eps H10).
move=> dlt H11.
exists dlt.
apply conj.
apply (proj1 H11).
move=> x H12.
apply (proj2 H11 x).
apply conj.
elim (proj1 H12).
move=> l H13.
rewrite (proj2 H13).
apply I.
apply (proj2 H12).
move=> r.
reflexivity.
move=> mr H6 H7 H8.
suff: (limit_R_minf R_met f (Full_set R) mr).
move=> H9.
elim (H9 (y - mr)).
move=> m0 H10.
exists (Rmin m0 (br - 1)).
apply conj.
apply I.
apply conj.
apply (Rle_lt_trans (Rmin m0 (br - 1)) (br - 1) br).
apply (Rmin_r m0 (br - 1)).
rewrite - {2} (Rplus_0_r br).
apply (Rplus_lt_compat_l br (- 1) 0).
apply (Ropp_lt_gt_0_contravar 1).
apply Rlt_0_1.
apply (Rplus_lt_reg_r (- mr) (f (Rmin m0 (br - 1))) y).
apply (Rle_lt_trans (f (Rmin m0 (br - 1)) + - mr) (dist R_met (f (Rmin m0 (br - 1))) mr) (y + - mr)).
apply (Rle_abs (f (Rmin m0 (br - 1)) + - mr)).
apply (H10 (Rmin m0 (br - 1))).
apply conj.
apply (Full_intro R (Rmin m0 (br - 1))).
apply (Rmin_l m0 (br - 1)).
apply (Rgt_minus y mr H6).
suff: (forall (r : R), f r = (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (Rval r)).
move=> H9.
apply (proj2 (limit_R_minf_extend_same R_met f (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (Full_set R) mr H9)).
apply (proj2 (limit_in_R_R_extend_same_2 Rextend_met (fun r : Rextend => match r with
| Rval r0 => f r0
| _ => 0
end) (fun r : Rextend => exists l : R, In R (Full_set R) l /\ r = Rval l) Rminf mr)).
move=> eps H10.
elim (H7 eps H10).
move=> dlt H11.
exists dlt.
apply conj.
apply (proj1 H11).
move=> x H12.
apply (proj2 H11).
apply conj.
elim (proj1 H12).
move=> l H13.
rewrite (proj2 H13).
apply I.
apply (proj2 H12).
move=> r.
reflexivity.
move=> ar.
elim m.
move=> H6.
apply False_ind.
apply H6.
move=> H6 H7.
suff: (limit_minf_R R_met f (fun (r : R) => ar < r) ar).
move=> H8.
elim (H8 y).
move=> dlt H9.
elim b.
move=> H10.
exists (ar + dlt * / 2).
apply conj.
rewrite - {1} (Rplus_0_r ar).
apply (Rplus_lt_compat_l ar 0 (dlt * / 2)).
apply (eps2_Rgt_R0 dlt (proj1 H9)).
apply conj.
apply I.
apply (proj2 H9 (ar + dlt * / 2)).
apply conj.
rewrite - {1} (Rplus_0_r ar).
apply (Rplus_lt_compat_l ar 0 (dlt * / 2)).
apply (eps2_Rgt_R0 dlt (proj1 H9)).
unfold dist.
unfold R_met.
unfold R_dist.
rewrite (Rplus_comm ar (dlt * / 2)).
unfold Rminus.
rewrite (Rplus_assoc (dlt * / 2) ar (- ar)).
rewrite (Rplus_opp_r ar).
rewrite (Rplus_0_r (dlt * / 2)).
rewrite (Rabs_right (dlt * / 2)).
rewrite - (Rplus_0_r (dlt * / 2)).
rewrite - {2} (eps2 dlt).
apply (Rplus_lt_compat_l (dlt * / 2) 0 (dlt * / 2)).
apply (eps2_Rgt_R0 dlt (proj1 H9)).
left.
apply (eps2_Rgt_R0 dlt (proj1 H9)).
move=> H10.
apply False_ind.
apply H10.
move=> br H10.
exists (ar + (Rmin dlt (br - ar)) * / 2).
apply conj.
rewrite - {1} (Rplus_0_r ar).
apply (Rplus_lt_compat_l ar 0 (Rmin dlt (br - ar) * / 2)).
apply (eps2_Rgt_R0 (Rmin dlt (br - ar))).
unfold Rmin.
elim (Rle_dec dlt (br - ar)).
move=> H11.
apply (proj1 H9).
move=> H11.
apply (Rgt_minus br ar H10).
apply conj.
apply (Rle_lt_trans (ar + Rmin dlt (br - ar) * / 2) (ar + (br - ar) * / 2) br).
apply (Rplus_le_compat_l ar (Rmin dlt (br - ar) * / 2) ((br - ar) * / 2)).
apply (Rmult_le_compat_r (/ 2) (Rmin dlt (br - ar)) (br - ar)).
left.
apply (Rinv_0_lt_compat 2 Two_Gt_Zero).
apply (Rmin_r dlt (br - ar)).
suff: (br = ar + (br - ar)).
move=> H11.
rewrite {2} H11.
apply (Rplus_lt_compat_l ar ((br - ar) * / 2) (br - ar)).
rewrite - (Rplus_0_r ((br - ar) * / 2)).
rewrite - {2} (eps2 (br - ar)).
apply (Rplus_lt_compat_l ((br - ar) * / 2) 0 ((br - ar) * / 2)).
apply (eps2_Rgt_R0 (br - ar)).
apply (Rgt_minus br ar H10).
rewrite (Rplus_comm ar (br - ar)).
rewrite (Rplus_assoc br (- ar) ar).
rewrite (Rplus_opp_l ar).
rewrite (Rplus_0_r br).
reflexivity.
apply (proj2 H9 (ar + Rmin dlt (br - ar) * / 2)).
apply conj.
rewrite - {1} (Rplus_0_r ar).
apply (Rplus_lt_compat_l ar 0 (Rmin dlt (br - ar) * / 2)).
apply (eps2_Rgt_R0 (Rmin dlt (br - ar))).
unfold Rmin.
elim (Rle_dec dlt (br - ar)).
move=> H11.
apply (proj1 H9).
move=> H11.
apply (Rgt_minus br ar H10).
unfold dist.
unfold R_met.
unfold R_dist.
rewrite (Rplus_comm ar (Rmin dlt (br - ar) * / 2)).
unfold Rminus.
rewrite (Rplus_assoc (Rmin dlt (br - ar) * / 2) ar (- ar)).
rewrite (Rplus_opp_r ar).
rewrite (Rplus_0_r (Rmin dlt (br - ar) * / 2)).
rewrite (Rabs_right (Rmin dlt (br - ar) * / 2)).
apply (Rle_lt_trans (Rmin dlt (br - ar) * / 2) (dlt * / 2) dlt).
apply (Rmult_le_compat_r (/ 2) (Rmin dlt (br - ar)) dlt).
left.
apply (Rinv_0_lt_compat 2 Two_Gt_Zero).
apply (Rmin_l dlt (br - ar)).
rewrite - (Rplus_0_r (dlt * / 2)).
rewrite - {2} (eps2 dlt).
apply (Rplus_lt_compat_l (dlt * / 2) 0 (dlt * / 2)).
apply (eps2_Rgt_R0 dlt (proj1 H9)).
left.
apply (eps2_Rgt_R0 (Rmin dlt (br - ar))).
unfold Rmin.
elim (Rle_dec dlt (br - ar)).
move=> H11.
apply (proj1 H9).
move=> H11.
apply (Rgt_minus br ar H10).
apply (proj2 (limit_minf_R_extend_same R_met f (fun r : R => ar < r) ar)).
suff: (forall (r : R), (fun r : Base R_met => Rval (f r)) r = (RextendFunUnWrapRextend f) (Rval r)).
move=> H8.
apply (proj2 (limit_in_R_R_extend_same_1 Rextend_met (fun r : Base R_met => Rval (f r)) (RextendFunUnWrapRextend f) (fun r : R => ar < r) ar Rminf H8)).
move=> eps H9.
elim (H7 eps H9).
move=> dlt H10.
exists dlt.
apply conj.
apply (proj1 H10).
move=> x H11.
apply (proj2 H10 x).
apply conj.
elim (proj1 H11).
move=> l H12.
rewrite (proj2 H12).
apply (proj1 H12).
apply (proj2 H11).
move=> r.
reflexivity.
move=> mr H6 H7.
elim b.
move=> H8.
suff: (limit_in R_met R_met f (fun (r : R) => ar < r) ar mr).
move=> H9.
elim (H9 (y - mr)).
move=> dlt H10.
exists (ar + (dlt * / 2)).
apply conj.
rewrite - {1} (Rplus_0_r ar).
apply (Rplus_lt_compat_l ar 0 (dlt * / 2)).
apply (eps2_Rgt_R0 dlt (proj1 H10)).
apply conj.
apply I.
apply (Rplus_lt_reg_r (- mr) (f (ar + dlt * / 2)) y).
apply (Rle_lt_trans (f (ar + dlt * / 2) + - mr) (dist R_met (f (ar + dlt * / 2)) mr) (y - mr)).
apply (Rle_abs (f (ar + dlt * / 2) - mr)).
apply (proj2 H10 (ar + dlt * / 2)).
apply conj.
rewrite - {1} (Rplus_0_r ar).
apply (Rplus_lt_compat_l ar 0 (dlt * / 2)).
apply (eps2_Rgt_R0 dlt (proj1 H10)).
unfold dist.
unfold R_met.
unfold R_dist.
rewrite (Rplus_comm ar (dlt * / 2)).
unfold Rminus.
rewrite (Rplus_assoc (dlt * / 2) ar (- ar)).
rewrite (Rplus_opp_r ar).
rewrite (Rplus_0_r (dlt * / 2)).
rewrite (Rabs_right (dlt * / 2)).
rewrite - (Rplus_0_r (dlt * / 2)).
rewrite - {2} (eps2 dlt).
apply (Rplus_lt_compat_l (dlt * / 2) 0 (dlt * / 2)).
apply (eps2_Rgt_R0 dlt (proj1 H10)).
left.
apply (eps2_Rgt_R0 dlt (proj1 H10)).
apply (Rgt_minus y mr H6).
apply (proj2 (limit_in_R_R_extend_same_2 R_met f (fun r : R => ar < r) ar mr)).
suff: (forall (r : R), (fun (r : Base R_met) => Rval (f r)) r = (RextendFunUnWrapRextend f) (Rval r)).
move=> H9.
apply (proj2 (limit_in_R_R_extend_same_1 Rextend_met (fun r : Base R_met => Rval (f r)) (RextendFunUnWrapRextend f) (fun r : R => ar < r) ar (Rval mr) H9)).
move=> eps H10.
elim (H7 eps H10).
move=> dlt H11.
exists dlt.
apply conj.
apply (proj1 H11).
move=> x H12.
apply (proj2 H11).
apply conj.
elim (proj1 H12).
move=> l H13.
rewrite (proj2 H13).
apply (proj1 H13).
apply (proj2 H12).
move=> r.
reflexivity.
move=> H8.
apply False_ind.
apply H8.
move=> br H8.
suff: (limit_in R_met R_met f (fun (r : R) => ar < r) ar mr).
move=> H9.
elim (H9 (y - mr)).
move=> dlt H10.
exists (ar + ((Rmin dlt (br - ar)) * / 2)).
apply conj.
rewrite - {1} (Rplus_0_r ar).
apply (Rplus_lt_compat_l ar 0 (Rmin dlt (br - ar) * / 2)).
apply (eps2_Rgt_R0 (Rmin dlt (br - ar))).
unfold Rmin.
elim (Rle_dec dlt (br - ar)).
move=> H11.
apply (proj1 H10).
move=> H11.
apply (Rgt_minus br ar H8).
apply conj.
apply (Rle_lt_trans (ar + Rmin dlt (br - ar) * / 2) (ar + (br - ar) * / 2) br).
apply (Rplus_le_compat_l ar (Rmin dlt (br - ar) * / 2) ((br - ar) * / 2)).
apply (Rmult_le_compat_r (/ 2) (Rmin dlt (br - ar)) (br - ar)).
left.
apply (Rinv_0_lt_compat 2 Two_Gt_Zero).
apply (Rmin_r dlt (br - ar)).
suff: (br = ar + (br - ar)).
move=> H11.
rewrite {2} H11.
apply (Rplus_lt_compat_l ar ((br - ar) * / 2) (br - ar)).
rewrite - (Rplus_0_r ((br - ar) * / 2)).
rewrite - {2} (eps2 (br - ar)).
apply (Rplus_lt_compat_l ((br - ar) * / 2) 0 ((br - ar) * / 2)).
apply (eps2_Rgt_R0 (br - ar)).
apply (Rgt_minus br ar H8).
rewrite (Rplus_comm ar (br - ar)).
rewrite (Rplus_assoc br (- ar) ar).
rewrite (Rplus_opp_l ar).
rewrite (Rplus_0_r br).
reflexivity.
apply (Rplus_lt_reg_r (- mr) (f (ar + Rmin dlt (br - ar) * / 2)) y).
apply (Rle_lt_trans (f (ar + Rmin dlt (br - ar) * / 2) + - mr) (dist R_met (f (ar + Rmin dlt (br - ar) * / 2)) mr) (y - mr)).
apply (Rle_abs (f (ar + Rmin dlt (br - ar) * / 2) - mr)).
apply (proj2 H10 (ar + Rmin dlt (br - ar) * / 2)).
apply conj.
rewrite - {1} (Rplus_0_r ar).
apply (Rplus_lt_compat_l ar 0 (Rmin dlt (br - ar) * / 2)).
apply (eps2_Rgt_R0 (Rmin dlt (br - ar))).
unfold Rmin.
elim (Rle_dec dlt (br - ar)).
move=> H11.
apply (proj1 H10).
move=> H11.
apply (Rgt_minus br ar H8).
unfold dist.
unfold R_met.
unfold R_dist.
rewrite (Rplus_comm ar (Rmin dlt (br - ar) * / 2)).
unfold Rminus.
rewrite (Rplus_assoc (Rmin dlt (br - ar) * / 2) ar (- ar)).
rewrite (Rplus_opp_r ar).
rewrite (Rplus_0_r (Rmin dlt (br - ar) * / 2)).
rewrite (Rabs_right (Rmin dlt (br - ar) * / 2)).
apply (Rlt_le_trans (Rmin dlt (br - ar) * / 2) (Rmin dlt (br - ar)) dlt).
rewrite - (Rplus_0_r (Rmin dlt (br - ar) * / 2)).
rewrite - {2} (eps2 (Rmin dlt (br - ar))).
apply (Rplus_lt_compat_l (Rmin dlt (br - ar) * / 2) 0 (Rmin dlt (br - ar) * / 2)).
apply (eps2_Rgt_R0 (Rmin dlt (br - ar))).
unfold Rmin.
elim (Rle_dec dlt (br - ar)).
move=> H11.
apply (proj1 H10).
move=> H11.
apply (Rgt_minus br ar H8).
apply (Rmin_l dlt (br - ar)).
left.
apply (eps2_Rgt_R0 (Rmin dlt (br - ar))).
unfold Rmin.
elim (Rle_dec dlt (br - ar)).
move=> H11.
apply (proj1 H10).
move=> H11.
apply (Rgt_minus br ar H8).
apply (Rgt_minus y mr H6).
apply (proj2 (limit_in_R_R_extend_same_2 R_met f (fun r : R => ar < r) ar mr)).
suff: (forall (r : R), (fun (r : Base R_met) => Rval (f r)) r = (RextendFunUnWrapRextend f) (Rval r)).
move=> H9.
apply (proj2 (limit_in_R_R_extend_same_1 Rextend_met (fun r : Base R_met => Rval (f r)) (RextendFunUnWrapRextend f) (fun r : R => ar < r) ar (Rval mr) H9)).
move=> eps H10.
elim (H7 eps H10).
move=> dlt H11.
exists dlt.
apply conj.
apply (proj1 H11).
move=> x H12.
apply (proj2 H11).
apply conj.
elim (proj1 H12).
move=> l H13.
rewrite (proj2 H13).
apply (proj1 H13).
apply (proj2 H12).
move=> r.
reflexivity.
apply (proj1 H5).
apply H3.
apply H1.
Qed.

Lemma Theorem_8_1_corollary_3_1 : forall (f : R -> R) (a b : R), a < b -> (forall (x : R), a < x -> x < b -> ContinuousMet R_met R_met f (Full_set R) x) -> forall (m M : R), limit_in R_met R_met f (fun (r : R) => a < r) a m -> limit_in R_met R_met f (fun (r : R) => r < b) b M -> forall (y : R), ((m < y /\ y < M) \/ (M < y /\ y < m)) -> exists (x : R), a < x /\ x < b /\ y = f x.
Proof.
move=> f a b H1 H2 m M H3 H4 y H5.
suff: (limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun r : Rextend => Rextendlt (Rval a) r) (Rval a) (Rval m)).
move=> H6.
suff: (limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun r : Rextend => Rextendlt r (Rval b)) (Rval b) (Rval M)).
move=> H7.
elim (Theorem_8_1_corollary_3_sub f (Rval a) (Rval b) H1 H2 (Rval m) (Rval M) H6 H7 y H5).
move=> x H8.
exists x.
apply H8.
apply (proj1 (limit_in_R_R_extend_same_2 Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (fun (r : Rextend) => Rextendlt r (Rval b)) (Rval b) M)).
suff: (limit_in Rextend_met R_met (fun (r : Rextend) => match r with
  | Rval r0 => f r0
  | _ => 0
end) (fun r : Rextend => exists l : R, In R (fun r : R => r < b) l /\ r = Rval l) (Rval b) M).
move=> H7 eps H8.
elim (H7 eps H8).
move=> dlt H9.
exists (Rmin dlt ((dist Rextend_met Rminf (Rval b)) * / 2)).
apply conj.
unfold Rmin.
elim (Rle_dec dlt (dist Rextend_met Rminf (Rval b) * / 2)).
move=> H10.
apply (proj1 H9).
move=> H10.
apply (eps2_Rgt_R0 (dist Rextend_met Rminf (Rval b))).
elim (dist_pos Rextend_met Rminf (Rval b)).
apply.
move=> H11.
apply False_ind.
suff: (Rextendlt Rminf Rminf).
apply.
suff: (Rminf = (Rval b)).
move=> H12.
rewrite {2} H12.
apply I.
apply (proj1 (dist_refl Rextend_met Rminf (Rval b))).
apply H11.
elim.
move=> H10.
apply False_ind.
apply (proj1 H10).
move=> H10.
apply False_ind.
apply (Rle_not_lt (dist Rextend_met Rminf (Rval b)) (Rmin dlt (dist Rextend_met Rminf (Rval b) * / 2))).
apply (Rle_trans (Rmin dlt (dist Rextend_met Rminf (Rval b) * / 2)) (dist Rextend_met Rminf (Rval b) * / 2) (dist Rextend_met Rminf (Rval b))).
apply (Rmin_r dlt (dist Rextend_met Rminf (Rval b) * / 2)).
rewrite - (Rplus_0_r (dist Rextend_met Rminf (Rval b) * / 2)).
rewrite - {2} (eps2 (dist Rextend_met Rminf (Rval b))).
apply (Rplus_le_compat_l (dist Rextend_met Rminf (Rval b) * / 2) 0 (dist Rextend_met Rminf (Rval b) * / 2)).
rewrite - (Rmult_0_l (/ 2)).
apply (Rmult_le_compat_r (/ 2) 0 (dist Rextend_met Rminf (Rval b))).
left.
apply (Rinv_0_lt_compat 2 Two_Gt_Zero).
apply (Rge_le (dist Rextend_met Rminf (Rval b)) 0).
apply (dist_pos Rextend_met Rminf (Rval b)).
apply (proj2 H10).
move=> x H10.
apply (proj2 H9 (Rval x)).
apply conj.
exists x.
apply conj.
apply (proj1 H10).
reflexivity.
apply (Rlt_le_trans (dist Rextend_met (Rval x) (Rval b)) (Rmin dlt (dist Rextend_met Rminf (Rval b) * / 2)) dlt).
apply (proj2 H10).
apply (Rmin_l dlt (dist Rextend_met Rminf (Rval b) * / 2)).
apply (limit_in_R_R_extend_same_1 R_met f (fun r : Rextend => match r with
  | Rval r0 => f r0
  | _ => 0
end)).
move=> r.
reflexivity.
apply H4.
apply (proj1 (limit_in_R_R_extend_same_2 Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (fun (r : Rextend) => Rextendlt (Rval a) r) (Rval a) m)).
suff: (limit_in Rextend_met R_met (fun (r : Rextend) => match r with
  | Rval r0 => f r0
  | _ => 0
end) (fun (r : Rextend) => exists l : R, In R (fun (r : R) => a < r) l /\ r = Rval l) (Rval a) m).
move=> H6 eps H7.
elim (H6 eps H7).
move=> dlt H8.
exists (Rmin dlt ((dist Rextend_met Rinf (Rval a)) * / 2)).
apply conj.
unfold Rmin.
elim (Rle_dec dlt (dist Rextend_met Rinf (Rval a) * / 2)).
move=> H9.
apply (proj1 H8).
move=> H9.
apply (eps2_Rgt_R0 (dist Rextend_met Rinf (Rval a))).
elim (dist_pos Rextend_met Rinf (Rval a)).
apply.
move=> H10.
apply False_ind.
suff: (Rextendlt Rinf Rinf).
apply.
suff: (Rinf = (Rval a)).
move=> H11.
rewrite {1} H11.
apply I.
apply (proj1 (dist_refl Rextend_met Rinf (Rval a))).
apply H10.
elim.
move=> H9.
apply False_ind.
apply (Rle_not_lt (dist Rextend_met Rinf (Rval a)) (Rmin dlt (dist Rextend_met Rinf (Rval a) * / 2))).
apply (Rle_trans (Rmin dlt (dist Rextend_met Rinf (Rval a) * / 2)) (dist Rextend_met Rinf (Rval a) * / 2) (dist Rextend_met Rinf (Rval a))).
apply (Rmin_r dlt (dist Rextend_met Rinf (Rval a) * / 2)).
rewrite - (Rplus_0_r (dist Rextend_met Rinf (Rval a) * / 2)).
rewrite - {2} (eps2 (dist Rextend_met Rinf (Rval a))).
apply (Rplus_le_compat_l (dist Rextend_met Rinf (Rval a) * / 2) 0 (dist Rextend_met Rinf (Rval a) * / 2)).
rewrite - (Rmult_0_l (/ 2)).
apply (Rmult_le_compat_r (/ 2) 0 (dist Rextend_met Rinf (Rval a))).
left.
apply (Rinv_0_lt_compat 2 Two_Gt_Zero).
apply (Rge_le (dist Rextend_met Rinf (Rval a)) 0).
apply (dist_pos Rextend_met Rinf (Rval a)).
apply (proj2 H9).
move=> H9.
apply False_ind.
apply (proj1 H9).
move=> x H9.
apply (proj2 H8 (Rval x)).
apply conj.
exists x.
apply conj.
apply (proj1 H9).
reflexivity.
apply (Rlt_le_trans (dist Rextend_met (Rval x) (Rval a)) (Rmin dlt (dist Rextend_met Rinf (Rval a) * / 2)) dlt).
apply (proj2 H9).
apply (Rmin_l dlt (dist Rextend_met Rinf (Rval a) * / 2)).
apply (limit_in_R_R_extend_same_1 R_met f (fun r : Rextend => match r with
  | Rval r0 => f r0
  | _ => 0
end)).
move=> r.
reflexivity.
apply H3.
Qed.

Lemma Theorem_8_1_corollary_3_2 : forall (f : R -> R) (b : R), (forall (x : R), x < b -> ContinuousMet R_met R_met f (Full_set R) x) -> forall (m M : R), limit_R_minf R_met f (Full_set R) m -> limit_in R_met R_met f (fun (r : R) => r < b) b M -> forall (y : R), ((m < y /\ y < M) \/ (M < y /\ y < m)) -> exists (x : R), x < b /\ y = f x.
Proof.
move=> f b H1 m M H2 H3 y H4.
suff: (limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun r : Rextend => Rextendlt Rminf r) Rminf (Rval m)).
move=> H5.
suff: (limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun r : Rextend => Rextendlt r (Rval b)) (Rval b) (Rval M)).
move=> H6.
suff: (Rextendlt Rminf (Rval b)).
move=> H7.
suff: (forall (x : R), Rextendlt Rminf (Rval x) -> Rextendlt (Rval x) (Rval b) -> ContinuousMet R_met R_met f (Full_set R) x).
move=> H8.
elim (Theorem_8_1_corollary_3_sub f Rminf (Rval b) H7 H8 (Rval m) (Rval M) H5 H6 y H4).
move=> x H9.
exists x.
apply (proj2 H9).
move=> x H8 H9.
apply (H1 x).
apply H9.
apply I.
apply (proj1 (limit_in_R_R_extend_same_2 Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (fun (r : Rextend) => Rextendlt r (Rval b)) (Rval b) M)).
suff: (limit_in Rextend_met R_met (fun (r : Rextend) => match r with
  | Rval r0 => f r0
  | _ => 0
end) (fun r : Rextend => exists l : R, In R (fun r : R => r < b) l /\ r = Rval l) (Rval b) M).
move=> H6 eps H7.
elim (H6 eps H7).
move=> dlt H8.
exists (Rmin dlt ((dist Rextend_met Rminf (Rval b)) * / 2)).
apply conj.
unfold Rmin.
elim (Rle_dec dlt (dist Rextend_met Rminf (Rval b) * / 2)).
move=> H9.
apply (proj1 H8).
move=> H9.
apply (eps2_Rgt_R0 (dist Rextend_met Rminf (Rval b))).
elim (dist_pos Rextend_met Rminf (Rval b)).
apply.
move=> H10.
apply False_ind.
suff: (Rextendlt Rminf Rminf).
apply.
suff: (Rminf = (Rval b)).
move=> H11.
rewrite {2} H11.
apply I.
apply (proj1 (dist_refl Rextend_met Rminf (Rval b))).
apply H10.
elim.
move=> H9.
apply False_ind.
apply (proj1 H9).
move=> H9.
apply False_ind.
apply (Rle_not_lt (dist Rextend_met Rminf (Rval b)) (Rmin dlt (dist Rextend_met Rminf (Rval b) * / 2))).
apply (Rle_trans (Rmin dlt (dist Rextend_met Rminf (Rval b) * / 2)) (dist Rextend_met Rminf (Rval b) * / 2) (dist Rextend_met Rminf (Rval b))).
apply (Rmin_r dlt (dist Rextend_met Rminf (Rval b) * / 2)).
rewrite - (Rplus_0_r (dist Rextend_met Rminf (Rval b) * / 2)).
rewrite - {2} (eps2 (dist Rextend_met Rminf (Rval b))).
apply (Rplus_le_compat_l (dist Rextend_met Rminf (Rval b) * / 2) 0 (dist Rextend_met Rminf (Rval b) * / 2)).
rewrite - (Rmult_0_l (/ 2)).
apply (Rmult_le_compat_r (/ 2) 0 (dist Rextend_met Rminf (Rval b))).
left.
apply (Rinv_0_lt_compat 2 Two_Gt_Zero).
apply (Rge_le (dist Rextend_met Rminf (Rval b)) 0).
apply (dist_pos Rextend_met Rminf (Rval b)).
apply (proj2 H9).
move=> x H9.
apply (proj2 H8 (Rval x)).
apply conj.
exists x.
apply conj.
apply (proj1 H9).
reflexivity.
apply (Rlt_le_trans (dist Rextend_met (Rval x) (Rval b)) (Rmin dlt (dist Rextend_met Rminf (Rval b) * / 2)) dlt).
apply (proj2 H9).
apply (Rmin_l dlt (dist Rextend_met Rminf (Rval b) * / 2)).
apply (limit_in_R_R_extend_same_1 R_met f (fun r : Rextend => match r with
  | Rval r0 => f r0
  | _ => 0
end)).
move=> r.
reflexivity.
apply H3.
apply (proj1 (limit_in_R_R_extend_same_2 Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (fun (r : Rextend) => Rextendlt Rminf r) Rminf m)).
suff: (limit_in Rextend_met R_met (fun (r : Rextend) => match r with
  | Rval r0 => f r0
  | _ => 0
end) (fun (r : Rextend) => exists l : R, In R (Full_set R) l /\ r = Rval l) Rminf m).
move=> H5 eps H6.
elim (H5 eps H6).
move=> dlt H7.
exists (Rmin dlt ((dist Rextend_met Rinf Rminf) * / 2)).
apply conj.
unfold Rmin.
elim (Rle_dec dlt (dist Rextend_met Rinf Rminf * / 2)).
move=> H8.
apply (proj1 H7).
move=> H8.
apply (eps2_Rgt_R0 (dist Rextend_met Rinf Rminf)).
elim (dist_pos Rextend_met Rinf Rminf).
apply.
move=> H9.
apply False_ind.
suff: (Rextendlt Rinf Rinf).
apply.
suff: (Rinf = Rminf).
move=> H10.
rewrite {1} H10.
apply I.
apply (proj1 (dist_refl Rextend_met Rinf Rminf)).
apply H9.
elim.
move=> H8.
apply False_ind.
apply (Rle_not_lt (dist Rextend_met Rinf Rminf) (Rmin dlt (dist Rextend_met Rinf Rminf * / 2))).
apply (Rle_trans (Rmin dlt (dist Rextend_met Rinf Rminf * / 2)) (dist Rextend_met Rinf Rminf * / 2) (dist Rextend_met Rinf Rminf)).
apply (Rmin_r dlt (dist Rextend_met Rinf Rminf * / 2)).
rewrite - (Rplus_0_r (dist Rextend_met Rinf Rminf * / 2)).
rewrite - {2} (eps2 (dist Rextend_met Rinf Rminf)).
apply (Rplus_le_compat_l (dist Rextend_met Rinf Rminf * / 2) 0 (dist Rextend_met Rinf Rminf * / 2)).
rewrite - (Rmult_0_l (/ 2)).
apply (Rmult_le_compat_r (/ 2) 0 (dist Rextend_met Rinf Rminf)).
left.
apply (Rinv_0_lt_compat 2 Two_Gt_Zero).
apply (Rge_le (dist Rextend_met Rinf Rminf) 0).
apply (dist_pos Rextend_met Rinf Rminf).
apply (proj2 H8).
move=> H8.
apply False_ind.
apply (proj1 H8).
move=> x H8.
apply (proj2 H7 (Rval x)).
apply conj.
exists x.
apply conj.
apply (Full_intro R x).
reflexivity.
apply (Rlt_le_trans (dist Rextend_met (Rval x) Rminf) (Rmin dlt (dist Rextend_met Rinf Rminf * / 2)) dlt).
apply (proj2 H8).
apply (Rmin_l dlt (dist Rextend_met Rinf Rminf * / 2)).
apply (limit_R_minf_extend_same R_met f (fun r : Rextend => match r with
  | Rval r0 => f r0
  | _ => 0
end)).
move=> r.
reflexivity.
apply H2.
Qed.

Lemma Theorem_8_1_corollary_3_3 : forall (f : R -> R) (a : R), (forall (x : R), a < x -> ContinuousMet R_met R_met f (Full_set R) x) -> forall (m M : R), limit_in R_met R_met f (fun (r : R) => a < r) a m -> limit_R_inf R_met f (Full_set R) M -> forall (y : R), ((m < y /\ y < M) \/ (M < y /\ y < m)) -> exists (x : R), a < x /\ y = f x.
Proof.
move=> f a H1 m M H2 H3 y H4.
suff: (limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun r : Rextend => Rextendlt (Rval a) r) (Rval a) (Rval m)).
move=> H5.
suff: (limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun r : Rextend => Rextendlt r Rinf) Rinf (Rval M)).
move=> H6.
suff: (Rextendlt (Rval a) Rinf).
move=> H7.
suff: (forall (x : R), Rextendlt (Rval a) (Rval x) -> Rextendlt (Rval x) Rinf -> ContinuousMet R_met R_met f (Full_set R) x).
move=> H8.
elim (Theorem_8_1_corollary_3_sub f (Rval a) Rinf H7 H8 (Rval m) (Rval M) H5 H6 y H4).
move=> x H9.
exists x.
apply conj.
apply (proj1 H9).
apply (proj2 (proj2 H9)).
move=> x H8 H9.
apply (H1 x).
apply H8.
apply I.
apply (proj1 (limit_in_R_R_extend_same_2 Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (fun (r : Rextend) => Rextendlt r Rinf) Rinf M)).
suff: (limit_in Rextend_met R_met (fun (r : Rextend) => match r with
  | Rval r0 => f r0
  | _ => 0
end) (fun r : Rextend => exists l : R, In R (Full_set R) l /\ r = Rval l) Rinf M).
move=> H6 eps H7.
elim (H6 eps H7).
move=> dlt H8.
exists (Rmin dlt ((dist Rextend_met Rminf Rinf) * / 2)).
apply conj.
unfold Rmin.
elim (Rle_dec dlt ((dist Rextend_met Rminf Rinf) * / 2)).
move=> H9.
apply (proj1 H8).
move=> H9.
apply (eps2_Rgt_R0 (dist Rextend_met Rminf Rinf)).
elim (dist_pos Rextend_met Rminf Rinf).
apply.
move=> H10.
apply False_ind.
suff: (Rextendlt Rminf Rminf).
apply.
suff: (Rminf = Rinf).
move=> H11.
rewrite {2} H11.
apply I.
apply (proj1 (dist_refl Rextend_met Rminf Rinf)).
apply H10.
elim.
move=> H10.
apply False_ind.
apply (proj1 H10).
move=> H9.
apply False_ind.
apply (Rle_not_lt (dist Rextend_met Rminf Rinf) (Rmin dlt (dist Rextend_met Rminf Rinf * / 2))).
apply (Rle_trans (Rmin dlt (dist Rextend_met Rminf Rinf * / 2)) (dist Rextend_met Rminf Rinf * / 2) (dist Rextend_met Rminf Rinf)).
apply (Rmin_r dlt (dist Rextend_met Rminf Rinf * / 2)).
rewrite - (Rplus_0_r (dist Rextend_met Rminf Rinf * / 2)).
rewrite - {2} (eps2 (dist Rextend_met Rminf Rinf)).
apply (Rplus_le_compat_l (dist Rextend_met Rminf Rinf * / 2) 0 (dist Rextend_met Rminf Rinf * / 2)).
rewrite - (Rmult_0_l (/ 2)).
apply (Rmult_le_compat_r (/ 2) 0 (dist Rextend_met Rminf Rinf)).
left.
apply (Rinv_0_lt_compat 2 Two_Gt_Zero).
apply (Rge_le (dist Rextend_met Rminf Rinf) 0).
apply (dist_pos Rextend_met Rminf Rinf).
apply (proj2 H9).
move=> x H9.
apply (proj2 H8 (Rval x)).
apply conj.
exists x.
apply conj.
apply (Full_intro R x).
reflexivity.
apply (Rlt_le_trans (dist Rextend_met (Rval x) Rinf) (Rmin dlt (dist Rextend_met Rminf Rinf * / 2)) dlt).
apply (proj2 H9).
apply (Rmin_l dlt (dist Rextend_met Rminf Rinf * / 2)).
apply (limit_R_inf_extend_same R_met f (fun r : Rextend => match r with
  | Rval r0 => f r0
  | _ => 0
end)).
move=> r.
reflexivity.
apply H3.
apply (proj1 (limit_in_R_R_extend_same_2 Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (fun (r : Rextend) => Rextendlt (Rval a) r) (Rval a) m)).
suff: (limit_in Rextend_met R_met (fun (r : Rextend) => match r with
  | Rval r0 => f r0
  | _ => 0
end) (fun (r : Rextend) => exists l : R, In R (fun (r : R) => a < r) l /\ r = Rval l) (Rval a) m).
move=> H5 eps H6.
elim (H5 eps H6).
move=> dlt H7.
exists (Rmin dlt ((dist Rextend_met Rinf (Rval a)) * / 2)).
apply conj.
unfold Rmin.
elim (Rle_dec dlt (dist Rextend_met Rinf (Rval a) * / 2)).
move=> H8.
apply (proj1 H7).
move=> H8.
apply (eps2_Rgt_R0 (dist Rextend_met Rinf (Rval a))).
elim (dist_pos Rextend_met Rinf (Rval a)).
apply.
move=> H9.
apply False_ind.
suff: (Rextendlt Rinf Rinf).
apply.
suff: (Rinf = (Rval a)).
move=> H10.
rewrite {1} H10.
apply I.
apply (proj1 (dist_refl Rextend_met Rinf (Rval a))).
apply H9.
elim.
move=> H8.
apply False_ind.
apply (Rle_not_lt (dist Rextend_met Rinf (Rval a)) (Rmin dlt (dist Rextend_met Rinf (Rval a) * / 2))).
apply (Rle_trans (Rmin dlt (dist Rextend_met Rinf (Rval a) * / 2)) (dist Rextend_met Rinf (Rval a) * / 2) (dist Rextend_met Rinf (Rval a))).
apply (Rmin_r dlt (dist Rextend_met Rinf (Rval a) * / 2)).
rewrite - (Rplus_0_r (dist Rextend_met Rinf (Rval a) * / 2)).
rewrite - {2} (eps2 (dist Rextend_met Rinf (Rval a))).
apply (Rplus_le_compat_l (dist Rextend_met Rinf (Rval a) * / 2) 0 (dist Rextend_met Rinf (Rval a) * / 2)).
rewrite - (Rmult_0_l (/ 2)).
apply (Rmult_le_compat_r (/ 2) 0 (dist Rextend_met Rinf (Rval a))).
left.
apply (Rinv_0_lt_compat 2 Two_Gt_Zero).
apply (Rge_le (dist Rextend_met Rinf (Rval a)) 0).
apply (dist_pos Rextend_met Rinf (Rval a)).
apply (proj2 H8).
move=> H8.
apply False_ind.
apply (proj1 H8).
move=> x H8.
apply (proj2 H7 (Rval x)).
apply conj.
exists x.
apply conj.
apply (proj1 H8).
reflexivity.
apply (Rlt_le_trans (dist Rextend_met (Rval x) (Rval a)) (Rmin dlt (dist Rextend_met Rinf (Rval a) * / 2)) dlt).
apply (proj2 H8).
apply (Rmin_l dlt (dist Rextend_met Rinf (Rval a) * / 2)).
apply (limit_in_R_R_extend_same_1 R_met f (fun r : Rextend => match r with
  | Rval r0 => f r0
  | _ => 0
end)).
move=> r.
reflexivity.
apply H2.
Qed.

Lemma Theorem_8_1_corollary_3_4 : forall (f : R -> R), (forall (x : R), ContinuousMet R_met R_met f (Full_set R) x) -> forall (m M : R), limit_R_minf R_met f (Full_set R) m -> limit_R_inf R_met f (Full_set R) M -> forall (y : R), ((m < y /\ y < M) \/ (M < y /\ y < m)) -> exists (x : R), y = f x.
Proof.
move=> f H1 m M H2 H3 y H4.
suff: (limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun r : Rextend => Rextendlt Rminf r) Rminf (Rval m)).
move=> H5.
suff: (limit_in Rextend_met Rextend_met (RextendFunUnWrapRextend f) (fun r : Rextend => Rextendlt r Rinf) Rinf (Rval M)).
move=> H6.
suff: (Rextendlt Rminf Rinf).
move=> H7.
suff: (forall (x : R), Rextendlt Rminf (Rval x) -> Rextendlt (Rval x) Rinf -> ContinuousMet R_met R_met f (Full_set R) x).
move=> H8.
elim (Theorem_8_1_corollary_3_sub f Rminf Rinf H7 H8 (Rval m) (Rval M) H5 H6 y H4).
move=> x H9.
exists x.
apply (proj2 (proj2 H9)).
move=> x H8 H9.
apply (H1 x).
apply I.
apply (proj1 (limit_in_R_R_extend_same_2 Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (fun (r : Rextend) => Rextendlt r Rinf) Rinf M)).
suff: (limit_in Rextend_met R_met (fun (r : Rextend) => match r with
  | Rval r0 => f r0
  | _ => 0
end) (fun r : Rextend => exists l : R, In R (Full_set R) l /\ r = Rval l) Rinf M).
move=> H6 eps H7.
elim (H6 eps H7).
move=> dlt H8.
exists (Rmin dlt ((dist Rextend_met Rminf Rinf) * / 2)).
apply conj.
unfold Rmin.
elim (Rle_dec dlt ((dist Rextend_met Rminf Rinf) * / 2)).
move=> H9.
apply (proj1 H8).
move=> H9.
apply (eps2_Rgt_R0 (dist Rextend_met Rminf Rinf)).
elim (dist_pos Rextend_met Rminf Rinf).
apply.
move=> H10.
apply False_ind.
suff: (Rextendlt Rminf Rminf).
apply.
suff: (Rminf = Rinf).
move=> H11.
rewrite {2} H11.
apply I.
apply (proj1 (dist_refl Rextend_met Rminf Rinf)).
apply H10.
elim.
move=> H10.
apply False_ind.
apply (proj1 H10).
move=> H9.
apply False_ind.
apply (Rle_not_lt (dist Rextend_met Rminf Rinf) (Rmin dlt (dist Rextend_met Rminf Rinf * / 2))).
apply (Rle_trans (Rmin dlt (dist Rextend_met Rminf Rinf * / 2)) (dist Rextend_met Rminf Rinf * / 2) (dist Rextend_met Rminf Rinf)).
apply (Rmin_r dlt (dist Rextend_met Rminf Rinf * / 2)).
rewrite - (Rplus_0_r (dist Rextend_met Rminf Rinf * / 2)).
rewrite - {2} (eps2 (dist Rextend_met Rminf Rinf)).
apply (Rplus_le_compat_l (dist Rextend_met Rminf Rinf * / 2) 0 (dist Rextend_met Rminf Rinf * / 2)).
rewrite - (Rmult_0_l (/ 2)).
apply (Rmult_le_compat_r (/ 2) 0 (dist Rextend_met Rminf Rinf)).
left.
apply (Rinv_0_lt_compat 2 Two_Gt_Zero).
apply (Rge_le (dist Rextend_met Rminf Rinf) 0).
apply (dist_pos Rextend_met Rminf Rinf).
apply (proj2 H9).
move=> x H9.
apply (proj2 H8 (Rval x)).
apply conj.
exists x.
apply conj.
apply (Full_intro R x).
reflexivity.
apply (Rlt_le_trans (dist Rextend_met (Rval x) Rinf) (Rmin dlt (dist Rextend_met Rminf Rinf * / 2)) dlt).
apply (proj2 H9).
apply (Rmin_l dlt (dist Rextend_met Rminf Rinf * / 2)).
apply (limit_R_inf_extend_same R_met f (fun r : Rextend => match r with
  | Rval r0 => f r0
  | _ => 0
end)).
move=> r.
reflexivity.
apply H3.
apply (proj1 (limit_in_R_R_extend_same_2 Rextend_met (fun (r : Rextend) => (match r with
  | Rinf => 0
  | Rminf => 0
  | Rval r => f r
end)) (fun (r : Rextend) => Rextendlt Rminf r) Rminf m)).
suff: (limit_in Rextend_met R_met (fun (r : Rextend) => match r with
  | Rval r0 => f r0
  | _ => 0
end) (fun (r : Rextend) => exists l : R, In R (Full_set R) l /\ r = Rval l) Rminf m).
move=> H5 eps H6.
elim (H5 eps H6).
move=> dlt H7.
exists (Rmin dlt ((dist Rextend_met Rinf Rminf) * / 2)).
apply conj.
unfold Rmin.
elim (Rle_dec dlt (dist Rextend_met Rinf Rminf * / 2)).
move=> H8.
apply (proj1 H7).
move=> H8.
apply (eps2_Rgt_R0 (dist Rextend_met Rinf Rminf)).
elim (dist_pos Rextend_met Rinf Rminf).
apply.
move=> H9.
apply False_ind.
suff: (Rextendlt Rinf Rinf).
apply.
suff: (Rinf = Rminf).
move=> H10.
rewrite {1} H10.
apply I.
apply (proj1 (dist_refl Rextend_met Rinf Rminf)).
apply H9.
elim.
move=> H8.
apply False_ind.
apply (Rle_not_lt (dist Rextend_met Rinf Rminf) (Rmin dlt (dist Rextend_met Rinf Rminf * / 2))).
apply (Rle_trans (Rmin dlt (dist Rextend_met Rinf Rminf * / 2)) (dist Rextend_met Rinf Rminf * / 2) (dist Rextend_met Rinf Rminf)).
apply (Rmin_r dlt (dist Rextend_met Rinf Rminf * / 2)).
rewrite - (Rplus_0_r (dist Rextend_met Rinf Rminf * / 2)).
rewrite - {2} (eps2 (dist Rextend_met Rinf Rminf)).
apply (Rplus_le_compat_l (dist Rextend_met Rinf Rminf * / 2) 0 (dist Rextend_met Rinf Rminf * / 2)).
rewrite - (Rmult_0_l (/ 2)).
apply (Rmult_le_compat_r (/ 2) 0 (dist Rextend_met Rinf Rminf)).
left.
apply (Rinv_0_lt_compat 2 Two_Gt_Zero).
apply (Rge_le (dist Rextend_met Rinf Rminf) 0).
apply (dist_pos Rextend_met Rinf Rminf).
apply (proj2 H8).
move=> H8.
apply False_ind.
apply (proj1 H8).
move=> x H8.
apply (proj2 H7 (Rval x)).
apply conj.
exists x.
apply conj.
apply (Full_intro R x).
reflexivity.
apply (Rlt_le_trans (dist Rextend_met (Rval x) Rminf) (Rmin dlt (dist Rextend_met Rinf Rminf * / 2)) dlt).
apply (proj2 H8).
apply (Rmin_l dlt (dist Rextend_met Rinf Rminf * / 2)).
apply (limit_R_minf_extend_same R_met f (fun r : Rextend => match r with
  | Rval r0 => f r0
  | _ => 0
end)).
move=> r.
reflexivity.
apply H2.
Qed.

Lemma SqrtChooseN : forall (n : nat) (x : R), (n <> O) -> (x >= 0) -> {r : R | r >= 0 /\ x = pow r n}.
Proof.
move=> n x H1 H2.
apply constructive_definite_description.
apply (proj1 (unique_existence (fun (r : R) => r >= 0 /\ x = pow r n))).
apply conj.
suff: (exists (r : R), r >= 0 /\ pow r n >= x).
elim.
move=> r H3.
suff: (forall (x0 : R), In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (0, r) (Rge_le r 0 (proj1 H3)))) x0 -> ContinuousMet R_met R_met (fun x1 : R => x1 ^ n) (Full_set R) x0).
move=> H4.
elim (Theorem_8_1 (fun (x0 : R) => pow x0 n) 0 r (Rge_le r 0 (proj1 H3)) H4 x).
move=> x0 H5.
exists x0.
apply conj.
elim (proj1 H5).
move=> x1 H6 H7.
apply (Rle_ge 0 x1 H6).
apply (proj2 H5).
left.
apply conj.
suff: (forall (n: nat), 0 ^ (S n) <= x).
move=> H5.
elim (O_or_S n).
move=> H6.
rewrite - (proj2_sig H6).
apply (H5 (proj1_sig H6)).
move=> H6.
apply False_ind.
apply H1.
rewrite H6.
reflexivity.
move=> n0.
simpl.
rewrite (Rmult_0_l (pow 0 n0)).
apply (Rge_le x 0 H2).
apply (Rge_le (pow r n) x (proj2 H3)).
suff: (forall (n0 : nat) (x0 : R), ContinuousMet R_met R_met (fun x1 : R => x1 ^ n0) (Full_set R) x0).
move=> H4 x1 H5.
apply (H4 n x1).
elim.
move=> x0 eps H4.
exists 1.
apply conj.
apply Rlt_0_1.
move=> x1 H5.
unfold pow.
rewrite (proj2 (dist_refl R_met 1 1)).
apply H4.
reflexivity.
move=> n0 H4 x0.
apply (Theorem_6_6_3_5_R R_met (fun (x1 : R) => x1) (fun (x1 : R) => pow x1 n0) (Full_set R) x0).
move=> eps H5.
exists eps.
apply conj.
apply H5.
move=> x1 H6.
apply (proj2 H6).
apply H4.
exists (Rmax x 1).
apply conj.
unfold Rmax.
elim (Rle_dec x 1).
move=> H3.
left.
apply Rlt_0_1.
move=> H3.
apply H2.
suff: (forall (n0 : nat), n0 <> O -> pow (Rmax x 1) n0 >= x).
move=> H3.
apply (H3 n H1).
elim.
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> n0 H3 H4.
elim n0.
unfold pow.
rewrite (Rmult_1_r (Rmax x 1)).
apply (Rle_ge x (Rmax x 1)).
apply (Rmax_l x 1).
move=> n1 H5.
rewrite - {2} (Rmult_1_l x).
apply (Rmult_ge_compat (Rmax x 1) 1 (pow (Rmax x 1) (S n1)) x).
left.
apply Rlt_0_1.
apply H2.
apply (Rle_ge 1 (Rmax x 1)).
apply (Rmax_r x 1).
apply H5.
suff: (forall (r1 r2 : R), r1 > r2 -> r2 >= 0 -> (pow r1 n) > (pow r2 n)).
move=> H3 r1 r2 H4 H5.
elim (Rtotal_order r1 r2).
move=> H6.
apply False_ind.
apply (Rlt_irrefl x).
rewrite {1} (proj2 H4).
rewrite (proj2 H5).
apply (H3 r2 r1).
apply H6.
apply (proj1 H4).
elim.
apply.
move=> H6.
apply False_ind.
apply (Rlt_irrefl x).
rewrite {1} (proj2 H5).
rewrite (proj2 H4).
apply (H3 r1 r2).
apply H6.
apply (proj1 H5).
suff: (forall (n0 : nat), n0 <> O -> forall (r1 r2 : R), r1 > r2 -> r2 >= 0 -> (pow r1 n0) > (pow r2 n0)).
move=> H3.
apply (H3 n H1).
elim.
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> n0 H3 H4.
elim n0.
move=> r1 r2 H5 H6.
unfold pow.
rewrite (Rmult_1_r r1).
rewrite (Rmult_1_r r2).
apply H5.
move=> n1 H5 r1 r2 H6 H7.
apply (Rmult_le_0_lt_compat r2 r1 (pow r2 (S n1)) (pow r1 (S n1))).
apply (Rge_le r2 0 H7).
elim (S n1).
left.
apply Rlt_0_1.
move=> n2 H8.
rewrite - (Rmult_0_r 0).
apply (Rmult_le_compat 0 r2 0 (pow r2 n2)).
right.
reflexivity.
right.
reflexivity.
apply (Rge_le r2 0 H7).
apply H8.
apply H6.
apply (H5 r1 r2 H6 H7).
Qed.

Definition MySqrtN (n : nat) (H : n <> O) := fun (r : {x : R | x >= 0}) => proj1_sig (SqrtChooseN n (proj1_sig r) H (proj2_sig r)).

Lemma MySqrtNatureN : forall (n : nat) (H : n <> O) (r : {x : R | x >= 0}), (MySqrtN n H r) >= 0 /\ (proj1_sig r) = pow (MySqrtN n H r) n.
Proof.
move=> n H r.
apply (proj2_sig (SqrtChooseN n (proj1_sig r) H (proj2_sig r))).
Qed.

Lemma MySqrtNatureN2 : forall (n : nat) (H : n <> O) (r : {x : R | x >= 0}) (y : R), (y >= 0 /\ (proj1_sig r) = pow y n) -> (MySqrtN n H r) = y.
Proof.
move=> n H1 r y H2.
suff: (forall (r1 r2 : R), r1 > r2 -> r2 >= 0 -> (pow r1 n) > (pow r2 n)).
move=> H3.
elim (Rtotal_order (MySqrtN n H1 r) y).
move=> H4.
apply False_ind.
apply (Rlt_irrefl (proj1_sig r)).
rewrite {2} (proj2 H2).
rewrite (proj2 (proj2_sig (SqrtChooseN n (proj1_sig r) H1 (proj2_sig r)))).
apply (H3 y (MySqrtN n H1 r)).
apply H4.
apply (proj1 (proj2_sig (SqrtChooseN n (proj1_sig r) H1 (proj2_sig r)))).
elim.
apply.
move=> H4.
apply False_ind.
apply (Rlt_irrefl (proj1_sig r)).
rewrite {1} (proj2 H2).
rewrite (proj2 (proj2_sig (SqrtChooseN n (proj1_sig r) H1 (proj2_sig r)))).
apply (H3 (MySqrtN n H1 r) y).
apply H4.
apply (proj1 H2).
suff: (forall (n0 : nat), n0 <> O -> forall (r1 r2 : R), r1 > r2 -> r2 >= 0 -> (pow r1 n0) > (pow r2 n0)).
move=> H3.
apply (H3 n H1).
elim.
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> n0 H3 H4.
elim n0.
move=> r1 r2 H5 H6.
unfold pow.
rewrite (Rmult_1_r r1).
rewrite (Rmult_1_r r2).
apply H5.
move=> n1 H5 r1 r2 H6 H7.
apply (Rmult_le_0_lt_compat r2 r1 (pow r2 (S n1)) (pow r1 (S n1))).
apply (Rge_le r2 0 H7).
elim (S n1).
left.
apply Rlt_0_1.
move=> n2 H8.
rewrite - (Rmult_0_r 0).
apply (Rmult_le_compat 0 r2 0 (pow r2 n2)).
right.
reflexivity.
right.
reflexivity.
apply (Rge_le r2 0 H7).
apply H8.
apply H6.
apply (H5 r1 r2 H6 H7).
Qed.

Lemma Theorem_5_6_1_2 : forall (an : nat -> R) (H1 : PositiveSequence an), (exists (k : R), 0 < k < 1 /\ (exists (n0 : nat),forall (n : nat), (n >= n0)%nat -> forall (H2 : n <> O), MySqrtN n H2 (exist (fun (r : R) => r >= 0) (an n) (H1 n)) <= k)) -> (exists (s : R), Un_cv (sum_f_R0 an) s).
Proof.
move=> an H1 H2.
elim H2.
move=> k H3.
elim (proj2 H3).
move=> n0 H4.
apply (proj2 (SumShiftUnR2 an (S n0))).
apply (Theorem_5_5_1 (fun (n : nat) => an (n + S n0)%nat) (fun (n : nat) => pow k (n + S n0)%nat)).
move=> n.
apply (H1 (n + S n0)%nat).
move=> n.
left.
elim (n + S n0)%nat.
apply Rlt_0_1.
move=> n1 H5.
apply (Rmult_gt_0_compat k (pow k n1) (proj1 (proj1 H3)) H5).
move=> n.
suff: ((n + S n0)%nat <> O).
move=> H5.
suff: ((n + S n0)%nat >= n0)%nat.
move=> H6.
suff: (an (n + S n0)%nat = (proj1_sig (exist (fun r : R => r >= 0) (an (n + S n0)%nat) (H1 (n + S n0)%nat)))).
move=> H7.
rewrite H7.
rewrite (proj2 (MySqrtNatureN (n + S n0)%nat H5 (exist (fun r : R => r >= 0) (an (n + S n0)%nat) (H1 (n + S n0)%nat)))).
suff: (forall (m : nat) (r1 r2 : R), 0 <= r1 -> r1 <= r2 -> (pow r1 m) <= (pow r2 m)).
move=> H8.
apply (H8 (n + S n0)%nat (MySqrtN (n + S n0) H5 (exist (fun r : R => r >= 0) (an (n + S n0)%nat) (H1 (n + S n0)%nat))) k).
apply (Rge_le (MySqrtN (n + S n0) H5 (exist (fun r : R => r >= 0) (an (n + S n0)%nat) (H1 (n + S n0)%nat))) 0).
apply (proj1 (MySqrtNatureN (n + S n0)%nat H5 (exist (fun r : R => r >= 0) (an (n + S n0)%nat) (H1 (n + S n0)%nat)))).
apply (H4 (n + S n0)%nat H6 H5).
elim.
move=> r1 r2 H8 H9.
unfold pow.
right.
reflexivity.
move=> n1 H8 r1 r2 H9 H10.
apply (Rmult_le_compat r1 r2 (pow r1 n1) (pow r2 n1)).
apply H9.
elim n1.
left.
apply Rlt_0_1.
move=> n2 H11.
rewrite - (Rmult_0_r 0).
apply (Rmult_le_compat 0 r1 0 (pow r1 n2)).
right.
reflexivity.
right.
reflexivity.
apply H9.
apply H11.
apply H10.
apply (H8 r1 r2 H9 H10).
reflexivity.
elim n.
unfold plus.
apply (le_S n0 n0 (le_n n0)).
move=> n1 H6.
apply (le_S n0 (n1 + S n0) H6).
move=> H5.
apply (lt_0_neq (n + S n0)%nat).
unfold lt.
rewrite - ( plus_0_l 1).
apply (plus_le_compat 0 n 1 (S n0)).
apply (le_0_n n).
apply (le_n_S 0 n0).
apply (le_0_n n0).
rewrite H5.
reflexivity.
apply (proj1 (SumShiftUnR2 (pow k) (S n0))).
exists (1 / (1 - k)).
apply (Example_5_2 k).
rewrite (Rabs_right k).
apply (proj2 (proj1 H3)).
left.
apply (proj1 (proj1 H3)).
Qed.

Lemma Theorem_5_6_2_2 : forall (an : nat -> R) (H1 : PositiveSequence an), (exists (k : R), k > 1 /\ (exists (n0 : nat),forall (n : nat), (n >= n0)%nat -> forall (H2 : n <> O), MySqrtN n H2 (exist (fun (r : R) => r >= 0) (an n) (H1 n)) >= k)) -> (Un_inf (sum_f_R0 an)).
Proof.
move=> an H1 H2.
elim H2.
move=> k H3.
elim (proj2 H3).
move=> n0 H4.
apply (proj2 (SumShiftUninfR an (S n0))).
apply (Theorem_5_5_2 (fun (n : nat) => an (n + S n0)%nat) (fun (n : nat) => pow k (n + S n0)%nat)).
move=> n.
apply (H1 (n + S n0)%nat).
move=> n.
left.
elim (n + S n0)%nat.
apply Rlt_0_1.
move=> n1 H5.
apply (Rmult_gt_0_compat k (pow k n1)).
apply (Rlt_trans 0 1 k Rlt_0_1 (proj1 H3)).
apply H5.
move=> n.
suff: ((n + S n0)%nat <> O).
move=> H5.
suff: ((n + S n0)%nat >= n0)%nat.
move=> H6.
suff: (an (n + S n0)%nat = (proj1_sig (exist (fun r : R => r >= 0) (an (n + S n0)%nat) (H1 (n + S n0)%nat)))).
move=> H7.
apply (Rle_ge (k ^ (n + S n0)) (an (n + S n0)%nat)).
rewrite H7.
rewrite (proj2 (MySqrtNatureN (n + S n0)%nat H5 (exist (fun r : R => r >= 0) (an (n + S n0)%nat) (H1 (n + S n0)%nat)))).
suff: (forall (m : nat) (r1 r2 : R), 0 <= r1 -> r1 <= r2 -> (pow r1 m) <= (pow r2 m)).
move=> H8.
apply (H8 (n + S n0)%nat k (MySqrtN (n + S n0) H5 (exist (fun r : R => r >= 0) (an (n + S n0)%nat) (H1 (n + S n0)%nat)))).
left.
apply (Rlt_trans 0 1 k Rlt_0_1 (proj1 H3)).
apply (Rge_le (MySqrtN (n + S n0) H5 (exist (fun r : R => r >= 0) (an (n + S n0)%nat) (H1 (n + S n0)%nat))) k).
apply (H4 (n + S n0)%nat H6 H5).
elim.
move=> r1 r2 H8 H9.
unfold pow.
right.
reflexivity.
move=> n1 H8 r1 r2 H9 H10.
apply (Rmult_le_compat r1 r2 (pow r1 n1) (pow r2 n1)).
apply H9.
elim n1.
left.
apply Rlt_0_1.
move=> n2 H11.
rewrite - (Rmult_0_r 0).
apply (Rmult_le_compat 0 r1 0 (pow r1 n2)).
right.
reflexivity.
right.
reflexivity.
apply H9.
apply H11.
apply H10.
apply (H8 r1 r2 H9 H10).
reflexivity.
elim n.
unfold plus.
apply (le_S n0 n0 (le_n n0)).
move=> n1 H6.
apply (le_S n0 (n1 + S n0) H6).
move=> H5.
apply (lt_0_neq (n + S n0)%nat).
unfold lt.
rewrite - (plus_0_l 1).
apply (plus_le_compat 0 n 1 (S n0)).
apply (le_0_n n).
apply (le_n_S 0 n0).
apply (le_0_n n0).
rewrite H5.
reflexivity.
apply (proj1 (SumShiftUninfR (pow k) (S n0))).
apply (GeometricProgressionSumRUnInf k).
left.
apply (proj1 H3).
Qed.

Lemma Theorem_8_3_1_1 : forall (M : Metric_Space) (T : Type) (U : T -> (Ensemble (Base M))), (forall (t : T), OpenSetMet M (U t)) -> (OpenSetMet M (fun (m : (Base M)) => exists (t : T), In (Base M) (U t) m)).
Proof.
move=> M T U H1 x H2.
elim H2.
move=> t H3.
elim (H1 t x H3).
move=> eps H4.
exists eps.
apply conj.
apply (proj1 H4).
move=> y H5.
exists t.
apply (proj2 H4 y H5).
Qed.

Lemma Theorem_8_3_1_2 : forall (M : Metric_Space), forall (A B : Ensemble (Base M)), OpenSetMet M A -> OpenSetMet M B -> OpenSetMet M (Intersection (Base M) A B).
Proof.
move=> M A B H1 H2 x H3.
elim (H1 x).
move=> eps1 H4.
elim (H2 x).
move=> eps2 H5.
exists (Rmin eps1 eps2).
apply conj.
unfold Rmin.
elim (Rle_dec eps1 eps2).
move=> H6.
apply (proj1 H4).
move=> H6.
apply (proj1 H5).
move=> y H6.
apply (Intersection_intro (Base M) A B y).
apply (proj2 H4 y).
apply (Rlt_le_trans (dist M y x) (Rmin eps1 eps2) eps1).
apply H6.
apply (Rmin_l eps1 eps2).
apply (proj2 H5 y).
apply (Rlt_le_trans (dist M y x) (Rmin eps1 eps2) eps2).
apply H6.
apply (Rmin_r eps1 eps2).
elim H3.
move=> x0 H5 H6.
apply H6.
elim H3.
move=> x0 H4 H5.
apply H4.
Qed.

Lemma Theorem_8_3_1_3 : forall (M : Metric_Space), OpenSetMet M (Full_set (Base M)).
Proof.
move=> M x H1.
exists 1.
apply conj.
apply Rlt_0_1.
move=> y H2.
apply (Full_intro (Base M) y).
Qed.

Lemma Theorem_8_3_1_4 : forall (M : Metric_Space), OpenSetMet M (Empty_set (Base M)).
Proof.
move=> M x.
elim.
Qed.

Lemma Theorem_8_3_2_1 : forall (M : Metric_Space) (T : Type) (U : T -> (Ensemble (Base M))), (forall (t : T), ClosedSetMet M (U t)) -> (ClosedSetMet M (fun (m : (Base M)) => forall (t : T), In (Base M) (U t) m)).
Proof.
move=> M T U H1.
apply Extensionality_Ensembles.
apply conj.
apply (Proposition_6_1_2 M (fun m : Base M => forall t : T, In (Base M) (U t) m)).
move=> x H2 t.
rewrite (H1 t).
move=> eps H3.
elim (H2 eps H3).
move=> y H4.
exists y.
apply conj.
apply (proj1 H4).
apply (proj2 H4 t).
Qed.

Lemma Theorem_8_3_2_2 : forall (M : Metric_Space), forall (A B : Ensemble (Base M)), ClosedSetMet M A -> ClosedSetMet M B -> ClosedSetMet M (Union (Base M) A B).
Proof.
move=> M A B H1 H2.
apply Extensionality_Ensembles.
apply conj.
apply (Proposition_6_1_2 M (Union (Base M) A B)).
rewrite (Proposition_6_1_5 M A B).
move=> x.
elim.
move=> y.
rewrite {2} H1.
apply (Union_introl (Base M) (ClosureMet M A) B).
move=> y.
rewrite {2} H2.
apply (Union_intror (Base M) A (ClosureMet M B)).
Qed.

Lemma Theorem_8_3_2_3 : forall (M : Metric_Space), ClosedSetMet M (Full_set (Base M)).
Proof.
move=> M.
apply Extensionality_Ensembles.
apply conj.
apply (Proposition_6_1_2 M (Full_set (Base M))).
move=> x H1.
apply (Full_intro (Base M) x).
Qed.

Lemma Theorem_8_3_2_4 : forall (M : Metric_Space), ClosedSetMet M (Empty_set (Base M)).
Proof.
move=> M.
apply Extensionality_Ensembles.
apply conj.
move=> x.
elim.
move=> x H1.
elim (H1 1).
move=> y H2.
elim (proj2 H2).
apply Rlt_0_1.
Qed.

Definition RelativeOpenSetMet (M : Metric_Space) (X : Ensemble (Base M)) := fun (A : Ensemble (Base M)) => exists (OA : Ensemble (Base M)), OpenSetMet M OA /\ A = (Intersection (Base M) X OA).

Definition ConnectedMet (M : Metric_Space) (X : Ensemble (Base M)) := forall (A B : Ensemble (Base M)), (RelativeOpenSetMet M X A) -> (RelativeOpenSetMet M X B) -> X = (Union (Base M) A B) -> (Empty_set (Base M)) = (Intersection (Base M) A B) -> (A = (Empty_set (Base M)) \/ B = (Empty_set (Base M))).

Lemma ConnectedMetOpen : forall (M : Metric_Space) (X : Ensemble (Base M)), (OpenSetMet M X) -> ((ConnectedMet M X) <-> (forall (A B : Ensemble (Base M)), (OpenSetMet M A) -> (OpenSetMet M B) -> X = (Union (Base M) A B) -> (Empty_set (Base M)) = (Intersection (Base M) A B) -> (A = (Empty_set (Base M)) \/ B = (Empty_set (Base M))))).
Proof.
move=> M X H1.
apply conj.
move=> H2 A B H3 H4 H5.
apply (H2 A B).
exists A.
apply conj.
apply H3.
apply Extensionality_Ensembles.
apply conj.
move=> a H6.
apply (Intersection_intro (Base M) X A a).
rewrite H5.
left.
apply H6.
apply H6.
move=> a.
elim.
move=> a0 H6 H7.
apply H7.
exists B.
apply conj.
apply H4.
apply Extensionality_Ensembles.
apply conj.
move=> b H6.
apply (Intersection_intro (Base M) X B b).
rewrite H5.
right.
apply H6.
apply H6.
move=> b.
elim.
move=> b0 H6 H7.
apply H7.
apply H5.
move=> H2 A B H3 H4 H5 H6.
apply (H2 A B).
elim H3.
move=> Ax H7.
rewrite (proj2 H7).
apply (Theorem_8_3_1_2 M X Ax).
apply H1.
apply (proj1 H7).
elim H4.
move=> Bx H7.
rewrite (proj2 H7).
apply (Theorem_8_3_1_2 M X Bx).
apply H1.
apply (proj1 H7).
apply H5.
apply H6.
Qed.

Definition ArcwiseConnectedMet (M : Metric_Space) (A : Ensemble (Base M)) := forall (x y : Base M), In (Base M) A x -> In (Base M) A y -> exists (a b : R) (H : a <= b) (f : R -> Base M), f a = x /\ f b = y /\ (forall (r : R), In R (BoundedClosedSection (exist (fun (lr : R * R) => (fst lr) <= (snd lr)) (a, b) H)) r -> In (Base M) A (f r)) /\ (forall (r : R), In R (BoundedClosedSection (exist (fun (lr : R * R) => (fst lr) <= (snd lr)) (a, b) H)) r -> ContinuousMet R_met M f (BoundedClosedSection (exist (fun (lr : R * R) => (fst lr) <= (snd lr)) (a, b) H)) r).

Definition LineSegmentN (N : nat) (a b : Rn N) := (fun (r : Rn N) => exists (t : R), 0 <= t <= 1 /\ r = Rnplus N (Rnmult N (1 - t) a) (Rnmult N t b)).

Inductive ZigzagLineSegmentConnectN (N : nat) : (Ensemble (Rn N)) -> Rn N -> Rn N -> Prop :=
  | ZigzagSameN : forall (A : Ensemble (Rn N)) (r : Rn N), In (Rn N) A r -> ZigzagLineSegmentConnectN N A r r
  | ZigzagConnectN : forall (A : Ensemble (Rn N)) (r1 r2 r3 : Rn N), ZigzagLineSegmentConnectN N A r1 r2 -> Included (Rn N) (LineSegmentN N r2 r3) A -> ZigzagLineSegmentConnectN N A r1 r3.

Lemma Theorem_8_2_1 : forall (N : nat) (A : Ensemble (Rn N)), (OpenSetMet (Rn_met N) A) -> (ConnectedMet (Rn_met N) A) -> (forall (r1 r2 : Rn N), In (Rn N) A r1 -> In (Rn N) A r2 -> ZigzagLineSegmentConnectN N A r1 r2).
Proof.
move=> N A H1 H3 r1 r2 H4 H5.
suff: (OpenSetMet (Rn_met N) (Intersection (Rn N) A (fun (r : Rn N) => ZigzagLineSegmentConnectN N A r1 r))).
suff: (OpenSetMet (Rn_met N) (Intersection (Rn N) A (fun (r : Rn N) => ~ (ZigzagLineSegmentConnectN N A r1 r)))).
move=> H6 H7.
elim (proj1 (ConnectedMetOpen (Rn_met N) A H1) H3 (Intersection (Rn N) A (fun (r : Rn N) => ZigzagLineSegmentConnectN N A r1 r)) (Intersection (Rn N) A (fun (r : Rn N) => ~ (ZigzagLineSegmentConnectN N A r1 r)))).
move=> H8.
apply False_ind.
suff: (In (Rn N) (Intersection (Rn N) A (fun r : Rn N => ZigzagLineSegmentConnectN N A r1 r)) r1).
rewrite H8.
elim.
apply (Intersection_intro (Rn N) A (fun r : Rn N => ZigzagLineSegmentConnectN N A r1 r) r1).
apply H4.
apply (ZigzagSameN N A r1 H4).
move=> H8.
apply NNPP.
move=> H9.
suff: (In (Rn N) (Intersection (Rn N) A (fun r : Rn N => ~ ZigzagLineSegmentConnectN N A r1 r)) r2).
rewrite H8.
elim.
apply (Intersection_intro (Rn N) A (fun r : Rn N => ~ ZigzagLineSegmentConnectN N A r1 r) r2).
apply H5.
apply H9.
apply H7.
apply H6.
apply Extensionality_Ensembles.
apply conj.
move=> a H8.
elim (classic (ZigzagLineSegmentConnectN N A r1 a)).
move=> H9.
left.
apply (Intersection_intro (Rn N) A (fun r : Rn N => ZigzagLineSegmentConnectN N A r1 r) a).
apply H8.
apply H9.
move=> H9.
right.
apply (Intersection_intro (Rn N) A (fun r : Rn N => ~ ZigzagLineSegmentConnectN N A r1 r) a).
apply H8.
apply H9.
move=> a.
elim.
move=> a0.
elim.
move=> a1 H8 H9.
apply H8.
move=> a0.
elim.
move=> a1 H8 H9.
apply H8.
apply Extensionality_Ensembles.
apply conj.
move=> x.
elim.
move=> x.
elim.
move=> x0.
elim.
move=> x1 H8 H9 H10.
apply False_ind.
suff: (In (Rn N) (fun r : Rn N => ZigzagLineSegmentConnectN N A r1 r) x1).
elim H10.
move=> x2 H11 H12 H13.
apply (H12 H13).
apply H9.
move=> r H8.
elim (H1 r).
move=> eps H9.
exists eps.
apply conj.
apply (proj1 H9).
move=> a H10.
apply (Intersection_intro (Rn N) A (fun r0 : Rn N => ~ ZigzagLineSegmentConnectN N A r1 r0) a).
apply (proj2 H9 a H10).
move=> H11.
suff: (~ ZigzagLineSegmentConnectN N A r1 r).
apply.
apply (ZigzagConnectN N A r1 a r).
apply H11.
move=> x.
elim.
move=> t H12.
apply (proj2 H9 x).
apply (Rle_lt_trans (dist (Rn_met N) x r) (dist (Rn_met N) a r) eps).
unfold Rn_met.
unfold dist.
unfold Rn_dist.
rewrite - (Rmult_1_l (RnNorm N (Rnminus N a r))).
suff: (RnNorm N (Rnminus N x r) = (1 - t) * RnNorm N (Rnminus N a r)).
move=> H13.
rewrite H13.
apply (Rmult_le_compat_r (RnNorm N (Rnminus N a r)) (1 - t) 1).
apply (Rge_le (RnNorm N (Rnminus N a r)) 0 (proj1 (RnNormNature N (Rnminus N a r)))).
rewrite - {2} (Rplus_0_r 1).
apply (Rplus_le_compat_l 1 (- t) 0).
rewrite - Ropp_0.
apply (Ropp_le_contravar t 0 (proj1 (proj1 H12))).
rewrite - (Rabs_right (1 - t)).
rewrite - (Proposition_4_4_1 N (1 - t) (Rnminus N a r)).
suff: ((Rnminus N x r) = (Rnmult N (1 - t) (Rnminus N a r))).
move=> H13.
rewrite H13.
reflexivity.
unfold Rnminus.
rewrite (proj2 H12).
rewrite (Rnplus_comm N (Rnmult N (1 - t) a) (Rnmult N t r)).
suff: (Rnplus N (Rnplus N (Rnmult N t r) (Rnmult N (1 - t) a)) (Rnopp N r) = Vadd Rfield (RnVS N) (Vadd Rfield (RnVS N) (Vmul Rfield (RnVS N) t r) (Vmul Rfield (RnVS N) (1 - t) a)) (Vopp Rfield (RnVS N) r)).
move=> H13.
rewrite H13.
suff: (Rnmult N (1 - t) (Rnplus N a (Rnopp N r)) = Vmul Rfield (RnVS N) (1 - t) (Vadd Rfield (RnVS N) a (Vopp Rfield (RnVS N) r))).
move=> H14.
rewrite H14.
rewrite (Vadd_comm Rfield (RnVS N) (Vmul Rfield (RnVS N) t r) (Vmul Rfield (RnVS N) (1 - t) a)).
rewrite (Vadd_assoc Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - t) a) (Vmul Rfield (RnVS N) t r) (Vopp Rfield (RnVS N) r)).
rewrite (Vmul_add_distr_l Rfield (RnVS N) (1 - t) a (Vopp Rfield (RnVS N) r)).
suff: ((Vadd Rfield (RnVS N) (Vmul Rfield (RnVS N) t r) (Vopp Rfield (RnVS N) r)) = (Vmul Rfield (RnVS N) (1 - t) (Vopp Rfield (RnVS N) r))).
move=> H15.
rewrite H15.
reflexivity.
rewrite (Vmul_add_distr_r Rfield (RnVS N) 1 (- t) (Vopp Rfield (RnVS N) r)).
rewrite (Vadd_comm Rfield (RnVS N) (Vmul Rfield (RnVS N) t r) (Vopp Rfield (RnVS N) r)).
rewrite (Vmul_I_l Rfield (RnVS N) (Vopp Rfield (RnVS N) r)).
rewrite (Vmul_opp_opp Rfield (RnVS N) t r).
reflexivity.
reflexivity.
reflexivity.
apply (Rge_minus 1 t).
apply (Rle_ge t 1 (proj2 (proj1 H12))).
apply H10.
elim H8.
move=> a0 H12 H13.
apply H13.
elim H8.
move=> a0 H12 H13.
apply H12.
move=> r H8.
elim (H1 r).
move=> eps H9.
exists eps.
apply conj.
apply (proj1 H9).
move=> a H10.
apply (Intersection_intro (Rn N) A (fun r0 : Rn N => ZigzagLineSegmentConnectN N A r1 r0) a).
apply (proj2 H9 a H10).
apply (ZigzagConnectN N A r1 r a).
elim H8.
move=> a0 H11 H12.
apply H12.
move=> x.
elim.
move=> t H11.
apply (proj2 H9 x).
apply (Rle_lt_trans (dist (Rn_met N) x r) (dist (Rn_met N) a r) eps).
unfold Rn_met.
unfold dist.
unfold Rn_dist.
suff: (RnNorm N (Rnminus N x r) = t * RnNorm N (Rnminus N a r)).
move=> H13.
rewrite H13.
rewrite - {2} (Rmult_1_l (RnNorm N (Rnminus N a r))).
apply (Rmult_le_compat_r (RnNorm N (Rnminus N a r)) t 1).
apply (Rge_le (RnNorm N (Rnminus N a r)) 0 (proj1 (RnNormNature N (Rnminus N a r)))).
apply (proj2 (proj1 H11)).
suff: ((Rnminus N x r) = (Rnmult N t (Rnminus N a r))).
move=> H12.
rewrite H12.
rewrite - {2} (Rabs_right t).
rewrite - (Proposition_4_4_1 N t (Rnminus N a r)).
reflexivity.
apply (Rle_ge 0 t (proj1 (proj1 H11))).
unfold Rnminus.
rewrite (proj2 H11).
suff: (Rnplus N (Rnplus N (Rnmult N (1 - t) r) (Rnmult N t a)) (Rnopp N r) = Vadd Rfield (RnVS N) (Vadd Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - t) r) (Vmul Rfield (RnVS N) t a)) (Vopp Rfield (RnVS N) r)).
move=> H12.
rewrite H12.
suff: (Rnmult N t (Rnplus N a (Rnopp N r)) = Vmul Rfield (RnVS N) t (Vadd Rfield (RnVS N) a (Vopp Rfield (RnVS N) r))).
move=> H13.
rewrite H13.
rewrite (Vadd_comm Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - t) r) (Vmul Rfield (RnVS N) t a)).
rewrite (Vadd_assoc Rfield (RnVS N) (Vmul Rfield (RnVS N) t a) (Vmul Rfield (RnVS N) (1 - t) r) (Vopp Rfield (RnVS N) r)).
rewrite (Vmul_add_distr_l Rfield (RnVS N) t a (Vopp Rfield (RnVS N) r)).
suff: ((Vadd Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - t) r) (Vopp Rfield (RnVS N) r)) = (Vmul Rfield (RnVS N) t (Vopp Rfield (RnVS N) r))).
move=> H14.
rewrite H14.
reflexivity.
rewrite - {1} (Vmul_I_l Rfield (RnVS N) (Vopp Rfield (RnVS N) r)).
rewrite - (Vopp_mul_distr_r Rfield (RnVS N) (FI Rfield) r).
rewrite (Vopp_mul_distr_l Rfield (RnVS N) (FI Rfield) r).
rewrite - (Vmul_add_distr_r Rfield (RnVS N) (1 - t) (Fopp Rfield (FI Rfield)) r).
rewrite - (Vopp_mul_distr_r Rfield (RnVS N) t r).
rewrite (Vopp_mul_distr_l Rfield (RnVS N) t r).
suff: ((Fadd Rfield (1 - t) (Fopp Rfield (FI Rfield))) = (Fopp Rfield t)).
move=> H14.
rewrite H14.
reflexivity.
simpl.
rewrite (Rplus_comm (1 - t) (- 1)).
rewrite - (Rplus_assoc (- 1) 1 (- t)).
rewrite (Rplus_opp_l 1).
apply (Rplus_0_l (- t)).
reflexivity.
reflexivity.
apply H10.
elim H8.
move=> a0 H9 H10.
apply H9.
Qed.

Lemma Theorem_8_2_2 : forall (N : nat) (A : Ensemble (Rn N)), (OpenSetMet (Rn_met N) A) -> (forall (r1 r2 : Rn N), In (Rn N) A r1 -> In (Rn N) A r2 -> ZigzagLineSegmentConnectN N A r1 r2) -> (ArcwiseConnectedMet (Rn_met N) A).
Proof.
move=> N A H1.
suff: (forall (r1 r2 : Rn N), ZigzagLineSegmentConnectN N A r1 r2 -> exists (a b : R) (H : a <= b) (f : R -> Rn N), f a = r1 /\ f b = r2 /\ (forall r : R, In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H)) r -> In (Rn N) A (f r)) /\ (forall r : R, In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H)) r -> ContinuousMet R_met (Rn_met N) f (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H)) r)).
move=> H3 H4 r1 r2 H5 H6.
apply (H3 r1 r2).
apply (H4 r1 r2 H5 H6).
move=> r1 r2.
elim.
move=> A0 r H3.
exists 0.
exists 0.
suff: (0 <= 0).
move=> H4.
exists H4.
exists (fun (x : R) => r).
apply conj.
reflexivity.
apply conj.
reflexivity.
apply conj.
move=> x H5.
apply H3.
move=> x H5 eps H6.
exists 1.
apply conj.
apply Rlt_0_1.
move=> y H7.
rewrite (proj2 (dist_refl (Rn_met N) r r)).
apply H6.
reflexivity.
right.
reflexivity.
move=> A0 r01 r02 r03 H3.
elim.
move=> a.
elim.
move=> b.
elim.
move=> H4.
elim.
move=> f H5 H6.
exists a.
exists (b + 1).
suff: (a <= b + 1).
move=> H7.
exists H7.
exists (fun (r : R) => match (Rlt_le_dec r b) with
  | left _ => f r
  | right _ => Rnplus N (Rnmult N (1 - (r - b)) r02) (Rnmult N (r - b) r03)
end).
apply conj.
elim (Rlt_le_dec a b).
move=> H8.
apply (proj1 H5).
move=> H8.
suff: (a = b).
move=> H9.
rewrite H9.
unfold Rminus.
rewrite (Rplus_opp_r b).
rewrite Ropp_0.
rewrite (Rplus_0_r 1).
rewrite (Rnmult_I_l N r02).
suff: (Rnmult N 0 r03 = Vmul Rfield (RnVS N) 0 r03).
move=> H10.
rewrite H10.
rewrite (Vmul_O_l Rfield (RnVS N) r03).
suff: (Rnplus N r02 (VO Rfield (RnVS N)) = Vadd Rfield (RnVS N) r02 (VO Rfield (RnVS N))).
move=> H11.
rewrite H11.
rewrite (Vadd_O_r Rfield (RnVS N) r02).
rewrite - (proj1 H5).
rewrite - (proj1 (proj2 H5)).
rewrite H9.
reflexivity.
reflexivity.
reflexivity.
apply (Rle_antisym a b).
apply H4.
apply H8.
apply conj.
elim (Rlt_le_dec (b + 1) b).
move=> H8.
apply False_ind.
apply (Rlt_not_le b (b + 1)).
apply H8.
left.
apply (Rlt_plus_1 b).
move=> H8.
suff: ((1 - (b + 1 - b)) = 0).
move=> H9.
rewrite H9.
suff: ((b + 1 - b) = 1).
move=> H10.
rewrite H10.
rewrite (Rnmult_I_l N r03).
suff: (Rnplus N (Rnmult N 0 r02) r03 = Vadd Rfield (RnVS N) (Vmul Rfield (RnVS N) 0 r02) r03).
move=> H11.
rewrite H11.
rewrite (Vmul_O_l Rfield (RnVS N) r02).
apply (Vadd_O_l Rfield (RnVS N) r03).
reflexivity.
unfold Rminus.
rewrite (Rplus_comm (b + 1) (- b)).
rewrite - (Rplus_assoc (- b) b 1).
rewrite (Rplus_opp_l b).
apply (Rplus_0_l 1).
unfold Rminus.
rewrite (Ropp_minus_distr (b + 1) b).
rewrite - (Rplus_assoc 1 b (- (b + 1))).
rewrite (Rplus_comm 1 b).
apply (Rplus_opp_r (b + 1)).
apply conj.
move=> r H8.
elim (Rlt_le_dec r b).
elim H8.
move=> r0 H9 H10 H11.
apply (proj1 (proj2 (proj2 H5)) r0).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H4) r0).
apply H9.
left.
apply H11.
move=> H9.
apply (H6 (Rnplus N (Rnmult N (1 - (r - b)) r02) (Rnmult N (r - b) r03))).
exists (r - b).
apply conj.
apply conj.
apply (Rge_le (r - b) 0).
apply (Rge_minus r b).
apply (Rle_ge b r H9).
elim H8.
move=> r0 H10 H11.
suff: (1 = (b + 1) - b).
move=> H12.
rewrite H12.
apply (Rplus_le_compat_r (- b) r0 (b + 1)).
apply H11.
unfold Rminus.
rewrite (Rplus_comm (b + 1) (- b)).
rewrite - (Rplus_assoc (- b) b 1).
rewrite (Rplus_opp_l b).
rewrite (Rplus_0_l 1).
reflexivity.
reflexivity.
suff: (forall (r : R), In R (fun (r0 : R) => b <= r0 <= b + 1) r -> ContinuousMet R_met (Rn_met N) (fun (r0 : R) => Rnplus N (Rnmult N (1 - (r0 - b)) r02) (Rnmult N (r0 - b) r03)) (fun (r0 : R) => b <= r0 <= b + 1) r).
move=> H8 r H9.
elim (Rtotal_order r b).
move=> H10 eps H11.
suff: (In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H4)) r).
move=> H12.
elim (proj2 (proj2 (proj2 H5)) r H12 eps H11).
move=> dlt H13.
exists (Rmin (b - r) dlt).
apply conj.
unfold Rmin.
elim (Rle_dec (b - r) dlt).
move=> H14.
apply (Rgt_minus b r H10).
move=> H14.
apply (proj1 H13).
move=> y H14.
elim (Rlt_le_dec y b).
move=> H15.
elim (Rlt_le_dec r b).
move=> H16.
suff: (In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H4)) r).
move=> H17.
apply (proj2 H13 y).
apply conj.
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H4) y).
elim (proj1 H14).
move=> z H18 H19.
apply H18.
left.
apply H15.
apply (Rlt_le_trans (dist R_met y r) (Rmin (b - r) dlt) dlt (proj2 H14) (Rmin_r (b - r) dlt)).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H4) r).
elim H12.
move=> r0 H17 H18.
apply H17.
left.
apply H16.
move=> H16.
apply False_ind.
apply (Rlt_not_le b r H10 H16).
move=> H15.
apply False_ind.
apply (Rlt_not_le b y).
apply (Rlt_le_trans y ((Rmin (b - r) dlt) + r) b).
rewrite - (Rplus_0_r y).
rewrite - (Rplus_opp_l r).
rewrite - (Rplus_assoc y (- r) r).
apply (Rplus_lt_compat_r r (y - r) (Rmin (b - r) dlt)).
apply (Rle_lt_trans (y - r) (dist R_met y r) (Rmin (b - r) dlt)).
apply (Rle_abs (y - r)).
apply (proj2 H14).
rewrite - {2} (Rplus_0_r b).
rewrite - (Rplus_opp_l r).
rewrite - (Rplus_assoc b (- r) r).
apply (Rplus_le_compat_r r (Rmin (b - r) dlt) (b + - r)).
apply (Rmin_l (b - r) dlt).
apply H15.
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H4) r).
elim H9.
move=> r0 H12 H13.
apply H12.
left.
apply H10.
elim.
move=> H10 eps H11.
suff: (In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H4)) r).
move=> H12.
elim (proj2 (proj2 (proj2 H5)) r H12 eps H11).
move=> dlt1 H13.
suff: (b <= r <= b + 1).
move=> H14.
elim (H8 r H14 eps H11).
move=> dlt2 H15.
exists (Rmin dlt1 dlt2).
apply conj.
unfold Rmin.
elim (Rle_dec dlt1 dlt2).
move=> H16.
apply (proj1 H13).
move=> H16.
apply (proj1 H15).
move=> y H16.
elim (Rlt_le_dec y b).
elim (Rlt_le_dec r b).
move=> H17.
apply False_ind.
apply (Rlt_irrefl r).
rewrite {2} H10.
apply H17.
move=> H17 H18.
suff: ((Rnplus N (Rnmult N (1 - (r - b)) r02) (Rnmult N (r - b) r03)) = f r).
move=> H19.
rewrite H19.
apply (proj2 H13 y).
apply conj.
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H4) y).
elim (proj1 H16).
move=> y0 H20 H21.
apply H20.
left.
apply H18.
apply (Rlt_le_trans (dist R_met y r) (Rmin dlt1 dlt2) dlt1).
apply (proj2 H16).
apply (Rmin_l dlt1 dlt2).
rewrite H10.
unfold Rminus.
rewrite (Rplus_opp_r b).
rewrite Ropp_0.
rewrite (Rplus_0_r 1).
rewrite (Rnmult_I_l N r02).
suff: ((Rnmult N 0 r03) = RnO N).
move=> H19.
rewrite H19.
rewrite (proj1 (proj2 H5)).
apply (Vadd_O_r Rfield (RnVS N) r02).
apply (Vmul_O_l Rfield (RnVS N) r03).
move=> H17.
elim (Rlt_le_dec r b).
move=> H18.
apply False_ind.
apply (Rlt_irrefl r).
rewrite {2} H10.
apply H18.
move=> H18.
apply (proj2 H15 y).
apply conj.
apply conj.
apply H17.
elim (proj1 H16).
move=> y0 H19 H20.
apply H20.
apply (Rlt_le_trans (dist R_met y r) (Rmin dlt1 dlt2) dlt2).
apply (proj2 H16).
apply (Rmin_r dlt1 dlt2).
rewrite H10.
apply conj.
right.
reflexivity.
left.
apply (Rlt_plus_1 b).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H4) r).
rewrite H10.
apply H4.
rewrite H10.
right.
reflexivity.
move=> H10 eps H11.
suff: (b <= r <= b + 1).
move=> H12.
elim (H8 r H12 eps H11).
move=> dlt H13.
exists (Rmin dlt (r - b)).
apply conj.
unfold Rmin.
elim (Rle_dec dlt (r - b)).
move=> H14.
apply (proj1 H13).
move=> H14.
apply (Rgt_minus r b H10).
move=> y H14.
elim (Rlt_le_dec y b).
move=> H15.
apply False_ind.
apply (Rlt_not_le b y H15).
apply (Ropp_le_cancel b y).
apply (Rplus_le_reg_l r (- y) (- b)).
apply (Rle_trans (r + - y) (dist R_met y r) (r + - b)).
rewrite (dist_sym R_met y r).
apply (Rle_abs (r + - y)).
apply (Rle_trans (dist R_met y r) (Rmin dlt (r - b)) (r + - b)).
left.
apply (proj2 H14).
apply (Rmin_r dlt (r - b)).
move=> H15.
elim (Rlt_le_dec r b).
move=> H16.
apply False_ind.
apply (Rlt_not_le b r).
apply H16.
apply (proj1 H12).
move=> H16.
apply (proj2 H13 y).
apply conj.
apply conj.
apply H15.
elim (proj1 H14).
move=> y0 H17 H18.
apply H18.
apply (Rlt_le_trans (dist R_met y r) (Rmin dlt (r - b)) dlt).
apply (proj2 H14).
apply (Rmin_l dlt (r - b)).
apply conj.
left.
apply H10.
elim H9.
move=> r0 H12 H13.
apply H13.
elim (classic (r02 = r03)).
move=> H8 r H9 eps H10.
exists 1.
apply conj.
apply Rlt_0_1.
move=> y H11.
suff: (forall (x : R), (Rnplus N (Rnmult N (1 - x) r02) (Rnmult N x r03)) = r02).
move=> H12.
rewrite (H12 (y - b)).
rewrite (H12 (r - b)).
rewrite (proj2 (dist_refl (Rn_met N) r02 r02)).
apply H10.
reflexivity.
move=> x.
rewrite H8.
rewrite - (Rnmult_plus_distr_r N (1 - x) x r03).
rewrite (Rplus_assoc 1 (- x) x).
rewrite (Rplus_opp_l x).
rewrite (Rplus_0_r 1).
apply (Rnmult_I_l N r03).
move=> H8 r H9 eps H10.
exists (eps * / Rn_dist N r02 r03).
apply conj.
apply (Rmult_gt_0_compat eps (/ Rn_dist N r02 r03) H10).
apply (Rinv_0_lt_compat (Rn_dist N r02 r03)).
elim (Rn_dist_pos N r02 r03).
apply.
move=> H11.
apply False_ind.
apply H8.
apply (proj1 (dist_refl (Rn_met N) r02 r03) H11).
move=> y H11.
unfold Rn_met.
unfold dist.
unfold Rn_dist.
suff: ((Rnminus N (Rnplus N (Rnmult N (1 - (y - b)) r02) (Rnmult N (y - b) r03)) (Rnplus N (Rnmult N (1 - (r - b)) r02) (Rnmult N (r - b) r03))) = Rnmult N (r - y) (Rnminus N r02 r03)).
move=> H12.
rewrite H12.
rewrite (Proposition_4_4_1 N (r - y) (Rnminus N r02 r03)).
rewrite - (Rmult_1_r eps).
rewrite - (Rinv_l (RnNorm N (Rnminus N r02 r03))).
rewrite - (Rmult_assoc eps (/ RnNorm N (Rnminus N r02 r03)) (RnNorm N (Rnminus N r02 r03))).
apply (Rmult_lt_compat_r (RnNorm N (Rnminus N r02 r03)) (Rabs (r - y)) (eps * / RnNorm N (Rnminus N r02 r03))).
elim (Rn_dist_pos N r02 r03).
apply.
move=> H13.
apply False_ind.
apply H8.
apply (proj1 (dist_refl (Rn_met N) r02 r03) H13).
rewrite (Rabs_minus_sym r y).
apply (proj2 H11).
move=> H13.
apply H8.
apply (proj1 (dist_refl (Rn_met N) r02 r03) H13).
unfold Rnminus.
suff: (Rnplus N (Rnplus N (Rnmult N (1 - (y - b)) r02) (Rnmult N (y - b) r03)) (Rnopp N (Rnplus N (Rnmult N (1 - (r - b)) r02) (Rnmult N (r - b) r03))) = Vadd Rfield (RnVS N) (Vadd Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - (y - b)) r02) (Vmul Rfield (RnVS N) (y - b) r03)) (Vopp Rfield (RnVS N) (Vadd Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - (r - b)) r02) (Vmul Rfield (RnVS N) (r - b) r03)))).
move=> H12.
rewrite H12.
suff: (Rnmult N (r - y) (Rnplus N r02 (Rnopp N r03)) = Vmul Rfield (RnVS N) (r - y) (Vadd Rfield (RnVS N) r02 (Vopp Rfield (RnVS N) r03))).
move=> H13.
rewrite H13.
rewrite (Vopp_add_distr Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - (r - b)) r02) (Vmul Rfield (RnVS N) (r - b) r03)).
rewrite (Vadd_assoc Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - (y - b)) r02) (Vmul Rfield (RnVS N) (y - b) r03) (Vadd Rfield (RnVS N) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - (r - b)) r02)) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) (r - b) r03)))).
rewrite (Vadd_comm Rfield (RnVS N) (Vmul Rfield (RnVS N) (y - b) r03) (Vadd Rfield (RnVS N) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - (r - b)) r02)) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) (r - b) r03)))).
rewrite (Vadd_assoc Rfield (RnVS N) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - (r - b)) r02)) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) (r - b) r03)) (Vmul Rfield (RnVS N) (y - b) r03)).
rewrite - (Vadd_assoc Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - (y - b)) r02) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - (r - b)) r02)) (Vadd Rfield (RnVS N) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) (r - b) r03)) (Vmul Rfield (RnVS N) (y - b) r03))).
rewrite (Vopp_mul_distr_l Rfield (RnVS N) (1 - (r - b)) r02).
rewrite - (Vmul_add_distr_r Rfield (RnVS N) (1 - (y - b)) (Fopp Rfield (1 - (r - b))) r02).
suff: ((Fadd Rfield (1 - (y - b)) (Fopp Rfield (1 - (r - b)))) = r - y).
move=> H14.
rewrite H14.
rewrite (Vopp_mul_distr_l Rfield (RnVS N) (r - b) r03).
rewrite - (Vmul_add_distr_r Rfield (RnVS N) (Fopp Rfield (r - b)) (y - b) r03).
suff: ((Fadd Rfield (Fopp Rfield (r - b)) (y - b)) = - (r - y)).
move=> H15.
rewrite H15.
rewrite - (Vopp_mul_distr_l Rfield (RnVS N) (r - y) r03).
rewrite (Vopp_mul_distr_r Rfield (RnVS N) (r - y) r03).
rewrite (Vmul_add_distr_l Rfield (RnVS N) (r - y) r02 (Vopp Rfield (RnVS N) r03)).
reflexivity.
simpl.
rewrite (Ropp_minus_distr r b).
rewrite (Ropp_minus_distr r y).
rewrite (Rplus_comm (b - r) (y - b)).
rewrite (Rplus_assoc y (- b) (b - r)).
rewrite - (Rplus_assoc (- b) b (- r)).
rewrite (Rplus_opp_l b).
rewrite (Rplus_0_l (- r)).
reflexivity.
simpl.
rewrite (Ropp_minus_distr 1 (r - b)).
rewrite (Rplus_comm (1 - (y - b)) (r - b - 1)).
rewrite - (Rplus_assoc (r - b - 1) 1 (- (y - b))).
rewrite (Rplus_assoc (r - b) (- 1) 1).
rewrite (Rplus_opp_l 1).
rewrite (Rplus_0_r (r - b)).
rewrite (Ropp_minus_distr y b).
rewrite - (Rplus_assoc (r - b) b (- y)).
rewrite (Rplus_assoc r (- b) b).
rewrite (Rplus_opp_l b).
rewrite (Rplus_0_r r).
reflexivity.
reflexivity.
reflexivity.
apply (Rle_trans a b (b + 1) H4).
left.
apply (Rlt_plus_1 b).
Qed.

Lemma Theorem_8_2_3 : forall (M : Metric_Space) (A : Ensemble (Base M)), (OpenSetMet M A) -> (ArcwiseConnectedMet M A) -> (ConnectedMet M A).
Proof.
move=> M A H1 H3.
apply (proj2 (ConnectedMetOpen M A H1)).
move=> X Y H4 H5 H6 H7.
apply NNPP.
move=> H8.
suff: (Inhabited (Base M) X).
elim.
move=> x H9.
suff: (Inhabited (Base M) Y).
elim.
move=> y H10.
elim (H3 x y).
move=> a.
elim.
move=> b.
elim.
move=> H11.
elim.
move=> f H12.
suff: ({x : R | is_least_upper_bound (Intersection R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11)) (fun (r : R) => In (Base M) X (f r))) x}).
move=> H13.
suff: (In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11)) (proj1_sig H13)).
move=> H14.
suff: (In (Base M) A (f (proj1_sig H13))).
rewrite H6.
move=> H15.
suff: (~ In (Base M) X (f (proj1_sig H13))).
suff: (~ In (Base M) Y (f (proj1_sig H13))).
elim H15.
move=> z H16 H17 H18.
apply (H18 H16).
move=> z H16 H17 H18.
apply (H17 H16).
move=> H16.
elim (H5 (f (proj1_sig H13)) H16).
move=> dlt H17.
elim (proj2 (proj2 (proj2 H12)) (proj1_sig H13) H14 dlt).
move=> alp H18.
apply (Rlt_not_le (proj1_sig H13) (proj1_sig H13 - alp)).
rewrite - {2} (Rplus_0_r (proj1_sig H13)).
apply (Rplus_lt_compat_l (proj1_sig H13) (- alp) 0).
apply (Ropp_lt_gt_0_contravar alp).
apply (proj1 H18).
apply (Rge_le (proj1_sig H13 - alp) (proj1_sig H13)).
apply (proj2 (proj2_sig H13) (proj1_sig H13 - alp)).
move=> z H19.
apply NNPP.
move=> H20.
suff: (In (Base M) (Empty_set (Base M)) (f z)).
elim.
rewrite H7.
apply (Intersection_intro (Base M) X Y (f z)).
elim H19.
move=> w H21 H22.
apply H22.
apply (proj2 H17 (f z)).
apply (proj2 H18 z).
apply conj.
elim H19.
move=> w H21 H22.
apply H21.
unfold R_met.
unfold dist.
unfold R_dist.
rewrite (Rabs_minus_sym z (proj1_sig H13)).
rewrite (Rabs_right (proj1_sig H13 - z)).
apply (Rplus_lt_reg_r (- alp) (proj1_sig H13 - z) alp).
rewrite (Rplus_opp_r alp).
rewrite (Rplus_assoc (proj1_sig H13) (- z) (- alp)).
rewrite (Rplus_comm (- z) (- alp)).
rewrite - (Rplus_assoc (proj1_sig H13) (- alp) (- z)).
rewrite - (Rplus_opp_r z).
apply (Rplus_lt_compat_r (- z) (proj1_sig H13 - alp) z).
apply (Rnot_le_lt z (proj1_sig H13 - alp) H20).
apply (Rge_minus (proj1_sig H13) z).
apply (Rle_ge z (proj1_sig H13)).
apply (proj1 (proj2_sig H13) z).
apply H19.
apply (proj1 H17).
move=> H16.
suff: (proj1_sig H13 < b).
move=> H17.
elim (H4 (f (proj1_sig H13)) H16).
move=> dlt H18.
elim (proj2 (proj2 (proj2 H12)) (proj1_sig H13) H14 dlt).
move=> alp H19.
apply (Rlt_not_le (proj1_sig H13 + (Rmin (alp * / 2) (b - proj1_sig H13))) (proj1_sig H13)).
rewrite - {1} (Rplus_0_r (proj1_sig H13)).
apply (Rplus_lt_compat_l (proj1_sig H13) 0 (Rmin (alp * / 2) (b - proj1_sig H13))).
unfold Rmin.
elim (Rle_dec (alp * / 2) (b - proj1_sig H13)).
move=> H20.
apply (eps2_Rgt_R0 alp).
apply (proj1 H19).
move=> H20.
apply (Rgt_minus b (proj1_sig H13)).
apply H17.
apply (proj1 (proj2_sig H13) (proj1_sig H13 + Rmin (alp * / 2) (b - proj1_sig H13))).
apply (Intersection_intro R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11)) (fun r : R => In (Base M) X (f r)) (proj1_sig H13 + Rmin (alp * / 2) (b - proj1_sig H13))).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11) (proj1_sig H13 + Rmin (alp * / 2) (b - proj1_sig H13))).
apply (Rle_trans a (proj1_sig H13) (proj1_sig H13 + Rmin (alp * / 2) (b - proj1_sig H13))).
apply (proj1 (proj2_sig H13) a).
apply (Intersection_intro R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11)) (fun r : R => In (Base M) X (f r)) a).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11) a).
right.
reflexivity.
apply H11.
unfold In.
rewrite (proj1 H12).
apply H9.
rewrite - {1} (Rplus_0_r (proj1_sig H13)).
apply (Rplus_le_compat_l (proj1_sig H13) 0 (Rmin (alp * / 2) (b - proj1_sig H13))).
left.
unfold Rmin.
elim (Rle_dec (alp * / 2) (b - proj1_sig H13)).
move=> H20.
apply (eps2_Rgt_R0 alp).
apply (proj1 H19).
move=> H20.
apply (Rgt_minus b (proj1_sig H13)).
apply H17.
simpl.
rewrite - {4} (Rplus_0_r b).
rewrite - (Rplus_opp_l (proj1_sig H13)).
rewrite - (Rplus_assoc b (- proj1_sig H13) (proj1_sig H13)).
rewrite (Rplus_comm (b + - proj1_sig H13) (proj1_sig H13)).
apply (Rplus_le_compat_l (proj1_sig H13) (Rmin (alp * / 2) (b - proj1_sig H13)) (b + - proj1_sig H13)).
apply (Rmin_r (alp * / 2) (b - proj1_sig H13)).
apply (proj2 H18 (f (proj1_sig H13 + Rmin (alp * / 2) (b - proj1_sig H13)))).
apply (proj2 H19 (proj1_sig H13 + Rmin (alp * / 2) (b - proj1_sig H13))).
apply conj.
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11) (proj1_sig H13 + Rmin (alp * / 2) (b - proj1_sig H13))).
apply (Rle_trans a (proj1_sig H13) (proj1_sig H13 + Rmin (alp * / 2) (b - proj1_sig H13))).
apply (proj1 (proj2_sig H13) a).
apply (Intersection_intro R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11)) (fun r : R => In (Base M) X (f r)) a).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11) a).
right.
reflexivity.
apply H11.
unfold In.
rewrite (proj1 H12).
apply H9.
rewrite - {1} (Rplus_0_r (proj1_sig H13)).
apply (Rplus_le_compat_l (proj1_sig H13) 0 (Rmin (alp * / 2) (b - proj1_sig H13))).
left.
unfold Rmin.
elim (Rle_dec (alp * / 2) (b - proj1_sig H13)).
move=> H20.
apply (eps2_Rgt_R0 alp).
apply (proj1 H19).
move=> H20.
apply (Rgt_minus b (proj1_sig H13)).
apply H17.
simpl.
rewrite - {4} (Rplus_0_r b).
rewrite - (Rplus_opp_l (proj1_sig H13)).
rewrite - (Rplus_assoc b (- proj1_sig H13) (proj1_sig H13)).
rewrite (Rplus_comm (b + - proj1_sig H13) (proj1_sig H13)).
apply (Rplus_le_compat_l (proj1_sig H13) (Rmin (alp * / 2) (b - proj1_sig H13)) (b + - proj1_sig H13)).
apply (Rmin_r (alp * / 2) (b - proj1_sig H13)).
unfold R_met.
unfold dist.
unfold R_dist.
unfold Rminus.
rewrite (Rplus_comm (proj1_sig H13 + Rmin (alp * / 2) (b - proj1_sig H13)) (- proj1_sig H13)).
rewrite - (Rplus_assoc (- proj1_sig H13) (proj1_sig H13) (Rmin (alp * / 2) (b - proj1_sig H13))).
rewrite (Rplus_opp_l (proj1_sig H13)).
rewrite (Rplus_0_l (Rmin (alp * / 2) (b - proj1_sig H13))).
rewrite (Rabs_right (Rmin (alp * / 2) (b - proj1_sig H13))).
apply (Rle_lt_trans (Rmin (alp * / 2) (b - proj1_sig H13)) (alp * / 2) alp).
apply (Rmin_l (alp * / 2) (b - proj1_sig H13)).
rewrite - (Rplus_0_r (alp * / 2)).
rewrite - {2} (eps2 alp).
apply (Rplus_lt_compat_l (alp * / 2) 0 (alp * / 2)).
apply (eps2_Rgt_R0 alp).
apply (proj1 H19).
left.
unfold Rmin.
elim (Rle_dec (alp * / 2) (b - proj1_sig H13)).
move=> H20.
apply (eps2_Rgt_R0 alp).
apply (proj1 H19).
move=> H20.
apply (Rgt_minus b (proj1_sig H13)).
apply H17.
apply (proj1 H18).
elim (H5 y).
move=> eps H17.
suff: (In R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11)) b).
move=> H18.
elim (proj2 (proj2 (proj2 H12)) b H18 eps (proj1 H17)).
move=> dlt H19.
apply (Rle_lt_trans (proj1_sig H13) (b - dlt) b).
apply (Rge_le (b - dlt) (proj1_sig H13)).
apply (proj2 (proj2_sig H13) (b - dlt)).
move=> z H20.
apply (Rnot_lt_le (b - dlt) z).
move=> H21.
suff: (In (Base M) (Empty_set (Base M)) (f z)).
elim.
rewrite H7.
apply (Intersection_intro (Base M) X Y (f z)).
elim H20.
move=> z0 H22 H23.
apply H23.
apply (proj2 H17 (f z)).
rewrite - (proj1 (proj2 H12)).
apply (proj2 H19 z).
apply conj.
elim H20.
move=> z0 H22 H23.
apply H22.
unfold R_met.
unfold dist.
unfold R_dist.
rewrite (Rabs_minus_sym z b).
rewrite (Rabs_right (b - z)).
apply (Rplus_lt_reg_r z (b - z) dlt).
rewrite (Rplus_assoc b (- z) z).
rewrite (Rplus_opp_l z).
rewrite - (Rplus_opp_l dlt).
rewrite - (Rplus_assoc b (- dlt) dlt).
rewrite (Rplus_comm dlt z).
apply (Rplus_lt_compat_r dlt (b - dlt) z H21).
apply (Rge_minus b z).
apply (Rle_ge z b).
elim H20.
move=> z0 H22 H23.
elim H22.
move=> z1 H24 H25.
apply H25.
rewrite - {2} (Rplus_0_r b).
apply (Rplus_lt_compat_l b (- dlt) 0).
apply (Ropp_lt_gt_0_contravar dlt (proj1 H19)).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11) b H11).
right.
reflexivity.
apply H10.
apply (proj1 (proj2 (proj2 H12)) (proj1_sig H13)).
apply H14.
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11) (proj1_sig H13)).
apply (proj1 (proj2_sig H13) a).
apply (Intersection_intro R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11)) (fun r : R => In (Base M) X (f r)) a).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11) a).
right.
reflexivity.
apply H11.
unfold In.
rewrite (proj1 H12).
apply H9.
apply (Rge_le b (proj1_sig H13)).
apply (proj2 (proj2_sig H13) b).
move=> z.
elim.
move=> z0 H14 H15.
elim H14.
move=> z1 H16 H17.
apply H17.
apply (My_completeness_of_upper (Intersection R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11)) (fun r : R => In (Base M) X (f r)))).
apply conj.
apply (Inhabited_intro R (Intersection R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11)) (fun r : R => In (Base M) X (f r))) a).
apply (Intersection_intro R (BoundedClosedSection (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11)) (fun r : R => In (Base M) X (f r))).
apply (BoundedClosedSection_intro (exist (fun lr : R * R => fst lr <= snd lr) (a, b) H11) a).
right.
reflexivity.
apply H11.
unfold In.
rewrite (proj1 H12).
apply H9.
exists b.
move=> z.
elim.
move=> z0 H13 H14.
elim H13.
move=> z1 H15 H16.
apply H16.
rewrite H6.
left.
apply H9.
rewrite H6.
right.
apply H10.
apply NNPP.
move=> H10.
apply H8.
right.
apply Extensionality_Ensembles.
apply conj.
move=> y H11.
apply False_ind.
apply H10.
apply (Inhabited_intro (Base M) Y y H11).
move=> y.
elim.
apply NNPP.
move=> H9.
apply H8.
left.
apply Extensionality_Ensembles.
apply conj.
move=> x H10.
apply False_ind.
apply H9.
apply (Inhabited_intro (Base M) X x H10).
move=> x.
elim.
Qed.

Lemma Theorem_8_2_corollary : forall (N : nat), (ConnectedMet (Rn_met N) (Full_set (Rn N))).
Proof.
move=> N.
apply (Theorem_8_2_3 (Rn_met N) (Full_set (Rn N))).
apply (Theorem_8_3_1_3 (Rn_met N)).
move=> x y H1 H2.
exists 0.
exists 1.
suff: (0 <= 1).
move=> H3.
exists H3.
exists (fun (t : R) => Rnplus N (Rnmult N (1 - t) x) (Rnmult N t y)).
apply conj.
unfold Rminus.
rewrite Ropp_0.
rewrite (Rplus_0_r 1).
rewrite (Rnmult_I_l N x).
suff: ((Rnmult N 0 y) = RnO N).
move=> H4.
rewrite H4.
apply (Vadd_O_r Rfield (RnVS N) x).
apply (Vmul_O_l Rfield (RnVS N) y).
apply conj.
unfold Rminus.
rewrite (Rplus_opp_r 1).
rewrite (Rnmult_I_l N y).
suff: ((Rnmult N 0 x) = RnO N).
move=> H4.
rewrite H4.
apply (Vadd_O_l Rfield (RnVS N) y).
apply (Vmul_O_l Rfield (RnVS N) x).
apply conj.
move=> r H4.
apply (Full_intro (Rn N) (Rnplus N (Rnmult N (1 - r) x) (Rnmult N r y))).
move=> r H4 eps H5.
elim (classic (x = y)).
move=> H6.
exists 1.
apply conj.
apply Rlt_0_1.
move=> z H7.
suff: (forall (w : R), (Rnplus N (Rnmult N (1 - w) x) (Rnmult N w y)) = x).
move=> H8.
rewrite (H8 z).
rewrite (H8 r).
rewrite (proj2 (dist_refl (Rn_met N) x x)).
apply H5.
reflexivity.
move=> w.
rewrite H6.
rewrite - (Rnmult_plus_distr_r N (1 - w) w y).
rewrite (Rplus_assoc 1 (- w) w).
rewrite (Rplus_opp_l w).
rewrite (Rplus_0_r 1).
apply (Rnmult_I_l N y).
move=> H6.
exists (eps * / Rn_dist N x y).
apply conj.
apply (Rmult_gt_0_compat eps (/ Rn_dist N x y) H5).
apply (Rinv_0_lt_compat (Rn_dist N x y)).
elim (Rn_dist_pos N x y).
apply.
move=> H7.
apply False_ind.
apply H6.
apply (proj1 (dist_refl (Rn_met N) x y) H7).
move=> z H7.
unfold Rn_met.
unfold dist.
unfold Rn_dist.
suff: ((Rnminus N (Rnplus N (Rnmult N (1 - z) x) (Rnmult N z y)) (Rnplus N (Rnmult N (1 - r) x) (Rnmult N r y))) = Rnmult N (r - z) (Rnminus N x y)).
move=> H8.
rewrite H8.
rewrite (Proposition_4_4_1 N (r - z) (Rnminus N x y)).
rewrite - (Rmult_1_r eps).
rewrite - (Rinv_l (RnNorm N (Rnminus N x y))).
rewrite - (Rmult_assoc eps (/ RnNorm N (Rnminus N x y)) (RnNorm N (Rnminus N x y))).
apply (Rmult_lt_compat_r (RnNorm N (Rnminus N x y)) (Rabs (r - z)) (eps * / RnNorm N (Rnminus N x y))).
elim (Rn_dist_pos N x y).
apply.
move=> H9.
apply False_ind.
apply H6.
apply (proj1 (dist_refl (Rn_met N) x y) H9).
rewrite (Rabs_minus_sym r z).
apply (proj2 H7).
move=> H9.
apply H6.
apply (proj1 (dist_refl (Rn_met N) x y) H9).
unfold Rnminus.
suff: (Rnplus N (Rnplus N (Rnmult N (1 - z) x) (Rnmult N z y)) (Rnopp N (Rnplus N (Rnmult N (1 - r) x) (Rnmult N r y))) = Vadd Rfield (RnVS N) (Vadd Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - z) x) (Vmul Rfield (RnVS N) z y)) (Vopp Rfield (RnVS N) (Vadd Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - r) x) (Vmul Rfield (RnVS N) r y)))).
move=> H8.
rewrite H8.
suff: (Rnmult N (r - z) (Rnplus N x (Rnopp N y)) = Vmul Rfield (RnVS N) (r - z) (Vadd Rfield (RnVS N) x (Vopp Rfield (RnVS N) y))).
move=> H9.
rewrite H9.
rewrite (Vopp_add_distr Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - r) x) (Vmul Rfield (RnVS N) r y)).
rewrite (Vadd_assoc Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - z) x) (Vmul Rfield (RnVS N) z y) (Vadd Rfield (RnVS N) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - r) x)) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) r y)))).
rewrite (Vadd_comm Rfield (RnVS N) (Vmul Rfield (RnVS N) z y) (Vadd Rfield (RnVS N) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - r) x)) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) r y)))).
rewrite (Vadd_assoc Rfield (RnVS N) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - r) x)) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) r y)) (Vmul Rfield (RnVS N) z y)).
rewrite - (Vadd_assoc Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - z) x) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) (1 - r) x)) (Vadd Rfield (RnVS N) (Vopp Rfield (RnVS N) (Vmul Rfield (RnVS N) r y)) (Vmul Rfield (RnVS N) z y))).
rewrite (Vopp_mul_distr_l Rfield (RnVS N) (1 - r) x).
rewrite - (Vmul_add_distr_r Rfield (RnVS N) (1 - z) (Fopp Rfield (1 - r)) x).
suff: ((Fadd Rfield (1 - z) (Fopp Rfield (1 - r))) = r - z).
move=> H10.
rewrite H10.
rewrite (Vopp_mul_distr_l Rfield (RnVS N) r y).
rewrite - (Vmul_add_distr_r Rfield (RnVS N) (Fopp Rfield r) z y).
suff: ((Fadd Rfield (Fopp Rfield r) z) = - (r - z)).
move=> H11.
rewrite H11.
rewrite - (Vopp_mul_distr_l Rfield (RnVS N) (r - z) y).
rewrite (Vopp_mul_distr_r Rfield (RnVS N) (r - z) y).
rewrite (Vmul_add_distr_l Rfield (RnVS N) (r - z) x (Vopp Rfield (RnVS N) y)).
reflexivity.
simpl.
rewrite (Ropp_minus_distr r z).
apply (Rplus_comm (- r) z).
simpl.
rewrite (Ropp_minus_distr 1 r).
rewrite (Rplus_comm (1 - z) (r - 1)).
rewrite - (Rplus_assoc (r - 1) 1 (- z)).
rewrite (Rplus_assoc r (- 1) 1).
rewrite (Rplus_opp_l 1).
rewrite (Rplus_0_r r).
reflexivity.
reflexivity.
reflexivity.
left.
apply Rlt_0_1.
Qed.

End Kaisekinyuumonn1.