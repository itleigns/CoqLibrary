Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "BasicProperty" as BasicProperty.

From mathcomp
Require Import ssreflect.
Require Import Classical.
Require Import MyAlgebraicStructure.MyField. 

Section VectorSpace.

Record VectorSpace : Type := mkVectorSpace
{
VF   : Field;
VT   : Type;
VO : VT;
Vadd : VT -> VT -> VT;
Vmul : (FT VF) -> VT -> VT;
Vopp : VT -> VT;
Vadd_comm : forall (x y : VT), (Vadd x y) = (Vadd y x);
Vadd_assoc : forall (x y z : VT), (Vadd (Vadd x y) z) = (Vadd x (Vadd y z));
Vadd_O_l : forall x : VT, (Vadd VO x) = x;
Vadd_opp_r : forall x : VT, (Vadd x (Vopp x)) = VO;
Vmul_add_distr_l : forall (x : FT VF) (y z : VT), (Vmul x (Vadd y z)) = (Vadd (Vmul x y) (Vmul x z));
Vmul_add_distr_r : forall (x y : FT VF) (z : VT), (Vmul (Fadd VF x y) z) = (Vadd (Vmul x z) (Vmul y z));
Vmul_assoc : forall (x y : FT VF) (z : VT), (Vmul x (Vmul y z)) = (Vmul (Fmul VF x y) z);
Vmul_I_l : forall x : VT, (Vmul (FI VF) x) = x;
}.

Lemma Vadd_O_r : forall (v : VectorSpace) (x : VT v), (Vadd v x (VO v)) = x.
Proof.
move=> v x.
rewrite (Vadd_comm v x (VO v)).
apply (Vadd_O_l v x).
Qed.

Lemma Vadd_ne : forall (v : VectorSpace) (x : VT v), (Vadd v x (VO v)) = x /\ (Vadd v (VO v) x) = x.
Proof.
move=> v x.
apply conj.
apply (Vadd_O_r v x).
apply (Vadd_O_l v x).
Qed.

Lemma Vadd_opp_l : forall (v : VectorSpace) (x : VT v), (Vadd v (Vopp v x) x) = (VO v).
Proof.
move=> v x.
rewrite (Vadd_comm v (Vopp v x) x).
apply (Vadd_opp_r v x).
Qed.

Lemma Vadd_opp_r_uniq : forall (v : VectorSpace) (x y : VT v), (Vadd v x y) = (VO v) -> y = (Vopp v x).
Proof.
move=> v x y H1.
suff: (Vadd v (Vopp v x) (Vadd v x y)) = (Vadd v (Vopp v x) (VO v)).
move=> H2.
rewrite - (Vadd_O_r v (Vopp v x)).
rewrite - H2.
rewrite - (Vadd_assoc v (Vopp v x) x y).
rewrite (Vadd_opp_l v x).
rewrite (Vadd_O_l v y).
by [].
rewrite H1.
by [].
Qed.

Lemma Vadd_eq_compat_l : forall (v : VectorSpace) (x y z : VT v), y = z -> (Vadd v x y) = (Vadd v x z).
Proof.
move=> v x y z H1.
rewrite H1.
by [].
Qed.

Lemma Vadd_eq_compat_r : forall (v : VectorSpace) (x y z : VT v), y = z -> (Vadd v y x) = (Vadd v z x).
Proof.
move=> v x y z H1.
rewrite H1.
by [].
Qed.

Lemma Vadd_eq_reg_l : forall (v : VectorSpace) (x y z : VT v), (Vadd v x y) = (Vadd v x z) -> y = z.
Proof.
move=> v x y z H1.
rewrite - (Vadd_O_l v y).
rewrite - (Vadd_O_l v z).
rewrite - (Vadd_opp_l v x).
rewrite (Vadd_assoc v (Vopp v x) x y).
rewrite (Vadd_assoc v (Vopp v x) x z).
apply (Vadd_eq_compat_l v (Vopp v x) (Vadd v x y) (Vadd v x z)).
by [].
Qed.

Lemma Vadd_eq_reg_r : forall (v : VectorSpace) (x y z : VT v), (Vadd v y x) = (Vadd v z x) -> y = z.
Proof.
move=> v x y z H1.
rewrite - (Vadd_O_r v y).
rewrite - (Vadd_O_r v z).
rewrite - (Vadd_opp_r v x).
rewrite - (Vadd_assoc v y x (Vopp v x)).
rewrite - (Vadd_assoc v z x (Vopp v x)).
apply (Vadd_eq_compat_r v (Vopp v x) (Vadd v y x) (Vadd v z x)).
by [].
Qed.

Lemma Vadd_O_r_uniq : forall (v : VectorSpace) (x y : VT v), (Vadd v x y) = x -> y = (VO v).
Proof.
move=> v x y H1.
rewrite - (Vadd_O_l v y).
rewrite - (Vadd_opp_l v x).
rewrite (Vadd_assoc v (Vopp v x) x y).
rewrite H1.
by [].
Qed.

Lemma Vmul_O_r : forall (v : VectorSpace) (x : FT (VF v)), (Vmul v x (VO v)) = (VO v).
Proof.
move=> v x.
apply (Vadd_O_r_uniq v (Vmul v x (VO v)) (Vmul v x (VO v))).
rewrite - (Vmul_add_distr_l v x (VO v) (VO v)).
rewrite (Vadd_O_l v (VO v)).
by [].
Qed.

Lemma Vmul_O_l : forall (v : VectorSpace) (x : VT v), (Vmul v (FO (VF v)) x) = (VO v).
Proof.
move=> v x.
apply (Vadd_O_r_uniq v (Vmul v (FO (VF v)) x) (Vmul v (FO (VF v)) x)).
rewrite - (Vmul_add_distr_r v (FO (VF v)) (FO (VF v)) x).
rewrite (Fadd_O_l (VF v) (FO (VF v))).
by [].
Qed.

Lemma Vmul_eq_compat_l : forall (v : VectorSpace) (x : FT (VF v)) (y z : VT v), y = z -> (Vmul v x y) = (Vmul v x z).
Proof.
move=> v x y z H1.
rewrite H1.
by [].
Qed.

Lemma Vmul_eq_compat_r : forall (v : VectorSpace) (x : VT v) (y z : FT (VF v)), y = z -> (Vmul v y x) = (Vmul v z x).
Proof.
move=> v x y z H1.
rewrite H1.
by [].
Qed.

Lemma Vmul_eq_reg_l : forall (v : VectorSpace) (x : FT (VF v)) (y z : VT v), (Vmul v x y) = (Vmul v x z) -> x <> (FO (VF v)) -> y = z.
Proof.
move=> v x y z H1 H2.
rewrite - (Vmul_I_l v y).
rewrite - (Vmul_I_l v z).
rewrite - (Finv_l (VF v) x H2).
rewrite - (Vmul_assoc v (Finv (VF v) x) x y).
rewrite - (Vmul_assoc v (Finv (VF v) x) x z).
rewrite H1.
by [].
Qed.

Lemma Vmul_eq_reg_r : forall (v : VectorSpace) (x : VT v) (y z : FT (VF v)), (Vmul v y x) = (Vmul v z x) -> x <> (VO v) -> y = z.
Proof.
move=> v x y z H1 H2.
apply NNPP.
move=> H3.
apply H2.
rewrite - (Vmul_I_l v x).
rewrite - (Finv_l (VF v) (Fadd (VF v) y (Fopp (VF v) z))).
rewrite - (Vmul_assoc v (Finv (VF v) (Fadd (VF v) y (Fopp (VF v) z))) (Fadd (VF v) y (Fopp (VF v) z)) x).
suff: ((Vmul v (Fadd (VF v) y (Fopp (VF v) z)) x) = VO v).
move=> H4.
rewrite H4.
apply (Vmul_O_r v (Finv (VF v) (Fadd (VF v) y (Fopp (VF v) z)))).
apply (Vadd_eq_reg_r v (Vmul v z x) (Vmul v (Fadd (VF v) y (Fopp (VF v) z)) x) (VO v)).
rewrite (Vadd_O_l v (Vmul v z x)).
rewrite (Vmul_add_distr_r v y (Fopp (VF v) z) x).
rewrite (Vadd_assoc v (Vmul v y x) (Vmul v (Fopp (VF v) z) x) (Vmul v z x)).
rewrite - (Vmul_add_distr_r v (Fopp (VF v) z) z x).
rewrite (Fadd_opp_l (VF v) z).
rewrite (Vmul_O_l v x).
rewrite H1.
apply (Vadd_O_r v (Vmul v z x)).
move=> H4.
apply H3.
apply (Fminus_diag_uniq (VF v) y z H4).
Qed.

Lemma Vmul_integral : forall (v : VectorSpace) (x : FT (VF v)) (y : VT v), (Vmul v x y) = (VO v) -> x = (FO (VF v)) \/ y = (VO v).
Proof.
move=> v x y H1.
apply (NNPP (x = FO (VF v) \/ y = VO v)).
move=> H2.
apply H2.
right.
apply (Vmul_eq_reg_l v x y (VO v)).
rewrite H1.
rewrite (Vmul_O_r v x).
by [].
move=> H3.
apply H2.
left.
apply H3.
Qed.

Lemma Vmul_eq_O_compat : forall (v : VectorSpace) (x : FT (VF v)) (y : VT v), (x = (FO (VF v)) \/ y = (VO v)) -> (Vmul v x y) = (VO v).
Proof.
move=> v x y H1.
case H1.
move=> H2.
rewrite H2.
apply (Vmul_O_l v y).
move=> H2.
rewrite H2.
apply (Vmul_O_r v x).
Qed.

Lemma Vmul_eq_O_compat_r : forall (v : VectorSpace) (x : FT (VF v)) (y : VT v), x = (FO (VF v)) -> (Vmul v x y) = (VO v).
Proof.
move=> v x y H1.
rewrite H1.
apply (Vmul_O_l v y).
Qed.

Lemma Vmul_eq_O_compat_l : forall (v : VectorSpace) (x : FT (VF v)) (y : VT v), y = (VO v) -> (Vmul v x y) = (VO v).
Proof.
move=> v x y H1.
rewrite H1.
apply (Vmul_O_r v x).
Qed.

Lemma Vmul_neq_O_reg : forall (v : VectorSpace) (x : FT (VF v)) (y : VT v), (Vmul v x y) <> (VO v) -> x <> (FO (VF v)) /\ y <> (VO v).
Proof.
move=> v x y H1.
apply conj.
move=> H2.
apply H1.
rewrite H2.
apply (Vmul_O_l v y).
move=> H2.
apply H1.
rewrite H2.
apply (Vmul_O_r v x).
Qed.

Lemma Vmul_integral_contrapositive : forall (v : VectorSpace) (x : FT (VF v)) (y : VT v), x <> (FO (VF v)) /\ y <> (VO v) -> (Vmul v x y) <> (VO v).
Proof.
move=> v x y H1 H2.
apply (proj1 H1).
apply (Vmul_eq_reg_r v y x (FO (VF v))).
rewrite (Vmul_O_l v y).
apply H2.
apply (proj2 H1).
Qed.

Lemma Vmul_integral_contrapositive_currified : forall (v : VectorSpace) (x : FT (VF v)) (y : VT v), x <> (FO (VF v)) -> y <> (VO v) -> (Vmul v x y) <> (VO v).
Proof.
move=> v x y H1 H2 H3.
apply H1.
apply (Vmul_eq_reg_r v y x (FO (VF v))).
rewrite (Vmul_O_l v y).
apply H3.
apply H2.
Qed.

Lemma Vopp_eq_compat : forall (v : VectorSpace) (x y : VT v), x = y -> (Vopp v x) = (Vopp v y).
Proof.
move=> v x y H1.
rewrite H1.
by [].
Qed.

Lemma Vopp_O : forall (v : VectorSpace), (Vopp v (VO v)) = (VO v).
Proof.
move=> v.
apply (Vadd_O_r_uniq v (VO v) (Vopp v (VO v))).
apply (Vadd_opp_r v (VO v)).
Qed.

Lemma Vopp_eq_O_compat : forall (v : VectorSpace) (x : VT v), x = (VO v) -> (Vopp v x) = (VO v).
Proof.
move=> v x H1.
rewrite H1.
apply (Vopp_O v).
Qed.

Lemma Vopp_involutive : forall (v : VectorSpace) (x : VT v), (Vopp v (Vopp v x)) = x.
Proof.
move=> v x.
suff: x = Vopp v (Vopp v x).
move=> H1.
rewrite{2} H1.
by [].
apply (Vadd_opp_r_uniq v (Vopp v x)).
apply (Vadd_opp_l v x).
Qed.

Lemma Vopp_neq_O_compat : forall (v : VectorSpace) (x : VT v), x <> (VO v) -> (Vopp v x) <> (VO v).
Proof.
move=> v x H1.
move=> H2.
apply H1.
rewrite - (Vopp_involutive v x).
apply (Vopp_eq_O_compat v (Vopp v x) H2).
Qed.

Lemma Vopp_add_distr : forall (v : VectorSpace) (x y : VT v), (Vopp v (Vadd v x y)) = (Vadd v (Vopp v x) (Vopp v y)).
Proof.
move=> v x y.
suff: Vadd v (Vopp v x) (Vopp v y) = Vopp v (Vadd v x y).
move=> H1.
rewrite H1.
by [].
apply (Vadd_opp_r_uniq v (Vadd v x y)).
rewrite (Vadd_comm v x y).
rewrite - (Vadd_assoc v (Vadd v y x) (Vopp v x) (Vopp v y)).
rewrite (Vadd_assoc v y x (Vopp v x)).
rewrite (Vadd_opp_r v x).
rewrite (Vadd_O_r v y).
apply (Vadd_opp_r v y).
Qed.

Lemma Vopp_mul_distr_l : forall (v : VectorSpace) (x : FT (VF v)) (y : VT v), (Vopp v (Vmul v x y)) = (Vmul v (Fopp (VF v) x) y).
Proof.
move=> v x y.
suff: Vmul v (Fopp (VF v) x) y = Vopp v (Vmul v x y).
move=> H1.
rewrite H1.
by [].
apply (Vadd_opp_r_uniq v (Vmul v x y)).
rewrite - (Vmul_add_distr_r v x (Fopp (VF v) x) y).
rewrite (Fadd_opp_r (VF v) x).
apply (Vmul_O_l v y).
Qed.

Lemma Vopp_mul_distr_l_reverse : forall (v : VectorSpace) (x : FT (VF v)) (y : VT v), (Vmul v (Fopp (VF v) x) y) = (Vopp v (Vmul v x y)).
Proof.
move=> v x y.
rewrite (Vopp_mul_distr_l v x y).
reflexivity.
Qed.

Lemma Vopp_mul_distr_r : forall (v : VectorSpace) (x : FT (VF v)) (y : VT v), (Vopp v (Vmul v x y)) = (Vmul v x (Vopp v y)).
Proof.
move=> v x y.
suff: Vmul v x (Vopp v y) = Vopp v (Vmul v x y).
move=> H1.
rewrite H1.
by [].
apply (Vadd_opp_r_uniq v (Vmul v x y)).
rewrite - (Vmul_add_distr_l v x y (Vopp v y)).
rewrite (Vadd_opp_r v y).
apply (Vmul_O_r v x).
Qed.

Lemma Vopp_mul_distr_r_reverse : forall (v : VectorSpace) (x : FT (VF v)) (y : VT v), (Vmul v x (Vopp v y)) = (Vopp v (Vmul v x y)).
Proof.
move=> v x y.
rewrite (Vopp_mul_distr_r v x y).
reflexivity.
Qed.

Lemma Vmul_opp_opp : forall (v : VectorSpace) (x : FT (VF v)) (y : VT v), (Vmul v (Fopp (VF v) x) (Vopp v y)) = (Vmul v x y).
Proof.
move=> v x y.
rewrite (Vopp_mul_distr_l_reverse v x (Vopp v y)).
rewrite (Vopp_mul_distr_r_reverse v x y).
apply (Vopp_involutive v (Vmul v x y)).
Qed.

Lemma Vminus_O_r : forall (v : VectorSpace) (x : VT v), (Vadd v x (Vopp v (VO v))) = x.
Proof.
move=> v x.
rewrite (Vopp_O v).
apply (Vadd_O_r v x).
Qed.

Lemma Vminus_O_l : forall (v : VectorSpace) (x : VT v), (Vadd v (VO v) (Vopp v x)) = (Vopp v x).
Proof.
move=> v x.
apply (Vadd_O_l v (Vopp v x)).
Qed.

Lemma Vopp_minus_distr : forall (v : VectorSpace) (x y : VT v), (Vopp v (Vadd v x (Vopp v y))) = (Vadd v y (Vopp v x)).
Proof.
move=> v x y.
rewrite (Vopp_add_distr v x (Vopp v y)).
rewrite (Vopp_involutive v y).
apply (Vadd_comm v (Vopp v x) y).
Qed.

Lemma Vopp_minus_distr' : forall (v : VectorSpace) (x y : VT v), (Vopp v (Vadd v y (Vopp v x))) = (Vadd v x (Vopp v y)).
Proof.
move=> v x y.
rewrite (Vopp_add_distr v y (Vopp v x)).
rewrite (Vopp_involutive v x).
apply (Vadd_comm v (Vopp v y) x).
Qed.

Lemma Vminus_diag_eq : forall (v : VectorSpace) (x y : VT v), x = y -> (Vadd v x (Vopp v y)) = (VO v).
Proof.
move=> v x y H1.
rewrite H1.
apply (Vadd_opp_r v y).
Qed.

Lemma Vminus_diag_uniq : forall (v : VectorSpace) (x y : VT v), (Vadd v x (Vopp v y)) = (VO v) -> x = y.
Proof.
move=> v x y H1.
rewrite<- (Vadd_O_r v x).
rewrite<- (Vadd_opp_l v y).
rewrite<- (Vadd_O_l v y) at 3.
rewrite<- (Vadd_assoc v x (Vopp v y) y).
rewrite H1.
reflexivity.
Qed.

Lemma Vminus_diag_uniq_sym : forall (v : VectorSpace) (x y : VT v), (Vadd v y (Vopp v x)) = (VO v) -> x = y.
Proof.
move=> v x y H1.
rewrite (Vminus_diag_uniq v y x H1).
reflexivity.
Qed.

Lemma Vadd_minus : forall (v : VectorSpace) (x y : VT v), (Vadd v x (Vadd v y (Vopp v x))) = y.
Proof.
move=> v x y.
rewrite (Vadd_comm v y (Vopp v x)).
rewrite<- (Vadd_assoc v x (Vopp v x) y).
rewrite (Vadd_opp_r v x).
apply (Vadd_O_l v y).
Qed.

Lemma Vminus_eq_contra : forall (v : VectorSpace) (x y : VT v), x <> y -> (Vadd v x (Vopp v y)) <> (VO v).
Proof.
move=> v x y H1 H2.
apply H1.
apply (Vminus_diag_uniq v x y H2).
Qed.

Lemma Vminus_not_eq : forall (v : VectorSpace) (x y : VT v), (Vadd v x (Vopp v y)) <> (VO v) -> x <> y.
Proof.
move=> v x y H1 H2.
apply H1.
apply (Vminus_diag_eq v x y H2).
Qed.

Lemma Vminus_not_eq_right : forall (v : VectorSpace) (x y : VT v), (Vadd v y (Vopp v x)) <> (VO v) -> x <> y.
Proof.
move=> v x y H1 H2.
apply H1.
apply (Vminus_diag_eq v y x).
rewrite H2.
reflexivity.
Qed.

Lemma Vmul_minus_distr_l : forall (v : VectorSpace) (x : FT (VF v)) (y z : VT v), (Vmul v x (Vadd v y (Vopp v z))) = (Vadd v (Vmul v x y) (Vopp v (Vmul v x z))).
Proof.
move=> v x y z.
rewrite (Vmul_add_distr_l v x y (Vopp v z)).
rewrite (Vopp_mul_distr_r v x z).
reflexivity.
Qed.

End VectorSpace.