Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "BasicProperty" as BasicProperty.

From mathcomp
Require Import ssreflect.
Require Import Classical.
Require Import MyAlgebraicStructure.MyField. 

Section VectorSpace.

Record VectorSpace (F : Field) : Type := mkVectorSpace
{
VT   : Type;
VO : VT;
Vadd : VT -> VT -> VT;
Vmul : (FT F) -> VT -> VT;
Vopp : VT -> VT;
Vadd_comm : forall (x y : VT), (Vadd x y) = (Vadd y x);
Vadd_assoc : forall (x y z : VT), (Vadd (Vadd x y) z) = (Vadd x (Vadd y z));
Vadd_O_l : forall x : VT, (Vadd VO x) = x;
Vadd_opp_r : forall x : VT, (Vadd x (Vopp x)) = VO;
Vmul_add_distr_l : forall (x : FT F) (y z : VT), (Vmul x (Vadd y z)) = (Vadd (Vmul x y) (Vmul x z));
Vmul_add_distr_r : forall (x y : FT F) (z : VT), (Vmul (Fadd F x y) z) = (Vadd (Vmul x z) (Vmul y z));
Vmul_assoc : forall (x y : FT F) (z : VT), (Vmul x (Vmul y z)) = (Vmul (Fmul F x y) z);
Vmul_I_l : forall x : VT, (Vmul (FI F) x) = x;
}.

Lemma Vadd_O_r : forall (F : Field) (v : VectorSpace F) (x : VT F v), (Vadd F v x (VO F v)) = x.
Proof.
move=> F v x.
rewrite (Vadd_comm F v x (VO F v)).
apply (Vadd_O_l F v x).
Qed.

Lemma Vadd_ne : forall (F : Field) (v : VectorSpace F) (x : VT F v), (Vadd F v x (VO F v)) = x /\ (Vadd F v (VO F v) x) = x.
Proof.
move=> F v x.
apply conj.
apply (Vadd_O_r F v x).
apply (Vadd_O_l F v x).
Qed.

Lemma Vadd_opp_l : forall (F : Field) (v : VectorSpace F) (x : VT F v), (Vadd F v (Vopp F v x) x) = (VO F v).
Proof.
move=> F v x.
rewrite (Vadd_comm F v (Vopp F v x) x).
apply (Vadd_opp_r F v x).
Qed.

Lemma Vadd_opp_r_uniq : forall (F : Field) (v : VectorSpace F) (x y : VT F v), (Vadd F v x y) = (VO F v) -> y = (Vopp F v x).
Proof.
move=> F v x y H1.
suff: (Vadd F v (Vopp F v x) (Vadd F v x y)) = (Vadd F v (Vopp F v x) (VO F v)).
move=> H2.
rewrite - (Vadd_O_r F v (Vopp F v x)).
rewrite - H2.
rewrite - (Vadd_assoc F v (Vopp F v x) x y).
rewrite (Vadd_opp_l F v x).
rewrite (Vadd_O_l F v y).
by [].
rewrite H1.
by [].
Qed.

Lemma Vadd_eq_compat_l : forall (F : Field) (v : VectorSpace F) (x y z : VT F v), y = z -> (Vadd F v x y) = (Vadd F v x z).
Proof.
move=> F v x y z H1.
rewrite H1.
by [].
Qed.

Lemma Vadd_eq_compat_r : forall (F : Field) (v : VectorSpace F) (x y z : VT F v), y = z -> (Vadd F v y x) = (Vadd F v z x).
Proof.
move=> F v x y z H1.
rewrite H1.
by [].
Qed.

Lemma Vadd_eq_reg_l : forall (F : Field) (v : VectorSpace F) (x y z : VT F v), (Vadd F v x y) = (Vadd F v x z) -> y = z.
Proof.
move=> F v x y z H1.
rewrite - (Vadd_O_l F v y).
rewrite - (Vadd_O_l F v z).
rewrite - (Vadd_opp_l F v x).
rewrite (Vadd_assoc F v (Vopp F v x) x y).
rewrite (Vadd_assoc F v (Vopp F v x) x z).
apply (Vadd_eq_compat_l F v (Vopp F v x) (Vadd F v x y) (Vadd F v x z)).
by [].
Qed.

Lemma Vadd_eq_reg_r : forall (F : Field) (v : VectorSpace F) (x y z : VT F v), (Vadd F v y x) = (Vadd F v z x) -> y = z.
Proof.
move=> F v x y z H1.
rewrite - (Vadd_O_r F v y).
rewrite - (Vadd_O_r F v z).
rewrite - (Vadd_opp_r F v x).
rewrite - (Vadd_assoc F v y x (Vopp F v x)).
rewrite - (Vadd_assoc F v z x (Vopp F v x)).
apply (Vadd_eq_compat_r F v (Vopp F v x) (Vadd F v y x) (Vadd F v z x)).
by [].
Qed.

Lemma Vadd_O_r_uniq : forall (F : Field) (v : VectorSpace F) (x y : VT F v), (Vadd F v x y) = x -> y = (VO F v).
Proof.
move=> F v x y H1.
rewrite - (Vadd_O_l F v y).
rewrite - (Vadd_opp_l F v x).
rewrite (Vadd_assoc F v (Vopp F v x) x y).
rewrite H1.
by [].
Qed.

Lemma Vmul_O_r : forall (F : Field) (v : VectorSpace F) (x : FT F), (Vmul F v x (VO F v)) = (VO F v).
Proof.
move=> F v x.
apply (Vadd_O_r_uniq F v (Vmul F v x (VO F v)) (Vmul F v x (VO F v))).
rewrite - (Vmul_add_distr_l F v x (VO F v) (VO F v)).
rewrite (Vadd_O_l F v (VO F v)).
by [].
Qed.

Lemma Vmul_O_l : forall (F : Field) (v : VectorSpace F) (x : VT F v), (Vmul F v (FO F) x) = (VO F v).
Proof.
move=> F v x.
apply (Vadd_O_r_uniq F v (Vmul F v (FO F) x) (Vmul F v (FO F) x)).
rewrite - (Vmul_add_distr_r F v (FO F) (FO F) x).
rewrite (Fadd_O_l F (FO F)).
by [].
Qed.

Lemma Vmul_eq_compat_l : forall (F : Field) (v : VectorSpace F) (x : FT F) (y z : VT F v), y = z -> (Vmul F v x y) = (Vmul F v x z).
Proof.
move=> F v x y z H1.
rewrite H1.
by [].
Qed.

Lemma Vmul_eq_compat_r : forall (F : Field) (v : VectorSpace F) (x : VT F v) (y z : FT F), y = z -> (Vmul F v y x) = (Vmul F v z x).
Proof.
move=> F v x y z H1.
rewrite H1.
by [].
Qed.

Lemma Vmul_eq_reg_l : forall (F : Field) (v : VectorSpace F) (x : FT F) (y z : VT F v), (Vmul F v x y) = (Vmul F v x z) -> x <> (FO F) -> y = z.
Proof.
move=> F v x y z H1 H2.
rewrite - (Vmul_I_l F v y).
rewrite - (Vmul_I_l F v z).
rewrite - (Finv_l F x H2).
rewrite - (Vmul_assoc F v (Finv F x) x y).
rewrite - (Vmul_assoc F v (Finv F x) x z).
rewrite H1.
by [].
Qed.

Lemma Vmul_eq_reg_r : forall (F : Field) (v : VectorSpace F) (x : VT F v) (y z : FT F), (Vmul F v y x) = (Vmul F v z x) -> x <> (VO F v) -> y = z.
Proof.
move=> F v x y z H1 H2.
apply NNPP.
move=> H3.
apply H2.
rewrite - (Vmul_I_l F v x).
rewrite - (Finv_l F (Fadd F y (Fopp F z))).
rewrite - (Vmul_assoc F v (Finv F (Fadd F y (Fopp F z))) (Fadd F y (Fopp F z)) x).
suff: ((Vmul F v (Fadd F y (Fopp F z)) x) = VO F v).
move=> H4.
rewrite H4.
apply (Vmul_O_r F v (Finv F (Fadd F y (Fopp F z)))).
apply (Vadd_eq_reg_r F v (Vmul F v z x) (Vmul F v (Fadd F y (Fopp F z)) x) (VO F v)).
rewrite (Vadd_O_l F v (Vmul F v z x)).
rewrite (Vmul_add_distr_r F v y (Fopp F z) x).
rewrite (Vadd_assoc F v (Vmul F v y x) (Vmul F v (Fopp F z) x) (Vmul F v z x)).
rewrite - (Vmul_add_distr_r F v (Fopp F z) z x).
rewrite (Fadd_opp_l F z).
rewrite (Vmul_O_l F v x).
rewrite H1.
apply (Vadd_O_r F v (Vmul F v z x)).
move=> H4.
apply H3.
apply (Fminus_diag_uniq F y z H4).
Qed.

Lemma Vmul_integral : forall (F : Field) (v : VectorSpace F) (x : FT F) (y : VT F v), (Vmul F v x y) = (VO F v) -> x = (FO F) \/ y = (VO F v).
Proof.
move=> F v x y H1.
apply (NNPP (x = FO F \/ y = VO F v)).
move=> H2.
apply H2.
right.
apply (Vmul_eq_reg_l F v x y (VO F v)).
rewrite H1.
rewrite (Vmul_O_r F v x).
by [].
move=> H3.
apply H2.
left.
apply H3.
Qed.

Lemma Vmul_eq_O_compat : forall (F : Field) (v : VectorSpace F) (x : FT F) (y : VT F v), (x = (FO F) \/ y = (VO F v)) -> (Vmul F v x y) = (VO F v).
Proof.
move=> F v x y H1.
case H1.
move=> H2.
rewrite H2.
apply (Vmul_O_l F v y).
move=> H2.
rewrite H2.
apply (Vmul_O_r F v x).
Qed.

Lemma Vmul_eq_O_compat_r : forall (F : Field) (v : VectorSpace F) (x : FT F) (y : VT F v), x = (FO F) -> (Vmul F v x y) = (VO F v).
Proof.
move=> F v x y H1.
rewrite H1.
apply (Vmul_O_l F v y).
Qed.

Lemma Vmul_eq_O_compat_l : forall (F : Field) (v : VectorSpace F) (x : FT F) (y : VT F v), y = (VO F v) -> (Vmul F v x y) = (VO F v).
Proof.
move=> F v x y H1.
rewrite H1.
apply (Vmul_O_r F v x).
Qed.

Lemma Vmul_neq_O_reg : forall (F : Field) (v : VectorSpace F) (x : FT F) (y : VT F v), (Vmul F v x y) <> (VO F v) -> x <> (FO F) /\ y <> (VO F v).
Proof.
move=> F v x y H1.
apply conj.
move=> H2.
apply H1.
rewrite H2.
apply (Vmul_O_l F v y).
move=> H2.
apply H1.
rewrite H2.
apply (Vmul_O_r F v x).
Qed.

Lemma Vmul_integral_contrapositive : forall (F : Field) (v : VectorSpace F) (x : FT F) (y : VT F v), x <> (FO F) /\ y <> (VO F v) -> (Vmul F v x y) <> (VO F v).
Proof.
move=> F v x y H1 H2.
apply (proj1 H1).
apply (Vmul_eq_reg_r F v y x (FO F)).
rewrite (Vmul_O_l F v y).
apply H2.
apply (proj2 H1).
Qed.

Lemma Vmul_integral_contrapositive_currified : forall (F : Field) (v : VectorSpace F) (x : FT F) (y : VT F v), x <> (FO F) -> y <> (VO F v) -> (Vmul F v x y) <> (VO F v).
Proof.
move=> F v x y H1 H2 H3.
apply H1.
apply (Vmul_eq_reg_r F v y x (FO F)).
rewrite (Vmul_O_l F v y).
apply H3.
apply H2.
Qed.

Lemma Vopp_eq_compat : forall (F : Field) (v : VectorSpace F) (x y : VT F v), x = y -> (Vopp F v x) = (Vopp F v y).
Proof.
move=> F v x y H1.
rewrite H1.
by [].
Qed.

Lemma Vopp_O : forall (F : Field) (v : VectorSpace F), (Vopp F v (VO F v)) = (VO F v).
Proof.
move=> F v.
apply (Vadd_O_r_uniq F v (VO F v) (Vopp F v (VO F v))).
apply (Vadd_opp_r F v (VO F v)).
Qed.

Lemma Vopp_eq_O_compat : forall (F : Field) (v : VectorSpace F) (x : VT F v), x = (VO F v) -> (Vopp F v x) = (VO F v).
Proof.
move=> F v x H1.
rewrite H1.
apply (Vopp_O F v).
Qed.

Lemma Vopp_involutive : forall (F : Field) (v : VectorSpace F) (x : VT F v), (Vopp F v (Vopp F v x)) = x.
Proof.
move=> F v x.
suff: x = Vopp F v (Vopp F v x).
move=> H1.
rewrite{2} H1.
by [].
apply (Vadd_opp_r_uniq F v (Vopp F v x)).
apply (Vadd_opp_l F v x).
Qed.

Lemma Vopp_neq_O_compat : forall (F : Field) (v : VectorSpace F) (x : VT F v), x <> (VO F v) -> (Vopp F v x) <> (VO F v).
Proof.
move=> F v x H1 H2.
apply H1.
rewrite - (Vopp_involutive F v x).
apply (Vopp_eq_O_compat F v (Vopp F v x) H2).
Qed.

Lemma Vopp_add_distr : forall (F : Field) (v : VectorSpace F) (x y : VT F v), (Vopp F v (Vadd F v x y)) = (Vadd F v (Vopp F v x) (Vopp F v y)).
Proof.
move=> F v x y.
suff: Vadd F v (Vopp F v x) (Vopp F v y) = Vopp F v (Vadd F v x y).
move=> H1.
rewrite H1.
by [].
apply (Vadd_opp_r_uniq F v (Vadd F v x y)).
rewrite (Vadd_comm F v x y).
rewrite - (Vadd_assoc F v (Vadd F v y x) (Vopp F v x) (Vopp F v y)).
rewrite (Vadd_assoc F v y x (Vopp F v x)).
rewrite (Vadd_opp_r F v x).
rewrite (Vadd_O_r F v y).
apply (Vadd_opp_r F v y).
Qed.

Lemma Vopp_mul_distr_l : forall (F : Field) (v : VectorSpace F) (x : FT F) (y : VT F v), (Vopp F v (Vmul F v x y)) = (Vmul F v (Fopp F x) y).
Proof.
move=> F v x y.
suff: Vmul F v (Fopp F x) y = Vopp F v (Vmul F v x y).
move=> H1.
rewrite H1.
by [].
apply (Vadd_opp_r_uniq F v (Vmul F v x y)).
rewrite - (Vmul_add_distr_r F v x (Fopp F x) y).
rewrite (Fadd_opp_r F x).
apply (Vmul_O_l F v y).
Qed.

Lemma Vopp_mul_distr_l_reverse : forall (F : Field) (v : VectorSpace F) (x : FT F) (y : VT F v), (Vmul F v (Fopp F x) y) = (Vopp F v (Vmul F v x y)).
Proof.
move=> F v x y.
rewrite (Vopp_mul_distr_l F v x y).
reflexivity.
Qed.

Lemma Vopp_mul_distr_r : forall (F : Field) (v : VectorSpace F) (x : FT F) (y : VT F v), (Vopp F v (Vmul F v x y)) = (Vmul F v x (Vopp F v y)).
Proof.
move=> F v x y.
suff: Vmul F v x (Vopp F v y) = Vopp F v (Vmul F v x y).
move=> H1.
rewrite H1.
by [].
apply (Vadd_opp_r_uniq F v (Vmul F v x y)).
rewrite - (Vmul_add_distr_l F v x y (Vopp F v y)).
rewrite (Vadd_opp_r F v y).
apply (Vmul_O_r F v x).
Qed.

Lemma Vopp_mul_distr_r_reverse : forall (F : Field) (v : VectorSpace F) (x : FT F) (y : VT F v), (Vmul F v x (Vopp F v y)) = (Vopp F v (Vmul F v x y)).
Proof.
move=> F v x y.
rewrite (Vopp_mul_distr_r F v x y).
reflexivity.
Qed.

Lemma Vmul_opp_opp : forall (F : Field) (v : VectorSpace F) (x : FT F) (y : VT F v), (Vmul F v (Fopp F x) (Vopp F v y)) = (Vmul F v x y).
Proof.
move=> F v x y.
rewrite (Vopp_mul_distr_l_reverse F v x (Vopp F v y)).
rewrite (Vopp_mul_distr_r_reverse F v x y).
apply (Vopp_involutive F v (Vmul F v x y)).
Qed.

Lemma Vminus_O_r : forall (F : Field) (v : VectorSpace F) (x : VT F v), (Vadd F v x (Vopp F v (VO F v))) = x.
Proof.
move=> F v x.
rewrite (Vopp_O F v).
apply (Vadd_O_r F v x).
Qed.

Lemma Vminus_O_l : forall (F : Field) (v : VectorSpace F) (x : VT F v), (Vadd F v (VO F v) (Vopp F v x)) = (Vopp F v x).
Proof.
move=> F v x.
apply (Vadd_O_l F v (Vopp F v x)).
Qed.

Lemma Vopp_minus_distr : forall (F : Field) (v : VectorSpace F) (x y : VT F v), (Vopp F v (Vadd F v x (Vopp F v y))) = (Vadd F v y (Vopp F v x)).
Proof.
move=> F v x y.
rewrite (Vopp_add_distr F v x (Vopp F v y)).
rewrite (Vopp_involutive F v y).
apply (Vadd_comm F v (Vopp F v x) y).
Qed.

Lemma Vopp_minus_distr' : forall (F : Field) (v : VectorSpace F) (x y : VT F v), (Vopp F v (Vadd F v y (Vopp F v x))) = (Vadd F v x (Vopp F v y)).
Proof.
move=> F v x y.
rewrite (Vopp_add_distr F v y (Vopp F v x)).
rewrite (Vopp_involutive F v x).
apply (Vadd_comm F v (Vopp F v y) x).
Qed.

Lemma Vminus_diag_eq : forall (F : Field) (v : VectorSpace F) (x y : VT F v), x = y -> (Vadd F v x (Vopp F v y)) = (VO F v).
Proof.
move=> F v x y H1.
rewrite H1.
apply (Vadd_opp_r F v y).
Qed.

Lemma Vminus_diag_uniq : forall (F : Field) (v : VectorSpace F) (x y : VT F v), (Vadd F v x (Vopp F v y)) = (VO F v) -> x = y.
Proof.
move=> F v x y H1.
rewrite<- (Vadd_O_r F v x).
rewrite<- (Vadd_opp_l F v y).
rewrite<- (Vadd_O_l F v y) at 3.
rewrite<- (Vadd_assoc F v x (Vopp F v y) y).
rewrite H1.
reflexivity.
Qed.

Lemma Vminus_diag_uniq_sym : forall (F : Field) (v : VectorSpace F) (x y : VT F v), (Vadd F v y (Vopp F v x)) = (VO F v) -> x = y.
Proof.
move=> F v x y H1.
rewrite (Vminus_diag_uniq F v y x H1).
reflexivity.
Qed.

Lemma Vadd_minus : forall (F : Field) (v : VectorSpace F) (x y : VT F v), (Vadd F v x (Vadd F v y (Vopp F v x))) = y.
Proof.
move=> F v x y.
rewrite (Vadd_comm F v y (Vopp F v x)).
rewrite<- (Vadd_assoc F v x (Vopp F v x) y).
rewrite (Vadd_opp_r F v x).
apply (Vadd_O_l F v y).
Qed.

Lemma Vminus_eq_contra : forall (F : Field) (v : VectorSpace F) (x y : VT F v), x <> y -> (Vadd F v x (Vopp F v y)) <> (VO F v).
Proof.
move=> F v x y H1 H2.
apply H1.
apply (Vminus_diag_uniq F v x y H2).
Qed.

Lemma Vminus_not_eq : forall (F : Field) (v : VectorSpace F) (x y : VT F v), (Vadd F v x (Vopp F v y)) <> (VO F v) -> x <> y.
Proof.
move=> F v x y H1 H2.
apply H1.
apply (Vminus_diag_eq F v x y H2).
Qed.

Lemma Vminus_not_eq_right : forall (F : Field) (v : VectorSpace F) (x y : VT F v), (Vadd F v y (Vopp F v x)) <> (VO F v) -> x <> y.
Proof.
move=> F v x y H1 H2.
apply H1.
apply (Vminus_diag_eq F v y x).
rewrite H2.
reflexivity.
Qed.

Lemma Vmul_minus_distr_l : forall (F : Field) (v : VectorSpace F) (x : FT F) (y z : VT F v), (Vmul F v x (Vadd F v y (Vopp F v z))) = (Vadd F v (Vmul F v x y) (Vopp F v (Vmul F v x z))).
Proof.
move=> F v x y z.
rewrite (Vmul_add_distr_l F v x y (Vopp F v z)).
rewrite (Vopp_mul_distr_r F v x z).
reflexivity.
Qed.

End VectorSpace.