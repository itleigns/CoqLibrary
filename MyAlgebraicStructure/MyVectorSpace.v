Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "BasicProperty" as BasicProperty.
Add LoadPath "Tools" as Tools.

From mathcomp Require Import ssreflect.
Require Import Classical.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import MyAlgebraicStructure.MyField.
Require Import BasicProperty.MappingProperty.

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

Definition IsomorphicVS (F : Field) (v1 v2 : VectorSpace F) (f : VT F v1 -> VT F v2) := Bijective f /\ (forall (x y : VT F v1), f (Vadd F v1 x y) = Vadd F v2 (f x) (f y)) /\ (forall (c : FT F) (x : VT F v1), f (Vmul F v1 c x) = Vmul F v2 c (f x)).

Lemma IsomorphicChainVS : forall (F : Field) (v1 v2 v3 : VectorSpace F) (f : VT F v1 -> VT F v2) (g : VT F v2 -> VT F v3), IsomorphicVS F v1 v2 f -> IsomorphicVS F v2 v3 g -> IsomorphicVS F v1 v3 (fun (x : VT F v1) => g (f x)).
Proof.
move=> F v1 v2 v3 f g H1 H2.
apply conj.
apply (BijChain (VT F v1) (VT F v2) (VT F v3) f g (proj1 H1) (proj1 H2)).
apply conj.
move=> x y.
rewrite ((proj1 (proj2 H1)) x y).
apply ((proj1 (proj2 H2)) (f x) (f y)).
move=> c x.
rewrite (proj2 (proj2 H1) c x).
apply (proj2 (proj2 H2) c (f x)).
Qed.

Lemma IsomorphicInvVS : forall (F : Field) (v1 v2 : VectorSpace F) (f : VT F v1 -> VT F v2) (g : VT F v2 -> VT F v1), IsomorphicVS F v1 v2 f -> (forall (x : VT F v1), g (f x) = x) /\ (forall (y : VT F v2), f (g y) = y) -> IsomorphicVS F v2 v1 g.
Proof.
move=> F v1 v2 f g H1 H2.
apply conj.
exists f.
apply conj.
apply (proj2 H2).
apply (proj1 H2).
apply conj.
move=> x y.
apply (BijInj (VT F v1) (VT F v2) f (proj1 H1) (g (Vadd F v2 x y)) (Vadd F v1 (g x) (g y))).
rewrite (proj1 (proj2 H1) (g x) (g y)).
rewrite (proj2 H2 x).
rewrite (proj2 H2 y).
apply (proj2 H2 (Vadd F v2 x y)).
move=> c x.
apply (BijInj (VT F v1) (VT F v2) f (proj1 H1) (g (Vmul F v2 c x)) (Vmul F v1 c (g x))).
rewrite (proj2 (proj2 H1) c (g x)).
rewrite (proj2 H2 x).
apply (proj2 H2 (Vmul F v2 c x)).
Qed.

Definition Fn (F : Field) (N : nat) := ({m : nat | m < N} -> FT F).

Definition Fnadd (F : Field) (N : nat) := fun (f1 f2 : Fn F N) => (fun (n : {m : nat | m < N}) => Fadd F (f1 n) (f2 n)).

Definition Fnmul (F : Field) (N : nat) := fun (c : FT F) (f : Fn F N) => (fun (n : {m : nat | m < N}) => Fmul F c (f n)).

Definition Fnopp (F : Field) (N : nat) := fun (f : (Fn F N)) => (fun (n : {m : nat | m < N}) => Fopp F (f n)).

Definition Fnminus (F : Field) (N : nat) := fun (f1 f2 : (Fn F N)) => (Fnadd F N f1 (Fnopp F N f2)).

Definition FnO (F : Field) (N : nat) := (fun (n : {m : nat | m < N}) => FO F).

Lemma Fnadd_comm : forall (F : Field) (N : nat) (f1 f2 : Fn F N), (Fnadd F N f1 f2) = (Fnadd F N f2 f1).
Proof.
move=> F N f1 f2.
apply functional_extensionality.
move=> n.
apply (Fadd_comm F (f1 n) (f2 n)).
Qed.

Lemma Fnadd_assoc : forall (F : Field) (N : nat) (f1 f2 f3 : Fn F N), (Fnadd F N (Fnadd F N f1 f2) f3) = (Fnadd F N f1 (Fnadd F N f2 f3)).
Proof.
move=> F N f1 f2 f3.
apply functional_extensionality.
move=> n.
apply (Fadd_assoc F (f1 n) (f2 n) (f3 n)).
Qed.

Lemma Fnadd_O_l : forall (F : Field) (N : nat) (f : Fn F N), (Fnadd F N (FnO F N) f) = f.
Proof.
move=> F N f.
apply functional_extensionality.
move=> n.
apply (Fadd_O_l F (f n)).
Qed.

Lemma Fnadd_opp_r : forall (F : Field) (N : nat) (f : Fn F N), (Fnadd F N f (Fnopp F N f)) = (FnO F N).
Proof.
move=> F N f.
apply functional_extensionality.
move=> n.
apply (Fadd_opp_r F (f n)).
Qed.

Lemma Fnadd_distr_l : forall (F : Field) (N : nat) (c : FT F) (f1 f2 : Fn F N), (Fnmul F N c (Fnadd F N f1 f2)) = (Fnadd F N (Fnmul F N c f1) (Fnmul F N c f2)).
Proof.
move=> F N c f1 f2.
apply functional_extensionality.
move=> n.
apply (Fmul_add_distr_l F c (f1 n) (f2 n)).
Qed.

Lemma Fnadd_distr_r : forall (F : Field) (N : nat) (c1 c2 : FT F) (f : Fn F N), (Fnmul F N (Fadd F c1 c2) f) = (Fnadd F N (Fnmul F N c1 f) (Fnmul F N c2 f)).
Proof.
move=> F N c1 c2 f.
apply functional_extensionality.
move=> n.
apply (Fmul_add_distr_r F c1 c2 (f n)).
Qed.

Lemma Fnmul_assoc : forall (F : Field) (N : nat) (c1 c2 : FT F) (f : Fn F N), (Fnmul F N c1 (Fnmul F N c2 f)) = (Fnmul F N (Fmul F c1 c2) f).
Proof.
move=> F N c1 c2 f.
apply functional_extensionality.
move=> n.
unfold Fnmul.
rewrite (Fmul_assoc F c1 c2 (f n)).
reflexivity.
Qed.

Lemma Fnmul_I_l : forall (F : Field) (N : nat) (f : Fn F N), (Fnmul F N (FI F) f) = f.
Proof.
move=> F N f.
apply functional_extensionality.
move=> n.
apply (Fmul_I_l F (f n)).
Qed.

Definition FnVS (F : Field) (N : nat) := mkVectorSpace F (Fn F N) (FnO F N) (Fnadd F N) (Fnmul F N) (Fnopp F N) (Fnadd_comm F N) (Fnadd_assoc F N) (Fnadd_O_l F N) (Fnadd_opp_r F N) (Fnadd_distr_l F N) (Fnadd_distr_r F N) (Fnmul_assoc F N) (Fnmul_I_l F N).

Definition FVS (F : Field) := mkVectorSpace F (FT F) (FO F) (Fadd F) (Fmul F) (Fopp F) (Fadd_comm F) (Fadd_assoc F) (Fadd_O_l F) (Fadd_opp_r F) (Fmul_add_distr_l F) (Fmul_add_distr_r F) (Fmul_assoc_reverse F) (Fmul_I_l F).

End VectorSpace.
