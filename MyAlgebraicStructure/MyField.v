Add LoadPath "BasicProperty" as BasicProperty.

From mathcomp
Require Import ssreflect.
Require Import Classical.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import BasicProperty.NatProperty.

Section Field.

Record Field : Type := mkField
{
FT   : Type;
FO : FT;
FI : FT;
Fadd : FT -> FT -> FT;
Fmul : FT -> FT -> FT;
Fopp : FT -> FT;
Finv : FT -> FT;
Fadd_assoc : forall (x y z : FT), (Fadd (Fadd x y) z) = (Fadd x (Fadd y z));
Fmul_assoc : forall (x y z : FT), (Fmul (Fmul x y) z) = (Fmul x (Fmul y z));
Fadd_comm : forall (x y : FT), (Fadd x y) = (Fadd y x);
Fmul_comm : forall (x y : FT), (Fmul x y) = (Fmul y x);
Fadd_O_l : forall x : FT, (Fadd FO x) = x;
Fmul_I_l : forall x : FT, (Fmul FI x) = x;
Fadd_opp_r : forall x : FT, (Fadd x (Fopp x)) = FO;
Finv_l : forall x : FT, x <> FO -> (Fmul (Finv x) x) = FI;
Fmul_add_distr_l : forall (x y z : FT), (Fmul x (Fadd y z)) = (Fadd (Fmul x y) (Fmul x z))
}.

Lemma Fadd_O_r : forall (f : Field) (x : FT f), (Fadd f x (FO f)) = x.
Proof.
move=> f x.
rewrite (Fadd_comm f x (FO f)).
apply (Fadd_O_l f x).
Qed.

Lemma Fadd_ne : forall (f : Field) (x : FT f), (Fadd f x (FO f)) = x /\ (Fadd f (FO f) x) = x.
Proof.
move=> f x.
apply conj.
apply (Fadd_O_r f x).
apply (Fadd_O_l f x).
Qed.

Lemma Fadd_opp_l : forall (f : Field) (x : FT f), (Fadd f (Fopp f x) x) = (FO f).
Proof.
move=> f x.
rewrite (Fadd_comm f (Fopp f x) x).
apply (Fadd_opp_r f x).
Qed.

Lemma Fadd_opp_r_uniq : forall (f : Field) (x y : FT f), (Fadd f x y) = (FO f) -> y = (Fopp f x).
Proof.
move=> f x y H1.
suff: (Fadd f (Fopp f x) (Fadd f x y)) = (Fadd f (Fopp f x) (FO f)).
move=> H2.
rewrite - (Fadd_O_r f (Fopp f x)).
rewrite - H2.
rewrite - (Fadd_assoc f (Fopp f x) x y).
rewrite (Fadd_opp_l f x).
rewrite (Fadd_O_l f y).
by [].
rewrite H1.
by [].
Qed.

Lemma Fadd_eq_compat_l : forall (f : Field) (x y z : FT f), y = z -> (Fadd f x y) = (Fadd f x z).
Proof.
move=> f x y z H1.
rewrite H1.
by [].
Qed.

Lemma Fadd_eq_compat_r : forall (f : Field) (x y z : FT f), y = z -> (Fadd f y x) = (Fadd f z x).
Proof.
move=> f x y z H1.
rewrite H1.
by [].
Qed.

Lemma Fadd_eq_reg_l : forall (f : Field) (x y z : FT f), (Fadd f x y) = (Fadd f x z) -> y = z.
move=> f x y z H1.
rewrite - (Fadd_O_l f y).
rewrite - (Fadd_O_l f z).
rewrite - (Fadd_opp_l f x).
rewrite (Fadd_assoc f (Fopp f x) x y).
rewrite (Fadd_assoc f (Fopp f x) x z).
apply (Fadd_eq_compat_l f (Fopp f x) (Fadd f x y) (Fadd f x z)).
by [].
Qed.

Lemma Fadd_eq_reg_r : forall (f : Field) (x y z : FT f), (Fadd f y x) = (Fadd f z x) -> y = z.
move=> f x y z H1.
rewrite - (Fadd_O_r f y).
rewrite - (Fadd_O_r f z).
rewrite - (Fadd_opp_r f x).
rewrite - (Fadd_assoc f y x (Fopp f x)).
rewrite - (Fadd_assoc f z x (Fopp f x)).
apply (Fadd_eq_compat_r f (Fopp f x) (Fadd f y x) (Fadd f z x)).
by [].
Qed.

Lemma Fadd_O_r_uniq : forall (f : Field) (x y : FT f), (Fadd f x y) = x -> y = (FO f).
Proof.
move=> f x y H1.
rewrite - (Fadd_O_l f y).
rewrite - (Fadd_opp_l f x).
rewrite (Fadd_assoc f (Fopp f x) x y).
rewrite H1.
by [].
Qed.

Lemma Finv_r : forall (f : Field) (x : FT f), x <> (FO f) -> (Fmul f x (Finv f x)) = (FI f).
Proof.
move=> f x H1.
rewrite (Fmul_comm f x (Finv f x)).
apply (Finv_l f x H1).
Qed.

Lemma Finv_l_sym : forall (f : Field) (x : FT f), x <> (FO f) -> (FI f) = (Fmul f (Finv f x) x).
Proof.
move=> f x H1.
rewrite (Finv_l f x H1).
by [].
Qed.

Lemma Finv_r_sym : forall (f : Field) (x : FT f), x <> (FO f) -> (FI f) = (Fmul f x (Finv f x)).
Proof.
move=> f x H1.
rewrite (Finv_r f x H1).
by [].
Qed.

Lemma Fmul_O_r : forall (f : Field) (x : FT f), (Fmul f x (FO f)) = (FO f).
move=> f x.
apply (Fadd_O_r_uniq f (Fmul f x (FO f)) (Fmul f x (FO f))).
rewrite - (Fmul_add_distr_l f x (FO f) (FO f)).
rewrite (Fadd_O_l f (FO f)).
by [].
Qed.

Lemma Fmul_O_l : forall (f : Field) (x : FT f), (Fmul f (FO f) x) = (FO f).
move=> f x.
rewrite (Fmul_comm f (FO f) x).
apply (Fmul_O_r f x).
Qed.

Lemma Fmul_ne : forall (f : Field) (x : FT f), (Fmul f x (FI f)) = x /\ (Fmul f (FI f) x) = x.
move=> f x.
apply conj.
rewrite (Fmul_comm f x (FI f)).
apply (Fmul_I_l f x).
apply (Fmul_I_l f x).
Qed.

Lemma Fmul_I_r : forall (f : Field) (x : FT f), (Fmul f x (FI f)) = x.
Proof.
move=> f x.
rewrite (Fmul_comm f x (FI f)).
apply (Fmul_I_l f x).
Qed.

Lemma Fmul_eq_compat_l : forall (f : Field) (x y z : FT f), y = z -> (Fmul f x y) = (Fmul f x z).
Proof.
move=> f x y z H1.
rewrite H1.
by [].
Qed.

Lemma Fmul_eq_compat_r : forall (f : Field) (x y z : FT f), y = z -> (Fmul f y x) = (Fmul f z x).
Proof.
move=> f x y z H1.
rewrite H1.
by [].
Qed.

Lemma Fmul_eq_reg_l : forall (f : Field) (x y z : FT f), (Fmul f x y) = (Fmul f x z) -> x <> (FO f) -> y = z.
Proof.
move=> f x y z H1 H2.
rewrite - (Fmul_I_l f y).
rewrite - (Fmul_I_l f z).
rewrite - (Finv_l f x H2).
rewrite (Fmul_assoc f (Finv f x) x y).
rewrite (Fmul_assoc f (Finv f x) x z).
rewrite H1.
by [].
Qed.

Lemma Fmul_eq_reg_r : forall (f : Field) (x y z : FT f), (Fmul f y x) = (Fmul f z x) -> x <> (FO f) -> y = z.
Proof.
move=> f x y z H1 H2.
rewrite - (Fmul_I_r f y).
rewrite - (Fmul_I_r f z).
rewrite - (Finv_r f x H2).
rewrite - (Fmul_assoc f y x (Finv f x)).
rewrite - (Fmul_assoc f z x (Finv f x)).
rewrite H1.
by [].
Qed.

Lemma Fmul_integral : forall (f : Field) (x y : FT f), (Fmul f x y) = (FO f) -> x = (FO f) \/ y = (FO f).
Proof.
move=> f x y H1.
apply (NNPP (x = FO f \/ y = FO f)).
move=> H2.
apply H2.
right.
apply (Fmul_eq_reg_l f x y (FO f)).
rewrite H1.
rewrite (Fmul_O_r f x).
by [].
move=> H3.
apply H2.
left.
apply H3.
Qed.

Lemma Fmul_eq_O_compat : forall (f : Field) (x y : FT f), (x = (FO f) \/ y = (FO f)) -> (Fmul f x y) = (FO f).
Proof.
move=> f x y H1.
case H1.
move=> H2.
rewrite H2.
apply (Fmul_O_l f y).
move=> H2.
rewrite H2.
apply (Fmul_O_r f x).
Qed.

Lemma Fmul_eq_O_compat_r : forall (f : Field) (x y : FT f), x = (FO f) -> (Fmul f x y) = (FO f).
Proof.
move=> f x y H1.
rewrite H1.
apply (Fmul_O_l f y).
Qed.

Lemma Fmul_eq_O_compat_l : forall (f : Field) (x y : FT f), y = (FO f) -> (Fmul f x y) = (FO f).
Proof.
move=> f x y H1.
rewrite H1.
apply (Fmul_O_r f x).
Qed.

Lemma Fmul_neq_O_reg : forall (f : Field) (x y : FT f), (Fmul f x y) <> (FO f) -> x <> (FO f) /\ y <> (FO f).
Proof.
move=> f x y H1.
apply conj.
move=> H2.
apply H1.
rewrite H2.
apply (Fmul_O_l f y).
move=> H2.
apply H1.
rewrite H2.
apply (Fmul_O_r f x).
Qed.

Lemma Fmul_integral_contrapositive : forall (f : Field) (x y : FT f), x <> (FO f) /\ y <> (FO f) -> (Fmul f x y) <> (FO f).
Proof.
move=> f x y H1.
move=> H2.
apply (proj1 H1).
apply (Fmul_eq_reg_r f y x (FO f)).
rewrite (Fmul_O_l f y).
apply H2.
apply (proj2 H1).
Qed.

Lemma Fmul_integral_contrapositive_currified : forall (f : Field) (x y : FT f), x <> (FO f) -> y <> (FO f) -> (Fmul f x y) <> (FO f).
Proof.
move=> f x y H1 H2.
move=> H3.
apply H1.
apply (Fmul_eq_reg_r f y x (FO f)).
rewrite (Fmul_O_l f y).
apply H3.
apply H2.
Qed.

Lemma Fmul_add_distr_r : forall (f : Field) (x y z : FT f), (Fmul f (Fadd f x y) z) = (Fadd f (Fmul f x z) (Fmul f y z)).
Proof.
move=> f x y z.
rewrite (Fmul_comm f (Fadd f x y) z).
rewrite (Fmul_add_distr_l f z x y).
rewrite (Fmul_comm f x z).
rewrite (Fmul_comm f y z).
by [].
Qed.

Lemma Fopp_eq_compat : forall (f : Field) (x y : FT f), x = y -> (Fopp f x) = (Fopp f y).
Proof.
move=> f x y H1.
rewrite H1.
by [].
Qed.

Lemma Fopp_O : forall (f : Field), (Fopp f (FO f)) = (FO f).
Proof.
Proof.
move=> f.
apply (Fadd_O_r_uniq f (FO f) (Fopp f (FO f))).
apply (Fadd_opp_r f (FO f)).
Qed.

Lemma Fopp_eq_O_compat : forall (f : Field) (x : FT f), x = (FO f) -> (Fopp f x) = (FO f).
move=> f x H1.
rewrite H1.
apply (Fopp_O f).
Qed.

Lemma Fopp_involutive : forall (f : Field) (x : FT f), (Fopp f (Fopp f x)) = x.
move=> f x.
suff: x = Fopp f (Fopp f x).
move=> H1.
rewrite{2} H1.
by [].
apply (Fadd_opp_r_uniq f (Fopp f x)).
apply (Fadd_opp_l f x).
Qed.

Lemma Fopp_neq_O_compat : forall (f : Field) (x : FT f), x <> (FO f) -> (Fopp f x) <> (FO f).
move=> f x H1.
move=> H2.
apply H1.
rewrite - (Fopp_involutive f x).
apply (Fopp_eq_O_compat f (Fopp f x) H2).
Qed.

Lemma Fopp_add_distr : forall (f : Field) (x y : FT f), (Fopp f (Fadd f x y)) = (Fadd f (Fopp f x) (Fopp f y)).
Proof.
move=> f x y.
suff: Fadd f (Fopp f x) (Fopp f y) = Fopp f (Fadd f x y).
move=> H1.
rewrite H1.
by [].
apply (Fadd_opp_r_uniq f (Fadd f x y)).
rewrite (Fadd_comm f x y).
rewrite - (Fadd_assoc f (Fadd f y x) (Fopp f x) (Fopp f y)).
rewrite (Fadd_assoc f y x (Fopp f x)).
rewrite (Fadd_opp_r f x).
rewrite (Fadd_O_r f y).
apply (Fadd_opp_r f y).
Qed.

Lemma Fopp_mul_distr_l : forall (f : Field) (x y : FT f), (Fopp f (Fmul f x y)) = (Fmul f (Fopp f x) y).
Proof.
move=> f x y.
suff: Fmul f (Fopp f x) y = Fopp f (Fmul f x y).
move=> H1.
rewrite H1.
by [].
apply (Fadd_opp_r_uniq f (Fmul f x y)).
rewrite - (Fmul_add_distr_r f x (Fopp f x) y).
rewrite (Fadd_opp_r f x).
apply (Fmul_O_l f y).
Qed.

Lemma Fopp_mul_distr_l_reverse : forall (f : Field) (x y : FT f), (Fmul f (Fopp f x) y) = (Fopp f (Fmul f x y)).
Proof.
move=> f x y.
rewrite (Fopp_mul_distr_l f x y).
reflexivity.
Qed.

Lemma Fopp_mul_distr_r : forall (f : Field) (x y : FT f), (Fopp f (Fmul f x y)) = (Fmul f x (Fopp f y)).
Proof.
move=> f x y.
suff: Fmul f x (Fopp f y) = Fopp f (Fmul f x y).
move=> H1.
rewrite H1.
by [].
apply (Fadd_opp_r_uniq f (Fmul f x y)).
rewrite - (Fmul_add_distr_l f x y (Fopp f y)).
rewrite (Fadd_opp_r f y).
apply (Fmul_O_r f x).
Qed.

Lemma Fopp_mul_distr_r_reverse : forall (f : Field) (x y : FT f), (Fmul f x (Fopp f y)) = (Fopp f (Fmul f x y)).
Proof.
move=> f x y.
rewrite (Fopp_mul_distr_r f x y).
reflexivity.
Qed.

Lemma Fmul_opp_opp : forall (f : Field) (x y : FT f), (Fmul f (Fopp f x) (Fopp f y)) = (Fmul f x y).
Proof.
move=> f x y.
rewrite (Fopp_mul_distr_l_reverse f x (Fopp f y)).
rewrite (Fopp_mul_distr_r_reverse f x y).
apply (Fopp_involutive f (Fmul f x y)).
Qed.

Lemma Fminus_O_r : forall (f : Field) (x : FT f), (Fadd f x (Fopp f (FO f))) = x.
Proof.
move=> f x.
rewrite (Fopp_O f).
apply (Fadd_O_r f x).
Qed.

Lemma Fminus_O_l : forall (f : Field) (x : FT f), (Fadd f (FO f) (Fopp f x)) = (Fopp f x).
Proof.
move=> f x.
apply (Fadd_O_l f (Fopp f x)).
Qed.

Lemma Fopp_minus_distr : forall (f : Field) (x y : FT f), (Fopp f (Fadd f x (Fopp f y))) = (Fadd f y (Fopp f x)).
Proof.
move=> f x y.
rewrite (Fopp_add_distr f x (Fopp f y)).
rewrite (Fopp_involutive f y).
apply (Fadd_comm f (Fopp f x) y).
Qed.

Lemma Fopp_minus_distr' : forall (f : Field) (x y : FT f), (Fopp f (Fadd f y (Fopp f x))) = (Fadd f x (Fopp f y)).
Proof.
move=> f x y.
rewrite (Fopp_add_distr f y (Fopp f x)).
rewrite (Fopp_involutive f x).
apply (Fadd_comm f (Fopp f y) x).
Qed.

Lemma Fminus_diag_eq : forall (f : Field) (x y : FT f), x = y -> (Fadd f x (Fopp f y)) = (FO f).
Proof.
move=> f x y H1.
rewrite H1.
apply (Fadd_opp_r f y).
Qed.

Lemma Fminus_diag_uniq : forall (f : Field) (x y : FT f), (Fadd f x (Fopp f y)) = (FO f) -> x = y.
Proof.
move=> f x y H1.
rewrite<- (Fadd_O_r f x).
rewrite<- (Fadd_opp_l f y).
rewrite<- (Fadd_O_l f y) at 3.
rewrite<- (Fadd_assoc f x (Fopp f y) y).
rewrite H1.
reflexivity.
Qed.

Lemma Fminus_diag_uniq_sym : forall (f : Field) (x y : FT f), (Fadd f y (Fopp f x)) = (FO f) -> x = y.
Proof.
move=> f x y H1.
rewrite (Fminus_diag_uniq f y x H1).
reflexivity.
Qed.

Lemma Fadd_minus : forall (f : Field) (x y : FT f), (Fadd f x (Fadd f y (Fopp f x))) = y.
Proof.
move=> f x y.
rewrite (Fadd_comm f y (Fopp f x)).
rewrite<- (Fadd_assoc f x (Fopp f x) y).
rewrite (Fadd_opp_r f x).
apply (Fadd_O_l f y).
Qed.

Lemma Fminus_eq_contra : forall (f : Field) (x y : FT f), x <> y -> (Fadd f x (Fopp f y)) <> (FO f).
Proof.
move=> f x y H1 H2.
apply H1.
apply (Fminus_diag_uniq f x y H2).
Qed.

Lemma Fminus_not_eq : forall (f : Field) (x y : FT f), (Fadd f x (Fopp f y)) <> (FO f) -> x <> y.
Proof.
move=> f x y H1 H2.
apply H1.
apply (Fminus_diag_eq f x y H2).
Qed.

Lemma Fminus_not_eq_right : forall (f : Field) (x y : FT f), (Fadd f y (Fopp f x)) <> (FO f) -> x <> y.
Proof.
move=> f x y H1 H2.
apply H1.
apply (Fminus_diag_eq f y x).
rewrite H2.
reflexivity.
Qed.

Lemma Fmul_minus_distr_l : forall (f : Field) (x y z : FT f), (Fmul f x (Fadd f y (Fopp f z))) = (Fadd f (Fmul f x y) (Fopp f (Fmul f x z))).
Proof.
move=> f x y z.
rewrite (Fmul_add_distr_l f x y (Fopp f z)).
rewrite (Fopp_mul_distr_r f x z).
reflexivity.
Qed.

Lemma Fmul_inv_r_uniq : forall (f : Field) (x y : FT f), (Fmul f x y) = (FI f) -> y = (Finv f x).
Proof.
move=> f.
elim (classic ((FO f) = (FI f))).
move=> H1.
suff: (forall (x : FT f), x = (FO f)).
move=> H2 x y H3.
rewrite (H2 (Finv f x)).
apply (H2 y).
move=> x.
rewrite<- (Fmul_O_r f x).
rewrite H1.
rewrite (Fmul_I_r f x).
reflexivity.
move=> H1 x y H2.
suff: (x <> (FO f)).
move=> H3.
rewrite<- (Fmul_I_l f y).
rewrite<- (Finv_l f x H3).
rewrite (Fmul_assoc f (Finv f x) x y).
rewrite H2.
apply (Fmul_I_r f (Finv f x)).
move=> H3.
apply H1.
rewrite<- H2.
rewrite H3.
rewrite (Fmul_O_l f y).
reflexivity.
Qed.

Lemma Finv_1 : forall (f : Field), (Finv f (FI f)) = (FI f).
Proof.
move=> f.
rewrite{2} (Fmul_inv_r_uniq f (FI f) (FI f)).
reflexivity.
apply (Fmul_I_r f (FI f)).
Qed.

Lemma Finv_neq_O_compat : forall (f : Field) (x : FT f), x <> (FO f) -> (Finv f x) <> (FO f).
Proof.
move=> f.
elim (classic ((FO f) = (FI f))).
move=> H1.
suff: (forall (x : FT f), x = (FO f)).
move=> H2 x H3 H4.
apply H3.
apply (H2 x).
move=> x.
rewrite<- (Fmul_O_r f x).
rewrite H1.
rewrite (Fmul_I_r f x).
reflexivity.
move=> H1 x H2 H3.
apply H1.
rewrite (Finv_r_sym f x H2).
rewrite H3.
rewrite (Fmul_O_r f x).
reflexivity.
Qed.

Lemma Finv_involutive : forall (f : Field) (x : FT f), x <> (FO f) -> (Finv f (Finv f x)) = x.
Proof.
move=> f x H1.
rewrite{2} (Fmul_inv_r_uniq f (Finv f x) x).
reflexivity.
apply (Finv_l f x H1).
Qed.

Lemma Finv_mul_distr : forall (f : Field) (x y : FT f), x <> (FO f) -> y <> (FO f) -> (Finv f (Fmul f x y)) = (Fmul f (Finv f x) (Finv f y)).
Proof.
move=> f x y H1 H2.
rewrite (Fmul_inv_r_uniq f (Fmul f x y) (Fmul f (Finv f x) (Finv f y))).
reflexivity.
rewrite (Fmul_comm f x y).
rewrite - (Fmul_assoc f (Fmul f y x) (Finv f x) (Finv f y)).
rewrite (Fmul_assoc f y x (Finv f x)).
rewrite (Finv_r f x H1).
rewrite (Fmul_I_r f y).
apply (Finv_r f y H2).
Qed.

Lemma Fopp_inv_permute : forall (f : Field) (x : FT f), x <> (FO f) -> (Fopp f (Finv f x)) = (Finv f (Fopp f x)).
Proof.
move=> f x H1.
rewrite (Fmul_inv_r_uniq f (Fopp f x) (Fopp f (Finv f x))).
reflexivity.
rewrite (Fmul_opp_opp f x (Finv f x)).
apply (Finv_r f x H1).
Qed.

Lemma Finv_r_simpl_r : forall (f : Field) (x y : FT f), x <> (FO f) -> (Fmul f (Fmul f x (Finv f x)) y) = y.
Proof.
move=> f x y H1.
rewrite (Finv_r f x H1).
rewrite (Fmul_I_l f y).
reflexivity.
Qed.

Lemma Finv_r_simpl_l : forall (f : Field) (x y : FT f), x <> (FO f) -> (Fmul f (Fmul f y x) (Finv f x)) = y.
Proof.
move=> f x y H1.
rewrite (Fmul_assoc f y x (Finv f x)).
rewrite (Finv_r f x H1).
apply (Fmul_I_r f y).
Qed.

Lemma Finv_r_simpl_m : forall (f : Field) (x y : FT f), x <> (FO f) -> (Fmul f (Fmul f x y) (Finv f x)) = y.
Proof.
move=> f x y H1.
rewrite (Fmul_comm f x y).
rewrite (Fmul_assoc f y x (Finv f x)).
rewrite (Finv_r f x H1).
apply (Fmul_I_r f y).
Qed.

Lemma Finv_mult_simpl : forall (f : Field) (x y z : FT f), x <> (FO f) -> (Fmul f (Fmul f x (Finv f y)) (Fmul f z (Finv f x))) = (Fmul f z (Finv f y)).
Proof.
move=> f x y z H1.
rewrite (Fmul_comm f (Fmul f x (Finv f y)) (Fmul f z (Finv f x))).
rewrite (Fmul_assoc f z (Finv f x) (Fmul f x (Finv f y))).
rewrite - (Fmul_assoc f (Finv f x) x (Finv f y)).
rewrite (Finv_l f x H1).
rewrite (Fmul_I_l f (Finv f y)).
reflexivity.
Qed.

Definition NatCorrespondField := fun (f : Field) => (fix NatCorrespond (n : nat) : FT f := match n with
  | O => FO f
  | S n0 => (Fadd f (NatCorrespond n0) (FI f))
end).

Definition CharacteristicField := fun (f : Field) => (match excluded_middle_informative (Inhabited nat (fun (n : nat) => NatCorrespondField f (S n) = FO f)) with
  | left H => S (proj1_sig (min_nat_get (fun (n : nat) => NatCorrespondField f (S n) = FO f) H))
  | right _ => O
end).

End Field.