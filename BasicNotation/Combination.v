Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "Tools" as Tools.
Add LoadPath "BasicProperty" as BasicProperty.

From mathcomp Require Import ssreflect.
Require Import Coq.Arith.Mult.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import MyAlgebraicStructure.MyField.
Require Import Tools.MySum.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Sets.Ensembles.

Fixpoint fact (n : nat) : nat := match n with
  | O => 1
  | S n => S n * fact n
end.

Fixpoint perm (n k : nat) : nat := match k with
  | O => 1
  | S k => (match n with
    | O => O
    | S n => S n * (perm n k)
  end)
end.

Fixpoint conv (n k : nat) : nat := match k with
  | O => 1
  | S k => (match n with
    | O => O
    | S n => (conv n k) + (conv n (S k))
  end)
end.

Lemma fact_neq_0 : forall (n : nat), fact n <> 0.
Proof.
elim.
move=> H1.
elim (lt_irrefl (fact O)).
rewrite {1} H1.
apply (le_n 1).
move=> n H1 H2.
elim (mult_is_O (S n) (fact n) H2).
move=> H3.
suff: (let t := S n in match t with
  | O => True
  | S _ => False
end).
move=> H4.
apply H4.
rewrite H3.
apply I.
apply H1.
Qed.

Lemma permNature1 : forall (n : nat), perm n O = 1.
Proof.
elim.
reflexivity.
move=> n H1.
reflexivity.
Qed.

Lemma permNature2 : forall (n k : nat), perm n (S k) = perm n k * (n - k).
Proof.
elim.
elim.
reflexivity.
move=> n H1.
reflexivity.
move=> n H1.
elim.
simpl.
rewrite (permNature1 n).
rewrite (plus_0_r n).
rewrite (mult_1_r n).
reflexivity.
move=> k H2.
simpl.
rewrite (H1 k).
rewrite (mult_assoc n (perm n k) (n - k)).
rewrite (mult_plus_distr_r (perm n k) (n * perm n k) (n - k)).
reflexivity.
Qed.

Lemma convNature1 : forall (n : nat), conv n O = 1.
Proof.
elim.
reflexivity.
move=> n H1.
reflexivity.
Qed.

Lemma permOutSideDomain : forall (n k : nat), n < k -> (perm n k) = O.
Proof.
elim.
elim.
move=> H1.
elim (lt_irrefl O H1).
move=> n H1 H2.
reflexivity.
move=> n H1.
elim.
move=> H2.
elim (le_not_lt O (S n)).
apply (le_0_n (S n)).
apply H2.
move=> n0 H2 H3.
suff: (perm (S n) (S n0) = S n * perm n n0).
move=> H4.
rewrite H4.
rewrite (H1 n0 (le_S_n (S n) n0 H3)).
apply (mult_0_r (S n)).
reflexivity.
Qed.

Lemma permfactRelation : forall (n k : nat), n >= k -> (perm n k) * (fact (n - k)) = fact n.
Proof.
move=> n.
elim.
move=> H1.
rewrite (permNature1 n).
rewrite - (minus_n_O n).
apply (mult_1_l (fact n)).
move=> k H1 H2.
rewrite (permNature2 n k).
rewrite - (mult_assoc (perm n k) (n - k) (fact (n - S k))).
suff: (n - k = S (n - S k)).
move=> H3.
rewrite H3.
suff: (S (n - S k) * fact (n - S k) = fact (n - k)).
move=> H4.
rewrite H4.
apply (H1 (le_trans k (S k) n (le_S k k (le_n k)) H2)).
rewrite H3.
reflexivity.
apply (plus_reg_l (n - k) (S (n - S k)) k).
rewrite - (plus_Snm_nSm k (n - S k)).
rewrite (le_plus_minus_r (S k) n H2).
apply (le_plus_minus_r k n (le_trans k (S k) n (le_S k k (le_n k)) H2)).
Qed.

Lemma permfactRelationCorollary : forall (n : nat), fact n = perm n n.
Proof.
move=> n.
rewrite - (permfactRelation n n).
rewrite - (minus_n_n n).
apply (mult_1_r (perm n n)).
apply (le_n n).
Qed.

Lemma convOutSideDomain : forall (n k : nat), n < k -> (conv n k) = O.
Proof.
elim.
elim.
move=> H1.
elim (lt_irrefl O H1).
move=> n H1 H2.
reflexivity.
move=> n H1.
elim.
move=> H2.
elim (le_not_lt O (S n)).
apply (le_0_n (S n)).
apply H2.
move=> n0 H2 H3.
simpl.
rewrite (H1 n0 (le_S_n (S n) n0 H3)).
rewrite (H1 (S n0) (le_S (S n) n0 (le_S_n (S n) n0 H3))).
reflexivity.
Qed.

Lemma convfactRelation : forall (n k : nat), n >= k -> (conv n k) * (fact k) * (fact (n - k)) = fact n.
Proof.
elim.
move=> k H1.
elim (le_lt_or_eq k O H1).
move=> H2.
elim (le_not_lt O k (le_0_n k) H2).
move=> H2.
rewrite H2.
reflexivity.
move=> n H1.
elim.
move=> H2.
apply (plus_0_r (fact (S n))).
move=> k H2 H3.
simpl.
rewrite - {1}(mult_1_l (fact k)).
rewrite - (mult_plus_distr_r 1 k (fact k)).
rewrite - (mult_assoc (conv n k + conv n (S k)) ((1 + k) * fact k) (fact (n - k)))%nat.
rewrite (mult_plus_distr_r (conv n k) (conv n (S k)) ((1 + k) * fact k * fact (n - k))).
rewrite (mult_assoc (conv n k) ((1 + k) * fact k) (fact (n - k)))%nat.
rewrite (mult_assoc (conv n k) (1 + k) (fact k))%nat.
rewrite (mult_comm (conv n k) (1 + k)).
rewrite - (mult_assoc (1 + k) (conv n k) (fact k)).
rewrite - (mult_assoc (1 + k) (conv n k * fact k) (fact (n - k))).
rewrite (H1 k (le_S_n k n H3)).
elim (le_lt_or_eq k n (le_S_n k n H3)).
move=> H4.
suff: (n - k = S (n - (1 + k))).
move=> H5.
rewrite H5.
rewrite (mult_comm (S (n - (1 + k))) (fact (n - (1 + k))) : fact (S (n - (1 + k))) = fact (n - (1 + k)) * S (n - (1 + k))).
rewrite (mult_assoc ((1 + k) * fact k) (fact (n - (1 + k))) (S (n - (1 + k)))).
rewrite (mult_assoc (conv n (S k)) ((1 + k) * fact k * fact (n - (1 + k))) (S (n - (1 + k)))).
rewrite (mult_assoc (conv n (S k)) ((1 + k) * fact k) (fact (n - (1 + k)))).
rewrite (H1 (S k) H4 : conv n (S k) * ((1 + k) * fact k) * fact (n - (1 + k)) = fact n).
rewrite (mult_comm (fact n) (S (n - (1 + k)))).
rewrite - (mult_plus_distr_r (1 + k) (S (n - (1 + k))) (fact n)).
rewrite - (plus_n_Sm (1 + k) (n - (1 + k))).
rewrite (le_plus_minus_r (1 + k) n H4).
reflexivity.
apply (plus_reg_l (n - k) (S (n - (1 + k))) k).
rewrite (le_plus_minus_r k n (le_S_n k n H3)).
rewrite - (plus_n_Sm k (n - (1 + k))).
apply (le_plus_minus (1 + k) n H4).
move=> H4.
rewrite H4.
rewrite (convOutSideDomain n (S n) (le_n (S n))).
rewrite (mult_0_l ((1 + n) * fact n * fact (n - n))).
apply (plus_0_r (fact (S n))).
Qed.

Lemma convpermRelation : forall (n k : nat), (conv n k) * (fact k) = perm n k.
Proof.
move=> n k.
elim (le_or_lt k n).
move=> H1.
suff: (forall (m : nat), m <> O -> conv n k * fact k * m = perm n k * m -> conv n k * fact k = perm n k).
move=> H2.
apply (H2 (fact (n - k))).
apply (fact_neq_0 (n - k)).
rewrite (permfactRelation n k H1).
apply (convfactRelation n k H1).
move=> m H2 H3.
elim (le_or_lt (conv n k * fact k) (perm n k)).
move=> H4.
elim (le_lt_or_eq (conv n k * fact k) (perm n k) H4).
move=> H5.
elim (lt_irrefl (conv n k * fact k * m)).
rewrite {2} H3.
apply (mult_lt_compat_r (conv n k * fact k) (perm n k) m H5).
elim (le_lt_or_eq O m (le_0_n m)).
move=> H6.
apply H6.
move=> H6.
elim H2.
rewrite H6.
reflexivity.
move=> H5.
apply H5.
move=> H4.
elim (lt_irrefl (conv n k * fact k * m)).
rewrite {1} H3.
apply (mult_lt_compat_r (perm n k) (conv n k * fact k) m H4).
elim (le_lt_or_eq O m (le_0_n m)).
move=> H5.
apply H5.
move=> H5.
elim H2.
rewrite H5.
reflexivity.
move=> H1.
rewrite (convOutSideDomain n k H1).
rewrite (permOutSideDomain n k H1).
apply (mult_0_l (fact k)).
Qed.

Lemma convNature2 : forall (n k : nat), conv (S n) (S k) * (S k) = (S n) * conv n k.
Proof.
move=> n k.
suff: (forall (m : nat), m <> O -> conv (S n) (S k) * S k * m = S n * conv n k * m -> conv (S n) (S k) * S k = S n * conv n k).
move=> H1.
apply (H1 (fact k) (fact_neq_0 k)).
rewrite - (mult_assoc (S n) (conv n k) (fact k)).
rewrite (convpermRelation n k).
rewrite - (mult_assoc (conv (S n) (S k)) (S k) (fact k)).
apply (convpermRelation (S n) (S k)).
move=> m H1 H2.
elim (le_or_lt (conv (S n) (S k) * S k) (S n * conv n k)).
move=> H3.
elim (le_lt_or_eq (conv (S n) (S k) * S k) (S n * conv n k) H3).
move=> H4.
elim (lt_irrefl (conv (S n) (S k) * S k * m)).
rewrite {2} H2.
apply (mult_lt_compat_r (conv (S n) (S k) * S k) (S n * conv n k) m H4).
elim (le_lt_or_eq O m (le_0_n m)).
move=> H5.
apply H5.
move=> H5.
elim H1.
rewrite H5.
reflexivity.
move=> H4.
apply H4.
move=> H3.
elim (lt_irrefl (conv (S n) (S k) * S k * m)).
rewrite {1} H2.
apply (mult_lt_compat_r (S n * conv n k) (conv (S n) (S k) * S k) m H3).
elim (le_lt_or_eq O m (le_0_n m)).
move=> H4.
apply H4.
move=> H4.
elim H1.
rewrite H4.
reflexivity.
Qed.

Lemma convNature3 : forall (n m : nat), m <= n -> conv n m = conv n (n - m).
Proof.
move=> n m H1.
suff: (forall (k : nat), k <> O -> conv n m * k = conv n (n - m) * k -> conv n m = conv n (n - m)).
move=> H2.
apply (H2 (fact m * fact (n - m))).
move=> H3.
elim (mult_is_O (fact m) (fact (n - m)) H3).
apply (fact_neq_0 m).
apply (fact_neq_0 (n - m)).
rewrite (mult_assoc (conv n m) (fact m) (fact (n - m))).
rewrite (mult_comm (fact m) (fact (n - m))).
rewrite (mult_assoc (conv n (n - m)) (fact (n - m)) (fact m)).
suff: (m = n - (n - m)).
move=> H3.
rewrite {6} H3.
rewrite (convfactRelation n (n - m)).
apply (convfactRelation n m H1).
apply (plus_le_reg_l (n - m) n m).
rewrite (le_plus_minus_r m n H1).
apply (le_plus_r m n).
apply (plus_reg_l m (n - (n - m)) (n - m)).
rewrite (plus_comm (n - m) m).
rewrite (le_plus_minus_r (n - m) n).
apply (le_plus_minus_r m n H1).
apply (plus_le_reg_l (n - m) n m).
rewrite (le_plus_minus_r m n H1).
apply (le_plus_r m n).
move=> k H2 H3.
elim (le_or_lt (conv n m) (conv n (n - m))).
move=> H4.
elim (le_lt_or_eq (conv n m) (conv n (n - m)) H4).
move=> H5.
elim (lt_irrefl (conv n m * k)).
rewrite {2} H3.
apply (mult_lt_compat_r (conv n m) (conv n (n - m)) k H5).
suff: (k <> O).
elim k.
elim.
reflexivity.
move=> l H6 H7.
apply (le_n_S O l (le_0_n l)).
apply H2.
move=> H5.
apply H5.
move=> H4.
elim (lt_irrefl (conv n m * k)).
rewrite {1} H3.
apply (mult_lt_compat_r (conv n (n - m)) (conv n m) k H4).
suff: (k <> O).
elim k.
elim.
reflexivity.
move=> l H5 H6.
apply (le_n_S O l (le_0_n l)).
apply H2.
Qed.

Lemma BinomialTheoremF : forall (f : Field) (n : nat) (x y : FT f), PowF f (Fadd f x y) n = MySumF2 (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n))) (FPCM f) (fun (u : Count (S n)) => Fmul f (INF f (conv n (proj1_sig u))) (Fmul f (PowF f x (proj1_sig u)) (PowF f y (n - proj1_sig u)))).
Proof.
move=> f.
elim.
move=> x y.
rewrite (MySumF2Included (Count 1) (FiniteSingleton (Count 1) (exist (fun (n : nat) => (n < 1)) O (le_n 1)))).
rewrite (MySumF2Singleton (Count 1) (FPCM f) (fun (u : Count 1) => Fmul f (INF f (conv 0 (proj1_sig u))) (Fmul f (PowF f x (proj1_sig u)) (PowF f y (0 - proj1_sig u)))) (exist (fun (n : nat) => (n < 1)) O (le_n 1))).
rewrite MySumF2O.
simpl.
rewrite (Fmul_I_l f (FI f)).
rewrite (Fadd_O_l f (FI f)).
rewrite (Fmul_I_l f (FI f)).
rewrite (Fadd_O_r f (FI f)).
reflexivity.
move=> u.
elim.
move=> u0 H1 H2.
elim H1.
suff: (u0 = exist (fun (n : nat) => (n < 1)) O (le_n 1)).
move=> H3.
rewrite H3.
apply (In_singleton (Count 1)).
apply sig_map.
rewrite (le_antisym (proj1_sig (exist (fun (n : nat) => (n < 1)) O (le_n 1))) 0 (le_S_n (proj1_sig (exist (fun (n : nat) => (n < 1)) O (le_n 1))) 0 (proj2_sig (exist (fun (n : nat) => (n < 1)) O (le_n 1)))) (le_0_n (proj1_sig (exist (fun (n : nat) => (n < 1)) O (le_n 1))))).
apply (le_antisym (proj1_sig u0) 0 (le_S_n (proj1_sig u0) 0 (proj2_sig u0)) (le_0_n (proj1_sig u0))).
move=> u H1.
apply (Full_intro (Count 1) u).
suff: (forall (x y : FT f), Fmul f x y = Fmul f y x -> forall (k : nat), Fmul f y (PowF f x k) = Fmul f (PowF f x k) y).
move=> H1.
move=> n H2 x y.
suff: (Fmul f x y = Fmul f y x).
move=> H3.
suff: (PowF f (Fadd f x y) (S n) = Fmul f (Fadd f x y) (PowF f (Fadd f x y) n)).
move=> H4.
rewrite H4.
rewrite (H2 x y).
suff: (forall (m : Count (S (S n))), proj1_sig m <> O -> pred (proj1_sig m) < S n)%nat.
move=> H5.
rewrite (Fmul_add_distr_r f x y).
suff: (Fmul f x (MySumF2 (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n))) (FPCM f) (fun (u : Count (S n)) => Fmul f (INF f (conv n (proj1_sig u))) (Fmul f (PowF f x (proj1_sig u)) (PowF f y (n - proj1_sig u))))) = MySumF2 (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n))) (FPCM f) (fun (u : Count (S n)) => Fmul f x (Fmul f (INF f (conv n (proj1_sig u))) (Fmul f (PowF f x (proj1_sig u)) (PowF f y (n - proj1_sig u)))))).
move=> H6.
rewrite H6.
suff: (MySumF2 (Count (S (S n))) (exist (Finite (Count (S (S n)))) (Full_set (Count (S (S n)))) (CountFinite (S (S n)))) (FPCM f) (fun (m : (Count (S (S n)))) => match excluded_middle_informative (proj1_sig m = O) with
  | left _ => FO f
  | right H => Fmul f x (Fmul f (INF f (conv n (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H5 m H))))) (Fmul f (PowF f x (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H5 m H)))) (PowF f y (n - proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (pred (proj1_sig m)) (H5 m H))))))
end) = MySumF2 (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n))) (FPCM f) (fun (u : Count (S n)) => Fmul f x (Fmul f (INF f (conv n (proj1_sig u))) (Fmul f (PowF f x (proj1_sig u)) (PowF f y (n - proj1_sig u)))))).
move=> H7.
rewrite - H7.
suff: (Fmul f y (MySumF2 (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n))) (FPCM f) (fun (u : Count (S n)) => Fmul f (INF f (conv n (proj1_sig u))) (Fmul f (PowF f x (proj1_sig u)) (PowF f y (n - proj1_sig u))))) = MySumF2 (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n))) (FPCM f) (fun (u : Count (S n)) => Fmul f y (Fmul f (INF f (conv n (proj1_sig u))) (Fmul f (PowF f x (proj1_sig u)) (PowF f y (n - proj1_sig u)))))).
move=> H8.
rewrite H8.
suff: (MySumF2 (Count (S (S n))) (exist (Finite (Count (S (S n)))) (Full_set (Count (S (S n)))) (CountFinite (S (S n)))) (FPCM f) (fun (m : (Count (S (S n)))) => match excluded_middle_informative (proj1_sig m < S n)%nat with
  | left H => Fmul f y (Fmul f (INF f (conv n (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) )) (Fmul f (PowF f x (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) ) (PowF f y (n - (proj1_sig (exist (fun (k : nat) => (k < S n)%nat) (proj1_sig m) H)) ))))
  | right _ => FO f
end) = MySumF2 (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n))) (FPCM f) (fun (u : Count (S n)) => Fmul f y (Fmul f (INF f (conv n (proj1_sig u))) (Fmul f (PowF f x (proj1_sig u)) (PowF f y (n - proj1_sig u)))))).
move=> H9.
rewrite - H9.
apply eq_sym.
apply (MySumF2Distr (Count (S (S n))) (FPCM f) (exist (Finite (Count (S (S n)))) (Full_set (Count (S (S n)))) (CountFinite (S (S n))))).
move=> u H10.
elim (excluded_middle_informative (proj1_sig u = O)).
move=> H11.
elim (excluded_middle_informative (proj1_sig u < S n)).
move=> H12.
rewrite (Fadd_O_l f : forall (x : FT f), CMc (FPCM f) (FO f) x = x).
simpl proj1_sig.
rewrite H11.
rewrite (convNature1 (S n)).
rewrite (convNature1 n).
simpl.
rewrite (Fadd_O_l f (FI f)).
rewrite - (minus_n_O n).
rewrite (Fmul_I_l f (Fmul f (PowF f y n) y)).
rewrite (Fmul_I_l f (Fmul f (PowF f y n) y)).
rewrite (Fmul_I_l f (PowF f y n)).
rewrite (Fmul_I_l f (PowF f y n)).
apply (Fmul_comm f (PowF f y n) y).
elim.
rewrite H11.
apply (le_n_S O n (le_0_n n)).
move=> H11.
simpl proj1_sig.
elim (excluded_middle_informative (proj1_sig u < S n)).
move=> H12.
suff: (exists (m : nat), proj1_sig u = S m).
elim.
move=> m H13.
rewrite H13.
simpl.
rewrite (plus_INF f (conv n m) (conv n (S m))).
rewrite - (Fmul_assoc f x (INF f (conv n m))).
rewrite (Fmul_comm f x (INF f (conv n m))).
rewrite (Fmul_assoc f (INF f (conv n m)) x).
rewrite - (Fmul_assoc f x (PowF f x m) (PowF f y (n - m))).
rewrite (Fmul_comm f x (PowF f x m)).
rewrite - (Fmul_assoc f y (INF f (conv n (S m)))).
rewrite (Fmul_comm f y (INF f (conv n (S m)))).
rewrite (Fmul_assoc f (INF f (conv n (S m))) y).
rewrite - (Fmul_assoc f y (Fmul f (PowF f x m) x) (PowF f y (n - S m))).
rewrite (H1 x y H3 (S m)).
rewrite (Fmul_assoc f (PowF f x (S m)) y (PowF f y (n - S m))).
rewrite (Fmul_comm f y (PowF f y (n - S m))).
suff: (n - m = S (n - S m)).
move=> H14.
rewrite H14.
apply (Fmul_add_distr_r f).
apply (plus_reg_l (n - m) (S (n - S m)) m).
rewrite - (plus_Snm_nSm m (n - S m)).
suff: (proj1_sig u <= n).
rewrite H13.
move=> H14.
rewrite (le_plus_minus_r (S m) n H14).
apply (le_plus_minus_r m n (le_trans m (S m) n (le_S m m (le_n m)) H14)).
apply (le_S_n (proj1_sig u) n H12).
suff: (proj1_sig u <> 0).
elim (proj1_sig u).
elim.
reflexivity.
move=> m H13 H14.
exists m.
reflexivity.
apply H11.
move=> H12.
suff: (proj1_sig u = S n).
move=> H13.
rewrite H13.
rewrite (CM_O_r (FPCM f)).
rewrite (convNature3 (S n) (S n)).
rewrite - (minus_n_n (S n)).
rewrite (convNature1 (S n)).
rewrite (convNature3 n n).
rewrite - (minus_n_n n).
rewrite (convNature1 n).
simpl.
rewrite (Fadd_O_l f (FI f)).
rewrite (Fmul_I_r f (Fmul f (PowF f x n) x)).
rewrite (Fmul_I_r f (PowF f x n)).
rewrite (Fmul_I_l f (Fmul f (PowF f x n) x)).
rewrite (Fmul_I_l f (PowF f x n)).
apply (Fmul_comm f (PowF f x n) x).
apply (le_n n).
apply (le_n (S n)).
elim (le_lt_or_eq (proj1_sig u) (S n) (le_S_n (proj1_sig u) (S n) (proj2_sig u))).
move=> H13.
elim (H12 H13).
move=> H13.
apply H13.
rewrite (MySumF2NShiftL (S n)).
reflexivity.
apply (FiniteSetInduction (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Fmul_O_r f y).
move=> B b H8 H9 H10 H11.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Fmul_add_distr_l f).
rewrite H11.
reflexivity.
apply H10.
apply H10.
rewrite (MySumF2NShiftR (S n) H5).
reflexivity.
apply (FiniteSetInduction (Count (S n)) (exist (Finite (Count (S n))) (Full_set (Count (S n))) (CountFinite (S n)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
apply (Fmul_O_r f x).
move=> B b H6 H7 H8 H9.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (Fmul_add_distr_l f).
rewrite H9.
reflexivity.
apply H8.
apply H8.
move=> m H5.
suff: (exists (k : nat), proj1_sig m = S k).
elim.
move=> k H6.
rewrite H6.
unfold lt.
simpl.
rewrite - H6.
apply (le_S_n (proj1_sig m) (S n) (proj2_sig m)).
suff: (proj1_sig m <> 0).
elim (proj1_sig m).
elim.
reflexivity.
move=> k H6 H7.
exists k.
reflexivity.
apply H5.
apply (Fmul_comm f (PowF f (Fadd f x y) n) (Fadd f x y)).
apply (Fmul_comm f x y).
move=> x y H1.
elim.
rewrite (Fmul_I_l f y : Fmul f (PowF f x 0) y = y).
apply (Fmul_I_r f y).
move=> n H2.
simpl.
rewrite - (Fmul_assoc f y (PowF f x n) x).
rewrite H2.
rewrite (Fmul_assoc f (PowF f x n) y x).
rewrite (Fmul_assoc f (PowF f x n) x y).
rewrite H1.
reflexivity.
Qed.
