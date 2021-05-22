Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Image.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.ProofIrrelevanceFacts.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma sig_map : forall {T : Type} (P : T -> Prop) (x : {x : T | P x}) (y : {x : T | P x}), proj1_sig x = proj1_sig y -> x = y.
Proof.
intros A P x y.
case x.
intros xv xp.
case y.
intros yv yp .
simpl.
intro H1.
subst xv.
rewrite (proof_irrelevance (P yv) yp xp).
reflexivity.
Qed.

Section MySum.

Record CommutativeMonoid : Type := mkCommutativeMonoid
{
CMT : Type;
CMe : CMT;
CMc : CMT -> CMT -> CMT;
CM_comm : forall (x y : CMT), (CMc x y) = (CMc y x);
CM_O_r : forall (x : CMT), (CMc x CMe) = x;
CM_assoc : forall (x y z : CMT), (CMc (CMc x y) z) = (CMc x (CMc y z))
}.

Definition Count (N : nat) := {n : nat | n < N}.

Definition UnwrapF (CM : CommutativeMonoid) (N : nat) (F : (Count N) -> (CMT CM)) := fun (n : nat) => match (excluded_middle_informative (n < N)) with
  | left a => (F (exist (fun (n0 : nat) => (n0 < N)%nat) n a))
  | right _ => CMe CM
end.

Definition SumFSub (CM : CommutativeMonoid) (N : nat) := fix SumFSub (F : (Count N) -> (CMT CM)) (n : nat) {struct n} : (CMT CM) := match n with
  | O => CMe CM
  | S n0 => CMc CM (SumFSub F n0) (UnwrapF CM N F n0)
end.

Definition SumF (CM : CommutativeMonoid) (N : nat) := fun (F : (Count N) -> (CMT CM)) => SumFSub CM N F N.

Definition Injective (A B : Type) (f : A -> B) := forall x y, f x = f y -> x = y.

Definition Surjective (A B : Type) (f : A -> B) := forall y, exists x, f x = y.

Definition Bijective (A B : Type) (f : A -> B) := exists (g : B -> A), (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

Lemma SumWellDefinedSub : forall (CM : CommutativeMonoid) (N : nat) (F1 F2 : (Count N) -> (CMT CM)), (Bijective (Count N) (CMT CM) F1) -> (Bijective (Count N) (CMT CM) F2) -> ((SumF CM N F1) = (SumF CM N F2)).
Proof.
intros CM N.
cut (forall (m : nat) (F1 F2 : Count N -> CMT CM), Bijective (Count N) (CMT CM) F1 -> Bijective (Count N) (CMT CM) F2 -> (forall (m0 : Count N), (proj1_sig m0 >= m) -> (F1 m0) = (F2 m0)) -> SumF CM N F1 = SumF CM N F2).
intros H3 F1 F2 H1 H2.
apply (H3 N F1 F2 H1 H2).
intros m H4.
apply False_ind.
apply (le_not_lt N (proj1_sig m) H4 (proj2_sig m)).
cut (forall (F : Count N -> CMT CM), (forall (m1 m2 : Count N) , (proj1_sig m1 < proj1_sig m2) -> let Fsub := fun (n : Count N) => match (excluded_middle_informative (n = m1)) with
  | left _ => F m2
  | right _ => match (excluded_middle_informative (n = m2)) with
    | left _ => F m1
    | right _ => F n
  end
end in SumF CM N F = SumF CM N Fsub)).
intro H3.
intro m.
elim m.
intros F1 F2 H1 H2 H4.
cut (F1 = F2).
intro H5.
rewrite H5.
reflexivity.
apply functional_extensionality.
intro x.
apply (H4 x).
apply (le_0_n (proj1_sig x)).
intros n H4 F1.
elim (classic (n < N)).
intros H5 F2 H1 H2 H6.
elim H2.
intros G2 H7.
elim (classic (G2 (F1 (exist (fun (x : nat) => x < N) n H5)) = (exist (fun (x : nat) => x < N) n H5))).
intro H8.
apply H4.
apply H1.
apply H2.
intros m0 H9.
elim (le_lt_or_eq n (proj1_sig m0) H9).
apply (H6 m0).
intro H10.
cut (m0 = (exist (fun x : nat => x < N) n H5)).
intro H11.
rewrite H11.
rewrite<- H8 at 2.
rewrite (proj2 H7 (F1 (exist (fun x : nat => x < N) n H5))).
reflexivity.
apply sig_map.
simpl.
rewrite H10.
reflexivity.
cut (let a := (G2 (F1 (exist (fun x : nat => x < N) n H5))) in let b := (exist (fun x : nat => x < N) n H5) in G2 (F1 (exist (fun x : nat => x < N) n H5)) <> exist (fun x : nat => x < N) n H5 -> SumF CM N F1 = SumF CM N F2).
intro H8.
apply H8.
intros a b H8.
cut (let F2sub := fun (n : Count N) => match (excluded_middle_informative (n = a)) with
  | left _ => F2 b
  | right _ => match (excluded_middle_informative (n = b)) with
    | left _ => F2 a
    | right _ => F2 n
  end
end in SumF CM N F1 = SumF CM N F2).
intro H9.
apply H9.
intro F2sub.
cut (proj1_sig a < proj1_sig b).
intro H9.
cut (SumF CM N F1 = SumF CM N F2sub).
intro H10.
cut (SumF CM N F2 = SumF CM N F2sub).
intro H11.
rewrite H11.
apply H10.
apply (H3 F2 a b H9).
apply (H4 F1 F2sub).
apply H1.
exists (fun (x : CMT CM) => if excluded_middle_informative (G2 x = a) then b else if excluded_middle_informative (G2 x = b) then a else G2 x).
apply conj.
intro x.
elim (excluded_middle_informative (G2 (F2sub x) = a)).
unfold F2sub.
elim (excluded_middle_informative (x = a)).
intros H10 H11.
rewrite H10.
rewrite<- (proj1 H7 b).
apply H11.
intro H10.
elim (excluded_middle_informative (x = b)).
intro H11.
intro H12.
rewrite H11.
reflexivity.
intros H11 H12.
apply False_ind.
apply H10.
rewrite<- (proj1 H7 x).
apply H12.
intro H10.
elim (excluded_middle_informative (G2 (F2sub x) = b)).
unfold F2sub.
elim (excluded_middle_informative (x = a)).
intros H11 H12.
rewrite H11.
reflexivity.
intro H11.
elim (excluded_middle_informative (x = b)).
intros H12 H13.
apply False_ind.
apply (lt_irrefl (proj1_sig a)).
rewrite<- (proj1 H7 a) at 2.
rewrite H13.
apply H9.
intros H12 H13.
apply False_ind.
apply H12.
rewrite<- (proj1 H7 x).
apply H13.
intro H11.
unfold F2sub.
elim (excluded_middle_informative (x = a)).
intro H12.
apply False_ind.
apply H11.
unfold F2sub.
elim (excluded_middle_informative (x = a)).
intro H13.
apply (proj1 H7 b).
intro H13.
apply False_ind.
apply (H13 H12).
intro H12.
elim (excluded_middle_informative (x = b)).
intro H13.
apply False_ind.
apply H10.
unfold F2sub.
elim (excluded_middle_informative (x = a)).
intro H14.
apply False_ind.
apply (H12 H14).
intro H14.
elim (excluded_middle_informative (x = b)).
intro H15.
apply (proj1 H7 a).
intro H15.
apply False_ind.
apply (H15 H13).
intro H13.
apply (proj1 H7 x).
intro y.
elim (excluded_middle_informative (G2 y = a)).
intro H10.
unfold F2sub.
elim (excluded_middle_informative (@eq (Count N) b a)).
intro H11.
apply False_ind.
apply (lt_irrefl (proj1_sig a)).
rewrite<- H11 at 2.
apply H9.
intro H11.
elim (excluded_middle_informative (@eq (Count N) b b)).
intro H12.
rewrite<- H10.
apply (proj2 H7 y).
intro H12.
apply False_ind.
apply H12.
reflexivity.
intro H10.
elim (excluded_middle_informative (G2 y = b)).
intro H11.
unfold F2sub.
elim (excluded_middle_informative (a = a)).
intro H12.
rewrite<- H11.
apply (proj2 H7 y).
intro H12.
apply False_ind.
apply H12.
reflexivity.
intro H11.
unfold F2sub.
elim (excluded_middle_informative (G2 y = a)).
intro H12.
apply False_ind.
apply (H10 H12).
intro H12.
elim (excluded_middle_informative (G2 y = b)).
intro H13.
apply False_ind.
apply (H11 H13).
intro H13.
apply (proj2 H7 y).
intro m0.
intro H10.
elim (le_lt_or_eq n (proj1_sig m0) H10).
intro H11.
rewrite (H6 m0 H11).
unfold F2sub.
elim (excluded_middle_informative (m0 = a)).
intro H12.
apply False_ind.
apply (lt_irrefl (proj1_sig a)).
apply (PeanoNat.Nat.le_trans (S (proj1_sig a)) n (proj1_sig a)).
apply H9.
rewrite<- H12.
apply H10.
intro H12.
elim (excluded_middle_informative (m0 = b)).
intro H13.
apply False_ind.
apply (lt_irrefl (proj1_sig b)).
rewrite<- H13 at 2.
apply H11.
intro H13.
reflexivity.
intro H11.
unfold F2sub.
elim (excluded_middle_informative (m0 = a)).
intro H12.
apply False_ind.
apply (lt_irrefl (proj1_sig b)).
unfold proj1_sig at 1.
unfold b at 1.
rewrite H11.
rewrite H12.
apply H9.
intro H12.
elim (excluded_middle_informative (m0 = b)).
intro H13.
rewrite H13.
unfold a.
rewrite (proj2 H7 (F1 (exist (fun x : nat => x < N) n H5))).
reflexivity.
intro H13.
apply False_ind.
apply H13.
apply sig_map.
simpl.
rewrite H11.
reflexivity.
elim (nat_total_order (proj1_sig a) (proj1_sig b)).
intro H9.
apply H9.
intro H9.
apply False_ind.
apply H8.
elim H1.
intros G1 H10.
rewrite<- (proj1 H10 (G2 (F1 (exist (fun x : nat => x < N) n H5)))).
rewrite (H6 (G2 (F1 (exist (fun x : nat => x < N) n H5)))).
rewrite (proj2 H7 (F1 (exist (fun x : nat => x < N) n H5))).
apply (proj1 H10 (exist (fun x : nat => x < N) n H5)).
apply H9.
intro H9.
apply H8.
apply sig_map.
apply H9.
intros H5 F2 H6 H7 H8.
apply (H4 F1 F2 H6 H7).
intros m0 H9.
apply False_ind.
apply H5.
apply (PeanoNat.Nat.le_lt_trans n (proj1_sig m0) N).
apply H9.
apply (proj2_sig m0).
cut (forall (diff : nat) (F : Count N -> CMT CM) (m1 m2 : Count N), proj1_sig m2 = proj1_sig m1 + diff -> let Fsub := fun n : Count N => if excluded_middle_informative (n = m1) then F m2 else if excluded_middle_informative (n = m2) then F m1 else F n in SumF CM N F = SumF CM N Fsub).
intro H1.
intros F m1 m2 H3.
apply (H1 (proj1_sig m2 - proj1_sig m1) F m1 m2).
rewrite (Minus.le_plus_minus_r (proj1_sig m1) (proj1_sig m2)).
reflexivity.
apply (PeanoNat.Nat.le_trans (proj1_sig m1) (S (proj1_sig m1)) (proj1_sig m2)).
apply (le_S (proj1_sig m1) (proj1_sig m1)).
apply (le_n (proj1_sig m1)).
apply H3.
cut (forall (F : Count N -> CMT CM), (forall (m : nat) (H1 : m < N) (H2 : S m < N), let Fsub := fun (n : Count N) => match (excluded_middle_informative (proj1_sig n = m)) with
  | left _ => F (exist (fun (n0 : nat) => n0 < N) (S m) H2)
  | right _ => match (excluded_middle_informative (proj1_sig n = S m)) with
    | left _ => F (exist (fun (n0 : nat) => n0 < N) m H1)
    | right _ => F n
  end
end in SumF CM N F = SumF CM N Fsub)).
intros H1 diff.
elim diff.
intros F m1 m2 H3 Fsub.
cut (F = Fsub).
intro H4.
rewrite H4.
reflexivity.
cut (m1 = m2).
intro H4.
apply functional_extensionality.
intro x.
unfold Fsub.
elim (excluded_middle_informative (x = m1)).
intro H5.
rewrite H5.
rewrite H4.
reflexivity.
intro H5.
elim (excluded_middle_informative (x = m2)).
intro H6.
rewrite H6.
rewrite H4.
reflexivity.
intro H6.
reflexivity.
apply sig_map.
rewrite H3.
rewrite (Plus.plus_0_r (proj1_sig m1)).
reflexivity.
intros dif H2 F m1 m3 H4 Fsub.
cut (proj1_sig m1 + dif < N).
intro H5.
cut (let m2 := (exist (fun (n : nat) => n < N) (proj1_sig m1 + dif) H5) in SumF CM N F = SumF CM N Fsub).
intro H6.
apply H6.
intro m2.
cut (let Fsub1 := fun n : Count N => if excluded_middle_informative (n = m1) then F m2 else if excluded_middle_informative (n = m2) then F m1 else F n in SumF CM N F = SumF CM N Fsub).
intro H6.
apply H6.
intro Fsub1.
cut (let Fsub2 := fun n : Count N => if excluded_middle_informative (n = m1) then Fsub m2 else if excluded_middle_informative (n = m2) then Fsub m1 else Fsub n in SumF CM N F = SumF CM N Fsub).
intro H6.
apply H6.
intro Fsub2.
cut (SumF CM N Fsub1 = SumF CM N Fsub2).
intro H6.
cut (SumF CM N F = SumF CM N Fsub1).
intro H7.
cut (SumF CM N Fsub = SumF CM N Fsub2).
intro H8.
rewrite H7.
rewrite H8.
apply H6.
apply (H2 Fsub m1 m2).
reflexivity.
apply (H2 F m1 m2).
reflexivity.
cut (S (proj1_sig m1 + dif) < N).
intro H6.
cut (let Fsub3 := fun n : Count N => if excluded_middle_informative (proj1_sig n = proj1_sig m1 + dif) then Fsub1 (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6) else if excluded_middle_informative (proj1_sig n = S (proj1_sig m1 + dif)) then Fsub1 (exist (fun n1 : nat => n1 < N) (proj1_sig m1 + dif) H5) else Fsub1 n in SumF CM N Fsub1 = SumF CM N Fsub2).
intro H7.
apply H7.
intro Fsub3.
cut (Fsub2 = Fsub3).
intro H7.
rewrite H7.
unfold Fsub3.
apply (H1 Fsub1 (proj1_sig m1 + dif) H5 H6).
apply functional_extensionality.
intro x.
unfold Fsub2.
unfold Fsub3.
elim (excluded_middle_informative (x = m1)).
intro H7.
unfold Fsub.
elim (excluded_middle_informative (@eq (Count N) m2 m1)).
intro H8.
elim (excluded_middle_informative (proj1_sig x = proj1_sig m1 + dif)).
intro H9.
unfold Fsub1.
elim (excluded_middle_informative (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6 = m1)).
intro H10.
apply False_ind.
apply (lt_irrefl (proj1_sig m1)).
rewrite<- H10 at 2.
simpl.
apply (PeanoNat.Nat.le_lt_trans (proj1_sig m1) (proj1_sig m1 + dif) (S (proj1_sig m1 + dif))).
apply (Plus.le_plus_l (proj1_sig m1) dif).
apply (le_n (S (proj1_sig m1 + dif))).
intro H10.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n0 : nat => lt n0 N) (S (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif)) H6) m1)).
intro H11.
apply False_ind.
apply (H10 H11).
intro H11.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n0 : nat => lt n0 N) (S (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif)) H6) m2)).
intro H12.
apply False_ind.
apply H11.
rewrite H12.
apply H8.
intro H12.
cut (m3 = (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6)).
intro H13.
rewrite H13.
reflexivity.
apply sig_map.
simpl.
rewrite H4.
auto.
intro H9.
apply False_ind.
apply H9.
rewrite H7.
rewrite<- H8 at 1.
reflexivity.
intro H8.
elim (excluded_middle_informative (@eq (Count N) m2 m3)).
intro H9.
apply False_ind.
apply (lt_irrefl (proj1_sig m2)).
rewrite H9 at 2.
simpl.
rewrite H4.
apply (Plus.plus_lt_compat_l dif (S dif) (proj1_sig m1)).
apply (le_n (S dif)).
intro H9.
elim (excluded_middle_informative (proj1_sig x = proj1_sig m1 + dif)).
intro H10.
apply False_ind.
apply H8.
apply sig_map.
simpl.
rewrite<- H10.
rewrite H7.
reflexivity.
intro H10.
elim (excluded_middle_informative (proj1_sig x = S (proj1_sig m1 + dif))).
intro H11.
apply False_ind.
apply (lt_irrefl (proj1_sig m1)).
rewrite<- H7 at 2.
rewrite H11.
apply (PeanoNat.Nat.le_lt_trans (proj1_sig m1) (proj1_sig m1 + dif) (S (proj1_sig m1 + dif))).
apply (Plus.le_plus_l (proj1_sig m1) dif).
apply (le_n (S (proj1_sig m1 + dif))).
intro H11.
unfold Fsub1.
elim (excluded_middle_informative (x = m1)).
intro H12.
reflexivity.
intro H12.
apply False_ind.
apply (H12 H7).
intro H7.
elim (excluded_middle_informative (x = m2)).
intro H8.
elim (excluded_middle_informative (proj1_sig x = proj1_sig m1 + dif)).
intro H9.
unfold Fsub.
elim (excluded_middle_informative (m1 = m1)).
intro H10.
unfold Fsub1.
elim (excluded_middle_informative (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6 = m1)).
intro H11.
apply False_ind.
apply (lt_irrefl (proj1_sig m1)).
rewrite<- H11 at 2.
simpl.
apply (PeanoNat.Nat.le_lt_trans (proj1_sig m1) (proj1_sig m1 + dif) (S (proj1_sig m1 + dif))).
apply (Plus.le_plus_l (proj1_sig m1) dif).
apply (le_n (S (proj1_sig m1 + dif))).
intro H11.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n0 : nat => lt n0 N) (S (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif)) H6) m1)).
intro H12.
apply False_ind.
apply (H11 H12).
intro H12.
elim (excluded_middle_informative (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6 = m2)).
intro H13.
apply False_ind.
apply (lt_irrefl (proj1_sig m2)).
rewrite<- H13 at 2.
unfold m2.
simpl.
apply (le_n (S (proj1_sig m1 + dif))).
intro H13.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n0 : nat => lt n0 N) (S (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif)) H6) m2)).
intro H14.
apply False_ind.
apply (H13 H14).
intro H14.
cut (m3 = (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6)).
intro H15.
rewrite H15.
reflexivity.
apply sig_map.
simpl.
rewrite H4.
auto.
intro H10.
apply False_ind.
apply H10.
reflexivity.
intro H9.
apply False_ind.
apply H9.
rewrite H8.
reflexivity.
intro H8.
elim (excluded_middle_informative (proj1_sig x = proj1_sig m1 + dif)).
intro H9.
apply False_ind.
apply H8.
apply sig_map.
rewrite H9.
reflexivity.
intro H9.
elim (excluded_middle_informative (proj1_sig x = S (proj1_sig m1 + dif))).
intro H10.
unfold Fsub.
elim (excluded_middle_informative (x = m1)).
intro H11.
apply False_ind.
apply (H7 H11).
intro H11.
elim (excluded_middle_informative (x = m3)).
intro H12.
unfold Fsub1.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n1 : nat => lt n1 N) (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif) H5) m1)).
intro H13.
rewrite<- H13.
cut (exist (fun n1 : nat => n1 < N) (proj1_sig m1 + dif) H5 = m2).
intro H14.
rewrite H14.
reflexivity.
apply sig_map.
reflexivity.
intro H13.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n1 : nat => lt n1 N) (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif) H5) m2)).
intro H14.
reflexivity.
intro H14.
apply False_ind.
apply H14.
apply sig_map.
reflexivity.
intro H12.
apply False_ind.
apply H12.
apply sig_map.
rewrite H4.
rewrite H10.
auto.
intro H10.
unfold Fsub.
elim (excluded_middle_informative (x = m1)).
intro H11.
apply False_ind.
apply (H7 H11).
intro H11.
elim (excluded_middle_informative (x = m3)).
intro H12.
apply False_ind.
apply H10.
rewrite H12.
rewrite H4.
auto.
intro H12.
unfold Fsub1.
elim (excluded_middle_informative (x = m1)).
intro H13.
apply False_ind.
apply (H11 H13).
intro H13.
elim (excluded_middle_informative (x = m2)).
intro H14.
apply False_ind.
apply (H8 H14).
intro H14.
reflexivity.
cut (S (proj1_sig m1 + dif) = proj1_sig m1 + S dif).
intro H6.
rewrite H6.
rewrite<- H4.
apply (proj2_sig m3).
auto.
apply (PeanoNat.Nat.lt_trans (proj1_sig m1 + dif) (proj1_sig m1 + S dif) N).
apply (Plus.plus_lt_compat_l dif (S dif) (proj1_sig m1)).
apply (le_n (S dif)).
rewrite<- H4.
apply (proj2_sig m3).
intros F m H1 H2 Fsub.
unfold SumF.
cut (forall (n : nat), (n = S m -> SumFSub CM N F (S n) = SumFSub CM N Fsub (S n)) /\ (n <> S m -> SumFSub CM N F n = SumFSub CM N Fsub n)).
intro H3.
apply (proj2 (H3 N)).
intro H4.
apply (lt_irrefl N).
rewrite H4 at 1.
apply H2.
intro n.
elim n.
apply conj.
intro H3.
apply False_ind.
apply (PeanoNat.Nat.neq_succ_0 m).
rewrite H3.
reflexivity.
intro H3.
simpl.
reflexivity.
intros n0 H3.
apply conj.
intro H4.
simpl.
rewrite (CM_assoc CM (SumFSub CM N F n0) (UnwrapF CM N F n0) (UnwrapF CM N F (S n0))).
rewrite (CM_assoc CM (SumFSub CM N Fsub n0) (UnwrapF CM N Fsub n0) (UnwrapF CM N Fsub (S n0))).
cut ((CMc CM (UnwrapF CM N F n0) (UnwrapF CM N F (S n0))) = (CMc CM (UnwrapF CM N Fsub n0) (UnwrapF CM N Fsub (S n0)))).
intro H5.
rewrite H5.
cut ((SumFSub CM N F n0) = (SumFSub CM N Fsub n0)).
intro H6.
rewrite H6.
reflexivity.
apply (proj2 H3).
rewrite<- H4.
apply (n_Sn n0).
unfold UnwrapF.
elim (excluded_middle_informative (n0 < N)).
intro a.
elim (excluded_middle_informative ((S n0) < N)).
intro b.
unfold Fsub.
elim (excluded_middle_informative (proj1_sig (exist (fun n1 : nat => n1 < N) n0 a) = m)).
simpl.
intro H5.
elim (excluded_middle_informative (proj1_sig (exist (fun n1 : nat => n1 < N) (S n0) b) = m)).
simpl.
intro H6.
apply False_ind.
apply (n_Sn n0).
rewrite H5 at 1.
rewrite H6.
reflexivity.
intro H6.
elim (excluded_middle_informative (S n0 = m)).
intro H7.
apply False_ind.
apply (n_Sn n0).
rewrite H7.
rewrite H5.
reflexivity.
intro H7.
elim (excluded_middle_informative (S n0 = S m)).
intro H8.
rewrite (CM_comm CM (F (exist (fun n1 : nat => n1 < N) (S m) H2)) (F (exist (fun n1 : nat => n1 < N) m H1))).
cut ((exist (fun n1 : nat => n1 < N) n0 a) = (exist (fun n1 : nat => n1 < N) m H1)).
intro H9.
rewrite H9.
cut ((exist (fun n1 : nat => n1 < N) (S n0) b) = (exist (fun n1 : nat => n1 < N) (S m) H2)).
intro H10.
rewrite H10.
reflexivity.
apply sig_map.
simpl.
apply H8.
apply sig_map.
simpl.
apply H5.
intro H8.
apply False_ind.
apply (H8 H4).
intro H5.
apply False_ind.
apply H5.
simpl.
apply (PeanoNat.Nat.succ_inj n0 m).
apply H4.
intro H5.
apply False_ind.
apply H5.
rewrite H4.
apply H2.
intro H5.
apply False_ind.
apply H5.
cut (n0 = m).
intro H6.
rewrite H6.
apply H1.
apply (PeanoNat.Nat.succ_inj n0 m).
apply H4.
intro H4.
elim (classic (n0 = S m)).
apply (proj1 H3).
intro H5.
simpl.
rewrite<- (proj2 H3 H5).
unfold UnwrapF.
elim (excluded_middle_informative (n0 < N)).
intro a.
unfold Fsub.
elim (excluded_middle_informative (proj1_sig (exist (fun n1 : nat => n1 < N) n0 a) = m)).
simpl.
intro H6.
apply False_ind.
apply H4.
rewrite H6.
reflexivity.
intro H6.
elim (excluded_middle_informative (proj1_sig (exist (fun n1 : nat => n1 < N) n0 a) = S m)).
simpl.
intro H7.
apply False_ind.
apply (H5 H7).
intro H7.
reflexivity.
intro H6.
reflexivity.
Qed.

Lemma NumWellDefined : forall (U : Type) (A : Ensemble U), (Finite U A) -> {n : nat | cardinal U A n}.
Proof.
intros U A H1.
apply constructive_definite_description.
apply (proj1 (unique_existence (fun (n : nat) => cardinal U A n))).
apply conj.
apply (finite_cardinal U A H1).
intros n1 n2 H2 H3.
apply (cardinal_is_functional U A n1 H2 A n2 H3).
reflexivity.
Qed.

Definition Counter (U : Type) := fun (A : {X : Ensemble U | Finite U X}) => (proj1_sig (NumWellDefined U (proj1_sig A) (proj2_sig A))).

Lemma CounterNature : forall (U : Type) (A : {X : Ensemble U | Finite U X}), cardinal U (proj1_sig A) (Counter U A).
Proof.
intros U A.
apply (proj2_sig (NumWellDefined U (proj1_sig A) (proj2_sig A))).
Qed.

Lemma CountExistBijectiveFunction : forall (U : Type) (n : nat) (A : Ensemble U), (cardinal U A n) -> exists (F : (Count n) -> {x : U | A x}), Bijective (Count n) {x : U | A x} F.
Proof.
intros U n.
elim n.
intros A H1.
cut ((fun (n : nat) => n < 0) = Empty_set nat).
intro H2.
cut (Count 0 = {n : nat | Empty_set nat n}).
intro H3.
rewrite H3.
exists (fun (x : {n0 : nat | Empty_set nat n0}) => match (proj2_sig x) with
end).
cut (A = Empty_set U).
intro H4.
rewrite H4.
exists (fun (x : {u : U | Empty_set U u}) => match (proj2_sig x) with
end).
apply conj.
intro x.
elim (proj2_sig x).
intro y.
elim (proj2_sig y).
apply (cardinal_elim U A 0 H1).
unfold Count.
rewrite H2.
reflexivity.
apply Extensionality_Ensembles.
apply conj.
intros x H3.
apply False_ind.
apply (PeanoNat.Nat.nle_succ_0 x).
apply H3.
intros x H3.
elim H3.
intros n0 H1 A H2.
elim (cardinal_invert U A (S n0)).
intros A0 H3.
elim H3.
intros a H4.
elim (H1 A0 (proj2 (proj2 H4))).
intros F H5.
cut (forall (x : U), (A0 x) -> (A x)).
intro H6.
cut (A a).
intro H7.
exists (fun (x : Count (S n0)) => match (excluded_middle_informative (proj1_sig x < n0)) with
  | left H8 => (exist A (proj1_sig (F (exist (fun (m : nat) => m < n0) (proj1_sig x) H8))) (H6 (proj1_sig (F (exist (fun (m : nat) => m < n0) (proj1_sig x) H8))) (proj2_sig (F (exist (fun (m : nat) => m < n0) (proj1_sig x) H8)))))
  | right _ => (exist A a H7)
end).
cut (forall (x : U), (A x) -> {A0 x} + {a = x}).
intro H8.
elim H5.
intros G H9.
cut (forall (m : nat), m < n0 -> m < S n0).
intro H10.
exists (fun (y : {x : U | A x}) => match (H8 (proj1_sig y) (proj2_sig y)) with
  | left H11 => exist (fun (m : nat) => m < (S n0)) (proj1_sig (G (exist A0 (proj1_sig y) H11))) (H10 (proj1_sig (G (exist A0 (proj1_sig y) H11))) (proj2_sig (G (exist A0 (proj1_sig y) H11))))
  | right _ => exist (fun (m : nat) => m < (S n0)) n0 (le_n (S n0))
end).
apply conj.
intro m.
elim (excluded_middle_informative (proj1_sig m < n0)).
intro H11.
simpl.
elim (H8 (proj1_sig (F (exist (fun m0 : nat => m0 < n0) (proj1_sig m) H11))) (H6 (proj1_sig (F (exist (fun m0 : nat => m0 < n0) (proj1_sig m) H11))) (proj2_sig (F (exist (fun m0 : nat => m0 < n0) (proj1_sig m) H11))))).
intro H12.
apply sig_map.
simpl.
cut ((exist A0 (proj1_sig (F (exist (fun m0 : nat => m0 < n0) (proj1_sig m) H11))) H12) = (F (exist (fun m0 : nat => m0 < n0) (proj1_sig m) H11))).
intro H13.
rewrite H13.
rewrite (proj1 H9 (exist (fun m0 : nat => m0 < n0) (proj1_sig m) H11)).
reflexivity.
apply sig_map.
reflexivity.
intro H12.
apply False_ind.
apply (proj1 (proj2 H4)).
rewrite H12.
apply (proj2_sig (F (exist (fun m0 : nat => m0 < n0) (proj1_sig m) H11))).
intro H11.
elim (H8 (@proj1_sig U (fun x : U => A x) (@exist U A a H7)) (@proj2_sig U (fun x : U => A x) (@exist U A a H7))).
intro H12.
apply sig_map.
simpl.
apply False_ind.
apply (proj1 (proj2 H4)).
apply H12.
intro H12.
elim (le_lt_or_eq (S (proj1_sig m)) (S n0) (proj2_sig m)).
intro H13.
apply False_ind.
apply H11.
apply (lt_S_n (proj1_sig m) n0 H13).
intro H13.
apply sig_map.
simpl.
apply (PeanoNat.Nat.succ_inj n0 (proj1_sig m)).
rewrite H13.
reflexivity.
intro y.
elim (H8 (@proj1_sig U (fun x : U => A x) y) (@proj2_sig U (fun x : U => A x) y)).
intro H11.
elim (excluded_middle_informative (proj1_sig (exist (fun m : nat => m < S n0) (proj1_sig (G (exist A0 (proj1_sig y) H11))) (H10 (proj1_sig (G (exist A0 (proj1_sig y) H11))) (proj2_sig (G (exist A0 (proj1_sig y) H11))))) < n0)).
simpl.
intro H12.
apply sig_map.
simpl.
cut ((exist (fun m : nat => m < n0) (proj1_sig (G (exist A0 (proj1_sig y) H11))) H12) = (G (exist A0 (proj1_sig y) H11))).
intro H13.
rewrite H13.
rewrite (proj2 H9 (exist A0 (proj1_sig y) H11)).
reflexivity.
apply sig_map.
reflexivity.
simpl.
intro H12.
apply False_ind.
apply H12.
apply (proj2_sig (G (exist A0 (proj1_sig y) H11))).
intro H11.
simpl.
elim (excluded_middle_informative (n0 < n0)).
intro H12.
apply False_ind.
apply (lt_irrefl n0 H12).
intro H12.
apply sig_map.
apply H11.
intro m.
apply (le_S (S m) n0).
cut (Add U A0 a = fun (u : U) => match (excluded_middle_informative (A0 u)) with
  |left _ => True
  |right _ => a = u
end).
intro H8.
rewrite (proj1 H4).
rewrite H8.
intro u.
elim (excluded_middle_informative (A0 u)).
intros H9 H10.
left.
apply H9.
intros H9 H10.
right.
apply H10.
apply Extensionality_Ensembles.
apply conj.
intros u H8.
elim H8.
intros x H9.
unfold In.
elim (excluded_middle_informative (A0 x)).
intro H10.
apply I.
intro H10.
apply False_ind.
apply (H10 H9).
intros x H9.
unfold In.
elim (excluded_middle_informative (A0 x)).
intro H10.
apply I.
intro H10.
rewrite H9.
reflexivity.
intro u.
unfold In.
elim (excluded_middle_informative (A0 u)).
intros H8 H9.
left.
apply H8.
intros H8 H9.
right.
rewrite H9.
reflexivity.
rewrite (proj1 H4).
right.
reflexivity.
intros u H6.
rewrite (proj1 H4).
left.
apply H6.
apply H2.
Qed.

Lemma SumWellDefinedSub2 : forall (CM : CommutativeMonoid) (A : Ensemble (CMT CM)) (N : nat) (F1 F2 : (Count N) -> {x : CMT CM | A x}), (Bijective (Count N) {x : CMT CM | A x} F1) -> (Bijective (Count N) {x : CMT CM | A x} F2) -> ((SumF CM N (fun (x : Count N) => proj1_sig (F1 x))) = (SumF CM N (fun (x : Count N) => proj1_sig (F2 x)))).
Proof.
intros CM A N.
cut (forall (m : nat) (F1 F2 : Count N -> {x : CMT CM | A x}), Bijective (Count N) {x : CMT CM | A x} F1 -> Bijective (Count N) {x : CMT CM | A x} F2 -> (forall (m0 : Count N), (proj1_sig m0 >= m) -> (F1 m0) = (F2 m0)) -> SumF CM N (fun (x : Count N) => proj1_sig (F1 x)) = SumF CM N (fun (x : Count N) => proj1_sig (F2 x))).
intros H3 F1 F2 H1 H2.
apply (H3 N F1 F2 H1 H2).
intros m H4.
apply False_ind.
apply (le_not_lt N (proj1_sig m) H4 (proj2_sig m)).
cut (forall (F : Count N -> {x : CMT CM | A x}), (forall (m1 m2 : Count N) , (proj1_sig m1 < proj1_sig m2) -> let Fsub := fun (n : Count N) => match (excluded_middle_informative (n = m1)) with
  | left _ => F m2
  | right _ => match (excluded_middle_informative (n = m2)) with
    | left _ => F m1
    | right _ => F n
  end
end in SumF CM N (fun x : Count N => proj1_sig (F x)) = SumF CM N (fun x : Count N => proj1_sig (Fsub x)))).
intro H3.
intro m.
elim m.
intros F1 F2 H1 H2 H4.
cut (F1 = F2).
intro H5.
rewrite H5.
reflexivity.
apply functional_extensionality.
intro x.
apply (H4 x).
apply (le_0_n (proj1_sig x)).
intros n H4 F1.
elim (classic (n < N)).
intros H5 F2 H1 H2 H6.
elim H2.
intros G2 H7.
elim (classic (G2 (F1 (exist (fun (x : nat) => x < N) n H5)) = (exist (fun (x : nat) => x < N) n H5))).
intro H8.
apply H4.
apply H1.
apply H2.
intros m0 H9.
elim (le_lt_or_eq n (proj1_sig m0) H9).
apply (H6 m0).
intro H10.
cut (m0 = (exist (fun x : nat => x < N) n H5)).
intro H11.
rewrite H11.
rewrite<- H8 at 2.
rewrite (proj2 H7 (F1 (exist (fun x : nat => x < N) n H5))).
reflexivity.
apply sig_map.
simpl.
rewrite H10.
reflexivity.
cut (let a := (G2 (F1 (exist (fun x : nat => x < N) n H5))) in let b := (exist (fun x : nat => x < N) n H5) in G2 (F1 (exist (fun x : nat => x < N) n H5)) <> exist (fun x : nat => x < N) n H5 -> SumF CM N (fun x : Count N => proj1_sig (F1 x)) = SumF CM N (fun x : Count N => proj1_sig (F2 x))).
intro H8.
apply H8.
intros a b H8.
cut (let F2sub := fun (n : Count N) => match (excluded_middle_informative (n = a)) with
  | left _ => F2 b
  | right _ => match (excluded_middle_informative (n = b)) with
    | left _ => F2 a
    | right _ => F2 n
  end
end in SumF CM N (fun x : Count N => proj1_sig (F1 x)) = SumF CM N (fun x : Count N => proj1_sig (F2 x))).
intro H9.
apply H9.
intro F2sub.
cut (proj1_sig a < proj1_sig b).
intro H9.
cut (SumF CM N (fun x : Count N => proj1_sig (F1 x)) = SumF CM N (fun x : Count N => proj1_sig (F2sub x))).
intro H10.
cut (SumF CM N (fun x : Count N => proj1_sig (F2 x)) = SumF CM N (fun x : Count N => proj1_sig (F2sub x))).
intro H11.
rewrite H11.
apply H10.
apply (H3 F2 a b H9).
apply (H4 F1 F2sub).
apply H1.
exists (fun (x : {x : CMT CM | A x}) => if excluded_middle_informative (G2 x = a) then b else if excluded_middle_informative (G2 x = b) then a else G2 x).
apply conj.
intro x.
elim (excluded_middle_informative (G2 (F2sub x) = a)).
unfold F2sub.
elim (excluded_middle_informative (x = a)).
intros H10 H11.
rewrite H10.
rewrite<- (proj1 H7 b).
apply H11.
intro H10.
elim (excluded_middle_informative (x = b)).
intro H11.
intro H12.
rewrite H11.
reflexivity.
intros H11 H12.
apply False_ind.
apply H10.
rewrite<- (proj1 H7 x).
apply H12.
intro H10.
elim (excluded_middle_informative (G2 (F2sub x) = b)).
unfold F2sub.
elim (excluded_middle_informative (x = a)).
intros H11 H12.
rewrite H11.
reflexivity.
intro H11.
elim (excluded_middle_informative (x = b)).
intros H12 H13.
apply False_ind.
apply (lt_irrefl (proj1_sig a)).
rewrite<- (proj1 H7 a) at 2.
rewrite H13.
apply H9.
intros H12 H13.
apply False_ind.
apply H12.
rewrite<- (proj1 H7 x).
apply H13.
intro H11.
unfold F2sub.
elim (excluded_middle_informative (x = a)).
intro H12.
apply False_ind.
apply H11.
unfold F2sub.
elim (excluded_middle_informative (x = a)).
intro H13.
apply (proj1 H7 b).
intro H13.
apply False_ind.
apply (H13 H12).
intro H12.
elim (excluded_middle_informative (x = b)).
intro H13.
apply False_ind.
apply H10.
unfold F2sub.
elim (excluded_middle_informative (x = a)).
intro H14.
apply False_ind.
apply (H12 H14).
intro H14.
elim (excluded_middle_informative (x = b)).
intro H15.
apply (proj1 H7 a).
intro H15.
apply False_ind.
apply (H15 H13).
intro H13.
apply (proj1 H7 x).
intro y.
elim (excluded_middle_informative (G2 y = a)).
intro H10.
unfold F2sub.
elim (excluded_middle_informative (@eq (Count N) b a)).
intro H11.
apply False_ind.
apply (lt_irrefl (proj1_sig a)).
rewrite<- H11 at 2.
apply H9.
intro H11.
elim (excluded_middle_informative (@eq (Count N) b b)).
intro H12.
rewrite<- H10.
apply (proj2 H7 y).
intro H12.
apply False_ind.
apply H12.
reflexivity.
intro H10.
elim (excluded_middle_informative (G2 y = b)).
intro H11.
unfold F2sub.
elim (excluded_middle_informative (a = a)).
intro H12.
rewrite<- H11.
apply (proj2 H7 y).
intro H12.
apply False_ind.
apply H12.
reflexivity.
intro H11.
unfold F2sub.
elim (excluded_middle_informative (G2 y = a)).
intro H12.
apply False_ind.
apply (H10 H12).
intro H12.
elim (excluded_middle_informative (G2 y = b)).
intro H13.
apply False_ind.
apply (H11 H13).
intro H13.
apply (proj2 H7 y).
intro m0.
intro H10.
elim (le_lt_or_eq n (proj1_sig m0) H10).
intro H11.
rewrite (H6 m0 H11).
unfold F2sub.
elim (excluded_middle_informative (m0 = a)).
intro H12.
apply False_ind.
apply (lt_irrefl (proj1_sig a)).
apply (PeanoNat.Nat.le_trans (S (proj1_sig a)) n (proj1_sig a)).
apply H9.
rewrite<- H12.
apply H10.
intro H12.
elim (excluded_middle_informative (m0 = b)).
intro H13.
apply False_ind.
apply (lt_irrefl (proj1_sig b)).
rewrite<- H13 at 2.
apply H11.
intro H13.
reflexivity.
intro H11.
unfold F2sub.
elim (excluded_middle_informative (m0 = a)).
intro H12.
apply False_ind.
apply (lt_irrefl (proj1_sig b)).
unfold proj1_sig at 1.
unfold b at 1.
rewrite H11.
rewrite H12.
apply H9.
intro H12.
elim (excluded_middle_informative (m0 = b)).
intro H13.
rewrite H13.
unfold a.
rewrite (proj2 H7 (F1 (exist (fun x : nat => x < N) n H5))).
reflexivity.
intro H13.
apply False_ind.
apply H13.
apply sig_map.
simpl.
rewrite H11.
reflexivity.
elim (nat_total_order (proj1_sig a) (proj1_sig b)).
intro H9.
apply H9.
intro H9.
apply False_ind.
apply H8.
elim H1.
intros G1 H10.
rewrite<- (proj1 H10 (G2 (F1 (exist (fun x : nat => x < N) n H5)))).
rewrite (H6 (G2 (F1 (exist (fun x : nat => x < N) n H5)))).
rewrite (proj2 H7 (F1 (exist (fun x : nat => x < N) n H5))).
apply (proj1 H10 (exist (fun x : nat => x < N) n H5)).
apply H9.
intro H9.
apply H8.
apply sig_map.
apply H9.
intros H5 F2 H6 H7 H8.
apply (H4 F1 F2 H6 H7).
intros m0 H9.
apply False_ind.
apply H5.
apply (PeanoNat.Nat.le_lt_trans n (proj1_sig m0) N).
apply H9.
apply (proj2_sig m0).
cut (forall (diff : nat) (F : Count N -> {x : CMT CM | A x}) (m1 m2 : Count N), proj1_sig m2 = proj1_sig m1 + diff -> let Fsub := fun n : Count N => if excluded_middle_informative (n = m1) then F m2 else if excluded_middle_informative (n = m2) then F m1 else F n in SumF CM N (fun x : Count N => proj1_sig (F x)) = SumF CM N (fun x : Count N => proj1_sig (Fsub x))).
intro H1.
intros F m1 m2 H3.
apply (H1 (proj1_sig m2 - proj1_sig m1) F m1 m2).
rewrite (Minus.le_plus_minus_r (proj1_sig m1) (proj1_sig m2)).
reflexivity.
apply (PeanoNat.Nat.le_trans (proj1_sig m1) (S (proj1_sig m1)) (proj1_sig m2)).
apply (le_S (proj1_sig m1) (proj1_sig m1)).
apply (le_n (proj1_sig m1)).
apply H3.
cut (forall (F : Count N -> {x : CMT CM | A x}), (forall (m : nat) (H1 : m < N) (H2 : S m < N), let Fsub := fun (n : Count N) => match (excluded_middle_informative (proj1_sig n = m)) with
  | left _ => F (exist (fun (n0 : nat) => n0 < N) (S m) H2)
  | right _ => match (excluded_middle_informative (proj1_sig n = S m)) with
    | left _ => F (exist (fun (n0 : nat) => n0 < N) m H1)
    | right _ => F n
  end
end in SumF CM N (fun x : Count N => proj1_sig (F x)) = SumF CM N (fun x : Count N => proj1_sig (Fsub x)))).
intros H1 diff.
elim diff.
intros F m1 m2 H3 Fsub.
cut (F = Fsub).
intro H4.
rewrite H4.
reflexivity.
cut (m1 = m2).
intro H4.
apply functional_extensionality.
intro x.
unfold Fsub.
elim (excluded_middle_informative (x = m1)).
intro H5.
rewrite H5.
rewrite H4.
reflexivity.
intro H5.
elim (excluded_middle_informative (x = m2)).
intro H6.
rewrite H6.
rewrite H4.
reflexivity.
intro H6.
reflexivity.
apply sig_map.
rewrite H3.
rewrite (Plus.plus_0_r (proj1_sig m1)).
reflexivity.
intros dif H2 F m1 m3 H4 Fsub.
cut (proj1_sig m1 + dif < N).
intro H5.
cut (let m2 := (exist (fun (n : nat) => n < N) (proj1_sig m1 + dif) H5) in SumF CM N (fun x : Count N => proj1_sig (F x)) = SumF CM N (fun x : Count N => proj1_sig (Fsub x))).
intro H6.
apply H6.
intro m2.
cut (let Fsub1 := fun n : Count N => if excluded_middle_informative (n = m1) then F m2 else if excluded_middle_informative (n = m2) then F m1 else F n in SumF CM N (fun x : Count N => proj1_sig (F x)) = SumF CM N (fun x : Count N => proj1_sig (Fsub x))).
intro H6.
apply H6.
intro Fsub1.
cut (let Fsub2 := fun n : Count N => if excluded_middle_informative (n = m1) then Fsub m2 else if excluded_middle_informative (n = m2) then Fsub m1 else Fsub n in SumF CM N (fun x : Count N => proj1_sig (F x)) = SumF CM N (fun x : Count N => proj1_sig (Fsub x))).
intro H6.
apply H6.
intro Fsub2.
cut (SumF CM N (fun x : Count N => proj1_sig (Fsub1 x)) = SumF CM N (fun x : Count N => proj1_sig (Fsub2 x))).
intro H6.
cut (SumF CM N (fun x : Count N => proj1_sig (F x)) = SumF CM N (fun x : Count N => proj1_sig (Fsub1 x))).
intro H7.
cut (SumF CM N (fun x : Count N => proj1_sig (Fsub x)) = SumF CM N (fun x : Count N => proj1_sig (Fsub2 x))).
intro H8.
rewrite H7.
rewrite H8.
apply H6.
apply (H2 Fsub m1 m2).
reflexivity.
apply (H2 F m1 m2).
reflexivity.
cut (S (proj1_sig m1 + dif) < N).
intro H6.
cut (let Fsub3 := fun n : Count N => if excluded_middle_informative (proj1_sig n = proj1_sig m1 + dif) then Fsub1 (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6) else if excluded_middle_informative (proj1_sig n = S (proj1_sig m1 + dif)) then Fsub1 (exist (fun n1 : nat => n1 < N) (proj1_sig m1 + dif) H5) else Fsub1 n in SumF CM N (fun x : Count N => proj1_sig (Fsub1 x)) = SumF CM N (fun x : Count N => proj1_sig (Fsub2 x))).
intro H7.
apply H7.
intro Fsub3.
cut (Fsub2 = Fsub3).
intro H7.
rewrite H7.
unfold Fsub3.
apply (H1 Fsub1 (proj1_sig m1 + dif) H5 H6).
apply functional_extensionality.
intro x.
unfold Fsub2.
unfold Fsub3.
elim (excluded_middle_informative (x = m1)).
intro H7.
unfold Fsub.
elim (excluded_middle_informative (@eq (Count N) m2 m1)).
intro H8.
elim (excluded_middle_informative (proj1_sig x = proj1_sig m1 + dif)).
intro H9.
unfold Fsub1.
elim (excluded_middle_informative (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6 = m1)).
intro H10.
apply False_ind.
apply (lt_irrefl (proj1_sig m1)).
rewrite<- H10 at 2.
simpl.
apply (PeanoNat.Nat.le_lt_trans (proj1_sig m1) (proj1_sig m1 + dif) (S (proj1_sig m1 + dif))).
apply (Plus.le_plus_l (proj1_sig m1) dif).
apply (le_n (S (proj1_sig m1 + dif))).
intro H10.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n0 : nat => lt n0 N) (S (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif)) H6) m1)).
intro H11.
apply False_ind.
apply (H10 H11).
intro H11.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n0 : nat => lt n0 N) (S (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif)) H6) m2)).
intro H12.
apply False_ind.
apply H11.
rewrite H12.
apply H8.
intro H12.
cut (m3 = (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6)).
intro H13.
rewrite H13.
reflexivity.
apply sig_map.
simpl.
rewrite H4.
auto.
intro H9.
apply False_ind.
apply H9.
rewrite H7.
rewrite<- H8 at 1.
reflexivity.
intro H8.
elim (excluded_middle_informative (@eq (Count N) m2 m3)).
intro H9.
apply False_ind.
apply (lt_irrefl (proj1_sig m2)).
rewrite H9 at 2.
simpl.
rewrite H4.
apply (Plus.plus_lt_compat_l dif (S dif) (proj1_sig m1)).
apply (le_n (S dif)).
intro H9.
elim (excluded_middle_informative (proj1_sig x = proj1_sig m1 + dif)).
intro H10.
apply False_ind.
apply H8.
apply sig_map.
simpl.
rewrite<- H10.
rewrite H7.
reflexivity.
intro H10.
elim (excluded_middle_informative (proj1_sig x = S (proj1_sig m1 + dif))).
intro H11.
apply False_ind.
apply (lt_irrefl (proj1_sig m1)).
rewrite<- H7 at 2.
rewrite H11.
apply (PeanoNat.Nat.le_lt_trans (proj1_sig m1) (proj1_sig m1 + dif) (S (proj1_sig m1 + dif))).
apply (Plus.le_plus_l (proj1_sig m1) dif).
apply (le_n (S (proj1_sig m1 + dif))).
intro H11.
unfold Fsub1.
elim (excluded_middle_informative (x = m1)).
intro H12.
reflexivity.
intro H12.
apply False_ind.
apply (H12 H7).
intro H7.
elim (excluded_middle_informative (x = m2)).
intro H8.
elim (excluded_middle_informative (proj1_sig x = proj1_sig m1 + dif)).
intro H9.
unfold Fsub.
elim (excluded_middle_informative (m1 = m1)).
intro H10.
unfold Fsub1.
elim (excluded_middle_informative (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6 = m1)).
intro H11.
apply False_ind.
apply (lt_irrefl (proj1_sig m1)).
rewrite<- H11 at 2.
simpl.
apply (PeanoNat.Nat.le_lt_trans (proj1_sig m1) (proj1_sig m1 + dif) (S (proj1_sig m1 + dif))).
apply (Plus.le_plus_l (proj1_sig m1) dif).
apply (le_n (S (proj1_sig m1 + dif))).
intro H11.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n0 : nat => lt n0 N) (S (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif)) H6) m1)).
intro H12.
apply False_ind.
apply (H11 H12).
intro H12.
elim (excluded_middle_informative (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6 = m2)).
intro H13.
apply False_ind.
apply (lt_irrefl (proj1_sig m2)).
rewrite<- H13 at 2.
unfold m2.
simpl.
apply (le_n (S (proj1_sig m1 + dif))).
intro H13.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n0 : nat => lt n0 N) (S (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif)) H6) m2)).
intro H14.
apply False_ind.
apply (H13 H14).
intro H14.
cut (m3 = (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6)).
intro H15.
rewrite H15.
reflexivity.
apply sig_map.
simpl.
rewrite H4.
auto.
intro H10.
apply False_ind.
apply H10.
reflexivity.
intro H9.
apply False_ind.
apply H9.
rewrite H8.
reflexivity.
intro H8.
elim (excluded_middle_informative (proj1_sig x = proj1_sig m1 + dif)).
intro H9.
apply False_ind.
apply H8.
apply sig_map.
rewrite H9.
reflexivity.
intro H9.
elim (excluded_middle_informative (proj1_sig x = S (proj1_sig m1 + dif))).
intro H10.
unfold Fsub.
elim (excluded_middle_informative (x = m1)).
intro H11.
apply False_ind.
apply (H7 H11).
intro H11.
elim (excluded_middle_informative (x = m3)).
intro H12.
unfold Fsub1.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n1 : nat => lt n1 N) (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif) H5) m1)).
intro H13.
rewrite<- H13.
cut (exist (fun n1 : nat => n1 < N) (proj1_sig m1 + dif) H5 = m2).
intro H14.
rewrite H14.
reflexivity.
apply sig_map.
reflexivity.
intro H13.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n1 : nat => lt n1 N) (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif) H5) m2)).
intro H14.
reflexivity.
intro H14.
apply False_ind.
apply H14.
apply sig_map.
reflexivity.
intro H12.
apply False_ind.
apply H12.
apply sig_map.
rewrite H4.
rewrite H10.
auto.
intro H10.
unfold Fsub.
elim (excluded_middle_informative (x = m1)).
intro H11.
apply False_ind.
apply (H7 H11).
intro H11.
elim (excluded_middle_informative (x = m3)).
intro H12.
apply False_ind.
apply H10.
rewrite H12.
rewrite H4.
auto.
intro H12.
unfold Fsub1.
elim (excluded_middle_informative (x = m1)).
intro H13.
apply False_ind.
apply (H11 H13).
intro H13.
elim (excluded_middle_informative (x = m2)).
intro H14.
apply False_ind.
apply (H8 H14).
intro H14.
reflexivity.
cut (S (proj1_sig m1 + dif) = proj1_sig m1 + S dif).
intro H6.
rewrite H6.
rewrite<- H4.
apply (proj2_sig m3).
auto.
apply (PeanoNat.Nat.lt_trans (proj1_sig m1 + dif) (proj1_sig m1 + S dif) N).
apply (Plus.plus_lt_compat_l dif (S dif) (proj1_sig m1)).
apply (le_n (S dif)).
rewrite<- H4.
apply (proj2_sig m3).
intros F m H1 H2 Fsub.
unfold SumF.
cut (forall (n : nat), (n = S m -> SumFSub CM N (fun x : Count N => proj1_sig (F x)) (S n) = SumFSub CM N (fun x : Count N => proj1_sig (Fsub x)) (S n)) /\ (n <> S m -> SumFSub CM N (fun x : Count N => proj1_sig (F x)) n = SumFSub CM N (fun x : Count N => proj1_sig (Fsub x)) n)).
intro H3.
apply (proj2 (H3 N)).
intro H4.
apply (lt_irrefl N).
rewrite H4 at 1.
apply H2.
intro n.
elim n.
apply conj.
intro H3.
apply False_ind.
apply (PeanoNat.Nat.neq_succ_0 m).
rewrite H3.
reflexivity.
intro H3.
simpl.
reflexivity.
intros n0 H3.
apply conj.
intro H4.
simpl.
rewrite (CM_assoc CM (SumFSub CM N (fun x : Count N => proj1_sig (F x)) n0) (UnwrapF CM N (fun x : Count N => proj1_sig (F x)) n0) (UnwrapF CM N (fun x : Count N => proj1_sig (F x)) (S n0))).
rewrite (CM_assoc CM (SumFSub CM N (fun x : Count N => proj1_sig (Fsub x)) n0) (UnwrapF CM N (fun x : Count N => proj1_sig (Fsub x)) n0) (UnwrapF CM N (fun x : Count N => proj1_sig (Fsub x)) (S n0))).
cut ((CMc CM (UnwrapF CM N (fun x : Count N => proj1_sig (F x)) n0) (UnwrapF CM N (fun x : Count N => proj1_sig (F x)) (S n0))) = (CMc CM (UnwrapF CM N (fun x : Count N => proj1_sig (Fsub x)) n0) (UnwrapF CM N (fun x : Count N => proj1_sig (Fsub x)) (S n0)))).
intro H5.
rewrite H5.
cut ((SumFSub CM N (fun x : Count N => proj1_sig (F x)) n0) = (SumFSub CM N (fun x : Count N => proj1_sig (Fsub x)) n0)).
intro H6.
rewrite H6.
reflexivity.
apply (proj2 H3).
rewrite<- H4.
apply (n_Sn n0).
unfold UnwrapF.
elim (excluded_middle_informative (n0 < N)).
intro a.
elim (excluded_middle_informative ((S n0) < N)).
intro b.
unfold Fsub.
elim (excluded_middle_informative (proj1_sig (exist (fun n1 : nat => n1 < N) n0 a) = m)).
simpl.
intro H5.
elim (excluded_middle_informative (proj1_sig (exist (fun n1 : nat => n1 < N) (S n0) b) = m)).
simpl.
intro H6.
apply False_ind.
apply (n_Sn n0).
rewrite H5 at 1.
rewrite H6.
reflexivity.
intro H6.
elim (excluded_middle_informative (S n0 = m)).
intro H7.
apply False_ind.
apply (n_Sn n0).
rewrite H7.
rewrite H5.
reflexivity.
intro H7.
elim (excluded_middle_informative (S n0 = S m)).
intro H8.
rewrite (CM_comm CM ((fun x : Count N => proj1_sig (F x)) (exist (fun n1 : nat => n1 < N) (S m) H2)) ((fun x : Count N => proj1_sig (F x)) (exist (fun n1 : nat => n1 < N) m H1))).
cut ((exist (fun n1 : nat => n1 < N) n0 a) = (exist (fun n1 : nat => n1 < N) m H1)).
intro H9.
rewrite H9.
cut ((exist (fun n1 : nat => n1 < N) (S n0) b) = (exist (fun n1 : nat => n1 < N) (S m) H2)).
intro H10.
rewrite H10.
reflexivity.
apply sig_map.
simpl.
apply H8.
apply sig_map.
simpl.
apply H5.
intro H8.
apply False_ind.
apply (H8 H4).
intro H5.
apply False_ind.
apply H5.
simpl.
apply (PeanoNat.Nat.succ_inj n0 m).
apply H4.
intro H5.
apply False_ind.
apply H5.
rewrite H4.
apply H2.
intro H5.
apply False_ind.
apply H5.
cut (n0 = m).
intro H6.
rewrite H6.
apply H1.
apply (PeanoNat.Nat.succ_inj n0 m).
apply H4.
intro H4.
elim (classic (n0 = S m)).
apply (proj1 H3).
intro H5.
simpl.
rewrite<- (proj2 H3 H5).
unfold UnwrapF.
elim (excluded_middle_informative (n0 < N)).
intro a.
unfold Fsub.
elim (excluded_middle_informative (proj1_sig (exist (fun n1 : nat => n1 < N) n0 a) = m)).
simpl.
intro H6.
apply False_ind.
apply H4.
rewrite H6.
reflexivity.
intro H6.
elim (excluded_middle_informative (proj1_sig (exist (fun n1 : nat => n1 < N) n0 a) = S m)).
simpl.
intro H7.
apply False_ind.
apply (H5 H7).
intro H7.
reflexivity.
intro H6.
reflexivity.
Qed.

Lemma SumWellDefined : forall (CM : CommutativeMonoid) (A : {X : Ensemble (CMT CM) | Finite (CMT CM) X}), {s : (CMT CM) | forall (F : (Count (Counter (CMT CM) A)) -> {x : (CMT CM) | proj1_sig A x}), (Bijective (Count (Counter (CMT CM) A)) {x : (CMT CM) | proj1_sig A x} F) -> (SumF CM (Counter (CMT CM) A) (fun (x : (Count (Counter (CMT CM) A))) => proj1_sig (F x))) = s}.
Proof.
intros CM A.
apply constructive_definite_description.
apply (proj1 (unique_existence (fun (x : CMT CM) => forall F : Count (Counter (CMT CM) A) -> {x0 : CMT CM | proj1_sig A x0}, Bijective (Count (Counter (CMT CM) A)) {x0 : CMT CM | proj1_sig A x0} F -> SumF CM (Counter (CMT CM) A) (fun x0 : Count (Counter (CMT CM) A) => proj1_sig (F x0)) = x))).
apply conj.
elim (CountExistBijectiveFunction (CMT CM) (Counter (CMT CM) A) (proj1_sig A)).
intros F H1.
exists (SumF CM (Counter (CMT CM) A) (fun x : Count (Counter (CMT CM) A) => proj1_sig (F x))).
intros F1 H2.
apply (SumWellDefinedSub2 CM (proj1_sig A) (Counter (CMT CM) A) F1 F H2 H1).
apply (CounterNature (CMT CM) A).
intros S1 S2 H1 H2.
elim (CountExistBijectiveFunction (CMT CM) (Counter (CMT CM) A) (proj1_sig A)).
intros F H3.
rewrite<- (H1 F H3).
rewrite<- (H2 F H3).
reflexivity.
apply (CounterNature (CMT CM) A).
Qed.

Definition MySum (CM : CommutativeMonoid) (A : {X : Ensemble (CMT CM) | Finite (CMT CM) X}) := proj1_sig (SumWellDefined CM A).

Lemma MuSumNature : forall (CM : CommutativeMonoid) (A : {X : Ensemble (CMT CM) | Finite (CMT CM) X}) (F : (Count (Counter (CMT CM) A)) -> {x : (CMT CM) | proj1_sig A x}), (Bijective (Count (Counter (CMT CM) A)) {x : (CMT CM) | proj1_sig A x} F) -> (SumF CM (Counter (CMT CM) A) (fun (x : (Count (Counter (CMT CM) A))) => proj1_sig (F x))) = MySum CM A.
Proof.
intros CM A.
apply (proj2_sig (SumWellDefined CM A)).
Qed.

Definition FiniteType (U : Type) := Finite U (Full_set U).

Definition UnwrapGF (U : Type) (CM : CommutativeMonoid) (N : nat) (G : (Count N) -> U) (F : U -> (CMT CM)) := fun (n : nat) => match (excluded_middle_informative (n < N)) with
  | left a => (F (G (exist (fun (n0 : nat) => (n0 < N)%nat) n a)))
  | right _ => CMe CM
end.

Definition SumGFSub (U : Type) (CM : CommutativeMonoid) (N : nat) := fix SumGFSub (G : (Count N) -> U) (F : U -> (CMT CM)) (n : nat) {struct n} : (CMT CM) := match n with
  | O => CMe CM
  | S n0 => CMc CM (SumGFSub G F n0) (UnwrapGF U CM N G F n0)
end.

Definition SumGF (U : Type) (CM : CommutativeMonoid) (N : nat) := fun (G : (Count N) -> U) (F : U -> (CMT CM)) => SumGFSub U CM N G F N.

Lemma SumFWellDefinedSub : forall (U : Type) (CM : CommutativeMonoid) (N : nat) (G1 G2 : (Count N) -> U) (F : U -> (CMT CM)), (Bijective (Count N) U G1) -> (Bijective (Count N) U G2) -> ((SumGF U CM N G1 F) = (SumGF U CM N G2 F)).
Proof.
intros U CM N.
cut (forall (m : nat) (G1 G2 : Count N -> U) (F : U -> CMT CM), Bijective (Count N) U G1 -> Bijective (Count N) U G2 -> (forall (m0 : Count N), (proj1_sig m0 >= m) -> (G1 m0) = (G2 m0)) -> SumGF U CM N G1 F = SumGF U CM N G2 F).
intros H3 G1 G2 F H1 H2.
apply (H3 N G1 G2 F H1 H2).
intros m H4.
apply False_ind.
apply (le_not_lt N (proj1_sig m) H4 (proj2_sig m)).
cut (forall (G : Count N -> U) (F : U -> CMT CM), (forall (m1 m2 : Count N) , (proj1_sig m1 < proj1_sig m2) -> let Gsub := fun (n : Count N) => match (excluded_middle_informative (n = m1)) with
  | left _ => G m2
  | right _ => match (excluded_middle_informative (n = m2)) with
    | left _ => G m1
    | right _ => G n
  end
end in SumGF U CM N G F = SumGF U CM N Gsub F)).
intro H3.
intro m.
elim m.
intros G1 G2 F H1 H2 H4.
cut (G1 = G2).
intro H5.
rewrite H5.
reflexivity.
apply functional_extensionality.
intro x.
apply (H4 x).
apply (le_0_n (proj1_sig x)).
intros n H4 G1.
elim (classic (n < N)).
intros H5 G2 F H1 H2 H6.
elim H2.
intros GI2 H7.
elim (classic (GI2 (G1 (exist (fun (x : nat) => x < N) n H5)) = (exist (fun (x : nat) => x < N) n H5))).
intro H8.
apply H4.
apply H1.
apply H2.
intros m0 H9.
elim (le_lt_or_eq n (proj1_sig m0) H9).
apply (H6 m0).
intro H10.
cut (m0 = (exist (fun x : nat => x < N) n H5)).
intro H11.
rewrite H11.
rewrite<- H8 at 2.
rewrite (proj2 H7 (G1 (exist (fun x : nat => x < N) n H5))).
reflexivity.
apply sig_map.
simpl.
rewrite H10.
reflexivity.
cut (let a := (GI2 (G1 (exist (fun x : nat => x < N) n H5))) in let b := (exist (fun x : nat => x < N) n H5) in GI2 (G1 (exist (fun x : nat => x < N) n H5)) <> exist (fun x : nat => x < N) n H5 -> SumGF U CM N G1 F = SumGF U CM N G2 F).
intro H8.
apply H8.
intros a b H8.
cut (let G2sub := fun (n : Count N) => match (excluded_middle_informative (n = a)) with
  | left _ => G2 b
  | right _ => match (excluded_middle_informative (n = b)) with
    | left _ => G2 a
    | right _ => G2 n
  end
end in SumGF U CM N G1 F = SumGF U CM N G2 F).
intro H9.
apply H9.
intro G2sub.
cut (proj1_sig a < proj1_sig b).
intro H9.
cut (SumGF U CM N G1 F = SumGF U CM N G2sub F).
intro H10.
cut (SumGF U CM N G2 F = SumGF U CM N G2sub F).
intro H11.
rewrite H11.
apply H10.
apply (H3 G2 F a b H9).
apply (H4 G1 G2sub).
apply H1.
exists (fun (x : U) => if excluded_middle_informative (GI2 x = a) then b else if excluded_middle_informative (GI2 x = b) then a else GI2 x).
apply conj.
intro x.
elim (excluded_middle_informative (GI2 (G2sub x) = a)).
unfold G2sub.
elim (excluded_middle_informative (x = a)).
intros H10 H11.
rewrite H10.
rewrite<- (proj1 H7 b).
apply H11.
intro H10.
elim (excluded_middle_informative (x = b)).
intro H11.
intro H12.
rewrite H11.
reflexivity.
intros H11 H12.
apply False_ind.
apply H10.
rewrite<- (proj1 H7 x).
apply H12.
intro H10.
elim (excluded_middle_informative (GI2 (G2sub x) = b)).
unfold G2sub.
elim (excluded_middle_informative (x = a)).
intros H11 H12.
rewrite H11.
reflexivity.
intro H11.
elim (excluded_middle_informative (x = b)).
intros H12 H13.
apply False_ind.
apply (lt_irrefl (proj1_sig a)).
rewrite<- (proj1 H7 a) at 2.
rewrite H13.
apply H9.
intros H12 H13.
apply False_ind.
apply H12.
rewrite<- (proj1 H7 x).
apply H13.
intro H11.
unfold G2sub.
elim (excluded_middle_informative (x = a)).
intro H12.
apply False_ind.
apply H11.
unfold G2sub.
elim (excluded_middle_informative (x = a)).
intro H13.
apply (proj1 H7 b).
intro H13.
apply False_ind.
apply (H13 H12).
intro H12.
elim (excluded_middle_informative (x = b)).
intro H13.
apply False_ind.
apply H10.
unfold G2sub.
elim (excluded_middle_informative (x = a)).
intro H14.
apply False_ind.
apply (H12 H14).
intro H14.
elim (excluded_middle_informative (x = b)).
intro H15.
apply (proj1 H7 a).
intro H15.
apply False_ind.
apply (H15 H13).
intro H13.
apply (proj1 H7 x).
intro y.
elim (excluded_middle_informative (GI2 y = a)).
intro H10.
unfold G2sub.
elim (excluded_middle_informative (@eq (Count N) b a)).
intro H11.
apply False_ind.
apply (lt_irrefl (proj1_sig a)).
rewrite<- H11 at 2.
apply H9.
intro H11.
elim (excluded_middle_informative (@eq (Count N) b b)).
intro H12.
rewrite<- H10.
apply (proj2 H7 y).
intro H12.
apply False_ind.
apply H12.
reflexivity.
intro H10.
elim (excluded_middle_informative (GI2 y = b)).
intro H11.
unfold G2sub.
elim (excluded_middle_informative (a = a)).
intro H12.
rewrite<- H11.
apply (proj2 H7 y).
intro H12.
apply False_ind.
apply H12.
reflexivity.
intro H11.
unfold G2sub.
elim (excluded_middle_informative (GI2 y = a)).
intro H12.
apply False_ind.
apply (H10 H12).
intro H12.
elim (excluded_middle_informative (GI2 y = b)).
intro H13.
apply False_ind.
apply (H11 H13).
intro H13.
apply (proj2 H7 y).
intro m0.
intro H10.
elim (le_lt_or_eq n (proj1_sig m0) H10).
intro H11.
rewrite (H6 m0 H11).
unfold G2sub.
elim (excluded_middle_informative (m0 = a)).
intro H12.
apply False_ind.
apply (lt_irrefl (proj1_sig a)).
apply (PeanoNat.Nat.le_trans (S (proj1_sig a)) n (proj1_sig a)).
apply H9.
rewrite<- H12.
apply H10.
intro H12.
elim (excluded_middle_informative (m0 = b)).
intro H13.
apply False_ind.
apply (lt_irrefl (proj1_sig b)).
rewrite<- H13 at 2.
apply H11.
intro H13.
reflexivity.
intro H11.
unfold G2sub.
elim (excluded_middle_informative (m0 = a)).
intro H12.
apply False_ind.
apply (lt_irrefl (proj1_sig b)).
unfold proj1_sig at 1.
unfold b at 1.
rewrite H11.
rewrite H12.
apply H9.
intro H12.
elim (excluded_middle_informative (m0 = b)).
intro H13.
rewrite H13.
unfold a.
rewrite (proj2 H7 (G1 (exist (fun x : nat => x < N) n H5))).
reflexivity.
intro H13.
apply False_ind.
apply H13.
apply sig_map.
simpl.
rewrite H11.
reflexivity.
elim (nat_total_order (proj1_sig a) (proj1_sig b)).
intro H9.
apply H9.
intro H9.
apply False_ind.
apply H8.
elim H1.
intros GI1 H10.
rewrite<- (proj1 H10 (GI2 (G1 (exist (fun x : nat => x < N) n H5)))).
rewrite (H6 (GI2 (G1 (exist (fun x : nat => x < N) n H5)))).
rewrite (proj2 H7 (G1 (exist (fun x : nat => x < N) n H5))).
apply (proj1 H10 (exist (fun x : nat => x < N) n H5)).
apply H9.
intro H9.
apply H8.
apply sig_map.
apply H9.
intros H5 G2 F H6 H7 H8.
apply (H4 G1 G2 F H6 H7).
intros m0 H9.
apply False_ind.
apply H5.
apply (PeanoNat.Nat.le_lt_trans n (proj1_sig m0) N).
apply H9.
apply (proj2_sig m0).
cut (forall (diff : nat) (G : Count N -> U) (F : U -> CMT CM) (m1 m2 : Count N), proj1_sig m2 = proj1_sig m1 + diff -> let Gsub := fun n : Count N => if excluded_middle_informative (n = m1) then G m2 else if excluded_middle_informative (n = m2) then G m1 else G n in SumGF U CM N G F = SumGF U CM N Gsub F).
intro H1.
intros G F m1 m2 H3.
apply (H1 (proj1_sig m2 - proj1_sig m1) G F m1 m2).
rewrite (Minus.le_plus_minus_r (proj1_sig m1) (proj1_sig m2)).
reflexivity.
apply (PeanoNat.Nat.le_trans (proj1_sig m1) (S (proj1_sig m1)) (proj1_sig m2)).
apply (le_S (proj1_sig m1) (proj1_sig m1)).
apply (le_n (proj1_sig m1)).
apply H3.
cut (forall (G : Count N -> U) (F : U -> CMT CM), (forall (m : nat) (H1 : m < N) (H2 : S m < N), let Gsub := fun (n : Count N) => match (excluded_middle_informative (proj1_sig n = m)) with
  | left _ => G (exist (fun (n0 : nat) => n0 < N) (S m) H2)
  | right _ => match (excluded_middle_informative (proj1_sig n = S m)) with
    | left _ => G (exist (fun (n0 : nat) => n0 < N) m H1)
    | right _ => G n
  end
end in SumGF U CM N G F = SumGF U CM N Gsub F)).
intros H1 diff.
elim diff.
intros G F m1 m2 H3 Gsub.
cut (G = Gsub).
intro H4.
rewrite H4.
reflexivity.
cut (m1 = m2).
intro H4.
apply functional_extensionality.
intro x.
unfold Gsub.
elim (excluded_middle_informative (x = m1)).
intro H5.
rewrite H5.
rewrite H4.
reflexivity.
intro H5.
elim (excluded_middle_informative (x = m2)).
intro H6.
rewrite H6.
rewrite H4.
reflexivity.
intro H6.
reflexivity.
apply sig_map.
rewrite H3.
rewrite (Plus.plus_0_r (proj1_sig m1)).
reflexivity.
intros dif H2 G F m1 m3 H4 Gsub.
cut (proj1_sig m1 + dif < N).
intro H5.
cut (let m2 := (exist (fun (n : nat) => n < N) (proj1_sig m1 + dif) H5) in SumGF U CM N G F = SumGF U CM N Gsub F).
intro H6.
apply H6.
intro m2.
cut (let Gsub1 := fun n : Count N => if excluded_middle_informative (n = m1) then G m2 else if excluded_middle_informative (n = m2) then G m1 else G n in SumGF U CM N G F = SumGF U CM N Gsub F).
intro H6.
apply H6.
intro Gsub1.
cut (let Gsub2 := fun n : Count N => if excluded_middle_informative (n = m1) then Gsub m2 else if excluded_middle_informative (n = m2) then Gsub m1 else Gsub n in SumGF U CM N G F = SumGF U CM N Gsub F).
intro H6.
apply H6.
intro Gsub2.
cut (SumGF U CM N Gsub1 F = SumGF U CM N Gsub2 F).
intro H6.
cut (SumGF U CM N G F = SumGF U CM N Gsub1 F).
intro H7.
cut (SumGF U CM N Gsub F = SumGF U CM N Gsub2 F).
intro H8.
rewrite H7.
rewrite H8.
apply H6.
apply (H2 Gsub F m1 m2).
reflexivity.
apply (H2 G F m1 m2).
reflexivity.
cut (S (proj1_sig m1 + dif) < N).
intro H6.
cut (let Gsub3 := fun n : Count N => if excluded_middle_informative (proj1_sig n = proj1_sig m1 + dif) then Gsub1 (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6) else if excluded_middle_informative (proj1_sig n = S (proj1_sig m1 + dif)) then Gsub1 (exist (fun n1 : nat => n1 < N) (proj1_sig m1 + dif) H5) else Gsub1 n in SumGF U CM N Gsub1 F = SumGF U CM N Gsub2 F).
intro H7.
apply H7.
intro Gsub3.
cut (Gsub2 = Gsub3).
intro H7.
rewrite H7.
unfold Gsub3.
apply (H1 Gsub1 F (proj1_sig m1 + dif) H5 H6).
apply functional_extensionality.
intro x.
unfold Gsub2.
unfold Gsub3.
elim (excluded_middle_informative (x = m1)).
intro H7.
unfold Gsub.
elim (excluded_middle_informative (@eq (Count N) m2 m1)).
intro H8.
elim (excluded_middle_informative (proj1_sig x = proj1_sig m1 + dif)).
intro H9.
unfold Gsub1.
elim (excluded_middle_informative (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6 = m1)).
intro H10.
apply False_ind.
apply (lt_irrefl (proj1_sig m1)).
rewrite<- H10 at 2.
simpl.
apply (PeanoNat.Nat.le_lt_trans (proj1_sig m1) (proj1_sig m1 + dif) (S (proj1_sig m1 + dif))).
apply (Plus.le_plus_l (proj1_sig m1) dif).
apply (le_n (S (proj1_sig m1 + dif))).
intro H10.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n0 : nat => lt n0 N) (S (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif)) H6) m1)).
intro H11.
apply False_ind.
apply (H10 H11).
intro H11.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n0 : nat => lt n0 N) (S (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif)) H6) m2)).
intro H12.
apply False_ind.
apply H11.
rewrite H12.
apply H8.
intro H12.
cut (m3 = (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6)).
intro H13.
rewrite H13.
reflexivity.
apply sig_map.
simpl.
rewrite H4.
auto.
intro H9.
apply False_ind.
apply H9.
rewrite H7.
rewrite<- H8 at 1.
reflexivity.
intro H8.
elim (excluded_middle_informative (@eq (Count N) m2 m3)).
intro H9.
apply False_ind.
apply (lt_irrefl (proj1_sig m2)).
rewrite H9 at 2.
simpl.
rewrite H4.
apply (Plus.plus_lt_compat_l dif (S dif) (proj1_sig m1)).
apply (le_n (S dif)).
intro H9.
elim (excluded_middle_informative (proj1_sig x = proj1_sig m1 + dif)).
intro H10.
apply False_ind.
apply H8.
apply sig_map.
simpl.
rewrite<- H10.
rewrite H7.
reflexivity.
intro H10.
elim (excluded_middle_informative (proj1_sig x = S (proj1_sig m1 + dif))).
intro H11.
apply False_ind.
apply (lt_irrefl (proj1_sig m1)).
rewrite<- H7 at 2.
rewrite H11.
apply (PeanoNat.Nat.le_lt_trans (proj1_sig m1) (proj1_sig m1 + dif) (S (proj1_sig m1 + dif))).
apply (Plus.le_plus_l (proj1_sig m1) dif).
apply (le_n (S (proj1_sig m1 + dif))).
intro H11.
unfold Gsub1.
elim (excluded_middle_informative (x = m1)).
intro H12.
reflexivity.
intro H12.
apply False_ind.
apply (H12 H7).
intro H7.
elim (excluded_middle_informative (x = m2)).
intro H8.
elim (excluded_middle_informative (proj1_sig x = proj1_sig m1 + dif)).
intro H9.
unfold Gsub.
elim (excluded_middle_informative (m1 = m1)).
intro H10.
unfold Gsub1.
elim (excluded_middle_informative (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6 = m1)).
intro H11.
apply False_ind.
apply (lt_irrefl (proj1_sig m1)).
rewrite<- H11 at 2.
simpl.
apply (PeanoNat.Nat.le_lt_trans (proj1_sig m1) (proj1_sig m1 + dif) (S (proj1_sig m1 + dif))).
apply (Plus.le_plus_l (proj1_sig m1) dif).
apply (le_n (S (proj1_sig m1 + dif))).
intro H11.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n0 : nat => lt n0 N) (S (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif)) H6) m1)).
intro H12.
apply False_ind.
apply (H11 H12).
intro H12.
elim (excluded_middle_informative (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6 = m2)).
intro H13.
apply False_ind.
apply (lt_irrefl (proj1_sig m2)).
rewrite<- H13 at 2.
unfold m2.
simpl.
apply (le_n (S (proj1_sig m1 + dif))).
intro H13.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n0 : nat => lt n0 N) (S (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif)) H6) m2)).
intro H14.
apply False_ind.
apply (H13 H14).
intro H14.
cut (m3 = (exist (fun n0 : nat => n0 < N) (S (proj1_sig m1 + dif)) H6)).
intro H15.
rewrite H15.
reflexivity.
apply sig_map.
simpl.
rewrite H4.
auto.
intro H10.
apply False_ind.
apply H10.
reflexivity.
intro H9.
apply False_ind.
apply H9.
rewrite H8.
reflexivity.
intro H8.
elim (excluded_middle_informative (proj1_sig x = proj1_sig m1 + dif)).
intro H9.
apply False_ind.
apply H8.
apply sig_map.
rewrite H9.
reflexivity.
intro H9.
elim (excluded_middle_informative (proj1_sig x = S (proj1_sig m1 + dif))).
intro H10.
unfold Gsub.
elim (excluded_middle_informative (x = m1)).
intro H11.
apply False_ind.
apply (H7 H11).
intro H11.
elim (excluded_middle_informative (x = m3)).
intro H12.
unfold Gsub1.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n1 : nat => lt n1 N) (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif) H5) m1)).
intro H13.
rewrite<- H13.
cut (exist (fun n1 : nat => n1 < N) (proj1_sig m1 + dif) H5 = m2).
intro H14.
rewrite H14.
reflexivity.
apply sig_map.
reflexivity.
intro H13.
elim (excluded_middle_informative (@eq (Count N) (@exist nat (fun n1 : nat => lt n1 N) (Nat.add (@proj1_sig nat (fun n : nat => lt n N) m1) dif) H5) m2)).
intro H14.
reflexivity.
intro H14.
apply False_ind.
apply H14.
apply sig_map.
reflexivity.
intro H12.
apply False_ind.
apply H12.
apply sig_map.
rewrite H4.
rewrite H10.
auto.
intro H10.
unfold Gsub.
elim (excluded_middle_informative (x = m1)).
intro H11.
apply False_ind.
apply (H7 H11).
intro H11.
elim (excluded_middle_informative (x = m3)).
intro H12.
apply False_ind.
apply H10.
rewrite H12.
rewrite H4.
auto.
intro H12.
unfold Gsub1.
elim (excluded_middle_informative (x = m1)).
intro H13.
apply False_ind.
apply (H11 H13).
intro H13.
elim (excluded_middle_informative (x = m2)).
intro H14.
apply False_ind.
apply (H8 H14).
intro H14.
reflexivity.
cut (S (proj1_sig m1 + dif) = proj1_sig m1 + S dif).
intro H6.
rewrite H6.
rewrite<- H4.
apply (proj2_sig m3).
auto.
apply (PeanoNat.Nat.lt_trans (proj1_sig m1 + dif) (proj1_sig m1 + S dif) N).
apply (Plus.plus_lt_compat_l dif (S dif) (proj1_sig m1)).
apply (le_n (S dif)).
rewrite<- H4.
apply (proj2_sig m3).
intros G F m H1 H2 Gsub.
unfold SumGF.
cut (forall (n : nat), (n = S m -> SumGFSub U CM N G F (S n) = SumGFSub U CM N Gsub F (S n)) /\ (n <> S m -> SumGFSub U CM N G F n = SumGFSub U CM N Gsub F n)).
intro H3.
apply (proj2 (H3 N)).
intro H4.
apply (lt_irrefl N).
rewrite H4 at 1.
apply H2.
intro n.
elim n.
apply conj.
intro H3.
apply False_ind.
apply (PeanoNat.Nat.neq_succ_0 m).
rewrite H3.
reflexivity.
intro H3.
simpl.
reflexivity.
intros n0 H3.
apply conj.
intro H4.
simpl.
rewrite (CM_assoc CM (SumGFSub U CM N G F n0) (UnwrapGF U CM N G F n0) (UnwrapGF U CM N G F (S n0))).
rewrite (CM_assoc CM (SumGFSub U CM N Gsub F n0) (UnwrapGF U CM N Gsub F n0) (UnwrapGF U CM N Gsub F (S n0))).
cut ((CMc CM (UnwrapGF U CM N G F n0) (UnwrapGF U CM N G F (S n0))) = (CMc CM (UnwrapGF U CM N Gsub F n0) (UnwrapGF U CM N Gsub F (S n0)))).
intro H5.
rewrite H5.
cut ((SumGFSub U CM N G F n0) = (SumGFSub U CM N Gsub F n0)).
intro H6.
rewrite H6.
reflexivity.
apply (proj2 H3).
rewrite<- H4.
apply (n_Sn n0).
unfold UnwrapGF.
elim (excluded_middle_informative (n0 < N)).
intro a.
elim (excluded_middle_informative ((S n0) < N)).
intro b.
unfold Gsub.
elim (excluded_middle_informative (proj1_sig (exist (fun n1 : nat => n1 < N) n0 a) = m)).
simpl.
intro H5.
elim (excluded_middle_informative (proj1_sig (exist (fun n1 : nat => n1 < N) (S n0) b) = m)).
simpl.
intro H6.
apply False_ind.
apply (n_Sn n0).
rewrite H5 at 1.
rewrite H6.
reflexivity.
intro H6.
elim (excluded_middle_informative (S n0 = m)).
intro H7.
apply False_ind.
apply (n_Sn n0).
rewrite H7.
rewrite H5.
reflexivity.
intro H7.
elim (excluded_middle_informative (S n0 = S m)).
intro H8.
rewrite (CM_comm CM (F (G (exist (fun n1 : nat => n1 < N) (S m) H2))) (F (G (exist (fun n1 : nat => n1 < N) m H1)))).
cut ((exist (fun n1 : nat => n1 < N) n0 a) = (exist (fun n1 : nat => n1 < N) m H1)).
intro H9.
rewrite H9.
cut ((exist (fun n1 : nat => n1 < N) (S n0) b) = (exist (fun n1 : nat => n1 < N) (S m) H2)).
intro H10.
rewrite H10.
reflexivity.
apply sig_map.
simpl.
apply H8.
apply sig_map.
simpl.
apply H5.
intro H8.
apply False_ind.
apply (H8 H4).
intro H5.
apply False_ind.
apply H5.
simpl.
apply (PeanoNat.Nat.succ_inj n0 m).
apply H4.
intro H5.
apply False_ind.
apply H5.
rewrite H4.
apply H2.
intro H5.
apply False_ind.
apply H5.
cut (n0 = m).
intro H6.
rewrite H6.
apply H1.
apply (PeanoNat.Nat.succ_inj n0 m).
apply H4.
intro H4.
elim (classic (n0 = S m)).
apply (proj1 H3).
intro H5.
simpl.
rewrite<- (proj2 H3 H5).
unfold UnwrapGF.
elim (excluded_middle_informative (n0 < N)).
intro a.
unfold Gsub.
elim (excluded_middle_informative (proj1_sig (exist (fun n1 : nat => n1 < N) n0 a) = m)).
simpl.
intro H6.
apply False_ind.
apply H4.
rewrite H6.
reflexivity.
intro H6.
elim (excluded_middle_informative (proj1_sig (exist (fun n1 : nat => n1 < N) n0 a) = S m)).
simpl.
intro H7.
apply False_ind.
apply (H5 H7).
intro H7.
reflexivity.
intro H6.
reflexivity.
Qed.

Definition CounterType (U : Type) (H : (FiniteType U)) := Counter U (exist (Finite U) (Full_set U) H).

Lemma SumFWellDefined : forall (U : Type) (H : FiniteType U) (CM : CommutativeMonoid) (F : U -> (CMT CM)), {s : (CMT CM) | forall (G : (Count (CounterType U H)) -> U), (Bijective (Count (CounterType U H)) U G) -> (SumGF U CM (CounterType U H) G F) = s}.
Proof.
intros U H1 CM F.
apply constructive_definite_description.
apply (proj1 (unique_existence (fun (x : (CMT CM)) => forall G : Count (CounterType U H1) -> U,Bijective (Count (CounterType U H1)) U G -> SumGF U CM (CounterType U H1) G F = x))).
elim (CountExistBijectiveFunction U (CounterType U H1) (Full_set U)).
intros g H2.
cut (let G := fun (x : Count (CounterType U H1)) => proj1_sig (g x) in (exists x : CMT CM, forall G : Count (CounterType U H1) -> U, Bijective (Count (CounterType U H1)) U G -> SumGF U CM (CounterType U H1) G F = x) /\ uniqueness (fun x : CMT CM => forall G : Count (CounterType U H1) -> U, Bijective (Count (CounterType U H1)) U G -> SumGF U CM (CounterType U H1) G F = x)).
intro H3.
apply H3.
intro G.
cut (Bijective (Count (CounterType U H1)) U G).
intro H3.
apply conj.
exists (SumGF U CM (CounterType U H1) G F).
intros GI H4.
apply (SumFWellDefinedSub U CM (CounterType U H1) GI G F H4 H3).
elim H2.
intros gi H4.
intros S1 S2 H5 H6.
rewrite<- (H5 G H3).
rewrite<- (H6 G H3).
reflexivity.
elim H2.
intros gi H3.
exists (fun (u : U) => (gi (exist (Full_set U) u (Full_intro U u)))).
apply conj.
intro x.
cut ((exist (Full_set U) (G x) (Full_intro U (G x))) = g x).
intro H4.
rewrite H4.
apply (proj1 H3 x).
apply sig_map.
reflexivity.
intro y.
unfold G.
rewrite (proj2 H3 (exist (Full_set U) y (Full_intro U y))).
reflexivity.
apply (CounterNature U (exist (Finite U) (Full_set U) H1)).
Qed.

Definition MySumF (U : Type) (H : FiniteType U) (CM : CommutativeMonoid) (F : U -> (CMT CM)) := proj1_sig (SumFWellDefined U H CM F).

Lemma MySumFNature : forall (U : Type) (H : FiniteType U) (CM : CommutativeMonoid) (F : U -> (CMT CM)) (G : (Count (CounterType U H)) -> U), (Bijective (Count (CounterType U H)) U G) -> (SumGF U CM (CounterType U H) G F) = (MySumF U H CM F).
Proof.
intros U H1 CM F.
apply (proj2_sig (SumFWellDefined U H1 CM F)).
Qed.

Lemma EnsembleSetCardinal : forall (U : Type) (n : nat) (A : Ensemble U), (cardinal {u : U | A u} (Full_set {u : U | A u}) n) <-> (cardinal U A n).
Proof.
cut (forall (n : nat) (U : Type) (A : Ensemble U) (B : Ensemble U), cardinal {u : U | A u} (fun (uu : {u : U | A u}) => B (proj1_sig uu)) n <-> cardinal U (Intersection U A B) n).
intro H1.
intros U n A.
cut ((Full_set {u : U | A u}) = (fun uu : {u : U | A u} => (Full_set U) (proj1_sig uu))).
intro H2.
cut (A = (Intersection U A (Full_set U))).
intro H3.
rewrite H2.
rewrite H3 at 1.
apply (H1 n U A (Full_set U)).
apply Extensionality_Ensembles.
apply conj.
intros u H3.
apply (Intersection_intro U A (Full_set U) u H3).
apply (Full_intro U u).
intros u H3.
elim H3.
intros uu H4 H5.
apply H4.
apply Extensionality_Ensembles.
apply conj.
intros u H3.
apply (Full_intro U (proj1_sig u)).
intros u H3.
apply (Full_intro {u0 : U | A u0} u).
intro n.
elim n.
intros U A B.
apply conj.
intro H1.
cut ((Intersection U A B) = Empty_set U).
intro H2.
rewrite H2.
apply (card_empty U).
apply Extensionality_Ensembles.
apply conj.
intros u H2.
apply False_ind.
cut ((fun uu : {u : U | A u} => B (proj1_sig uu)) = (Empty_set {u : U | A u})).
intro H3.
cut (In U A u).
intro H4.
cut (Empty_set {u : U | A u} (exist A u H4)).
intro H5.
elim H5.
rewrite<- H3.
cut (In U B u).
intro H5.
apply H5.
elim H2.
intros x H5 H6.
apply H6.
elim H2.
intros x H4 H5.
apply H4.
apply (cardinal_elim {u : U | A u} (fun uu : {u0 : U | A u0} => B (proj1_sig uu)) O).
apply H1.
intros u H2.
elim H2.
intro H1.
cut ((fun uu : {u : U | A u} => B (proj1_sig uu)) = (Empty_set {u : U | A u})).
intro H2.
rewrite H2.
apply (card_empty {u : U | A u}).
apply Extensionality_Ensembles.
apply conj.
intros u H2.
cut ((Intersection U A B) = (Empty_set U)).
intro H3.
cut (In U (Intersection U A B) (proj1_sig u)).
rewrite H3.
intro H4.
elim H4.
apply (Intersection_intro U A B (proj1_sig u) (proj2_sig u) H2).
apply (cardinal_elim U (Intersection U A B) O).
apply H1.
intros u H2.
elim H2.
intros n0 H1.
intros U A B.
apply conj.
intro H2.
elim (cardinal_invert {u : U | A u} (fun uu : {u : U | A u} => B (proj1_sig uu)) (S n0) H2).
intros AB0 H3.
elim H3.
intros ab H4.
cut ((Intersection U A B) = Add U (fun (x : U) => exists (y : {u : U | A u}), (AB0 y) /\ x = (proj1_sig y)) (proj1_sig ab)).
intro H5.
rewrite H5.
apply card_add.
cut ((fun x : U => exists y : {u : U | A u}, AB0 y /\ x = proj1_sig y) = Intersection U A (fun x : U => exists y : {u : U | A u}, AB0 y /\ x = proj1_sig y)).
intro H6.
rewrite H6.
apply (proj1 (H1 U A (fun x : U => exists y : {u : U | A u}, AB0 y /\ x = proj1_sig y))).
cut ((fun uu : {u : U | A u} => exists y : {u : U | A u}, AB0 y /\ proj1_sig uu = proj1_sig y) = AB0).
intro H7.
rewrite H7.
apply (proj2 (proj2 H4)).
apply Extensionality_Ensembles.
apply conj.
intros u H7.
elim H7.
intros uu H8.
cut (u = uu).
intro H9.
rewrite H9.
apply (proj1 H8).
apply sig_map.
apply (proj2 H8).
intros u H7.
exists u.
apply conj.
apply H7.
reflexivity.
apply Extensionality_Ensembles.
apply conj.
intros u H6.
apply Intersection_intro.
elim H6.
intros uu H7.
rewrite (proj2 H7).
apply (proj2_sig uu).
apply H6.
intros u H6.
elim H6.
intros uu H7 H8.
apply H8.
intro H6.
elim H6.
intros u H7.
apply (proj1 (proj2 H4)).
cut (ab = u).
intro H8.
rewrite H8.
apply (proj1 H7).
apply sig_map.
apply (proj2 H7).
apply Extensionality_Ensembles.
apply conj.
intros u H5.
elim H5.
intros uu H6 H7.
cut (In {u : U | A u} (Add {u : U | A u} AB0 ab) (exist A uu H6)).
cut ((Add {u : U | A u} AB0 ab) = (fun (x : {u : U | A u}) => (match (excluded_middle_informative (AB0 x)) with
  | left _ => True
  | right _ => x = ab
end))).
intro H8.
rewrite H8.
unfold In.
elim (excluded_middle_informative (AB0 (exist A uu H6))).
intros H9 H10.
apply Union_introl.
exists (exist A uu H6).
apply conj.
apply H9.
reflexivity.
intros H9 H10.
apply Union_intror.
rewrite<- H10.
reflexivity.
apply Extensionality_Ensembles.
apply conj.
intros uuu H8.
unfold In.
elim (excluded_middle_informative (AB0 uuu)).
intro H9.
apply I.
elim H8.
intros uuuu H9 H10.
apply False_ind.
apply (H10 H9).
intros uuuu H9 H10.
rewrite H9.
reflexivity.
intro uuu.
unfold In.
elim (excluded_middle_informative (AB0 uuu)).
intros H8 H9.
apply Union_introl.
apply H8.
intros H8 H9.
apply Union_intror.
rewrite H9.
reflexivity.
rewrite<- (proj1 H4).
apply H7.
intros u H5.
elim H5.
intros uu H6.
apply Intersection_intro.
elim H6.
intros uuu H7.
rewrite (proj2 H7).
apply (proj2_sig uuu).
elim H6.
intros uuu H7.
rewrite (proj2 H7).
cut (In {u : U | A u} (fun uu : {u : U | A u} => B (proj1_sig uu)) uuu).
intro H8.
apply H8.
rewrite (proj1 H4).
apply Union_introl.
apply (proj1 H7).
intros uu H6.
apply Intersection_intro.
rewrite<- H6.
apply (proj2_sig ab).
rewrite<- H6.
cut (In {u : U | A u} (fun uu : {u : U | A u} => B (proj1_sig uu)) ab).
intro H7.
apply H7.
rewrite (proj1 H4).
apply Union_intror.
reflexivity.
intro H2.
elim (cardinal_invert U (Intersection U A B) (S n0) H2).
intros AB0 H3.
elim H3.
intros u H4.
cut (A u).
intro H5.
cut ((fun uu : {u0 : U | A u0} => B (proj1_sig uu)) = Add {u0 : U | A u0} (fun uu : {u0 : U | A u0} => AB0 (proj1_sig uu)) (exist A u H5)).
intro H6.
rewrite H6.
apply card_add.
apply (proj2 (H1 U A AB0)).
cut ((Intersection U A AB0) = AB0).
intro H7.
rewrite H7.
apply (proj2 (proj2 H4)).
apply Extensionality_Ensembles.
apply conj.
intros uu H7.
elim H7.
intros uuu H8 H9.
apply H9.
intros uu H7.
apply Intersection_intro.
cut ((Add U AB0 u) uu).
rewrite<- (proj1 H4).
intro H8.
elim H8.
intros uuu H9 H10.
apply H9.
apply Union_introl.
apply H7.
apply H7.
apply (proj1 (proj2 H4)).
apply Extensionality_Ensembles.
apply conj.
intros uu H6.
cut (In U (Intersection U A B) (proj1_sig uu)).
rewrite (proj1 H4).
intro H7.
cut (forall (uuu : U), In U (Add U AB0 u) uuu -> (AB0 uuu) \/ u = uuu).
intro H8.
elim (H8 (proj1_sig uu)).
intro H9.
apply Union_introl.
apply H9.
intro H9.
apply Union_intror.
cut ((exist A u H5) = uu).
intro H10.
rewrite H10.
apply In_singleton.
apply sig_map.
rewrite<- H9.
reflexivity.
apply H7.
intros uuu H8.
elim H8.
intros uuuu H9.
left.
apply H9.
intros uuuu H9.
right.
rewrite H9.
reflexivity.
apply Intersection_intro.
apply (proj2_sig uu).
apply H6.
intros uu H6.
elim H6.
intros uuu H7.
cut ((Intersection U A B) (proj1_sig uuu)).
intro H8.
cut (In U B (proj1_sig uuu)).
intro H9.
apply H9.
elim H8.
intros uuuu H9 H10.
apply H10.
rewrite (proj1 H4).
apply Union_introl.
apply H7.
intros uuu H7.
cut ((Intersection U A B) (proj1_sig uuu)).
intro H8.
cut (In U B (proj1_sig uuu)).
intro H9.
apply H9.
elim H8.
intros uuuu H9 H10.
apply H10.
rewrite (proj1 H4).
apply Union_intror.
rewrite<- H7.
reflexivity.
cut ((Add U AB0 u) u).
rewrite<- (proj1 H4).
intro H5.
elim H5.
intros uu H6 H7.
apply H6.
apply Union_intror.
reflexivity.
Qed.

Lemma EnsembleSetFinite : forall (U : Type) (A : Ensemble U), (Finite {u : U | A u} (Full_set {u : U | A u})) <-> Finite U A.
Proof.
intros U A.
apply conj.
intro H1.
elim (finite_cardinal {u : U | A u} (Full_set {u : U | A u}) H1).
intros n H2.
apply (cardinal_finite U A n).
apply EnsembleSetCardinal.
apply H2.
intro H1.
elim (finite_cardinal U A H1).
intros n H2.
apply (cardinal_finite {u : U | A u} (Full_set {u : U | A u}) n).
apply EnsembleSetCardinal.
apply H2.
Qed.

Definition MySumF2 (U : Type) (A : {X : Ensemble U | Finite U X}) (CM : CommutativeMonoid) (F : U -> (CMT CM)) := MySumF {u : U | (proj1_sig A) u} (proj2 (EnsembleSetFinite U (proj1_sig A)) (proj2_sig A)) CM (fun (x : {u : U | (proj1_sig A) u}) => F (proj1_sig x)).

Lemma MySumF2Nature : forall (U : Type) (A : {X : Ensemble U | Finite U X}) (CM : CommutativeMonoid) (F : U -> (CMT CM)) (G : (Count (Counter U A)) -> U) (H1 : forall (x : (Count (Counter U A))), proj1_sig A (G x)), (Bijective (Count (Counter U A)) {u : U | (proj1_sig A) u} (fun (x : (Count (Counter U A))) => exist (proj1_sig A) (G x) (H1 x))) -> (SumGF U CM (Counter U A) G F) = (MySumF2 U A CM F).
Proof.
intros U A CM.
cut ((Counter U A) = (CounterType {u : U | proj1_sig A u} (proj2 (EnsembleSetFinite U (proj1_sig A)) (proj2_sig A)))).
intro H1.
rewrite H1.
intros F G H2 H3.
unfold MySumF2.
unfold MySumF.
rewrite<- (proj2_sig (SumFWellDefined {u : U | proj1_sig A u} (proj2 (EnsembleSetFinite U (proj1_sig A)) (proj2_sig A)) CM (fun x : {u : U | proj1_sig A u} => F (proj1_sig x))) (fun (x : (Count (CounterType {u : U | proj1_sig A u} (proj2 (EnsembleSetFinite U (proj1_sig A)) (proj2_sig A))))) => exist (proj1_sig A) (G x) (H2 x))).
unfold SumGF.
cut (forall (n : nat), SumGFSub U CM (CounterType {u : U | proj1_sig A u} (proj2 (EnsembleSetFinite U (proj1_sig A)) (proj2_sig A))) G F n = SumGFSub {u : U | proj1_sig A u} CM (CounterType {u : U | proj1_sig A u} (proj2 (EnsembleSetFinite U (proj1_sig A)) (proj2_sig A))) (fun (x : Count (CounterType {u : U | proj1_sig A u} (proj2 (EnsembleSetFinite U (proj1_sig A)) (proj2_sig A)))) => exist (proj1_sig A) (G x) (H2 x)) (fun x : {u : U | proj1_sig A u} => F (proj1_sig x)) n).
intro H4.
apply (H4 (CounterType {u : U | proj1_sig A u} (proj2 (EnsembleSetFinite U (proj1_sig A)) (proj2_sig A)))).
intros n.
elim n.
simpl.
reflexivity.
intros n0 H4.
simpl.
cut ((UnwrapGF U CM (CounterType {u : U | proj1_sig A u} (proj2 (EnsembleSetFinite U (proj1_sig A)) (proj2_sig A))) G F n0) = (UnwrapGF {u : U | proj1_sig A u} CM (CounterType {u : U | proj1_sig A u} (proj2 (EnsembleSetFinite U (proj1_sig A)) (proj2_sig A))) (fun x : Count (CounterType {u : U | proj1_sig A u} (proj2 (EnsembleSetFinite U (proj1_sig A)) (proj2_sig A))) => exist (proj1_sig A) (G x) (H2 x)) (fun (x : {u : U | proj1_sig A u}) => F (proj1_sig x)) n0)).
intro H5.
rewrite H5.
rewrite H4.
reflexivity.
unfold UnwrapGF.
elim (excluded_middle_informative (n0 < CounterType {u : U | proj1_sig A u} (proj2 (EnsembleSetFinite U (proj1_sig A)) (proj2_sig A)))).
intro H5.
reflexivity.
intro H5.
reflexivity.
apply H3.
unfold CounterType.
unfold Counter.
elim (finite_cardinal U (proj1_sig A) (proj2_sig A)).
intros n H1.
rewrite<- (cardinal_is_functional U (proj1_sig A) n H1 (proj1_sig A) (proj1_sig (NumWellDefined U (proj1_sig A) (proj2_sig A))) (proj2_sig (NumWellDefined U (proj1_sig A) (proj2_sig A)))).
simpl.
cut (cardinal {u : U | proj1_sig A u} (Full_set {u : U | proj1_sig A u}) n).
intro H2.
rewrite<- (cardinal_is_functional {u : U | proj1_sig A u} (Full_set {u : U | proj1_sig A u}) n H2 (Full_set {u : U | proj1_sig A u}) (proj1_sig (NumWellDefined {u : U | proj1_sig A u} (Full_set {u : U | proj1_sig A u}) (proj2 (EnsembleSetFinite U (proj1_sig A)) (proj2_sig A)))) (proj2_sig (NumWellDefined {u : U | proj1_sig A u} (Full_set {u : U | proj1_sig A u}) (proj2 (EnsembleSetFinite U (proj1_sig A)) (proj2_sig A))))).
reflexivity.
reflexivity.
apply EnsembleSetCardinal.
apply H1.
reflexivity.
Qed.

Lemma ExistBijectiveFunctionCount : forall (U : Type) (n : nat) (A : Ensemble U), (exists (F : (Count n) -> {x : U | A x}), Bijective (Count n) {x : U | A x} F) -> (cardinal U A n).
Proof.
intros U n.
elim n.
intros A H1.
elim H1.
intros F H2.
elim H2.
intros G H3.
cut (A = Empty_set U).
intro H4.
rewrite H4.
apply card_empty.
apply Extensionality_Ensembles.
apply conj.
intros a H4.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig (G (exist A a H4)))).
apply (proj2_sig (G (exist A a H4))).
intros u H4.
elim H4.
intros n0 H1 A H2.
elim H2.
intros F H3.
cut (forall (n1 : Count n0), proj1_sig n1 < S n0).
intro H4.
cut (A = Add U (fun (u : U) => exists (n1 : Count n0), u = proj1_sig (F (exist (fun (m : nat) => m < S n0) (proj1_sig n1) (H4 n1)))) (proj1_sig (F (exist (fun (m : nat) => m < S n0) n0 (le_n (S n0)))))).
intro H5.
rewrite H5.
apply card_add.
apply (H1 (fun u : U => exists n1 : Count n0, u = proj1_sig (F (exist (fun m : nat => m < S n0) (proj1_sig n1) (H4 n1))))).
cut (forall (n2 : Count n0),exists (n1 : Count n0), proj1_sig (F (exist (fun m : nat => m < S n0) (proj1_sig n2) (H4 n2))) = proj1_sig (F (exist (fun m : nat => m < S n0) (proj1_sig n1) (H4 n1)))).
intro H6.
exists (fun (n1 : Count n0) => exist (fun (x : U) => exists n1 : Count n0, x = proj1_sig (F (exist (fun m : nat => m < S n0) (proj1_sig n1) (H4 n1)))) (proj1_sig (F (exist (fun m : nat => m < S n0) (proj1_sig n1) (H4 n1)))) (H6 n1)).
elim H3.
intros G H7.
cut (forall (u : {x : U | exists n1 : Count n0, x = proj1_sig (F (exist (fun m : nat => m < S n0) (proj1_sig n1) (H4 n1)))}), (A (proj1_sig u))).
intro H8.
cut (forall (u : {x : U | exists n1 : Count n0, x = proj1_sig (F (exist (fun m : nat => m < S n0) (proj1_sig n1) (H4 n1)))}), proj1_sig (G (exist A (proj1_sig u) (H8 u))) < n0).
intro H9.
exists (fun (u : {x : U | exists n1 : Count n0, x = proj1_sig (F (exist (fun m : nat => m < S n0) (proj1_sig n1) (H4 n1)))}) => exist (fun (n2 : nat) => n2 < n0) (proj1_sig (G (exist A (proj1_sig u) (H8 u)))) (H9 u)).
apply conj.
intros n3.
apply sig_map.
simpl.
cut ((exist A (proj1_sig (F (exist (fun m : nat => m < S n0) (proj1_sig n3) (H4 n3)))) (H8 (exist (fun x : U => exists n1 : Count n0, x = proj1_sig (F (exist (fun m : nat => m < S n0) (proj1_sig n1) (H4 n1)))) (proj1_sig (F (exist (fun m : nat => m < S n0) (proj1_sig n3) (H4 n3)))) (H6 n3)))) = (F (exist (fun m : nat => m < S n0) (proj1_sig n3) (H4 n3)))).
intro H10.
rewrite H10.
rewrite (proj1 H7 (exist (fun m : nat => m < S n0) (proj1_sig n3) (H4 n3))).
reflexivity.
apply sig_map.
reflexivity.
intro y.
apply sig_map.
simpl.
cut ((exist (fun m : nat => m < S n0) (proj1_sig (G (exist A (proj1_sig y) (H8 y)))) (H4 (exist (fun n2 : nat => n2 < n0) (proj1_sig (G (exist A (proj1_sig y) (H8 y)))) (H9 y)))) = (G (exist A (proj1_sig y) (H8 y)))).
intro H10.
rewrite H10.
rewrite (proj2 H7 (exist A (proj1_sig y) (H8 y))).
reflexivity.
apply sig_map.
reflexivity.
intro u.
elim (proj2_sig u).
intros x H9.
cut (A (proj1_sig (F (exist (fun m : nat => m < S n0) (proj1_sig x) (H4 x))))).
intro H10.
cut ((exist A (proj1_sig u) (H8 u)) = (exist A (proj1_sig (F (exist (fun m : nat => m < S n0) (proj1_sig x) (H4 x)))) H10)).
intro H11.
rewrite H11.
cut ((exist A (proj1_sig (F (exist (fun m : nat => m < S n0) (proj1_sig x) (H4 x)))) H10) = (F (exist (fun m : nat => m < S n0) (proj1_sig x) (H4 x)))).
intro H12.
rewrite H12.
rewrite (proj1 H7 (exist (fun m : nat => m < S n0) (proj1_sig x) (H4 x))).
apply (proj2_sig x).
apply sig_map.
reflexivity.
apply sig_map.
apply H9.
rewrite<- H9.
apply (H8 u).
intro u.
elim (proj2_sig u).
intros n1 H8.
rewrite H8.
apply (proj2_sig (F (exist (fun m : nat => m < S n0) (proj1_sig n1) (H4 n1)))).
intro n2.
exists n2.
reflexivity.
intro H6.
elim H6.
intros n1 H7.
apply (PeanoNat.Nat.lt_irrefl (proj1_sig n1)).
cut (n0 = (proj1_sig n1)).
intro H8.
rewrite<- H8 at 2.
apply (proj2_sig n1).
cut ((F (exist (fun m : nat => m < S n0) n0 (le_n (S n0)))) = (F (exist (fun m : nat => m < S n0) (proj1_sig n1) (H4 n1)))).
intro H8.
cut (proj1_sig (exist (fun m : nat => m < S n0) n0 (le_n (S n0))) = proj1_sig (exist (fun m : nat => m < S n0) (proj1_sig n1) (H4 n1))).
intro H9.
apply H9.
elim H3.
intros G H9.
rewrite<- (proj1 H9 (exist (fun m : nat => m < S n0) n0 (le_n (S n0)))).
rewrite H8.
rewrite (proj1 H9 (exist (fun m : nat => m < S n0) (proj1_sig n1) (H4 n1))).
reflexivity.
apply sig_map.
apply H7.
apply Extensionality_Ensembles.
apply conj.
intros a H5.
elim H3.
intros G H6.
elim (classic (proj1_sig (G (exist A a H5)) < n0)).
intro H7.
apply Union_introl.
exists (exist (fun (n1 : nat) => n1 < n0) (proj1_sig (G (exist A a H5))) H7).
simpl.
cut ((exist (fun m : nat => m < S n0) (proj1_sig (G (exist A a H5))) (H4 (exist (fun n1 : nat => n1 < n0) (proj1_sig (G (exist A a H5))) H7))) = (G (exist A a H5))).
intro H8.
rewrite H8.
rewrite (proj2 H6 (exist A a H5)).
reflexivity.
apply sig_map.
reflexivity.
intro H7.
apply Union_intror.
cut (proj1_sig (G (exist A a H5)) = n0).
intro H8.
cut ((exist (fun m : nat => m < S n0) n0 (le_n (S n0))) = (G (exist A a H5))).
intro H9.
rewrite H9.
rewrite (proj2 H6 (exist A a H5)).
apply In_singleton.
apply sig_map.
rewrite H8.
reflexivity.
elim (le_lt_or_eq (S (proj1_sig (G (exist A a H5)))) (S n0)).
intro H8.
apply False_ind.
apply H7.
apply (lt_S_n (proj1_sig (G (exist A a H5))) n0 H8).
intro H8.
apply (PeanoNat.Nat.succ_inj (proj1_sig (G (exist A a H5))) n0 H8).
apply (proj2_sig (G (exist A a H5))).
intros u H5.
elim H5.
intros u0 H6.
elim H6.
intros n1 H7.
rewrite H7.
apply (proj2_sig (F (exist (fun m : nat => m < S n0) (proj1_sig n1) (H4 n1)))).
intros u0 H6.
rewrite<- H6.
apply (proj2_sig (F (exist (fun m : nat => m < S n0) n0 (le_n (S n0))))).
intro n1.
apply (le_S (S (proj1_sig n1)) n0).
apply (proj2_sig n1).
Qed.

Lemma MySumF2Nature2 : forall (U : Type) (A : {X : Ensemble U | Finite U X}) (CM : CommutativeMonoid) (F : U -> (CMT CM)) (N : nat) (G : (Count N) -> U) (H1 : forall (n : Count N), proj1_sig A (G n)), Bijective (Count N) {u : U | proj1_sig A u} (fun x : Count N => exist (proj1_sig A) (G x) (H1 x)) -> (SumGF U CM N G F) = (MySumF2 U A CM F).
Proof.
cut (forall (U : Type) (A : {X : Ensemble U | Finite U X}) (CM : CommutativeMonoid) (F : U -> CMT CM) (N : nat), (exists (G1 : Count N -> U), (forall n0 : Count N, proj1_sig A (G1 n0)) /\ (forall (H1 : forall n : Count N, proj1_sig A (G1 n)), (Bijective (Count N) {u : U | proj1_sig A u} (fun x : Count N => exist (proj1_sig A) (G1 x) (H1 x))))) -> forall (G : Count N -> U) (H1 : forall n : Count N, proj1_sig A (G n)), Bijective (Count N) {u : U | proj1_sig A u} (fun x : Count N => exist (proj1_sig A) (G x) (H1 x)) -> SumGF U CM N G F = MySumF2 U A CM F).
intros H1 U A CM F N G H2 H3.
cut (exists G1 : Count N -> U, (forall n0 : Count N, proj1_sig A (G1 n0)) /\ (forall H1 : forall n0 : Count N, proj1_sig A (G1 n0), Bijective (Count N) {u : U | proj1_sig A u} (fun x : Count N => exist (proj1_sig A) (G1 x) (H1 x)))).
intro H4.
apply (H1 U A CM F N H4 G H2 H3).
exists G.
apply conj.
apply H2.
intro H4.
cut ((fun x : Count N => exist (proj1_sig A) (G x) (H4 x)) = (fun x : Count N => exist (proj1_sig A) (G x) (H2 x))).
intro H5.
rewrite H5.
apply H3.
apply functional_extensionality.
intro n.
apply sig_map.
reflexivity.
intros U A CM F N H1.
cut (N = Counter U A).
intro H2.
rewrite H2.
intros G H3.
apply (MySumF2Nature U A CM F G H3).
cut (cardinal U (proj1_sig A) N).
intro H2.
cut (cardinal U (proj1_sig A) (Counter U A)).
intro H3.
apply (cardinal_is_functional U (proj1_sig A) N H2 (proj1_sig A) (Counter U A) H3).
reflexivity.
apply (proj2_sig (NumWellDefined U (proj1_sig A) (proj2_sig A))).
elim H1.
intros G H2.
apply (ExistBijectiveFunctionCount U N (proj1_sig A)).
exists ((fun x : Count N => exist (proj1_sig A) (G x) (proj1 H2 x))).
apply (proj2 H2 (proj1 H2)).
Qed.

Lemma CM_comm_assoc : forall (CM : CommutativeMonoid) (x y z w : CMT CM), CMc CM (CMc CM x y) (CMc CM z w) = CMc CM (CMc CM x z) (CMc CM y w).
Proof.
intros CM x y z w.
rewrite (CM_assoc CM x y (CMc CM z w)).
rewrite<- (CM_assoc CM y z w).
rewrite (CM_comm CM y z).
rewrite (CM_assoc CM z y w).
rewrite<- (CM_assoc CM x z (CMc CM y w)).
reflexivity.
Qed.

Definition FiniteUnion (U : Type) (A B : {X : Ensemble U | Finite U X}) := (exist (Finite U) (Union U (proj1_sig A) (proj1_sig B)) (Union_preserves_Finite U (proj1_sig A) (proj1_sig B) (proj2_sig A) (proj2_sig B))).

Lemma MySumF2Union : forall (U : Type) (CM : CommutativeMonoid) (F : U -> CMT CM) (A : {X : Ensemble U | Finite U X}) (B : {X : Ensemble U | Finite U X}), (forall (u : U), In U (proj1_sig B) u -> ~ In U (proj1_sig A) u) -> (MySumF2 U (FiniteUnion U A B) CM F) = (CMc CM (MySumF2 U A CM F) (MySumF2 U B CM F)).
Proof.
cut (forall (U : Type) (CM : CommutativeMonoid) (F : U -> CMT CM) (N : nat) (A : {X : Ensemble U | Finite U X}) (B : {X : Ensemble U | Finite U X}), (forall (u : U), In U (proj1_sig B) u -> ~ In U (proj1_sig A) u) -> (cardinal U (proj1_sig B) N) -> (MySumF2 U (exist (Finite U) (Union U (proj1_sig A) (proj1_sig B)) (Union_preserves_Finite U (proj1_sig A) (proj1_sig B) (proj2_sig A) (proj2_sig B))) CM F) = (CMc CM (MySumF2 U A CM F) (MySumF2 U B CM F))).
intros H1 U CM F A B H2.
elim (finite_cardinal U (proj1_sig B) (proj2_sig B)).
intros N H3.
apply (H1 U CM F N A B H2 H3).
intros U CM F N.
elim N.
intros A B H1 H2.
cut (proj1_sig B = Empty_set U).
intro H3.
cut ((exist (Finite U) (Union U (proj1_sig A) (proj1_sig B)) (Union_preserves_Finite U (proj1_sig A) (proj1_sig B) (proj2_sig A) (proj2_sig B))) = A).
intro H4.
cut (MySumF2 U B CM F = CMe CM).
intro H5.
rewrite H4.
rewrite H5.
rewrite (CM_O_r CM (MySumF2 U A CM F)).
reflexivity.
cut (Finite U (Empty_set U)).
intro H5.
cut (B = exist (Finite U) (Empty_set U) H5).
intro H6.
rewrite H6.
cut (forall (u : Count 0), (Empty_set nat) (proj1_sig u)).
intro H7.
cut (let G : ((Count 0) -> U) := (fun (n : Count 0) => match (H7 n) with
end) in MySumF2 U (exist (Finite U) (Empty_set U) H5) CM F = CMe CM).
intro H8.
apply H8.
intro G.
cut (forall (n : Count 0), proj1_sig (exist (Finite U) (Empty_set U) H5) (G n)).
intro H9.
rewrite<- (MySumF2Nature2 U (exist (Finite U) (Empty_set U) H5) CM F 0 G H9).
unfold SumGF.
unfold SumGFSub.
reflexivity.
simpl.
exists (fun (u : {u : U | Empty_set U u}) => match (proj2_sig u) with
end).
apply conj.
intro n.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig n)).
apply (proj2_sig n).
intro y.
elim (proj2_sig y).
intro n.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig n)).
apply (proj2_sig n).
intro n.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig n)).
apply (proj2_sig n).
apply sig_map.
apply H3.
apply Empty_is_finite.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
intros u H4.
elim H4.
intros uu H5.
apply H5.
intros uu.
rewrite H3.
intro H5.
elim H5.
intros u H4.
left.
apply H4.
apply (cardinal_elim U (proj1_sig B) 0 H2).
cut (forall (A : {X : Ensemble U | Finite U X}) (u : U), (~ In U (proj1_sig A) u) -> (MySumF2 U (exist (Finite U) (Add U (proj1_sig A) u) (Add_preserves_Finite U (proj1_sig A) u (proj2_sig A))) CM F) = (CMc CM (MySumF2 U A CM F) (F u))).
intros H1 n H2 A B H3 H4.
elim (cardinal_invert U (proj1_sig B) (S n) H4).
intros B0 H5.
elim H5.
intros b H6.
cut (Finite U B0).
intro H7.
cut ((Union U (proj1_sig A) (proj1_sig B)) = Add U (Union U (proj1_sig A) B0) b).
intro H8.
cut ((exist (Finite U) (Union U (proj1_sig A) (proj1_sig B)) (Union_preserves_Finite U (proj1_sig A) (proj1_sig B) (proj2_sig A) (proj2_sig B))) = (exist (Finite U) (Add U (Union U (proj1_sig A) B0) b) (Add_preserves_Finite U (Union U (proj1_sig A) B0) b (Union_preserves_Finite U (proj1_sig A) B0 (proj2_sig A) H7)))).
intro H9.
rewrite H9.
rewrite (H1 (exist (Finite U) (Union U (proj1_sig A) B0) (Union_preserves_Finite U (proj1_sig A) B0 (proj2_sig A) H7))).
cut ((MySumF2 U (exist (Finite U) (Union U (proj1_sig A) B0) (Union_preserves_Finite U (proj1_sig A) B0 (proj2_sig A) H7)) CM F) = MySumF2 U (@exist (Ensemble U) (Finite U) (Union U (@proj1_sig (Ensemble U) (fun X : Ensemble U => Finite U X) A) (@proj1_sig (Ensemble U) (fun X : Ensemble U => Finite U X) (@exist (Ensemble U) (Finite U) B0 H7))) (Union_preserves_Finite U (@proj1_sig (Ensemble U) (fun X : Ensemble U => Finite U X) A) (@proj1_sig (Ensemble U) (fun X : Ensemble U => Finite U X) (@exist (Ensemble U) (Finite U) B0 H7)) (@proj2_sig (Ensemble U) (fun X : Ensemble U => Finite U X) A) (@proj2_sig (Ensemble U) (fun X : Ensemble U => Finite U X) (@exist (Ensemble U) (Finite U) B0 H7)))) CM F).
intro H10.
rewrite H10.
rewrite (H2 A (exist (Finite U) B0 H7)).
cut (B = (exist (Finite U) (Add U B0 b) (Add_preserves_Finite U B0 b H7))).
intro H11.
rewrite H11.
cut (MySumF2 U (exist (Finite U) (Add U B0 b) (Add_preserves_Finite U B0 b H7)) CM F = MySumF2 U (@exist (Ensemble U) (Finite U) (Add U (@proj1_sig (Ensemble U) (fun X : Ensemble U => Finite U X) (@exist (Ensemble U) (Finite U) B0 H7)) b) (Add_preserves_Finite U (@proj1_sig (Ensemble U) (fun X : Ensemble U => Finite U X) (@exist (Ensemble U) (Finite U) B0 H7)) b (@proj2_sig (Ensemble U) (fun X : Ensemble U => Finite U X) (@exist (Ensemble U) (Finite U) B0 H7)))) CM F).
intro H12.
rewrite H12.
rewrite (H1 (exist (Finite U) B0 H7) b).
apply (CM_assoc CM (MySumF2 U A CM F) (MySumF2 U (exist (Finite U) B0 H7) CM F) (F b)).
apply (proj1 (proj2 H6)).
simpl.
reflexivity.
apply sig_map.
apply (proj1 H6).
simpl.
intros u H11.
apply (H3 u).
rewrite (proj1 H6).
left.
apply H11.
simpl.
apply (proj2 (proj2 H6)).
simpl.
reflexivity.
simpl.
intro H10.
cut ((proj1_sig A b) \/ (B0 b)).
intro H11.
elim H11.
intro H12.
apply (H3 b).
rewrite (proj1 H6).
apply Union_intror.
apply In_singleton.
apply H12.
intro H12.
apply (proj1 (proj2 H6) H12).
elim H10.
intros u H11.
left.
apply H11.
intros u H11.
right.
apply H11.
apply sig_map.
simpl.
apply H8.
apply Extensionality_Ensembles.
apply conj.
intros u H8.
elim H8.
intros uu H9.
apply Union_introl.
apply Union_introl.
apply H9.
rewrite (proj1 H6).
intros uu H9.
elim H9.
intros uuu H10.
apply Union_introl.
apply Union_intror.
apply H10.
intros uuu H10.
apply Union_intror.
apply H10.
intros u H8.
elim H8.
intros uu H9.
elim H9.
intros uuu H10.
apply Union_introl.
apply H10.
intros uuu H10.
apply Union_intror.
rewrite (proj1 H6).
apply Union_introl.
apply H10.
intros uu H9.
apply Union_intror.
rewrite (proj1 H6).
apply Union_intror.
apply H9.
apply (cardinal_finite U B0 n (proj2 (proj2 H6))).
intros A u H1.
elim (CountExistBijectiveFunction U (Counter U A) (proj1_sig A)).
intros G H2.
cut (forall (n : (Count (Counter U A))), (proj1_sig A (proj1_sig (G n)))).
intro H3.
rewrite<- (MySumF2Nature U A CM F (fun (n : (Count (Counter U A))) => (proj1_sig (G n))) H3).
cut (let G2 := (fun (n : (Count (S (Counter U A)))) => match excluded_middle_informative (proj1_sig n < Counter U A) with
  | left a => proj1_sig (G (exist (fun (n1 : nat) => n1 < (Counter U A)) (proj1_sig n) a))
  | right _ => u
end) in MySumF2 U (exist (Finite U) (Add U (proj1_sig A) u) (Add_preserves_Finite U (proj1_sig A) u (proj2_sig A))) CM F = CMc CM (SumGF U CM (Counter U A) (fun n : Count (Counter U A) => proj1_sig (G n)) F) (F u)).
intro H4.
apply H4.
intro G2.
cut (forall (n : (Count (S (Counter U A)))), ((Add U (proj1_sig A) u) (G2 n))).
intro H4.
rewrite<- (MySumF2Nature2 U (exist (Finite U) (Add U (proj1_sig A) u) (Add_preserves_Finite U (proj1_sig A) u (proj2_sig A))) CM F (S (Counter U A)) G2 H4).
unfold SumGF.
simpl.
cut ((SumGFSub U CM (S (Counter U A)) G2 F (Counter U A)) = (SumGFSub U CM (Counter U A) (fun n : Count (Counter U A) => proj1_sig (G n)) F (Counter U A))).
intro H5.
rewrite H5.
cut ((UnwrapGF U CM (S (Counter U A)) G2 F (Counter U A)) = (F u)).
intro H6.
rewrite H6.
reflexivity.
unfold UnwrapGF.
elim (excluded_middle_informative (Counter U A < S (Counter U A))).
intros H6.
unfold G2.
elim (excluded_middle_informative (proj1_sig (exist (fun n0 : nat => n0 < S (Counter U A)) (Counter U A) H6) < Counter U A)).
intros H7.
apply False_ind.
apply (PeanoNat.Nat.lt_irrefl (Counter U A)).
apply H7.
intro H7.
reflexivity.
intro H6.
apply False_ind.
apply H6.
apply (le_n (S (Counter U A))).
cut (forall (n : nat), (n <= (Counter U A)) -> SumGFSub U CM (S (Counter U A)) G2 F n = SumGFSub U CM (Counter U A) (fun n : Count (Counter U A) => proj1_sig (G n)) F n).
intro H5.
apply (H5 (Counter U A)).
apply (le_n (Counter U A)).
intro n.
elim n.
simpl.
reflexivity.
intros n0 H5 H6.
simpl.
rewrite H5.
cut ((UnwrapGF U CM (S (Counter U A)) G2 F n0) = (UnwrapGF U CM (Counter U A) (fun n1 : Count (Counter U A) => proj1_sig (G n1)) F n0)).
intro H7.
rewrite H7.
reflexivity.
unfold UnwrapGF.
elim (excluded_middle_informative (n0 < S (Counter U A))).
intro H7.
elim (excluded_middle_informative (n0 < Counter U A)).
intro H8.
unfold G2.
elim (excluded_middle_informative (proj1_sig (exist (fun n1 : nat => n1 < S (Counter U A)) n0 H7) < Counter U A)).
intro H9.
cut ((exist (fun n1 : nat => n1 < Counter U A) (proj1_sig (exist (fun n1 : nat => n1 < S (Counter U A)) n0 H7)) H9) = (exist (fun n1 : nat => n1 < Counter U A) n0 H8)).
intro H10.
rewrite H10.
reflexivity.
apply sig_map.
reflexivity.
intro H9.
apply False_ind.
apply H9.
simpl.
apply H8.
simpl.
intro H8.
apply False_ind.
apply (H8 H6).
intro H7.
apply False_ind.
apply H7.
apply (le_S (S n0) (Counter U A)).
apply H6.
apply (le_S_n n0 (Counter U A)).
apply (le_S (S n0) (Counter U A)).
apply H6.
simpl.
elim H2.
intros GI H5.
cut (forall (n : Count (Counter U A)), proj1_sig n < (S (Counter U A))).
intro H6.
exists (fun (u1 : {u0 : U | Add U (proj1_sig A) u u0}) => match excluded_middle_informative (proj1_sig A (proj1_sig u1)) with
  | left a => exist (fun (n : nat) => n < (S (Counter U A))) (proj1_sig (GI (exist (proj1_sig A) (proj1_sig u1) a))) (H6 (GI (exist (proj1_sig A) (proj1_sig u1) a)))
  | right _ => exist (fun (n : nat) => n < (S (Counter U A))) (Counter U A) (le_n (S (Counter U A)))
end).
apply conj.
intro n.
elim (excluded_middle_informative (@proj1_sig (Ensemble U) (fun X : Ensemble U => Finite U X) A (@proj1_sig U (fun u0 : U => Add U (@proj1_sig (Ensemble U) (fun X : Ensemble U => Finite U X) A) u u0) (@exist U (Add U (@proj1_sig (Ensemble U) (fun X : Ensemble U => Finite U X) A) u) (G2 n) (H4 n))))).
intro H7.
apply sig_map.
simpl.
elim (excluded_middle_informative (proj1_sig n < Counter U A)).
intro H8.
cut ((exist (proj1_sig A) (G2 n) H7) = G (exist (fun (n0 : nat) => n0 < (Counter U A)) (proj1_sig n) H8)).
intro H9.
rewrite H9.
rewrite (proj1 H5 (exist (fun n0 : nat => n0 < Counter U A) (proj1_sig n) H8)).
reflexivity.
apply sig_map.
simpl.
unfold G2.
elim (excluded_middle_informative (proj1_sig n < Counter U A)).
intro H9.
cut ((exist (fun n1 : nat => n1 < Counter U A) (proj1_sig n) H9) = (exist (fun n0 : nat => n0 < Counter U A) (proj1_sig n) H8)).
intro H10.
rewrite H10.
reflexivity.
apply sig_map.
reflexivity.
intro H9.
apply False_ind.
apply (H9 H8).
intro H8.
apply False_ind.
apply H1.
cut (G2 n = u).
intro H9.
rewrite<- H9.
apply H7.
unfold G2.
elim (excluded_middle_informative (proj1_sig n < Counter U A)).
intro H9.
apply False_ind.
apply (H8 H9).
intro H9.
reflexivity.
simpl.
intro H7.
apply sig_map.
simpl.
cut (G2 n = u).
unfold G2.
elim (excluded_middle_informative (proj1_sig n < Counter U A)).
intros H8 H9.
apply False_ind.
apply H1.
rewrite<- H9.
apply (proj2_sig (G (exist (fun n1 : nat => n1 < Counter U A) (proj1_sig n) H8))).
intros H8 H9.
elim (le_lt_or_eq (S (proj1_sig n)) (S (Counter U A))).
intro H10.
apply False_ind.
apply H8.
apply (lt_S_n (proj1_sig n) (Counter U A)).
apply H10.
intro H10.
rewrite (PeanoNat.Nat.succ_inj (proj1_sig n) (Counter U A) H10).
reflexivity.
apply (proj2_sig n).
cut (~ proj1_sig A (G2 n)).
unfold G2.
elim (excluded_middle_informative (proj1_sig n < Counter U A)).
intros H8 H9.
apply False_ind.
apply (H9 (proj2_sig (G (exist (fun n1 : nat => n1 < Counter U A) (proj1_sig n) H8)))).
intros H8 H9.
reflexivity.
apply H7.
intro y.
apply sig_map.
simpl.
elim (excluded_middle_informative (proj1_sig A (proj1_sig y))).
intro H7.
unfold G2.
elim (excluded_middle_informative (proj1_sig (exist (fun n : nat => n < S (Counter U A)) (proj1_sig (GI (exist (proj1_sig A) (proj1_sig y) H7))) (H6 (GI (exist (proj1_sig A) (proj1_sig y) H7)))) < Counter U A)).
intro H8.
simpl.
cut ((exist (fun n1 : nat => n1 < Counter U A) (proj1_sig (GI (exist (proj1_sig A) (proj1_sig y) H7))) H8) = (GI (exist (proj1_sig A) (proj1_sig y) H7))).
intro H9.
rewrite H9.
rewrite (proj2 H5 (exist (proj1_sig A) (proj1_sig y) H7)).
reflexivity.
apply sig_map.
reflexivity.
simpl.
intro H8.
apply False_ind.
apply (H8 (proj2_sig (GI (exist (proj1_sig A) (proj1_sig y) H7)))).
intro H7.
unfold G2.
elim (excluded_middle_informative (proj1_sig (exist (fun n : nat => n < S (Counter U A)) (Counter U A) (le_n (S (Counter U A)))) < Counter U A)).
simpl.
intro H8.
apply False_ind.
apply (PeanoNat.Nat.lt_irrefl (Counter U A)).
apply H8.
intro H8.
cut (forall (u1 : U), (Add U (proj1_sig A) u u1) -> (proj1_sig A u1) \/ (Singleton U u u1)).
intro H9.
elim (H9 (proj1_sig y) (proj2_sig y)).
intro H10.
apply False_ind.
apply (H7 H10).
intro H10.
rewrite<- H10.
reflexivity.
intros uu H9.
elim H9.
intros uuu H10.
left.
apply H10.
intros uuu H10.
right.
apply H10.
intro n.
apply (le_S (S (proj1_sig n)) (Counter U A)).
apply (proj2_sig n).
intro n.
unfold G2.
elim (excluded_middle_informative (proj1_sig n < Counter U A)).
intro H4.
left.
apply (proj2_sig (G (exist (fun n1 : nat => n1 < Counter U A) (proj1_sig n) H4))).
intro H4.
right.
reflexivity.
cut ((fun x : Count (Counter U A) => exist (proj1_sig A) (proj1_sig (G x)) (H3 x)) = G).
intro H4.
rewrite H4.
apply H2.
apply functional_extensionality.
intro u1.
apply sig_map.
reflexivity.
intro n.
apply (proj2_sig (G n)).
apply (proj2_sig (NumWellDefined U (proj1_sig A) (proj2_sig A))).
Qed.

Definition FiniteIntersection (U : Type) (A : {X : Ensemble U | Finite U X}) (B : Ensemble U) := (exist (Finite U) (Intersection U B (proj1_sig A)) (Intersection_preserves_finite U (proj1_sig A) (proj2_sig A) B)).

Lemma MySumF2Excluded : forall (U : Type) (CM : CommutativeMonoid) (F : U -> CMT CM) (A : {X : Ensemble U | Finite U X}) (B : Ensemble U), (MySumF2 U A CM F) = (CMc CM (MySumF2 U (FiniteIntersection U A B) CM F) (MySumF2 U (FiniteIntersection U A (Ensembles.Complement U B)) CM F)).
Proof.
intros U CM F A B.
rewrite<- (MySumF2Union U CM F (FiniteIntersection U A B) (FiniteIntersection U A (Ensembles.Complement U B))).
cut (A = (FiniteUnion U (FiniteIntersection U A B) (FiniteIntersection U A (Ensembles.Complement U B)))).
intro H1.
rewrite<- H1.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
intros a H1.
elim (classic (B a)).
intro H2.
left.
apply Intersection_intro.
apply H2.
apply H1.
intro H2.
right.
apply Intersection_intro.
apply H2.
apply H1.
intros u H1.
elim H1.
intros uu H2.
elim H2.
intros uuu H3 H4.
apply H4.
intros uu H2.
elim H2.
intros uuu H3 H4.
apply H4.
simpl.
intros u H1 H2.
cut (Ensembles.Complement U B u).
intro H3.
apply H3.
elim H2.
intros uu H4 H5.
apply H4.
elim H1.
intros uu H3 H4.
apply H3.
Qed.

Definition FiniteSingleton (U : Type) (u : U) := (exist (Finite U) (Singleton U u) (Singleton_is_finite U u)).

Lemma MySumF2Singleton : forall (U : Type) (CM : CommutativeMonoid) (F : U -> CMT CM) (u : U), (MySumF2 U (FiniteSingleton U u) CM F) = (F u).
Proof.
intros U CM F u.
cut (forall (n : Count 1), proj1_sig (FiniteSingleton U u) ((fun (n1 : Count 1) => u) n)).
intro H1.
rewrite<- (MySumF2Nature2 U (FiniteSingleton U u) CM F 1 (fun (n1 : Count 1) => u) H1).
unfold SumGF.
unfold SumGFSub.
unfold UnwrapGF.
elim (excluded_middle_informative (0 < 1)).
intro H2.
rewrite (CM_comm CM (CMe CM) (F u)).
apply (CM_O_r CM (F u)).
intro H2.
apply False_ind.
apply H2.
apply (le_n 1).
simpl.
exists (fun (u : {u0 : U | Singleton U u u0}) => (exist (fun (n : nat) => n < 1) 0 (le_n 1))).
apply conj.
intro x.
apply sig_map.
simpl.
apply (Le.le_n_0_eq (proj1_sig x)).
apply (le_S_n (proj1_sig x) 0).
apply (proj2_sig x).
intro y.
apply sig_map.
simpl.
rewrite<- (proj2_sig y).
reflexivity.
intro n.
simpl.
apply (In_singleton U u).
Qed.

Definition FiniteEmpty (U : Type) := (exist (Finite U) (Empty_set U) (Empty_is_finite U)).

Lemma MySumF2Empty : forall (U : Type) (CM : CommutativeMonoid) (F : U -> CMT CM), (MySumF2 U (FiniteEmpty U) CM F) = (CMe CM).
Proof.
intros U CM F.
cut (forall (n : Count 0), False).
intro H1.
cut (forall (n1 : Count 0), (proj1_sig (exist (Finite U) (Empty_set U) (Empty_is_finite U))) ((fun (n : Count 0) => match (H1 n) with
end) n1)).
intro H2.
rewrite<- (MySumF2Nature2 U (FiniteEmpty U) CM F 0 (fun (n : Count 0) => match (H1 n) with
end) H2).
unfold SumGF.
simpl.
reflexivity.
simpl.
exists (fun (u : {u : U | Empty_set U u}) => match (proj2_sig u) with
end).
apply conj.
intro n.
apply False_ind.
apply (H1 n).
intro y.
elim (proj2_sig y).
intro n.
apply False_ind.
apply (H1 n).
intro n.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig n) (proj2_sig n)).
Qed.

Definition FiniteAdd (U : Type) (A : {X : Ensemble U | Finite U X}) (a : U) := (exist (Finite U) (Add U (proj1_sig A) a) (Add_preserves_Finite U (proj1_sig A) a (proj2_sig A))).

Lemma MySumF2Add : forall (U : Type) (CM : CommutativeMonoid) (F : U -> CMT CM) (A : {X : Ensemble U | Finite U X}) (a : U), ~ In U (proj1_sig A) a -> (MySumF2 U (FiniteAdd U A a) CM F) = (CMc CM (MySumF2 U A CM F) (F a)).
Proof.
intros U CM F A a H1.
cut ((FiniteAdd U A a) = (FiniteUnion U A (FiniteSingleton U a))).
intro H2.
rewrite H2.
rewrite (MySumF2Union U CM F A (FiniteSingleton U a)).
rewrite (MySumF2Singleton U CM F a).
reflexivity.
intros u H3.
rewrite<- H3.
apply H1.
apply sig_map.
simpl.
reflexivity.
Qed.

Lemma FiniteSetInduction : forall (U : Type) (A : {X : Ensemble U | Finite U X}) (P : {X : Ensemble U | Finite U X} -> Prop), ((P (FiniteEmpty U)) /\ (forall (B : {X : Ensemble U | Finite U X}) (b : U), (Included U (proj1_sig B) (proj1_sig A)) -> (In U (proj1_sig A) b) -> (~ In U (proj1_sig B) b) -> (P B) -> (P (FiniteAdd U B b)))) -> (P A).
Proof.
intros U A P H1.
cut (forall (N : nat) (B : {X : Ensemble U | Finite U X}), (Included U (proj1_sig B) (proj1_sig A)) -> (cardinal U (proj1_sig B) N) -> (P B)).
intro H2.
elim (finite_cardinal U (proj1_sig A) (proj2_sig A)).
intros n H3.
apply (H2 n A).
intros u H4.
apply H4.
apply H3.
intro N.
elim N.
intros B H2 H3.
cut (B = (exist (Finite U) (Empty_set U) (Empty_is_finite U))).
intro H4.
rewrite H4.
apply (proj1 H1).
apply sig_map.
simpl.
elim (cardinal_elim U (proj1_sig B) 0 H3).
reflexivity.
intros n H2.
intros B H3 H4.
elim (cardinal_invert U (proj1_sig B) (S n)).
intros B0 H5.
elim H5.
intros b H6.
cut (Finite U B0).
intro H7.
cut (B = (exist (Finite U) (Add U (proj1_sig (exist (Finite U) B0 H7)) b) (Add_preserves_Finite U (proj1_sig (exist (Finite U) B0 H7)) b (proj2_sig (exist (Finite U) B0 H7))))).
intro H8.
rewrite H8.
apply (proj2 H1 (exist (Finite U) B0 H7) b).
simpl.
intros u H9.
cut (proj1_sig B u).
apply (H3 u).
rewrite (proj1 H6).
left.
apply H9.
cut (proj1_sig B b).
apply (H3 b).
rewrite (proj1 H6).
right.
reflexivity.
simpl.
apply (proj1 (proj2 H6)).
apply (H2 (exist (Finite U) B0 H7)).
simpl.
intros u H9.
apply (H3 u).
rewrite (proj1 H6).
left.
apply H9.
apply (proj2 (proj2 H6)).
apply sig_map.
apply (proj1 H6).
apply (cardinal_finite U B0 n (proj2 (proj2 H6))).
apply H4.
Qed.

Lemma MySumF2Induction : forall (U : Type) (A : {X : Ensemble U | Finite U X}) (CM : CommutativeMonoid) (F : U -> CMT CM) (P : (CMT CM) -> Prop), ((P (CMe CM)) /\ (forall (cm : CMT CM) (u : U), (In U (proj1_sig A) u) -> (P cm) -> (P (CMc CM cm (F u))))) -> (P (MySumF2 U A CM F)).
Proof.
intros U A CM F P H1.
apply (FiniteSetInduction U A).
apply conj.
rewrite (MySumF2Empty U CM F).
apply (proj1 H1).
intros B b H2 H3 H4 H5.
rewrite (MySumF2Add U CM F B b).
apply (proj2 H1 (MySumF2 U B CM F) b H3 H5).
apply H4.
Qed.

Lemma MySumF2BijectiveSame : forall (U1 : Type) (A1 : {X : Ensemble U1 | Finite U1 X}) (U2 : Type) (A2 : {X : Ensemble U2 | Finite U2 X}) (CM : CommutativeMonoid) (F : U2 -> CMT CM) (G : U1 -> U2) (H : forall (u : U1), (proj1_sig A1 u) -> (proj1_sig A2 (G u))), (Bijective {u : U1 | proj1_sig A1 u} {u : U2 | proj1_sig A2 u} (fun (u : {u : U1 | proj1_sig A1 u}) => (exist (proj1_sig A2) (G (proj1_sig u)) (H (proj1_sig u) (proj2_sig u))))) -> (MySumF2 U1 A1 CM (fun (u : U1) => F (G u))) = (MySumF2 U2 A2 CM F).
Proof.
intros U1 A1 U2 A2 CM F L H1 H2.
elim (CountExistBijectiveFunction U1 (Counter U1 A1) (proj1_sig A1) (proj2_sig (NumWellDefined U1 (proj1_sig A1) (proj2_sig A1)))).
intros G H3.
rewrite<- (MySumF2Nature U1 A1 CM (fun u : U1 => F (L u)) (fun (n : Count (Counter U1 A1)) => proj1_sig (G n)) (fun (n : Count (Counter U1 A1)) => proj2_sig (G n))).
rewrite<- (MySumF2Nature2 U2 A2 CM F (Counter U1 A1) (fun (n : Count (Counter U1 A1)) => L (proj1_sig (G n))) (fun (n : Count (Counter U1 A1)) => H1 (proj1_sig (G n)) (proj2_sig (G n)))).
unfold SumGF.
cut (forall (N : nat), SumGFSub U1 CM (Counter U1 A1) (fun n : Count (Counter U1 A1) => proj1_sig (G n)) (fun u : U1 => F (L u)) N = SumGFSub U2 CM (Counter U1 A1) (fun n : Count (Counter U1 A1) => L (proj1_sig (G n))) F N).
intro H4.
apply (H4 (Counter U1 A1)).
intro N.
elim N.
simpl.
reflexivity.
intros n H4.
simpl.
rewrite H4.
unfold UnwrapGF.
elim (excluded_middle_informative (n < Counter U1 A1)).
intro H5.
reflexivity.
intro H5.
reflexivity.
elim H2.
intros LI H4.
elim H3.
intros GI H5.
exists (fun (u : {u : U2 | proj1_sig A2 u}) => (GI (LI u))).
apply conj.
intro n.
rewrite (proj1 H4 (G n)).
apply (proj1 H5 n).
intro y.
rewrite (proj2 H5 (LI y)).
apply (proj2 H4 y).
cut ((fun x : Count (Counter U1 A1) => exist (proj1_sig A1) (proj1_sig (G x)) (proj2_sig (G x))) = G).
intro H4.
rewrite H4.
apply H3.
apply functional_extensionality.
intro n.
apply sig_map.
reflexivity.
Qed.

Definition FiniteIm (U1 U2 : Type) (F : U1 -> U2) (A : {X : Ensemble U1 | Finite U1 X}):= (exist (Finite U2) (Im U1 U2 (proj1_sig A) F) (finite_image U1 U2 (proj1_sig A) F (proj2_sig A))).

Lemma MySumF2BijectiveSame2 : forall (U1 U2 : Type) (A : {X : Ensemble U1 | Finite U1 X}) (G : U1 -> U2) (CM : CommutativeMonoid) (F : U2 -> CMT CM), (forall (u1 u2 : U1), In U1 (proj1_sig A) u1 -> In U1 (proj1_sig A) u2 -> G u1 = G u2 -> u1 = u2) -> (MySumF2 U1 A CM (compose F G)) = (MySumF2 U2 (FiniteIm U1 U2 G A) CM F).
Proof.
intros U1 U2 A G CM F H1.
cut (forall (u : U1), proj1_sig A u -> (Im U1 U2 (proj1_sig A) G) (G u)).
intro H2.
apply (MySumF2BijectiveSame U1 A U2 (FiniteIm U1 U2 G A) CM F G H2).
cut (forall (u2 : U2), In U2 (Im U1 U2 (proj1_sig A) G) u2 -> {u1 : U1 | In U1 (proj1_sig A) u1 /\ G u1 = u2}).
intro H3.
exists (fun (x : {u : U2 | proj1_sig (FiniteIm U1 U2 G A) u}) => exist (proj1_sig A) (proj1_sig (H3 (proj1_sig x) (proj2_sig x))) (proj1 (proj2_sig (H3 (proj1_sig x) (proj2_sig x))))).
apply conj.
intro x.
apply sig_map.
apply (H1 (proj1_sig (H3 (G (proj1_sig x)) (H2 (proj1_sig x) (proj2_sig x)))) (proj1_sig x)).
apply (proj1 (proj2_sig (H3 (G (proj1_sig x)) (H2 (proj1_sig x) (proj2_sig x))))).
apply (proj2_sig x).
apply (proj2 (proj2_sig (H3 (G (proj1_sig x)) (H2 (proj1_sig x) (proj2_sig x))))).
intro y.
apply sig_map.
apply (proj2 (proj2_sig (H3 (proj1_sig y) (proj2_sig y)))).
intros u2 H3.
apply constructive_definite_description.
apply (proj1 (unique_existence (fun (x : U1) => In U1 (proj1_sig A) x /\ G x = u2))).
apply conj.
elim H3.
intros x H4 y H5.
exists x.
apply conj.
apply H4.
rewrite H5.
reflexivity.
intros x1 x2 H4 H5.
apply (H1 x1 x2 (proj1 H4) (proj1 H5)).
rewrite (proj2 H5).
apply (proj2 H4).
intros u H2.
apply (Im_intro U1 U2 (proj1_sig A) G u H2 (G u)).
reflexivity.
Qed.

Lemma MySumF2ImageSum : forall (U1 U2 : Type) (A : {X : Ensemble U1 | Finite U1 X}) (CM : CommutativeMonoid) (F : U1 -> CMT CM) (G : U1 -> U2), (MySumF2 U1 A CM F) = (MySumF2 U2 (FiniteIm U1 U2 G A) CM (fun (u2 : U2) => MySumF2 U1 (FiniteIntersection U1 A (fun (u1 : U1) => G u1 = u2)) CM F)).
Proof.
intros U1 U2 A CM F G.
cut (A = (exist (Finite U1) (Intersection U1 (fun (u1 : U1) => proj1_sig (exist (Finite U2) (Im U1 U2 (proj1_sig A) G) (finite_image U1 U2 (proj1_sig A) G (proj2_sig A))) (G u1)) (proj1_sig A)) (Intersection_preserves_finite U1 (proj1_sig A) (proj2_sig A) (fun (u1 : U1) => proj1_sig (exist (Finite U2) (Im U1 U2 (proj1_sig A) G) (finite_image U1 U2 (proj1_sig A) G (proj2_sig A))) (G u1))))).
intro H1.
cut (MySumF2 U1 A CM F = MySumF2 U1 (exist (Finite U1) (Intersection U1 (fun (u1 : U1) => proj1_sig (exist (Finite U2) (Im U1 U2 (proj1_sig A) G) (finite_image U1 U2 (proj1_sig A) G (proj2_sig A))) (G u1)) (proj1_sig A)) (Intersection_preserves_finite U1 (proj1_sig A) (proj2_sig A) (fun (u1 : U1) => proj1_sig (exist (Finite U2) (Im U1 U2 (proj1_sig A) G) (finite_image U1 U2 (proj1_sig A) G (proj2_sig A))) (G u1)))) CM F).
intro H2.
rewrite H2.
apply (FiniteSetInduction U2 (exist (Finite U2) (Im U1 U2 (proj1_sig A) G) (finite_image U1 U2 (proj1_sig A) G (proj2_sig A))) (fun (B : {X : Ensemble U2 | Finite U2 X}) => MySumF2 U1 (exist (Finite U1) (Intersection U1 (fun u1 : U1 => proj1_sig B (G u1)) (proj1_sig A)) (Intersection_preserves_finite U1 (proj1_sig A) (proj2_sig A) (fun u1 : U1 => proj1_sig B (G u1)))) CM F = MySumF2 U2 B CM (fun u2 : U2 => MySumF2 U1 (exist (Finite U1) (Intersection U1 (fun u1 : U1 => G u1 = u2) (proj1_sig A)) (Intersection_preserves_finite U1 (proj1_sig A) (proj2_sig A) (fun u1 : U1 => G u1 = u2))) CM F))).
apply conj.
cut ((@exist (Ensemble U1) (Finite U1) (Intersection U1 (fun u1 : U1 => @proj1_sig (Ensemble U2) (fun X : Ensemble U2 => Finite U2 X) (FiniteEmpty U2) (G u1)) (@proj1_sig (Ensemble U1) (fun X : Ensemble U1 => Finite U1 X) A)) (Intersection_preserves_finite U1 (@proj1_sig (Ensemble U1) (fun X : Ensemble U1 => Finite U1 X) A) (@proj2_sig (Ensemble U1) (fun X : Ensemble U1 => Finite U1 X) A) (fun u1 : U1 => @proj1_sig (Ensemble U2) (fun X : Ensemble U2 => Finite U2 X) (FiniteEmpty U2) (G u1)))) = (FiniteEmpty U1)).
intro H3.
rewrite H3.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
intros u1 H3.
elim H3.
intros uu1 H4 H5.
elim H4.
intros u1 H3.
elim H3.
intros B b H3 H4 H5 H6.
simpl.
rewrite MySumF2Add.
cut ((exist (Finite U1) (Intersection U1 (fun u1 : U1 => Add U2 (proj1_sig B) b (G u1)) (proj1_sig A)) (Intersection_preserves_finite U1 (proj1_sig A) (proj2_sig A) (fun u1 : U1 => Add U2 (proj1_sig B) b (G u1)))) = FiniteUnion U1 (exist (Finite U1) (Intersection U1 (fun u1 : U1 => (proj1_sig B) (G u1)) (proj1_sig A)) (Intersection_preserves_finite U1 (proj1_sig A) (proj2_sig A) (fun u1 : U1 => (proj1_sig B) (G u1)))) (exist (Finite U1) (Intersection U1 (fun u1 : U1 => (Singleton U2 b) (G u1)) (proj1_sig A)) (Intersection_preserves_finite U1 (proj1_sig A) (proj2_sig A) (fun u1 : U1 => (Singleton U2 b) (G u1))))).
intro H7.
rewrite H7.
rewrite MySumF2Union.
rewrite H6.
cut ((MySumF2 U1 (exist (Finite U1) (Intersection U1 (fun u1 : U1 => Singleton U2 b (G u1)) (proj1_sig A)) (Intersection_preserves_finite U1 (proj1_sig A) (proj2_sig A) (fun u1 : U1 => Singleton U2 b (G u1)))) CM F) = (MySumF2 U1 (exist (Finite U1) (Intersection U1 (fun u1 : U1 => G u1 = b) (proj1_sig A)) (Intersection_preserves_finite U1 (proj1_sig A) (proj2_sig A) (fun u1 : U1 => G u1 = b))) CM F)).
intro H8.
rewrite H8.
reflexivity.
cut ((exist (Finite U1) (Intersection U1 (fun u1 : U1 => Singleton U2 b (G u1)) (proj1_sig A)) (Intersection_preserves_finite U1 (proj1_sig A) (proj2_sig A) (fun u1 : U1 => Singleton U2 b (G u1)))) = (exist (Finite U1) (Intersection U1 (fun u1 : U1 => G u1 = b) (proj1_sig A)) (Intersection_preserves_finite U1 (proj1_sig A) (proj2_sig A) (fun u1 : U1 => G u1 = b)))).
intro H8.
rewrite H8.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
intros u1 H8.
apply Intersection_intro.
elim H8.
intros uu1 H9 H10.
rewrite H9.
reflexivity.
elim H8.
intros uu1 H9 H10.
apply H10.
intros u1 H8.
apply Intersection_intro.
elim H8.
intros uu1 H9 H10.
unfold In.
rewrite H9.
reflexivity.
elim H8.
intros uu1 H9 H10.
apply H10.
intro u1.
simpl.
unfold In.
intros H8 H9.
apply H5.
cut (b = (G u1)).
intro H10.
rewrite H10.
elim H9.
intros uu1 H11 H12.
apply H11.
elim H8.
intros uu1 H10 H11.
rewrite H10.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
intros u1 H7.
elim H7.
intro uu1.
unfold In.
intro H8.
cut (((proj1_sig B) (G uu1)) \/ ((Singleton U2 b) (G uu1))).
intro H9.
elim H9.
intros H10 H11.
left.
apply Intersection_intro.
apply H10.
apply H11.
intros H10 H11.
right.
apply Intersection_intro.
apply H10.
apply H11.
elim H8.
intros u2 H9.
left.
apply H9.
intros u2 H9.
right.
apply H9.
intros u1 H7.
elim H7.
intros uu1 H8.
elim H8.
intros uuu1 H9 H10.
apply Intersection_intro.
left.
apply H9.
apply H10.
intros uu1 H8.
elim H8.
intros uuu1 H9 H10.
apply Intersection_intro.
right.
apply H9.
apply H10.
apply H5.
rewrite<- H1.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
intros u1 H1.
apply Intersection_intro.
apply (Im_intro U1 U2 (proj1_sig A) G u1).
apply H1.
reflexivity.
apply H1.
intros u1 H1.
elim H1.
intros uu1 H2 H3.
apply H3.
Qed.

Lemma FinitePairFinite : forall (U V : Type) (u : Ensemble U) (v : Ensemble V), (Finite U u) -> (Finite V v) -> (Finite (U * V) (fun (uv : (U * V)) => (u (fst uv)) /\ (v (snd uv)))).
Proof.
cut (forall (n : nat) (U V : Type) (u : Ensemble U) (v : V) , cardinal U u n -> cardinal (U * V) (fun (uv : (U * V)) => (u (fst uv)) /\ ((Singleton V v) (snd uv))) n).
intros H1 U V u v H2 H3.
elim H3.
cut ((fun uv : U * V => u (fst uv) /\ Empty_set V (snd uv)) = Empty_set (U * V)).
intro H4.
rewrite H4.
apply Empty_is_finite.
apply Extensionality_Ensembles.
apply conj.
intros uv H4.
elim (proj2 H4).
intros uv H4.
elim H4.
intros A H4 H5 v0 H6.
cut ((fun uv : U * V => u (fst uv) /\ Add V A v0 (snd uv)) = Union (U * V) (fun uv : U * V => u (fst uv) /\ A (snd uv)) (fun uv : U * V => u (fst uv) /\ (Singleton V v0) (snd uv))).
intro H7.
rewrite H7.
apply Union_preserves_Finite.
apply H5.
elim (finite_cardinal U u H2).
intros n H8.
apply (cardinal_finite (U * V) (fun uv : U * V => u (fst uv) /\ Singleton V v0 (snd uv)) n).
apply (H1 n U V u v0 H8).
apply Extensionality_Ensembles.
apply conj.
intros uv H7.
cut (A (snd uv) \/ Singleton V v0 (snd uv)).
intro H8.
elim H8.
intro H9.
left.
apply conj.
apply H7.
apply H9.
intro H9.
right.
apply conj.
apply H7.
apply H9.
elim (proj2 H7).
intros uv1 H8.
left.
apply H8.
intros uv1 H8.
right.
apply H8.
intros uv H7.
elim H7.
intros uv1 H8.
apply conj.
apply H8.
left.
apply H8.
intros uv1 H8.
apply conj.
apply H8.
right.
apply H8.
intro n.
elim n.
intros U V u v H1.
rewrite (cardinal_invert U u 0 H1).
cut ((fun uv : U * V => Empty_set U (fst uv) /\ Singleton V v (snd uv)) = Empty_set (U * V)).
intro H2.
rewrite H2.
apply card_empty.
apply Extensionality_Ensembles.
apply conj.
intros uv H2.
elim (proj1 H2).
intros uv H2.
elim H2.
intros n0 H1 U V u v H2.
elim (cardinal_invert U u (S n0) H2).
intros uu H3.
elim H3.
intros u1 H4.
cut ((fun uv : U * V => u (fst uv) /\ Singleton V v (snd uv)) = Add (U * V) (fun uv : U * V => uu (fst uv) /\ Singleton V v (snd uv)) (u1 , v)).
intro H5.
rewrite H5.
apply card_add.
apply (H1 U V uu v (proj2 (proj2 H4))).
intro H6.
apply (proj1 (proj2 H4)).
apply (proj1 H6).
apply Extensionality_Ensembles.
apply conj.
intro uv.
rewrite (proj1 H4).
intro H5.
cut (uu (fst uv) \/ Singleton U u1 (fst uv)).
intro H6.
elim H6.
intro H7.
left.
apply conj.
apply H7.
apply H5.
intro H8.
right.
rewrite H8.
rewrite (proj2 H5).
rewrite<- surjective_pairing.
reflexivity.
elim (proj1 H5).
intros u2 H6.
left.
apply H6.
intros u2 H6.
right.
apply H6.
intros uv H5.
elim H5.
intros uv1 H6.
apply conj.
rewrite (proj1 H4).
left.
apply (proj1 H6).
apply (proj2 H6).
intros uv1 H6.
apply conj.
rewrite (proj1 H4).
right.
rewrite<- H6.
simpl.
reflexivity.
rewrite<- H6.
simpl.
reflexivity.
Qed.

Definition FinitePair (U V : Type) (A : {X : Ensemble U | Finite U X}) (B : {X : Ensemble V | Finite V X}) := (exist (Finite (U * V)) (fun (uv : (U * V)) => ((proj1_sig A) (fst uv)) /\ ((proj1_sig B) (snd uv))) (FinitePairFinite U V (proj1_sig A) (proj1_sig B) (proj2_sig A) (proj2_sig B))).

Lemma MySumF2Pair : forall (U V : Type) (A : {X : Ensemble U | Finite U X}) (B : {X : Ensemble V | Finite V X}) (CM : CommutativeMonoid) (F : U -> V -> CMT CM), (MySumF2 (U * V) (FinitePair U V A B) CM (fun (uv : U * V) => F (fst uv) (snd uv))) = (MySumF2 U A CM (fun (u : U) => MySumF2 V B CM (F u))).
Proof.
intros U V A B CM F.
rewrite (MySumF2ImageSum (U * V) U (FinitePair U V A B) CM (fun uv : U * V => F (fst uv) (snd uv)) fst).
cut (forall (u : U), proj1_sig A u -> (fun u2 : U => MySumF2 (U * V) (FiniteIntersection (U * V) (FinitePair U V A B) (fun u1 : U * V => fst u1 = u2)) CM (fun uv : U * V => F (fst uv) (snd uv))) u = (fun u : U => MySumF2 V B CM (F u)) u).
intro H1.
elim (classic (proj1_sig B = Empty_set V)).
intro H2.
cut (B = FiniteEmpty V).
intro H3.
rewrite H3.
cut ((fun u : U => MySumF2 V (FiniteEmpty V) CM (F u)) = (fun u : U => CMe CM)).
intro H4.
rewrite H4.
cut ((fun u2 : U => MySumF2 (U * V) (FiniteIntersection (U * V) (FinitePair U V A (FiniteEmpty V)) (fun u1 : U * V => fst u1 = u2)) CM (fun uv : U * V => F (fst uv) (snd uv))) = (fun u : U => CMe CM)).
intro H5.
rewrite H5.
cut (forall (C : {X : Ensemble U | Finite U X}), MySumF2 U C CM (fun _ : U => CMe CM) = CMe CM).
intro H6.
rewrite H6.
rewrite H6.
reflexivity.
intro C.
apply MySumF2Induction.
apply conj.
reflexivity.
intros cm u H6 H7.
rewrite CM_O_r.
apply H7.
apply functional_extensionality.
intro u.
cut ((FiniteIntersection (U * V) (FinitePair U V A (FiniteEmpty V)) (fun u1 : U * V => fst u1 = u)) = FiniteEmpty (U * V)).
intro H5.
rewrite H5.
apply MySumF2Empty.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
intros uv H5.
elim H5.
intros uv1 H6 H7.
elim (proj2 H7).
intros uv H5.
elim H5.
apply functional_extensionality.
intro u.
apply MySumF2Empty.
apply sig_map.
apply H2.
intro H2.
cut ((FiniteIm (U * V) U fst (FinitePair U V A B)) = A).
intro H3.
rewrite H3.
apply (FiniteSetInduction U A (fun (A0 : {X : Ensemble U | Finite U X}) => MySumF2 U A0 CM (fun u2 : U => MySumF2 (U * V) (FiniteIntersection (U * V) (FinitePair U V A B) (fun u1 : U * V => fst u1 = u2)) CM (fun uv : U * V => F (fst uv) (snd uv))) = MySumF2 U A0 CM (fun u : U => MySumF2 V B CM (F u)))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
intros B0 b H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H7.
rewrite (H1 b).
reflexivity.
apply H5.
apply H6.
apply H6.
apply sig_map.
simpl.
cut (exists (v : V), proj1_sig B v).
intro H3.
elim H3.
intros v H4.
apply Extensionality_Ensembles.
apply conj.
intros u H5.
elim H5.
intros uv H6 u0 H7.
rewrite H7.
apply H6.
intros u H5.
apply (Im_intro (U * V) U (fun uv : U * V => proj1_sig A (fst uv) /\ proj1_sig B (snd uv)) fst (u , v)).
apply conj.
apply H5.
apply H4.
reflexivity.
apply NNPP.
intro H3.
apply H2.
apply Extensionality_Ensembles.
apply conj.
intros v H4.
apply False_ind.
apply H3.
exists v.
apply H4.
intros v H4.
elim H4.
intros u H10.
apply (FiniteSetInduction V B).
apply conj.
cut ((FiniteIntersection (U * V) (FinitePair U V A (FiniteEmpty V)) (fun u1 : U * V => fst u1 = u)) = (FiniteEmpty (U * V))).
intro H1.
rewrite H1.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
intros uv H1.
elim H1.
intros uv1 H2 H3.
elim (proj2 H3).
intros uv H1.
elim H1.
intros B0 b H1 H2 H3 H4.
cut ((FiniteIntersection (U * V) (FinitePair U V A (FiniteAdd V B0 b)) (fun u1 : U * V => fst u1 = u)) = (FiniteAdd (U * V) (FiniteIntersection (U * V) (FinitePair U V A B0) (fun u1 : U * V => fst u1 = u)) (u , b))).
intro H5.
rewrite H5.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H4.
reflexivity.
apply H3.
unfold In.
simpl.
intro H6.
apply H3.
cut ((fun uv : U * V => proj1_sig A (fst uv) /\ proj1_sig B0 (snd uv)) (u, b)).
intro H7.
apply (proj2 H7).
elim H6.
intros uv H7 H8.
apply H8.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
intros uv H5.
elim H5.
intros uv1 H6 H7.
cut ((proj1_sig B0) (snd uv1) \/ (Singleton V b) (snd uv1)).
intro H8.
elim H8.
intro H9.
left.
apply Intersection_intro.
apply H6.
apply conj.
apply (proj1 H7).
apply H9.
intro H9.
right.
rewrite H9.
rewrite<- H6.
rewrite surjective_pairing.
reflexivity.
elim (proj2 H7).
intros v H8.
left.
apply H8.
intros v H8.
right.
apply H8.
intros uv H5.
apply Intersection_intro.
elim H5.
intros uv1 H6.
elim H6.
intros uv2 H7 H8.
apply H7.
intros uv1 H6.
rewrite<- H6.
reflexivity.
elim H5.
intros uv1 H6.
elim H6.
intros uv2 H7 H8.
apply conj.
apply (proj1 H8).
left.
apply (proj2 H8).
intros uv1 H6.
rewrite<- H6.
apply conj.
apply H10.
right.
reflexivity.
Qed.

Lemma MySumF2Same : forall (U : Type) (A : {X : Ensemble U | Finite U X}) (CM : CommutativeMonoid) (F1 F2 : U -> CMT CM), (forall (u : U), proj1_sig A u -> F1 u = F2 u) -> (MySumF2 U A CM F1) = (MySumF2 U A CM F2).
Proof.
intros U A CM F1 F2 H1.
apply (FiniteSetInduction U A).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
intros B b H2 H3 H4 H5.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H5.
rewrite (H1 b).
reflexivity.
apply H3.
apply H4.
apply H4.
Qed.

Lemma MySumF2O : forall (U : Type) (A : {X : Ensemble U | Finite U X}) (CM : CommutativeMonoid) (F : U -> CMT CM), (forall (u : U), proj1_sig A u -> F u = CMe CM) -> (MySumF2 U A CM F) = CMe CM.
Proof.
intros U A CM F H1.
apply (FiniteSetInduction U A).
apply conj.
rewrite MySumF2Empty.
reflexivity.
intros B b H2 H3 H4 H5.
rewrite MySumF2Add.
rewrite H5.
rewrite (H1 b).
apply (CM_O_r CM (CMe CM)).
apply H3.
apply H4.
Qed.

Lemma MySumF2Included : forall (U : Type) (A B : {X : Ensemble U | Finite U X}) (CM : CommutativeMonoid) (F : U -> CMT CM), (Included U (proj1_sig A) (proj1_sig B)) -> (MySumF2 U B CM F) = CMc CM (MySumF2 U A CM F) (MySumF2 U (FiniteIntersection U B (Ensembles.Complement U (proj1_sig A))) CM F).
Proof.
intros U A B CM F H1.
rewrite (MySumF2Excluded U CM F B (proj1_sig A)).
cut (FiniteIntersection U B (proj1_sig A) = A).
intro H2.
rewrite H2.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
intros u H2.
elim H2.
intros u0 H3 H4.
apply H3.
intros u H2.
apply (Intersection_intro U (proj1_sig A) (proj1_sig B) u H2 (H1 u H2)).
Qed.

Lemma CountFinite : forall (N : nat), Finite (Count N) (Full_set (Count N)).
Proof.
intro N.
apply EnsembleSetFinite.
elim N.
cut ((fun u : nat => (u < 0)%nat) = Empty_set nat).
intro H1.
rewrite H1.
apply Empty_is_finite.
apply Extensionality_Ensembles.
apply conj.
intros n H1.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r n H1).
intros n H1.
elim H1.
intros n H1.
cut ((fun u : nat => (u < S n)%nat) = Add nat (fun u : nat => (u < n)%nat) n).
intro H2.
rewrite H2.
apply (Union_is_finite nat (fun u : nat => (u < n)%nat) H1 n).
apply (lt_irrefl n).
apply Extensionality_Ensembles.
apply conj.
intros m H2.
elim (classic (m = n)).
intro H3.
right.
rewrite H3.
reflexivity.
intro H3.
left.
elim (le_lt_or_eq (S m) (S n) H2).
apply (lt_S_n m n).
intro H4.
apply False_ind.
apply H3.
apply (PeanoNat.Nat.succ_inj m n H4).
intros m H2.
elim H2.
intros m1 H3.
apply (le_S (S m1) n).
apply H3.
intros m1 H3.
rewrite H3.
apply (le_n (S m1)).
Qed.

Lemma CountFinite2 : forall (N : nat), Finite nat (fun (n : nat) => n < N).
Proof.
intro N.
elim N.
cut ((fun n : nat => n < 0) = Empty_set nat).
intro H1.
rewrite H1.
apply (Empty_is_finite nat).
apply Extensionality_Ensembles.
apply conj.
intros n H1.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r n H1).
intros n H1.
elim H1.
intros n H1.
cut ((fun n0 : nat => n0 < S n) = Add nat (fun n0 : nat => n0 < n) n).
intro H2.
rewrite H2.
apply (Union_is_finite nat (fun n0 : nat => n0 < n) H1 n).
apply (lt_irrefl n).
apply Extensionality_Ensembles.
apply conj.
intros m H2.
elim (le_lt_or_eq m n).
intro H3.
left.
apply H3.
intro H3.
rewrite H3.
right.
apply (In_singleton nat n).
apply (le_S_n m n H2).
intros m H2.
elim H2.
intros k H3.
apply (le_trans (S k) n (S n) H3 (le_S n n (le_n n))).
intros k H3.
elim H3.
apply (le_n (S n)).
Qed.

Lemma MySumF2NSame : forall (N : nat) (CM : CommutativeMonoid) (F : nat -> CMT CM) (f : Count N -> CMT CM) (A : Ensemble nat), (forall (m : Count N), In nat A (proj1_sig m) -> F (proj1_sig m) = f m) -> (MySumF2 (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun (m : Count N) => In nat A (proj1_sig m))) CM f) = (MySumF2 nat (FiniteIntersection nat (exist (Finite nat) (fun (m : nat) => m < N) (CountFinite2 N)) A) CM F).
Proof.
intros N CM F f A H1.
cut (forall (u : Count N), proj1_sig (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun m : Count N => In nat A (proj1_sig m))) u -> proj1_sig (FiniteIntersection nat (exist (Finite nat) (fun m : nat => m < N) (CountFinite2 N)) A) (proj1_sig u)).
intro H2.
rewrite<- (MySumF2BijectiveSame (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun m : Count N => In nat A (proj1_sig m))) nat (FiniteIntersection nat (exist (Finite nat) (fun m : nat => m < N) (CountFinite2 N)) A) CM F (fun (m : Count N) => proj1_sig m) H2).
apply (MySumF2Same (Count N) (FiniteIntersection (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (fun m : Count N => In nat A (proj1_sig m))) CM).
intros u H3.
rewrite (H1 u).
reflexivity.
elim H3.
intros m H4 H5.
apply H4.
simpl.
cut (forall (k : {u : nat | Intersection nat A (fun m : nat => m < N) u}), proj1_sig k < N).
intro H3.
cut (forall (k : {u : nat | Intersection nat A (fun m : nat => m < N) u}), In (Count N) (Intersection (Count N) (fun m : Count N => In nat A (proj1_sig m)) (Full_set (Count N))) (exist (fun (m : nat) => m < N) (proj1_sig k) (H3 k))).
intro H4.
exists (fun (k : {u : nat | Intersection nat A (fun m : nat => m < N) u}) => exist (Intersection (Count N) (fun m : Count N => In nat A (proj1_sig m)) (Full_set (Count N))) (exist (fun (m : nat) => m < N) (proj1_sig k) (H3 k)) (H4 k)).
apply conj.
intro x.
apply sig_map.
apply sig_map.
reflexivity.
intro y.
apply sig_map.
reflexivity.
intro k.
apply (Intersection_intro (Count N)).
unfold In.
elim (proj2_sig k).
intros m H4 H5.
apply H4.
apply (Full_intro (Count N)).
intro k.
elim (proj2_sig k).
intros m H3 H4.
apply H4.
intros u H2.
apply (Intersection_intro nat).
elim H2.
intros m H3 H4.
apply H3.
apply (proj2_sig u).
Qed.

Lemma MySumF2Sn : forall (N : nat) (CM : CommutativeMonoid) (F : nat -> CMT CM), (MySumF2 nat (exist (Finite nat) (fun (m : nat) => m < S N) (CountFinite2 (S N))) CM F) = CMc CM (MySumF2 nat (exist (Finite nat) (fun (m : nat) => m < N) (CountFinite2 N)) CM F) (F N).
Proof.
intros N CM F.
rewrite (MySumF2Included nat (exist (Finite nat) (fun m : nat => m < N) (CountFinite2 N)) (exist (Finite nat) (fun m : nat => m < S N) (CountFinite2 (S N))) CM F).
simpl.
cut ((FiniteIntersection nat (exist (Finite nat) (fun m : nat => m < S N) (CountFinite2 (S N))) (Complement nat (fun m : nat => m < N))) = FiniteSingleton nat N).
intro H1.
rewrite H1.
rewrite MySumF2Singleton.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
intros n H1.
cut (n = N).
intro H2.
rewrite H2.
apply (In_singleton nat N).
elim H1.
intros m H2 H3.
elim (le_lt_or_eq m N).
intro H4.
apply False_ind.
apply H2.
apply H4.
intro H4.
apply H4.
apply (le_S_n m N H3).
intros n H1.
elim H1.
apply (Intersection_intro nat).
apply (lt_irrefl N).
apply (le_n (S N)).
intros n H1.
apply (le_S (S n) N H1).
Qed.

Lemma MySumF2Sn2 : forall (N : nat) (H1 : forall (m : Count N), proj1_sig m < S N) (H2 : N < S N) (CM : CommutativeMonoid) (F : Count (S N) -> CMT CM), (MySumF2 (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) CM F) = CMc CM (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) CM (fun (m : Count N) => F (exist (fun (n : nat) => n < S N) (proj1_sig m) (H1 m)))) (F (exist (fun (n : nat) => n < S N) N H2)).
Proof.
intros N H1 H2 CM F.
rewrite (MySumF2Excluded (Count (S N)) CM F (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (fun (m : Count (S N)) => proj1_sig m < N)).
cut ((FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (Complement (Count (S N)) (fun m : Count (S N) => proj1_sig m < N))) = (FiniteSingleton (Count (S N)) (exist (fun n : nat => n < S N) N H2))).
intro H3.
rewrite H3.
rewrite MySumF2Singleton.
cut (forall (u : Count N), proj1_sig (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) u -> proj1_sig (FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (fun m : Count (S N) => proj1_sig m < N)) (exist (fun n : nat => n < S N) (proj1_sig u) (H1 u))).
intro H4.
rewrite<- (MySumF2BijectiveSame (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) (Count (S N)) (FiniteIntersection (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) (fun m : Count (S N) => proj1_sig m < N)) CM F (fun (m : Count N) => exist (fun n : nat => n < S N) (proj1_sig m) (H1 m)) H4).
reflexivity.
simpl.
cut (forall (u0 : {u : Count (S N) | Intersection (Count (S N)) (fun m : Count (S N) => proj1_sig m < N) (Full_set (Count (S N))) u}), proj1_sig (proj1_sig u0) < N).
intro H5.
exists (fun (u0 : {u : Count (S N) | Intersection (Count (S N)) (fun m : Count (S N) => proj1_sig m < N) (Full_set (Count (S N))) u}) => exist (Full_set (Count N)) (exist (fun (n : nat) => n < N) (proj1_sig (proj1_sig u0)) (H5 u0)) (Full_intro (Count N) (exist (fun (n : nat) => n < N) (proj1_sig (proj1_sig u0)) (H5 u0)))).
apply conj.
intro x.
apply sig_map.
apply sig_map.
reflexivity.
intro y.
apply sig_map.
apply sig_map.
reflexivity.
intro u0.
elim (proj2_sig u0).
intros m H5 H6.
apply H5.
intros u H4.
apply Intersection_intro.
apply (proj2_sig u).
apply (Full_intro (Count (S N))).
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
intros u H3.
elim H3.
intros u0 H4 H5.
cut (u0 = (exist (fun n : nat => n < S N) N H2)).
intro H6.
rewrite H6.
apply (In_singleton (Count (S N))).
apply sig_map.
elim (le_lt_or_eq (proj1_sig u0) N).
intro H6.
apply False_ind.
apply (H4 H6).
intro H6.
apply H6.
apply (le_S_n (proj1_sig u0) N (proj2_sig u0)).
intros u H3.
elim H3.
apply Intersection_intro.
apply (lt_irrefl N).
apply (Full_intro (Count (S N))).
Qed.

Lemma MySumF2Sn2_exists : forall (N : nat), exists (H1 : forall (m : Count N), proj1_sig m < S N) (H2 : N < S N), forall (CM : CommutativeMonoid) (F : Count (S N) -> CMT CM), (MySumF2 (Count (S N)) (exist (Finite (Count (S N))) (Full_set (Count (S N))) (CountFinite (S N))) CM F) = CMc CM (MySumF2 (Count N) (exist (Finite (Count N)) (Full_set (Count N)) (CountFinite N)) CM (fun (m : Count N) => F (exist (fun (n : nat) => n < S N) (proj1_sig m) (H1 m)))) (F (exist (fun (n : nat) => n < S N) N H2)).
Proof.
intro N.
exists (fun (m : Count N) => le_S (S (proj1_sig m)) N (proj2_sig m)).
exists (le_n (S N)).
apply (MySumF2Sn2 N (fun (m : Count N) => le_S (S (proj1_sig m)) N (proj2_sig m)) (le_n (S N))).
Qed.

Lemma MySumF2Distr : forall (U : Type) (CM : CommutativeMonoid) (A : {X : Ensemble U | Finite U X}) (F G FG : U -> CMT CM), (forall (u : U), In U (proj1_sig A) u -> FG u = CMc CM (F u) (G u)) -> MySumF2 U A CM FG = CMc CM (MySumF2 U A CM F) (MySumF2 U A CM G).
Proof.
intros U CM A F G FG H1.
apply (FiniteSetInduction U A).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite (CM_O_r CM (CMe CM)).
reflexivity.
intros B b H2 H3 H4 H5.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite (CM_comm_assoc CM).
rewrite (H1 b H3).
rewrite H5.
reflexivity.
apply H4.
apply H4.
apply H4.
Qed.

End MySum.
