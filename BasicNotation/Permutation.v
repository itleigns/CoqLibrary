Add LoadPath "Tools" as Tools.
Add LoadPath "BasicProperty" as BasicProperty.
Add LoadPath "BasicNotation" as BasicNotation.

From mathcomp Require Import ssreflect.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Image.
Require Import Coq.Arith.Le.
Require Import Tools.MySum.
Require Import BasicProperty.MappingProperty.
Require Import BasicNotation.Parity.

Definition Permutation (N : nat) := {f : {n : nat | n < N} -> {n : nat | n < N} | Bijective f}.

Lemma PermutationFinite : forall (N : nat), Finite (Permutation N) (Full_set (Permutation N)).
Proof.
move=> N.
apply (FiniteSigSame ({n : nat | n < N} -> {n : nat | n < N})).
apply (Finite_downward_closed ({n : nat | n < N} -> {n : nat | n < N}) (Full_set ({n : nat | n < N} -> {n : nat | n < N}))).
apply (CountFiniteBijective ({n : nat | n < N} -> {n : nat | n < N})).
exists (PeanoNat.Nat.pow N N).
elim (CountPow N N).
move=> f.
elim.
move=> g H1.
exists g.
exists f.
apply conj.
apply (proj2 H1).
apply (proj1 H1).
move=> f H1.
apply (Full_intro ({n : nat | n < N} -> {n : nat | n < N}) f).
Qed.

Definition PermutationCompose (N : nat) (f g : Permutation N) := exist (fun (h : {n : nat | n < N} -> {n : nat | n < N}) => Bijective h) (compose (proj1_sig f) (proj1_sig g)) (BijChain {n : nat | n < N} {n : nat | n < N} {n : nat | n < N} (proj1_sig g) (proj1_sig f) (proj2_sig g) (proj2_sig f)).

Lemma PermutationIDSub : forall (N : nat), Bijective (fun (k : {n : nat | n < N}) => k).
Proof.
move=> N.
exists (fun k : {n : nat | n < N} => k).
apply conj.
move=> x.
reflexivity.
move=> y.
reflexivity.
Qed.

Definition PermutationID (N : nat) := exist (fun (f : {n : nat | n < N} -> {n : nat | n < N}) => Bijective f) (fun (k : {n : nat | n < N}) => k) (PermutationIDSub N).

Lemma PermutationInvSub : forall (N : nat) (f : Permutation N), Bijective (proj1_sig (BijectiveInvExist {n : nat | n < N} {n : nat | n < N} (proj1_sig f) (proj2_sig f))).
Proof.
move=> N f.
exists (proj1_sig f).
apply conj.
apply (proj2 (proj2_sig (BijectiveInvExist {n : nat | n < N} {n : nat | n < N} (proj1_sig f) (proj2_sig f)))).
apply (proj1 (proj2_sig (BijectiveInvExist {n : nat | n < N} {n : nat | n < N} (proj1_sig f) (proj2_sig f)))).
Qed.

Definition PermutationInv (N : nat) (f : Permutation N) := exist (fun (f : {n : nat | n < N} -> {n : nat | n < N}) => Bijective f) (proj1_sig (BijectiveInvExist {n : nat | n < N} {n : nat | n < N} (proj1_sig f) (proj2_sig f))) (PermutationInvSub N f).

Lemma PermutationCompose_assoc : forall (N : nat) (f g h : Permutation N), PermutationCompose N (PermutationCompose N f g) h = PermutationCompose N f (PermutationCompose N g h).
Proof.
move=> N f g h.
apply sig_map.
reflexivity.
Qed.

Lemma PermutationCompose_O_r : forall (N : nat) (f : Permutation N), PermutationCompose N f (PermutationID N) = f.
Proof.
move=> N f.
apply sig_map.
reflexivity.
Qed.

Lemma PermutationCompose_O_l : forall (N : nat) (f : Permutation N), PermutationCompose N (PermutationID N) f = f.
Proof.
move=> N f.
apply sig_map.
reflexivity.
Qed.

Lemma PermutationCompose_inv_r : forall (N : nat) (f : Permutation N), PermutationCompose N f (PermutationInv N f) = (PermutationID N).
Proof.
move=> N f.
apply sig_map.
apply functional_extensionality.
apply (proj2 (proj2_sig (BijectiveInvExist {n : nat | n < N} {n : nat | n < N} (proj1_sig f) (proj2_sig f)))).
Qed.

Lemma PermutationCompose_inv_l : forall (N : nat) (f : Permutation N), PermutationCompose N (PermutationInv N f) f = (PermutationID N).
Proof.
move=> N f.
apply sig_map.
apply functional_extensionality.
apply (proj1 (proj2_sig (BijectiveInvExist {n : nat | n < N} {n : nat | n < N} (proj1_sig f) (proj2_sig f)))).
Qed.

Lemma PermutationSwapSub : forall (N : nat) (x y : {n : nat | n < N}), Bijective (fun (k : {n : nat | n < N}) => match excluded_middle_informative (k = x) with
  | left _ => y
  | right _ => match excluded_middle_informative (k = y) with
    | left _ => x
    | right _ => k
  end
end).
Proof.
move=> N x y.
exists (fun (k : {n : nat | n < N}) => match excluded_middle_informative (k = x) with
  | left _ => y
  | right _ => match excluded_middle_informative (k = y) with
    | left _ => x
    | right _ => k
  end
end).
suff: (forall (k : {n : nat | n < N}), compose (fun (k : {n : nat | n < N}) => match excluded_middle_informative (k = x) with
  | left _ => y
  | right _ => match excluded_middle_informative (k = y) with
    | left _ => x
    | right _ => k
  end
end) (fun (k : {n : nat | n < N}) => match excluded_middle_informative (k = x) with
  | left _ => y
  | right _ => match excluded_middle_informative (k = y) with
    | left _ => x
    | right _ => k
  end
end) k = k).
move=> H1.
apply conj.
apply H1.
apply H1.
move=> k.
unfold compose.
elim (excluded_middle_informative (k = x)).
move=> H1.
elim (excluded_middle_informative (y = x)).
rewrite H1.
apply.
move=> H2.
elim (excluded_middle_informative (y = y)).
move=> H3.
rewrite H1.
reflexivity.
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> H1.
elim (excluded_middle_informative (k = y)).
move=> H2.
elim (excluded_middle_informative (x = x)).
move=> H3.
rewrite H2.
reflexivity.
move=> H3.
apply False_ind.
apply H3.
reflexivity.
move=> H2.
elim (excluded_middle_informative (k = x)).
move=> H3.
apply False_ind.
apply (H1 H3).
move=> H3.
elim (excluded_middle_informative (k = y)).
move=> H4.
apply False_ind.
apply (H2 H4).
move=> H4.
reflexivity.
Qed.

Definition PermutationSwap (N : nat) (x y : {n : nat | n < N}) := exist (fun (f : {n : nat | n < N} -> {n : nat | n < N}) => Bijective f) (fun (k : {n : nat | n < N}) => match excluded_middle_informative (k = x) with
  | left _ => y
  | right _ => match excluded_middle_informative (k = y) with
    | left _ => x
    | right _ => k
  end
end) (PermutationSwapSub N x y).

Lemma PermutationSwap_comm : forall (N : nat) (x y : {n : nat | n < N}), PermutationSwap N x y = PermutationSwap N y x.
Proof.
move=> N x y.
apply sig_map.
simpl.
apply functional_extensionality.
move=> k.
elim (excluded_middle_informative (k = x)).
elim (excluded_middle_informative (k = y)).
move=> H1 H2.
rewrite - H1.
apply H2.
move=> H1 H2.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma PermutationSwap_same : forall (N : nat) (x : {n : nat | n < N}), PermutationSwap N x x = PermutationID N.
Proof.
move=> N x.
apply sig_map.
simpl.
apply functional_extensionality.
move=> k.
elim (excluded_middle_informative (k = x)).
move=> H1.
rewrite H1.
reflexivity.
move=> H1.
reflexivity.
Qed.

Lemma PermutationParitySub : forall (N : nat), Finite ({n : nat | n < N} * {n : nat | n < N}) (fun (xy : {n : nat | n < N} * {n : nat | n < N}) => proj1_sig (fst xy) < proj1_sig (snd xy)).
Proof.
move=> N.
apply (Finite_downward_closed ({n : nat | n < N} * {n : nat | n < N}) (Full_set ({n : nat | n < N} * {n : nat | n < N}))).
apply (cardinal_finite ({n : nat | n < N} * {n : nat | n < N}) (Full_set ({n : nat | n < N} * {n : nat | n < N})) (N * N)).
apply (proj1 (CountCardinalBijective ({n : nat | n < N} * {n : nat | n < N}) (N * N))).
elim (proj2_sig (CountMult N N)).
move=> f H1.
exists f.
exists (proj1_sig (CountMult N N)).
apply conj.
apply (proj2 H1).
apply (proj1 H1).
move=> xy H1.
apply (Full_intro ({n : nat | n < N} * {n : nat | n < N}) xy).
Qed.

Definition PermutationParity (N : nat) (f : Permutation N) := MySumF2 ({n : nat | n < N} * {n : nat | n < N}) (exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun (xy : {n : nat | n < N} * {n : nat | n < N}) => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N)) ParityXORCM (fun (xy : {n : nat | n < N} * {n : nat | n < N}) => match excluded_middle_informative (proj1_sig (proj1_sig f (fst xy)) < proj1_sig (proj1_sig f (snd xy))) with
  | left _ => OFF
  | right _ => ON
end).

Lemma PermutationComposeParity : forall (N : nat) (f g : Permutation N), PermutationParity N (PermutationCompose N f g) = ParityXOR (PermutationParity N f) (PermutationParity N g).
Proof.
move=> N f g.
unfold PermutationParity.
suff: ((exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N)) = (FiniteIm ({n : nat | n < N} * {n : nat | n < N}) ({n : nat | n < N} * {n : nat | n < N}) (fun (xy : {n : nat | n < N} * {n : nat | n < N}) => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => (proj1_sig g (fst xy), proj1_sig g (snd xy))
  | right _ => (proj1_sig g (snd xy), proj1_sig g (fst xy))
end) (exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N)))).
move=> H1.
rewrite {2} H1.
rewrite - (MySumF2BijectiveSame2 ({n : nat | n < N} * {n : nat | n < N}) ({n : nat | n < N} * {n : nat | n < N}) (exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N)) (fun (xy : {n : nat | n < N} * {n : nat | n < N}) => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => (proj1_sig g (fst xy), proj1_sig g (snd xy))
  | right _ => (proj1_sig g (snd xy), proj1_sig g (fst xy))
end) ParityXORCM (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig f (fst xy)) < proj1_sig (proj1_sig f (snd xy))) with
  | left _ => OFF
  | right _ => ON
end)).
apply (FiniteSetInduction ({n : nat | n < N} * {n : nat | n < N}) (exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H2 H3 H4 H5.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite MySumF2Add.
rewrite H5.
simpl.
suff: ((match excluded_middle_informative (proj1_sig (compose (proj1_sig f) (proj1_sig g) (fst b)) < proj1_sig (compose (proj1_sig f) (proj1_sig g) (snd b))) with
  | left _ => OFF
  | right _ => ON
end) = ParityXOR (compose (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig f (fst xy)) < proj1_sig (proj1_sig f (snd xy))) with
  | left _ => OFF
  | right _ => ON
end) (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => (proj1_sig g (fst xy), proj1_sig g (snd xy))
  | right _ => (proj1_sig g (snd xy), proj1_sig g (fst xy))
end) b) (match excluded_middle_informative (proj1_sig (proj1_sig g (fst b)) < proj1_sig (proj1_sig g (snd b))) with
  | left _ => OFF
  | right _ => ON
end)).
move=> H6.
rewrite H6.
rewrite - (ParityXOR_assoc (ParityXOR (MySumF2 ({n : nat | n < N} * {n : nat | n < N}) B ParityXORCM (compose (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig f (fst xy)) < proj1_sig (proj1_sig f (snd xy))) with
  | left _ => OFF
  | right _ => ON
end) (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => (proj1_sig g (fst xy), proj1_sig g (snd xy))
  | right _ => (proj1_sig g (snd xy), proj1_sig g (fst xy))
end))) (MySumF2 ({n : nat | n < N} * {n : nat | n < N}) B ParityXORCM (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => OFF
  | right _ => ON
end))) (compose (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig f (fst xy)) < proj1_sig (proj1_sig f (snd xy))) with
  | left _ => OFF
  | right _ => ON
end) (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => (proj1_sig g (fst xy), proj1_sig g (snd xy))
  | right _ => (proj1_sig g (snd xy), proj1_sig g (fst xy))
end) b) (match excluded_middle_informative (proj1_sig (proj1_sig g (fst b)) < proj1_sig (proj1_sig g (snd b))) with
  | left _ => OFF
  | right _ => ON
end)).
rewrite (ParityXOR_assoc (MySumF2 ({n : nat | n < N} * {n : nat | n < N}) B ParityXORCM (compose (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig f (fst xy)) < proj1_sig (proj1_sig f (snd xy))) with
  | left _ => OFF
  | right _ => ON
end) (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => (proj1_sig g (fst xy), proj1_sig g (snd xy))
  | right _ => (proj1_sig g (snd xy), proj1_sig g (fst xy))
end))) (MySumF2 ({n : nat | n < N} * {n : nat | n < N}) B ParityXORCM (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => OFF
  | right _ => ON
end)) (compose (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig f (fst xy)) < proj1_sig (proj1_sig f (snd xy))) with
  | left _ => OFF
  | right _ => ON
end) (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => (proj1_sig g (fst xy), proj1_sig g (snd xy))
  | right _ => (proj1_sig g (snd xy), proj1_sig g (fst xy))
end) b)).
rewrite (ParityXOR_comm (MySumF2 ({n : nat | n < N} * {n : nat | n < N}) B ParityXORCM (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => OFF
  | right _ => ON
end)) (compose (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig f (fst xy)) < proj1_sig (proj1_sig f (snd xy))) with
  | left _ => OFF
  | right _ => ON
end) (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => (proj1_sig g (fst xy), proj1_sig g (snd xy))
  | right _ => (proj1_sig g (snd xy), proj1_sig g (fst xy))
end) b)).
rewrite - (ParityXOR_assoc (MySumF2 ({n : nat | n < N} * {n : nat | n < N}) B ParityXORCM (compose (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig f (fst xy)) < proj1_sig (proj1_sig f (snd xy))) with
  | left _ => OFF
  | right _ => ON
end) (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => (proj1_sig g (fst xy), proj1_sig g (snd xy))
  | right _ => (proj1_sig g (snd xy), proj1_sig g (fst xy))
end))) (compose (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig f (fst xy)) < proj1_sig (proj1_sig f (snd xy))) with
  | left _ => OFF
  | right _ => ON
end) (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => (proj1_sig g (fst xy), proj1_sig g (snd xy))
  | right _ => (proj1_sig g (snd xy), proj1_sig g (fst xy))
end) b) (MySumF2 ({n : nat | n < N} * {n : nat | n < N}) B ParityXORCM (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => OFF
  | right _ => ON
end))).
apply ParityXOR_assoc.
unfold compose.
elim (excluded_middle_informative (proj1_sig (proj1_sig g (fst b)) < proj1_sig (proj1_sig g (snd b)))).
move=> H6.
rewrite ParityXOR_O_r.
reflexivity.
simpl.
move=> H6.
elim (excluded_middle_informative (proj1_sig (proj1_sig f (proj1_sig g (fst b))) < proj1_sig (proj1_sig f (proj1_sig g (snd b))))).
elim (excluded_middle_informative (proj1_sig (proj1_sig f (proj1_sig g (snd b))) < proj1_sig (proj1_sig f (proj1_sig g (fst b))))).
move=> H7 H8.
apply False_ind.
apply (lt_irrefl (proj1_sig (proj1_sig f (proj1_sig g (snd b)))) (lt_trans (proj1_sig (proj1_sig f (proj1_sig g (snd b)))) (proj1_sig (proj1_sig f (proj1_sig g (fst b)))) (proj1_sig (proj1_sig f (proj1_sig g (snd b)))) H7 H8)).
move=> H7 H8.
reflexivity.
elim (excluded_middle_informative (proj1_sig (proj1_sig f (proj1_sig g (snd b))) < proj1_sig (proj1_sig f (proj1_sig g (fst b))))).
move=> H7 H8.
reflexivity.
move=> H7 H8.
apply False_ind.
apply (lt_not_le (proj1_sig (fst b)) (proj1_sig (snd b)) H3).
suff: ((snd b) = (fst b)).
move=> H9.
rewrite H9.
apply (le_n (proj1_sig (fst b))).
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig g) (proj2_sig g)).
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig f) (proj2_sig f)).
apply sig_map.
elim (le_or_lt (proj1_sig (proj1_sig f (proj1_sig g (snd b)))) (proj1_sig (proj1_sig f (proj1_sig g (fst b))))).
move=> H9.
elim (le_lt_or_eq (proj1_sig (proj1_sig f (proj1_sig g (snd b)))) (proj1_sig (proj1_sig f (proj1_sig g (fst b)))) H9).
move=> H10.
apply False_ind.
apply (H7 H10).
apply.
move=> H9.
apply False_ind.
apply (H8 H9).
apply H4.
apply H4.
apply H4.
simpl.
move=> u1 u2 H2 H3.
elim (excluded_middle_informative (proj1_sig (proj1_sig g (fst u1)) < proj1_sig (proj1_sig g (snd u1)))).
elim (excluded_middle_informative (proj1_sig (proj1_sig g (fst u2)) < proj1_sig (proj1_sig g (snd u2)))).
move=> H4 H5 H6.
apply injective_projections.
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig g) (proj2_sig g)).
suff: (proj1_sig g (fst u1) = fst (proj1_sig g (fst u1), proj1_sig g (snd u1))).
move=> H7.
rewrite H7.
rewrite H6.
reflexivity.
reflexivity.
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig g) (proj2_sig g)).
suff: (proj1_sig g (snd u1) = snd (proj1_sig g (fst u1), proj1_sig g (snd u1))).
move=> H7.
rewrite H7.
rewrite H6.
reflexivity.
reflexivity.
move=> H4 H5 H6.
apply False_ind.
apply (lt_irrefl (proj1_sig (fst u1))).
apply (lt_trans (proj1_sig (fst u1)) (proj1_sig (snd u1)) (proj1_sig (fst u1)) H2).
suff: (snd u1 = fst u2).
move=> H7.
suff: (fst u1 = snd u2).
move=> H8.
rewrite H7.
rewrite H8.
apply H3.
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig g) (proj2_sig g)).
suff: (proj1_sig g (fst u1) = fst (proj1_sig g (fst u1), proj1_sig g (snd u1))).
move=> H8.
rewrite H8.
rewrite H6.
reflexivity.
reflexivity.
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig g) (proj2_sig g)).
suff: (proj1_sig g (snd u1) = snd (proj1_sig g (fst u1), proj1_sig g (snd u1))).
move=> H7.
rewrite H7.
rewrite H6.
reflexivity.
reflexivity.
elim (excluded_middle_informative (proj1_sig (proj1_sig g (fst u2)) < proj1_sig (proj1_sig g (snd u2)))).
move=> H4 H5 H6.
apply False_ind.
apply (lt_irrefl (proj1_sig (fst u2))).
apply (lt_trans (proj1_sig (fst u2)) (proj1_sig (snd u2)) (proj1_sig (fst u2)) H3).
suff: (snd u2 = fst u1).
move=> H7.
suff: (fst u2 = snd u1).
move=> H8.
rewrite H7.
rewrite H8.
apply H2.
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig g) (proj2_sig g)).
suff: (proj1_sig g (fst u2) = fst (proj1_sig g (fst u2), proj1_sig g (snd u2))).
move=> H8.
rewrite H8.
rewrite - H6.
reflexivity.
reflexivity.
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig g) (proj2_sig g)).
suff: (proj1_sig g (snd u2) = snd (proj1_sig g (fst u2), proj1_sig g (snd u2))).
move=> H7.
rewrite H7.
rewrite - H6.
reflexivity.
reflexivity.
move=> H4 H5 H6.
apply injective_projections.
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig g) (proj2_sig g)).
suff: (proj1_sig g (fst u1) = snd (proj1_sig g (snd u1), proj1_sig g (fst u1))).
move=> H7.
rewrite H7.
rewrite H6.
reflexivity.
reflexivity.
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig g) (proj2_sig g)).
suff: (proj1_sig g (snd u1) = fst (proj1_sig g (snd u1), proj1_sig g (fst u1))).
move=> H7.
rewrite H7.
rewrite H6.
reflexivity.
reflexivity.
apply sig_map.
simpl.
apply Extensionality_Ensembles.
apply conj.
move=> k H1.
elim (proj2_sig g).
move=> ginv H2.
elim (le_or_lt (proj1_sig (ginv (fst k))) (proj1_sig (ginv (snd k)))).
move=> H3.
elim (le_lt_or_eq (proj1_sig (ginv (fst k))) (proj1_sig (ginv (snd k)))).
move=> H4.
apply (Im_intro ({n : nat | n < N} * {n : nat | n < N}) ({n : nat | n < N} * {n : nat | n < N}) (fun (xy : {n : nat | n < N} * {n : nat | n < N}) => proj1_sig (fst xy) < proj1_sig (snd xy)) (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => (proj1_sig g (fst xy), proj1_sig g (snd xy))
  | right _ => (proj1_sig g (snd xy), proj1_sig g (fst xy))
end) (ginv (fst k), ginv (snd k))).
apply H4.
simpl.
elim (excluded_middle_informative (proj1_sig (proj1_sig g (ginv (fst k))) < proj1_sig (proj1_sig g (ginv (snd k))))).
move=> H5.
apply injective_projections.
rewrite (proj2 H2 (fst k)).
reflexivity.
rewrite (proj2 H2 (snd k)).
reflexivity.
move=> H5.
apply False_ind.
apply H5.
rewrite (proj2 H2 (fst k)).
rewrite (proj2 H2 (snd k)).
apply H1.
move=> H4.
apply False_ind.
suff: (fst k = snd k).
move=> H5.
apply (lt_irrefl (proj1_sig (fst k))).
rewrite {2} H5.
apply H1.
apply (BijInj {n : nat | n < N} {n : nat | n < N} ginv).
exists (proj1_sig g).
apply conj.
apply (proj2 H2).
apply (proj1 H2).
apply sig_map.
apply H4.
apply H3.
move=> H3.
apply (Im_intro ({n : nat | n < N} * {n : nat | n < N}) ({n : nat | n < N} * {n : nat | n < N}) (fun (xy : {n : nat | n < N} * {n : nat | n < N}) => proj1_sig (fst xy) < proj1_sig (snd xy)) (fun (xy : {n : nat | n < N} * {n : nat | n < N}) => match excluded_middle_informative (proj1_sig (proj1_sig g (fst xy)) < proj1_sig (proj1_sig g (snd xy))) with
  | left _ => (proj1_sig g (fst xy), proj1_sig g (snd xy))
  | right _ => (proj1_sig g (snd xy), proj1_sig g (fst xy))
end) (ginv (snd k), ginv (fst k))).
apply H3.
simpl.
elim (excluded_middle_informative (proj1_sig (proj1_sig g (ginv (snd k))) < proj1_sig (proj1_sig g (ginv (fst k))))).
move=> H4.
apply False_ind.
apply (lt_irrefl (proj1_sig (snd k))).
apply (lt_trans (proj1_sig (snd k)) (proj1_sig (fst k)) (proj1_sig (snd k))).
rewrite - (proj2 H2 (fst k)).
rewrite - (proj2 H2 (snd k)).
apply H4.
apply H1.
move=> H4.
apply injective_projections.
rewrite (proj2 H2 (fst k)).
reflexivity.
rewrite (proj2 H2 (snd k)).
reflexivity.
move=> xy.
elim.
move=> k H1 y.
elim (excluded_middle_informative (proj1_sig (proj1_sig g (fst k)) < proj1_sig (proj1_sig g (snd k)))).
move=> H2 H3.
rewrite H3.
apply H2.
move=> H2 H3.
rewrite H3.
elim (le_or_lt (proj1_sig (proj1_sig g (snd k))) (proj1_sig (proj1_sig g (fst k)))).
move=> H4.
elim (le_lt_or_eq (proj1_sig (proj1_sig g (snd k))) (proj1_sig (proj1_sig g (fst k)))).
apply.
move=> H5.
apply False_ind.
apply (lt_irrefl (proj1_sig (snd k))).
suff: (snd k = fst k).
move=> H6.
rewrite {1} H6.
apply H1.
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig g) (proj2_sig g)).
apply sig_map.
apply H5.
apply H4.
move=> H4.
apply False_ind.
apply (H2 H4).
Qed.

Lemma PermutationIDParity : forall (N : nat), PermutationParity N (PermutationID N) = OFF.
Proof.
move=> N.
apply MySumF2O.
move=> u H1.
elim (excluded_middle_informative (proj1_sig (proj1_sig (PermutationID N) (fst u)) < proj1_sig (proj1_sig (PermutationID N) (snd u)))).
move=> H2.
reflexivity.
move=> H2.
apply False_ind.
apply (H2 H1).
Qed.

Lemma PermutationInvParity : forall (N : nat) (f : Permutation N), PermutationParity N (PermutationInv N f) = PermutationParity N f.
Proof.
move=> N f.
suff: (PermutationParity N (PermutationID N) = OFF).
rewrite - (PermutationCompose_inv_l N f).
rewrite (PermutationComposeParity N (PermutationInv N f) f).
elim (PermutationParity N (PermutationInv N f)).
elim (PermutationParity N f).
move=> H1.
reflexivity.
apply.
elim (PermutationParity N f).
move=> H1.
rewrite - H1.
reflexivity.
apply.
apply (PermutationIDParity N).
Qed.

Lemma PermutationSwapParity : forall (N : nat) (x y : {n : nat | n < N}), x <> y -> PermutationParity N (PermutationSwap N x y) = ON.
Proof.
suff: (forall (N : nat) (x y : {n : nat | n < N}), proj1_sig x < proj1_sig y -> PermutationParity N (PermutationSwap N x y) = ON).
move=> H1 N x y H2.
elim (nat_total_order (proj1_sig x) (proj1_sig y)).
apply (H1 N x y).
rewrite (PermutationSwap_comm N x y).
apply (H1 N y x).
move=> H3.
apply H2.
apply sig_map.
apply H3.
move=> N x y H1.
unfold PermutationParity.
rewrite (MySumF2Excluded ({n : nat | n < N} * {n : nat | n < N}) ParityXORCM (fun (xy : {n : nat | n < N} * {n : nat | n < N}) => match excluded_middle_informative (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy)) < proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy))) with
  | left _ => OFF
  | right _ => ON
end) (exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N)) (fun xy : {n : nat | n < N} * {n : nat | n < N} => (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy)) > proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy))))).
rewrite (MySumF2O ({n : nat | n < N} * {n : nat | n < N}) (FiniteIntersection ({n : nat | n < N} * {n : nat | n < N}) (exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun (xy : {n : nat | n < N} * {n : nat | n < N}) => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N)) (Complement ({n : nat | n < N} * {n : nat | n < N}) (fun (xy : {n : nat | n < N} * {n : nat | n < N}) => proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy)) > proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy)))))).
rewrite (CM_O_r ParityXORCM).
suff: (Included ({n : nat | n < N} * {n : nat | n < N}) (proj1_sig (FiniteAdd ({n : nat | n < N} * {n : nat | n < N}) (FiniteUnion ({n : nat | n < N} * {n : nat | n < N}) (FiniteIm {n : nat | n < N} ({n : nat | n < N} * {n : nat | n < N}) (fun (k : {n : nat | n < N}) => (x, k)) (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (fun (k : {n : nat | n < N}) => proj1_sig x < proj1_sig k < proj1_sig y))) (FiniteIm {n : nat | n < N} ({n : nat | n < N} * {n : nat | n < N}) (fun (k : {n : nat | n < N}) => (k, y)) (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (fun (k : {n : nat | n < N}) => proj1_sig x < proj1_sig k < proj1_sig y))) ) (x, y))) (proj1_sig (FiniteIntersection ({n : nat | n < N} * {n : nat | n < N}) (exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N)) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy)) > proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy)))) )).
move=> H2.
suff: ((FiniteIntersection ({n : nat | n < N} * {n : nat | n < N}) (exist (Finite ({n : nat | n < N} * {n : nat | n < N})) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (fst xy) < proj1_sig (snd xy)) (PermutationParitySub N)) (fun xy : {n : nat | n < N} * {n : nat | n < N} => proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy)) > proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy)))) = (FiniteAdd ({n : nat | n < N} * {n : nat | n < N}) (FiniteUnion ({n : nat | n < N} * {n : nat | n < N}) (FiniteIm {n : nat | n < N} ({n : nat | n < N} * {n : nat | n < N}) (fun (k : {n : nat | n < N}) => (x, k)) (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (fun (k : {n : nat | n < N}) => proj1_sig x < proj1_sig k < proj1_sig y))) (FiniteIm {n : nat | n < N} ({n : nat | n < N} * {n : nat | n < N}) (fun (k : {n : nat | n < N}) => (k, y)) (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (fun (k : {n : nat | n < N}) => proj1_sig x < proj1_sig k < proj1_sig y))) ) (x, y))).
move=> H3.
rewrite H3.
rewrite MySumF2Add.
suff: ((MySumF2 ({n : nat | n < N} * {n : nat | n < N}) (FiniteUnion ({n : nat | n < N} * {n : nat | n < N}) (FiniteIm {n : nat | n < N} ({n : nat | n < N} * {n : nat | n < N}) (fun k : {n : nat | n < N} => (x, k)) (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (fun k : {n : nat | n < N} => proj1_sig x < proj1_sig k < proj1_sig y))) (FiniteIm {n : nat | n < N} ({n : nat | n < N} * {n : nat | n < N}) (fun k : {n : nat | n < N} => (k, y)) (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (fun k : {n : nat | n < N} => proj1_sig x < proj1_sig k < proj1_sig y)))) ParityXORCM (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy)) < proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy))) with
  | left _ => OFF
  | right _ => ON
end)) = OFF).
move=> H4.
rewrite H4.
elim (H2 (x, y)).
move=> xy H5 H6.
elim (excluded_middle_informative (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy)) < proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy)))).
move=> H7.
apply False_ind.
apply (lt_irrefl (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy))) (lt_trans (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy))) (proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy))) (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy))) H7 H5)).
move=> H7.
reflexivity.
right.
apply In_singleton.
rewrite MySumF2Union.
rewrite - (MySumF2BijectiveSame2 {n : nat | n < N} ({n : nat | n < N} * {n : nat | n < N}) (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (fun k : {n : nat | n < N} => proj1_sig x < proj1_sig k < proj1_sig y)) (fun (k : {n : nat | n < N}) => (x, k)) ParityXORCM (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy)) < proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy))) with
  | left _ => OFF
  | right _ => ON
end)).
rewrite - (MySumF2BijectiveSame2 {n : nat | n < N} ({n : nat | n < N} * {n : nat | n < N}) (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (fun k : {n : nat | n < N} => proj1_sig x < proj1_sig k < proj1_sig y)) (fun (k : {n : nat | n < N}) => (k, y)) ParityXORCM (fun xy : {n : nat | n < N} * {n : nat | n < N} => match excluded_middle_informative (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy)) < proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy))) with
  | left _ => OFF
  | right _ => ON
end)).
unfold compose.
apply (FiniteSetInduction {n : nat | n < N} (FiniteIntersection {n : nat | n < N} (exist (Finite {n : nat | n < N}) (Full_set {n : nat | n < N}) (CountFinite N)) (fun k : {n : nat | n < N} => proj1_sig x < proj1_sig k < proj1_sig y))).
apply conj.
rewrite MySumF2Empty.
rewrite MySumF2Empty.
reflexivity.
move=> B b H4 H5 H6 H7.
rewrite MySumF2Add.
rewrite MySumF2Add.
elim (H2 (x, b)).
move=> xy1 H8 H9.
elim (excluded_middle_informative (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy1)) < proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy1)))).
move=> H10.
apply False_ind.
apply (lt_irrefl (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy1))) (lt_trans (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy1))) (proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy1))) (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy1))) H10 H8)).
move=> H10.
elim (H2 (b, y)).
move=> xy2 H11 H12.
elim (excluded_middle_informative (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy2)) < proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy2)))).
move=> H13.
apply False_ind.
apply (lt_irrefl (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy2))) (lt_trans (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy2))) (proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy2))) (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy2))) H13 H11)).
move=> H13.
simpl.
rewrite (ParityXOR_comm (MySumF2 {n : nat | n < N} B ParityXORCM (fun k : {n : nat | n < N} => match excluded_middle_informative (proj1_sig (match excluded_middle_informative (k = x) with
    | left _ => y
    | right _ => match excluded_middle_informative (k = y) with
      | left _ => x
      | right _ => k
    end
  end) < proj1_sig (match excluded_middle_informative (y = x) with
    | left _ => y
    | right _ => match excluded_middle_informative (y = y) with
      | left _ => x
      | right _ => y
    end
  end)) with
  | left _ => OFF
  | right _ => ON
end)) ON).
rewrite - (ParityXOR_assoc (ParityXOR (MySumF2 {n : nat | n < N} B ParityXORCM (fun k : {n : nat | n < N} => match excluded_middle_informative (proj1_sig (match excluded_middle_informative (x = x) with
    | left _ => y
    | right _ => match excluded_middle_informative (x = y) with
      | left _ => x
      | right _ => x
    end
  end) < proj1_sig (match excluded_middle_informative (k = x) with
    | left _ => y
    | right _ => match excluded_middle_informative (k = y) with
      | left _ => x
      | right _ => k
    end
  end)) with
  | left _ => OFF
  | right _ => ON
end)) ON) ON (MySumF2 {n : nat | n < N} B ParityXORCM (fun k : {n : nat | n < N} => match excluded_middle_informative (proj1_sig (match excluded_middle_informative (k = x) with
    | left _ => y
    | right _ => match excluded_middle_informative (k = y) with
      | left _ => x
      | right _ => k
    end
  end) < proj1_sig (match excluded_middle_informative (y = x) with
    | left _ => y
    | right _ => match excluded_middle_informative (y = y) with
      | left _ => x
      | right _ => y
    end
  end)) with
  | left _ => OFF
  | right _ => ON
end))).
rewrite (ParityXOR_assoc (MySumF2 {n : nat | n < N} B ParityXORCM (fun k : {n : nat | n < N} => match excluded_middle_informative (proj1_sig (match excluded_middle_informative (x = x) with
    | left _ => y
    | right _ => match excluded_middle_informative (x = y) with
      | left _ => x
      | right _ => x
    end
  end) < proj1_sig (match excluded_middle_informative (k = x) with
    | left _ => y
    | right _ => match excluded_middle_informative (k = y) with
      | left _ => x
      | right _ => k
    end
  end)) with
  | left _ => OFF
  | right _ => ON
end)) ON ON).
simpl.
rewrite ParityXOR_O_r.
apply H7.
left.
right.
apply (Im_intro {n : nat | n < N} ({n : nat | n < N} * {n : nat | n < N}) (Intersection {n : nat | n < N} (fun (k : {n : nat | n < N}) => proj1_sig x < proj1_sig k < proj1_sig y) (Full_set {n : nat | n < N})) (fun (k : {n : nat | n < N}) => (k, y)) b H5).
reflexivity.
left.
left.
apply (Im_intro {n : nat | n < N} ({n : nat | n < N} * {n : nat | n < N}) (Intersection {n : nat | n < N} (fun (k : {n : nat | n < N}) => proj1_sig x < proj1_sig k < proj1_sig y) (Full_set {n : nat | n < N})) (fun (k : {n : nat | n < N}) => (x, k)) b H5).
reflexivity.
apply H6.
apply H6.
move=> u1 u2 H4 H5 H6.
suff: (u1 = fst (u1, y)).
move=> H7.
rewrite H7.
rewrite H6.
reflexivity.
reflexivity.
move=> u1 u2 H4 H5 H6.
suff: (u1 = snd (x, u1)).
move=> H7.
rewrite H7.
rewrite H6.
reflexivity.
reflexivity.
move=> u.
elim.
move=> k1 H4 z1 H5 H6.
suff: (z1 = (k1, y)).
elim H6.
move=> k2 H7 z2 H9 H10.
apply (lt_irrefl (proj1_sig (snd z2))).
rewrite {1} H9.
rewrite H10.
elim H7.
move=> l H11 H12.
apply (proj2 H11).
apply H5.
move=> H4.
suff: ((exists (k : {n : nat | n < N}), (proj1_sig x < proj1_sig k < proj1_sig y) /\ (x, k) = (x, y)) \/ (exists (k : {n : nat | n < N}), (proj1_sig x < proj1_sig k < proj1_sig y) /\ (k, y) = (x, y))).
elim.
elim.
move=> k H5.
apply (lt_irrefl (proj1_sig (snd (x, k)))).
rewrite {2} (proj2 H5).
apply (proj2 (proj1 H5)).
elim.
move=> k H5.
apply (lt_irrefl (proj1_sig (fst (k, y)))).
rewrite {1} (proj2 H5).
apply (proj1 (proj1 H5)).
elim H4.
move=> xy.
elim.
move=> k H5 z H6.
left.
rewrite H6.
exists k.
apply conj.
elim H5.
move=> k0 H7 H8.
apply H7.
reflexivity.
move=> xy.
elim.
move=> k H5 z H6.
right.
rewrite H6.
exists k.
apply conj.
elim H5.
move=> k0 H7 H8.
apply H7.
reflexivity.
apply sig_map.
apply Extensionality_Ensembles.
apply conj.
move=> xy.
elim.
move=> xy1.
unfold In.
unfold PermutationSwap.
simpl.
elim (excluded_middle_informative (fst xy1 = x)).
elim (excluded_middle_informative (snd xy1 = x)).
move=> H3 H4 H5.
apply False_ind.
apply (lt_irrefl (proj1_sig y) H5).
elim (excluded_middle_informative (snd xy1 = y)).
move=> H3 H4 H5 H6 H7.
right.
suff: (xy1 = (x, y)).
move=> H8.
rewrite H8.
apply In_singleton.
apply injective_projections.
apply H5.
apply H3.
move=> H3 H4 H5 H6 H7.
left.
left.
apply (Im_intro {n : nat | n < N} ({n : nat | n < N} * {n : nat | n < N}) (Intersection {n : nat | n < N} (fun k : {n : nat | n < N} => proj1_sig x < proj1_sig k < proj1_sig y) (Full_set {n : nat | n < N})) (fun k : {n : nat | n < N} => (x, k)) (snd xy1)).
apply Intersection_intro.
apply conj.
rewrite - H5.
apply H7.
apply H6.
apply Full_intro.
apply injective_projections.
apply H5.
reflexivity.
elim (excluded_middle_informative (fst xy1 = y)).
elim (excluded_middle_informative (snd xy1 = x)).
move=> H3 H4 H5 H6 H7.
apply False_ind.
apply (lt_irrefl (proj1_sig (fst xy1))).
apply (lt_trans (proj1_sig (fst xy1)) (proj1_sig (snd xy1)) (proj1_sig (fst xy1)) H7).
rewrite H3.
rewrite H4.
apply H1.
elim (excluded_middle_informative (snd xy1 = y)).
move=> H3 H4 H5 H6 H7.
apply False_ind.
apply (lt_irrefl (proj1_sig x) H7).
move=> H3 H4 H5 H6 H7 H8.
apply False_ind.
apply (lt_irrefl (proj1_sig x)).
apply (lt_trans (proj1_sig x) (proj1_sig (fst xy1)) (proj1_sig x)).
rewrite H5.
apply H1.
apply (lt_trans (proj1_sig (fst xy1)) (proj1_sig (snd xy1)) (proj1_sig x) H8 H7).
elim (excluded_middle_informative (snd xy1 = x)).
move=> H3 H4 H5 H6 H7.
apply False_ind.
apply (lt_irrefl (proj1_sig y)).
apply (lt_trans (proj1_sig y) (proj1_sig x) (proj1_sig y)).
apply (lt_trans (proj1_sig y) (proj1_sig (fst xy1)) (proj1_sig x) H6).
rewrite - H3.
apply H7.
apply H1.
elim (excluded_middle_informative (snd xy1 = y)).
move=> H3 H4 H5 H6 H7 H8.
left.
right.
apply (Im_intro {n : nat | n < N} ({n : nat | n < N} * {n : nat | n < N}) (Intersection {n : nat | n < N} (fun k : {n : nat | n < N} => proj1_sig x < proj1_sig k < proj1_sig y) (Full_set {n : nat | n < N})) (fun k : {n : nat | n < N} => (k, y)) (fst xy1)).
apply Intersection_intro.
apply conj.
apply H7.
rewrite - H3.
apply H8.
apply Full_intro.
apply injective_projections.
reflexivity.
apply H3.
move=> H3 H4 H5 H6 H7 H8.
apply False_ind.
apply (lt_irrefl (proj1_sig (fst xy1)) (lt_trans (proj1_sig (fst xy1)) (proj1_sig (snd xy1)) (proj1_sig (fst xy1)) H8 H7)).
apply H2.
move=> xy.
elim.
move=> xy1.
elim.
move=> xy2.
elim.
move=> k H2 z H3.
apply Intersection_intro.
rewrite H3.
unfold PermutationSwap.
unfold In.
simpl.
elim (excluded_middle_informative (x = x)).
elim (excluded_middle_informative (k = x)).
move=> H4.
apply False_ind.
apply (lt_irrefl (proj1_sig k)).
rewrite {1} H4.
elim H2.
move=> k1 H5 H6.
apply (proj1 H5).
elim (excluded_middle_informative (k = y)).
move=> H4 H5 H6.
apply H1.
move=> H4 H5 H6.
elim H2.
move=> k1 H7 H8.
apply (proj2 H7).
move=> H4.
apply False_ind.
apply H4.
reflexivity.
rewrite H3.
elim H2.
move=> k1 H4 H5.
apply (proj1 H4).
move=> xy2.
elim.
move=> k H2 z H3.
apply Intersection_intro.
rewrite H3.
unfold PermutationSwap.
unfold In.
simpl.
elim (excluded_middle_informative (k = x)).
move=> H4.
apply False_ind.
apply (lt_irrefl (proj1_sig k)).
rewrite {1} H4.
elim H2.
move=> k1 H5 H6.
apply (proj1 H5).
elim (excluded_middle_informative (k = y)).
move=> H4.
apply False_ind.
apply (lt_irrefl (proj1_sig k)).
rewrite {2} H4.
elim H2.
move=> k1 H5 H6.
apply (proj2 H5).
elim (excluded_middle_informative (y = x)).
move=> H4.
apply False_ind.
apply (lt_irrefl (proj1_sig y)).
rewrite {1} H4.
apply H1.
elim (excluded_middle_informative (y = y)).
move=> H4 H5 H6 H7.
elim H2.
move=> k1 H8 H9.
apply (proj1 H8).
move=> H4.
apply False_ind.
apply H4.
reflexivity.
rewrite H3.
elim H2.
move=> k1 H4 H5.
apply (proj2 H4).
move=> xy1.
elim.
apply Intersection_intro.
unfold PermutationSwap.
unfold In.
simpl.
elim (excluded_middle_informative (x = x)).
elim (excluded_middle_informative (y = x)).
move=> H2.
apply False_ind.
apply (lt_irrefl (proj1_sig y)).
rewrite {1} H2.
apply H1.
elim (excluded_middle_informative (y = y)).
move=> H2 H3 H4.
apply H1.
move=> H2.
apply False_ind.
apply H2.
reflexivity.
move=> H2.
apply False_ind.
apply H2.
reflexivity.
apply H1.
move=> u.
elim.
move=> xy H2 H3.
elim (excluded_middle_informative (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy)) < proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy)))).
move=> H4.
reflexivity.
move=> H4.
apply False_ind.
elim (nat_total_order (proj1_sig (proj1_sig (PermutationSwap N x y) (fst xy))) (proj1_sig (proj1_sig (PermutationSwap N x y) (snd xy)))).
apply H4.
apply H2.
move=> H5.
apply (lt_irrefl (proj1_sig (fst xy))).
suff: (fst xy = snd xy).
move=> H6.
rewrite {2} H6.
apply H3.
apply (BijInj {n : nat | n < N} {n : nat | n < N} (proj1_sig (PermutationSwap N x y)) (proj2_sig (PermutationSwap N x y)) (fst xy) (snd xy)).
apply sig_map.
apply H5.
Qed.
