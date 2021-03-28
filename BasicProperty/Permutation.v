Add LoadPath "Tools" as Tools.
Add LoadPath "BasicProperty" as BasicProperty.

From mathcomp Require Import ssreflect.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Image.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.Mult.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Le.
Require Import Tools.MySum.
Require Import BasicProperty.MappingProperty.

Lemma CountAdd : forall (N M : nat), {f : {n : nat | n < N} + {n : nat | n < M} -> {n : nat | n < N + M} | Bijective f}.
Proof.
suff: (forall (N M : nat) (k : {n : nat | n < N}), proj1_sig k < N + M).
move=> H1.
suff: (forall (N M : nat) (k : {n : nat | n < M}), N + proj1_sig k < N + M).
move=> H2.
suff: (forall (N M : nat) (k : {n : nat | n < N + M}), ~ proj1_sig k < N -> proj1_sig k - N < M).
move=> H3 N M.
exists (fun (k : {n : nat | n < N} + {n : nat | n < M}) => match k with
  | inl l => exist (fun (n : nat) => n < N + M) (proj1_sig l) (H1 N M l)
  | inr l => exist (fun (n : nat) => n < N + M) (N + proj1_sig l) (H2 N M l)
end).
exists (fun (k : {n : nat | n < N + M}) => match excluded_middle_informative (proj1_sig k < N) with
  | left H => inl (exist (fun (n : nat) => n < N) (proj1_sig k) H)
  | right H => inr (exist (fun (n : nat) => n < M) (proj1_sig k - N) (H3 N M k H))
end).
apply conj.
elim.
move=> k.
elim (excluded_middle_informative (proj1_sig (exist (fun n : nat => n < N + M) (proj1_sig k) (H1 N M k)) < N)).
move=> H4.
simpl.
suff: ((exist (fun n : nat => n < N) (proj1_sig k) H4) = k).
move=> H5.
rewrite H5.
reflexivity.
apply sig_map.
reflexivity.
move=> H4.
apply False_ind.
apply H4.
apply (proj2_sig k).
move=> k.
elim (excluded_middle_informative (proj1_sig (exist (fun n : nat => n < N + M) (N + proj1_sig k) (H2 N M k)) < N)).
move=> H4.
apply False_ind.
apply (lt_irrefl N).
apply (le_trans (S N) (S (N + proj1_sig k)) N).
apply (le_n_S N (N + proj1_sig k)).
rewrite - {1} (plus_0_r N).
apply (plus_le_compat_l 0 (proj1_sig k) N (le_0_n (proj1_sig k))).
apply H4.
move=> H4.
simpl.
suff: ((exist (fun n : nat => n < M) (N + proj1_sig k - N) (H3 N M (exist (fun n : nat => n < N + M) (N + proj1_sig k) (H2 N M k)) H4)) = k).
move=> H5.
rewrite H5.
reflexivity.
apply sig_map.
simpl.
apply (minus_plus N (proj1_sig k)).
move=> k.
elim (excluded_middle_informative (proj1_sig k < N)).
move=> H4.
apply sig_map.
reflexivity.
move=> H4.
apply sig_map.
simpl.
apply (le_plus_minus_r N (proj1_sig k)).
elim (le_or_lt N (proj1_sig k)).
apply.
move=> H5.
apply False_ind.
apply (H4 H5).
move=> N M k H3.
apply (plus_lt_reg_l (proj1_sig k - N) M N).
rewrite (le_plus_minus_r N (proj1_sig k)).
apply (proj2_sig k).
elim (le_or_lt N (proj1_sig k)).
apply.
move=> H4.
apply False_ind.
apply (H3 H4).
apply (fun (N M : nat) (k : {n : nat | n < M}) => (plus_lt_compat_l (proj1_sig k) M N) (proj2_sig k)).
move=> N M k.
unfold lt.
rewrite - (plus_0_r (S (proj1_sig k))).
apply (plus_le_compat (S (proj1_sig k)) N 0 M (proj2_sig k) (le_0_n M)).
Qed.

Lemma CountMult : forall (N M : nat), {f : {n : nat | n < N} * {n : nat | n < M} -> {n : nat | n < N * M} | Bijective f}.
Proof.
move=> N M.
elim N.
exists (fun (xy : {n : nat | n < 0} * {n : nat | n < M}) => match (PeanoNat.Nat.nlt_0_r (proj1_sig (fst xy)) (proj2_sig (fst xy))) with
end).
suff: (forall (k : {n : nat | n < 0 * N}), False).
move=> H1.
exists (fun (k : {n : nat | n < 0 * N}) => match (H1 k) with
end).
apply conj.
move=> x.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig (fst x)) (proj2_sig (fst x))).
move=> y.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig y)).
rewrite - {2} (mult_0_l N).
apply (proj2_sig y).
rewrite (mult_0_l N).
apply (fun (k : {n : nat | n < 0}) => (PeanoNat.Nat.nlt_0_r (proj1_sig k) (proj2_sig k))).
simpl.
move=> K H1.
suff: {f : {n : nat | n < S K} * {n : nat | n < M} -> {n : nat | n < M} + {n : nat | n < K * M} | Bijective f}.
move=> H2.
exists (compose (proj1_sig (CountAdd M (K * M))) (proj1_sig H2)).
apply BijChain.
apply (proj2_sig H2).
apply (proj2_sig (CountAdd M (K * M))).
exists (fun (xy : {n : nat | n < S K} * {n : nat | n < M}) => match excluded_middle_informative (proj1_sig (fst xy) < K) with
  | left H => inr (proj1_sig H1 (exist (fun (k : nat) => k < K) (proj1_sig (fst xy)) H, snd xy))
  | right _ => inl (snd xy)
end).
elim (proj2_sig H1).
move=> g H2.
exists (fun (x : {n : nat | n < M} + {n : nat | n < K * M}) => match x with
  | inl k => (exist (fun (n : nat) => n < S K) K (le_n (S K)), k)
  | inr k => (exist (fun (n : nat) => n < S K) (proj1_sig (fst (g k))) (le_trans (S (proj1_sig (fst (g k)))) K (S K) (proj2_sig (fst (g k))) (le_S K K (le_n K))), snd (g k))
end).
apply conj.
move=> x.
elim (excluded_middle_informative (proj1_sig (fst x) < K)).
move=> H3.
apply injective_projections.
apply sig_map.
simpl.
rewrite (proj1 H2 (exist (fun k : nat => k < K) (proj1_sig (fst x)) H3, snd x)).
reflexivity.
simpl.
rewrite (proj1 H2 (exist (fun k : nat => k < K) (proj1_sig (fst x)) H3, snd x)).
reflexivity.
move=> H3.
apply injective_projections.
apply sig_map.
simpl.
elim (le_lt_or_eq (proj1_sig (fst x)) K).
move=> H4.
apply False_ind.
apply (H3 H4).
move=> H4.
rewrite H4.
reflexivity.
apply (le_S_n (proj1_sig (fst x)) K (proj2_sig (fst x))).
reflexivity.
elim.
simpl.
elim (excluded_middle_informative (K < K)).
move=> H3.
apply False_ind.
apply (lt_irrefl K H3).
move=> H3 H4.
reflexivity.
simpl.
move=> k.
elim (excluded_middle_informative (proj1_sig (fst (g k)) < K)).
move=> H4.
suff: ((proj1_sig H1 (exist (fun n : nat => n < K) (proj1_sig (fst (g k))) H4, snd (g k))) = k).
move=> H5.
rewrite H5.
reflexivity.
suff: ((exist (fun n : nat => n < K) (proj1_sig (fst (g k))) H4, snd (g k)) = g k).
move=> H5.
rewrite H5.
apply (proj2 H2 k).
apply injective_projections.
suff: (exist (fun n : nat => n < K) (proj1_sig (fst (g k))) H4 = fst (g k)).
move=> H5.
rewrite H5.
reflexivity.
apply sig_map.
reflexivity.
reflexivity.
move=> H3.
apply False_ind.
apply (H3 (proj2_sig (fst (g k)))).
Qed.

Lemma CountPow : forall (N M : nat), {f : ({n : nat | n < N} -> {n : nat | n < M}) -> {n : nat | n < M ^ N} | Bijective f}.
Proof.
move=> N M.
elim N.
simpl.
exists (fun (_ : {n : nat | n < 0} -> {n : nat | n < M}) => exist (fun (n : nat) => n < S O) O (le_n (S O))).
exists (fun (m : {n : nat | n < S O}) (k : {n : nat | n < O}) => match (PeanoNat.Nat.nlt_0_r (proj1_sig k) (proj2_sig k)) with
end).
apply conj.
move=> x.
apply functional_extensionality.
move=> k.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig k) (proj2_sig k)).
move=> y.
apply sig_map.
simpl.
elim (le_lt_or_eq (proj1_sig y) O).
move=> H1.
apply False_ind.
apply (PeanoNat.Nat.nlt_0_r (proj1_sig y) H1).
move=> H1.
rewrite H1.
reflexivity.
apply (le_S_n (proj1_sig y) O (proj2_sig y)).
move=> K.
elim.
move=> f1 H1.
simpl.
suff: ({f : ({n : nat | n < S K} -> {n : nat | n < M}) -> ({n : nat | n < M} * {n : nat | n < M ^ K}) | Bijective f}).
elim.
move=> f2 H2.
exists (compose (proj1_sig (CountMult M (M ^ K))) f2).
apply BijChain.
apply H2.
apply (proj2_sig (CountMult M (M ^ K))).
exists (fun (x : {n : nat | n < S K} -> {n : nat | n < M}) => (x (exist (fun (n : nat) => n < S K) K (le_n (S K))), f1 (fun (m : {n : nat | n < K}) => x (exist (fun (n : nat) => n < S K) (proj1_sig m) (le_trans (S (proj1_sig m)) K (S K) (proj2_sig m) (le_S K K (le_n K))))))).
elim H1.
move=> g1 H2.
exists (fun (x : {n : nat | n < M} * {n : nat | n < M ^ K}) (k : {n : nat | n < S K}) => match excluded_middle_informative (proj1_sig k < K) with
  | left H => g1 (snd x) (exist (fun (n : nat) => n < K) (proj1_sig k) H)
  | right H => fst x
end).
apply conj.
move=> x.
apply functional_extensionality.
move=> k.
elim (excluded_middle_informative (proj1_sig k < K)).
move=> H3.
simpl.
rewrite (proj1 H2 (fun m : {n : nat | n < K} => x (exist (fun n : nat => n < S K) (proj1_sig m) (Nat.le_trans (S (proj1_sig m)) K (S K) (proj2_sig m) (le_S K K (le_n K)))))).
suff: ((exist (fun n : nat => n < S K) (proj1_sig (exist (fun n : nat => n < K) (proj1_sig k) H3)) (Nat.le_trans (S (proj1_sig (exist (fun n : nat => n < K) (proj1_sig k) H3))) K (S K) (proj2_sig (exist (fun n : nat => n < K) (proj1_sig k) H3)) (le_S K K (le_n K)))) = k).
move=> H4.
rewrite H4.
reflexivity.
apply sig_map.
reflexivity.
move=> H3.
suff: ((exist (fun n : nat => n < S K) K (le_n (S K))) = k).
move=> H4.
rewrite H4.
reflexivity.
apply sig_map.
elim (le_lt_or_eq (proj1_sig k) K (le_S_n (proj1_sig k) K (proj2_sig k))).
move=> H4.
apply False_ind.
apply (H3 H4).
move=> H4.
rewrite H4.
reflexivity.
move=> y.
simpl.
elim (excluded_middle_informative (K < K)).
move=> H3.
apply False_ind.
apply (lt_irrefl K H3).
move=> H3.
apply injective_projections.
reflexivity.
apply (BijInj {n : nat | n < M ^ K} ({n : nat | n < K} -> {n : nat | n < M}) g1).
exists f1.
apply conj.
apply (proj2 H2).
apply (proj1 H2).
simpl.
rewrite (proj1 H2 (fun m : {n : nat | n < K} => match excluded_middle_informative (proj1_sig m < K) with
  | left H => g1 (snd y) (exist (fun n : nat => n < K) (proj1_sig m) H)
  | right _ => fst y
end)).
apply functional_extensionality.
move=> k.
elim (excluded_middle_informative (proj1_sig k < K)).
move=> H4.
suff: ((exist (fun n : nat => n < K) (proj1_sig k) H4) = k).
move=> H5.
rewrite H5.
reflexivity.
apply sig_map.
reflexivity.
move=> H4.
apply False_ind.
apply (H4 (proj2_sig k)).
Qed.

Inductive Parity :=
  | ON : Parity
  | OFF : Parity.

Definition ParityXOR (x y : Parity) := match x with
  | ON => match y with
    | ON => OFF
    | OFF => ON
  end
  | OFF => match y with
    | ON => ON
    | OFF => OFF
  end
end.

Lemma ParityXOR_comm : forall (x y : Parity), ParityXOR x y = ParityXOR y x.
Proof.
elim.
elim.
reflexivity.
reflexivity.
elim.
reflexivity.
reflexivity.
Qed.

Lemma ParityXOR_O_r : forall (x : Parity), ParityXOR x OFF = x.
Proof.
elim.
reflexivity.
reflexivity.
Qed.

Lemma ParityXOR_assoc : forall (x y z : Parity), ParityXOR (ParityXOR x y) z = ParityXOR x (ParityXOR y z).
Proof.
elim.
elim.
elim.
reflexivity.
reflexivity.
elim.
reflexivity.
reflexivity.
elim.
elim.
reflexivity.
reflexivity.
elim.
reflexivity.
reflexivity.
Qed.

Definition ParityXORCM := mkCommutativeMonoid Parity OFF ParityXOR ParityXOR_comm ParityXOR_O_r ParityXOR_assoc.

Definition Permutation (N : nat) := {f : {n : nat | n < N} -> {n : nat | n < N} | Bijective f}.

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

Definition PermutationCompose (N : nat) (f g : Permutation N) := exist (fun (h : {n : nat | n < N} -> {n : nat | n < N}) => Bijective h) (compose (proj1_sig f) (proj1_sig g)) (BijChain {n : nat | n < N} {n : nat | n < N} {n : nat | n < N} (proj1_sig g) (proj1_sig f) (proj2_sig g) (proj2_sig f)).

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
