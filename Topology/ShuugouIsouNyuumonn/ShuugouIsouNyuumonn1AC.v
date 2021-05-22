Add LoadPath "Tools" as Tools.
Add LoadPath "BasicProperty" as BasicProperty.
Add LoadPath "LibraryExtension" as LibraryExtension.
Add LoadPath "Topology/ShuugouIsouNyuumonn" as Topology.ShuugouIsouNyuumonn.

From mathcomp Require Import ssreflect.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Program.Basics.
Require Import Topology.ShuugouIsouNyuumonn.ShuugouIsouNyuumonn1.
Require Import BasicProperty.MappingProperty.

Lemma Formula_P47_2 : forall (U : Type) (T : U -> Type) (A : forall (u : U), Ensemble (T u)), (forall (u : U), A u <> Empty_set (T u)) -> ProductionEnsemble U T A <> Empty_set (forall (u : U), T u).
Proof.
move=> U T A H1 H2.
suff: (forall (u : U), {t : T u | In (T u) (A u) t}).
move=> H3.
suff: (In (forall (u : U), T u) (ProductionEnsemble U T A) (fun (u : U) => proj1_sig (H3 u))).
rewrite H2.
elim.
apply (ProductionEnsemble_intro U T A).
apply (fun (u : U) => proj2_sig (H3 u)).
move=> u.
apply constructive_indefinite_description.
apply NNPP.
move=> H3.
apply (H1 u).
apply Extensionality_Ensembles.
apply conj.
move=> u0 H4.
apply False_ind.
apply H3.
exists u0.
apply H4.
move=> u0.
elim.
Qed.

Lemma Theorem_7_1_1 : forall (U T : Type) (f : U -> T), Surjective f -> exists (g : T -> U), compose f g = (fun (t : T) => t).
Proof.
move=> U T f H1.
suff: (forall (t : T), {u : U | f u = t}).
move=> H2.
exists (fun (t : T) => proj1_sig (H2 t)).
apply functional_extensionality.
move=> t.
apply (proj2_sig (H2 t)).
move=> t.
apply constructive_indefinite_description.
apply (H1 t).
Qed.

Lemma Theorem_7_corollary_2 : forall (U T : Type), (exists (f : U -> T), Surjective f) -> (exists (g : T -> U), Injective g).
Proof.
move=> U T.
elim.
move=> f H1.
elim (Theorem_7_1_1 U T f H1).
move=> g H2.
exists g.
apply (Theorem_7_2_2 T U g).
exists f.
apply H2.
Qed.
