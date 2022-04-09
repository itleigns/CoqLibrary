Add LoadPath "Analysis/KaisekiNyuumonn" as Analysis.KaisekiNyuumonn.
Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "Tools" as Tools.
Add LoadPath "BasicProperty" as BasicProperty.
Add LoadPath "LibraryExtension" as LibraryExtension.
Add LoadPath "Topology/ShuugouIsouNyuumonn" as Topology.ShuugouIsouNyuumonn.
Add LoadPath "LibraryExtension" as LibraryExtension.
Add LoadPath "Topology/ShuugouIsouNyuumonn" as Topology.ShuugouIsouNyuumonn.

From mathcomp Require Import ssreflect.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Image.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Tools.MySum.
Require Import Tools.BasicTools.
Require Import BasicProperty.MappingProperty.
Require Import LibraryExtension.DatatypesExtension.
Require Import Topology.ShuugouIsouNyuumonn.ShuugouIsouNyuumonn1.
Require Import Topology.ShuugouIsouNyuumonn.ShuugouIsouNyuumonn1AC.
Require Import Topology.ShuugouIsouNyuumonn.ShuugouIsouNyuumonn2.

Lemma Theorem_2_dash : forall (A B : Type), (exists (f : A -> B), Injective f) ->
       (exists (g : A -> B), Surjective g) -> SameCard A B.
Proof.
move=> A B H1 H2.
apply (Theorem_2 A B H1 (Theorem_7_corollary_2 A B H2)).
Qed.

Lemma Theorem_2_dash_dash : forall (A B : Type), (exists (f : A -> B), Surjective f) ->
       (exists (g : B -> A), Surjective g) -> SameCard A B.
Proof.
move=> A B H1 H2.
apply (Theorem_2 A B (Theorem_7_corollary_2 B A H2) (Theorem_7_corollary_2 A B H1)).
Qed.

Lemma cardLeDef3 : forall (A B : Type), A -> cardLe A B <-> exists (f : B -> A), Surjective f.
Proof.
move=> A B a.
apply conj.
move=> H1.
apply (Theorem_7_corollary_1 A B a H1).
move=> H1.
apply (Theorem_7_corollary_2 B A H1).
Qed.

Lemma Theorem_4 : forall (T : Type), ~ Finite T (Full_set T) -> exists (A : Ensemble T), SameCard {t : T | In T A t} nat.
Proof.
move=> T H1.
suff: (forall (A : {B : Ensemble T | ~ Finite T B}), {t : T | In T (proj1_sig A) t}).
move=> H2.
suff: (forall (A : Ensemble T) (t : T), In T A t -> ~ Finite T A -> ~ Finite T (Subtract T A t)).
move=> H3.
suff: (let F := fix F (n : nat) : (T * {B : Ensemble T | ~ Finite T B}) := match n with
  | O => (proj1_sig (H2 (exist (fun (A : Ensemble T) => ~ Finite T A) (Full_set T) H1)), (exist (fun (A : Ensemble T) => ~ Finite T A) (Subtract T (Full_set T) (proj1_sig (H2 (exist (fun (A : Ensemble T) => ~ Finite T A) (Full_set T) H1)))) (H3 (Full_set T) (proj1_sig (H2 (exist (fun (A : Ensemble T) => ~ Finite T A) (Full_set T) H1))) (proj2_sig (H2 (exist (fun (A : Ensemble T) => ~ Finite T A) (Full_set T) H1))) H1)))
  | S n => (proj1_sig (H2 (snd (F n))), (exist (fun (A : Ensemble T) => ~ Finite T A) (Subtract T (proj1_sig (snd (F n))) (proj1_sig (H2 (snd (F n))))) (H3 (proj1_sig (snd (F n))) (proj1_sig (H2 (snd (F n)))) (proj2_sig (H2 (snd (F n)))) (proj2_sig (snd (F n))))))
end in exists (A : Ensemble T), SameCard {t : T | In T A t} nat).
apply.
move=> F.
exists (Im nat T (Full_set nat) (fun (n : nat) => fst (F n))).
apply Formula_1_2.
exists (fun (m : nat) => exist (Im nat T (Full_set nat) (fun (n : nat) => fst (F n))) (fst (F m)) (Im_intro nat T (Full_set nat) (fun (n : nat) => fst (F n)) m (Full_intro nat m) (fst (F m)) eq_refl)).
apply InjSurjBij.
suff: (forall (m1 m2 : nat), m1 <= m2 -> Included T (proj1_sig (snd (F m2))) (proj1_sig (snd (F m1)))).
move=> H4.
suff: (forall (m1 m2 : nat), m1 < m2 -> fst (F m1) <> fst (F m2)).
move=> H5 m1 m2 H6.
elim (le_or_lt m1 m2).
move=> H7.
elim (le_lt_or_eq m1 m2 H7).
move=> H8.
elim (H5 m1 m2 H8).
suff: (fst (F m1) = proj1_sig (exist (Im nat T (Full_set nat) (fun (n : nat) => fst (F n))) 
       (fst (F m1))
       (Im_intro nat T (Full_set nat) (fun (n : nat) => fst (F n)) m1
          (Full_intro nat m1) (fst (F m1)) eq_refl))).
move=> H9.
rewrite H9.
rewrite H6.
reflexivity.
reflexivity.
apply.
move=> H7.
elim (H5 m2 m1 H7).
suff: (fst (F m1) = proj1_sig (exist (Im nat T (Full_set nat) (fun (n : nat) => fst (F n))) 
       (fst (F m1))
       (Im_intro nat T (Full_set nat) (fun (n : nat) => fst (F n)) m1
          (Full_intro nat m1) (fst (F m1)) eq_refl))).
move=> H8.
rewrite H8.
rewrite H6.
reflexivity.
reflexivity.
move=> m1 m2 H5 H6.
suff: (~ In T (proj1_sig (snd (F m1))) (fst (F m1))).
elim.
suff: (exists (n : nat), m2 = S n).
elim.
move=> n H7.
apply (H4 m1 n).
apply (le_S_n m1 n).
rewrite - H7.
apply H5.
rewrite H6.
rewrite H7.
apply (proj2_sig (H2 (snd (F n)))).
suff: (m1 < m2).
elim m2.
move=> H7.
elim (le_not_lt O m1 (le_0_n m1) H7).
move=> k H7 H8.
exists k.
reflexivity.
apply H5.
elim m1.
move=> H7.
apply (proj2 H7).
apply (In_singleton T).
move=> n H7 H8.
apply (proj2 H8).
apply (In_singleton T).
move=> m1 m2.
elim.
move=> t H4.
apply H4.
move=> m3 H4 H5 t H6.
apply (H5 t).
apply (proj1 H6).
move=> t.
suff: (exists (n : nat), fst (F n) = proj1_sig t).
elim.
move=> n H4.
exists n.
apply sig_map.
apply H4.
elim (proj2_sig t).
move=> x H4 y H5.
exists x.
rewrite H5.
reflexivity.
move=> A t H3 H4 H5.
apply H4.
suff: (A = Add T (Subtract T A t) t).
move=> H6.
rewrite H6.
apply (Union_is_finite T (Subtract T A t) H5 t).
move=> H7.
apply (proj2 H7).
apply (In_singleton T t).
apply Extensionality_Ensembles.
apply conj.
move=> a H6.
elim (classic (t = a)).
move=> H7.
right.
rewrite H7.
apply (In_singleton T a).
move=> H7.
left.
apply conj.
apply H6.
move=> H8.
apply H7.
elim H8.
reflexivity.
move=> a.
elim.
move=> t0 H6.
apply (proj1 H6).
move=> t0.
elim.
apply H3.
move=> A.
apply constructive_indefinite_description.
apply NNPP.
move=> H2.
apply (proj2_sig A).
suff: (proj1_sig A = Empty_set T).
move=> H3.
rewrite H3.
apply (Empty_is_finite T).
apply Extensionality_Ensembles.
apply conj.
move=> t H3.
elim H2.
exists t.
apply H3.
move=> t.
elim.
Qed.

Lemma Theorem_4_corollary : forall (C : CardT), InfiniteCard C -> CardLe (Card nat) C.
Proof.
move=> C H1.
elim (proj2_sig C).
move=> T H2.
rewrite - (CardLeNature nat T (Card nat) C (ERref Type CardEquivalence nat)).
apply (proj2 (cardLeDef2 nat T)).
elim (Theorem_4 T).
move=> B H3.
exists B.
apply (Formula_1_2 {t : T | In T B t} nat H3).
move=> H3.
apply H1.
elim (finite_cardinal T (Full_set T) H3).
move=> n H4.
exists n.
suff: (C = EquivalenceRelationQuotientFunction Type CardEquivalence T).
move=> H5.
rewrite H5.
apply (Formula_66_1 T (Count n)).
apply (Formula_1_2 (Count n) T (proj2 (CountCardinalBijective T n) H4)).
apply sig_map.
apply H2.
rewrite H2.
apply (Formula_1_1 T).
Qed.

Lemma Theorem_5_2_1 : forall (T : Type) (Ti : T -> Type), cardLe T nat -> (forall (t : T), cardLe (Ti t) nat) -> cardLe (sumT T Ti) nat.
Proof.
move=> T Ti.
elim.
move=> f H1 H2.
suff: (forall (t : T), {fi : Ti t -> nat | Injective fi}).
move=> H3.
elim (Formula_1_2 nat (nat * nat) Example_3).
move=> g H4.
exists (fun (x : sumT T Ti) => match x with
  | inT t tf => g (f t, proj1_sig (H3 t) tf)
end).
suff: (forall (t1 t2 : T), (t1 = t2) -> forall (tf1 : Ti t1) (tf2 : Ti t2), proj1_sig (H3 t1) tf1 = proj1_sig (H3 t2) tf2 -> inT T Ti t1 tf1 = inT T Ti t2 tf2).
move=> H5 x1 x2.
elim x1.
move=> t1 tf1.
elim x2.
move=> t2 tf2 H6.
apply (H5 t1 t2).
apply (H1 t1 t2).
suff: (f t1 = fst (f t1, proj1_sig (H3 t1) tf1)).
move=> H7.
rewrite H7.
rewrite (BijInj (nat * nat) nat g H4 (f t1, proj1_sig (H3 t1) tf1) (f t2, proj1_sig (H3 t2) tf2) H6).
reflexivity.
reflexivity.
suff: (proj1_sig (H3 t1) tf1 = snd (f t1, proj1_sig (H3 t1) tf1)).
move=> H7.
rewrite H7.
rewrite (BijInj (nat * nat) nat g H4 (f t1, proj1_sig (H3 t1) tf1) (f t2, proj1_sig (H3 t2) tf2) H6).
reflexivity.
reflexivity.
move=> t1 t2 H5.
rewrite H5.
move=> tf1 tf2 H6.
rewrite (proj2_sig (H3 t2) tf1 tf2 H6).
reflexivity.
move=> t.
apply constructive_indefinite_description.
apply (H2 t).
Qed.

Lemma Theorem_5_2_2 : forall (T : Type) (Ti : T -> Type), cardLe T nat -> (forall (t : T), cardLe (Ti t) nat) -> (exists (t : T), SameCard (Ti t) nat) -> SameCard (sumT T Ti) nat.
Proof.
move=> T Ti H1 H2 H3.
apply (Theorem_2 (sumT T Ti) nat).
apply (Theorem_5_2_1 T Ti H1 H2).
elim H3.
move=> t H4.
elim (Formula_1_2 (Ti t) nat H4).
move=> f H5.
exists (fun (n : nat) => inT T Ti t (f n)).
move=> n1 n2 H6.
apply (BijInj nat (Ti t) f H5 n1 n2).
suff: (f n1 = let temp := inT T Ti t (f n1) in match temp with
  | inT t0 tf0 => match excluded_middle_informative (t0 = t) with
    | left H => TypeEqConvert (Ti t0) (Ti t) (f_equal Ti H) tf0
    | right _ => f n1
  end
end).
move=> H7.
rewrite H7.
rewrite H6.
simpl.
elim (excluded_middle_informative (t = t)).
move=> H8.
apply (TypeEqConvertNature (Ti t) (f_equal Ti H8) (f n2)).
elim.
reflexivity.
simpl.
elim (excluded_middle_informative (t = t)).
move=> H7.
rewrite (TypeEqConvertNature (Ti t) (f_equal Ti H7) (f n1)).
reflexivity.
elim.
reflexivity.
Qed.

Lemma Theorem_6 : forall (T : Type) (A : Ensemble T), ~ Finite T (Complement T A) -> cardLe {t : T | In T A t} nat -> SameCard T {t : T | ~ In T A t}.
Proof.
move=> T A H1 H2.
suff: (exists (B : Ensemble T), SameCard {t : T | ~ In T A t /\ In T B t} nat).
elim.
move=> B H3.
suff: (SameCard {t : T | In T A t \/ In T B t} {t : T | ~ In T A t /\ In T B t}).
elim.
move=> f.
elim.
move=> g H4.
suff: (forall (t : T), ~ (In T A t \/ In T B t) -> ~ In T A t).
move=> H5.
exists (fun (t : T) => match excluded_middle_informative (In T A t \/ In T B t) with
  | left H => exist (fun (t : T) => ~ In T A t) (proj1_sig (f (exist (fun (t : T) => In T A t \/ In T B t) t H))) (proj1 (proj2_sig (f (exist (fun (t : T) => In T A t \/ In T B t) t H))))
  | right H => exist (fun (t : T) => ~ In T A t) t (H5 t H)
end).
exists (fun (t : {t : T | ~ In T A t}) => match excluded_middle_informative (In T B (proj1_sig t)) with
  | left H => proj1_sig (g (exist (fun (t : T) => ~ In T A t /\ In T B t) (proj1_sig t) (conj (proj2_sig t) H)))
  | right _ => proj1_sig t
end).
apply conj.
move=> x.
elim (excluded_middle_informative (In T A x \/ In T B x)).
move=> H6.
simpl.
elim (excluded_middle_informative
    (In T B (proj1_sig (f (exist (fun (t : T) => In T A t \/ In T B t) x H6))))).
move=> H7.
suff: ((exist (fun (t : T) => ~ In T A t /\ In T B t)
        (proj1_sig (f (exist (fun (t : T) => In T A t \/ In T B t) x H6)))
        (conj
           (proj1
              (proj2_sig (f (exist (fun (t : T) => In T A t \/ In T B t) x H6))))
           H7)) = (f (exist (fun (t : T) => In T A t \/ In T B t) x H6))).
move=> H8.
rewrite H8.
rewrite (proj1 H4).
reflexivity.
apply sig_map.
reflexivity.
elim.
apply (proj2 (proj2_sig (f (exist (fun (t : T) => In T A t \/ In T B t) x H6)))).
move=> H6.
elim (excluded_middle_informative
    (In T B (proj1_sig (exist (fun (t : T) => ~ In T A t) x (H5 x H6))))).
move=> H7.
elim H6.
right.
apply H7.
move=> H7.
reflexivity.
move=> y.
elim (excluded_middle_informative (In T B (proj1_sig y))).
move=> H6.
elim (excluded_middle_informative
    (In T A
       (proj1_sig
          (g
             (exist (fun (t : T) => ~ In T A t /\ In T B t) 
                (proj1_sig y) (conj (proj2_sig y) H6)))) \/
     In T B
       (proj1_sig
          (g
             (exist (fun (t : T) => ~ In T A t /\ In T B t) 
                (proj1_sig y) (conj (proj2_sig y) H6)))))).
move=> H7.
suff: ((exist (fun (t : T) => In T A t \/ In T B t)
           (proj1_sig
              (g
                 (exist (fun (t : T) => ~ In T A t /\ In T B t) 
                    (proj1_sig y) (conj (proj2_sig y) H6)))) H7) = (g
                 (exist (fun (t : T) => ~ In T A t /\ In T B t) 
                    (proj1_sig y) (conj (proj2_sig y) H6)))).
move=> H8.
rewrite H8.
rewrite (proj2 H4).
apply sig_map.
reflexivity.
apply sig_map.
reflexivity.
elim.
apply (proj2_sig
     (g
        (exist (fun (t : T) => ~ In T A t /\ In T B t) 
           (proj1_sig y) (conj (proj2_sig y) H6)))).
move=> H6.
elim (excluded_middle_informative (In T A (proj1_sig y) \/ In T B (proj1_sig y))).
move=> H7.
elim H6.
elim H7.
move=> H8.
elim ((proj2_sig y) H8).
apply.
move=> H7.
apply sig_map.
reflexivity.
move=> t H5 H6.
apply H5.
left.
apply H6.
apply (Formula_1_3 {t : T | In T A t \/ In T B t} nat {t : T | ~ In T A t /\ In T B t}).
apply (Theorem_2 {t : T | In T A t \/ In T B t} nat).
elim (Formula_1_2 nat (nat * nat) Example_3).
move=> f H4.
elim H2.
move=> g H5.
elim H3.
move=> h H6.
suff: (forall (t : {t : T | In T A t \/ In T B t}), ~ In T A (proj1_sig t) -> ~ In T A (proj1_sig t) /\ In T B (proj1_sig t)).
move=> H7.
exists (fun (t : {t : T | In T A t \/ In T B t}) => match excluded_middle_informative (In T A (proj1_sig t)) with
  | left H => f (g (exist A (proj1_sig t) H), O)
  | right H => f (h (exist (fun (t : T) => ~ In T A t /\ In T B t) (proj1_sig t) (H7 t H)), 1)
end).
move=> t1 t2.
elim (excluded_middle_informative (In T A (proj1_sig t1))).
move=> H8.
elim (excluded_middle_informative (In T A (proj1_sig t2))).
move=> H9 H10.
apply sig_map.
suff: (proj1_sig t1 = proj1_sig (exist A (proj1_sig t1) H8)).
move=> H11.
rewrite H11.
rewrite (H5 (exist A (proj1_sig t1) H8) (exist A (proj1_sig t2) H9)).
reflexivity.
suff: (g (exist A (proj1_sig t1) H8) = fst (g (exist A (proj1_sig t1) H8), 0)).
move=> H12.
rewrite H12.
rewrite (BijInj (nat * nat) nat f H4 (g (exist A (proj1_sig t1) H8), 0) (g (exist A (proj1_sig t2) H9), 0) H10).
reflexivity.
reflexivity.
reflexivity.
move=> H9 H10.
elim (lt_irrefl (snd (g (exist A (proj1_sig t1) H8), 0))).
rewrite {2} (BijInj (nat * nat) nat f H4 (g (exist A (proj1_sig t1) H8), 0) (h
           (exist (fun t : T => ~ In T A t /\ In T B t) 
              (proj1_sig t2) (H7 t2 H9)), 1) H10).
apply (le_n 1).
move=> H8.
elim (excluded_middle_informative (In T A (proj1_sig t2))).
move=> H9 H10.
elim (lt_irrefl (snd (h
           (exist (fun (t : T) => ~ In T A t /\ In T B t) 
              (proj1_sig t1) (H7 t1 H8)), 1))).
rewrite {1} (BijInj (nat * nat) nat f H4 (h
           (exist (fun (t : T) => ~ In T A t /\ In T B t) 
              (proj1_sig t1) (H7 t1 H8)), 1) (g (exist A (proj1_sig t2) H9), 0) H10).
apply (le_n 1).
move=> H9 H10.
apply sig_map.
suff: (proj1_sig t1 = proj1_sig (exist (fun (t : T) => ~ In T A t /\ In T B t) 
              (proj1_sig t1) (H7 t1 H8))).
move=> H11.
rewrite H11.
rewrite (BijInj {t : T | ~ In T A t /\ In T B t} nat h H6 (exist (fun (t : T) => ~ In T A t /\ In T B t) 
              (proj1_sig t1) (H7 t1 H8)) (exist (fun (t : T) => ~ In T A t /\ In T B t) 
              (proj1_sig t2) (H7 t2 H9))).
reflexivity.
suff: (h (exist (fun (t : T) => ~ In T A t /\ In T B t) (proj1_sig t1) (H7 t1 H8)) = fst (h
           (exist (fun (t : T) => ~ In T A t /\ In T B t) 
              (proj1_sig t1) (H7 t1 H8)), 1)).
move=> H12.
rewrite H12.
rewrite (BijInj (nat * nat) nat f H4 (h
           (exist (fun (t : T) => ~ In T A t /\ In T B t) 
              (proj1_sig t1) (H7 t1 H8)), 1) (h
           (exist (fun (t : T) => ~ In T A t /\ In T B t) 
              (proj1_sig t2) (H7 t2 H9)), 1) H10).
reflexivity.
reflexivity.
reflexivity.
move=> t H7.
apply conj.
apply H7.
elim (proj2_sig t).
move=> H8.
elim (H7 H8).
apply.
elim (Formula_1_2 {t : T | ~ In T A t /\ In T B t} nat H3).
move=> f H4.
suff: (forall (n : nat), In T A (proj1_sig (f n)) \/ In T B (proj1_sig (f n))).
move=> H5.
exists (fun (n : nat) => exist (fun (t : T) => In T A t \/ In T B t) (proj1_sig (f n)) (H5 n)).
move=> n1 n2 H6.
apply (BijInj nat {t : T | ~ In T A t /\ In T B t} f H4 n1 n2).
apply sig_map.
suff: (proj1_sig (f n1) = proj1_sig (exist (fun (t : T) => In T A t \/ In T B t) (proj1_sig (f n1)) (H5 n1))).
move=> H7.
rewrite H7.
rewrite H6.
reflexivity.
reflexivity.
move=> n.
right.
apply (proj2 (proj2_sig (f n))).
apply (Formula_1_2 {t : T | ~ In T A t /\ In T B t} nat H3).
elim (Theorem_4 {t : T | In T (Complement T A) t}).
move=> B.
elim.
move=> f H3.
exists (fun (t : T) => match excluded_middle_informative (In T A t) with
  | left _ => False
  | right H => In {t : T | In T (Complement T A) t} B (exist (Complement T A) t H)
end).
suff: (forall (t : {t : T
  | ~ In T A t /\
    In T
      (fun (t0 : T) =>
       match excluded_middle_informative (In T A t0) with
       | left _ => False
       | right H =>
           In {t1 : T | In T (Complement T A) t1} B
             (exist (Complement T A) t0 H)
       end) t}), In T (Complement T A) (proj1_sig t)).
move=> H4.
suff: (forall (t : {t : T
  | ~ In T A t /\
    In T
      (fun (t0 : T) =>
       match excluded_middle_informative (In T A t0) with
       | left _ => False
       | right H =>
           In {t1 : T | In T (Complement T A) t1} B
             (exist (Complement T A) t0 H)
       end) t}), In {t0 : T | In T (Complement T A) t0} B (exist
(Complement T A) (proj1_sig t)
(H4 t))).
move=> H5.
exists (fun (t : {t : T
  | ~ In T A t /\
    In T
      (fun (t0 : T) =>
       match excluded_middle_informative (In T A t0) with
       | left _ => False
       | right H =>
           In {t1 : T | In T (Complement T A) t1} B
             (exist (Complement T A) t0 H)
       end) t}) => f (exist B (exist
(Complement T A) (proj1_sig t)
(H4 t)) (H5 t))).
elim H3.
move=> g H6.
suff: (forall (n : nat), In T (fun (t : T) => ~ In T A t /\
    In T
      (fun (t0 : T) =>
       match excluded_middle_informative (In T A t0) with
       | left _ => False
       | right H =>
           In {t1 : T | In T (Complement T A) t1} B
             (exist (Complement T A) t0 H)
       end) t) (proj1_sig (proj1_sig (g n)))).
move=> H7.
exists (fun (n : nat) => exist (fun (t : T) => ~ In T A t /\
    In T
      (fun (t0 : T) =>
       match excluded_middle_informative (In T A t0) with
       | left _ => False
       | right H =>
           In {t1 : T | In T (Complement T A) t1} B
             (exist (Complement T A) t0 H)
       end) t) (proj1_sig (proj1_sig (g n))) (H7 n)).
apply conj.
move=> x.
apply sig_map.
simpl.
rewrite (proj1 H6).
reflexivity.
move=> y.
simpl.
rewrite - {6} (proj2 H6 y).
apply (f_equal f).
apply sig_map.
apply sig_map.
reflexivity.
move=> n.
unfold In.
apply conj.
apply (proj2_sig (proj1_sig (g n))).
elim (excluded_middle_informative (A
       (@proj1_sig T (fun (t : T) => Complement T A t)
          (@proj1_sig (@sig T (fun (t : T) => Complement T A t))
             (fun (t : @sig T (fun (t : T) => Complement T A t)) => B t) 
             (g n))))).
move=> H7.
elim (proj2_sig (proj1_sig (g n)) H7).
move=> H7.
suff: ((exist (Complement T A) (proj1_sig (proj1_sig (g n))) H7) = proj1_sig (g n)).
move=> H8.
rewrite H8.
apply (proj2_sig (g n)).
apply sig_map.
reflexivity.
move=> t.
suff: (In T (fun (t0 : T) =>
         match excluded_middle_informative (In T A t0) with
         | left _ => False
         | right H =>
             In {t1 : T | In T (Complement T A) t1} B
               (exist (Complement T A) t0 H)
         end) (proj1_sig t)).
unfold In.
elim (excluded_middle_informative (A
             (@proj1_sig T
                (fun (t0 : T) =>
                 and (not (A t0))
                   match excluded_middle_informative (A t0) return Prop with
                   | left _ => False
                   | right H => B (@exist T (Complement T A) t0 H)
                   end) t))).
move=> H5.
elim.
move=> H5.
suff: (H5 = H4 t).
move=> H6.
rewrite H6.
apply.
apply proof_irrelevance.
apply (proj2 (proj2_sig t)).
move=> t.
apply (proj1 (proj2_sig t)).
move=> H3.
apply H1.
apply (proj2 (FiniteSigSame T (Complement T A)) H3).
Qed.

Lemma Theorem_6_corollary_1 : forall (T1 T2 : Type), ~ Finite T1 (Full_set T1) -> cardLe T2 nat -> SameCard T1 (T1 + T2).
Proof.
move=> T1 T2 H1 H2.
elim (Theorem_6 (T1 + T2) (fun (t : T1 + T2) => match t with
  | inl _ => False
  | inr _ => True
end)).
move=> f.
elim.
move=> g H3.
exists (fun (t : T1) => g (exist (fun (t0 : T1 + T2) => ~ match t0 with
                             | inl _ => False
                             | inr _ => True
                             end) (inl t) (fun (b : False) => b))).
exists (let temp : forall (t : T1 + T2), ~
      In (T1 + T2)
        (fun (t0 : T1 + T2) => match t0 with
                             | inl _ => False
                             | inr _ => True
                             end) t -> T1 := (fun (t : T1 + T2) => match t with
  | inl t0 => fun (H : False -> False) => t0
  | inr t0 => fun (H : True -> False) => match H I with
  end
end) in fun (t : T1 + T2) => temp (proj1_sig (f t)) (proj2_sig (f t))).
apply conj.
move=> t.
simpl.
rewrite (proj2 H3).
reflexivity.
move=> t.
rewrite - {2} (proj1 H3 t).
apply (f_equal g).
apply sig_map.
simpl.
suff: (forall (t1 : T1 + T2) (H : ~
        In (T1 + T2)
          (fun (t1 : T1 + T2) =>
           match t1 with
           | inl _ => False
           | inr _ => True
           end) t1), inl
  (match
     t1 as t0
     return
       (~
        In (T1 + T2)
          (fun (t1 : T1 + T2) =>
           match t1 with
           | inl _ => False
           | inr _ => True
           end) t0 -> T1)
   with
   | inl t0 => fun (_ : False -> False) => t0
   | inr _ => fun (H : True -> False) => match H I return T1 with
                                       end
   end H) = t1).
move=> H4.
apply (H4 (proj1_sig (f t)) (proj2_sig (f t))).
elim.
move=> t1 H4.
reflexivity.
move=> t2 H4.
elim (H4 I).
move=> H3.
apply H1.
apply (proj1 (CountFiniteBijective T1)).
elim (proj2 (CountFiniteBijective {t : T1 + T2 | In (T1 + T2) (Complement (T1 + T2)
          (fun (t : T1 + T2) => match t with
                              | inl _ => False
                              | inr _ => True
                              end)) t})).
move=> N.
elim.
move=> f.
elim.
move=> g H4.
exists N.
exists (let temp : forall (t : T1 + T2), ~
      In (T1 + T2)
        (fun (t0 : T1 + T2) => match t0 with
                             | inl _ => False
                             | inr _ => True
                             end) t -> T1 := (fun (t : T1 + T2) => match t with
  | inl t0 => fun (H : False -> False) => t0
  | inr t0 => fun (H : True -> False) => match H I with
  end
end) in fun (m : Count N) => temp (proj1_sig (f m)) (proj2_sig (f m))).
exists (fun (t : T1) => g (exist (fun (t0 : T1 + T2) => ~ match t0 with
                             | inl _ => False
                             | inr _ => True
                             end) (inl t) (fun (b : False) => b))).
apply conj.
move=> x.
rewrite - {2} (proj1 H4 x).
apply (f_equal g).
apply sig_map.
simpl.
suff: (forall (t1 : T1 + T2) (H : ~
        In (T1 + T2)
          (fun (t1 : T1 + T2) =>
           match t1 with
           | inl _ => False
           | inr _ => True
           end) t1), inl
  (match
     t1 as t0
     return
       (~
        In (T1 + T2)
          (fun (t1 : T1 + T2) =>
           match t1 with
           | inl _ => False
           | inr _ => True
           end) t0 -> T1)
   with
   | inl t0 => fun (_ : False -> False) => t0
   | inr _ => fun (H : True -> False) => match H I return T1 with
                                       end
   end H) = t1).
move=> H5.
apply (H5 (proj1_sig (f x)) (proj2_sig (f x))).
elim.
move=> t1 H5.
reflexivity.
move=> t2 H5.
elim (H5 I).
move=> y.
simpl.
rewrite (proj2 H4).
reflexivity.
apply (proj1 (FiniteSigSame (T1 + T2)
       (Complement (T1 + T2)
          (fun (t : T1 + T2) => match t with
                              | inl _ => False
                              | inr _ => True
                              end))) H3).
elim H2.
move=> f H3.
exists (let temp : forall (t : T1 + T2),
      (match t with
                             | inl _ => False
                             | inr _ => True
                             end) -> T2 := (fun (t : T1 + T2) => match t with
  | inl _ => fun (H : False) => match H with
  end
  | inr t0 => fun (H : True) => t0
end) in fun (t : {t : T1 + T2
  | In (T1 + T2)
      (fun (t0 : T1 + T2) => match t0 with
                           | inl _ => False
                           | inr _ => True
                           end) t}) => f (temp (proj1_sig t) (proj2_sig t))).
move=> t1 t2.
simpl.
suff: (forall (t1 t2 : T1 + T2) (H1 : In (T1 + T2)
         (fun (t0 : T1 + T2) =>
          match t0 with
          | inl _ => False
          | inr _ => True
          end) t1) (H2 : In (T1 + T2)
         (fun (t0 : T1 + T2) =>
          match t0 with
          | inl _ => False
          | inr _ => True
          end) t2), match
     t1 as t
     return (match t with
             | inl _ => False
             | inr _ => True
             end -> T2)
   with
   | inl _ => fun (H : False) => match H return T2 with
                               end
   | inr t0 => fun (_ : True) => t0
   end H1 = match
     t2 as t
     return (match t with
             | inl _ => False
             | inr _ => True
             end -> T2)
   with
   | inl _ => fun (H : False) => match H return T2 with
                               end
   | inr t0 => fun (_ : True) => t0
   end H2 -> t1 = t2).
move=> H4 H5.
apply sig_map.
apply (H4 (proj1_sig t1) (proj1_sig t2) (proj2_sig t1) (proj2_sig t2)).
apply H3.
apply H5.
elim.
move=> t3 t4.
elim.
move=> t3.
elim.
move=> t4 H4.
elim.
move=> t4 H5 H6 H7.
rewrite H7.
reflexivity.
Qed.

Lemma Theorem_6_corollary_2 : forall (T : Type), ~ Finite T (Full_set T) -> exists (A : Ensemble T), Strict_Included T A (Full_set T) /\ SameCard T {t : T | In T A t}.
Proof.
move=> T H1.
suff: (exists (t : T), True).
elim.
move=> t H2.
exists (Complement T (Singleton T t)).
apply conj.
apply conj.
move=> t0 H3.
apply (Full_intro T t0).
move=> H3.
suff: (In T (Complement T (Singleton T t)) t).
move=> H4.
apply H4.
apply (In_singleton T t).
rewrite H3.
apply (Full_intro T t).
apply (Theorem_6 T (Singleton T t)).
move=> H3.
apply H1.
suff: (Full_set T = Add T (Complement T (Singleton T t)) t).
move=> H4.
rewrite H4.
apply (Union_is_finite T (Complement T (Singleton T t)) H3 t).
move=> H5.
apply H5.
apply (In_singleton T t).
apply Extensionality_Ensembles.
apply conj.
move=> t0 H4.
elim (classic (t = t0)).
move=> H5.
rewrite H5.
right.
apply (In_singleton T t0).
move=> H5.
left.
move=> H6.
apply H5.
elim H6.
reflexivity.
move=> t0 H4.
apply (Full_intro T t0).
exists (fun (t1 : {t0 : T | In T (Singleton T t) t0}) => O).
move=> t1 t2 H3.
apply sig_map.
elim (proj2_sig t1).
elim (proj2_sig t2).
reflexivity.
apply NNPP.
move=> H2.
apply H1.
suff: (Full_set T = Empty_set T).
move=> H3.
rewrite H3.
apply (Empty_is_finite T).
apply Extensionality_Ensembles.
apply conj.
move=> t.
elim H2.
exists t.
apply I.
move=> t H3.
apply (Full_intro T t).
Qed.

Lemma Theorem_9 : forall (T : Type) (tf : T -> Type) (C : CardT), (forall (t : T), Card (tf t) = C) -> Card (sumT T tf) = CardMult C (Card T).
Proof.
move=> T1 tf C H1.
elim (EquivalenceRelationQuotientInhabited Type CardEquivalence C).
move=> T2 H2.
suff: (proj1_sig C T2).
move=> H3.
suff: (forall (t : T1), {ft : tf t -> T2 | Bijective ft}).
move=> H4.
suff: (forall (t : T1), {gt : T2 -> tf t | (forall (x : tf t), gt (proj1_sig (H4 t) x) = x) /\ (forall (y : T2), proj1_sig (H4 t) (gt y) = y)}).
move=> H5.
rewrite - (CardMultNature T2 T1 C (Card T1)).
apply (proj1 (Formula_66_1 (sumT T1 tf) (T2 * T1))).
exists (fun (x : sumT T1 tf) => match x with
  | inT t x0 => (proj1_sig (H4 t) x0, t)
end).
exists (fun (x : T2 * T1) => inT T1 tf (snd x) (proj1_sig (H5 (snd x)) (fst x))).
apply conj.
elim.
move=> t x.
rewrite (proj1 (proj2_sig (H5 t)) x).
reflexivity.
elim.
move=> a b.
rewrite (proj2 (proj2_sig (H5 b)) a).
reflexivity.
apply H3.
apply (Formula_1_1 T1).
move=> t.
apply constructive_indefinite_description.
apply (proj2_sig (H4 t)).
move=> t.
apply constructive_indefinite_description.
apply (proj2 (Formula_66_1 (tf t) T2)).
rewrite (H1 t).
apply H2.
rewrite H2.
apply (Formula_1_1 T2).
Qed.

Lemma Formula_83 : forall (T : Type) (tf : T -> Type) (C : CardT), (forall (t : T), Card (tf t) = C) -> Card (forall (t : T), tf t) = CardPow C (Card T).
Proof.
move=> T1 tf C H1.
elim (EquivalenceRelationQuotientInhabited Type CardEquivalence C).
move=> T2 H2.
suff: (proj1_sig C T2).
move=> H3.
suff: (forall (t : T1), {ft : tf t -> T2 | Bijective ft}).
move=> H4.
suff: (forall (t : T1), {gt : T2 -> tf t | (forall (x : tf t), gt (proj1_sig (H4 t) x) = x) /\ (forall (y : T2), proj1_sig (H4 t) (gt y) = y)}).
move=> H5.
rewrite - (CardPowNature T2 T1 C (Card T1)).
apply (proj1 (Formula_66_1 (forall (t : T1), tf t) (T1 -> T2))).
exists (fun (x : forall (t : T1), tf t) (t : T1) => proj1_sig (H4 t) (x t)).
exists (fun (x : T1 -> T2) (t : T1) => proj1_sig (H5 t) (x t)).
apply conj.
move=> x.
apply functional_extensionality_dep.
move=> t.
apply (proj1 (proj2_sig (H5 t)) (x t)).
move=> y.
apply functional_extensionality.
move=> t.
apply (proj2 (proj2_sig (H5 t)) (y t)).
apply H3.
apply (Formula_1_1 T1).
move=> t.
apply constructive_indefinite_description.
apply (proj2_sig (H4 t)).
move=> t.
apply constructive_indefinite_description.
apply (proj2 (Formula_66_1 (tf t) T2)).
rewrite (H1 t).
apply H2.
rewrite H2.
apply (Formula_1_1 T2).
Qed.
