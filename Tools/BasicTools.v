From mathcomp Require Import ssreflect.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.JMeq.

Lemma sig_map : forall {T : Type} (P : T -> Prop) (x : {x : T | P x}) (y : {x : T | P x}), proj1_sig x = proj1_sig y -> x = y.
Proof.
move=> T P.
suff: (forall (xv yv : T), xv = yv -> forall (xp : P xv) (yp : P yv), exist P xv xp = exist P yv yp).
move=> H1 x y.
elim x.
move=> xv xp.
elim y.
move=> yv yp.
simpl.
move=> H2.
apply (H1 xv yv H2 xp yp).
move=> xv yv H1.
rewrite H1.
move=> xp yp.
rewrite (proof_irrelevance (P yv) yp xp).
reflexivity.
Qed.

Lemma TypeEqConvertExist : forall (T1 T2 : Type), T1 = T2 -> {f : T1 -> T2 | forall (t : T1), JMeq t (f t)}.
Proof.
move=> T1 T2 H1.
rewrite H1.
exists (fun (t : T2) => t).
move=> t.
apply (JMeq_refl t).
Qed.

Definition TypeEqConvert (T1 T2 : Type) (H : T1 = T2) := proj1_sig (TypeEqConvertExist T1 T2 H).

Lemma TypeEqConvertNature : forall (T : Type) (H : T = T) (t : T), TypeEqConvert T T H t = t.
Proof.
move=> T H t.
apply JMeq_eq.
apply JMeq_sym.
apply (proj2_sig (TypeEqConvertExist T T H) t).
Qed.
