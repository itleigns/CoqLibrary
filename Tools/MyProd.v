Require Import Coq.Lists.List.

Record Monoid : Type := mkMonoid
{
MoT : Type;
Moe : MoT;
Moc : MoT -> MoT -> MoT;
Mo_O_r : forall (x : MoT), (Moc x Moe) = x;
Mo_O_l : forall (x : MoT), (Moc Moe x) = x;
Mo_assoc : forall (x y z : MoT), (Moc (Moc x y) z) = (Moc x (Moc y z))
}.

Definition MyProdFL (U : Type) (a : list U) (mo : Monoid) (F : U -> MoT mo) := fold_right (fun (u : U) (m : MoT mo) => Moc mo (F u) m) (Moe mo) a.

Lemma MyProdFLSingle : forall (U : Type) (u : U) (mo : Monoid) (F : U -> MoT mo), MyProdFL U (u :: nil) mo F = F u.
Proof.
intros U u mo F.
apply (Mo_O_r mo (F u)).
Qed.

Lemma MyProdFLApp : forall (U : Type) (a b : list U) (mo : Monoid) (F : U -> MoT mo), MyProdFL U (app a b) mo F = Moc mo (MyProdFL U a mo F) (MyProdFL U b mo F).
Proof.
intros U a b mo F.
elim a.
simpl.
rewrite (Mo_O_l mo (MyProdFL U b mo F)).
reflexivity.
intros u a0 H1.
simpl.
rewrite H1.
rewrite (Mo_assoc mo (F u) (MyProdFL U a0 mo F) (MyProdFL U b mo F)).
reflexivity.
Qed.

Lemma Mo_assoc_reverse : forall (mo : Monoid) (m1 m2 m3 : MoT mo), Moc mo m3 (Moc mo m2 m1) = Moc mo (Moc mo m3 m2) m1.
Proof.
intros mo m1 m2 m3.
rewrite (Mo_assoc mo m3 m2 m1).
reflexivity.
Qed.

Definition ReverseMonoid (mo : Monoid) := mkMonoid (MoT mo) (Moe mo) (fun (m1 m2 : MoT mo) => Moc mo m2 m1) (Mo_O_l mo) (Mo_O_r mo) (Mo_assoc_reverse mo).

Lemma MyProdFLReverse : forall (U : Type) (a : list U) (mo : Monoid) (F : U -> MoT mo), MyProdFL U a mo F = MyProdFL U (rev a) (ReverseMonoid mo) F.
Proof.
intros U a mo F.
elim a.
reflexivity.
intros a0 l H1.
simpl.
rewrite (MyProdFLApp U (rev l) (a0 :: nil) (ReverseMonoid mo) F).
rewrite H1.
rewrite (MyProdFLSingle U a0 (ReverseMonoid mo) F).
reflexivity.
Qed.
