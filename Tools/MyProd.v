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

Definition MyProdFL (mo : Monoid) (a : list (MoT mo)) := fold_right (fun (m0 : MoT mo) (m : MoT mo) => Moc mo m0 m) (Moe mo) a.

Lemma MyProdFLSingle : forall (mo : Monoid) (m : MoT mo), MyProdFL mo (m :: nil) = m.
Proof.
intros mo m.
apply (Mo_O_r mo m).
Qed.

Lemma MyProdFLApp : forall (mo : Monoid) (a b : list (MoT mo)), MyProdFL mo (app a b) = Moc mo (MyProdFL mo a) (MyProdFL mo b).
Proof.
intros mo a b.
elim a.
simpl.
rewrite (Mo_O_l mo (MyProdFL mo b)).
reflexivity.
intros a0 l H1.
simpl.
rewrite H1.
rewrite (Mo_assoc mo a0 (MyProdFL mo l) (MyProdFL mo b)).
reflexivity.
Qed.

Lemma Mo_assoc_reverse : forall (mo : Monoid) (m1 m2 m3 : MoT mo), Moc mo m3 (Moc mo m2 m1) = Moc mo (Moc mo m3 m2) m1.
Proof.
intros mo m1 m2 m3.
rewrite (Mo_assoc mo m3 m2 m1).
reflexivity.
Qed.

Definition ReverseMonoid (mo : Monoid) := mkMonoid (MoT mo) (Moe mo) (fun (m1 m2 : MoT mo) => Moc mo m2 m1) (Mo_O_l mo) (Mo_O_r mo) (Mo_assoc_reverse mo).

Lemma MyProdFLReverse : forall (mo : Monoid) (a : list (MoT mo)), MyProdFL mo a = MyProdFL (ReverseMonoid mo) (rev a).
Proof.
intros mo a.
elim a.
reflexivity.
intros a0 l H1.
simpl.
rewrite H1.
cut ((@app (MoT mo) (@rev (MoT mo) l) (@cons (MoT mo) a0 (@nil (MoT mo)))) = (@app (MoT (ReverseMonoid mo)) (@rev (MoT mo) l) (@cons (MoT mo) a0 (@nil (MoT mo))))).
intro H2.
rewrite H2.
rewrite (MyProdFLApp (ReverseMonoid mo) (rev l) (a0 :: nil)).
cut ((@cons (MoT mo) a0 (@nil (MoT mo))) = (@cons (MoT (ReverseMonoid mo)) a0 (@nil (MoT (ReverseMonoid mo))))).
intro H3.
rewrite H3.
rewrite (MyProdFLSingle (ReverseMonoid mo) a0).
reflexivity.
reflexivity.
reflexivity.
Qed.
