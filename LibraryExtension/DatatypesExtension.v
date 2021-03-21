From mathcomp Require Import ssreflect.

Lemma injective_inl : forall (T1 T2 : Type) (t1 t2 : T1), inl T2 t1 = inl T2 t2 -> t1 = t2.
Proof.
move=> T1 T2 t1 t2 H1.
suff: (let f := fun (t : sum T1 T2) => match t with
  | inl t0 => t0
  | inr _ => t1
end in t1 = t2).
apply.
move=> f.
suff: (t1 = f (inl t1)).
move=> H2.
rewrite H2.
rewrite H1.
reflexivity.
reflexivity.
Qed.

Lemma injective_inr : forall (T1 T2 : Type) (t1 t2 : T2), inr T1 t1 = inr T1 t2 -> t1 = t2.
Proof.
move=> T1 T2 t1 t2 H1.
suff: (let f := fun (t : sum T1 T2) => match t with
  | inl _ => t1
  | inr t0 => t0
end in t1 = t2).
apply.
move=> f.
suff: (t1 = f (inr t1)).
move=> H2.
rewrite H2.
rewrite H1.
reflexivity.
reflexivity.
Qed.

Inductive sumT (T : Type) (tf : T -> Type) : Type := 
  | inT : forall (t : T), (tf t) -> sumT T tf.
