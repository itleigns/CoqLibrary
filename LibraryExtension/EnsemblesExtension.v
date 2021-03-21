From mathcomp Require Import ssreflect.
Require Import Coq.Sets.Ensembles.

Inductive IntersectionT (U : Type) (T : Type) (A : T -> Ensemble U) : Ensemble U :=
  | IntersectionT_intro : forall (x : U), (forall (t : T), In U (A t) x) -> In U (IntersectionT U T A) x.

Inductive UnionT (U : Type) (T : Type) (A : T -> Ensemble U) : Ensemble U :=
  | UnionT_intro : forall (x : U) (t : T), In U (A t) x -> In U (UnionT U T A) x.
