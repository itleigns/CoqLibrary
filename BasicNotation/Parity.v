Add LoadPath "Tools" as Tools.

From mathcomp Require Import ssreflect.
Require Import Tools.MySum.

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
