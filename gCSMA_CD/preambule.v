Require Import Peano_dec.

Implicit Arguments None [A].

Definition ifeq (i j : nat) (C : Set) (a b : C) : C :=
  if eq_nat_dec i j then a else b.
Implicit Arguments ifeq [C].