Require Import ZArith.
Require Import BinNums.

Require Import Names.
Require Import Bitvector.
Import Bitvector.

Module QFBV.

  Inductive formula :=
  | BVAdd : formula -> formula -> formula
  | BVLit : bv -> formula
  | BVVar : name -> formula
  .

End QFBV.

Module Core.

  Inductive formula :=
  | CEqual : QFBV.formula -> QFBV.formula -> formula
  | CDistinct : QFBV.formula -> QFBV.formula -> formula
  .

End Core.
