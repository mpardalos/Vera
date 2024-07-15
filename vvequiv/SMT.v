Require Import ZArith.
Require Import BinNums.
Require Import String.

Require Import Bitvector.
Require Import Common (port_direction).
Import Bitvector.

Module SMT.
  Inductive qfbv {T} :=
  | BVAdd : qfbv -> qfbv -> qfbv
  | BVNeg : qfbv -> qfbv
  | BVLit : bv -> qfbv
  | BVVar : T -> qfbv
  | BVZeroExtend : positive -> qfbv -> qfbv
  | BVExtract : N -> N -> qfbv -> qfbv
  | CoreITE : qfbv -> qfbv -> qfbv -> qfbv
  .

  Arguments qfbv : clear implicits.

  Inductive sort :=
  | SBitVector : positive -> sort
  .

  Inductive formula {N} :=
  | CDeclare : N -> sort -> formula
  | CEqual : qfbv N -> qfbv N -> formula
  | CDistinct : qfbv N -> qfbv N -> formula
  .

  Arguments formula : clear implicits.

  Record smt_netlist {N : Type} : Type :=
    SMTNetlist
      { smtnlName : string
      ; smtnlPorts : list (N * port_direction)
      ; smtnlFormulas : list (formula N)
      }.

  Arguments smt_netlist : clear implicits.
End SMT.
