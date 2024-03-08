Require Import ZArith.
Require Import BinNums.
Require Import String.

Require Import Names.
Require Import Bitvector.
Require Import Common (port_direction).
Import Bitvector.

Module QFBV.

  Inductive formula :=
  | BVAdd : formula -> formula -> formula
  | BVNeg : formula -> formula
  | BVLit : bv -> formula
  | BVVar : name -> formula
  .

End QFBV.

Module Core.

  Inductive SMTSort :=
  | SBitVector : positive -> SMTSort
  .

  Inductive formula :=
  | CDeclare : name -> SMTSort -> formula
  | CEqual : QFBV.formula -> QFBV.formula -> formula
  | CDistinct : QFBV.formula -> QFBV.formula -> formula
  .

  Record smt_netlist :=
    SMTNetlist
      { smtnlName : string
      ; smtnlPorts : list (name * port_direction)
      ; smtnlFormulas : list Core.formula
      }.

End Core.
