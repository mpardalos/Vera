From Coq Require Import ZArith.
From Coq Require Import BinNums.
From Coq Require Import String.

From nbits Require Import NBits.
From mathcomp Require Import seq.

From vera Require Import Common (port_direction).

Local Open Scope bits_scope.

Module SMT.
  Inductive qfbv {T} :=
  | BVAdd : qfbv -> qfbv -> qfbv
  | BVMul : qfbv -> qfbv -> qfbv
  | BVNeg : qfbv -> qfbv
  | BVShl : qfbv -> qfbv -> qfbv
  | BVLShr : qfbv -> qfbv -> qfbv
  | BVLit : bits -> qfbv
  | BVVar : T -> qfbv
  | BVZeroExtend : nat -> qfbv -> qfbv
  | BVExtract : nat -> nat -> qfbv -> qfbv
  | CoreITE : qfbv -> qfbv -> qfbv -> qfbv
  .

  Arguments qfbv : clear implicits.

  Inductive sort :=
  | SBitVector : positive -> sort
  .

  Inductive formula {T} :=
  | CDeclare : T -> sort -> formula
  | CEqual : qfbv T -> qfbv T -> formula
  | CDistinct : qfbv T -> qfbv T -> formula
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
