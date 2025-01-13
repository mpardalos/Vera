From Coq Require Import ZArith.
From Coq Require Import BinNums.
From Coq Require Import String.

From vera Require Import Common (port_direction).
From vera Require Import Bitvector.

Module SMT.
  Inductive qfbv {T} :=
  | BVOr : qfbv -> qfbv -> qfbv
  | BVAnd : qfbv -> qfbv -> qfbv
  | BVAdd : qfbv -> qfbv -> qfbv
  | BVMul : qfbv -> qfbv -> qfbv
  | BVNeg : qfbv -> qfbv
  | BVNot : qfbv -> qfbv
  | BVShl : qfbv -> qfbv -> qfbv
  | BVLShr : qfbv -> qfbv -> qfbv
  | BVLit : BV.t -> qfbv
  | BVVar : T -> qfbv
  | BVZeroExtend : N -> qfbv -> qfbv
  | BVExtract : N -> N -> qfbv -> qfbv
  | BVConcat : qfbv -> qfbv -> qfbv
  | CoreEq : qfbv -> qfbv -> qfbv
  | CoreNot : qfbv -> qfbv
  | CoreITE : qfbv -> qfbv -> qfbv -> qfbv
  .

  Arguments qfbv : clear implicits.

  Inductive sort :=
  | SBitVector : N -> sort
  .

  Inductive formula {T} :=
  | CDeclare : T -> sort -> formula
  | CEqual : qfbv T -> qfbv T -> formula
  | CDistinct : qfbv T -> qfbv T -> formula
  .

  Arguments formula : clear implicits.

  Record smt_netlist {name : Type} : Type :=
    SMTNetlist
      { smtnlName : string
      ; smtnlPorts : list (name * port_direction)
      ; smtnlFormulas : list (formula name)
      }.

  Arguments smt_netlist : clear implicits.
End SMT.
