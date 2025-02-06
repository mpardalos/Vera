From Coq Require Import ZArith.
From Coq Require Import BinNums.
From Coq Require Import String.

From vera Require Import Common.
From vera Require Import Bitvector.

From SMTCoqApi Require SMTLib.

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

  Record smtlib_query :=
    MkSMTLibQuery
      { nameSMTToVerilog : NatFunMap.t string;
        nameVerilogToSMT : StrFunMap.t (nat * SMTLib.sort);
        declarations : list (nat * SMTLib.sort);
        assertions : list SMTLib.term
      }.

  Definition model interp_sort_sym :=
    forall (n : nat) (dom : list SMTLib.sort) (codom : SMTLib.sort), SMTLib.interp_fun_type interp_sort_sym dom codom.

  Definition no_uninterp_sorts : nat -> Type := fun _ => False.

  Definition max_var (q : smtlib_query) : nat :=
    List.list_max (List.map fst (declarations q)).

  Definition satisfied_by
    (query : smtlib_query)
    (interp_sort_sym : nat -> Type)
    (interp_fun_sym : model interp_sort_sym) :=
    List.Forall
      (fun term => SMTLib.interp_term interp_sort_sym interp_fun_sym term =
                  Some (existT _ SMTLib.Sort_Bool true))
      (assertions query).

  Definition sat (query : smtlib_query) : Prop := exists interp_sort_sym interp_fun_sym, satisfied_by query interp_sort_sym interp_fun_sym.

  Definition unsat (query : smtlib_query) : Prop := forall interp_sort_sym interp_fun_sym, ~ (satisfied_by query interp_sort_sym interp_fun_sym).
End SMT.
