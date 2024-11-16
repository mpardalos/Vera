From Coq Require Import BinIntDef.
From Coq Require Import BinNums.
From Coq Require Import FSets.
From Coq Require Import List.
From Coq Require Import Program.
From Coq Require Import Psatz.
From Coq Require Import String.
From Coq Require Import ZArith.

From Equations Require Import Equations.
From ExtLib Require Import Data.List.
From ExtLib Require Import Data.Monads.EitherMonad.
From ExtLib Require Import Data.Monads.StateMonad.
From ExtLib Require Import Data.String.
From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.MonadState.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Monoid.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Programming.Show.
From nbits Require Import NBits.

From vera Require Import Verilog.
From vera Require Import SMT.
From vera Require Import Common.
From vera Require EnvStack.

Import ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.
Local Open Scope bits_scope.

Definition transf := sum string.

Definition transfer_name (n : string) : transf string := raise "not implemented"%string.

Equations expr_to_smt : TypedVerilog.expression -> transf (SMT.qfbv string) :=
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryPlus lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVAdd lhs__smt rhs__smt);
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryMinus lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVAdd lhs__smt (SMT.BVNeg rhs__smt));
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryStar lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVMul lhs__smt rhs__smt);
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryShiftLeft lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVShl lhs__smt rhs__smt);
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryShiftLeftArithmetic lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVShl lhs__smt rhs__smt);
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryShiftRight lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVLShr lhs__smt rhs__smt);
  expr_to_smt (TypedVerilog.BinaryOp _ _ _ _) :=
    raise "Unsupported operator in SMT"%string;
  expr_to_smt (TypedVerilog.Conditional cond ifT ifF) :=
    cond__smt <- expr_to_smt cond ;;
    ifT__smt <- expr_to_smt ifT ;;
    ifF__smt <- expr_to_smt ifF ;;
    ret (SMT.CoreITE cond__smt ifT__smt ifF__smt);
  expr_to_smt (TypedVerilog.BitSelect vec idx) :=
    vec__smt <- expr_to_smt vec ;;
    idx__smt <- expr_to_smt idx ;;
    ret (SMT.BVExtract 0 0 (SMT.BVLShr vec__smt idx__smt));
  expr_to_smt (TypedVerilog.Conversion from to expr) :=
    _;
  expr_to_smt (TypedVerilog.IntegerLiteral val) :=
    ret (SMT.BVLit val);
  expr_to_smt (TypedVerilog.NamedExpression t n) :=
    n__smt <- transfer_name n ;;
    ret (SMT.BVVar n__smt).

Definition verilog_to_smt
  (vmodule : TypedVerilog.vmodule)
  : sum string (SMT.smt_netlist string) := raise "not_implemented"%string.
