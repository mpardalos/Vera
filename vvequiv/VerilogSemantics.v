From Coq Require Import BinNums.
From Coq Require Import BinNat.
From Coq Require Import BinPos.
From Coq Require Import String.
From Coq Require FMaps.
From Coq Require FMapFacts.
From Coq Require Import List.
From Coq Require Import ssreflect.
Import ListNotations.

From vvequiv Require Import Verilog.
From vvequiv Require Import Common.
From vvequiv Require Import Bitvector.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Data.Monads.OptionMonad.
Import MonadNotation.
Local Open Scope monad_scope.

From Equations Require Import Equations.

Import Bitvector.

Record VerilogState :=
  MkVerilogState
    { regState : StrMap.t Bitvector.bv
    ; nbaValues : StrMap.t Bitvector.bv
    }
.

Definition set_reg (name : string) (value : Bitvector.bv) (st : VerilogState) : VerilogState :=
  {| regState := StrMap.add name value (regState st)
  ; nbaValues := nbaValues st
  |}
.

Definition set_nba (name : string) (value : Bitvector.bv) (st : VerilogState) : VerilogState :=
  {| regState := regState st
  ; nbaValues := StrMap.add name value (nbaValues st)
  |}
.

Equations
  eval_op : Verilog.op -> Bitvector.bv -> Bitvector.bv -> Bitvector.bv :=
  eval_op _ lhs rhs := _
.
Admit Obligations.

Equations
  eval_expr : VerilogState -> Verilog.expression -> option Bitvector.bv :=
  eval_expr st (Verilog.BinaryOp op lhs rhs) :=
    lhs__val <- eval_expr st lhs ;;
    rhs__val <- eval_expr st rhs ;;
    ret (eval_op op lhs__val rhs__val) ;
  eval_expr st (Verilog.IntegerLiteral val) := Some val;
  eval_expr st (Verilog.NamedExpression name) := StrMap.find name (regState st)
.

Equations
  exec_statement : VerilogState -> Verilog.statement -> option VerilogState :=
  exec_statement st (Verilog.Block stmts) :=
    List.fold_left
      (fun mSt stmt => st <- mSt ;; exec_statement st stmt)
      stmts
      (Some st)
  ;
  exec_statement st (Verilog.If cond trueBranch falseBranch) :=
    condVal <- eval_expr st cond ;;
    if N.eqb (Bitvector.value condVal) 0%N
    then exec_statement st trueBranch
    else exec_statement st falseBranch
  ;
  exec_statement st (Verilog.BlockingAssign (Verilog.NamedExpression name) rhs) :=
    rhs__val <- eval_expr st rhs ;;
    Some (set_reg name rhs__val st)
  ;
  exec_statement st (Verilog.BlockingAssign lhs rhs) :=
    None;
  exec_statement st (Verilog.NonBlockingAssign (Verilog.NamedExpression name) rhs) :=
    rhs__val <- eval_expr st rhs ;;
    Some (set_nba name rhs__val st)
  ;
  exec_statement st (Verilog.NonBlockingAssign lhs rhs) :=
    None
.

Equations
  exec_module_item : VerilogState -> Verilog.module_item -> option VerilogState :=
  exec_module_item st (Verilog.AlwaysFF stmt) :=
    exec_statement st stmt;
  exec_module_item st (Verilog.ContinuousAssign (Verilog.NamedExpression name) rhs) :=
    rhs__val <- eval_expr st rhs ;;
    Some (set_reg name rhs__val st)
  ;
  exec_module_item st (Verilog.ContinuousAssign _ _) :=
    None
.

Inductive step_module (m : Verilog.vmodule) (st1 st2 : VerilogState) : Prop :=
  | step_
