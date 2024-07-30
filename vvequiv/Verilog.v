Require Import Common.
Require Import Bitvector.
Import Bitvector (bv(..), mkBV).

Require Import String.
Require Import ZArith.
Require Import BinNums.

Require Import List.
Import ListNotations.
From Coq Require Arith Lia Program.
From Equations Require Import Equations.

(* This module will be Verilog.Verilog. Redundant, but it is needed for extraction. See Extraction.v *)
Module Verilog.
  Inductive vtype := Logic : N -> N -> vtype.

  Variant StorageType := Reg | Wire.

  Equations Derive NoConfusionHom EqDec for vtype.
  Next Obligation.
    destruct x as [hi1 lo1].
    destruct y as [hi2 lo2].
    destruct (N.eq_dec hi1 hi2); destruct (N.eq_dec lo1 lo2); subst.
    - left. reflexivity.
    - right. intros contra. inversion contra.
      auto.
    - right. intros contra. inversion contra.
      auto.
    - right. intros contra. inversion contra.
      auto.
  Defined.

  Inductive op := Plus | Minus.

  Inductive expression :=
  | BinaryOp : op -> expression -> expression -> expression
  | IntegerLiteral : bv -> expression
  | NamedExpression : string -> expression.

  Record variable :=
    MkVariable
      { varType : vtype
      ; varStorageType : StorageType
      ; varName : string
      }.

  Record port :=
    MkPort
      { portDirection : port_direction
      ; portName : string
      }.

  Inductive statement :=
  | Block (body : list statement)
  | BlockingAssign (lhs rhs : expression)
  | NonBlockingAssign (lhs rhs : expression)
  | If (condition : expression) (trueBranch falseBranch : statement)
  .

  Inductive module_item : Set :=
  | ContinuousAssign : expression -> expression -> module_item
  | AlwaysFF : statement -> module_item
  .

  (** Verilog modules *)
  Record vmodule : Set :=
    MkMod
      { modName : string
      ; modPorts : list port
      ; modVariables : list variable
      ; modBody : list module_item
      }.

  Record raw_declaration :=
    MkRawDeclaration
      { rawDeclStorageType : StorageType
      ; rawDeclPortDeclaration : option port_direction
      ; rawDeclName : string
      ; rawDeclType : option vtype
      }
  .

  (** Verilog modules (as parsed) *)
  Record raw_vmodule : Set :=
    MkRawModule
      { rawModName : string
      ; rawModPorts : list port
      ; rawModBody : list (module_item + raw_declaration)
      }
  .
End Verilog.

Module TypedVerilog.
  Export Verilog(vtype(..), op(..), variable(..), port(..)).

  Inductive expression :=
  | BinaryOp : vtype -> op -> expression -> expression -> expression
  | Conversion : vtype -> vtype -> expression -> expression
  | IntegerLiteral : bv -> expression
  | NamedExpression : vtype -> string -> expression
  .

  Inductive Statement :=
  | Block (body : list Statement)
  | BlockingAssign (lhs rhs : expression)
  | NonBlockingAssign (lhs rhs : expression)
  | If (condition : expression) (trueBranch falseBranch : Statement)
  .

  Inductive module_item : Set :=
  | ContinuousAssign : expression -> expression -> module_item
  | AlwaysFF : Statement -> module_item
  .

  (** Verilog modules *)
  Record vmodule : Set :=
    MkMod
      { modName : string
      ; modPorts : list port
      ; modVariables : list variable
      ; modBody : list module_item
      }.
End TypedVerilog.
