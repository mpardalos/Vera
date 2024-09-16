From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import BinNums.

From nbits Require Import NBits.

From vera Require Import Common.

Require Import List.
Import ListNotations.
From Coq Require Arith Lia Program.
From Equations Require Import Equations.

(* This module will be Verilog.Verilog. Redundant, but it is needed for extraction. See Extraction.v *)
Module Verilog.
  Inductive vtype := Logic : nat -> nat -> vtype.

  Definition vtype_width (t : Verilog.vtype) : nat :=
    let (hi, lo) := t in
    ((max hi lo) - (min hi lo)) + 1
  .

  Variant StorageType := Reg | Wire.

  Equations Derive NoConfusionHom EqDec for vtype.

  Variant op :=
    | Plus
    | Minus
    | Multiply
    | ShiftLeft
    | ShiftRight
  .

  Inductive expression :=
  | BinaryOp : op -> expression -> expression -> expression
  | IntegerLiteral : bits -> expression
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
  | IntegerLiteral : bits -> expression
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

Module VerilogNotations.
  Notation "[ hi .: lo ]" :=
    (Verilog.Logic hi lo)
      (format "[ hi '.:' lo ]").
End VerilogNotations.
