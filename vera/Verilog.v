From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import BinNums.

From nbits Require Import NBits.
From mathcomp Require Import seq.
From ExtLib Require Import Programming.Show.

From vera Require Import Common.

Require Import List.
Import ListNotations.
From Coq Require Arith Lia Program.
From Equations Require Import Equations.

(* This module will be Verilog.Verilog. Redundant, but it is needed for extraction. See Extraction.v *)
Module Verilog.
  Definition vtype := nat.

  Variant StorageType := Reg | Wire.

  Variant op :=
    | BinaryPlus (* '+' *)
    | BinaryMinus (* '-' *)
    | BinaryStar (* '*' *)
    | BinarySlash (* '/' *)
    | BinaryPercent (* '%' *)
    | BinaryEqualsEquals (* '==' *)
    | BinaryNotEquals (* '!=' *)
    | BinaryEqualsEqualsEquals (* '===' *)
    | BinaryNotEqualsEquals (* '!==' *)
    | BinaryWildcardEqual (* '==?' *)
    | BinaryWildcardNotEqual (* '!=?' *)
    | BinaryLogicalAnd (* '&&' *)
    | BinaryLogicalOr (* '||' *)
    | BinaryExponent (* '**' *)
    | BinaryLessThan (* '<' *)
    | BinaryLessThanEqual (* '<=' *)
    | BinaryGreaterThan (* '>' *)
    | BinaryGreaterThanEqual (* '>=' *)
    | BinaryBitwiseAnd (* '&' *)
    | BinaryBitwiseOr (* '|' *)
    | BinaryBitwiseXor (* '^' *)
    | BinaryXNor (* '^~', '~^' *)
    | BinaryShiftRight (* '>>' *)
    | BinaryShiftLeft (* '<<' *)
    | BinaryShiftRightArithmetic (* '>>>' *)
    | BinaryShiftLeftArithmetic (* '<<<' *)
    | BinaryLogicalImplication (* '->' *)
    | BinaryLogicalEquivalence (* '<->' *)
  .

  Section op_show.
    Local Open Scope string.
    Import ShowNotation.
    Global Instance op_Show : Show op :=
      { show u :=
          match u with
          | BinaryPlus => "+"
          | BinaryMinus => "-"
          | BinaryStar => "*"
          | BinarySlash => "/"
          | BinaryPercent => "%"
          | BinaryEqualsEquals => "=="
          | BinaryNotEquals => "!="
          | BinaryEqualsEqualsEquals => "==="
          | BinaryNotEqualsEquals => "!=="
          | BinaryWildcardEqual => "==?"
          | BinaryWildcardNotEqual => "!=?"
          | BinaryLogicalAnd => "&&"
          | BinaryLogicalOr => "||"
          | BinaryExponent => "**"
          | BinaryLessThan => "<"
          | BinaryLessThanEqual => "<="
          | BinaryGreaterThan => ">"
          | BinaryGreaterThanEqual => ">="
          | BinaryBitwiseAnd => "&"
          | BinaryBitwiseOr => "|"
          | BinaryBitwiseXor => "^"
          | BinaryXNor => "^~"
          | BinaryShiftRight => ">>"
          | BinaryShiftLeft => "<<"
          | BinaryShiftRightArithmetic => ">>>"
          | BinaryShiftLeftArithmetic => "<<<"
          | BinaryLogicalImplication => "->"
          | BinaryLogicalEquivalence => "<->"
          end
      }.
  End op_show.

  Inductive expression :=
  | BinaryOp : op -> expression -> expression -> expression
  | Conditional : expression -> expression -> expression -> expression
  | BitSelect : expression -> expression -> expression
  | IntegerLiteral : bits -> expression
  | NamedExpression : string -> expression.

  Variant vector_declaration :=
    | Scalar
    | Vector (msb : nat) (lsb : nat).

  Equations vector_declaration_width : Verilog.vector_declaration -> nat :=
    vector_declaration_width Verilog.Scalar := 1 ;
    vector_declaration_width (Verilog.Vector hi lo) := 1 + (max hi lo) - (min hi lo).

  Record variable :=
    MkVariable
      { varVectorDeclaration : vector_declaration
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
  | AlwaysComb : statement -> module_item
  | AlwaysFF : statement -> module_item
  | Initial : statement -> module_item
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
  Export Verilog(vtype, op(..), variable(..), port(..)).

  Inductive expression :=
  | BinaryOp : vtype -> op -> expression -> expression -> expression
  | Conditional : expression -> expression -> expression -> expression
  | BitSelect : expression -> expression -> expression
  | Conversion : vtype -> vtype -> expression -> expression
  | IntegerLiteral : bits -> expression
  | NamedExpression : vtype -> string -> expression
  .

  Equations expr_type : TypedVerilog.expression -> Verilog.vtype :=
    expr_type (TypedVerilog.BinaryOp t _ _ _) := t;
    expr_type (TypedVerilog.BitSelect _ _) := 1;
    expr_type (TypedVerilog.Conditional _ tBranch fBranch) := expr_type tBranch; (**  TODO: need to check fBranch? *)
    expr_type (TypedVerilog.Conversion _ t _) := t;
    expr_type (TypedVerilog.IntegerLiteral v) := size v;
    expr_type (TypedVerilog.NamedExpression t _) := t.

  Inductive Statement :=
  | Block (body : list Statement)
  | BlockingAssign (lhs rhs : expression)
  | NonBlockingAssign (lhs rhs : expression)
  | If (condition : expression) (trueBranch falseBranch : Statement)
  .

  Inductive module_item : Set :=
  | AlwaysComb : Statement -> module_item
  | AlwaysFF : Statement -> module_item
  | Initial : Statement -> module_item
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
    (Verilog.Vector hi lo)
      (format "[ hi '.:' lo ]").
End VerilogNotations.
