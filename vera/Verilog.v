From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import BinNums.

From ExtLib Require Import Programming.Show.

From vera Require Import Common.
From vera Require Import Bitvector.
Import (notations) Bitvector.BV.

Require Import List.
Import ListNotations.
From Coq Require Arith Lia Program.
From Coq Require Import Structures.Equalities.
From Coq Require Arith.PeanoNat.
From Equations Require Import Equations.

Module VerilogCommon.
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

  Variant vector_declaration :=
    | Scalar
    | Vector (msb : N) (lsb : N).

  Equations vector_declaration_width : vector_declaration -> N :=
    vector_declaration_width Scalar := 1%N ;
    vector_declaration_width (Vector hi lo) := 1%N + (N.max hi lo) - (N.min hi lo).

  Variant StorageType := Reg | Wire.

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
End VerilogCommon.

Module MkVerilog(Annotation : DecidableType).
  Include VerilogCommon.

  Inductive expression :=
  | BinaryOp : op -> expression -> expression -> expression
  | Conditional : expression -> expression -> expression -> expression
  | BitSelect : expression -> expression -> expression
  | IntegerLiteral : BV.t -> expression
  | NamedExpression : Annotation.t -> string -> expression
  | Resize : N -> expression -> expression
  .

  Inductive statement :=
  | Block (body : list statement)
  | BlockingAssign (lhs rhs : expression)
  | NonBlockingAssign (lhs rhs : expression)
  | If (condition : expression) (trueBranch falseBranch : statement)
  .

  Inductive module_item :=
  | AlwaysComb : statement -> module_item
  | AlwaysFF : statement -> module_item
  | Initial : statement -> module_item
  .

  (** Verilog modules *)
  Record vmodule :=
    MkMod
      { modName : string
      ; modPorts : list port
      ; modVariables : list variable
      ; modBody : list module_item
      }.

  Module Notations.
    Notation "[ hi .: lo ]" :=
      (Vector hi lo)
        (format "[ hi '.:' lo ]").
  End Notations.
End MkVerilog.

Module TypedVerilog.
  Include MkVerilog(N).

  Definition vtype := N.

  Equations expr_type : expression -> N :=
    expr_type (BinaryOp _ lhs _) := expr_type lhs;
    expr_type (BitSelect _ _) := 1%N;
    expr_type (Conditional _ tBranch fBranch) := expr_type tBranch; (**  TODO: need to check fBranch? *)
    expr_type (Resize t _) := t;
    expr_type (TypedVerilog.IntegerLiteral v) := BV.size v;
    expr_type (NamedExpression t _) := t.
End TypedVerilog.

Module Unit_as_MDT <: MiniDecidableType.
  Definition t := unit.
  Definition eq_dec (x y : unit) : { x = y } + { x <> y } :=
    match x, y with
    | tt, tt => left eq_refl
    end.
End Unit_as_MDT.

Module Unit_as_DT := Make_UDT(Unit_as_MDT).

Module Verilog := MkVerilog(Unit_as_DT).
