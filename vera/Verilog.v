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
  Variant binop :=
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


  Variant unaryop :=
    | UnaryPlus (* +  *)
    | UnaryMinus (* -  *)
    | UnaryNegation (* !  *)
    (* TODO: reduction operators *)
    (*
    | UnaryReduce... (* ~  *)
    | UnaryReduce... (* &  *)
    | UnaryReduce... (* ~& *)
    | UnaryReduce... (* |  *)
    | UnaryReduce... (* ~| *)
    | UnaryReduce... (* ^  *)
    | UnaryReduce... (* ~^ *)
    | UnaryReduce... (* ^~ *)
     *)
  .

  Section op_show.
    Local Open Scope string.
    Import ShowNotation.
    Global Instance binop_Show : Show binop :=
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
    Global Instance unaryop_Show : Show unaryop :=
      { show u :=
          match u with
          | UnaryPlus => "+"
          | UnaryMinus => "-"
          | UnaryNegation => "!"
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
  | BinaryOp : binop -> expression -> expression -> expression
  | UnaryOp : unaryop -> expression -> expression
  | Conditional : expression -> expression -> expression -> expression
  | BitSelect : expression -> expression -> expression
  | Concatenation : list expression -> expression
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

  Definition inputs (v : vmodule) : list string :=
    map_opt (fun p => match p with
                   | {|
                       portDirection := PortIn;
                       portName := name
                     |} => Some name
                   | _ => None
                   end)
      (modPorts v).

  Definition outputs (v : vmodule) : list string :=
    map_opt (fun p => match p with
                   | {|
                       portDirection := PortOut;
                       portName := name
                     |} => Some name
                   | _ => None
                   end)
      (modPorts v).
End MkVerilog.

Module Verilog.
  Include MkVerilog(N).

  Definition vtype := N.

  Equations expr_type : expression -> N :=
    expr_type (BinaryOp _ lhs _) := expr_type lhs;
    (* TODO: Unary operators might change expression type *)
    expr_type (UnaryOp _ operand):= expr_type operand;
    expr_type (BitSelect _ _) := 1%N;
    expr_type (Concatenation exprs) := fold_left N.add (map expr_type exprs) 0%N;
    expr_type (Conditional _ tBranch fBranch) := expr_type tBranch; (**  TODO: need to check fBranch? *)
    expr_type (Resize t _) := t;
    expr_type (IntegerLiteral v) := BV.size v;
    expr_type (NamedExpression t _) := t.
End Verilog.

Module Unit_as_MDT <: MiniDecidableType.
  Definition t := unit.
  Definition eq_dec (x y : unit) : { x = y } + { x <> y } :=
    match x, y with
    | tt, tt => left eq_refl
    end.
End Unit_as_MDT.

Module Unit_as_DT := Make_UDT(Unit_as_MDT).

(* Not used at the moment *)
Module UntypedVerilog := MkVerilog(Unit_as_DT).
