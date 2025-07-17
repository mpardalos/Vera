From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import BinNums.

From ExtLib Require Import Programming.Show.

From vera Require Import Common.
From vera Require Import Bitvector.
Import (notations) Bitvector.RawBV.

Require Import List.
From Coq Require Arith Lia Program.
From Coq Require Import Structures.Equalities.
From Coq Require Arith.PeanoNat.
From Equations Require Import Equations.

Import ListNotations.
Import SigTNotations.

Module VerilogCommon.
  Variant binop :=
    | BinaryPlus (* '+' *)
    | BinaryMinus (* '-' *)
    | BinaryStar (* '*' *)
    (* | BinarySlash (* '/' *) *)
    (* | BinaryPercent (* '%' *) *)
    (* | BinaryEqualsEquals (* '==' *) *)
    (* | BinaryNotEquals (* '!=' *) *)
    (* | BinaryEqualsEqualsEquals (* '===' *) *)
    (* | BinaryNotEqualsEquals (* '!==' *) *)
    (* | BinaryWildcardEqual (* '==?' *) *)
    (* | BinaryWildcardNotEqual (* '!=?' *) *)
    (* | BinaryLogicalAnd (* '&&' *) *)
    (* | BinaryLogicalOr (* '||' *) *)
    (* | BinaryExponent (* '**' *) *)
    (* | BinaryLessThan (* '<' *) *)
    (* | BinaryLessThanEqual (* '<=' *) *)
    (* | BinaryGreaterThan (* '>' *) *)
    (* | BinaryGreaterThanEqual (* '>=' *) *)
    | BinaryBitwiseAnd (* '&' *)
    | BinaryBitwiseOr (* '|' *)
    (* | BinaryBitwiseXor (* '^' *) *)
    (* | BinaryXNor (* '^~', '~^' *) *)
    | BinaryShiftRight (* '>>' *)
    | BinaryShiftLeft (* '<<' *)
    (* | BinaryShiftRightArithmetic (* '>>>' *) *)
    | BinaryShiftLeftArithmetic (* '<<<' *)
    (* | BinaryLogicalImplication (* '->' *) *)
    (* | BinaryLogicalEquivalence (* '<->' *) *)
  .


  Variant unaryop :=
    | UnaryPlus (* +  *)
    (* | UnaryMinus (* -  *) *)
    (* | UnaryNegation (* !  *) *)
    (* | UnaryReduce... (* ~  *) *)
    (* | UnaryReduce... (* &  *) *)
    (* | UnaryReduce... (* ~& *) *)
    (* | UnaryReduce... (* |  *) *)
    (* | UnaryReduce... (* ~| *) *)
    (* | UnaryReduce... (* ^  *) *)
    (* | UnaryReduce... (* ~^ *) *)
    (* | UnaryReduce... (* ^~ *) *)
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
          (* | BinarySlash => "/" *)
          (* | BinaryPercent => "%" *)
          (* | BinaryEqualsEquals => "==" *)
          (* | BinaryNotEquals => "!=" *)
          (* | BinaryEqualsEqualsEquals => "===" *)
          (* | BinaryNotEqualsEquals => "!==" *)
          (* | BinaryWildcardEqual => "==?" *)
          (* | BinaryWildcardNotEqual => "!=?" *)
          (* | BinaryLogicalAnd => "&&" *)
          (* | BinaryLogicalOr => "||" *)
          (* | BinaryExponent => "**" *)
          (* | BinaryLessThan => "<" *)
          (* | BinaryLessThanEqual => "<=" *)
          (* | BinaryGreaterThan => ">" *)
          (* | BinaryGreaterThanEqual => ">=" *)
          | BinaryBitwiseAnd => "&"
          | BinaryBitwiseOr => "|"
          (* | BinaryBitwiseXor => "^" *)
          (* | BinaryXNor => "^~" *)
          | BinaryShiftRight => ">>"
          | BinaryShiftLeft => "<<"
          (* | BinaryShiftRightArithmetic => ">>>" *)
          | BinaryShiftLeftArithmetic => "<<<"
          (* | BinaryLogicalImplication => "->" *)
          (* | BinaryLogicalEquivalence => "<->" *)
          end
      }.
    Global Instance unaryop_Show : Show unaryop :=
      { show u :=
          match u with
          | UnaryPlus => "+"
          (* | UnaryMinus => "-" *)
          (* | UnaryNegation => "!" *)
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
      { varPort : option port_direction
      ; varVectorDeclaration : vector_declaration
      ; varStorageType : StorageType
      ; varName : string
      }.

  Definition varWidth (v : variable) : N := vector_declaration_width (varVectorDeclaration v).
End VerilogCommon.

Module Verilog.
  Include VerilogCommon.

  Definition vtype := N.

  Equations binop_width : Verilog.binop -> N -> N :=
    binop_width BinaryPlus n := n; (* "+" *)
    binop_width BinaryMinus n := n; (* "-" *)
    binop_width BinaryStar n := n; (* "*" *)
    (* binop_width BinarySlash n := n; (* "/" *) *)
    (* binop_width BinaryPercent n := n; (* "%" *) *)
    (* binop_width BinaryExponent n := n; (* "**" *) *)
    (* binop_width BinaryEqualsEquals n := 1; (* "==" *) *)
    (* binop_width BinaryNotEquals n := 1; (* "!=" *) *)
    (* binop_width BinaryEqualsEqualsEquals n := 1; (* "===" *) *)
    (* binop_width BinaryNotEqualsEquals n := 1; (* "!==" *) *)
    (* binop_width BinaryWildcardEqual n := 1; (* "==?" *) *)
    (* binop_width BinaryWildcardNotEqual n := 1; (* "!=?" *) *)
    (* binop_width BinaryLogicalAnd n := 1; (* "&&" *) *)
    (* binop_width BinaryLogicalOr n := 1; (* "||" *) *)
    (* binop_width BinaryLessThan n := 1; (* "<" *) *)
    (* binop_width BinaryLessThanEqual n := 1; (* "<=" *) *)
    (* binop_width BinaryGreaterThan n := 1; (* ">" *) *)
    (* binop_width BinaryGreaterThanEqual n := 1; (* ">=" *) *)
    binop_width BinaryBitwiseAnd n := n; (* "&" *)
    binop_width BinaryBitwiseOr n := n; (* "|" *)
    (* binop_width BinaryBitwiseXor n := n; (* "^" *) *)
    (* binop_width BinaryXNor n := n; (* "^~" *) *)
    binop_width BinaryShiftRight n := n; (* ">>" *)
    binop_width BinaryShiftLeft n := n; (* "<<" *)
    (* binop_width BinaryShiftRightArithmetic n := n; (* ">>>" *) *)
    binop_width BinaryShiftLeftArithmetic n := n; (* "<<<" *)
    (* binop_width BinaryLogicalImplication n := 1; (* "->" *) *)
    (* binop_width BinaryLogicalEquivalence n := 1 (* "<->" *) *)
  .

  Equations unop_width : Verilog.unaryop -> N -> N :=
    unop_width UnaryPlus n := n.

  Global Transparent binop_width unop_width.

  Inductive expression : N -> Type :=
  | BinaryOp {w} (op : binop) : expression w -> expression w -> expression (binop_width op w)
  | UnaryOp {w} (op : unaryop) : expression w -> expression (unop_width op w)
  | Conditional {w_val w_cond : N} : expression w_cond -> expression w_val -> expression w_val -> expression w_val
  | BitSelect {w_val w_sel} : expression w_val -> expression w_sel -> expression 1
  (* We break up the concatenation to make the type more convenient *)
  | Concatenation {w1 w2} (e1 : expression w1) (e2 : expression w2) : expression (w1 + w2)
  | IntegerLiteral (w : N) : BV.bitvector w -> expression w
  | NamedExpression (w : N) : string -> expression w
  | Resize {w_from} (w_to : N) : expression w_from -> expression w_to
  .

  Definition expr_type {w} (e : expression w) := w.

  Inductive statement :=
  | Block (body : list statement)
  | BlockingAssign {w} (lhs rhs : expression w)
  | NonBlockingAssign {w} (lhs rhs : expression w)
  | If {w_cond} (condition : expression w_cond) (trueBranch falseBranch : statement)
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
      ; modVariables : list variable
      ; modBody : list module_item
      }.

  Module Notations.
    Notation "[ hi .: lo ]" :=
      (Vector hi lo)
        (format "[ hi '.:' lo ]").
  End Notations.

  Definition input_vars (v : vmodule) : list variable :=
    map_opt (fun p => match varPort p with
                   | Some PortIn => Some p
                   | _ => None
                   end)
      (modVariables v).

  Definition output_vars (v : vmodule) : list variable :=
    map_opt (fun p => match varPort p with
                   | Some PortOut => Some p
                   | _ => None
                   end)
      (modVariables v).

  Definition input_names (v : vmodule) : list string :=
    map varName (input_vars v).

  Definition output_names (v : vmodule) : list string :=
    map varName (output_vars v).

  Definition input_widths (v : vmodule) : list (N * string) :=
    map (fun v => (varWidth v, varName v)) (input_vars v).

  Definition output_widths (v : vmodule) : list (N * string) :=
    map (fun v => (varWidth v, varName v)) (output_vars v).
End Verilog.
