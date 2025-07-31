From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import BinNums.

From ExtLib Require Import Programming.Show.

From vera Require Import Common.
From vera Require Import Bitvector.
From vera Require Import Decidable.
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

  Record variable_declaration :=
    MkVariableDeclaration
      { varDeclPort : option port_direction
      ; varDeclVectorDeclaration : vector_declaration
      ; varDeclStorageType : StorageType
      ; varDeclName : string
      }.

  Definition varDeclWidth (v : variable_declaration) : N := vector_declaration_width (varDeclVectorDeclaration v).
End VerilogCommon.

Module Verilog.
  Include VerilogCommon.

  Definition vtype := N.

  Definition name := string.

  Record variable :=
    MkVariable
      { varName : name
      ; varType : vtype
      }.

  #[global]
  Instance dec_eq_variable (x y : variable) : DecProp (x = y) :=
    mk_dec_eq.

  Definition variable_of_decl (decl : variable_declaration) : variable :=
    {| varName := varDeclName decl
    ; varType := varDeclWidth decl
    |}.

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
  | NamedExpression (var : Verilog.variable) : expression (Verilog.varType var)
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
      { modName : name
      ; modVariableDecls : list variable_declaration
      ; modBody : list module_item
      }.

  Definition modVariables (v : vmodule) : list variable :=
    map variable_of_decl (modVariableDecls v).

  Module Notations.
    Notation "[ hi .: lo ]" :=
      (Vector hi lo)
        (format "[ hi '.:' lo ]").
  End Notations.

  Definition module_inputs (v : Verilog.vmodule) : list variable :=
    map_opt
      (fun decl =>
         match varDeclPort decl with
         | Some PortIn => Some (variable_of_decl decl)
         | _ => None
         end)
      (modVariableDecls v).

  Definition module_outputs (v : Verilog.vmodule) : list variable :=
    map_opt
      (fun decl =>
         match varDeclPort decl with
         | Some PortOut => Some (variable_of_decl decl)
         | _ => None
         end)
      (modVariableDecls v).

  Definition var_names : list variable -> list name :=
    map varName.

  Equations
    expr_reads {w} : Verilog.expression w -> list Verilog.variable :=
    expr_reads (Verilog.UnaryOp op operand) :=
      expr_reads operand ;
    expr_reads (Verilog.BinaryOp op lhs rhs) :=
      expr_reads lhs ++ expr_reads rhs ;
    expr_reads (Verilog.Conditional cond tBranch fBranch) :=
      expr_reads cond ++ expr_reads tBranch ++ expr_reads fBranch ;
    expr_reads (Verilog.BitSelect vec idx) :=
      expr_reads vec ++ expr_reads idx;
    expr_reads (Verilog.Resize t expr) :=
      expr_reads expr;
    expr_reads (Verilog.Concatenation e1 e2) :=
      expr_reads e1 ++ expr_reads e2 ;
    expr_reads (Verilog.IntegerLiteral _ val) :=
      [] ;
    expr_reads (Verilog.NamedExpression var) :=
      [var].

  Equations
    statement_reads : Verilog.statement -> list Verilog.variable :=
    statement_reads (Verilog.Block stmts) :=
      statement_reads_lst stmts ;
    statement_reads (Verilog.If cond trueBranch falseBranch) :=
      expr_reads cond ++ statement_reads trueBranch ++ statement_reads falseBranch ;
    statement_reads (Verilog.BlockingAssign lhs rhs) :=
      expr_reads rhs ; (* ONLY looking at rhs here *)
    statement_reads (Verilog.NonBlockingAssign lhs rhs) :=
      expr_reads rhs ; (* ...and here *)
  where statement_reads_lst : list Verilog.statement -> list Verilog.variable :=
    statement_reads_lst [] := [];
    statement_reads_lst (hd :: tl) :=
      statement_reads hd ++ statement_reads_lst tl;
  .

  Equations
    statement_writes : Verilog.statement -> list Verilog.variable :=
    statement_writes (Verilog.Block stmts) :=
      statement_writes_lst stmts ;
    statement_writes (Verilog.If cond trueBranch falseBranch) :=
      statement_writes trueBranch ++ statement_writes falseBranch ;
    statement_writes (Verilog.BlockingAssign lhs rhs) :=
      expr_reads lhs ; (* ONLY looking at lhs here *)
    statement_writes (Verilog.NonBlockingAssign lhs rhs) :=
      expr_reads lhs ; (* ...and here *)
  where statement_writes_lst : list Verilog.statement -> list Verilog.variable :=
    statement_writes_lst [] := [];
    statement_writes_lst (hd :: tl) :=
      statement_writes hd ++ statement_writes_lst tl;
  .

  Equations module_item_reads_comb : Verilog.module_item -> list Verilog.variable :=
    module_item_reads_comb (Verilog.AlwaysComb stmt) => statement_reads stmt ;
    module_item_reads_comb (Verilog.AlwaysFF _) => [] ;
    (* TODO: idk if this is right? Initial blocks definitely don't matter
      after initalization, but maybe there should be some kind of check for
      that? In any case, only matters once we do synchronous *)
    module_item_reads_comb (Verilog.Initial stmt) => [] ;
  .

  Equations module_item_writes_comb : Verilog.module_item -> list Verilog.variable :=
    module_item_writes_comb (Verilog.AlwaysComb stmt) => statement_writes stmt ;
    module_item_writes_comb (Verilog.AlwaysFF _) => [] ;
    (* TODO: See above comment. *)
    module_item_writes_comb (Verilog.Initial stmt) => [] ;
  .
End Verilog.
