From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import BinNums.

From ExtLib Require Import Programming.Show.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Data.Monads.EitherMonad.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.Monads.

From vera Require Import Common.
From vera Require Import Tactics.
From vera Require Import Bitvector.
From vera Require Import Decidable.
Import (notations) Bitvector.RawBV.

Require Import List.
From Coq Require Arith Lia Program.
From Coq Require Import Structures.Equalities.
From Coq Require Arith.PeanoNat.
From Equations Require Import Equations.

Import ListNotations.
Import MonadLetNotation.
Import SigTNotations.
Local Open Scope monad_scope.

Module VerilogCommon.
  Variant arithmeticop :=
    | ArithmeticPlus (* '+' *)
    | ArithmeticMinus (* '-' *)
    | ArithmeticStar (* '*' *)
    (* | ArithmeticSlash (* '/' *) *)
    (* | ArithmeticPercent (* '%' *) *)
    (* | BinaryExponent (* '**' *) *)
    .

Variant bitwiseop :=
    | BinaryBitwiseAnd (* '&' *)
    | BinaryBitwiseOr (* '|' *)
    (* | BinaryBitwiseXor (* '^' *) *)
  .

  (* Variant logicalop :=
   *   | BinaryEqualsEquals (\* '==' *\)
   *   | BinaryEqualsEqualsEquals (\* '===' *\)
   *   | BinaryGreaterThan (\* '>' *\)
   *   | BinaryGreaterThanEqual (\* '>=' *\)
   *   | BinaryLessThan (\* '<' *\)
   *   | BinaryLessThanEqual (\* '<=' *\)
   *   | BinaryLogicalAnd (\* '&&' *\)
   *   | BinaryLogicalEquivalence (\* '<->' *\)
   *   | BinaryLogicalImplication (\* '->' *\)
   *   | BinaryLogicalOr (\* '||' *\)
   *   | BinaryNotEquals (\* '!=' *\)
   *   | BinaryNotEqualsEquals (\* '!==' *\)
   *   | BinaryWildcardEqual (\* '==?' *\)
   *   | BinaryWildcardNotEqual (\* '!=?' *\)
   *   | BinaryXNor (\* '^~', '~^' *\)
   * . *)

  Variant shiftop :=
    | BinaryShiftRight (* '>>' *)
    | BinaryShiftLeft (* '<<' *)
    (* | BinaryShiftRightArithmetic (* '>>>' *) *)
    | BinaryShiftLeftArithmetic (* '<<<' *)
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
    Global Instance arithmeticop_Show : Show arithmeticop :=
      { show u :=
          match u with
          | ArithmeticPlus => "+"
          | ArithmeticMinus => "-"
          | ArithmeticStar => "*"
          (* | BinarySlash => "/" *)
          (* | BinaryPercent => "%" *)
          (* | BinaryExponent => "**" *)
          end
      }.

    Global Instance shiftop_Show : Show shiftop :=
      { show u :=
          match u with
          | BinaryShiftRight => ">>"
          | BinaryShiftLeft => "<<"
          (* | BinaryShiftRightArithmetic => ">>>" *)
          | BinaryShiftLeftArithmetic => "<<<"
          end
      }.

    Global Instance bitwiseop_Show : Show bitwiseop :=
      { show u :=
          match u with
          | BinaryBitwiseAnd => "&"
          | BinaryBitwiseOr => "|"
          (* | BinaryBitwiseXor => "^" *)
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

  Definition vtype := N.

  Definition name := string.

  Record variable :=
    MkVariable
      { varName : name
      ; varType : vtype
      }.

  Definition variable_of_decl (decl : variable_declaration) : variable :=
    {| varName := varDeclName decl
    ; varType := varDeclWidth decl
    |}.

End VerilogCommon.

Module Verilog.
  Include VerilogCommon.

  #[global]
  Instance dec_eq_variable (x y : variable) : DecProp (x = y) :=
    mk_dec_eq.

  Inductive expression : N -> Type :=
  | ArithmeticOp {w} (op : arithmeticop) : expression w -> expression w -> expression w
  | BitwiseOp {w} (op : bitwiseop) : expression w -> expression w -> expression w
  | ShiftOp {w1 w2} (op : shiftop) : expression w1 -> expression w2 -> expression w1
  | UnaryOp {w} (op : unaryop) : expression w -> expression w
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
      }
  .

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

  Lemma module_input_in_vars v : forall var,
      List.In var (Verilog.module_inputs v) ->
      List.In var (Verilog.modVariables v).
  Proof.
    unfold Verilog.module_inputs, Verilog.modVariables.
    induction (Verilog.modVariableDecls v); crush.
  Qed.

  Lemma module_outputs_in_vars v : forall var,
      List.In var (Verilog.module_outputs v) ->
      List.In var (Verilog.modVariables v).
  Proof.
    unfold Verilog.module_outputs, Verilog.modVariables.
    induction (Verilog.modVariableDecls v); crush.
  Qed.

  Definition var_names : list variable -> list name :=
    map varName.

  Equations
    expr_reads {w} : Verilog.expression w -> list Verilog.variable :=
    expr_reads (Verilog.UnaryOp op operand) :=
      expr_reads operand ;
    expr_reads (Verilog.ArithmeticOp op lhs rhs) :=
      expr_reads lhs ++ expr_reads rhs ;
    expr_reads (Verilog.BitwiseOp op lhs rhs) :=
      expr_reads lhs ++ expr_reads rhs ;
    expr_reads (Verilog.ShiftOp op lhs rhs) :=
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

  Equations module_item_reads : Verilog.module_item -> list Verilog.variable :=
    module_item_reads (Verilog.AlwaysComb stmt) => statement_reads stmt ;
    module_item_reads (Verilog.AlwaysFF _) => [] ;
    (* TODO: idk if this is right? Initial blocks definitely don't matter
      after initalization, but maybe there should be some kind of check for
      that? In any case, only matters once we do synchronous *)
    module_item_reads (Verilog.Initial stmt) => [] ;
  .

  Equations module_item_writes : Verilog.module_item -> list Verilog.variable :=
    module_item_writes (Verilog.AlwaysComb stmt) => statement_writes stmt ;
    module_item_writes (Verilog.AlwaysFF _) => [] ;
    (* TODO: See above comment. *)
    module_item_writes (Verilog.Initial stmt) => [] ;
  .

  Equations module_body_reads : list Verilog.module_item -> list Verilog.variable :=
    module_body_reads [] := [];
    module_body_reads (hd :: tl) := module_item_reads hd ++ module_body_reads tl
  .

  Equations module_body_writes : list Verilog.module_item -> list Verilog.variable :=
    module_body_writes [] := [];
    module_body_writes (hd :: tl) := module_item_writes hd ++ module_body_writes tl
  .

End Verilog.

Module RawVerilog.
  Include VerilogCommon.

  Inductive expression : Type :=
  | ArithmeticOp (op : arithmeticop) (lhs rhs : expression)
  | BitwiseOp (op : bitwiseop) (lhs rhs : expression)
  | ShiftOp (op : shiftop) (lhs rhs : expression)
  | UnaryOp (op : unaryop) (expr : expression)
  | Conditional (cond ifT ifF : expression)
  | BitSelect (vec idx : expression)
  (* We break up the concatenation to make the type more convenient *)
  | Concatenation (lhs rhs : expression)
  | IntegerLiteral (val : RawBV.bitvector)
  | NamedExpression (var : variable)
  | Resize (to : N) (expr : expression)
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
      { modName : name
      ; modVariableDecls : list variable_declaration
      ; modBody : list module_item
      }
  .

  Definition modVariables (v : vmodule) : list variable :=
    map variable_of_decl (modVariableDecls v).

  Definition module_inputs (v : vmodule) : list variable :=
    map_opt
      (fun decl =>
         match varDeclPort decl with
         | Some PortIn => Some (variable_of_decl decl)
         | _ => None
         end)
      (modVariableDecls v).

  Definition module_outputs (v : vmodule) : list variable :=
    map_opt
      (fun decl =>
         match varDeclPort decl with
         | Some PortOut => Some (variable_of_decl decl)
         | _ => None
         end)
      (modVariableDecls v).

  Lemma module_input_in_vars v : forall var,
      List.In var (module_inputs v) ->
      List.In var (modVariables v).
  Proof.
    unfold module_inputs, modVariables.
    induction (modVariableDecls v); crush.
  Qed.

  Lemma module_outputs_in_vars v : forall var,
      List.In var (module_outputs v) ->
      List.In var (modVariables v).
  Proof.
    unfold module_outputs, modVariables.
    induction (modVariableDecls v); crush.
  Qed.
End RawVerilog.

Module Typecheck.

Definition transf := sum string.

Equations cast_width {w1} (err : string) (w2 : N) (e : Verilog.expression w1)
  : transf (Verilog.expression w2) :=
| err, w2, e with (N.eq_dec w1 w2) => {
  | left eq_refl => inr e
  | right _ => inl (err
    ++ " (Tried to use expression of width "
    ++ to_string (N.to_nat w1) ++ " as width " ++ to_string (N.to_nat w2) ++ ")")%string
}.

Equations tc_expr (expr : RawVerilog.expression) : transf { w & Verilog.expression w } := {
| RawVerilog.ArithmeticOp op lhs rhs =>
  let* (w_lhs; t_lhs) := tc_expr lhs in
  let* (w_rhs; t_rhs) := tc_expr rhs in
  let* t_rhs' := cast_width ("Different widths in " ++ to_string op) w_lhs t_rhs in
  inr (_; Verilog.ArithmeticOp op t_lhs t_rhs')
| RawVerilog.BitwiseOp op lhs rhs =>
  let* (w_lhs; t_lhs) := tc_expr lhs in
  let* (w_rhs; t_rhs) := tc_expr rhs in
  let* t_rhs' := cast_width ("Different widths in " ++ to_string op) w_lhs t_rhs in
  inr (_; Verilog.BitwiseOp op t_lhs t_rhs')
| RawVerilog.ShiftOp op lhs rhs =>
  let* (w_lhs; t_lhs) := tc_expr lhs in
  let* (w_rhs; t_rhs) := tc_expr rhs in
  inr (_; Verilog.ShiftOp op t_lhs t_rhs)
| RawVerilog.UnaryOp op expr =>
  let* (w_expr; t_expr) := tc_expr expr in
  inr (_; Verilog.UnaryOp op t_expr)
| RawVerilog.Conditional cond ifTrue ifFalse =>
  let* (w_cond; t_cond) := tc_expr cond in
  let* (w_ifTrue; t_ifTrue) := tc_expr ifTrue in
  let* (w_ifFalse; t_ifFalse) := tc_expr ifFalse in
  let* t_ifFalse' := cast_width "Different widths in conditional" w_ifTrue t_ifFalse in
  inr (_; Verilog.Conditional t_cond t_ifTrue t_ifFalse')
| RawVerilog.BitSelect vec idx =>
  let* (w_vec; t_vec) := tc_expr vec in
  let* (w_idx; t_idx) := tc_expr idx in
  inr (_; Verilog.BitSelect t_vec t_idx)
| RawVerilog.Concatenation lhs rhs =>
  let* (w_lhs; t_lhs) := tc_expr lhs in
  let* (w_rhs; t_rhs) := tc_expr rhs in
  inr (_; Verilog.BitSelect t_lhs t_rhs)
| RawVerilog.IntegerLiteral bits =>
  inr (_; Verilog.IntegerLiteral _ (BV.of_bits bits))
| RawVerilog.NamedExpression var =>
  inr (_; Verilog.NamedExpression var)
| RawVerilog.Resize to expr =>
  let* (w_expr; t_expr) := tc_expr expr in
  inr (_; Verilog.Resize to t_expr)
}.


Equations tc_statement : RawVerilog.statement -> transf Verilog.statement := {
| RawVerilog.Block body =>
  let* t_body := tc_statement_lst body in
  inr (Verilog.Block t_body)
    where
      tc_statement_lst : list RawVerilog.statement -> transf (list Verilog.statement) := {
      | [] := inr []
      | (stmt :: stmts) :=
      	let* t_stmt := tc_statement stmt in
	let* t_stmts := tc_statement_lst stmts in
	inr (t_stmt :: t_stmts)
      }
| RawVerilog.BlockingAssign lhs rhs =>
  let* (w_lhs; t_lhs) := tc_expr lhs in
  let* (w_rhs; t_rhs) := tc_expr rhs in
  let* t_rhs' := cast_width "Different widths in blocking assign" w_lhs t_rhs in
  inr (Verilog.BlockingAssign t_lhs t_rhs')
| RawVerilog.NonBlockingAssign lhs rhs =>
  let* (w_lhs; t_lhs) := tc_expr lhs in
  let* (w_rhs; t_rhs) := tc_expr rhs in
  let* t_rhs' := cast_width "Different widths in nonblocking assign" w_lhs t_rhs in
  inr (Verilog.BlockingAssign t_lhs t_rhs')
| RawVerilog.If condition trueBranch falseBranch =>
  let* (_; t_cond) := tc_expr condition in
  let* t_trueBranch := tc_statement trueBranch in
  let* t_falseBranch := tc_statement falseBranch in
  inr (Verilog.If t_cond t_trueBranch t_falseBranch)
}
.

Equations tc_module_item : RawVerilog.module_item -> transf Verilog.module_item := {
| RawVerilog.AlwaysComb stmt =>
  let* t_stmt := tc_statement stmt in
  inr (Verilog.AlwaysComb t_stmt)
| RawVerilog.AlwaysFF stmt =>
  let* t_stmt := tc_statement stmt in
  inr (Verilog.AlwaysFF t_stmt)
| RawVerilog.Initial stmt =>
  let* t_stmt := tc_statement stmt in
  inr (Verilog.Initial t_stmt)
}.

Equations tc_module_item_lst : list RawVerilog.module_item -> transf (list Verilog.module_item) := {
| [] => inr []
| (mi :: mis) =>
  let* t_mi := tc_module_item mi in
  let* t_mis := tc_module_item_lst mis in
  inr (t_mi :: t_mis)
}.

Equations tc_vmodule : RawVerilog.vmodule -> transf Verilog.vmodule := {
| m =>
  let* t_modBody := tc_module_item_lst (RawVerilog.modBody m) in
  inr {|
      Verilog.modName := RawVerilog.modName m;
      Verilog.modVariableDecls := RawVerilog.modVariableDecls m;
      Verilog.modBody := t_modBody
  |}
}.
End Typecheck.
