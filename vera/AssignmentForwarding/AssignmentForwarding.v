From Stdlib Require Import BinNums.
From Stdlib Require List.
From Stdlib Require Import String.

From Equations Require Import Equations.
From ExtLib Require Import Structures.Monads.

From vera Require Import Verilog.
Import Verilog.
From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.

Import List.ListNotations.
Local Open Scope list.
Import EqNotations.
Import MonadLetNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Record substitution :=
  MkSubstitution {
    var : variable;
    expr : expression (varType var)
  }.

Section inline_one.
  Context (var : variable).
  Context (replacement : expression (varType var)).

  Equations
    expr_inline_var {w} : expression w -> expression w := {
    | NamedExpression other_var with (dec (other_var = var)) => {
      | left eq_refl => replacement
      | right _ => NamedExpression other_var
    }
    (* These just walk the tree *)
    | ArithmeticOp op lhs rhs => ArithmeticOp op (expr_inline_var lhs) (expr_inline_var rhs)
    | BitwiseOp op lhs rhs => (BitwiseOp op (expr_inline_var lhs) (expr_inline_var rhs))
    | ShiftOp op lhs rhs => (ShiftOp op (expr_inline_var lhs) (expr_inline_var rhs))
    | UnaryOp p e => (UnaryOp p (expr_inline_var e))
    | Conditional cond ifT ifF => (Conditional (expr_inline_var cond) (expr_inline_var ifT) (expr_inline_var ifF))
    | BitSelect vec idx => BitSelect (expr_inline_var vec) (expr_inline_var idx)
    | Concatenation lhs rhs => (Concatenation (expr_inline_var lhs) (expr_inline_var rhs))
    | IntegerLiteral _ val => IntegerLiteral _ val
    | Resize to e => (Resize to (expr_inline_var e))
    }.

  Equations
    stmt_inline_var : statement -> statement := {
    | Block stmts => Block (stmt_lst_inline_var stmts)
      where stmt_lst_inline_var : list statement -> list statement := {
      | [] => []
      | (hd :: tl) => stmt_inline_var hd :: stmt_lst_inline_var tl
      }
    | BlockingAssign lhs rhs => BlockingAssign lhs (expr_inline_var rhs)
    | NonBlockingAssign lhs rhs => BlockingAssign lhs (expr_inline_var rhs)
    | If cond ifT ifF => If (expr_inline_var cond) (stmt_inline_var ifT) (stmt_inline_var ifF)
    }.

  Equations
    module_item_inline_var : module_item -> module_item := {
    | AlwaysComb stmt => AlwaysComb (stmt_inline_var stmt)
    | AlwaysFF stmt => AlwaysFF (stmt_inline_var stmt)
    | Initial stmt => Initial (stmt_inline_var stmt)
    }.

  Equations
    module_item_lst_inline_var : list module_item -> list module_item := {
    | [] => []
    | (hd :: tl) => module_item_inline_var hd :: module_item_lst_inline_var tl
    }.

  Definition vmodule_inline_var (m : vmodule) : vmodule := {|
    modName := modName m;
    modVariableDecls := modVariableDecls m;
    modBody := module_item_lst_inline_var (modBody m)
  |}.
End inline_one.

Equations vmodule_inline_var_lst
  : list substitution -> vmodule -> vmodule := {
| [], m => m
| (MkSubstitution var replacement :: tl), m =>
  vmodule_inline_var var replacement (vmodule_inline_var_lst tl m)
}.

Equations module_item_collect_substitution (mi : module_item) : string + substitution := {
| AlwaysComb (BlockingAssign (NamedExpression var) rhs) => inr (MkSubstitution var rhs)
| AlwaysComb _ => inl "always_comb block with invalid structure in inlining stage"
| AlwaysFF _ => inl "Unexpected always_ff block in inlining stage"
| Initial _ => inl "Unexpected initial block in inlining stage"
}.

Equations module_item_lst_collect_substitutions (mis : list module_item) : string + list substitution := {
| [] => inr []
| (hd :: tl) =>
  let* sub := module_item_collect_substitution hd in
  let* subs := module_item_lst_collect_substitutions tl in
  inr (sub :: subs)
}.

Equations target_pred : (variable -> bool) -> module_item -> bool := {
| p, AlwaysComb (BlockingAssign (NamedExpression var) rhs) => p var
| _, _ => false
}.

(* TODO: Handle decls, and do in separate pass *)
(* TODO: also: deshittify *)
Definition vmodule_keep_only_outputs (m : vmodule) : vmodule := {|
  modName := modName m;
  modVariableDecls := List.filter
   (fun d => match (varDeclPort d) with | Some _ => true | None => false end)
   (modVariableDecls m);
  modBody := List.filter
    (target_pred
      (fun var => List.anyb (fun var' => String.eqb (varName var) (varName var'))
      (module_outputs m)))
    (modBody m)
|}.

Definition forward_assignments (m : vmodule) : string + vmodule :=
  let* substitutions := module_item_lst_collect_substitutions (modBody m) in
  inr (vmodule_keep_only_outputs (vmodule_inline_var_lst substitutions m)).
