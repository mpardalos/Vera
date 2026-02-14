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
From vera Require VerilogSemantics.
Import VerilogSemantics.Sort (module_items_sorted).

Import List.ListNotations.
Local Open Scope list.
Import EqNotations.
Import MonadLetNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Section inline_one.
  Context (var : Verilog.variable).
  Context (replacement : Verilog.expression (Verilog.varType var)).

  Equations
    apply_substitution_expr {w} : expression w -> expression w := {
    | NamedExpression other_var with (dec (other_var = var)) => {
      | left eq_refl => replacement
      | right _ => NamedExpression other_var
    }
    (* These just walk the tree *)
    | ArithmeticOp op lhs rhs => ArithmeticOp op (apply_substitution_expr lhs) (apply_substitution_expr rhs)
    | BitwiseOp op lhs rhs => (BitwiseOp op (apply_substitution_expr lhs) (apply_substitution_expr rhs))
    | ShiftOp op lhs rhs => (ShiftOp op (apply_substitution_expr lhs) (apply_substitution_expr rhs))
    | UnaryOp p e => (UnaryOp p (apply_substitution_expr e))
    | Conditional cond ifT ifF => (Conditional (apply_substitution_expr cond) (apply_substitution_expr ifT) (apply_substitution_expr ifF))
    | BitSelect vec idx => BitSelect (apply_substitution_expr vec) (apply_substitution_expr idx)
    | Concatenation lhs rhs => (Concatenation (apply_substitution_expr lhs) (apply_substitution_expr rhs))
    | IntegerLiteral _ val => IntegerLiteral _ val
    | Resize to e => (Resize to (apply_substitution_expr e))
    }.

  Equations
    apply_substitution_module_body : list module_item -> list module_item := {
    | [] => []
    | ((AlwaysComb (BlockingAssign lhs rhs)) :: tl) =>
       (AlwaysComb (BlockingAssign lhs (apply_substitution_expr rhs))) :: apply_substitution_module_body tl
    }.
End inline_one.

Lemma apply_substitution_module_body_length v r l :
  List.length (apply_substitution_module_body v r l) = List.length l.
Proof. funelim (apply_substitution_module_body v r l); crush. Qed.

Equations forward_assignments_body (mis : list module_item) : string + list module_item by wf (List.length mis) lt := {
| [] => inr []
| (AlwaysComb (BlockingAssign (NamedExpression var) rhs) :: tl) =>
  let* tl' := forward_assignments_body (apply_substitution_module_body var rhs tl) in
  inr (AlwaysComb (BlockingAssign (NamedExpression var) rhs) :: tl')
| (_ :: _) => inl "always_comb block with invalid structure in inlining stage"
}.
Next Obligation. rewrite apply_substitution_module_body_length. lia. Qed.

Definition forward_assignments (m : vmodule) : string + vmodule :=
  assert_dec (List.NoDup (module_body_writes (modBody m))) "Duplicate write";;
  assert_dec (module_items_sorted (module_inputs m) (modBody m)) "Module items unsorted" ;;
  let* body := forward_assignments_body (modBody m) in
  inr {|
    modName := modName m;
    modVariableDecls := modVariableDecls m;
    modBody := body
  |}.
