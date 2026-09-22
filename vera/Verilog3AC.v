From vera Require Import Verilog.
From vera Require Import Variables.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import Bitvector.
From vera Require Import Common.
From vera Require Import VerilogSemantics.
Import Verilog.
Import ExactEquivalence.
Import CombinationalOnly.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Programming.Show.

From Stdlib Require Import BinNums.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import String.
From Stdlib Require Import List.

From Equations Require Import Equations.

Import MonadLetNotation.
Import ListNotations.
Import Verilog.Notations.
Local Open Scope monad_scope.
Local Open Scope string.
Local Open Scope list.
Local Open Scope verilog_scope.

Import EqNotations.
Import SigTNotations.
Opaque N.add N.sub.

Definition result := sum string.

Section definition.
  Notation tmp_var idx w wf := (Var.MkVariable ("t" ++ to_string idx)%string w wf).

  Notation assign_var var expr := (AlwaysComb (BlockingAssign (AssignVar var) AssignVar_wf expr)).

  Equations to_3ac_assign (fresh : nat) (var : Var.t) (expr : Verilog.expression (Var.varType var))
    : result (list module_item * nat) by struct expr := {
    | fresh, Var.MkVariable name _ wf, NamedExpression var' =>
      let var := Var.MkVariable name (Var.varType var') wf in
      inr ([assign_var var (NamedExpression var')], fresh)
    | fresh, Var.MkVariable name _ wf, @ArithmeticOp w op lhs rhs =>
      let var := Var.MkVariable name w wf in
      let lhs_var := tmp_var fresh w wf in
      let rhs_var := tmp_var (S fresh) w wf in
      let fresh_1 := S (S fresh) in
      let* (lhs_items, fresh_2) := to_3ac_assign fresh_1 lhs_var lhs in
      let* (rhs_items, fresh_3) := to_3ac_assign fresh_2 rhs_var rhs in
      let mi := assign_var var (ArithmeticOp op (NamedExpression lhs_var) (NamedExpression rhs_var)) in
      inr (lhs_items ++ rhs_items ++ [mi], fresh_3)
    | fresh, Var.MkVariable name _ wf, @BitwiseOp w op lhs rhs =>
      let var := Var.MkVariable name w wf in
      let lhs_var := tmp_var fresh w wf in
      let rhs_var := tmp_var (S fresh) w wf in
      let fresh_1 := S (S fresh) in
      let* (lhs_items, fresh_2) := to_3ac_assign fresh_1 lhs_var lhs in
      let* (rhs_items, fresh_3) := to_3ac_assign fresh_2 rhs_var rhs in
      let mi := assign_var var (BitwiseOp op (NamedExpression lhs_var) (NamedExpression rhs_var)) in
      inr (lhs_items ++ rhs_items ++ [mi], fresh_3)
    | fresh, Var.MkVariable name _ wf, @ShiftOp w1 w2 op lhs rhs wf_lhs wf_rhs =>
      let var := Var.MkVariable name w1 wf in
      let lhs_var := tmp_var fresh w1 wf_lhs in
      let rhs_var := tmp_var (S fresh) w2 wf_rhs in
      let fresh_1 := S (S fresh) in
      let* (lhs_items, fresh_2) := to_3ac_assign fresh_1 lhs_var lhs in
      let* (rhs_items, fresh_3) := to_3ac_assign fresh_2 rhs_var rhs in
      let mi := assign_var var (ShiftOp op (NamedExpression lhs_var) (NamedExpression rhs_var) wf_lhs wf_rhs) in
      inr (lhs_items ++ rhs_items ++ [mi], fresh_3)
    | fresh, Var.MkVariable name _ wf, @UnaryOp w op operand =>
      let var := Var.MkVariable name (unaryop_result op w) wf in
      let* wf_operand := assert_dec (w > 0)%N "Unexpected 0 width" in
      let operand_var := tmp_var fresh w wf_operand in
      let fresh_1 := S fresh in
      let* (operand_items, fresh_2) := to_3ac_assign fresh_1 operand_var operand in
      let mi := assign_var var (UnaryOp op (NamedExpression operand_var)) in
      inr (operand_items ++ [mi], fresh_2)
    | fresh, Var.MkVariable name _ wf, @Conditional w_val w_cond cond if_true if_false =>
      let var := Var.MkVariable name w_val wf in
      let* wf_cond := assert_dec (w_cond > 0)%N "Unexpected 0 width" in
      let cond_var := tmp_var fresh w_cond wf_cond in
      let if_true_var := tmp_var (S fresh) w_val wf in
      let if_false_var := tmp_var (S (S fresh)) w_val wf in
      let fresh_1 := S (S (S fresh)) in
      let* (cond_items, fresh_2) := to_3ac_assign fresh_1 cond_var cond in
      let* (if_true_items, fresh_3) := to_3ac_assign fresh_2 if_true_var if_true in
      let* (if_false_items, fresh_4) := to_3ac_assign fresh_3 if_false_var if_false in
      let mi := assign_var var (Conditional (NamedExpression cond_var) (NamedExpression if_true_var) (NamedExpression if_false_var)) in
      inr (cond_items ++ if_true_items ++ if_false_items ++ [mi], fresh_4)
    | fresh, Var.MkVariable name _ wf, @RangeSelect w slice =>
      let var := Var.MkVariable name w wf in
      inr ([assign_var var (RangeSelect slice)], fresh)
    | fresh, Var.MkVariable name _ wf, @BitSelect w_sel vec sel =>
      let var := Var.MkVariable name 1%N wf in
      let* wf_sel := assert_dec (w_sel > 0)%N "Unexpected 0 width" in
      let sel_var := tmp_var fresh w_sel wf_sel in
      let fresh_1 := S fresh in
      let* (sel_items, fresh_2) := to_3ac_assign fresh_1 sel_var sel in
      let mi := assign_var var (BitSelect vec (NamedExpression sel_var)) in
      inr (sel_items ++ [mi], fresh_2)
    | fresh, Var.MkVariable name _ wf, @Concatenation w1 w2 lhs rhs =>
      let var := Var.MkVariable name (w1 + w2)%N wf in
      let* wf_lhs := assert_dec (w1 > 0)%N "Unexpected 0 width" in
      let* wf_rhs := assert_dec (w2 > 0)%N "Unexpected 0 width" in
      let lhs_var := tmp_var fresh w1 wf_lhs in
      let rhs_var := tmp_var (S fresh) w2 wf_rhs in
      let fresh_1 := S (S fresh) in
      let* (lhs_items, fresh_2) := to_3ac_assign fresh_1 lhs_var lhs in
      let* (rhs_items, fresh_3) := to_3ac_assign fresh_2 rhs_var rhs in
      let mi := assign_var var (Concatenation (NamedExpression lhs_var) (NamedExpression rhs_var)) in
      inr (lhs_items ++ rhs_items ++ [mi], fresh_3)
    | fresh, Var.MkVariable name _ wf, @Replication w count operand =>
      let var := Var.MkVariable name (count * w)%N wf in
      let* wf_operand := assert_dec (w > 0)%N "Unexpected 0 width" in
      let operand_var := tmp_var fresh w wf_operand in
      let fresh_1 := S fresh in
      let* (operand_items, fresh_2) := to_3ac_assign fresh_1 operand_var operand in
      let mi := assign_var var (Replication count (NamedExpression operand_var)) in
      inr (operand_items ++ [mi], fresh_2)
    | fresh, Var.MkVariable name _ wf, IntegerLiteral w value =>
      let var := Var.MkVariable name w wf in
      inr ([assign_var var (IntegerLiteral w value)], fresh)
    | fresh, Var.MkVariable name _ wf, @Resize w_from w_to operand wf_to =>
      let var := Var.MkVariable name w_to wf in
      let* wf_operand := assert_dec (w_from > 0)%N "Unexpected 0 width" in
      let operand_var := tmp_var fresh w_from wf_operand in
      let fresh_1 := S fresh in
      let* (operand_items, fresh_2) := to_3ac_assign fresh_1 operand_var operand in
      let mi := assign_var var (Resize w_to (NamedExpression operand_var) wf_to) in
      inr (operand_items ++ [mi], fresh_2)
    }.

  Definition to_3ac_module_item (fresh : nat) (mi : module_item) : result (list module_item * nat) :=
    match mi with
    | AlwaysComb (BlockingAssign (AssignVar var) _ expr) => to_3ac_assign fresh var expr
    | AlwaysComb (BlockingAssign target _ _) => inl ("Unexpected assign LHS in 3AC pass: " ++ to_string target)%string
    end.

  Fixpoint to_3ac_module_body (fresh_1 : nat) (body : list module_item) : result (list module_item * nat) :=
    match body with
    | mi :: mis =>
      let* (mi_expanded, fresh_2) := to_3ac_module_item fresh_1 mi in
      let* (mis_expanded, fresh_3) := to_3ac_module_body fresh_2 mis in
      inr (mi_expanded ++ mis_expanded, fresh_3)
    | [] => inr ([], fresh_1)
    end.

  Definition to_3ac_vmodule {i o} (v : vmodule i o) : result (vmodule i o) :=
    traceBracket ("Convert to 3AC " ++ Verilog.modName v) (
      assert_dec (vmodule_sorted v) "Unsorted module in break_concat_assigns";;
      let* (body, _) := to_3ac_module_body 0 (modBody v) in
      ret {|
        modName := modName v;
        modBody := body; 
        modWfIODisjoint := modWfIODisjoint v;
        modWfInputsNoDup := modWfInputsNoDup v;
        modWfOutputsNoDup := modWfOutputsNoDup v;
      |}).
End definition.

Theorem to_3ac_exact_equivalence {i o} (v1 v2 : vmodule i o) :
  to_3ac_vmodule v1 = inr v2 ->
  v1 ~~~ v2.
Proof. Admitted.
