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

  Equations to_3ac_assign (fresh : nat) (var : Var.t) (expr : Verilog.expression (Var.varType var))
    : result (list module_item * nat) by struct expr := {
    | fresh, Var.MkVariable name _ wf, NamedExpression var' =>
      let var := Var.MkVariable name (Var.varType var') wf in
      inr ([AlwaysComb (BlockingAssign (AssignVar var) AssignVar_wf (NamedExpression var'))], fresh)
    | fresh, Var.MkVariable name _ wf, @ArithmeticOp w op lhs rhs =>
      let var := Var.MkVariable name w wf in
      let lhs_var := tmp_var fresh w wf in
      let rhs_var := tmp_var (S fresh) w wf in
      let fresh_1 := S (S fresh) in
      let* (lhs_items, fresh_2) := to_3ac_assign fresh_1 lhs_var lhs in
      let* (rhs_items, fresh_3) := to_3ac_assign fresh_2 rhs_var rhs in
      let mi :=
        AlwaysComb (BlockingAssign
          (AssignVar var) AssignVar_wf
          (ArithmeticOp op (NamedExpression lhs_var) (NamedExpression rhs_var)))
        in
      inr (lhs_items ++ rhs_items ++ [mi], fresh_3)
    | _, _, _ => inl "TODO"%string
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
