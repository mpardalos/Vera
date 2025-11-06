From Coq Require Import BinNums.

From Equations Require Import Equations.
From ExtLib Require Import Structures.Monads.

From vera Require Import Verilog.
Import Verilog.
From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import AssignmentForwarding.AssignmentForwarding.

Import EqNotations.
Import MonadLetNotation.

Require Import VerilogSemantics.
Import CombinationalOnly.

Lemma expr_inline_var_correct {w} regs var (replacement : expression (varType var)) (e : expression w) :
  regs var = eval_expr regs replacement ->
  eval_expr regs e = eval_expr regs (expr_inline_var var replacement e).
Proof.
  funelim (expr_inline_var var replacement e);
    intros; simp expr_inline_var eval_expr;
    try rewrite <- H by assumption;
    try rewrite <- H0 by assumption;
    try rewrite <- H1 by assumption;
    try reflexivity.
  - unfold expr_inline_var_clause_1.
    rewrite Heq.
    crush.
  - unfold expr_inline_var_clause_1.
    rewrite Heq.
    now simp eval_expr.
Qed.
