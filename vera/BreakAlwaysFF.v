From vera Require Import Verilog.
From vera Require Import VerilogSemantics.
From vera Require Import Common.
Import Verilog.
Import ExactEquivalence.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Traversable Data.List.
From Stdlib Require Import String List.
From Equations Require Import Equations.

Import MonadLetNotation.
Import ListNotations.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Local Open Scope verilog_scope.

Equations break_always_ff_statement (stmt : statement)
    : string + list module_item by struct stmt :=
  break_always_ff_statement (NonblockingAssign lhs wf rhs) :=
    inr [AlwaysFF (NonblockingAssign lhs wf rhs)];
  break_always_ff_statement (BlockingAssign _ _ _) :=
    inl "Unexpected blocking assignment inside always_ff in BreakAlwaysFF";
  break_always_ff_statement (If _ _ _) :=
    inl "Unexpected If inside always_ff in BreakAlwaysFF";
  break_always_ff_statement (Block body) := break_always_ff_body body
  where break_always_ff_body (body : list statement)
      : string + list module_item by struct body :=
    break_always_ff_body [] := inr [];
    break_always_ff_body (stmt :: rest) :=
      let* items := break_always_ff_statement stmt in
      let* rest' := break_always_ff_body rest in
      inr (List.app items rest')
  .

Definition break_always_ff_module_item (mi : module_item) : string + list module_item :=
  match mi with
  | AlwaysFF stmt => break_always_ff_statement stmt
  | _ => inr [mi]
  end.

Definition break_always_ff_module_body (body : list module_item) : string + list module_item :=
  let* bodies := mapT break_always_ff_module_item body in
  inr (List.concat bodies).

Definition break_always_ff_vmodule {i o} (v : vmodule i o) : string + vmodule i o :=
  traceBracket ("Break always_ff " ++ modName v) (
    let* body := break_always_ff_module_body (modBody v) in
    inr {|
      modName := modName v;
      modBody := body;
      modWfIODisjoint := modWfIODisjoint v;
      modWfInputsNoDup := modWfInputsNoDup v;
      modWfOutputsNoDup := modWfOutputsNoDup v;
    |}).

Theorem break_always_ff_exact_equivalence {i o} (v1 v2 : vmodule i o) :
  break_always_ff_vmodule v1 = inr v2 ->
  v1 ~~~ v2.
Proof. Admitted.
