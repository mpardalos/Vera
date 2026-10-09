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

Equations break_statement : (statement -> module_item) -> statement -> string + list module_item :=
  break_statement mk (NonblockingAssign lhs wf rhs) :=
    inr [mk (NonblockingAssign lhs wf rhs)];
  break_statement mk (BlockingAssign lhs wf rhs) :=
    inr [mk (BlockingAssign lhs wf rhs)];
  break_statement mk (If _ _ _) :=
    inl "Unexpected If inside always_ff in BreakAlwaysFF";
  break_statement mk (Block body) := break_body body
  where break_body : list statement -> string + list module_item :=
    break_body [] := inr [];
    break_body (stmt :: rest) :=
      let* items := break_statement mk stmt in
      let* rest' := break_body rest in
      inr (List.app items rest')
  .

Definition break_module_item (mi : module_item) : string + list module_item :=
  match mi with
  | Initial stmt => break_statement Initial stmt
  | AlwaysFF stmt => break_statement AlwaysFF stmt
  | AlwaysComb stmt => break_statement AlwaysComb stmt
  | _ => inr [mi]
  end.

Definition break_always_ff_module_body (body : list module_item) : string + list module_item :=
  let* bodies := mapT break_module_item body in
  inr (List.concat bodies).

Definition break_blocks_vmodule {i o} (v : vmodule i o) : string + vmodule i o :=
  traceBracket ("Break always_ff " ++ modName v) (
    let* body := break_always_ff_module_body (modBody v) in
    inr {|
      modName := modName v;
      modBody := body;
      modWfIODisjoint := modWfIODisjoint v;
      modWfInputsNoDup := modWfInputsNoDup v;
      modWfOutputsNoDup := modWfOutputsNoDup v;
    |}).

Theorem break_blocks_exact_equivalence {i o} (v1 v2 : vmodule i o) :
  break_blocks_vmodule v1 = inr v2 ->
  v1 ~~~ v2.
Proof. Admitted.
