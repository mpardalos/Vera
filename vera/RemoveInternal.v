From Stdlib Require Import BinNums.
From Stdlib Require Import List.
From Stdlib Require Import String.

From Equations Require Import Equations.
From ExtLib Require Import Structures.Monads.

From vera Require Import Verilog.
Import Verilog.
From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import VerilogSemantics.
Import CombinationalOnly.
Import ExactEquivalence.

Import ListNotations.
Local Open Scope list.
Import EqNotations.
Import MonadLetNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Local Open Scope verilog.

Equations module_body_drop_vars (vars : list variable) (body : list module_item) : list (module_item) :=
  module_body_drop_vars vars [] := [];
  module_body_drop_vars vars (AlwaysComb (BlockingAssign (NamedExpression var) rhs) :: body) with dec (In var vars) := {
    | left _ => module_body_drop_vars vars body
    | right _ => AlwaysComb (BlockingAssign (NamedExpression var) rhs) :: module_body_drop_vars vars body
  };
  module_body_drop_vars vars ((AlwaysComb (BlockingAssign _ _)) :: body) := body
  .

Definition decls_drop_internal := List.filter
  (fun d => match varDeclPort d with
          | Some _ => true
	  | None => false
	  end).

Definition find_internal_vars := map_opt
  (fun d => match varDeclPort d with
          | Some _ => None
	  | None => Some (variable_of_decl d)
	  end).

Definition decls_find_internal_vars := List.filter
  (fun d => match (varDeclPort d) with
          | Some _ => true
	  | None => false
	  end).

Definition vmodule_drop_internal (m : vmodule) : string + vmodule :=
  assert_dec (list_subset (module_body_reads (modBody m)) (module_inputs m))
    "Internal read remains in drop_internal";;
  assert_dec ((module_items_sorted (module_inputs m) (modBody m)))
    "Unsorted module in drop_internal";;
  let decls := decls_drop_internal (modVariableDecls m) in
  let internal_vars := find_internal_vars (modVariableDecls m) in
  let body := module_body_drop_vars internal_vars (modBody m) in
  ret {|
    modName := modName m;
    modVariableDecls := decls;
    modBody := body
  |}.

Lemma decls_drop_internal_keep_inputs decls :
  Verilog.inputs_of_decls (decls_drop_internal decls) =
  inputs_of_decls decls.
Proof.
  funelim (Verilog.inputs_of_decls decls); simpl.
  - reflexivity.
  - rewrite Heq. simp inputs_of_decls. rewrite Heq. simpl.
    rewrite H. reflexivity.
  - rewrite Heq. simp inputs_of_decls. rewrite Heq. simpl.
    rewrite H. reflexivity.
  - rewrite Heq. simp inputs_of_decls.
Qed.

Lemma decls_drop_internal_keep_outputs decls :
  Verilog.outputs_of_decls (decls_drop_internal decls) =
  outputs_of_decls decls.
Proof.
  funelim (Verilog.outputs_of_decls decls); simpl.
  - reflexivity.
  - rewrite Heq. simp outputs_of_decls. rewrite Heq. simpl.
    rewrite H. reflexivity.
  - rewrite Heq. simp outputs_of_decls. rewrite Heq. simpl.
    rewrite H. reflexivity.
  - rewrite Heq. simp outputs_of_decls.
Qed.

(* TODO: Move me to VerilogSemantics *)
Lemma limit_to_regs_twice e vars : e // vars // vars = e // vars.
Proof. Admitted.

(* Not quite right. This is missing "They should crash together" *)
Lemma exact_by_output_equality v1 v2:
  module_inputs v1 = module_inputs v2 ->
  module_outputs v1 = module_outputs v2 ->
  (forall initial final1 final2,
    run_vmodule v1 initial = Some final1 ->
    run_vmodule v2 initial = Some final2 ->
    final1 =( module_outputs v1 )= final2) ->
  v1 ~~~ v2.
Proof. Admitted.

Theorem vmodule_drop_internal_correct v1 v2 :
  vmodule_drop_internal v1 = inr v2 ->
  v1 ~~~ v2.
Proof.
  intros H.
  unfold vmodule_drop_internal in H.
  monad_inv.
  apply exact_by_output_equality.
  - symmetry. apply decls_drop_internal_keep_inputs.
  - symmetry. apply decls_drop_internal_keep_outputs.
  - intros * Hrun1 Hrun2.
    unfold run_vmodule in *.
    unfold module_inputs, module_outputs in *; simpl in *.
    rewrite sort_module_items_stable in *; expect 3; cycle 1.
    { assumption. }
    { unfold module_inputs in *. admit. (* TODO: Result is sorted *) }
    unfold mk_initial_state, module_inputs in *; simpl in *.
    rewrite decls_drop_internal_keep_inputs in *.
    admit.
Admitted.
