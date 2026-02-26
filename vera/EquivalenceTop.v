From vera Require Import Verilog.
From vera Require VerilogSemantics.
Import VerilogSemantics.Sort.
From vera Require Import VerilogSMT.
Import (coercions) SMT.
From vera Require AssignmentForwarding.
From vera Require DropInternal.
From vera Require VerilogEquivalence.

From ExtLib Require Import Structures.Monads.

From Stdlib Require Import String.

From Equations Require Import Equations.

Import MonadLetNotation.
Local Open Scope monad_scope.
Local Open Scope string.

Definition sort_module (v : Verilog.vmodule) : string + Verilog.vmodule :=
  let* sorted_body :=
    match sort_module_items (Verilog.module_inputs v) (Verilog.modBody v) with
    | None => inl "Module not sortable"
    | Some sorted => inr sorted
    end in
  ret {|
    Verilog.modName := Verilog.modName v;
    Verilog.modVariableDecls := Verilog.modVariableDecls v;
    Verilog.modBody := sorted_body
  |}.

Definition equivalence_query_general (verilog1 verilog2 : Verilog.vmodule) : sum string (SMT.smt_with_namemap) :=
  let* sorted1 := sort_module verilog1 in
  let* inlined1 := AssignmentForwarding.forward_assignments sorted1 in
  let* internal_dropped1 := DropInternal.drop_internal inlined1 in

  let* sorted2 := sort_module verilog2 in
  let* inlined2 := AssignmentForwarding.forward_assignments sorted2 in
  let* internal_dropped2 := DropInternal.drop_internal inlined2 in

  VerilogEquivalence.equivalence_query internal_dropped1 internal_dropped2.

From vera Require Import VerilogSMT.
From vera Require Import SMTQueries.
From vera Require Import VerilogSemantics.
Import CombinationalOnly.
Import Equivalence.
Import ExactEquivalence.
From vera Require Import Common.
From vera Require Import Tactics.
From vera Require Import AssignmentForwardingCorrect.
From vera Require Import VerilogEquivalenceCorrectness.

From Stdlib Require Import Relations.
From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Setoid.

Local Open Scope verilog.

Theorem sort_module_equivalent v1 v2 :
  sort_module v1 = inr v2 ->
  v1 ~~~ v2.
Proof.
  unfold sort_module. intros H. monad_inv.
  apply equal_exact_equivalence; try reflexivity; expect 1.
  unfold run_vmodule. simpl.
  unfold Verilog.module_inputs in *; simpl in *.
  intros regs. rewrite E0.
  rewrite sort_module_items_stable
    by eauto using sort_module_items_sorted.
  reflexivity.
Qed.

Lemma equivalence_query_clean_left v1 v2 smt :
  VerilogEquivalence.equivalence_query v1 v2 = inr smt ->
  clean_module v1.
Proof.
  intros H.
  unfold VerilogEquivalence.equivalence_query in H.
  monad_inv.
  eapply VerilogEquivalenceCorrectness.verilog_to_smt_clean.
  eassumption.
Qed.

Lemma equivalence_query_clean_right v1 v2 smt :
  VerilogEquivalence.equivalence_query v1 v2 = inr smt ->
  clean_module v2.
Proof.
  intros H.
  unfold VerilogEquivalence.equivalence_query in H.
  monad_inv.
  eapply VerilogEquivalenceCorrectness.verilog_to_smt_clean.
  eassumption.
Qed.

Lemma transfer_clean v1 v2 :
  v1 ~~~ v2 ->
  clean_module v1 ->
  clean_module v2.
Proof.
  intros [Hinput_names Houtput_names Hequiv].
  unfold clean_module.
  rewrite <- Hinput_names, Houtput_names.
  intros Hclean e Hinputs_defined.
  specialize (Hclean e Hinputs_defined).
  destruct Hclean as [e' [Hrun [Hinputs Houtputs_defined]]].
  specialize (Hequiv e'). destruct Hequiv as [Hequiv _].
  unfold "⇓" in Hequiv. edestruct Hequiv as [e'' [Hrun'' [Hinputs'' [Houtputs_defined'' Hmatch'']]]]; clear Hequiv. 
  - exists e'. repeat split.
    + setoid_rewrite <- Hinputs at 1.
      apply Hrun.
    + setoid_rewrite <- Hinputs. 
      apply VerilogToSMTCorrect.defined_value_for_has_value_for.
      apply Hinputs_defined.
    + apply VerilogToSMTCorrect.defined_value_for_has_value_for.
      rewrite <- Houtput_names in Houtputs_defined.
      apply Houtputs_defined.
  - symmetry in Hmatch''.
    rewrite <- Hinput_names, <- Houtput_names in *.
    RegisterState.unpack_match_on.
    exists e''. repeat split.
    + rewrite Hinputs at 1. apply Hrun''.
    + transitivity e'; eassumption.
    + rewrite <- H0. apply Houtputs_defined.
Qed.

Global Instance Proper_equivalent_behaviour_exact_equivalence :
  Proper
    (exact_equivalence ==> exact_equivalence ==> iff)
    (equivalent_behaviour).
Proof.
  intros v1 v2 Heq v1' v2' Heq'. split; intro Heq_behaviour.
  - constructor.
    + destruct Heq, Heq', Heq_behaviour. congruence.
    + destruct Heq, Heq', Heq_behaviour. congruence.
    + destruct Heq_behaviour.
      eapply transfer_clean; eassumption.
    + destruct Heq_behaviour.
      eapply transfer_clean; eassumption.
    + destruct Heq, Heq', Heq_behaviour.
      setoid_rewrite <- execution_match0.
      setoid_rewrite <- execution_match1.
      setoid_rewrite <- inputs_same0.
      setoid_rewrite <- outputs_same0.
      assumption.
  - constructor.
    + destruct Heq, Heq', Heq_behaviour. congruence.
    + destruct Heq, Heq', Heq_behaviour. congruence.
    + destruct Heq_behaviour.
      eapply transfer_clean; try symmetry; eassumption.
    + inv Heq_behaviour.
      eapply transfer_clean; try symmetry; eassumption.
    + destruct Heq, Heq', Heq_behaviour.
      setoid_rewrite execution_match0.
      setoid_rewrite execution_match1.
      setoid_rewrite inputs_same0.
      setoid_rewrite outputs_same0.
      assumption.
Qed.

Theorem equivalence_query_general_unsat_correct v1 v2 smt :
  equivalence_query_general v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ (SMT.query smt)) ->
  equivalent_behaviour v1 v2.
Proof.
  unfold equivalence_query_general.
  intros. monad_inv.
  do 2 apply_somewhere AssignmentForwardingCorrect.assignment_forwarding_exact_equivalence.
  do 2 apply_somewhere sort_module_equivalent.
  do 2 apply_somewhere DropInternal.drop_internal_correct.
  apply_somewhere VerilogEquivalenceCorrectness.equivalence_query_unsat_correct; [|eassumption].
  repeat match goal with
         | [ H : ?l ~~~ ?l' |- ?l ~~ ?r ] => rewrite H; clear H
         | [ H : ?r ~~~ ?r' |- ?l ~~ ?r ] => rewrite H; clear H
	 end.
  assumption.
Qed.

Lemma counterexample_transfer v1 v2 v1' v2' e1 e2 :
  v1 ~~~ v1' ->
  v2 ~~~ v2' ->
  counterexample_execution v1 e1 v2 e2 ->
  counterexample_execution v1' e1 v2' e2.
Proof.
  intros [] [] Hcounterexample.
  unfold counterexample_execution in *.
  rewrite <- execution_match0.
  rewrite <- execution_match1.
  rewrite <- inputs_same0.
  rewrite <- outputs_same0.
  assumption.
Qed.

Global Instance Proper_counterexample_execution_exact_equivalence :
  Proper
    (exact_equivalence ==> eq ==> exact_equivalence ==> eq ==> iff)
    counterexample_execution.
Proof.
  repeat intro; subst; split; intro.
  - eapply counterexample_transfer; eauto.
  - eapply counterexample_transfer; (symmetry + idtac); eauto.
Qed.

Theorem equivalence_query_general_sat_correct v1 v2 smt ρ :
  equivalence_query_general v1 v2 = inr smt ->
  satisfied_by ρ (SMT.query smt) ->
  exists e1 e2, counterexample_execution v1 e1 v2 e2.
Proof.
  intros. unfold equivalence_query_general in *. monad_inv.
  do 2 apply_somewhere AssignmentForwardingCorrect.assignment_forwarding_exact_equivalence.
  do 2 apply_somewhere sort_module_equivalent.
  do 2 apply_somewhere DropInternal.drop_internal_correct.
  repeat match goal with
         | [ H : ?l ~~~ ?l' |- context[?l] ] => setoid_rewrite H; clear H
	 end.
  eexists. eexists.
  eapply equivalence_query_sat_correct; eassumption.
Qed.

Print Assumptions equivalence_query_general_unsat_correct.
Print Assumptions equivalence_query_general_sat_correct.
