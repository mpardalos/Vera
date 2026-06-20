From vera Require Import Verilog.
From vera Require VerilogSemantics.
Import VerilogSemantics.Sort.
From vera Require Import VerilogSMT.
From vera Require Import VerilogSimpl.
From vera Require VerilogEquivalence.
From vera Require Import Common.

From ExtLib Require Import Structures.Monads.

From Stdlib Require Import String.

From Equations Require Import Equations.

Import MonadLetNotation.
Local Open Scope monad_scope.
Local Open Scope string.

Definition sort_vmodule (v : Verilog.vmodule) : string + Verilog.vmodule :=
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

Definition equivalence_query_general (verilog1 verilog2 : Verilog.vmodule) : sum string SMTQueries.query :=
  let* sorted1 := trace "Sort left" (sort_vmodule verilog1) in
  let simplified1 := trace "Simpl left" (simpl_vmodule sorted1) in

  let* sorted2 := trace "Sort right" (sort_vmodule verilog2) in
  let simplified2 := trace "Simpl right" (simpl_vmodule sorted2) in

  trace "Construct equivalence query"
    (VerilogEquivalence.equivalence_query simplified1 simplified2).

From vera Require Import VerilogSMT.
From vera Require Import SMTQueries.
From vera Require Import VerilogSemantics.
Import CombinationalOnly.
Import DefinedEquivalence.
Import ExactEquivalence.
From vera Require Import Tactics.
From vera Require Import VerilogEquivalenceCorrectness.

From Stdlib Require Import Relations.
From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Setoid.

Local Open Scope verilog.

Theorem sort_vmodule_exact_equivalence v1 v2 :
  sort_vmodule v1 = inr v2 ->
  v2 ~~~ v1.
Proof.
  unfold sort_vmodule. intros H.
  monad_inv.
  rename_match (sort_module_items _ _ = Some _) into Hsort.
  apply equal_exact_equivalence; try reflexivity; expect 1.
  unfold run_vmodule. simpl.
  unfold Verilog.module_inputs in *; simpl in *.
  apply functional_extensionality.
  intros regs. rewrite Hsort.
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

Theorem equivalence_query_general_unsat_correct v1 v2 smt :
  equivalence_query_general v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ smt) ->
  v1 ~~ v2.
Proof.
  unfold equivalence_query_general.
  intros. monad_inv.
  rewrite <- sort_vmodule_exact_equivalence with (v1:=v1) by eassumption.
  rewrite <- sort_vmodule_exact_equivalence with (v1:=v2) by eassumption.
  rewrite <- simpl_vmodule_exact_equivalence with (v:=v).
  rewrite <- simpl_vmodule_exact_equivalence with (v:=v0).
  eapply VerilogEquivalenceCorrectness.equivalence_query_unsat_correct.
  all: eassumption.
Qed.

(* This only works because ~~~ (exact equivalence) says that internal
   vars are the same. If it only matched external variables, then we
   would need to have an existential here: valid executions of v1, v2
   would have matching executions in v1', v2', but those would not be
   definitionally equal. *)
Lemma counterexample_transfer v1 v2 v1' v2' e1 e2 :
  v1 ~~~ v1' ->
  v2 ~~~ v2' ->
  counterexample_execution v1 e1 v2 e2 ->
  counterexample_execution v1' e1 v2' e2.
Proof.
  unfold counterexample_execution.
  intros Heq1 Heq2 [Hadmit1 [Hadmit2 [Hmatch_inputs Hmatch_outputs]]].
  (* eexists. eexists. *)
  unpack_goal.
  - rewrite <- Heq1. apply Hadmit1.
  - rewrite <- Heq2. apply Hadmit2.
  - erewrite <- exact_equivalence_same_inputs by eassumption.
    eassumption.
  - erewrite <- exact_equivalence_same_outputs by eassumption.
    eassumption.
Qed.

(* Proof using this rewrite only works because all of our
   verilog-to-verilog passes (sort, simplify) preserve internal variables
   exactly. If any of them added/removed vars, then we would need a
   more relaxed equivalence, and that would not transfer counter-examples
   exactly. The transferring would involve existentials (if there is a
   counter-example for one module then there is one for the other, and the
   two match on external ports)*)

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
  satisfied_by ρ smt ->
  exists e1 e2, counterexample_execution v1 e1 v2 e2.
Proof.
  intros. unfold equivalence_query_general in *. monad_inv.
  eexists. eexists.
  eapply counterexample_transfer with (v1:=simpl_vmodule v) (v2:=simpl_vmodule v0).
  - rewrite simpl_vmodule_exact_equivalence.
    apply sort_vmodule_exact_equivalence.
    assumption.
  - rewrite simpl_vmodule_exact_equivalence.
    apply sort_vmodule_exact_equivalence.
    assumption.
  - eapply equivalence_query_sat_correct.
    all: eassumption.
Qed.

Print Assumptions equivalence_query_general_unsat_correct.
Print Assumptions equivalence_query_general_sat_correct.
