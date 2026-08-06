From vera Require Import Verilog.
From vera Require Import Variables.
From vera Require VerilogSemantics.
Import VerilogSemantics.Sort.
From vera Require Import VerilogSMT.
From vera Require Import VerilogSimpl.
From vera Require Import BreakConstAssigns.
From vera Require Import DropUnused.
From vera Require VerilogEquivalence.
From vera Require Import Common.
From vera Require Import VerilogSemantics.
From vera Require Import Tactics.
Import CombinationalOnly.
Import DefinedEquivalence.
Import ExactEquivalence.

From ExtLib Require Import Structures.Monads.

From Stdlib Require Import String.

From Equations Require Import Equations.

Import MonadLetNotation.
Local Open Scope monad_scope.
Local Open Scope string.
Local Open Scope verilog_scope.

Module Pass.
  Record t := Mk {
    pass_name : string;
    pass_apply :> Verilog.vmodule -> string + Verilog.vmodule;
    pass_correct : forall v1 v2, pass_apply v1 = inr v2 -> v1 ~~~ v2
  }.

  #[program]
  Definition pure
    (name : string)
    (f : Verilog.vmodule -> Verilog.vmodule)
    (f_correct : forall v, f v ~~~ v)
    : t := {|
      pass_name := name;
      pass_apply v := ret (f v)
    |}.
  Next Obligation. symmetry. apply f_correct. Qed.

  #[program]
  Definition compose (p1 p2 : t) : t := {|
    pass_name := pass_name p1 ++ " ∘ " ++ pass_name p2;
    pass_apply v :=
      let* v' := pass_apply p1 v in
      pass_apply p2 v'
  |}.
  Next Obligation.
    monad_inv.
    transitivity v.
    - eapply pass_correct. eassumption.
    - eapply pass_correct. eassumption.
  Qed.
End Pass.

Import (coercions) Pass.

Declare Scope pass_scope.
Delimit Scope pass_scope with pass.

Infix "∘" := Pass.compose (at level 20, right associativity) : pass_scope.

Local Open Scope pass.

Definition sort_vmodule (v : Verilog.vmodule) : string + Verilog.vmodule :=
  traceBracket ("Sort " ++ Verilog.modName v) (
    let* sorted_body :=
      match sort_module_items (LocationSet.of_varset (VarSet.of_list (Verilog.module_inputs v))) (Verilog.modBody v) with
      | None => inl "Module not sortable"
      | Some sorted => inr sorted
      end in
    ret {|
      Verilog.modName := Verilog.modName v;
      Verilog.modVariableDecls := Verilog.modVariableDecls v;
      Verilog.modBody := sorted_body
    |}
  ).

Theorem sort_vmodule_exact_equivalence v1 v2 :
  sort_vmodule v1 = inr v2 ->
  v1 ~~~ v2.
Proof.
  unfold sort_vmodule. intros H.
  simpl in H. monad_inv.
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

Definition sort_vmodule_pass : Pass.t :=
  Pass.Mk "Sort" sort_vmodule sort_vmodule_exact_equivalence.
Definition simpl_vmodule_pass : Pass.t :=
  Pass.pure "Simpl" simpl_vmodule simpl_vmodule_exact_equivalence.
Definition break_const_assigns_pass : Pass.t :=
  Pass.pure "BreakConstAssigns" break_const_assigns_vmodule break_const_assigns_exact_equivalence.
Definition drop_unused_pass : Pass.t :=
  Pass.Mk "DropUnused" drop_unused drop_unused_exact_equivalence.

Definition verilog_pipeline : Pass.t :=
  sort_vmodule_pass
  ∘ simpl_vmodule_pass
  ∘ break_const_assigns_pass
  ∘ drop_unused_pass.

Definition lower_verilog :=
  Pass.pass_apply verilog_pipeline.

Definition verilog_to_smt_general t verilog : sum string SMTQueries.query :=
  let* verilog' := verilog_pipeline verilog in
  VerilogToSMT.verilog_to_smt t verilog'.

Definition equivalence_query_general (verilog1 verilog2 : Verilog.vmodule) : sum string SMTQueries.query :=
  let* verilog1' := verilog_pipeline verilog1 in
  let* verilog2' := verilog_pipeline verilog2 in

  VerilogEquivalence.equivalence_query verilog1' verilog2'.

(****** Continue here **********)

From vera Require Import VerilogSMT.
From vera Require Import SMTQueries.
From vera Require Import VerilogEquivalenceCorrectness.

From Stdlib Require Import Relations.
From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Setoid.

Lemma equivalence_query_clean_left v1 v2 smt :
  VerilogEquivalence.equivalence_query v1 v2 = inr smt ->
  clean_module v1.
Proof.
  intros H.
  unfold VerilogEquivalence.equivalence_query in H.
  simpl in H.
  monad_inv.
  eapply VerilogToSMTCorrect.verilog_to_smt_clean.
  eassumption.
Qed.

Lemma equivalence_query_clean_right v1 v2 smt :
  VerilogEquivalence.equivalence_query v1 v2 = inr smt ->
  clean_module v2.
Proof.
  intros H.
  unfold VerilogEquivalence.equivalence_query in H.
  simpl in H.
  monad_inv.
  eapply VerilogToSMTCorrect.verilog_to_smt_clean.
  eassumption.
Qed.

Opaque verilog_pipeline.

Theorem equivalence_query_general_unsat_correct v1 v2 smt :
  equivalence_query_general v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ smt) ->
  v1 ~~ v2.
Proof.
  unfold equivalence_query_general.
  intros. monad_inv.
  rewrite Pass.pass_correct with (v1:=v1) by eassumption.
  rewrite Pass.pass_correct with (v1:=v2) by eassumption.
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
  eapply counterexample_transfer with (v1:=v) (v2:=v0).
  - symmetry. eapply Pass.pass_correct. eassumption.
  - symmetry. eapply Pass.pass_correct. eassumption.
  - eapply equivalence_query_sat_correct. all: eassumption.
Qed.

Print Assumptions equivalence_query_general_unsat_correct.
Print Assumptions equivalence_query_general_sat_correct.
