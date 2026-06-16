From vera Require Import Verilog.
From vera Require Import VerilogSMT.
From vera Require Import SMTQueries.
From vera Require Import Common.
From vera Require Import Bitvector.
From vera Require VerilogToSMT.
From vera Require VerilogToSMT.VerilogToSMTCorrect.
From vera Require Import VerilogEquivalence.
From vera Require VerilogSemantics.
Import VerilogSemantics.Sort (vmodule_sortable).
From vera Require Import Tactics.
From vera Require Import Decidable.

Import VerilogSemantics.
Import VerilogSemantics.CombinationalOnly.
Import DefinedEquivalence.

From Stdlib Require Import Relations.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Lia.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Classical.
From Stdlib Require Import ZArith.
From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Setoid.

From Equations Require Import Equations.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Data.Monads.OptionMonad.
From ExtLib Require Import Data.List.

Import (notations) RegisterState.
Import MonadLetNotation.
Import ListNotations.
Import EqNotations.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
Local Open Scope verilog.

Import SigTNotations.

Ltac decompose_all_records :=
  repeat match goal with
         | [ H : _ |- _ ] => progress (decompose record H); clear H
	 end.

Definition smt_same_value var (ρ : SMTLib.valuation) :=
  ρ (verilog_to_smt_var VerilogLeft var) =
  ρ (verilog_to_smt_var VerilogRight var).

Definition smt_all_same_values (vars : list Verilog.variable) (ρ : SMTLib.valuation) :=
  Forall (fun verilogName => smt_same_value verilogName ρ) vars.

Lemma smt_all_same_values_cons var vars ρ :
  smt_all_same_values (var :: vars) ρ <->
    smt_same_value var ρ /\ smt_all_same_values vars ρ.
Proof. apply List.Forall_cons_iff. Qed.

Definition smt_distinct_value (var : Verilog.variable) (ρ : SMTLib.valuation) :=
  ρ (verilog_to_smt_var VerilogLeft var) <>
  ρ (verilog_to_smt_var VerilogRight var).

Definition smt_some_distinct_values vars (ρ : SMTLib.valuation) :=
  Exists (fun verilogName => smt_distinct_value verilogName ρ) vars.

Definition counterexample_valuation v1 v2 ρ :=
  smt_all_same_values (Verilog.module_inputs v1) ρ
  /\ smt_some_distinct_values (Verilog.module_outputs v1) ρ
  /\ v1 ⇓ execution_of_valuation VerilogLeft ρ
  /\ v2 ⇓ execution_of_valuation VerilogRight ρ
  .

Definition execution_some_distinct_value (C : Verilog.variable -> Prop) (e1 e2 : execution) : Prop :=
  exists var bv1 bv2,
    C var
    /\ e1 var = XBV.from_bv bv1
    /\ e2 var = XBV.from_bv bv2
    /\ bv1 <> bv2.

Definition counterexample_execution v1 e1 v2 e2 :=
  v1 ⇓ e1
  /\ v2 ⇓ e2
  /\ e1 =!!(Verilog.module_inputs v1)!!= e2
  /\ ~ (e1 =(Verilog.module_outputs v1)= e2).

Lemma smt_some_distinct_values_cons var vars ρ :
  smt_some_distinct_values (var :: vars) ρ <->
    smt_distinct_value var ρ \/ smt_some_distinct_values vars ρ.
Proof. apply List.Exists_cons. Qed.

Lemma term_reflect_false P :
  (forall ρ, ~ P ρ) ->
  term_reflect SMTLib.Term_False P.
Proof. unfold term_reflect, term_satisfied_by. crush. Qed.

Lemma term_reflect_eq s (t1 t2 : SMTLib.term s):
  term_reflect (SMTLib.Term_Eq t1 t2) (fun ρ => SMTLib.interp_term ρ t1 = SMTLib.interp_term ρ t2).
Proof.
  unfold term_reflect, term_satisfied_by.
  intros.
  simpl.
  apply SMTLib.value_eqb_eq.
Qed.

Lemma term_reflect_not P (t : SMTLib.term SMTLib.Sort_Bool):
  term_reflect t (fun ρ => P ρ) ->
  term_reflect (SMTLib.Term_Not t) (fun ρ => ~ P ρ).
Proof.
  unfold term_reflect, term_satisfied_by.
  intros H1. simpl.
  setoid_rewrite <- H1.
  crush.
Qed.

Lemma mk_var_same_spec : forall name,
  term_reflect (mk_var_same name) (smt_same_value name).
Proof.
  unfold mk_var_same, smt_same_value.
  intros * Hfunc.
  apply term_reflect_eq.
Qed.

Global Instance term_reflect_proper :
  Proper
    (eq ==> pointwise_relation SMTLib.valuation iff ==> iff)
    term_reflect.
Proof.
  unfold term_reflect.
  typeclasses eauto.
Qed.

Lemma mk_inputs_same_spec : forall inputs,
  term_reflect (mk_inputs_same inputs) (smt_all_same_values inputs).
Proof.
  intros ?. induction inputs.
  - simp mk_inputs_same.
    unfold smt_all_same_values.
    setoid_rewrite List.Forall_nil_iff.
    crush.
  - intros. simp mk_inputs_same in *.
    unfold smt_all_same_values.
    setoid_rewrite Forall_cons_iff.
    apply term_reflect_and.
    + apply mk_var_same_spec.
    + apply IHinputs.
Qed.

Lemma mk_var_distinct_spec name :
  term_reflect (mk_var_distinct name) (smt_distinct_value name).
Proof.
  intros *.
  unfold mk_var_distinct, smt_distinct_value.
  apply term_reflect_not.
  apply term_reflect_eq.
Qed.

Lemma mk_outputs_distinct_spec outputs :
  term_reflect (mk_outputs_distinct outputs) (smt_some_distinct_values outputs).
Proof.
  induction outputs.
  - simp mk_outputs_distinct.
    apply term_reflect_false.
    intros ρ contra.
    inv contra.
  - intros.
    simp mk_outputs_distinct.
    unfold smt_some_distinct_values.
    setoid_rewrite Exists_cons.
    apply term_reflect_or.
    + apply mk_var_distinct_spec.
    + apply IHoutputs.
Qed.

Lemma satisfied_by_cons_iff t q ρ :
  satisfied_by ρ (t :: q) <->
  term_satisfied_by ρ t /\ satisfied_by ρ q.
Proof. apply List.Forall_cons_iff. Qed.

Lemma satisfied_by_app_iff q1 q2 ρ :
  satisfied_by ρ (q1 ++ q2)%list <->
  satisfied_by ρ q1 /\ satisfied_by ρ q2.
Proof. apply List.Forall_app. Qed.

Lemma smt_reflect_cons t q P1 P2 :
  term_reflect t P1 ->
  smt_reflect q P2 ->
  smt_reflect (t :: q) (fun ρ => P1 ρ /\ P2 ρ).
Proof.
  unfold term_reflect, smt_reflect.
  intros H1 H2.
  setoid_rewrite satisfied_by_cons_iff.
  setoid_rewrite H1.
  setoid_rewrite H2.
  reflexivity.
Qed.
  
Lemma smt_reflect_app q1 q2 P1 P2 :
  smt_reflect q1 P1 ->
  smt_reflect q2 P2 ->
  smt_reflect (q1 ++ q2)%list (fun ρ => P1 ρ /\ P2 ρ).
Proof.
  unfold term_reflect, smt_reflect.
  intros H1 H2.
  setoid_rewrite satisfied_by_app_iff.
  setoid_rewrite H1.
  setoid_rewrite H2.
  reflexivity.
Qed.

Theorem equivalence_query_spec verilog1 verilog2 smt :
  equivalence_query verilog1 verilog2 = inr smt ->
  smt_reflect
    smt
    (counterexample_valuation verilog1 verilog2).
Proof.
  unfold equivalence_query.
  intros H.
  monad_inv.
  simpl in *.
  unfold counterexample_valuation.

  repeat (apply smt_reflect_cons || apply smt_reflect_app); expect 4.
  - apply mk_inputs_same_spec; eassumption.
  - apply mk_outputs_distinct_spec; eassumption.
  - apply VerilogToSMTCorrect.verilog_to_smt_correct; eassumption.
  - apply VerilogToSMTCorrect.verilog_to_smt_correct; eassumption.
Qed.

Lemma smt_same_values_eq var vars ρ :
  smt_all_same_values vars ρ ->
  In var vars ->
  ρ (verilog_to_smt_var VerilogLeft var) = ρ (verilog_to_smt_var VerilogRight var).
Proof.
  unfold smt_all_same_values, smt_same_value.
  intros Hmatch Hin.
  rewrite List.Forall_forall in Hmatch.
  apply Hmatch.
  apply Hin.
Qed.

Lemma smt_distinct_values_not_defined_match vars ρ :
  smt_some_distinct_values vars ρ ->
  ~ (execution_of_valuation VerilogLeft ρ =(vars)= execution_of_valuation VerilogRight ρ).
Proof.
  unfold smt_some_distinct_values.
  rewrite List.Exists_exists.
  intros [var [Hin Hsmt_distinct]] contra.
  unfold smt_distinct_value in Hsmt_distinct.
  unfold "_ =( _ )= _" in contra.
  specialize (contra var Hin).
  unfold execution_of_valuation in contra.
  decompose_all_records. 
  apply XBV.from_bv_injective in contra.
  contradiction.
Qed.

Lemma smt_all_same_values_execution_match vars ρ :
  smt_all_same_values vars ρ ->
  (execution_of_valuation VerilogLeft ρ) =!!(
    vars
  )!!= (execution_of_valuation VerilogRight ρ).
Proof.
  unfold smt_all_same_values, smt_same_value.
  rewrite List.Forall_forall.
  intros Hmatch.
  apply RegisterState.defined_match_on_iff.
  intros var Hvar. specialize (Hmatch var Hvar).
  unfold execution_of_valuation.
  rewrite Hmatch.
  eauto.
Qed.

Lemma execution_defined_match_smt_all_same_values vars ρ :
  (execution_of_valuation VerilogLeft ρ) =!!(vars)!!= (execution_of_valuation VerilogRight ρ) ->
  smt_all_same_values vars ρ.
Proof.
  rewrite RegisterState.defined_match_on_iff.
  unfold smt_all_same_values, smt_same_value.
  rewrite List.Forall_forall.
  intros H var Hvar_in.
  insterU H. destruct H as [bv [Hlookup_left Hlookup_right]].

  eapply execution_of_valuation_inv in Hlookup_left.
  eapply execution_of_valuation_inv in Hlookup_right.
  congruence.
Qed.

Lemma imply_or_iff P Q :
  (~ P \/ Q) <-> (P -> Q).
Proof.
  split.
  - apply or_to_imply.
  - apply imply_to_or.
Qed.

Lemma not_and_or_iff P Q :
  ~ (P /\ Q) <-> (~ P \/ ~ Q).
Proof.
  split.
  - apply not_and_or.
  - apply or_not_and.
Qed.

Lemma not_defined_match_some_distinct C e1 e2 :
  RegisterState.defined_value_for C e1 ->
  RegisterState.defined_value_for C e2 ->
  ~ (e1 =!!{ C }!!= e2) ->
  execution_some_distinct_value C e1 e2.
Proof.
  rewrite RegisterState.defined_match_on_iff.
  unfold
    execution_some_distinct_value,
    RegisterState.defined_value_for
    in *.
  intros Hvalues_left Hvalues_right H.
  apply not_all_ex_not in H.
  destruct H as [var Hvar].
  exists var.
  setoid_rewrite <- imply_or_iff at 2 in Hvar.
  apply not_or_and in Hvar.
  destruct Hvar as [HC Hvar].
  apply NNPP in HC.
  insterU Hvalues_left. insterU Hvalues_right.
  destruct Hvalues_left as [bv_left Hbv_left].
  destruct Hvalues_right as [bv_right Hbv_right].
  rewrite Hbv_left in *. clear Hbv_left.
  rewrite Hbv_right in *. clear Hbv_right.
  exists bv_left, bv_right.
  repeat split; eauto; [].
  intro contra. subst bv_right.
  apply Hvar. clear Hvar. crush.
Qed.

Lemma not_execution_defined_match_on_smt_some_distinct_values vars ρ :
  execution_some_distinct_value
    (fun var : Verilog.variable => In var vars)
    (execution_of_valuation VerilogLeft ρ)
    (execution_of_valuation VerilogRight ρ) ->
  smt_some_distinct_values vars ρ.
Proof.
  unfold execution_some_distinct_value, smt_some_distinct_values, smt_distinct_value in *.
  rewrite List.Exists_exists.
  intros [var [bv1 [bv2 [Hin [Hlookup_left [Hlookup_right Hneq]]]]]].
  apply execution_of_valuation_inv in Hlookup_left. decompose record Hlookup_left.
  apply execution_of_valuation_inv in Hlookup_right. decompose record Hlookup_right.
  eexists. split; [eassumption|].
  congruence.
Qed.

Lemma defined_match_on_defined_value_left C e1 e2 :
  RegisterState.execution_defined_match_on C e1 e2 ->
  RegisterState.defined_value_for C e1.
Proof. unfold RegisterState.execution_defined_match_on. crush. Qed.

Lemma defined_match_on_defined_value_right C e1 e2 :
  RegisterState.execution_defined_match_on C e1 e2 ->
  RegisterState.defined_value_for C e2.
Proof.
  unfold RegisterState.execution_defined_match_on.
  intros [Hmatch Hdefined].
  rewrite <- Hmatch.
  apply Hdefined.
Qed.

Local Open Scope verilog.

Global Instance match_on_eq_subrelation (P : Verilog.variable -> Prop) : 
  subrelation eq (RegisterState.match_on P).
Proof. intros a b <-. reflexivity. Qed.

Global Instance Proper_valid_execution v :
  Proper
    (RegisterState.match_on (fun var => In var (Verilog.modVariables v)) ==> iff)
    (valid_execution v).
Proof.
  repeat intro.
  unfold valid_execution.
  RegisterState.unpack_match_on.
  assert (Hmatch_inputs : x =( Verilog.module_inputs v)= y)
    by now setoid_rewrite Verilog.module_input_in_vars.
  split.
  all: intros H1.
  - setoid_rewrite <- H at 2.
    setoid_rewrite <- Hmatch_inputs.
    apply H1.
  - rewrite H at 2.
    setoid_rewrite Hmatch_inputs.
    apply H1.
Qed.

Ltac assert_rewrite r :=
  let H := fresh "H" in
  assert ( H : r ); [|rewrite H; clear H].

Lemma list_subset_empty {A} (l : list A) :
  list_subset [] l.
Proof. apply Forall_nil. Qed.

Lemma execution_congruent v e1 e2 :
  v ⇓ e1 -> v ⇓ e2 ->
  e1 =( Verilog.module_inputs v )= e2 ->
  e1 =( Verilog.module_outputs v )= e2.
Proof.
  unfold "⇓".
  intros Hadmit1 Hadmit2 Hinput_match.
  RegisterState.unpack_match_on.
  assert (Houtputs1 : run_vmodule v e1 =( Verilog.module_outputs v )= e1)
    by now setoid_rewrite Verilog.module_outputs_in_vars.
  rewrite <- Houtputs1.
  assert (Houtputs2 : run_vmodule v e2 =( Verilog.module_outputs v )= e2)
    by now setoid_rewrite Verilog.module_outputs_in_vars.
  rewrite <- Houtputs2.
  rewrite Hinput_match.
  reflexivity.
Qed.

Lemma no_counterexample_equivalent_iff v1 v2 :
  Verilog.module_inputs v1 = Verilog.module_inputs v2 ->
  Verilog.module_outputs v1 = Verilog.module_outputs v2 ->
  clean_module v1 ->
  clean_module v2 ->
  (forall e1 e2, ~ counterexample_execution v1 e1 v2 e2) <-> (v1 ~~ v2).
Proof.
  intros Hinput_match Houtput_match Hclean1 Hclean2.
  unfold counterexample_execution.
  split. 
  - intros H.
    constructor; try assumption; [idtac].
    intros e Hno_exes.
    (* split; intros He.
     * (\* This is duplicated, ideally we want a "without loss of generality" tactic *\)
     * + RegisterState.unpack_defined_value_for. *)
    assert (Hmatch_inputs : run_vmodule v1 e =!!( Verilog.module_inputs v1 )!!= run_vmodule v2 e). {
      split.
      - rewrite preserve_inputs by assumption.
        rewrite Hinput_match.
        rewrite preserve_inputs by assumption.
	reflexivity.
      - rewrite preserve_inputs by assumption.
        apply Hno_exes.
    }
    assert (Hrun1 : v1 ⇓ run_vmodule v1 e). {
      apply admit_run_vmodule.
      apply Hclean1.
    }
    assert (Hrun2 : v2 ⇓ run_vmodule v2 e). {
      apply admit_run_vmodule.
      apply Hclean2.
    }
    specialize (H (run_vmodule v1 e) (run_vmodule v2 e)).
    apply not_and_or in H. destruct H; [contradiction|].
    apply not_and_or in H. destruct H; [contradiction|].
    apply not_and_or in H. destruct H; [contradiction|].
    apply NNPP in H.
    assumption.
  - intros [] e1 e2 [Hadmit1 [Hadmit2 [[Hmatch_inputs Hinputs_defined] Hno_match_outputs]]].
    unfold "⇓" in Hadmit1, Hadmit2.
    contradict Hno_match_outputs.
    assert (Hmatch_outputs1 : run_vmodule v1 e1 =( Verilog.module_outputs v1 )= e1)
      by now setoid_rewrite Verilog.module_outputs_in_vars.
    assert (Hmatch_outputs2 : run_vmodule v2 e2 =( Verilog.module_outputs v2 )= e2)
      by now setoid_rewrite Verilog.module_outputs_in_vars.
    rewrite <- Hmatch_outputs1.
    rewrite <- Houtput_match in Hmatch_outputs2. rewrite <- Hmatch_outputs2.
    rewrite Hinput_match in Hmatch_inputs. setoid_rewrite <- Hmatch_inputs.
    apply execution_match0.
    apply Hinputs_defined.
Qed.

Lemma not_equivalent_counterexample_iff v1 v2 :
  Verilog.module_inputs v1 = Verilog.module_inputs v2 ->
  Verilog.module_outputs v1 = Verilog.module_outputs v2 ->
  clean_module v1 ->
  clean_module v2 ->
  (exists e1 e2, counterexample_execution v1 e1 v2 e2) <-> ~ (v1 ~~ v2).
Proof.
  intros Hinput_match Houtput_match Hclean1 Hclean2.
  setoid_rewrite <- no_counterexample_equivalent_iff; try assumption; [idtac].
  split.
  - intros [e1 [e2 H1]] H2. eapply H2. eapply H1.
  - intros H1.
    apply not_all_ex_not in H1. destruct H1 as [e1 H1].
    apply not_all_ex_not in H1. destruct H1 as [e2 H1].
    apply NNPP in H1.
    exists e1, e2. apply H1.
Qed.

Record verilog_to_smt_checked (v : Verilog.vmodule) := MkVerilogToSMTChecked {
    io_disjoint : disjoint (Verilog.module_inputs v) (Verilog.module_outputs v);
    no_duplicate_writes : NoDup (Verilog.module_body_writes (Verilog.modBody v));
    (* no_duplicate_outputs : NoDup (Verilog.module_outputs v); *)
    all_vars_driven : Permutation (Verilog.modVariables v) (Verilog.module_body_writes (Verilog.modBody v) ++ Verilog.module_inputs v);
    sorted : module_items_sorted (Verilog.module_inputs v) (Verilog.modBody v);
}.

Lemma verilog_to_smt_checks tag v smt :
  VerilogToSMT.verilog_to_smt tag v = inr smt ->
  verilog_to_smt_checked v.
Proof.
  intros H.
  unfold VerilogToSMT.verilog_to_smt in H. monad_inv.
  constructor; try assumption.
Qed.

Record equivalence_query_checked (v1 v2 : Verilog.vmodule) := MkEquivalenceQueryChecked {
  verilog_to_smt_eqn1 : exists tag smt, VerilogToSMT.verilog_to_smt tag v1 = inr smt;
  verilog_to_smt_eqn2 : exists tag smt, VerilogToSMT.verilog_to_smt tag v2 = inr smt;
  verilog_to_smt_checked1 : verilog_to_smt_checked v1;
  verilog_to_smt_checked2 : verilog_to_smt_checked v2;
  inputs_match : Verilog.module_inputs v1 = Verilog.module_inputs v2;
  outputs_match : Verilog.module_outputs v1 = Verilog.module_outputs v2;
}.

Lemma equivalence_query_checks v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  equivalence_query_checked v1 v2.
Proof.
  intros H.
  unfold equivalence_query in H. monad_inv.
  constructor; eauto using verilog_to_smt_checks.
Qed.

Lemma counterexample_valuation_execution v1 v2 ρ :
  equivalence_query_checked v1 v2 ->
  counterexample_valuation v1 v2 ρ <->
    counterexample_execution
      v1 (execution_of_valuation VerilogLeft ρ)
      v2 (execution_of_valuation VerilogRight ρ).
Proof.
  intros Hequivalence_query.
  destruct Hequivalence_query.
  inv verilog_to_smt_checked3.
  inv verilog_to_smt_checked4.
  unfold counterexample_valuation, counterexample_execution.
  split. 
  - unpack_goal.
    + assumption.
    + assumption.
    + apply smt_all_same_values_execution_match. assumption.
    + apply smt_distinct_values_not_defined_match. assumption.
  - unpack_goal.
    + apply execution_defined_match_smt_all_same_values. assumption.
    + apply not_execution_defined_match_on_smt_some_distinct_values; expect 1.
      apply not_defined_match_some_distinct.
      * apply execution_of_valuation_defined_value.
      * apply execution_of_valuation_defined_value.
      * unfold "_ =!!( _ )!!= _". intuition eauto.
    + assumption.
    + assumption.
Qed.

Theorem equivalence_query_execution_spec v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  smt_reflect
    smt
    (fun ρ => counterexample_execution
      v1 (execution_of_valuation VerilogLeft ρ)
      v2 (execution_of_valuation VerilogRight ρ)).
Proof.
  intros Hfunc.
  setoid_rewrite <- counterexample_valuation_execution;
    [|eauto using equivalence_query_checks].
  eapply equivalence_query_spec.
  assumption.
Qed.

Theorem equivalence_query_sat_correct v1 v2 smt ρ :
  equivalence_query v1 v2 = inr smt ->
  satisfied_by ρ smt ->
  counterexample_execution
    v1 (execution_of_valuation VerilogLeft ρ)
    v2 (execution_of_valuation VerilogRight ρ).
Proof.
  intros.
  eapply equivalence_query_execution_spec.
  all: eassumption.
Qed.

Lemma limit_to_regs_rewrite vars e1 e2 :
  (forall var, In var vars -> e1 var = e2 var) ->
  RegisterState.limit_to_regs vars e1 = RegisterState.limit_to_regs vars e2.
Proof.
  unfold RegisterState.limit_to_regs.
  intros Heq.
  apply functional_extensionality_dep.
  intros var. autodestruct; crush.
Qed.

Global Instance Proper_defined_match_on_impl :
  Proper
    ((pointwise_relation Verilog.variable Basics.impl) --> eq ==> eq ==> Basics.impl)
    RegisterState.execution_defined_match_on.
Proof. repeat intro. subst. crush. Qed.

Global Instance Proper_defined_match_on_match_on C:
  Proper
    (RegisterState.match_on C ==> RegisterState.match_on C ==> iff)
    (RegisterState.execution_defined_match_on C).
Proof.
  repeat intro.
  subst.
  unfold RegisterState.execution_defined_match_on.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma counterexample_execution_rewrite_left v e1 e1' v2 e2 :
  e1 =( Verilog.modVariables v )= e1' ->
  counterexample_execution v e1 v2 e2 <-> counterexample_execution v e1' v2 e2.
Proof.
  unfold counterexample_execution.
  intros H.
  split.
  all: intros [Hvalid1 [Hvalid2 [Hdefined_in Hnot_defined_out]]].
  all: unpack_goal.
  all: try eassumption.
  all: assert (Hinputs : e1 =( Verilog.module_inputs v)= e1')
         by now setoid_rewrite Verilog.module_input_in_vars.
  all: assert (Houtputs : e1 =( Verilog.module_outputs v)= e1')
         by now setoid_rewrite Verilog.module_outputs_in_vars.
  - rewrite H in Hvalid1. assumption.
  - rewrite <- Hinputs. apply Hdefined_in.
  - rewrite <- Houtputs. apply Hnot_defined_out.
  - rewrite H. assumption.
  - rewrite Hinputs. apply Hdefined_in.
  - rewrite Houtputs. apply Hnot_defined_out.
Qed.

Lemma counterexample_execution_rewrite_right v1 e1 v2 e2 e2' :
  Verilog.module_inputs v1 = Verilog.module_inputs v2 ->
  Verilog.module_outputs v1 = Verilog.module_outputs v2 ->
  e2 =( Verilog.modVariables v2 )= e2' ->
  counterexample_execution v1 e1 v2 e2 <-> counterexample_execution v1 e1 v2 e2'.
Proof.
  unfold counterexample_execution.
  intros -> -> H.
  split.
  all: intros [Hvalid1 [Hvalid2 [Hdefined_in Hnot_defined_out]]].
  all: unpack_goal.
  all: try eassumption.
  all: assert (Hinputs : e2 =( Verilog.module_inputs v2)= e2')
         by now setoid_rewrite Verilog.module_input_in_vars.
  all: assert (Houtputs : e2 =( Verilog.module_outputs v2)= e2')
         by now setoid_rewrite Verilog.module_outputs_in_vars.
  - rewrite H in Hvalid2. assumption.
  - rewrite <- Hinputs. apply Hdefined_in.
  - rewrite <- Houtputs. apply Hnot_defined_out.
  - rewrite H. assumption.
  - rewrite Hinputs. apply Hdefined_in.
  - rewrite Houtputs. apply Hnot_defined_out.
Qed.

Lemma verilog_to_smt_clean tag v smt :
  VerilogToSMT.verilog_to_smt tag v = inr smt ->
  clean_module v.
Proof.
  intros Htransf.
  edestruct (verilog_to_smt_checks _ _ _ Htransf).
  apply clean_module_statically; try eassumption; expect 1.
  eexists. apply sort_module_items_stable. apply sorted0.
Qed.

(* TODO: Move me to semantics *)
Lemma valid_execution_all_vars_defined v e :
  clean_module v ->
  v ⇓ e ->
  RegisterState.defined_value_for (fun var => List.In var (Verilog.module_inputs v)) e ->
  RegisterState.defined_value_for (fun var => List.In var (Verilog.modVariables v)) e.
Proof.
  unfold "⇓".
  intros [? Hvars_defined] Hadmit Hinputs_defined.
  rewrite <- Hadmit.
  apply Hvars_defined.
  apply Hinputs_defined.
Qed.

Lemma equivalence_query_unsat_no_counterexample v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ smt) ->
  (forall e1 e2, ~ counterexample_execution v1 e1 v2 e2).
Proof.
  intros Hquery Hunsat e1 e2 Hcounterexample.
  destruct (equivalence_query_checks v1 v2 smt)
    as [[? [? ?]] [? [? ?]] ? ? inputs_match outputs_match];
    [assumption|].
  eapply Hunsat with (ρ := valuation_of_executions e1 e2).
  eapply equivalence_query_execution_spec; eauto.
  erewrite
    counterexample_execution_rewrite_left,
    counterexample_execution_rewrite_right.
  all: try eassumption.
  all: expect 2.
  1: eapply execution_of_valuation_right_match_on.
  2: eapply execution_of_valuation_left_match_on.
  all: unfold counterexample_execution in Hcounterexample.
  all: decompose record Hcounterexample.
  all: eapply valid_execution_all_vars_defined.
  - eapply verilog_to_smt_clean. eassumption.
  - assumption.
  - rewrite <- inputs_match.
    eapply defined_match_on_defined_value_right. eassumption.
  - eapply verilog_to_smt_clean. eassumption.
  - assumption.
  - eapply defined_match_on_defined_value_left. eassumption.
Qed.

Theorem equivalence_query_unsat_correct v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ smt) ->
  v1 ~~ v2.
Proof.
  intros Hquery Hunsat.
  destruct (equivalence_query_checks v1 v2 smt)
    as [[? [? ?]] [? [? ?]] [] [] inputs_match outputs_match];
    [assumption|].
  apply no_counterexample_equivalent_iff; eauto using verilog_to_smt_clean.
  eapply equivalence_query_unsat_no_counterexample; eauto.
Qed.

Print Assumptions equivalence_query_unsat_correct.
