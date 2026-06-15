From vera Require Import Verilog.
From vera Require Import VerilogSMT.
From vera Require Import SMTQueries.
From vera Require Import Common.
Import (coercions) VerilogSMTBijection.
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
Import Equivalence.

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

Import SigTNotations.

(* FIXME: Move me to SMT *)
Lemma match_map_vars_tag_same tag (m1 m2 : VerilogSMTBijection.t) vars :
  (forall var, m1 (tag, var) = m2 (tag, var)) ->
  match_map_vars tag m1 vars <-> match_map_vars tag m2 vars.
Proof.
  unfold match_map_vars.
  intros H. setoid_rewrite H.
  reflexivity.
Qed.

Ltac decompose_all_records :=
  repeat match goal with
         | [ H : _ |- _ ] => progress (decompose record H); clear H
	 end.

Definition smt_same_value var (m : VerilogSMTBijection.t) (ρ : SMTLib.valuation) :=
  exists smtName1 smtName2,
    m (TaggedVariable.VerilogLeft, var) = Some smtName1 /\
      m (TaggedVariable.VerilogRight, var) = Some smtName2 /\
      ρ (SMTLib.Sort_BitVec (Verilog.varType var)) smtName1 =
        ρ (SMTLib.Sort_BitVec (Verilog.varType var)) smtName2.

Definition smt_all_same_values
  (vars : list Verilog.variable) (m : VerilogSMTBijection.t) (ρ : SMTLib.valuation) :=
  Forall (fun verilogName => smt_same_value verilogName m ρ) vars.

Lemma smt_all_same_values_cons var vars m ρ :
  smt_all_same_values (var :: vars) m ρ <->
    smt_same_value var m ρ /\ smt_all_same_values vars m ρ.
Proof. apply List.Forall_cons_iff. Qed.

Definition smt_distinct_value (var : Verilog.variable) (m : VerilogSMTBijection.t) (ρ : SMTLib.valuation) :=
  exists smtName1 smtName2,
    m (TaggedVariable.VerilogLeft, var) = Some smtName1 /\
      m (TaggedVariable.VerilogRight, var) = Some smtName2 /\
      ρ (SMTLib.Sort_BitVec (Verilog.varType var)) smtName1 <>
        ρ (SMTLib.Sort_BitVec (Verilog.varType var)) smtName2.

Definition smt_some_distinct_values
  vars (m : VerilogSMTBijection.t) (ρ : SMTLib.valuation) :=
  Exists (fun verilogName => smt_distinct_value verilogName m ρ) vars.

Definition counterexample_valuation v1 v2 m ρ :=
  smt_all_same_values (Verilog.module_inputs v1) m ρ
  /\ smt_some_distinct_values (Verilog.module_outputs v1) m ρ
  /\ valid_execution v1 (execution_of_valuation TaggedVariable.VerilogLeft m ρ)
  /\ valid_execution v2 (execution_of_valuation TaggedVariable.VerilogRight m ρ)
  .

Definition execution_some_distinct_value (C : Verilog.variable -> Prop) (e1 e2 : execution) : Prop :=
  exists var bv1 bv2,
    C var
    /\ e1 var = XBV.from_bv bv1
    /\ e2 var = XBV.from_bv bv2
    /\ bv1 <> bv2.

Definition counterexample_execution v1 e1 v2 e2 :=
  valid_execution v1 e1
  /\ valid_execution v2 e2
  /\ e1 =!!(Verilog.module_inputs v1)!!= e2
  /\ ~ (e1 =(Verilog.module_outputs v1)= e2).

Lemma smt_some_distinct_values_cons var vars m ρ :
  smt_some_distinct_values (var :: vars) m ρ <->
    smt_distinct_value var m ρ \/ smt_some_distinct_values vars m ρ.
Proof. apply List.Exists_cons. Qed.

Lemma term_reflect_false P :
  (forall ρ, ~ P ρ) ->
  term_reflect SMTLib.Term_False P.
Proof. unfold term_reflect, term_satisfied_by. crush. Qed.

Lemma mk_var_same_spec : forall name m q,
  mk_var_same name m = inr q ->
  term_reflect q (smt_same_value name m).
Proof.
  intros * Hfunc.
  funelim (mk_var_same name m); try congruence.
  rewrite <- Heqcall in *. clear Heqcall. inv Hfunc.
  intros ρ.
  unfold smt_same_value, SMTQueries.term_satisfied_by.
  simpl.
  rewrite BV.bv_eq_reflect.
  split; intros * H.
  - eauto.
  - destruct H as [smt_name1' [smt_name2' [H0 [H1 H2]]]].
    replace smt_name1' with smt_name1 in * by congruence.
    replace smt_name2' with smt_name2 in * by congruence.
    apply H2.
Qed.

Global Instance term_reflect_proper :
  Proper
    (eq ==> pointwise_relation SMTLib.valuation iff ==> iff)
    term_reflect.
Proof.
  unfold term_reflect.
  typeclasses eauto.
Qed.

Lemma mk_inputs_same_spec : forall inputs m q,
  mk_inputs_same inputs m = inr q ->
  term_reflect q (smt_all_same_values inputs m).
Proof.
  intros ?. induction inputs.
  - intros. simp mk_inputs_same in *. inv H.
    unfold smt_all_same_values.
    setoid_rewrite List.Forall_nil_iff.
    crush.
  - intros. simp mk_inputs_same in H.
    autodestruct_eqn E.
    unfold smt_all_same_values.
    setoid_rewrite Forall_cons_iff.
    apply term_reflect_and.
    + apply mk_var_same_spec. apply E.
    + apply IHinputs. assumption.
Qed.

Lemma mk_var_distinct_spec name m t :
  mk_var_distinct name m = inr t ->
  term_reflect t (smt_distinct_value name m).
Proof.
  intros * Hfunc.
  funelim (mk_var_distinct name m); try congruence.
  rewrite <- Heqcall in *. clear Heqcall. inv Hfunc.
  intros ρ.
  unfold term_satisfied_by, smt_distinct_value. simpl.
  rewrite Bool.negb_true_iff.
  rewrite BV.bv_neq_reflect.
  split; intros * H.
  - eauto.
  - destruct H as [smt_name1' [smt_name2' [H0 [H1 H2]]]].
    replace smt_name1' with smt_name1 in * by congruence.
    replace smt_name2' with smt_name2 in * by congruence.
    apply H2.
Qed.

Lemma mk_outputs_distinct_spec outputs m t :
  mk_outputs_distinct outputs m = inr t ->
  term_reflect t (smt_some_distinct_values outputs m).
Proof.
  revert t m. induction outputs.
  - intros * H. simp mk_outputs_distinct in H. inv H.
    apply term_reflect_false.
    intros ρ contra.
    inv contra.
  - intros.
    simp mk_outputs_distinct in H.
    autodestruct_eqn E.
    insterU IHoutputs.
    unfold smt_some_distinct_values.
    setoid_rewrite List.Exists_cons.
    apply term_reflect_or.
    + apply mk_var_distinct_spec.
      eassumption.
    + eapply IHoutputs.
Qed.

Lemma execution_of_valuation_map_equal (m1 m2 : VerilogSMTBijection.t) tag ρ:
  (forall n, m1 (tag, n) = m2 (tag, n)) ->
  execution_of_valuation tag m1 ρ = execution_of_valuation tag m2 ρ.
Proof.
  intros.
  unfold execution_of_valuation.
  apply functional_extensionality_dep.
  intros name.
  rewrite <- H.
  reflexivity.
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
    (assertions smt)
    (counterexample_valuation verilog1 verilog2 (nameMap smt)).
Proof.
  unfold equivalence_query.
  intros H.
  monad_inv.
  simpl in *.
  remember (VerilogSMTBijection.combine _ _ _ _) as m_combined.
  unfold counterexample_valuation.

  repeat (apply smt_reflect_cons || apply smt_reflect_app); expect 4.
  - apply mk_inputs_same_spec; eassumption.
  - apply mk_outputs_distinct_spec; eassumption.
  - setoid_rewrite execution_of_valuation_map_equal. 
    + eapply VerilogToSMTCorrect.verilog_to_smt_correct.
      eassumption.
    + replace m_combined. intros.
      eapply VerilogSMTBijection.combine_different_tag_left
        with (t2 := TaggedVariable.VerilogRight).
      * discriminate.
      * eapply verilog_to_smt_only_tag; eassumption.
      * eapply verilog_to_smt_only_tag; eassumption.
  - setoid_rewrite execution_of_valuation_map_equal. 
    + eapply VerilogToSMTCorrect.verilog_to_smt_correct.
      eassumption.
    + replace m_combined. intros.
      eapply VerilogSMTBijection.combine_different_tag_right
        with (t1 := TaggedVariable.VerilogLeft).
      * discriminate.
      * eapply verilog_to_smt_only_tag; eassumption.
      * eapply verilog_to_smt_only_tag; eassumption.
Qed.

Lemma smt_same_values_eq var vars m n1 n2 ρ :
  smt_all_same_values vars m ρ ->
  In var vars ->
  m (TaggedVariable.VerilogLeft, var) = Some n1 ->
  m (TaggedVariable.VerilogRight, var) = Some n2 ->
  ρ (SMTLib.Sort_BitVec (Verilog.varType var)) n1 = ρ (SMTLib.Sort_BitVec (Verilog.varType var)) n2.
Proof.
  unfold smt_all_same_values, smt_same_value.
  intros Hmatch Hin Hm1 Hm2.
  rewrite List.Forall_forall in Hmatch.
  insterU Hmatch.
  destruct Hmatch as [n1' [n2' [? [? ?]]]].
  replace n1' with n1 in * by crush.
  replace n2' with n2 in * by crush.
  crush.
Qed.

(* Lemma valid_execution_of_valuation_match v tag m ρ :
 *   Permutation (Verilog.module_body_writes (Verilog.modBody v)) (Verilog.module_outputs v) ->
 *   VerilogToSMT.all_vars_driven v ->
 *   valid_execution v (execution_of_valuation tag m ρ) ->
 *   verilog_smt_match_states_partial
 *     (fun var => In var (Verilog.modVariables v))
 *     tag m (execution_of_valuation tag m ρ) ρ.
 * Proof.
 *   intros Houtputs Hdriven Hvalid.
 *   pose proof (verilog_smt_match_states_execution_of_valuation_same tag m ρ).
 * Admitted. *)

Lemma smt_distinct_values_not_defined_match vars m ρ :
  smt_some_distinct_values vars m ρ ->
  ~ (execution_of_valuation TaggedVariable.VerilogLeft m ρ =(
       vars
     )= execution_of_valuation TaggedVariable.VerilogRight m ρ).
Proof.
  unfold smt_some_distinct_values.
  rewrite List.Exists_exists.
  intros [var [Hin Hsmt_distinct]] contra.
  unfold smt_distinct_value in Hsmt_distinct.
  unfold "_ =( _ )= _" in contra.
  specialize (contra var Hin).
  unfold execution_of_valuation in contra.
  decompose_all_records. 
  replace (m (TaggedVariable.VerilogLeft, var)) in contra.
  replace (m (TaggedVariable.VerilogRight, var)) in contra.
  apply XBV.from_bv_injective in contra.
  contradiction.
Qed.

Lemma smt_all_same_values_execution_match vars m ρ :
  smt_all_same_values vars m ρ ->
  (execution_of_valuation TaggedVariable.VerilogLeft m ρ) =!!(
    vars
  )!!= (execution_of_valuation TaggedVariable.VerilogRight m ρ).
Proof.
  unfold smt_all_same_values, smt_same_value.
  rewrite List.Forall_forall.
  intros Hmatch.
  apply RegisterState.defined_match_on_iff.
  intros var Hvar. specialize (Hmatch var Hvar).
  destruct Hmatch as [smtName1 [smtName2 [Hm1 [Hm2 Hmatch]]]].
  unfold execution_of_valuation.
  rewrite Hm1, Hm2, Hmatch. 
  eauto.
Qed.

(* Replace me with above *)
(* Lemma smt_all_same_inputs_execution_match v1 v2 m ρ :
 *   Permutation (Verilog.module_body_writes (Verilog.modBody v1)) (Verilog.module_outputs v1) ->
 *   Permutation (Verilog.module_body_writes (Verilog.modBody v2)) (Verilog.module_outputs v2) ->
 *   VerilogToSMT.all_vars_driven v1 ->
 *   VerilogToSMT.all_vars_driven v2 ->
 *   valid_execution v1 (execution_of_valuation TaggedVariable.VerilogLeft m ρ) ->
 *   valid_execution v2 (execution_of_valuation TaggedVariable.VerilogRight m ρ) ->
 *   Verilog.module_inputs v1 = Verilog.module_inputs v2 ->
 *   smt_all_same_values (Verilog.module_inputs v1) m ρ ->
 *   (execution_of_valuation TaggedVariable.VerilogLeft m ρ) =!!(
 *     Verilog.module_inputs v1
 *   )!!= (execution_of_valuation TaggedVariable.VerilogRight m ρ).
 * Admitted. *)

Lemma execution_defined_match_smt_all_same_values vars m ρ :
  (execution_of_valuation TaggedVariable.VerilogLeft m ρ) =!!(
    vars
  )!!= (execution_of_valuation TaggedVariable.VerilogRight m ρ) ->
  smt_all_same_values vars m ρ.
Proof.
  rewrite RegisterState.defined_match_on_iff.
  unfold smt_all_same_values, smt_same_value.
  rewrite List.Forall_forall.
  intros H var Hvar_in.
  insterU H. destruct H as [bv [Hlookup_left Hlookup_right]].

  eapply execution_of_valuation_inv in Hlookup_left.
  decompose record Hlookup_left. clear Hlookup_left.

  eapply execution_of_valuation_inv in Hlookup_right.
  decompose record Hlookup_right. clear Hlookup_right.
  eexists. eexists. unpack_goal; crush.
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

Lemma not_execution_defined_match_on_smt_some_distinct_values vars m ρ :
  execution_some_distinct_value
    (fun var : Verilog.variable => In var vars)
    (execution_of_valuation TaggedVariable.VerilogLeft m ρ)
    (execution_of_valuation TaggedVariable.VerilogRight m ρ) ->
  smt_some_distinct_values vars m ρ.
Proof.
  unfold execution_some_distinct_value, smt_some_distinct_values, smt_distinct_value in *.
  rewrite List.Exists_exists.
  intros [var [bv1 [bv2 [Hin [Hlookup_left [Hlookup_right Hneq]]]]]].
  apply execution_of_valuation_inv in Hlookup_left. decompose record Hlookup_left.
  apply execution_of_valuation_inv in Hlookup_right. decompose record Hlookup_right.
  eexists. split; [eassumption|].
  do 2 eexists.
  unpack_goal; crush.
Qed.

Lemma all_driven_outputs_driven v :
  disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
  VerilogToSMT.all_vars_driven v ->
  list_subset (Verilog.module_outputs v) (Verilog.module_body_writes (Verilog.modBody v)).
Proof.
  unfold VerilogToSMT.all_vars_driven, disjoint, list_subset.
  rewrite ! List.Forall_forall.
  intros Hdisjoint Hdriven var Houtput.
  edestruct Hdriven.
  - eapply Verilog.module_outputs_in_vars. eassumption.
  - exfalso. crush.
  - assumption.
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

(* TODO: Move me to Match.v *)
Lemma execution_of_valuation_all_defined tag (m : VerilogSMTBijection.t) ρ :
  RegisterState.defined_value_for
    (fun var => exists n, m (tag, var) = Some n)
    (execution_of_valuation tag m ρ).
Proof.
  unfold RegisterState.defined_value_for, execution_of_valuation.
  intros var [n HC].
  crush.
Qed.

Local Open Scope verilog.

Global Instance match_on_eq_subrelation (P : Verilog.variable -> Prop) : 
  subrelation eq (RegisterState.match_on P).
Proof. intros a b <-. reflexivity. Qed.

Global Instance Proper_valid_execution v :
  Proper
    (RegisterState.match_on (fun var => In var (Verilog.module_inputs v ++ Verilog.module_outputs v)) ==> iff)
    (valid_execution v).
Proof.
  repeat intro.
  unfold valid_execution.
  RegisterState.unpack_match_on.
  split.
  all: intros H1.
  - rewrite <- H at 1.
    rewrite H1.
    RegisterState.unpack_match_on; assumption.
  - rewrite H at 1.
    rewrite H1.
    symmetry.
    RegisterState.unpack_match_on; assumption.
Qed.

(* Lemma transfer_execution v e :
 *   clean_module v ->
 *   RegisterState.defined_value_for (fun var => In var (Verilog.module_inputs v)) e ->
 *   exists e', e =!!( Verilog.module_inputs v )!!= e' /\ v ⇓ e'.
 * Proof.
 *   unfold clean_module.
 *   intros Hclean Hinputs.
 *   specialize (Hclean _ Hinputs).
 *   destruct Hclean as [Hmatch Houtputs].
 *   exists (run_vmodule v (e // Verilog.module_inputs v)). split.
 *   - crush.
 *   - unfold "⇓". unpack_goal.
 *     + setoid_rewrite <- Hmatch at 1.
 *       apply VerilogToSMTCorrect.defined_value_for_has_value_for.
 *       apply Hinputs.
 *     + setoid_rewrite <- Hmatch. 
 *       apply VerilogToSMTCorrect.defined_value_for_has_value_for.
 *       apply Hinputs.
 *     + apply VerilogToSMTCorrect.defined_value_for_has_value_for.
 *       apply Houtputs.
 * Qed. *)

Lemma clean_defined_outputs v e :
  clean_module v ->
  v ⇓ e ->
  RegisterState.defined_value_for
    (fun var : Verilog.variable => In var (Verilog.module_inputs v)) e ->
  RegisterState.defined_value_for
    (fun var : Verilog.variable => In var (Verilog.module_outputs v)) e.
Proof.
  unfold "⇓".
  intros Hclean Hmatch Hinputs. 
  RegisterState.unpack_match_on.
  rename_match (_ =( Verilog.module_outputs _ )= _) into Hmatch_outputs.
  rewrite <- Hmatch_outputs.
  apply Hclean.
  apply Hinputs.
Qed.

Ltac assert_rewrite r :=
  let H := fresh "H" in
  assert ( H : r ); [|rewrite H; clear H].

Lemma list_subset_empty {A} (l : list A) :
  list_subset [] l.
Proof. apply Forall_nil. Qed.

(* Lemma module_items_sorted_reads inputs body :
 *   module_items_sorted inputs body ->
 *   list_subset (Verilog.module_body_reads body) inputs.
 * Proof.
 *   induction 1.
 *   - simp module_body_reads.
 *     apply list_subset_empty.
 *   - simp module_body_reads.
 *     apply list_subset_app. split.
 *     + assumption.
 *     +  *)

(* Move me to semantics *)
Lemma run_vmodule_defined r v:
  (* This should just be "sortable", not "sorted" *)
  module_items_sorted (Verilog.module_inputs v) (Verilog.modBody v) ->
  (* This should be removed, see exec_module_body_defined note *)
  list_subset (Verilog.module_body_reads (Verilog.modBody v)) (Verilog.module_inputs v) ->
  list_subset (Verilog.module_outputs v) (Verilog.module_body_writes (Verilog.modBody v)) ->
  RegisterState.defined_value_for
    (fun var : Verilog.variable => In var (Verilog.module_inputs v))
    r ->
  RegisterState.defined_value_for
    (fun var : Verilog.variable => In var (Verilog.module_outputs v))
    (run_vmodule v r).
Proof.
  intros * Hsorted Hreads_in Houtputs_in Hinputs_defined.
  unfold run_vmodule, mk_initial_state.
  rewrite sort_module_items_stable by assumption.
  eapply exec_module_body_defined.
  - reflexivity.
  - etransitivity.
    + eassumption.
    + apply list_subset_app_r.
  - setoid_rewrite Hreads_in.
    apply RegisterState.defined_value_for_limit_to_regs.
    assumption.
Qed.

Lemma execution_congruent v e1 e2 :
  v ⇓ e1 -> v ⇓ e2 ->
  e1 =( Verilog.module_inputs v )= e2 ->
  e1 =( Verilog.module_outputs v )= e2.
Proof.
  unfold "⇓".
  intros Hadmit1 Hadmit2 Hinput_match.
  RegisterState.unpack_match_on.
  rename_match (run_vmodule v e1 =( Verilog.module_outputs _ )= e1) into Houtputs1.
  rewrite <- Houtputs1.
  rename_match (run_vmodule v e2 =( Verilog.module_outputs _ )= e2) into Houtputs2.
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
    split; intros He.
    (* This is duplicated, ideally we want a "without loss of generality" tactic *)
    + RegisterState.unpack_defined_value_for.
      assert (Hrun2 : v2 ⇓ run_vmodule v2 e). {
        apply admit_run_vmodule.
	apply Hclean2.
      }
      assert (Hmatch_inputs : e =!!( Verilog.module_inputs v1 )!!= run_vmodule v2 e). {
	split; [|assumption].
	symmetry.
	rewrite Hinput_match.
	apply Hclean2.
      }
      specialize (H e (run_vmodule v2 e)).
      apply not_and_or in H. destruct H; [contradiction|].
      apply not_and_or in H. destruct H; [contradiction|].
      apply not_and_or in H. destruct H; [contradiction|].
      apply NNPP in H.
      assert (Hmatch_all :
        e =( Verilog.module_inputs v2 ++ Verilog.module_outputs v2
	  )= run_vmodule v2 e). {
	  RegisterState.unpack_match_on.
	- rewrite Hinput_match in Hmatch_inputs.
	  destruct Hmatch_inputs. assumption.
	- rewrite Houtput_match in H. assumption.
      }
      rewrite Hmatch_all.
      assumption.
    + RegisterState.unpack_defined_value_for.
      assert (Hrun1 : v1 ⇓ run_vmodule v1 e). {
        apply admit_run_vmodule.
	apply Hclean1.
      }
      assert (Hmatch_inputs : e =!!( Verilog.module_inputs v1 )!!= run_vmodule v1 e). {
	split; [|assumption].
	symmetry.
	apply Hclean1.
      }
      specialize (H (run_vmodule v1 e) e).
      apply not_and_or in H. destruct H; [contradiction|].
      apply not_and_or in H. destruct H; [contradiction|].
      apply not_and_or in H. destruct H; [symmetry in Hmatch_inputs; contradiction|].
      apply NNPP in H.
      assert_rewrite (
          e =(
	    Verilog.module_inputs v1 ++ Verilog.module_outputs v1
          )= run_vmodule v1 e). {
	RegisterState.unpack_match_on.
	- destruct Hmatch_inputs. assumption.
	- symmetry. assumption.
      }
      assumption.
  - intros [] e1 e2 Hcontra. decompose record Hcontra. clear Hcontra.
    rename_match (v1 ⇓ e1) into Hadmit1.
    rename_match (v2 ⇓ e2) into Hadmit2.
    rename_match (e1 =!!( Verilog.module_inputs v1 )!!= e2) into Hmatch_inputs.
    rename_match (~ (e1 =( Verilog.module_outputs v1 )= e2)) into Hno_match_outputs.
    erewrite <- execution_match0 in Hadmit2; cycle 1. {
      RegisterState.unpack_defined_value_for.
      - destruct Hmatch_inputs as [Hmatch_inputs ?]. rewrite <- Hmatch_inputs. assumption.
      - rewrite Houtput_match.
        apply clean_defined_outputs; try assumption; expect 1.
	destruct Hmatch_inputs as [Hmatch_inputs Hdefined_inputs].
	rewrite <- Hinput_match.
	rewrite <- Hmatch_inputs.
	assumption.
    }
    contradict Hno_match_outputs.
    apply execution_congruent.
    + assumption.
    + assumption.
    + destruct Hmatch_inputs. assumption.
Qed.

Print Assumptions no_counterexample_equivalent_iff.

Lemma not_equivalent_counterexample_iff v1 v2 :
  Verilog.module_inputs v1 = Verilog.module_inputs v2 ->
  Verilog.module_outputs v1 = Verilog.module_outputs v2 ->
  clean_module v1 ->
  clean_module v2 ->
  (exists e1 e2, counterexample_execution v1 e1 v2 e2) <-> (~ equivalent_behaviour v1 v2).
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
    only_reads_inputs : list_subset (Verilog.module_body_reads (Verilog.modBody v)) (Verilog.module_inputs v);
    all_vars_driven : VerilogToSMT.all_vars_driven v;
    no_duplicate_writes : NoDup (Verilog.module_body_writes (Verilog.modBody v));
    no_duplicate_outputs : NoDup (Verilog.module_outputs v);
    writes_outputs : Permutation (Verilog.module_body_writes (Verilog.modBody v)) (Verilog.module_outputs v);
    sorted : module_items_sorted (Verilog.module_inputs v) (Verilog.modBody v);
}.

Lemma verilog_to_smt_checks tag start v smt :
  VerilogToSMT.verilog_to_smt tag start v = inr smt ->
  verilog_to_smt_checked v.
Proof.
  intros H.
  unfold VerilogToSMT.verilog_to_smt in H. monad_inv.
  constructor; try assumption.
Qed.

Record equivalence_query_checked (v1 v2 : Verilog.vmodule) smt := MkEquivalenceQueryChecked {
  verilog_to_smt_eqn1 : exists tag start smt, VerilogToSMT.verilog_to_smt tag start v1 = inr smt;
  verilog_to_smt_eqn2 : exists tag start smt, VerilogToSMT.verilog_to_smt tag start v2 = inr smt;
  verilog_to_smt_checked1 : verilog_to_smt_checked v1;
  verilog_to_smt_checked2 : verilog_to_smt_checked v2;
  map_match_left : match_map_vars
    TaggedVariable.VerilogLeft (nameMap smt) (Verilog.modVariables v1);
  map_match_right : match_map_vars
    TaggedVariable.VerilogRight (nameMap smt) (Verilog.modVariables v2);
  inputs_match : Verilog.module_inputs v1 = Verilog.module_inputs v2;
  outputs_match : Verilog.module_outputs v1 = Verilog.module_outputs v2;
}.

Lemma equivalence_query_map_match_left v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  match_map_vars TaggedVariable.VerilogLeft (nameMap smt) (Verilog.modVariables v1).
Proof.
  unfold equivalence_query.
  intros. monad_inv. simpl.
  eapply match_map_vars_tag_same.
  - eapply VerilogSMTBijection.combine_different_tag_left;
      eauto using verilog_to_smt_only_tag;
      discriminate.
  - eapply VerilogToSMTCorrect.verilog_to_smt_map_match.
    eassumption.
Qed.

Lemma equivalence_query_map_match_right v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  match_map_vars TaggedVariable.VerilogRight (nameMap smt) (Verilog.modVariables v2).
Proof.
  unfold equivalence_query.
  intros. monad_inv. simpl.
  eapply match_map_vars_tag_same.
  - eapply VerilogSMTBijection.combine_different_tag_right;
      eauto using verilog_to_smt_only_tag;
      discriminate.
  - eapply VerilogToSMTCorrect.verilog_to_smt_map_match.
    eassumption.
Qed.

Lemma equivalence_query_checks v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  equivalence_query_checked v1 v2 smt.
Proof.
  intros H.
  epose proof (equivalence_query_map_match_left _ _ _ ltac:(eauto)).
  epose proof (equivalence_query_map_match_right _ _ _ ltac:(eauto)).
  unfold equivalence_query in H. monad_inv.
  constructor; eauto using verilog_to_smt_checks.
Qed.

Lemma counterexample_valuation_execution v1 v2 ρ q :
  equivalence_query_checked v1 v2 q ->
  counterexample_valuation v1 v2 (nameMap q) ρ <->
    counterexample_execution
      v1 (execution_of_valuation TaggedVariable.VerilogLeft (nameMap q) ρ)
      v2 (execution_of_valuation TaggedVariable.VerilogRight (nameMap q) ρ).
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
      * eapply RegisterState.defined_value_for_impl; [|apply execution_of_valuation_all_defined].
	simpl. intros.
	apply map_match_left0.
	apply Verilog.module_outputs_in_vars.
	assumption.
      * eapply RegisterState.defined_value_for_impl; [|apply execution_of_valuation_all_defined].
	simpl. intros.
	apply map_match_right0.
	apply Verilog.module_outputs_in_vars.
	rewrite <- outputs_match0.
	assumption.
      * unfold "_ =!!( _ )!!= _". intuition eauto.
    + assumption.
    + assumption.
Qed.

Theorem equivalence_query_execution_spec v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  smt_reflect
    (assertions smt)
    (fun ρ => counterexample_execution
      v1 (execution_of_valuation TaggedVariable.VerilogLeft (nameMap smt) ρ)
      v2 (execution_of_valuation TaggedVariable.VerilogRight (nameMap smt) ρ)).
Proof.
  intros Hfunc.
  setoid_rewrite <- counterexample_valuation_execution;
    [|eauto using equivalence_query_checks].
  eapply equivalence_query_spec.
  assumption.
Qed.

Theorem equivalence_query_sat_correct v1 v2 smt ρ :
  equivalence_query v1 v2 = inr smt ->
  satisfied_by ρ (assertions smt) ->
  counterexample_execution
    v1 (execution_of_valuation TaggedVariable.VerilogLeft (nameMap smt) ρ)
    v2 (execution_of_valuation TaggedVariable.VerilogRight (nameMap smt) ρ).
Proof. intros. now apply equivalence_query_execution_spec. Qed.

Lemma limit_to_regs_rewrite vars e1 e2 :
  (forall var, In var vars -> e1 var = e2 var) ->
  RegisterState.limit_to_regs vars e1 = RegisterState.limit_to_regs vars e2.
Proof.
  unfold RegisterState.limit_to_regs.
  intros Heq.
  apply functional_extensionality_dep.
  intros var. autodestruct; crush.
Qed.

Lemma valid_execution_rewrite v e1 e2 :
  e1 =(Verilog.module_inputs v ++ Verilog.module_outputs v)= e2 ->
  valid_execution v e1 <-> valid_execution v e2.
Proof.
  intros Heq.
  unfold run_vmodule, mk_initial_state.
  rewrite Heq. reflexivity.
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
  e1 =( Verilog.module_inputs v ++ Verilog.module_outputs v )= e1' ->
  counterexample_execution v e1 v2 e2 <-> counterexample_execution v e1' v2 e2.
Proof.
  unfold counterexample_execution.
  intros H.
  split; intros [Hvalid1 [Hvalid2 [Hdefined_in Hnot_defined_out]]];
    unpack_goal; try eassumption.
  - rewrite H in Hvalid1. assumption.
  - RegisterState.unpack_match_on.
    rewrite <- H.
    assumption.
  - RegisterState.unpack_match_on.
    rewrite <- H0.
    assumption.
  - rewrite H. assumption.
  - RegisterState.unpack_match_on.
    rewrite H.
    assumption.
  - RegisterState.unpack_match_on.
    rewrite H0.
    assumption.
Qed.

Lemma counterexample_execution_rewrite_right v1 e1 v2 e2 e2' :
  Verilog.module_inputs v1 = Verilog.module_inputs v2 ->
  Verilog.module_outputs v1 = Verilog.module_outputs v2 ->
  e2 =( Verilog.module_inputs v2 ++ Verilog.module_outputs v2 )= e2' ->
  counterexample_execution v1 e1 v2 e2 <-> counterexample_execution v1 e1 v2 e2'.
Proof.
  unfold counterexample_execution.
  intros inputs_same outputs_same H.
  split; intros [Hvalid1 [Hvalid2 [Hmatch_in Hnot_defined_out]]];
    unpack_goal; try eassumption.
  1,4: match goal with
       | [ |- ?v2 ⇓ ?e' ] =>
         rewrite H || rewrite <- H; assumption
       end.
  all: rewrite <- inputs_same in *.
  all: rewrite <- outputs_same in *.
  all: RegisterState.unpack_match_on.
  all: rename_match (e2 =( Verilog.module_inputs v1 )= e2') into Hmatch_inputs.
  all: rename_match (e2 =( Verilog.module_outputs v1 )= e2') into Hmatch_outputs.
  - rewrite <- Hmatch_inputs. assumption.
  - rewrite <- Hmatch_outputs. assumption.
  - rewrite Hmatch_inputs. assumption.
  - rewrite Hmatch_outputs. assumption.
Qed.

Lemma valid_execution_all_vars_defined tag start v q e :
  VerilogToSMT.verilog_to_smt tag start v = inr q ->
  valid_execution v e ->
  RegisterState.defined_value_for (fun var => List.In var (Verilog.module_inputs v)) e ->
  RegisterState.defined_value_for (fun var => List.In var (Verilog.modVariables v)) e.
Proof.
  intros.
  assert (VerilogToSMT.all_vars_driven v) as Hdriven
    by (unfold VerilogToSMT.verilog_to_smt in *; monad_inv; assumption).
  eapply RegisterState.defined_value_for_impl.
  - eapply List.Forall_forall.
    eapply Hdriven.
  - RegisterState.unpack_defined_value_for.
    + assumption.
    + eapply VerilogToSMTCorrect.valid_execution_no_exes_written; eassumption.
Qed.

Lemma verilog_to_smt_clean tag start v smt :
  VerilogToSMT.verilog_to_smt tag start v = inr smt ->
  clean_module v.
Proof.
  intros H. eapply verilog_to_smt_checks in H. destruct H.
  apply clean_module_statically; try eassumption.
Qed.

Lemma inputs_outputs_subset v :
  list_subset
    (Verilog.module_inputs v ++ Verilog.module_outputs v)
    (Verilog.modVariables v).
Proof.
  apply list_subset_app. unfold list_subset. rewrite ! Forall_forall.
  split.
  - apply Verilog.module_input_in_vars.
  - apply Verilog.module_outputs_in_vars.
Qed.

Lemma equivalence_query_unsat_no_counterexample v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ (assertions smt)) ->
  (forall e1 e2, ~ counterexample_execution v1 e1 v2 e2).
Proof.
  intros Hquery Hunsat e1 e2 Hcounterexample.
  destruct (equivalence_query_checks v1 v2 smt)
    as [[? [? [? ?]]] [? [? [? ?]]] [] [] ? ? inputs_match outputs_match];
    [assumption|].
  eapply Hunsat with (ρ := valuation_of_executions (nameMap smt) e1 e2).
  eapply equivalence_query_execution_spec; eauto.
  erewrite
    counterexample_execution_rewrite_left,
    counterexample_execution_rewrite_right.
  - eassumption.
  - eassumption.
  - eassumption.
  - setoid_rewrite inputs_outputs_subset.
    eapply execution_of_valuation_right_match_on; [|assumption].
    (* defined_value_for right-tagged vars *)
    destruct Hcounterexample as [? [? [[Hinputs_match Hinputs_defined] ?]]].
    eapply valid_execution_all_vars_defined; eauto.
    setoid_rewrite Hinputs_match in Hinputs_defined.
    rewrite inputs_match in Hinputs_defined.
    apply Hinputs_defined.
  - setoid_rewrite inputs_outputs_subset.
    eapply execution_of_valuation_left_match_on; [|assumption].
    (* defined_value_for left-tagged vars *)
    destruct Hcounterexample as [? [? [[Hinputs_match Hinputs_defined] ?]]].
    eapply valid_execution_all_vars_defined; eauto.
Qed.

Theorem equivalence_query_unsat_correct v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ (assertions smt)) ->
  equivalent_behaviour v1 v2.
Proof.
  intros Hquery Hunsat.
  destruct (equivalence_query_checks v1 v2 smt)
    as [[? [? [? ?]]] [? [? [? ?]]] [] [] inputs_match outputs_match];
    [assumption|].
  apply no_counterexample_equivalent_iff; eauto using verilog_to_smt_clean.
  eapply equivalence_query_unsat_no_counterexample; eauto.
Qed.
