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
  /\ valid_execution v1 (execution_of_valuation VerilogLeft ρ)
  /\ valid_execution v2 (execution_of_valuation VerilogRight ρ)
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

Lemma valid_execution_all_vars_defined tag v q e :
  VerilogToSMT.verilog_to_smt tag v = inr q ->
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

Lemma verilog_to_smt_clean tag v smt :
  VerilogToSMT.verilog_to_smt tag v = inr smt ->
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
  all: setoid_rewrite inputs_outputs_subset.
  1: eapply execution_of_valuation_right_match_on.
  2: eapply execution_of_valuation_left_match_on.
  all: unfold counterexample_execution in Hcounterexample.
  all: decompose record Hcounterexample.
  all: eapply valid_execution_all_vars_defined.
  all: try eassumption.
  all: expect 2.
  1: rewrite <- inputs_match.
  1: eapply defined_match_on_defined_value_right.
  2: eapply defined_match_on_defined_value_left.
  all: eassumption.
Qed.

Theorem equivalence_query_unsat_correct v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ smt) ->
  equivalent_behaviour v1 v2.
Proof.
  intros Hquery Hunsat.
  destruct (equivalence_query_checks v1 v2 smt)
    as [[? [? ?]] [? [? ?]] [] [] inputs_match outputs_match];
    [assumption|].
  apply no_counterexample_equivalent_iff; eauto using verilog_to_smt_clean.
  eapply equivalence_query_unsat_no_counterexample; eauto.
Qed.
