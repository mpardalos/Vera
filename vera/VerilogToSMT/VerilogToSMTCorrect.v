From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import VerilogToSMT.
From vera Require Import VerilogSMT.
From vera Require SMTQueries.
From vera Require Import VerilogSemantics.
Import CombinationalOnly.
Import Facts.
From vera Require Import Verilog.
From vera Require Import Bitvector.
Import RawXBV(bit(..)).
From vera Require Import VerilogToSMT.Expressions.

From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.MonadState.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Functor.

From Stdlib Require List.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import String.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import NArith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Setoid.

From Equations Require Import Equations.

Import List.ListNotations.
Import CommonNotations.
Import MonadLetNotation.
Import FunctorNotation.
Import SigTNotations.
Local Open Scope monad_scope.
Local Open Scope list.
Local Open Scope verilog.

Lemma defined_value_for_set_reg_intro_out C regs var xbv :
  (~ C var) ->
  RegisterState.defined_value_for C (RegisterState.set_reg var xbv regs) ->
  RegisterState.defined_value_for C regs.
Proof.
  unfold RegisterState.defined_value_for.
  intros HnotC Hdefined var1 HC.
  insterU Hdefined.
  destruct Hdefined as [? ?].
  autorewrite with register_state in *.
  crush.
Qed.

Lemma module_item_to_smt_satisfiable tag (mi : Verilog.module_item) :
  forall t regs ρ,
    disjoint (Verilog.module_item_reads mi) (Verilog.module_item_writes mi) ->
    transfer_module_item tag mi = inr t ->
    verilog_smt_match_states_partial
      (fun var => List.In var (Verilog.module_item_reads mi ++ Verilog.module_item_writes mi))
      tag
      (exec_module_item regs mi) ρ ->
    SMTQueries.term_satisfied_by ρ t.
Proof.
  funelim (transfer_module_item tag mi); expect 1.
  intros * Hdisjoint * Hexec Hmatch.
  monad_inv; expect 1.
  simp exec_module_item exec_statement in *.
  monad_inv.
  unfold SMTQueries.satisfied_by, SMTQueries.term_satisfied_by. repeat constructor.
  simpl.
  apply BV.bv_eq_reflect.

  simp module_item_reads module_item_writes
    statement_reads statement_writes expr_reads
    in *.
  simpl in Hmatch.
  disjoint_saturate.
  unpack_verilog_smt_match_states_partial. 
  rename_match
    (verilog_smt_match_states_partial (fun _ => List.In _ (Verilog.expr_reads _)) _ _ _)
    into Hbefore.
  rename_match
    (verilog_smt_match_states_partial (fun _ => List.In _ [var]) _ _ _)
    into Hafter.
  apply verilog_smt_match_states_partial_set_reg_out in Hbefore; [|now disjoint_saturate].
  apply XBV.from_bv_injective.
  erewrite <- expr_to_smt_value by eassumption.
  rewrite <- Hafter by eauto with datatypes.
  apply RegisterState.set_reg_get_in.
Qed.

Lemma smt_eq_sat_iff s ρ (l r : SMTLib.term s) :
  SMTQueries.term_satisfied_by ρ (SMTLib.Term_Eq l r) <->
    (SMTLib.interp_term ρ l = SMTLib.interp_term ρ r).
Proof.
  unfold SMTQueries.term_satisfied_by.
  simpl. apply SMTLib.value_eqb_eq.
Qed.

Lemma module_item_to_smt_valid tag  (mi : Verilog.module_item) :
  disjoint (Verilog.module_item_reads mi) (Verilog.module_item_writes mi) ->
  forall ρ t,
    transfer_module_item tag mi = inr t ->
    SMTQueries.term_satisfied_by ρ t ->
    forall r1,
      verilog_smt_match_states_partial
        (fun var => List.In var (Verilog.module_item_reads mi))
        tag r1 ρ ->
      verilog_smt_match_states_partial
        (fun var => List.In var (Verilog.module_item_writes mi))
        tag (exec_module_item r1 mi) ρ.
Proof.
  funelim (transfer_module_item tag mi);
    intros * Hdisjoint * Htransf Hsat * Hmatch1; monad_inv; [idtac].
  simp module_item_reads module_item_writes statement_writes statement_reads expr_reads in *.
  simp exec_module_item exec_statement in *.
  monad_inv.
  rewrite smt_eq_sat_iff in Hsat.
  pose proof expr_to_smt_valid as Hvalue_match. insterU Hvalue_match.
  inv Hvalue_match. simpl.
  unpack_verilog_smt_match_states_partial.
  all: unfold verilog_smt_match_states_partial.
  all: intros * [].
  all: expect 1.
  rewrite RegisterState.set_reg_get_in.
  simpl in Hsat.
  rewrite Hsat.
  assumption.
Qed.

Lemma mapT_list_eq_nil A B (f : A -> option B) l :
  List.mapT_list f l = Some []%list ->
  l = []%list.
Proof. destruct l; crush. Qed.

Lemma mapT_list_eq_cons A B l : forall (f : A -> option B) l' b,
  List.mapT_list f l = Some (b :: l')%list ->
  exists (a : A) (tl : list A), l = (a :: tl)%list /\ f a = Some b /\ List.mapT_list f tl = Some l'.
Proof.
  destruct l; intros * H; [crush|].
  inv H. autodestruct_eqn E.
  some_inv. eauto.
Qed.

Global Instance verilog_smt_match_states_partial_match_on_proper C :
  Proper
    (eq ==> (RegisterState.match_on C) ==> eq ==> iff)
    (verilog_smt_match_states_partial C).
Proof.
  repeat intro. subst.
  unfold verilog_smt_match_states_partial.
  split.
  all: intros H var Hvar.
  all: specialize (H var Hvar).
  1: rewrite <- H0 by assumption.
  2: rewrite H0 by assumption.
  all: assumption.
Qed.

Lemma transfer_module_body_exec_satisfiable inputs body :
  forall tag r1 q ρ,
    module_items_sorted inputs body ->
    transfer_module_body tag body = inr q ->
    verilog_smt_match_states_partial
      (fun var => List.In var (inputs ++ Verilog.module_body_writes body))
      tag (exec_module_body r1 body) ρ ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q.
Proof.
  revert inputs.
  induction body; intros * Hsorted Htransfer Hmatch; simp module_body_reads module_body_writes transfer_module_body in *; [some_inv; constructor|].
  simp exec_module_body in Hmatch. simpl in Hmatch.
  monad_inv.
  constructor.
  - inv Hsorted.
    eapply module_item_to_smt_satisfiable with (regs:=r1); expect 3.
    { rewrite H1. symmetry. assumption. }
    { eassumption. }
    unpack_verilog_smt_match_states_partial.
    + setoid_rewrite H1.
      setoid_rewrite <- Facts.exec_module_body_preserve in H; cycle 1.
      {
        apply module_items_sorted_no_overwrite in H4.
	now disjoint_saturate.
      }
      assumption.
    + setoid_rewrite <- Facts.exec_module_body_preserve in H0; cycle 1.
      {
        apply module_items_sorted_no_overwrite in H4.
	now disjoint_saturate.
      }
      assumption.
  - inv Hsorted.
    eapply IHbody; eauto; expect 1.
    eapply verilog_smt_match_states_partial_impl; [|eassumption].
    intros. simpl.
    rewrite ! List.in_app_iff in *.
    intuition assumption.
Qed.

Lemma transfer_module_body_satisfiable v tag ρ q :
    Permutation (Verilog.modVariables v) (Verilog.module_body_writes (Verilog.modBody v) ++ Verilog.module_inputs v) ->
    module_items_sorted (Verilog.module_inputs v) (Verilog.modBody v) ->
    transfer_module_body tag (Verilog.modBody v) = inr q ->
    v ⇓ (execution_of_valuation tag ρ) ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q.
Proof.
  intros * Hall_driven Hsorted Htransfer Hvalid .
  unfold "⇓" in Hvalid.
  RegisterState.unpack_match_on.
  repeat unfold mk_initial_state, run_vmodule in *.
  rewrite ! sort_module_items_stable in * by eassumption.
  eapply transfer_module_body_exec_satisfiable; eauto.
  apply execution_match_on_verilog_smt_match_states_partial.
  RegisterState.unpack_match_on.
  - setoid_rewrite Verilog.module_input_in_vars.
    apply Hvalid.
  - setoid_replace (Verilog.module_body_writes (Verilog.modBody v)) with (Verilog.modVariables v)
      using relation (@list_subset Verilog.variable).
    2: rewrite Hall_driven; apply list_subset_app_r.
    apply Hvalid.
Qed.

Global Instance verilog_smt_match_states_partial_proper C :
  Proper
    (eq ==> (RegisterState.match_on C) ==> eq ==> iff)
    (verilog_smt_match_states_partial C).
Proof.
  unfold verilog_smt_match_states_partial.
  repeat intro. subst.
  split; intros.
  - rewrite <- H by assumption.
    rewrite H0 by assumption.
    reflexivity.
  - rewrite <- H by assumption.
    rewrite H0 by assumption.
    reflexivity.
Qed.

Lemma transfer_module_body_exec_valid inputs body : forall tag ρ q,
    module_items_sorted inputs body ->
    transfer_module_body tag body = inr q ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q ->
    forall r1,
      verilog_smt_match_states_partial
        (fun var => List.In var inputs) tag
	r1 ρ ->
      verilog_smt_match_states_partial
        (fun var => List.In var (Verilog.module_body_writes body)) tag
	(exec_module_body r1 body) ρ.
Proof.
  revert inputs.
  induction body.
  all: intros * Hsorted Htransfer Hsat * Hmatch1.
  all: simpl in *.
  all: simp module_body_reads module_body_writes transfer_module_body exec_module_body in *.
  all: autorewrite with list.
  1: crush. all: expect 1.
  unpack_list_subset.
  disjoint_saturate.
  monad_inv. inv Hsat. inv Hsorted.
  rename_match (module_items_sorted (Verilog.module_item_writes a ++ inputs) body) into Hsorted.
  rename_match (list_subset (Verilog.module_item_reads a) inputs) into Hitem_reads.
  simpl.
  unpack_verilog_smt_match_states_partial.
  - apply module_items_sorted_no_overwrite in Hsorted. disjoint_saturate.
    rewrite <- Facts.exec_module_body_preserve by ((symmetry + idtac); assumption).
    eapply module_item_to_smt_valid.
    + rewrite Hitem_reads. symmetry. assumption.
    + eassumption.
    + eassumption.
    + setoid_rewrite Hitem_reads. assumption.
  - eapply IHbody.
    all: try eassumption.
    all: expect 1.
    unpack_verilog_smt_match_states_partial.
    + eapply module_item_to_smt_valid.
      * rewrite Hitem_reads. symmetry. assumption.
      * eassumption.
      * eassumption.
      * setoid_rewrite Hitem_reads. assumption.
    + rewrite <- Facts.exec_module_item_preserve
        by ((symmetry + idtac); assumption).
      eassumption.
Qed.

Lemma transfer_module_body_valid tag v ρ q :
  module_items_sorted (Verilog.module_inputs v) (Verilog.modBody v) ->
  Permutation (Verilog.modVariables v) (Verilog.module_body_writes (Verilog.modBody v) ++ Verilog.module_inputs v) ->
  transfer_module_body tag (Verilog.modBody v) = inr q ->
  List.Forall (SMTQueries.term_satisfied_by ρ) q ->
  v ⇓ execution_of_valuation tag ρ.
Proof.
  intros * Hsorted Hall_driven Htransfer Hsat.
  unfold valid_execution.
  repeat unfold mk_initial_state, run_vmodule in *.
  rewrite sort_module_items_stable by assumption. simpl.
  eapply verilog_smt_match_states_partial_execution_match_on.
  setoid_rewrite Hall_driven.
  unpack_verilog_smt_match_states_partial.
  - eapply transfer_module_body_exec_valid.
    + eassumption.
    + eassumption.
    + eassumption.
    + rewrite RegisterState.limit_to_regs_match_on.
      apply verilog_smt_match_states_execution_of_valuation_same.
  - rewrite <- Facts.exec_module_body_preserve.
    + rewrite RegisterState.limit_to_regs_match_on.
      apply verilog_smt_match_states_execution_of_valuation_same.
    + symmetry.
      eapply module_items_sorted_no_overwrite.
      apply Hsorted.
Qed.

Import EqNotations.

Theorem verilog_to_smt_correct tag v smt :
  verilog_to_smt tag v = inr smt ->
  SMTQueries.smt_reflect
    smt
    (fun ρ => v ⇓ execution_of_valuation tag ρ).
Proof.
  unfold verilog_to_smt.
  intros Htransf ρ.
  monad_inv. simpl in *.
  split.
  all: intros H.
  - eapply transfer_module_body_valid.
    all: eassumption.
  - eapply transfer_module_body_satisfiable.
    all: eassumption.
Qed.

Print Assumptions verilog_to_smt_correct.
