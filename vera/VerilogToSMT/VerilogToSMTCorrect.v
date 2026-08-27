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
From vera Require Import Variables.
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
Import Verilog.Notations.
Import EqNotations.
Local Open Scope monad_scope.
Local Open Scope list.
Local Open Scope verilog_scope.

Opaque N.add N.sub.

Lemma smt_eq_sat_iff s ρ (l r : SMTLib.term s) :
  SMTQueries.term_satisfied_by ρ (SMTLib.Term_Eq l r) <->
    (SMTLib.interp_term ρ l = SMTLib.interp_term ρ r).
Proof.
  unfold SMTQueries.term_satisfied_by.
  simpl. apply SMTLib.value_eqb_eq.
Qed.

Lemma assign_target_to_smt_value {w} tag (target : Verilog.assign_target w) :
  forall ρ target_smt,
    assign_target_to_smt tag target = inr target_smt ->
    read_target (execution_of_valuation tag ρ) target =
      XBV.from_bv (SMTLib.interp_term ρ target_smt).
Proof.
  induction target.
  all: intros * Htarget_smt.
  all: simp assign_target_to_smt read_target in *.
  all: monad_inv; simpl.
  - reflexivity.
  - destruct loc as [vec idx].
    simp assign_target_to_smt in Htarget_smt. inv Htarget_smt.
    rewrite <- smt_select_bit_value by (simpl in wf; lia).
    unfold RegisterState.get_location.
    rewrite <- XBV.extr_one_bit by exact wf.
    reflexivity.
  - destruct slice.
    simp assign_target_to_smt in Htarget_smt. inv Htarget_smt.
    apply XBV.extr_no_exes.
    simpl. lia.
  - erewrite IHtarget1 by reflexivity.
    erewrite IHtarget2 by reflexivity.
    apply XBV.concat_no_exes.
Qed.

Lemma module_item_to_smt_satisfiable tag (mi : Verilog.module_item) :
  forall t regs ρ,
    LocationSet.Disjoint (Verilog.module_item_reads mi) (Verilog.module_item_writes mi) ->
    transfer_module_item tag mi = inr t ->
    verilog_smt_match_states_partial
      (Verilog.module_item_reads mi ∪ Verilog.module_item_writes mi)
      tag
      (exec_module_item regs mi) ρ ->
    SMTQueries.term_satisfied_by ρ t.
Proof.
  unfold verilog_smt_match_states_partial in *.
  funelim (transfer_module_item tag mi).
  all: intros * Hdisjoint * Htransfer Hmatch.
  all: monad_inv; expect 1.
  simp exec_module_item exec_statement in Hmatch.
  rewrite smt_eq_sat_iff.
  RegisterState.unpack_match_on.
  rename_match (_ =( Verilog.expr_reads _ )= _) into Hreads.
  rename_match (_ =( Verilog.assign_target_writes _ )= _) into Hwrites.
  cbn in *.
  apply Facts.set_target_match_before in Hreads; [|LocationSet.setdec].
  apply XBV.from_bv_injective.
  erewrite <- assign_target_to_smt_value by eassumption.
  erewrite <- Facts.read_target_change_regs by eassumption.
  rewrite Facts.read_target_set_target by assumption.
  eapply expr_to_smt_value.
  all: eassumption.
Qed.

Lemma assign_target_to_smt_valid {w} tag (target : Verilog.assign_target w) :
  Verilog.assign_target_wf target ->
  forall regs ρ target_smt,
    assign_target_to_smt tag target = inr target_smt ->
    verilog_smt_match_states_partial
      (Verilog.assign_target_writes target)
      tag
      (set_target regs target (XBV.from_bv (SMTLib.interp_term ρ target_smt)))
      ρ.
Proof.
  intros Hwf * Htarget_smt.
  rewrite <- (assign_target_to_smt_value tag target ρ target_smt Htarget_smt).
  apply set_target_from_state. exact Hwf.
Qed.

Lemma module_item_to_smt_valid tag  (mi : Verilog.module_item) :
  LocationSet.Disjoint (Verilog.module_item_reads mi) (Verilog.module_item_writes mi) ->
  forall ρ t,
    transfer_module_item tag mi = inr t ->
    SMTQueries.term_satisfied_by ρ t ->
    forall r1,
      verilog_smt_match_states_partial
        (Verilog.module_item_reads mi)
        tag r1 ρ ->
      verilog_smt_match_states_partial
        (Verilog.module_item_writes mi)
        tag (exec_module_item r1 mi) ρ.
Proof.
  funelim (transfer_module_item tag mi);
    intros * Hdisjoint * Htransf Hsat * Hmatch1; monad_inv; [idtac].
  simpl in *.
  simp exec_module_item exec_statement in *.
  monad_inv.
  rewrite smt_eq_sat_iff in Hsat.
  pose proof expr_to_smt_value as Hvalue_match. insterU Hvalue_match.
  rewrite Hvalue_match, <- Hsat.
  eapply assign_target_to_smt_valid; eassumption.
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
      (inputs ∪ Verilog.module_body_writes body)
      tag (exec_module_body r1 body) ρ ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q.
Proof.
  revert inputs.
  induction body; intros * Hsorted Htransfer Hmatch; simpl in *; simp transfer_module_body in *; [some_inv; constructor|].
  simp exec_module_body in Hmatch. simpl in Hmatch.
  monad_inv.
  constructor.
  - inv Hsorted.
    rename_match (module_items_sorted _ body) into Hsorted.
    apply module_item_to_smt_satisfiable with (tag:=tag)(mi:=a) (regs:=r1);
      [LocationSet.setdec|eassumption|].
    unpack_verilog_smt_match_states_partial.
    + setoid_rewrite H1.
      setoid_rewrite <- Facts.exec_module_body_preserve in H; cycle 1. {
        apply module_items_sorted_no_overwrite in Hsorted.
	LocationSet.setdec.
      }
      assumption.
    + setoid_rewrite <- Facts.exec_module_body_preserve in H0; cycle 1. {
        apply module_items_sorted_no_overwrite in Hsorted.
	LocationSet.setdec.
      }
      assumption.
  - inv Hsorted.
    eapply IHbody; eauto; expect 1.
    eapply verilog_smt_match_states_partial_impl; [|eassumption].
    LocationSet.setdec.
Qed.

Lemma transfer_module_body_satisfiable {i o} (v : Verilog.vmodule i o) tag ρ q :
    module_items_sorted (LocationSet.of_varset (VarSet.of_list i)) (Verilog.modBody v) ->
    transfer_module_body tag (Verilog.modBody v) = inr q ->
    v ⇓ execution_of_valuation tag ρ ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q.
Proof.
  intros * Hsorted Htransfer Hvalid .
  unfold "⇓" in Hvalid.
  RegisterState.unpack_match_on.
  repeat unfold mk_initial_state, run_vmodule in *.
  rewrite ! sort_module_items_stable in * by eassumption.
  eapply transfer_module_body_exec_satisfiable; eauto.
  apply execution_match_on_verilog_smt_match_states_partial.
  unfold Verilog.module_locations in Hvalid.
  RegisterState.unpack_match_on.
  - eassumption.
  - eassumption.
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

Lemma verilog_smt_match_states_partial_empty {tag r ρ} :
  verilog_smt_match_states_partial {} tag r ρ.
Proof. intros var Hvar. exfalso. LocationSet.setdec. Qed.

Lemma transfer_module_body_exec_valid inputs body : forall tag ρ q,
    module_items_sorted inputs body ->
    transfer_module_body tag body = inr q ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q ->
    forall r1,
      verilog_smt_match_states_partial inputs tag
	r1 ρ ->
      verilog_smt_match_states_partial
        (Verilog.module_body_writes body) tag
	(exec_module_body r1 body) ρ.
Proof.
  revert inputs.
  induction body.
  all: intros * Hsorted Htransfer Hsat * Hmatch1.
  all: simpl in *.
  all: simp transfer_module_body exec_module_body in *.
  1: exact verilog_smt_match_states_partial_empty.
  simpl in *.
  monad_inv.
  inv Hsat. inv Hsorted.
  rename_match (module_items_sorted (Verilog.module_item_writes a ∪ inputs) body) into Hsorted.
  rename_match (Verilog.module_item_reads a ⊆ inputs) into Hitem_reads.
  simpl.
  unpack_verilog_smt_match_states_partial.
  - apply module_items_sorted_no_overwrite in Hsorted.
    rewrite <- Facts.exec_module_body_preserve by LocationSet.setdec.
    eapply module_item_to_smt_valid.
    + LocationSet.setdec.
    + eassumption.
    + eassumption.
    + rewrite Hitem_reads. assumption.
  - eapply IHbody.
    all: try eassumption; expect 1.
    unpack_verilog_smt_match_states_partial.
    + eapply module_item_to_smt_valid.
      * LocationSet.setdec.
      * eassumption.
      * eassumption.
      * rewrite Hitem_reads. assumption.
    + rewrite <- Facts.exec_module_item_preserve by LocationSet.setdec.
      eassumption.
Qed.

Lemma transfer_module_body_valid {i o} tag (v : Verilog.vmodule i o) ρ q :
  module_items_sorted (LocationSet.of_varset (VarSet.of_list i)) (Verilog.modBody v) ->
  LocationSet.Equal
    (Verilog.module_locations v)
    (Verilog.module_writes v ∪ LocationSet.of_varset (VarSet.of_list i)) ->
  transfer_module_body tag (Verilog.modBody v) = inr q ->
  List.Forall (SMTQueries.term_satisfied_by ρ) q ->
  v ⇓ execution_of_valuation tag ρ.
Proof.
  intros * Hsorted Hall_driven Htransfer Hsat.
  unfold valid_execution.
  repeat unfold mk_initial_state, run_vmodule in *.
  rewrite sort_module_items_stable by assumption. simpl.
  eapply verilog_smt_match_states_partial_execution_match_on.
  unfold Verilog.module_locations.
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

Lemma sorted_reads_driven inputs body :
  module_items_sorted inputs body ->
  Verilog.module_body_reads body ⊆ Verilog.module_body_writes body ∪ inputs.
Proof.
  induction 1.
  all: simpl.
  all: LocationSet.setdec.
Qed.

Section Clean.
  Variable tag : VarTag.

  #[local]
  Lemma set_target_defined {w} regs (target : Verilog.assign_target w) bv :
    Verilog.assign_target_wf target ->
    RegisterState.defined_value_for (Verilog.assign_target_writes target)
      (set_target regs target (XBV.from_bv bv)).
  Proof.
    intros target_wf. revert regs bv.
    induction target_wf.
    all: intros.
    all: simp set_target; simpl.
    - unfold RegisterState.defined_value_for.
      intros loc Hloc.
      apply LocationSet.of_variable_spec in Hloc.
      destruct Hloc as [<- Hloc_wf].
      unfold RegisterState.get_location.
      rewrite RegisterState.set_reg_get_in.
      rewrite XBV.bit_of_as_bv by exact Hloc_wf.
      destruct (BV.bitOf _ bv).
      all: discriminate.
    - unfold RegisterState.defined_value_for.
      intros loc' Hloc'.
      apply LocationSet.singleton_spec in Hloc'.
      unfold LocationSet.E.eq in Hloc'. subst loc'.
      rewrite RegisterState.get_location_set_location.
      rewrite XBV.bit_of_as_bv by lia.
      destruct (BV.bitOf _ bv).
      all: discriminate.
    - unfold RegisterState.defined_value_for.
      intros loc Hloc.
      apply LocationSet.of_slice_spec in Hloc.
      unfold RegisterState.get_location, RegisterState.set_slice.
      destruct loc, slice, Hloc. simpl in *. subst.
      rewrite RegisterState.set_reg_get_in.
      rewrite XBV.set_slice_get_in by lia.
      rewrite XBV.bit_of_as_bv by lia.
      destruct (BV.bitOf _ bv).
      all: discriminate.
    - rewrite ! XBV.extr_no_exes by lia.
      RegisterState.unpack_defined_value_for.
      + eapply IHtarget_wf1.
      + rewrite set_target_preserve by exact Hno_overlap.
        eapply IHtarget_wf2.
  Qed.

  #[local]
  Lemma expr_to_smt_defined {w} (expr : Verilog.expression w) regs t :
    expr_to_smt tag expr = inr t ->
    RegisterState.defined_value_for (Verilog.expr_reads expr) regs ->
    exists bv, eval_expr regs expr = XBV.from_bv bv.
  Proof.
    intros Hexpr_to_smt Hinputs_defined.
    eexists.
    eapply expr_to_smt_value with (ρ := valuation_of_executions regs regs).
    - eassumption.
    - unfold verilog_smt_match_states_partial.
      symmetry.
      destruct tag.
      + apply execution_of_valuation_left_match_on. exact Hinputs_defined.
      + apply execution_of_valuation_right_match_on. exact Hinputs_defined.
  Qed.

  #[local]
  Lemma module_item_clean mi init smt :
    transfer_module_item tag mi = inr smt ->
    RegisterState.defined_value_for (Verilog.module_item_reads mi) init ->
    RegisterState.defined_value_for (Verilog.module_item_writes mi) (exec_module_item init mi).
  Proof.
    destruct mi as [[? target target_wf expr]].
    simp transfer_module_item exec_module_item exec_statement; simpl.
    intros Htransf Hinputs_defined.
    monad_inv.
    edestruct (expr_to_smt_defined expr) as [bv Heval]; [eassumption|eassumption|].
    rewrite Heval.
    apply set_target_defined.
    exact target_wf.
  Qed.

  #[local]
  Lemma module_body_clean inputs body init smt :
    module_items_sorted inputs body ->
    transfer_module_body tag body = inr smt ->
    RegisterState.defined_value_for inputs init ->
    RegisterState.defined_value_for (Verilog.module_body_writes body) (exec_module_body init body).
  Proof.
    intros Hsorted Htransf Hinputs_defined.
    funelim (transfer_module_body tag body).
    all: clear Heqcall.
    - apply RegisterState.defined_value_for_empty.
    - simp transfer_module_body in Htransf. monad_inv.
      simp exec_module_body. simpl.
      inv Hsorted.
      rename_match (Verilog.module_item_reads hd ⊆ inputs) into Hitem_reads_in_inputs.
      rename_match (module_items_sorted (Verilog.module_item_writes hd ∪ inputs) tl) into Htl_sorted.
      RegisterState.unpack_defined_value_for.
      + rewrite <- Facts.exec_module_body_preserve
          by (apply module_items_sorted_no_overwrite in Htl_sorted; LocationSet.setdec).
        eapply module_item_clean; try eassumption.
        rewrite Hitem_reads_in_inputs. exact Hinputs_defined.
      + eapply H; eauto; expect 1.
        RegisterState.unpack_defined_value_for.
        * eapply module_item_clean; try eassumption.
          rewrite Hitem_reads_in_inputs. exact Hinputs_defined.
        * rewrite <- Facts.exec_module_item_preserve by (symmetry; assumption).
          exact Hinputs_defined.
  Qed.

  Theorem verilog_to_smt_clean {i o} (v : Verilog.vmodule i o) smt :
    verilog_to_smt tag v = inr smt ->
    DefinedEquivalence.clean_module v.
  Proof.
    unfold verilog_to_smt. simpl.
    intros Htransf. monad_inv.
    rename_match (module_items_sorted _ _) into Hsorted.
    rename_match (LocationSet.of_varset (VarSet.of_list o) ⊆ Verilog.module_writes v) into Houtputs_driven.
    constructor.
    intros * Hinputs_defined.
    unfold run_vmodule, mk_initial_state.
    rewrite sort_module_items_stable by assumption.
    unfold Verilog.module_locations.
    assert (Hwrites_defined : RegisterState.defined_value_for (Verilog.module_writes v)
        (exec_module_body (e // VarSet.of_list i) (Verilog.modBody v))). {
      eapply module_body_clean.
      all: try eassumption; expect 1.
      apply RegisterState.defined_value_for_limit_to_regs.
      exact Hinputs_defined.
    }

    assert (Hinputs_defined_after : RegisterState.defined_value_for (LocationSet.of_varset (VarSet.of_list i))
        (exec_module_body (e // VarSet.of_list i) (Verilog.modBody v))). {
      rewrite <- Facts.exec_module_body_preserve
        by (symmetry; eapply module_items_sorted_no_overwrite; exact Hsorted).
      apply RegisterState.defined_value_for_limit_to_regs.
      exact Hinputs_defined.
    }

    RegisterState.unpack_defined_value_for.
    - exact Hinputs_defined_after.
    - rewrite Houtputs_driven. exact Hwrites_defined.
    - unfold Verilog.module_reads. rewrite sorted_reads_driven by eassumption.
      RegisterState.unpack_defined_value_for.
      + exact Hwrites_defined.
      + exact Hinputs_defined_after.
    - exact Hwrites_defined.
  Qed.
End Clean.

Theorem verilog_to_smt_correct {i o} tag (v : Verilog.vmodule i o) smt :
  verilog_to_smt tag v = inr smt ->
  SMTQueries.smt_reflect
    smt
    (fun ρ => v ⇓ execution_of_valuation tag ρ).
Proof.
  unfold verilog_to_smt.
  intros Htransf ρ. simpl in Htransf.
  monad_inv. simpl in *.
  split.
  all: intros H.
  - eapply transfer_module_body_valid.
    all: try eassumption.
    unfold Verilog.module_locations.
    assert (Verilog.module_reads v ⊆ Verilog.module_writes v ∪ LocationSet.of_varset (VarSet.of_list i))
      by now apply sorted_reads_driven.
    LocationSet.setdec.
  - eapply transfer_module_body_satisfiable.
    all: try eassumption.
Qed.
