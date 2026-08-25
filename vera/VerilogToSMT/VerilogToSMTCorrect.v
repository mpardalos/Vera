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
Local Open Scope monad_scope.
Local Open Scope list.
Local Open Scope verilog_scope.

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
  funelim (transfer_module_item tag mi).
  all: intros * Hdisjoint * Hexec Hmatch.
  all: monad_inv; expect 1.
  simp exec_module_item exec_statement in *.
  monad_inv.
  unfold SMTQueries.satisfied_by, SMTQueries.term_satisfied_by. repeat constructor.
  simpl.
  apply BV.bv_eq_reflect.

  simpl in Hmatch, Hdisjoint.
  disjoint_saturate.
  unpack_verilog_smt_match_states_partial. 
  rename_match
    (verilog_smt_match_states_partial (Verilog.expr_reads _) _ _ _)
    into Hbefore.
  rename_match
    (verilog_smt_match_states_partial (Verilog.assign_target_writes _) _ _ _)
    into Hafter.
  simp set_target in Hbefore, Hafter.
  (* apply verilog_smt_match_states_partial_set_reg_out in Hbefore;
   *   [|LocationSet.setdec].
   * assert (RegisterState.set_reg var (eval_expr regs rhs) regs var
   *         = execution_of_valuation tag ρ var) as Hafter_var. {
   *   apply XBV.bitOf_ext. intros bit_idx Hbit_idx.
   *   apply (Hafter (Location.Mk var bit_idx)).
   *   apply LocationSet.of_variable_spec. auto.
   * }
   * rewrite RegisterState.set_reg_get_in in Hafter_var.
   * unfold execution_of_valuation in Hafter_var.
   * apply XBV.from_bv_injective.
   * erewrite <- expr_to_smt_value by eassumption.
   * symmetry. apply Hafter_var. *)
Admitted.

Lemma smt_eq_sat_iff s ρ (l r : SMTLib.term s) :
  SMTQueries.term_satisfied_by ρ (SMTLib.Term_Eq l r) <->
    (SMTLib.interp_term ρ l = SMTLib.interp_term ρ r).
Proof.
  unfold SMTQueries.term_satisfied_by.
  simpl. apply SMTLib.value_eqb_eq.
Qed.

Lemma convert_bv_concat_low {w1 w2} (high : BV.bitvector w1) (low : BV.bitvector w2) :
  convert w2 (XBV.from_bv (BV.bv_concat high low)) = XBV.from_bv low.
Proof.
  rewrite <- XBV.concat_no_exes.
  funelim (convert w2 (XBV.concat (XBV.from_bv high) (XBV.from_bv low))); clear Heqcall.
  - lia.
  - XBV.bitvector_erase.
    rewrite RawXBV.extr_of_concat_lo.
    2: { rewrite RawXBV.from_bv_size. lia. }
    2: { rewrite RawXBV.from_bv_size, wf. lia. }
    unfold RawXBV.extr.
    rewrite RawXBV.from_bv_size, wf.
    replace (w2 + 0)%N with w2 by lia.
    rewrite N.leb_refl. cbn.
    apply RawXBV.extract_full.
    rewrite RawXBV.from_bv_size, wf. reflexivity.
  - XBV.bitvector_erase.
    apply RawXBV.concat_empty1.
    rewrite RawXBV.from_bv_size, wf0. lia.
Qed.

Lemma convert_bv_concat_high {w1 w2} (high : BV.bitvector w1) (low : BV.bitvector w2) :
  convert w1 (XBV.shr (XBV.from_bv (BV.bv_concat high low)) w2) = XBV.from_bv high.
Proof.
  rewrite <- XBV.concat_no_exes.
  funelim (convert w1
    (XBV.shr (XBV.concat (XBV.from_bv high) (XBV.from_bv low)) w2)); clear Heqcall.
  - lia.
  - XBV.bitvector_erase.
    rewrite RawXBV.shr_as_concat.
    rewrite N2Nat.id.
    rewrite RawXBV.concat_size.
    rewrite ! RawXBV.from_bv_size, wf0, wf.
    replace (w1 + w2 - w2)%N with w1 by lia.
    rewrite RawXBV.extr_of_concat_lo; expect 3.
    2: { autorewrite with xbv_size. lia. }
    2: { autorewrite with xbv_size. lia. }
    rewrite RawXBV.extr_of_extr by (autorewrite with xbv_size; lia).
    replace (w2 + 0)%N with w2 by lia.
    rewrite RawXBV.extr_of_concat_hi; expect 3.
    2: { rewrite RawXBV.from_bv_size, wf. lia. }
    2: { rewrite ! RawXBV.from_bv_size, wf0, wf. lia. }
    rewrite RawXBV.from_bv_size, wf.
    replace (w2 - w2)%N with 0%N by lia.
    unfold RawXBV.extr.
    rewrite RawXBV.from_bv_size, wf0.
    replace (w1 + 0)%N with w1 by lia.
    rewrite N.leb_refl. cbn.
    apply RawXBV.extract_full.
    rewrite RawXBV.from_bv_size, wf0. reflexivity.
  - XBV.bitvector_erase.
    assert (Hw2 : w2 = 0%N) by lia. subst w2. cbn.
    rewrite RawXBV.concat_empty2.
    + rewrite Hw2. cbn. rewrite RawXBV.shr_equation_1. reflexivity.
    + rewrite RawXBV.from_bv_size, Hw2. reflexivity.
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
  intros Hwf.
  induction Hwf; intros * Htarget_smt;
    simp assign_target_to_smt in Htarget_smt; monad_inv;
    simp set_target; simpl.
  - intros [v bit_idx] Hloc.
    apply LocationSet.of_variable_spec in Hloc. cbn in Hloc.
    destruct Hloc as [Hv _]. subst v.
    unfold RegisterState.get_location, execution_of_valuation.
    rewrite RegisterState.set_reg_get_in. reflexivity.
  - destruct loc as [vec idx]. cbn in *.
    simp assign_target_to_smt in Htarget_smt. inv Htarget_smt.
    intros loc' Hloc'.
    apply LocationSet.singleton_spec in Hloc'. unfold LocationSet.E.eq in Hloc'. subst loc'.
    unfold RegisterState.get_location, RegisterState.set_location, execution_of_valuation.
    rewrite RegisterState.set_reg_get_in, XBV.set_bit_get_in.
    pose proof (smt_select_bit_value ρ (Var.varType vec) (var_to_smt tag vec) idx wf) as Hselect.
    apply (f_equal (XBV.bitOf 0)) in Hselect.
    simpl in Hselect.
    change (XBV.bitOf 0
      (XBV.from_bv (SMTLib.interp_term ρ (smt_select_bit (var_to_smt tag vec) idx)))
      = XBV.bitOf idx (XBV.from_bv (ρ (verilog_to_smt_var tag vec)))).
    rewrite <- Hselect. reflexivity.
  - dependent elimination slice.
    simp assign_target_to_smt in Htarget_smt. inv Htarget_smt.
    intros loc Hloc.
    apply LocationSet.of_slice_spec in Hloc.
    unfold Slice.has_location in Hloc. cbn in Hloc.
    destruct Hloc as [Hvar Hidx].
    unfold RegisterState.get_location, RegisterState.set_slice, execution_of_valuation.
    cbn [Slice.get_var Slice.get_lo].
    rewrite <- Hvar, RegisterState.set_reg_get_in.
    replace (Location.idx loc) with (lo + (Location.idx loc - lo))%N by lia.
    change (lo <= Location.idx loc < lo + (1 + hi - lo))%N in Hidx.
    assert (Hoff : (Location.idx loc - lo < 1 + hi - lo)%N) by lia.
    rewrite XBV.set_slice_get_in by exact Hoff.
    simpl.
    change (XBV.bitOf (Location.idx loc - lo)
      (XBV.from_bv (BV.bv_extr lo (1 + hi - lo) (ρ (verilog_to_smt_var tag var)))) =
      XBV.bitOf (lo + (Location.idx loc - lo))
        (XBV.from_bv (ρ (verilog_to_smt_var tag var)))).
    rewrite <- XBV.extr_no_exes by lia.
    rewrite XBV.extr_bitOf by lia.
    f_equal.
  - apply verilog_smt_match_states_partial_split_iff. split.
    + rewrite convert_bv_concat_high.
      apply IHHwf1. reflexivity.
    + rewrite convert_bv_concat_low.
      pose proof (IHHwf2 regs ρ t0 eq_refl) as IHrhs.
      intros loc Hloc.
      transitivity (RegisterState.get_location
        (set_target regs rhs (XBV.from_bv (SMTLib.interp_term ρ t0))) loc).
      * exact (set_target_preserve lhs _ _ _ Hno_overlap loc Hloc).
      * apply IHrhs. exact Hloc.
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

Lemma verilog_to_smt_clean {i o} tag (v : Verilog.vmodule i o) smt :
  verilog_to_smt tag v = inr smt ->
  DefinedEquivalence.clean_module v.
Proof.
  unfold verilog_to_smt. simpl. intros Htransf. monad_inv.
  constructor.
  (* No Xs in vars *)
  admit.
Admitted.

Import EqNotations.

Lemma sorted_reads_driven inputs body :
  module_items_sorted inputs body ->
  Verilog.module_body_reads body ⊆ Verilog.module_body_writes body ∪ inputs.
Proof.
  induction 1.
  all: simpl.
  all: LocationSet.setdec.
Qed.

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
