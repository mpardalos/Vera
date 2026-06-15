From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import VerilogToSMT.
From vera Require Import VerilogSMT.
From vera Require SMTQueries.
From vera Require Import VerilogSemantics.
Import CombinationalOnly.
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

Lemma module_item_to_smt_satisfiable
  tag (mi : Verilog.module_item) inputs outputs :
  disjoint inputs outputs ->
  forall t regs ρ,
    transfer_module_item tag inputs outputs mi = inr t ->
    verilog_smt_match_states_partial
      (fun var => List.In var (Verilog.module_item_reads mi ++ Verilog.module_item_writes mi))
      tag
      (exec_module_item regs mi) ρ ->
    SMTQueries.term_satisfied_by ρ t.
Proof.
  funelim (transfer_module_item tag inputs outputs mi); expect 1.
  intros * Hdisjoint * Hexec Hmatch.
  monad_inv; expect 1.
  simp exec_module_item exec_statement in *.
  monad_inv.
  unfold SMTQueries.satisfied_by, SMTQueries.term_satisfied_by. repeat constructor.
  simpl.

  destruct (eval_expr_no_exes _ regs rhs) as [bv_rhs Hbv_rhs]; expect 2. {
    simp module_item_reads module_item_writes
      statement_reads statement_writes expr_reads
      in *.
    simpl in Hmatch.
    setoid_rewrite List.in_app_iff in Hmatch .
    apply verilog_smt_match_states_partial_split_iff in Hmatch.
    destruct Hmatch as [Hmatch_reads Hmatch_var].
    eapply defined_value_for_set_reg_intro_out with (var:=var). {
      rewrite List.Forall_forall in *.
      eapply disjoint_r_intro in Hdisjoint; eauto.
    }
    eapply verilog_smt_match_states_partial_defined_value_for.
    eassumption.
  }
  apply XBV.to_from_bv_inverse in Hbv_rhs. rewrite Hbv_rhs in *.

  apply BV.bv_eq_reflect.

  simpl in Hmatch.
  simp module_item_reads module_item_writes statement_writes statement_reads expr_reads in Hmatch.
  apply XBV.from_bv_injective.
  erewrite <- Hmatch by eauto with datatypes.
  rewrite RegisterState.set_reg_get_in.
  rewrite <- Hbv_rhs.
  eapply expr_to_smt_value.
  - eassumption.
  - unpack_verilog_smt_match_states_partial. 
    eapply verilog_smt_match_states_partial_set_reg_out; [|eassumption].
    unfold disjoint in *. rewrite List.Forall_forall in *. firstorder.
Qed.

Lemma smt_eq_sat_iff s ρ (l r : SMTLib.term s) :
  SMTQueries.term_satisfied_by ρ (SMTLib.Term_Eq l r) <->
    (SMTLib.interp_term ρ l = SMTLib.interp_term ρ r).
Proof.
  unfold SMTQueries.term_satisfied_by.
  simpl. apply SMTLib.value_eqb_eq.
Qed.

Lemma module_item_to_smt_valid tag  (mi : Verilog.module_item) inputs outputs :
  disjoint inputs outputs ->
  forall ρ t,
    transfer_module_item tag inputs outputs mi = inr t ->
    SMTQueries.term_satisfied_by ρ t ->
    forall r1,
      verilog_smt_match_states_partial
        (fun var => List.In var (Verilog.module_item_reads mi))
        tag r1 ρ ->
          verilog_smt_match_states_partial
            (fun var => List.In var (Verilog.module_item_reads mi ++ Verilog.module_item_writes mi))
              tag
              (exec_module_item r1 mi) ρ.
Proof.
  funelim (transfer_module_item tag inputs outputs mi);
    intros * Hdisjoint * Htransf Hsat * Hmatch1; monad_inv; [idtac].
  simp module_item_reads module_item_writes statement_writes statement_reads expr_reads in *.
  simp exec_module_item exec_statement in *.
  monad_inv.
  rewrite smt_eq_sat_iff in Hsat.
  pose proof expr_to_smt_valid as Hvalue_match. insterU Hvalue_match.
  inv Hvalue_match. simpl.
  unpack_verilog_smt_match_states_partial.
  - apply verilog_smt_match_states_partial_set_reg_out; [|assumption].
    unfold disjoint in *.
    rewrite List.Forall_forall in *.
    firstorder.
  - unfold verilog_smt_match_states_partial.
    intros. inv H; [|crush].
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

Lemma transfer_module_item_inputs tag inputs outputs mi t :
  transfer_module_item tag inputs outputs mi = inr t ->
  list_subset (Verilog.module_item_reads mi) inputs.
Proof.
  unfold list_subset.
  funelim (transfer_module_item tag inputs outputs mi); intros; try discriminate.
  monad_inv.
  simp module_item_reads statement_reads.
Qed.

Lemma transfer_module_item_outputs tag inputs outputs mi t :
  transfer_module_item tag inputs outputs mi = inr t ->
  list_subset (Verilog.module_item_writes mi) outputs.
Proof.
  unfold list_subset.
  funelim (transfer_module_item tag inputs outputs mi); intros; try discriminate.
  monad_inv.
  simp module_item_writes statement_writes expr_reads.
  eauto with datatypes.
Qed.

Lemma transfer_module_body_outputs tag inputs outputs mis t :
  transfer_module_body tag inputs outputs mis = inr t ->
  list_subset (Verilog.module_body_writes mis) outputs.
Proof.
  funelim (transfer_module_body tag inputs outputs mis); intros; try discriminate.
  - inv H. simp module_body_writes. constructor.
  - monad_inv.
    simp module_body_writes in *.
    apply list_subset_app.
    split; eauto using transfer_module_item_outputs with datatypes.
Qed.

Lemma transfer_module_body_inputs tag inputs outputs mis t :
  transfer_module_body tag inputs outputs mis = inr t ->
  list_subset (Verilog.module_body_reads mis) inputs.
Proof.
  funelim (transfer_module_body tag inputs inputs mis); intros; try discriminate.
  - inv H. simp module_body_reads. constructor.
  - simp transfer_module_body module_body_reads in *.
    monad_inv.
    apply list_subset_app.
    split; eauto using transfer_module_item_inputs with datatypes.
Qed.

Lemma transfer_module_body_exec_satisfiable inputs outputs body :
  forall tag r1 q ρ,
    disjoint inputs outputs ->
    transfer_module_body tag inputs outputs body = inr q ->
    verilog_smt_match_states_partial
      (fun var => List.In var (Verilog.module_body_reads body ++ Verilog.module_body_writes body))
      tag (exec_module_body r1 body) ρ ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q.
Proof.
  induction body; intros * Hdisjoint Htransfer Hmatch; simp module_body_reads module_body_writes transfer_module_body in *; [some_inv; constructor|].
  simp exec_module_body in Hmatch. simpl in Hmatch.
  monad_inv.
  constructor.
  - eapply module_item_to_smt_satisfiable with (inputs := inputs) (regs:=r1).
    all: try eassumption; expect 1.
    eapply verilog_smt_match_states_partial_change_regs with (r1 := (exec_module_body (exec_module_item r1 a) body)). {
      intros.
      symmetry. eapply Facts.exec_module_body_preserve; [clear H|apply H].
      unfold disjoint in *.
      rewrite ! List.Forall_forall in *.
      setoid_rewrite List.in_app_iff.
      setoid_rewrite transfer_module_item_inputs; try eassumption.
      intros var' [Hvar_read|Hvar_write].
      - setoid_rewrite transfer_module_body_outputs; try eassumption.
        eauto.
      - eauto.
    }
    eapply verilog_smt_match_states_partial_impl; [|eassumption].
    intros. simpl.
    rewrite ! List.in_app_iff in *.
    intuition assumption.
  - eapply IHbody; try eauto; [idtac].
    eapply verilog_smt_match_states_partial_impl; [|eassumption].
    intros. simpl.
    rewrite ! List.in_app_iff in *.
    intuition assumption.
Qed.

Import Facts.

Local Open Scope verilog.

Lemma transfer_module_body_satisfiable v tag ρ q :
    List.NoDup (Verilog.module_body_writes (Verilog.modBody v)) ->
    list_subset (Verilog.module_body_reads (Verilog.modBody v)) (Verilog.module_inputs v) ->
    Permutation (Verilog.module_body_writes (Verilog.modBody v)) (Verilog.module_outputs v) ->
    disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
    module_items_sorted (Verilog.module_inputs v) (Verilog.modBody v) ->
    transfer_module_body tag (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
    v ⇓ (execution_of_valuation tag ρ) ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q.
Proof.
  intros * Hwrites_ndup Hreads_subset Hwrites_permute Hdisjoint Hsorted Htransfer Hvalid .
  unfold "⇓" in Hvalid.
  RegisterState.unpack_match_on.
  rename_match (_ =( Verilog.module_inputs _ )= _) into Hmatch_inputs.
  rename_match (_ =( Verilog.module_outputs _ )= _) into Hmatch_outputs.
  repeat unfold mk_initial_state, run_vmodule in *.
  rewrite ! sort_module_items_stable in * by eassumption.
  eapply transfer_module_body_exec_satisfiable; eauto.
  (* apply transfer_module_body_inputs in Htransfer.
   * rewrite List.Forall_forall in Htransfer. *)
  apply execution_match_on_verilog_smt_match_states_partial.
  RegisterState.unpack_match_on.
  - setoid_rewrite Hreads_subset. apply Hmatch_inputs.
  - setoid_rewrite Hwrites_permute. apply Hmatch_outputs.
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

Lemma transfer_module_body_exec_valid inputs outputs body : forall tag ρ q,
    disjoint inputs outputs ->
    list_subset (Verilog.module_body_writes body) outputs ->
    transfer_module_body tag inputs outputs body = inr q ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q ->
    forall r1,
      verilog_smt_match_states_partial
        (fun var => List.In var inputs) tag
	r1 ρ ->
      verilog_smt_match_states_partial
        (fun var => List.In var (inputs ++ Verilog.module_body_writes body)) tag
	(exec_module_body r1 body) ρ.
Proof.
  induction body.
  all: intros * Hdisjoint Houtputs_in Htransfer Hsat * Hmatch1.
  all: simpl in *.
  all: simp module_body_reads module_body_writes transfer_module_body exec_module_body in *.
  all: autorewrite with list.
  1: crush. all: expect 1.
  unpack_list_subset.
  disjoint_saturate.
  monad_inv. inv Hsat.
  rename_match (list_subset (Verilog.module_item_writes a) outputs) into Hitem_writes.
  rename_match (list_subset (Verilog.module_item_reads a) inputs) into Hitem_reads.
  eapply verilog_smt_match_states_partial_split with
    (C1 := fun var => List.In var (inputs ++ Verilog.module_body_writes body))
    (C2 := fun var => List.In var (Verilog.module_item_writes a)).
  - repeat setoid_rewrite List.in_app_iff. intros ? [? | [? | ?]]; auto.
  - simpl.
    eapply IHbody; try eassumption; expect 1.
    setoid_rewrite <- Facts.exec_module_item_preserve; [assumption|].
    setoid_rewrite Hitem_writes. assumption.
  - simpl.
    setoid_rewrite <- Facts.exec_module_body_preserve; [|assumption].
    eapply verilog_smt_match_states_partial_impl; cycle 1.
    + eapply module_item_to_smt_valid; cycle 1.
      * eassumption.
      * assumption.
      * setoid_rewrite Hitem_reads. assumption.
      * assumption.
    + setoid_rewrite List.in_app_iff. auto.
Qed.

Lemma transfer_module_body_valid tag v ρ q :
  module_items_sorted (Verilog.module_inputs v) (Verilog.modBody v) ->
  list_subset (Verilog.module_body_reads (Verilog.modBody v)) (Verilog.module_inputs v) ->
  Permutation (Verilog.module_body_writes (Verilog.modBody v)) (Verilog.module_outputs v) ->
  List.NoDup (Verilog.module_body_writes (Verilog.modBody v)) ->
  disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
  transfer_module_body tag (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
  List.Forall (SMTQueries.term_satisfied_by ρ) q ->
  valid_execution v (execution_of_valuation tag ρ).
Proof.
  intros * Hsorted Hinputs_subset Houtputs_permute Hnodup_writes Hdisjoint Htransfer Hsat.
  unfold valid_execution.
  repeat unfold mk_initial_state, run_vmodule in *.
  rewrite sort_module_items_stable by assumption. simpl.
  eapply verilog_smt_match_states_partial_execution_match_on.
  setoid_rewrite <- Houtputs_permute.
  eapply transfer_module_body_exec_valid.
  - eassumption.
  - rewrite Houtputs_permute. reflexivity.
  - eassumption.
  - eassumption.
  - assert (H : execution_of_valuation tag ρ // Verilog.module_inputs v =( Verilog.module_inputs v )= execution_of_valuation tag ρ). {
      apply RegisterState.match_on_limit_to_regs_iff.
      apply RegisterState.limit_to_regs_twice.
    } rewrite H. clear H.
    apply verilog_smt_match_states_execution_of_valuation_same.
Qed.

Import EqNotations.

Theorem verilog_to_smt_correct tag v smt :
  verilog_to_smt tag v = inr smt ->
  SMTQueries.smt_reflect
    smt
    (fun ρ => valid_execution v (execution_of_valuation tag ρ)).
Proof.
  intros H ρ.
  split.
  - intros Hsat.
    unfold verilog_to_smt in H.
    monad_inv. simpl in *.
    eapply transfer_module_body_valid.
    all: eassumption.
  - intros Hvalid.
    unfold verilog_to_smt in H. monad_inv. simpl in *.
    unfold SMTQueries.satisfied_by. simpl.
    eapply transfer_module_body_satisfiable.
    all: eassumption.
Qed.

Lemma defined_value_for_execution_match_on C e' e :
  e' ={ C }= e ->
  RegisterState.defined_value_for C e' ->
  RegisterState.defined_value_for C e.
Proof.
  unfold "_ ={ _ }= _", RegisterState.defined_value_for.
  intros Hmatch Hdefined var HC.
  insterU Hmatch. insterU Hdefined.
  destruct Hdefined as [bv ?].
  exists bv. crush.
Qed.

(* Move me to semantics *)
(* Should be replaced by just clean_module *)
Lemma valid_execution_no_exes_written v : forall e tag q,
    verilog_to_smt tag v = inr q ->
    valid_execution v e ->
    RegisterState.defined_value_for (fun var => List.In var (Verilog.module_inputs v)) e ->
    RegisterState.defined_value_for (fun var => List.In var (Verilog.module_body_writes (Verilog.modBody v))) e.
Proof.
  unfold valid_execution, all_vars_driven.
  intros * Htransf Hmatch Hinputs_defined.
  unfold verilog_to_smt in Htransf. monad_inv.
  rename_match (module_items_sorted _ _) into Hsorted.
  rename_match (Permutation _ _) into Hout_permute.
  unfold run_vmodule in Hmatch.
  rewrite sort_module_items_stable in Hmatch by apply Hsorted.
  RegisterState.unpack_match_on.
  rename_match (exec_module_body _ _ =( Verilog.module_outputs _ )= _) into Hmatch_out.
  setoid_rewrite <- Hout_permute in Hmatch_out.
  rewrite <- Hmatch_out.
  apply Clean.exec_module_body_defined with (l_before := Verilog.module_inputs v).
  - assumption.
  - apply list_subset_app_r.
  - unfold mk_initial_state.
    assert (Hdrop_limit : e // Verilog.module_inputs v =( Verilog.module_inputs v )= e). {
        apply RegisterState.match_on_limit_to_regs_iff.
        apply RegisterState.limit_to_regs_twice.
    } rewrite Hdrop_limit.
    apply Hinputs_defined.
Qed.
