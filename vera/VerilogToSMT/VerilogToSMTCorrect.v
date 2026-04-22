From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import VerilogToSMT.
From vera Require Import VerilogSMT.
From vera Require SMTQueries.
Import (coercions) VerilogSMTBijection.
From vera Require Import VerilogSemantics.
Import CombinationalOnly.
From vera Require Import Verilog.
From vera Require Import Bitvector.
Import RawXBV(bit(..)).
From vera Require Import VerilogToSMT.Expressions.
From vera Require Import VerilogToSMT.Match.

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

Lemma assign_vars_vars start vars :
  List.map fst (assign_vars start vars) = vars.
Proof.
  revert start.
  induction vars; intros;
    simp assign_vars in *; cbn in *.
  - reflexivity.
  - rewrite IHvars. reflexivity.
Qed.

Lemma assign_vars_smtname_start start vars :
  List.Forall (fun n => n >= start) (List.map snd (assign_vars start vars)).
Proof.
  revert start.
  induction vars;
    intros; simp assign_vars in *; cbn in *;
    constructor.
  - lia.
  - specialize (IHvars (S start)).
    revert IHvars.
    eapply List.Forall_impl.
    lia.
Qed.

Lemma assign_vars_smtname_nodup start vars :
  List.NoDup (List.map snd (assign_vars start vars)).
Proof.
  revert start.
  induction vars; intros; simp assign_vars in *; cbn in *;
    constructor.
  - intro contra.
    pose proof (assign_vars_smtname_start (S start) vars).
    eapply List.Forall_forall in H; try eassumption.
    lia.
  - eapply IHvars.
Qed.

Lemma assign_vars_fst vars : forall start,
  List.map fst (assign_vars start vars) = vars.
Proof.
  induction vars; intros; simp assign_vars in *; crush.
Qed.

Lemma mk_bijection_smt_map_match tag start m vars :
  mk_bijection tag (assign_vars start vars) = inr m ->
  SMT.match_map_vars tag m vars.
Proof.
  Opaque VerilogSMTBijection.lookup_left.
  unfold SMT.match_map_vars.
  remember (assign_vars start vars) as assignment.
  epose proof (assign_vars_smtname_nodup _ _) as Hnodup;
    rewrite <- Heqassignment in Hnodup.
  epose proof (assign_vars_fst _ _) as Hvars;
    rewrite <- Heqassignment in Hvars.
  clear start Heqassignment.
  generalize dependent Hnodup.
  generalize dependent vars.
  generalize dependent m.
  induction assignment; intros * ? ? Hbijection.
  - simp mk_bijection in *. inv Hbijection.
    split; intros H; cbn in *; solve_by_inverts 2%nat.
  - destruct a as [var smtName].
    simp mk_bijection in Hbijection; inv Hbijection; autodestruct.
    inv Hnodup.
    split; intros H.
    + destruct H as [smtName' H].
      cbn. cbn in H.
      autodestruct; cbn in *; subst.
      * left. congruence.
      * right.
        edestruct IHassignment; eauto.
    + cbn. autodestruct.
      * eauto.
      * eapply IHassignment; eauto; now some_inv.
Qed.

Lemma verilog_to_smt_map_match tag start v smt :
  verilog_to_smt tag start v = inr smt ->
  SMT.match_map_vars tag (SMT.nameMap smt) (Verilog.modVariables v).
Proof.
  intros.
  unfold verilog_to_smt in *. simpl in *.
  autodestruct_eqn E. cbn.
  eauto using mk_bijection_smt_map_match.
Qed.

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
  tag m (mi : Verilog.module_item) inputs outputs :
  disjoint inputs outputs ->
  forall t regs ρ,
    transfer_module_item tag m inputs outputs mi = inr t ->
    verilog_smt_match_states_partial
      (fun var => List.In var (Verilog.module_item_reads mi ++ Verilog.module_item_writes mi))
      tag m
      (exec_module_item regs mi) ρ ->
    SMTQueries.term_satisfied_by ρ t.
Proof.
  funelim (transfer_module_item tag m inputs outputs mi); expect 1.
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
  apply XBV.from_bv_injective.

  erewrite <- var_to_smt_value with (var := var) (regs := (RegisterState.set_reg var (XBV.from_bv bv_rhs) regs)); eauto; cycle 1.
  {
    eapply verilog_smt_match_states_partial_impl; [|eassumption].
    intros. subst.
    simp module_item_reads module_item_writes statement_writes statement_reads expr_reads.
    eauto with datatypes.
  }
  rewrite RegisterState.set_reg_get_in. simpl.
  rewrite <- Hbv_rhs.

  eapply expr_to_smt_value; [eassumption|].
  eapply verilog_smt_match_states_partial_set_reg_out; cycle 1.
  - eapply verilog_smt_match_states_partial_impl; [|eassumption].
    intros. simpl.
    simp module_item_reads module_item_writes statement_writes statement_reads expr_reads.
    eauto with datatypes.
  - rewrite List.Forall_forall in *.
    eapply disjoint_r_intro in Hdisjoint; eauto.
Qed.

Lemma smt_eq_sat_iff s ρ (l r : SMTLib.term s) :
  SMTQueries.term_satisfied_by ρ (SMTLib.Term_Eq l r) <->
    (SMTLib.interp_term ρ l = SMTLib.interp_term ρ r).
Proof.
  unfold SMTQueries.term_satisfied_by.
  simpl. apply SMTLib.value_eqb_eq.
Qed.

Lemma module_item_to_smt_valid tag m (mi : Verilog.module_item) inputs outputs :
  disjoint inputs outputs ->
  forall ρ t,
    transfer_module_item tag m inputs outputs mi = inr t ->
    SMTQueries.term_satisfied_by ρ t ->
    forall r1,
      verilog_smt_match_states_partial
        (fun var => List.In var (Verilog.module_item_reads mi))
        tag m r1 ρ ->
          verilog_smt_match_states_partial
            (fun var => List.In var (Verilog.module_item_reads mi ++ Verilog.module_item_writes mi))
              tag m
              (exec_module_item r1 mi) ρ.
Proof.
  funelim (transfer_module_item tag m inputs outputs mi);
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
    edestruct var_to_smt_valid as [xbv_var [Heval_var Hmatch_var]]; eauto.
    eexists. split; [eassumption|].
    unfold verilog_smt_match_on_name.
    rewrite Hmatch_var.
    rewrite RegisterState.set_reg_get_in.
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

Lemma transfer_module_item_inputs tag m inputs outputs mi t :
  transfer_module_item tag m inputs outputs mi = inr t ->
  list_subset (Verilog.module_item_reads mi) inputs.
Proof.
  unfold list_subset.
  funelim (transfer_module_item tag m inputs outputs mi); intros; try discriminate.
  monad_inv.
  simp module_item_reads statement_reads.
Qed.

Lemma transfer_module_item_outputs tag m inputs outputs mi t :
  transfer_module_item tag m inputs outputs mi = inr t ->
  list_subset (Verilog.module_item_writes mi) outputs.
Proof.
  unfold list_subset.
  funelim (transfer_module_item tag m inputs outputs mi); intros; try discriminate.
  monad_inv.
  simp module_item_writes statement_writes expr_reads.
  eauto with datatypes.
Qed.

Lemma transfer_module_body_outputs tag m inputs outputs mis t :
  transfer_module_body tag m inputs outputs mis = inr t ->
  list_subset (Verilog.module_body_writes mis) outputs.
Proof.
  funelim (transfer_module_body tag m inputs outputs mis); intros; try discriminate.
  - inv H. simp module_body_writes. constructor.
  - monad_inv.
    simp module_body_writes in *.
    apply list_subset_app.
    split; eauto using transfer_module_item_outputs with datatypes.
Qed.

Lemma transfer_module_body_inputs tag m inputs outputs mis t :
  transfer_module_body tag m inputs outputs mis = inr t ->
  list_subset (Verilog.module_body_reads mis) inputs.
Proof.
  funelim (transfer_module_body tag m inputs inputs mis); intros; try discriminate.
  - inv H. simp module_body_reads. constructor.
  - simp transfer_module_body module_body_reads in *.
    monad_inv.
    apply list_subset_app.
    split; eauto using transfer_module_item_inputs with datatypes.
Qed.

Lemma transfer_module_body_exec_satisfiable inputs outputs body :
  forall tag (m : VerilogSMTBijection.t) r1 q ρ,
    disjoint inputs outputs ->
    transfer_module_body tag m inputs outputs body = inr q ->
    verilog_smt_match_states_partial
      (fun var => List.In var (Verilog.module_body_reads body ++ Verilog.module_body_writes body))
      tag m (exec_module_body r1 body) ρ ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q.
Proof.
  (* generalize dependent (Verilog.module_outputs v). intro outputs.
   * generalize dependent (Verilog.module_inputs v). intro inputs.
   * generalize dependent (Verilog.modBody v). intro body. *)
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

Lemma transfer_module_body_satisfiable v tag (m : VerilogSMTBijection.t) ρ q :
    List.NoDup (Verilog.module_body_writes (Verilog.modBody v)) ->
    list_subset (Verilog.module_body_reads (Verilog.modBody v)) (Verilog.module_inputs v) ->
    Permutation (Verilog.module_body_writes (Verilog.modBody v)) (Verilog.module_outputs v) ->
    disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
    module_items_sorted (Verilog.module_inputs v) (Verilog.modBody v) ->
    transfer_module_body tag m (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
    SMT.match_map_vars tag m (Verilog.modVariables v) ->
    v ⇓ (SMT.execution_of_valuation tag m ρ) ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q.
Proof.
  intros * Hwrites_ndup Hreads_subset Hwrites_permute Hdisjoint Hsorted Htransfer Hmatch_vars Hvalid .
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
  - RegisterState.unpack_defined_value_for.
    + setoid_rewrite Hreads_subset.
      rewrite Hmatch_inputs.
      eapply RegisterState.defined_value_for_impl;
        [|now apply SMT.execution_of_valuation_defined_value].
      simpl. intros.
      apply Hmatch_vars.
      apply Verilog.module_input_in_vars.
      assumption.
    + setoid_rewrite Hwrites_permute.
      setoid_rewrite Hmatch_outputs.
      eapply RegisterState.defined_value_for_impl;
        [|now apply SMT.execution_of_valuation_defined_value].
      simpl. intros.
      apply Hmatch_vars.
      apply Verilog.module_outputs_in_vars.
      assumption.
  - RegisterState.unpack_match_on.
    + setoid_rewrite Hreads_subset. apply Hmatch_inputs.
    + setoid_rewrite Hwrites_permute. apply Hmatch_outputs.
Qed.

Global Instance verilog_smt_match_states_partial_proper C :
  Proper
    (eq ==> eq ==> (RegisterState.match_on C) ==> eq ==> iff)
    (verilog_smt_match_states_partial C).
Proof.
  unfold verilog_smt_match_states_partial.
  repeat intro. subst.
  split; intros.
  - edestruct H as [smtName [Hlookup Hmatch]]; [eassumption|].
    eexists. split; [eauto|].
    inv Hmatch.
    unfold verilog_smt_match_on_name.
    now rewrite <- H1.
  - edestruct H as [smtName [Hlookup Hmatch]]; [eassumption|].
    eexists. split; [eauto|].
    inv Hmatch. 
    unfold verilog_smt_match_on_name.
    now rewrite H1.
Qed.

Lemma transfer_module_body_exec_valid inputs outputs body : forall tag m ρ q,
    disjoint inputs outputs ->
    list_subset (Verilog.module_body_writes body) outputs ->
    transfer_module_body tag m inputs outputs body = inr q ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q ->
    forall r1,
      verilog_smt_match_states_partial
        (fun var => List.In var inputs) tag m
	r1 ρ ->
      verilog_smt_match_states_partial
        (fun var => List.In var (inputs ++ Verilog.module_body_writes body)) tag m
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

Lemma transfer_module_body_valid tag m v ρ q :
  module_items_sorted (Verilog.module_inputs v) (Verilog.modBody v) ->
  list_subset (Verilog.module_body_reads (Verilog.modBody v)) (Verilog.module_inputs v) ->
  Permutation (Verilog.module_body_writes (Verilog.modBody v)) (Verilog.module_outputs v) ->
  List.NoDup (Verilog.module_body_writes (Verilog.modBody v)) ->
  disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
  transfer_module_body tag m (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
  List.Forall (SMTQueries.term_satisfied_by ρ) q ->
  SMT.match_map_vars tag m (Verilog.modVariables v) ->
  valid_execution v (SMT.execution_of_valuation tag m ρ).
Proof.
  intros * Hsorted Hinputs_subset Houtputs_permute Hnodup_writes Hdisjoint Htransfer Hsat Hmatch_vars.
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
  - assert (H : SMT.execution_of_valuation tag m ρ // Verilog.module_inputs v =( Verilog.module_inputs v )= SMT.execution_of_valuation tag m ρ). {
      apply RegisterState.match_on_limit_to_regs_iff.
      apply RegisterState.limit_to_regs_twice.
    } rewrite H. clear H.
    eapply verilog_smt_match_states_partial_impl; cycle 1.
    + apply verilog_smt_match_states_execution_of_valuation_same.
    + simpl. intros.
      apply Hmatch_vars.
      apply Verilog.module_input_in_vars.
      assumption.
Qed.

Lemma bij_gsi (m : VerilogSMTBijection.t) tag var smtName prf1 prf2 :
  VerilogSMTBijection.insert (tag, var) smtName m prf1 prf2 (tag, var) = Some smtName.
Proof. crush. Qed.

Lemma bij_gso (m : VerilogSMTBijection.t) x1 x2 smtName prf1 prf2 :
  x1 <> x2 ->
  VerilogSMTBijection.insert x1 smtName m prf1 prf2 x2 = m x2.
Proof. crush. Qed.

Lemma mk_bijection_lookup tag assignments : forall m var smtName,
  mk_bijection tag assignments = inr m ->
  List.In (var, smtName) assignments ->
  m (tag, var) = Some smtName.
Proof.
  induction assignments as [|[var smtName]]; intros * H Hin.
  - simp mk_bijection in H. inv H.
    crush.
  - simp mk_bijection in H.
    monad_inv.
    inv Hin.
    + inv H.
      apply bij_gsi.
    + insterU IHassignments.
      rewrite bij_gso; crush.
Qed.

Import EqNotations.

Theorem verilog_to_smt_correct tag start v smt :
  verilog_to_smt tag start v = inr smt ->
  SMTQueries.smt_reflect
    (SMT.query smt)
    (fun ρ => valid_execution v (SMT.execution_of_valuation tag (SMT.nameMap smt) ρ)).
Proof.
  intros H ρ.
  split.
  - intros Hsat.
    unfold verilog_to_smt in H.
    monad_inv. simpl in *.
    eapply transfer_module_body_valid.
    all: eauto using mk_bijection_smt_map_match.
  - intros Hvalid.
    unfold verilog_to_smt in H. monad_inv. simpl in *.
    unfold SMTQueries.satisfied_by. simpl.
    eapply transfer_module_body_satisfiable.
    all: eauto using mk_bijection_smt_map_match.
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
Lemma valid_execution_no_exes_written v : forall e tag start q,
    verilog_to_smt tag start v = inr q ->
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
