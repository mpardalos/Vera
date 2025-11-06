From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import VerilogToSMT.
From vera Require Import VerilogSMT.
From vera Require SMTQueries.
Import (coercions) VerilogSMTBijection.
From vera Require Import VerilogSemantics.
From vera Require Import Verilog.
Import CombinationalOnly.
From vera Require Import Bitvector.
Import RawXBV(bit(..)).
From vera Require Import VerilogToSMT.Expressions.
From vera Require Import VerilogToSMT.Match.

From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.MonadState.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Functor.

From Coq Require List.
From Coq Require Import String.
From Coq Require Import Logic.ProofIrrelevance.
From Coq Require Import NArith.
From Coq Require Import PeanoNat.
From Coq Require Import Morphisms.
From Coq Require Import Setoid.

From Equations Require Import Equations.

Import List.ListNotations.
Import CommonNotations.
Import MonadLetNotation.
Import FunctorNotation.
Import SigTNotations.

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
  defined_value_for C (set_reg var xbv regs) ->
  defined_value_for C regs.
Proof.
  unfold defined_value_for.
  intros HnotC Hdefined var1 HC.
  insterU Hdefined.
  destruct Hdefined as [? [? ?]].
  rewrite set_reg_get_out in H by crush.
  crush.
Qed.

Lemma module_item_to_smt_satisfiable
  tag m (mi : Verilog.module_item) inputs outputs :
  disjoint inputs outputs ->
  forall t regs regs' ρ,
    transfer_module_item tag m inputs outputs mi = inr t ->
    exec_module_item regs mi = Some regs' ->
    verilog_smt_match_states_partial
      (fun var => List.In var (Verilog.module_item_reads mi ++ Verilog.module_item_writes mi))
      tag m regs' ρ ->
    SMTQueries.term_satisfied_by ρ t.
Proof.
  funelim (transfer_module_item tag m inputs outputs mi); intros; monad_inv; [idtac].
  simp exec_module_item exec_statement in *.
  monad_inv.
  unfold SMTQueries.satisfied_by, SMTQueries.term_satisfied_by. repeat constructor.
  simpl.

  edestruct eval_expr_no_exes as [bv_rhs Hbv_rhs]; eauto; [idtac|idtac]. {
    simp module_item_reads module_item_writes
      statement_reads statement_writes expr_reads
      in *.
    setoid_rewrite List.in_app_iff in H2.
    apply verilog_smt_match_states_partial_split_iff in H2.
    destruct H2.
    eapply defined_value_for_set_reg_intro_out with (var:=var). {
      rewrite List.Forall_forall in *.
      eapply disjoint_r_intro in H; eauto.
    }
    eapply verilog_smt_match_states_partial_defined_value_for.
    eassumption.
  }
  apply XBV.to_from_bv_inverse in Hbv_rhs. subst x.

  erewrite var_to_smt_value with (var := var) (regs := (set_reg var (XBV.from_bv bv_rhs) regs)); eauto; cycle 1.
  {
    eapply verilog_smt_match_states_partial_impl; [|eassumption].
    intros. subst.
    simp module_item_reads module_item_writes statement_writes statement_reads expr_reads.
    eauto with datatypes.
  }
  rewrite set_reg_get_in. simpl. rewrite XBV.xbv_bv_inverse.

  erewrite expr_to_smt_value with (expr := rhs) (regs := regs); eauto; cycle 1. {
    eapply verilog_smt_match_states_partial_set_reg_out; cycle 1.
    - eapply verilog_smt_match_states_partial_impl; [|eassumption].
      intros. simpl.
      simp module_item_reads module_item_writes statement_writes statement_reads expr_reads.
      eauto with datatypes.
    - rewrite List.Forall_forall in *.
      eapply disjoint_r_intro in H; eauto.
  }
  rewrite E. simpl. rewrite XBV.xbv_bv_inverse.
  autodestruct; [|contradiction].
  repeat f_equal. apply BV.bv_eq_reflect. apply eq_rect_eq.
Qed.

Lemma smt_eq_sat_iff ρ l r :
  SMTQueries.term_satisfied_by ρ (SMTLib.Term_Eq l r) <->
    (exists v,
        SMTLib.interp_term ρ l = Some v /\
        SMTLib.interp_term ρ r = Some v).
Proof.
  unfold SMTQueries.term_satisfied_by.
  split; intros H.
  - inv H. simpl in *. autodestruct_eqn E.
    apply_somewhere SMTLib.value_eqb_eq.
    subst. eauto.
  - destruct H as [v [Hl Hr]].
    repeat constructor. simpl.
    rewrite Hl, Hr.
    repeat f_equal.
    now apply SMTLib.value_eqb_eq.
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
      exists r2, exec_module_item r1 mi = Some r2 /\
              verilog_smt_match_states_partial
                (fun var => List.In var (Verilog.module_item_reads mi ++ Verilog.module_item_writes mi))
                tag m r2 ρ.
Proof.
  funelim (transfer_module_item tag m inputs outputs mi);
    intros * Hdisjoint * Htransf Hsat * Hmatch1; monad_inv; [idtac].
  simp module_item_reads module_item_writes statement_writes statement_reads expr_reads in *.
  simp exec_module_item exec_statement in *.
  monad_inv.
  rewrite smt_eq_sat_iff in Hsat. destruct Hsat as [v [Ht0 Ht1]].
  edestruct expr_to_smt_valid as [xbv_expr [Heval_expr Hmatch_expr]]; eauto; [idtac].
  edestruct eval_expr_no_exes;
    eauto using verilog_smt_match_states_partial_defined_value_for;
    [idtac].
  apply_somewhere XBV.bv_xbv_inverse. subst xbv_expr.
  rewrite Heval_expr.
  edestruct var_to_smt_valid as [xbv_var [Heval_var Hmatch_var]]; eauto.
  simpl. eexists. split; [reflexivity|].
  eapply verilog_smt_match_states_partial_split. solve [apply List.in_app_or].
  - eapply verilog_smt_match_states_partial_set_reg_elim. {
      eexists. split. { eassumption. }
      replace (ρ xbv_var).
      inv Hmatch_expr.
      apply_somewhere RawXBV.from_bv_injective.
      repeat f_equal.
      now apply BV.of_bits_equal.
    }
    eassumption.
  - unfold verilog_smt_match_states_partial.
    intros * Hin.
    inv Hin; [|crush].
    exists xbv_var. split. { eassumption. }
    econstructor.
    + eassumption.
    + eapply set_reg_get_in.
    + eassumption.
Qed.

Definition inputs_of_execution
  (input_vars : list Verilog.variable)
  (e : execution) :
  option (list {n : N & XBV.xbv n}) :=
  List.mapT_list (fun var => match e var with
                          | Some xbv => Some (_; xbv)
                          | None => None
                          end) input_vars.

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

(* TODO: StrFunMap.gsi *)

Lemma exec_statement_reads_has_values_before r1 r2 stmt :
  exec_statement r1 stmt = Some r2 ->
  List.Forall (fun n => exists v, r1 n = v) (Verilog.statement_reads stmt).
Proof.
  rewrite List.Forall_forall.
  eapply exec_statement_elim
    with
    (P := fun regs stmt result =>
            result = Some r2 ->
            forall x, List.In x (Verilog.statement_reads stmt) ->
                 exists v, r1 x = v)
    (P0 := fun regs stmts result =>
             result = Some r2 ->
             forall x, List.In x (Verilog.statement_reads_lst stmts) ->
                  exists v, r1 x = v);
    crush.
Qed.

Lemma exec_statement_preserve stmt : forall r1 r2 var,
  exec_statement r1 stmt = Some r2 ->
  (~ List.In var (Verilog.statement_writes stmt)) ->
  r1 var = r2 var.
Proof.
  intros *. revert r2.
  eapply exec_statement_elim with
    (P0 :=
       fun r stmts out => forall r2,
           out = Some r2 ->
           ~ List.In var (Verilog.statement_writes_lst stmts) ->
           r var = r2 var
    ); intros; try discriminate;
    simp statement_writes expr_reads in *;
    try rewrite List.in_app_iff in *;
    monad_inv.
  - rewrite set_reg_get_out; crush.
  - crush.
  - crush.
  - crush.
  - crush.
  - repeat
       multimatch goal with
       | [ H: forall _, _ |- _ ] => insterU H
       end;
    congruence.
Qed.

Lemma exec_module_item_preserve mi : forall r1 r2 var,
  exec_module_item r1 mi = Some r2 ->
  (~ List.In var (Verilog.module_item_writes mi)) ->
  r1 var = r2 var.
Proof.
  intros.
  funelim (exec_module_item r1 mi); simp exec_module_item in *; try discriminate; [idtac].
  eapply exec_statement_preserve; eauto.
Qed.

Lemma run_multistep_preserve procs : forall r1 r2 var,
  run_multistep
    {| regState := r1; pendingProcesses := procs |} =
    Some {| regState := r2; pendingProcesses := [] |} ->
  (~ List.In var (Verilog.module_body_writes procs)) ->
  r1 var = r2 var.
Proof.
  induction procs; intros * Hrun Hin; simp run_multistep in *.
  - inv Hrun. reflexivity.
  - simp module_body_writes in *. rewrite List.in_app_iff in *.
    monad_inv.
    transitivity (r var).
    + eapply exec_module_item_preserve; eauto.
    + eapply IHprocs; eauto.
Qed.

Lemma transfer_module_item_inputs tag m inputs outputs mi t :
  transfer_module_item tag m inputs outputs mi = inr t ->
  List.Forall (fun var => List.In var inputs) (Verilog.module_item_reads mi).
Proof.
  funelim (transfer_module_item tag m inputs outputs mi); intros; try discriminate.
  monad_inv.
  simp module_item_reads.
Qed.

Lemma transfer_module_item_outputs tag m inputs outputs mi t :
  transfer_module_item tag m inputs outputs mi = inr t ->
  List.Forall (fun var => List.In var outputs) (Verilog.module_item_writes mi).
Proof.
  funelim (transfer_module_item tag m inputs outputs mi); intros; try discriminate.
  monad_inv.
  simp module_item_writes statement_writes expr_reads.
  eauto with datatypes.
Qed.

Lemma transfer_module_body_outputs tag m inputs outputs mis t :
  transfer_module_body tag m inputs outputs mis = inr t ->
  List.Forall (fun var => List.In var outputs) (Verilog.module_body_writes mis).
Proof.
  funelim (transfer_module_body tag m inputs outputs mis); intros; try discriminate.
  - inv H. simp module_body_writes. constructor.
  - monad_inv.
    simp module_body_writes in *.
    eapply List.Forall_app.
    eauto using transfer_module_item_outputs with datatypes.
Qed.

Lemma transfer_module_body_inputs tag m inputs outputs mis t :
  transfer_module_body tag m inputs outputs mis = inr t ->
  List.Forall (fun var => List.In var inputs) (Verilog.module_body_reads mis).
Proof.
  funelim (transfer_module_body tag m inputs inputs mis); intros; try discriminate.
  - inv H. simp module_body_reads. constructor.
  - simp transfer_module_body module_body_reads in *.
    monad_inv.
    eapply List.Forall_app.
    eauto using transfer_module_item_inputs with datatypes.
Qed.

Lemma transfer_module_body_run_multistep_satisfiable v :
  forall tag (m : VerilogSMTBijection.t) r1 r2 q ρ,
    disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
    transfer_module_body tag m (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
    run_multistep {| regState := r1; pendingProcesses := Verilog.modBody v |} =
      Some {| regState := r2; pendingProcesses := [] |} ->
    verilog_smt_match_states_partial
      (fun var => List.In var (Verilog.module_body_reads (Verilog.modBody v) ++ Verilog.module_body_writes (Verilog.modBody v)))
      tag m r2 ρ ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q.
Proof.
  generalize dependent (Verilog.module_outputs v). intro outputs.
  generalize dependent (Verilog.module_inputs v). intro inputs.
  generalize dependent (Verilog.modBody v). intro body.
  induction body; intros * Hdisjoint Htransfer Hvalid Hmatch; simp module_body_reads module_body_writes transfer_module_body in *; [some_inv; constructor|].
  simp run_multistep in Hvalid.
  monad_inv.
  constructor.
  - eapply module_item_to_smt_satisfiable with (inputs := inputs).
    + eassumption.
    + eassumption.
    + eassumption.
    + eapply verilog_smt_match_states_partial_change_regs with (r1 := r2). {
        intros.
        rewrite ! List.in_app_iff in *.
        pose proof transfer_module_item_inputs as Hinputs. insterU Hinputs.
        pose proof transfer_module_item_outputs as Houtputs. insterU Houtputs.
        rewrite List.Forall_forall in *.
        symmetry. eapply run_multistep_preserve. eassumption.
        intro Hinbody.
        destruct H.
        - eapply disjoint_l_intro with (l:=inputs); eauto; [idtac].
          pose proof transfer_module_body_outputs as Hbody_outputs.
          insterU Hbody_outputs. rewrite List.Forall_forall in Hbody_outputs.
          auto.
        - eapply disjoint_l_intro; eauto.
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

Lemma execution_match_on_impl C1 C2 e1 e2:
  (forall var, C2 var -> C1 var) ->
  execution_match_on C1 e1 e2 ->
  execution_match_on C2 e1 e2.
Proof. unfold execution_match_on. crush. Qed.

Lemma transfer_module_body_satisfiable v :
  forall tag (m : VerilogSMTBijection.t) ρ q,
    disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
    transfer_module_body tag m (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
    valid_execution v (SMT.execution_of_valuation tag m ρ) ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q.
Proof.
  intros * Hdisjoint Htransfer Hvalid.
  destruct Hvalid as [e' [? ?]].
  eapply transfer_module_body_run_multistep_satisfiable; eauto; [idtac].
  apply execution_match_on_verilog_smt_match_states_partial.
  eapply execution_match_on_impl; [|eassumption].
  simpl. setoid_rewrite List.in_app_iff.
  intuition eauto.
  apply transfer_module_body_inputs in Htransfer.
  rewrite List.Forall_forall in Htransfer.
  auto.
Qed.

Lemma transfer_module_body_run_multistep_valid v : forall tag m ρ q,
    disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
    transfer_module_body tag m (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
    List.Forall (SMTQueries.term_satisfied_by ρ) q ->
    forall r1,
      verilog_smt_match_states_partial
        (fun var => List.In var (Verilog.module_inputs v))
        tag m r1 ρ ->
      exists r2,
        run_multistep {| regState := r1; pendingProcesses := Verilog.modBody v |} =
          Some {| regState := r2; pendingProcesses := [] |} /\
          verilog_smt_match_states_partial
            (fun var =>
               List.In var (Verilog.module_inputs v ++
                              Verilog.module_body_writes (Verilog.modBody v))
            ) tag m r2 ρ.
Proof.
  generalize dependent (Verilog.module_outputs v). intro outputs.
  generalize dependent (Verilog.module_inputs v). intro inputs.
  generalize dependent (Verilog.modBody v). intro body.
  clear v.
  induction body; intros * Hdisjoint Htransfer Hsat * Hmatch1;
    simpl in *;
    simp module_body_reads module_body_writes transfer_module_body run_multistep in *;
    autorewrite with list;
    [crush|].
  monad_inv. inv Hsat.
  edestruct module_item_to_smt_valid with (inputs := inputs) as [r_mid [Heval_mid Hmatch_mid]]; try eauto; [|]. {
    eapply verilog_smt_match_states_partial_impl; [|eassumption].
    simpl. intros.
    unfold list_subset in l.
    rewrite List.Forall_forall in l.
    auto.
  }
  rewrite Heval_mid. simpl.
  edestruct IHbody with (r1 := r_mid) as [r2 [Heval2 Hmatch2]]; try eassumption. {
    eapply verilog_smt_match_states_partial_change_regs. {
      intros. eapply exec_module_item_preserve; [eassumption|].
      intro.
      pose proof transfer_module_item_outputs as Houtputs. insterU Houtputs.
      pose proof transfer_module_body_inputs as Hinputs. insterU Hinputs.
      rewrite List.Forall_forall in *.
      eapply disjoint_l_intro with (l:=inputs); eauto.
    }
    eapply verilog_smt_match_states_partial_impl; [|eassumption]. {
      simpl. intros.
      assumption.
    }
  }
  exists r2.
  split. eassumption.
  eapply verilog_smt_match_states_partial_split; cycle 1.
  - eapply verilog_smt_match_states_partial_change_regs; [|eapply Hmatch_mid].
    intros.
    rewrite ! List.in_app_iff in *.
    pose proof transfer_module_item_inputs as Hinputs. insterU Hinputs.
    pose proof transfer_module_item_outputs as Houtputs. insterU Houtputs.
    rewrite List.Forall_forall in *.
    eapply run_multistep_preserve. eassumption.
    intro Hinbody.
    destruct H.
    + eapply disjoint_l_intro with (l:=inputs); eauto; [idtac].
      pose proof transfer_module_body_outputs as Hbody_outputs.
      insterU Hbody_outputs. rewrite List.Forall_forall in Hbody_outputs.
      auto.
    + eapply disjoint_l_intro; eauto.
  - eapply Hmatch2.
  - repeat setoid_rewrite List.in_app_iff. intros.
    intuition assumption.
Qed.

Lemma transfer_module_body_valid tag m v ρ q :
  list_subset (Verilog.module_body_reads (Verilog.modBody v)) (Verilog.module_inputs v) ->
  disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
  transfer_module_body tag m (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
  (forall var : Verilog.variable, List.In var (Verilog.module_inputs v) -> valuation_has_var tag m ρ var) ->
  List.Forall (SMTQueries.term_satisfied_by ρ) q ->
  valid_execution v (SMT.execution_of_valuation tag m ρ).
Proof.
  intros * Hsubset Hdisjoint Htransfer Hhas_vars Hsat.
  edestruct transfer_module_body_run_multistep_valid
    with (r1 := limit_to_regs (Verilog.module_inputs v) (SMT.execution_of_valuation tag m ρ))
    as [final [H1 H2]].
  - eassumption.
  - eassumption.
  - eassumption.
  - eapply verilog_smt_match_states_partial_change_regs
      with (r1 := SMT.execution_of_valuation tag m ρ). {
      intros.
      unfold list_subset in Hsubset.
      rewrite List.Forall_forall in Hsubset.
      unfold limit_to_regs.
      autodestruct; crush.
    }
    apply verilog_smt_match_states_execution_of_valuation_same.
    assumption.
  - unfold valid_execution.
    eexists. split; [eassumption|].
    apply verilog_smt_match_states_partial_execution_match_on.
    eapply verilog_smt_match_states_partial_impl; [|eassumption].
    simpl. setoid_rewrite List.in_app_iff.
    intuition eauto.
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

Lemma declarations_satisfied_valuation_has_var tag m start var vars ρ :
  List.Forall
    (fun '(n, s) => exists v : SMTLib.value, ρ n = Some v /\ SMTQueries.value_has_sort v s)
    (mk_declarations (assign_vars start vars)) ->
  mk_bijection tag (assign_vars start vars) = inr m ->
  List.In var vars ->
  valuation_has_var tag m ρ var.
Proof.
  intros H Hbijection Hin.
  rewrite <- assign_vars_vars with (start:=start) in Hin.
  generalize dependent (assign_vars start vars).
  clear vars.
  intro assignments. intros.

  unfold mk_declarations in H.
  rewrite List.Forall_map, List.Forall_forall in H.

  rewrite List.in_map_iff in Hin.
  destruct Hin as [[var' smtName] [Heq Hin]].
  simpl in Heq. subst var'.

  specialize (H (var, smtName) ltac:(assumption)).
  simpl in H. destruct H as [v [Hv Hhas_sort]].

  inv Hhas_sort.
  unfold valuation_has_var.
  exists smtName, bv. split; [|eassumption].

  eauto using mk_bijection_lookup.
Qed.

Import EqNotations.

Lemma execution_of_valuation_inv tag m ρ var xbv :
  SMT.execution_of_valuation tag m ρ var = Some xbv ->
  exists smtName bv,
    m (tag, var) = Some smtName /\
      XBV.to_bv xbv = Some bv /\
      ρ smtName = Some (SMTLib.Value_BitVec (Verilog.varType var) bv).
Proof.
  unfold SMT.execution_of_valuation.
  intros H.
  autodestruct_eqn E.
  simpl.
  rewrite XBV.xbv_bv_inverse.
  eauto.
Qed.

Lemma complete_execution_valuation_satisfied_declarations tag m v ρ start :
  mk_bijection tag (assign_vars start (Verilog.modVariables v)) = inr m ->
  complete_execution v (SMT.execution_of_valuation tag m ρ) ->
  List.Forall
    (fun '(n, s) => exists v0 : SMTLib.value, ρ n = Some v0 /\ SMTQueries.value_has_sort v0 s)
    (mk_declarations (assign_vars start (Verilog.modVariables v))).
Proof.
  unfold mk_declarations.
  rewrite Lists.List.Forall_map.
  rewrite List.Forall_forall.
  unfold complete_execution.
  intros Hbijection H [var smtName] Hin.
  assert (List.In var (Verilog.modVariables v)) as Hin2. {
    replace var with (fst (var, smtName)) by reflexivity.
    erewrite <- assign_vars_vars with (start:=start).
    apply List.in_map.
    assumption.
  }
  apply H in Hin2.
  destruct Hin2 as [xbv Hlookup].
  apply execution_of_valuation_inv in Hlookup.
  destruct Hlookup as [smtName' [bv Hlookup]].
  decompose record Hlookup. clear Hlookup.
  assert (m (tag, var) = Some smtName)
    by eauto using mk_bijection_lookup.
  replace smtName' with smtName in * by congruence.
  eexists. split; [eassumption|constructor].
Qed.

Lemma valid_execution_inputs_have_value v e var :
  valid_execution v e ->
  List.In var (Verilog.module_inputs v) ->
  exists xbv, e var = Some xbv.
Proof.
  unfold valid_execution.
  intros [e' [Hrun Hmatch]] Hin.
  unfold execution_match_on in Hmatch.
  setoid_rewrite List.in_app_iff in Hmatch.
  edestruct Hmatch as [xbv [He' He]]; eauto.
Qed.

Lemma valid_execution_writes_have_value v e var :
  valid_execution v e ->
  List.In var (Verilog.module_body_writes (Verilog.modBody v)) ->
  exists xbv, e var = Some xbv.
Proof.
  unfold valid_execution.
  intros [e' [Hrun Hmatch]] Hin.
  unfold execution_match_on in Hmatch.
  setoid_rewrite List.in_app_iff in Hmatch.
  edestruct Hmatch as [xbv [He' He]]; eauto.
Qed.

Lemma valid_execution_complete v : forall e,
    all_vars_driven v ->
    valid_execution v e ->
    complete_execution v e.
Proof.
  unfold all_vars_driven, complete_execution.
  induction (Verilog.modVariables v); [crush|].
  intros * Hdriven Hvalid * Hin.
  inv Hdriven.
  inv Hin; [|solve [auto]].
  clear IHl.
  destruct H1.
  - eauto using valid_execution_inputs_have_value.
  - eauto using valid_execution_writes_have_value.
Qed.

Lemma verilog_to_smt_has_vars tag start v smt ρ :
  verilog_to_smt tag start v = inr smt ->
  SMTQueries.satisfied_by ρ (SMT.query smt) ->
  forall var : Verilog.variable,
    List.In var (Verilog.modVariables v) ->
    valuation_has_var tag (SMT.nameMap smt) ρ var.
Proof.
  intros Hfunc Hsat var Hin.
  unfold verilog_to_smt in Hfunc.
  monad_inv. simpl in *.
  eapply declarations_satisfied_valuation_has_var.
  + inv Hsat. eassumption.
  + eauto using mk_bijection_smt_map_match.
  + assumption.
Qed.

Theorem verilog_to_smt_correct tag start v smt :
  verilog_to_smt tag start v = inr smt ->
  SMTQueries.smt_reflect
    (SMT.query smt)
    (fun ρ => valid_execution v (SMT.execution_of_valuation tag (SMT.nameMap smt) ρ)).
Proof.
  intros H ρ _.
  split.
  - intros Hsat.
    pose proof (verilog_to_smt_has_vars _ _ _ _ _ H Hsat) as Hhas_vars.
    unfold verilog_to_smt in H. monad_inv. simpl in *.
    eapply transfer_module_body_valid; try (some_inv; eassumption); [].
    intros var Hvar_in.
    unfold list_subset in *. rewrite List.Forall_forall in *.
    apply Hhas_vars.
    apply Verilog.module_input_in_vars.
    assumption.
  - intros Hvalid.
    unfold verilog_to_smt in H. monad_inv. simpl in *.
    unfold SMTQueries.satisfied_by. simpl.
    split.
    + eapply complete_execution_valuation_satisfied_declarations.
      * eassumption.
      * apply valid_execution_complete; eassumption.
    + eapply transfer_module_body_satisfiable; eassumption.
Qed.

Print Assumptions verilog_to_smt_correct.

Lemma defined_value_for_impl C1 C2 e :
  (forall var, C2 var -> C1 var) ->
  defined_value_for C1 e ->
  defined_value_for C2 e.
Proof. unfold defined_value_for. firstorder. Qed.

Lemma defined_value_for_set_reg C var xbv regs :
  defined_value_for C regs ->
  ~ XBV.has_x xbv ->
  defined_value_for C (set_reg var xbv regs).
Proof.
  unfold defined_value_for.
  intros Hno_exes Hno_x var' HC.
  destruct (dec (var' = var)).
  - subst var'.
    rewrite set_reg_get_in.
    eauto.
  - rewrite set_reg_get_out by crush.
    auto.
Qed.

Definition defined_value_for_all := defined_value_for (fun _ => True).

Lemma exec_module_item_no_exes C tag m t regs inputs outputs mi : forall regs',
    transfer_module_item tag m inputs outputs mi = inr t ->
    exec_module_item regs mi = Some regs' ->
    defined_value_for (fun var => C var \/ List.In var (Verilog.module_item_reads mi)) regs ->
    defined_value_for (fun var => C var \/ List.In var (Verilog.module_item_reads mi) \/ List.In var (Verilog.module_item_writes mi)) regs'.
Proof.
  funelim (transfer_module_item tag m inputs outputs mi);
    simp
      transfer_module_item
      exec_module_item
      exec_statement
      module_item_reads
      statement_reads
      expr_reads;
    intros; try discriminate; [].
  monad_inv.
  simp module_item_writes statement_writes expr_reads. simpl.
  unfold defined_value_for.
  intros var' Hvar_in'.
  destruct (dec (var' = var)).
  - subst.
    rewrite set_reg_get_in.
    eexists. split; [reflexivity|].
    apply XBV.not_has_x_to_bv.
    eapply eval_expr_no_exes; cycle 1; try eassumption.
    eapply defined_value_for_impl; cycle 1; [eassumption|firstorder].
  - assert (C var' \/ List.In var' (Verilog.expr_reads rhs)) by crush. clear Hvar_in'.
    rewrite set_reg_get_out by congruence.
    eauto.
Qed.

Lemma run_multistep_no_exes body : forall C tag m inputs outputs t regs regs',
  transfer_module_body tag m inputs outputs body = inr t ->
  run_multistep (MkVerilogState regs body) = Some (MkVerilogState regs' []) ->
  defined_value_for
    (fun var => C var
             \/ List.In var (Verilog.module_body_reads body))
    regs ->
  defined_value_for
    (fun var => C var
             \/ List.In var (Verilog.module_body_writes body)
             \/ List.In var (Verilog.module_body_reads body))
    regs'.
Proof.
  induction body;
    simpl in *; intros * Htransfer Hrun Hdefined.
  - simp run_multistep transfer_module_body module_body_reads in *.
    inv Hrun. intros var Hvar_in.
    simp module_body_writes in *. crush.
  - (* FIXME: simp tactic just hangs here *)
    autorewrite
      with transfer_module_body
           run_multistep
           module_body_reads
      in *.
    monad_inv.
    simp module_body_writes.
    setoid_rewrite List.in_app_iff.
    rewrite <- ! defined_value_for_split_iff.
    unpack_defined_value_for.
    pose proof (exec_module_item_no_exes
                  (fun v => C v
                         \/ List.In v (Verilog.module_body_reads body)))
      as Ha.
    specialize (IHbody (fun var => C var
                                \/ List.In var (Verilog.module_item_reads a)
                                \/ List.In var (Verilog.module_item_writes a))).
    simpl in *.
    unpack_defined_value_for.
    insterU Ha. unpack_defined_value_for.
    insterU IHbody. simpl in IHbody.
    unpack_defined_value_for.
    repeat split; assumption.
Qed.

Lemma defined_value_for_execution_match_on C e' e :
  execution_match_on C e' e ->
  defined_value_for C e' ->
  defined_value_for C e.
Proof.
  unfold execution_match_on, defined_value_for.
  intros Hmatch Hdefined var HC.
  insterU Hmatch. insterU Hdefined.
  destruct Hmatch as [xbv [? ?]].
  destruct Hdefined as [xbv' [? ?]].
  replace xbv' with xbv in * by congruence.
  eauto.
Qed.

(* Move me to semantics *)
Lemma valid_execution_no_exes_written v : forall e tag start q,
    verilog_to_smt tag start v = inr q ->
    valid_execution v e ->
    defined_value_for (fun var => List.In var (Verilog.module_inputs v)) e ->
    defined_value_for (fun var => List.In var (Verilog.module_body_writes (Verilog.modBody v))) e.
Proof.
  unfold valid_execution, all_vars_driven.
  intros * Htransf [e' [Hrun Hmatch]] Hinputs_defined.
  unfold verilog_to_smt in Htransf. monad_inv.
  unfold list_subset in *. rewrite List.Forall_forall in *.
  assert
    (defined_value_for
       (fun var : Verilog.variable =>
          List.In var (Verilog.module_inputs v)
          \/ List.In var (Verilog.module_body_reads (Verilog.modBody v)))
       (limit_to_regs (Verilog.module_inputs v) e)) as Hdefined_initial. {
    unfold limit_to_regs, defined_value_for.
    intros var [|]; autodestruct; crush.
  }
  pose proof (run_multistep_no_exes
                (Verilog.modBody v)
                (fun var => List.In var (Verilog.module_inputs v))) as H.
  simpl in *.
  insterU H.
  setoid_rewrite List.in_app_iff in Hmatch.
  eapply defined_value_for_impl; cycle 1.
  - eapply defined_value_for_execution_match_on; [eassumption|].
    eapply defined_value_for_impl; [|eassumption].
    intros var [Hvar_in | Hvar_in]; crush.
  - crush.
Qed.
