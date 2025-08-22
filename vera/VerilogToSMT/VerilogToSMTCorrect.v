From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import VerilogToSMT.
From vera Require Import SMT.
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
Import MonadNotation.
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

Lemma mk_bijection_smt_map_match tag start v m :
  mk_bijection tag (assign_vars start (Verilog.modVariables v)) = inr m ->
  SMT.match_map_verilog tag m v.
Proof.
  Opaque VerilogSMTBijection.lookup_left.
  unfold SMT.match_map_verilog.
  generalize (Verilog.modVariables v). clear v. intro vars.
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
  SMT.match_map_verilog tag (SMT.nameMap smt) v.
Proof.
  intros.
  unfold verilog_to_smt in *. simpl in *.
  autodestruct_eqn E. cbn.
  eauto using mk_bijection_smt_map_match.
Qed.

Lemma mk_bijection_only_tag tag vars m :
  mk_bijection tag vars = inr m ->
  VerilogSMTBijection.only_tag tag m.
Proof.
  revert m.
  funelim (mk_bijection tag vars); intros.
  - inv H. apply VerilogSMTBijection.only_tag_empty.
  - simp mk_bijection in H0; inv H0; autodestruct.
    eauto using VerilogSMTBijection.only_tag_insert.
Qed.

Lemma verilog_to_smt_only_tag tag start v s :
  verilog_to_smt tag start v = inr s ->
  VerilogSMTBijection.only_tag tag (SMT.nameMap s).
Proof.
  intros.
  unfold verilog_to_smt in *. simpl in *.
  autodestruct_eqn E. cbn.
  eauto using mk_bijection_only_tag.
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
    SMTLib.term_satisfied_by ρ t.
Proof.
  funelim (transfer_module_item tag m inputs outputs mi); intros; monad_inv; [idtac].
  simp exec_module_item exec_statement in *.
  monad_inv.
  unfold SMTLib.satisfied_by, SMTLib.term_satisfied_by. repeat constructor.
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

  erewrite FIXME_expr_to_smt_value with (expr := rhs) (regs := regs); eauto; cycle 1. {
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
  SMTLib.term_satisfied_by ρ (SMTLib.Term_Eq l r) <->
    (exists v,
        SMTLib.interp_term ρ l = Some v /\
        SMTLib.interp_term ρ r = Some v).
Proof.
  unfold SMTLib.term_satisfied_by.
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
    SMTLib.term_satisfied_by ρ t ->
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
    SMTLib.satisfied_by ρ q.
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

Lemma transfer_module_body_satisfiable v :
  forall tag (m : VerilogSMTBijection.t) e q,
    disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
    transfer_module_body tag m (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
    valid_execution v e ->
    SMTLib.satisfied_by (SMT.valuation_of_execution m e) q.
Proof.
  intros * Hdisjoint Htransfer Hvalid.
  inv Hvalid.
  eapply transfer_module_body_run_multistep_satisfiable; eauto using verilog_smt_match_states_valuation_of_execution_same.
Qed.

Lemma transfer_module_body_run_multistep_valid v : forall tag m ρ q,
    disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
    transfer_module_body tag m (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
    SMTLib.satisfied_by ρ q ->
    forall r1,
      verilog_smt_match_states_partial
        (fun var => List.In var (Verilog.module_body_reads (Verilog.modBody v)))
        tag m r1 ρ ->
      exists r2,
        run_multistep {| regState := r1; pendingProcesses := Verilog.modBody v |} =
          Some {| regState := r2; pendingProcesses := [] |} /\
          verilog_smt_match_states_partial
            (fun var =>
               List.In var (Verilog.module_body_reads (Verilog.modBody v) ++
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
    [crush|].
  monad_inv. inv Hsat.
  edestruct module_item_to_smt_valid with (inputs := inputs) as [r_mid [Heval_mid Hmatch_mid]]; try eauto; [|]. {
    eapply verilog_smt_match_states_partial_impl; [|eassumption].
    simpl. intros.
    eapply List.in_app_iff. crush.
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
      apply List.in_app_iff.
      auto.
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

Lemma FAKE_verilog_smt_match_states_partial_valid_execution v tag m final ρ :
  verilog_smt_match_states_partial
         (fun var : Verilog.variable =>
          List.In var
            (Verilog.module_body_reads (Verilog.modBody v) ++ Verilog.module_body_writes (Verilog.modBody v)))
         tag m final ρ ->
  valid_execution v (SMT.execution_of_valuation tag m ρ).
Proof. Admitted.

Lemma FAKE_body_reads_inputs_same v :
  Verilog.module_body_reads (Verilog.modBody v) = Verilog.module_inputs v.
Proof. Admitted.

Lemma FAKE_body_writes_outputs_same v :
  Verilog.module_body_reads (Verilog.modBody v) = Verilog.module_inputs v.
Proof. Admitted.

Lemma transfer_module_body_valid tag m v ρ q :
  disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
  transfer_module_body tag m (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
  SMTLib.satisfied_by ρ q ->
  valid_execution v (SMT.execution_of_valuation tag m ρ).
Proof.
  intros * Hdisjoint Htransfer_body Hsat.
  edestruct transfer_module_body_run_multistep_valid
    with (r1 := limit_to_regs (Verilog.module_inputs v) (SMT.execution_of_valuation tag m ρ))
    as [final [H1 H2]].
  - eassumption.
  - eassumption.
  - eassumption.
  - rewrite FAKE_body_reads_inputs_same.
    eapply verilog_smt_match_states_partial_change_regs
      with (r1 := SMT.execution_of_valuation tag m ρ). {
      intros.
      unfold limit_to_regs.
      now autodestruct.
    }
    apply verilog_smt_match_states_execution_of_valuation_same.
  - eapply FAKE_verilog_smt_match_states_partial_valid_execution.
    eassumption.
Qed.

Lemma valuation_of_execution_of_valuation m tag ρ :
  SMT.valuation_of_execution m (SMT.execution_of_valuation tag m ρ) = ρ.
Proof. Admitted.

Lemma transfer_module_body_correct v :
  forall tag (m : VerilogSMTBijection.t) q,
    disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
    transfer_module_body tag m (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
    SMTLibFacts.smt_reflect q (fun ρ => valid_execution v (SMT.execution_of_valuation tag m ρ)).
Proof.
  intros * Hdisjoint Htransfer_body.
  split; intro.
  - eapply transfer_module_body_valid; eassumption.
  - replace ρ with (SMT.valuation_of_execution m (SMT.execution_of_valuation tag m ρ))
      by apply valuation_of_execution_of_valuation.
    eapply transfer_module_body_satisfiable; eassumption.
Qed.

Theorem verilog_to_smt_correct tag start v smt :
  verilog_to_smt tag start v = inr smt ->
  SMTLibFacts.smt_reflect
    (SMT.query smt)
    (fun ρ => valid_execution v (SMT.execution_of_valuation tag (SMT.nameMap smt) ρ)).
Proof.
  unfold verilog_to_smt.
  intros H.
  inv H. autodestruct_eqn E. cbn in *.
  eapply transfer_module_body_correct; try eassumption.
Qed.

Print Assumptions verilog_to_smt_correct.
Print Assumptions transfer_module_body_satisfiable.
Print Assumptions transfer_module_body_valid.
