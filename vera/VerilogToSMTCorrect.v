From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import VerilogToSMT.
From vera Require Import SMT.
From vera Require Import VerilogSemantics.
From vera Require Import Verilog.
Import CombinationalOnly.

From Coq Require List.

From Equations Require Import Equations.

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

Lemma mk_bijection_smt_map_match tag start v m :
  mk_bijection tag (assign_vars start (Verilog.modVariables v)) = inr m ->
  SMT.match_map_verilog tag m v.
Proof.
  Opaque VerilogSMTBijection.lookup_left.
  unfold SMT.match_map_verilog.
  replace (variable_names (Verilog.modVariables v)) with (variable_names (List.map fst (assign_vars start (Verilog.modVariables v))))
    by now rewrite assign_vars_vars.
  remember (assign_vars start (Verilog.modVariables v)) as assignment.
  epose proof (assign_vars_smtname_nodup _ _) as Hnodup;
    rewrite <- Heqassignment in Hnodup.
  clear v start Heqassignment.
  generalize dependent Hnodup.
  generalize dependent m.
  induction assignment; intros * ? Hbijection.
  - simp mk_bijection in *. inv Hbijection.
    split; intros H; cbn in *; solve_by_inverts 2%nat.
  - unfold variable_names.
    destruct a as [var smtName].
    simp mk_bijection in Hbijection; inv Hbijection; autodestruct.
    intros. split; intros H.
    + destruct H as [smtName' H].
      cbn.
      cbn in H.
      repeat match goal with
      | [ H: context[sumbool_rec _ _ _  (?d ?a ?b)] |- _ ] =>
          destruct (d a b); cbn in H; subst; try (congruence || contradiction)
      | [ |- context[sumbool_rec _ _ _  (?d ?a ?b)] ] =>
          destruct (d a b); cbn in H; subst; try (congruence || contradiction)
      end.
      * eauto.
      * right.
        unfold variable_names in IHassignment.
        eapply IHassignment.
        -- now inv Hnodup.
        -- reflexivity.
        -- eauto.
    + cbn.
      repeat match goal with
      | [ H: context[sumbool_rec _ _ _  (?d ?a ?b)] |- _ ] =>
          destruct (d a b); cbn in H; subst; try (congruence || contradiction)
      | [ |- context[sumbool_rec _ _ _  (?d ?a ?b)] ] =>
          destruct (d a b); cbn; subst; try (congruence || contradiction)
      end.
      * eauto.
      * inv Hnodup. inv H; eapply IHassignment; eauto.
        cbn in *. contradiction.
Qed.

Lemma verilog_to_smt_map_match tag start v smt :
  verilog_to_smt tag start v = inr smt ->
  SMT.match_map_verilog tag (SMT.nameMap smt) v.
Proof.
  intros.
  funelim (verilog_to_smt tag start v);
    simp verilog_to_smt in *;
    try rewrite Heq in *;
    simpl in *;
    try discriminate.
  autodestruct_eqn E. cbn.
  eauto using mk_bijection_smt_map_match.
Qed.


Theorem verilog_to_smt_correct tag start v smt :
  verilog_to_smt tag start v = inr smt ->
  SMTLibFacts.smt_reflect
    (SMT.query smt)
    (fun ρ => valid_execution v (SMT.execution_of_valuation tag (SMT.nameMap smt) ρ)).
Proof.
Admitted.

Lemma verilog_to_smt_only_tag t n v s :
  verilog_to_smt t n v = inr s ->
  VerilogSMTBijection.only_tag t (SMT.nameMap s).
Admitted.
