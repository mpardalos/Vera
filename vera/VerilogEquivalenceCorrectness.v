From vera Require Import Verilog.
From vera Require Import SMT.
Import (coercions) SMT.
From vera Require Import Common.
Import (coercions) VerilogSMTBijection.
From vera Require Import Bitvector.
From vera Require VerilogTypecheck.
From vera Require VerilogCanonicalize.
From vera Require VerilogToSMT.
From vera Require VerilogToSMTCorrect.
From vera Require Import VerilogEquivalence.
From vera Require VerilogSemantics.
From vera Require Import Tactics.
From vera Require Import Decidable.

Import VerilogSemantics.CombinationalOnly.

From Coq Require Import Relations.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Lia.

From Equations Require Import Equations.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Data.Monads.OptionMonad.
From ExtLib Require Import Data.List.

Import MonadNotation.
Open Scope monad_scope.
Require Import ZArith.
Require Import String.

From Coq Require Import List.
Import ListNotations.
Import EqNotations.
Local Open Scope string.
Local Open Scope Z_scope.

Definition match_on_regs
  (regs : list string)
  (st1 st2 : RegisterState)
  : Prop :=
  List.Forall
    (fun 'n =>
       exists v, st1 n = Some v
            /\ st2 n = Some v
            /\ ~ XBV.has_x v
    ) regs.

Definition equivalent_behaviour v1 v2 :=
  forall (input : list XBV.t)
    (input_wf1 : input_valid v1 input)
    (input_wf2 : input_valid v2 input)
    (* (outputs_same : Verilog.outputs v1 = Verilog.outputs v2) *)
    (input_vals_defined : Forall (fun bv => ~ XBV.has_x bv) input)
    (final1 final2 : VerilogState),
    run_multistep (initial_state v1 input) = Some final1 ->
    run_multistep (initial_state v2 input) = Some final2 ->
    match_on_regs (Verilog.outputs v1) (regState final1) (regState final2).

Record equivalent (v1 v2 : Verilog.vmodule) : Prop :=
  MkEquivalent {
      interface_inputs_match : Verilog.inputs v1 = Verilog.inputs v2;
      interface_outputs_match : Verilog.outputs v1 = Verilog.outputs v2;
      no_errors1 : no_errors v1;
      no_errors2 : no_errors v2;
      behaviour_match : equivalent_behaviour v1 v2;
    }
.

Section V.
  Import Verilog.
  Definition assign_out : vmodule :=
    {|
      modName := "assign_out";
      modPorts := [
        MkPort PortIn "in";
        MkPort PortOut "out"
      ];
      modVariables := [
        MkVariable Verilog.Scalar Verilog.Wire "in";
        MkVariable Verilog.Scalar Verilog.Wire "out"
      ];
      modBody := [
        AlwaysComb (BlockingAssign (NamedExpression 1%N "out") (NamedExpression 1%N "in"))
      ];
    |}.

  Definition assign_out_twostep : vmodule :=
    {|
      modName := "assign_out";
      modPorts := [
        MkPort PortIn "in";
        MkPort PortOut "out"
      ];
      modVariables := [
        MkVariable Verilog.Scalar Verilog.Wire "in";
        MkVariable Verilog.Scalar Verilog.Wire "v";
        MkVariable Verilog.Scalar Verilog.Wire "out"
      ];
      modBody := [
        AlwaysComb (BlockingAssign (NamedExpression 1%N "out") (NamedExpression 1%N "v"));
        AlwaysComb (BlockingAssign (NamedExpression 1%N "v") (NamedExpression 1%N "in"))
      ];
    |}.

  Example assign_out_equivalent : equivalent assign_out assign_out.
  Proof.
    constructor; try auto.
    - unfold no_errors. intros.
      repeat (destruct input; try solve [simpl in *; discriminate]).
      eexists.
      repeat (unfold assign_out, set_reg, initial_state; simpl).
      repeat (try econstructor; try unfold step; simpl; try simp run_step run_multistep exec_module_item exec_statement).
    - unfold no_errors. intros.
      repeat (destruct input; try solve [simpl in *; discriminate]).
      eexists.
      repeat (unfold assign_out, set_reg, initial_state; simpl).
      repeat (try econstructor; try unfold step; simpl; try simp run_step run_multistep exec_module_item exec_statement).
    - unfold equivalent_behaviour.
      intros ? ? ? ? ? ? eval1 eval2.
      repeat (destruct input; try solve [simpl in *; discriminate]).
      unfold assign_out, set_reg in eval1; simpl in eval1.
      unfold assign_out, set_reg in eval2; simpl in eval2.
      repeat constructor.
      repeat (simp run_multistep run_step exec_module_item exec_statement eval_expr in *; simpl in * );
        unfold set_reg in *; simpl in *; try solve_by_inverts 3%nat.
      inv eval1.
      inv eval2.
      eexists. intuition.
      inv input_vals_defined. contradiction.
  Qed.
End V.

Lemma match_on_regs_trans :
  forall rs v1 v2 v3,
    match_on_regs rs v1 v2 ->
    match_on_regs rs v2 v3 ->
    match_on_regs rs v1 v3.
Proof.
  intro rs.
  induction rs; unfold match_on_regs.
  - constructor.
  - intros * H1 H2.
    rewrite Forall_forall in *.
    intros x Hin.
    destruct (H1 ltac:(assumption) ltac:(assumption)) as [val1 ?].
    destruct (H2 ltac:(assumption) ltac:(assumption)) as [val2 ?].
    exists val1.
    intuition congruence.
Qed.

Lemma match_on_regs_sym :
  forall rs v1 v2,
    match_on_regs rs v1 v2 ->
    match_on_regs rs v2 v1.
Proof.
  intro rs.
  induction rs; unfold match_on_regs.
  - constructor.
  - intros * H.
    rewrite Forall_forall in *.
    intros x Hin.
    destruct (H ltac:(assumption) ltac:(assumption)) as [val ?].
    exists val.
    intuition congruence.
Qed.

Lemma equivalent_trans v1 v2 v3 :
  equivalent v1 v2 ->
  equivalent v2 v3 ->
  equivalent v1 v3.
Proof.
  intros [interface_inputs_match1 interface_outputs_match1 no_errors1 no_errors2 behaviour_match1].
  intros [interface_inputs_match2 interface_outputs_match2 _ no_errors3 behaviour_match2].
  unfold equivalent_behaviour in *.
  constructor; unfold equivalent_behaviour in *; simpl in *.
  all: (try rewrite <- interface_inputs_match2 in *;
        try rewrite <- interface_inputs_match1 in *;
        try rewrite <- interface_outputs_match2 in *;
        try rewrite <- interface_outputs_match1 in *;
        simpl in *
       ).
  - congruence.
  - congruence.
  - assumption.
  - assumption.
  - intros ? ? input_wf3 ? ? final3 Hrun1 Hrun3.
    assert (input_valid v2 input) as input_wf2. {
      unfold input_valid in *.
      rewrite <- interface_inputs_match1.
      assumption.
    }
    specialize (behaviour_match1 input ltac:(assumption) ltac:(assumption)).
    specialize (behaviour_match2 input ltac:(assumption) ltac:(assumption)).
    assert (exists final', run_multistep (initial_state v2 input) = Some final') as H1. {
      unfold no_errors in *. eauto.
    }
    destruct H1.
    eapply match_on_regs_trans; eauto.
Qed.

Lemma equivalent_sym v1 v2 :
  equivalent v1 v2 ->
  equivalent v2 v1.
Proof.
  intros [interface_inputs_match1 interface_outputs_match1 no_errors1 no_errors2 behaviour_match1].
  constructor.
  - congruence.
  - congruence.
  - assumption.
  - assumption.
  - simpl in *. unfold equivalent_behaviour. intros.
    rewrite <- interface_outputs_match1 in *.
    apply match_on_regs_sym.
    eauto.
Qed.

Theorem canonicalize_correct v v' :
  VerilogCanonicalize.canonicalize_verilog v = inr v' ->
  equivalent v v'.
Admitted.

Lemma FIXME_no_errors v : no_errors v.
Admitted.

Remark FIXME_verilog_outputs_in_variables name v:
  In name (Verilog.outputs v) ->
  In name (variable_names (Verilog.modVariables v)).
Admitted.

(** This depends on typechecking pass (module does not write to its inputs) *)
Lemma run_multistep_preserve_initial_values v input final :
  input_valid v input ->
  run_multistep (initial_state v input) = Some final ->
  Forall (fun n => regState final n = regState (initial_state v input) n) (Verilog.inputs v).
Proof. Admitted.

Definition smt_same_value (var : string) (m : VerilogSMTBijection.t) (ρ : SMTLib.valuation) :=
  exists smtName1 smtName2 v,
    m (TaggedName.VerilogLeft, var) = Some smtName1 /\
      m (TaggedName.VerilogRight, var) = Some smtName2 /\
      ρ smtName1 = Some v /\
      ρ smtName2 = Some v.

Definition smt_all_same_values
  (vars : list string) (m : VerilogSMTBijection.t) (ρ : SMTLib.valuation) :=
  Forall (fun verilogName => smt_same_value verilogName m ρ) vars.

Definition smt_distinct_value (var : string) (m : VerilogSMTBijection.t) (ρ : SMTLib.valuation) :=
  exists smtName1 smtName2 v1 v2,
    m (TaggedName.VerilogLeft, var) = Some smtName1 /\
      m (TaggedName.VerilogRight, var) = Some smtName2 /\
      ρ smtName1 = Some v1 /\
      ρ smtName2 = Some v2 /\
      v1 <> v2.

Definition smt_has_value (tag : TaggedName.Tag) (var : string) (nameMap : VerilogSMTBijection.t) (ρ : SMTLib.valuation) :=
  exists smtName v, nameMap (tag, var) = Some smtName /\ ρ smtName = Some v.

Definition smt_all_have_values
  (tag : TaggedName.Tag) (vars : list string) (nameMap : VerilogSMTBijection.t) (ρ : SMTLib.valuation) :=
  Forall (fun verilogName => smt_has_value tag verilogName nameMap ρ) vars.

Definition smt_some_distinct_values
  (vars : list string) (m : VerilogSMTBijection.t) (ρ : SMTLib.valuation) :=
  Exists (fun verilogName => smt_distinct_value verilogName m ρ) vars.

Lemma mk_var_same_spec : forall name m q,
  mk_var_same name m = inr q ->
  SMTLibFacts.smt_reflect [q] (smt_same_value name m).
Proof.
  intros * Hfunc.
  funelim (mk_var_same name m); try congruence.
  (* destruct (size1 =? size2)%N eqn:Esize; try congruence. *)
  (* rewrite N.eqb_eq in Esize; subst. *)
  replace q with (SMTLib.Term_Eq (SMTLib.Term_Const smt_name1) (SMTLib.Term_Const smt_name2)) by congruence.
  unfold smt_same_value.
  split; intros * H.
  - inv H. inv H2.
    destruct (ρ smt_name1) eqn:E1 ; try discriminate.
    destruct (ρ smt_name2) eqn:E2 ; try discriminate.
    inv H0.
    rewrite SMTLib.value_eqb_eq in H1. subst.
    exists smt_name1. exists smt_name2. exists v0.
    rewrite E1. rewrite E2.
    intuition trivial.
  - repeat econstructor.
    destruct H as [smt_name1' [smt_name2' [w [v [H0 [H1 H2]]]]]].
    replace smt_name1' with smt_name1 in * by congruence.
    replace smt_name2' with smt_name2 in * by congruence.
    unfold SMTLib.term_satisfied_by. simpl.
    destruct (ρ smt_name1) eqn:E1; destruct (ρ smt_name2) eqn:E2; try discriminate.
    repeat match goal with
           | [ v1 : SMTLib.value, v2 : SMTLib.value, H : Some ?v1 = Some ?v2 |- _ ] =>
               inv H
           end.
    replace (SMTLib.value_eqb _ _) with true
      by (symmetry; now apply SMTLib.value_eqb_eq).
    reflexivity.
Qed.

(* TODO: Move me to smtcoqapi *)
Lemma smtlib_and_conj : forall (q1 q2 : SMTLib.term) (P1 P2 : SMTLib.valuation -> Prop),
    SMTLibFacts.smt_reflect [q1] P1 ->
    SMTLibFacts.smt_reflect [q2] P2 ->
    SMTLibFacts.smt_reflect [SMTLib.Term_And q1 q2] (fun ρ : SMTLib.valuation => P1 ρ /\ P2 ρ).
Proof.
  intros * H1 H2.
  split; intros H0.
  - unfold SMTLib.satisfied_by in H0.
    inv H0. inv H4.
    destruct (SMTLib.interp_term ρ q1) as [[ b1 | ? | ? ] | ] eqn:E1; try discriminate.
    destruct (SMTLib.interp_term ρ q2) as [[ b2 | ? | ? ] | ] eqn:E2; try discriminate.
    inv H0. apply andb_prop in H3. intuition; subst.
    + apply H1. repeat constructor. apply E1.
    + apply H2. repeat constructor. apply E2.
  - destruct H0 as [HP1 HP2].
    repeat econstructor.
    unfold SMTLib.term_satisfied_by. simpl.
    replace (SMTLib.interp_term ρ q1) with (Some (SMTLib.Value_Bool true)); cycle 1. {
      apply H1 in HP1. inv HP1. symmetry. assumption.
    }
    replace (SMTLib.interp_term ρ q2) with (Some (SMTLib.Value_Bool true)); cycle 1. {
      apply H2 in HP2. inv HP2. symmetry. assumption.
    }
    reflexivity.
Qed.
    
Lemma mk_inputs_same_spec : forall inputs m q,
  mk_inputs_same inputs m = inr q ->
  SMTLibFacts.smt_reflect [q] (smt_all_same_values inputs m).
Proof.
  intros ?. induction inputs.
  - intros. inv H. simp mk_inputs_same.
    unfold smt_all_same_values.
    eapply SMTLibFacts.smt_reflect_rewrite. {
      intros. apply Forall_nil_iff.
    }
    repeat constructor.
  - intros. simp mk_inputs_same in H.
    autodestruct_eqn E.
    unfold smt_all_same_values.
    eapply SMTLibFacts.smt_reflect_rewrite. {
      intros. apply Forall_cons_iff.
    }
    apply smtlib_and_conj.
    + apply mk_var_same_spec. apply E.
    + apply IHinputs. assumption.
Qed.

Definition smtlib_is_bool ρ q := exists b, SMTLib.interp_term ρ q = Some (SMTLib.Value_Bool b).

(* TODO: Move me to smtcoqapi *)
Lemma smtlib_or_disj : forall (q1 q2 : SMTLib.term) (P1 P2 : SMTLib.valuation -> Prop),
    SMTLibFacts.smt_reflect [q1] P1 ->
    SMTLibFacts.smt_reflect [q2] P2 ->
    SMTLibFacts.smt_reflect
      [SMTLib.Term_Or q1 q2]
      (fun ρ : SMTLib.valuation => (P1 ρ /\ smtlib_is_bool ρ q2) \/ (smtlib_is_bool ρ q1 /\ P2 ρ)).
Proof.
  intros * H1 H2.
  split; intros H0.
  - unfold SMTLib.satisfied_by in H0.
    inv H0. inv H4.
    destruct (SMTLib.interp_term ρ q1) as [[ b1 | ? | ? ] | ] eqn:E1; try discriminate.
    destruct (SMTLib.interp_term ρ q2) as [[ b2 | ? | ? ] | ] eqn:E2; try discriminate.
    unfold smtlib_is_bool.
    inv H0. apply Bool.orb_prop in H3. intuition (subst; eauto).
    + left. intuition eauto. 
      apply H1. repeat constructor. apply E1.
    + right. intuition eauto.
      apply H2. repeat constructor. apply E2.
  - repeat econstructor.
    unfold SMTLib.term_satisfied_by. simpl.
    (* destruct H0 as [[HP1 [b1 Hbool1]] | [HP2 [b2 Hbool2]]]. *)
    destruct H0 as [[HP1 [b2 Hbool2]] | [[b1 Hbool1] HP2]].
    + replace (SMTLib.interp_term ρ q1) with (Some (SMTLib.Value_Bool true)); cycle 1. {
        apply H1 in HP1. inv HP1. symmetry. assumption.
      }
      rewrite Hbool2.
      now rewrite Bool.orb_true_l.
    + replace (SMTLib.interp_term ρ q2) with (Some (SMTLib.Value_Bool true)); cycle 1. {
        apply H2 in HP2. inv HP2. symmetry. assumption.
      }
      rewrite Hbool1.
      now rewrite Bool.orb_true_r.
Qed.

(* TODO: Move me to smtcoqapi *)
Lemma value_eqb_neq v1 v2 : SMTLib.value_eqb v1 v2 = false <-> v1 <> v2.
Proof.
  split; intros H.
  - intros contra.
    apply SMTLib.value_eqb_eq in contra.
    congruence.
  - destruct (SMTLib.value_eqb v1 v2) eqn:E; try reflexivity.
    apply SMTLib.value_eqb_eq in E.
    contradiction.
Qed.

Lemma mk_var_distinct_spec : forall name m q,
  mk_var_distinct name m = inr q ->
  SMTLibFacts.smt_reflect [q] (smt_distinct_value name m).
Proof.
  intros * Hfunc.
  funelim (mk_var_distinct name m); try congruence.
  (* destruct (size1 =? size2)%N eqn:Esize; try congruence. *)
  (* rewrite N.eqb_eq in Esize; subst. *)
  replace q with (SMTLib.Term_Not (SMTLib.Term_Eq
                                     (SMTLib.Term_Const smt_name1)
                                     (SMTLib.Term_Const smt_name2)))
    by congruence.
  unfold smt_distinct_value.
  split; intros * H.
  - inv H. inv H2.
    destruct (ρ smt_name1) eqn:E1 ; try discriminate.
    destruct (ρ smt_name2) eqn:E2 ; try discriminate.
    inv H0.
    rewrite Bool.negb_true_iff in H1.
    rewrite value_eqb_neq in H1. subst.
    exists smt_name1. exists smt_name2. exists v. exists v0.
    rewrite E1. rewrite E2.
    intuition trivial.
  - repeat econstructor.
    destruct H as [smt_name1' [smt_name2' [w [v [v0 [H0 [H1 [H2 H3]]]]]]]].
    replace smt_name1' with smt_name1 in * by congruence.
    replace smt_name2' with smt_name2 in * by congruence.
    unfold SMTLib.term_satisfied_by. simpl.
    destruct (ρ smt_name1) eqn:E1; destruct (ρ smt_name2) eqn:E2; try discriminate.
    repeat match goal with
           | [ v1 : SMTLib.value, v2 : SMTLib.value, H : Some ?v1 = Some ?v2 |- _ ] =>
               inv H
           end.
    replace (SMTLib.value_eqb _ _) with false
      by (symmetry; now apply value_eqb_neq).
    reflexivity.
Qed.

Lemma smtlib_is_bool_or ρ t1 t2:
  smtlib_is_bool ρ t1 /\ smtlib_is_bool ρ t2 <-> smtlib_is_bool ρ (SMTLib.Term_Or t1 t2).
Proof.
  split.
  - intros * [[v1 H1] [v2 H2]].
    unfold smtlib_is_bool.
    simpl. rewrite H1. rewrite H2.
    eauto.
  - intros [v H]. simpl in H.
    autodestruct_eqn E.
    unfold smtlib_is_bool in *.
    eauto.
Qed.

Lemma mk_var_distinct_is_bool var : forall m t ρ,
    smt_has_value TaggedName.VerilogLeft var m ρ ->
    smt_has_value TaggedName.VerilogRight var m ρ ->
    mk_var_distinct var m = inr t ->
    smtlib_is_bool ρ t.
Proof.
  intros * Hval1 Hval2 H.
  funelim (mk_var_distinct var m); try congruence.
  match type of Heqcall with
  | inr ?t' = mk_var_distinct _ _  => replace t with t' in * by congruence
  end.
  unfold smtlib_is_bool. simpl.
  destruct Hval1 as [smt_name1' [v1 [? Hval1]]]. replace smt_name1' with smt_name1 in * by congruence.
  destruct Hval2 as [smt_name2' [v2 [? Hval2]]]. replace smt_name2' with smt_name2 in * by congruence.
  rewrite Hval1. rewrite Hval2.
  eauto.
Qed.

Lemma mk_var_distinct_has_value var : forall m tag t ρ,
    mk_var_distinct var m = inr t ->
    smtlib_is_bool ρ t ->
    smt_has_value tag var m ρ.
Proof.
  intros * Hdistinct Hisbool.
  funelim (mk_var_distinct var m); try congruence.
  match type of Heqcall with
  | inr ?t' = mk_var_distinct _ _  => replace t with t' in * by congruence
  end.
  unfold smtlib_is_bool in *. simpl in *.
  unfold smt_has_value.
  autodestruct_eqn E; try solve_by_inverts 2%nat.
  destruct tag; intuition eauto.
Qed.

Lemma mk_outputs_distinct_is_bool outputs : forall m t ρ,
    smt_all_have_values TaggedName.VerilogLeft outputs m ρ ->
    smt_all_have_values TaggedName.VerilogRight outputs m ρ ->
    mk_outputs_distinct outputs m = inr t ->
    smtlib_is_bool ρ t.
Proof.
  induction outputs; intros * Hval1 Hval2 H; simp mk_outputs_distinct in *.
  - inv H. repeat econstructor.
  - autodestruct_eqn E.
    inv Hval1. inv Hval2.
    fold (smt_all_have_values TaggedName.VerilogLeft outputs m ρ) in *.
    fold (smt_all_have_values TaggedName.VerilogRight outputs m ρ) in *.
    apply smtlib_is_bool_or.
    eauto using mk_var_distinct_is_bool.
Qed.

Lemma mk_outputs_distinct_have_values outputs : forall m tag t ρ,
    mk_outputs_distinct outputs m = inr t ->
    smtlib_is_bool ρ t ->
    smt_all_have_values tag outputs m ρ.
Proof.
  induction outputs; intros * Hdistinct Hisbool.
  - repeat econstructor.
  - simp mk_outputs_distinct in *.
    autodestruct_eqn E.
    constructor; fold (smt_all_have_values tag outputs m ρ) in *.
    + eapply mk_var_distinct_has_value. eassumption.
      apply smtlib_is_bool_or in Hisbool. intuition auto.
    + eapply IHoutputs. eassumption.
      apply smtlib_is_bool_or in Hisbool. intuition auto.
Qed.

Lemma smt_distinct_value_has_value tag var m ρ :
  smt_distinct_value var m ρ ->
  smt_has_value tag var m ρ.
Proof. destruct tag; firstorder. Qed.

Lemma mk_outputs_distinct_spec outputs m q:
  mk_outputs_distinct outputs m = inr q ->
  SMTLibFacts.smt_reflect [q] (fun ρ => smt_some_distinct_values outputs m ρ
                                     /\ smt_all_have_values TaggedName.VerilogLeft outputs m ρ
                                     /\ smt_all_have_values TaggedName.VerilogRight outputs m ρ).
Proof.
  revert q m. induction outputs.
  - intros. inv H. simp mk_outputs_distinct.
    unfold smt_some_distinct_values.
    eapply SMTLibFacts.smt_reflect_rewrite with (P2 := fun _ => False). {
      intuition (try eapply Exists_nil; eauto).
    }
    apply SMTLibFacts.unsat_smt_reflect_false.
    unfold SMTLib.unsatisfiable.
    intros * contra. inv contra. inv H1.
  - intros.
    simp mk_outputs_distinct in H.
    autodestruct_eqn E.
    specialize (IHoutputs _ _ ltac:(eassumption)).
    unfold smt_some_distinct_values.
    unshelve (epose proof
                (smtlib_or_disj t t0
                   (smt_distinct_value a m)
                   (fun ρ => smt_some_distinct_values outputs m ρ
                          /\ smt_all_have_values TaggedName.VerilogLeft  outputs m ρ
                          /\ smt_all_have_values TaggedName.VerilogRight outputs m ρ) _ _) as Hreflect).
    { auto using mk_var_distinct_spec. }
    { assumption. }
    eapply SMTLibFacts.smt_reflect_rewrite. 2: apply Hreflect.
    intros. simpl.
    unfold smt_all_have_values.
    rewrite Exists_cons.
    rewrite 2 Forall_cons_iff.
    fold (smt_all_have_values TaggedName.VerilogLeft  outputs m ρ) in *.
    fold (smt_all_have_values TaggedName.VerilogRight outputs m ρ) in *.
    fold (smt_some_distinct_values outputs m ρ) in *.
    intuition (eauto using mk_outputs_distinct_is_bool,
                mk_var_distinct_is_bool,
                smt_distinct_value_has_value,
                mk_outputs_distinct_have_values,
                mk_var_distinct_has_value).
Qed.

Definition counterexample_valuation v1 v2 m ρ :=
  valid_execution v1 (SMT.execution_of_valuation TaggedName.VerilogLeft m ρ)
  /\ valid_execution v2 (SMT.execution_of_valuation TaggedName.VerilogRight m ρ)
  /\ smt_all_same_values (Verilog.inputs v1) m ρ
  /\ smt_some_distinct_values (Verilog.outputs v1) m ρ
  /\ smt_all_have_values TaggedName.VerilogLeft (Verilog.outputs v1) m ρ
  /\ smt_all_have_values TaggedName.VerilogRight (Verilog.outputs v1) m ρ.

Definition execution_same_value (e1 e2 : execution) name :=
  exists v, e1 name = Some v /\ e2 name = Some v.

Definition execution_all_same_values e1 e2 names :=
  Forall (execution_same_value e1 e2) names.

Definition execution_distinct_value (e1 e2 : execution) name :=
  exists v1 v2, e1 name = Some v1 /\ e2 name = Some v2 /\ (XBV.has_x v1 \/ XBV.has_x v2 \/ v1 <> v2).

Definition execution_some_distinct_values e1 e2 names :=
  Exists (execution_distinct_value e1 e2) names.

Definition execution_has_value (e : execution) name :=
  exists v, e name = Some v.

Definition execution_all_have_values e names :=
  Forall (execution_has_value e) names.

Definition execution_not_x (e : execution) name :=
  forall v, e name = Some v -> ~ XBV.has_x v.

Definition execution_no_exes (e : execution) names :=
  Forall (execution_not_x e) names.

Definition counterexample_execution v1 e1 v2 e2 :=
  valid_execution v1 e1
  /\ valid_execution v2 e2
  /\ execution_all_same_values e1 e2 (Verilog.inputs v1)
  /\ execution_some_distinct_values e1 e2 (Verilog.outputs v1)
  /\ execution_all_have_values e1 (Verilog.outputs v1)
  /\ execution_all_have_values e2 (Verilog.outputs v1).

Definition only_bitvectors (ρ : SMTLib.valuation) :=
  forall n v, ρ n = Some v -> (exists w bv, v = SMTLib.Value_BitVec w bv).

Remark complete_execution_outputs_have_values e v :
  complete_execution v e ->
  execution_all_have_values e (Verilog.outputs v).
Proof.
  unfold complete_execution, execution_all_have_values.
  intros. apply Forall_forall. intros name Hname_in_outputs.
  apply FIXME_verilog_outputs_in_variables in Hname_in_outputs.
  firstorder.
Qed.

Remark valid_execution_outputs_have_values e v :
  valid_execution v e ->
  execution_all_have_values e (Verilog.outputs v).
Proof. eauto using valid_execution_complete, complete_execution_outputs_have_values. Qed.

Theorem all_same_values_execution_of_valuation names m ρ :
  only_bitvectors ρ ->
  smt_all_same_values names m ρ ->
  execution_all_same_values
    (SMT.execution_of_valuation TaggedName.VerilogLeft m ρ)
    (SMT.execution_of_valuation TaggedName.VerilogRight m ρ)
    names.
Proof.
  intro Honly_bv.
  unfold smt_all_same_values, execution_all_same_values in *.
  apply Forall_impl.
  unfold smt_same_value, execution_same_value.
  intros ? [smtName1 [smtName2 [v [? [? [? ?]]]]]].
  edestruct Honly_bv with (n := smtName1) as [w [bv Hbv]]; try eassumption; subst v.
  eexists. split.
  all: eauto using SMT.execution_of_valuation_some.
Qed.

Theorem some_distinct_values_execution_of_valuation names m ρ :
  only_bitvectors ρ ->
  smt_some_distinct_values names m ρ ->
  execution_some_distinct_values
    (SMT.execution_of_valuation TaggedName.VerilogLeft m ρ)
    (SMT.execution_of_valuation TaggedName.VerilogRight m ρ) names.
Proof.
  intros Honly_bv.
  unfold smt_some_distinct_values, execution_some_distinct_values in *.
  apply Exists_impl.
  unfold smt_distinct_value, execution_distinct_value.
  intros ? [smtName1 [smtName2 [v1 [v2 [H0 [H1 [H2 [H3 H4]]]]]]]].
  edestruct Honly_bv with (n := smtName1) as [w1 [bv1 Hbv1]]; try eassumption; subst v1.
  edestruct Honly_bv with (n := smtName2) as [w2 [bv2 Hbv2]]; try eassumption; subst v2.
  eexists. eexists.
  split. { eauto using SMT.execution_of_valuation_some. }
  split. { eauto using SMT.execution_of_valuation_some. }
  right. right.
  intro contra; contradict H4.
  apply XBV.from_bv_injective in contra.
  destruct bv1; destruct bv2. inv contra. simpl in *. now subst.
Qed.

Theorem all_have_values_execution_of_valuation tag names m ρ :
  only_bitvectors ρ ->
  smt_all_have_values tag names m ρ ->
  execution_all_have_values (SMT.execution_of_valuation tag m ρ) names.
Proof.
  intros Honly_bv.
  unfold smt_all_have_values, execution_all_have_values in *.
  apply Forall_impl.
  unfold smt_has_value, execution_has_value.
  intros ? [smtName [v [H0 H1]]].
  edestruct Honly_bv with (n := smtName) as [w [bv Hbv]]; try eassumption; subst v.
  eexists.
  eauto using SMT.execution_of_valuation_some.
Qed.

Theorem counterexample_valuation_execution v1 v2 m ρ:
  only_bitvectors ρ ->
  counterexample_valuation v1 v2 m ρ ->
  counterexample_execution
    v1 (SMT.execution_of_valuation TaggedName.VerilogLeft m ρ)
    v2 (SMT.execution_of_valuation TaggedName.VerilogRight m ρ).
Proof.
  unfold counterexample_valuation, counterexample_execution.
  intros Honly_bv [Hvalid1 [Hvalid2 [Hinputsame [Houtdistinct [Houtputsexist1 Houtputsexist2]]]]].
  split. { assumption. }
  split. { assumption. }
  split. { now eapply all_same_values_execution_of_valuation. }
  split. { now eapply some_distinct_values_execution_of_valuation. }
  split. { now eapply all_have_values_execution_of_valuation. }
  now eapply all_have_values_execution_of_valuation.
Qed.

Definition match_map_execution (tag : TaggedName.Tag) (m : VerilogSMTBijection.t) (e : execution) :=
  forall name, (exists smtName, m (tag, name) = Some smtName) <-> (exists xbv, e name = Some xbv).

Lemma match_map_execution_of_verilog v tag m e :
  valid_execution v e ->
  SMT.match_map_verilog tag m v ->
  match_map_execution tag m e.
Proof.
  intros Hvalid Hmatch verilogName.
  assert (complete_execution v e) as Hcomplete by eauto using valid_execution_complete; clear Hvalid.
  unfold complete_execution, SMT.match_map_verilog, match_map_execution in *.
  specialize (Hcomplete verilogName). specialize (Hmatch verilogName).
  rewrite Hmatch. clear Hmatch.
  firstorder.
Qed.

Lemma Forall_impl_In {A} (P Q : A -> Prop) (l : list A) :
  (forall a : A, In a l -> P a -> Q a) ->
  Forall P l -> Forall Q l.
Proof. rewrite ! Forall_forall. firstorder. Qed.

Lemma Exists_impl_In {A} (P Q : A -> Prop) (l : list A) :
  (forall a : A, In a l -> P a -> Q a) ->
  Exists P l -> Exists Q l.
Proof.
  rewrite ! Exists_exists.
  intros Himpl [x [Hin HP]].
  eauto.
Qed.

Lemma all_same_values_valuation_of_executions e1 e2 names m :
  match_map_execution TaggedName.VerilogLeft m e1 ->
  match_map_execution TaggedName.VerilogRight m e2 ->
  execution_no_exes e1 names ->
  execution_all_same_values e1 e2 names ->
  smt_all_same_values names m (SMT.valuation_of_executions m e1 e2).
Proof.
  unfold smt_all_same_values, execution_all_same_values in *.
  intros Hmatch1 Hmatch2 Hno_exes.
  unfold execution_no_exes, execution_not_x in Hno_exes; rewrite Forall_forall in Hno_exes.
  apply Forall_impl_In.
  unfold smt_same_value, execution_same_value, execution_no_exes in *.
  intros name Hname_in [bv [H1 H2]].
  destruct Hmatch1 with (name := name) as [Hmatch1_fw Hmatch1_bw].
  edestruct Hmatch1_bw as [smtName1 HsmtName1]. { eauto. }
  destruct Hmatch2 with (name := name) as [Hmatch2_fw Hmatch2_bw].
  edestruct Hmatch2_bw as [smtName2 HsmtName2]. { eauto. }
  unfold match_map_execution in *.
  exists smtName1. exists smtName2.
  assert (exists v : RawBV.t, XBV.to_bv bv = Some v) as Hto_bv. {
    apply XBV.not_has_x_to_bv. eauto.
  } destruct Hto_bv.
  erewrite SMT.valuation_of_executions_some_left; eauto.
  erewrite SMT.valuation_of_executions_some_right; eauto.
Qed.

Lemma FIXME_valid_executions_no_exes v e name xbv :
  valid_execution v e ->
  e name = Some xbv ->
  ~ XBV.has_x xbv.
Admitted.

Lemma some_distinct_values_valuation_of_executions e1 e2 names m :
  match_map_execution TaggedName.VerilogLeft m e1 ->
  match_map_execution TaggedName.VerilogRight m e2 ->
  execution_no_exes e1 names ->
  execution_no_exes e2 names ->
  execution_some_distinct_values e1 e2 names ->
  smt_some_distinct_values names m (SMT.valuation_of_executions m e1 e2).
Proof.
  unfold smt_some_distinct_values, execution_some_distinct_values in *.
  intros Hmatch1 Hmatch2 Hno_exes1 Hno_exes2.
  unfold execution_no_exes, execution_not_x in *; rewrite Forall_forall in Hno_exes1, Hno_exes2.
  apply Exists_impl_In.
  unfold smt_distinct_value, execution_distinct_value.
  intros name Hname_in [v1 [v2 [H1 [H2 Hdistinct]]]].
  decompose [or] Hdistinct; clear Hdistinct; try solve [exfalso; firstorder].
  destruct Hmatch1 with (name := name) as [Hmatch1_fw Hmatch1_bw].
  edestruct Hmatch1_bw as [smtName1 HsmtName1]. { eauto. }
  destruct Hmatch2 with (name := name) as [Hmatch2_fw Hmatch2_bw].
  edestruct Hmatch2_bw as [smtName2 HsmtName2]. { eauto. }
  unfold match_map_execution in *.
  exists smtName1. exists smtName2.
  assert (exists bv : RawBV.t, XBV.to_bv v1 = Some bv) as Hto_bv1. {
    apply XBV.not_has_x_to_bv. eauto.
  } destruct Hto_bv1 as [bv1 Hbv1].
  assert (exists bv : RawBV.t, XBV.to_bv v2 = Some bv) as Hto_bv2. {
    apply XBV.not_has_x_to_bv. eauto.
  } destruct Hto_bv2 as [bv2 Hbv2].
  erewrite SMT.valuation_of_executions_some_left; eauto.
  erewrite SMT.valuation_of_executions_some_right; eauto.
  eexists. eexists. repeat (split; eauto).
  intro contra. apply H0.
  inv contra.
  unfold BVList.RAWBITVECTOR_LIST.of_bits in *.
  subst bv2.
  eapply XBV.to_bv_injective; eassumption.
Qed.

Lemma all_have_values_left_valuation_of_executions e1 e2 names m :
  execution_no_exes e1 names ->
  match_map_execution TaggedName.VerilogLeft m e1 ->
  execution_all_have_values e1 names ->
  smt_all_have_values TaggedName.VerilogLeft names m (SMT.valuation_of_executions m e1 e2).
Proof.
  intros Hno_exes Hmatch.
  unfold execution_all_have_values, execution_has_value, smt_all_have_values, smt_has_value, match_map_execution in *.
  unfold execution_no_exes, execution_not_x in *; rewrite Forall_forall in Hno_exes.
  eapply Forall_impl_In.
  intros name Hname_in [xbv Hxbv].
  destruct Hmatch with (name := name) as [_ [smtName HsmtName]]; eauto.
  exists smtName.
  assert (exists bv : RawBV.t, XBV.to_bv xbv = Some bv) as Hto_bv. {
    apply XBV.not_has_x_to_bv. eauto.
  } destruct Hto_bv as [bv Hbv].
  erewrite SMT.valuation_of_executions_some_left; eauto.
Qed.

Lemma all_have_values_right_valuation_of_executions e1 e2 names m :
  execution_no_exes e2 names ->
  match_map_execution TaggedName.VerilogRight m e2 ->
  execution_all_have_values e2 names ->
  smt_all_have_values TaggedName.VerilogRight names m (SMT.valuation_of_executions m e1 e2).
Proof.
  intros Hno_exes Hmatch.
  unfold execution_all_have_values, execution_has_value, smt_all_have_values, smt_has_value, match_map_execution in *.
  unfold execution_no_exes, execution_not_x in *; rewrite Forall_forall in Hno_exes.
  eapply Forall_impl_In.
  intros name Hname_in [xbv Hxbv].
  destruct Hmatch with (name := name) as [_ [smtName HsmtName]]; eauto.
  exists smtName.
  assert (exists bv : RawBV.t, XBV.to_bv xbv = Some bv) as Hto_bv. {
    apply XBV.not_has_x_to_bv. eauto.
  } destruct Hto_bv as [bv Hbv].
  erewrite SMT.valuation_of_executions_some_right; eauto.
Qed.

Lemma counterexample_execution_valuation v1 v2 m e1 e2 :
  SMT.match_map_verilog TaggedName.VerilogLeft m v1 ->
  SMT.match_map_verilog TaggedName.VerilogRight m v2 ->
  counterexample_execution v1 e1 v2 e2 ->
  counterexample_valuation v1 v2 m (SMT.valuation_of_executions m e1 e2).
Proof.
  unfold counterexample_valuation, counterexample_execution.
  intros Hmatch1 Hmatch2 [Hvalid1 [Hvalid2 [Hinputsame [Houtputdifferent [Houtputexist1 Houtputexist2]]]]].
  assert (match_map_execution TaggedName.VerilogLeft m e1) by eauto using match_map_execution_of_verilog.
  assert (match_map_execution TaggedName.VerilogRight m e2) by eauto using match_map_execution_of_verilog.
  assert (forall names, execution_no_exes e1 names). {
    intros. unfold execution_no_exes, execution_not_x. apply Forall_forall.
    intros. eauto using FIXME_valid_executions_no_exes.
  }
  assert (forall names, execution_no_exes e2 names). {
    intros. unfold execution_no_exes, execution_not_x. apply Forall_forall.
    intros. eauto using FIXME_valid_executions_no_exes.
  }
  repeat split.
  - erewrite SMT.execution_left_of_valuation_of_executions.
    + assumption.
    + eauto using FIXME_valid_executions_no_exes.
    + eauto using FIXME_valid_executions_no_exes.
    + eassumption.
    + eauto using valid_execution_complete.
  - erewrite SMT.execution_right_of_valuation_of_executions.
    + assumption.
    + eauto using FIXME_valid_executions_no_exes.
    + eauto using FIXME_valid_executions_no_exes.
    + eassumption.
    + eauto using valid_execution_complete.
  - apply all_same_values_valuation_of_executions; eauto.
  - apply some_distinct_values_valuation_of_executions; eauto.
  - apply all_have_values_left_valuation_of_executions; eauto.
  - apply all_have_values_right_valuation_of_executions; eauto.
Qed.

Lemma execution_of_valuation_map_equal (m1 m2 : VerilogSMTBijection.t) tag ρ:
  (forall n, m1 (tag, n) = m2 (tag, n)) ->
  SMT.execution_of_valuation tag m1 ρ = SMT.execution_of_valuation tag m2 ρ.
Proof.
  intros.
  unfold SMT.execution_of_valuation.
  apply functional_extensionality.
  intros name.
  rewrite <- H.
  reflexivity.
Qed.

Theorem equivalence_query_canonical_spec verilog1 verilog2 smt :
  equivalence_query_canonical verilog1 verilog2 = inr smt ->
  SMTLibFacts.smt_reflect
    (SMT.query smt)
    (counterexample_valuation verilog1 verilog2 (SMT.nameMap smt)).
Proof.
  unfold equivalence_query_canonical.
  intros H.
  inv H. autodestruct_eqn E. simpl.
  remember (VerilogSMTBijection.combine _ _ _ _) as m_combined.
  apply SMTLibFacts.concat_conj. {
    eapply SMTLibFacts.smt_reflect_rewrite with
      (P2 := (fun ρ => valid_execution verilog1 (SMT.execution_of_valuation TaggedName.VerilogLeft (SMT.nameMap s) ρ))).
    - intros.
      rewrite (execution_of_valuation_map_equal m_combined (SMT.nameMap s)). reflexivity.
      replace m_combined.
      eapply VerilogSMTBijection.combine_different_tag_left with (t2 := TaggedName.VerilogRight).
      + discriminate.
      + eapply VerilogToSMTCorrect.verilog_to_smt_only_tag; eassumption.
      + eapply VerilogToSMTCorrect.verilog_to_smt_only_tag; eassumption.
    - eapply VerilogToSMTCorrect.verilog_to_smt_correct; eassumption.
  }
  apply SMTLibFacts.concat_conj. {
    eapply SMTLibFacts.smt_reflect_rewrite with
      (P2 := (fun ρ => valid_execution verilog2 (SMT.execution_of_valuation TaggedName.VerilogRight (SMT.nameMap s0) ρ))).
    - intros.
      rewrite (execution_of_valuation_map_equal m_combined (SMT.nameMap s0)). reflexivity.
      replace m_combined.
      eapply VerilogSMTBijection.combine_different_tag_right with (t1 := TaggedName.VerilogLeft).
      + discriminate.
      + eapply VerilogToSMTCorrect.verilog_to_smt_only_tag; eassumption.
      + eapply VerilogToSMTCorrect.verilog_to_smt_only_tag; eassumption.
    - eapply VerilogToSMTCorrect.verilog_to_smt_correct; eassumption.
  }
  fold ([t] ++ [t0])%list.
  apply SMTLibFacts.concat_conj.
  - eapply mk_inputs_same_spec. eassumption.
  - apply (mk_outputs_distinct_spec _ _ _ ltac:(eassumption)).
Qed.

Lemma not_distinct_same_value var m ρ :
  smt_has_value TaggedName.VerilogLeft var m ρ ->
  smt_has_value TaggedName.VerilogRight var m ρ ->
  ~ (smt_distinct_value var m ρ) ->
  smt_same_value var m ρ.
Proof.
  unfold smt_has_value, smt_distinct_value, smt_same_value.
  intros [smtName1 [v1 [Hname1 Hval1]]] [smtName2 [v2 [Hname2 Hval2]]] H.
  exists smtName1. exists smtName2. exists v1.
  enough (v1 = v2) by intuition congruence.
  destruct (SMTLib.value_eqb v1 v2) eqn:E.
  - now apply SMTLib.value_eqb_eq.
  - apply value_eqb_neq in E.
    contradict H.
    repeat eexists; intuition eauto.
Qed.

Lemma not_some_distinct_all_same vars m ρ :
  smt_all_have_values TaggedName.VerilogLeft  vars m ρ ->
  smt_all_have_values TaggedName.VerilogRight vars m ρ ->
  ~ (smt_some_distinct_values vars m ρ) ->
  smt_all_same_values vars m ρ.
Proof.
  unfold smt_some_distinct_values, smt_all_same_values, smt_all_have_values.
  rewrite ! Forall_forall, Exists_exists.
  intros.
  eauto 15 using not_distinct_same_value.
Qed.

Ltac dec_left_tac :=
  left; solve [repeat (progress eexists); firstorder].

Ltac dec_right_tac :=
  right; intros H; decompose [and] H; firstorder; solve_by_inverts 3%nat.

Ltac dec_tac := solve [dec_left_tac || dec_right_tac].

Instance dec_match_on_regs regs s1 s2 : DecProp (match_on_regs regs s1 s2).
Proof.
  unfold match_on_regs.
  eapply @dec_Forall.
  intros.
  destruct (s1 x), (s2 x); try dec_tac.
  destruct (dec (t0 = t)), (dec (XBV.has_x t)); subst;
    dec_tac.
Qed.

Lemma run_multistep_execution v input final :
  input_valid v input ->
  run_multistep (initial_state v input) = Some final ->
  valid_execution v (regState final).
Proof. unfold valid_execution. eauto. Qed.

Lemma initial_state_same_inputs v1 v2 input :
  Verilog.inputs v1 = Verilog.inputs v2 ->
  regState (initial_state v1 input) = regState (initial_state v2 input).
Proof.
  intros.
  unfold initial_state.
  replace (Verilog.inputs v2).
  simpl.
  reflexivity.
Qed.

Lemma initial_state_has_input_values v input :
  input_valid v input ->
  Forall (fun n => exists val, regState (initial_state v input) n = Some val) (Verilog.inputs v).
Proof.
  unfold input_valid, initial_state in *; simpl in *.
  revert input.
  induction (Verilog.inputs v). solve [auto].
  simpl.
  intros. destruct input as [ | input_hd input_tl ]; try discriminate.
  simpl in H. inv H. specialize (IHl input_tl ltac:(assumption)).
  constructor.
  - simpl. unfold StrFunMap.insert.
    rewrite eqb_refl. eauto.
  - simpl. unfold StrFunMap.insert.
    rewrite Forall_forall in *.
    intros name Hname_in.
    destruct (a =? name)%string; eauto.
Qed.

Lemma same_input_values_preserved v1 v2 input final1 final2
  (inputs_same : Verilog.inputs v1 = Verilog.inputs v2)
  (input_wf1 : input_valid v1 input)
  (input_wf2 : input_valid v2 input)
  (input_vals_defined : Forall (fun bv : XBV.t => ~ XBV.has_x bv) input)
  (run1 : run_multistep (initial_state v1 input) = Some final1)
  (run2 : run_multistep (initial_state v2 input) = Some final2) :
  execution_all_same_values (regState final1) (regState final2) (Verilog.inputs v1).
Proof.
  unfold execution_all_same_values.
  apply run_multistep_preserve_initial_values in run1; try assumption.
  apply run_multistep_preserve_initial_values in run2; try assumption.
  unfold execution_same_value.
  apply Forall_forall. rewrite Forall_forall in run1, run2.
  intros name Hname_in.
  specialize (run1 name Hname_in).
  rewrite <- inputs_same in run2. specialize (run2 name Hname_in).
  rewrite run1.
  erewrite <- initial_state_same_inputs in run2 by eassumption. rewrite run2.
  pose proof (initial_state_has_input_values v1 input ltac:(auto)) as Hhas_values.
  rewrite Forall_forall in Hhas_values.
  edestruct Hhas_values; eauto.
Qed.

Instance dec_execution_distinct_value e1 e2 name :
  DecProp (execution_distinct_value e1 e2 name).
Proof.
  unfold DecProp, execution_distinct_value.
  destruct (e1 name) as [v1|] eqn:E1, (e2 name) as [v2|] eqn:E2; try dec_tac.
  destruct (dec (v1 = v2)); try dec_tac.
  subst v2.
  destruct (dec (XBV.has_x v1)); dec_tac.
Qed.

Instance dec_execution_some_distinct_values e1 e2 names :
  DecProp (execution_some_distinct_values e1 e2 names).
Proof.
  unfold execution_some_distinct_values.
  typeclasses eauto.
Qed.

Lemma not_exists_forall {A} (P : A -> Prop) : (~ exists x, P x) -> forall x, ~ P x.
Proof. firstorder. Qed.

Lemma not_exists_forall2 {A B} (P : A -> B -> Prop) : (~ exists x y, P x y) -> forall x y, ~ P x y.
Proof. firstorder. Qed.

Lemma not_match_on_regs_distinct_values names st1 st2 :
  execution_all_have_values st1 names ->
  execution_all_have_values st2 names ->
  ~ match_on_regs names st1 st2 ->
  execution_some_distinct_values st1 st2 names.
Proof.
  unfold match_on_regs.
  rewrite Forall_forall.
  intros Hhave1 Hhave2 H.
  destruct (dec (execution_some_distinct_values st1 st2 names)); try assumption.
  contradict H.
  intros name Hname_in.

  unfold execution_some_distinct_values in n.

  rewrite Exists_exists in n. eapply not_exists_forall with (x := name) in n.
  destruct (dec (execution_distinct_value st1 st2 name));
    try solve [firstorder]; clear n.
  unfold execution_distinct_value in *.

  unfold execution_all_have_values, execution_has_value in *.
  rewrite Forall_forall in *.
  edestruct Hhave1 as [v1 Hv1]; eauto. rewrite Hv1.
  edestruct Hhave2 as [v2 Hv2]; eauto. rewrite Hv2.

  eapply not_exists_forall2 with (x := v1) (y := v2) in n0.
  destruct (dec (v1 = v2)); try solve [firstorder].
  subst.

  exists v2. repeat split.
  destruct (dec (XBV.has_x v2)); firstorder.
Qed.

Lemma no_counterexample_equivalent v1 v2 :
  Verilog.inputs v1 = Verilog.inputs v2 ->
  Verilog.outputs v1 = Verilog.outputs v2 ->
  (forall e1 e2, ~ counterexample_execution v1 e1 v2 e2) ->
  equivalent_behaviour v1 v2.
Proof.
  unfold equivalent_behaviour.
  unfold counterexample_execution.
  intros.
  (* unfold SMT.valid_execution in *. *)
  reductio_ad_absurdum.
  specialize (H1 (regState final1) (regState final2)).
  contradict H1. repeat split.
  - unfold valid_execution. eauto.
  - unfold valid_execution. eauto.
  - eapply same_input_values_preserved; eauto.
  - eapply not_match_on_regs_distinct_values; eauto.
    + eapply valid_execution_outputs_have_values. unfold valid_execution. eauto.
    + replace (Verilog.outputs v1).
      eapply valid_execution_outputs_have_values. unfold valid_execution. eauto.
  - apply valid_execution_outputs_have_values.
    eapply run_multistep_execution; eauto.
  - replace (Verilog.outputs v1).
    apply valid_execution_outputs_have_values.
    eapply run_multistep_execution; eauto.
Qed.

Lemma equivalence_query_canonical_same_inputs v1 v2 query :
  equivalence_query_canonical v1 v2 = inr query ->
  Verilog.inputs v1 = Verilog.inputs v2.
Proof.
  intros H.
  unfold equivalence_query_canonical in *.
  inv H. autodestruct_eqn E. auto.
Qed.

Lemma equivalence_query_canonical_same_outputs v1 v2 query :
  equivalence_query_canonical v1 v2 = inr query ->
  Verilog.outputs v1 = Verilog.outputs v2.
Proof.
  intros H.
  unfold equivalence_query_canonical in *.
  inv H. autodestruct_eqn E. auto.
Qed.

Lemma match_map_verilog_tag_equal tag v (m1 m2 : VerilogSMTBijection.t) :
  (forall n, m1 (tag, n) = m2 (tag, n)) ->
  SMT.match_map_verilog tag m1 v ->
  SMT.match_map_verilog tag m2 v.
Proof.
  unfold SMT.match_map_verilog.
  intros Heq Hmatch.
  intros verilogName. specialize (Hmatch verilogName).
  now rewrite Heq in Hmatch.
Qed.

Theorem equivalence_query_canonical_correct verilog1 verilog2 query :
  equivalence_query_canonical verilog1 verilog2 = inr query ->
  SMTLib.unsatisfiable (SMT.query query) ->
  equivalent verilog1 verilog2.
Proof.
  intros Hquery Hunsat.
  pose proof (equivalence_query_canonical_spec _ _ _ Hquery).
  assert (forall e1 e2, not (counterexample_valuation verilog1 verilog2 (SMT.nameMap query)
                      (SMT.valuation_of_executions (SMT.nameMap query) e1 e2))). {
    intros.
    eapply SMTLibFacts.unsat_negation; eassumption.
  }
  clear Hunsat. clear H.
  constructor.
  - unfold equivalence_query_canonical in *.
    inv Hquery. autodestruct_eqn E. auto.
  - unfold equivalence_query_canonical in *.
    inv Hquery. autodestruct_eqn E. auto.
  - apply FIXME_no_errors.
  - apply FIXME_no_errors.
  - eapply no_counterexample_equivalent.
    + eauto using equivalence_query_canonical_same_inputs.
    + eauto using equivalence_query_canonical_same_outputs.
    + intros * contra.
      specialize (H0 e1 e2). eapply H0. clear H0.
      eapply counterexample_execution_valuation.
      * unfold equivalence_query_canonical in Hquery; inv Hquery; autodestruct_eqn E.
        simpl.
        eapply match_map_verilog_tag_equal with (m1 := (SMT.nameMap s)).
        -- intros.
           erewrite VerilogSMTBijection.combine_different_tag_left with (t2 := TaggedName.VerilogRight);
             try discriminate; eauto using VerilogToSMTCorrect.verilog_to_smt_only_tag.
        -- eapply VerilogToSMTCorrect.verilog_to_smt_map_match; eauto.
      * unfold equivalence_query_canonical in Hquery; inv Hquery; autodestruct_eqn E.
        simpl.
        eapply match_map_verilog_tag_equal with (m1 := (SMT.nameMap s0)).
        -- intros.
           erewrite VerilogSMTBijection.combine_different_tag_right with (t1 := TaggedName.VerilogLeft);
             try discriminate; eauto using VerilogToSMTCorrect.verilog_to_smt_only_tag.
        -- eapply VerilogToSMTCorrect.verilog_to_smt_map_match; eauto.
      * eassumption.
Qed.

Definition vera_says_equivalent v1 v2 :=
  exists q, equivalence_query v1 v2 = inr q /\ SMTLib.unsatisfiable (SMT.query q).

Theorem equivalence_query_correct verilog1 verilog2 :
  vera_says_equivalent verilog1 verilog2 -> equivalent verilog1 verilog2.
Proof.
  intros [q [Hquery Hunsat]].
  unfold equivalence_query in *; inv Hquery; autodestruct_eqn E.
  eauto 10 using
    equivalent_trans,
    equivalent_sym,
    canonicalize_correct,
    equivalence_query_canonical_correct.
Qed.

Print Assumptions equivalence_query_correct.
