From vera Require Import Verilog.
From vera Require Import VerilogSMT.
From vera Require Import SMTQueries.
Import (coercions) SMT.
From vera Require Import Common.
Import (coercions) VerilogSMTBijection.
From vera Require Import Bitvector.
From vera Require VerilogTypecheck.
From vera Require VerilogCanonicalize.
From vera Require VerilogToSMT.
From vera Require VerilogToSMT.VerilogToSMTCorrect.
From vera Require Import VerilogToSMT.Match.
From vera Require Import VerilogEquivalence.
From vera Require VerilogSemantics.
From vera Require Import Tactics.
From vera Require Import Decidable.

Import VerilogSemantics.CombinationalOnly.

From Coq Require Import Relations.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Lia.
From Coq Require Import Morphisms.
From Coq Require Import Classical.

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

Import SigTNotations.

Definition smt_same_value var (m : VerilogSMTBijection.t) (ρ : SMTQueries.valuation) :=
  exists smtName1 smtName2 v,
    m (TaggedVariable.VerilogLeft, var) = Some smtName1 /\
      m (TaggedVariable.VerilogRight, var) = Some smtName2 /\
      ρ smtName1 = Some v /\
      ρ smtName2 = Some v.

Definition smt_all_same_values
  (vars : list Verilog.variable) (m : VerilogSMTBijection.t) (ρ : SMTQueries.valuation) :=
  Forall (fun verilogName => smt_same_value verilogName m ρ) vars.

Lemma smt_all_same_values_cons var vars m ρ :
  smt_all_same_values (var :: vars) m ρ <->
    smt_same_value var m ρ /\ smt_all_same_values vars m ρ.
Proof. apply List.Forall_cons_iff. Qed.

Definition smt_has_value tag (m : VerilogSMTBijection.t) var (ρ : SMTQueries.valuation) :=
  exists smtName v, m (tag, var) = Some smtName /\ ρ smtName = Some v.

Definition smt_all_have_values
  tag vars (m : VerilogSMTBijection.t) (ρ : SMTQueries.valuation) :=
  Forall (fun var => smt_has_value tag m var ρ) vars.

Lemma smt_all_have_values_cons tag var vars m ρ :
  smt_all_have_values tag (var :: vars) m ρ <->
    smt_has_value tag m var ρ /\ smt_all_have_values tag vars m ρ.
Proof. apply List.Forall_cons_iff. Qed.

Definition smt_distinct_value (var : Verilog.variable) (m : VerilogSMTBijection.t) (ρ : SMTQueries.valuation) :=
  exists smtName1 smtName2 v1 v2,
    m (TaggedVariable.VerilogLeft, var) = Some smtName1 /\
      m (TaggedVariable.VerilogRight, var) = Some smtName2 /\
      ρ smtName1 = Some v1 /\
      ρ smtName2 = Some v2 /\
      v1 <> v2.

Definition smt_some_distinct_values
  vars (m : VerilogSMTBijection.t) (ρ : SMTQueries.valuation) :=
  Exists (fun verilogName => smt_distinct_value verilogName m ρ) vars.

Definition counterexample_valuation v1 v2 m ρ :=
  valid_execution v1 (SMT.execution_of_valuation TaggedVariable.VerilogLeft m ρ)
  /\ valid_execution v2 (SMT.execution_of_valuation TaggedVariable.VerilogRight m ρ)
  /\ smt_all_same_values (Verilog.module_inputs v1) m ρ
  /\ smt_some_distinct_values (Verilog.module_outputs v1) m ρ
  /\ smt_all_have_values TaggedVariable.VerilogLeft (Verilog.module_outputs v1) m ρ
  /\ smt_all_have_values TaggedVariable.VerilogRight (Verilog.module_outputs v1) m ρ.

Definition execution_some_distinct_value (C : Verilog.variable -> Prop) (e1 e2 : execution) : Prop :=
  exists var bv1 bv2,
    C var
    /\ e1 var = Some (XBV.from_bv bv1)
    /\ e2 var = Some (XBV.from_bv bv2)
    /\ bv1 <> bv2.

Definition counterexample_execution v1 e1 v2 e2 :=
  valid_execution v1 e1
  /\ valid_execution v2 e2
  /\ execution_defined_match_on (fun var => In var (Verilog.module_inputs v1)) e1 e2
  /\ ~ execution_defined_match_on (fun var => In var (Verilog.module_outputs v1)) e1 e2.

Lemma smt_some_distinct_values_cons var vars m ρ :
  smt_some_distinct_values (var :: vars) m ρ <->
    smt_distinct_value var m ρ \/ smt_some_distinct_values vars m ρ.
Proof. apply List.Exists_cons. Qed.

Lemma term_reflect_false C P :
  (forall ρ, C ρ -> ~ P ρ) ->
  term_reflect_if C SMTLib.Term_False P.
Proof. unfold term_reflect_if, term_satisfied_by. crush. Qed.

Lemma mk_var_same_spec : forall name m q,
  mk_var_same name m = inr q ->
  term_reflect q (smt_same_value name m).
Proof.
  intros * Hfunc.
  funelim (mk_var_same name m); try congruence.
  rewrite <- Heqcall in *. clear Heqcall. inv Hfunc.
  intros ρ _.
  split; intros * H.
  - inv H. autodestruct_eqn E.
    unfold smt_same_value.
    rewrite SMTLib.value_eqb_eq in *. subst.
    eauto 7.
  - unfold SMTQueries.term_satisfied_by. simpl.
    destruct H as [smt_name1' [smt_name2' [w [v [H0 [H1 H2]]]]]].
    replace smt_name1' with smt_name1 in * by congruence.
    replace smt_name2' with smt_name2 in * by congruence.
    rewrite H1, H2, SMTLib.value_eqb_refl.
    reflexivity.
Qed.

Global Instance term_reflect_proper :
  Proper
    (eq ==> pointwise_relation valuation iff ==> iff)
    term_reflect.
Proof.
  unfold term_reflect.
  typeclasses eauto.
Qed.

Lemma mk_inputs_same_spec : forall inputs m q,
  mk_inputs_same inputs m = inr q ->
  term_reflect q (smt_all_same_values inputs m).
Proof.
  intros ?. induction inputs.
  - intros. simp mk_inputs_same in *. inv H.
    unfold smt_all_same_values.
    setoid_rewrite List.Forall_nil_iff.
    crush.
  - intros. simp mk_inputs_same in H.
    autodestruct_eqn E.
    unfold smt_all_same_values.
    setoid_rewrite Forall_cons_iff.
    apply term_reflect_and.
    + apply mk_var_same_spec. apply E.
    + apply IHinputs. assumption.
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

Lemma mk_var_distinct_spec name m t :
  mk_var_distinct name m = inr t ->
  term_reflect t (smt_distinct_value name m).
Proof.
  intros * Hfunc.
  funelim (mk_var_distinct name m); try congruence.
  rewrite <- Heqcall in *. clear Heqcall. inv Hfunc.
  intros ρ _.
  split; intros * H.
  - inv H. autodestruct_eqn E.
    rewrite Bool.negb_true_iff in *.
    apply_somewhere value_eqb_neq. subst.
    unfold smt_distinct_value.
    eauto 10.
  - unfold SMTQueries.term_satisfied_by. simpl.
    destruct H as [smt_name1' [smt_name2' [w [v [v0 [H0 [H1 [H2 H3]]]]]]]].
    replace smt_name1' with smt_name1 in * by congruence.
    replace smt_name2' with smt_name2 in * by congruence.
    rewrite H1, H2.
    apply value_eqb_neq in H3. rewrite H3.
    reflexivity.
Qed.


Lemma term_reflect_if_cond_impl C1 C2 t P :
  (forall ρ, C2 ρ -> C1 ρ) ->
  term_reflect_if C1 t P ->
  term_reflect_if C2 t P.
Proof. unfold term_reflect_if. crush. Qed.

Lemma mk_var_distinct_eval_spec var m ρ t :
  mk_var_distinct var m = inr t ->
  smt_has_value TaggedVariable.VerilogLeft m var ρ ->
  smt_has_value TaggedVariable.VerilogRight m var ρ ->
  exists b, SMTLib.interp_term ρ t = Some (SMTLib.Value_Bool b).
Proof.
  intros Hfunc Hhas_value_left Hhas_value_right.
  funelim (mk_var_distinct var m); try congruence.
  rewrite <- Heqcall in *. clear Heqcall. inv Hfunc.
  destruct Hhas_value_left as [smtName_l [v_l [Hmatch_l Hv_l]]].
  destruct Hhas_value_right as [smtName_r [v_r [Hmatch_r Hv_r]]].
  replace smt_name1 with smtName_l in * by congruence.
  replace smt_name2 with smtName_r in * by congruence.
  simpl.
  replace (ρ smtName_l). replace (ρ smtName_r).
  eauto.
Qed.

Lemma mk_outputs_distinct_eval_spec outputs m ρ t :
  mk_outputs_distinct outputs m = inr t ->
  smt_all_have_values TaggedVariable.VerilogLeft outputs m ρ ->
  smt_all_have_values TaggedVariable.VerilogRight outputs m ρ ->
  exists b, SMTLib.interp_term ρ t = Some (SMTLib.Value_Bool b).
Proof.
  revert t.
  induction outputs; simp mk_outputs_distinct;
    intros t Hfunc Hhave_values_left Hhave_values_right.
  - inv Hfunc. simpl. eauto.
  - autodestruct_eqn E.
    rewrite smt_all_have_values_cons in Hhave_values_left, Hhave_values_right.
    destruct Hhave_values_left as [Hhas_value_left Hhave_values_left].
    destruct Hhave_values_right as [Hhas_value_right Hhave_values_right].
    edestruct mk_var_distinct_eval_spec as [b1 Hb1]; eauto.
    edestruct IHoutputs as [b2 Hb2]; eauto.
    simpl. rewrite Hb1, Hb2.
    eauto.
Qed.

Lemma mk_outputs_distinct_spec outputs m t :
  mk_outputs_distinct outputs m = inr t ->
  term_reflect_if
    (fun ρ =>
       smt_all_have_values TaggedVariable.VerilogLeft outputs m ρ
       /\ smt_all_have_values TaggedVariable.VerilogRight outputs m ρ)
    t
    (smt_some_distinct_values outputs m).
Proof.
  revert t m. induction outputs.
  - intros * H. simp mk_outputs_distinct in H. inv H.
    apply term_reflect_false.
    intros ρ _ contra.
    inv contra.
  - intros.
    simp mk_outputs_distinct in H.
    autodestruct_eqn E.
    insterU IHoutputs.
    unfold smt_some_distinct_values.
    setoid_rewrite List.Exists_cons.
    eapply term_reflect_if_cond_impl; cycle 1. {
      eapply term_reflect_or.
      - apply mk_var_distinct_spec.
        eassumption.
      - eapply IHoutputs.
    }
    simpl.
    setoid_rewrite smt_all_have_values_cons.
    intros ρ [[Hvals1 Hvals2] [Hvals3 Hvals4]].
    (intuition try assumption); [|].
    + eapply mk_var_distinct_eval_spec; eauto.
    + eapply mk_outputs_distinct_eval_spec; eauto.
Qed.

Lemma execution_of_valuation_map_equal (m1 m2 : VerilogSMTBijection.t) tag ρ:
  (forall n, m1 (tag, n) = m2 (tag, n)) ->
  SMT.execution_of_valuation tag m1 ρ = SMT.execution_of_valuation tag m2 ρ.
Proof.
  intros.
  unfold SMT.execution_of_valuation.
  apply functional_extensionality_dep.
  intros name.
  rewrite <- H.
  reflexivity.
Qed.

(* TODO: This should be more general, or at least moved to Verilog.v *)
Lemma module_output_in_vars v : forall var,
  List.In var (Verilog.module_outputs v) ->
  List.In var (Verilog.modVariables v).
Proof.
  unfold Verilog.module_outputs, Verilog.modVariables.
  induction (Verilog.modVariableDecls v); crush.
Qed.

Lemma verilog_to_smt_outputs_have_values tag start v s ρ:
  VerilogToSMT.verilog_to_smt tag start v = inr s ->
  ρ ⊧ SMT.query s ->
  smt_all_have_values tag (Verilog.module_outputs v) (SMT.nameMap s) ρ.
Proof.
  unfold VerilogToSMT.verilog_to_smt, smt_all_have_values, smt_has_value, "⊧", valuation_matches_decls.
  intros H.
  monad_inv. simpl in *. intros [Hdecls Hassertions].
  intros.
  rewrite List.Forall_forall. intros var Hvar_in.
  apply module_output_in_vars in Hvar_in.
  pose proof VerilogToSMTCorrect.declarations_satisfied_valuation_has_var as H.
  insterU H. destruct H as [smtName [bv [Ht Hρ]]].
  eauto.
Qed.

Lemma satisfied_by_add_assertion_iff t q prf ρ :
  satisfied_by ρ (add_assertion t q prf) <->
  term_satisfied_by ρ t /\ satisfied_by ρ q.
Proof.
  unfold add_assertion, satisfied_by.
  simpl.
  rewrite List.Forall_cons_iff.
  crush.
Qed.

Lemma satisfied_by_combine_iff q1 q2 ρ :
  satisfied_by ρ (SMTQueries.combine q1 q2) <->
  satisfied_by ρ q1 /\ satisfied_by ρ q2.
Proof.
  unfold SMTQueries.combine, satisfied_by, valuation_matches_decls.
  simpl.
  rewrite ! List.Forall_app.
  crush.
Qed.

Lemma smt_has_value_tag_equal (m1 m2 : VerilogSMTBijection.t) var tag ρ :
  (forall var, m1 (tag, var) = m2 (tag, var)) ->
  smt_has_value tag m1 var ρ <-> smt_has_value tag m2 var ρ.
Proof.
  unfold smt_has_value.
  intros H. rewrite H. reflexivity.
Qed.

Lemma smt_all_have_values_tag_equal (m1 m2 : VerilogSMTBijection.t) vars tag ρ :
  (forall var, m1 (tag, var) = m2 (tag, var)) ->
  smt_all_have_values tag vars m1 ρ <-> smt_all_have_values tag vars m2 ρ.
Proof.
  unfold smt_all_have_values.
  rewrite ! List.Forall_forall.
  intros.
  setoid_rewrite smt_has_value_tag_equal; eauto.
  reflexivity.
Qed.

Theorem equivalence_query_spec verilog1 verilog2 smt :
  equivalence_query verilog1 verilog2 = inr smt ->
  smt_reflect
    (SMT.query smt)
    (counterexample_valuation verilog1 verilog2 (SMT.nameMap smt)).
Proof.
  unfold equivalence_query.
  intros H.
  monad_inv.
  simpl in *.
  remember (VerilogSMTBijection.combine _ _ _ _) as m_combined.
  unfold counterexample_valuation.

  eapply smt_reflect_if_elim.
  - eapply smt_reflect_if_rewrite; cycle 1.
    + apply add_assertion_reflect_if. {
        apply mk_outputs_distinct_spec; eassumption.
      }
      apply add_assertion_reflect_if. {
        apply term_reflect_if_intro.
        apply mk_inputs_same_spec; eassumption.
      }
      apply smt_reflect_if_intro.
      apply concat_conj.
      * eapply VerilogToSMTCorrect.verilog_to_smt_correct.
        eassumption.
      * eapply VerilogToSMTCorrect.verilog_to_smt_correct.
        eassumption.
    + simpl. intros ρ [Hvalues_left Hvalues_right].
      split; intros H; decompose record H; clear H;
        repeat split; try eassumption.
      * erewrite execution_of_valuation_map_equal; [eassumption|].
        replace m_combined. intros. symmetry.
        eapply VerilogSMTBijection.combine_different_tag_left
          with (t2 := TaggedVariable.VerilogRight).
        -- discriminate.
        -- eapply verilog_to_smt_only_tag; eassumption.
        -- eapply verilog_to_smt_only_tag; eassumption.
      * erewrite execution_of_valuation_map_equal; [eassumption|].
        replace m_combined. intros. symmetry.
        eapply VerilogSMTBijection.combine_different_tag_right
          with (t1 := TaggedVariable.VerilogLeft).
        -- discriminate.
        -- eapply verilog_to_smt_only_tag; eassumption.
        -- eapply verilog_to_smt_only_tag; eassumption.
      * erewrite execution_of_valuation_map_equal; [eassumption|].
        replace m_combined. intros.
        eapply VerilogSMTBijection.combine_different_tag_left
          with (t2 := TaggedVariable.VerilogRight).
        -- discriminate.
        -- eapply verilog_to_smt_only_tag; eassumption.
        -- eapply verilog_to_smt_only_tag; eassumption.
      * erewrite execution_of_valuation_map_equal; [eassumption|].
        replace m_combined. intros.
        eapply VerilogSMTBijection.combine_different_tag_right
          with (t1 := TaggedVariable.VerilogLeft).
        -- discriminate.
        -- eapply verilog_to_smt_only_tag; eassumption.
        -- eapply verilog_to_smt_only_tag; eassumption.
  - simpl. intros. crush.
  - simpl.
    intros ρ H.
    rewrite ! satisfied_by_add_assertion_iff, satisfied_by_combine_iff in H.
    decompose record H. clear H.
    replace m_combined.
    split.
    + eapply smt_all_have_values_tag_equal. {
        intros.
        eapply VerilogSMTBijection.combine_different_tag_left
          with (t2 := TaggedVariable.VerilogRight).
        - discriminate.
        - eapply verilog_to_smt_only_tag; eassumption.
        - eapply verilog_to_smt_only_tag; eassumption.
      }
      eapply verilog_to_smt_outputs_have_values; eassumption.
    + eapply smt_all_have_values_tag_equal. {
        intros.
        eapply VerilogSMTBijection.combine_different_tag_right
          with (t1 := TaggedVariable.VerilogLeft).
        - discriminate.
        - eapply verilog_to_smt_only_tag; eassumption.
        - eapply verilog_to_smt_only_tag; eassumption.
      }
      replace (Verilog.module_outputs verilog1).
      eapply verilog_to_smt_outputs_have_values; try eassumption.
Qed.

Lemma smt_same_values_eq var vars m n1 n2 ρ :
  smt_all_same_values vars m ρ ->
  In var vars ->
  m (TaggedVariable.VerilogLeft, var) = Some n1 ->
  m (TaggedVariable.VerilogRight, var) = Some n2 ->
  ρ n1 = ρ n2.
Proof.
  unfold smt_all_same_values, smt_same_value.
  intros Hmatch Hin Hm1 Hm2.
  rewrite List.Forall_forall in Hmatch.
  insterU Hmatch.
  destruct Hmatch as [n1' [n2'[v [? [? [? ?]]]]]].
  replace n1' with n1 in * by crush.
  replace n2' with n2 in * by crush.
  crush.
Qed.

Lemma execution_of_valuation_inv tag m ρ var bv :
  SMT.execution_of_valuation tag m ρ var = Some (XBV.from_bv bv) ->
  exists smtName,
    m (tag, var) = Some smtName /\
    ρ smtName = Some (SMTLib.Value_BitVec (Verilog.varType var) bv).
Proof.
  unfold SMT.execution_of_valuation.
  intros H.
  autodestruct_eqn E. simpl in *.
  apply XBV.from_bv_injective in H1; subst.
  eauto.
Qed.

Lemma valid_execution_of_valuation_match v tag m ρ :
  VerilogToSMT.all_vars_driven v ->
  valid_execution v (SMT.execution_of_valuation tag m ρ) ->
  verilog_smt_match_states_partial
    (fun var => In var (Verilog.modVariables v))
    tag m (SMT.execution_of_valuation tag m ρ) ρ.
Proof.
  unfold verilog_smt_match_states_partial.
  intros Hdriven Hvalid.
  apply VerilogToSMTCorrect.valid_execution_complete in Hvalid; [|eassumption].
  unfold complete_execution in Hvalid.
  intros var Hvar_in. insterU Hvalid.
  destruct Hvalid as [xbv Hxbv].
  pose proof SMT.execution_of_valuation_no_exes as H.
  insterU H. rewrite XBV.not_has_x_to_bv in H.
  destruct H as [bv Hbv]. apply XBV.bv_xbv_inverse in Hbv. subst xbv.
  edestruct execution_of_valuation_inv as [smtName [Hm Hρ]]; [eassumption|].
  eexists. split; [eassumption|].
  econstructor; try eassumption; [].
  constructor.
Qed.

Lemma smt_distinct_values_not_defined_match vars m ρ :
  smt_some_distinct_values vars m ρ ->
  ~ execution_defined_match_on
    (fun var : Verilog.variable => In var vars)
    (SMT.execution_of_valuation TaggedVariable.VerilogLeft m ρ)
    (SMT.execution_of_valuation TaggedVariable.VerilogRight m ρ).
Proof.
  unfold execution_defined_match_on, smt_some_distinct_values.
  rewrite List.Exists_exists.
  intros Hsmt_distinct Hexecution_same.
  destruct Hsmt_distinct as [var [Hvar_in Hsmt_distinct]].
  insterU Hexecution_same.
  edestruct Hexecution_same as [xbv [Hxbv_left [Hxbv_right Hxbv_nox]]].
  clear Hexecution_same.
  setoid_rewrite XBV.not_has_x_to_bv in Hxbv_nox.
  destruct Hxbv_nox as [bv Hbv].
  apply XBV.bv_xbv_inverse in Hbv. subst xbv.
  unfold smt_distinct_value in Hsmt_distinct.

  edestruct Hsmt_distinct
    as [smtName1 [smtName2 [val1 [val2 [Hm_l [Hm_r [Hρ1 [Hρ2 Hvneq]]]]]]]].
  contradict Hvneq.

  apply execution_of_valuation_inv in Hxbv_left.
  destruct Hxbv_left as [smtName1' [Hm_l' Hρ1']].
  replace smtName1' with smtName1 in * by congruence.

  apply execution_of_valuation_inv in Hxbv_right.
  destruct Hxbv_right as [smtName2' [Hm_r' Hρ2']].
  replace smtName2' with smtName2 in * by congruence.

  rewrite Hρ1' in Hρ1. inv Hρ1.
  rewrite Hρ2' in Hρ2. inv Hρ2.
  reflexivity.
Qed.

Lemma smt_all_same_inputs_execution_match v1 v2 m ρ :
  VerilogToSMT.all_vars_driven v1 ->
  VerilogToSMT.all_vars_driven v2 ->
  valid_execution v1 (SMT.execution_of_valuation TaggedVariable.VerilogLeft m ρ) ->
  valid_execution v2 (SMT.execution_of_valuation TaggedVariable.VerilogRight m ρ) ->
  Verilog.module_inputs v1 = Verilog.module_inputs v2 ->
  smt_all_same_values (Verilog.module_inputs v1) m ρ ->
  execution_defined_match_on
    (fun var : Verilog.variable => In var (Verilog.module_inputs v1))
    (SMT.execution_of_valuation TaggedVariable.VerilogLeft m ρ)
    (SMT.execution_of_valuation TaggedVariable.VerilogRight m ρ).
Proof.
  unfold smt_all_same_values, execution_defined_match_on.
  intros Hdriven1 Hdriven2 Hvalid1 Hvalid2 Hmatch_inputs Hsmt_same var Hvar_in.
  edestruct (valid_execution_of_valuation_match v1) as
    [smtName_left [Hm_left [xbv_l val_l Hsmtval_l Hverilogval_l Hmatchvals_l]]];
    [ eassumption
    | eassumption
    | apply Verilog.module_input_in_vars; eassumption
    |].
  edestruct (valid_execution_of_valuation_match v2) as
    [smtName_right [Hm_right [xbv_r val_r Hsmtval_r Hverilogval_r Hmatchvals_r]]];
    [ eassumption
    | eassumption
    | apply Verilog.module_input_in_vars; rewrite <- Hmatch_inputs; eassumption
    |].
  rewrite Hverilogval_l, Hverilogval_r.
  replace val_r with val_l in *.
  + inv Hmatchvals_l. inv Hmatchvals_r.
    apply_somewhere inj_pair2. subst.
    eexists. repeat split; try reflexivity; [].
    apply XBV.not_has_x_to_bv.
    rewrite XBV.xbv_bv_inverse.
    eauto.
  + pose proof smt_same_values_eq as Heq.
    insterU Heq.
    rewrite Hsmtval_l, Hsmtval_r in Heq.
    inv Heq. reflexivity.
Qed.

Lemma execution_defined_match_smt_all_same_values vars m ρ :
  execution_defined_match_on
                   (fun var : Verilog.variable => In var vars)
                   (SMT.execution_of_valuation TaggedVariable.VerilogLeft m ρ)
                   (SMT.execution_of_valuation TaggedVariable.VerilogRight m ρ) ->
  smt_all_same_values vars m ρ.
Proof.
  unfold execution_defined_match_on, smt_all_same_values, smt_same_value.
  rewrite List.Forall_forall.
  intros H var Hvar_in.
  insterU H. destruct H as [xbv [Hlookup_left [Hlookup_right Hno_x]]].
  apply XBV.not_has_x_to_bv in Hno_x.
  destruct Hno_x as [bv Hbv]. apply XBV.bv_xbv_inverse in Hbv. subst xbv.

  eapply execution_of_valuation_inv in Hlookup_left.
  decompose record Hlookup_left. clear Hlookup_left.

  eapply execution_of_valuation_inv in Hlookup_right.
  decompose record Hlookup_right. clear Hlookup_right.
  eauto 10.
Qed.

Lemma valid_execution_smt_all_outputs_have_values v tag m ρ :
  VerilogToSMT.all_vars_driven v ->
  valid_execution v (SMT.execution_of_valuation tag m ρ) ->
  smt_all_have_values tag (Verilog.module_outputs v) m ρ.
Proof.
  intros Hvars_driven Hvalid.
  pose proof (VerilogToSMTCorrect.valid_execution_complete v) as H.
  insterU H. clear Hvalid Hvars_driven.
  unfold complete_execution, smt_all_have_values, smt_has_value in *.
  apply List.Forall_forall. intros var Hvar_in.
  apply Verilog.module_outputs_in_vars in Hvar_in.
  edestruct H as [xbv Hlookup]; [eassumption|clear H].
  pose proof SMT.execution_of_valuation_no_exes as H.
  insterU H. rewrite XBV.not_has_x_to_bv in H.
  destruct H as [bv Hbv]. apply XBV.bv_xbv_inverse in Hbv. subst xbv.
  eapply execution_of_valuation_inv in Hlookup.
  decompose record Hlookup. clear Hlookup.
  eauto.
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
  defined_value_for C e1 ->
  defined_value_for C e2 ->
  ~ execution_defined_match_on C e1 e2 ->
  execution_some_distinct_value C e1 e2.
Proof.
  unfold
    execution_defined_match_on,
    execution_some_distinct_value,
    defined_value_for
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
  destruct Hvalues_left as [xbv_left [Hxbv_left Hnox_left]].
  destruct Hvalues_right as [xbv_right [Hxbv_right Hnox_right]].
  rewrite XBV.not_has_x_to_bv in Hnox_left, Hnox_right.
  destruct Hnox_left as [bv_left Hbv_left].
  destruct Hnox_right as [bv_right Hbv_right].
  apply XBV.bv_xbv_inverse in Hbv_left.
  apply XBV.bv_xbv_inverse in Hbv_right.
  subst.
  exists bv_left, bv_right.
  repeat split; eauto; [].
  intro contra. subst bv_right.
  apply Hvar.
  exists (XBV.from_bv bv_left).
  repeat split; try eassumption.
  apply XBV.not_has_x_to_bv.
  setoid_rewrite XBV.xbv_bv_inverse. eauto.
Qed.

Lemma not_execution_defined_match_on_smt_some_distinct_values vars m ρ :
  execution_some_distinct_value
    (fun var : Verilog.variable => In var vars)
    (SMT.execution_of_valuation TaggedVariable.VerilogLeft m ρ)
    (SMT.execution_of_valuation TaggedVariable.VerilogRight m ρ) ->
  smt_some_distinct_values vars m ρ.
Proof.
  unfold execution_some_distinct_value, smt_some_distinct_values, smt_distinct_value in *.
  rewrite List.Exists_exists.
  intros [var [bv1 [bv2 [Hin [Hlookup_left [Hlookup_right Hneq]]]]]].
  apply execution_of_valuation_inv in Hlookup_left. decompose record Hlookup_left.
  apply execution_of_valuation_inv in Hlookup_right. decompose record Hlookup_right.
  eexists. split; [eassumption|].
  do 4 eexists. repeat split; eauto.
  intro contra. inv contra. apply_somewhere inj_pair2.
  contradiction.
Qed.

Lemma all_driven_outputs_driven v var :
  disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
  VerilogToSMT.all_vars_driven v ->
  In var (Verilog.module_outputs v) ->
  In var (Verilog.module_body_writes (Verilog.modBody v)).
Proof.
  unfold VerilogToSMT.all_vars_driven, disjoint.
  rewrite ! List.Forall_forall.
  intros Hdisjoint Hdriven Houtput.
  edestruct Hdriven.
  - eapply module_output_in_vars.
    eassumption.
  - exfalso. crush.
  - assumption.
Qed.

Lemma defined_match_on_defined_value_left C e1 e2 :
  execution_defined_match_on C e1 e2 ->
  defined_value_for C e1.
Proof.
  unfold execution_defined_match_on, defined_value_for.
  crush.
Qed.

Lemma defined_match_on_defined_value_right C e1 e2 :
  execution_defined_match_on C e1 e2 ->
  defined_value_for C e2.
Proof.
  unfold execution_defined_match_on, defined_value_for.
  crush.
Qed.

Ltac monad_inv2 :=
  try discriminate;
  repeat match goal with
    | [ H : (_ ;; _)%monad = _ |- _ ] => inv H || learn H; inversion H; subst
    | [ H : _ = (_ ;; _)%monad |- _ ] => inv H || learn H; inversion H; subst
    | [ H : inl _ = inl _ |- _ ] =>      inv H || learn H; inversion H; subst
    | [ H : inr _ = inr _ |- _ ] =>      inv H || learn H; inversion H; subst
    | [ H : ret _ = inr _ |- _ ] =>      inv H || learn H; inversion H; subst
    | [ H : inr _ = ret _ |- _ ] =>      inv H || learn H; inversion H; subst
    end;
  let E := fresh "E" in
  autodestruct_eqn E;
  repeat match goal with
    | [ E : sum_with_eqn ?x = inr _, e : ?x = inr _ |- _ ] =>
        rewrite e in E; simpl in E; inv E
    end;
  monad_cleanup
.

Lemma counterexample_valuation_execution v1 v2 m ρ q :
  equivalence_query v1 v2 = inr q ->
  counterexample_valuation v1 v2 m ρ <->
    counterexample_execution
      v1 (SMT.execution_of_valuation TaggedVariable.VerilogLeft m ρ)
      v2 (SMT.execution_of_valuation TaggedVariable.VerilogRight m ρ).
Proof.
  intros Hequivalence_query.
  assert (VerilogToSMT.all_vars_driven v1) as Hvars_driven1.
  {
    unfold equivalence_query in *. monad_inv.
    pose proof e1 as e1'.
    pose proof e2 as e2'.
    unfold VerilogToSMT.verilog_to_smt in e1'.
    unfold VerilogToSMT.verilog_to_smt in e2'.
    monad_inv.
    assumption.
  }
  assert (VerilogToSMT.all_vars_driven v2) as Hvars_driven2.
  {
    unfold equivalence_query in *. monad_inv.
    pose proof e1 as e1'.
    pose proof e2 as e2'.
    unfold VerilogToSMT.verilog_to_smt in e1'.
    unfold VerilogToSMT.verilog_to_smt in e2'.
    monad_inv.
    assumption.
  }
  assert (disjoint (Verilog.module_inputs v1) (Verilog.module_outputs v1)) as Hdisjoint.
  {
    unfold equivalence_query in *. monad_inv.
    pose proof e1 as e1'.
    pose proof e2 as e2'.
    unfold VerilogToSMT.verilog_to_smt in e1'.
    unfold VerilogToSMT.verilog_to_smt in e2'.
    monad_inv.
    assumption.
  }
  assert (Verilog.module_inputs v1 = Verilog.module_inputs v2) as Hmatch_inputs.
  {
    unfold equivalence_query in *. monad_inv.
    pose proof e1 as e1'.
    pose proof e2 as e2'.
    unfold VerilogToSMT.verilog_to_smt in e1'.
    unfold VerilogToSMT.verilog_to_smt in e2'.
    monad_inv.
    assumption.
  }
  assert (Verilog.module_outputs v1 = Verilog.module_outputs v2) as Hmatch_outputs.
  {
    unfold equivalence_query in *. monad_inv.
    pose proof e1 as e1'.
    pose proof e2 as e2'.
    unfold VerilogToSMT.verilog_to_smt in e1'.
    unfold VerilogToSMT.verilog_to_smt in e2'.
    monad_inv.
    assumption.
  }
  unfold counterexample_valuation, counterexample_execution.
  split; intros H; decompose record H; clear H; repeat split.
  - assumption.
  - assumption.
  - eapply smt_all_same_inputs_execution_match;
      eassumption.
  - eapply smt_distinct_values_not_defined_match;
      eassumption.
  - eassumption.
  - eassumption.
  - apply execution_defined_match_smt_all_same_values;
      assumption.
  - apply not_execution_defined_match_on_smt_some_distinct_values; [].
    apply not_defined_match_some_distinct.
    + eapply VerilogToSMTCorrect.defined_value_for_impl.
      * intros. eapply all_driven_outputs_driven; eassumption.
      * unfold equivalence_query in *. monad_inv.
        eapply VerilogToSMTCorrect.valid_execution_no_exes_written.
        -- eassumption.
        -- eassumption.
        -- eapply defined_match_on_defined_value_left. eassumption.
    + rewrite Hmatch_outputs, Hmatch_inputs in *.
      eapply VerilogToSMTCorrect.defined_value_for_impl.
      * intros. eapply all_driven_outputs_driven; eassumption.
      * unfold equivalence_query in *. monad_inv.
        eapply VerilogToSMTCorrect.valid_execution_no_exes_written.
        -- eassumption.
        -- eassumption.
        -- eapply defined_match_on_defined_value_right. eassumption.
    + assumption.
  - eapply valid_execution_smt_all_outputs_have_values;
      eassumption.
  - rewrite Hmatch_outputs.
    eapply valid_execution_smt_all_outputs_have_values;
      eassumption.
Qed.

Lemma valuation_has_var_tag_equal tag (m1 m2 : VerilogSMTBijection.t) ρ var :
  (forall n, m1 (tag, n) = m2 (tag, n)) ->
  valuation_has_var tag m1 ρ var <-> valuation_has_var tag m2 ρ var.
Proof.
  unfold valuation_has_var.
  intros Heq.
  split.
  all:
    intros Hmatch;
    decompose record Hmatch;
    rewrite Heq in *;
    eauto.
Qed.

Ltac inv_equivalence_query_sat :=
  match goal with
  | [ Hfunc: equivalence_query _ _ = inr ?smt, Hsat : _ ⊧ SMT.query ?smt |- _ ] =>
      unfold equivalence_query in Hfunc; monad_inv; simpl in *;
      rewrite ! satisfied_by_add_assertion_iff, satisfied_by_combine_iff in Hsat;
      decompose record Hsat
  end.

Theorem equivalence_query_execution_spec v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  smt_reflect
    (SMT.query smt)
    (fun ρ => counterexample_execution
      v1 (SMT.execution_of_valuation TaggedVariable.VerilogLeft (SMT.nameMap smt) ρ)
      v2 (SMT.execution_of_valuation TaggedVariable.VerilogRight (SMT.nameMap smt) ρ)).
Proof.
  intros Hfunc.
  setoid_rewrite <- counterexample_valuation_execution; [|eassumption].
  eapply equivalence_query_spec.
  assumption.
Qed.

Definition equivalent_behaviour (v1 v2 : Verilog.vmodule) : Prop :=
  forall e1 e2,
    valid_execution v1 e1 ->
    valid_execution v2 e2 ->
    execution_defined_match_on
      (fun var => In var (Verilog.module_inputs v1))
      e1 e2 ->
    execution_defined_match_on
      (fun var => In var (Verilog.module_outputs v1))
      e1 e2.

Record equivalent v1 v2:=
  MkEquivalent
    {
      equiv_inputs : Verilog.module_inputs v1 = Verilog.module_inputs v2;
      equiv_outputs : Verilog.module_outputs v1 = Verilog.module_outputs v2;
      equiv_behaviour : equivalent_behaviour v1 v2
    }.

Lemma no_counterexample_equivalent_iff v1 v2 :
  (forall e1 e2, ~ counterexample_execution v1 e1 v2 e2) <-> (equivalent_behaviour v1 v2).
Proof.
  unfold equivalent_behaviour, counterexample_execution.
  split; intros H e1 e2.
  - intros.
    specialize (H e1 e2).
    apply not_and_or in H. destruct H; [contradiction|].
    apply not_and_or in H. destruct H; [contradiction|].
    apply not_and_or in H. destruct H; [contradiction|].
    apply NNPP in H. assumption.
  - intros Hcontra. decompose record Hcontra.
    insterU H. contradiction.
Qed.

Theorem equivalence_query_sat_correct v1 v2 smt ρ :
  equivalence_query v1 v2 = inr smt ->
  satisfied_by ρ (SMT.query smt) ->
  counterexample_execution
    v1 (SMT.execution_of_valuation TaggedVariable.VerilogLeft (SMT.nameMap smt) ρ)
    v2 (SMT.execution_of_valuation TaggedVariable.VerilogRight (SMT.nameMap smt) ρ).
Proof. intros. now apply equivalence_query_execution_spec. Qed.

Definition match_map_execution tag (m : VerilogSMTBijection.t) (e : execution) :=
  forall var,
    (exists smtName, m (tag, var) = Some smtName) <-> (exists xbv, e var = Some xbv).

Lemma execution_of_valuation_inverse_left (m : VerilogSMTBijection.t) var e1 e2 :
  defined_value_for (fun var => exists n, m (TaggedVariable.VerilogLeft, var) = Some n) e1 ->
  (exists n, m (TaggedVariable.VerilogLeft, var) = Some n) ->
  SMT.execution_of_valuation TaggedVariable.VerilogLeft m (SMT.valuation_of_executions m e1 e2) var =
    e1 var.
Proof.
  unfold SMT.execution_of_valuation, SMT.valuation_of_executions.
  intros Hdefined Hexists.
  unfold defined_value_for in Hdefined.
  insterU Hdefined.
  destruct Hexists as [n Hm].
  rewrite Hm.
  rewrite VerilogSMTBijection.bij_wf in Hm.
  rewrite Hm.
  rewrite <- VerilogSMTBijection.bij_wf in Hm.

  edestruct Hdefined as [xbv [Hxbv Hxbv_nox]]; eauto; [].
  rewrite XBV.not_has_x_to_bv in Hxbv_nox.
  destruct Hxbv_nox as [bv Hbv].
  rewrite Hxbv, Hbv.

  autodestruct; [|contradiction].
  rewrite <- eq_rect_eq.
  f_equal.
  now apply XBV.bv_xbv_inverse.
Qed.

Lemma execution_of_valuation_inverse_right (m : VerilogSMTBijection.t) var e1 e2 :
  defined_value_for (fun var => exists n, m (TaggedVariable.VerilogRight, var) = Some n) e2 ->
  (exists n, m (TaggedVariable.VerilogRight, var) = Some n) ->
  SMT.execution_of_valuation TaggedVariable.VerilogRight m (SMT.valuation_of_executions m e1 e2) var =
    e2 var.
Proof.
  unfold SMT.execution_of_valuation, SMT.valuation_of_executions.
  intros Hdefined Hexists.
  unfold defined_value_for in Hdefined.
  insterU Hdefined.
  destruct Hexists as [n Hm].
  rewrite Hm.
  rewrite VerilogSMTBijection.bij_wf in Hm.
  rewrite Hm.
  rewrite <- VerilogSMTBijection.bij_wf in Hm.

  edestruct Hdefined as [xbv [Hxbv Hxbv_nox]]; eauto; [].
  rewrite XBV.not_has_x_to_bv in Hxbv_nox.
  destruct Hxbv_nox as [bv Hbv].
  rewrite Hxbv, Hbv.

  autodestruct; [|contradiction].
  rewrite <- eq_rect_eq.
  f_equal.
  now apply XBV.bv_xbv_inverse.
Qed.

Lemma limit_to_regs_rewrite vars e1 e2 :
  (forall var, In var vars -> e1 var = e2 var) ->
  limit_to_regs vars e1 = limit_to_regs vars e2.
Proof.
  unfold limit_to_regs.
  intros Heq.
  apply functional_extensionality_dep.
  intros var. autodestruct; crush.
Qed.

Lemma valid_execution_rewrite v e1 e2 :
  list_subset (Verilog.module_body_writes (Verilog.modBody v)) (Verilog.modVariables v) ->
  (forall var, In var (Verilog.modVariables v) -> e1 var = e2 var) ->
  valid_execution v e1 <-> valid_execution v e2.
Proof.
  unfold valid_execution, execution_match_on, list_subset.
  rewrite List.Forall_forall.
  intros Hwrites_in_vars Heq.
  split; intros [e' [Hrun H]].
  - exists e'. split.
    + now rewrite <- limit_to_regs_rewrite with (e1 := e1)
        by auto using Verilog.module_input_in_vars.
    + intros var Hvar_in.
      rewrite <- Heq; cycle 1. {
        apply List.in_app_iff in Hvar_in.
        destruct Hvar_in;
          auto using Verilog.module_input_in_vars.
      }
      auto.
  - exists e'. split.
    + now rewrite limit_to_regs_rewrite with (e2 := e2)
        by auto using Verilog.module_input_in_vars.
    + intros var Hvar_in.
      rewrite Heq; cycle 1. {
        apply List.in_app_iff in Hvar_in.
        destruct Hvar_in;
          auto using Verilog.module_input_in_vars.
      }
      auto.
Qed.

Lemma execution_defined_match_on_rewrite_left C e1 e1' e2 :
  (forall var, C var -> e1 var = e1' var) ->
  execution_defined_match_on C e1 e2 <-> execution_defined_match_on C e1' e2.
Proof.
  unfold execution_defined_match_on.
  intros Heq. split; intros Hmatch var HC.
  - rewrite <- Heq; auto.
  - rewrite Heq; auto.
Qed.

Lemma execution_defined_match_on_rewrite_right C e1 e2 e2' :
  (forall var, C var -> e2 var = e2' var) ->
  execution_defined_match_on C e1 e2 <-> execution_defined_match_on C e1 e2'.
Proof.
  unfold execution_defined_match_on.
  intros Heq. split; intros Hmatch var HC.
  - rewrite <- Heq; auto.
  - rewrite Heq; auto.
Qed.

Lemma counterexample_execution_rewrite_left v1 e1 e1' v2 e2 :
  list_subset (Verilog.module_body_writes (Verilog.modBody v1)) (Verilog.modVariables v1) ->
  (forall var, In var (Verilog.modVariables v1) -> e1 var = e1' var) ->
  counterexample_execution v1 e1 v2 e2 <-> counterexample_execution v1 e1' v2 e2.
Proof.
  unfold counterexample_execution.
  intros Hwrites_in_vars Heq.
  split; intros [Hvalid1 [Hvalid2 [Hdefined_in Hnot_defined_out]]];
    repeat split; try eassumption.
  - rewrite <- valid_execution_rewrite; eassumption.
  - rewrite <- execution_defined_match_on_rewrite_left;
      eauto using Verilog.module_input_in_vars.
  - rewrite <- execution_defined_match_on_rewrite_left;
      eauto using Verilog.module_outputs_in_vars.
  - rewrite valid_execution_rewrite; eassumption.
  - rewrite execution_defined_match_on_rewrite_left;
      eauto using Verilog.module_input_in_vars.
  - rewrite execution_defined_match_on_rewrite_left;
      eauto using Verilog.module_outputs_in_vars.
Qed.

Lemma counterexample_execution_rewrite_right v1 e1 v2 e2 e2' :
  Verilog.module_inputs v1 = Verilog.module_inputs v2 ->
  Verilog.module_outputs v1 = Verilog.module_outputs v2 ->
  list_subset (Verilog.module_body_writes (Verilog.modBody v2)) (Verilog.modVariables v2) ->
  (forall var, In var (Verilog.modVariables v2) -> e2 var = e2' var) ->
  counterexample_execution v1 e1 v2 e2 <-> counterexample_execution v1 e1 v2 e2'.
Proof.
  unfold counterexample_execution.
  intros Hinputs_same Houtputs_same Hwrites_in_vars Heq.
  rewrite Hinputs_same, Houtputs_same.
  split; intros [Hvalid1 [Hvalid2 [Hdefined_in Hnot_defined_out]]];
    repeat split; try eassumption.
  - rewrite <- valid_execution_rewrite; eassumption.
  - rewrite <- execution_defined_match_on_rewrite_right;
      eauto using Verilog.module_input_in_vars.
  - rewrite <- execution_defined_match_on_rewrite_right;
      eauto using Verilog.module_outputs_in_vars.
  - rewrite valid_execution_rewrite; eassumption.
  - rewrite execution_defined_match_on_rewrite_right;
      eauto using Verilog.module_input_in_vars.
  - rewrite execution_defined_match_on_rewrite_right;
      eauto using Verilog.module_outputs_in_vars.
Qed.

Lemma match_map_execution_map_equal (m1 m2 : VerilogSMTBijection.t) tag e:
  (forall n, m1 (tag, n) = m2 (tag, n)) ->
  match_map_execution tag m1 e <-> match_map_execution tag m2 e.
Proof.
  intros.
  unfold match_map_execution.
  setoid_rewrite H.
  reflexivity.
Qed.

Lemma verilog_to_smt_match_map_execution tag start v s e :
  VerilogToSMT.verilog_to_smt tag start v = inr s ->
  exact_execution v e ->
  match_map_execution tag (SMT.nameMap s) e.
Proof.
  unfold match_map_execution, exact_execution.
  intros Hfunc Hexact.
  pose proof VerilogToSMTCorrect.verilog_to_smt_map_match as Hmap_vars.
  insterU Hmap_vars.
  unfold SMT.match_map_vars in *.
  intros ?.
  etransitivity; eauto.
Qed.

Lemma valid_execution_all_vars_defined tag start v q e :
  VerilogToSMT.verilog_to_smt tag start v = inr q ->
  valid_execution v e ->
  defined_value_for (fun var => List.In var (Verilog.module_inputs v)) e ->
  defined_value_for (fun var => List.In var (Verilog.modVariables v)) e.
Proof.
  intros.
  assert (VerilogToSMT.all_vars_driven v) as Hdriven
    by (unfold VerilogToSMT.verilog_to_smt in *; monad_inv; assumption).
  eapply VerilogToSMTCorrect.defined_value_for_impl.
  - eapply List.Forall_forall.
    eapply Hdriven.
  - apply defined_value_for_split_iff.
    split.
    + assumption.
    + eapply VerilogToSMTCorrect.valid_execution_no_exes_written; eassumption.
Qed.

(* FIXME: Move me to SMT *)
Lemma match_map_vars_tag_same tag (m1 m2 : VerilogSMTBijection.t) vars :
  (forall var, m1 (tag, var) = m2 (tag, var)) ->
  SMT.match_map_vars tag m1 vars <-> SMT.match_map_vars tag m2 vars.
Proof.
  unfold SMT.match_map_vars.
  intros H. setoid_rewrite H.
  reflexivity.
Qed.

Lemma equivalence_query_map_match_left v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  SMT.match_map_vars TaggedVariable.VerilogLeft (SMT.nameMap smt) (Verilog.modVariables v1).
Proof.
  unfold equivalence_query.
  intros. monad_inv. simpl.
  eapply match_map_vars_tag_same.
  - eapply VerilogSMTBijection.combine_different_tag_left;
      eauto using verilog_to_smt_only_tag;
      discriminate.
  - eapply VerilogToSMTCorrect.verilog_to_smt_map_match.
    eassumption.
Qed.

Lemma equivalence_query_map_match_right v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  SMT.match_map_vars TaggedVariable.VerilogRight (SMT.nameMap smt) (Verilog.modVariables v2).
Proof.
  unfold equivalence_query.
  intros. monad_inv. simpl.
  eapply match_map_vars_tag_same.
  - eapply VerilogSMTBijection.combine_different_tag_right;
      eauto using verilog_to_smt_only_tag;
      discriminate.
  - eapply VerilogToSMTCorrect.verilog_to_smt_map_match.
    eassumption.
Qed.

Theorem equivalence_query_unsat_correct v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ (SMT.query smt)) ->
  equivalent_behaviour v1 v2.
Proof.
  intros Hquery Hunsat.
  apply no_counterexample_equivalent_iff.
  intros e1 e2 Hcounterexample.
  remember (SMT.valuation_of_executions (SMT.nameMap smt) e1 e2) as ρ.
  assert (Verilog.module_inputs v1 = Verilog.module_inputs v2) as Hinputs_match. {
    unfold equivalence_query in *. monad_inv. simpl in *.
    assumption.
  }
  assert (Verilog.module_outputs v1 = Verilog.module_outputs v2) as Houtputs_match. {
    unfold equivalence_query in *. monad_inv. simpl in *.
    assumption.
  }
  assert (list_subset (Verilog.module_body_writes (Verilog.modBody v1)) (Verilog.modVariables v1)) as Hwrites_in_vars1. {
    unfold equivalence_query in *. monad_inv. simpl in *.
    clear E5 E6. (* These prevent the next monad_inv from running. Eww *)
    unfold VerilogToSMT.verilog_to_smt in *. monad_inv. simpl in *.
    assumption.
  }
  assert (list_subset (Verilog.module_body_writes (Verilog.modBody v2)) (Verilog.modVariables v2)) as Hwrites_in_vars2. {
    unfold equivalence_query in *. monad_inv. simpl in *.
    clear E5 E6. (* These prevent the next monad_inv from running. Eww *)
    unfold VerilogToSMT.verilog_to_smt in *. monad_inv. simpl in *.
    assumption.
  }
  erewrite
    <- counterexample_execution_rewrite_left,
    <- counterexample_execution_rewrite_right
    in Hcounterexample.
  - eapply Hunsat with (ρ := ρ).
    subst ρ.
    eapply equivalence_query_execution_spec; eauto.
  - assumption.
  - assumption.
  - assumption.
  - intros var Hvar_in.
    pose proof equivalence_query_map_match_right as Hmatch.
    insterU Hmatch. unfold SMT.match_map_vars in Hmatch.
    eapply execution_of_valuation_inverse_right.
    + (* defined_value_for right-tagged vars *)
      eapply VerilogToSMTCorrect.defined_value_for_impl; [apply Hmatch|].
      unfold equivalence_query in Hquery. monad_inv. simpl in *.
      eapply valid_execution_all_vars_defined; cycle 1.
      * unfold counterexample_execution in Hcounterexample.
        decompose record Hcounterexample. assumption.
      * unfold counterexample_execution in Hcounterexample.
        decompose record Hcounterexample.
        eapply defined_match_on_defined_value_right.
        rewrite <- Hinputs_match.
        eassumption.
      * eassumption.
    + eapply Hmatch. assumption.
  - assumption.
  - intros var Hvar_in.
    pose proof equivalence_query_map_match_left as Hmatch.
    insterU Hmatch. unfold SMT.match_map_vars in Hmatch.
    eapply execution_of_valuation_inverse_left.
    + (* defined_value_for left-tagged vars *)
      eapply VerilogToSMTCorrect.defined_value_for_impl; [apply Hmatch|].
      unfold equivalence_query in Hquery. monad_inv. simpl in *.
      eapply valid_execution_all_vars_defined; cycle 1.
      * unfold counterexample_execution in Hcounterexample.
        decompose record Hcounterexample. assumption.
      * unfold counterexample_execution in Hcounterexample.
        decompose record Hcounterexample.
        eapply defined_match_on_defined_value_left.
        eassumption.
      * eassumption.
    + eapply Hmatch. assumption.
Qed.

Print Assumptions equivalence_query_unsat_correct.
Print Assumptions equivalence_query_sat_correct.
