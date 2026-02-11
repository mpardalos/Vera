From vera Require Import Verilog.
From vera Require Import VerilogSMT.
From vera Require Import SMTQueries.
Import (coercions) SMT.
From vera Require Import Common.
Import (coercions) VerilogSMTBijection.
From vera Require Import Bitvector.
From vera Require VerilogToSMT.
From vera Require VerilogToSMT.VerilogToSMTCorrect.
From vera Require Import VerilogToSMT.Match.
From vera Require Import VerilogEquivalence.
From vera Require VerilogSemantics.
From vera Require VerilogSort.
From vera Require Import Tactics.
From vera Require Import Decidable.

Import VerilogSemantics.
Import VerilogSemantics.CombinationalOnly.
Import Equivalence.

From Stdlib Require Import Relations.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Lia.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Classical.
From Stdlib Require Import ZArith.
From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Setoid.

From Equations Require Import Equations.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Data.Monads.OptionMonad.
From ExtLib Require Import Data.List.

Import (notations) RegisterState.
Import MonadLetNotation.
Import ListNotations.
Import EqNotations.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope monad_scope.

Import SigTNotations.

Ltac decompose_all_records :=
  repeat match goal with
         | [ H : _ |- _ ] => progress (decompose record H); clear H
	 end.

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
  /\ e1 =!!(Verilog.module_inputs v1)!!= e2
  /\ ~ (e1 =(Verilog.module_outputs v1)= e2).

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
  Permutation (Verilog.module_body_writes (Verilog.modBody v)) (Verilog.module_outputs v) ->
  VerilogToSMT.all_vars_driven v ->
  valid_execution v (SMT.execution_of_valuation tag m ρ) ->
  verilog_smt_match_states_partial
    (fun var => In var (Verilog.modVariables v))
    tag m (SMT.execution_of_valuation tag m ρ) ρ.
Proof.
  unfold verilog_smt_match_states_partial.
  intros Houtputs Hdriven Hvalid.
  apply VerilogToSMTCorrect.valid_execution_complete in Hvalid; [|assumption|eassumption].
  unfold complete_execution, RegisterState.has_value_for in Hvalid.
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
  ~ (SMT.execution_of_valuation TaggedVariable.VerilogLeft m ρ =!!(
       vars
     )!!= SMT.execution_of_valuation TaggedVariable.VerilogRight m ρ).
Proof.
  unfold smt_some_distinct_values.
  rewrite RegisterState.defined_match_on_iff, List.Exists_exists.
  intros [var [Hin Hsmt_distinct]] Hcontra.
  edestruct Hcontra as [bv [Hleft Hright]]; [eassumption|]. clear Hcontra.
  apply execution_of_valuation_inv in Hleft.
  apply execution_of_valuation_inv in Hright.
  unfold smt_distinct_value in Hsmt_distinct.

  decompose_all_records. crush.
Qed.

Lemma smt_all_same_inputs_execution_match v1 v2 m ρ :
  Permutation (Verilog.module_body_writes (Verilog.modBody v1)) (Verilog.module_outputs v1) ->
  Permutation (Verilog.module_body_writes (Verilog.modBody v2)) (Verilog.module_outputs v2) ->
  VerilogToSMT.all_vars_driven v1 ->
  VerilogToSMT.all_vars_driven v2 ->
  valid_execution v1 (SMT.execution_of_valuation TaggedVariable.VerilogLeft m ρ) ->
  valid_execution v2 (SMT.execution_of_valuation TaggedVariable.VerilogRight m ρ) ->
  Verilog.module_inputs v1 = Verilog.module_inputs v2 ->
  smt_all_same_values (Verilog.module_inputs v1) m ρ ->
  (SMT.execution_of_valuation TaggedVariable.VerilogLeft m ρ) =!!(
    Verilog.module_inputs v1
  )!!= (SMT.execution_of_valuation TaggedVariable.VerilogRight m ρ).
Proof.
  unfold smt_all_same_values.
  rewrite RegisterState.defined_match_on_iff.
  intros Houtputs1 Houtputs2 Hdriven1 Hdriven2 Hvalid1 Hvalid2 Hmatch_inputs Hsmt_same var Hvar_in.
  edestruct (valid_execution_of_valuation_match v1) as
    [smtName_left [Hm_left [xbv_l val_l Hsmtval_l Hverilogval_l Hmatchvals_l]]];
    [ assumption
    | eassumption
    | eassumption
    | apply Verilog.module_input_in_vars; eassumption
    |].
  edestruct (valid_execution_of_valuation_match v2) as
    [smtName_right [Hm_right [xbv_r val_r Hsmtval_r Hverilogval_r Hmatchvals_r]]];
    [ assumption
    | eassumption
    | eassumption
    | apply Verilog.module_input_in_vars; rewrite <- Hmatch_inputs; eassumption
    |].
  rewrite Hverilogval_l, Hverilogval_r.
  replace val_r with val_l in *.
  - inv Hmatchvals_l. inv Hmatchvals_r.
    crush.
  - pose proof smt_same_values_eq as Heq.
    insterU Heq.
    rewrite Hsmtval_l, Hsmtval_r in Heq.
    inv Heq. reflexivity.
Qed.

Lemma execution_defined_match_smt_all_same_values vars m ρ :
  (SMT.execution_of_valuation TaggedVariable.VerilogLeft m ρ) =!!(
    vars
  )!!= (SMT.execution_of_valuation TaggedVariable.VerilogRight m ρ) ->
  smt_all_same_values vars m ρ.
Proof.
  rewrite RegisterState.defined_match_on_iff.
  unfold smt_all_same_values, smt_same_value.
  rewrite List.Forall_forall.
  intros H var Hvar_in.
  insterU H. destruct H as [bv [Hlookup_left Hlookup_right]].

  eapply execution_of_valuation_inv in Hlookup_left.
  decompose record Hlookup_left. clear Hlookup_left.

  eapply execution_of_valuation_inv in Hlookup_right.
  decompose record Hlookup_right. clear Hlookup_right.
  eauto 10.
Qed.

Lemma valid_execution_smt_all_outputs_have_values v tag m ρ :
  Permutation (Verilog.module_body_writes (Verilog.modBody v)) (Verilog.module_outputs v) ->
  VerilogToSMT.all_vars_driven v ->
  valid_execution v (SMT.execution_of_valuation tag m ρ) ->
  smt_all_have_values tag (Verilog.module_outputs v) m ρ.
Proof.
  intros Houtputs Hvars_driven Hvalid.
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
  RegisterState.defined_value_for C e1 ->
  RegisterState.defined_value_for C e2 ->
  ~ (e1 =!!{ C }!!= e2) ->
  execution_some_distinct_value C e1 e2.
Proof.
  rewrite RegisterState.defined_match_on_iff.
  unfold
    execution_some_distinct_value,
    RegisterState.defined_value_for
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
  destruct Hvalues_left as [bv_left Hbv_left].
  destruct Hvalues_right as [bv_right Hbv_right].
  rewrite Hbv_left in *. clear Hbv_left.
  rewrite Hbv_right in *. clear Hbv_right.
  exists bv_left, bv_right.
  repeat split; eauto; [].
  intro contra. subst bv_right.
  apply Hvar. clear Hvar. crush.
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
  intro contra. inv contra.
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
  RegisterState.execution_defined_match_on C e1 e2 ->
  RegisterState.defined_value_for C e1.
Proof. unfold RegisterState.execution_defined_match_on. crush. Qed.

Lemma defined_match_on_defined_value_right C e1 e2 :
  RegisterState.execution_defined_match_on C e1 e2 ->
  RegisterState.defined_value_for C e2.
Proof.
  unfold RegisterState.execution_defined_match_on.
  intros [Hmatch Hdefined].
  rewrite <- Hmatch.
  apply Hdefined.
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

(* TODO: Move me to Match.v *)
Lemma execution_of_valuation_all_defined C tag m ρ :
  RegisterState.has_value_for C (SMT.execution_of_valuation tag m ρ) ->
  RegisterState.defined_value_for C (SMT.execution_of_valuation tag m ρ).
Proof.
  unfold RegisterState.has_value_for, RegisterState.defined_value_for.
  intros * Hhas_value var HC.
  insterU Hhas_value. destruct Hhas_value as [xbv Hlookup].
  rewrite Hlookup.
  unfold SMT.execution_of_valuation in Hlookup.
  autodestruct_eqn E. crush.
Qed.

Lemma valid_execution_has_value_for_writes v e :
  Permutation (Verilog.module_body_writes (Verilog.modBody v)) (Verilog.module_outputs v) ->
  valid_execution v e ->
  RegisterState.has_value_for
    (fun var : Verilog.variable => In var (Verilog.module_body_writes (Verilog.modBody v)))
    e.
Proof.
  unfold valid_execution. intros Houtputs Hvalid. 
  decompose record Hvalid. setoid_rewrite Houtputs. assumption.
Qed.

Lemma valid_execution_has_value_for_inputs v e :
  valid_execution v e ->
  RegisterState.has_value_for
    (fun var : Verilog.variable => In var (Verilog.module_inputs v))
    e.
Proof.
  unfold valid_execution. intros Hvalid. 
  decompose record Hvalid. assumption.
Qed.

Import Setoid.

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
  assert (Permutation (Verilog.module_body_writes (Verilog.modBody v1)) (Verilog.module_outputs v1)) as Houtputs1.
  {
    unfold equivalence_query in *. monad_inv.
    pose proof e1 as e1'.
    pose proof e2 as e2'.
    unfold VerilogToSMT.verilog_to_smt in e1'.
    unfold VerilogToSMT.verilog_to_smt in e2'.
    monad_inv.
    assumption.
  }
  assert (Permutation (Verilog.module_body_writes (Verilog.modBody v2)) (Verilog.module_outputs v2)) as Houtputs2.
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
  split; intros H; decompose record H; clear H.
  - repeat split.
    + assumption.
    + assumption.
    + eapply smt_all_same_inputs_execution_match;
        eassumption.
    + apply execution_of_valuation_all_defined.
      apply valid_execution_has_value_for_inputs.
      assumption.
    + apply smt_distinct_values_not_defined_match in H3.
      intro contra. apply H3. clear H3.
      unfold "_ =!!( _ )!!= _". split; [assumption|].
      setoid_replace
        (fun var : Verilog.variable => In var (Verilog.module_outputs v1))
      	with
        (fun var : Verilog.variable => In var (Verilog.module_body_writes (Verilog.modBody v1)))
	by (unfold pointwise_relation, Basics.impl; eauto using all_driven_outputs_driven).
      apply execution_of_valuation_all_defined.
      apply valid_execution_has_value_for_writes; assumption.
  - repeat split.
    + eassumption.
    + eassumption.
    + apply execution_defined_match_smt_all_same_values.
      assumption.
    + apply not_execution_defined_match_on_smt_some_distinct_values; [].
      apply not_defined_match_some_distinct.
      * setoid_replace
          (fun var : Verilog.variable => In var (Verilog.module_outputs v1))
        	with
          (fun var : Verilog.variable => In var (Verilog.module_body_writes (Verilog.modBody v1)))
	  by (unfold pointwise_relation, Basics.impl; eauto using all_driven_outputs_driven).
	apply execution_of_valuation_all_defined.
        apply valid_execution_has_value_for_writes; assumption.
      * rewrite Hmatch_outputs, Hmatch_inputs in *.
        setoid_replace
          (fun var : Verilog.variable => In var (Verilog.module_outputs v2))
        	with
          (fun var : Verilog.variable => In var (Verilog.module_body_writes (Verilog.modBody v2)))
	  by (unfold pointwise_relation, Basics.impl; eauto using all_driven_outputs_driven).
	apply execution_of_valuation_all_defined.
        apply valid_execution_has_value_for_writes; assumption.
      * unfold "_ =!!( _ )!!= _". intuition eauto.
    + eapply valid_execution_smt_all_outputs_have_values;
        eassumption.
    + rewrite Hmatch_outputs.
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

Local Open Scope verilog.

Global Instance Proper_limit_to_regs regs :
  Proper
    (RegisterState.match_on (fun var => In var regs) ==> eq)
    (RegisterState.limit_to_regs regs).
Proof.
  repeat intro.
  unfold "//", "_ =( _ )= _" in *.
  apply functional_extensionality_dep. intro var.
  autodestruct; eauto.
Qed.

Global Instance Proper_valid_execution v :
  Proper
    (RegisterState.match_on (fun var => In var (Verilog.module_inputs v ++ Verilog.module_outputs v)) ==> iff)
    (valid_execution v).
Proof.
  repeat intro.
  unfold valid_execution.
  RegisterState.unpack_match_on.
  rename_match (_ =( Verilog.module_inputs _ )= _ ) into inputs_same.
  rename_match (_ =( Verilog.module_outputs _ )= _ ) into outputs_same.
  split.
  - intros H. decompose record H; clear H.
    RegisterState.unpack_match_on.
    rewrite inputs_same in *; clear inputs_same.
    rewrite outputs_same in *; clear outputs_same.
    exists x0. repeat split; RegisterState.unpack_match_on; try eassumption.
  - intros H. decompose record H; clear H.
    RegisterState.unpack_match_on.
    rewrite <- inputs_same in *; clear inputs_same.
    rewrite <- outputs_same in *; clear outputs_same.
    exists x0. repeat split; RegisterState.unpack_match_on; try eassumption.
Qed.

Lemma transfer_execution v e :
  clean_module v ->
  RegisterState.defined_value_for (fun var => In var (Verilog.module_inputs v)) e ->
  exists e', e =!!( Verilog.module_inputs v )!!= e' /\ v ⇓ e'.
Proof. Admitted.

Lemma clean_defined_outputs v e :
  clean_module v ->
  v ⇓ e ->
  RegisterState.defined_value_for
    (fun var : Verilog.variable => In var (Verilog.module_outputs v)) e.
Proof. Admitted.

Lemma execution_congruent v e1 e2 :
  v ⇓ e1 -> v ⇓ e2 ->
  e1 =( Verilog.module_inputs v )= e2 ->
  e1 =( Verilog.module_outputs v )= e2.
Proof.
  unfold "⇓".
  intros Hadmit1 Hadmit2 Hinput_match.
  decompose record Hadmit1. clear Hadmit1.
  decompose record Hadmit2. clear Hadmit2.
  match goal with
  | [ H : run_vmodule v (e1 // Verilog.module_inputs v) = Some ?x |- _ ] =>
    rename H into Hrun1; rename x into e1'
  end.
  match goal with
  | [ H : run_vmodule v (e2 // Verilog.module_inputs v) = Some ?x |- _ ] =>
    rename H into Hrun2; rename x into e2'
  end.
  rewrite <- Hinput_match in Hrun2.
  replace e2' with e1' in * by congruence.
  RegisterState.unpack_match_on.
  transitivity e1'.
  - symmetry. assumption.
  - assumption.
Qed.

Lemma no_counterexample_equivalent_iff v1 v2 :
  Verilog.module_inputs v1 = Verilog.module_inputs v2 ->
  Verilog.module_outputs v1 = Verilog.module_outputs v2 ->
  clean_module v1 ->
  clean_module v2 ->
  (forall e1 e2, ~ counterexample_execution v1 e1 v2 e2) <-> (equivalent_behaviour v1 v2).
Proof.
  intros Hinput_match Houtput_match Hclean1 Hclean2.
  unfold counterexample_execution.
  split. 
  - intros H. constructor; try assumption; [idtac].
    intros e Hno_exes.
    split; intros He.
    + RegisterState.unpack_defined_value_for.
      destruct (transfer_execution v2 e) as [e' [Hinput_values He']];
        [assumption|rewrite <- Hinput_match; assumption|]. 
      rewrite <- Hinput_match in Hinput_values.
      specialize (H e e').
      apply not_and_or in H. destruct H; [contradiction|].
      apply not_and_or in H. destruct H; [contradiction|].
      apply not_and_or in H. destruct H; [contradiction|].
      apply NNPP in H.
      eapply Proper_valid_execution; [|eassumption].
      rewrite <- Hinput_match, <- Houtput_match.
      destruct Hinput_values.
      RegisterState.unpack_match_on; assumption.
    + RegisterState.unpack_defined_value_for.
      destruct (transfer_execution v1 e) as [e' [Hinput_values He']];
        [assumption|assumption|]. 
      (* rewrite Hinput_match in Hinput_values. *)
      symmetry in Hinput_values.
      specialize (H e' e).
      apply not_and_or in H. destruct H; [contradiction|].
      apply not_and_or in H. destruct H; [contradiction|].
      apply not_and_or in H. destruct H; [contradiction|].
      apply NNPP in H.
      destruct Hinput_values.
      setoid_replace e with e'
        using relation (RegisterState.match_on (fun var => In var (Verilog.module_inputs v1 ++ Verilog.module_outputs v1)))
	by (RegisterState.unpack_match_on; symmetry; assumption).
      assumption.
  - intros [] e1 e2 Hcontra. decompose record Hcontra. clear Hcontra.
    erewrite <- execution_match0 in H1; cycle 1. {
      RegisterState.unpack_defined_value_for.
      - destruct H0. rewrite <- H0. assumption.
      - rewrite Houtput_match.
        apply clean_defined_outputs; assumption.
    }
    apply H3. apply execution_congruent.
    + assumption.
    + assumption.
    + destruct H0. assumption.
Qed.

Print Assumptions no_counterexample_equivalent_iff.

Lemma not_equivalent_counterexample_iff v1 v2 :
  Verilog.module_inputs v1 = Verilog.module_inputs v2 ->
  Verilog.module_outputs v1 = Verilog.module_outputs v2 ->
  clean_module v1 ->
  clean_module v2 ->
  (exists e1 e2, counterexample_execution v1 e1 v2 e2) <-> (~ equivalent_behaviour v1 v2).
Proof.
  intros Hinput_match Houtput_match Hclean1 Hclean2.
  setoid_rewrite <- no_counterexample_equivalent_iff; try assumption; [idtac].
  split.
  - intros [e1 [e2 H1]] H2. eapply H2. eapply H1.
  - intros H1.
    apply not_all_ex_not in H1. destruct H1 as [e1 H1].
    apply not_all_ex_not in H1. destruct H1 as [e2 H1].
    apply NNPP in H1.
    exists e1, e2. apply H1.
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
  RegisterState.defined_value_for (fun var => exists n, m (TaggedVariable.VerilogLeft, var) = Some n) e1 ->
  (exists n, m (TaggedVariable.VerilogLeft, var) = Some n) ->
  SMT.execution_of_valuation TaggedVariable.VerilogLeft m (SMT.valuation_of_executions m e1 e2) var =
    e1 var.
Proof.
  unfold SMT.execution_of_valuation, SMT.valuation_of_executions.
  intros Hdefined Hexists.
  unfold RegisterState.defined_value_for in Hdefined.
  insterU Hdefined.
  destruct Hexists as [n Hm].
  rewrite Hm.
  rewrite VerilogSMTBijection.bij_wf in Hm.
  rewrite Hm.
  rewrite <- VerilogSMTBijection.bij_wf in Hm.

  edestruct Hdefined as [bv Hbv]. clear Hdefined.
  rewrite Hbv, XBV.xbv_bv_inverse.

  autodestruct; [|contradiction].
  rewrite <- eq_rect_eq.
  reflexivity.
Qed.

Lemma execution_of_valuation_inverse_right (m : VerilogSMTBijection.t) var e1 e2 :
  RegisterState.defined_value_for (fun var => exists n, m (TaggedVariable.VerilogRight, var) = Some n) e2 ->
  (exists n, m (TaggedVariable.VerilogRight, var) = Some n) ->
  SMT.execution_of_valuation TaggedVariable.VerilogRight m (SMT.valuation_of_executions m e1 e2) var =
    e2 var.
Proof.
  unfold SMT.execution_of_valuation, SMT.valuation_of_executions.
  intros Hdefined Hexists.
  unfold RegisterState.defined_value_for in Hdefined.
  insterU Hdefined.
  destruct Hexists as [n Hm].
  rewrite Hm.
  rewrite VerilogSMTBijection.bij_wf in Hm.
  rewrite Hm.
  rewrite <- VerilogSMTBijection.bij_wf in Hm.

  edestruct Hdefined as [bv Hbv]. clear Hdefined.
  rewrite Hbv, XBV.xbv_bv_inverse.

  autodestruct; [|contradiction].
  rewrite <- eq_rect_eq.
  reflexivity.
Qed.

Lemma limit_to_regs_rewrite vars e1 e2 :
  (forall var, In var vars -> e1 var = e2 var) ->
  RegisterState.limit_to_regs vars e1 = RegisterState.limit_to_regs vars e2.
Proof.
  unfold RegisterState.limit_to_regs.
  intros Heq.
  apply functional_extensionality_dep.
  intros var. autodestruct; crush.
Qed.

Lemma valid_execution_rewrite v e1 e2 :
  e1 =(Verilog.module_inputs v ++ Verilog.module_outputs v)= e2 ->
  valid_execution v e1 <-> valid_execution v e2.
Proof.
  intros Heq.
  unfold run_vmodule, mk_initial_state.
  rewrite Heq. reflexivity.
Qed.

Lemma counterexample_execution_rewrite_left v e1 e1' v2 e2 :
  e1 =( Verilog.module_inputs v ++ Verilog.module_outputs v )= e1' ->
  counterexample_execution v e1 v2 e2 <-> counterexample_execution v e1' v2 e2.
Proof.
  unfold counterexample_execution.
  intros H.
  split; intros [Hvalid1 [Hvalid2 [Hdefined_in Hnot_defined_out]]];
    repeat split; try eassumption.
  - rewrite H in Hvalid1. assumption.
  - RegisterState.unpack_match_on. transitivity e1.
    + symmetry. assumption.
    + destruct Hdefined_in. assumption.
  - RegisterState.unpack_match_on.
    rewrite <- H.
    destruct Hdefined_in. assumption.
  - intro. contradict Hnot_defined_out.
    RegisterState.unpack_match_on.
    transitivity e1'; assumption.
  - rewrite H. assumption.
  - RegisterState.unpack_match_on.
    transitivity e1'.
    + assumption.
    + destruct Hdefined_in. assumption.
  - RegisterState.unpack_match_on.
    rewrite H.
    destruct Hdefined_in. assumption.
  - intro. contradict Hnot_defined_out.
    RegisterState.unpack_match_on.
    transitivity e1.
    + symmetry. assumption.
    + assumption.
Qed.

Lemma counterexample_execution_rewrite_right v1 e1 v2 e2 e2' :
  Verilog.module_inputs v1 = Verilog.module_inputs v2 ->
  Verilog.module_outputs v1 = Verilog.module_outputs v2 ->
  e2 =( Verilog.module_inputs v2 ++ Verilog.module_outputs v2 )= e2' ->
  counterexample_execution v1 e1 v2 e2 <-> counterexample_execution v1 e1 v2 e2'.
Proof.

  unfold counterexample_execution.
  intros inputs_same outputs_same H.
  split; intros [Hvalid1 [Hvalid2 [Hdefined_in Hnot_defined_out]]];
    repeat split; try eassumption.
  - rewrite H in Hvalid2. assumption.
  - rewrite inputs_same in *.
    RegisterState.unpack_match_on. transitivity e2.
    + destruct Hdefined_in. assumption.
    + assumption.
  - rewrite inputs_same in *.
    RegisterState.unpack_match_on.
    destruct Hdefined_in. assumption.
  - rewrite outputs_same in *.
    intro. contradict Hnot_defined_out.
    RegisterState.unpack_match_on.
    transitivity e2'.
    + assumption.
    + symmetry. assumption.
  - rewrite H. assumption.
  - rewrite inputs_same in *.
    RegisterState.unpack_match_on.
    transitivity e2'.
    + destruct Hdefined_in. assumption.
    + symmetry. assumption.
  - RegisterState.unpack_match_on.
    destruct Hdefined_in. assumption.
  - rewrite outputs_same in *.
    intro. contradict Hnot_defined_out.
    RegisterState.unpack_match_on.
    transitivity e2.
    + assumption.
    + assumption.
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
  RegisterState.defined_value_for (fun var => List.In var (Verilog.module_inputs v)) e ->
  RegisterState.defined_value_for (fun var => List.In var (Verilog.modVariables v)) e.
Proof.
  intros.
  assert (VerilogToSMT.all_vars_driven v) as Hdriven
    by (unfold VerilogToSMT.verilog_to_smt in *; monad_inv; assumption).
  eapply RegisterState.defined_value_for_impl.
  - eapply List.Forall_forall.
    eapply Hdriven.
  - RegisterState.unpack_defined_value_for.
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

Record verilog_to_smt_checked (v : Verilog.vmodule) := MkVerilogToSMTChecked {
    io_disjoint : disjoint (Verilog.module_inputs v) (Verilog.module_outputs v);
    only_reads_inputs : list_subset (Verilog.module_body_reads (Verilog.modBody v)) (Verilog.module_inputs v);
    all_vars_driven : VerilogToSMT.all_vars_driven v;
    no_duplicate_writes : NoDup (Verilog.module_body_writes (Verilog.modBody v));
    no_duplicate_outputs : NoDup (Verilog.module_outputs v);
    writes_outputs : Permutation (Verilog.module_body_writes (Verilog.modBody v)) (Verilog.module_outputs v);
    all_module_items_clean : Forall clean_module_item_structure (Verilog.modBody v);
    sortable : VerilogSort.vmodule_sortable v;
}.

Lemma verilog_to_smt_checks tag start v smt :
  VerilogToSMT.verilog_to_smt tag start v = inr smt ->
  verilog_to_smt_checked v.
Proof.
  intros H.
  unfold VerilogToSMT.verilog_to_smt in H. monad_inv.
  constructor; assumption.
Qed.

Record equivalence_query_checked (v1 v2 : Verilog.vmodule) := MkEquivalenceQueryChecked {
  verilog_to_smt_eqn1 : exists tag start smt, VerilogToSMT.verilog_to_smt tag start v1 = inr smt;
  verilog_to_smt_eqn2 : exists tag start smt, VerilogToSMT.verilog_to_smt tag start v2 = inr smt;
  verilog_to_smt_checked1 : verilog_to_smt_checked v1;
  verilog_to_smt_checked2 : verilog_to_smt_checked v2;
  inputs_match : Verilog.module_inputs v1 = Verilog.module_inputs v2;
  outputs_match : Verilog.module_outputs v1 = Verilog.module_outputs v2;
}.

Lemma equivalence_query_checks v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  equivalence_query_checked v1 v2.
Proof.
  intros H.
  unfold equivalence_query in H. monad_inv.
  constructor; eauto using verilog_to_smt_checks.
Qed.

Lemma verilog_to_smt_clean tag start v smt :
  VerilogToSMT.verilog_to_smt tag start v = inr smt ->
  clean_module v.
Proof.
  intros H. eapply verilog_to_smt_checks in H. destruct H.
  apply clean_module_statically; eassumption.
Qed.

Theorem equivalence_query_unsat_correct v1 v2 smt :
  equivalence_query v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ (SMT.query smt)) ->
  equivalent_behaviour v1 v2.
Proof.
  intros Hquery Hunsat.
  destruct (equivalence_query_checks v1 v2 smt)
    as [[? [? [? ?]]] [? [? [? ?]]] [] [] inputs_match outputs_match];
    [assumption|].
  apply no_counterexample_equivalent_iff; eauto using verilog_to_smt_clean.
  intros e1 e2 Hcounterexample.
  remember (SMT.valuation_of_executions (SMT.nameMap smt) e1 e2) as ρ.
  (* assert (VerilogSort.vmodule_sortable v1). {
   *   unfold equivalence_query in *. monad_inv. assumption.
   * }
   * assert (VerilogSort.vmodule_sortable v2). {
   *   unfold equivalence_query in *. monad_inv. assumption.
   * } *)
  erewrite
    <- counterexample_execution_rewrite_left,
    <- counterexample_execution_rewrite_right
    in Hcounterexample.
  - eapply Hunsat with (ρ := ρ).
    subst ρ.
    eapply equivalence_query_execution_spec; eauto.
  - assumption.
  - assumption.
  - intros var Hvar_in.
    pose proof equivalence_query_map_match_right as Hmatch.
    insterU Hmatch. unfold SMT.match_map_vars in Hmatch.
    eapply execution_of_valuation_inverse_right.
    + (* defined_value_for right-tagged vars *)
      eapply RegisterState.defined_value_for_impl; [apply Hmatch|].
      unfold equivalence_query in Hquery. monad_inv. simpl in *.
      eapply valid_execution_all_vars_defined; cycle 1.
      * unfold counterexample_execution in Hcounterexample.
        decompose record Hcounterexample. assumption.
      * unfold counterexample_execution in Hcounterexample.
        decompose record Hcounterexample.
        eapply defined_match_on_defined_value_right.
        rewrite <- inputs_match.
	decompose_all_records.
	split; [now apply H2|].
	apply execution_of_valuation_all_defined.
        apply valid_execution_has_value_for_inputs.
        assumption.
      * eassumption.
    + eapply Hmatch.
      rewrite in_app_iff in Hvar_in.
      destruct Hvar_in; auto using Verilog.module_input_in_vars, Verilog.module_outputs_in_vars.
  - intros var Hvar_in.
    pose proof equivalence_query_map_match_left as Hmatch.
    insterU Hmatch. unfold SMT.match_map_vars in Hmatch.
    eapply execution_of_valuation_inverse_left.
    + (* defined_value_for left-tagged vars *)
      eapply RegisterState.defined_value_for_impl; [apply Hmatch|].
      unfold equivalence_query in Hquery. monad_inv. simpl in *.
      eapply valid_execution_all_vars_defined; cycle 1.
      * unfold counterexample_execution in Hcounterexample.
        decompose record Hcounterexample. assumption.
      * unfold counterexample_execution in Hcounterexample.
        decompose record Hcounterexample.
        eapply defined_match_on_defined_value_right.
	decompose_all_records.
	split; [symmetry; now eapply H2|].
	destruct H2. rewrite <- H2. assumption.
      * eassumption.
    + eapply Hmatch.
      rewrite in_app_iff in Hvar_in.
      destruct Hvar_in; auto using Verilog.module_input_in_vars, Verilog.module_outputs_in_vars.
Qed.

Lemma assignment_forwarding_equivalent_behaviour v1 v2 :
  AssignmentForwarding.forward_assignments v1 = inr v2 ->
  equivalent_behaviour v1 v2.
Proof. Admitted.

Theorem equivalence_query_general_unsat_correct v1 v2 smt :
  equivalence_query_general v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ (SMT.query smt)) ->
  equivalent_behaviour v1 v2.
Proof.
  unfold equivalence_query_general.
  intros. monad_inv.
  transitivity v. {
    apply assignment_forwarding_equivalent_behaviour. assumption.
  }
  symmetry. transitivity v0. {
    apply assignment_forwarding_equivalent_behaviour. assumption.
  } symmetry.
  eapply equivalence_query_unsat_correct; eassumption.
Qed.

Theorem equivalence_query_general_sat_correct v1 v2 smt ρ :
  equivalence_query_general v1 v2 = inr smt ->
  satisfied_by ρ (SMT.query smt) ->
  exists e1 e2, counterexample_execution v1 e1 v2 e2.
Proof.
  unfold equivalence_query_general.
  intros Hquery Hsat. monad_inv.
  rename_match (AssignmentForwarding.forward_assignments v1 = inr _) into Hforward1.
  rename_match (AssignmentForwarding.forward_assignments v2 = inr _) into Hforward2.
  rename_match (equivalence_query _ _ = inr _) into Hquery.
  destruct (equivalence_query_checks v v0 smt)
    as [[? [? [? ?]]] [? [? [? ?]]] [] [] inputs_match outputs_match];
    [assumption|].
  edestruct (assignment_forwarding_equivalent_behaviour v1 v); [eassumption|].
  edestruct (assignment_forwarding_equivalent_behaviour v2 v0); [eassumption|].

  apply not_equivalent_counterexample_iff; [congruence|congruence|assumption|assumption|].
  intro Hequiv.
  eapply equivalence_query_sat_correct in Hquery; [|eassumption].
  assert (equivalent_behaviour v v0) as Hequiv0. {
    etransitivity. {
      symmetry. apply assignment_forwarding_equivalent_behaviour. apply Hforward1.
    }
    etransitivity. { apply Hequiv. }
    apply assignment_forwarding_equivalent_behaviour. apply Hforward2.
  } contradict Hequiv0.

  apply not_equivalent_counterexample_iff; [congruence|congruence|assumption|assumption|].
  eexists. eexists. apply Hquery.
Qed.

Print Assumptions equivalence_query_general_unsat_correct.
Print Assumptions equivalence_query_general_sat_correct.
