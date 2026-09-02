From vera Require Import Verilog.
From vera Require Import Variables.
From vera Require Import VerilogSMT.
From vera Require Import SMTQueries.
From vera Require Import Common.
From vera Require Import Bitvector.
From vera Require VerilogToSMT.
From vera Require VerilogToSMT.VerilogToSMTCorrect.
From vera Require Import VerilogEquivalence.
From vera Require VerilogSemantics.
Import VerilogSemantics.Sort (vmodule_sortable).
From vera Require Import Tactics.
From vera Require Import Decidable.

Import VerilogSemantics.
Import VerilogSemantics.CombinationalOnly.
Import DefinedEquivalence.

From Stdlib Require Import Relations.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Lia.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Classical.
From Stdlib Require Import ZArith.
From Stdlib Require Import Nnat.
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
Import Verilog.Notations.

Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
Local Open Scope verilog_scope.

Import SigTNotations.

Ltac decompose_all_records :=
  repeat match goal with
         | [ H : _ |- _ ] => progress (decompose record H); clear H
	 end.

Definition smt_same_value var (ρ : SMTLib.valuation) :=
  ρ (verilog_to_smt_var VerilogLeft var) =
  ρ (verilog_to_smt_var VerilogRight var).

Definition smt_all_same_values (vars : VarSet.t) (ρ : SMTLib.valuation) :=
  forall var, VarSet.In var vars -> smt_same_value var ρ.

Lemma smt_all_same_values_empty_iff {ρ} : smt_all_same_values VarSet.empty ρ <-> True.
Proof. split; [trivial|]. intros var Hvar_in. VarSet.setdec. Qed.

Lemma smt_all_same_values_add var vars :
  pointwise_relation SMTLib.valuation iff
  (smt_all_same_values (VarSet.add var vars))
  (fun ρ => smt_same_value var ρ /\ smt_all_same_values vars ρ).
Proof.
  unfold smt_all_same_values.
  split.
  - intros H.
    split.
    + apply H. VarSet.setdec.
    + intros var' Hvar'. apply H. VarSet.setdec.
  - intros [Hhd Htl] var' Hvar'.
    destruct (dec (var' = var)).
    + subst. apply Hhd.
    + apply Htl. VarSet.setdec.
Qed.

Definition smt_distinct_value (var : Var.t) (ρ : SMTLib.valuation) :=
  ρ (verilog_to_smt_var VerilogLeft var) <>
  ρ (verilog_to_smt_var VerilogRight var).

Definition smt_some_distinct_values (vars : VarSet.t) (ρ : SMTLib.valuation) :=
  exists var, VarSet.In var vars /\ smt_distinct_value var ρ.

Definition counterexample_valuation {i o} (v1 v2 : Verilog.vmodule i o) ρ :=
  smt_all_same_values (VarSet.of_list i) ρ
  /\ smt_some_distinct_values (VarSet.of_list o) ρ
  /\ v1 ⇓ execution_of_valuation VerilogLeft ρ
  /\ v2 ⇓ execution_of_valuation VerilogRight ρ
  .

Definition execution_some_distinct_value (C : VarSet.t) (e1 e2 : execution) : Prop :=
  exists var bv1 bv2,
    VarSet.In var C
    /\ e1 var = XBV.from_bv bv1
    /\ e2 var = XBV.from_bv bv2
    /\ bv1 <> bv2.

Definition counterexample_execution {i o} (v1 v2 : Verilog.vmodule i o) e1 e2 :=
  v1 ⇓ e1
  /\ v2 ⇓ e2
  /\ e1 =!!(LocationSet.of_varset (VarSet.of_list i))!!= e2
  /\ ~ (e1 =(LocationSet.of_varset (VarSet.of_list o))= e2).

Lemma smt_some_distinct_values_add var vars :
  pointwise_relation SMTLib.valuation iff
    (smt_some_distinct_values (VarSet.add var vars))
    (fun ρ => smt_distinct_value var ρ \/ smt_some_distinct_values vars ρ).
Proof.
  unfold smt_some_distinct_values.
  split.
  - intros [var' [Hin Hdistinct]].
    destruct (dec (var' = var)).
    + subst. left. exact Hdistinct.
    + right. exists var'. split.
      * VarSet.setdec.
      * exact Hdistinct.
  - intros [Hdistinct | [var' [Hin Hdistinct]]].
    + exists var. split.
      * VarSet.setdec.
      * exact Hdistinct.
    + exists var'. split.
      * VarSet.setdec.
      * exact Hdistinct.
Qed.

Lemma term_reflect_false P :
  (forall ρ, ~ P ρ) ->
  term_reflect SMTLib.Term_False P.
Proof. unfold term_reflect, term_satisfied_by. crush. Qed.

Lemma term_reflect_true P :
  (forall ρ, P ρ) ->
  term_reflect SMTLib.Term_True P.
Proof. unfold term_reflect, term_satisfied_by. crush. Qed.

Lemma term_reflect_eq s (t1 t2 : SMTLib.term s):
  term_reflect (SMTLib.Term_Eq t1 t2) (fun ρ => SMTLib.interp_term ρ t1 = SMTLib.interp_term ρ t2).
Proof.
  unfold term_reflect, term_satisfied_by.
  intros.
  simpl.
  apply SMTLib.value_eqb_eq.
Qed.

Lemma term_reflect_not P (t : SMTLib.term SMTLib.Sort_Bool):
  term_reflect t (fun ρ => P ρ) ->
  term_reflect (SMTLib.Term_Not t) (fun ρ => ~ P ρ).
Proof.
  unfold term_reflect, term_satisfied_by.
  intros H1. simpl.
  setoid_rewrite <- H1.
  intros ρ.
  destruct (SMTLib.interp_term ρ t); crush.
Qed.

Opaque N.of_nat N.to_nat N.add N.sub reflexivity.

Lemma term_reflect_eq_bitwise_rec w idx wf (t1 t2 : SMTLib.term (SMTLib.Sort_BitVec w)):
  term_reflect
    (eq_bitwise w t1 t2 idx wf)
    (fun ρ => BV.bv_extr 0 (N.of_nat idx) (SMTLib.interp_term ρ t1)
          = BV.bv_extr 0 (N.of_nat idx) (SMTLib.interp_term ρ t2)).
Proof.
  unfold term_reflect, term_satisfied_by.
  intros.
  funelim (eq_bitwise w t1 t2 idx wf).
  all: clear Heqcall.
  - simpl. split.
    { intros. exact (BV.bv_zero_eq _ _). }
    { intros. reflexivity. }
  - specialize (H ρ). simpl. 
    rewrite Bool.andb_true_iff.
    rewrite BV.bv_eq_reflect.
    replace (N.of_nat (S idx_pred)) with (1 + N.of_nat idx_pred)%N by lia.
    rewrite ! BV.bv_extr_plus by lia. rewrite N.add_0_l.
    rewrite BV.bv_concat_eq_iff.
    rewrite H. clear H.
    apply and_iff_compat_r.
    replace (1 + N.of_nat idx_pred - N.of_nat idx_pred)%N with 1%N by lia.
    reflexivity.
Qed.

Lemma term_reflect_eq_bitwise w wf (t1 t2 : SMTLib.term (SMTLib.Sort_BitVec w)):
  term_reflect
    (eq_bitwise w t1 t2 (N.to_nat w) wf)
    (fun ρ => SMTLib.interp_term ρ t1 = SMTLib.interp_term ρ t2).
Proof.
  replace (fun ρ : SMTLib.valuation => SMTLib.interp_term ρ t1 = SMTLib.interp_term ρ t2)
    with  (fun ρ : SMTLib.valuation => BV.bv_extr 0 (N.of_nat (N.to_nat w)) (SMTLib.interp_term ρ t1)
                                   = BV.bv_extr 0 (N.of_nat (N.to_nat w)) (SMTLib.interp_term ρ t2)).
  - apply term_reflect_eq_bitwise_rec.
  - apply functional_extensionality. intros ρ.
    rewrite N2Nat.id. rewrite ! BV.bv_extr_full. reflexivity.
Qed.

Lemma mk_var_same_spec : forall name,
  term_reflect (mk_var_same name) (smt_same_value name).
Proof.
  unfold mk_var_same, smt_same_value.
  intros * Hfunc.
  apply term_reflect_eq.
Qed.

Global Instance Proper_term_reflect :
  Proper
    (eq ==> pointwise_relation SMTLib.valuation iff ==> iff)
    term_reflect.
Proof. unfold term_reflect. solve_proper. Qed.

Global Instance Proper_smt_all_same_values :
  Proper
    (VarSet.Equal ==> pointwise_relation _ iff)
    smt_all_same_values.
Proof. unfold smt_all_same_values. solve_proper. Qed.

Global Instance Proper_smt_some_distinct_values :
  Proper
    (VarSet.Equal ==> pointwise_relation _ iff)
    smt_some_distinct_values.
Proof. unfold smt_some_distinct_values. solve_proper. Qed.

Lemma mk_inputs_same_spec : forall inputs,
  term_reflect (mk_inputs_same inputs) (smt_all_same_values (VarSet.of_list inputs)).
Proof.
  intros ?. induction inputs.
  all: simp mk_inputs_same.
  - apply term_reflect_true.
    setoid_rewrite smt_all_same_values_empty_iff.
    trivial.
  - intros. simp mk_inputs_same in *.
    setoid_rewrite VarSet.of_list_cons.
    setoid_rewrite smt_all_same_values_add.
    apply term_reflect_and.
    + apply mk_var_same_spec.
    + apply IHinputs.
Qed.

Lemma mk_var_distinct_spec name :
  term_reflect (mk_var_distinct name) (smt_distinct_value name).
Proof.
  intros *.
  unfold mk_var_distinct, smt_distinct_value.
  apply term_reflect_not.
  (* apply term_reflect_eq. *)
  change
    ((fun ρ : SMTLib.valuation =>
      ρ (verilog_to_smt_var VerilogLeft name) =
      ρ (verilog_to_smt_var VerilogRight name)))
    with
    ((fun ρ : SMTLib.valuation =>
      SMTLib.interp_term ρ (SMTLib.Term_Const (verilog_to_smt_var VerilogLeft name)) =
      SMTLib.interp_term ρ (SMTLib.Term_Const (verilog_to_smt_var VerilogRight name)))).
  apply term_reflect_eq_bitwise.
Qed.

Lemma mk_outputs_distinct_spec outputs :
  term_reflect (mk_outputs_distinct outputs) (smt_some_distinct_values (VarSet.of_list outputs)).
Proof.
  induction outputs.
  - simp mk_outputs_distinct.
    apply term_reflect_false.
    intros ρ [].
    VarSet.setdec.
  - intros.
    simp mk_outputs_distinct.
    setoid_rewrite VarSet.of_list_cons.
    setoid_rewrite smt_some_distinct_values_add.
    apply term_reflect_or.
    + apply mk_var_distinct_spec.
    + apply IHoutputs.
Qed.

Lemma satisfied_by_cons_iff t q ρ :
  satisfied_by ρ (t :: q) <->
  term_satisfied_by ρ t /\ satisfied_by ρ q.
Proof. apply List.Forall_cons_iff. Qed.

Lemma satisfied_by_app_iff q1 q2 ρ :
  satisfied_by ρ (q1 ++ q2)%list <->
  satisfied_by ρ q1 /\ satisfied_by ρ q2.
Proof. apply List.Forall_app. Qed.

Lemma smt_reflect_cons t q P1 P2 :
  term_reflect t P1 ->
  smt_reflect q P2 ->
  smt_reflect (t :: q) (fun ρ => P1 ρ /\ P2 ρ).
Proof.
  unfold term_reflect, smt_reflect.
  intros H1 H2.
  setoid_rewrite satisfied_by_cons_iff.
  setoid_rewrite H1.
  setoid_rewrite H2.
  reflexivity.
Qed.
  
Lemma smt_reflect_app q1 q2 P1 P2 :
  smt_reflect q1 P1 ->
  smt_reflect q2 P2 ->
  smt_reflect (q1 ++ q2)%list (fun ρ => P1 ρ /\ P2 ρ).
Proof.
  unfold term_reflect, smt_reflect.
  intros H1 H2.
  setoid_rewrite satisfied_by_app_iff.
  setoid_rewrite H1.
  setoid_rewrite H2.
  reflexivity.
Qed.

Theorem equivalence_query_spec {i o} (verilog1 verilog2 : Verilog.vmodule i o) smt :
  equivalence_query verilog1 verilog2 = inr smt ->
  smt_reflect
    smt
    (counterexample_valuation verilog1 verilog2).
Proof.
  unfold equivalence_query.
  intros H. simpl in H.
  monad_inv.
  simpl in *.
  unfold counterexample_valuation.

  repeat (apply smt_reflect_cons || apply smt_reflect_app); expect 4.
  - apply mk_inputs_same_spec; eassumption.
  - apply mk_outputs_distinct_spec; eassumption.
  - apply VerilogToSMTCorrect.verilog_to_smt_correct; eassumption.
  - apply VerilogToSMTCorrect.verilog_to_smt_correct; eassumption.
Qed.

Lemma smt_same_values_eq var vars ρ :
  smt_all_same_values vars ρ ->
  VarSet.In var vars ->
  ρ (verilog_to_smt_var VerilogLeft var) = ρ (verilog_to_smt_var VerilogRight var).
Proof. unfold smt_all_same_values, smt_same_value. auto. Qed.

Lemma smt_distinct_values_not_defined_match vars ρ :
  smt_some_distinct_values vars ρ ->
  ~ (execution_of_valuation VerilogLeft ρ
       =( LocationSet.of_varset vars )=
     execution_of_valuation VerilogRight ρ).
Proof.
  unfold smt_some_distinct_values.
  intros [var [Hin Hsmt_distinct]] contra.
  unfold smt_distinct_value in Hsmt_distinct.
  apply Hsmt_distinct.
  apply XBV.from_bv_injective.
  apply XBV.bitOf_ext. intros bit_idx Hbit_idx.
  apply (contra (Location.Mk var bit_idx)).
  apply LocationSet.of_varset_spec. auto.
Qed.

Lemma smt_all_same_values_execution_match vars ρ :
  smt_all_same_values vars ρ ->
  (execution_of_valuation VerilogLeft ρ) =!!(
    LocationSet.of_varset vars
  )!!= (execution_of_valuation VerilogRight ρ).
Proof.
  unfold smt_all_same_values, smt_same_value.
  intros Hmatch.
  apply RegisterState.defined_match_on_iff.
  intros loc Hloc.
  apply LocationSet.of_varset_spec in Hloc.
  destruct Hloc as [Hvar_in Hidx].
  specialize (Hmatch _ Hvar_in).
  unfold execution_of_valuation, RegisterState.get_location.
  rewrite Hmatch.
  rewrite XBV.bit_of_as_bv by assumption.
  destruct (BV.bitOf _ _); cbn; eauto.
Qed.

Lemma execution_defined_match_smt_all_same_values vars ρ :
  (execution_of_valuation VerilogLeft ρ)
    =!!( LocationSet.of_varset vars )!!=
  (execution_of_valuation VerilogRight ρ) ->
  smt_all_same_values vars ρ.
Proof.
  rewrite RegisterState.defined_match_on_iff.
  unfold smt_all_same_values, smt_same_value.
  intros H var Hvar_in.
  apply XBV.from_bv_injective.
  apply XBV.bitOf_ext. intros bit_idx Hbit_idx.
  edestruct (H (Location.Mk var bit_idx)) as [b [Hb1 Hb2]].
  { apply LocationSet.of_varset_spec. auto. }
  eapply RawXBV.bit_to_bool_injective; eauto.
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

Lemma not_defined_match_some_distinct (C : VarSet.t) e1 e2 :
  RegisterState.defined_value_for (LocationSet.of_varset C) e1 ->
  RegisterState.defined_value_for (LocationSet.of_varset C) e2 ->
  ~ (e1 =!!( LocationSet.of_varset C )!!= e2) ->
  execution_some_distinct_value C e1 e2.
Proof.
  intros Hdef1 Hdef2 Hnmatch.
  assert (~ (e1 =( LocationSet.of_varset C )= e2)) as Hnmatch'
      by (intro; apply Hnmatch; split; assumption).
  unfold RegisterState.match_on in Hnmatch'.
  apply not_all_ex_not in Hnmatch'.
  destruct Hnmatch' as [loc Hloc].
  apply imply_to_and in Hloc.
  destruct Hloc as [Hin Hneq].
  pose proof Hin as Hin'.
  apply LocationSet.of_varset_spec in Hin'.
  destruct Hin' as [Hvar_in Hidx].
  edestruct (XBV.bitOf_no_exes_to_bv _ (e1 (Location.var loc))) as [bv1 Hbv1]. {
    intros i Hi. apply (Hdef1 (Location.Mk (Location.var loc) i)).
    apply LocationSet.of_varset_spec. auto.
  }
  edestruct (XBV.bitOf_no_exes_to_bv _ (e2 (Location.var loc))) as [bv2 Hbv2]. {
    intros i Hi. apply (Hdef2 (Location.Mk (Location.var loc) i)).
    apply LocationSet.of_varset_spec. auto.
  }
  apply XBV.bv_xbv_inverse in Hbv1.
  apply XBV.bv_xbv_inverse in Hbv2.
  exists (Location.var loc), bv1, bv2.
  repeat split; auto; [].
  intro contra. subst bv2.
  apply Hneq.
  unfold RegisterState.get_location.
  congruence.
Qed.

Lemma not_defined_match_on_smt_some_distinct_values vars ρ :
  execution_some_distinct_value
    vars
    (execution_of_valuation VerilogLeft ρ)
    (execution_of_valuation VerilogRight ρ) ->
  smt_some_distinct_values vars ρ.
Proof.
  unfold execution_some_distinct_value, smt_some_distinct_values, smt_distinct_value in *.
  intros [var [bv1 [bv2 [Hin [Hlookup_left [Hlookup_right Hneq]]]]]].
  apply execution_of_valuation_inv in Hlookup_left. decompose record Hlookup_left.
  apply execution_of_valuation_inv in Hlookup_right. decompose record Hlookup_right.
  eexists. split; [eassumption|].
  congruence.
Qed.

Lemma defined_match_on_defined_value_left C e1 e2 :
  RegisterState.defined_match_on C e1 e2 ->
  RegisterState.defined_value_for C e1.
Proof. intros [_ H]. exact H. Qed.

Lemma defined_match_on_defined_value_right C e1 e2 :
  RegisterState.defined_match_on C e1 e2 ->
  RegisterState.defined_value_for C e2.
Proof.
  unfold RegisterState.defined_match_on.
  intros [Hmatch Hdefined].
  rewrite <- Hmatch.
  apply Hdefined.
Qed.

Global Instance match_on_eq_subrelation vars : 
  subrelation eq (RegisterState.match_on vars).
Proof. intros a b <-. reflexivity. Qed.

Global Instance Proper_execution_permitted {i o} (v : Verilog.vmodule i o) :
  Proper
    (RegisterState.match_on (Verilog.module_locations v) ==> iff)
    (execution_permitted v).
Proof.
  unfold execution_permitted.
  repeat intro.
  setoid_replace x with y
    using relation (RegisterState.match_on (Verilog.module_locations v))
    at 2
    by assumption.
  unfold Verilog.module_locations in H.
  RegisterState.unpack_match_on.
  setoid_replace x with y
    using relation (RegisterState.match_on (LocationSet.of_varset (VarSet.of_list i)))
    by assumption.
  reflexivity.
Qed.

Ltac assert_rewrite r :=
  let H := fresh "H" in
  assert ( H : r ); [|rewrite H; clear H].

Lemma list_subset_empty {A} (l : list A) :
  list_subset [] l.
Proof. apply Forall_nil. Qed.

Lemma execution_congruent {i o} (v : Verilog.vmodule i o) e1 e2 :
  v ⇓ e1 -> v ⇓ e2 ->
  e1 =( LocationSet.of_varset (VarSet.of_list i) )= e2 ->
  e1 =( LocationSet.of_varset (VarSet.of_list o) )= e2.
Proof.
  unfold "⇓".
  intros Hpermitted1 Hpermitted2 Hinput_match.
  unfold Verilog.module_locations in *.
  RegisterState.unpack_match_on.
  setoid_replace e1 with (run_vmodule v e1)
    using relation (RegisterState.match_on (LocationSet.of_varset (VarSet.of_list o)))
    by (symmetry; assumption).
  setoid_replace e2 with (run_vmodule v e2)
    using relation (RegisterState.match_on (LocationSet.of_varset (VarSet.of_list o)))
    by (symmetry; assumption).
  rewrite Hinput_match.
  reflexivity.
Qed.

Lemma no_counterexample_equivalent_iff {i o} (v1 v2 : Verilog.vmodule i o) :
  vmodule_sortable v1 ->
  vmodule_sortable v2 ->
  (forall e1 e2, ~ counterexample_execution v1 v2 e1 e2) <-> (v1 ~~ v2).
Proof.
  intros Hsortable1 Hsortable2.
  unfold counterexample_execution.
  split. 
  - intros H.
    intros e Hno_exes.
    assert (Hmatch_inputs : run_vmodule v1 e =!!( LocationSet.of_varset (VarSet.of_list i) )!!= run_vmodule v2 e). {
      split.
      - do 2 rewrite Facts.run_vmodule_preserve_inputs by assumption.
	reflexivity.
      - rewrite Facts.run_vmodule_preserve_inputs by assumption.
        exact Hno_exes.
    }
    assert (Hrun1 : v1 ⇓ run_vmodule v1 e) by apply Facts.run_vmodule_permitted.
    assert (Hrun2 : v2 ⇓ run_vmodule v2 e) by apply Facts.run_vmodule_permitted.
    specialize (H (run_vmodule v1 e) (run_vmodule v2 e)).
    apply not_and_or in H. destruct H; [contradiction|].
    apply not_and_or in H. destruct H; [contradiction|].
    apply not_and_or in H. destruct H; [contradiction|].
    apply NNPP in H.
    assumption.
  - intros H e1 e2 [Hpermitted1 [Hpermitted2 [[Hmatch_inputs Hinputs_defined] Hno_match_outputs]]].
    unfold "⇓" in Hpermitted1, Hpermitted2.
    contradict Hno_match_outputs.
    unfold Verilog.module_locations in *.
    RegisterState.unpack_match_on.
    setoid_replace e1 with (run_vmodule v1 e1)
      using relation (RegisterState.match_on (LocationSet.of_varset (VarSet.of_list o)))
      by (symmetry; assumption).
    setoid_replace e2 with (run_vmodule v2 e2)
      using relation (RegisterState.match_on (LocationSet.of_varset (VarSet.of_list o)))
      by (symmetry; assumption).
    rewrite <- Hmatch_inputs.
    apply H.
    exact Hinputs_defined.
Qed.

Lemma not_equivalent_counterexample_iff {i o} (v1 v2 : Verilog.vmodule i o) :
  Verilog.module_inputs v1 = Verilog.module_inputs v2 ->
  Verilog.module_outputs v1 = Verilog.module_outputs v2 ->
  vmodule_sortable v1 ->
  vmodule_sortable v2 ->
  (exists e1 e2, counterexample_execution v1 v2 e1 e2) <-> ~ (v1 ~~ v2).
Proof.
  intros Hinput_match Houtput_match Hsortable1 Hsortable2.
  setoid_rewrite <- no_counterexample_equivalent_iff; try assumption; [idtac].
  split.
  - intros [e1 [e2 H1]] H2. eapply H2. eapply H1.
  - intros H1.
    apply not_all_ex_not in H1. destruct H1 as [e1 H1].
    apply not_all_ex_not in H1. destruct H1 as [e2 H1].
    apply NNPP in H1.
    exists e1, e2. apply H1.
Qed.

Record verilog_to_smt_checked {i o} (v : Verilog.vmodule i o) := MkVerilogToSMTChecked {
  sorted : module_items_sorted (LocationSet.of_varset (VarSet.of_list (Verilog.module_inputs v))) (Verilog.modBody v);
}.

Lemma verilog_to_smt_checks {i o} tag (v : Verilog.vmodule i o) smt :
  VerilogToSMT.verilog_to_smt tag v = inr smt ->
  verilog_to_smt_checked v.
Proof.
  intros H.
  unfold VerilogToSMT.verilog_to_smt in H. simpl in H. monad_inv.
  constructor; assumption.
Qed.

Record equivalence_query_checked {i o} (v1 v2 : Verilog.vmodule i o) :=
  MkEquivalenceQueryChecked {
    verilog_to_smt_eqn1 : exists tag smt, VerilogToSMT.verilog_to_smt tag v1 = inr smt;
    verilog_to_smt_eqn2 : exists tag smt, VerilogToSMT.verilog_to_smt tag v2 = inr smt;
    verilog_to_smt_checked1 : verilog_to_smt_checked v1;
    verilog_to_smt_checked2 : verilog_to_smt_checked v2;
  }.

Lemma equivalence_query_checks {i o} (v1 v2 : Verilog.vmodule i o) smt :
  equivalence_query v1 v2 = inr smt ->
  equivalence_query_checked v1 v2.
Proof.
  intros H.
  unfold equivalence_query in H. simpl in H. monad_inv.
  constructor; eauto using verilog_to_smt_checks.
Qed.

Lemma counterexample_valuation_execution {i o} (v1 v2 : Verilog.vmodule i o) ρ :
  equivalence_query_checked v1 v2 ->
  counterexample_valuation v1 v2 ρ <->
    counterexample_execution v1 v2
      (execution_of_valuation VerilogLeft ρ)
      (execution_of_valuation VerilogRight ρ).
Proof.
  intros Hequivalence_query.
  destruct Hequivalence_query.
  inv verilog_to_smt_checked3.
  inv verilog_to_smt_checked4.
  unfold counterexample_valuation, counterexample_execution.
  split. 
  - unpack_goal.
    + assumption.
    + assumption.
    + apply smt_all_same_values_execution_match. assumption.
    + apply smt_distinct_values_not_defined_match. assumption.
  - unpack_goal.
    + apply execution_defined_match_smt_all_same_values. assumption.
    + apply not_defined_match_on_smt_some_distinct_values; expect 1.
      apply not_defined_match_some_distinct.
      * apply execution_of_valuation_defined_value, LocationSet.of_varset_in_bounds.
      * apply execution_of_valuation_defined_value, LocationSet.of_varset_in_bounds.
      * unfold "_ =!!( _ )!!= _". intuition eauto.
    + assumption.
    + assumption.
Qed.

Theorem equivalence_query_execution_spec {i o} (v1 v2 : Verilog.vmodule i o) smt :
  equivalence_query v1 v2 = inr smt ->
  smt_reflect
    smt
    (fun ρ => counterexample_execution v1 v2
      (execution_of_valuation VerilogLeft ρ)
      (execution_of_valuation VerilogRight ρ)).
Proof.
  intros Hfunc.
  setoid_rewrite <- counterexample_valuation_execution;
    [|eauto using equivalence_query_checks].
  eapply equivalence_query_spec.
  assumption.
Qed.

Theorem equivalence_query_sat_correct {i o} (v1 v2 : Verilog.vmodule i o) smt ρ :
  equivalence_query v1 v2 = inr smt ->
  satisfied_by ρ smt ->
  counterexample_execution v1 v2
    (execution_of_valuation VerilogLeft ρ)
    (execution_of_valuation VerilogRight ρ).
Proof.
  intros.
  eapply equivalence_query_execution_spec.
  all: eassumption.
Qed.

Lemma limit_to_regs_rewrite (vars : VarSet.t) e1 e2 :
  (forall var, VarSet.In var vars -> e1 var = e2 var) ->
  RegisterState.limit_to_regs vars e1 = RegisterState.limit_to_regs vars e2.
Proof.
  unfold RegisterState.limit_to_regs.
  intros Heq.
  apply functional_extensionality_dep.
  intros var. autodestruct; crush.
Qed.

Lemma counterexample_execution_rewrite_left {i o} (v v2 : Verilog.vmodule i o) e1 e1' e2 :
  e1 =( Verilog.module_locations v )= e1' ->
  counterexample_execution v v2 e1 e2 <-> counterexample_execution v v2 e1' e2.
Proof.
  unfold counterexample_execution.
  intros H.
  split.
  all: intros [Hvalid1 [Hvalid2 [Hdefined_in Hnot_defined_out]]].
  all: unpack_goal.
  all: try eassumption.
  all: assert (Hinputs : e1 =( LocationSet.of_varset (VarSet.of_list i) )= e1')
         by (unfold Verilog.module_locations in H; RegisterState.unpack_match_on; assumption).
  all: assert (Houtputs : e1 =( LocationSet.of_varset (VarSet.of_list o) )= e1')
         by (unfold Verilog.module_locations in H; RegisterState.unpack_match_on; assumption).
  - rewrite <- H. exact Hvalid1.
  - rewrite <- Hinputs. apply Hdefined_in.
  - rewrite <- Houtputs. apply Hnot_defined_out.
  - rewrite H. assumption.
  - rewrite Hinputs. apply Hdefined_in.
  - rewrite Houtputs. apply Hnot_defined_out.
Qed.

Lemma counterexample_execution_rewrite_right {i o} (v1 v2 : Verilog.vmodule i o) e1 e2 e2' :
  e2 =( Verilog.module_locations v2 )= e2' ->
  counterexample_execution v1 v2 e1 e2 <-> counterexample_execution v1 v2 e1 e2'.
Proof.
  unfold counterexample_execution.
  intros H.
  split.
  all: intros [Hvalid1 [Hvalid2 [Hdefined_in Hnot_defined_out]]].
  all: unpack_goal.
  all: try eassumption.
  all: assert (Hinputs : e2 =( LocationSet.of_varset (VarSet.of_list i) )= e2')
         by (unfold Verilog.module_locations in H; RegisterState.unpack_match_on; assumption).
  all: assert (Houtputs : e2 =( LocationSet.of_varset (VarSet.of_list o) )= e2')
         by (unfold Verilog.module_locations in H; RegisterState.unpack_match_on; assumption).
  - rewrite <- H. exact Hvalid2.
  - rewrite <- Hinputs. apply Hdefined_in.
  - rewrite <- Houtputs. apply Hnot_defined_out.
  - rewrite H. assumption.
  - rewrite Hinputs. apply Hdefined_in.
  - rewrite Houtputs. apply Hnot_defined_out.
Qed.

(* TODO: Move me to semantics *)
Lemma permitted_execution_all_vars_defined {i o} (v : Verilog.vmodule i o) e :
  clean_module v ->
  v ⇓ e ->
  RegisterState.defined_value_for (LocationSet.of_varset (VarSet.of_list i)) e ->
  RegisterState.defined_value_for (Verilog.module_locations v) e.
Proof.
  unfold "⇓".
  intros [Hvars_defined] Hpermitted Hinputs_defined.
  rewrite <- Hpermitted.
  apply Hvars_defined.
  apply Hinputs_defined.
Qed.

Lemma equivalence_query_unsat_no_counterexample {i o} (v1 v2 : Verilog.vmodule i o) smt :
  equivalence_query v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ smt) ->
  (forall e1 e2, ~ counterexample_execution v1 v2 e1 e2).
Proof.
  intros Hquery Hunsat e1 e2 Hcounterexample.
  destruct (equivalence_query_checks v1 v2 smt)
    as [[? [? ?]] [? [? ?]] ? ?];
    [assumption|].
  eapply Hunsat with (ρ := valuation_of_executions e1 e2).
  eapply equivalence_query_execution_spec; eauto.
  erewrite
    counterexample_execution_rewrite_left,
    counterexample_execution_rewrite_right.
  all: try eassumption.
  all: expect 2.
  1: eapply execution_of_valuation_right_match_on.
  2: eapply execution_of_valuation_left_match_on.
  all: unfold counterexample_execution in Hcounterexample.
  all: decompose record Hcounterexample.
  all: eapply permitted_execution_all_vars_defined.
  - eapply VerilogToSMTCorrect.verilog_to_smt_clean. eassumption.
  - assumption.
  - eapply defined_match_on_defined_value_right. eassumption.
  - eapply VerilogToSMTCorrect.verilog_to_smt_clean. eassumption.
  - assumption.
  - eapply defined_match_on_defined_value_left. eassumption.
Qed.

Theorem equivalence_query_unsat_correct {i o} (v1 v2 : Verilog.vmodule i o) smt :
  equivalence_query v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ smt) ->
  v1 ~~ v2.
Proof.
  intros Hquery Hunsat.
  destruct (equivalence_query_checks v1 v2 smt)
    as [[? [? ?]] [? [? ?]] [] []];
    [assumption|].
  apply no_counterexample_equivalent_iff; eauto using VerilogToSMTCorrect.verilog_to_smt_clean.
  - unfold vmodule_sortable. eexists.
    apply sort_module_items_stable.
    assumption.
  - unfold vmodule_sortable. eexists.
    apply sort_module_items_stable.
    assumption.
  - eapply equivalence_query_unsat_no_counterexample; eauto.
Qed.
