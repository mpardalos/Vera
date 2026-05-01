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

From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.MonadState.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Functor.

From Stdlib Require List.
From Stdlib Require Import String.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import NArith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Setoid.

Import EqNotations.

From Equations Require Import Equations.

Import List.ListNotations.
Import CommonNotations.
Import MonadLetNotation.
Import FunctorNotation.
Import SigTNotations.

Local Open Scope list.

Definition verilog_smt_match_on_name (regs : RegisterState.t) (ρ : SMTLib.valuation) var smtName : Prop :=
  regs var = Some (XBV.from_bv (ρ (SMTLib.Sort_BitVec (Verilog.varType var)) smtName)).
    
Definition verilog_smt_match_states_partial
  (cond : Verilog.variable -> Prop)
  (tag : TaggedVariable.Tag)
  (m : VerilogSMTBijection.t)
  (regs : RegisterState.t)
  (ρ : SMTLib.valuation) : Prop :=
  forall var,
    cond var ->
    exists smtName,
      m (tag, var) = Some smtName
      /\ verilog_smt_match_on_name regs ρ var smtName.

Global Instance verilog_smt_match_states_partial_proper :
  Proper
    (pointwise_relation Verilog.variable iff ==> eq ==> eq ==> eq ==> eq ==> iff)
    verilog_smt_match_states_partial.
Proof.
  repeat intro. subst.
  crush.
Qed.

Lemma verilog_smt_match_states_execution_of_valuation_same tag (m : VerilogSMTBijection.t) ρ :
  verilog_smt_match_states_partial (fun var => exists smtName, m (tag, var) = Some smtName) tag m (SMT.execution_of_valuation tag m ρ) ρ.
Proof.
  intros Hhas_var.
  unfold verilog_smt_match_states_partial, SMT.execution_of_valuation.
  intros [smtName HsmtName].
  exists smtName. split; [eassumption|].
  unfold verilog_smt_match_on_name.
  rewrite HsmtName.
  reflexivity.
Qed.

Lemma verilog_smt_match_states_partial_impl P1 P2 tag m regs ρ :
  (forall x, P2 x -> P1 x) ->
  verilog_smt_match_states_partial P1 tag m regs ρ ->
  verilog_smt_match_states_partial P2 tag m regs ρ.
Proof. crush. Qed.

Lemma verilog_smt_match_states_partial_set_reg_out C tag m r ρ var val :
  ~ C var ->
  verilog_smt_match_states_partial C tag m (RegisterState.set_reg var val r) ρ <->
  verilog_smt_match_states_partial C tag m r ρ.
Proof.
  intro Hcond1.
  unfold verilog_smt_match_states_partial.
  unfold verilog_smt_match_on_name in *.
  split; intros H * Hcond2.
  - destruct (dec (var0 = var)).
    + subst. contradiction.
    + insterU H. destruct H as [smtName [? Hverilogval]].
      econstructor. split. { eassumption. }
      rewrite RegisterState.set_reg_get_out in Hverilogval by congruence.
      eassumption.
  - destruct (dec (var0 = var)).
    + subst. contradiction.
    + insterU H. destruct H as [smtName [? Hverilogval]].
      econstructor. split. { eassumption. }
      rewrite RegisterState.set_reg_get_out by congruence.
      assumption.
Qed.

Lemma verilog_smt_match_states_partial_split C1 C2 C3 tag m reg ρ :
  (forall var, C3 var -> C1 var \/ C2 var) ->
  verilog_smt_match_states_partial C1 tag m reg ρ ->
  verilog_smt_match_states_partial C2 tag m reg ρ ->
  verilog_smt_match_states_partial C3 tag m reg ρ.
Proof.
  unfold verilog_smt_match_states_partial.
  intros Himpl H1 H2 * HC3.
  apply Himpl in HC3.
  destruct HC3; eauto.
Qed.

Lemma verilog_smt_match_states_partial_split_iff C1 C2 tag m reg ρ :
  verilog_smt_match_states_partial (fun var => C1 var \/ C2 var) tag m reg ρ <->
    (verilog_smt_match_states_partial C1 tag m reg ρ
     /\ verilog_smt_match_states_partial C2 tag m reg ρ).
Proof. unfold verilog_smt_match_states_partial. crush. Qed.

Lemma verilog_smt_match_states_partial_set_reg_elim C tag (m : VerilogSMTBijection.t) regs ρ var bv :
  (exists smtName,
      m (tag, var) = Some smtName /\ ρ (SMTLib.Sort_BitVec (Verilog.varType var)) smtName = bv) ->
  verilog_smt_match_states_partial C tag m regs ρ ->
  verilog_smt_match_states_partial C tag m (RegisterState.set_reg var (XBV.from_bv bv) regs) ρ.
Proof.
  unfold verilog_smt_match_states_partial.
  unfold verilog_smt_match_on_name.
  intros Hvar Hrest *.
  destruct (dec (var0 = var)); intros Hcond.
  - subst.
    insterU Hvar. destruct Hvar as [? [? ?]].
    insterU Hrest. destruct Hrest as [? [? ?]].
    replace x0 with x in * by congruence.
    repeat econstructor; try eassumption; expect 1.
    rewrite RegisterState.set_reg_get_in.
    subst. reflexivity.
  - insterU Hvar. destruct Hvar as [? [? ?]].
    insterU Hrest. destruct Hrest as [? [? ?]].
    repeat econstructor; try eassumption; expect 1.
    rewrite RegisterState.set_reg_get_out; eauto.
Qed.

Lemma verilog_smt_match_states_partial_change_regs C tag m r1 r2 ρ :
  (forall var, C var -> r1 var = r2 var) ->
  verilog_smt_match_states_partial C tag m r1 ρ ->
  verilog_smt_match_states_partial C tag m r2 ρ.
Proof.
  unfold verilog_smt_match_states_partial.
  intros Hsame Hmatch1 * Hcond.
  insterU Hsame. insterU Hcond. insterU Hmatch1.
  destruct Hmatch1 as [smtName [? ?]].
  exists smtName.
  split. { eassumption. }
  unfold verilog_smt_match_on_name in *.
  congruence.
Qed.

Ltac unpack_verilog_smt_match_states_partial :=
  repeat match goal with
    | [ H: verilog_smt_match_states_partial (fun _ => _ \/ _) _ _ _ _ |- _ ] =>
        apply verilog_smt_match_states_partial_split_iff in H;
        destruct H
    | [ H: verilog_smt_match_states_partial (fun _ => List.In _ (_ ++ _)) _ _ _ _ |- _ ] =>
        setoid_rewrite List.in_app_iff in H
    | [ |- verilog_smt_match_states_partial (fun _ => List.In _ (_ ++ _)) _ _ _ _ ] =>
        setoid_rewrite List.in_app_iff
    | [ |- verilog_smt_match_states_partial (fun _ => _ \/ _) _ _ _ _ ] =>
        apply verilog_smt_match_states_partial_split_iff; split
    end.

Lemma verilog_smt_match_states_partial_defined_value_for C tag m regs ρ :
  verilog_smt_match_states_partial C tag m regs ρ ->
  RegisterState.defined_value_for C regs.
Proof.
  unfold verilog_smt_match_states_partial, verilog_smt_match_on_name, RegisterState.defined_value_for.
  intros Hmatch * Hcond.
  edestruct Hmatch as [? [? ?]]; eauto.
Qed.

Lemma verilog_smt_match_states_partial_execution_match_on C tag m ρ e :
    verilog_smt_match_states_partial C tag m e ρ ->
    e ={ C }= SMT.execution_of_valuation tag m ρ.
Proof.
  unfold verilog_smt_match_states_partial, "_ ={ _ }= _".
  unfold verilog_smt_match_on_name.
  intros H var Hvar.
  edestruct H as [? [H1 H2]]; [eauto|].
  unfold SMT.execution_of_valuation.
  rewrite H1. assumption.
Qed.


Lemma verilog_smt_match_states_partial_execution_defined_value_for C tag m ρ e :
    verilog_smt_match_states_partial C tag m e ρ ->
    RegisterState.defined_value_for C e.
Proof.
  unfold verilog_smt_match_states_partial, RegisterState.defined_value_for.
  intros H var Hvar.
  edestruct H as [? [H1 H2]]; [eauto|].
  inv H2. eauto.
Qed.

Lemma execution_match_on_verilog_smt_match_states_partial C tag m ρ e :
    RegisterState.defined_value_for C e ->
    e ={ C }= (SMT.execution_of_valuation tag m ρ) ->
    verilog_smt_match_states_partial C tag m e ρ.
Proof.
  unfold RegisterState.defined_value_for, verilog_smt_match_states_partial, "_ =( _ )= _".
  intros Hdefined Heq var Hvar.
  insterU Hdefined. insterU Heq.
  unfold SMT.execution_of_valuation in Heq.
  destruct Hdefined as [bv Hbv]. 
  unfold verilog_smt_match_on_name in *.
  rewrite Hbv in *. clear Hbv.
  destruct (m (tag, var)); [|discriminate].
  rewrite Heq. eauto.
Qed.
