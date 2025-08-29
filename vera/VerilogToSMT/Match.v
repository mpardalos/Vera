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

Import EqNotations.

From Equations Require Import Equations.

Import List.ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Import SigTNotations.

Local Open Scope list.

Inductive verilog_smt_match_value {w} : XBV.xbv w -> SMTLib.value -> Prop :=
| verilog_smt_match_value_intro bv :
  verilog_smt_match_value (XBV.from_bv bv) (SMTLib.Value_BitVec w bv).

Definition verilog_smt_match_to_bv n (xbv : XBV.xbv n) (bv : BV.bitvector n):
  XBV.to_bv xbv = Some bv ->
  verilog_smt_match_value xbv (SMTLib.Value_BitVec n bv).
Proof.
  intros H.
  apply XBV.bv_xbv_inverse in H.
  subst xbv.
  constructor.
Qed.

Definition verilog_smt_match_to_bv_bits
  n1 n2 (xbv : XBV.xbv n1) (bv1 : BV.bitvector n1) (bv2 : BV.bitvector n2):
  XBV.to_bv xbv = Some bv1 ->
  BV.bits bv1 = BV.bits bv2 ->
  verilog_smt_match_value xbv (SMTLib.Value_BitVec n2 bv2).
Proof.
  destruct bv1 as [bv1 wf1], bv2 as [bv2 wf2]. simpl. intros H1 H2.
  apply XBV.bv_xbv_inverse in H1.
  subst.
  constructor.
Qed.

Definition valuation_has_var tag (m : VerilogSMTBijection.t) ρ var : Prop :=
  exists smtName bv,
    m (tag, var) = Some smtName /\
      ρ smtName = Some (SMTLib.Value_BitVec (Verilog.varType var) bv).

Inductive verilog_smt_match_on_name (regs : RegisterState) (ρ : SMTLib.valuation) var smtName : Prop :=
| verilog_smt_match_on_names_intro xbv val
    (Hsmtval : ρ smtName = Some val)
    (Hverilogval : regs var = Some xbv)
    (Hmatchvals : verilog_smt_match_value xbv val).

(* TODO: No longer used, deleteme *)
Definition verilog_smt_match_states
  (tag : TaggedVariable.Tag)
  (m : VerilogSMTBijection.t)
  (regs : RegisterState)
  (ρ : SMTLib.valuation) : Prop :=
  forall verilogName smtName,
    m (tag, verilogName) = Some smtName ->
    verilog_smt_match_on_name regs ρ verilogName smtName.

Definition verilog_smt_match_states_partial
  (cond : Verilog.variable -> Prop)
  (tag : TaggedVariable.Tag)
  (m : VerilogSMTBijection.t)
  (regs : RegisterState)
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

Lemma verilog_smt_match_states_execution_of_valuation_same C tag (m : VerilogSMTBijection.t) ρ :
  (forall var, C var -> valuation_has_var tag m ρ var) ->
  verilog_smt_match_states_partial C tag m (SMT.execution_of_valuation tag m ρ) ρ.
Proof.
  intros Hhas_var.
  unfold verilog_smt_match_states_partial, SMT.execution_of_valuation.
  intros var HC.
  edestruct Hhas_var as [smtName [bv [HsmtName HsmtVal]]]; eauto.
  exists smtName. split; [eassumption|].
  econstructor.
  - eassumption.
  - rewrite HsmtName.
    rewrite HsmtVal.
    autodestruct; [|contradiction].
    f_equal.
    rewrite <- eq_rect_eq.
    reflexivity.
  - constructor.
Qed.

Lemma verilog_smt_match_states_partial_impl P1 P2 tag m regs ρ :
  (forall x, P2 x -> P1 x) ->
  verilog_smt_match_states_partial P1 tag m regs ρ ->
  verilog_smt_match_states_partial P2 tag m regs ρ.
Proof. crush. Qed.

Lemma verilog_smt_match_states_partial_set_reg_out C tag m r ρ var val :
  ~ C var ->
  verilog_smt_match_states_partial C tag m (set_reg var val r) ρ <->
  verilog_smt_match_states_partial C tag m r ρ.
Proof.
  intro Hcond1.
  unfold verilog_smt_match_states_partial.
  split; intros H * Hcond2.
  - destruct (dec (var0 = var)).
    + subst. contradiction.
    + insterU H. destruct H as [smtName [? []]].
      econstructor. split. { eassumption. }
      rewrite set_reg_get_out in Hverilogval by congruence.
      econstructor; eassumption.
  - destruct (dec (var0 = var)).
    + subst. contradiction.
    + insterU H. destruct H as [smtName [? []]].
      econstructor. split. { eassumption. }
      econstructor; try eassumption; [idtac].
      rewrite set_reg_get_out by congruence.
      eassumption.
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
      m (tag, var) = Some smtName /\ ρ smtName = Some (SMTLib.Value_BitVec _ bv)) ->
  verilog_smt_match_states_partial C tag m regs ρ ->
  verilog_smt_match_states_partial C tag m (set_reg var (XBV.from_bv bv) regs) ρ.
Proof.
  unfold verilog_smt_match_states_partial.
  intros Hvar Hrest *.
  destruct (dec (var0 = var)); intros Hcond.
  - subst.
    insterU Hvar. destruct Hvar as [? [? ?]].
    insterU Hrest. destruct Hrest as [? [? []]].
    replace x0 with x in * by congruence.
    inv Hmatchvals.
    repeat econstructor; try eassumption; [idtac].
    rewrite set_reg_get_in.
    repeat f_equal.
    rewrite H0 in Hsmtval. inv Hsmtval.
    apply_somewhere inj_pair2.
    assumption.
  - insterU Hvar. destruct Hvar as [? [? ?]].
    insterU Hrest. destruct Hrest as [? [? []]].
    inv Hmatchvals.
    repeat econstructor; try eassumption; [idtac].
    rewrite set_reg_get_out; eauto.
Qed.

Lemma verilog_smt_match_states_partial_change_regs C tag m r1 r2 ρ :
  (forall var, C var -> r1 var = r2 var) ->
  verilog_smt_match_states_partial C tag m r1 ρ ->
  verilog_smt_match_states_partial C tag m r2 ρ.
Proof.
  unfold verilog_smt_match_states_partial.
  intros Hsame Hmatch1 * Hcond.
  insterU Hsame. insterU Hcond. insterU Hmatch1.
  destruct Hmatch1 as [smtName [? []]].
  exists smtName.
  split. { eassumption. }
  econstructor; try eassumption; [idtac].
  rewrite <- Hsame. assumption.
Qed.

Definition defined_value_for (C : Verilog.variable -> Prop) (regs : RegisterState) :=
  forall (var : Verilog.variable),
    C var ->
    exists xbv, regs var = Some xbv /\ ~ XBV.has_x xbv.

Global Instance defined_value_for_proper :
  Proper (pointwise_relation Verilog.variable iff ==> eq ==> iff) defined_value_for.
Proof. repeat intro. subst. crush. Qed.

Lemma defined_value_for_split_iff (C1 C2 : Verilog.variable -> Prop) regs :
  (defined_value_for C1 regs /\ defined_value_for C2 regs) <->
    (defined_value_for (fun var => C1 var \/ C2 var) regs).
Proof. unfold defined_value_for. crush. Qed.

Lemma verilog_smt_match_states_partial_defined_value_for C tag m regs ρ :
  verilog_smt_match_states_partial C tag m regs ρ ->
  defined_value_for C regs.
Proof.
  unfold verilog_smt_match_states_partial, defined_value_for.
  intros Hmatch * Hcond.
  insterU Hmatch.
  destruct Hmatch as [? [? []]].
  inv Hmatchvals.
  exists (XBV.from_bv bv).
  split; eauto.
  apply XBV.not_has_x_to_bv.
  eexists. eapply XBV.xbv_bv_inverse.
Qed.

Lemma verilog_smt_match_states_partial_execution_match_on C tag m ρ e :
    verilog_smt_match_states_partial C tag m e ρ ->
    execution_match_on C e (SMT.execution_of_valuation tag m ρ).
Proof.
  unfold verilog_smt_match_states_partial, execution_match_on.
  intros H var Hvar.
  edestruct H as [? [H1 H2]]; [eauto|].
  inv H2. inv Hmatchvals.
  unfold SMT.execution_of_valuation.
  rewrite H1, Hsmtval.
  autodestruct; [|contradiction].
  rewrite <- eq_rect_eq.
  crush.
Qed.

Lemma execution_match_on_verilog_smt_match_states_partial C tag m ρ e :
    execution_match_on C e (SMT.execution_of_valuation tag m ρ) ->
    verilog_smt_match_states_partial C tag m e ρ.
Proof.
  unfold verilog_smt_match_states_partial, execution_match_on.
  intros H var Hvar.
  edestruct H as [? [H1 H2]]; [eassumption|].
  unfold SMT.execution_of_valuation in H2.
  autodestruct_eqn E.
  eexists. split; [reflexivity|].
  econstructor; eauto.
  simpl.
  constructor.
Qed.
