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

Inductive verilog_smt_match_on_name (regs : RegisterState) (ρ : SMTLib.valuation) var smtName : Prop :=
| verilog_smt_match_on_names_intro xbv val
    (Hsmtval : ρ smtName = Some val)
    (Hverilogval : regs var = Some xbv)
    (Hmatchvals : verilog_smt_match_value xbv val).

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
  forall var smtName,
    cond var ->
    m (tag, var) = Some smtName ->
    verilog_smt_match_on_name regs ρ var smtName.

(* Written by Claude *in one shot* wat. *)
Instance verilog_smt_match_states_partial_morphism
  (tag : TaggedVariable.Tag)
  (m : VerilogSMTBijection.t)
  (regs : RegisterState)
  (ρ : SMTLib.valuation) :
  Proper (pointwise_relation Verilog.variable iff ==> iff)
    (fun cond => verilog_smt_match_states_partial cond tag m regs ρ).
Proof.
  intros cond1 cond2 H_equiv.
  unfold verilog_smt_match_states_partial.
  split; intros H verilogName smtName.
  - intros H_cond1 H_map.
    apply (H verilogName smtName).
    + apply H_equiv. exact H_cond1.
    + exact H_map.
  - intros H_cond2 H_map.
    apply (H verilogName smtName).
    + apply H_equiv. exact H_cond2.
    + exact H_map.
Qed.
