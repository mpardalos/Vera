From Stdlib Require Import ZArith.
From Stdlib Require Import BinNums.
From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Morphisms.

From Equations Require Import Equations.

From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Bitvector.
From vera Require Import VerilogSemantics.
From vera Require Import Verilog.
From vera Require Import Tactics.
From vera Require SMTQueries.
Import VerilogSemantics.CombinationalOnly.

From vera Require Import BVList.
Import BITVECTOR_LIST.

From vera Require SMTLib.

Import ListNotations.
Local Open Scope list.

Import SigTNotations.

Module TaggedVariable.
  Inductive Tag :=
  | VerilogLeft
  | VerilogRight
  .

  #[global] Instance dec_eq_tag (a b : Tag) : DecProp (a = b) :=
    mk_dec_eq.

  Definition t := (Tag * Verilog.variable)%type.

  Definition eq (l r : t) := l = r.

  Definition eq_equiv : Equivalence eq := eq_equivalence.

  Definition eq_dec (x y : t) : { eq x y } + { ~ eq x y } :=
    dec (x = y).
End TaggedVariable.

Module VerilogSMTBijection.
  Include PartialBijection(TaggedVariable)(NatAsUDT).

  Definition only_tag t m := forall tag smtName,
      option_map fst (bij_inverse m smtName) = Some tag ->
      tag = t.

  Lemma only_tag_empty t : only_tag t empty.
  Proof. cbv. discriminate. Qed.

  Lemma only_tag_insert tag name b m :
    only_tag tag m ->
    forall H1 H2,
      only_tag tag (insert (tag, name) b m H1 H2).
  Proof.
    unfold insert, only_tag.
    intros.
    unfold option_map in *.
    repeat (autodestruct_eqn E; cbn in * ); try reflexivity.
    eapply H. now erewrite E.
  Qed.

  Lemma combine_different_tag_left (m1 m2 : t) (t1 t2 : TaggedVariable.Tag) prf1 prf2:
    (t1 <> t2) ->
    only_tag t1 m1 ->
    only_tag t2 m2 ->
    forall n, combine m1 m2 prf1 prf2 (t1, n) = m1 (t1, n).
  Proof.
    intros.
    unfold combine. simpl.
    destruct (m1 (t1, n)) eqn:E1; try reflexivity.
    destruct (m2 (t1, n)) eqn:E2; try reflexivity.
    exfalso.
    apply bij_wf in E2.
    erewrite (H1 t1) in H. contradiction.
    now erewrite E2.
  Qed.

  Lemma combine_different_tag_right (m1 m2 : VerilogSMTBijection.t) (t1 t2 : TaggedVariable.Tag) prf1 prf2:
    (t1 <> t2) ->
    only_tag t1 m1 ->
    only_tag t2 m2 ->
    forall n, VerilogSMTBijection.combine m1 m2 prf1 prf2 (t2, n) = m2 (t2, n).
  Proof.
    intros.
    unfold VerilogSMTBijection.combine. simpl.
    destruct (m1 (t2, n)) eqn:E1; try reflexivity.
    destruct (m2 (t2, n)) eqn:E2; try reflexivity.
    - exfalso.
      apply VerilogSMTBijection.bij_wf in E1.
      erewrite (H0 t2) in H. contradiction.
      now erewrite E1.
    - exfalso.
      apply VerilogSMTBijection.bij_wf in E1.
      erewrite (H0 t2) in H. contradiction.
      now erewrite E1.
  Qed.
End VerilogSMTBijection.

Import VerilogSMTBijection (bij_inverse, bij_apply, bij_wf).
Import (coercions) VerilogSMTBijection.

Definition match_map_vars (tag : TaggedVariable.Tag) (map : VerilogSMTBijection.t) vars :=
  forall var, (exists smtName, map (tag, var) = Some smtName) <-> (In var vars).

Record smt_with_namemap :=
  MkSMTWithNameMap
    { assertions : SMTQueries.query;
      nameMap : VerilogSMTBijection.t;
    }.

Definition max_declaration (q : SMTQueries.query) : nat :=
  List.list_max (SMTQueries.domain q).

Lemma max_declaration_domain q name :
  In name (SMTQueries.domain q) ->
  name <= max_declaration q.
Proof.
  unfold max_declaration, SMTQueries.domain.
  revert name. rewrite <- Forall_forall.
  apply list_max_le.
  trivial.
Qed.

Equations default (s : SMTLib.sort) : SMTLib.interp_sort s :=
  default (SMTLib.Sort_Bool) := false;
  default (SMTLib.Sort_BitVec n) := BV.zeros n.

Import EqNotations.

Definition execution_of_valuation (tag : TaggedVariable.Tag) (m : VerilogSMTBijection.t) (ρ : SMTLib.valuation) : execution :=
  fun var =>
    match m (tag, var) with
    | Some smtName => XBV.from_bv (ρ (SMTLib.Sort_BitVec (Verilog.varType var)) smtName)
    | None => XBV.exes _
    end
.

Lemma execution_of_valuation_defined_value tag (m : VerilogSMTBijection.t) ρ:
  RegisterState.defined_value_for
    (fun var => exists smtName, m (tag, var) = Some smtName)
    (execution_of_valuation tag m ρ).
Proof.
  unfold execution_of_valuation.
  intros var [smtName Hvar].
  rewrite Hvar.
  eauto.
Qed.

Definition valuation_of_executions (m : VerilogSMTBijection.t) (e1 e2 : execution) : SMTLib.valuation :=
  fun s smtName =>
    match s as s' return SMTLib.interp_sort s' with
    | SMTLib.Sort_Bool => default _
    | SMTLib.Sort_BitVec w => 
      match bij_inverse m smtName with
| None => default _
| Some (tag, verilogVar) =>
  match dec (Verilog.varType verilogVar = w) with
  | right _ => default _
  | left E =>
          let e :=
            match tag with
            | TaggedVariable.VerilogLeft => e1
            | TaggedVariable.VerilogRight => e2
            end
          in
            match XBV.to_bv (e verilogVar) with
            (* TODO: Fix handling of Xs *)
            | None => default _
            | Some val => rew E in val
            end
  end
end
    end.

Lemma execution_of_valuation_left_match_on (m : VerilogSMTBijection.t) e1 e2 l :
  RegisterState.defined_value_for (fun var => In var l) e1 ->
  match_map_vars TaggedVariable.VerilogLeft m l ->
  execution_of_valuation TaggedVariable.VerilogLeft m
    (valuation_of_executions m e1 e2) =( l )= e1.
Proof.
  unfold execution_of_valuation, valuation_of_executions.
  (* intros Hdefined Hexists var Hvar_in. *)
  intros Hdefined Hmatch var Hvar_in.
  pose proof Hvar_in as H.
  apply Hmatch in H. destruct H as [smtName HsmtName].
  rewrite HsmtName.
  rewrite VerilogSMTBijection.bij_wf in HsmtName.
  rewrite HsmtName.
  apply Hdefined in Hvar_in. destruct Hvar_in as [bv Hbv].
  rewrite Hbv, XBV.xbv_bv_inverse.
  autodestruct; [|contradiction].
  rewrite <- eq_rect_eq.
  reflexivity.
Qed.

Lemma execution_of_valuation_right_match_on (m : VerilogSMTBijection.t) e1 e2 l :
  RegisterState.defined_value_for (fun var => In var l) e2 ->
  match_map_vars TaggedVariable.VerilogRight m l ->
  execution_of_valuation TaggedVariable.VerilogRight m
    (valuation_of_executions m e1 e2) =( l )= e2.
Proof.
  unfold execution_of_valuation, valuation_of_executions.
  (* intros Hdefined Hexists var Hvar_in. *)
  intros Hdefined Hmatch var Hvar_in.
  pose proof Hvar_in as H.
  apply Hmatch in H. destruct H as [smtName HsmtName].
  rewrite HsmtName.
  rewrite VerilogSMTBijection.bij_wf in HsmtName.
  rewrite HsmtName.
  apply Hdefined in Hvar_in. destruct Hvar_in as [bv Hbv].
  rewrite Hbv, XBV.xbv_bv_inverse.
  autodestruct; [|contradiction].
  rewrite <- eq_rect_eq.
  reflexivity.
Qed.

Definition verilog_smt_match_on_name (regs : RegisterState.t) (ρ : SMTLib.valuation) var smtName : Prop :=
  regs var = XBV.from_bv (ρ (SMTLib.Sort_BitVec (Verilog.varType var)) smtName).
    
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

(* Might not be needed *)
Global Instance verilog_smt_match_states_partial_proper :
  Proper
    (pointwise_relation Verilog.variable iff ==> eq ==> eq ==> eq ==> eq ==> iff)
    verilog_smt_match_states_partial.
Proof.
  repeat intro. subst.
  crush.
Qed.

Global Instance verilog_smt_match_states_partial_impl_proper :
  Proper
    (pointwise_relation Verilog.variable Basics.impl ==> eq ==> eq ==> eq ==> eq ==> Basics.flip Basics.impl)
    verilog_smt_match_states_partial.
Proof.
  repeat intro. subst.
  crush.
Qed.

Lemma verilog_smt_match_states_execution_of_valuation_same tag (m : VerilogSMTBijection.t) ρ :
  verilog_smt_match_states_partial (fun var => exists smtName, m (tag, var) = Some smtName) tag m (execution_of_valuation tag m ρ) ρ.
Proof.
  intros Hhas_var.
  unfold verilog_smt_match_states_partial, execution_of_valuation.
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
      assumption.
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
    repeat f_equal.
    congruence.
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
    e ={ C }= execution_of_valuation tag m ρ.
Proof.
  unfold verilog_smt_match_states_partial, "_ ={ _ }= _".
  unfold verilog_smt_match_on_name.
  intros H var Hvar.
  edestruct H as [? [H1 H2]]; [eauto|].
  unfold execution_of_valuation.
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

Lemma execution_of_valuation_inv tag m ρ var bv :
  execution_of_valuation tag m ρ var = XBV.from_bv bv ->
  exists smtName,
    m (tag, var) = Some smtName /\
    ρ (SMTLib.Sort_BitVec (Verilog.varType var)) smtName = bv .
Proof.
  unfold execution_of_valuation.
  intros H.
  (* We don't know that var is in m. We could have added it directly
  as an assumption, but we can also deduce it from the fact that the
  value of the var in e is defined. This is only possible, however, if
  the var is not zero-width (because zero-width Xs are
  indistinguishable from zero-width 0/1s). This lemma is why we have
  added varTypeWf into verilog variables *)

  destruct (m (tag, var)).
  - apply XBV.from_bv_injective in H.
    eauto.
  - exfalso.
    apply f_equal with (f:=XBV.to_bv) in H.
    autorewrite with xbv in H.
    rewrite XBV.exes_to_bv in H by apply Verilog.varTypeWf.
    discriminate.
Qed.

Lemma execution_match_on_verilog_smt_match_states_partial C tag m ρ e :
    RegisterState.defined_value_for C e ->
    e ={ C }= (execution_of_valuation tag m ρ) ->
    verilog_smt_match_states_partial C tag m e ρ.
Proof.
  unfold RegisterState.defined_value_for, verilog_smt_match_states_partial, "_ =( _ )= _".
  intros Hdefined Heq var Hvar.
  insterU Hdefined. insterU Heq.
  destruct Hdefined as [bv Hbv]. 
  unfold verilog_smt_match_on_name in *.
  unfold execution_of_valuation in *.

  (* TODO: Use execution_of_valuation_inv instead. *)

  (* We don't know that var is in m. We could have added it directly
  as an assumption, but we can also deduce it from the fact that the
  value of the var in e is defined. This is only possible, however, if
  the var is not zero-width (because zero-width Xs are
  indistinguishable from zero-width 0/1s). This lemma is why we have
  added varTypeWf into verilog variables *)

  destruct (m (tag, var)); [solve [eauto]|].
  exfalso.
  rewrite Hbv in Heq. clear Hbv.
  apply f_equal with (f:=XBV.to_bv) in Heq.
  autorewrite with xbv in Heq.
  rewrite XBV.exes_to_bv in Heq by apply Verilog.varTypeWf.
  discriminate.
Qed.
