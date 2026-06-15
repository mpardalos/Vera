From Stdlib Require Import ZArith.
From Stdlib Require Import BinNums.
From Stdlib Require Import Ascii.
From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Morphisms.

From Equations Require Import Equations.
From Equations.Prop Require Import Logic.
From ExtLib Require Import Data.Monads.EitherMonad.
From ExtLib Require Import Structures.Monad.

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
Import SigTNotations.
Import MonadLetNotation.

Local Open Scope list.
Local Open Scope monad_scope.

Inductive VarTag := VerilogLeft | VerilogRight.

Definition tag_choose {A} t (x1 x2 : A) : A :=
  match t with
  | VerilogLeft => x1
  | VerilogRight => x2
  end.

#[global] Instance dec_eq_tag (a b : VarTag) : DecProp (a = b) :=
  mk_dec_eq.

Equations default (s : SMTLib.sort) : SMTLib.interp_sort s :=
  default (SMTLib.Sort_Bool) := false;
  default (SMTLib.Sort_BitVec n) := BV.zeros n.

Definition tag_name (t : VarTag) (s : string) : string :=
  (match t with
   | VerilogLeft => "l"
   | VerilogRight => "r"
   end ++ "__" ++ s)%string.

Definition untag_name (s : string) : option (VarTag * string) :=
  match s with
  | (String "l" (String "_" (String "_" s'))) => Some (VerilogLeft, s')
  | (String "r" (String "_" (String "_" s'))) => Some (VerilogRight, s')
  | _ => None
  end.

Lemma tag_name_injective_tag t t' n n' :
  tag_name t n = tag_name t' n' ->
  t = t'.
Proof.
  unfold untag_name, tag_name.
  destruct t, t'.
  all: crush.
Qed.

Lemma tag_name_injective_name t t' n n' :
  tag_name t n = tag_name t' n' ->
  n = n'.
Proof.
  unfold untag_name, tag_name.
  destruct t, t'.
  all: crush.
Qed.

Lemma untag_tag_name t s : untag_name (tag_name t s) = Some (t, s).
Proof.
  unfold untag_name, tag_name.
  destruct t; reflexivity.
Qed.

Lemma tag_untag_name t n n' :
  untag_name n = Some (t, n') ->
  tag_name t n' = n.
Proof.
 unfold untag_name, tag_name.
 intros H.
 autodestruct; reflexivity.
Qed.

Lemma tag_untag_name_none t n n' :
  untag_name n = None ->
  tag_name t n' <> n.
Proof.
 intros H contra.
 apply f_equal with (f:=untag_name) in contra.
 rewrite H in contra.
 rewrite untag_tag_name in contra.
 discriminate.
Qed.

Definition verilog_to_smt_var (t : VarTag) (var : Verilog.variable) : SMTLib.const_sym :=
  {|
    SMTLib.symName := tag_name t (Verilog.varName var);
    SMTLib.symSort := SMTLib.Sort_BitVec (Verilog.varType var)
  |}.

Definition smt_to_verilog_var (sym : SMTLib.const_sym) : option (VarTag * Verilog.variable)  :=
  let* (t, name) := untag_name (SMTLib.symName sym) in
  let* w := match SMTLib.symSort sym with
            | SMTLib.Sort_BitVec w => Some w
	    | _ => None
	    end in
  let* prf := opt_dec (w > 0)%N in
  Some (t, Verilog.MkVariable name w prf).

Lemma verilog_to_smt_to_verilog_var t var : smt_to_verilog_var (verilog_to_smt_var t var) = Some (t, var).
Proof.
  unfold smt_to_verilog_var, verilog_to_smt_var.
  destruct var.
  simpl. rewrite untag_tag_name. monad_inv.
  - do 3 f_equal. apply proof_irrelevance.
  - exfalso. destruct varType; crush.
Qed.

Lemma smt_to_verilog_to_smt_var_some sym t var :
  smt_to_verilog_var sym = Some (t, var) ->
  verilog_to_smt_var t var = sym.
Proof.
  unfold smt_to_verilog_var, verilog_to_smt_var.
  destruct sym, var.
  intros H. monad_inv. simpl in *.
  apply tag_untag_name in E.
  rewrite E.
  reflexivity.
Qed.

Lemma smt_to_verilog_to_smt_var_none sym t var :
  smt_to_verilog_var sym = None ->
  verilog_to_smt_var t var <> sym.
Proof.
  intros H contra.
  apply f_equal with (f:=smt_to_verilog_var) in contra.
  rewrite H in contra.
  rewrite verilog_to_smt_to_verilog_var in contra.
  discriminate.
Qed.

Import EqNotations.

Definition execution_of_valuation (tag : VarTag) (ρ : SMTLib.valuation) : execution :=
  fun var => XBV.from_bv (ρ (verilog_to_smt_var tag var)).

Lemma execution_of_valuation_defined_value C tag ρ:
  RegisterState.defined_value_for C (execution_of_valuation tag ρ).
Proof.
  unfold execution_of_valuation.
  intros var _.
  eauto.
Qed.

Definition valuation_of_executions (e1 e2 : execution) : SMTLib.valuation :=
  fun sym =>
  match untag_name (SMTLib.symName sym), SMTLib.symSort sym with
  | Some (t, varName), SMTLib.Sort_BitVec w =>
    match dec (w > 0)%N with
    | left prf =>
      match XBV.to_bv (tag_choose t e1 e2 (Verilog.MkVariable varName w prf)) with
      | Some bv => bv
      | None => default (SMTLib.Sort_BitVec w)
      end
    | right _ => default (SMTLib.Sort_BitVec w)
    end
  | _, s => default s
  end.

Lemma execution_of_valuation_left_match_on e1 e2 l :
  RegisterState.defined_value_for (fun var => In var l) e1 ->
  execution_of_valuation VerilogLeft
    (valuation_of_executions e1 e2) =( l )= e1.
Proof.
  (* intros Hdefined Hexists var Hvar_in. *)
  intros Hdefined var Hvar_in.
  unfold valuation_of_executions, execution_of_valuation, verilog_to_smt_var.
  destruct var. simpl.
  destruct (dec (varType > 0)%N) as [varTypeWf'|?]; [|contradiction].
  replace varTypeWf' with varTypeWf in * by apply proof_irrelevance.
  autodestruct_eqn E.
  - apply XBV.bv_xbv_inverse. assumption.
  - exfalso.
    edestruct Hdefined as [bv Hbv]; [apply Hvar_in|].
    rewrite Hbv in E.
    rewrite XBV.xbv_bv_inverse in E.
    discriminate.
Qed.

Lemma execution_of_valuation_right_match_on e1 e2 l :
  RegisterState.defined_value_for (fun var => In var l) e2 ->
  execution_of_valuation VerilogRight
    (valuation_of_executions e1 e2) =( l )= e2.
Proof.
  (* intros Hdefined Hexists var Hvar_in. *)
  intros Hdefined var Hvar_in.
  unfold valuation_of_executions, execution_of_valuation, verilog_to_smt_var.
  destruct var. simpl.
  destruct (dec (varType > 0)%N) as [varTypeWf'|?]; [|contradiction].
  replace varTypeWf' with varTypeWf in * by apply proof_irrelevance.
  autodestruct_eqn E.
  - apply XBV.bv_xbv_inverse. assumption.
  - exfalso.
    edestruct Hdefined as [bv Hbv]; [apply Hvar_in|].
    rewrite Hbv in E.
    rewrite XBV.xbv_bv_inverse in E.
    discriminate.
Qed.

Definition verilog_smt_match_states_partial
  (cond : Verilog.variable -> Prop)
  (tag : VarTag)
  (regs : RegisterState.t)
  (ρ : SMTLib.valuation) : Prop :=
  forall var, cond var -> regs var = XBV.from_bv (ρ (verilog_to_smt_var tag var)).

(* Might not be needed *)
Global Instance verilog_smt_match_states_partial_proper :
  Proper
    (pointwise_relation Verilog.variable iff ==> eq ==> eq ==> eq ==> iff)
    verilog_smt_match_states_partial.
Proof.
  repeat intro. subst.
  crush.
Qed.

Global Instance verilog_smt_match_states_partial_impl_proper :
  Proper
    (pointwise_relation Verilog.variable Basics.impl ==> eq ==> eq ==> eq ==> Basics.flip Basics.impl)
    verilog_smt_match_states_partial.
Proof.
  repeat intro. subst.
  crush.
Qed.

Lemma verilog_smt_match_states_execution_of_valuation_same C tag ρ :
  verilog_smt_match_states_partial C tag (execution_of_valuation tag ρ) ρ.
Proof.
  intros Hhas_var.
  unfold verilog_smt_match_states_partial, execution_of_valuation.
  crush.
Qed.

Lemma verilog_smt_match_states_partial_impl P1 P2 tag regs ρ :
  (forall x, P2 x -> P1 x) ->
  verilog_smt_match_states_partial P1 tag regs ρ ->
  verilog_smt_match_states_partial P2 tag regs ρ.
Proof. crush. Qed.

Lemma verilog_smt_match_states_partial_set_reg_out C tag r ρ var val :
  ~ C var ->
  verilog_smt_match_states_partial C tag (RegisterState.set_reg var val r) ρ <->
  verilog_smt_match_states_partial C tag r ρ.
Proof.
  intro Hcond1.
  unfold verilog_smt_match_states_partial.
  split.
  all: intros H * Hcond2.
  all: destruct (dec (var0 = var)); [subst; contradiction|].
  all: rewrite <- H by assumption.
  all: rewrite RegisterState.set_reg_get_out by congruence.
  all: reflexivity.
Qed.

Lemma verilog_smt_match_states_partial_split C1 C2 C3 tag reg ρ :
  (forall var, C3 var -> C1 var \/ C2 var) ->
  verilog_smt_match_states_partial C1 tag reg ρ ->
  verilog_smt_match_states_partial C2 tag reg ρ ->
  verilog_smt_match_states_partial C3 tag reg ρ.
Proof.
  unfold verilog_smt_match_states_partial.
  intros Himpl H1 H2 * HC3.
  apply Himpl in HC3.
  destruct HC3; eauto.
Qed.

Lemma verilog_smt_match_states_partial_split_iff C1 C2 tag reg ρ :
  verilog_smt_match_states_partial (fun var => C1 var \/ C2 var) tag reg ρ <->
    (verilog_smt_match_states_partial C1 tag reg ρ
     /\ verilog_smt_match_states_partial C2 tag reg ρ).
Proof. unfold verilog_smt_match_states_partial. crush. Qed.

Lemma verilog_smt_match_states_partial_set_reg_elim C tag regs ρ var bv :
  (ρ (verilog_to_smt_var tag var) = bv) ->
  verilog_smt_match_states_partial C tag regs ρ ->
  verilog_smt_match_states_partial C tag (RegisterState.set_reg var (XBV.from_bv bv) regs) ρ.
Proof.
  unfold verilog_smt_match_states_partial.
  intros Hvar Hrest *.
  destruct (dec (var0 = var)); intros Hcond.
  - subst.
    apply RegisterState.set_reg_get_in.
  - rewrite RegisterState.set_reg_get_out by congruence.
    apply Hrest. apply Hcond.
Qed.

Lemma verilog_smt_match_states_partial_change_regs C tag r1 r2 ρ :
  (forall var, C var -> r1 var = r2 var) ->
  verilog_smt_match_states_partial C tag r1 ρ ->
  verilog_smt_match_states_partial C tag r2 ρ.
Proof.
  unfold verilog_smt_match_states_partial.
  intros Hsame Hmatch1 * Hcond.
  insterU Hsame. insterU Hcond. insterU Hmatch1.
  congruence.
Qed.

Ltac unpack_verilog_smt_match_states_partial :=
  repeat match goal with
    | [ H: verilog_smt_match_states_partial (fun _ => _ \/ _) _ _ _ |- _ ] =>
        apply verilog_smt_match_states_partial_split_iff in H;
        destruct H
    | [ H: verilog_smt_match_states_partial (fun _ => List.In _ (_ ++ _)) _ _ _ |- _ ] =>
        setoid_rewrite List.in_app_iff in H
    | [ |- verilog_smt_match_states_partial (fun _ => List.In _ (_ ++ _)) _ _ _ ] =>
        setoid_rewrite List.in_app_iff
    | [ |- verilog_smt_match_states_partial (fun _ => _ \/ _) _ _ _ ] =>
        apply verilog_smt_match_states_partial_split_iff; split
    end.

Lemma verilog_smt_match_states_partial_defined_value_for C tag regs ρ :
  verilog_smt_match_states_partial C tag regs ρ ->
  RegisterState.defined_value_for C regs.
Proof.
  unfold verilog_smt_match_states_partial, RegisterState.defined_value_for.
  intros Hmatch * Hcond.
  eauto.
Qed.

Lemma verilog_smt_match_states_partial_execution_match_on C tag ρ e :
    verilog_smt_match_states_partial C tag e ρ ->
    e ={ C }= execution_of_valuation tag ρ.
Proof.
  unfold verilog_smt_match_states_partial, "_ ={ _ }= _".
  intros H var Hvar.
  apply H.
  apply Hvar.
Qed.

Lemma verilog_smt_match_states_partial_execution_defined_value_for C tag ρ e :
    verilog_smt_match_states_partial C tag e ρ ->
    RegisterState.defined_value_for C e.
Proof.
  unfold verilog_smt_match_states_partial, RegisterState.defined_value_for.
  intros H var Hvar.
  rewrite H by assumption.
  eauto.
Qed.

Lemma execution_of_valuation_inv tag ρ var bv :
  execution_of_valuation tag ρ var = XBV.from_bv bv ->
  ρ (verilog_to_smt_var tag var) = bv.
Proof.
  unfold execution_of_valuation.
  apply XBV.from_bv_injective.
Qed.

Lemma execution_match_on_verilog_smt_match_states_partial C tag ρ e :
    e ={ C }= (execution_of_valuation tag ρ) ->
    verilog_smt_match_states_partial C tag e ρ.
Proof.
  unfold execution_of_valuation, verilog_smt_match_states_partial, "_ =( _ )= _".
  trivial.
Qed.
