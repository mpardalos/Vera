From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
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
From vera Require Import Variables.
From vera Require Import Tactics.
From vera Require SMTQueries.
Import VerilogSemantics.CombinationalOnly.

From vera Require Import BVList.
Import BITVECTOR_LIST.

From vera Require SMTLib.

Import ListNotations.
Import SigTNotations.
Import MonadLetNotation.
Import Verilog.Notations.

Local Open Scope list.
Local Open Scope monad_scope.
Local Open Scope verilog_scope.

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

Definition verilog_to_smt_var (t : VarTag) (var : Var.t) : SMTLib.const_sym :=
  {|
    SMTLib.symName := tag_name t (Var.varName var);
    SMTLib.symSort := SMTLib.Sort_BitVec (Var.varType var)
  |}.

Definition smt_to_verilog_var (sym : SMTLib.const_sym) : option (VarTag * Var.t)  :=
  let* (t, name) := untag_name (SMTLib.symName sym) in
  let* w := match SMTLib.symSort sym with
            | SMTLib.Sort_BitVec w => Some w
	    | _ => None
	    end in
  let* prf := opt_dec (w > 0)%N in
  Some (t, Var.MkVariable name w prf).

Lemma verilog_to_smt_to_verilog_var t var : smt_to_verilog_var (verilog_to_smt_var t var) = Some (t, var).
Proof.
  unfold smt_to_verilog_var, verilog_to_smt_var.
  destruct var.
  simpl. rewrite untag_tag_name. monad_inv.
  - replace g with varTypeWf by (apply proof_irrelevance).
    reflexivity.
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
  LocationSet.InBounds C ->
  RegisterState.defined_value_for C (execution_of_valuation tag ρ).
Proof.
  intros Hwf loc Hin.
  specialize (Hwf loc Hin).
  unfold execution_of_valuation, RegisterState.get_location.
  rewrite XBV.bit_of_as_bv by assumption.
  destruct (BV.bitOf _ _); discriminate.
Qed.

Equations valuation_of_executions : execution -> execution -> SMTLib.valuation := {
  | e1, e2, {| SMTLib.symName := symName; SMTLib.symSort := SMTLib.Sort_BitVec w |} with untag_name symName, (dec (w > 0)%N) => {
    | Some (t, varName), left prf =>
        XBV.to_bv_def false (tag_choose t e1 e2 (Var.MkVariable varName w prf))
    | _, _ => default (SMTLib.Sort_BitVec w)
  }
  | e1, e2, {| SMTLib.symSort := s |} => default s
}.

Remark to_from_smt_value_inversion {n} idx (xbv : XBV.xbv n) :
  XBV.bitOf idx xbv <> RawXBV.X ->
  XBV.bitOf idx (XBV.from_bv (XBV.to_bv_def false xbv)) = XBV.bitOf idx xbv.
Proof.
  unfold XBV.bitOf, RawXBV.bitOf.
  XBV.bitvector_erase.
  subst.
  generalize dependent (N.to_nat idx). clear idx. 
  induction bv0; intros idx H; [reflexivity|].
  destruct idx; simpl.
  - destruct a; simpl in *.
    + contradiction.
    + reflexivity.
    + reflexivity.
  - simpl in H.
    apply IHbv0.
    exact H.
Qed.

Lemma execution_of_valuation_left_match_on e1 e2 ls :
  RegisterState.defined_value_for ls e1 ->
  execution_of_valuation VerilogLeft
    (valuation_of_executions e1 e2) =( ls )= e1.
Proof.
  intros Hdefined loc Hin.
  pose proof (Hdefined _ Hin) as Hnot_x.
  unfold RegisterState.get_location, execution_of_valuation in *.
  destruct loc as [[varName varType] idx]; simpl in *.
  unfold verilog_to_smt_var. simpl.
  simp valuation_of_executions.
  rewrite untag_tag_name.
  simpl.
  rewrite (dec_yes varTypeWf).
  apply to_from_smt_value_inversion.
  apply Hnot_x.
Qed.

Lemma execution_of_valuation_right_match_on e1 e2 ls :
  RegisterState.defined_value_for ls e2 ->
  execution_of_valuation VerilogRight
    (valuation_of_executions e1 e2) =( ls )= e2.
Proof.
  intros Hdefined loc Hin.
  pose proof (Hdefined _ Hin) as Hnot_x.
  unfold RegisterState.get_location, execution_of_valuation in *.
  destruct loc as [[varName varType] idx]; simpl in *.
  unfold verilog_to_smt_var. simpl.
  simp valuation_of_executions.
  rewrite untag_tag_name.
  simpl.
  rewrite (dec_yes varTypeWf).
  apply to_from_smt_value_inversion.
  apply Hnot_x.
Qed.

Definition verilog_smt_match_states_partial
  (locs : LocationSet.t)
  (tag : VarTag)
  (regs : RegisterState.t)
  (ρ : SMTLib.valuation) : Prop :=
  regs =( locs )= execution_of_valuation tag ρ.

(* Might not be needed *)
Global Instance verilog_smt_match_states_partial_proper :
  Proper
    (LocationSet.Equal ==> eq ==> eq ==> eq ==> iff)
    verilog_smt_match_states_partial.
Proof.
  intros l1 l2 Heq tag ? <- regs ? <- ρ ? <-.
  split; intros H loc Hloc; apply H, Heq, Hloc.
Qed.

Global Instance Proper_verilog_smt_match_states_partial_subset :
  Proper
    (LocationSet.Subset --> eq ==> eq ==> eq ==> Basics.impl)
    verilog_smt_match_states_partial.
Proof.
  intros l1 l2 Hsub tag ? <- regs ? <- ρ ? <- H loc Hloc.
  apply H, Hsub, Hloc.
Qed.

Global Instance Proper_verilog_smt_match_states_partial_subset_flip :
  Proper
    (LocationSet.Subset ==> eq ==> eq ==> eq ==> Basics.flip Basics.impl)
    verilog_smt_match_states_partial.
Proof.
  intros l1 l2 Hsub tag ? <- regs ? <- ρ ? <- H loc Hloc.
  apply H, Hsub, Hloc.
Qed.

Lemma verilog_smt_match_states_execution_of_valuation_same C tag ρ :
  verilog_smt_match_states_partial C tag (execution_of_valuation tag ρ) ρ.
Proof.
  intros loc _. reflexivity.
Qed.

Lemma verilog_smt_match_states_partial_impl locs1 locs2 tag regs ρ :
  LocationSet.Subset locs1 locs2 ->
  verilog_smt_match_states_partial locs2 tag regs ρ ->
  verilog_smt_match_states_partial locs1 tag regs ρ.
Proof.
  intros Hsub H loc Hloc. apply H, Hsub, Hloc.
Qed.

Lemma verilog_smt_match_states_partial_set_reg_out locs tag r ρ var val :
  LocationSet.Disjoint (LocationSet.of_variable var) locs ->
  verilog_smt_match_states_partial locs tag (RegisterState.set_reg var val r) ρ <->
  verilog_smt_match_states_partial locs tag r ρ.
Proof.
  intro Hdisj.
  unfold verilog_smt_match_states_partial, "_ =( _ )= _".
  split.
  all: intros H loc Hloc; specialize (H loc Hloc).
  all: unfold RegisterState.get_location in *.
  all: destruct (dec (Location.var loc = var)) as [e|n];
    [ assert (~ LocationSet.In loc (LocationSet.of_variable var)) as Hnotin
        by (intro Hc; eapply Hdisj; apply LocationSet.inter_spec; eauto);
      rewrite LocationSet.of_variable_spec in Hnotin;
      assert (Var.varType var <= Location.idx loc)%N as Hoob
        by (apply N.nlt_ge; intro Hlt; apply Hnotin; auto)
    | ].
  all: try (rewrite RegisterState.set_reg_get_out in * by congruence; assumption).
  all: rewrite e in *.
  all: rewrite RegisterState.set_reg_get_in in *.
  all: rewrite ! XBV.bitOf_overflow in * by assumption.
  all: reflexivity.
Qed.

Lemma verilog_smt_match_states_partial_split_iff C1 C2 tag reg ρ :
  verilog_smt_match_states_partial (C1 ∪ C2) tag reg ρ <->
    (verilog_smt_match_states_partial C1 tag reg ρ
     /\ verilog_smt_match_states_partial C2 tag reg ρ).
Proof.
  unfold verilog_smt_match_states_partial.
  apply RegisterState.match_on_split_union.
Qed.

Lemma verilog_smt_match_states_partial_set_reg_elim C tag regs ρ var bv :
  (ρ (verilog_to_smt_var tag var) = bv) ->
  verilog_smt_match_states_partial C tag regs ρ ->
  verilog_smt_match_states_partial C tag (RegisterState.set_reg var (XBV.from_bv bv) regs) ρ.
Proof.
  intros Hvar Hrest loc Hloc.
  specialize (Hrest loc Hloc).
  unfold RegisterState.get_location, execution_of_valuation in *.
  destruct (dec (Location.var loc = var)) as [e|n].
  - rewrite e.
    rewrite RegisterState.set_reg_get_in.
    rewrite Hvar. reflexivity.
  - rewrite RegisterState.set_reg_get_out by congruence.
    exact Hrest.
Qed.

Ltac unpack_verilog_smt_match_states_partial :=
  repeat match goal with
    | [ H: verilog_smt_match_states_partial (_ ∪ _) _ _ _ |- _ ] =>
        apply verilog_smt_match_states_partial_split_iff in H;
        destruct H
    | [ |- verilog_smt_match_states_partial (_ ∪ _) _ _ _ ] =>
        apply verilog_smt_match_states_partial_split_iff; split
    end.

Lemma verilog_smt_match_states_partial_defined_value_for C tag regs ρ :
  LocationSet.InBounds C ->
  verilog_smt_match_states_partial C tag regs ρ ->
  RegisterState.defined_value_for C regs.
Proof.
  intros Hwf Hmatch loc Hloc.
  specialize (Hwf loc Hloc). specialize (Hmatch loc Hloc).
  unfold RegisterState.get_location, execution_of_valuation in *.
  rewrite Hmatch.
  rewrite XBV.bit_of_as_bv by assumption.
  destruct (BV.bitOf _ _); discriminate.
Qed.

Lemma verilog_smt_match_states_partial_execution_match_on C tag ρ e :
    verilog_smt_match_states_partial C tag e ρ ->
    e =( C )= execution_of_valuation tag ρ.
Proof. trivial. Qed.

Lemma verilog_smt_match_states_partial_execution_defined_value_for C tag ρ e :
    LocationSet.InBounds C ->
    verilog_smt_match_states_partial C tag e ρ ->
    RegisterState.defined_value_for C e.
Proof. apply verilog_smt_match_states_partial_defined_value_for. Qed.

Lemma execution_of_valuation_inv tag ρ var bv :
  execution_of_valuation tag ρ var = XBV.from_bv bv ->
  ρ (verilog_to_smt_var tag var) = bv.
Proof.
  unfold execution_of_valuation.
  apply XBV.from_bv_injective.
Qed.

Lemma execution_match_on_verilog_smt_match_states_partial C tag ρ e :
    e =( C )= (execution_of_valuation tag ρ) ->
    verilog_smt_match_states_partial C tag e ρ.
Proof. trivial. Qed.
