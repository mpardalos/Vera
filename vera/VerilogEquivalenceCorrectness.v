From vera Require Import Verilog.
From vera Require Import SMT.
From vera Require Import Common.
From vera Require Import Bitvector.
From vera Require VerilogTypecheck.
From vera Require VerilogCanonicalize.
From vera Require VerilogToSMT.
From vera Require Import VerilogEquivalence.
From vera Require VerilogSemantics.
From vera Require Import Tactics.

Import VerilogSemantics.CombinationalOnly.

From Coq Require Import Relations.
From Coq Require Import Sorting.Permutation.

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
  (v1 v2 : VerilogState)
  : Prop :=
  List.Forall
    (fun 'n =>
       exists v, regState v1 n = Some v
            /\ regState v2 n = Some v
            /\ ~ XBV.has_x v
    ) regs.

Definition no_errors (v : Verilog.vmodule) :=
  forall (input_vals : list XBV.t)
    (input_len_ok : length input_vals = length (Verilog.inputs v))
    (input_vals_defined : Forall (fun bv => ~ XBV.has_x bv) input_vals),
    let init := set_regs (List.combine (Verilog.inputs v) input_vals) (initial_state v) in
    exists final, multistep_eval init final.

Record equivalent (v1 v2 : Verilog.vmodule) : Prop :=
  MkEquivalent {
      interface_inputs_match : Verilog.inputs v1 = Verilog.inputs v2;
      interface_outputs_match : Verilog.outputs v1 = Verilog.outputs v2;
      no_errors1 : no_errors v1;
      no_errors2 : no_errors v2;
      behaviour_match :
      forall (input_vals : list XBV.t)
        (input_len_ok : length input_vals = length (Verilog.inputs v1))
        (input_vals_defined : Forall (fun bv => ~ XBV.has_x bv) input_vals)
        (final1 final2 : VerilogState),
        let init1 := set_regs (List.combine (Verilog.inputs v1) input_vals) (initial_state v1) in
        let init2 := set_regs (List.combine (Verilog.inputs v1) input_vals) (initial_state v2) in
        multistep_eval init1 final1 ->
        multistep_eval init2 final2 ->
        match_on_regs (Verilog.outputs v1) final1 final2;
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
End V.

Example assign_out_equivalent : equivalent assign_out assign_out.
Proof.
  constructor; try auto.
  - unfold no_errors. intros.
    repeat (destruct input_vals; try solve [simpl in *; discriminate]).
    eexists.
    repeat (unfold no_errors, assign_out, set_reg, initial_state; simpl).
    repeat (try econstructor; try unfold step; simpl; try simp run_step exec_module_item exec_statement).
  - unfold no_errors. intros.
    repeat (destruct input_vals; try solve [simpl in *; discriminate]).
    repeat (unfold no_errors, assign_out, set_reg, initial_state; simpl).
    eexists.
    repeat (try econstructor; try unfold step; simpl; try simp run_step exec_module_item exec_statement).
  - unfold match_on_regs.
    intros * ? ? * [eval1 blocked1] [eval2 blocked2].
    simpl in input_len_ok.
    repeat (destruct input_vals; try solve [simpl in *; discriminate]).
    repeat (destruct input_vals_defined; try solve [simpl in *; discriminate]).
    simpl in *.
    unfold assign_out, set_reg in eval1; simpl in eval1.
    unfold assign_out, set_reg in eval2; simpl in eval2.
    repeat constructor.
    unfold multistep_eval, multistep in *.
    eapply clos_trans_t1n in eval1; inversion eval1 as [ ? step1 | ? ? step1_1 step1_2 ]; subst;
      repeat (unfold step in *; simp run_step exec_module_item exec_statement eval_expr in *; simpl in * );
      unfold set_reg in *; simpl in *; try solve_by_inverts 3%nat.
    eapply clos_trans_t1n in eval2.
    inversion eval2 as [ ? step2 | ? ? step2_1 step2_2 ]; subst;
      repeat (unfold step in *; simp run_step exec_module_item exec_statement eval_expr in *; simpl in * );
      unfold set_reg in *; simpl in *; try solve_by_inverts 3%nat.
    inv step1.
    inv step2.
    eexists. intuition.
Qed.

Theorem canonicalize_correct v v' :
  VerilogCanonicalize.canonicalize_verilog v = inr v' ->
  equivalent v v'.
Admitted.

Definition match_on_regs_smt
  (regs : list string)
  (nameMap : StrFunMap.t (nat * SMTLib.sort))
  (v : VerilogState)
  (m : SMT.model SMT.no_uninterp_sorts)
  : Prop :=
  List.Forall
    (fun regName =>
       exists (varName : nat) (bv : BV.t),
         regState v regName = Some (XBV.from_bv bv) /\
           nameMap regName = Some (varName, SMTLib.Sort_BitVec (BV.size bv)) /\
           m varName [] (SMTLib.Sort_BitVec (BV.size bv)) = BVList.BITVECTOR_LIST.of_bits bv
    ) regs.

Definition match_verilog_model
  (nameMap : StrFunMap.t (nat * SMTLib.sort))
  (v : Verilog.vmodule)
  (m : SMT.model SMT.no_uninterp_sorts)
  : Prop :=
  forall (input_vals : list XBV.t)
    (input_len_ok : length input_vals = length (Verilog.inputs v))
    (input_vals_defined : Forall (fun bv => ~ XBV.has_x bv) input_vals)
    (final : VerilogState),
    let init := set_regs (List.combine (Verilog.inputs v) input_vals) (initial_state v) in
    multistep_eval init final ->
    match_on_regs_smt (Verilog.inputs v) nameMap init m ->
    match_on_regs_smt (Verilog.outputs v) nameMap final m
.

Theorem verilog_to_smt_correct start v q :
  VerilogToSMT.verilog_to_smt start v = inr q ->
  forall model,
  SMT.satisfied_by q (fun _ => False) model ->
  match_verilog_model (SMT.nameVerilogToSMT q) v model.
Admitted.

Lemma mapT_list_sum_in {A B E} (f : A -> sum E B) (l : list A) (l' : list B) :
  List.mapT_list f l = inr l' ->
  forall x, In x l -> exists y, f x = inr y /\ In y l'.
Proof.
  generalize dependent f. generalize dependent l'.
  induction l; intros * H * Hin; simpl in *.
  - contradiction.
  - destruct (f a) eqn:Hfa; try discriminate.
    destruct (mapT_list f l) as [|tl] eqn:Heq; try discriminate.
Admitted.

Theorem equivalence_query_canonical_correct verilog1 verilog2 query :
  equivalence_query_canonical verilog1 verilog2 = inr query ->
  SMT.unsat query ->
  equivalent verilog1 verilog2.
Proof.
  intros Hquery Hunsat.
  unfold equivalence_query_canonical in *.
  inv Hquery.
  unfold mk_equivalence_formulas in *.
  repeat (
      match goal with
      | [ H : (match ?m with _ => _ end) = _ |- _ ] =>
          destruct m eqn:?; try discriminate
      | [ H : inr _ = inr _ |- _ ] => inv H
      | [ H : assert_dec _ _ = inr _ |- _ ] => clear H
      | [ H : VerilogToSMT.verilog_to_smt _ _ = inr _ |- _ ] =>
          pose proof (verilog_to_smt_correct _ _ _ H); clear H
      | [ H : mapT_list _ _ = inr _ |- _ ] =>
          learn (mapT_list_sum_in _ _ _ H)
      end; simpl in *
    ).
  repeat match goal with
         | [ L : Learnt _ |- _ ] => clear L
         end.

  constructor.
  - congruence.
  - congruence.
  - admit. (* no_errors verilog1 *)
  - admit. (* no_errors verilog2 *)
  - simpl. intros.
    unfold match_on_regs.
    apply List.Forall_forall; intros outreg Houtreg.
    move Hunsat at bottom.
    unfold SMT.unsat in Hunsat.
    move H1 at bottom.
    destruct (H1 outreg ltac:(assumption)) as [? [ ? ? ]].
    repeat match goal with
           | [ H : context[match ?d with _ => _ end] |- _] =>
               destruct d eqn:?; subst; try discriminate
           | [ H : inr _ = inr _ |- _] => inv H
           end.
    destruct (regState final1 outreg) as [v|].
    + exists v. intuition.
        admit.
      * admit.
    + admit.
Admitted.

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
  constructor; simpl in *.
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
  - intros.
    specialize (behaviour_match1 input_vals ltac:(assumption) ltac:(assumption)).
    specialize (behaviour_match2 input_vals ltac:(assumption) ltac:(assumption)).
    assert (exists final', multistep_eval (set_regs (combine (Verilog.inputs v1) input_vals) (initial_state v2)) final') as H1. {
      unfold no_errors in *.
      rewrite <- interface_inputs_match2 in *.
      rewrite <- interface_inputs_match1 in *.
      simpl in *.
      eauto.
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
  - simpl in *. intros.
    rewrite <- interface_outputs_match1 in *.
    rewrite <- interface_inputs_match1 in *.
    apply match_on_regs_sym.
    eauto.
Qed.

Theorem equivalence_query_correct verilog1 verilog2 query :
  equivalence_query verilog1 verilog2 = inr query ->
  SMT.unsat query ->
  equivalent verilog1 verilog2.
Proof.
  intros Hquery Hunsat.
  unfold equivalence_query in *.
  inv Hquery.
  repeat
    match goal with
    | [ H : (match ?m with _ => _ end) = _ |- _ ] =>
        destruct m eqn:?; try discriminate
    end.
  repeat match goal with
         | [ H : VerilogCanonicalize.canonicalize_verilog _ = inr _ |- _ ] =>
             apply canonicalize_correct in H
         end.
  repeat match goal with
         | [ H : VerilogToSMT.verilog_to_smt _ _ = inr _ |- _ ] =>
             pose proof (verilog_to_smt_correct _ _ _ H); clear H
         end.
  intuition eauto using equivalent_trans, equivalent_sym, equivalence_query_canonical_correct.
Qed.

Print Assumptions equivalence_query_correct.
