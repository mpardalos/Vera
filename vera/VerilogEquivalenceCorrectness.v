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

From Equations Require Import Equations.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Data.Monads.EitherMonad.
Import MonadNotation.
Open Scope monad_scope.
Require Import ZArith.
Require Import String.

From Coq Require Import List.
Import ListNotations.
Import EqNotations.

Definition match_on_regs
  (regs : list (string * string))
  (v1 v2 : VerilogState)
  : Prop :=
  List.Forall
    (fun '(n1, n2) =>
       exists v, regState v1 n1 = Some v
            /\ regState v2 n2 = Some v
            /\ ~ XBV.has_x v
    ) regs.

Definition equivalent
  (inputs outputs : list (string * string))
  (v1 v2 : Verilog.vmodule)
  : Prop :=
  forall (input_vals : list XBV.t)
    (input_len_ok : length input_vals = length inputs)
    (input_vals_defined : Forall (fun bv => ~ XBV.has_x bv) input_vals)
    (final1 final2 : VerilogState),
    let init1 :=
      set_regs (List.map
                  (fun '((n, _), v) => (n, v))
                  (List.combine inputs input_vals))
        (initial_state v1)
    in
    let init2 :=
      set_regs (List.map
                  (fun '((_, n), v) => (n, v))
                  (List.combine inputs input_vals))
        (initial_state v2)
    in
    multistep_eval init1 final1 ->
    multistep_eval init2 final2 ->
    match_on_regs outputs final1 final2
.

Local Open Scope string.

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

#[local] Open Scope Z_scope.

Example assign_out_equivalent : equivalent [("in", "in")] [("out", "out")] assign_out assign_out.
Proof.
  unfold equivalent, match_on_regs.
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

Example assign_out_twostep_equivalent : equivalent [("in", "in")] [("out", "out")] assign_out assign_out_twostep.
Proof.
  unfold equivalent, match_on_regs.
  intros * ? ? * [eval1 blocked1] [eval2 blocked2].
  simpl in input_len_ok.
  repeat (destruct input_vals_defined; try solve [simpl in *; discriminate]).
  simpl in *.
  (* unfold assign_out, set_reg in eval1; simpl in eval1. *)
  (* unfold assign_out, set_reg in eval2; simpl in eval2. *)
  repeat constructor.
  unfold multistep_eval, multistep in *.
  eapply clos_trans_t1n in eval1; inversion eval1 as [ ? step1 | ? ? step1_1 step1_2 ]; subst;
    repeat (unfold step in *; simp run_step exec_module_item exec_statement eval_expr in *; simpl in * );
    unfold set_reg in *; simpl in *; try solve_by_inverts 3%nat.
  inv step1.
  eapply clos_trans_t1n in eval2; inversion eval2 as [ ? step2 | ? ? step2_1 step2_2 ]; subst;
    repeat (unfold step in *; simp run_step exec_module_item exec_statement eval_expr in *; simpl in * );
    unfold set_reg in *; simpl in *; try solve_by_inverts 3%nat.
  inv step2_1.
  inversion step2_2 as [ ? step2_2' | ? ? step2_2' step2_3 ]; subst;
    repeat (unfold step in *; simp run_step exec_module_item exec_statement eval_expr in *; simpl in * );
    unfold set_reg in *; simpl in *; try solve_by_inverts 3%nat.
  inv step2_2'.
  eexists. simpl.
  intuition. f_equal.
Admitted.

Definition inputs (v : Verilog.vmodule) : list string :=
  map_opt (fun p => match p with
                 | {|
                     Verilog.portDirection := PortIn;
                     Verilog.portName := name
                   |} => Some name
                 | _ => None
                 end)
    (Verilog.modPorts v).

Definition outputs (v : Verilog.vmodule) : list string :=
  map_opt (fun p => match p with
                 | {|
                     Verilog.portDirection := PortOut;
                     Verilog.portName := name
                   |} => Some name
                 | _ => None
                 end)
    (Verilog.modPorts v).

Theorem canonicalize_correct v v' :
  VerilogCanonicalize.canonicalize_verilog v = inr v' ->
  equivalent (List.map dupe (inputs v)) (List.map dupe (outputs v)) v v'.
Admitted.

Compute SMTLib.interp_fun_type SMT.no_uninterp_sorts [] (SMTLib.Sort_BitVec 5).

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
    (input_len_ok : length input_vals = length (inputs v))
    (input_vals_defined : Forall (fun bv => ~ XBV.has_x bv) input_vals)
    (final : VerilogState),
    let init := set_regs (List.combine (inputs v) input_vals) (initial_state v) in
    multistep_eval init final ->
    match_on_regs_smt (inputs v) nameMap init m ->
    match_on_regs_smt (outputs v) nameMap final m
.

Theorem verilog_to_smt_correct start v q :
  VerilogToSMT.verilog_to_smt start v = inr q ->
  forall model,
  SMT.satisfied_by q (fun _ => False) model ->
  match_verilog_model (SMT.nameVerilogToSMT q) v model.
Admitted.

Theorem equivalence_query_correct input_pairs output_pairs verilog1 verilog2 query :
  equivalence_query input_pairs output_pairs verilog1 verilog2 = inr query ->
  SMT.unsat query ->
  equivalent input_pairs output_pairs verilog1 verilog2.
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
  (* Owl goes here *)
Admitted.
