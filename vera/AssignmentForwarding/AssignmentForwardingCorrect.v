From Stdlib Require Import BinNums.
From Stdlib Require Import List.
From Stdlib Require Import ProofIrrelevance.
From Stdlib Require Import String.
From Stdlib Require Import Setoid.

From Equations Require Import Equations.
From ExtLib Require Import Structures.Monads.

From vera Require Import Verilog.
Import Verilog.
From vera Require Import VerilogSemantics.
Import CombinationalOnly.
Import Facts.
Import ExactEquivalence.
From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import AssignmentForwarding.AssignmentForwarding.

Import ListNotations.
Import EqNotations.
Import MonadLetNotation.
Import SigTNotations.

Require Import VerilogSemantics.
Import CombinationalOnly.

Local Open Scope verilog.

Lemma not_in_app_iff A (x : A) l1 l2 : ~ In x (l1 ++ l2) <-> (~ In x l1 /\ ~ In x l2).
Proof.
  split; intros.
  - split; intro contra; contradict H; apply in_app_iff; crush.
  - destruct H as [H1 H2]. rewrite in_app_iff. intros []; contradiction.
Qed.

Ltac unpack_in :=
  repeat match goal with
         | [ H : ~ (In _ (_ ++ _)) |- _] => apply not_in_app_iff in H; destruct H
         | [ H : (In _ (_ ++ _)) |- _] => apply in_app_iff in H; destruct H
         | [ |- ~ In _ (_ ++ _) ] => apply not_in_app_iff; split
	 end.

Section Apply.
  Lemma apply_substitution_expr_no_effect {w} (e : expression w) v r :
    ~ In v (expr_reads e) ->
    apply_substitution_expr v r e = e.
  Proof.
    funelim (apply_substitution_expr v r e);
      intros; simp expr_reads apply_substitution_expr in *;
      unpack_in;
      try rewrite H by assumption;
      try rewrite H0 by assumption;
      try rewrite H1 by assumption;
      crush.
  Qed.
  
  Lemma apply_substitution_expr_correct {w} v r (e : expression w) regs :
    eval_expr regs r = regs v ->
    eval_expr regs (apply_substitution_expr v r e) = eval_expr regs e.
  Proof.
    funelim (apply_substitution_expr v r e);
      intros; simp apply_substitution_expr eval_expr;
      try rewrite H by assumption;
      try rewrite H0 by assumption;
      try rewrite H1 by assumption;
      try reflexivity.
  Qed.

  Lemma apply_substitution_module_body_valid v r (body : list module_item) regs :
    eval_expr regs r = regs v ->
    ~ In v (module_body_writes body) ->
    disjoint (module_body_writes body) (expr_reads r) ->
    exec_module_body regs (apply_substitution_module_body v r body) =
      exec_module_body regs body.
  Proof.
    revert regs.
    funelim (apply_substitution_module_body v r body); [reflexivity|].
    clear Heqcall.
    intros * Heval Hvalid Hreads_preserved.
    simp module_body_writes module_item_writes statement_writes in *. unpack_in.
    simp exec_module_body exec_module_item in *.
    destruct lhs; simp expr_reads exec_statement in *; simpl; try reflexivity; expect 1.
    disjoint_saturate.
    rewrite ! apply_substitution_expr_correct by assumption.
    destruct (eval_expr regs rhs) eqn:E; [|reflexivity].
    apply H; try assumption; expect 1.
    rewrite RegisterState.set_reg_get_out by crush.
    rewrite <- Heval.
    apply eval_expr_change_regs.
    apply RegisterState.match_on_set_reg_elim.
    assumption.
  Qed.
End Apply.

Lemma apply_substitution_expr_reads w var v r e :
  In var (expr_reads (apply_substitution_expr (w:=w) v r e)) ->
  (In var (expr_reads e) \/ In var (expr_reads r)).
Proof.
  induction e;
    intros; simp expr_reads apply_substitution_expr in *;
    unpack_in; try rewrite ! in_app_iff; try crush; expect 1.
  match type of H with context[dec ?P] =>
    destruct (dec P); crush
  end.
Qed.

Lemma apply_substitution_writes v r body :
  module_body_writes (apply_substitution_module_body v r body) = module_body_writes body.
Proof.
  funelim (apply_substitution_module_body v r body);
    simp module_body_writes module_item_writes statement_writes expr_reads in *;
    crush.
Qed.

Lemma disjoint_app_iff A (l1 l2 l3 : list A) :
  (disjoint l1 l3 /\ disjoint l2 l3) <-> (disjoint (l1 ++ l2) l3).
Proof.
  unfold disjoint.
  setoid_rewrite List.Forall_forall.
  setoid_rewrite in_app_iff.
  crush.
Qed.

Lemma list_subset_app_l A (l1 l2 l3 : list A) :
  list_subset l1 l2 ->
  list_subset l1 (l2 ++ l3).
Proof.
  unfold list_subset.
  rewrite ! Forall_forall. setoid_rewrite in_app_iff.
  crush.
Qed.

Lemma list_subset_app_r A (l1 l2 l3 : list A) :
  list_subset l1 l3 ->
  list_subset l1 (l2 ++ l3).
Proof.
  unfold list_subset.
  rewrite ! Forall_forall. setoid_rewrite in_app_iff.
  crush.
Qed.

Lemma apply_substitution_sorted vars v r body :
  ~ In v (module_body_writes body) ->
  disjoint (module_body_writes body) (expr_reads r) ->
  list_subset (expr_reads r) vars ->
  module_items_sorted vars body ->
  module_items_sorted vars (apply_substitution_module_body v r body).
Proof.
  intros Hno_write Hreads_stable Hreads_available Hsorted.
  funelim (apply_substitution_module_body v r body);
    simp module_body_writes module_item_writes statement_writes expr_reads in *;
    expect 1.
  clear Heqcall.
  inv Hsorted. unpack_in. disjoint_saturate.
  simp module_body_writes module_item_writes statement_writes
       module_body_reads module_item_reads statement_reads expr_reads
    in *.
  constructor.
  - simp module_body_writes module_item_writes statement_writes
       module_body_reads module_item_reads statement_reads expr_reads
    in *.
    unfold list_subset in *. rewrite Forall_forall in *.
    intros var Hvar_in. apply apply_substitution_expr_reads in Hvar_in.
    destruct Hvar_in; eauto.
  - eauto.
  - simp module_body_writes module_item_writes statement_writes
         expr_reads module_item_reads statement_reads expr_reads in *.
    apply H; eauto.
    apply list_subset_app_r. assumption.
Qed.

Lemma module_items_sorted_no_overwrite inputs body :
  module_items_sorted inputs body ->
  disjoint (module_body_writes body) inputs.
Proof.
  induction 1.
  - constructor.
  - simp module_body_writes.
    unfold disjoint in *.
    rewrite ! Forall_forall in *.
    setoid_rewrite in_app_iff.
    setoid_rewrite in_app_iff in IHmodule_items_sorted.
    crush.
Qed.

From Stdlib Require Import Relations.
From Stdlib Require Import Morphisms.

Global Instance Proper_list_subset_in A :
  Proper (eq ==> list_subset ==> Basics.impl) (@In A).
Proof.
  repeat intro. subst.
  unfold list_subset in *. rewrite Forall_forall in *.
  auto.
Qed.

Global Instance Proper_list_subset_disjoint A :
  Proper (list_subset --> list_subset --> Basics.impl) (@disjoint A).
Proof.
  repeat intro. subst.
  unfold Basics.flip, list_subset, disjoint in *. rewrite Forall_forall in *.
  crush.
Qed.

Lemma forward_assignments_body_correct vars regs body body' :
  NoDup (module_body_writes body) ->
  module_items_sorted vars body ->
  forward_assignments_body body = inr body' ->
  exec_module_body regs body' = exec_module_body regs body.
Proof.
  intros Hnodup Hsorted Hexec.
  funelim (forward_assignments_body body);
    rewrite <- Heqcall in *; clear Heqcall; inv Hexec;
    try reflexivity; expect 1.
  monad_inv.
  simp module_body_writes module_item_writes statement_writes expr_reads in *.
  inv Hnodup. inv Hsorted.
  simp
    module_body_writes module_item_writes statement_writes expr_reads
    module_body_reads module_item_reads statement_reads expr_reads
    in *.
  disjoint_saturate.
  simp exec_module_body exec_module_item exec_statement.
  destruct (eval_expr regs rhs) eqn:Heval; simpl; [|reflexivity].
  specialize (H ([var] ++ vars) (RegisterState.set_reg var x regs) l).
  rewrite H; cycle 1.
  - rewrite apply_substitution_writes. assumption.
  - apply apply_substitution_sorted; eauto.
    + rename_match (module_items_sorted _ tl) into Hsorted_tl.
      apply module_items_sorted_no_overwrite in Hsorted_tl. disjoint_saturate.
      rename_match (list_subset (expr_reads rhs) vars) into Hrhs_in_vars.
      rename_match (disjoint vars (module_body_writes tl)) into Hno_overwrite.
      rewrite Hrhs_in_vars. symmetry. apply Hno_overwrite.
    + apply list_subset_app_r. assumption.
  - reflexivity.
  - apply apply_substitution_module_body_valid.
    + rewrite RegisterState.set_reg_get_in.
      erewrite eval_expr_change_regs; [eassumption|].
      apply RegisterState.match_on_set_reg_elim.
      rename_match (list_subset (expr_reads rhs) vars) into Hrhs_in_vars.
      rewrite Hrhs_in_vars. assumption.
    + assumption.
    + rename_match (module_items_sorted _ tl) into Hsorted_tl.
      apply module_items_sorted_no_overwrite in Hsorted_tl. disjoint_saturate.
      rename_match (list_subset (expr_reads rhs) vars) into Hrhs_in_vars.
      rename_match (disjoint vars (module_body_writes tl)) into Hno_overwrite.
      rewrite Hrhs_in_vars. symmetry. apply Hno_overwrite.
Qed.

Lemma module_inputs_same v1 v2 :
  modVariableDecls v1 = modVariableDecls v2 ->
  module_inputs v1 = module_inputs v2.
Proof. unfold module_inputs. crush. Qed.

Lemma module_outputs_same v1 v2 :
  modVariableDecls v1 = modVariableDecls v2 ->
  module_outputs v1 = module_outputs v2.
Proof. unfold module_outputs. crush. Qed.

Lemma initial_state_same v1 v2 regs :
  modVariableDecls v1 = modVariableDecls v2 ->
  mk_initial_state v1 regs = mk_initial_state v2 regs.
Proof.
  unfold mk_initial_state.
  intros.
  erewrite module_inputs_same by eassumption.
  reflexivity.
Qed.

Lemma forward_assignments_body_writes body body' :
  forward_assignments_body body = inr body' ->
  module_body_writes body' = module_body_writes body.
Proof.
  intros H.
  funelim (forward_assignments_body body);
    rewrite <- Heqcall in *; clear Heqcall; monad_inv;
    [reflexivity|].
  simp module_body_writes module_item_writes statement_writes expr_reads.
  rewrite H by auto.
  rewrite apply_substitution_writes.
  reflexivity.
Qed. 

Lemma forward_assignments_body_sorted inputs body body' :
  NoDup (module_body_writes body) ->
  module_items_sorted inputs body ->
  forward_assignments_body body = inr body' ->
  module_items_sorted inputs body'.
Proof.
  intros Hnodup Hsorted Hforward.
  funelim (forward_assignments_body body);
    rewrite <- Heqcall in *; clear Heqcall; monad_inv;
    [assumption|].
  inv Hsorted.
  autorewrite with
    expr_reads module_item_reads statement_reads
    module_body_writes module_item_writes statement_writes
    in *.
  disjoint_saturate.
  constructor.
  - assumption.
  - autorewrite with
      expr_reads module_item_reads statement_reads
      module_body_writes module_item_writes statement_writes
      in *. constructor; auto.
  - eapply H.
    + rewrite apply_substitution_writes. assumption.
    + apply apply_substitution_sorted; eauto.
      * rename_match (module_items_sorted _ tl) into Hsorted_tl.
        apply module_items_sorted_no_overwrite in Hsorted_tl. disjoint_saturate.
        rename_match (list_subset (expr_reads rhs) inputs) into Hrhs_in_vars.
        rename_match (disjoint inputs (module_body_writes tl)) into Hno_overwrite.
	rewrite Hrhs_in_vars. symmetry. apply Hno_overwrite.
      * apply list_subset_app_r. assumption.
    + reflexivity.
Qed.

Lemma forward_assignments_correct regs v1 v2 :
  forward_assignments v1 = inr v2 ->
  run_vmodule v1 regs = run_vmodule v2 regs.
Proof.
  intros.
  unfold forward_assignments, run_vmodule, opt_to_sum in *.
  monad_inv. simpl in *.
  rewrite ! sort_module_items_stable
    by eauto using forward_assignments_body_sorted.
  replace (mk_initial_state
     {| modName := modName v1; modVariableDecls := modVariableDecls v1; modBody := l |} regs)
     with (mk_initial_state v1 regs) by now apply initial_state_same.
  symmetry.
  eapply forward_assignments_body_correct; eassumption.
Qed.

Lemma equal_exact_equivalence v1 v2 :
  module_inputs v1 = module_inputs v2 ->
  module_outputs v1 = module_outputs v2 ->
  (forall regs, run_vmodule v1 regs = run_vmodule v2 regs) ->
  v1 ~~~ v2.
Proof.
  intros Hinputs Houtputs Hmatch.
  constructor; try eassumption; expect 1.
  intros regs.
  unfold "⇓".
  rewrite Hinputs, Houtputs, Hmatch.
  reflexivity.
Qed.

Lemma assignment_forwarding_exact_equivalence v1 v2 :
  AssignmentForwarding.forward_assignments v1 = inr v2 ->
  v1 ~~~ v2.
Proof.
  intros H.
  apply equal_exact_equivalence.
  - apply module_inputs_same.
    unfold forward_assignments in *. monad_inv. reflexivity.
  - apply module_outputs_same.
    unfold forward_assignments in *. monad_inv. reflexivity.
  - intros.
    apply forward_assignments_correct.
    assumption.
Qed.

Print Assumptions assignment_forwarding_exact_equivalence.
