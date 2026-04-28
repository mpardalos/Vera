From Stdlib Require Import BinNums.
From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Relations.
From Stdlib Require Import Morphisms.

From Equations Require Import Equations.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Functor.

From vera Require Import Verilog.
Import Verilog.
From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import VerilogSemantics.
Import VerilogSemantics.CombinationalOnly.
Import VerilogSemantics.Facts.
Import VerilogSemantics.ExactEquivalence.

Import ListNotations.
Local Open Scope list.
Import EqNotations.
Import MonadLetNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Local Open Scope verilog.

Equations module_body_keep_vars (vars : list variable) (body : list module_item) : list (module_item) :=
  module_body_keep_vars vars [] := [];
  module_body_keep_vars vars (AlwaysComb (BlockingAssign var rhs) :: body) with dec (In var vars) := {
    | right _ => module_body_keep_vars vars body
    | left _ => AlwaysComb (BlockingAssign var rhs) :: module_body_keep_vars vars body
  };
  .

Definition decls_drop_internal := List.filter
  (fun d => match varDeclPort d with
          | Some _ => true
	  | None => false
	  end).

Definition drop_internal (m : vmodule) : string + vmodule :=
  assert_dec (list_subset (module_body_reads (modBody m)) (module_inputs m))
    "Internal read remains in drop_internal";;
  assert_dec ((module_items_sorted (module_inputs m) (modBody m)))
    "Unsorted module in drop_internal";;
  assert_dec (NoDup (module_body_writes (modBody m)))
    "Duplicate writes in drop_internal";;
  assert_dec (disjoint (module_inputs m) (module_body_writes (modBody m)))
    "Writes to inputs in drop_internal";;
  let decls := decls_drop_internal (modVariableDecls m) in
  let body := module_body_keep_vars (module_outputs m) (modBody m) in
  ret {|
    modName := modName m;
    modVariableDecls := decls;
    modBody := body
  |}.

Lemma decls_drop_internal_keep_inputs decls :
  Verilog.inputs_of_decls (decls_drop_internal decls) =
  inputs_of_decls decls.
Proof.
  funelim (Verilog.inputs_of_decls decls); simpl.
  - reflexivity.
  - rewrite Heq. simp inputs_of_decls. rewrite Heq. simpl.
    rewrite H. reflexivity.
  - rewrite Heq. simp inputs_of_decls. rewrite Heq. simpl.
    rewrite H. reflexivity.
  - rewrite Heq. simp inputs_of_decls.
Qed.

Lemma decls_drop_internal_keep_outputs decls :
  Verilog.outputs_of_decls (decls_drop_internal decls) =
  outputs_of_decls decls.
Proof.
  funelim (Verilog.outputs_of_decls decls); simpl.
  - reflexivity.
  - rewrite Heq. simp outputs_of_decls. rewrite Heq. simpl.
    rewrite H. reflexivity.
  - rewrite Heq. simp outputs_of_decls. rewrite Heq. simpl.
    rewrite H. reflexivity.
  - rewrite Heq. simp outputs_of_decls.
Qed.

Lemma module_items_sorted_permute l1 l2 body :
  Permutation l1 l2 ->
  module_items_sorted l1 body ->
  module_items_sorted l2 body.
Proof.
  intros Hpermutation Hsorted. revert l2 Hpermutation.
  induction Hsorted; constructor.
  - now rewrite <- Hpermutation.
  - now rewrite <- Hpermutation.
  - eapply IHHsorted.
    now rewrite Hpermutation.
Qed.

Global Instance Proper_module_items_sorted_permute :
  Proper
    (@Permutation _ ==> eq ==> iff)
    module_items_sorted.
Proof.
  intros l1 l2 Hpermutation ? _ []. split; intro H.
  - eapply module_items_sorted_permute; eassumption.
  - eapply module_items_sorted_permute; (symmetry + idtac); eassumption.
Qed.

Lemma module_items_sorted_skip l1 l2 body :
  disjoint l1 (module_body_reads body) ->
  module_items_sorted (l1 ++ l2) body ->
  module_items_sorted l2 body.
Proof.
  revert l1 l2.
  induction body; intros * Hdisjoint Hsorted; inv Hsorted; intros; constructor.
  - simp module_body_reads in *. disjoint_saturate.
    unfold list_subset, disjoint in *. rewrite Forall_forall in *.
    setoid_rewrite in_app_iff in H1. crush.
  - simp module_body_reads in *. disjoint_saturate. unpack_in.
    symmetry. assumption.
  - eapply IHbody; expect 2; cycle 1.
    + rewrite app_assoc.
      rewrite Permutation_app_comm with (l' := module_item_writes a).
      rewrite <- app_assoc.
      eassumption.
    + simp module_body_reads in *. disjoint_saturate.
      symmetry. assumption.
Qed.

Lemma module_items_sorted_add l1 l2 body :
  disjoint l1 (module_body_writes body) ->
  module_items_sorted l2 body ->
  module_items_sorted (l1 ++ l2) body.
Proof.
  revert l1 l2.
  induction body;
    intros * Hdisjoint Hsorted; inv Hsorted; intros; constructor;
    simp module_body_writes in *.
  - unfold list_subset, disjoint in *. rewrite Forall_forall in *.
    setoid_rewrite in_app_iff. crush.
  - unfold list_subset, disjoint in *. rewrite Forall_forall in *.
    setoid_rewrite in_app_iff in Hdisjoint. setoid_rewrite in_app_iff.
    crush.
  - disjoint_saturate.
    rewrite app_assoc.
    rewrite Permutation_app_comm with (l := module_item_writes a).
    rewrite <- app_assoc.
    eapply IHbody; expect 2; cycle 1.
    + assumption.
    + symmetry. assumption.
Qed.

Lemma module_items_sorted_skip1 var vars body :
  ~ In var (module_body_reads body) ->
  module_items_sorted (var :: vars) body ->
  module_items_sorted vars body.
Proof.
  intros.
  apply module_items_sorted_skip with (l1 := [var]).
  - constructor; crush.
  - crush.
Qed.

Lemma module_body_keep_vars_correct init vars inputs body :
  module_items_sorted inputs body ->
  NoDup (module_body_writes body) ->
  list_subset (module_body_reads body) inputs ->
  (exec_module_body init (module_body_keep_vars vars body))
    =( vars )=
  (exec_module_body init body).
Proof.
  revert init.
  funelim (module_body_keep_vars vars body).
  all: intros init Hsorted Hnodup Hreads.
  all: simp exec_module_body exec_module_item exec_statement; simpl.
  all: clear Heqcall.
  1: reflexivity.
  - inv Hsorted.
    simp module_body_writes module_item_writes statement_writes
         module_body_reads module_item_reads statement_reads expr_reads
      in *.
    unpack_list_subset. disjoint_saturate.
    apply H with (inputs:=inputs); try assumption; expect 1.
    eapply module_items_sorted_skip1; simpl in *; [|eassumption].
    unfold list_subset in *. rewrite Forall_forall in *. crush.
  - inv Hsorted.
    simp module_body_writes module_item_writes statement_writes
         module_body_reads module_item_reads statement_reads expr_reads
      in *.
    unpack_list_subset. disjoint_saturate.
    (* edestruct (eval_expr_has_values_some _ rhs) as [x Heval_rhs]; expect 2. {
     *   eapply RegisterState.has_value_for_impl; [|eassumption].
     *   simpl. apply Forall_forall. assumption. 
     * } *)
    (* rewrite Heval_rhs. *)
    simpl in *.
    rewrite H with (inputs:=inputs); try assumption; expect 2.
    + apply exec_module_body_change_preserve.
      * rewrite RegisterState.match_on_set_reg_elim; [reflexivity|].
        unfold list_subset in *. rewrite Forall_forall in *. crush.
      * rewrite RegisterState.match_on_set_reg_elim; [reflexivity|].
        assumption.
    + eapply module_items_sorted_skip1; simpl in *; [|eassumption].
      unfold list_subset in *. rewrite Forall_forall in *. crush.
Qed.

Lemma module_body_keep_vars_preserve init vars l inputs body :
  module_items_sorted inputs body ->
  NoDup (module_body_writes body) ->
  list_subset (module_body_reads body) inputs ->
  disjoint l (module_body_writes body) ->
  (exec_module_body init (module_body_keep_vars vars body))
    =( l )=
  (exec_module_body init body).
Proof.
  revert init.
  funelim (module_body_keep_vars vars body).
  all: intros init Hsorted Hnodup Hreads Hnot_written.
  all: simp exec_module_body exec_module_item exec_statement; simpl.
  all: clear Heqcall.
  all: try reflexivity; expect 2.
  - inv Hsorted.
    simp module_body_writes module_item_writes statement_writes
         module_body_reads module_item_reads statement_reads expr_reads
      in *.
    unpack_list_subset. disjoint_saturate.
    apply H with (inputs:=inputs); try assumption.
    + eapply module_items_sorted_skip1; simpl in *; [|eassumption].
      unfold list_subset in *. rewrite Forall_forall in *. crush.
    + symmetry. assumption.
  - inv Hsorted.
    simp module_body_writes module_item_writes statement_writes
         module_body_reads module_item_reads statement_reads expr_reads
      in *.
    unpack_list_subset. disjoint_saturate.
    simpl in *.
    erewrite H with (inputs:=inputs); try assumption; expect 3; cycle 1.
    + eapply module_items_sorted_skip1; simpl in *; [|eassumption].
      unfold list_subset in *. rewrite Forall_forall in *. crush.
    + symmetry. assumption.
    + apply exec_module_body_change_preserve.
      * rewrite RegisterState.match_on_set_reg_elim; [reflexivity|].
        unfold list_subset in *. rewrite Forall_forall in *. crush.
      * rewrite RegisterState.match_on_set_reg_elim; [reflexivity|].
        assumption.
Qed.

Lemma module_items_sorted_reads_subset inputs body :
  disjoint (module_body_writes body) inputs ->
  list_subset (module_body_reads body) inputs ->
  NoDup (module_body_writes body) ->
  module_items_sorted inputs body.
Proof.
  intros Hsubset.
  induction body.
  - constructor.
  - constructor;
      simp module_body_reads module_body_writes in *;
      disjoint_saturate; unpack_list_subset.
    + assumption.
    + assumption.
    + apply module_items_sorted_add.
      * unfold list_subset, disjoint in *. rewrite Forall_forall in *. crush.
      * apply IHbody; assumption.
Qed.

Lemma module_body_keep_vars_reads vars body :
  list_subset
    (module_body_reads (module_body_keep_vars vars body))
    (module_body_reads body).
Proof.
  funelim (module_body_keep_vars vars body);
    simp module_body_reads module_item_reads statement_reads expr_reads;
    try reflexivity;
    unfold list_subset in *; rewrite Forall_forall in *; setoid_rewrite in_app_iff;
    crush.
Qed.  

Lemma module_body_keep_vars_writes_subset_body vars body :
  list_subset
    (module_body_writes (module_body_keep_vars vars body))
    (module_body_writes body).
Proof.
  funelim (module_body_keep_vars vars body);
    simp module_body_writes module_item_writes statement_writes expr_reads;
    try reflexivity;
    unfold list_subset in *; rewrite Forall_forall in *; setoid_rewrite in_app_iff;
    crush.
Qed.  

Lemma module_body_keep_vars_writes_NoDup vars body :
  NoDup (module_body_writes body) ->
  NoDup (module_body_writes (module_body_keep_vars vars body)).
Proof.
  intros Hnodup.
  funelim (module_body_keep_vars vars body);
    simp module_body_writes module_item_writes statement_writes expr_reads in *.
  - simpl in *. inv Hnodup. constructor; auto.
    now rewrite module_body_keep_vars_writes_subset_body.
  - apply H. now inv Hnodup.
Qed.  

Theorem drop_internal_correct v1 v2 :
  drop_internal v1 = inr v2 ->
  v1 ~~~ v2.
Proof.
  intros H.
  unfold drop_internal in H.
  monad_inv.
  apply exact_by_output_equality.
  - symmetry. apply decls_drop_internal_keep_inputs.
  - symmetry. apply decls_drop_internal_keep_outputs.
  - intros *.
    unfold run_vmodule in *.
    unfold module_inputs, module_outputs in *; simpl in *.
    rewrite ! sort_module_items_stable in *; expect 3; cycle 1.
    + rewrite decls_drop_internal_keep_inputs.
      apply module_items_sorted_reads_subset.
      * rewrite module_body_keep_vars_writes_subset_body.
        symmetry. assumption.
      * rewrite module_body_keep_vars_reads.
        assumption.
      * apply module_body_keep_vars_writes_NoDup. assumption.
    + assumption.
    + unfold mk_initial_state, module_inputs in *; simpl in *.
      rewrite decls_drop_internal_keep_inputs in *.
      symmetry.
      RegisterState.unpack_match_on.
      * eapply module_body_keep_vars_preserve; try eassumption.
      * eapply module_body_keep_vars_correct; eassumption.
Qed.
