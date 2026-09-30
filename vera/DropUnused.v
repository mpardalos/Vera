From vera Require Import Verilog.
From vera Require Import Variables.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import Bitvector.
From vera Require Import Common.
Import Verilog.
From vera Require Import VerilogSemantics.
Import CombinationalOnly.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Programming.Show.

From Stdlib Require Import BinNums.
From Stdlib Require Import ZArith.
From Stdlib Require Import String.
From Stdlib Require Import List.

From Equations Require Import Equations.

Import MonadLetNotation.
Import ListNotations.
Import Verilog.Notations.
Local Open Scope monad_scope.
Local Open Scope string.
Local Open Scope list.
Local Open Scope verilog_scope.

Import EqNotations.
Arguments N.add _ _ : simpl never.
Arguments N.sub _ _ : simpl never.

Definition result := sum string.

(* This will create partially (and wholly) undriven variables *)

Equations module_body_keep_assigns :
    LocationSet.t ->
    list module_item ->
    result (LocationSet.t * list module_item) := {
  | keep, [] => inr (LocationSet.empty, []);
  | keep, (Initial _ :: _) => inl "Unexpected initial block in DropUnused"
  | keep, (AlwaysComb (Block _) :: body) => inl "Unexpected Block in DropUnused"
  | keep, (AlwaysComb (BlockingAssign lhs _ rhs) :: body)
    with (LocationSet.disjoint (assign_target_writes lhs) keep) => {
    | true =>
      let* (dropped', body') := module_body_keep_assigns keep body in
      inr (assign_target_writes lhs ∪ dropped', body')
    | false =>
      let* (dropped', body') := module_body_keep_assigns keep body in
      inr (dropped', AlwaysComb (BlockingAssign lhs _ rhs) :: body')
    }
  | keep, (AlwaysFF _ :: _) => inl "Unexpected always_ff block in DropUnused"
}.

Definition drop_unused1 {i o} (v : vmodule i o) : result (LocationSet.t * vmodule i o) :=
  traceBracket ("Drop unused (iteration) " ++ Verilog.modName v) (
    let external_vars :=
      LocationSet.union
        (LocationSet.of_varset (VarSet.of_list i))
        (LocationSet.of_varset (VarSet.of_list o)) in
    let keep_locations :=
        (external_vars ∪ module_body_reads (modBody v)) in
    let* (dropped, v') := module_body_keep_assigns keep_locations (modBody v) in
    inr (dropped, {|
      modName := modName v;
      modBody := v';
      modWfIODisjoint := modWfIODisjoint v;
      modWfInputsNoDup := modWfInputsNoDup v;
      modWfOutputsNoDup := modWfOutputsNoDup v;
    |})
  ).

Fixpoint drop_unused_rec {i o} (fuel : nat) (v : vmodule i o) : result (vmodule i o) :=
  match fuel with
  | 0 => ret v
  | S n =>
    let* (dropped, m') := drop_unused1 v in
    if LocationSet.is_empty (trace ("Dropped " ++ to_string (LocationSet.cardinal dropped) ++ " locations") dropped)
    then ret m'
    else drop_unused_rec n m'
  end.

Definition drop_unused {i o} (v : vmodule i o) : result (vmodule i o) :=
  traceBracket ("Drop unused " ++ Verilog.modName v) (
    assert_dec
      (Sort.module_items_sorted
        (LocationSet.of_varset (VarSet.of_list (Verilog.module_inputs v)))
        (modBody v))
      "Unsorted module in drop_internal";;
    drop_unused_rec (List.length (modBody v)) v
  ).

Lemma module_body_keep_assigns_reads keep dropped body body' :
  module_body_reads body ⊆ keep ->
  module_body_keep_assigns keep body = inr (dropped, body') ->
  module_body_reads body' ⊆ module_body_reads body.
Proof.
  intros Hreads_kept Hrun.
  funelim (module_body_keep_assigns keep body).
  all: rewrite <- Heqcall in Hrun; clear Heqcall.
  all: monad_inv. all: expect 3.
  all: simpl; simp exec_module_body; simpl.
  1: LocationSet.setdec.
  (* all: rewrite (surjective_pairing (module_body_keep_assigns keep body)); simpl in *. *)
  all: cbn in *.
  all: rewrite H by (reflexivity || LocationSet.setdec).
  all: LocationSet.setdec.
Qed.

Lemma module_body_keep_assigns_spec keep dropped init body body' :
  module_body_reads body ⊆ keep ->
  module_body_keep_assigns keep body = inr (dropped, body') ->
  exec_module_body init body' =( keep )= exec_module_body init body.
Proof.
  intros Hreads_kept Hrun.
  funelim (module_body_keep_assigns keep body).
  all: rewrite <- Heqcall in Hrun; clear Heqcall.
  all: monad_inv. all: expect 3.
  1: reflexivity.
  all: simp exec_module_body exec_module_item exec_statement; simpl in *.
  2: eapply H; LocationSet.setdec.
  apply LocationSet.disjoint_spec in Heq.
  rewrite Facts.exec_module_body_change_preserve.
  - eapply H.
    + LocationSet.setdec.
    + reflexivity.
  - symmetry. apply Facts.set_target_preserve.
    rewrite module_body_keep_assigns_reads.
    3: eassumption. all: LocationSet.setdec.
  - symmetry. apply Facts.set_target_preserve.
    LocationSet.setdec.
Qed.

Import ExactEquivalence.

Lemma module_body_keep_assigns_sorted keep dropped vars body body' :
  module_body_reads body ⊆ keep ->
  module_body_keep_assigns keep body = inr (dropped, body') ->
  module_items_sorted vars body ->
  module_items_sorted vars body'.
Proof.
  intros Hreads_kept Hrun Hsorted.
  funelim (module_body_keep_assigns keep body).
  all: rewrite <- Heqcall in Hrun; clear Heqcall.
  all: monad_inv. all: expect 3.
  1: solve [constructor].
  all: cbn in *.
  all: inv Hsorted.
  - apply LocationSet.disjoint_spec in Heq.
    eapply module_items_sorted_skip with (vars_skip := assign_target_writes lhs).
    + rewrite module_body_keep_assigns_reads.
      3: eassumption. all: LocationSet.setdec.
    + eapply H. all: intuition LocationSet.setdec.
  - constructor; try assumption; expect 1.
    eapply H. all: intuition LocationSet.setdec.
Qed.

Lemma drop_unused1_transfer_sorted {i o} dropped (v1 v2 : vmodule i o) :
  drop_unused1 v1 = inr (dropped, v2) ->
  vmodule_sorted v1 ->
  vmodule_sorted v2.
Proof.
  intros Hdrop Hsorted.
  destruct v1, v2.
  unfold drop_unused1 in Hdrop.
  simpl in *.
  monad_inv.
  eapply module_body_keep_assigns_sorted. 2: eassumption.
  - LocationSet.setdec.
  - exact Hsorted.
Qed.

Lemma drop_unused1_exact_equivalence {i o} dropped (v1 v2 : vmodule i o) :
  vmodule_sorted v1 ->
  drop_unused1 v1 = inr (dropped, v2) ->
  v1 ~~~ v2.
Proof.
  intros Hsorted H.
  apply exact_by_output_equality.
  unfold run_vmodule, mk_initial_state.
  intros.
  rewrite sort_module_items_stable by exact Hsorted.
  rewrite sort_module_items_stable by (eapply drop_unused1_transfer_sorted; eassumption).
  destruct v1, v2. unfold drop_unused1 in *. simpl in *.
  monad_inv.
  symmetry.
  eapply RegisterState.match_on_subset; cycle 1.
  - eapply module_body_keep_assigns_spec. 2: eassumption.
    LocationSet.setdec.
  - LocationSet.setdec.
Qed.

#[local] Opaque drop_unused1.

Theorem drop_unused_exact_equivalence {i o} (v1 v2 : vmodule i o) :
  drop_unused v1 = inr v2 ->
  v1 ~~~ v2.
Proof.
  unfold drop_unused. simpl.
  generalize (Datatypes.length (modBody v1)). intro fuel.
  intros H.
  monad_inv.
  revert v1 v2 m H.
  induction fuel.
  all: intros.
  all: simpl in H.
  all: monad_inv.
  - reflexivity.
  - eapply drop_unused1_exact_equivalence; eassumption.
  - transitivity v.
    + eapply drop_unused1_exact_equivalence; eassumption.
    + apply IHfuel; [|eassumption].
      eapply drop_unused1_transfer_sorted; eassumption.
Qed.
