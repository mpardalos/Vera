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
Opaque N.add N.sub.

(* This will create partially (and wholly) undriven variables *)

Equations module_body_keep_assigns :
    LocationSet.t ->
    list module_item ->
    (LocationSet.t * list module_item) := {
  | keep, [] => (LocationSet.empty, []);
  | keep, (AlwaysComb (BlockingAssign lhs _ rhs) :: body)
    with (LocationSet.disjoint (assign_target_writes lhs) keep) => {
    | true =>
      trace
        ("Dropping " ++ to_string (BlockingAssign lhs _ rhs))%string
        ( let (dropped', body') := module_body_keep_assigns keep body in
          (assign_target_writes lhs ∪ dropped', body'))
    | false =>
      let (dropped', body') := module_body_keep_assigns keep body in
      (dropped', AlwaysComb (BlockingAssign lhs _ rhs) :: body')
  }
}.

Definition drop_unused1 {i o} (v : vmodule i o) : string + (LocationSet.t * vmodule i o) :=
  traceBracket ("Drop unused (iteration) " ++ Verilog.modName v) (
    let external_vars :=
      LocationSet.union
        (LocationSet.of_varset (VarSet.of_list i))
        (LocationSet.of_varset (VarSet.of_list o)) in
    let keep_locations :=
        (external_vars ∪ module_body_reads (modBody v)) in
    let result := module_body_keep_assigns keep_locations (modBody v) in
    inr (fst result, {|
      modName := modName v;
      modBody := snd result;
      modWfIODisjoint := modWfIODisjoint v;
      modWfInputsNoDup := modWfInputsNoDup v;
      modWfOutputsNoDup := modWfOutputsNoDup v;
    |})
  ).

Fixpoint drop_unused_rec {i o} (fuel : nat) (v : vmodule i o) : string + vmodule i o :=
  match fuel with
  | 0 => ret v
  | S n =>
    let* (dropped, m') := drop_unused1 v in
    if LocationSet.is_empty (trace ("Dropped " ++ to_string (LocationSet.cardinal dropped) ++ " locations") dropped)
    then ret m'
    else drop_unused_rec n m'
  end.

Definition drop_unused {i o} (v : vmodule i o) : string + vmodule i o :=
  traceBracket ("Drop unused " ++ Verilog.modName v) (
    assert_dec
      (Sort.module_items_sorted
        (LocationSet.of_varset (VarSet.of_list (Verilog.module_inputs v)))
        (modBody v))
      "Unsorted module in drop_internal";;
    drop_unused_rec (List.length (modBody v)) v
  ).

Lemma module_body_keep_assigns_reads keep body :
  module_body_reads body ⊆ keep ->
  module_body_reads (snd (module_body_keep_assigns keep body)) ⊆ module_body_reads body.
Proof.
  funelim (module_body_keep_assigns keep body).
  all: intros Hreads_kept.
  all: simpl; simp exec_module_body; simpl.
  all: clear Heqcall.
  1: LocationSet.setdec.
  all: rewrite (surjective_pairing (module_body_keep_assigns keep body)); simpl in *.
  all: rewrite H by LocationSet.setdec.
  all: LocationSet.setdec.
Qed.

Lemma module_body_keep_assigns_spec keep init body :
  module_body_reads body ⊆ keep ->
  exec_module_body init (snd (module_body_keep_assigns keep body)) =( keep )= exec_module_body init body.
Proof.
  intros Hreads_kept.
  funelim (module_body_keep_assigns keep body).
  all: simpl; simp exec_module_body; simpl.
  all: clear Heqcall.
  1: reflexivity.
  all: rewrite (surjective_pairing (module_body_keep_assigns keep body)); simpl in *.
  all: simp exec_module_body exec_module_item exec_statement; simpl in *.
  2: apply H; LocationSet.setdec.
  apply LocationSet.disjoint_spec in Heq.
  rewrite Facts.exec_module_body_change_preserve.
  - apply H; LocationSet.setdec.
  - symmetry. apply Facts.set_target_preserve.
    rewrite module_body_keep_assigns_reads by LocationSet.setdec.
    LocationSet.setdec.
  - symmetry. apply Facts.set_target_preserve.
    LocationSet.setdec.
Qed.

Import ExactEquivalence.

Lemma module_body_keep_assigns_sorted keep vars body :
  module_body_reads body ⊆ keep ->
  module_items_sorted vars body ->
  module_items_sorted vars (snd (module_body_keep_assigns keep body)).
Proof.
  funelim (module_body_keep_assigns keep body).
  all: clear Heqcall.
  all: intros Hreads Hsorted.
  1: solve [constructor].
  all: cbn in *.
  all: rewrite (surjective_pairing (module_body_keep_assigns keep body)); simpl.
  all: inv Hsorted.
  - apply LocationSet.disjoint_spec in Heq.
    eapply module_items_sorted_skip with (vars_skip := assign_target_writes lhs).
    + rewrite module_body_keep_assigns_reads. all: LocationSet.setdec.
    + apply H. all: intuition LocationSet.setdec.
  - constructor; try assumption; expect 1.
    apply H. all: intuition LocationSet.setdec.
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
  apply module_body_keep_assigns_sorted.
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
  - apply module_body_keep_assigns_spec.
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
