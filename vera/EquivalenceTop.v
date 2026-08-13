From vera Require Verilog.
Import Verilog.Verilog.
Import Verilog.Notations.
From vera Require Import Variables.
From vera Require VerilogSemantics.
Import VerilogSemantics.Sort.
From vera Require Import VerilogSMT.
From vera Require Import VerilogSimpl.
From vera Require Import BreakConstAssigns.
From vera Require Import DropUnused.
From vera Require VerilogEquivalence.
From vera Require Import Common.
From vera Require Import VerilogSemantics.
From vera Require Import Tactics.
From vera Require Import Decidable.
Import CombinationalOnly.
Import DefinedEquivalence.
Import ExactEquivalence.

From ExtLib Require Import Structures.Monads.

From Stdlib Require Import String.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import ProofIrrelevance.

From Equations Require Import Equations.

Import MonadLetNotation.
Local Open Scope monad_scope.
Local Open Scope string.
Local Open Scope verilog_scope.

Module Pass.
  Record t := Mk {
    pass_name : string;
    pass_apply : forall [i o], vmodule i o -> string + vmodule i o;
    pass_correct : forall [i o] (v1 v2 : vmodule i o), pass_apply v1 = inr v2 -> v1 ~~~ v2
  }.

  #[local]
  Obligation Tactic := intros.

  #[program]
  Definition pure
    (name : string)
    (f : forall {i o}, vmodule i o -> vmodule i o)
    (f_correct : forall {i o} (v : vmodule i o), f v ~~~ v)
    : t := {|
      pass_name := name;
      pass_apply _ _ v := ret (f v);
    |}.
  Next Obligation. inv H. symmetry. apply f_correct. Qed.

  #[program]
  Definition compose (p1 p2 : t) : t := {|
    pass_name := pass_name p1 ++ " ∘ " ++ pass_name p2;
    pass_apply _ _ v :=
      let* v' := pass_apply p1 v in
      pass_apply p2 v'
  |}.
  Next Obligation.
    simpl in H.
    monad_inv.
    transitivity v.
    - eapply pass_correct. eassumption.
    - eapply pass_correct. eassumption.
  Qed.
End Pass.

Import (coercions) Pass.

Declare Scope pass_scope.
Delimit Scope pass_scope with pass.

Infix "∘" := Pass.compose (at level 20, right associativity) : pass_scope.

Local Open Scope pass.

Section sort.
  Import SigTNotations.

  Program Definition sort_module_body {i o} (v : vmodule i o)
    : string
      + {
        sorted : list module_item
        & sort_module_items (LocationSet.of_varset (VarSet.of_list (module_inputs v))) (modBody v) = Some sorted
      } :=
    match sort_module_items (LocationSet.of_varset (VarSet.of_list (module_inputs v))) (modBody v) with
    | None => inl "Module not sortable"
    | Some sorted => inr (sorted; _)
    end.

  Lemma sort_module_body_spec {i o} (v : vmodule i o) sorted Hsort :
    sort_module_body v = inr (sorted; Hsort) ->
    sort_module_items
      (LocationSet.of_varset (VarSet.of_list (module_inputs v)))
      (modBody v) = Some sorted.
  Proof.
    unfold sort_module_body.
    destruct (sort_module_items
                (LocationSet.of_varset (VarSet.of_list (module_inputs v)))
                (modBody v)) eqn:E;
      intros; congruence.
  Qed.

  #[refine]
  Definition sort_vmodule {i o} (v : vmodule i o) : string + vmodule i o :=
    traceBracket ("Sort " ++ modName v) (
      let* (sorted_body; Hsort) := sort_module_body v in
      ret {|
        modName := modName v;
        modBody := sorted_body;
      |}
    ).
  Proof. all: destruct v; assumption. Defined.
  
  Theorem sort_vmodule_exact_equivalence {i o} (v1 v2 : vmodule i o) :
    sort_vmodule v1 = inr v2 ->
    v1 ~~~ v2.
  Proof.
    unfold sort_vmodule. intros H.
    simpl in H. monad_inv.
    pose proof (sort_module_body_spec _ _ _ E) as Hsort.
    apply equal_exact_equivalence; try reflexivity; expect 1.
    unfold run_vmodule. simpl.
    unfold module_inputs in *; simpl in *.
    apply functional_extensionality.
    intros regs. rewrite Hsort.
    rewrite sort_module_items_stable
      by eauto using sort_module_items_sorted.
    reflexivity.
  Qed.
End sort.

Definition sort_vmodule_pass : Pass.t :=
  Pass.Mk "Sort" (@sort_vmodule) (@sort_vmodule_exact_equivalence).
Definition simpl_vmodule_pass : Pass.t :=
  Pass.pure "Simpl" (@simpl_vmodule) (@simpl_vmodule_exact_equivalence).
Definition break_const_assigns_pass : Pass.t :=
  Pass.pure "BreakConstAssigns" (@break_const_assigns_vmodule) (@break_const_assigns_exact_equivalence).
Definition drop_unused_pass : Pass.t :=
  Pass.Mk "DropUnused" (@drop_unused) (@drop_unused_exact_equivalence).

Definition verilog_pipeline : Pass.t :=
  sort_vmodule_pass
  ∘ simpl_vmodule_pass
  ∘ break_const_assigns_pass
  ∘ drop_unused_pass.

Definition lower_verilog :=
  Pass.pass_apply verilog_pipeline.

Import EqNotations.

Definition verilog_to_smt_general {i o} t (verilog : vmodule i o) : sum string SMTQueries.query :=
  let* verilog' := Pass.pass_apply verilog_pipeline verilog in
  VerilogToSMT.verilog_to_smt t verilog'.

Definition rew_interface {i1 o1 i2 o2} (inputs_eq : i1 = i2) (outputs_eq : o1 = o2) (v : vmodule i1 o1) : vmodule i2 o2 :=
  rew [fun i : list Var.t => vmodule i o2] inputs_eq in
  rew [fun o : list Var.t => vmodule i1 o] outputs_eq in v.

Search (_ = rew _ in _).

Lemma rew_interface_refl {i o} (inputs_eq : i = i) (outputs_eq : o = o) (v : vmodule i o) :
  rew_interface inputs_eq outputs_eq v = v.
Proof. unfold rew_interface. rewrite <- ! eq_rect_eq. reflexivity. Qed.
  
Definition equivalence_query_general {i1 o1 i2 o2} (verilog1 : vmodule i1 o1) (verilog2 : vmodule i2 o2)
    : sum string SMTQueries.query :=
  let* verilog1' := Pass.pass_apply verilog_pipeline verilog1 in
  let* verilog2' := Pass.pass_apply verilog_pipeline verilog2 in

  let* inputs_eq := assert_dec (i2 = i1) "Incompatible inputs" in
  let* outputs_eq := assert_dec (o2 = o1) "Incompatible outputs" in

  VerilogEquivalence.equivalence_query verilog1' (rew_interface inputs_eq outputs_eq verilog2').

(****** Continue here **********)

From vera Require Import VerilogSMT.
From vera Require Import SMTQueries.
From vera Require Import VerilogEquivalenceCorrectness.

From Stdlib Require Import Relations.
From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Setoid.

Lemma equivalence_query_clean_left {i o} (v1 v2 : vmodule i o) smt :
  VerilogEquivalence.equivalence_query v1 v2 = inr smt ->
  clean_module v1.
Proof.
  intros H.
  unfold VerilogEquivalence.equivalence_query in H.
  simpl in H.
  monad_inv.
  eapply VerilogToSMTCorrect.verilog_to_smt_clean.
  eassumption.
Qed.

Lemma equivalence_query_clean_right {i o} (v1 v2 : vmodule i o) smt :
  VerilogEquivalence.equivalence_query v1 v2 = inr smt ->
  clean_module v2.
Proof.
  intros H.
  unfold VerilogEquivalence.equivalence_query in H.
  simpl in H.
  monad_inv.
  eapply VerilogToSMTCorrect.verilog_to_smt_clean.
  eassumption.
Qed.

Opaque verilog_pipeline.

Theorem equivalence_query_general_unsat_correct {i o} (v1 : vmodule i o) (v2 : vmodule i o) smt :
  equivalence_query_general v1 v2 = inr smt ->
  (forall ρ, ~ satisfied_by ρ smt) ->
  v1 ~~ v2.
Proof.
  unfold equivalence_query_general.
  intros. monad_inv.
  rewrite rew_interface_refl in *.
  rewrite Pass.pass_correct with (v1:=v1) by eassumption.
  rewrite Pass.pass_correct with (v1:=v2) by eassumption.
  eapply VerilogEquivalenceCorrectness.equivalence_query_unsat_correct.
  all: try eassumption.
Qed.

Lemma transfer_execution {i o} (v v' : vmodule i o) e :
  v ~~~ v' ->
  v ⇓ e ->
  exists e',
    e =( LocationSet.of_varset (VarSet.of_list i) ∪ LocationSet.of_varset (VarSet.of_list o) )= e'
    /\ v' ⇓ e'.
Proof.
  unfold "⇓", "~~~", module_locations.
  intros Hequiv Hadmit.
  exists (run_vmodule v' e).
  unpack_goal.
  - symmetry.
    RegisterState.unpack_match_on.
    + apply Facts.run_vmodule_preserve_inputs.
    + rewrite <- Hequiv. assumption.
  - setoid_rewrite Facts.run_vmodule_preserve_inputs at 2.
    reflexivity.
Qed.

Lemma transfer_counterexample {i o} (v1 v1' v2 v2' : vmodule i o) e1 e2 :
  v1 ~~~ v1' ->
  v2 ~~~ v2' ->
  counterexample_execution v1 v2 e1 e2 ->
  exists e1' e2',
    e1 =( LocationSet.of_varset (VarSet.of_list i) ∪ LocationSet.of_varset (VarSet.of_list o) )= e1'
    /\ e2 =( LocationSet.of_varset (VarSet.of_list i) ∪ LocationSet.of_varset (VarSet.of_list o) )= e2'
    /\ counterexample_execution v1' v2' e1' e2'.
Proof.
  unfold counterexample_execution.
  intros Heq1 Heq2 [Hadmit1 [Hadmit2 [Hmatch_inputs Hmatch_outputs]]].
  destruct (transfer_execution v1 v1' e1) as [e1' [? ?]]; try assumption; expect 1.
  destruct (transfer_execution v2 v2' e2) as [e2' [? ?]]; try assumption; expect 1.
  exists e1'. exists e2'.
  unpack_goal.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - RegisterState.unpack_match_on.
    do 2 match goal with
    | H : _ =( ?l )= _ |- _ => (rewrite H || rewrite <- H); clear H
    end.
    assumption.
  - RegisterState.unpack_match_on.
    do 2 match goal with
    | H : _ =( ?l )= _ |- _ => (rewrite H || rewrite <- H); clear H
    end.
    assumption.
Qed.

Theorem equivalence_query_general_sat_correct {i o} (v1 v2 : vmodule i o) smt ρ :
  equivalence_query_general v1 v2 = inr smt ->
  satisfied_by ρ smt ->
  exists e1 e2, counterexample_execution v1 v2 e1 e2.
Proof.
  intros. unfold equivalence_query_general in *. monad_inv.
  rewrite rew_interface_refl in *.
  rename_match (ρ ⊧ smt) into Hsat.
  eapply equivalence_query_sat_correct in Hsat; try eassumption; expect 1.
  edestruct (transfer_counterexample v v1 v0 v2) as [e1' [e2' [? [? Hcex]]]].
  - symmetry. eapply Pass.pass_correct. eassumption.
  - symmetry. eapply Pass.pass_correct. eassumption.
  - eassumption.
  - exists e1'. exists e2'. exact Hcex.
Qed.

Print Assumptions equivalence_query_general_unsat_correct.
Print Assumptions equivalence_query_general_sat_correct.
