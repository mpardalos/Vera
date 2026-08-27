From vera Require Import Verilog.
From vera Require Import Variables.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import Bitvector.
From vera Require Import Common.
From vera Require Import VerilogSemantics.
Import Verilog.
Import ExactEquivalence.
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
Import SigTNotations.
Opaque N.add N.sub.

Section definition.
  Equations break_const_assign {w} (t : assign_target w) : assign_target_wf t -> XBV.xbv w -> list module_item := {
    | (@AssignConcat w_hi w_lo target_hi target_lo), wf, val :=
      break_const_assign target_lo _ (XBV.extr val 0 w_lo)
      ++ break_const_assign target_hi _ (XBV.extr val w_lo w_hi)
    | target, t_wf, val := [AlwaysComb (BlockingAssign target t_wf (IntegerLiteral _ val))]
  }.
  Next Obligation. inv wf. assumption. Qed.
  Next Obligation. inv wf. assumption. Qed.

  Equations break_const_assigns_module_body : list module_item -> list module_item := {
    | AlwaysComb (BlockingAssign target wf (IntegerLiteral _ val)) :: tl =>
      trace
        ("Break const assign to " ++ to_string target)
        (break_const_assign target wf val)
      ++ break_const_assigns_module_body tl
    | mi :: tl => mi :: break_const_assigns_module_body tl
    | [] => []
  }.

  Definition break_const_assigns_vmodule {i o} (v : vmodule i o) : string + vmodule i o :=
    traceBracket ("Break const assigns " ++ Verilog.modName v) (
      assert_dec (vmodule_sorted v) "Unsorted module in break_const_assigns";;
      ret {|
        modName := modName v;
        modBody := break_const_assigns_module_body (modBody v);
        modWfIODisjoint := modWfIODisjoint v;
        modWfInputsNoDup := modWfInputsNoDup v;
        modWfOutputsNoDup := modWfOutputsNoDup v;
      |}).
End definition.

Section accessed.
  Lemma break_const_assign_writes {w} (target : assign_target w) wf val :
    LocationSet.Equal
      (module_body_writes (break_const_assign target wf val))
      (assign_target_writes target).
  Proof.
    funelim (break_const_assign target wf val).
    all: simpl.
    all: try LocationSet.setdec; expect 1.
    rewrite module_body_writes_app, H, H0.
    LocationSet.setdec.
  Qed.
End accessed.

Section semantics.
  Lemma exec_module_body_app regs body1 body2 :
    exec_module_body regs (body1 ++ body2) =
    exec_module_body (exec_module_body regs body1) body2.
  Proof.
    revert regs.
    induction body1; intros regs; simpl; simp exec_module_body; simpl.
    - reflexivity.
    - apply IHbody1.
  Qed.

  Lemma exec_break_const_assign {w} (target : assign_target w) wf val regs :
    exec_module_body regs (break_const_assign target wf val) =
    set_target regs target val.
  Proof.
    funelim (break_const_assign target wf val).
    all: simp exec_module_body exec_module_item exec_statement eval_expr set_target; simpl.
    all: try reflexivity. all: expect 1.
    rewrite exec_module_body_app, H, H0.
    reflexivity.
  Qed.

  Lemma exec_break_const_assigns_module_body regs body :
    exec_module_body regs (break_const_assigns_module_body body) =
    exec_module_body regs body.
  Proof.
    funelim (break_const_assigns_module_body body).
    all: clear Heqcall.
    all: simp exec_module_body; simpl.
    all: try reflexivity; try eauto.
    rename_match (forall regs, exec_module_body regs _ = _) into IH.
    rewrite exec_module_body_app, exec_break_const_assign, IH.
    reflexivity.
  Qed.
End semantics.

Section sort.
  #[local]
  Lemma break_const_assign_sorted {w} (target : assign_target w) wf val vars :
    LocationSet.Disjoint (assign_target_writes target) vars ->
    module_items_sorted vars (break_const_assign target wf val).
  Proof.
    funelim (break_const_assign target wf val).
    all: intros Hdisjoint; simpl in *.
    all: try (constructor; [LocationSet.setdec | exact Hdisjoint | constructor]);
      expect 1.
    apply module_items_sorted_app.
    - apply H. LocationSet.setdec.
    - apply H0. rewrite break_const_assign_writes.
      pose proof wf as Hwf. inv Hwf.
      LocationSet.setdec.
  Qed.

  Lemma break_const_assigns_sorted vars body :
    module_items_sorted vars body ->
    module_items_sorted vars (break_const_assigns_module_body body).
  Proof.
    funelim (break_const_assigns_module_body body).
    all: clear Heqcall; intros Hsorted; inv Hsorted.
    all: simpl.
    all: try (constructor; try assumption; eauto).
    rename_match (forall vars, module_items_sorted vars tl -> _) into IH.
    rename_match (LocationSet.Disjoint _ vars) into Hdisjoint.
    rename_match (module_items_sorted _ tl) into Hsorted_tl.
    apply module_items_sorted_app.
    - apply break_const_assign_sorted. exact Hdisjoint.
    - apply IH.
      eapply module_items_sorted_permute_vars with
        (l := assign_target_writes target ∪ vars).
      + rewrite break_const_assign_writes. LocationSet.setdec.
      + exact Hsorted_tl.
  Qed.
End sort.

Theorem break_const_assigns_exact_equivalence {i o} (v1 v2 : vmodule i o) :
  break_const_assigns_vmodule v1 = inr v2 ->
  v1 ~~~ v2.
Proof.
  unfold break_const_assigns_vmodule. simpl.
  intros Hbreak.
  monad_inv.
  rename_match (vmodule_sorted v1) into Hsorted.
  apply exact_by_output_equality.
  intros initial.
  unfold run_vmodule; simpl.
  rewrite ! sort_module_items_stable.
  - rewrite exec_break_const_assigns_module_body.
    reflexivity.
  - apply break_const_assigns_sorted.
    exact Hsorted.
  - exact Hsorted.
Qed.
