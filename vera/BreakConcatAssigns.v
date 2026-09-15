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
From Stdlib Require Import NArith.
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
  Lemma assign_target_width_positive {w} (t : assign_target w) : (w > 0)%N.
  Proof.
    induction t; try lia.
    - apply Var.varTypeWf.
    - destruct slice; lia.
  Qed.

  Equations extract_assign_rhs {w} (rhs : expression w) (lo width : N)
      (wf : (w > 0)%N) (wf_width : (width > 0)%N) : expression width := {
    | IntegerLiteral _ val, lo, width, _, _ => IntegerLiteral width (XBV.extr val lo width)
    | rhs, lo, width, wf, wf_width =>
      Resize width
        (ShiftOp BinaryShiftRight rhs
          (IntegerLiteral _ (XBV.from_bv (BV.of_bits (RawBV.of_N_full lo))))
          wf _)
        wf_width
  }.
  Solve All Obligations with
    (destruct lo as [|p]; [cbn; lia | destruct p; cbn; lia]).

  Equations break_concat_assign {w} (t : assign_target w) : assign_target_wf t -> expression w -> list module_item := {
    | (@AssignConcat w_hi w_lo target_hi target_lo), wf, val :=
      break_concat_assign target_lo _
        (extract_assign_rhs val 0 w_lo
          (assign_target_width_positive (AssignConcat target_hi target_lo))
          (assign_target_width_positive target_lo))
      ++ break_concat_assign target_hi _
        (extract_assign_rhs val w_lo w_hi
          (assign_target_width_positive (AssignConcat target_hi target_lo))
          (assign_target_width_positive target_hi))
    | target, t_wf, val := [AlwaysComb (BlockingAssign target t_wf val)]
  }.
  Next Obligation. inv wf. assumption. Qed.
  Next Obligation. inv wf. assumption. Qed.

  Equations break_concat_assigns_module_body : list module_item -> list module_item := {
    | AlwaysComb (BlockingAssign target wf val) :: tl =>
      trace
        ("Break concat assign to " ++ to_string target)
        (break_concat_assign target wf val)
      ++ break_concat_assigns_module_body tl
    | [] => []
  }.

  Definition break_concat_assigns_vmodule {i o} (v : vmodule i o) : string + vmodule i o :=
    traceBracket ("Break concat assigns " ++ Verilog.modName v) (
      assert_dec (vmodule_sorted v) "Unsorted module in break_concat_assigns";;
      ret {|
        modName := modName v;
        modBody := break_concat_assigns_module_body (modBody v);
        modWfIODisjoint := modWfIODisjoint v;
        modWfInputsNoDup := modWfInputsNoDup v;
        modWfOutputsNoDup := modWfOutputsNoDup v;
      |}).
End definition.

Section accessed.
  Lemma extract_assign_rhs_reads {w} (rhs : expression w) lo width wf wf_width :
    LocationSet.Equal (expr_reads (extract_assign_rhs rhs lo width wf wf_width)) (expr_reads rhs).
  Proof.
    funelim (extract_assign_rhs rhs lo width wf wf_width).
    all: cbn; LocationSet.setdec.
  Qed.

  Lemma break_concat_assign_writes {w} (target : assign_target w) wf val :
    LocationSet.Equal
      (module_body_writes (break_concat_assign target wf val))
      (assign_target_writes target).
  Proof.
    funelim (break_concat_assign target wf val).
    all: simpl.
    all: try LocationSet.setdec; expect 1.
    rewrite module_body_writes_app, H, H0.
    LocationSet.setdec.
  Qed.
End accessed.

Section semantics.
  Lemma convert_shr_extr {n} (v : XBV.xbv n) lo w :
    (lo + w <= n)%N ->
    convert w (XBV.shr v lo) = XBV.extr v lo w.
  Proof.
    intros Hbound.
    funelim (convert w (XBV.shr v lo)); try lia.
    all: clear Heqcall.
    2: {
      assert (lo = 0%N) by lia; subst lo.
      destruct_rew.
      rewrite XBV.extr_full.
      XBV.bitvector_erase.
      apply RawXBV.shr_equation_1.
    }
    XBV.bitvector_erase.
    rewrite RawXBV.shr_as_concat, N2Nat.id.
    rewrite RawXBV.extr_of_concat_lo;
      try rewrite RawXBV.extr_width; try (unfold RawXBV.size; lia).
    rewrite RawXBV.extr_of_extr; try (unfold RawXBV.size; lia).
    rewrite N.add_0_r; reflexivity.
  Qed.

  Lemma eval_extract_assign_rhs {w} (rhs : expression w) lo width wf wf_width regs :
    (lo + width <= w)%N ->
    eval_expr regs (extract_assign_rhs rhs lo width wf wf_width) =
    XBV.extr (eval_expr regs rhs) lo width.
  Proof.
    funelim (extract_assign_rhs rhs lo width wf wf_width).
    all: intros Hbound; simp eval_expr; try reflexivity.
    all: simp eval_shiftop.
    all: rewrite XBV.to_N_from_bv.
    all: change (BV.to_N (BV.of_bits (RawBV.of_N_full lo)))
      with (RawBV.to_N (RawBV.of_N_full lo)).
    all: rewrite RawBV.to_N_of_N_full; simp eval_shiftop.
    all: apply convert_shr_extr; assumption.
  Qed.

  Lemma exec_module_body_app regs body1 body2 :
    exec_module_body (body1 ++ body2) regs =
    exec_module_body body2 (exec_module_body body1 regs).
  Proof.
    revert regs.
    induction body1; intros regs; simpl; simp exec_module_body; simpl.
    - reflexivity.
    - apply IHbody1.
  Qed.

  Lemma exec_break_concat_assign {w} (target : assign_target w) wf val regs :
    LocationSet.Disjoint (assign_target_writes target) (expr_reads val) ->
    exec_module_body (break_concat_assign target wf val) regs =
    set_target target (eval_expr regs val) regs.
  Proof.
    funelim (break_concat_assign target wf val).
    all: clear Heqcall; intros Hdisjoint; cbn in Hdisjoint.
    all: simp exec_module_body exec_module_item exec_statement set_target; simpl.
    all: try reflexivity. all: expect 1.
    rewrite exec_module_body_app.
    repeat match goal with
    | IH : forall regs, _ -> exec_module_body _ regs = _ |- _ =>
      rewrite IH by (rewrite extract_assign_rhs_reads; LocationSet.setdec)
    end.
    rewrite ! eval_extract_assign_rhs by lia.
    rewrite (Facts.eval_expr_change_regs _ val (set_target _ _ _) regs).
    2: apply Facts.set_target_preserve; LocationSet.setdec.
    reflexivity.
  Qed.

  Lemma exec_break_concat_assigns_module_body regs body :
    forall vars, module_items_sorted vars body ->
    exec_module_body (break_concat_assigns_module_body body) regs =
    exec_module_body body regs.
  Proof.
    funelim (break_concat_assigns_module_body body).
    all: clear Heqcall; intros vars Hsorted; inv Hsorted.
    all: simp exec_module_body; simpl.
    all: try reflexivity; try eauto.
    rewrite exec_module_body_app, exec_break_concat_assign by (simpl in *; LocationSet.setdec).
    simp exec_module_item exec_statement.
  Qed.
End semantics.

Section sort.
  #[local]
  Lemma break_concat_assign_sorted {w} (target : assign_target w) wf val vars :
    LocationSet.Subset (expr_reads val) vars ->
    LocationSet.Disjoint (assign_target_writes target) vars ->
    module_items_sorted vars (break_concat_assign target wf val).
  Proof.
    funelim (break_concat_assign target wf val).
    all: intros Hreads Hdisjoint; simpl in *.
    all: try (constructor; [LocationSet.setdec | exact Hdisjoint | constructor]);
      expect 1.
    apply module_items_sorted_app.
    - apply H; rewrite ? extract_assign_rhs_reads; LocationSet.setdec.
    - apply H0; rewrite ? extract_assign_rhs_reads, ? break_concat_assign_writes.
      + LocationSet.setdec.
      + pose proof wf as Hwf. inv Hwf.
        LocationSet.setdec.
  Qed.

  Lemma break_concat_assigns_sorted vars body :
    module_items_sorted vars body ->
    module_items_sorted vars (break_concat_assigns_module_body body).
  Proof.
    funelim (break_concat_assigns_module_body body).
    all: clear Heqcall; intros Hsorted; inv Hsorted.
    all: simpl.
    all: try (constructor; try assumption; eauto).
    rename_match (forall vars, module_items_sorted vars tl -> _) into IH.
    rename_match (LocationSet.Disjoint _ vars) into Hdisjoint.
    rename_match (module_items_sorted _ tl) into Hsorted_tl.
    apply module_items_sorted_app.
    - apply break_concat_assign_sorted; assumption.
    - apply IH.
      eapply module_items_sorted_permute_vars with
        (l := assign_target_writes target ∪ vars).
      + rewrite break_concat_assign_writes. LocationSet.setdec.
      + exact Hsorted_tl.
  Qed.
End sort.

Theorem break_concat_assigns_exact_equivalence {i o} (v1 v2 : vmodule i o) :
  break_concat_assigns_vmodule v1 = inr v2 ->
  v1 ~~~ v2.
Proof.
  unfold break_concat_assigns_vmodule. simpl.
  intros Hbreak.
  monad_inv.
  rename_match (vmodule_sorted v1) into Hsorted.
  apply exact_by_output_equality.
  intros initial.
  unfold run_vmodule; simpl.
  rewrite ! sort_module_items_stable.
  - erewrite exec_break_concat_assigns_module_body by exact Hsorted.
    reflexivity.
  - apply break_concat_assigns_sorted.
    exact Hsorted.
  - exact Hsorted.
Qed.
