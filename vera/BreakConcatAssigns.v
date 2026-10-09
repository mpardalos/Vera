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
Arguments N.add _ _ : simpl never.
Arguments N.sub _ _ : simpl never.

Definition break_concat_assigns_undefined : module_item -> list module_item. Admitted.
Extract Constant break_concat_assigns_undefined =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED: break_concat_assigns_undefined"")".

Section definition.
  Equations extract_assign_rhs {w} (rhs : expression (Logic w)) (lo : N)
      (width : positive) : expression (Logic width) := {
    | IntegerLiteral _ val, lo, width => IntegerLiteral width (XBV.extr val lo width)
    | rhs, lo, width =>
      Resize width
        (ShiftOp BinaryShiftRight rhs
          (IntegerLiteral (N.succ_pos (N.pred (RawBV.size (RawBV.of_N_full lo))))
            (rew _ in XBV.from_bv (BV.of_bits (RawBV.of_N_full lo)))))
  }.
  Solve All Obligations with
    (intros; rewrite N.succ_pos_spec; destruct lo as [|[p|p|]]; cbn; lia).

  Equations break_concat_assign {w} (t : assign_target w) : assign_target_wf t -> expression w -> list module_item := {
    | (@AssignConcat w_hi w_lo target_hi target_lo), wf, val :=
      break_concat_assign target_lo _
        (extract_assign_rhs val 0 w_lo)
      ++ break_concat_assign target_hi _
        (extract_assign_rhs val w_lo w_hi)
    | target, t_wf, val := [AlwaysComb (BlockingAssign target t_wf val)]
  }.
  Next Obligation. inv wf. assumption. Qed.
  Next Obligation. inv wf. assumption. Qed.

  Local Obligation Tactic := idtac.

  Equations break_concat_assigns_module_body
      (body : list module_item) : list module_item by struct body := {
    | (Initial s) :: tl =>
      break_concat_assigns_undefined (Initial s)
    | AlwaysComb (BlockingAssign target wf val) :: tl =>
        break_concat_assign target wf val ++ break_concat_assigns_module_body tl
    (* TODO: NonblockingAssign *)
    | AlwaysComb (NonblockingAssign target wf val) :: tl =>
      break_concat_assigns_undefined (AlwaysComb (NonblockingAssign target wf val))
    | AlwaysComb (Block stmts) :: tl =>
      break_concat_assigns_undefined (AlwaysComb (Block stmts))
    | AlwaysComb (If cond ifT ifF) :: tl =>
      break_concat_assigns_undefined (AlwaysComb (If cond ifT ifF))
    | AlwaysFF s :: tl =>
      break_concat_assigns_undefined (AlwaysFF s)
    | ConcurrentAssertion expr :: tl =>
      break_concat_assigns_undefined (ConcurrentAssertion expr)
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
  Lemma extract_assign_rhs_reads {w} (rhs : expression (Logic w)) lo width :
    LocationSet.Equal (expr_reads (extract_assign_rhs rhs lo width)) (expr_reads rhs).
  Proof.
    funelim (extract_assign_rhs rhs lo width).
    all: cbn; LocationSet.setdec.
  Qed.

  Lemma break_concat_assign_writes {w} (target : assign_target w) wf val :
    LocationSet.Equal
      (module_body_writes_blocking (break_concat_assign target wf val))
      (assign_target_writes target).
  Proof.
    funelim (break_concat_assign target wf val).
    all: simpl.
    all: try LocationSet.setdec; expect 1.
    rewrite module_body_writes_blocking_app, H, H0.
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

  Lemma eval_extract_assign_rhs {w} (rhs : expression (Logic w)) lo (width : positive) regs :
    (lo + width <= w)%N ->
    eval_expr regs (extract_assign_rhs rhs lo width) =
    XBV.extr (eval_expr regs rhs) lo width.
  Proof.
    funelim (extract_assign_rhs rhs lo width).
    all: intros Hbound; simp eval_expr; try reflexivity.
    all: simp eval_shiftop.
    all: rewrite <- (map_subst (@XBV.to_N)), rew_const.
    all: rewrite XBV.to_N_from_bv.
    all: change (BV.to_N (BV.of_bits (RawBV.of_N_full lo)))
      with (RawBV.to_N (RawBV.of_N_full lo)).
    all: rewrite RawBV.to_N_of_N_full; simp eval_shiftop.
    all: apply convert_shr_extr; assumption.
  Qed.

  Lemma exec_module_body_app regs body1 body2 :
    exec_module_body regs (body1 ++ body2) =
    exec_module_body (exec_module_body regs body1) body2.
  Proof.
    revert regs.
    induction body1; intros regs; simpl; simp exec_module_body; simpl.
    - reflexivity.
    - apply IHbody1.
  Qed.

  Lemma exec_break_concat_assign {w} (target : assign_target w) wf val regs :
    LocationSet.Disjoint (assign_target_writes target) (expr_reads val) ->
    exec_module_body regs (break_concat_assign target wf val) =
    set_target regs target (eval_expr regs val).
  Proof.
    funelim (break_concat_assign target wf val).
    all: clear Heqcall; intros Hdisjoint; cbn in Hdisjoint.
    all: simp exec_module_body exec_module_item exec_statement set_target; simpl.
    all: try reflexivity. all: expect 1.
    rewrite exec_module_body_app.
    repeat match goal with
    | IH : forall regs, _ -> exec_module_body regs _ = _ |- _ =>
      rewrite IH by (rewrite extract_assign_rhs_reads; LocationSet.setdec)
    end.
    rewrite ! eval_extract_assign_rhs by lia.
    rewrite (Facts.eval_expr_change_regs _ val (set_target _ _ _) regs).
    2: apply Facts.set_target_preserve; LocationSet.setdec.
    reflexivity.
  Qed.

  Lemma exec_break_concat_assigns_module_body regs body :
    forall vars, module_items_sorted vars body ->
    exec_module_body regs (break_concat_assigns_module_body body) =
    exec_module_body regs body.
  Proof.
    intros * Hsorted.
    funelim (break_concat_assigns_module_body body).
    - reflexivity.
    - admit. (* TODO: initial *)
    - inv Hsorted.
      simp exec_module_body; simpl.
      try reflexivity; try eauto.
      rewrite exec_module_body_app, exec_break_concat_assign by (simpl in *; LocationSet.setdec).
      simp exec_module_item exec_statement.
    - admit. (* TODO: NonblockingAssign *)
    - admit. (* TODO: Blocks *)
    - admit. (* TODO: If *)
    - admit. (* TODO: always_ff *)
    - admit. (* TODO: concurrent assertions *)
  Admitted.
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
    intros Hsorted.
    funelim (break_concat_assigns_module_body body).
    all: clear Heqcall.
    - constructor.
    - admit. (* TODO: initial *)
    - inv Hsorted.
      rename_match (forall vars, module_items_sorted vars tl -> _) into IH.
      rename_match (LocationSet.Disjoint _ vars) into Hdisjoint.
      rename_match (module_items_sorted _ tl) into Hsorted_tl.
      apply module_items_sorted_app.
      + apply break_concat_assign_sorted; assumption.
      + apply IH.
        eapply module_items_sorted_permute_vars with
          (l := assign_target_writes target ∪ vars).
        * rewrite break_concat_assign_writes. LocationSet.setdec.
        * exact Hsorted_tl.
    - admit. (* TODO: NonblockingAssign *)
    - admit. (* TODO: Blocks *)
    - admit. (* TODO: If *)
    - admit. (* TODO: always_ff *)
    - admit. (* TODO: concurrent assertions *)
  Admitted.
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
