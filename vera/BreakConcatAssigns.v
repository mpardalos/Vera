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

  Equations break_concat_assign {A w}
      (mk_item : forall w' (t': assign_target w'), assign_target_wf t' -> expression w' -> A)
      (t : assign_target w)
      : assign_target_wf t -> expression w -> list A := {
    | mk_item, (@AssignConcat w_hi w_lo target_hi target_lo), wf, val :=
      break_concat_assign mk_item target_lo _
        (extract_assign_rhs val 0 w_lo)
      ++ break_concat_assign mk_item target_hi _
        (extract_assign_rhs val w_lo w_hi)
    | mk_item, target, t_wf, val := [mk_item _ target t_wf val]
  }.
  Next Obligation. inv wf. assumption. Qed.
  Next Obligation. inv wf. assumption. Qed.

  Local Obligation Tactic := idtac.

  Equations break_concat_assigns_module_body
      (body : list module_item) : string + list module_item by struct body := {
    | Initial stmt :: tl => 
      let* tl' := break_concat_assigns_module_body tl in
      inr (Initial stmt :: tl')
    | AlwaysComb (BlockingAssign target wf val) :: tl =>
      let* tl' := break_concat_assigns_module_body tl in
      inr (break_concat_assign (fun w t wf val => AlwaysComb (BlockingAssign t wf val)) target wf val ++ tl')
    | AlwaysComb _ :: _ => inl "Expected blocking assignment in always_comb in BreakConcatAssigns"
    | AlwaysFF (NonblockingAssign target wf val) :: tl =>
      let* tl' := break_concat_assigns_module_body tl in
      inr (break_concat_assign (fun w t wf val => AlwaysFF (NonblockingAssign t wf val)) target wf val ++ tl')
    | AlwaysFF _ :: _ => inl "Expected nonblocking assignment in always_ff in BreakConcatAssigns"
    | ConcurrentAssertion expr :: tl =>
      let* tl' := break_concat_assigns_module_body tl in
      inr (ConcurrentAssertion expr :: tl')
    | [] => inr []
  }.

  Definition break_concat_assigns_vmodule {i o} (v : vmodule i o) : string + vmodule i o :=
    traceBracket ("Break concat assigns " ++ Verilog.modName v) (
      assert_dec (vmodule_sorted v) "Unsorted module in break_concat_assigns";;
      let* body := break_concat_assigns_module_body (modBody v) in
      ret {|
        modName := modName v;
        modBody := body;
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

  Lemma break_concat_assign_writes {w} mk_item (target : assign_target w) wf val :
    (forall w (target' : assign_target w) wf' val', LocationSet.Equal
      (module_item_writes_blocking (mk_item _ target' wf' val'))
      (assign_target_writes target')) ->
    LocationSet.Equal
      (module_body_writes_blocking (break_concat_assign mk_item target wf val))
      (assign_target_writes target).
  Proof.
    intros Hwrites. revert wf val.
    induction target as [var | loc bound | width slice | wh wl hi IHhi lo IHlo].
    all: intros Hwf val.
    all: simp break_concat_assign; simpl.
    (* Passthrough cases *)
    all: try (rewrite Hwrites; solve [reflexivity | LocationSet.setdec]).
    all: expect 1.
    (* Actual concat assign *)
    rewrite module_body_writes_blocking_app, IHhi, IHlo.
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
    exec_module_body regs (break_concat_assign (fun w t wf val => AlwaysComb (BlockingAssign t wf val)) target wf val) =
    set_target regs target (eval_expr regs val).
  Proof.
    revert wf val regs.
    induction target as [var | loc bound | width slice | wh wl hi IHhi lo IHlo];
    intros Hwf val regs Hdisjoint; simp break_concat_assign.
    all: simp exec_module_body exec_module_item exec_statement set_target; simpl.
    all: try reflexivity; expect 1.
    rewrite exec_module_body_app.
    rewrite IHlo, IHhi by
      (rewrite extract_assign_rhs_reads; simpl in Hdisjoint; LocationSet.setdec).
    rewrite ! eval_extract_assign_rhs by lia.
    rewrite (Facts.eval_expr_change_regs _ val (set_target _ _ _) regs).
    2: apply Facts.set_target_preserve; simpl in Hdisjoint; LocationSet.setdec.
    reflexivity.
  Qed.

  (* TODO: Prove once AlwaysFF execution semantics is defined. *)
  Lemma exec_break_concat_assign_nonblocking {w} (target : assign_target w) wf val regs :
    exec_module_body regs
      (break_concat_assign (fun w t wf val => AlwaysFF (NonblockingAssign t wf val)) target wf val) =
    exec_module_item regs (AlwaysFF (NonblockingAssign target wf val)).
  Proof. Admitted.

  Lemma exec_break_concat_assigns_module_body regs body body' :
    forall vars, module_items_sorted vars body ->
    break_concat_assigns_module_body body = inr body' ->
    exec_module_body regs body' = exec_module_body regs body.
  Proof.
    intros * Hsorted Hbreak.
    funelim (break_concat_assigns_module_body body).
    all: rewrite <- Heqcall in Hbreak; clear Heqcall; monad_inv.
    all: try reflexivity; inv Hsorted.
    all: simp exec_module_body; simpl.
    all: rewrite ? exec_module_body_app, ? exec_break_concat_assign,
      ? exec_break_concat_assign_nonblocking by (simpl in *; LocationSet.setdec).
    all: simp exec_module_item exec_statement.
    all: eauto.
  Qed.
End semantics.

Section sort.
  #[local]
  Lemma break_concat_assign_sorted {w} (target : assign_target w) wf val vars :
    LocationSet.Subset (expr_reads val) vars ->
    LocationSet.Disjoint (assign_target_writes target) vars ->
    module_items_sorted vars
      (break_concat_assign (fun w t wf val => AlwaysComb (BlockingAssign t wf val)) target wf val).
  Proof.
    revert wf val vars.
    induction target as [var | loc bound | width slice | wh wl hi IHhi lo IHlo];
    intros Hwf val vars Hreads Hdisjoint; simp break_concat_assign.
    all: try (constructor; [exact Hreads | exact Hdisjoint | constructor]).
    apply module_items_sorted_app.
    - apply IHlo; rewrite ? extract_assign_rhs_reads; simpl in Hdisjoint; LocationSet.setdec.
    - apply IHhi; rewrite ? extract_assign_rhs_reads, ? break_concat_assign_writes by reflexivity.
      + LocationSet.setdec.
      + inv Hwf. simpl in Hdisjoint. LocationSet.setdec.
  Qed.

  #[local]
  Lemma break_concat_assign_nonblocking_writes {w} (target : assign_target w) wf val :
    LocationSet.Equal
      (module_body_writes_blocking
        (break_concat_assign (fun w t wf val => AlwaysFF (NonblockingAssign t wf val)) target wf val)) {}.
  Proof.
    revert wf val.
    induction target as [var | loc bound | width slice | wh wl hi IHhi lo IHlo];
    intros Hwf val; simp break_concat_assign; simpl.
    all: try LocationSet.setdec.
    rewrite module_body_writes_blocking_app, IHhi, IHlo.
    LocationSet.setdec.
  Qed.

  #[local]
  Lemma break_concat_assign_nonblocking_sorted {w} (target : assign_target w) wf val vars :
    LocationSet.Subset (expr_reads val) vars ->
    module_items_sorted vars
      (break_concat_assign (fun w t wf val => AlwaysFF (NonblockingAssign t wf val)) target wf val).
  Proof.
    revert wf val vars.
    induction target as [var | loc bound | width slice | wh wl hi IHhi lo IHlo];
    intros Hwf val vars Hreads; simp break_concat_assign.
    all: try (constructor; [exact Hreads | simpl; LocationSet.setdec | constructor]).
    apply module_items_sorted_app.
    - apply IHlo. rewrite extract_assign_rhs_reads. exact Hreads.
    - apply IHhi. rewrite extract_assign_rhs_reads. LocationSet.setdec.
  Qed.

  Lemma break_concat_assigns_sorted vars body body' :
    module_items_sorted vars body ->
    break_concat_assigns_module_body body = inr body' ->
    module_items_sorted vars body'.
  Proof.
    intros Hsorted Hbreak.
    funelim (break_concat_assigns_module_body body).
    all: rewrite <- Heqcall in Hbreak; clear Heqcall; monad_inv.
    all: try solve [constructor].
    all: inv Hsorted.
    all: try solve [constructor; eauto].
    all: apply module_items_sorted_app;
      [solve [apply break_concat_assign_sorted; assumption
             |apply break_concat_assign_nonblocking_sorted; assumption] | ].
    all: rewrite ? break_concat_assign_nonblocking_writes.
    all: rewrite ? break_concat_assign_writes by reflexivity.
    all: eapply module_items_sorted_permute_vars; [|eauto]; cbn; LocationSet.setdec.
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
  - erewrite <- exec_break_concat_assigns_module_body by eassumption.
    reflexivity.
  - eapply break_concat_assigns_sorted; eassumption.
  - exact Hsorted.
Qed.
