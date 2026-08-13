From vera Require Import Verilog.
From vera Require Import Variables.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import Bitvector.
From vera Require Import Common.
Import Verilog.
(* From vera Require VerilogSemantics. *)

From ExtLib Require Import Structures.Monads.

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

(* Program Definition simpl_resize {from : N} (to : N) (expr : expression from) (wf : (to > 0)%N) : expression to :=
 *   match dec (from < to)%N with
 *   | left _ => rew [expression] _ in Concatenation (IntegerLiteral _ (XBV.zeros (to - from))) expr
 *   | right _ => rew [expression] _ in RangeSelect expr (to - 1) 0 _ _
 *   end.
 * Next Obligation. lia. Qed.
 * Next Obligation. lia. Qed.
 * Next Obligation. apply N.compare_gt_iff in H. lia. Qed.
 * Next Obligation. lia. Qed. *)

Program Definition equalized_shiftop {w1 w2}
    (wf : (w1 > 0)%N) op (lhs : expression w1) (rhs : expression w2)
    : expression w1 :=
  Resize w1
    (ShiftOp op
      (Resize (N.max w1 w2) lhs _)
      (Resize (N.max w1 w2) rhs _)
      _ _)
    _.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

Show Obligation Tactic.

#[local]
Obligation Tactic :=
  simpl in *; Tactics.program_simplify;
  CoreTactics.equations_simpl;
  try Tactics.program_solve_wf;
  try solve [apply Var.varTypeWf];
  try lia.

Equations simpl_expr {w} : expression w -> expression w := {
  | UnaryOp op e => UnaryOp op (simpl_expr e)
  | ArithmeticOp op lhs rhs => ArithmeticOp op (simpl_expr lhs) (simpl_expr rhs)
  | BitwiseOp op lhs rhs => BitwiseOp op (simpl_expr lhs) (simpl_expr rhs)
  | @ShiftOp w1 w2 op lhs rhs _ _ with dec (w1 = w2) => {
    | left E => ShiftOp op (simpl_expr lhs) (simpl_expr rhs) _ _
    | right _ =>
      (* Shift operand widths must match in SMTLIB *)
      equalized_shiftop _ op (simpl_expr lhs) (simpl_expr rhs)
  }
  | Concatenation e1 e2 => Concatenation (simpl_expr e1) (simpl_expr e2)
  | Replication n e =>
    (* TODO: Convert replications to concats *)
    Replication n (simpl_expr e)
  | Conditional cond ifT ifF => Conditional (simpl_expr cond) (simpl_expr ifT) (simpl_expr ifF)
  | RangeSelect slice => RangeSelect slice
  | BitSelect vec (IntegerLiteral w idx) => BitSelect vec (IntegerLiteral w idx)
  | BitSelect vec idx =>
    (* No variable bitselect in SMTLIB. Also, the shift we add must be balanced, as above. *)
    Resize 1 (equalized_shiftop _ BinaryShiftRight (NamedExpression vec) idx) _
  | Resize to expr wf => Resize to (simpl_expr expr) wf
  | IntegerLiteral w val => IntegerLiteral w val
  | NamedExpression var => NamedExpression var
}.

Definition simpl_module_body : list module_item -> list module_item :=
    map (fun '(AlwaysComb (BlockingAssign lhs rhs)) => AlwaysComb (BlockingAssign lhs (simpl_expr rhs))).

Lemma simpl_module_body_writes mis :
  LocationSet.Equal
    (module_body_writes (simpl_module_body mis))
    (module_body_writes mis).
Proof.
  induction mis.
  - reflexivity.
  - destruct a as [[lhs rhs]]. simpl.
    rewrite IHmis. reflexivity.
Qed.

#[refine]
Definition simpl_vmodule {i o} (v : vmodule i o) : vmodule i o :=
  traceBracket ("Simplify " ++ Verilog.modName v) {|
    Verilog.modName := Verilog.modName v;
    Verilog.modBody := simpl_module_body (Verilog.modBody v);
  |}.
Proof. all: destruct v; assumption. Defined.

From vera Require Import VerilogSemantics.
Import (notations) RegisterState.
From vera Require Import Tactics.

From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import NArith.

Import CombinationalOnly.
Import EqNotations.
Local Open Scope verilog.

Lemma convert_extend_to_N from to (xbv : XBV.xbv from) val :
  (to >= from)%N ->
  XBV.to_N xbv = Some val ->
  XBV.to_N (convert to xbv) = Some val.
Proof.
  intros.
  funelim (convert to xbv); [idtac|lia|idtac].
  - destruct_rew. simpl. apply XBV.extend_to_N. assumption.
  - destruct_rew. simpl. assumption.
Qed.

Lemma convert_extend_to_N_none from to (xbv : XBV.xbv from) :
  (to >= from)%N ->
  XBV.to_N xbv = None ->
  XBV.to_N (convert to xbv) = None.
Proof.
  intros.
  funelim (convert to xbv).
  - destruct_rew. simpl. apply XBV.extend_to_N_none2. assumption.
  - lia.
  - destruct_rew. simpl. assumption.
Qed.

Lemma convert_shr_convert n1 n2 (xbv : XBV.xbv n1) shamt :
  (n2 >= n1)%N ->
  convert n1 (XBV.shr (convert n2 xbv) shamt) = XBV.shr xbv shamt.
Proof.
  intros.
  funelim (convert n2 xbv); [idtac|lia|idtac].
  all: destruct_rew; simpl.
  - funelim (convert from (XBV.shr (XBV.concat (XBV.zeros (to - from)) value) shamt)); [lia|idtac|lia].
    apply XBV.extr_shr_extend.
  - funelim (convert from (XBV.shr value shamt)); [lia|lia|idtac].
    rewrite <- eq_rect_eq. reflexivity.
Qed.

Lemma convert_shl_convert n1 n2 (xbv : XBV.xbv n1) shamt :
  (n2 >= n1)%N ->
  convert n1 (XBV.shl (convert n2 xbv) shamt) = XBV.shl xbv shamt.
Proof.
  intros.
  funelim (convert n2 xbv); [idtac|lia|idtac].
  all: destruct_rew; simpl.
  - funelim (convert from (XBV.shl (XBV.concat (XBV.zeros (to - from)) value) shamt)); [lia|idtac|lia].
    apply XBV.extr_shl_extend.
  - funelim (convert from (XBV.shl value shamt)); [lia|lia|idtac].
    rewrite <- eq_rect_eq. reflexivity.
Qed.

Lemma convert_exes n1 n2 :
  (n2 <= n1)%N ->
  convert n2 (XBV.exes n1) = XBV.exes n2.
Proof.
  intros.
  funelim (convert n2 (XBV.exes n1)).
  - lia.
  - apply XBV.extr_exes.
  - destruct_rew. reflexivity.
Qed.

(* TODO: Move me to bitvectors *)
Lemma bitOf_exes i n : XBV.bitOf i (XBV.exes n) = RawXBV.X.
Proof. apply nth_repeat. Qed.

Hint Rewrite bitOf_exes : xbv.

(* TODO: Move me to bitvectors *)
Lemma shr_empty n : RawXBV.shr [] n = [].
Proof. destruct n. all: simp shr. all: reflexivity. Qed.

Hint Rewrite shr_empty : shr.

(* TODO: Move me to bitvectors *)
Lemma bitOf_shr w n (xbv : XBV.xbv w) :
  (n < w)%N ->
  XBV.bitOf 0 (XBV.shr xbv n) =
  XBV.bitOf n xbv.
Proof.
  intros Hin_bounds.
  unfold XBV.shr, XBV.bitOf.
  XBV.bitvector_erase. subst.
  N_to_nat.
  unfold RawXBV.bitOf.
  funelim (RawXBV.shr bv n); expect 3.
  1, 2: reflexivity.
  simpl in *.
  rewrite <- H by lia.
  apply app_nth1.
  pose proof (RawXBV.shr_size n bs).
  crush.
Qed.

Hint Rewrite bitOf_shr using lia : xbv.

Lemma extr_all w (xbv : XBV.xbv w) : XBV.extr xbv 0 w = xbv.
Proof.
  XBV.bitvector_erase. subst.
  unfold RawXBV.extr, RawXBV.size.
  autodestruct_eqn E; [|apply N.leb_gt in E; lia].
  clear E.
  induction bv.
  - reflexivity.
  - rewrite Nat2N.id in *. simpl in *. simp extract.
    f_equal. exact IHbv.
Qed.

Lemma eval_equalized_shiftop {w1 w2} regs op wf (lhs : expression w1) (rhs : expression w2) :
  eval_expr regs (equalized_shiftop wf op lhs rhs)
    = eval_shiftop op (eval_expr regs lhs) (eval_expr regs rhs).
Proof.
  unfold equalized_shiftop.
  simp eval_expr. simpl.
  generalize (eval_expr regs lhs). clear lhs. intro lhs.
  generalize (eval_expr regs rhs). clear rhs. intro rhs.
  funelim (eval_shiftop op lhs rhs).
  all: simp eval_shiftop.
  all: match type of Heq with
       | (_ = Some _) => apply convert_extend_to_N with (to := N.max n1 n2) in Heq
       | (_ = None) => apply convert_extend_to_N_none with (to := N.max n1 n2) in Heq
       end; [|lia].
  all: rewrite Heq; simpl.
  - apply convert_shr_convert. lia.
  - apply convert_exes. lia.
  - apply convert_shl_convert. lia.
  - apply convert_exes. lia.
  - apply convert_shl_convert. lia.
  - apply convert_exes. lia.
Qed.

Lemma simpl_expr_correct {w} regs (e : expression w) :
  eval_expr regs (simpl_expr e) = eval_expr regs e.
Proof.
  funelim (simpl_expr e).
  all: simp eval_expr in *; simpl in *.
  all: repeat match goal with
       | [ Hinduct : forall r, eval_expr r (simpl_expr _) = eval_expr r _ |- _ ] =>
         rewrite Hinduct in *
       end.
  all: try reflexivity.
  all: clear Heqcall.
  all: (* TODO: Skip all the variants of the bitselect for now *)
       try match goal with
       | |- convert 1 _ = _ => admit
       end.
  (* - (\* Variable bitselect *\)
   *   rewrite eval_equalized_shiftop.
   *   simp eval_shiftop.
   *   unfold select_bit.
   *   destruct (XBV.to_N (eval_expr regs idx)) eqn:E; simpl.
   *   + (\* well-defined *\)
   *     rewrite bitOf_shr by (apply XBV.to_N_max_bound in E; lia).
   *     rewrite H.
   *     reflexivity.
   *   + (\* X index *\)
   *     rewrite bitOf_exes.
   *     XBV.bitvector_erase.
   *     reflexivity. *)
  (* - (\* Resize *\)
   *   rewrite eval_simpl_resize. rewrite H. reflexivity. *)
  - (* shifts *)
    rewrite eval_equalized_shiftop.
    rewrite H. rewrite H0.
    reflexivity.
Admitted.

(* Lemma simpl_resize_reads {from} to (e : expression from) wf :
 *   LocationSet.Equal (expr_reads (simpl_resize to e wf)) (expr_reads e).
 * Proof.
 *   unfold simpl_resize.
 *   destruct (dec (from < to)%N).
 *   all: destruct_rew; simpl.
 *   - LocationSet.setdec.
 *   - reflexivity.
 * Qed. *)

Lemma equalized_shiftop_reads_reads_permutation w1 w2 wf op (lhs : expression w1) (rhs : expression w2) :
  LocationSet.Equal (expr_reads (equalized_shiftop wf op lhs rhs)) (expr_reads lhs ∪ expr_reads rhs).
Proof. reflexivity. Qed.

Lemma simpl_expr_reads_permutation w (e : expression w) :
  LocationSet.Equal (expr_reads (simpl_expr e)) (expr_reads e).
Proof.
  funelim (simpl_expr e); clear Heqcall.
  all: simpl.
  all: try rewrite equalized_shiftop_reads_reads_permutation.
  all: try rewrite !simpl_resize_reads.
  all: try destruct_rew.
  all: repeat match goal with
       | [ H : LocationSet.Equal (expr_reads (simpl_expr _)) (expr_reads _) |- _ ] =>
         rewrite H
       end.
  all: (reflexivity || LocationSet.setdec).
Qed.

Lemma simpl_vmodule_correct init {i o} (v : vmodule i o) :
  run_vmodule (simpl_vmodule v) init = run_vmodule v init.
Proof.
  unfold run_vmodule, mk_initial_state, simpl_vmodule, simpl_module_body.
  simpl.
  
  rewrite sort_module_items_map; expect 3; cycle 1.
  {
    intros [[lhs rhs]].
    simp module_item_reads module_item_writes statement_reads statement_writes expr_reads.
    apply simpl_expr_reads_permutation.
  }
  {
    intros [[lhs rhs]].
    simp module_item_reads module_item_writes statement_reads statement_writes expr_reads.
    reflexivity.
  }

  destruct (sort_module_items (LocationSet.of_varset (VarSet.of_list i)) (modBody v));
    simpl; [|reflexivity].
  generalize (init // VarSet.of_list i). clear init v.
  induction l; intros r; [reflexivity|].
  destruct a; expect 1. destruct s; expect 1.
  simpl. simp exec_module_body exec_module_item exec_statement. simpl.
  simp exec_module_body.
  rewrite simpl_expr_correct.
  apply IHl.
Qed.

Import ExactEquivalence.

Theorem simpl_vmodule_exact_equivalence {i o} (v : vmodule i o) :
  simpl_vmodule v ~~~ v.
Proof.
  apply exact_by_output_equality.
  intros initial. rewrite simpl_vmodule_correct.
  reflexivity.
Qed.
