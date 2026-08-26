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

Equations simpl_expr {w} (e : expression w) : expression w := {
  | UnaryOp op e => UnaryOp op (simpl_expr e)
  | ArithmeticOp op lhs rhs => ArithmeticOp op (simpl_expr lhs) (simpl_expr rhs)
  | BitwiseOp op lhs rhs => BitwiseOp op (simpl_expr lhs) (simpl_expr rhs)
  | @ShiftOp w1 w2 op lhs rhs wf_lhs wf_rhs with dec (w1 = w2) => {
    | left E => ShiftOp op (simpl_expr lhs) (simpl_expr rhs) wf_lhs wf_rhs
    | right _ =>
      (* Shift operand widths must match in SMTLIB *)
      equalized_shiftop wf_lhs op (simpl_expr lhs) (simpl_expr rhs)
  }
  | Concatenation e1 e2 => Concatenation (simpl_expr e1) (simpl_expr e2)
  | Replication n e =>
    (* TODO: Convert replications to concats *)
    Replication n (simpl_expr e)
  | Conditional cond ifT ifF => Conditional (simpl_expr cond) (simpl_expr ifT) (simpl_expr ifF)
  | RangeSelect slice => RangeSelect slice
  | BitSelect vec idx => BitSelect vec (simpl_expr idx)
  | Resize to expr wf => Resize to (simpl_expr expr) wf
  | IntegerLiteral w val => IntegerLiteral w val
  | NamedExpression var => NamedExpression var
  }.

Definition simpl_module_body : list module_item -> list module_item :=
    map (fun '(AlwaysComb (BlockingAssign lhs wf rhs)) => AlwaysComb (BlockingAssign lhs wf (simpl_expr rhs))).

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

From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import NArith.

Import CombinationalOnly.
Local Open Scope verilog.

(* (\* TODO: Move me to bitvectors *\)
 * Lemma bitOf_exes i n : XBV.bitOf i (XBV.exes n) = RawXBV.X.
 * Proof. apply nth_repeat. Qed.
 * 
 * Hint Rewrite bitOf_exes : xbv.
 * 
 * (\* TODO: Move me to bitvectors *\)
 * Lemma shr_empty n : RawXBV.shr [] n = [].
 * Proof. destruct n. all: simp shr. all: reflexivity. Qed.
 * 
 * Hint Rewrite shr_empty : shr.
 * 
 * (\* TODO: Move me to bitvectors *\)
 * Lemma bitOf_shr w n (xbv : XBV.xbv w) :
 *   (n < w)%N ->
 *   XBV.bitOf 0 (XBV.shr xbv n) =
 *   XBV.bitOf n xbv.
 * Proof.
 *   intros Hin_bounds.
 *   unfold XBV.shr, XBV.bitOf.
 *   XBV.bitvector_erase. subst.
 *   N_to_nat.
 *   unfold RawXBV.bitOf.
 *   funelim (RawXBV.shr bv n); expect 3.
 *   1, 2: reflexivity.
 *   simpl in *.
 *   rewrite <- H by lia.
 *   apply app_nth1.
 *   pose proof (RawXBV.shr_size n bs).
 *   crush.
 * Qed.
 * 
 * Hint Rewrite bitOf_shr using lia : xbv.
 * 
 * Lemma extr_all w (xbv : XBV.xbv w) : XBV.extr xbv 0 w = xbv.
 * Proof.
 *   XBV.bitvector_erase. subst.
 *   unfold RawXBV.extr, RawXBV.size.
 *   autodestruct_eqn E; [|apply N.leb_gt in E; lia].
 *   clear E.
 *   induction bv.
 *   - reflexivity.
 *   - rewrite Nat2N.id in *. simpl in *. simp extract.
 *     f_equal. exact IHbv.
 * Qed. *)

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
       | (_ = Some _) => apply XBV.resize_extend_to_N with (to := N.max n1 n2) in Heq
       | (_ = None) => apply XBV.resize_extend_to_N_none with (to := N.max n1 n2) in Heq
       end; [|lia].
  all: rewrite Heq; simpl.
  - apply XBV.resize_shr_resize. lia.
  - apply XBV.resize_exes. lia.
  - apply XBV.resize_shl_resize. lia.
  - apply XBV.resize_exes. lia.
  - apply XBV.resize_shl_resize. lia.
  - apply XBV.resize_exes. lia.
Qed.

(* Lemma select_bit_extr {w} (x : XBV.xbv w) n :
 *   select_bit x n = XBV.extr x n 1.
 * Proof.
 *   unfold select_bit, XBV.bitOf.
 *   XBV.bitvector_erase.
 *   unfold RawXBV.extr, RawXBV.bitOf.
 *   subst.
 *   funelim (RawXBV.extract bv (N.to_nat n) (N.to_nat 1)).
 *   (\* solve this *\)
 * Admitted.
 * 
 * Lemma convert_one {w} (x : XBV.xbv w) :
 *   (w > 0)%N ->
 *   convert 1 x = select_bit x 0.
 * Proof.
 *   intros Hwf.
 *   rewrite select_bit_extr.
 *   funelim (convert 1 x).
 *   - lia.
 *   - reflexivity.
 *   - assert (from = 1)%N by lia. subst.
 *     destruct_rew. simpl.
 *     rewrite extr_all. reflexivity.
 * Qed. *)

Lemma simpl_expr_correct {w} regs (e : expression w) :
  eval_expr regs (simpl_expr e) = eval_expr regs e.
Proof.
  funelim (simpl_expr e).
  all: try rewrite eval_equalized_shiftop.
  all: simp eval_expr.
  all: repeat match goal with
       | [ Hinduct : forall r, eval_expr r (simpl_expr _) = eval_expr r _ |- _ ] =>
         rewrite Hinduct in *
       end.
  all: reflexivity.
Qed.

Lemma equalized_shiftop_reads_reads_Equal w1 w2 wf op (lhs : expression w1) (rhs : expression w2) :
  LocationSet.Equal (expr_reads (equalized_shiftop wf op lhs rhs)) (expr_reads lhs ∪ expr_reads rhs).
Proof. reflexivity. Qed.

Lemma simpl_expr_reads_Equal w (e : expression w) :
  LocationSet.Equal (expr_reads (simpl_expr e)) (expr_reads e).
Proof.
  funelim (simpl_expr e); clear Heqcall.
  all: simpl.
  all: repeat match goal with
       | [ H : LocationSet.Equal (expr_reads (simpl_expr _)) (expr_reads _) |- _ ] =>
         rewrite H
       end.
  all: try LocationSet.setdec.
  all: expect 1. (* BitSelect *)
  destruct idx.
  all: simpl in *; simp simpl_expr in *; simpl in *.
  all: try rewrite ! H.
  all: try reflexivity.
  all: expect 1.
  destruct (dec (w1 = w2)); simpl in *.
  all: rewrite H.
  all: reflexivity.
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
    apply simpl_expr_reads_Equal.
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
