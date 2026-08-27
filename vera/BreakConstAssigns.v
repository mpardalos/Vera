From vera Require Import Verilog.
From vera Require Import Variables.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import Bitvector.
From vera Require Import Common.
Import Verilog.
(* From vera Require VerilogSemantics. *)

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

Equations break_const_assign {w} (t : assign_target w) : assign_target_wf t -> XBV.xbv w -> list module_item := {
  | (@AssignConcat w_hi w_lo target_hi target_lo), wf, val :=
    break_const_assign target_hi _ (XBV.extr val w_lo w_hi)
    ++ break_const_assign target_lo _ (XBV.extr val 0 w_lo)
  | target, t_wf, val := [AlwaysComb (BlockingAssign target t_wf (IntegerLiteral _ val))]
}.
Next Obligation. inv wf. assumption. Qed.
Next Obligation. inv wf. assumption. Qed.

Equations break_const_assigns_module_item : module_item -> list module_item := {
  | AlwaysComb (BlockingAssign target wf (IntegerLiteral _ val)) :=
    trace
      ("Break const assign to " ++ to_string target)
      (break_const_assign target wf val)
  | mi := [ mi ]
}.

Definition break_const_assigns_module_body : list module_item -> list module_item :=
  flat_map break_const_assigns_module_item.

Definition break_const_assigns_vmodule {i o} (v : vmodule i o) : vmodule i o :=
  traceBracket ("Break const assigns " ++ Verilog.modName v) {|
    modName := modName v;
    modBody := break_const_assigns_module_body (modBody v);
    modWfIODisjoint := modWfIODisjoint v;
    modWfInputsNoDup := modWfInputsNoDup v;
    modWfOutputsNoDup := modWfOutputsNoDup v;
  |}.

Lemma break_const_assigns_module_item_writes mi :
  LocationSet.Equal
    (module_body_writes (break_const_assigns_module_item mi))
    (module_item_writes mi).
Proof.
  funelim (break_const_assigns_module_item mi).
  all: clear Heqcall; simpl.
  all: try LocationSet.setdec; expect 1.
  funelim (break_const_assign target wf val).
  all: simpl.
  all: try LocationSet.setdec; expect 1.
  rewrite module_body_writes_app.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

From vera Require Import VerilogSemantics.
Import ExactEquivalence.

Lemma break_const_assign_width {w} (target : assign_target w) wf (val : XBV.xbv w) :
  N_sum (map (fun '(AlwaysComb (@BlockingAssign w' _ _ _)) => w') (break_const_assign target wf val)) = w.
Proof.
  funelim (break_const_assign target wf val).
  all: simpl; try apply N.add_0_r; expect 1.
  rewrite map_app.
  rewrite N_sum_app.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma break_const_assign_exes {w} (target : assign_target w) wf (val : BV.bitvector w) :
  Forall
    (fun mi =>
      match mi with
      | AlwaysComb (BlockingAssign lhs _ (IntegerLiteral _ val')) => exists bv_val', val' = XBV.from_bv bv_val'
      | AlwaysComb (BlockingAssign lhs _ _) => True
      end)
    (break_const_assign target wf (XBV.from_bv val)).
Proof.
  revert val.
  induction target.
  all: intros.
  all: simp break_const_assign.
  all: eauto; expect 1.
  apply Forall_app.
  rewrite ! XBV.extr_no_exes by lia.
  split.
  - apply IHtarget1.
  - apply IHtarget2.
Qed.

Theorem break_const_assigns_exact_equivalence {i o} (v : vmodule i o) :
  break_const_assigns_vmodule v ~~~ v.
Proof. Admitted.
