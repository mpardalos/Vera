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
Import SigTNotations.
Opaque N.add N.sub.

Equations break_const_assign {w} : assign_target w -> XBV.xbv w -> list { w' & (assign_target w' * XBV.xbv w') } := {
  | (@AssignConcat w_hi w_lo target_hi target_lo), val :=
    break_const_assign target_hi (XBV.extr val w_lo w_hi)
    ++ break_const_assign target_lo (XBV.extr val 0 w_lo)
  | target, val := [(_; (target, val))]
}.

Equations break_const_assigns_module_item : module_item -> list module_item := {
  | AlwaysComb (BlockingAssign target (IntegerLiteral _ val)) :=
    map
      (fun '(w; (target, val)) => AlwaysComb (BlockingAssign target (IntegerLiteral _ val)))
      (break_const_assign target val)
  | mi := [ mi ]
}.

Definition break_const_assigns_module_body : list module_item -> list module_item :=
  flat_map break_const_assigns_module_item.

Lemma break_const_assigns_module_item_writes mi :
  LocationSet.Equal
    (module_body_writes (break_const_assigns_module_item mi))
    (module_item_writes mi).
Proof.
  funelim (break_const_assigns_module_item mi).
  all: clear Heqcall; simpl.
  all: try LocationSet.setdec; expect 1.
  funelim (break_const_assign target val).
  all: simpl.
  all: try LocationSet.setdec; expect 1.
  rewrite map_app.
  rewrite module_body_writes_app.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma break_const_assigns_module_body_writes mis :
  LocationSet.Equal
    (module_body_writes (break_const_assigns_module_body mis))
    (module_body_writes mis).
Proof.
  unfold break_const_assigns_module_body.
  induction mis.
  all: simpl.
  2: rewrite module_body_writes_app, break_const_assigns_module_item_writes, IHmis.
  all: reflexivity.
Qed.

Lemma break_const_assigns_wf_write_targets v :
   module_body_writes (break_const_assigns_module_body (modBody v))
   ⊆ LocationSet.of_varset
       (VarSet.diff
          (VarSet.of_list (map variable_of_decl (modVariableDecls v)))
          (VarSet.of_list (inputs_of_decls (modVariableDecls v)))).
Proof.
  rewrite break_const_assigns_module_body_writes.
  apply Verilog.modWfWriteTargets.
Qed.

Definition break_const_assigns_vmodule (v : vmodule) : vmodule :=
  traceBracket ("Break const assigns " ++ Verilog.modName v) {|
    Verilog.modName := Verilog.modName v;
    Verilog.modVariableDecls := Verilog.modVariableDecls v;
    Verilog.modBody := break_const_assigns_module_body (Verilog.modBody v);
    Verilog.modWfVariablesNoDup := Verilog.modWfVariablesNoDup v;
    Verilog.modWfWriteTargets := break_const_assigns_wf_write_targets v;
  |}.

From vera Require Import VerilogSemantics.
Import ExactEquivalence.

Lemma break_const_assign_width {w} (target : assign_target w) (val : XBV.xbv w) :
  N_sum (map (fun '(w'; _) => w') (break_const_assign target val)) = w.
Proof.
  funelim (break_const_assign target val).
  all: simpl; try apply N.add_0_r; expect 1.
  rewrite map_app.
  rewrite N_sum_app.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma break_const_assign_exes {w} (target : assign_target w) (val : BV.bitvector w) :
  Forall
    (fun '(w'; (_, val')) => exists bv_val', val' = XBV.from_bv bv_val')
    (break_const_assign target (XBV.from_bv val)).
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

Theorem break_const_assigns_exact_equivalence v :
  break_const_assigns_vmodule v ~~~ v.
Proof. Admitted.
