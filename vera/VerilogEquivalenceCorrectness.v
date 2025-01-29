From vera Require Import Verilog.
From vera Require Import SMT.
From vera Require Import Common.
From vera Require Import Bitvector.
From vera Require VerilogTypecheck.
From vera Require VerilogCanonicalize.
From vera Require VerilogToSMT.
From vera Require VerilogSemantics.
Import VerilogSemantics.CombinationalOnly.

From Coq Require Import Relations.

From Equations Require Import Equations.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Data.Monads.EitherMonad.
Import MonadNotation.
Open Scope monad_scope.
Require Import ZArith.
Require Import String.
Require Import List.
Import ListNotations.
Import EqNotations.

Definition match_on_regs
  (regs : list (string * string))
  (v1 v2 : VerilogState)
  : Prop :=
  List.Forall
    (fun '(n1, n2) => exists v,
         StrMap.find n1 (regState v1) = Some v /\
           StrMap.find n2 (regState v2) = Some v
    )
    regs.

Definition equivalent
  (inputs outputs : list (string * string))
  (v1 v2 : Verilog.vmodule)
  : Prop :=
  forall (input_vals : list BV.t)
    (input_len_ok : length input_vals = length inputs)
    (final1 final2 : VerilogState),
    let init1 :=
      set_regs (List.map
                  (fun '((n, _), v) => (n, v))
                  (List.combine inputs input_vals))
        (initial_state v1)
    in
    let init2 :=
      set_regs (List.map
                  (fun '((_, n), v) => (n, v))
                  (List.combine inputs input_vals))
        (initial_state v1)
    in
    multistep_eval init1 final1 ->
    multistep_eval init2 final2 ->
    match_on_regs outputs final1 final2
.

Local Open Scope string.

Section V.
  Import Verilog.
  Definition assign_out : vmodule :=
    {|
      modName := "assign_out";
      modPorts := [
        MkPort PortIn "in";
        MkPort PortOut "out"
      ];
      modVariables := [
        MkVariable Verilog.Scalar Verilog.Wire "in";
        MkVariable Verilog.Scalar Verilog.Wire "out"
      ];
      modBody := [
        AlwaysComb (BlockingAssign (NamedExpression 1%N "out") (NamedExpression 1%N "in"))
      ];
    |}.
End V.

#[local] Open Scope Z_scope.

(* This tactic due to Clement Pit-Claudel with some minor additions by JDP to
   allow the result to be named: https://pit-claudel.fr/clement/MSc/#org96a1b5f *)
Inductive Learnt {A: Type} (a: A) :=
  | AlreadyKnown : Learnt a.

Ltac learn_tac fact name :=
  lazymatch goal with
  | [ H: Learnt fact |- _ ] =>
    fail 0 "fact" fact "has already been learnt"
  | _ => let type := type of fact in
        lazymatch goal with
        | [ H: @Learnt type _ |- _ ] =>
          fail 0 "fact" fact "of type" type "was already learnt through" H
        | _ => let learnt := fresh "Learn" in
              pose proof (AlreadyKnown fact) as learnt; pose proof fact as name
        end
  end.

Tactic Notation "learn" constr(fact) := let name := fresh "H" in learn_tac fact name.
Tactic Notation "learn" constr(fact) "as" simple_intropattern(name) := learn_tac fact name.

Ltac unfold_rec c := unfold c; fold c.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
    match type of T with Prop =>
      inversion H;
      match n with S (S (?n')) => subst; try constructor; solve_by_inverts (S n') end
    end
  end.

Ltac solve_by_invert := solve_by_inverts 1.

Ltac inv H := inversion H; subst; clear H.

Ltac do_step eval :=
  inv eval; repeat (unfold step in *; simp run_step exec_module_item exec_statement eval_expr in *; simpl in *); unfold set_reg in *; simpl in *; try solve_by_inverts 3%nat.

Example assign_out_equivalent : equivalent [("in", "in")] [("out", "out")] assign_out assign_out.
Proof.
  unfold equivalent, match_on_regs.
  intros * ? * [eval1 blocked1] [eval2 blocked2].
  simpl in input_len_ok.
  repeat (destruct input_vals; try solve [simpl in *; discriminate]).
  simpl in *.
  unfold assign_out, set_reg in eval1; simpl in eval1.
  unfold assign_out, set_reg in eval2; simpl in eval2.
  repeat constructor.
  unfold multistep_eval, multistep in *.
  eapply clos_trans_t1n in eval1.
  eapply clos_trans_t1n in eval2.
  inversion eval1 as [ ? step1 | ? ? step1_1 step1_2 ]; subst;
    repeat (unfold step in *; simp run_step exec_module_item exec_statement eval_expr in *; simpl in *);
    unfold set_reg in *; simpl in *; try solve_by_inverts 3%nat.


    inversion eval2 as [ ? step2 | ? ? step2_1 step2_2 ]; subst;
  inv step1.
  inv step2.
  exists b. simpl.
  now rewrite StrMap.add_eq_o.
  -
Qed.
