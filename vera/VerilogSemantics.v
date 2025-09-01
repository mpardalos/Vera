From Coq Require Import BinNat.
From Coq Require Import String.
From Coq Require Import Nat.
From Coq Require Import Structures.OrderedTypeEx.
From Coq Require Import List.
From Coq Require Import ssreflect.
From Coq Require Import Relations.
From Coq Require Import Structures.Equalities.
From Coq Require Import Psatz.
From Coq Require Import Program.Equality.
From Coq Require Import Morphisms.

From vera Require Import Verilog.
From vera Require Import Common.
From vera Require Import Bitvector.
Import (notations) XBV.
Import RawXBV (bit(..)).
From vera Require Import Tactics.
From vera Require Import Decidable.

From Equations Require Import Equations.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Data.Monads.OptionMonad.
From ExtLib Require Import Data.List.

Import ListNotations.
Import MonadLetNotation.
Import SigTNotations.
Local Open Scope monad_scope.
Local Open Scope bv_scope.

Set Bullet Behavior "Strict Subproofs".

Module CombinationalOnly.
  Definition Process := Verilog.module_item.

  Section Sorted.
    Equations module_items_sorted : list Verilog.module_item -> Prop :=
      module_items_sorted [] := True;
      module_items_sorted (mi :: mis) :=
        Forall (fun mi' => disjoint (Verilog.module_item_writes mi) (Verilog.module_item_reads mi')) mis
               /\ module_items_sorted mis
    .

    Global Instance dec_module_items_sorted ms : DecProp (module_items_sorted ms).
    Proof.
      induction ms;
        simp module_items_sorted;
        try typeclasses eauto.
    Defined.
  End Sorted.

  Module VariableAsMDT <: MiniDecidableType.
    Definition t := Verilog.variable.
    Definition eq_dec (x y : t) := dec (x = y).
  End VariableAsMDT.

  Module VariableAsUDT := Make_UDT(VariableAsMDT).

  Module VariableDepMap := MkDepFunMap(VariableAsUDT).

  Definition RegisterState := VariableDepMap.t (fun var => XBV.xbv (Verilog.varType var)).

  Record VerilogState :=
    MkVerilogState
      { regState : RegisterState
      ; pendingProcesses : list Process
      }
  .

  Definition set_reg (var : Verilog.variable) (value : XBV.xbv (Verilog.varType var)) : RegisterState -> RegisterState :=
    VariableDepMap.insert var value.

  Lemma set_reg_get_in var val regs :
    set_reg var val regs var = Some val.
  Proof.
    unfold set_reg, VariableDepMap.insert.
    autodestruct; [|contradiction].
    dependent destruction e.
    reflexivity.
  Qed.

  Lemma set_reg_get_out var1 var2 val regs :
    var1 <> var2 ->
    set_reg var1 val regs var2 = regs var2.
  Proof.
    intros.
    unfold set_reg, VariableDepMap.insert.
    autodestruct; [contradiction|].
    reflexivity.
  Qed.

  Definition pop_pending_process (st : VerilogState) : VerilogState :=
    {| regState := regState st
    ; pendingProcesses := tail (pendingProcesses st)
    |}
  .

  Definition variable_names vars : list string :=
    map Verilog.varName vars.

  Equations bv_binop {w} : (BV.bitvector w -> BV.bitvector w -> BV.bitvector w) -> XBV.xbv w -> XBV.xbv w -> XBV.xbv w :=
    bv_binop f l r with XBV.to_bv l, XBV.to_bv r => {
      | Some lbv, Some rbv => XBV.from_bv (f lbv rbv)
      | _, _ => XBV.exes (XBV.size l)
      }.

  Definition bitwise_binop_raw (f : bit -> bit -> bit) (l r : RawXBV.xbv) : RawXBV.xbv :=
    map2 f l r.

  Lemma map2_size {A B C} (f : A -> B -> C) (l : list A) (r : list B) :
    length (map2 f l r) = min (length l) (length r).
  Proof.
    funelim (map2 f l r); simp map2; simpl; try crush.
  Qed.

  Definition bitwise_binop_raw_size f l r :
    RawXBV.size l = RawXBV.size r ->
    RawXBV.size (bitwise_binop_raw f l r) = RawXBV.size l.
  Proof.
    intros.
    unfold RawXBV.size, bitwise_binop_raw in *.
    rewrite map2_size.
    lia.
  Qed.

  Local Obligation Tactic := intros.

  Program Definition bitwise_binop {n} (f : bit -> bit -> bit) (l r : XBV.xbv n) : XBV.xbv n :=
    {| XBV.bv := bitwise_binop_raw f (XBV.bits l) (XBV.bits r) |}.
  Next Obligation.
    rewrite bitwise_binop_raw_size; now rewrite ! XBV.wf.
  Qed.

  Equations and_bit : bit -> bit -> bit :=
    and_bit I I := I;
    and_bit O _ := O;
    and_bit _ O := O;
    and_bit X _ := X;
    and_bit _ X := X.

  Equations or_bit : bit -> bit -> bit :=
    or_bit O O := O;
    or_bit I _ := I;
    or_bit _ I := I;
    or_bit X _ := X;
    or_bit _ X := X.

  Equations eval_binop {n} (op : Verilog.binop) : XBV.xbv n -> XBV.xbv n -> XBV.xbv (Verilog.binop_width op n) :=
    eval_binop Verilog.BinaryPlus l r := bv_binop (@BV.bv_add _) l r;
    eval_binop Verilog.BinaryMinus l r := bv_binop (fun bvl bvr => BV.bv_add bvl (BV.bv_neg bvr)) l r;
    eval_binop Verilog.BinaryStar l r := bv_binop (@BV.bv_mult _) l r;
    eval_binop Verilog.BinaryBitwiseAnd l r := bitwise_binop and_bit l r;
    eval_binop Verilog.BinaryBitwiseOr l r := bitwise_binop or_bit l r;
    eval_binop Verilog.BinaryShiftLeft l r with XBV.to_N r := {
      | Some shamt => XBV.shl l shamt
      | None => XBV.exes n
      };
    eval_binop Verilog.BinaryShiftRight l r with XBV.to_N r := {
      | Some shamt => XBV.shr l shamt
      | None => XBV.exes n
      };
    eval_binop Verilog.BinaryShiftLeftArithmetic l r with XBV.to_N r := {
      | Some shamt => XBV.shl l shamt
      | None => XBV.exes n
      };
  .

  Equations eval_unaryop {n} (op : Verilog.unaryop) (operand : XBV.xbv n) : XBV.xbv (Verilog.unop_width op n) :=
    eval_unaryop Verilog.UnaryPlus x := x
  .

  (* Notation rewriting a b e := (@eq_rect_r _ a _ e b _). *)
  (* Notation with_rewrite e := (eq_rect_r _ e _). *)

  Import EqNotations.

  Equations convert {from} (to : N) (value : XBV.xbv from) : XBV.xbv to :=
    convert to value with dec (from < to)%N := {
      | left Hlt => rew _ in XBV.concat (XBV.zeros (to - from)%N) value
      | right Hge with dec (from > to)%N => {
        | left Hgr => rew _ in XBV.extr value 0 to;
        | right Hle => rew _ in value
        }
      }.
  Next Obligation. crush. Qed.
  Next Obligation. crush. Qed.
  Next Obligation. crush. Qed.
  Next Obligation. crush. Defined.

  Definition select_bit {w1 w2} (vec : XBV.xbv w1) (idx : XBV.xbv w2) : XBV.xbv 1 :=
    match XBV.to_N idx with
    | None => XBV.of_bits [X]
    | Some n => XBV.of_bits [XBV.bitOf (N.to_nat n) vec]
    end.

  (* TODO: Check that ?: semantics match with standard *)
  Definition eval_conditional {w_cond w} (cond : XBV.xbv w_cond) (ifT : XBV.xbv w) (ifF : XBV.xbv w) : XBV.xbv w :=
      match XBV.to_bv cond with
      | None => XBV.exes (XBV.size ifT)
      | Some cond_bv =>
          if BV.is_zero cond_bv
          then ifF
          else ifT
      end.

  Equations
    eval_expr {w} (regs: RegisterState) (e : Verilog.expression w) : option (XBV.xbv w) :=
    eval_expr regs (Verilog.UnaryOp op operand) :=
      let* operand_val := eval_expr regs operand in
      Some (eval_unaryop op operand_val);
    eval_expr regs (Verilog.BinaryOp op lhs rhs) :=
      let* lhs__val := eval_expr regs lhs in
      let* rhs__val := eval_expr regs rhs in
      Some (eval_binop op lhs__val rhs__val);
    eval_expr regs (Verilog.Conditional cond tBranch fBranch) :=
      let* cond__val := eval_expr regs cond in
      let* tBranch__val := eval_expr regs tBranch in
      let* fBranch__val := eval_expr regs fBranch in
      Some (eval_conditional cond__val tBranch__val fBranch__val);
    eval_expr regs (Verilog.BitSelect vec idx) :=
      let* vec__val := eval_expr regs vec in
      let* idx__val := eval_expr regs idx in
      Some (select_bit vec__val idx__val);
    eval_expr regs (Verilog.Resize t expr) :=
      let* val := eval_expr regs expr in
      Some (convert t val);
    eval_expr regs (Verilog.Concatenation e1 e2) :=
      let* val1 := eval_expr regs e1 in
      let* val2 := eval_expr regs e2 in
      Some (XBV.concat val1 val2);
    eval_expr regs (Verilog.IntegerLiteral _ val) :=
      Some (XBV.from_bv val) ;
    eval_expr regs (Verilog.NamedExpression var) :=
      regs var.

  Equations
    exec_statement (regs : RegisterState) (stmt : Verilog.statement) : option RegisterState by struct :=
    exec_statement regs (Verilog.Block stmts) := exec_statements regs stmts ;
    exec_statement regs (Verilog.If cond trueBranch falseBranch) :=
      let* cond__val := eval_expr regs cond in
      (*
       * If the cond_predicate expression evaluates to true (that is, has a
       * nonzero known value), the first statement shall be executed. If it
       * evaluates to false (that is, has a zero value or the value is x or z), the
       * first statement shall not execute. If there is an else statement and the
       * cond_predicate expression is false, the else statement shall be
       * executed.
       *)
      match XBV.to_bv cond__val with
      | None => exec_statement regs falseBranch
      | Some cond__bv =>
        if BV.is_zero cond__bv
        then exec_statement regs falseBranch
        else exec_statement regs trueBranch
      end
    ;
    exec_statement regs (Verilog.BlockingAssign (Verilog.NamedExpression var) rhs) :=
      let* rhs__val := eval_expr regs rhs in
      Some (set_reg var rhs__val regs)
    ;
    exec_statement regs (Verilog.BlockingAssign lhs rhs) :=
      None;
    exec_statement regs (Verilog.NonBlockingAssign lhs rhs) :=
      None;
  where exec_statements (regs : RegisterState) (stmts : list Verilog.statement) : option RegisterState :=
    exec_statements regs [] := Some regs;
    exec_statements regs (hd :: tl) :=
      let* regs' := exec_statement regs hd in
      exec_statements regs' tl;
  .

  Equations
    exec_module_item : RegisterState -> Verilog.module_item -> option RegisterState :=
    exec_module_item st (Verilog.Initial _) :=
      None; (* initial blocks are not part of the semantics *)
    exec_module_item st (Verilog.AlwaysFF stmt) :=
      None; (* always_ff is not allowed *)
    exec_module_item st (Verilog.AlwaysComb stmt ) :=
      exec_statement st stmt;
  .

  Equations run_step : VerilogState -> option VerilogState :=
    run_step (MkVerilogState reg []) := None;
    run_step (MkVerilogState reg (p :: ps)) :=
      let* _ := opt_dec (module_items_sorted (p :: ps)) in
      let* reg' := exec_module_item reg p in
      Some (MkVerilogState reg' ps).

  Equations run_multistep (st : VerilogState) : option VerilogState by wf (length (pendingProcesses st)) :=
    run_multistep (MkVerilogState reg []) := Some (MkVerilogState reg []);
    run_multistep (MkVerilogState reg (p :: ps)) :=
      let* reg' := exec_module_item reg p in
      run_multistep (MkVerilogState reg' ps).
  Next Obligation. crush. Qed.

  Definition step (st1 st2 : VerilogState) := run_step st1 = Some st2.

  Definition blocked (st : VerilogState) := run_step st = None.

  Definition final (st : VerilogState) := pendingProcesses st = [].

  Import Tactics.

  Lemma final_is_blocked : forall st, final st -> blocked st.
  Proof.
    unfold final, blocked.
    intros [reg procs] Hprocs.
    simpl in *; subst.
    simp step; auto.
  Qed.

  Lemma multistep_final : forall (st st' : VerilogState),
    run_multistep st = Some st' -> final st'.
  Proof.
    intros [regs procs]. revert regs.
    unfold final.
    induction procs; intros.
    - simp run_multistep in *. now some_inv.
    - simp run_multistep in *. inv H.
      autodestruct. eauto.
  Qed.

  Lemma multistep_blocked : forall (st st' : VerilogState),
      run_multistep st = Some st' -> blocked st'.
  Proof. eauto using final_is_blocked, multistep_final. Qed.

  (** The values of the final state of the execution of module *)
  Definition execution := RegisterState.

  Definition execution_match_on (C : Verilog.variable -> Prop) (e1 e2 : execution) : Prop :=
    forall var, C var -> exists xbv, e1 var = Some xbv /\ e2 var = Some xbv.

  Global Instance execution_match_on_proper :
    Proper (pointwise_relation Verilog.variable iff ==> eq ==> eq ==> iff) execution_match_on.
  Proof. repeat intro. subst. crush. Qed.

  Definition limit_to_regs (vars : list Verilog.variable) (regs : RegisterState) : RegisterState :=
    fun var =>
      match dec (In var vars) with
      | left prf => regs var
      | right prf => None
      end.

  Definition valid_execution (v : Verilog.vmodule) (e : execution) :=
    exists e' : execution,
      run_multistep
        {| regState := limit_to_regs (Verilog.module_inputs v) e; pendingProcesses := Verilog.modBody v |} =
        Some {| regState := e'; pendingProcesses := [] |}
      /\ execution_match_on
          (fun var => In var (Verilog.module_inputs v ++
                             Verilog.module_body_writes (Verilog.modBody v)))
          e' e.

  (** All variables of v have a value in the execution *)
  Definition complete_execution (v : Verilog.vmodule) (e : execution) :=
    forall var, In var (Verilog.modVariables v) -> exists bv, e var = Some bv.

  (** All variables of v, *and no other variables*, have a value in the execution *)
  Definition exact_execution (v : Verilog.vmodule) (e : execution) :=
    forall var, In var (Verilog.modVariables v) -> exists bv, e var = Some bv.

  Definition no_errors (v : Verilog.vmodule) :=
    forall (initial : RegisterState)
      (input_defined : forall var, exists xbv, initial var = Some xbv -> ~ XBV.has_x xbv),
    exists final, run_multistep {| regState := initial; pendingProcesses := Verilog.modBody v |} = Some final.
End CombinationalOnly.
