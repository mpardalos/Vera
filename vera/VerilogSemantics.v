From Coq Require Import BinPos.
From Coq Require Import String.
From Coq Require Import Nat.
From Coq Require FMaps.
From Coq Require MSets.
From Coq Require Import Structures.OrderedTypeEx.
From Coq Require FMapFacts.
From Coq Require Import List.
From Coq Require Import ssreflect.
From Coq Require Import Relations.
From Coq Require Import Structures.Equalities.

From vera Require Verilog.
From vera Require Import Common.

From nbits Require Import NBits.
From mathcomp Require Import seq.
From Equations Require Import Equations.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Data.Monads.OptionMonad.

Import ListNotations.
Import MonadNotation.
Local Open Scope bits_scope.
Local Open Scope monad_scope.

Set Bullet Behavior "Strict Subproofs".

Module CombinationalOnly(VType: DecidableType).
  Module Verilog := Verilog.MkVerilog(VType).

  Definition Process := Verilog.module_item.

  Record VerilogState :=
    MkVerilogState
      { regState : StrMap.t bits
      ; pendingProcesses : list Process
      }
  .

  Definition set_reg (name : string) (value : bits) (st : VerilogState) : VerilogState :=
    {| regState := StrMap.add name value (regState st)
    ; pendingProcesses := pendingProcesses st
    |}
  .

  Definition pop_pending_process (st : VerilogState) : VerilogState :=
    {| regState := regState st
    ; pendingProcesses := tail (pendingProcesses st)
    |}
  .

  Equations
    eval_op (op : Verilog.op) (lhs rhs : bits) (width_match : size lhs = size rhs) : bits :=
    eval_op Verilog.BinaryPlus lhs rhs prf := lhs +# rhs;
    eval_op _ lhs rhs prf := _
  .
  Admit Obligations.

  Equations
    eval_expr : VerilogState -> Verilog.expression -> option bits :=
    eval_expr st (Verilog.BinaryOp _ op lhs rhs) :=
      lhs__val <- eval_expr st lhs ;;
      rhs__val <- eval_expr st rhs ;;
      match eq_dec (size lhs__val) (size rhs__val) with
      | left prf => ret (eval_op op lhs__val rhs__val _)
      | right _ => None
      end;
    eval_expr st (Verilog.Conditional cond tBranch fBranch) :=
      cond__val <- eval_expr st cond ;;
      tBranch__val <- eval_expr st tBranch ;;
      fBranch__val <- eval_expr st fBranch ;;
      match (eq_dec (size tBranch__val) (size fBranch__val)), (eq_dec cond__val ((size cond__val)-bits of 0)) with
      | left size_ok, left cond_zero => ret fBranch__val
      | left size_ok, right cond_not_zero => ret tBranch__val
      | right _, _ => None
      end;
    eval_expr st (Verilog.BitSelect vec idx) :=
      vec__val <- eval_expr st vec ;;
      idx__val <- eval_expr st idx ;;
      ret [ nth false vec__val (to_nat idx__val) ];
    eval_expr st (Verilog.Annotation _ expr) := eval_expr st expr ;
    eval_expr st (Verilog.IntegerLiteral val) := Some val;
    eval_expr st (Verilog.NamedExpression _ name) := StrMap.find name (regState st)
  .

  Equations
    exec_statement (st : VerilogState) (stmt : Verilog.statement) : option VerilogState by struct :=
    exec_statement st (Verilog.Block stmts) := exec_statements st stmts ;
    exec_statement st (Verilog.If cond trueBranch falseBranch) :=
      condVal <- eval_expr st cond ;;
      if (to_nat condVal) =? 0
      then exec_statement st falseBranch
      else exec_statement st trueBranch
    ;
    exec_statement st (Verilog.BlockingAssign (Verilog.NamedExpression _ name) rhs) :=
      rhs__val <- eval_expr st rhs ;;
      Some (set_reg name rhs__val st)
    ;
    exec_statement st (Verilog.BlockingAssign lhs rhs) :=
      None;
    exec_statement st (Verilog.NonBlockingAssign lhs rhs) :=
      None;
  where exec_statements (st : VerilogState) (stmts : list Verilog.statement) : option VerilogState :=
    exec_statements st [] := Some st;
    exec_statements st (hd :: tl) :=
      st' <- exec_statement st hd ;;
      exec_statements st' tl;
  .

  Lemma exec_statement_procs : forall st1 stmt st2,
      exec_statement st1 stmt = Some st2 ->
      pendingProcesses st1 = pendingProcesses st2
  .
  Proof.
    refine (fst (exec_statement_elim
                   (fun st1 stmt mSt2 => forall st2, mSt2 = Some st2 -> pendingProcesses st1 = pendingProcesses st2)
                   (fun st1 stmts mSt2 => forall st2, mSt2 = Some st2 -> pendingProcesses st1 = pendingProcesses st2)
                   _ _ _ _ _ _ _ _ _ _ _ )); intros; auto; try discriminate.
    - inversion H; destruct (eval_expr st rhs); try discriminate; clear H.
      inversion H1; clear H1.
      reflexivity.
    - inversion H1; destruct (eval_expr st cond); try discriminate; clear H1.
      destruct (to_nat b =? 0); auto.
    - inversion H. reflexivity.
    - inversion H1; clear H1.
      destruct (exec_statement st hd) eqn:E; try discriminate.
      transitivity (pendingProcesses v); eauto.
  Qed.

  Definition least_element {A} (m : NameMap.t A) : option (name * A) :=
    List.hd_error (NameMap.elements m).

  Equations
    exec_module_item : VerilogState -> Verilog.module_item -> option VerilogState :=
    exec_module_item st (Verilog.Initial _) :=
      Some st;
    exec_module_item st (Verilog.AlwaysFF stmt) :=
      None; (* always_ff is not allowed *)
    exec_module_item st (Verilog.AlwaysComb stmt ) :=
      exec_statement st stmt;
  .

  Equations step : VerilogState -> option VerilogState :=
    step (MkVerilogState reg []) := None;
    step (MkVerilogState reg (p :: ps)) := exec_module_item (MkVerilogState reg ps) p.

  Definition blocked (st : VerilogState) : Prop :=
    step st = None.

  Definition final (st : VerilogState) : Prop :=
    pendingProcesses st = [].

  Lemma final_is_blocked : forall st, final st -> blocked st.
  Proof.
    unfold final, blocked.
    intros [reg procs] Hprocs.
    simpl in *; subst.
    simp step.
    trivial.
  Qed.
End CombinationalOnly.
