From Coq Require Import BinNat.
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
From Coq Require Import Psatz.

From vera Require Import Verilog.
From vera Require Import Common.
From vera Require Import Bitvector.
Import (notations) Bitvector.BV.

From Equations Require Import Equations.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Data.Monads.OptionMonad.
From ExtLib Require Import Data.List.

Import ListNotations.
Import MonadNotation.
Import SigTNotations.
Local Open Scope monad_scope.
Local Open Scope bv_scope.

Set Bullet Behavior "Strict Subproofs".

Module CombinationalOnly.
  Definition Process := Verilog.module_item.

  Record VerilogState :=
    MkVerilogState
      { regState : StrMap.t BV.t
      ; pendingProcesses : list Process
      }
  .

  Definition set_reg (name : string) (value : BV.t) (st : VerilogState) : VerilogState :=
    {| regState := StrMap.add name value (regState st)
    ; pendingProcesses := pendingProcesses st
    |}
  .

  Definition pop_pending_process (st : VerilogState) : VerilogState :=
    {| regState := regState st
    ; pendingProcesses := tail (pendingProcesses st)
    |}
  .

  Definition is_always_comb (it : Verilog.module_item) : bool :=
    match it with
    | Verilog.AlwaysComb _ => true
    | _ => false
    end.

  Definition initial_state (m : Verilog.vmodule) : VerilogState :=
    {|
      regState := StrMap.empty _;
      pendingProcesses := List.filter is_always_comb (Verilog.modBody m)
    |}.

  Equations
    eval_binop
      (op : Verilog.binop)
      (lhs : BV.t)
      (rhs : BV.t)
    : BV.t :=
    eval_binop Verilog.BinaryPlus lhs rhs := BV.bv_add lhs rhs;
    eval_binop _ lhs rhs := _
  .
  Admit Obligations.

  Equations
    eval_unaryop
      (operator : Verilog.unaryop)
      (operand : BV.t)
    : BV.t :=
    eval_unaryop _ operand := _
  .
  Admit Obligations.


  (* Notation rewriting a b e := (@eq_rect_r _ a _ e b _). *)
  (* Notation with_rewrite e := (eq_rect_r _ e _). *)

  Definition convert (m : N) (value : BV.t) : BV.t :=
    match N.compare (BV.size value) m with
    | Lt => BV.bv_zextn (m - (BV.size value)) (BV.size value) value
    | Gt => BV.bv_extr 0 m (BV.size value) value
    | Eq => value
    end.

  Definition select_bit (vec : BV.t) (idx : BV.t) : BV.t := [BV.bitOf 0 (BV.bv_shr vec idx)].

  Equations
    eval_expr : VerilogState -> Verilog.expression -> option BV.t :=
    eval_expr st (Verilog.UnaryOp op operand) :=
      operand__val <- eval_expr st operand ;;
      ret (eval_unaryop op operand__val) ;
    eval_expr st (Verilog.BinaryOp op lhs rhs) :=
      lhs__val <- eval_expr st lhs ;;
      rhs__val <- eval_expr st rhs ;;
      ret (eval_binop op lhs__val rhs__val) ;
    eval_expr st (Verilog.Conditional cond tBranch fBranch) :=
      cond__val <- eval_expr st cond ;;
      tBranch__val <- eval_expr st tBranch ;;
      fBranch__val <- eval_expr st fBranch ;;
      if BV.is_zero cond__val
      then ret fBranch__val
      else ret tBranch__val;
    eval_expr st (Verilog.BitSelect vec idx) :=
      vec__val <- eval_expr st vec ;;
      idx__val <- eval_expr st idx ;;
      ret (select_bit vec__val idx__val);
    eval_expr st (Verilog.Resize t expr) :=
      val <- eval_expr st expr ;;
      ret (convert t val);
    eval_expr st (Verilog.Concatenation exprs) :=
      vals <- mapT (eval_expr st) exprs ;;
      ret (concat vals);
    eval_expr st (Verilog.IntegerLiteral val) := ret val ;
    eval_expr st (Verilog.NamedExpression _ name) := StrMap.find name (regState st)
  .

  Equations
    exec_statement (st : VerilogState) (stmt : Verilog.statement) : option VerilogState by struct :=
    exec_statement st (Verilog.Block stmts) := exec_statements st stmts ;
    exec_statement st (Verilog.If cond trueBranch falseBranch) :=
      cond__val <- eval_expr st cond ;;
      if BV.is_zero cond__val
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
                   _ _ _ _ _ _ _ _ _ _ _ _ _ )); intros; auto; try discriminate.
    - inversion H; destruct (eval_expr st rhs); try discriminate; clear H.
      inversion H1; clear H1.
      reflexivity.
    - inversion H1; destruct (eval_expr st cond); try discriminate; clear H1.
      destruct (BV.is_zero _); eauto.
    - inversion H. reflexivity.
    - inversion H1; clear H1.
      destruct (exec_statement st hd) eqn:E; try discriminate.
      transitivity (pendingProcesses v); eauto.
  Qed.

  Equations
    exec_module_item : VerilogState -> Verilog.module_item -> option VerilogState :=
    exec_module_item st (Verilog.Initial _) :=
      None; (* initial blocks are not part of the semantics *)
    exec_module_item st (Verilog.AlwaysFF stmt) :=
      None; (* always_ff is not allowed *)
    exec_module_item st (Verilog.AlwaysComb stmt ) :=
      exec_statement st stmt;
  .

  Equations run_step : VerilogState -> option VerilogState :=
    run_step (MkVerilogState reg []) := None;
    run_step (MkVerilogState reg (p :: ps)) := exec_module_item (MkVerilogState reg ps) p.

  Definition step (st1 st2 : VerilogState) : Prop := run_step st1 = Some st2.

  Definition multistep := clos_trans VerilogState step.

  Definition blocked (st : VerilogState) : Prop := run_step st = None.

  Definition final (st : VerilogState) : Prop :=
    pendingProcesses st = [].

  Definition multistep_eval st1 st2 := multistep st1 st2 /\ blocked st2.

  Lemma final_is_blocked : forall st, final st -> blocked st.
  Proof.
    unfold final, blocked.
    intros [reg procs] Hprocs.
    simpl in *; subst.
    simp step; auto.
  Qed.
End CombinationalOnly.
