From Coq Require Import BinNums.
From Coq Require Import BinNat.
From Coq Require Import BinPos.
From Coq Require Import String.
From Coq Require FMaps.
From Coq Require MSets.
From Coq Require Import Structures.OrderedTypeEx.
From Coq Require FMapFacts.
From Coq Require Import List.
From Coq Require Import ssreflect.
Import ListNotations.

From vvequiv Require Import Verilog.
From vvequiv Require Import Common.
From vvequiv Require Import Bitvector.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Data.Monads.OptionMonad.
Import MonadNotation.
Local Open Scope monad_scope.

From Equations Require Import Equations.

Import Bitvector.

Definition Process := Verilog.module_item.

Definition PendingProcesses := list Process.

Record VerilogState :=
  MkVerilogState
    { regState : StrMap.t Bitvector.bv
    ; nbaValues : StrMap.t Bitvector.bv
    ; pendingProcesses : NameMap.t Process
    }
.

Definition set_reg (name : string) (value : Bitvector.bv) (st : VerilogState) : VerilogState :=
  {| regState := StrMap.add name value (regState st)
  ; nbaValues := nbaValues st
  ; pendingProcesses := pendingProcesses st
  |}
.

Definition set_nba (name : string) (value : Bitvector.bv) (st : VerilogState) : VerilogState :=
  {| regState := regState st
  ; nbaValues := StrMap.add name value (nbaValues st)
  ; pendingProcesses := pendingProcesses st
  |}
.

Equations
  eval_op : Verilog.op -> Bitvector.bv -> Bitvector.bv -> Bitvector.bv :=
  eval_op _ lhs rhs := _
.
Admit Obligations.

Equations
  eval_expr : VerilogState -> Verilog.expression -> option Bitvector.bv :=
  eval_expr st (Verilog.BinaryOp op lhs rhs) :=
    lhs__val <- eval_expr st lhs ;;
    rhs__val <- eval_expr st rhs ;;
    ret (eval_op op lhs__val rhs__val) ;
  eval_expr st (Verilog.IntegerLiteral val) := Some val;
  eval_expr st (Verilog.NamedExpression name) := StrMap.find name (regState st)
.

Equations
  exec_statement (st : VerilogState) (stmt : Verilog.statement) : option VerilogState by struct :=
  exec_statement st (Verilog.Block stmts) := exec_statements st stmts ;
  exec_statement st (Verilog.If cond trueBranch falseBranch) :=
    condVal <- eval_expr st cond ;;
    if N.eqb (Bitvector.value condVal) 0%N
    then exec_statement st trueBranch
    else exec_statement st falseBranch
  ;
  exec_statement st (Verilog.BlockingAssign (Verilog.NamedExpression name) rhs) :=
    rhs__val <- eval_expr st rhs ;;
    Some (set_reg name rhs__val st)
  ;
  exec_statement st (Verilog.BlockingAssign lhs rhs) :=
    None;
  exec_statement st (Verilog.NonBlockingAssign (Verilog.NamedExpression name) rhs) :=
    rhs__val <- eval_expr st rhs ;;
    Some (set_nba name rhs__val st)
  ;
  exec_statement st (Verilog.NonBlockingAssign lhs rhs) :=
    None;
where exec_statements (st : VerilogState) (stmts : list Verilog.statement) : option VerilogState :=
  exec_statements st [] := Some st;
  exec_statements st (hd :: tl) :=
    st' <- exec_statement st hd ;;
    exec_statements st' tl;
.

Equations
  exec_module_item : VerilogState -> Verilog.module_item -> option VerilogState :=
  exec_module_item st (Verilog.AlwaysFF stmt) :=
    exec_statement st stmt;
  exec_module_item st (Verilog.ContinuousAssign (Verilog.NamedExpression name) rhs) :=
    rhs__val <- eval_expr st rhs ;;
    Some (set_reg name rhs__val st)
  ;
  exec_module_item st (Verilog.ContinuousAssign _ _) :=
    None
.

Lemma exec_statement_procs : forall st1 stmt st2,
    exec_statement st1 stmt = Some st2 ->
    pendingProcesses st1 = pendingProcesses st2
.
Proof.
  refine (fst (exec_statement_elim
                 (fun st1 stmt mSt2 => forall st2, mSt2 = Some st2 -> pendingProcesses st1 = pendingProcesses st2)
                 (fun st1 stmts mSt2 => forall st2, mSt2 = Some st2 -> pendingProcesses st1 = pendingProcesses st2)
                 _ _ _ _ _ _ _ _ _ _)); intros; auto; try discriminate.
  - inversion H; destruct (eval_expr st rhs); try discriminate; clear H.
    inversion H1; clear H1.
    reflexivity.
  - inversion H; destruct (eval_expr st rhs); try discriminate; clear H.
    inversion H1; clear H1.
    reflexivity.
  - inversion H1; destruct (eval_expr st cond); try discriminate; clear H1.
    destruct (value b =? 0)%N; auto.
  - inversion H. reflexivity.
  - inversion H1; clear H1.
    destruct (exec_statement st hd) eqn:E; try discriminate.
    transitivity (pendingProcesses v); eauto.
Qed.

Lemma exec_module_item_procs : forall st1 st2 mi,
    exec_module_item st1 mi = Some st2 ->
    pendingProcesses st1 = pendingProcesses st2
.
Proof.
  intros * H.
  funelim (exec_module_item st1 mi); simp exec_module_item in *.
  - discriminate.
  - discriminate.
  - inversion H as [H']; clear H.
    destruct (eval_expr st rhs); try discriminate.
    inversion H' as [H'']; clear H' H''.
    reflexivity.
  - eauto using exec_statement_procs.
Qed.

Definition least_element {A} (m : NameMap.t A) : option (name * A) :=
  List.hd_error (NameMap.elements m).

Definition flush_nonblocking (st : VerilogState) : VerilogState :=
  {|
    regState := StrMap.map2 opt_or (nbaValues st) (regState st);
    nbaValues := StrMap.empty bv;
    pendingProcesses := pendingProcesses st
  |}
.

Inductive step_ndet (st1 st2 : VerilogState) : Prop :=
| step_ndet_exec_process
    (st_temp : VerilogState)
    (p_name : name)
    (p : Process)
    (p_pending : NameMap.MapsTo p_name p (pendingProcesses st1))
    (p_exec : exec_module_item st1 p = Some st_temp)
    (p_removed : pendingProcesses st2 = NameMap.remove p_name (pendingProcesses st1))
| step_ndet_flush_nonblocking
    (no_processes_pending : NameMap.Empty (pendingProcesses st1))
    (nba_pending : ~ StrMap.Empty (nbaValues st1))
    (flushed : st2 = flush_nonblocking st1)
.

Definition ndet_blocked (st : VerilogState) : Prop :=
  ~ exists st', step_ndet st st'.

Definition ndet_final (st : VerilogState) : Prop :=
  NameMap.Empty (pendingProcesses st) /\ StrMap.Empty (nbaValues st).

Lemma ndet_final_blocked_iff (st : VerilogState) : ndet_final st -> ndet_blocked st.
Proof.
  intros [Hprocs Hnbas] [st' Hstep].
  destruct Hstep.
  - eapply Hprocs. eauto.
  - contradiction.
Qed.

Inductive step_sequential (st1 st2 : VerilogState) :=
| step_sequential_exec_process
    (st_temp : VerilogState)
    (p_name : name)
    (p : Process)
    (p_first : least_element (pendingProcesses st1) = Some (p_name, p))
    (p_exec : exec_module_item st1 p = Some st_temp)
    (p_removed : pendingProcesses st2 = NameMap.remove p_name (pendingProcesses st1))
.

Equations stmt_driven_signals : Verilog.statement -> StrSet.t :=
  stmt_driven_signals (Verilog.Block body) :=
    List.fold_left StrSet.union (List.map stmt_driven_signals body) StrSet.empty;
  stmt_driven_signals (Verilog.BlockingAssign (Verilog.NamedExpression n) rhs) :=
    StrSet.singleton n ;
  stmt_driven_signals (Verilog.BlockingAssign _ _) :=
    StrSet.empty;
  stmt_driven_signals (Verilog.NonBlockingAssign (Verilog.NamedExpression n) rhs) :=
    StrSet.singleton n ;
  stmt_driven_signals (Verilog.NonBlockingAssign _ _) :=
    StrSet.empty;
  stmt_driven_signals (Verilog.If _ trueBranch falseBranch) :=
    StrSet.union (stmt_driven_signals trueBranch) (stmt_driven_signals falseBranch)
.

Equations driven_signals : Process -> StrSet.t :=
  driven_signals (Verilog.ContinuousAssign (Verilog.NamedExpression n) _) :=
    StrSet.singleton n ;
  driven_signals (Verilog.ContinuousAssign _ _) :=
    StrSet.empty;
  driven_signals (Verilog.AlwaysFF stmts) :=
    stmt_driven_signals stmts
.

Definition is_continuous_assign (p : Process) : Prop :=
  match p with
  | Verilog.ContinuousAssign _ _ => True
  | _ => False
  end
.

Definition no_continuous_assigns (st : VerilogState) : Prop :=
  forall n p, NameMap.MapsTo n p (pendingProcesses st) -> ~ is_continuous_assign p
.

Definition single_driver (st : VerilogState) :=
  forall n1 n2 p1 p2,
    n1 <> n2 ->
    NameMap.MapsTo n1 p1 (pendingProcesses st) ->
    NameMap.MapsTo n2 p2 (pendingProcesses st) ->
    StrSet.Empty (StrSet.inter (driven_signals p1) (driven_signals p2))
.

(* Invalid, because they are equivalent in the eventual state, not in each individual step *)
Conjecture ndet_sequential_equivalence:
  forall (st1 st2 st2': VerilogState),
    single_driver st1 ->
    no_continuous_assigns st1 ->
    step_ndet st1 st2 ->
    step_sequential st1 st2' ->
    st2 = st2'.
(* No matter what process we pick for ndet, it will not affect the evaluation of other processes *)


Import VerilogNotations.
Import BitvectorNotations.

Definition nondeterminism1 : Verilog.vmodule :=
  {|
    Verilog.modName := "nondeterminism1";
    Verilog.modPorts := [
      Verilog.MkPort PortIn "clk";
      Verilog.MkPort PortOut "a";
      Verilog.MkPort PortOut "b"
    ];
    Verilog.modVariables := [
      Verilog.MkVariable (Verilog.Logic 1 0) Verilog.Reg "a";
      Verilog.MkVariable (Verilog.Logic 1 0) Verilog.Reg "b"
    ];
    Verilog.modBody := [
      Verilog.AlwaysFF
        ( Verilog.BlockingAssign
            (Verilog.NamedExpression "a")
            (Verilog.BinaryOp
               Verilog.Plus
               (Verilog.NamedExpression "a")
               (Verilog.IntegerLiteral (Bitvector.mkBV 1 2))));
      Verilog.AlwaysFF
        ( Verilog.BlockingAssign
            (Verilog.NamedExpression "b")
            (Verilog.IntegerLiteral (Bitvector.mkBV 1 2)))
    ]
  |}
.

Print nondeterminism1.

Definition initial_state (m : Verilog.vmodule) : VerilogState :=
  {|
    regState :=
      (* TODO: correct initialization of regs *)
      List.fold_left
        (fun vars var => StrMap.add (Verilog.varName var) (mkBV 0 32) vars)
        (Verilog.modVariables m)
        (StrMap.empty bv);
    nbaValues := StrMap.empty bv;
    pendingProcesses :=
      snd
        (List.fold_left
           (fun '(nextName, procs) proc =>
            (Pos.succ nextName, NameMap.add nextName proc procs))
           (Verilog.modBody m)
           (1%positive, NameMap.empty Process))
  |}
.

Compute (initial_state nondeterminism1).
