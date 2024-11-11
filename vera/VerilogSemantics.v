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

From vera Require Import Verilog.
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

Definition Process := TypedVerilog.module_item.

Definition PendingProcesses := list Process.

Record VerilogState :=
  MkVerilogState
    { regState : StrMap.t bits
    ; nbaValues : StrMap.t bits
    ; pendingProcesses : NameMap.t Process
    }
.

Definition set_reg (name : string) (value : bits) (st : VerilogState) : VerilogState :=
  {| regState := StrMap.add name value (regState st)
  ; nbaValues := nbaValues st
  ; pendingProcesses := pendingProcesses st
  |}
.

Definition set_nba (name : string) (value : bits) (st : VerilogState) : VerilogState :=
  {| regState := regState st
  ; nbaValues := StrMap.add name value (nbaValues st)
  ; pendingProcesses := pendingProcesses st
  |}
.

Definition remove_process (name : name) (st : VerilogState) : VerilogState :=
  {| regState := regState st
  ; nbaValues := nbaValues st
  ; pendingProcesses := NameMap.remove name (pendingProcesses st)
  |}
.

Equations
  eval_op (op : Verilog.op) (lhs rhs : bits) (width_match : size lhs = size rhs) : bits :=
  eval_op Verilog.BinaryPlus lhs rhs prf := lhs +# rhs;
  eval_op _ lhs rhs prf := _
.
Admit Obligations.

Require Import Psatz.

Equations
  eval_expr : VerilogState -> TypedVerilog.expression -> option bits :=
  eval_expr st (TypedVerilog.BinaryOp _ op lhs rhs) :=
    lhs__val <- eval_expr st lhs ;;
    rhs__val <- eval_expr st rhs ;;
    match eq_dec (size lhs__val) (size rhs__val) with
    | left prf => ret (eval_op op lhs__val rhs__val _)
    | right _ => None
    end;
  eval_expr st (TypedVerilog.Conversion from_type to_type expr) :=
    val <- eval_expr st expr;;
    let width := Verilog.vtype_width to_type in
    ret (if size val <? width
         then zext width val
         else low width val)
  ;
  eval_expr st (TypedVerilog.IntegerLiteral val) := Some val;
  eval_expr st (TypedVerilog.NamedExpression _ name) := StrMap.find name (regState st)
.

Equations
  exec_statement (st : VerilogState) (stmt : TypedVerilog.Statement) : option VerilogState by struct :=
  exec_statement st (TypedVerilog.Block stmts) := exec_statements st stmts ;
  exec_statement st (TypedVerilog.If cond trueBranch falseBranch) :=
    condVal <- eval_expr st cond ;;
    if (to_nat condVal) =? 0
    then exec_statement st falseBranch
    else exec_statement st trueBranch
  ;
  exec_statement st (TypedVerilog.BlockingAssign (TypedVerilog.NamedExpression _ name) rhs) :=
    rhs__val <- eval_expr st rhs ;;
    Some (set_reg name rhs__val st)
  ;
  exec_statement st (TypedVerilog.BlockingAssign lhs rhs) :=
    None;
  exec_statement st (TypedVerilog.NonBlockingAssign (TypedVerilog.NamedExpression _ name) rhs) :=
    rhs__val <- eval_expr st rhs ;;
    Some (set_nba name rhs__val st)
  ;
  exec_statement st (TypedVerilog.NonBlockingAssign lhs rhs) :=
    None;
where exec_statements (st : VerilogState) (stmts : list TypedVerilog.Statement) : option VerilogState :=
  exec_statements st [] := Some st;
  exec_statements st (hd :: tl) :=
    st' <- exec_statement st hd ;;
    exec_statements st' tl;
.

Equations
  exec_module_item : VerilogState -> TypedVerilog.module_item -> option VerilogState :=
  exec_module_item st (TypedVerilog.AlwaysFF stmt) :=
    exec_statement st stmt;
  exec_module_item st (TypedVerilog.ContinuousAssign (TypedVerilog.NamedExpression _ name) rhs) :=
    rhs__val <- eval_expr st rhs ;;
    Some (set_reg name rhs__val st)
  ;
  exec_module_item st (TypedVerilog.ContinuousAssign _ _) :=
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
                 _ _ _ _ _ _ _ _ _ _ _ _)); intros; auto; try discriminate.
  - inversion H; destruct (eval_expr st rhs); try discriminate; clear H.
    inversion H1; clear H1.
    reflexivity.
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

Lemma exec_module_item_procs : forall st1 st2 mi,
    exec_module_item st1 mi = Some st2 ->
    pendingProcesses st1 = pendingProcesses st2
.
Proof.
  intros * H.
  funelim (exec_module_item st1 mi); simp exec_module_item in *.
  - discriminate.
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
    nbaValues := StrMap.empty bits;
    pendingProcesses := pendingProcesses st
  |}
.

Inductive step_ndet (st1 st2 : VerilogState) : Prop :=
| step_ndet_exec_process
    (p_name : name)
    (p : Process)
    (p_pending : NameMap.MapsTo p_name p (pendingProcesses st1))
    (p_exec : exec_module_item (remove_process p_name st1) p = Some st2)
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

Definition multistep_ndet : VerilogState -> VerilogState -> Prop :=
  clos_refl_trans VerilogState step_ndet.

Definition evaluate_ndet (st1 st2 : VerilogState) : Prop :=
  multistep_ndet st1 st2 /\ ndet_final st2.

Inductive step_sequential (st1 st2 : VerilogState) :=
| step_sequential_exec_process
    (p_name : name)
    (p : Process)
    (p_first : least_element (pendingProcesses st1) = Some (p_name, p))
    (p_exec : exec_module_item (remove_process p_name st1) p = Some st2)
.

Equations stmt_driven_signals : TypedVerilog.Statement -> StrSet.t :=
  stmt_driven_signals (TypedVerilog.Block body) :=
    List.fold_left StrSet.union (List.map stmt_driven_signals body) StrSet.empty;
  stmt_driven_signals (TypedVerilog.BlockingAssign (TypedVerilog.NamedExpression _ n) rhs) :=
    StrSet.singleton n ;
  stmt_driven_signals (TypedVerilog.BlockingAssign _ _) :=
    StrSet.empty;
  stmt_driven_signals (TypedVerilog.NonBlockingAssign (TypedVerilog.NamedExpression _ n) rhs) :=
    StrSet.singleton n ;
  stmt_driven_signals (TypedVerilog.NonBlockingAssign _ _) :=
    StrSet.empty;
  stmt_driven_signals (TypedVerilog.If _ trueBranch falseBranch) :=
    StrSet.union (stmt_driven_signals trueBranch) (stmt_driven_signals falseBranch)
.

Equations driven_signals : Process -> StrSet.t :=
  driven_signals (TypedVerilog.ContinuousAssign (TypedVerilog.NamedExpression _ n) _) :=
    StrSet.singleton n ;
  driven_signals (TypedVerilog.ContinuousAssign _ _) :=
    StrSet.empty;
  driven_signals (TypedVerilog.AlwaysFF stmts) :=
    stmt_driven_signals stmts
.

Definition is_continuous_assign (p : Process) : Prop :=
  match p with
  | TypedVerilog.ContinuousAssign _ _ => True
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

Definition nondeterminism1 : TypedVerilog.vmodule :=
  {|
    TypedVerilog.modName := "nondeterminism1";
    TypedVerilog.modPorts := [
      Verilog.MkPort PortIn "clk";
      Verilog.MkPort PortOut "a";
      Verilog.MkPort PortOut "b"
    ];
    TypedVerilog.modVariables := [
      Verilog.MkVariable [1.:0] Verilog.Reg "a";
      Verilog.MkVariable [1.:0] Verilog.Reg "b"
    ];
    TypedVerilog.modBody := [
      TypedVerilog.AlwaysFF
        ( TypedVerilog.BlockingAssign
            (TypedVerilog.NamedExpression [1.:0] "a")
            (TypedVerilog.BinaryOp
               [1.:0]
               Verilog.Plus
               (TypedVerilog.NamedExpression [1.:0] "a")
               (TypedVerilog.IntegerLiteral (2-bits of 1))));
      TypedVerilog.AlwaysFF
        ( TypedVerilog.BlockingAssign
            (TypedVerilog.NamedExpression [1.:0] "b")
            (TypedVerilog.NamedExpression [1.:0] "a"))
    ]
  |}
.

Definition initial_state (m : TypedVerilog.vmodule) : VerilogState :=
  {|
    regState :=
      (* TODO: correct initialization of regs *)
      List.fold_left
        (fun vars var =>
           StrMap.add
             (Verilog.varName var)
             ((Verilog.vtype_width (Verilog.varType var))-bits of 0)
             vars)
        (TypedVerilog.modVariables m)
        (StrMap.empty bits);
    nbaValues := StrMap.empty bits;
    pendingProcesses :=
      snd
        (List.fold_left
           (fun '(nextName, procs) proc =>
            (Pos.succ nextName, NameMap.add nextName proc procs))
           (TypedVerilog.modBody m)
           (1%positive, NameMap.empty Process))
  |}
.

Compute (initial_state nondeterminism1).

Ltac verilog_exec_tac :=
  repeat progress
    (simp exec_module_item exec_statement eval_expr
     || unfold remove_process, set_reg
     || simpl).

Ltac verilog_step_process_tac n :=
  apply rt_step;
  eapply step_ndet_exec_process with (p_name := n);
  repeat (try progress verilog_exec_tac; reflexivity).

Ltac maps_to_tac :=
  apply StrMapFacts.find_mapsto_iff;
  unfold StrMap.add, StrMap.find;
  simpl;
  (reflexivity || f_equal).

Example nondeterminism1_eval1 :
  exists st,
    evaluate_ndet (initial_state nondeterminism1) st
    /\ StrMap.MapsTo "a"%string (2-bits of 1) (regState st)
    /\ StrMap.MapsTo "b"%string (2-bits of 1) (regState st)
.
Proof.
  unfold evaluate_ndet.
  eexists.
  repeat split.
  {
    unfold nondeterminism1, initial_state; simpl.
    eapply rt_trans.
    - verilog_step_process_tac 1%positive.
    - verilog_step_process_tac 2%positive.
  }
  all: simpl; simp eval_op bv_add_truncate.
  - apply NameMapFacts.is_empty_iff. reflexivity.
  - apply StrMapFacts.is_empty_iff. reflexivity.
  - maps_to_tac.
  - maps_to_tac.
Qed.

Example nondeterminism1_eval2 :
  exists st,
    evaluate_ndet (initial_state nondeterminism1) st
    /\ StrMap.MapsTo "a"%string (2-bits of 1) (regState st)
    /\ StrMap.MapsTo "b"%string (2-bits of 0) (regState st)
.
Proof.
  unfold evaluate_ndet.
  eexists.
  repeat split.
  {
    unfold nondeterminism1, initial_state; simpl.
    eapply rt_trans.
    - verilog_step_process_tac 2%positive.
    - verilog_step_process_tac 1%positive.
  }
  all: simpl; simp eval_op bv_add_truncate.
  - apply NameMapFacts.is_empty_iff. reflexivity.
  - apply StrMapFacts.is_empty_iff. reflexivity.
  - maps_to_tac.
  - maps_to_tac.
Qed.
