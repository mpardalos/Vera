From Coq Require Import BinNat.
From Coq Require Import String.
From Coq Require Import Nat.
From Coq Require Import Structures.OrderedTypeEx.
From Coq Require Import List.
From Coq Require Import ssreflect.
From Coq Require Import Relations.
From Coq Require Import Structures.Equalities.
From Coq Require Import Psatz.

From vera Require Import Verilog.
From vera Require Import Common.
From vera Require Import Bitvector.
Import (notations) XBV.
Import XBV (X, I, O).
From vera Require Import Tactics.
From vera Require Import Decidable.

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

  Definition RegisterState := StrFunMap.t XBV.t.

  Record VerilogState :=
    MkVerilogState
      { regState : RegisterState
      ; pendingProcesses : list Process
      }
  .

  Definition set_reg (name : string) (value : XBV.t) (st : VerilogState) : VerilogState :=
    {| regState := fun n => if (n =? name)%string then Some value else (regState st n)
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

  Definition input_valid (v : Verilog.vmodule) (input : list XBV.t) :=
    List.length input = List.length (Verilog.inputs v).

  Definition initial_state (m : Verilog.vmodule) (input : list XBV.t) : VerilogState :=
    {|
      regState := StrFunMap.of_list (List.combine (Verilog.inputs m) input);
      pendingProcesses := List.filter is_always_comb (Verilog.modBody m)
    |}.

  Equations bv_binop : (RawBV.t -> RawBV.t -> RawBV.t) -> XBV.t -> XBV.t -> XBV.t :=
    bv_binop f l r with XBV.to_bv l, XBV.to_bv r => {
      | Some lbv, Some rbv => XBV.from_bv (f lbv rbv)
      | _, _ => XBV.exes (XBV.size l)
      }.

  Definition bitwise_binop (f : XBV.bit -> XBV.bit -> XBV.bit) (l r : XBV.t) : XBV.t :=
    map2 f l r.

  Equations and_bit : XBV.bit -> XBV.bit -> XBV.bit :=
    and_bit I I := I;
    and_bit O _ := O;
    and_bit _ O := O;
    and_bit X _ := X;
    and_bit _ X := X.

  Equations or_bit : XBV.bit -> XBV.bit -> XBV.bit :=
    or_bit O O := O;
    or_bit I _ := I;
    or_bit _ I := I;
    or_bit X _ := X;
    or_bit _ X := X.

  Equations eval_binop : Verilog.binop -> XBV.t -> XBV.t -> XBV.t :=
    eval_binop Verilog.BinaryPlus l r := bv_binop RawBV.bv_add l r;
    eval_binop Verilog.BinaryMinus l r := bv_binop (fun bvl bvr => RawBV.bv_add bvl (RawBV.bv_neg bvr)) l r;
    eval_binop Verilog.BinaryStar l r := bv_binop RawBV.bv_mult l r;
    eval_binop Verilog.BinaryBitwiseAnd l r := bitwise_binop and_bit l r;
    eval_binop Verilog.BinaryBitwiseOr l r := bitwise_binop or_bit l r;
    eval_binop op l r := XBV.exes (XBV.size l)
  .

  Definition eval_unaryop (operator : Verilog.unaryop) (operand : XBV.t) : XBV.t.
  Admitted.

  (* Notation rewriting a b e := (@eq_rect_r _ a _ e b _). *)
  (* Notation with_rewrite e := (eq_rect_r _ e _). *)

  Equations convert (to : N) (value : XBV.t) : XBV.t :=
    convert to value with N.compare to (XBV.size value) => {
      | Lt => XBV.extr value 0 to
      | Gt => XBV.zextn value (to - (XBV.size value))%N
      | Eq => value
      }.

  Definition select_bit (vec : XBV.t) (idx : XBV.t) : XBV.t :=
    [XBV.bitOf 0 (XBV.x_binop RawBV.bv_shr vec idx)].

  Equations
    eval_expr : VerilogState -> Verilog.expression -> option XBV.t :=
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
      (* TODO: Check that ?: semantics match with standard *)
      match XBV.to_bv cond__val with
      | None => ret (XBV.exes (XBV.size tBranch__val))
      | Some cond__bv =>
        if RawBV.is_zero cond__bv
        then ret fBranch__val
        else ret tBranch__val
      end;
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
    eval_expr st (Verilog.IntegerLiteral val) := ret (XBV.from_bv val) ;
    eval_expr st (Verilog.NamedExpression t name) :=
      match regState st name with
      | None => Some (XBV.exes t)
      | Some v => ret v
      end
  .

  Equations
    exec_statement (st : VerilogState) (stmt : Verilog.statement) : option VerilogState by struct :=
    exec_statement st (Verilog.Block stmts) := exec_statements st stmts ;
    exec_statement st (Verilog.If cond trueBranch falseBranch) :=
      cond__val <- eval_expr st cond ;;
      (*
       * If the cond_predicate expression evaluates to true (that is, has a
       * nonzero known value), the first statement shall be executed. If it
       * evaluates to false (that is, has a zero value or the value is x or z), the
       * first statement shall not execute. If there is an else statement and the
       * cond_predicate expression is false, the else statement shall be
       * executed.
       *)
      match XBV.to_bv cond__val with
      | None => exec_statement st falseBranch
      | Some cond__bv =>
        if RawBV.is_zero cond__bv
        then exec_statement st falseBranch
        else exec_statement st trueBranch
      end
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
    - inversion H2; destruct (eval_expr st cond); try discriminate; clear H2.
      destruct (XBV.to_bv _); eauto.
      destruct (RawBV.is_zero _); eauto.
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

  Lemma exec_module_item_procs : forall st1 mi st2,
      exec_module_item st1 mi = Some st2 ->
      pendingProcesses st1 = pendingProcesses st2
  .
  Proof.
    intros st [] st2 H; simp exec_module_item in H.
    - eapply exec_statement_procs. eassumption.
    - discriminate.
    - discriminate.
  Qed.

  Equations run_step : VerilogState -> option VerilogState :=
    run_step (MkVerilogState reg []) := None;
    run_step (MkVerilogState reg (p :: ps)) := exec_module_item (MkVerilogState reg ps) p.

  Equations run_multistep (st : VerilogState) : option VerilogState by wf (length (pendingProcesses st)) :=
    run_multistep st =>
      (match run_step st as n' return run_step st = n' -> _ with
      | Some next => fun _ => match pendingProcesses next with
                          | [] => Some next
                          | (_::_) => run_multistep next
                          end
      | None => fun _ => None
      end) eq_refl
  .
  Next Obligation.
    clear run_multistep.
    revert next e.
    destruct st as [nextReg nextProcs].
    induction nextProcs; intros; simp run_step in *; simpl in *.
    - discriminate.
    - match type of e with
      | exec_module_item ?a ?b = _ =>
          funelim (exec_module_item a b);
          simp exec_module_item in *;
          try discriminate
      end.
      apply exec_statement_procs in e. simpl in e. subst.
      lia.
  Qed.

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
    - simp run_multistep in H. simp run_step in H. discriminate.
    - simp run_multistep in H.
      simp run_step in H.
      destruct (exec_module_item {| regState := regs; pendingProcesses := procs |} a) eqn:E;
        try discriminate.
      apply exec_module_item_procs in E. simpl in E. rewrite <- E in *.
      destruct procs.
      + inv H. congruence.
      + destruct v; simpl in *.
        rewrite <- E in *.
        eapply IHprocs.
        eassumption.
  Qed.

  Lemma multistep_blocked : forall (st st' : VerilogState),
      run_multistep st = Some st' -> blocked st'.
  Proof. eauto using final_is_blocked, multistep_final. Qed.

  Definition variable_widths vars : list (string * N):=
    map (fun var => (Verilog.varName var, Verilog.varWidth var)) vars.

  Definition variable_names vars : list string :=
    map Verilog.varName vars.

  Lemma variable_widths_names n w l:
    In (n, w) (variable_widths l) -> In n (variable_names l).
  Proof.
    revert n w.
    induction l; intros; simpl in *.
    - contradiction.
    - destruct H.
      + inversion H. subst.
        eauto.
      + right. eauto.
  Qed.

  Lemma variable_names_widths n l:
    In n (variable_names l) -> exists w, In (n, w) (variable_widths l).
  Proof.
    revert n.
    induction l; intros; simpl in *.
    - contradiction.
    - destruct H.
      + subst. eauto.
      + destruct (IHl _ H).
        eexists. eauto.
  Qed.


  (** The values of the final state of the execution of module *)
  Definition execution := string -> option XBV.t.

  Definition valid_execution (v : Verilog.vmodule) (e : execution) :=
    exists input final,
      input_valid v input
      /\ run_multistep (initial_state v input) = Some final
      /\ regState final = e.

  Definition complete_execution (v : Verilog.vmodule) (e : execution) :=
    forall name,
      In name (variable_names (Verilog.modVariables v))
         <-> exists bv, e name = Some bv.

  Lemma valid_execution_complete : forall v e,
      valid_execution v e -> complete_execution v e.
  Admitted.

  Definition no_errors (v : Verilog.vmodule) :=
    forall (input : list XBV.t)
      (input_wf : input_valid v input)
      (input_defined : Forall (fun bv => ~ XBV.has_x bv) input),
    exists final, run_multistep (initial_state v input) = Some final.
End CombinationalOnly.
