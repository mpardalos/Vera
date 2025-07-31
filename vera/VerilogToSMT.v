From Coq Require Import BinIntDef.
From Coq Require Import BinNums.
From Coq Require Import FSets.
From Coq Require Import List.
From Coq Require Import Program.
From Coq Require Import Psatz.
From Coq Require Import String.
From Coq Require Import ZArith.

From Equations Require Import Equations.
From ExtLib Require Import Data.List.
From ExtLib Require Import Data.Monads.EitherMonad.
From ExtLib Require Import Data.Monads.StateMonad.
From ExtLib Require Import Data.String.
From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.MonadState.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Monoid.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Programming.Show.

From SMTCoqApi Require SMTLib.

From vera Require Import Verilog.
From vera Require Import Common.
Import (coercions) VerilogSMTBijection.
From vera Require EnvStack.
From vera Require Import Bitvector.
From vera Require Import SMT.
From vera Require Import Decidable.
From vera Require Import Tactics.

Import ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.

Local Definition smtname := nat.
Local Definition width := N.

Definition transf := sum string.

Equations cast_from_to (from to: N) (t : SMTLib.term) : SMTLib.term :=
  cast_from_to from to t with N.compare to from => {
    | Lt => SMTLib.Term_BVExtract (N.to_nat to - 1) 0 t
    (* smtlib concat is backwards *)
    | Gt => SMTLib.Term_BVConcat (SMTLib.Term_BVLit _ (BV.zeros (to - from))) t
    | Eq => t
    }
.

Definition static_value {w} (expr : Verilog.expression w) : option (BV.bitvector w) :=
  match expr with
  | Verilog.IntegerLiteral _ val => Some val
  | _ => None
  end.

Definition statically_in_bounds {w} (max_val : N) (expr : Verilog.expression w) : Prop :=
  opt_prop (fun v => (BV.to_N v) < max_val)%N (static_value expr) \/ ((2 ^ w) < max_val)%N.

Definition smt_var_info : Type := (smtname * width).

Section expr_to_smt.
  Variable var_verilog_to_smt : StrFunMap.t smt_var_info.

  (* Used for checking expected invariants (assignments only read module outputs and write to module inputs) *)
  Variable inputs : list Verilog.variable.
  Variable outputs : list Verilog.variable.

  Equations var_to_smt (var : Verilog.variable): transf SMTLib.term :=
    var_to_smt var with var_verilog_to_smt (Verilog.varName var) := {
      | None => raise ("Name not declared: " ++ (Verilog.varName var))%string
      | Some (n__smt, width) with dec (width = (Verilog.varType var)) => {
        | left E => ret (SMTLib.Term_Const n__smt)
        | right _ => raise ("Incorrect sort for " ++ (Verilog.varName var))%string
        }
      }.

  Definition smt_select_bit vec_width vec_smt idx_width idx_smt :=
    SMTLib.Term_BVExtract 0 0
      (SMTLib.Term_BVBinOp SMTLib.BVShr
         (cast_from_to vec_width (N.max vec_width idx_width) vec_smt)
         (cast_from_to idx_width (N.max vec_width idx_width) idx_smt)).

  Equations binop_to_smt : Verilog.binop -> SMTLib.term -> SMTLib.term -> transf SMTLib.term :=
    binop_to_smt Verilog.BinaryPlus lhs rhs :=
      ret (SMTLib.Term_BVBinOp SMTLib.BVAdd lhs rhs);
    binop_to_smt Verilog.BinaryMinus lhs rhs :=
      ret (SMTLib.Term_BVBinOp SMTLib.BVAdd lhs (SMTLib.Term_BVUnaryOp SMTLib.BVNeg rhs));
    binop_to_smt Verilog.BinaryStar lhs rhs :=
      ret (SMTLib.Term_BVBinOp SMTLib.BVMul lhs rhs);
    binop_to_smt Verilog.BinaryShiftLeft lhs rhs :=
      ret (SMTLib.Term_BVBinOp SMTLib.BVShl lhs rhs);
    binop_to_smt Verilog.BinaryShiftLeftArithmetic lhs rhs :=
      ret (SMTLib.Term_BVBinOp SMTLib.BVShl lhs rhs);
    binop_to_smt Verilog.BinaryShiftRight lhs rhs :=
      ret (SMTLib.Term_BVBinOp SMTLib.BVShr lhs rhs);
    binop_to_smt Verilog.BinaryBitwiseOr lhs rhs :=
      ret (SMTLib.Term_BVBinOp SMTLib.BVOr lhs rhs);
    binop_to_smt Verilog.BinaryBitwiseAnd lhs rhs :=
      ret (SMTLib.Term_BVBinOp SMTLib.BVAnd lhs rhs)
  .

  Equations unaryop_to_smt : Verilog.unaryop -> SMTLib.term -> transf SMTLib.term :=
    unaryop_to_smt Verilog.UnaryPlus operand :=
      ret operand ;
    (* unaryop_to_smt Verilog.UnaryMinus operand := *)
    (*   ret (SMTLib.Term_BVUnaryOp SMTLib.BVNeg operand); *)
    (* unaryop_to_smt Verilog.UnaryNegation operand := *)
    (*   ret (SMTLib.Term_BVUnaryOp SMTLib.BVNot operand) *)
  .

  Equations expr_to_smt {w} : Verilog.expression w -> transf SMTLib.term :=
    expr_to_smt (Verilog.UnaryOp op operand) :=
      operand__smt <- expr_to_smt operand ;;
      unaryop_to_smt op operand__smt ;
    expr_to_smt (Verilog.BinaryOp op lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      binop_to_smt op lhs__smt rhs__smt;
    expr_to_smt (Verilog.Concatenation e1 e2) :=
      e1_smt <- expr_to_smt e1 ;;
      e2_smt <- expr_to_smt e2 ;;
      ret (SMTLib.Term_BVConcat e1_smt e2_smt);
    expr_to_smt (Verilog.Conditional cond ifT ifF) :=
      let t__cond := Verilog.expr_type cond in
      condval__smt <- expr_to_smt cond ;;
      ifT__smt <- expr_to_smt ifT ;;
      ifF__smt <- expr_to_smt ifF ;;
      let cond__smt := SMTLib.Term_Not
                       (SMTLib.Term_Eq
                          condval__smt
                          (SMTLib.Term_BVLit _ (BV.zeros t__cond)))
      in
      ret (SMTLib.Term_ITE cond__smt ifT__smt ifF__smt);
    expr_to_smt (Verilog.BitSelect vec idx) :=
      let t__vec := Verilog.expr_type vec in
      let t__idx := Verilog.expr_type idx in
      inb <- assert_dec (statically_in_bounds t__vec idx) "Cannot statically determine if index is in bounds"%string;;
      vec__smt <- expr_to_smt vec ;;
      idx__smt <- expr_to_smt idx ;;
      ret (smt_select_bit t__vec vec__smt t__idx idx__smt);
    expr_to_smt (Verilog.Resize to expr) :=
      let from := Verilog.expr_type expr in
      expr__smt <- expr_to_smt expr ;;
      assert_dec (to > 0)%N "Resize to 0 is not allowed"%string;;
      ret (cast_from_to from to expr__smt);
    expr_to_smt (Verilog.IntegerLiteral w val) :=
      ret (SMTLib.Term_BVLit w val);
    expr_to_smt (Verilog.NamedExpression var) :=
      var_to_smt var
  .

  Equations transfer_module_item : Verilog.module_item -> transf SMTLib.term :=
    transfer_module_item (Verilog.AlwaysComb (Verilog.BlockingAssign (Verilog.NamedExpression var) rhs)) :=
      assert_dec (In var outputs) "Assignment target must be module outputs"%string ;;
      assert_dec (List.Forall (fun n => In n inputs) (Verilog.expr_reads rhs)) "Only reads from module inputs allowed"%string ;;
      lhs__smt <- var_to_smt var ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (SMTLib.Term_Eq lhs__smt rhs__smt);
    transfer_module_item (Verilog.AlwaysComb _) := raise "Only single-assignment always_comb (assign) allowed"%string;
    transfer_module_item (Verilog.AlwaysFF stmt) := raise "always_ff not implemented"%string;
    transfer_module_item (Verilog.Initial stmt) := raise "initial not implemented"%string
  .

  Equations transfer_module_body : list Verilog.module_item -> transf (list SMTLib.term) :=
    transfer_module_body [] := ret [];
    transfer_module_body (hd :: tl) :=
      a <- transfer_module_item hd ;;
      b <- transfer_module_body tl ;;
      ret (a :: b)
  .
End expr_to_smt.

Equations assign_vars (start : smtname) (vars : list Verilog.variable) : list (Verilog.variable * smtname) :=
  assign_vars start (var :: rest) :=
    (var, start) :: (assign_vars (1 + start) rest);
  assign_vars start nil :=
    nil.

Definition mk_var_map (vars : list (Verilog.variable * smtname)) : StrFunMap.t (smtname * width) :=
  List.fold_right
    (fun '(var, smt__name) acc => StrFunMap.insert (Verilog.varName var) (smt__name, Verilog.varType var) acc)
    StrFunMap.empty vars.

Equations mk_bijection (tag : TaggedName.Tag) (vars : list (Verilog.variable * smtname)) : transf VerilogSMTBijection.t :=
  mk_bijection tag ((var, name__smt) :: xs) :=
    tail_bijection <- mk_bijection tag xs ;;
    prf1 <- assert_dec (tail_bijection (tag, Verilog.varName var) = None) "Duplicate variable name"%string ;;
    prf2 <- assert_dec (VerilogSMTBijection.bij_inverse tail_bijection name__smt = None) "Duplicate smt name"%string ;;
    ret (VerilogSMTBijection.insert (tag, Verilog.varName var) name__smt tail_bijection prf1 prf2);
  mk_bijection tag [] := ret VerilogSMTBijection.empty.

Definition verilog_to_smt (name_tag : TaggedName.Tag) (var_start : nat) (vmodule : Verilog.vmodule) : transf SMT.smt_with_namemap :=
  let var_assignment := assign_vars var_start (Verilog.modVariables vmodule) in
  let var_map := mk_var_map var_assignment in
  nameMap <- mk_bijection name_tag var_assignment ;;
  body_smt <- transfer_module_body
               var_map
               (Verilog.module_inputs vmodule)
               (Verilog.module_outputs vmodule)
               (Verilog.modBody vmodule) ;;
  inr {|
      SMT.nameMap := nameMap;
      SMT.widths := List.map (fun '(var, smtname) => (smtname, Verilog.varType var)) var_assignment;
      SMT.query := body_smt;
    |}
.
