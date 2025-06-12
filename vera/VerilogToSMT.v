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
    | Gt => SMTLib.Term_BVConcat t (SMTLib.Term_BVLit _ (BV.zeros (to - from)))
    | Eq => t
    }
.

Definition smt_var_info : Type := (smtname * width).

Section expr_to_smt.
  Variable var_verilog_to_smt : StrFunMap.t smt_var_info.

  Equations term_for_name (t : Verilog.vtype) (name : string) : transf SMTLib.term :=
    term_for_name t name with var_verilog_to_smt name := {
      | None => raise ("Name not declared: " ++ name)%string
      | Some (n__smt, width) with dec (width = t) => {
        | left E => ret (SMTLib.Term_Const n__smt)
        | right _ => raise ("Incorrect sort for " ++ name)%string
        }
      }.

  Definition smt_select_bit vec_width vec_smt idx_width idx_smt :=
    SMTLib.Term_BVExtract 0 0
      (SMTLib.Term_BVBinOp SMTLib.BVShr
         (cast_from_to vec_width (N.max vec_width idx_width) vec_smt)
         (cast_from_to idx_width (N.max vec_width idx_width) idx_smt)).

  Equations expr_to_smt {w} : Verilog.expression w -> transf SMTLib.term :=
    expr_to_smt (Verilog.UnaryOp Verilog.UnaryPlus operand) :=
      expr_to_smt operand ;
    expr_to_smt (Verilog.UnaryOp Verilog.UnaryMinus operand) :=
      operand__smt <- expr_to_smt operand ;;
      ret (SMTLib.Term_BVUnaryOp SMTLib.BVNeg operand__smt);
    expr_to_smt (Verilog.UnaryOp Verilog.UnaryNegation operand) :=
      operand__smt <- expr_to_smt operand ;;
      ret (SMTLib.Term_BVUnaryOp SMTLib.BVNot operand__smt);
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryPlus lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (SMTLib.Term_BVBinOp SMTLib.BVAdd lhs__smt rhs__smt);
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryMinus lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (SMTLib.Term_BVBinOp SMTLib.BVAdd lhs__smt (SMTLib.Term_BVUnaryOp SMTLib.BVNeg rhs__smt));
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryStar lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (SMTLib.Term_BVBinOp SMTLib.BVMul lhs__smt rhs__smt);
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryShiftLeft lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (SMTLib.Term_BVBinOp SMTLib.BVShl lhs__smt rhs__smt);
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryShiftLeftArithmetic lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (SMTLib.Term_BVBinOp SMTLib.BVShl lhs__smt rhs__smt);
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryShiftRight lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (SMTLib.Term_BVBinOp SMTLib.BVShr lhs__smt rhs__smt);
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryBitwiseOr lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (SMTLib.Term_BVBinOp SMTLib.BVOr lhs__smt rhs__smt);
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryBitwiseAnd lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (SMTLib.Term_BVBinOp SMTLib.BVAnd lhs__smt rhs__smt);
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryGreaterThan lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      raise "todo"%string;
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryLessThan lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      raise "todo"%string;
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryLessThanEqual lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      raise "todo"%string;
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryEqualsEquals lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      raise "todo"%string;
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryLogicalAnd lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      raise "todo"%string;
    expr_to_smt (Verilog.BinaryOp op _ _) :=
      raise ("Unsupported operator in SMT: " ++ to_string op)%string;
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
    expr_to_smt (Verilog.NamedExpression t n) :=
      term_for_name t n
  .

  Equations transfer_comb_assignments : Verilog.statement -> transf (list SMTLib.term) :=
    transfer_comb_assignments (Verilog.Block stmts) =>
      lists <- mapT transfer_comb_assignments stmts ;;
      ret (concat lists) ;
    transfer_comb_assignments (Verilog.BlockingAssign (Verilog.NamedExpression t name) rhs) =>
      lhs__smt <- term_for_name t name ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret [SMTLib.Term_Eq lhs__smt rhs__smt];
    transfer_comb_assignments _ =>
      raise "VerilogToSMT: Invalid expression in always_comb block"%string
  .
End expr_to_smt.

Equations transfer_initial (stmt : Verilog.statement) : transf (list SMTLib.term) :=
  transfer_initial (Verilog.Block stmts) =>
    lists <- mapT transfer_initial stmts ;;
    ret (concat lists) ;
  transfer_initial (Verilog.BlockingAssign
                      (Verilog.NamedExpression _ n)
                      (Verilog.IntegerLiteral _ val)) =>
    (* raise "VerilogToSMT: initial block blegh"%string; *)
    ret [] ;
  transfer_initial (Verilog.BlockingAssign
                      (Verilog.NamedExpression _ n)
                     (Verilog.Resize _ (Verilog.IntegerLiteral _ val))) =>
    (* raise "VerilogToSMT: initial block blegh"%string; *)
    ret [] ;
  transfer_initial _ =>
    raise "VerilogToSMT: Invalid expression in initial block"%string
.

Equations assign_vars (start : smtname) (vars : list Verilog.variable) : list (Verilog.variable * smtname) :=
  assign_vars start (var :: rest) :=
    (var, start) :: (assign_vars (1 + start) rest);
  assign_vars start nil :=
    nil.

Definition mk_var_map (vars : list (Verilog.variable * smtname)) : StrFunMap.t (smtname * width) :=
  List.fold_right
    (fun '(var, smt__name) acc => StrFunMap.insert (Verilog.varName var) (smt__name, Verilog.varWidth var) acc)
    StrFunMap.empty vars.

Equations mk_bijection (tag : TaggedName.Tag) (vars : list (Verilog.variable * smtname)) : transf VerilogSMTBijection.t :=
  mk_bijection tag ((var, name__smt) :: xs) :=
    tail_bijection <- mk_bijection tag xs ;;
    prf1 <- assert_dec (tail_bijection (tag, Verilog.varName var) = None) "Duplicate variable name"%string ;;
    prf2 <- assert_dec (VerilogSMTBijection.bij_inverse tail_bijection name__smt = None) "Duplicate smt name"%string ;;
    ret (VerilogSMTBijection.insert (tag, Verilog.varName var) name__smt tail_bijection prf1 prf2);
  mk_bijection tag [] := ret VerilogSMTBijection.empty.

Equations verilog_to_smt (name_tag : TaggedName.Tag) (var_start : nat) (vmodule : Verilog.vmodule)
  : transf SMT.smt_with_namemap :=
  verilog_to_smt name_tag var_start vmodule with Verilog.modBody vmodule := {
    | [ Verilog.Initial initial_body;
        Verilog.AlwaysFF (Verilog.Block []);
        Verilog.AlwaysComb always_comb_body
      ] =>
        let var_assignment := assign_vars var_start (Verilog.modVariables vmodule) in
        let var_map := mk_var_map var_assignment in
        nameMap <- mk_bijection name_tag var_assignment ;;
        initial_smt <- transfer_initial initial_body ;;
        always_comb_smt <- transfer_comb_assignments var_map always_comb_body ;;
        inr {|
            SMT.nameMap := nameMap;
            SMT.widths := List.map (fun '(var, smtname) => (smtname, Verilog.varWidth var)) var_assignment;
            SMT.query := initial_smt ++ always_comb_smt;
          |}
    | _ => raise "Non-canonical verilog passed to verilog_to_smt"%string
    }.
