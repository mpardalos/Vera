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
From nbits Require Import NBits.

From vera Require Import Verilog.
From vera Require Import SMT.
From vera Require Import Common.
From vera Require EnvStack.

Import ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.
Local Open Scope bits_scope.

Definition transf := sum string.

Equations expr_to_smt : TypedVerilog.expression -> transf (SMT.qfbv string) :=
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryPlus lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVAdd lhs__smt rhs__smt);
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryMinus lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVAdd lhs__smt (SMT.BVNeg rhs__smt));
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryStar lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVMul lhs__smt rhs__smt);
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryShiftLeft lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVShl lhs__smt rhs__smt);
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryShiftLeftArithmetic lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVShl lhs__smt rhs__smt);
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryShiftRight lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVLShr lhs__smt rhs__smt);
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryGreaterThan lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    raise "todo"%string;
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryLessThan lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    raise "todo"%string;
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryLessThanEqual lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    raise "todo"%string;
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryEqualsEquals lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    raise "todo"%string;
  expr_to_smt (TypedVerilog.BinaryOp _ Verilog.BinaryLogicalAnd lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    raise "todo"%string;
  expr_to_smt (TypedVerilog.BinaryOp _ op _ _) :=
    raise ("Unsupported operator in SMT: " ++ to_string op)%string;
  expr_to_smt (TypedVerilog.Conditional cond ifT ifF) :=
    cond__smt <- expr_to_smt cond ;;
    ifT__smt <- expr_to_smt ifT ;;
    ifF__smt <- expr_to_smt ifF ;;
    ret (SMT.CoreITE cond__smt ifT__smt ifF__smt);
  expr_to_smt (TypedVerilog.BitSelect vec idx) :=
    vec__smt <- expr_to_smt vec ;;
    idx__smt <- expr_to_smt idx ;;
    ret (SMT.BVExtract 0 0 (SMT.BVLShr vec__smt idx__smt));
  expr_to_smt (TypedVerilog.Conversion from to expr) :=
    _;
  expr_to_smt (TypedVerilog.IntegerLiteral val) :=
    ret (SMT.BVLit val);
  expr_to_smt (TypedVerilog.NamedExpression t n) :=
    ret (SMT.BVVar n).


Definition transfer_ports (ports : list Verilog.port) : transf (list (string * port_direction)) :=
  ret (map (fun '(Verilog.MkPort dir name) => (name, dir)) ports).

Equations transfer_initial (stmt : TypedVerilog.Statement) : transf (list (SMT.formula string)) :=
  transfer_initial (TypedVerilog.Block stmts) =>
    lists <- mapT transfer_initial stmts ;;
    ret (concat lists) ;
  transfer_initial (TypedVerilog.BlockingAssign
                      (TypedVerilog.NamedExpression _ n)
                      (TypedVerilog.IntegerLiteral val)) =>
    (* raise "VerilogToSMT: initial block blegh"%string; *)
    ret [] ;
  transfer_initial (TypedVerilog.BlockingAssign
                      (TypedVerilog.NamedExpression _ n)
                      (TypedVerilog.Conversion _ _ (TypedVerilog.IntegerLiteral val))) =>
    (* raise "VerilogToSMT: initial block blegh"%string; *)
    ret [] ;
  transfer_initial _ =>
    raise "VerilogToSMT: Invalid expression in initial block"%string
.

Equations transfer_comb_assignments (_ : TypedVerilog.Statement) : transf (list (SMT.formula string)) :=
  transfer_comb_assignments (TypedVerilog.Block stmts) =>
    lists <- mapT transfer_comb_assignments stmts ;;
    ret (concat lists) ;
  transfer_comb_assignments (TypedVerilog.BlockingAssign (TypedVerilog.NamedExpression _ n) rhs) =>
    rhs__smt <- expr_to_smt rhs ;;
    ret [SMT.CEqual (SMT.BVVar n) rhs__smt] ;
  transfer_comb_assignments _ =>
    raise "VerilogToSMT: Invalid expression in always_comb block"%string
.

Definition verilog_to_smt (vmodule : TypedVerilog.vmodule) : transf (SMT.smt_netlist string) :=
  match TypedVerilog.modBody vmodule with
  | [ TypedVerilog.Initial initial_body;
      TypedVerilog.AlwaysFF (TypedVerilog.Block []);
      TypedVerilog.AlwaysComb always_comb_body
    ] =>
      ports <- transfer_ports (TypedVerilog.modPorts vmodule) ;;
      initial_smt <- transfer_initial initial_body ;;
      always_comb_smt <- transfer_comb_assignments always_comb_body ;;
      ret {|
          SMT.smtnlName := TypedVerilog.modName vmodule ;
          SMT.smtnlPorts := ports ;
          SMT.smtnlFormulas := initial_smt ++ always_comb_smt
        |}
  | [ TypedVerilog.Initial _;
      TypedVerilog.AlwaysFF _;
      TypedVerilog.AlwaysComb _
    ] => raise "always_ff not yet supported"%string
  | _ => raise "Non-canonical verilog passed to verilog_to_smt"%string
  end
.
