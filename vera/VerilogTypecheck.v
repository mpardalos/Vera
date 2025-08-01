From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import BinPos.
From Coq Require Import BinNat.
From Coq Require Arith Lia Program.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.MonadState.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Data.Monads.StateMonad.
From ExtLib Require Import Data.Monads.EitherMonad.
From ExtLib Require Import Data.List.
From Equations Require Import Equations.

From vera Require Import Verilog.
From vera Require Import Common.
From vera Require Import Verilog.
From vera Require Import Common.
From vera Require EnvStack.
From vera Require Import Common.
From vera Require Import Bitvector.
Import (notations) Bitvector.RawBV.

Import MonadNotation.
Import FunctorNotation.
Import ListNotations.
Import SigTNotations.
Open Scope monad_scope.

Definition TCBindings := StrMap.t Verilog.vtype.

Definition TCContext := Verilog.vtype.

Definition TC := sum string.

Definition tc_var (Γ : TCBindings) (var : Verilog.variable) : TC unit :=
    match StrMap.find (Verilog.varName var) Γ with
    | None => raise "Name not in context"%string
    | Some t_env =>
        if N.eq_dec t_env (Verilog.varType var)
        then ret tt
        else raise "Different type in env vs expression"%string
    end.

Equations tc_lvalue {w} : TCBindings -> Verilog.expression w -> TC unit :=
  tc_lvalue Γ (Verilog.UnaryOp _ _) :=
    raise "Unary operator not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.BinaryOp _ _ _) :=
    raise "Binary operator not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.Conditional _ _ _) :=
    raise "Conditional not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.Concatenation _ _) :=
    (* TODO: Allow concatenation as lvalue *)
    raise "Concatenation not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.IntegerLiteral _ _) :=
    raise "Constant not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.Resize _ e) :=
    raise "Resize not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.BitSelect _ _) :=
    raise "BitSelect lvalues not implemented"%string;
  tc_lvalue Γ (Verilog.NamedExpression var) :=
    tc_var Γ var .

Definition dec_value_matches_type (v: RawBV.t) (t: Verilog.vtype) : { RawBV.size v = t } + { RawBV.size v <> t } :=
  N.eq_dec (RawBV.size v) t.

Equations tc_expr {w} : TCBindings -> Verilog.expression w -> TC unit :=
  tc_expr Γ (Verilog.UnaryOp op e) :=
    typed_e <- tc_expr Γ e ;;
    ret tt ;
  tc_expr Γ (Verilog.BinaryOp op l r) :=
    typed_l <- tc_expr Γ l ;;
    typed_r <- tc_expr Γ r ;;
    ret tt ;
  tc_expr Γ (Verilog.BitSelect target index) :=
    typed_target <- tc_expr Γ target ;;
    typed_index <- tc_expr Γ index ;;
    ret tt ;
  tc_expr Γ (Verilog.Conditional cond tBranch fBranch) :=
    tc_expr Γ cond ;;
    tc_expr Γ tBranch ;;
    tc_expr Γ fBranch ;;
    if (N.eq_dec (Verilog.expr_type tBranch) (Verilog.expr_type fBranch)) then
      ret tt
    else
      raise "Conditional branches do not match"%string ;
  tc_expr Γ (Verilog.Concatenation l r) :=
    tc_expr Γ l ;;
    tc_expr Γ r ;;
    ret tt ;
  tc_expr Γ (Verilog.IntegerLiteral _ value) :=
    ret tt;
  tc_expr Γ (Verilog.NamedExpression var) :=
    tc_var Γ var ;
  tc_expr Γ (Verilog.Resize t e) :=
    tc_expr Γ e
.

Equations tc_stmt : TCBindings -> Verilog.statement -> TC unit :=
  tc_stmt Γ (Verilog.Block body) :=
    mapT (tc_stmt Γ) body ;;
    ret tt ;
  tc_stmt Γ (Verilog.BlockingAssign lhs rhs) :=
    typed_lhs <- tc_lvalue Γ lhs ;;
    typed_rhs <- tc_expr Γ rhs ;;
    ret tt;
  tc_stmt Γ (Verilog.NonBlockingAssign lhs rhs) :=
    typed_lhs <- tc_lvalue Γ lhs ;;
    typed_rhs <- tc_expr Γ rhs ;;
    ret tt;
  tc_stmt Γ (Verilog.If condition trueBranch falseBranch) :=
    typed_condition <- tc_expr Γ condition ;;
    typed_trueBranch <- tc_stmt Γ trueBranch ;;
    typed_falseBranch <- tc_stmt Γ falseBranch ;;
    ret tt
.

Equations tc_module_item : TCBindings -> Verilog.module_item -> TC unit :=
| Γ, (Verilog.AlwaysComb body) => tc_stmt Γ body
| Γ, (Verilog.AlwaysFF body) => tc_stmt Γ body
| Γ, (Verilog.Initial body) => tc_stmt Γ body
.

Equations variables_to_bindings : list Verilog.variable -> TCBindings :=
  variables_to_bindings [] :=
    StrMap.empty Verilog.vtype;
  variables_to_bindings (var :: tl) :=
    StrMap.add (Verilog.varName var) (Verilog.varType var) (variables_to_bindings tl).

Definition tc_vmodule (m : Verilog.vmodule) : TC unit :=
  let Γ := variables_to_bindings (Verilog.modVariables m) in
  modBody <- mapT (tc_module_item Γ) (Verilog.modBody m) ;;
  ret tt.
