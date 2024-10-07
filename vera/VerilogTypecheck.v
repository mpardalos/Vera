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
From nbits Require Import NBits.
From mathcomp Require Import seq.

From vera Require Import Verilog.
From vera Require Import Common.
From vera Require Import Verilog.
From vera Require Import Netlist.
From vera Require Import Common.
From vera Require EnvStack.
From vera Require Import Common.

Import MonadNotation.
Import FunctorNotation.
Import ListNotations.
Open Scope monad_scope.

Definition TCBindings := StrMap.t Verilog.vtype.

Definition TCContext := Verilog.vtype.

Definition TC := sum string.

Equations expr_type : TypedVerilog.expression -> Verilog.vtype :=
  expr_type (TypedVerilog.BinaryOp t _ _ _) := t;
  expr_type (TypedVerilog.Conversion _ t _) := t;
  expr_type (TypedVerilog.IntegerLiteral v) := Verilog.Logic (size v - 1) 0;
  expr_type (TypedVerilog.NamedExpression t _) := t.

Equations tc_lvalue : TCBindings -> Verilog.expression -> TC TypedVerilog.expression :=
  tc_lvalue Γ (Verilog.BinaryOp op l r) :=
    raise "Binary operator not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.IntegerLiteral _) :=
    raise "Constant not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.NamedExpression n) :=
    match StrMap.find n Γ with
    | None => raise "Name not in context"%string
    | Some t => ret (TypedVerilog.NamedExpression t n)
    end.

Definition dec_value_matches_type (v: bits) (t: Verilog.vtype) : { size v = Verilog.vtype_width t } + { size v <> Verilog.vtype_width t } :=
  eq_dec (size v) (Verilog.vtype_width t).

Equations tc_expr : TCContext -> TCBindings -> Verilog.expression -> TC TypedVerilog.expression :=
  tc_expr ctx Γ (Verilog.BinaryOp op l r) :=
    typed_l <- tc_expr ctx Γ l ;;
    typed_r <- tc_expr ctx Γ r ;;
    ret (TypedVerilog.BinaryOp ctx op typed_l typed_r) ;
  tc_expr ctx Γ (Verilog.IntegerLiteral value) :=
    if dec_value_matches_type value ctx then
      ret (TypedVerilog.IntegerLiteral value)
    else
      ret (TypedVerilog.Conversion
             (Verilog.Logic (size value - 1) 0)
             ctx
             (TypedVerilog.IntegerLiteral value));
  tc_expr ctx Γ (Verilog.NamedExpression n) :=
    match StrMap.find n Γ with
    | None =>
        raise "Name not in context"%string
    | Some t =>
        if eq_dec t ctx then
          ret (TypedVerilog.NamedExpression t n)
        else
          ret (TypedVerilog.Conversion t ctx (TypedVerilog.NamedExpression t n))
    end
.

Equations tc_stmt : TCBindings -> Verilog.statement -> TC TypedVerilog.Statement :=
  tc_stmt Γ (Verilog.Block body) :=
    TypedVerilog.Block <$> mapT (tc_stmt Γ) body;
  tc_stmt Γ (Verilog.BlockingAssign lhs rhs) :=
    typed_lhs <- tc_lvalue Γ lhs ;;
    typed_rhs <- tc_expr (expr_type typed_lhs) Γ rhs ;;
    ret (TypedVerilog.BlockingAssign typed_lhs typed_rhs);
  tc_stmt Γ (Verilog.NonBlockingAssign lhs rhs) :=
    typed_lhs <- tc_lvalue Γ lhs ;;
    typed_rhs <- tc_expr (expr_type typed_lhs) Γ rhs ;;
    ret (TypedVerilog.NonBlockingAssign typed_lhs typed_rhs);
  tc_stmt Γ (Verilog.If condition trueBranch falseBranch) :=
    typed_condition <- tc_lvalue Γ condition ;;
    typed_trueBranch <- tc_stmt Γ trueBranch ;;
    typed_falseBranch <- tc_stmt Γ falseBranch ;;
    ret (TypedVerilog.If typed_condition typed_trueBranch typed_falseBranch)
.
Admit Obligations.


Equations tc_module_item : TCBindings -> Verilog.module_item -> TC TypedVerilog.module_item :=
| Γ, (Verilog.ContinuousAssign to from) =>
    typed_to <- tc_lvalue Γ to ;;
    typed_from <- tc_expr (expr_type typed_to) Γ from ;;
    ret (TypedVerilog.ContinuousAssign typed_to typed_from)
| Γ, (Verilog.AlwaysFF body) =>
    TypedVerilog.AlwaysFF <$> tc_stmt Γ body
.

Equations variables_to_bindings : list Verilog.variable -> TCBindings :=
  variables_to_bindings [] :=
    StrMap.empty Verilog.vtype;
  variables_to_bindings ((Verilog.MkVariable t _st n) :: tl) :=
    StrMap.add n t (variables_to_bindings tl).

Definition tc_vmodule (m : Verilog.vmodule) : TC TypedVerilog.vmodule :=
  let Γ := variables_to_bindings (Verilog.modVariables m) in
  modBody <- mapT (tc_module_item Γ) (Verilog.modBody m) ;;
  ret
    {|
      TypedVerilog.modName := Verilog.modName m;
      TypedVerilog.modPorts := Verilog.modPorts m;
      TypedVerilog.modVariables := Verilog.modVariables m;
      TypedVerilog.modBody := modBody;
    |}
.