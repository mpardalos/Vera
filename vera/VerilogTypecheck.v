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
Import (notations) Bitvector.BV.

Import MonadNotation.
Import FunctorNotation.
Import ListNotations.
Import SigTNotations.
Open Scope monad_scope.

Definition TCBindings := StrMap.t TypedVerilog.vtype.

Definition TCContext := TypedVerilog.vtype.

Definition TC := sum string.

Equations tc_lvalue : TCBindings -> Verilog.expression -> TC TypedVerilog.expression :=
  tc_lvalue Γ (Verilog.BinaryOp _ _ _) :=
    raise "Binary operator not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.Conditional _ _ _) :=
    raise "Conditional not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.IntegerLiteral _) :=
    raise "Constant not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.Resize _ e) :=
    raise "Resize not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.BitSelect _ _) :=
    raise "BitSelect lvalues not implemented"%string;
  tc_lvalue Γ (Verilog.NamedExpression tt n) :=
    match StrMap.find n Γ with
    | None => raise "Name not in context"%string
    | Some t => ret (TypedVerilog.NamedExpression t n)
    end.

Definition dec_value_matches_type (v: BV.t) (t: TypedVerilog.vtype) : { BV.size v = t } + { BV.size v <> t } :=
  N.eq_dec (BV.size v) t.

Equations tc_expr : option TCContext -> TCBindings -> Verilog.expression -> TC TypedVerilog.expression :=
  tc_expr ctx Γ (Verilog.BinaryOp op l r) :=
    typed_l <- tc_expr ctx Γ l ;;
    typed_r <- tc_expr ctx Γ r ;;
    ret (TypedVerilog.BinaryOp op typed_l typed_r);
  tc_expr ctx Γ (Verilog.BitSelect target index) :=
    typed_target <- tc_expr ctx Γ target ;;
    (* TODO: Unclear from the standard if this is context- or self-determined *)
    typed_index <- tc_expr None Γ index ;; 
    ret (TypedVerilog.BitSelect typed_target typed_index) ;
  tc_expr ctx Γ (Verilog.Conditional cond tBranch fBranch) :=
    typed_cond <- tc_expr ctx Γ cond ;;
    typed_tBranch <- tc_expr ctx Γ tBranch ;;
    typed_fBranch <- tc_expr ctx Γ fBranch ;;
    if (N.eq_dec (TypedVerilog.expr_type typed_tBranch) (TypedVerilog.expr_type typed_fBranch)) then
      ret (TypedVerilog.Conditional typed_cond typed_tBranch typed_fBranch)
    else
      (**  TODO: Should probably upcast, *)
      raise "Conditional branches do not match"%string ;
  tc_expr None Γ (Verilog.IntegerLiteral value) :=
    ret (TypedVerilog.IntegerLiteral value) ;
  tc_expr (Some ctx) Γ (Verilog.IntegerLiteral value) :=
    ret (TypedVerilog.IntegerLiteral value);
  tc_expr None Γ (Verilog.NamedExpression _ n) :=
    match StrMap.find n Γ with
    | None =>
        raise "Name not in context"%string
    | Some t =>
        ret (TypedVerilog.NamedExpression t n)
    end ;
  tc_expr (Some ctx) Γ (Verilog.NamedExpression _ n) :=
    match StrMap.find n Γ with
    | None =>
        raise "Name not in context"%string
    | Some t =>
        ret (TypedVerilog.NamedExpression t n)
    end;
  tc_expr ctx Γ (Verilog.Resize _ e) := tc_expr ctx Γ e
.

Equations tc_stmt : TCBindings -> Verilog.statement -> TC TypedVerilog.statement :=
  tc_stmt Γ (Verilog.Block body) :=
    TypedVerilog.Block <$> mapT (tc_stmt Γ) body;
  tc_stmt Γ (Verilog.BlockingAssign lhs rhs) :=
    typed_lhs <- tc_lvalue Γ lhs ;;
    typed_rhs <- tc_expr (Some (TypedVerilog.expr_type typed_lhs)) Γ rhs ;;
    ret (TypedVerilog.BlockingAssign typed_lhs typed_rhs);
  tc_stmt Γ (Verilog.NonBlockingAssign lhs rhs) :=
    typed_lhs <- tc_lvalue Γ lhs ;;
    typed_rhs <- tc_expr (Some (TypedVerilog.expr_type typed_lhs)) Γ rhs ;;
    ret (TypedVerilog.NonBlockingAssign typed_lhs typed_rhs);
  tc_stmt Γ (Verilog.If condition trueBranch falseBranch) :=
    typed_condition <- tc_expr None Γ condition ;;
    typed_trueBranch <- tc_stmt Γ trueBranch ;;
    typed_falseBranch <- tc_stmt Γ falseBranch ;;
    ret (TypedVerilog.If typed_condition typed_trueBranch typed_falseBranch)
.

Equations tc_module_item : TCBindings -> Verilog.module_item -> TC TypedVerilog.module_item :=
| Γ, (Verilog.AlwaysComb body) =>
    TypedVerilog.AlwaysComb <$> tc_stmt Γ body
| Γ, (Verilog.AlwaysFF body) =>
    TypedVerilog.AlwaysFF <$> tc_stmt Γ body
| Γ, (Verilog.Initial body) =>
    TypedVerilog.Initial <$> tc_stmt Γ body
.

Equations variables_to_bindings : list Verilog.variable -> TCBindings :=
  variables_to_bindings [] :=
    StrMap.empty TypedVerilog.vtype;
  variables_to_bindings ((Verilog.MkVariable vecDecl _st n) :: tl) :=
    StrMap.add n (Verilog.vector_declaration_width vecDecl) (variables_to_bindings tl).

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
