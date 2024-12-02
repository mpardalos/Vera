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
  tc_lvalue Γ (Verilog.BinaryOp _ _ _ _) :=
    raise "Binary operator not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.Conditional _ _ _) :=
    raise "Conditional not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.IntegerLiteral _) :=
    raise "Constant not permitted as lvalue"%string;
  tc_lvalue Γ (Verilog.Annotation _ e) :=
    tc_lvalue Γ (e);
  tc_lvalue Γ (Verilog.BitSelect _ _) :=
    raise "BitSelect lvalues not implemented"%string;
  tc_lvalue Γ (Verilog.NamedExpression tt n) :=
    match StrMap.find n Γ with
    | None => raise "Name not in context"%string
    | Some t => ret (TypedVerilog.NamedExpression t n)
    end.

Definition dec_value_matches_type {n} (v: BV.t n) (t: TypedVerilog.vtype) : { n = t } + { n <> t } :=
  N.eq_dec n t.

Equations tc_expr : option TCContext -> TCBindings -> Verilog.expression -> TC TypedVerilog.expression :=
  tc_expr ctx Γ (Verilog.BinaryOp _ op l r) :=
    match op with
    | Verilog.BinaryPlus (* '+' *)
    | Verilog.BinaryMinus (* '-' *)
    | Verilog.BinaryStar (* '*' *)
    | Verilog.BinarySlash (* '/' *)
    | Verilog.BinaryPercent (* '%' *)
      =>
        typed_l <- tc_expr ctx Γ l ;;
        typed_r <- tc_expr ctx Γ r ;;
        ret (TypedVerilog.BinaryOp (N.max (TypedVerilog.expr_type typed_l) (TypedVerilog.expr_type typed_r)) op typed_l typed_r)
    | Verilog.BinaryShiftRight (* '>>' *)
    | Verilog.BinaryShiftLeft (* '<<' *)
    | Verilog.BinaryShiftRightArithmetic (* '>>>' *)
    | Verilog.BinaryShiftLeftArithmetic (* '<<<' *)
      =>
        typed_l <- tc_expr ctx Γ l ;;
        typed_r <- tc_expr None Γ r ;;
        ret (TypedVerilog.BinaryOp (TypedVerilog.expr_type typed_l) op typed_l typed_r)
    | Verilog.BinaryLessThan (* '<' *)
    | Verilog.BinaryLessThanEqual (* '<=' *)
    | Verilog.BinaryGreaterThan (* '>' *)
    | Verilog.BinaryGreaterThanEqual (* '>=' *)
    | Verilog.BinaryEqualsEquals (* '==' *)
    | Verilog.BinaryNotEquals (* '!=' *)
    | Verilog.BinaryEqualsEqualsEquals (* '===' *)
    | Verilog.BinaryNotEqualsEquals (* '!==' *)
    | Verilog.BinaryWildcardEqual (* '==?' *)
    | Verilog.BinaryWildcardNotEqual (* '!=?' *)
      =>
        typed_l <- tc_expr None Γ l ;;
        typed_r <- tc_expr None Γ r ;;
        (* TODO: Make sure we are doing zero-extension here *)
        match N.compare (TypedVerilog.expr_type typed_l) (TypedVerilog.expr_type typed_r) with
        | Lt => 
            typed_l_final <- tc_expr (Some (TypedVerilog.expr_type typed_r)) Γ l ;;
            ret (TypedVerilog.BinaryOp (TypedVerilog.expr_type typed_r) op typed_l_final typed_r)
        | Gt => 
            typed_r_final <- tc_expr (Some (TypedVerilog.expr_type typed_l)) Γ r ;;
            ret (TypedVerilog.BinaryOp (TypedVerilog.expr_type typed_l) op typed_l typed_r_final)
        | Eq => ret (TypedVerilog.BinaryOp 1 op typed_l typed_r)
        end
    | Verilog.BinaryLogicalAnd (* '&&' *)
    | Verilog.BinaryLogicalOr (* '||' *)
    | Verilog.BinaryLogicalImplication (* '->' *)
    | Verilog.BinaryLogicalEquivalence (* '<->' *)
      =>
        typed_l <- tc_expr None Γ l ;;
        typed_r <- tc_expr None Γ r ;;
        ret (TypedVerilog.BinaryOp 1 op typed_l typed_r)
    | Verilog.BinaryBitwiseAnd (* '&' *)
    | Verilog.BinaryBitwiseOr (* '|' *)
    | Verilog.BinaryBitwiseXor (* '^' *)
    | Verilog.BinaryXNor (* '^~', '~^' *)
      => raise "bitwise operators missing"%string
    | Verilog.BinaryExponent (* '**' *)
      => raise "Exponent operator missing"%string
    end;
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
  tc_expr (Some ctx) Γ (@Verilog.IntegerLiteral width value) :=
    if N.eq_dec width ctx then
      ret (TypedVerilog.IntegerLiteral value)
    else
      ret (TypedVerilog.Annotation
             ctx
             (TypedVerilog.IntegerLiteral value));
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
        if N.eq_dec t ctx then
          ret (TypedVerilog.NamedExpression t n)
        else
          ret (TypedVerilog.Annotation ctx (TypedVerilog.NamedExpression t n))
    end;
  tc_expr ctx Γ (Verilog.Annotation _ e) := tc_expr ctx Γ e
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
Admit Obligations.


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
