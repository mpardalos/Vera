From Stdlib Require Import ZArith.
From Stdlib Require Import String.
From Stdlib Require Import Psatz.
From Stdlib Require Import List.

From Equations Require Import Equations.

From ExtLib Require Import Programming.Show.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.MonadExc.

From vera Require Import Common.
From vera Require Import Tactics.
From vera Require Import Decidable.
From vera Require Btor2.
From vera Require Import Verilog.
From vera Require Import Variables.
From vera Require Import Bitvector.

Module V := Verilog.

Derive NoConfusion for V.type V.expression.

Import EqNotations.
Import MonadLetNotation.
Import ListNotations.
Local Open Scope monad_scope.
Local Open Scope string.

Coercion Npos : positive >-> N.
Coercion V.Logic : positive >-> Verilog.type.

Implicit Types (venv : Verilog.environment).
Implicit Types (benv : Btor2.environment).

Definition transfer_type (t : Verilog.type) : Btor2.Sort.t :=
  match t with
  | Verilog.Logic w => Btor2.Sort.BitVec (Npos w)
  end.

Coercion transfer_type : Verilog.type >-> Btor2.Sort.t.

Definition transfer_env venv : Btor2.environment :=
  fun n => fmap transfer_type (venv n).

Lemma transfer_env_valid {venv var} : V.var_valid venv var ->
  transfer_env venv (Var.varName var) = Some (Btor2.Sort.BitVec (Var.varType var)).
Proof. unfold V.var_valid, transfer_env in *. intros ->. reflexivity. Qed.

Equations transfer_expr {venv t} (e : @V.expression venv t) : result (@Btor2.expr (transfer_env venv) (transfer_type t)) := {
  | V.ArithmeticOp op lhs rhs =>
    let* lhs' := transfer_expr lhs in
    let* rhs' := transfer_expr rhs in
    inr (match op with
      | V.ArithmeticPlus => Btor2.Add lhs' rhs'
      | V.ArithmeticMinus => Btor2.Sub lhs' rhs'
      | V.ArithmeticStar => Btor2.Mul lhs' rhs'
      end)
  | V.LogicalOp op lhs rhs =>
    let* lhs' := transfer_expr lhs in
    let* rhs' := transfer_expr rhs in
    inr (match op with
      | V.EqualsEquals => Btor2.Eq lhs' rhs'
      | V.NotEquals => Btor2.NEq lhs' rhs'
      | V.LogicalAnd => Btor2.And (Btor2.RedOr lhs') (Btor2.RedOr rhs')
      | V.LogicalOr => Btor2.Or (Btor2.RedOr lhs') (Btor2.RedOr rhs')
      end)
  | V.BitwiseOp op lhs rhs =>
    let* lhs' := transfer_expr lhs in
    let* rhs' := transfer_expr rhs in
    inr (match op with
      | V.BinaryBitwiseAnd => Btor2.And lhs' rhs'
      | V.BinaryBitwiseOr => Btor2.Or lhs' rhs'
      | V.BinaryBitwiseXor => Btor2.XOr lhs' rhs'
      end)
  | @V.ShiftOp _ w1 w2 op lhs rhs =>
    let* lhs' := transfer_expr lhs in
    let* rhs' := transfer_expr rhs in
    let* E := assert_dec (Npos w2 = Npos w1) "Incompatible widths in btor shift" in
    let rhs' := rew [fun n => Btor2.expr (Btor2.Sort.BitVec n)] E in rhs' in
    inr (match op with
      | V.BinaryShiftLeft => Btor2.Sll lhs' rhs'
      | V.BinaryShiftLeftArithmetic => Btor2.Sll lhs' rhs'
      | V.BinaryShiftRight => Btor2.Srl lhs' rhs'
      end)
  | @V.UnaryOp _ w op operand =>
    let* operand' := transfer_expr operand in
    inr (match op as op' return Btor2.expr (transfer_type (V.Logic (V.unaryop_result op' w))) with
      | V.UnaryPlus => operand'
      | V.UnaryNot => Btor2.Not operand'
      | V.UnaryReduceAnd => Btor2.RedAnd operand'
      | V.UnaryLogicalNot => Btor2.Not (Btor2.RedOr operand')
      end)
  | V.Conditional cond ifT ifF =>
    let* cond' := transfer_expr cond in
    let* ifT' := transfer_expr ifT in
    let* ifF' := transfer_expr ifF in
    inr (Btor2.ITE (Btor2.RedOr cond') ifT' ifF')
  | V.RangeSelect (Slice.Mk var hi lo wf) wt =>
    let var' := Btor2.ExprRef (Btor2.Ref.Mk (transfer_env venv)
      (Var.varType var) (Var.varName var) (transfer_env_valid wt)) in
    inr (rew [fun n => Btor2.expr (Btor2.Sort.BitVec n)] _ in
      Btor2.Slice hi lo var')
  | V.BitSelect var (V.IntegerLiteral _ idx) wt =>
    let* idx := opt_to_sum "Xs in btor bit-select index" (XBV.to_N idx) in
    assert_dec (idx < Npos (Var.varType var))%N "Out-of-bounds btor bit-select";;
    let var' := Btor2.ExprRef (Btor2.Ref.Mk (transfer_env venv)
      (Var.varType var) (Var.varName var) (transfer_env_valid wt)) in
    inr (rew [fun n => Btor2.expr (Btor2.Sort.BitVec n)] _ in
      Btor2.Slice idx idx var')
  | V.BitSelect _ _ _ => inl "Unexpected variable bit-select in btor translation"
  | V.Concatenation lhs rhs =>
    let* lhs' := transfer_expr lhs in
    let* rhs' := transfer_expr rhs in
    inr (rew [fun n => Btor2.expr (Btor2.Sort.BitVec n)] _ in
      Btor2.Concat lhs' rhs')
  | V.Replication _ _ => inl "Unexpected replication in btor translation"
  | @V.Resize _ from to e with dec (to <= from)%positive => {
    | left prf =>
      let* e' := transfer_expr e in
      inr (rew [fun n => Btor2.expr (Btor2.Sort.BitVec n)]
        _ in Btor2.Slice (Pos.pred_N to) 0 e')
    | right prf =>
      let* e' := transfer_expr e in
      inr (rew [fun n => Btor2.expr (Btor2.Sort.BitVec n)]
        _ in Btor2.UnsignedExtend (Npos to - Npos from)%N e')
  }
  | V.IntegerLiteral _ xbv =>
    match XBV.to_bv xbv with
    | Some bv => inr (Btor2.Constant bv)
    | None => inl "Unexpected X literal in btor translation"
    end
  | V.NamedExpression var wt =>
    inr (Btor2.ExprRef (Btor2.Ref.Mk (transfer_env venv) (Var.varType var) (Var.varName var) (transfer_env_valid wt)))
}.
Solve All Obligations with lia.

Equations transfer_module_item {venv} (e : @Verilog.module_item venv) : result (list (@Btor2.node (transfer_env venv))) := {
  | V.Initial (V.BlockingAssign (V.AssignVar lhs wt_lhs) wf rhs) =>
    let* rhs' := transfer_expr rhs in
    inr [
      Btor2.StateDecl (Var.varName lhs) _ (transfer_env_valid wt_lhs);
      Btor2.StateInit (Var.varName lhs) rhs' (transfer_env_valid wt_lhs)
    ]
  | V.AlwaysComb (V.BlockingAssign (V.AssignVar lhs wt_lhs) wf rhs) =>
    let* rhs' := transfer_expr rhs in
    inr [Btor2.Operator (Var.varName lhs) rhs' (transfer_env_valid wt_lhs)]
  | V.AlwaysFF (V.NonblockingAssign (V.AssignVar lhs wt_lhs) wf rhs) =>
    let* rhs' := transfer_expr rhs in
    inr [Btor2.StateNext (Var.varName lhs) rhs' (transfer_env_valid wt_lhs)]
  | V.ConcurrentAssertion expr =>
    let* expr' := transfer_expr (V.UnaryOp V.UnaryNot expr) in
    inr [Btor2.Bad expr']
  | mi => inl ("Unexpected module item in btor translation: " ++ to_string mi)
}.

Definition transfer_module_body {venv} (mis : list Verilog.module_item) : result (list (@Btor2.node (transfer_env venv))) :=
  let* nodess := mapT transfer_module_item mis in
  inr (List.concat nodess).

Definition transfer_vmodule {i o} (v : V.vmodule i o) : result Btor2.btor :=
  let env := transfer_env (V.modEnv v) in
  let* body := transfer_module_body (V.modBody v) in
  inr {|
    Btor2.btorEnv := env;
    Btor2.btorBody := body
  |}.
