From Stdlib Require Import BinIntDef.
From Stdlib Require Import BinNums.
From Stdlib Require Import FSets.
From Stdlib Require Import List.
From Stdlib Require Import Program.
From Stdlib Require Import Psatz.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import Sorting.Permutation.

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

From vera Require SMTLib.
Import SMTLib (Sort_BitVec, Sort_Bool).

From vera Require Import Verilog.
From vera Require Import Common.
From vera Require Import Bitvector.
From vera Require Import VerilogSMT.
From vera Require Import SMTQueries.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require VerilogSemantics.
Import VerilogSemantics.Clean.
Import VerilogSemantics.Sort.

Import ListNotations.
Import CommonNotations.
Import MonadLetNotation.
Import FunctorNotation.
Import EqNotations.
Local Open Scope monad_scope.

Local Definition smtname := nat.
Local Definition width := N.

Definition transf := sum string.

Local Obligation Tactic := intros.
Equations cast_from_to (from to: N) (t : SMTLib.term (Sort_BitVec from)) : SMTLib.term (Sort_BitVec to) :=
  cast_from_to from 0 t => SMTLib.Term_BVLit _ (BV.of_bits []);
  cast_from_to from to t with dec (from < to)%N => {
    | left lt => rew [fun n => SMTLib.term (Sort_BitVec n)] _ in SMTLib.Term_BVConcat (SMTLib.Term_BVLit _ (BV.zeros (to - from))) t
    | right ge => rew [fun n => SMTLib.term (Sort_BitVec n)] _ in SMTLib.Term_BVExtract (to - 1) 0 _ t
    }
.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

Definition static_value {w} (expr : Verilog.expression w) : option (BV.bitvector w) :=
  match expr with
  | Verilog.IntegerLiteral _ val => Some val
  | _ => None
  end.

Definition statically_in_bounds {w} (max_val : N) (expr : Verilog.expression w) : Prop :=
  opt_prop (fun v => (BV.to_N v) < max_val)%N (static_value expr) \/ ((2 ^ w) < max_val)%N.

Definition smt_var_info : Type := (smtname * width).

Section expr_to_smt.
  Variable tag : VarTag.

  Definition var_to_smt (var : Verilog.variable): (SMTLib.term (Sort_BitVec (Verilog.varType var))) :=
    SMTLib.Term_Const (verilog_to_smt_var tag var).

  Definition smt_select_bit {w}
    (vec_smt : SMTLib.term (Sort_BitVec w))
    (idx : N)
    : SMTLib.term (Sort_BitVec 1):=
    rew [fun n => SMTLib.term (SMTLib.Sort_BitVec n)] (N.add_sub 1 idx) in
      SMTLib.Term_BVExtract idx idx (N.le_refl idx) vec_smt.

  Equations arithmeticop_to_smt {w} :
      Verilog.arithmeticop ->
      SMTLib.term (Sort_BitVec w) ->
      SMTLib.term (Sort_BitVec w) ->
      (SMTLib.term (Sort_BitVec w)) :=
    arithmeticop_to_smt Verilog.ArithmeticPlus lhs rhs :=
      SMTLib.Term_BVBinOp SMTLib.BVAdd lhs rhs;
    arithmeticop_to_smt Verilog.ArithmeticMinus lhs rhs :=
      SMTLib.Term_BVBinOp SMTLib.BVAdd lhs (SMTLib.Term_BVUnaryOp SMTLib.BVNeg rhs);
    arithmeticop_to_smt Verilog.ArithmeticStar lhs rhs :=
      SMTLib.Term_BVBinOp SMTLib.BVMul lhs rhs;
    .

  Equations shiftop_to_smt {w} : Verilog.shiftop -> SMTLib.term (Sort_BitVec w) -> SMTLib.term (Sort_BitVec w) -> (SMTLib.term (Sort_BitVec w)) :=
    shiftop_to_smt Verilog.BinaryShiftLeft lhs rhs :=
      (SMTLib.Term_BVBinOp SMTLib.BVShl lhs rhs);
    shiftop_to_smt Verilog.BinaryShiftLeftArithmetic lhs rhs :=
      (SMTLib.Term_BVBinOp SMTLib.BVShl lhs rhs);
    shiftop_to_smt Verilog.BinaryShiftRight lhs rhs :=
      (SMTLib.Term_BVBinOp SMTLib.BVShr lhs rhs);
  .

  Equations bitwiseop_to_smt {w} : Verilog.bitwiseop -> SMTLib.term (Sort_BitVec w) -> SMTLib.term (Sort_BitVec w) -> SMTLib.term (Sort_BitVec w) :=
    bitwiseop_to_smt Verilog.BinaryBitwiseOr lhs rhs :=
      SMTLib.Term_BVBinOp SMTLib.BVOr lhs rhs;
    bitwiseop_to_smt Verilog.BinaryBitwiseXor lhs rhs :=
      SMTLib.Term_BVBinOp SMTLib.BVXor lhs rhs;
    bitwiseop_to_smt Verilog.BinaryBitwiseAnd lhs rhs :=
      SMTLib.Term_BVBinOp SMTLib.BVAnd lhs rhs
  .

  Equations unaryop_to_smt {w} : Verilog.unaryop -> SMTLib.term (Sort_BitVec w) -> (SMTLib.term (Sort_BitVec w)) :=
    unaryop_to_smt Verilog.UnaryPlus operand :=
      operand ;
    (* unaryop_to_smt Verilog.UnaryMinus operand := *)
    (*   ret (SMTLib.Term_BVUnaryOp SMTLib.BVNeg operand); *)
    unaryop_to_smt Verilog.UnaryNot operand :=
      (SMTLib.Term_BVUnaryOp SMTLib.BVNot operand)
  .

  Definition conditional_to_smt {w_val}
    (cond_type : Verilog.vtype) (cond : SMTLib.term (Sort_BitVec cond_type)) (ifT ifF : SMTLib.term (Sort_BitVec w_val))
    : SMTLib.term (Sort_BitVec w_val) :=
    SMTLib.Term_ITE
      (SMTLib.Term_Not (SMTLib.Term_Eq cond (SMTLib.Term_BVLit _ (BV.zeros cond_type))))
      ifT ifF
  .

  Equations expr_to_smt {w} : Verilog.expression w -> transf (SMTLib.term (Sort_BitVec w)) :=
    expr_to_smt (Verilog.UnaryOp op operand) :=
      let* operand_smt := expr_to_smt operand in
      ret (unaryop_to_smt op operand_smt) ;
    expr_to_smt (Verilog.ArithmeticOp op lhs rhs) :=
      let* lhs_smt := expr_to_smt lhs in
      let* rhs_smt := expr_to_smt rhs in
      ret (arithmeticop_to_smt op lhs_smt rhs_smt);
    expr_to_smt (Verilog.BitwiseOp op lhs rhs) :=
      let* lhs_smt := expr_to_smt lhs in
      let* rhs_smt := expr_to_smt rhs in
      ret (bitwiseop_to_smt op lhs_smt rhs_smt);
    expr_to_smt (Verilog.ShiftOp op lhs rhs _ _) :=
      let* lhs_smt := expr_to_smt lhs in
      let* rhs_smt := expr_to_smt rhs in
      let* e := assert_dec _ "Incompatible widths in shift"%string in
      ret (shiftop_to_smt op lhs_smt (rew [fun n => SMTLib.term (SMTLib.Sort_BitVec n)] e in rhs_smt));
    expr_to_smt (Verilog.Concatenation e1 e2) :=
      let* e1_smt := expr_to_smt e1 in
      let* e2_smt := expr_to_smt e2 in
      ret (SMTLib.Term_BVConcat e1_smt e2_smt);
    expr_to_smt (Verilog.Replication _ _) :=
      raise "Unexpected replication in VerilogToSMT stage"%string ;
    expr_to_smt (Verilog.Conditional cond ifT ifF) :=
      let cond_type := Verilog.expr_type cond in
      let* cond_smt := expr_to_smt cond in
      let* ifT_smt := expr_to_smt ifT in
      let* ifF_smt := expr_to_smt ifF in
      ret (conditional_to_smt cond_type cond_smt ifT_smt ifF_smt);
    expr_to_smt (Verilog.RangeSelect vec hi lo _ wf) :=
      let* vec_smt := expr_to_smt vec in
      ret (SMTLib.Term_BVExtract hi lo wf vec_smt);
    expr_to_smt (Verilog.BitSelect_width vec idx _ _) :=
      raise "Unexpected variable bit select"%string;
    expr_to_smt (Verilog.BitSelect_const vec idx _) :=
      let* vec_smt := expr_to_smt vec in
      ret (smt_select_bit vec_smt idx);
    expr_to_smt (Verilog.Resize to expr _) :=
      let from := Verilog.expr_type expr in
      let* expr_smt := expr_to_smt expr in
      ret (cast_from_to from to expr_smt);
    expr_to_smt (Verilog.IntegerLiteral w val) :=
      ret (SMTLib.Term_BVLit w val);
    expr_to_smt (Verilog.NamedExpression var) :=
      ret (var_to_smt var)
  .

  Equations transfer_module_item : Verilog.module_item -> transf (SMTLib.term Sort_Bool) :=
    transfer_module_item (Verilog.AlwaysComb (Verilog.BlockingAssign var rhs)) :=
      let lhs_smt := var_to_smt var in
      let* rhs_smt := expr_to_smt rhs in
      ret (SMTLib.Term_Eq lhs_smt rhs_smt);
  .

  Equations transfer_module_body : list Verilog.module_item -> transf (list (SMTLib.term Sort_Bool)) :=
    transfer_module_body [] := ret [];
    transfer_module_body (hd :: tl) :=
      let* a := transfer_module_item hd in
      let* b := transfer_module_body tl in
      ret (a :: b)
  .
End expr_to_smt.

Definition mk_declarations : list (Verilog.variable * smtname) -> list SMTQueries.declaration :=
  map (fun '(var, name) => (name, SMTLib.Sort_BitVec (Verilog.varType var))).

Definition assert_permutation {A} `{forall (x y : A), DecProp (x = y)}
  (l1 l2 : list A) (nodup1 : NoDup l1) : option (Permutation l1 l2) :=
  match dec (length l2 <= length l1), dec (incl l1 l2) with
  | left prf1, left prf2 => Some (NoDup_Permutation_bis nodup1 prf1 prf2)
  | _, _ => None
  end.

Definition verilog_to_smt (name_tag : VarTag) (vmodule : Verilog.vmodule) : transf SMTQueries.query :=
  assert_dec
    (disjoint (Verilog.module_inputs vmodule) (Verilog.module_outputs vmodule))
    "Overlapping inputs and outputs"%string ;;
  assert_dec
    (NoDup (Verilog.module_body_writes (Verilog.modBody vmodule)))
    "Duplicate writes"%string ;;
  let* nodup := assert_dec
    (NoDup (Verilog.modVariables vmodule))
    "Duplicate variables"%string in
  opt_to_sum "Undriven variables"%string
             (assert_permutation (Verilog.modVariables vmodule)
	                         (Verilog.module_body_writes (Verilog.modBody vmodule) ++ Verilog.module_inputs vmodule)
				 nodup) ;;
  assert_dec
    (module_items_sorted (Verilog.module_inputs vmodule) (Verilog.modBody vmodule))
    "Module items unsorted"%string ;;
  transfer_module_body name_tag (Verilog.modBody vmodule)
.
