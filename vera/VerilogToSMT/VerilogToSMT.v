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
Import (coercions) VerilogSMTBijection.
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
    | left lt => rew _ in SMTLib.Term_BVConcat (SMTLib.Term_BVLit _ (BV.zeros (to - from))) t
    | right ge => rew _ in SMTLib.Term_BVExtract (to - 1) 0 _ t
    }
.
Next Obligation. f_equal. lia. Qed.
Next Obligation. f_equal. lia. Qed.
Next Obligation. f_equal. lia. Qed.

Definition static_value {w} (expr : Verilog.expression w) : option (BV.bitvector w) :=
  match expr with
  | Verilog.IntegerLiteral _ val => Some val
  | _ => None
  end.

Definition statically_in_bounds {w} (max_val : N) (expr : Verilog.expression w) : Prop :=
  opt_prop (fun v => (BV.to_N v) < max_val)%N (static_value expr) \/ ((2 ^ w) < max_val)%N.

Definition smt_var_info : Type := (smtname * width).

Section expr_to_smt.
  Variable tag : TaggedVariable.Tag.
  Variable name_bijection : VerilogSMTBijection.t.

  (* Used for checking expected invariants (assignments only read module outputs and write to module inputs) *)
  Variable inputs : list Verilog.variable.
  Variable outputs : list Verilog.variable.

  Equations var_to_smt (var : Verilog.variable): transf (SMTLib.term (Sort_BitVec (Verilog.varType var))) :=
    var_to_smt var with name_bijection (tag, var) := {
      | None => raise ("Name not declared: " ++ (Verilog.varName var))%string
      | Some n_smt => ret (SMTLib.Term_Const _ n_smt)
      }.

  Definition smt_select_bit vec_width vec_smt idx_width idx_smt :=
    SMTLib.Term_BVExtract 0 0 ltac:(lia)
      (SMTLib.Term_BVBinOp SMTLib.BVShr
         (cast_from_to vec_width (N.max vec_width idx_width) vec_smt)
         (cast_from_to idx_width (N.max vec_width idx_width) idx_smt)).

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
      let* lhs_smt_short := expr_to_smt lhs in
      let* rhs_smt_short := expr_to_smt rhs in
      let lhs_width := Verilog.expr_type lhs in
      let rhs_width := Verilog.expr_type rhs in
      (* Added to syntax *)
      (* assert_dec (lhs_width > 0)%N "0 width"%string ;;
       * assert_dec (rhs_width > 0)%N "0 width"%string ;; *)
      let op_width := N.max lhs_width rhs_width in
      let lhs_smt := cast_from_to lhs_width op_width lhs_smt_short in
      let rhs_smt := cast_from_to rhs_width op_width rhs_smt_short in
      let long_result := shiftop_to_smt op lhs_smt rhs_smt in
      ret (cast_from_to op_width lhs_width long_result);
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
    expr_to_smt (Verilog.BitSelect_width vec idx _) :=
      let t_vec := Verilog.expr_type vec in
      let t_idx := Verilog.expr_type idx in
      let* vec_smt := expr_to_smt vec in
      let* idx_smt := expr_to_smt idx in
      ret (smt_select_bit t_vec vec_smt t_idx idx_smt);
    expr_to_smt (@Verilog.BitSelect_const _ t_idx vec idx _) :=
      let t_vec := Verilog.expr_type vec in
      let* vec_smt := expr_to_smt vec in
      let idx_smt := SMTLib.Term_BVLit t_idx idx in
      ret (smt_select_bit t_vec vec_smt t_idx idx_smt);
    expr_to_smt (Verilog.Resize to expr _) :=
      let from := Verilog.expr_type expr in
      let* expr_smt := expr_to_smt expr in
      ret (cast_from_to from to expr_smt);
    expr_to_smt (Verilog.IntegerLiteral w val) :=
      ret (SMTLib.Term_BVLit w val);
    expr_to_smt (Verilog.NamedExpression var) :=
      var_to_smt var
  .

  Equations transfer_module_item : Verilog.module_item -> transf (SMTLib.term Sort_Bool) :=
    transfer_module_item (Verilog.AlwaysComb (Verilog.BlockingAssign (Verilog.NamedExpression var) rhs)) :=
      assert_dec (In var outputs) "Assignment target must be module outputs"%string ;;
      assert_dec (List.Forall (fun n => In n inputs) (Verilog.expr_reads rhs)) "Only reads from module inputs allowed"%string ;;
      let* lhs_smt := var_to_smt var in
      let* rhs_smt := expr_to_smt rhs in
      ret (SMTLib.Term_Eq lhs_smt rhs_smt);
    transfer_module_item (Verilog.AlwaysComb _) := raise "Only single-assignment always_comb (assign) allowed"%string;
  .

  Equations transfer_module_body : list Verilog.module_item -> transf (list (SMTLib.term Sort_Bool)) :=
    transfer_module_body [] := ret [];
    transfer_module_body (hd :: tl) :=
      assert_dec
        (disjoint
           (Verilog.module_item_writes hd)
           (Verilog.module_body_writes tl))
        "Multiply-driven net"%string ;;
      assert_dec
        (list_subset (Verilog.module_item_reads hd) inputs)
        "Read from non-module-input"%string ;;
      let* a := transfer_module_item hd in
      let* b := transfer_module_body tl in
      ret (a :: b)
  .
End expr_to_smt.

Equations assign_vars (start : smtname) (vars : list Verilog.variable) : list (Verilog.variable * smtname) :=
  assign_vars start (var :: rest) :=
    (var, start) :: (assign_vars (1 + start) rest);
  assign_vars start nil :=
    nil.

Definition mk_var_map (vars : list (Verilog.variable * smtname)) : StrFunMap.t smtname :=
  List.fold_right
    (fun '(var, smt_name) acc => StrFunMap.insert (Verilog.varName var) smt_name acc)
    StrFunMap.empty vars.

Equations mk_bijection (tag : TaggedVariable.Tag) (vars : list (Verilog.variable * smtname)) : transf VerilogSMTBijection.t :=
  mk_bijection tag ((var, name_smt) :: xs) :=
    let* tail_bijection := mk_bijection tag xs in
    let* prf1 := assert_dec (tail_bijection (tag, var) = None) "Duplicate variable name"%string in
    let* prf2 := assert_dec (VerilogSMTBijection.bij_inverse tail_bijection name_smt = None) "Duplicate smt name"%string in
    ret (VerilogSMTBijection.insert (tag, var) name_smt tail_bijection prf1 prf2);
  mk_bijection tag [] := ret VerilogSMTBijection.empty.

Definition mk_declarations : list (Verilog.variable * smtname) -> list SMTQueries.declaration :=
  map (fun '(var, name) => (name, SMTLib.Sort_BitVec (Verilog.varType var))).

Definition all_vars_driven v :=
  Forall
    (fun var => List.In var (Verilog.module_inputs v) \/
               List.In var (Verilog.module_body_writes (Verilog.modBody v)))
    (Verilog.modVariables v).

Definition assert_permutation {A} `{forall (x y : A), DecProp (x = y)}
  (l1 l2 : list A) (nodup1 : NoDup l1) : option (Permutation l1 l2) :=
  match dec (length l2 <= length l1), dec (incl l1 l2) with
  | left prf1, left prf2 => Some (NoDup_Permutation_bis nodup1 prf1 prf2)
  | _, _ => None
  end.

Definition verilog_to_smt (name_tag : TaggedVariable.Tag) (var_start : nat) (vmodule : Verilog.vmodule) : transf SMT.smt_with_namemap :=
  assert_dec
    (disjoint (Verilog.module_inputs vmodule) (Verilog.module_outputs vmodule))
    "Overlapping inputs and outputs"%string ;;
  assert_dec
    (list_subset (Verilog.module_body_reads (Verilog.modBody vmodule)) (Verilog.module_inputs vmodule))
    "Read from non-module-input"%string ;;
  assert_dec (all_vars_driven vmodule) "Undriven variables"%string ;;
  let* writes_nodup := assert_dec
    (NoDup (Verilog.module_body_writes (Verilog.modBody vmodule)))
    "Duplicate writes"%string in
  assert_dec
    (NoDup (Verilog.module_outputs vmodule))
    "Duplicate outputs"%string ;;
  opt_to_sum "Non-output variables written to"%string
    (assert_permutation
      (Verilog.module_body_writes (Verilog.modBody vmodule))
      (Verilog.module_outputs vmodule)
      writes_nodup ) ;;
  assert_dec
    (Forall clean_module_item_structure (Verilog.modBody vmodule))
    "Invalid module item"%string ;;
  (* This is implied by the above, so it could be removed, added to
  void writing a proof. *)
  assert_dec
    (module_items_sorted (Verilog.module_inputs vmodule) (Verilog.modBody vmodule))
    "Module items unsorted"%string ;;
  let var_assignment := assign_vars var_start (Verilog.modVariables vmodule) in
  let* nameMap := mk_bijection name_tag var_assignment in
  let* assertions :=
    transfer_module_body
      name_tag
      nameMap
      (Verilog.module_inputs vmodule)
      (Verilog.module_outputs vmodule)
      (Verilog.modBody vmodule)
  in
  inr {|
      SMT.nameMap := nameMap;
      SMT.query := assertions
    |}
.
