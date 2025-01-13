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

From vera Require Import Verilog.
From vera Require Import SMT.
From vera Require Import Common.
From vera Require EnvStack.
From vera Require Import Bitvector.

Import ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.

Definition transf := sum string.

Definition cast_from_to {name} (from to: N) (expr : SMT.qfbv name) : SMT.qfbv name :=
  match N.compare to from with
  | Lt => SMT.BVExtract (to - 1) 0 expr
  | Gt => SMT.BVZeroExtend (to - from) expr
  | Eq => expr
  end
.

Equations expr_to_smt : Verilog.expression -> transf (SMT.qfbv string) :=
  expr_to_smt (Verilog.UnaryOp Verilog.UnaryPlus operand) :=
    expr_to_smt operand ;
  expr_to_smt (Verilog.UnaryOp Verilog.UnaryMinus operand) :=
    operand__smt <- expr_to_smt operand ;;
    ret (SMT.BVNeg operand__smt);
  expr_to_smt (Verilog.UnaryOp Verilog.UnaryNegation operand) :=
    operand__smt <- expr_to_smt operand ;;
    ret (SMT.BVNot operand__smt);
  expr_to_smt (Verilog.BinaryOp Verilog.BinaryPlus lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVAdd lhs__smt rhs__smt);
  expr_to_smt (Verilog.BinaryOp Verilog.BinaryMinus lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVAdd lhs__smt (SMT.BVNeg rhs__smt));
  expr_to_smt (Verilog.BinaryOp Verilog.BinaryStar lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVMul lhs__smt rhs__smt);
  expr_to_smt (Verilog.BinaryOp Verilog.BinaryShiftLeft lhs rhs) :=
    let t__lhs := Verilog.expr_type lhs in
    let t__rhs := Verilog.expr_type rhs in
    let t__shift := N.max t__lhs t__rhs in
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (cast_from_to t__shift t__lhs
           (SMT.BVShl
              (cast_from_to t__lhs t__shift lhs__smt)
              (cast_from_to t__rhs t__shift rhs__smt)));
  expr_to_smt (Verilog.BinaryOp Verilog.BinaryShiftLeftArithmetic lhs rhs) :=
    let t__lhs := Verilog.expr_type lhs in
    let t__rhs := Verilog.expr_type rhs in
    let t__shift := N.max t__lhs t__rhs in
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (cast_from_to t__shift t__lhs
           (SMT.BVShl
              (cast_from_to t__lhs t__shift lhs__smt)
              (cast_from_to t__rhs t__shift rhs__smt)));
  expr_to_smt (Verilog.BinaryOp Verilog.BinaryShiftRight lhs rhs) :=
    let t__lhs := Verilog.expr_type lhs in
    let t__rhs := Verilog.expr_type rhs in
    let t__shift := N.max t__lhs t__rhs in
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (cast_from_to t__shift t__lhs
           (SMT.BVLShr
              (cast_from_to t__lhs t__shift lhs__smt)
              (cast_from_to t__rhs t__shift rhs__smt)));
  expr_to_smt (Verilog.BinaryOp Verilog.BinaryBitwiseOr lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVOr lhs__smt rhs__smt);
  expr_to_smt (Verilog.BinaryOp Verilog.BinaryBitwiseAnd lhs rhs) :=
    lhs__smt <- expr_to_smt lhs ;;
    rhs__smt <- expr_to_smt rhs ;;
    ret (SMT.BVAnd lhs__smt rhs__smt);
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
  expr_to_smt (Verilog.Concatenation []) :=
    raise "Unsupported empty concatenation in SMT"%string;
  expr_to_smt (Verilog.Concatenation (hd :: tl)) :=
    hd__smt <- expr_to_smt hd ;;
    tl__smt <- mapT expr_to_smt tl ;;
    ret (fold_left SMT.BVConcat tl__smt hd__smt);
  expr_to_smt (Verilog.Conditional cond ifT ifF) :=
    let t__cond := Verilog.expr_type cond in
    condval__smt <- expr_to_smt cond ;;
    ifT__smt <- expr_to_smt ifT ;;
    ifF__smt <- expr_to_smt ifF ;;
    let cond__smt := SMT.CoreNot
                     (SMT.CoreEq
                        condval__smt
                        (SMT.BVLit (BV.zeros t__cond)))
    in
    ret (SMT.CoreITE cond__smt ifT__smt ifF__smt);
  expr_to_smt (Verilog.BitSelect vec idx) :=
    let t__vec := Verilog.expr_type vec in
    let t__idx := Verilog.expr_type idx in
    let t__shift := N.max t__vec t__idx in
    vec__smt <- expr_to_smt vec ;;
    idx__smt <- expr_to_smt idx ;;
    ret (SMT.BVExtract 0 0
           (SMT.BVLShr
              (cast_from_to t__vec t__shift vec__smt)
              (cast_from_to t__idx t__shift idx__smt)));
  expr_to_smt (Verilog.Resize to expr) :=
    let from := Verilog.expr_type expr in
    expr__smt <- expr_to_smt expr ;;
    ret (cast_from_to from to expr__smt);
  expr_to_smt (Verilog.IntegerLiteral val) :=
    ret (SMT.BVLit val);
  expr_to_smt (Verilog.NamedExpression t n) :=
    ret (SMT.BVVar n).

Definition transfer_ports (ports : list Verilog.port) : list (string * port_direction) :=
  map (fun '(Verilog.MkPort dir name) => (name, dir)) ports.

Definition transfer_vars (vars : list Verilog.variable) : list (SMT.formula string) :=
  map
    (fun '(Verilog.MkVariable vec storage name) =>
       SMT.CDeclare name
         (SMT.SBitVector (Verilog.vector_declaration_width vec)))
    vars.

Equations transfer_initial (stmt : Verilog.statement) : transf (list (SMT.formula string)) :=
  transfer_initial (Verilog.Block stmts) =>
    lists <- mapT transfer_initial stmts ;;
    ret (concat lists) ;
  transfer_initial (Verilog.BlockingAssign
                      (Verilog.NamedExpression _ n)
                      (Verilog.IntegerLiteral val)) =>
    (* raise "VerilogToSMT: initial block blegh"%string; *)
    ret [] ;
  transfer_initial (Verilog.BlockingAssign
                      (Verilog.NamedExpression _ n)
                      (Verilog.Resize _ (Verilog.IntegerLiteral val))) =>
    (* raise "VerilogToSMT: initial block blegh"%string; *)
    ret [] ;
  transfer_initial _ =>
    raise "VerilogToSMT: Invalid expression in initial block"%string
.

Equations transfer_comb_assignments : Verilog.statement -> transf (list (SMT.formula string)) :=
  transfer_comb_assignments (Verilog.Block stmts) =>
    lists <- mapT transfer_comb_assignments stmts ;;
    ret (concat lists) ;
  transfer_comb_assignments (Verilog.BlockingAssign (Verilog.NamedExpression _ name) rhs) =>
    rhs__smt <- expr_to_smt rhs ;;
    ret [SMT.CEqual (SMT.BVVar name) rhs__smt] ;
  transfer_comb_assignments _ =>
    raise "VerilogToSMT: Invalid expression in always_comb block"%string
.

Definition verilog_to_smt (vmodule : Verilog.vmodule) : transf (SMT.smt_netlist string) :=
  match Verilog.modBody vmodule with
  | [ Verilog.Initial initial_body;
      Verilog.AlwaysFF (Verilog.Block []);
      Verilog.AlwaysComb always_comb_body
    ] =>
      let ports := transfer_ports (Verilog.modPorts vmodule) in
      let var_decls := transfer_vars (Verilog.modVariables vmodule) in
      initial_smt <- transfer_initial initial_body ;;
      always_comb_smt <- transfer_comb_assignments always_comb_body ;;
      ret {|
          SMT.smtnlName := Verilog.modName vmodule ;
          SMT.smtnlPorts := ports ;
          SMT.smtnlFormulas := var_decls ++ initial_smt ++ always_comb_smt
        |}
  | [ Verilog.Initial _;
      Verilog.AlwaysFF _;
      Verilog.AlwaysComb _
    ] => raise "always_ff not yet supported"%string
  | _ => raise "Non-canonical verilog passed to verilog_to_smt"%string
  end
.
