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
From vera Require EnvStack.
From vera Require Import Bitvector.
From vera Require Import SMT.

Import ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.

Definition transf := sum string.

Definition cast_from_to (from to: N) (expr : SMTLib.term) : SMTLib.term :=
  match N.compare to from with
  | Lt => SMTLib.Term_BVExtract (nat_of_N (to - 1)) 0 expr
  | Gt => SMTLib.Term_BVConcat (SMTLib.Term_BVLit (BV.zeros (to - from))) expr
  | Eq => expr
  end
.

Section expr_to_smt.
  Variable var_verilog_to_smt : StrFunMap.t (nat * SMTLib.sort).

  Definition term_for_name (t : Verilog.vtype) (name : string) : transf SMTLib.term :=
    match var_verilog_to_smt name with
    | None => raise ("Name not declared: " ++ name)%string
    | Some (n__smt, sort) =>
        match sort with
        | SMTLib.Sort_BitVec sort_len =>
            if (sort_len =? t)%N
            then ret (SMTLib.Term_Fun (n__smt, ([], sort)) [])
            else raise ("Incorrect sort for " ++ name)%string
        | _ => raise ("Incorrect sort for " ++ name)%string
        end
    end.


  Equations expr_to_smt : Verilog.expression -> transf SMTLib.term :=
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
      let t__lhs := Verilog.expr_type lhs in
      let t__rhs := Verilog.expr_type rhs in
      let t__shift := N.max t__lhs t__rhs in
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (cast_from_to t__shift t__lhs
             (SMTLib.Term_BVBinOp SMTLib.BVShl
                (cast_from_to t__lhs t__shift lhs__smt)
                (cast_from_to t__rhs t__shift rhs__smt)));
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryShiftLeftArithmetic lhs rhs) :=
      let t__lhs := Verilog.expr_type lhs in
      let t__rhs := Verilog.expr_type rhs in
      let t__shift := N.max t__lhs t__rhs in
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (cast_from_to t__shift t__lhs
             (SMTLib.Term_BVBinOp SMTLib.BVShl
                (cast_from_to t__lhs t__shift lhs__smt)
                (cast_from_to t__rhs t__shift rhs__smt)));
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryShiftRight lhs rhs) :=
      let t__lhs := Verilog.expr_type lhs in
      let t__rhs := Verilog.expr_type rhs in
      let t__shift := N.max t__lhs t__rhs in
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (cast_from_to t__shift t__lhs
             (SMTLib.Term_BVBinOp SMTLib.BVShr
                (cast_from_to t__lhs t__shift lhs__smt)
                (cast_from_to t__rhs t__shift rhs__smt)));
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
    expr_to_smt (Verilog.Concatenation []) :=
      raise "Unsupported empty concatenation in SMT"%string;
    expr_to_smt (Verilog.Concatenation (hd :: tl)) :=
      hd__smt <- expr_to_smt hd ;;
      tl__smt <- mapT expr_to_smt tl ;;
      ret (fold_left SMTLib.Term_BVConcat tl__smt hd__smt);
    expr_to_smt (Verilog.Conditional cond ifT ifF) :=
      let t__cond := Verilog.expr_type cond in
      condval__smt <- expr_to_smt cond ;;
      ifT__smt <- expr_to_smt ifT ;;
      ifF__smt <- expr_to_smt ifF ;;
      let cond__smt := SMTLib.Term_Not
                       (SMTLib.Term_Eq
                          condval__smt
                          (SMTLib.Term_BVLit (BV.zeros t__cond)))
      in
      ret (SMTLib.Term_ITE cond__smt ifT__smt ifF__smt);
    expr_to_smt (Verilog.BitSelect vec idx) :=
      let t__vec := Verilog.expr_type vec in
      let t__idx := Verilog.expr_type idx in
      let t__shift := N.max t__vec t__idx in
      vec__smt <- expr_to_smt vec ;;
      idx__smt <- expr_to_smt idx ;;
      ret (SMTLib.Term_BVExtract 0 0
             (SMTLib.Term_BVBinOp SMTLib.BVShr
                (cast_from_to t__vec t__shift vec__smt)
                (cast_from_to t__idx t__shift idx__smt)));
    expr_to_smt (Verilog.Resize to expr) :=
      let from := Verilog.expr_type expr in
      expr__smt <- expr_to_smt expr ;;
      ret (cast_from_to from to expr__smt);
    expr_to_smt (Verilog.IntegerLiteral val) :=
      ret (SMTLib.Term_BVLit val);
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

Definition transfer_ports (ports : list Verilog.port) : list (string * port_direction) :=
  map (fun '(Verilog.MkPort dir name) => (name, dir)) ports.

Fixpoint transfer_vars (start : nat) (vars : list Verilog.variable) : list (string * nat * SMTLib.sort) :=
  match vars with
  | (Verilog.MkVariable vec storage name) :: rest =>
      (name, start, (SMTLib.Sort_BitVec (Verilog.vector_declaration_width vec))) :: (transfer_vars (1 + start) rest)
  | nil => nil
  end.

Definition declarations_of_vars : list (string * nat * SMTLib.sort) -> list (nat * SMTLib.sort) :=
  List.map (fun '(_, n, s) => (n, s)).

Definition names_of_vars (vars : list (string * nat * SMTLib.sort)) : StrFunMap.t (nat * SMTLib.sort) :=
  List.fold_left
    (fun acc '(verilog__name, smt__name, sort) => StrFunMap.insert verilog__name (smt__name, sort) acc)
    vars StrFunMap.empty.

Equations transfer_initial (stmt : Verilog.statement) : transf (list SMTLib.term) :=
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

Definition verilog_to_smt (var_start : nat) (vmodule : Verilog.vmodule) : transf (StrFunMap.t (nat * SMTLib.sort) * SMT.smtlib_query) :=
  match Verilog.modBody vmodule with
  | [ Verilog.Initial initial_body;
      Verilog.AlwaysFF (Verilog.Block []);
      Verilog.AlwaysComb always_comb_body
    ] =>
      let ports := transfer_ports (Verilog.modPorts vmodule) in
      let var_decls := transfer_vars var_start (Verilog.modVariables vmodule) in
      let var_map := names_of_vars var_decls in
      initial_smt <- transfer_initial initial_body ;;
      always_comb_smt <- transfer_comb_assignments var_map always_comb_body ;;
      ret (var_map, {|
          SMT.declarations := declarations_of_vars var_decls;
          SMT.assertions := initial_smt ++ always_comb_smt
        |})
  | [ Verilog.Initial _;
      Verilog.AlwaysFF _;
      Verilog.AlwaysComb _
    ] => raise "always_ff not yet supported"%string
  | _ => raise "Non-canonical verilog passed to verilog_to_smt"%string
  end
.
