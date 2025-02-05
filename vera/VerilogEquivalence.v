From vera Require Import Verilog.
From vera Require Import SMT.
From vera Require Import Common.
From vera Require VerilogTypecheck.
From vera Require VerilogCanonicalize.
From vera Require VerilogToSMT.

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

Require Import ZArith.
Require Import String.
Require Import List.

Import ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.
Local Open Scope string.

Section prefixing.
  Variable prefix : string.

  Definition prefix_name (name : string) : string :=
    prefix ++ "__" ++ name.

  Equations prefix_names_qfbv : SMT.qfbv string -> SMT.qfbv string := {
    | SMT.BVVar n => SMT.BVVar (prefix_name n)
    | SMT.BVOr l r => SMT.BVOr (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVAnd l r => SMT.BVAnd (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVAdd l r => SMT.BVAdd (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVMul l r => SMT.BVMul (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVNeg e => SMT.BVNeg (prefix_names_qfbv e)
    | SMT.BVNot e => SMT.BVNot (prefix_names_qfbv e)
    | SMT.BVShl l r => SMT.BVShl (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVLShr l r => SMT.BVLShr (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVLit val => SMT.BVLit val
    | SMT.BVZeroExtend count e => SMT.BVZeroExtend count (prefix_names_qfbv e)
    | SMT.BVExtract lo hi e => SMT.BVExtract lo hi (prefix_names_qfbv e)
    | SMT.BVConcat l r => SMT.BVConcat (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.CoreEq l r => SMT.CoreEq (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.CoreNot e => SMT.CoreNot (prefix_names_qfbv e)
    | SMT.CoreITE cond ifT ifF => SMT.CoreITE (prefix_names_qfbv cond) (prefix_names_qfbv ifT) (prefix_names_qfbv ifF)
    }.

  Equations prefix_names_formula : SMT.formula string -> SMT.formula string := {
    | SMT.CDeclare name sort => SMT.CDeclare (prefix_name name) sort
    | SMT.CEqual l r => SMT.CEqual (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.CDistinct l r => SMT.CDistinct (prefix_names_qfbv l) (prefix_names_qfbv r)
    }.

  Definition prefix_names_formulas : list (SMT.formula string) -> list (SMT.formula string) :=
    List.map prefix_names_formula.

  Definition prefix_names_smt_netlist (smtnl : SMT.smt_netlist string) : SMT.smt_netlist string :=
    {| SMT.smtnlName := SMT.smtnlName smtnl ;
      SMT.smtnlPorts := List.map (fun '(name, dir) => (prefix_name name, dir) ) (SMT.smtnlPorts smtnl) ;
      SMT.smtnlFormulas := List.map prefix_names_formula (SMT.smtnlFormulas smtnl)
    |}.
End prefixing.

Definition prefix_pair (prefix_left prefix_right : string): (string * string) -> (string * string) :=
  fun '(n1, n2) => (prefix_name prefix_left n1, prefix_name prefix_right n2).

Definition mk_equivalence_formulas
  (input_pairs output_pairs : list (string * string))
  (namemap1 namemap2 : StrFunMap.t (nat * SMTLib.sort))
  : sum string (list SMTLib.term) :=
  inputs_same <-
    mapT (fun '(n1, n2) =>
            match namemap1 n1, namemap2 n2 return sum string SMTLib.term with
            | Some (smt_name1, SMTLib.Sort_BitVec size1),
              Some (smt_name2, SMTLib.Sort_BitVec size2) =>
                if (size1 =? size2)%N
                then inr (SMTLib.Term_Eq
                            (SMTLib.Term_Fun (smt_name1, ([], SMTLib.Sort_BitVec size1)) [])
                            (SMTLib.Term_Fun (smt_name2, ([], SMTLib.Sort_BitVec size2)) []))
                else inl "err"%string
            | _, _ => inl "err"%string
            end) input_pairs;;
  outputs_different <-
    mapT (
        fun '(n1, n2) =>
          match namemap1 n1, namemap2 n2 return sum string SMTLib.term with
          | Some (smt_name1, SMTLib.Sort_BitVec size1),
            Some (smt_name2, SMTLib.Sort_BitVec size2) =>
              if (size1 =? size2)%N
              then inr (SMTLib.Term_Not (SMTLib.Term_Eq
                                           (SMTLib.Term_Fun (smt_name1, ([], SMTLib.Sort_BitVec size1)) [])
                                           (SMTLib.Term_Fun (smt_name2, ([], SMTLib.Sort_BitVec size2)) [])))
              else inl "err"%string
          | _, _ => inl "err"%string
          end) output_pairs;;
  ret (app inputs_same outputs_different)
.

Definition equivalence_query
  (input_pairs output_pairs : list (string * string))
  (verilog1 verilog2 : Verilog.vmodule)
  : sum string SMT.smtlib_query :=

  VerilogTypecheck.tc_vmodule verilog1 ;;
  VerilogTypecheck.tc_vmodule verilog2 ;;

  canonical_verilog1 <- VerilogCanonicalize.canonicalize_verilog verilog1 ;;
  canonical_verilog2 <- VerilogCanonicalize.canonicalize_verilog verilog2 ;;

  '(query1_map, query1) <- VerilogToSMT.verilog_to_smt 0 canonical_verilog1 ;;
  '(query2_map, query2) <- VerilogToSMT.verilog_to_smt (1 + SMT.max_var query1) canonical_verilog2 ;;
  equivalence_formulas <- mk_equivalence_formulas input_pairs output_pairs query1_map query2_map ;;

  ret {|
      SMT.declarations := SMT.declarations query1 ++ SMT.declarations query2;
      SMT.assertions := SMT.assertions query1 ++ SMT.assertions query2 ++ equivalence_formulas
    |}
.
