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

From Coq Require Import ZArith.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Sorting.Permutation.

Import ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.
Local Open Scope string.

Definition mk_equivalence_formulas
  (inputs outputs : list string)
  (namemap1 namemap2 : StrFunMap.t (nat * SMTLib.sort))
  : sum string (list SMTLib.term) :=
  inputs_same <-
    mapT (fun n =>
            match namemap1 n, namemap2 n with
            | Some (smt_name1, SMTLib.Sort_BitVec size1),
              Some (smt_name2, SMTLib.Sort_BitVec size2) =>
                if (size1 =? size2)%N
                then inr (SMTLib.Term_Eq
                            (SMTLib.Term_Fun (smt_name1, ([], SMTLib.Sort_BitVec size1)) [])
                            (SMTLib.Term_Fun (smt_name2, ([], SMTLib.Sort_BitVec size2)) []))
                else inl "err"%string
            | _, _ => inl "err"%string
            end) inputs;;

  outputs_different <-
    mapT (
        fun n =>
          match namemap1 n, namemap2 n return sum string SMTLib.term with
          | Some (smt_name1, SMTLib.Sort_BitVec size1),
            Some (smt_name2, SMTLib.Sort_BitVec size2) =>
              if (size1 =? size2)%N
              then inr (SMTLib.Term_Not (SMTLib.Term_Eq
                                           (SMTLib.Term_Fun (smt_name1, ([], SMTLib.Sort_BitVec size1)) [])
                                           (SMTLib.Term_Fun (smt_name2, ([], SMTLib.Sort_BitVec size2)) [])))
              else inl "err"%string
          | _, _ => inl "err"%string
          end) outputs;;

  let outputs_different_any :=
    List.fold_left
      (fun acc q => SMTLib.Term_Or acc q)
      outputs_different
      SMTLib.Term_False
  in
  ret (app inputs_same [outputs_different_any])
.

Axiom dec_permutation : forall (l1 l2 : list string), { Permutation l1 l2 } + { ~ Permutation l1 l2 }.

Definition assert_dec {P E} (dec : { P } + { ~ P }) (err : E) : sum E P :=
  match dec with
  | left prf => inr prf
  | right _  => inl err
  end
.

Definition equivalence_query_canonical
  (canonical_verilog1 canonical_verilog2 : Verilog.vmodule)
  : sum string (SMT.smtlib_query) :=

  inputs_ok1 <- assert_dec
                 (list_eq_dec string_dec (Verilog.inputs canonical_verilog1) (Verilog.inputs canonical_verilog2))
                 "Inputs don't match" ;;

  outputs_ok2 <- assert_dec
                 (list_eq_dec string_dec (Verilog.outputs canonical_verilog1) (Verilog.outputs canonical_verilog2))
                 "Outputs don't match" ;;

  query1 <- VerilogToSMT.verilog_to_smt 0 canonical_verilog1 ;;
  query2 <- VerilogToSMT.verilog_to_smt (1 + SMT.max_var query1) canonical_verilog2 ;;
  equivalence_formulas <-
    mk_equivalence_formulas
      (Verilog.inputs canonical_verilog1) (Verilog.outputs canonical_verilog1)
      (SMT.nameVerilogToSMT query1) (SMT.nameVerilogToSMT query2) ;;

  ret {|
      SMT.nameSMTToVerilog :=
        NatFunMap.combine
          (NatFunMap.map (fun s => "left__" ++ s) (SMT.nameSMTToVerilog query1))
          (NatFunMap.map (fun s => "right__" ++ s) (SMT.nameSMTToVerilog query2));
      SMT.nameVerilogToSMT :=
        StrFunMap.combine
          (SMT.nameVerilogToSMT query1)
          (SMT.nameVerilogToSMT query2);
      SMT.declarations := SMT.declarations query1 ++ SMT.declarations query2;
      SMT.assertions := SMT.assertions query1 ++ SMT.assertions query2 ++ equivalence_formulas
    |}
.

Definition equivalence_query (verilog1 verilog2 : Verilog.vmodule) : sum string SMT.smtlib_query :=
  VerilogTypecheck.tc_vmodule verilog1 ;;
  VerilogTypecheck.tc_vmodule verilog2 ;;

  inputs_ok1 <- assert_dec (list_eq_dec string_dec (Verilog.inputs verilog1) (Verilog.inputs verilog2)) "Inputs don't match" ;;
  outputs_ok2 <- assert_dec (list_eq_dec string_dec (Verilog.outputs verilog1) (Verilog.outputs verilog2)) "Outputs don't match" ;;

  canonical_verilog1 <- VerilogCanonicalize.canonicalize_verilog verilog1 ;;
  canonical_verilog2 <- VerilogCanonicalize.canonicalize_verilog verilog2 ;;

  equivalence_query_canonical canonical_verilog1 canonical_verilog2
.
