From vera Require Import Verilog.
From vera Require Import SMT.
Import (coercions) SMT.
From vera Require Import Common.
Import (coercions) VerilogSMTBijection.
Import VerilogSMTBijection (bij_inverse, bij_apply, bij_wf).
From vera Require VerilogTypecheck.
From vera Require VerilogCanonicalize.
From vera Require VerilogToSMT.
From vera Require Import Decidable.

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
From Coq Require Import Structures.Equalities.

Import ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.
Local Open Scope string.

Equations mk_var_same (var : Verilog.variable) (namemap : VerilogSMTBijection.t)
  : sum string SMTLib.term := {
  | var, namemap with namemap (TaggedVariable.VerilogLeft, Verilog.varName var), namemap (TaggedVariable.VerilogRight, Verilog.varName var) => {
    | Some smt_name1, Some smt_name2 =>
        inr (SMTLib.Term_Eq (SMTLib.Term_Const smt_name1) (SMTLib.Term_Const smt_name2))
    | _, _ => inl "mk_var_same"%string
    }
  }
  .

Equations mk_inputs_same (inputs : list Verilog.variable) (namemap : VerilogSMTBijection.t)
  : sum string SMTLib.term := {
  | [], m => inr SMTLib.Term_True
  | (var :: vars), m =>
      match
        mk_var_same var m,
        mk_inputs_same vars m
      with
      | inr hd, inr tl =>
          inr (SMTLib.Term_And hd tl)
      | _, _ => inl "err"%string
      end
  }.

Equations mk_var_distinct (var : Verilog.variable) (namemap : VerilogSMTBijection.t)
  : sum string SMTLib.term := {
  | var, namemap with namemap (TaggedVariable.VerilogLeft, Verilog.varName var), namemap (TaggedVariable.VerilogRight, Verilog.varName var) => {
    | Some smt_name1, Some smt_name2 =>
        inr (SMTLib.Term_Not (SMTLib.Term_Eq (SMTLib.Term_Const smt_name1) (SMTLib.Term_Const smt_name2)))
    | _, _ => inl "mk_var_distinct"%string
    }
  }
  .

Equations mk_outputs_distinct (inputs : list Verilog.variable) (namemap : VerilogSMTBijection.t)
  : sum string SMTLib.term := {
  | [], m => inr SMTLib.Term_False
  | (var :: vars), m =>
      match
        mk_var_distinct var m,
        mk_outputs_distinct vars m
      with
      | inr hd, inr tl =>
          inr (SMTLib.Term_Or hd tl)
      | _, _ => inl "err"%string
      end
  }.

Program Definition equivalence_query_canonical
  (canonical_verilog1 canonical_verilog2 : Verilog.vmodule)
  : sum string (SMT.smt_with_namemap) :=

  inputs_ok1 <- assert_dec (Verilog.module_inputs canonical_verilog1 = Verilog.module_inputs canonical_verilog2) "Inputs don't match" ;;
  outputs_ok1 <- assert_dec (Verilog.module_outputs canonical_verilog1 = Verilog.module_outputs canonical_verilog2) "Outputs don't match" ;;

  smt1 <- VerilogToSMT.verilog_to_smt TaggedVariable.VerilogLeft 0 canonical_verilog1 ;;
  smt2 <- VerilogToSMT.verilog_to_smt TaggedVariable.VerilogRight (1 + SMT.max_var (SMT.query smt1)) canonical_verilog2 ;;

  let nameMap := VerilogSMTBijection.combine (SMT.nameMap smt1) (SMT.nameMap smt2) _ _ in

  inputs_same <- mk_inputs_same (Verilog.module_inputs canonical_verilog1) nameMap ;;
  outputs_distinct <- mk_outputs_distinct (Verilog.module_outputs canonical_verilog1) nameMap ;;

  ret {|
      SMT.nameMap := nameMap ;
      SMT.widths := SMT.widths smt1 ++ SMT.widths smt2;
      SMT.query := (SMT.query smt1 ++ SMT.query smt2 ++ [inputs_same] ++ [outputs_distinct])%list
    |}
.
Next Obligation. (* No shared verilog names *) Admitted.
Next Obligation. (* No shared SMT names *) Admitted.

Definition equivalence_query (verilog1 verilog2 : Verilog.vmodule) : sum string SMT.smt_with_namemap :=
  VerilogTypecheck.tc_vmodule verilog1 ;;
  VerilogTypecheck.tc_vmodule verilog2 ;;

  canonical_verilog1 <- VerilogCanonicalize.canonicalize_verilog verilog1 ;;
  canonical_verilog2 <- VerilogCanonicalize.canonicalize_verilog verilog2 ;;

  equivalence_query_canonical canonical_verilog1 canonical_verilog2
.
