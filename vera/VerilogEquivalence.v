From vera Require Import Verilog.
From vera Require VerilogSemantics.
Import VerilogSemantics.Sort.
From vera Require Import VerilogSMT.
From vera Require Import Common.
From vera Require AssignmentForwarding.
From vera Require VerilogToSMT.
From vera Require SMTQueries.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require DropInternal.

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

From Stdlib Require Import ZArith.
From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Structures.Equalities.

From Equations Require Import Equations.

Import SigTNotations.
Import ListNotations.
Import CommonNotations.
Import MonadLetNotation.
Import FunctorNotation.
Local Open Scope monad_scope.
Local Open Scope string.

Definition mk_var_same (var : Verilog.variable) : (SMTLib.term SMTLib.Sort_Bool) := 
  SMTLib.Term_Eq (SMTLib.Term_Const (verilog_to_smt_var VerilogLeft var))
                 (SMTLib.Term_Const (verilog_to_smt_var VerilogRight var)).

Equations mk_inputs_same (inputs : list Verilog.variable) : SMTLib.term SMTLib.Sort_Bool := {
  | [] => SMTLib.Term_True
  | (var :: vars) => SMTLib.Term_And (mk_var_same var) (mk_inputs_same vars)
}.

Definition mk_var_distinct (var : Verilog.variable) : SMTLib.term SMTLib.Sort_Bool :=
  SMTLib.Term_Not (SMTLib.Term_Eq (SMTLib.Term_Const (verilog_to_smt_var VerilogLeft var))
                                  (SMTLib.Term_Const (verilog_to_smt_var VerilogRight var)))
  .

Equations mk_outputs_distinct (inputs : list Verilog.variable) : SMTLib.term SMTLib.Sort_Bool := {
  | [] => SMTLib.Term_False
  | (var :: vars) => SMTLib.Term_Or (mk_var_distinct var) (mk_outputs_distinct vars)
}.

Program Definition equivalence_query (verilog1 verilog2 : Verilog.vmodule) : sum string SMTQueries.query :=
  let* inputs_ok1 :=
    assert_dec
      (Verilog.module_inputs verilog1 = Verilog.module_inputs verilog2)
      ("Inputs don't match:" ++ newline
      ++ to_string (Verilog.module_inputs verilog1) ++ newline
      ++ to_string (Verilog.module_inputs verilog2) )
    in
  let* outputs_ok1 :=
    assert_dec
      (Verilog.module_outputs verilog1 = Verilog.module_outputs verilog2)
      ("Outputs don't match:" ++ newline
      ++ to_string (Verilog.module_outputs verilog1) ++ newline
      ++ to_string (Verilog.module_outputs verilog2) )
    in

  let* smt1 := VerilogToSMT.verilog_to_smt VerilogLeft verilog1 in
  let* smt2 := VerilogToSMT.verilog_to_smt VerilogRight verilog2 in

  let inputs_same := mk_inputs_same (Verilog.module_inputs verilog1) in
  let outputs_distinct := mk_outputs_distinct (Verilog.module_outputs verilog1) in

  inr (inputs_same :: outputs_distinct :: (smt1 ++ smt2))
.
