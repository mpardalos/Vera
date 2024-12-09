From Coq Require Import List.

From vera Require Import Verilog.
From vera Require Import VerilogSemantics.
From vera Require Import VerilogCanonicalize.
From vera Require Import Common.
From vera Require Import Bitvector.
Import (notations) Bitvector.BV.

Import ListNotations.
Local Open Scope monad_scope.
Local Open Scope bv_scope.

Theorem canonicalize_correct (m1 m2 : Verilog.vmodule) (st_final : CombinationalOnly.VerilogState) :
  canonicalize_module m1 = inr m2 ->
  CombinationalOnly.multistep_eval (CombinationalOnly.initial_state m1) st_final ->
  CombinationalOnly.multistep_eval (CombinationalOnly.initial_state m2) st_final.
Admitted.
