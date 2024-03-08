Require Import Verilog.
Require Import VerilogToNetlist.
Require Import NetlistToSMT.
Require Import SMT.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Data.Monads.EitherMonad.
Import MonadNotation.
Open Scope monad_scope.
Require Import String.
Require Import List.
Import ListNotations.


Definition equivalence_query (verilog1 verilog2 : Verilog.vmodule) : sum string (list Core.formula) :=
  netlist1 <- verilog_to_netlist verilog1 ;;
  netlist2 <- verilog_to_netlist verilog2 ;;
  let smt_netlist1 := netlist_to_smt netlist1 in
  let smt_netlist2 := netlist_to_smt netlist2 in
  let formulas1 := (Core.smtnlFormulas smt_netlist1) in
  let formulas2 := (Core.smtnlFormulas smt_netlist2) in
  ret (formulas1 ++ formulas2)
.
