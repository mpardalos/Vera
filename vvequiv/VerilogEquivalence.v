Require Import Verilog.
Require Import Netlist.
Require Import VerilogToNetlist.
Require Import NetlistToSMT.
Require Import SMT.
Require Import Common.
Require VerilogTypecheck.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Data.Monads.EitherMonad.
Import MonadNotation.
Open Scope monad_scope.
Require Import ZArith.
Require Import String.
Require Import List.
Import ListNotations.
Import EqNotations.

Definition mk_equivalence_formulas (smtnl1 smtnl2 : SMT.smt_netlist name) : sum string (list (SMT.formula name)) :=
  let inputs1 := filter (fun (a: (name * port_direction)) => let (_, dir) := a in is_port_in dir) (SMT.smtnlPorts smtnl1) in
  let inputs2 := filter (fun (a: (name * port_direction)) => let (_, dir) := a in is_port_in dir) (SMT.smtnlPorts smtnl2) in
  let outputs1 := filter (fun (a: (name * port_direction)) => let (_, dir) := a in is_port_out dir) (SMT.smtnlPorts smtnl1) in
  let outputs2 := filter (fun (a: (name * port_direction)) => let (_, dir) := a in is_port_out dir) (SMT.smtnlPorts smtnl2) in
  if negb (length inputs1 =? length inputs2) then inl "Input counts do not match"%string
  else if negb (length outputs1 =? length outputs2) then inl "Output counts do not match"%string
       else let input_pairs: list ((name * port_direction) * (name * port_direction)) := combine inputs1 inputs2 in
            let output_pairs: list ((name * port_direction) * (name * port_direction)) := combine outputs1 outputs2 in
            let inputs_same :=
              map (fun a =>
                     let in1 := fst (fst a) in
                     let in2 := fst (snd a) in
                     SMT.CEqual (SMT.BVVar in1) (SMT.BVVar in2))
                input_pairs in
            let outputs_different :=
              map (fun a =>
                     let in1 := fst (fst a) in
                     let in2 := fst (snd a) in
                     SMT.CDistinct (SMT.BVVar in1) (SMT.BVVar in2))
                output_pairs in
            inr (inputs_same ++ outputs_different)
.

Definition equivalence_query (verilog1 verilog2 : Verilog.vmodule) : sum string (list (SMT.formula name)) :=
  typed_verilog1 <- VerilogTypecheck.tc_vmodule verilog1 ;;
  typed_verilog2 <- VerilogTypecheck.tc_vmodule verilog2 ;;
  netlist_result1 <- verilog_to_netlist 1%positive typed_verilog1  ;;
  let netlist1 := fst netlist_result1 in
  let final_state := snd netlist_result1 in
  netlist_result2 <- verilog_to_netlist (nextName final_state) typed_verilog2 ;;
  let netlist2 := fst netlist_result2 in
  let smt_netlist1 := netlist_to_smt netlist1 in
  let smt_netlist2 := netlist_to_smt netlist2 in
  let formulas1 := (SMT.smtnlFormulas smt_netlist1) in
  let formulas2 := (SMT.smtnlFormulas smt_netlist2) in
  equivalence_formulas <- mk_equivalence_formulas smt_netlist1 smt_netlist2 ;;
  (** Add equivalence queries *)
  ret (formulas1 ++ formulas2 ++ equivalence_formulas)
.
