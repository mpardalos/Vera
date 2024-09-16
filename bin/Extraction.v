From vera Require Netlist.
From vera Require NetlistToSMT.
From vera Require SMT.
From vera Require Verilog.
From vera Require VerilogEquivalence.
From vera Require VerilogToNetlist.
From vera Require Common.
From vera Require ParseRawVerilog.

From Coq Require Extraction.
From Coq Require Import extraction.ExtrOcamlBasic.
From Coq Require Import extraction.ExtrOcamlString.
From Coq Require Import extraction.ExtrOcamlZInt.
From Coq Require Import BinInt.

Extraction Language OCaml.

Extract Inlined Constant List.flat_map => "List.concat_map".


Extraction "Vera.ml"
  VerilogEquivalence.equivalence_query
  Verilog.Verilog
  VerilogTypecheck.tc_vmodule
  Verilog.TypedVerilog
  VerilogToNetlist.verilog_to_netlist
  Netlist.Netlist
  NetlistToSMT.netlist_to_smt
  SMT.SMT
  Common.NameMap
  ParseRawVerilog.parse_raw_verilog
  .
