From vvequiv Require Verilog.
From vvequiv Require Netlist.
From vvequiv Require VerilogToNetlist.
From vvequiv Require NetlistToSMT.
From vvequiv Require SMT.

From Coq Require Extraction.
From Coq Require Import extraction.ExtrOcamlBasic.
From Coq Require Import extraction.ExtrOcamlString.
From Coq Require Import extraction.ExtrOcamlZInt.
From Coq Require Import BinInt.

Extraction Language OCaml.

Extract Inlined Constant List.flat_map => "List.concat_map".

Extraction "VVEquiv.ml"
  Bitvector.Bitvector
  Verilog.Verilog
  VerilogToNetlist.verilog_to_netlist
  Netlist.Netlist
  NetlistToSMT.netlist_to_smt
  SMT.QFBV
  SMT.Core
  .
