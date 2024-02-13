From vvequiv Require Verilog.
From vvequiv Require Netlist.
From vvequiv Require VerilogToNetlist.
From Coq Require Extraction.
From Coq Require Import extraction.ExtrOcamlBasic.
From Coq Require Import extraction.ExtrOcamlString.
From Coq Require Import extraction.ExtrOcamlZInt.
From Coq Require Import BinInt.

Extraction Language OCaml.

Extract Inlined Constant List.flat_map => "List.concat_map".

Separate Extraction VerilogToNetlist.transfer_module.
Extraction Library Verilog.
Extraction Library Netlist.
