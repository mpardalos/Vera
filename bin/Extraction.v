From vera Require SMT.
From vera Require Verilog.
From vera Require VerilogEquivalence.
From vera Require VerilogToSMT.
From vera Require Common.

From Coq Require Extraction.
From Coq Require Import BinNat.
From Coq Require Import extraction.ExtrOcamlBasic.
From Coq Require Import extraction.ExtrOcamlString.
From Coq Require Import extraction.ExtrOcamlZInt.
From Coq Require Import BinInt.

Extraction Language OCaml.

Extract Inlined Constant List.flat_map => "List.concat_map".

Definition int_from_nat := N.of_nat.
Definition int_to_nat := N.to_nat.

Definition bits_from_nat := NBitsDef.from_nat.
Definition bits_to_nat := NBitsDef.to_nat.
Definition bits_from_int sz n := NBitsDef.from_nat (int_to_nat sz) (int_to_nat n).
Definition bits_to_int b := int_from_nat (bits_to_nat b).

Extraction "Vera.ml"
  bits_from_nat
  bits_to_nat
  bits_from_int
  bits_to_int
  int_from_nat
  int_to_nat
  VerilogEquivalence.equivalence_query
  Verilog.Verilog
  VerilogTypecheck.tc_vmodule
  Verilog.TypedVerilog
  VerilogToSMT.expr_to_smt
  VerilogCanonicalize.canonicalize_verilog
  SMT.SMT
  Common.NameMap
  .
