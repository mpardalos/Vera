From vera Require SMT.
From vera Require Verilog.
From vera Require VerilogEquivalence.
From vera Require VerilogToSMT.
From vera Require Common.
From vera Require Bitvector.

From SMTCoq Require Import BVList.
From SMTCoqApi Require SMTLib.

From Coq Require Extraction.
From Coq Require Import BinNat.
From Coq Require Import extraction.ExtrOcamlBasic.
From Coq Require Import extraction.ExtrOcamlString.
From Coq Require Import extraction.ExtrOcamlZInt.
From Coq Require Import BinInt.
From Coq Require Import String.

Import SigTNotations.

Extraction Language OCaml.

Extract Inlined Constant List.flat_map => "List.concat_map".

Definition int_from_nat :=
  N.of_nat.
Definition int_to_nat :=
  N.to_nat.

Definition bits_from_int (w : N) (n : N) :=
  Bitvector.RawBV.of_N_fixed w n.

(** There is deliberately no bits_to_int. Bitvectors are unbounded where ints
are 3-bit. We provide bits_to_binary_string as an alternative for
pretty-printing *)

Definition bits_to_binary_string (v: RAWBITVECTOR_LIST.bitvector) : string :=
  Bitvector.RawBV.to_string (Bitvector.RawBV.of_bits v).

Extraction "Vera.ml"
  bits_from_int
  bits_to_binary_string
  int_from_nat
  int_to_nat
  VerilogEquivalence.equivalence_query
  Verilog.UntypedVerilog
  VerilogTypecheck.tc_vmodule
  Verilog.Verilog
  VerilogToSMT.expr_to_smt
  VerilogCanonicalize.canonicalize_verilog
  SMT.SMT
  (* Common.NameMap *)
  .
