From vera Require SMT.
From vera Require Verilog.
From vera Require VerilogEquivalence.
From vera Require VerilogToSMT.
From vera Require Common.
From vera Require Bitvector.

From SMTCoq Require Import BVList.

From Coq Require Extraction.
From Coq Require Import BinNat.
From Coq Require Import extraction.ExtrOcamlBasic.
From Coq Require Import extraction.ExtrOcamlString.
From Coq Require Import extraction.ExtrOcamlZInt.
From Coq Require Import BinInt.

Import SigTNotations.

Extraction Language OCaml.

Extract Inlined Constant List.flat_map => "List.concat_map".

Definition int_from_nat :=
  N.of_nat.
Definition int_to_nat :=
  N.to_nat.

Definition bits_from_int (w : N) (n : N) :=
  Bitvector.BV.of_N_fixed w n.


Definition bits_to_int (v: RAWBITVECTOR_LIST.bitvector) :=
  Bitvector.BV.to_N (Bitvector.BV.of_bits v).
(* Definition bits_from_nat (n : nat) : Bitvector.BV.some_bitvector := int_to_nat (bits_to_int v). *)
(* Definition bits_to_nat {w} (v: Bitvector.BV.t w) := int_ *)

Extraction "Vera.ml"
  (* bits_from_nat *)
  (* bits_to_nat *)
  bits_from_int
  bits_to_int
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
