From vera Require VerilogSMT.
From vera Require Verilog.
From vera Require VerilogEquivalence.
From vera Require EquivalenceTop.
From vera Require VerilogToSMT.
From vera Require Common.
From vera Require Bitvector.
From vera Require AssignmentForwarding.
From vera Require VerilogSemantics.

From vera Require Import BVList.
From vera Require SMTLib.

From Stdlib Require Extraction.
From Stdlib Require Import BinNat.
From Stdlib Require Import extraction.ExtrOcamlBasic.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Stdlib Require Import extraction.ExtrOcamlZBigInt.
From Stdlib Require Import extraction.ExtrOcamlNatBigInt.
From Stdlib Require Import extraction.ExtrOcamlIntConv.
From Stdlib Require Import BinInt.
From Stdlib Require Import String.

Import SigTNotations.

Extraction Language OCaml.

(* The following assume that N,Z,nat are extracted to the same type *)
(* Map conversion functions to identity to avoid recursive of_succ_nat *)
Extract Inlined Constant N.of_nat => "(fun x -> x)".
Extract Inlined Constant N.to_nat => "(fun x -> x)".
Extract Inlined Constant Z.of_nat => "(fun x -> x)".
Extract Inlined Constant Z.to_nat => "(fun x -> x)".

(* If you use positive numbers directly *)
Extract Inlined Constant Pos.of_nat => "(fun x -> x)".
Extract Inlined Constant Pos.to_nat => "(fun x -> x)".

Extract Inlined Constant List.flat_map => "List.concat_map".

(* Debug tracing — override extraction to print *)
Extract Inlined Constant Common.trace =>
  "(fun msg x -> Printf.printf ""%s\n%!"" msg; x)".

Definition int_from_nat :=
  N.of_nat.
Definition int_to_nat :=
  N.to_nat.

Definition bits_from_int (w : N) (n : N) :=
  Bitvector.RawBV.of_N_fixed w n.

(** There is deliberately no bits_to_int. Bitvectors are unbounded where ints
are 63-bit. We provide bits_to_binary_string as an alternative for
pretty-printing *)

Definition bits_to_binary_string (v: RAWBITVECTOR_LIST.bitvector) : string :=
  Bitvector.RawBV.to_string (Bitvector.RawBV.of_bits v).

Extraction "Vera.ml"
  bits_from_int
  bits_to_binary_string
  int_from_nat
  int_to_nat
  VerilogEquivalence.equivalence_query
  EquivalenceTop.equivalence_query_general
  Verilog.Typecheck.tc_vmodule
  VerilogToSMT.expr_to_smt
  AssignmentForwarding.forward_assignments
  DropInternal.drop_internal
  VerilogSemantics.Sort.sort_module_items
  (* Common.NameMap *)
  .
