Require BinPos.
Require Import Structures.Equalities.

Module Type Bitvector(Export D : DecidableType).
  Export D.
  Parameter t : Set.
  Parameter size : Set.

  Parameter length : t -> size.
  Parameter size_from_pos : BinPos.positive -> size.
  Coercion size_from_pos : BinPos.positive >-> size.
End Bitvector.

From nbits Require NBitsDef NBitsOp.
From mathcomp Require seq.

Module Decidable_bits <: DecidableType.
  Import NBitsDef.
  Definition t := bits.
  Definition eq: t -> t -> Prop. Admitted.
  Definition eq_equiv : Equivalence eq. Admitted.
  Definition eq_dec : forall x y, { eq x y } + { ~ (eq x y)}. Admitted.
End Decidable_bits.

Module Bitvector_bits <: Bitvector(Decidable_bits).
  Module D := Decidable_bits.
  Import NBitsDef.
  Definition t := bits.
  Definition size := nat.

  Definition length : t -> size := seq.size.
  Definition size_from_pos : BinPos.positive -> size := BinPos.nat_of_P.
End Bitvector_bits.
