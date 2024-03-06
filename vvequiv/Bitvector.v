Require Import BinNat.
Require Import BinPos.
Require Import Psatz.

Module Bitvector.

Record bv :=
  BV
    { value : N
    ; width : positive
    ; wf : (value < Npos (2 ^ width))%N
    }.

Notation mkBV v w := (BV v w ltac:(lia)) (only parsing).

End Bitvector.
