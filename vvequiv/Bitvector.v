Require Import BinNat.
Require Import BinPos.
Require Import Psatz.
Require Import Structures.OrderedType.
Require Import Program.
Require Import Arith.

Module Bitvector.

  Record bv :=
    BV
      { value : N
      ; width : positive
      ; wf : (value < Npos (2 ^ width))%N
      }.

  Program Definition mkBV_check (v : N) (w : positive) :=
    if dec (v <? (Npos (2 ^ w)))%N
    then Some (BV v w _)
    else None.
  Next Obligation. apply N.ltb_lt. auto. Qed.

  Notation mkBV v w := (BV v w ltac:(lia)) (only parsing).

End Bitvector.
