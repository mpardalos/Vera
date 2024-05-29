Require Import BinNat.
Require Import BinPos.
Require Import Psatz.
Require Import Structures.OrderedType.
Require Import Program.
Require Import Arith.

From Equations Require Import Equations.

Module Bitvector.

  Local Open Scope N.

  (** Unsigned bitvectors *)
  Record bv :=
    BV
      { value : N
      ; width : positive
      ; wf : value < 2 ^ (Npos width)
      }.

  Program Definition mkBV_check (v : N) (w : positive) :=
    if dec (v <? (Npos (2 ^ w)))%N
    then Some (BV v w _)
    else None.
  Next Obligation. apply N.ltb_lt. auto. Qed.

  Notation mkBV v w := (BV v w ltac:(lia)) (only parsing).

  (** Add the bitvectors, adding a bit to the width to accomodate overflow *)
  Equations bv_add_extend (bv1 bv2 : bv) (width_match : (width bv1 = width bv2)) : bv :=
    bv_add_extend (BV v1 w1 wf1) (BV v2 w2 wf2) width_match := BV (v1 + v2) (w1 + 1) _.
  Next Obligation.
    assert ((v1 + v2) < 2 * (2 ^ Npos w2)) by lia.
    replace (2 * (2 ^ Npos w2))  with (2 ^ (1 + Npos w2)) in *.

    enough (N.pos (2 ^ w2) + N.pos (2 ^ w2) < N.pos (2 ^ (w2 + 1))) by lia.
    replace (N.pos (2 ^ w2) + N.pos (2 ^ w2)) with (2 * N.pos (2^w2)) by lia.
    replace (2 * N.pos (2^w2)) with (N.pos (2 ^ (w2 + 1))).



End Bitvector.
