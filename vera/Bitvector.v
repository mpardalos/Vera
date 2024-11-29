From SMTCoq Require Import BVList.

Module BV.
  Include BITVECTOR_LIST.
  Notation t := bitvector.
  Definition some_bitvector := {n : _ & bitvector n}.
  Definition is_zero {n} (a : bitvector n) :=
    bv_eq a (zeros n).
End BV.
