From SMTCoq Require Import BVList.

Module BV.
  Include BITVECTOR_LIST.
  Notation t := bitvector.
  Definition some_bitvector := {n : _ & bitvector n}.
End BV.
