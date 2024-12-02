From Coq Require Import BinNat BinPos.
From Coq Require Import List.
From Coq Require Import Psatz.

From SMTCoq Require Import BVList.

From Equations Require Import Equations.

Import SigTNotations.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope positive_scope.

Module BV.
  Include BITVECTOR_LIST.
  Notation t := bitvector.
  Definition some_bitvector := {n : _ & bitvector n}.
  Definition is_zero {n} (a : bitvector n) :=
    bv_eq a (zeros n).

  Equations of_pos_full (value : positive) : some_bitvector := {
    | xH => (_ ; #b|1|)
    | (p~1) => let '( _ ; head ) := of_pos_full p in (_ ; bv_concat head #b|1|)
    | (p~0) => let '( _ ; head ) := of_pos_full p in (_ ; bv_concat head #b|0|)
  }.

  Equations of_N_full (value : N) : some_bitvector := {
    | N0 => (_ ; #b|0|)
    | Npos p => of_pos_full p
  }.

  Definition of_pos_fixed (width : N) (value : positive) : bitvector width :=
    let '(width_full ; value) := of_pos_full value in
    bv_extr 0 width value.

  Definition of_N_fixed (width : N) (value : N) : bitvector width :=
    let '(width_full ; value) := of_N_full value in
    bv_extr 0 width value.

  Fixpoint to_positive (bs : list bool) : positive :=
    match bs with
    | [] => xH (** wrong! *)
    | b :: bs =>
        if b
        then if negb (fold_left orb bs false)
             then xH
             else (to_positive bs)~1
        else (to_positive bs)~0
    end.

  Definition to_N {w} (val : bitvector w) : N :=
    if negb (fold_left orb (bits val) false)
    then N0
    else Npos (to_positive (bits val)).
End BV.
