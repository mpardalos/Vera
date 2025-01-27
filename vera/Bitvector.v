From Coq Require Import BinNat BinPos.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import String.

From SMTCoq Require Import BVList.

From Equations Require Import Equations.

Import SigTNotations.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope positive_scope.

Module BV.
  Include RAWBITVECTOR_LIST.
  Notation t := bitvector.
  (* Definition some_bitvector := {n : _ & bitvector n}. *)
  Definition is_zero (a : bitvector) :=
    bv_eq a (zeros (size a)).

  Equations of_pos_full (value : positive) : bitvector := {
    | xH => [true]
    | (p~1) => bv_concat (of_pos_full p) [true]
    | (p~0) => bv_concat (of_pos_full p) [false]
  }.

  Equations of_N_full (value : N) : bitvector := {
    | N0 => [false]
    | Npos p => of_pos_full p
  }.

  (** We use concat instead of bv_zextn because bv_zextn is broken! It adds
  zeros at the start instead of the end, effectively shifting the value *)
  (* TODO: Report issue with zextn *)
  Definition of_pos_fixed (width : N) (value : positive) : bitvector :=
    let bv := of_pos_full value in
    if (N.ltb (size bv) width)
    then bv_concat (zeros (width - size bv)) bv
    else bv_extr 0 width (size bv) bv.

  Definition of_N_fixed (width : N) (value : N) : bitvector :=
    let bv := of_N_full value in
    if (N.ltb (size bv) width)
    then bv_concat (zeros (width - size bv)) bv
    else bv_extr 0 width (size bv) bv.

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

  Definition to_N (val : bitvector) : N :=
    if negb (fold_left orb (bits val) false)
    then N0
    else Npos (to_positive (bits val)).

  Fixpoint to_string (val : bitvector) : string :=
    match val with
    | [] => ""
    | b::bs => to_string bs ++ (if b then "1" else "0")
    end.
End BV.
