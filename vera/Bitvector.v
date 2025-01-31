From Coq Require Import BinNat BinPos.
From Coq Require Import List.
From Coq Require Import Nat.
From Coq Require Import Psatz.
From Coq Require Import String.
From Coq Require Import Logic.Decidable.

From SMTCoq Require Import BVList.

From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Data.Monads.OptionMonad.
From ExtLib Require Import Data.List.


From Equations Require Import Equations.

Import SigTNotations.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope bv_scope.

Module BV.
  Include RAWBITVECTOR_LIST.
  Notation t := bitvector.
  (* Definition some_bitvector := {n : _ & bitvector n}. *)
  Definition is_zero (a : bitvector) :=
    bv_eq a (zeros (size a)).

  Equations of_pos_full (value : positive) : bitvector := {
    | xH => [true]
    | (p~1)%positive => bv_concat (of_pos_full p) [true]
    | (p~0)%positive => bv_concat (of_pos_full p) [false]
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

Module XBV.
  Variant bit := X | I | O.

  Definition t := list bit.

  Definition bit_to_bool b :=
    match b with
    | I => Some true
    | O => Some false
    | X => None
    end
  .

  Fixpoint exes (count : nat) : t :=
    match count with
    | 0%nat => []
    | S n => X :: exes n
    end
  .

  Definition bit_eq_dec (b1 b2: bit) : { b1 = b2 } + { b1 <> b2 }.
  Proof. unfold decidable. decide equality. Qed.

  Definition from_bv (bv : BV.t) : t :=
    List.map (fun (b: bool) => if b then I else O) bv
  .

  Definition to_bv (bv : t) : option BV.t :=
    mapT bit_to_bool bv
  .

  Definition x_binop f l r :=
    match to_bv l, to_bv r with
    | Some l_bv, Some r_bv => from_bv (f l_bv r_bv)
    | _, _ =>
        if (length l) =? (length r)
        then exes (length l)
        else nil
    end
  .
End XBV.
