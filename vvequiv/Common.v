Require Import BinNat.
Require Import FMapPositive.
Require Import List.

Variant port_direction := PortIn | PortOut.

Definition name := positive.

Module NameMap.
  Include PositiveMap.
  Import ListNotations.

  Fixpoint from_list {A} (l : list (positive * A)) : t A :=
    match l with
    | nil => empty A
    | (k,v)::xs => add k v (from_list xs)
    end
  .
End NameMap.
