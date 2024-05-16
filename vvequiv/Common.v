Require Import BinNat.
Require Import FMapPositive.
Require Import List.

Variant port_direction := PortIn | PortOut.

Definition is_port_in dir :=
  match dir with
  | PortIn => true
  | _ => false
  end
.

Definition is_port_out dir :=
  match dir with
  | PortOut => true
  | _ => false
  end
.

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
