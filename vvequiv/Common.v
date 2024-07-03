Require Import BinNat.
Require Import FMapPositive.
Require Import List.
Require Import FMaps.
From Equations Require Import Equations.

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
  Include FMapFacts.
  Import ListNotations.

  Fixpoint insert_all {A} (l : list (positive * A)) (m : t A) : t A :=
    match l with
    | nil => empty A
    | (k,v)::xs => add k v (insert_all xs m)
    end
  .

  Definition from_list {A} (l : list (positive * A)) : t A :=
    insert_all l (empty A)
  .

  Definition combine {A} (l r : t A) : t A :=
    insert_all (elements l) r
  .
End NameMap.

Module NameMapFacts := FMapFacts.Facts(NameMap).

Module StrMap := FMapList.Make(String_as_OT).

Equations opt_or : forall {A}, option A -> option A -> option A :=
  opt_or (Some x) _ := Some x;
  opt_or None o := o.

Equations opt_or_else : forall {A}, option A -> A -> A :=
  opt_or_else (Some x) _ := x;
  opt_or_else None o := o.
