Require Import BinNat.
Require Import ZArith.
Require Import BinNums.
Require Import BinIntDef.
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
  Fixpoint insert_all {A} (l : list (name * A)) (m : NameMap.t A) : NameMap.t A :=
    match l with
    | nil => m
    | (k,v)::xs => NameMap.add k v (insert_all xs m)
    end
  .

  Definition from_list {A} (l : list (positive * A)) : NameMap.t A :=
    insert_all l (NameMap.empty A)
  .

  Definition combine {A} (l r : NameMap.t A) : NameMap.t A :=
    insert_all (NameMap.elements l) r
  .
  Definition opt_or {A} (l r : option A) : option A :=
    match l, r with
    | (Some x), _ => Some x
    | None, o => o
    end
  .

  (* Lemma gcombine {A} k (l r : NameMap.t A) : *)
  (*   NameMap.find k (combine l r) = opt_or (NameMap.find k l) (NameMap.find k r) *)
  (* . *)
  (* Proof. *)
  (*   unfold combine. *)
  (*   generalize dependent k. *)
  (*   generalize dependent r. *)
  (*   induction l using NameMapProperties.map_induction; intros. *)
  (*   - replace (NameMap.elements l) with (@nil (name * A)). *)
  (*     replace (NameMap.find k l) with (@None A). *)
  (*     reflexivity. *)
  (*     + symmetry. *)
  (*       apply NameMapFacts.not_find_in_iff. *)
  (*       unfold NameMap.Empty in *. *)
  (*       unfold NameMap.In in *. *)
  (*       intros [c contra]. *)
  (*       specialize (H k c). *)
  (*       contradiction. *)
  (*     + symmetry. *)
  (*       apply NameMapProperties.elements_Empty. *)
  (*       eauto. *)
  (*   - admit. *)
  (* Admitted. *)
End NameMap.

Module NameMapFacts := FMapFacts.Facts(NameMap).
Module StrMap := FMapList.Make(String_as_OT).

Equations opt_or_else : forall {A}, option A -> A -> A :=
  opt_or_else (Some x) _ := x;
  opt_or_else None o := o.
