Require Import BinNat.
Require Import ZArith.
Require Import BinNums.
Require Import BinIntDef.
Require Import FMapPositive.
Require Import List.
Require Import FMaps.
Require Import FSets.
From ExtLib Require Import Structures.Maps.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Functor.
Import ApplicativeNotation.
Import FunctorNotation.

From Equations Require Import Equations.
From Coq Require Import Psatz.
From Coq Require Import ssreflect.

Module CommonNotations.
  Notation "{! x }" := (@exist _ _ x _).
  Notation "{! x | p }" := (@exist _ _ x p).
End CommonNotations.

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

Definition opt_or {A} (l r : option A) : option A :=
  match l with
  | Some x => Some x
  | None => r
  end
.

Module MapExtras(M: FMapInterface.WS).
  Import ListNotations.

  Fixpoint insert_all {A} (l : list (M.key * A)) (m : M.t A) : M.t A :=
    match l with
    | nil => m
    | (k,v)::xs => M.add k v (insert_all xs m)
    end
  .

  Definition from_list {A} (l : list (M.key * A)) : M.t A :=
    insert_all l (M.empty A)
  .

  Definition combine {A} (l r : M.t A) : M.t A := M.map2 opt_or l r.

  Lemma gcombine {A} k (l r : M.t A) :
    M.find k (combine l r) = opt_or (M.find k l) (M.find k r)
  .
  Admitted.

  Definition union_both {A B} (l : M.t A) (r : M.t B)
    : M.t (option A * option B) :=
    M.map2
      (fun lv rv =>
         match lv, rv with
         | None, None => None
         | _, _ => Some (lv, rv)
         end)
      l r.
End MapExtras.

Module StrMap.
  Include FMapList.Make(String_as_OT).
  Include FMapFacts.Facts.
  Include MapExtras.
End StrMap.

Module StrSet.
 Module X' := OrdersAlt.Update_OT String_as_OT.
 Module MSet := MSetList.Make X'.
 Include FSetCompat.Backport_Sets String_as_OT MSet.
End StrSet.

Equations opt_or_else : forall {A}, option A -> A -> A :=
  opt_or_else (Some x) _ := x;
  opt_or_else None o := o.
