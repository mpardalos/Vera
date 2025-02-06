Require Import BinNat.
Require Import ZArith.
Require Import BinNums.
Require Import BinIntDef.
Require Import FMapPositive.
Require Import List.
Require Import FMaps.
Require Import FSets.
Require Import Structures.Equalities.

From ExtLib Require Import Structures.Maps.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Functor.
Import ApplicativeNotation.
Import FunctorNotation.

From Equations Require Import Equations.
From Coq Require Import Psatz.
From Coq Require Import ssreflect.

Import ListNotations.

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

Fixpoint map_opt {A B} (f : A -> option B) (lst : list A) : list B :=
  match lst with
  | [] => []
  | (x :: xs) => match f x with
               | None => map_opt f xs
               | Some x' => x' :: map_opt f xs
               end
  end
.

Definition dupe {A} (x : A) := (x, x).

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

Module MkFunMap(Key: BooleanEqualityType').
  Import (notations) Key.

  Definition t A := Key.t -> option A.

  Definition empty {A} : t A := fun _ => None.

  Definition insert {A} (k: Key.t) (v: A) (m: t A) : t A :=
    fun k' => if k =? k' then Some v else m k'.

  Definition remove {A} (k: Key.t) (m: t A) : t A :=
    fun k' => if k =? k' then None else m k'.

  Definition of_list {A} (elems : list (Key.t * A)) : t A :=
    List.fold_left (fun acc '(k, v) => insert k v acc) elems empty.

  Definition combine {A} (l r : t A) : t A :=
    fun k => match l k with
          | Some x => Some x
          | None => r k
          end.

  Definition map {A B} (f : A -> B) (m : t A) : t B :=
    fun k => match m k with | Some x => Some (f x) | None => None end.
End MkFunMap.

Module StringUsualBoolEq <: UsualBoolEq.
  Import String.
  Definition t := String.string.
  Definition eq (s1 s2 : String.string) := s1 = s2.
  Definition eqb := String.eqb.
  Definition eqb_eq := String.eqb_eq.
End StringUsualBoolEq.
Module StringAsDT := Make_UDTF(StringUsualBoolEq).
Module StrFunMap := MkFunMap(StringAsDT).

Module NatFunMap := MkFunMap(Nat).
