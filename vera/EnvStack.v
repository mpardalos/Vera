From vera Require Import Common.
From Coq Require Import List.
Import ListNotations.

From Equations Require Import Equations.

Definition t A := list (NameMap.t A).

Definition empty (A : Type) : t A := [NameMap.empty A].

Equations lookup {A} : NameMap.key -> t A -> option A :=
  lookup n [] := None;
  lookup n (m :: ms) :=
    match NameMap.find n m with
    | None => lookup n ms
    | Some x => Some x
    end
.

Equations add {A} : NameMap.key -> A -> t A -> t A :=
  add n v [] := [];
  add n v (m :: ms) := NameMap.add n v m :: ms
.

Definition push {A} (env : t A) : t A :=
  NameMap.empty A :: env
.

Equations pop {A} : t A -> option (NameMap.t A) * t A :=
  pop (m :: ms) := (Some m, ms);
  pop [] := (None, [])
.

Equations flatten {A} : t A -> NameMap.t A :=
  flatten [] := NameMap.empty A;
  flatten (m::ms) := NameMap.combine m (flatten ms)
.

Section Correct.
  Lemma lookup_push :
    forall A (E : t A) k,
    lookup k (push E) = lookup k E.
  Proof.
    intros.
    unfold push.
    simp lookup.
    rewrite NameMapFacts.empty_o.
    reflexivity.
  Qed.

  Lemma lookup_empty :
    forall A (E : t A) k,
    lookup k (empty A) = None.
  Proof.
    intros.
    unfold empty.
    simp lookup.
    rewrite NameMapFacts.empty_o.
    reflexivity.
  Qed.
End Correct.
