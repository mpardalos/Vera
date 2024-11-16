From vera Require Import Common.
From Coq Require Import List.
Import ListNotations.

From Equations Require Import Equations.

Module M(M: FMapInterface.WS).
  Module Extras := MapExtras(M).
  Module Facts := FMapFacts.Facts(M).

  Definition t A := list (M.t A).

  Definition empty (A : Type) : t A := [M.empty A].

  Equations lookup {A} : M.key -> t A -> option A :=
    lookup n [] := None;
    lookup n (m :: ms) :=
      match M.find n m with
      | None => lookup n ms
      | Some x => Some x
      end
  .

  Equations add {A} : M.key -> A -> t A -> t A :=
    add n v [] := [];
    add n v (m :: ms) := M.add n v m :: ms
  .

  Definition push {A} (env : t A) : t A :=
    M.empty A :: env
  .

  Equations pop {A} : t A -> option (M.t A) * t A :=
    pop (m :: ms) := (Some m, ms);
    pop [] := (None, [])
  .

  Equations flatten {A} : t A -> M.t A :=
    flatten [] := M.empty A;
    flatten (m::ms) := Extras.combine m (flatten ms)
  .

  Section Correct.
    Lemma lookup_push :
      forall A (E : t A) k,
        lookup k (push E) = lookup k E.
    Proof.
      intros.
      unfold push.
      simp lookup.
      rewrite Facts.empty_o.
      reflexivity.
    Qed.

    Lemma lookup_empty :
      forall A (E : t A) k,
        lookup k (empty A) = None.
    Proof.
      intros.
      unfold empty.
      simp lookup.
      rewrite Facts.empty_o.
      reflexivity.
    Qed.
  End Correct.
End M.
