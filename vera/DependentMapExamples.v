From Stdlib Require Import List Bool Lia Structures.OrdersEx.
From vera Require Import DependentMap DependentMapProperties.
Import ListNotations.

Module M := DependentMap.Make(OrdersEx.Nat_as_OT).

(** Key zero stores a boolean; every other key stores a natural number. *)
Definition value (k : nat) : Type :=
  match k with 0 => bool | S _ => nat end.

Definition sample : M.t value :=
  M.add 2 7 (M.add 0 true (M.empty value)).

Fail Definition wrong_value := M.add 0 5 (M.empty value).

Example lookup_and_membership :
  M.find 0 sample = Some true /\ M.find 2 sample = Some 7 /\
  M.find 1 sample = None /\ M.mem 0 sample = true /\
  M.mem 1 sample = false /\ M.is_empty (M.empty value) = true.
Proof. vm_compute; repeat split; reflexivity. Qed.

Example replace_and_remove :
  M.find 0 (M.add 0 false sample) = Some false /\
  M.cardinal (M.add 0 false sample) = 2 /\
  M.find 0 (M.remove 0 sample) = None /\
  M.find 2 (M.remove 0 sample) = Some 7.
Proof. vm_compute; repeat split; reflexivity. Qed.

Definition as_nat (k : nat) : value k -> nat :=
  match k as k return value k -> nat with
  | 0 => fun b => if b then 1 else 0
  | S _ => fun n => n
  end.

Definition mapped : M.t (fun _ => nat) := M.map as_nat sample.

Example map_and_fold :
  M.find 0 mapped = Some 1 /\ M.find 2 mapped = Some 7 /\
  M.fold (fun k v acc => as_nat k v + acc) sample 0 = 8.
Proof. vm_compute; repeat split; reflexivity. Qed.

Example enumeration :
  M.elements sample = [existT value 0 true; existT value 2 7] /\
  M.cardinal sample = 2.
Proof. vm_compute; repeat split; reflexivity. Qed.

Definition same_value (k : nat) : value k -> value k -> bool :=
  match k as k return value k -> value k -> bool with
  | 0 => Bool.eqb
  | S _ => Nat.eqb
  end.

Example equality :
  M.equal same_value sample (M.add 0 true (M.add 2 7 (M.empty value))) = true /\
  M.equal same_value sample (M.add 0 false sample) = false.
Proof. vm_compute; repeat split; reflexivity. Qed.

Definition combine (k : nat) (left right : option (value k)) : option nat :=
  match left, right with
  | Some l, Some r => Some (as_nat k l + as_nat k r)
  | Some v, None | None, Some v => Some (as_nat k v)
  | None, None => Some 99
  end.

Definition merged : M.t (fun _ => nat) :=
  M.map2 combine sample (M.add 3 9 (M.add 0 true (M.empty value))).

Example merge_overlap_and_unilateral_bindings :
  M.find 0 merged = Some 2 /\ M.find 2 merged = Some 7 /\
  M.find 3 merged = Some 9 /\ M.cardinal merged = 3.
Proof. vm_compute; repeat split; reflexivity. Qed.

Example merge_disjoint :
  M.elements (M.map2 combine (M.add 0 true (M.empty value))
    (M.add 2 7 (M.empty value))) =
  [existT (fun _ => nat) 0 1; existT (fun _ => nat) 2 7].
Proof. vm_compute; reflexivity. Qed.

(** Like FMap.map2, the callback is ignored outside the union of domains,
    even though [combine k None None] returns [Some 99]. *)
Example merge_absent_bindings :
  M.find 1 merged = None /\
  M.is_empty (M.map2 combine (M.empty value) (M.empty value)) = true /\
  M.find 2 (M.map2 combine sample (M.empty value)) = Some 7.
Proof. vm_compute; repeat split; reflexivity. Qed.

Example merge_drop_bindings :
  M.is_empty (M.map2 (C := value) (fun _ _ _ => None) sample sample) = true.
Proof. vm_compute; reflexivity. Qed.

Module P := DepMapProperties(M).
Module StringProperties := DepMapProperties(StringDepMap).
Module NProperties := DepMapProperties(NDepMap).
Module PositiveProperties := DepMapProperties(PositiveDepMap).
Import P.F.

(** Rewriting under dependent operations uses extensional map equality. *)
Example rewrite_equal_maps (m n : M.t value) :
  M.Equal m n -> M.find 0 (M.add 2 9 m) = M.find 0 (M.add 2 9 n).
Proof. intros Heq. now setoid_rewrite Heq. Qed.

Example list_roundtrip (m : M.t value) : M.Equal (P.of_list (P.to_list m)) m.
Proof. apply P.of_list_3. Qed.

Example duplicate_list_keys :
  M.find 0 (P.of_list [existT value 0 false; existT value 0 true]) = Some false.
Proof. vm_compute; reflexivity. Qed.

(** A fold invariant can relate two different accumulators. *)
Example fold_counts_twice (m : M.t value) :
  M.fold (fun _ _ acc => 2 + acc) m 0 = 2 * M.cardinal m.
Proof.
  rewrite P.cardinal_fold.
  apply P.fold_rel with (R := fun doubled count => doubled = 2 * count).
  - reflexivity.
  - intros k v doubled count Hmap Heq. cbn. lia.
Qed.

Definition large_value k (v : value k) := Nat.leb 2 (as_nat k v).

Example filter_and_quantifiers :
  M.elements (P.filter large_value sample) = [existT value 2 7] /\
  P.for_all large_value sample = false /\ P.exists_ large_value sample = true /\
  P.for_all large_value (M.empty value) = true /\
  P.exists_ large_value (M.empty value) = false.
Proof. vm_compute; repeat split; reflexivity. Qed.

Example partition_values :
  M.elements (fst (P.partition large_value sample)) = [existT value 2 7] /\
  M.elements (snd (P.partition large_value sample)) = [existT value 0 true].
Proof. vm_compute; repeat split; reflexivity. Qed.

Definition updates := M.add 0 false (M.add 3 9 (M.empty value)).

Example update_restrict_diff :
  M.find 0 (P.update sample updates) = Some false /\
  M.find 2 (P.update sample updates) = Some 7 /\
  M.find 3 (P.update sample updates) = Some 9 /\
  M.elements (P.restrict sample updates) = [existT value 0 true] /\
  M.elements (P.diff sample updates) = [existT value 2 7].
Proof. vm_compute; repeat split; reflexivity. Qed.
