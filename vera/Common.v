From Stdlib Require Import BinIntDef.
From Stdlib Require Import BinNat.
From Stdlib Require Import BinNums.
From Stdlib Require Import FMapPositive.
From Stdlib Require Import FMaps.
From Stdlib Require Import FSets.
From Stdlib Require Import List.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import ZArith.
From Stdlib Require Import Classical.

From ExtLib Require Import Programming.Show.
From ExtLib Require Import Structures.Maps.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Functor.
(* Just for instances *)
From ExtLib Require Data.Monads.OptionMonad.
From ExtLib Require Data.List.
Import ApplicativeNotation.
Import FunctorNotation.

From Equations Require Import Equations.
From Stdlib Require Import Psatz.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import NArith.

From vera Require Import Tactics.
From vera Require Import Decidable.

Import ListNotations.
Import SigTNotations.

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

Definition opt_def {A} (v : A) (o : option A) : A :=
  match o with
  | Some x => x
  | None => v
  end
.

Definition opt_prop {A} (p : A -> Prop) (o : option A) :=
  match o with
  | Some x => p x
  | None => False
  end.

Instance dec_opt_prop {A P} {o : option A} `{(forall x, DecProp (P x))} : DecProp ( opt_prop P o ).
Proof. destruct o; crush. Qed.

Equations map_opt {A B} (f : A -> option B) (lst : list A) : list B :=
  map_opt f [] := [];
  map_opt f (x :: xs) with f x := {
    | None => map_opt f xs
    | Some x' => x' :: map_opt f xs
  }
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

Lemma map_injective {A B} : forall (f : A -> B) (l1 l2 : list A),
    (forall x y, f x = f y -> x = y) ->
    map f l1 = map f l2 ->
    l1 = l2.
Proof.
  intros *. generalize dependent l1.
  induction l2; intros * Hinj Hmap.
  - simpl in *.
    eauto using map_eq_nil.
  - destruct l1; simpl in *; try discriminate.
    inv Hmap.
    f_equal.
    + eapply Hinj. assumption.
    + eapply IHl2; assumption.
Qed.

Lemma mapT_list_option_length {A B} (f : A -> option B) (l : list A) :
  forall (l' : list B), mapT f l = Some l' ->
                   List.length l = List.length l'.
Proof.
  induction l; intros; cbn in *; try solve_by_inverts 2%nat.
  autodestruct_eqn E. cbn. eauto.
Qed.

Equations map2 {A B C} : (A -> B -> C) -> list A -> list B -> list C :=
  map2 f (hd_a :: tl_a) (hd_b :: tl_b) := f hd_a hd_b :: map2 f tl_a tl_b;
  map2 f nil _ := nil;
  map2 f _ nil := nil.

Lemma map2_length {A B C} (f : A -> B -> C) l1 l2 : List.length (map2 f l1 l2) = min (List.length l1) (List.length l2).
Proof. funelim (map2 f l1 l2); simp map2; simpl; crush. Qed.

Definition N_sum : list N -> N :=
  fold_right N.add 0%N.

Definition disjoint {A} (l r : list A) : Prop :=
  Forall (fun x => ~ In x r) l.

Lemma disjoint_elim_l A (l r : list A) :
  Forall (fun x => ~ In x r) l ->
  disjoint l r.
Proof. trivial. Qed.

Lemma disjoint_elim_r A (l r : list A) :
  Forall (fun x => ~ In x l) r ->
  disjoint l r.
Proof. unfold disjoint. rewrite ! Forall_forall. crush. Qed.

Lemma disjoint_l_intro A (l r : list A) : forall x,
  disjoint l r ->
  In x l ->
  ~ In x r.
Proof. unfold disjoint. setoid_rewrite Forall_forall. firstorder. Qed.

Lemma disjoint_r_intro A (l r : list A) : forall x,
  disjoint l r ->
  In x r ->
  ~ In x l.
Proof. unfold disjoint. setoid_rewrite Forall_forall. firstorder. Qed.

Lemma disjoint_app_l {A} (l1 l2 l3 : list A):
  disjoint (l1 ++ l2) l3 ->
  disjoint l1 l3.
Proof.
  unfold disjoint.
  rewrite ! List.Forall_app.
  crush.
Qed.

Lemma disjoint_app_r {A} (l1 l2 l3 : list A):
  disjoint (l1 ++ l2) l3 ->
  disjoint l2 l3.
Proof.
  unfold disjoint.
  rewrite ! List.Forall_app.
  crush.
Qed.

Lemma disjoint_app {A} (l1 l2 l3 : list A):
  disjoint (l1 ++ l2) l3 ->
  disjoint l1 l3 /\ disjoint l2 l3.
Proof.
  unfold disjoint.
  rewrite ! List.Forall_app.
  crush.
Qed.

Lemma disjoint_sym {A} (l1 l2 : list A):
  disjoint l1 l2 ->
  disjoint l2 l1.
Proof.
  unfold disjoint.
  rewrite ! List.Forall_forall.
  crush.
Qed.

Lemma disjoint_sym_iff {A} (l1 l2 : list A):
  disjoint l1 l2 <-> disjoint l2 l1.
Proof.
  unfold disjoint.
  rewrite ! List.Forall_forall.
  crush.
Qed.

(* Checking that typeclasses eauto can indeed figure out DecProp (disjoint l r) *)
Goal (forall (l r : list nat), DecProp (disjoint l r)). typeclasses eauto. Qed.

Definition list_subset {A} (sub sup : list A) : Prop :=
  Forall (fun x => In x sup) sub.

Ltac propertize_lists1 H :=
  match type of H with
  | list_subset _ _ =>
    unfold list_subset in H; rewrite Forall_forall in H
  end.

Ltac propertize_lists :=
  repeat match goal with
         | [ H : _ |- _ ] => propertize_lists1 H
         | [ |- list_subset _ _ ] => unfold list_subset; rewrite Forall_forall
         end.

Lemma list_subset_refl {A} (l : list A) :
  list_subset l l .
Proof. unfold list_subset. rewrite ! List.Forall_forall. crush. Qed.

Lemma list_subset_trans {A} (l1 l2 l3 : list A) :
  list_subset l1 l2 -> list_subset l2 l3 -> list_subset l1 l3.
Proof. unfold list_subset. rewrite ! List.Forall_forall. crush. Qed.

Add Parametric Relation A :
  (list A) list_subset
  reflexivity proved by list_subset_refl
  transitivity proved by list_subset_trans
  as list_subset_rel.

Global Instance Proper_list_subset_in A :
  Proper (eq ==> list_subset ==> Basics.impl) (@In A).
Proof.
  repeat intro. subst.
  unfold list_subset in *.
  rewrite List.Forall_forall in *.
  auto.
Qed.

Global Instance Proper_list_subset_disjoint A :
  Proper (list_subset --> list_subset --> Basics.impl) (@disjoint A).
Proof.
  intros ? ? Hsub1 ? ? Hsub2 Hin. subst.
  unfold Basics.flip, list_subset, disjoint in *.
  rewrite ! Forall_forall in *.
  crush.
Qed.

Lemma list_subset_app_r A (l1 l2 : list A) :
  list_subset l1 (l1 ++ l2).
Proof.
 unfold list_subset. rewrite ! Forall_forall. setoid_rewrite in_app_iff.
 crush.
Qed.

Lemma list_subset_app_l A (l1 l2 : list A) :
  list_subset l1 (l2 ++ l1).
Proof.
 unfold list_subset. rewrite ! Forall_forall. setoid_rewrite in_app_iff.
 crush.
Qed.

Lemma list_subset_app A (l1 l2 l3 : list A) :
  list_subset (l1 ++ l2) l3 <->
    (list_subset l1 l3 /\ list_subset l2 l3).
Proof.
 unfold list_subset. rewrite ! Forall_forall. setoid_rewrite in_app_iff.
 crush.
Qed.

Ltac unpack_list_subset :=
  repeat match goal with
  | [ H : list_subset (_ ++ _) _ |- _ ] =>
    apply list_subset_app in H; destruct H
  end.

Add Parametric Relation A :
  (list A) disjoint
  symmetry proved by disjoint_sym
  as disjoint_rel.

Add Parametric Morphism A : (@disjoint A)
  with signature (@Permutation A) ==> (@Permutation A) ==> iff
  as disjoint_permute.
Proof.
  unfold Proper, "==>", disjoint.
  setoid_rewrite List.Forall_forall.
  intros l1 l1' Hpermute1 l2 l2' Hpermute2.
  split; intros H x Hin1 Hin2.
  - eapply H.
    + eapply Permutation_in.
      * symmetry. eassumption.
      * eassumption.
    + eapply Permutation_in.
      * symmetry. eassumption.
      * eassumption.
  - eapply H.
    + eapply Permutation_in.
      * eassumption.
      * eassumption.
    + eapply Permutation_in.
      * eassumption.
      * eassumption.
Qed.

Add Parametric Morphism A : (@list_subset A)
  with signature (@Permutation A) ==> (@Permutation A) ==> iff
  as list_subset_permute.
Proof.
  unfold Proper, "==>", disjoint.
  setoid_rewrite List.Forall_forall.
  intros l1 l1' Hpermute1 l2 l2' Hpermute2.
  setoid_rewrite Hpermute1.
  setoid_rewrite Hpermute2.
  reflexivity.
Qed.

Add Parametric Morphism A : (@disjoint A)
  with signature list_subset --> list_subset --> Basics.impl
  as disjoint_subset.
Proof.
  unfold Basics.impl.
  unfold Proper, "==>", disjoint.
  setoid_rewrite List.Forall_forall.
  crush.
Qed.

(* Checking that typeclasses eauto can indeed figure out DecProp (list_subset l r) *)

Goal (forall (sub sup : list nat), DecProp (list_subset sub sup)). typeclasses eauto. Qed.

Lemma removelast_cons_length {A} (a : A) (l : list A) :
  List.length (List.removelast (a :: l)) = List.length l.
Proof. induction l; crush. Qed.

Lemma map_removelast {A B} (f : A -> B) (l : list A) :
  List.map f (List.removelast l) = List.removelast (List.map f l).
Proof.
  induction l; simpl; [reflexivity|].
  destruct l; simpl in *; [reflexivity|].
  now rewrite IHl.
Qed.

Lemma Nat2N_inj_le : forall n m, (N.of_nat n <= N.of_nat m)%N <-> n <= m.
Proof. lia. Qed.

Lemma Nat2N_inj_lt : forall n m, (N.of_nat n < N.of_nat m)%N <-> n < m.
Proof. lia. Qed.

Lemma N2Nat_inj_le : forall n m, (N.to_nat n <= N.to_nat m) <-> (n <= m)%N.
Proof. lia. Qed.

Lemma N2Nat_inj_lt : forall n m, (N.to_nat n < N.to_nat m) <-> (n < m)%N.
Proof. lia. Qed.

Hint Rewrite <- Nat2N.inj_add Nat2N.inj_mul Nat2N.inj_sub Nat2N.inj_min Nat2N.inj_max : N_to_nat.
Hint Rewrite N2Nat.id Nat2N.id : N_to_nat.

Ltac N_to_nat :=
  repeat match goal with
         | [ x : N |- _ ] =>
	 let Heqx := fresh "Heq" in
	 let x_temp := fresh x in
	 remember (N.to_nat x) as x_temp eqn:Heqx;
	 apply (f_equal N.of_nat) in Heqx;
	 rewrite N2Nat.id in Heqx;
	 rewrite <- Heqx in *;
	 clear x Heqx;
	 rename x_temp into x
	 end;
  autorewrite with N_to_nat in *;
  repeat match goal with
         | [ H : (_ <= _)%N |- _ ] => apply Nat2N_inj_le in H
         | [ H : (_ < _)%N |- _ ] => apply Nat2N_inj_lt in H
         | [ |- (_ <= _)%N ] => apply N2Nat_inj_le
         | [ |- (_ < _)%N ] => apply N2Nat_inj_lt
	 | _ => progress ( autorewrite with N_to_nat in * )
  end.

Ltac destruct_mins := 
    repeat match goal with
           | [ |- context[N.min ?l ?r] ] =>
	     let Heqmin := fresh "Heqmin" in (
	       destruct (N.min_spec l r) as [[? Heqmin]|[? Heqmin]];
	       rewrite Heqmin in *;
	       clear Heqmin;
	       try lia
	     )
           | [ H : context[N.min ?l ?r] |- _ ] =>
	     let Heqmin := fresh "Heqmin" in (
	       destruct (N.min_spec l r) as [[? Heqmin]|[? Heqmin]];
	       rewrite Heqmin in *;
	       clear Heqmin;
	       try lia
	     )
           | [ |- context[Nat.min ?l ?r] ] =>
	     let Heqmin := fresh "Heqmin" in (
	       destruct (Nat.min_spec l r) as [[? Heqmin]|[? Heqmin]];
	       rewrite Heqmin in *;
	       clear Heqmin;
	       try lia
	     )
           | [ H : context[Nat.min ?l ?r] |- _ ] =>
	     let Heqmin := fresh "Heqmin" in (
	       destruct (Nat.min_spec l r) as [[? Heqmin]|[? Heqmin]];
	       rewrite Heqmin in *;
	       clear Heqmin;
	       try lia
	     )
	   end.

Hint Rewrite
  N.leb_le N.leb_gt
  Nat.leb_le Nat.leb_gt
  : kill_bools.

Ltac kill_bools := autorewrite with kill_bools in *.

Lemma NoDup_app_iff A (l1 l2 : list A) :
  NoDup (l1 ++ l2) <-> (NoDup l1 /\ NoDup l2 /\ disjoint l1 l2).
Proof.
  revert l2.
  induction l1; split; intros; repeat split.
  - constructor.
  - assumption.
  - constructor.
  - crush.
  - eapply NoDup_app_remove_r. eassumption.
  - eapply NoDup_app_remove_l. eassumption.
  - simpl in H. inv H.
    eapply IHl1 in H3. decompose record H3. clear H3.
    setoid_rewrite in_app_iff in H2.
    constructor; crush.
  - decompose record H. clear H.
    inv H0. inv H3. simpl. constructor.
    + rewrite in_app_iff. crush.
    + rewrite Forall_forall in H6.
      apply NoDup_app; eassumption.
Qed.

Lemma disjoint_app_iff {A} (l1 l2 l3 : list A):
  disjoint (l1 ++ l2) l3 <->
  disjoint l1 l3 /\ disjoint l2 l3.
Proof.
  unfold disjoint.
  rewrite ! Forall_app, ! Forall_forall.
  crush.
Qed.

Ltac disjoint_saturate :=
  repeat match goal with
         | [ H : disjoint (_ :: ?l1) ?l2 |- _ ] =>
	   inv H; fold (disjoint l1 l2) in *
         | [ H : disjoint ?l2 (_ :: ?l1) |- _ ] =>
	   symmetry in H;
	   inv H; fold (disjoint l1 l2) in *
         | [ H : disjoint (_ ++ _) _ |- _ ] =>
           rewrite ! disjoint_app_iff in H;
           decompose record H;
           clear H
         | [ H : disjoint _ (_ ++ _) |- _ ] =>
           symmetry in H;
           rewrite ! disjoint_app_iff in H;
           decompose record H;
           clear H
         | [ H : NoDup (_ ++ _) |- _ ] =>
           apply NoDup_app_iff in H;
           decompose record H;
           clear H
         | [ H : NoDup (_ :: _) |- _ ] =>
           inv H
         | [ H : NoDup [] |- _ ] =>
           clear H
         | [ H : Forall _ [] |- _ ] => clear H
         | [ H : ~ (In _ []) |- _ ] => clear H
         | [ H : ~ (In _ (_ ++ _)) |- _ ] => rewrite in_app_iff in H
         | [ H : ~ (In _ (_ :: _)) |- _ ] => apply not_in_cons in H; destruct H
         | [ H : ~ (_ \/ _) |- _ ] => apply not_or_and in H; destruct H
         end.

Definition opt_to_sum {E A} (e: E) (o : option A) : E + A :=
  match o with
  | None => inl e
  | Some a => inr a
  end.

Definition newline : string := String "010" EmptyString.

(* Debug tracing — computes to identity in proofs, extracts to Printf *)
Definition trace {A : Type} (_msg : string) (x : A) : A := x.
Arguments trace / _ _.

Definition traceShowId {A : Type} `{Show A} (prefix : string) (x : A) : A :=
  trace (prefix ++ to_string x) x.
Arguments traceShowId / _ _.
