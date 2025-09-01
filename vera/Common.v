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
(* Just for instances *)
From ExtLib Require Data.Monads.OptionMonad.
From ExtLib Require Data.List.
Import ApplicativeNotation.
Import FunctorNotation.

From Equations Require Import Equations.
From Coq Require Import Psatz.
From Coq Require Import ssreflect.
From Coq Require Import String.
From Coq Require Import Logic.ProofIrrelevance.
From Coq Require Import Arith.PeanoNat.

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

Module MkDepFunMap(Key: UsualDecidableTypeBoth).
  Import (notations) Key.

  Definition t A := forall (k : Key.t), option (A k).

  Definition empty {A} : t A := fun _ => None.

  Definition remove {A} (k: Key.t) (m: t A) : t A :=
    fun k' => match Key.eq_dec k k' with
           | left _ => None
           | right _ => m k'
           end.

  Definition insert {A} (k: Key.t) (v: A k) (m: t A) : t A :=
    fun k' => match Key.eq_dec k k' with
           | left e => match e with
                      | eq_refl => Some v
                      end
           | right _ => m k'
           end.

  Fixpoint of_list {A} (elems : list {k : Key.t & A k}) : t A :=
    match elems with
    | [] => fun _ => None
    | (k; v) :: tl => insert k v (of_list tl)
    end
  .

  Definition combine {A} (l r : t A) : t A :=
    fun k => match l k with
          | Some x => Some x
          | None => r k
          end.

  Definition map {A B} (f : forall {k}, A k -> B k) (m : t A) : t B :=
    fun k => match m k with
          | Some x => Some (f x)
          | None => None
          end.
End MkDepFunMap.

Module MkFunMap(Key: BooleanEqualityType').
  Import (notations) Key.

  Definition t A := Key.t -> option A.

  Definition empty {A} : t A := fun _ => None.

  Definition insert {A} (k: Key.t) (v: A) (m: t A) : t A :=
    fun k' => if k =? k' then Some v else m k'.

  Definition remove {A} (k: Key.t) (m: t A) : t A :=
    fun k' => if k =? k' then None else m k'.

  Fixpoint of_list {A} (elems : list (Key.t * A)) : t A :=
    match elems with
    | [] => fun _ => None
    | (k, v) :: tl => insert k v (of_list tl)
    end
  .

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
Module StringAsUDT := Make_UDTF(StringUsualBoolEq).
Module StrFunMap := MkFunMap(StringAsUDT).

Module NatAsUDT := Make_UDTF(Nat).
Module NatFunMap := MkFunMap(Nat).

Module PartialBijection(A: UsualDecidableType)(B: UsualDecidableType).
  Structure t :=
    MkPartialBijection {
      bij_apply :> A.t -> option B.t;
      bij_inverse : B.t -> option A.t;
      bij_wf : forall a b, bij_apply a = Some b <-> bij_inverse b = Some a
    }.

  Lemma extensional_equality (m1 m2 : t) :
    (forall a, m1 a = m2 a) ->
    (forall b, bij_inverse m1 b = bij_inverse m2 b) ->
    @eq t m1 m2.
  Proof.
    intros Ha Hb.
    apply functional_extensionality in Ha.
    apply functional_extensionality in Hb.
    destruct m1, m2; cbn in *.
    generalize dependent bij_wf0.
    generalize dependent bij_wf1.
    rewrite Ha. rewrite Hb.
    intros.
    f_equal.
    apply proof_irrelevance.
  Qed.

  Program Definition empty : t :=
    {|
      bij_apply _ := None;
      bij_inverse _ := None
    |}.

  Next Obligation. firstorder solve_by_invert. Qed.

  Fixpoint lookup_left (pairs : list (A.t * B.t)) (a : A.t) :=
    match pairs with
    | [] => None
    | ((a0, b0) :: tl) =>
        match A.eq_dec a a0 with
        | left _ => Some b0
        | right _ => lookup_left tl a
        end
    end.

  Lemma lookup_left_in pairs :
    forall a b, lookup_left pairs a = Some b -> In (a, b) pairs.
  Proof.
    induction pairs as [ | [a0 b0] tl ]; intros.
    - inv H.
    - simpl in *.
      destruct (A.eq_dec a a0).
      + left. inv H. reflexivity.
      + right. apply IHtl. apply H.
  Qed.

  Lemma lookup_left_some_iff p ps x y :
      lookup_left (p :: ps) x = Some y <->
        ((fst p = x /\ snd p = y) \/ (fst p <> x /\ lookup_left ps x = Some y)).
  Proof.
    simpl.
    destruct p as [a b].
    destruct (A.eq_dec x a); subst; simpl; split; intros.
    - inv H. eauto.
    - inv H; inv H0; congruence.
    - firstorder.
    - inv H; inv H0; congruence.
  Qed.

  Fixpoint lookup_right (pairs : list (A.t * B.t)) (b : B.t) :=
    match pairs with
    | [] => None
    | ((a0, b0) :: tl) =>
        match B.eq_dec b b0 with
        | left _ => Some a0
        | right _ => lookup_right tl b
        end
    end.

  Lemma lookup_right_in pairs :
    forall a b, lookup_right pairs b = Some a -> In (a, b) pairs.
  Proof.
    induction pairs as [ | [a0 b0] tl ]; intros.
    - inv H.
    - simpl in *.
      destruct (B.eq_dec b b0).
      + left. inv H. reflexivity.
      + right. apply IHtl. apply H.
  Qed.

  Program Definition insert
    (a : A.t) (b : B.t) (m : t)
    (not_a : bij_apply m a = None)
    (not_b : bij_inverse m b = None)
    :=
    {|
      bij_apply a':=
        match A.eq_dec a' a with
        | left _ => Some b
        | right _ => m a'
        end;
      bij_inverse b' :=
        match B.eq_dec b' b with
        | left _ => Some a
        | right _ => bij_inverse m b'
        end;
    |}.
  Next Obligation.
    destruct (A.eq_dec a0 a), (B.eq_dec b0 b); subst;
      firstorder (try apply_somewhere bij_wf; congruence).
  Qed.

  Lemma lookup_insert_in k v m prf1 prf2 :
    insert k v m prf1 prf2 k = Some v.
  Proof.
    simpl. destruct (A.eq_dec k k).
    - reflexivity.
    - contradiction.
  Qed.

  Lemma lookup_insert_out k v k' m prf1 prf2 :
    k <> k' ->
    insert k v m prf1 prf2 k' = m k'.
  Proof.
    simpl. intros H. destruct (A.eq_dec k' k).
    - subst. contradiction.
    - reflexivity.
  Qed.

  Program Definition from_pairs
    (pairs : list (A.t * B.t))
    (nodup_left : NoDup (List.map fst pairs))
    (nodup_right : NoDup (List.map snd pairs))
    : t :=
    {|
      bij_apply := lookup_left pairs;
      bij_inverse := lookup_right pairs;
    |}.
  Next Obligation.
    generalize dependent b.
    generalize dependent a.
    induction pairs as [ | [a0 b0] tl ]; intros.
    - simpl in *. split; discriminate.
    - simpl in *.
      inversion nodup_left as [ | ? ? left1 left2 ]; subst; clear nodup_left.
      inversion nodup_right as [ | ? ? right1 right2 ]; subst; clear nodup_right.
      specialize (IHtl left2 right2).
      destruct (A.eq_dec a a0); destruct (B.eq_dec b b0); subst.
      + split; reflexivity.
      + split.
        * congruence.
        * intros.
          exfalso.
          apply left1.
          apply IHtl in H.
          apply lookup_left_in in H.
          eapply in_map_iff.
          eexists. split; try eassumption; reflexivity.
      + split.
        * intros.
          exfalso.
          apply right1.
          apply lookup_left_in in H.
          eapply in_map_iff.
          eexists. split; try eassumption; reflexivity.
        * congruence.
      + eauto.
  Qed.

  Definition from_pairs_cons p ps : forall H1 H2 H3 H4 H5 H6,
    from_pairs (p :: ps) H1 H2 = insert (fst p) (snd p) (from_pairs ps H3 H4) H5 H6.
  Proof.
    destruct p as [hd_a hd_b].
    revert hd_a hd_b.
    induction ps; intros; apply extensional_equality.
    - intros a'. cbn.
      destruct (A.eq_dec _ _); eauto.
    - intros b'. cbn.
      destruct (B.eq_dec _ _); eauto.
    - cbn in *. intros a'.
      destruct (A.eq_dec a' _); eauto.
    - cbn in *. intros b'.
      destruct (B.eq_dec b' _); eauto.
  Qed.

  Program Definition combine
    (l r : t)
    (no_overlap : forall a b, bij_apply l a = Some b -> r a = None)
    (no_overlap_inverse : forall a b, bij_inverse l b = Some a -> bij_inverse r b = None)
    : t :=
    {|
      bij_apply a := match bij_apply l a with
                     | Some b => Some b
                     | None => bij_apply r a
                     end;
      bij_inverse b := match bij_inverse r b with
                       | Some a => Some a
                       | None => bij_inverse l b
                       end
    |}.
  Next Obligation.
    destruct (bij_apply l a) eqn:Ela;
      destruct (bij_inverse l b) eqn:Elb;
      destruct (bij_apply r a) eqn:Era;
      destruct (bij_inverse r b) eqn:Erb;
      split; intros H; inv H;
      (match goal with
       | [ H: _ |- _] => apply bij_wf in H; congruence
       | [ H: _ |- _] => apply no_overlap in H; congruence
       | [ H: _ |- _] => apply no_overlap_inverse in H; congruence
       end).
  Qed.
End PartialBijection.

Module StrNatBijection := PartialBijection(StringAsUDT)(NatAsUDT).

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

(* Just checking that typeclasses eauto can indeed figure out DecProp (disjoint l r) *)
Goal (forall (l r : list nat), DecProp (disjoint l r)). typeclasses eauto. Qed.

Definition list_subset {A} (sub sup : list A) : Prop :=
  Forall (fun x => In x sup) sub.

(* Same for subset *)
Goal (forall (sub sup : list nat), DecProp (list_subset sub sup)). typeclasses eauto. Qed.
