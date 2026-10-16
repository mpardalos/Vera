From Stdlib Require Import List Bool Morphisms RelationClasses.
From Stdlib Require Import Logic.Eqdep_dec Sorting.SetoidList.
From vera Require Import DependentMap.

(** Dependent counterparts of [FMapFacts.Facts] and [FMapFacts.Properties].

    [Module P := DepMapProperties(NDepMap).] provides properties of an
    existing dependent map. Its nested [P.F] module supplies lookup facts
    and rewriting instances. Value families replace the ordinary [elt]
    parameter, and association lists contain dependent pairs.
*)
(** Lookup facts and rewriting support, following [FMapFacts.Facts].
    Facts involving values keep their key fixed, or explicitly transport the
    value across an equality of keys. *)
Module DepMapFacts (Import M : DependentMap.DepMap).
  Notation eq_dec := E.eq_dec.
  Definition eqb x y := if E.eq_dec x y then true else false.

  Lemma eq_bool_alt b b' : b = b' <-> (b = true <-> b' = true).
  Proof. destruct b, b'; intuition. Qed.

  Lemma eq_option_alt {B} (o o' : option B) :
    o = o' <-> (forall v, o = Some v <-> o' = Some v).
  Proof.
    split; [intros ->; reflexivity|].
    destruct o as [v|], o' as [v'|]; intros H; try reflexivity.
    - symmetry. apply (proj1 (H v)); reflexivity.
    - specialize (H v). intuition discriminate.
    - specialize (H v'). intuition discriminate.
  Qed.

  Lemma MapsTo_fun {A} (m : t A) x (e e' : A x) :
    MapsTo x e m -> MapsTo x e' m -> e = e'.
  Proof. rewrite !M.find_mapsto_iff. congruence. Qed.

  Lemma In_iff {A} (m : t A) x y : x = y -> (In x m <-> In y m).
  Proof. intros ->; reflexivity. Qed.

  Lemma MapsTo_iff {A} (m : t A) x y (e : A x) (Hxy : x = y) :
    MapsTo x e m <-> MapsTo y (eq_rect x A e y Hxy) m.
  Proof. destruct Hxy; reflexivity. Qed.

  Lemma mem_in_iff {A} (m : t A) x : In x m <-> mem x m = true.
  Proof. apply M.mem_in_iff. Qed.

  Lemma not_mem_in_iff {A} (m : t A) x : ~ In x m <-> mem x m = false.
  Proof. rewrite mem_in_iff. destruct (mem x m); intuition discriminate. Qed.

  Lemma In_dec {A} (m : t A) x : {In x m} + {~ In x m}.
  Proof. destruct (mem x m) eqn:Hmem; [left|right];
    [apply mem_in_iff|apply not_mem_in_iff]; assumption. Defined.

  Lemma find_mapsto_iff {A} (m : t A) x e : MapsTo x e m <-> find x m = Some e.
  Proof. apply M.find_mapsto_iff. Qed.

  Lemma not_find_in_iff {A} (m : t A) x : ~ In x m <-> find x m = None.
  Proof.
    unfold In. setoid_rewrite find_mapsto_iff.
    destruct (find x m) as [v|]; split; intros H; try reflexivity.
    - exfalso. apply H. now exists v.
    - discriminate.
    - intros [v Hv]; discriminate.
  Qed.

  Lemma in_find_iff {A} (m : t A) x : In x m <-> find x m <> None.
  Proof.
    unfold In. setoid_rewrite find_mapsto_iff.
    destruct (find x m) as [v|]; split; intros H; try discriminate.
    - now exists v.
    - destruct H as [v Hv]; discriminate.
    - contradiction.
  Qed.

  Lemma equal_iff {A} (m n : t A) cmp : Equivb cmp m n <-> equal cmp m n = true.
  Proof. apply M.equal_iff. Qed.

  Lemma empty_mapsto_iff {A} x (e : A x) : MapsTo x e (empty A) <-> False.
  Proof. rewrite find_mapsto_iff, M.empty_o. intuition discriminate. Qed.

  Lemma empty_in_iff {A} x : In x (empty A) <-> False.
  Proof. rewrite in_find_iff, M.empty_o. intuition. Qed.

  Lemma is_empty_iff {A} (m : t A) : Empty m <-> is_empty m = true.
  Proof. apply M.is_empty_iff. Qed.

  Lemma add_mapsto_iff {A} (m : t A) x y (e : A x) (e' : A y) :
    MapsTo y e' (add x e m) <->
    existT A x e = existT A y e' \/ (x <> y /\ MapsTo y e' m).
  Proof.
    destruct (E.eq_dec x y) as [Hxy|Hxy].
    - subst y. rewrite find_mapsto_iff, M.add_eq_o.
      split.
      + intros Heq; injection Heq as Heq; subst e'; now left.
      + intros [Heq|[Hneq _]]; [|contradiction].
        apply (inj_pair2_eq_dec key E.eq_dec) in Heq. now subst e'.
    - rewrite !find_mapsto_iff, M.add_neq_o by assumption.
      split; [tauto|]. intros [Heq|[_ Hmap]]; [|assumption].
      apply (f_equal (@projT1 key A)) in Heq. contradiction.
  Qed.

  Lemma add_in_iff {A} (m : t A) x y (e : A x) :
    In y (add x e m) <-> x = y \/ In y m.
  Proof.
    destruct (E.eq_dec x y) as [->|Hxy].
    - split; [auto|]. intros _. exists e. apply M.add_1.
    - rewrite !in_find_iff, M.add_neq_o by assumption. tauto.
  Qed.

  Lemma add_neq_mapsto_iff {A} (m : t A) x y e e' :
    x <> y -> (MapsTo y e' (add x e m) <-> MapsTo y e' m).
  Proof. intros Hxy. rewrite !find_mapsto_iff, M.add_neq_o by assumption. reflexivity. Qed.

  Lemma add_neq_in_iff {A} (m : t A) x y e :
    x <> y -> (In y (add x e m) <-> In y m).
  Proof. rewrite add_in_iff. tauto. Qed.

  Lemma remove_mapsto_iff {A} (m : t A) x y e :
    MapsTo y e (remove x m) <-> x <> y /\ MapsTo y e m.
  Proof.
    destruct (E.eq_dec x y) as [->|Hxy]; rewrite !find_mapsto_iff.
    - rewrite M.remove_eq_o. intuition discriminate.
    - rewrite M.remove_neq_o by assumption. tauto.
  Qed.

  Lemma remove_in_iff {A} (m : t A) x y :
    In y (remove x m) <-> x <> y /\ In y m.
  Proof.
    destruct (E.eq_dec x y) as [->|Hxy]; rewrite !in_find_iff.
    - rewrite M.remove_eq_o. intuition.
    - rewrite M.remove_neq_o by assumption. tauto.
  Qed.

  Lemma remove_neq_mapsto_iff {A} (m : t A) x y e :
    x <> y -> (MapsTo y e (remove x m) <-> MapsTo y e m).
  Proof. rewrite remove_mapsto_iff. tauto. Qed.

  Lemma remove_neq_in_iff {A} (m : t A) x y :
    x <> y -> (In y (remove x m) <-> In y m).
  Proof. rewrite remove_in_iff. tauto. Qed.

  Lemma elements_mapsto_iff {A} (m : t A) x e :
    MapsTo x e m <-> List.In (existT A x e) (elements m).
  Proof. apply M.elements_iff. Qed.

  Lemma elements_in_iff {A} (m : t A) x :
    In x m <-> exists e, List.In (existT A x e) (elements m).
  Proof. unfold In. now setoid_rewrite elements_mapsto_iff. Qed.

  Lemma map_mapsto_iff {A B} (m : t A) x b (f : forall k, A k -> B k) :
    MapsTo x b (map f m) <-> exists a, b = f x a /\ MapsTo x a m.
  Proof.
    rewrite find_mapsto_iff, M.map_o. setoid_rewrite find_mapsto_iff.
    destruct (find x m) as [v|]; cbn; split.
    - intros Heq; injection Heq as Heq. exists v; auto.
    - intros [a [-> Heq]]. now injection Heq as ->.
    - discriminate.
    - intros [a [_ Heq]]; discriminate.
  Qed.

  Lemma map_in_iff {A B} (m : t A) x (f : forall k, A k -> B k) :
    In x (map f m) <-> In x m.
  Proof.
    rewrite !in_find_iff, M.map_o. destruct (find x m); cbn; intuition discriminate.
  Qed.

  Definition mapi_in_iff := @map_in_iff.
  Definition mapi_mapsto_iff := @map_mapsto_iff.
  Lemma mapi_inv {A B} (m : t A) x b (f : forall k, A k -> B k) :
    MapsTo x b (mapi f m) -> exists a, b = f x a /\ MapsTo x a m.
  Proof. apply map_mapsto_iff. Qed.
  Definition mapi_1bis := @M.map_1.

  Ltac map_iff := repeat (progress (
    rewrite add_mapsto_iff || rewrite add_in_iff ||
    rewrite remove_mapsto_iff || rewrite remove_in_iff ||
    rewrite empty_mapsto_iff || rewrite empty_in_iff ||
    rewrite map_mapsto_iff || rewrite map_in_iff || rewrite mapi_in_iff)).

  Lemma mem_find_b {A} (m : t A) x :
    mem x m = match find x m with Some _ => true | None => false end.
  Proof.
    destruct (find x m) as [v|] eqn:Hfind.
    - apply mem_in_iff. exists v. now apply M.find_2.
    - apply not_mem_in_iff, not_find_in_iff; assumption.
  Qed.

  Lemma mem_b {A} (m : t A) x y : x = y -> mem x m = mem y m.
  Proof. intros ->; reflexivity. Qed.

  Lemma find_o {A} (m : t A) x y (Hxy : x = y) :
    option_map (fun e => eq_rect x A e y Hxy) (find x m) = find y m.
  Proof. destruct Hxy. destruct (find x m); reflexivity. Qed.

  Definition empty_o := @M.empty_o.
  Lemma empty_a {A} x : mem x (empty A) = false.
  Proof. rewrite mem_find_b, empty_o; reflexivity. Qed.

  Lemma add_eq_o {A} (m : t A) x y e (Hxy : x = y) :
    find y (add x e m) = Some (eq_rect x A e y Hxy).
  Proof. destruct Hxy. apply M.add_eq_o. Qed.
  Lemma add_neq_o {A} (m : t A) x y e :
    x <> y -> find y (add x e m) = find y m.
  Proof. apply M.add_neq_o. Qed.
  Lemma add_o {A} (m : t A) x y e :
    find y (add x e m) =
      match E.eq_dec x y with
      | left Hxy => Some (eq_rect x A e y Hxy)
      | right _ => find y m
      end.
  Proof. destruct (E.eq_dec x y); [apply add_eq_o|apply add_neq_o]; assumption. Qed.

  Lemma add_eq_b {A} (m : t A) x y e : x = y -> mem y (add x e m) = true.
  Proof. intros ->. apply mem_in_iff. exists e; apply M.add_1. Qed.
  Lemma add_neq_b {A} (m : t A) x y e :
    x <> y -> mem y (add x e m) = mem y m.
  Proof. intros Hxy. rewrite !mem_find_b, add_neq_o by assumption. reflexivity. Qed.
  Lemma add_b {A} (m : t A) x y e : mem y (add x e m) = eqb x y || mem y m.
  Proof. unfold eqb. destruct (E.eq_dec x y); cbn;
    [apply add_eq_b|apply add_neq_b]; assumption. Qed.

  Lemma remove_eq_o {A} (m : t A) x y : x = y -> find y (remove x m) = None.
  Proof. intros ->; apply M.remove_eq_o. Qed.
  Lemma remove_neq_o {A} (m : t A) x y : x <> y -> find y (remove x m) = find y m.
  Proof. apply M.remove_neq_o. Qed.
  Lemma remove_o {A} (m : t A) x y :
    find y (remove x m) = if E.eq_dec x y then None else find y m.
  Proof. destruct (E.eq_dec x y); [apply remove_eq_o|apply remove_neq_o]; assumption. Qed.
  Lemma remove_eq_b {A} (m : t A) x y : x = y -> mem y (remove x m) = false.
  Proof. intros ->. rewrite mem_find_b, M.remove_eq_o; reflexivity. Qed.
  Lemma remove_neq_b {A} (m : t A) x y : x <> y -> mem y (remove x m) = mem y m.
  Proof. intros Hxy. rewrite !mem_find_b, remove_neq_o by assumption. reflexivity. Qed.
  Lemma remove_b {A} (m : t A) x y : mem y (remove x m) = negb (eqb x y) && mem y m.
  Proof. unfold eqb. destruct (E.eq_dec x y); cbn;
    [apply remove_eq_b|apply remove_neq_b]; assumption. Qed.

  Lemma map_o {A B} (m : t A) x (f : forall k, A k -> B k) :
    find x (map f m) = option_map (f x) (find x m).
  Proof. apply M.map_o. Qed.
  Lemma map_b {A B} (m : t A) x (f : forall k, A k -> B k) :
    mem x (map f m) = mem x m.
  Proof. rewrite !mem_find_b, map_o. destruct (find x m); reflexivity. Qed.
  Definition mapi_o := @map_o.
  Definition mapi_b := @map_b.
  Lemma map2_1bis {A B C} (m : t A) (n : t B) x
    (f : forall k, option (A k) -> option (B k) -> option (C k)) :
    f x None None = None -> find x (map2 f m n) = f x (find x m) (find x n).
  Proof. apply M.map2_1bis. Qed.

  (** Lookup in a list of dependent entries, retaining the first binding
      when a key occurs more than once. *)
  Fixpoint findA {A} (k : key) (entries : list (sigT A)) : option (A k) :=
    match entries with
    | nil => None
    | existT _ j v :: rest =>
        match E.eq_dec j k with
        | left Heq => Some (eq_rect j A v k Heq)
        | right _ => findA k rest
        end
    end.

  Lemma findA_NoDup {A} (entries : list (sigT A)) k (v : A k) :
    NoDup (List.map (@projT1 key A) entries) ->
    (findA k entries = Some v <-> List.In (existT A k v) entries).
  Proof.
    induction entries as [|[j w] entries IH]; intros Hnodup; cbn.
    - intuition discriminate.
    - inversion Hnodup as [|? ? Hfresh Htail]; subst.
      destruct (E.eq_dec j k) as [Heq|Hneq].
      + destruct Heq; cbn. split.
        * intros Heq; injection Heq as Heq; subst v; now left.
        * intros [Heq|Hin].
          -- apply (inj_pair2_eq_dec key E.eq_dec) in Heq. now subst v.
          -- exfalso. apply Hfresh, in_map_iff.
             exists (existT A j v); now split.
      + rewrite IH by assumption. split; [now right|].
        intros [Heq|Hin]; [|assumption].
        apply (f_equal (@projT1 key A)) in Heq. contradiction.
  Qed.

  Lemma elements_o {A} (m : t A) k : find k m = findA k (elements m).
  Proof.
    apply eq_option_alt. intro v.
    rewrite <- find_mapsto_iff, findA_NoDup by apply elements_3w.
    apply elements_mapsto_iff.
  Qed.

  Lemma elements_b {A} (m : t A) x :
    mem x m = existsb (fun p => eqb x (projT1 p)) (elements m).
  Proof.
    rewrite eq_bool_alt, <- mem_in_iff, elements_in_iff, existsb_exists.
    split.
    - intros [e Hin]. exists (existT A x e); split; [assumption|].
      unfold eqb; cbn. destruct (E.eq_dec x x); [reflexivity|contradiction].
    - intros [[y e] [Hin Heq]]. unfold eqb in Heq; cbn in Heq.
      destruct (E.eq_dec x y) as [->|Hxy]; [now exists e|discriminate].
  Qed.

  Lemma Equal_mapsto_iff {A} (m n : t A) :
    Equal m n <-> (forall k e, MapsTo k e m <-> MapsTo k e n).
  Proof.
    unfold Equal. split.
    - intros Heq k e. rewrite !find_mapsto_iff, Heq. reflexivity.
    - intros Hmap k. apply eq_option_alt. intro e. rewrite <- !find_mapsto_iff. apply Hmap.
  Qed.

  Lemma Equal_Equiv {A} (m n : t A) : Equal m n <-> Equiv (fun k => @eq (A k)) m n.
  Proof.
    rewrite Equal_mapsto_iff. unfold Equiv. split.
    - intros Hmap. split.
      + intros k. unfold In. now setoid_rewrite Hmap.
      + intros k v w Hv Hw. apply (MapsTo_fun n k v w); [now apply Hmap|assumption].
    - intros [Hdom Hval] k e. split; intros Hmap.
      + assert (Hin : In k n) by (apply Hdom; now exists e).
        destruct Hin as [v Hv]. rewrite (Hval k e v Hmap Hv). assumption.
      + assert (Hin : In k m) by (apply Hdom; now exists e).
        destruct Hin as [v Hv]. rewrite <- (Hval k v e Hv Hmap). assumption.
  Qed.

  Definition compat_cmp {A : key -> Type} (R : forall k, A k -> A k -> Prop)
    (cmp : forall k, A k -> A k -> bool) :=
    forall k e e', cmp k e e' = true <-> R k e e'.

  Lemma Equiv_Equivb {A} (R : forall k, A k -> A k -> Prop) cmp :
    compat_cmp R cmp -> forall m n, Equiv R m n <-> Equivb cmp m n.
  Proof.
    intros Hcmp m n. unfold Equivb, Equiv. unfold compat_cmp in Hcmp.
    split; intros [Hdom Hval]; split; [assumption| |assumption|];
      intros k v w Hv Hw; apply Hcmp, Hval; assumption.
  Qed.

  Lemma Equal_Equivb {A} cmp :
    (forall k (e e' : A k), cmp k e e' = true <-> e = e') ->
    forall m n, Equal m n <-> Equivb cmp m n.
  Proof. intros Hcmp m n. rewrite Equal_Equiv. apply Equiv_Equivb. exact Hcmp. Qed.

  Lemma Equal_Equivb_eqdec {A} (eq_elt_dec : forall k (e e' : A k), {e = e'} + {e <> e'}) :
    forall m n, Equal m n <->
      Equivb (fun k e e' => if eq_elt_dec k e e' then true else false) m n.
  Proof. apply Equal_Equivb. intros k e e'. destruct (eq_elt_dec k e e'); intuition discriminate. Qed.

  Lemma Equal_refl {A} (m : t A) : Equal m m.
  Proof. intros k; reflexivity. Qed.
  Lemma Equal_sym {A} (m n : t A) : Equal m n -> Equal n m.
  Proof. intros Heq k; symmetry; apply Heq. Qed.
  Lemma Equal_trans {A} (m n p : t A) : Equal m n -> Equal n p -> Equal m p.
  Proof. intros Hmn Hnp k; rewrite Hmn; apply Hnp. Qed.

  #[global] Instance Equal_ST {A} : Equivalence (@Equal A).
  Proof. split; [exact Equal_refl|exact Equal_sym|exact Equal_trans]. Qed.

  #[global] Instance In_m {A} : Proper (eq ==> Equal ==> iff) (@In A).
  Proof. intros x y -> m n Heq. rewrite !in_find_iff, Heq. reflexivity. Qed.
  #[global] Instance MapsTo_m {A} k : Proper (eq ==> Equal ==> iff) (@MapsTo A k).
  Proof. intros v w -> m n Heq. rewrite !find_mapsto_iff, Heq. reflexivity. Qed.
  #[global] Instance Empty_m {A} : Proper (Equal ==> iff) (@Empty A).
  Proof.
    intros m n Heq. rewrite Equal_mapsto_iff in Heq. unfold Empty.
    setoid_rewrite Heq. reflexivity.
  Qed.
  #[global] Instance is_empty_m {A} : Proper (Equal ==> eq) (@is_empty A).
  Proof. intros m n Heq. rewrite eq_bool_alt, <- !is_empty_iff. exact (Empty_m m n Heq). Qed.
  #[global] Instance mem_m {A} : Proper (eq ==> Equal ==> eq) (@mem A).
  Proof. intros x y -> m n Heq. rewrite eq_bool_alt, <- !mem_in_iff. exact (In_m y y eq_refl m n Heq). Qed.
  #[global] Instance find_m {A} k : Proper (Equal ==> eq) (@find A k).
  Proof. intros m n Heq; apply Heq. Qed.
  #[global] Instance add_m {A} k : Proper (eq ==> Equal ==> Equal) (@add A k).
  Proof. intros v w -> m n Heq y. rewrite !add_o, Heq. reflexivity. Qed.
  #[global] Instance remove_m {A} : Proper (eq ==> Equal ==> Equal) (@remove A).
  Proof. intros x y -> m n Heq k. rewrite !remove_o, Heq. reflexivity. Qed.
  #[global] Instance map_m {A B} : Proper (eq ==> Equal ==> Equal) (@map A B).
  Proof. intros f g -> m n Heq k. rewrite !map_o, Heq. reflexivity. Qed.
  #[global] Instance mapi_m {A B} : Proper (eq ==> Equal ==> Equal) (@mapi A B).
  Proof. apply map_m. Qed.
  #[global] Instance map2_m {A B C} :
    Proper (eq ==> Equal ==> Equal ==> Equal) (@map2 A B C).
  Proof. intros f g -> m m' Hm n n' Hn k. rewrite !M.map2_o, Hm, Hn. reflexivity. Qed.

  Notation not_find_mapsto_iff := not_find_in_iff.
End DepMapFacts.

Module DepMapProperties (M : DependentMap.DepMap).
  Module Import F := DepMapFacts M.
  Import M.

  Definition Add {A} k (v : A k) (m m' : t A) := Equal m' (add k v m).

  Lemma Add_transpose_neqkey {A} k1 k2 (v1 : A k1) (v2 : A k2)
    (m1 m2 m3 : t A) :
    k1 <> k2 -> Add k1 v1 m1 m2 -> Add k2 v2 m2 m3 ->
    {m | Add k2 v2 m1 m /\ Add k1 v1 m m3}.
  Proof.
    intros Hneq Hadd1 Hadd2. exists (add k2 v2 m1).
    split; [intros k; reflexivity|]. intros k. rewrite Hadd2.
    destruct (E.eq_dec k1 k) as [Heq|Hneq1].
    - subst k. rewrite M.add_neq_o by congruence.
      rewrite Hadd1, !M.add_eq_o. reflexivity.
    - destruct (E.eq_dec k2 k) as [Heq|Hneq2].
      + subst k. rewrite M.add_eq_o, M.add_neq_o, M.add_eq_o by assumption. reflexivity.
      + rewrite !M.add_neq_o by assumption.
        rewrite Hadd1, M.add_neq_o by assumption. reflexivity.
  Qed.

  Lemma elements_Empty {A} (m : t A) : Empty m <-> elements m = nil.
  Proof.
    split.
    - intros Hempty. destruct (elements m) as [|[k v] entries] eqn:Hentries;
        [reflexivity|].
      exfalso. apply (Hempty k v), elements_2. rewrite Hentries; now left.
    - intros Hempty k v Hmap. apply elements_1 in Hmap.
      rewrite Hempty in Hmap. contradiction.
  Qed.

  Lemma elements_empty {A} : elements (empty A) = nil.
  Proof. apply elements_Empty, empty_1. Qed.

  Definition uncurry {A : key -> Type} {B : Type}
    (f : forall k, A k -> B) (entry : sigT A) : B :=
    f (projT1 entry) (projT2 entry).

  Definition of_list {A} (entries : list (sigT A)) : t A :=
    fold_right (fun entry m => add (projT1 entry) (projT2 entry) m)
      (empty A) entries.
  Definition to_list {A} := @elements A.

  (** [of_list] and list lookup both retain the first binding at each key;
      this equality therefore also holds for lists with duplicate keys. *)
  Lemma of_list_1b {A} (entries : list (sigT A)) k :
    find k (of_list entries) = F.findA k entries.
  Proof.
    induction entries as [|[j v] entries IH].
    - apply empty_o.
    - change (find k (add j v (of_list entries)) = F.findA k (existT A j v :: entries)).
      rewrite F.add_o. cbn [F.findA]. rewrite IH. reflexivity.
  Qed.

  Lemma findA_rev {A} (entries : list (sigT A)) k :
    NoDup (List.map (@projT1 key A) entries) ->
    F.findA k entries = F.findA k (rev entries).
  Proof.
    intros Hnodup. apply F.eq_option_alt; intro v.
    rewrite !F.findA_NoDup; [apply in_rev| |assumption].
    rewrite map_rev. now apply NoDup_rev.
  Qed.

  Lemma of_list_1 {A} (entries : list (sigT A)) k (v : A k) :
    NoDup (List.map (@projT1 key A) entries) ->
    (MapsTo k v (of_list entries) <-> List.In (existT A k v) entries).
  Proof.
    induction entries as [|[j w] entries IH]; intros Hnodup.
    - cbn. split; [intros Hmap; exact (empty_1 k v Hmap)|contradiction].
    - inversion Hnodup as [|? ? Hfresh Htail]; subst.
      change (MapsTo k v (add j w (of_list entries)) <->
        existT A j w = existT A k v \/ List.In (existT A k v) entries).
      destruct (E.eq_dec j k) as [Heq|Hneq].
      + subst j. rewrite M.find_mapsto_iff, M.add_eq_o. split.
        * intros Heq. inversion Heq. now left.
        * intros [Heq|Hin].
          -- apply (inj_pair2_eq_dec key E.eq_dec) in Heq. now subst w.
          -- exfalso. apply Hfresh. apply in_map_iff.
             exists (existT A k v). now split.
      + rewrite M.find_mapsto_iff, M.add_neq_o by assumption.
        rewrite <- M.find_mapsto_iff, IH by assumption.
        split; [now right|]. intros [Heq|Hin]; [|assumption].
        apply (f_equal (@projT1 key A)) in Heq. contradiction.
  Qed.

  Lemma of_list_2 {A} (entries : list (sigT A)) :
    NoDup (List.map (@projT1 key A) entries) ->
    forall entry, List.In entry entries <-> List.In entry (to_list (of_list entries)).
  Proof.
    intros Hnodup [k v]. unfold to_list.
    rewrite <- elements_iff, of_list_1 by assumption. reflexivity.
  Qed.

  Lemma of_list_3 {A} (m : t A) : Equal (of_list (to_list m)) m.
  Proof.
    intros k. assert (Hmaps : forall v,
      find k (of_list (to_list m)) = Some v <-> find k m = Some v).
    { intros v. rewrite <- !M.find_mapsto_iff, of_list_1.
      - unfold to_list. symmetry. apply elements_iff.
      - apply elements_3w. }
    destruct (find k (of_list (to_list m))) as [v|] eqn:Hleft,
      (find k m) as [w|] eqn:Hright; try reflexivity.
    - specialize (Hmaps v). intuition congruence.
    - specialize (Hmaps v). intuition discriminate.
    - specialize (Hmaps w). intuition discriminate.
  Qed.

  Lemma fold_spec_right {A B} (m : t A) (init : B)
    (f : forall k, A k -> B -> B) :
    fold f m init = fold_right
      (fun entry acc => f (projT1 entry) (projT2 entry) acc)
      init (rev (elements m)).
  Proof. rewrite fold_1. symmetry. apply fold_left_rev_right. Qed.

  Lemma fold_rec {A B} (P : t A -> B -> Type)
    (f : forall k, A k -> B -> B) (init : B) (m : t A) :
    (forall m, Empty m -> P m init) ->
    (forall k v acc m' m'', MapsTo k v m -> ~ In k m' ->
      Add k v m' m'' -> P m' acc -> P m'' (f k v acc)) ->
    P m (fold f m init).
  Proof.
    intros Hempty Hstep. rewrite fold_spec_right.
    set (entries := rev (elements m)).
    assert (Hnodup : NoDup (List.map (@projT1 key A) entries)).
    { unfold entries. rewrite map_rev. apply NoDup_rev, elements_3w. }
    assert (Hmaps : forall k v, MapsTo k v m <-> List.In (existT A k v) entries).
    { intros k v. unfold entries. rewrite <- in_rev. apply elements_iff. }
    assert (Hstep' : forall k v acc m' m'',
      List.In (existT A k v) entries -> ~ In k m' ->
      Add k v m' m'' -> P m' acc -> P m'' (f k v acc)).
    { intros k v acc m' m'' Hin. apply Hstep, Hmaps, Hin. }
    clearbody entries. clear Hstep. revert m Hmaps.
    induction entries as [|[k v] entries IH]; intros m Hmaps; cbn.
    - apply Hempty. intros k v Hmap. apply Hmaps in Hmap. contradiction.
    - pose proof Hnodup as Hcons.
      apply NoDup_cons_iff in Hcons as [Hfresh Htail].
      apply Hstep' with (of_list entries).
      + now left.
      + intros [w Hmap]. apply of_list_1 in Hmap; [|assumption].
        apply Hfresh. apply in_map_iff. exists (existT A k w). now split.
      + intros j. assert (Hfind : forall w,
          find j m = Some w <-> find j (add k v (of_list entries)) = Some w).
        { intros w. rewrite <- !M.find_mapsto_iff, Hmaps.
          change (List.In (existT A j w) (existT A k v :: entries) <->
            MapsTo j w (of_list (existT A k v :: entries))).
          symmetry. apply of_list_1. exact Hnodup. }
        destruct (find j m) as [w|] eqn:Hleft,
          (find j (add k v (of_list entries))) as [z|] eqn:Hright;
          try reflexivity.
        * specialize (Hfind w). intuition congruence.
        * specialize (Hfind w). intuition discriminate.
        * specialize (Hfind z). intuition discriminate.
      + apply IH; try assumption.
        * intros j w acc m' m'' Hin. apply Hstep'. now right.
        * intros j w. apply of_list_1. assumption.
  Qed.

  Lemma fold_rec_bis {A B} (P : t A -> B -> Type)
    (f : forall k, A k -> B -> B) (init : B) (m : t A) :
    (forall m m' acc, Equal m m' -> P m acc -> P m' acc) ->
    P (empty A) init ->
    (forall k v acc m', MapsTo k v m -> ~ In k m' ->
      P m' acc -> P (add k v m') (f k v acc)) ->
    P m (fold f m init).
  Proof.
    intros Hproper Hempty Hstep. apply fold_rec.
    - intros m' Hempty'. apply Hproper with (empty A); [|assumption].
      intros k. rewrite empty_o. destruct (find k m') as [v|] eqn:Hfind;
        [|reflexivity].
      exfalso. apply (Hempty' k v), find_2, Hfind.
    - intros k v acc m' m'' Hmap Hfresh Hadd Hrec.
      apply Hproper with (add k v m'); [intros j; symmetry; apply Hadd|].
      now apply Hstep.
  Qed.

  Lemma fold_rec_nodep {A B} (P : B -> Type)
    (f : forall k, A k -> B -> B) (init : B) (m : t A) :
    P init -> (forall k v acc, MapsTo k v m -> P acc -> P (f k v acc)) ->
    P (fold f m init).
  Proof.
    intros Hempty Hstep. apply fold_rec_bis with (P := fun _ => P); auto.
  Qed.

  Lemma fold_rec_weak {A B} (P : t A -> B -> Type)
    (f : forall k, A k -> B -> B) (init : B) :
    (forall m m' acc, Equal m m' -> P m acc -> P m' acc) ->
    P (empty A) init ->
    (forall k v acc m, ~ In k m -> P m acc -> P (add k v m) (f k v acc)) ->
    forall m, P m (fold f m init).
  Proof. intros Hproper Hempty Hstep m. apply fold_rec_bis; auto. Qed.

  Lemma fold_rel {A B C} (R : B -> C -> Type)
    (f : forall k, A k -> B -> B) (g : forall k, A k -> C -> C)
    (init : B) (init' : C) (m : t A) :
    R init init' ->
    (forall k v acc acc', MapsTo k v m -> R acc acc' ->
      R (f k v acc) (g k v acc')) ->
    R (fold f m init) (fold g m init').
  Proof.
    intros Hempty Hstep. rewrite !fold_spec_right.
    set (entries := rev (elements m)).
    assert (Hstep' : forall k v acc acc', List.In (existT A k v) entries ->
      R acc acc' -> R (f k v acc) (g k v acc')).
    { intros k v acc acc' Hin. apply Hstep, elements_2.
      apply in_rev. exact Hin. }
    clearbody entries. clear Hstep m.
    induction entries as [|[k v] entries IH]; cbn; [assumption|].
    apply Hstep'; [now left|]. apply IH.
    intros j w acc acc' Hin. apply Hstep'. now right.
  Qed.

  Lemma map_induction {A} (P : t A -> Type) :
    (forall m, Empty m -> P m) ->
    (forall m m', P m -> forall k v, ~ In k m -> Add k v m m' -> P m') ->
    forall m, P m.
  Proof.
    intros Hempty Hstep m.
    apply (fold_rec (fun m (_ : unit) => P m) (fun _ _ _ => tt) tt m); eauto.
  Qed.

  Lemma map_induction_bis {A} (P : t A -> Type) :
    (forall m m', Equal m m' -> P m -> P m') ->
    P (empty A) ->
    (forall k v m, ~ In k m -> P m -> P (add k v m)) ->
    forall m, P m.
  Proof.
    intros Hproper Hempty Hstep m.
    apply (fold_rec_bis (fun m (_ : unit) => P m) (fun _ _ _ => tt) tt m); eauto.
  Qed.

  Lemma fold_identity {A} (m : t A) : Equal (fold (@add A) m (empty A)) m.
  Proof.
    apply fold_rec with (P := fun m acc => Equal acc m).
    - intros m' Hempty k. rewrite empty_o.
      destruct (find k m') as [v|] eqn:Hfind; [|reflexivity].
      exfalso. apply (Hempty k v), find_2, Hfind.
    - intros k v acc m' m'' Hmap Hfresh Hadd Hequal j. rewrite Hadd.
      destruct (E.eq_dec k j) as [Heq|Hneq].
      + subst j. rewrite !M.add_eq_o. reflexivity.
      + rewrite !M.add_neq_o by assumption. apply Hequal.
  Qed.

  Definition eq_key {A : key -> Type} (p q : sigT A) := projT1 p = projT1 q.
  Definition eq_key_elt {A : key -> Type} : sigT A -> sigT A -> Prop := eq.

  #[global] Instance eqk_equiv {A} : Equivalence (@eq_key A).
  Proof. unfold eq_key; split; congruence. Qed.
  #[global] Instance eqke_equiv {A} : Equivalence (@eq_key_elt A).
  Proof. apply eq_equivalence. Qed.

  Lemma nodup_keys_NoDupA {A} (entries : list (sigT A)) :
    NoDup (List.map (@projT1 key A) entries) -> NoDupA eq_key entries.
  Proof.
    induction entries as [|entry entries IH]; cbn; intros Hnodup; constructor.
    - inversion Hnodup as [|? ? Hfresh Htail]; subst.
      intros Hin. apply InA_alt in Hin. destruct Hin as [other [Heq Hin]].
      apply Hfresh, in_map_iff. exists other. split; [symmetry; exact Heq | exact Hin].
    - apply IH. now inversion Hnodup.
  Qed.

  Lemma InA_eqke_eqk {A} (p q : sigT A) entries :
    eq_key p q -> InA eq_key_elt p entries -> InA eq_key q entries.
  Proof.
    intros Hkey Hin. apply InA_alt in Hin. destruct Hin as [other [<- Hin]].
    apply InA_alt. exists p. split; [symmetry; exact Hkey | exact Hin].
  Qed.

  Lemma NoDupA_eqk_eqke {A} (entries : list (sigT A)) :
    NoDupA eq_key entries -> NoDupA eq_key_elt entries.
  Proof.
    induction 1 as [|entry entries Hfresh Hnodup IH]; constructor; auto.
    intros Hin. apply Hfresh. eapply InA_eqke_eqk; [reflexivity | exact Hin].
  Qed.

  Section Fold_More.
    Context {A : key -> Type} {B : Type}.
    Variable eqA : B -> B -> Prop.
    Context {st : Equivalence eqA}.
    Variable f : forall k, A k -> B -> B.
    Hypothesis Comp : forall k, Proper (eq ==> eqA ==> eqA) (f k).

    Lemma fold_init m i i' : eqA i i' -> eqA (fold f m i) (fold f m i').
    Proof.
      intros Hinit. apply fold_rel with (R := eqA); [exact Hinit |].
      intros k v acc acc' Hmap Heq. now apply Comp.
    Qed.

    Lemma fold_Empty m i : Empty m -> eqA (fold f m i) i.
    Proof.
      intros Hempty. rewrite fold_spec_right, (proj1 (elements_Empty m) Hempty).
      cbn. reflexivity.
    Qed.

    Definition transpose_neqkey := forall k k' (v : A k) (v' : A k') acc,
      k <> k' -> eqA (f k v (f k' v' acc)) (f k' v' (f k v acc)).
    Hypothesis Tra : transpose_neqkey.

    Lemma fold_commutes i m k (v : A k) : ~ In k m ->
      eqA (fold f m (f k v i)) (f k v (fold f m i)).
    Proof.
      intros Hfresh. apply fold_rel with (R := fun a b => eqA a (f k v b)).
      - reflexivity.
      - intros j w acc acc' Hmap Heq.
        transitivity (f j w (f k v acc')); [now apply Comp |].
        apply Tra. intros ->. apply Hfresh. now exists w.
    Qed.

    Local Lemma fold_right_equiv (entries entries' : list (sigT A)) i :
      NoDup (List.map (@projT1 key A) entries) ->
      NoDup (List.map (@projT1 key A) entries') ->
      (forall entry, List.In entry entries <-> List.In entry entries') ->
      eqA (fold_right (fun entry => f (projT1 entry) (projT2 entry)) i entries)
          (fold_right (fun entry => f (projT1 entry) (projT2 entry)) i entries').
    Proof.
      intros Hdup Hdup' Hequiv.
      apply fold_right_equivlistA_restr with
        (eqA := @eq_key_elt A) (R := complement (@eq_key A)).
      - apply eqke_equiv.
      - exact st.
      - intros [k v] entry Heq acc acc' Hacc. unfold eq_key_elt in Heq.
        subst entry. now apply Comp.
      - unfold complement, eq_key. intros p q Hneq Heq. apply Hneq. symmetry; exact Heq.
      - intros p p' Hp q q' Hq. unfold eq_key_elt in Hp, Hq. now subst.
      - intros [k v] [k' v'] acc Hneq. apply Tra. exact Hneq.
      - apply NoDupA_eqk_eqke, nodup_keys_NoDupA, Hdup.
      - apply NoDupA_eqk_eqke, nodup_keys_NoDupA, Hdup'.
      - rewrite <- NoDupA_altdef. apply nodup_keys_NoDupA, Hdup.
      - intros entry. rewrite !InA_alt. unfold eq_key_elt.
        split; intros [other [<- Hin]]; exists entry; split;
          try reflexivity; now apply Hequiv.
    Qed.

    Lemma fold_Equal m m' i : Equal m m' -> eqA (fold f m i) (fold f m' i).
    Proof.
      intros Heq. rewrite !fold_spec_right. apply fold_right_equiv.
      - rewrite map_rev. apply NoDup_rev, elements_3w.
      - rewrite map_rev. apply NoDup_rev, elements_3w.
      - intros [k v]. rewrite <- !in_rev, <- !elements_iff, !M.find_mapsto_iff, Heq.
        reflexivity.
    Qed.

    Lemma fold_Equal2 m m' i j : Equal m m' -> eqA i j ->
      eqA (fold f m i) (fold f m' j).
    Proof.
      intros Hmap Hinit. transitivity (fold f m' i).
      - now apply fold_Equal.
      - now apply fold_init.
    Qed.

    Lemma fold_Add m m' k (v : A k) i : ~ In k m -> Add k v m m' ->
      eqA (fold f m' i) (f k v (fold f m i)).
    Proof.
      intros Hfresh Hadd. rewrite !fold_spec_right.
      change (eqA
        (fold_right (fun entry => f (projT1 entry) (projT2 entry)) i (rev (elements m')))
        (fold_right (fun entry => f (projT1 entry) (projT2 entry)) i
          (existT A k v :: rev (elements m)))).
      apply fold_right_equiv.
      - rewrite map_rev. apply NoDup_rev, elements_3w.
      - cbn. constructor.
        + intros Hin. apply in_map_iff in Hin.
          destruct Hin as [[j w] [Heq Hin]]. cbn in Heq. subst j.
          apply Hfresh. exists w. apply elements_2. now apply in_rev.
        + rewrite map_rev. apply NoDup_rev, elements_3w.
      - intros [j w]. cbn. rewrite <- !in_rev, <- !elements_iff.
        change (MapsTo j w m' <-> existT A k v = existT A j w \/ MapsTo j w m).
        rewrite (proj1 (F.Equal_mapsto_iff _ _) Hadd j w), F.add_mapsto_iff.
        split; [tauto |]. intros [Heq | Hmap]; [now left | right].
        split; [|exact Hmap]. intros ->. apply Hfresh. now exists w.
    Qed.

    Lemma fold_add m k (v : A k) i : ~ In k m ->
      eqA (fold f (add k v m) i) (f k v (fold f m i)).
    Proof. intros Hfresh. apply fold_Add; [assumption | intros j; reflexivity]. Qed.
  End Fold_More.

  Lemma cardinal_fold {A} (m : t A) : cardinal m = fold (fun _ _ => S) m 0.
  Proof. rewrite M.cardinal_1, fold_1. symmetry. apply fold_left_S_0. Qed.

  Lemma cardinal_Empty {A} (m : t A) : Empty m <-> cardinal m = 0.
  Proof. rewrite elements_Empty, M.cardinal_1. symmetry. apply length_zero_iff_nil. Qed.

  Lemma Equal_cardinal {A} (m m' : t A) : Equal m m' -> cardinal m = cardinal m'.
  Proof.
    intros Heq. rewrite !cardinal_fold. apply fold_Equal with (eqA := eq); auto.
    - intros k v w -> acc acc' ->. reflexivity.
    - intros k k' v v' acc Hneq. reflexivity.
  Qed.

  Lemma cardinal_1 {A} (m : t A) : Empty m -> cardinal m = 0.
  Proof. apply cardinal_Empty. Qed.

  Lemma cardinal_2 {A} (m m' : t A) k (v : A k) :
    ~ In k m -> Add k v m m' -> cardinal m' = S (cardinal m).
  Proof.
    intros Hfresh Hadd. rewrite !cardinal_fold.
    apply fold_Add with (eqA := eq) (k := k) (v := v); auto.
    - intros j w w' -> acc acc' ->. reflexivity.
    - intros j j' w w' acc Hneq. reflexivity.
  Qed.

  Lemma cardinal_Add_In {A} (m m' : t A) k (v : A k) :
    In k m -> Add k v m m' -> cardinal m' = cardinal m.
  Proof.
    intros [old Hold] Hadd.
    assert (Hremove : Add k old (remove k m) m).
    { intros j. destruct (E.eq_dec k j) as [->|Hneq].
      - rewrite M.add_eq_o. now apply find_1.
      - rewrite M.add_neq_o, M.remove_neq_o by assumption. reflexivity. }
    assert (Hremove' : Add k v (remove k m) m').
    { intros j. rewrite Hadd. destruct (E.eq_dec k j) as [->|Hneq].
      - now rewrite !M.add_eq_o.
      - now rewrite !M.add_neq_o, M.remove_neq_o by assumption. }
    rewrite (cardinal_2 _ _ _ _ (remove_1 k m) Hremove).
    eapply cardinal_2; [apply remove_1 | exact Hremove'].
  Qed.

  Lemma cardinal_inv_1 {A} (m : t A) : cardinal m = 0 -> Empty m.
  Proof. apply cardinal_Empty. Qed.

  Lemma cardinal_inv_2 {A} (m : t A) n : cardinal m = S n ->
    {entry : sigT A | MapsTo (projT1 entry) (projT2 entry) m}.
  Proof.
    rewrite M.cardinal_1. destruct (elements m) as [|entry entries] eqn:Hentries;
      [discriminate|]. intros _. exists entry. apply elements_2.
    rewrite Hentries. destruct entry. now left.
  Qed.

  Lemma cardinal_inv_2b {A} (m : t A) : cardinal m <> 0 ->
    {entry : sigT A | MapsTo (projT1 entry) (projT2 entry) m}.
  Proof.
    intros Hnonzero. destruct (cardinal m) as [|n] eqn:Hcard; [contradiction|].
    now apply (cardinal_inv_2 m n).
  Qed.

  #[global] Instance cardinal_m {A} : Proper (@Equal A ==> eq) (@cardinal A).
  Proof. intros m m' Heq. now apply Equal_cardinal. Qed.

  Local Set Implicit Arguments.
  (** Additional notions and operations, as in [FMapFacts.Properties]. *)
  Section Helpers.
  Context {A : key -> Type}.

  Definition Disjoint (m m' : t A) :=
    forall k, ~(In k m /\ In k m').

  Definition Partition (m m1 m2 : t A) :=
    Disjoint m1 m2 /\
    (forall k e, MapsTo k e m <-> MapsTo k e m1 \/ MapsTo k e m2).

  Definition filter (f : forall k, A k -> bool) (m : t A) : t A :=
    map2 (fun k value _ =>
      match value with Some e => if f k e then Some e else None | None => None end)
      m (empty A).

  Definition for_all (f : forall k, A k -> bool) (m : t A) :=
    forallb (fun p => f (projT1 p) (projT2 p)) (elements m).

  Definition exists_ (f : forall k, A k -> bool) (m : t A) :=
    existsb (fun p => f (projT1 p) (projT2 p)) (elements m).

  Definition partition (f : forall k, A k -> bool) (m : t A) :=
    (filter f m, filter (fun k e => negb (f k e)) m).

  (** The second map takes priority on shared keys. *)
  Definition update (m m' : t A) :=
    map2 (fun _ left right => match right with Some e => Some e | None => left end) m m'.

  Definition restrict (m m' : t A) := filter (fun k _ => mem k m') m.
  Definition diff (m m' : t A) := filter (fun k _ => negb (mem k m')) m.

  Lemma filter_iff (f : forall k, A k -> bool) m k e :
    MapsTo k e (filter f m) <-> MapsTo k e m /\ f k e = true.
  Proof.
    unfold filter. rewrite !find_mapsto_iff, map2_o, empty_o.
    destruct (find k m) as [v|]; cbn; [destruct (f k v) eqn:Hf|];
      intuition congruence.
  Qed.

  Lemma for_all_iff (f : forall k, A k -> bool) m :
    for_all f m = true <-> (forall k e, MapsTo k e m -> f k e = true).
  Proof.
    unfold for_all. rewrite forallb_forall. split.
    - intros H k e Hmap. apply (H (existT A k e)), elements_1, Hmap.
    - intros H [k e] Hin. apply H, elements_2, Hin.
  Qed.

  Lemma exists_iff (f : forall k, A k -> bool) m :
    exists_ f m = true <->
      (exists p, MapsTo (projT1 p) (projT2 p) m /\ f (projT1 p) (projT2 p) = true).
  Proof.
    unfold exists_. rewrite existsb_exists. split;
      intros [[k e] [Hmap Hf]]; exists (existT A k e); split; auto;
      [apply elements_2|apply elements_1]; assumption.
  Qed.

  Lemma Disjoint_alt m m' :
    Disjoint m m' <->
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> False).
  Proof.
    unfold Disjoint, In. firstorder.
  Qed.

  Lemma partition_iff_1 (f : forall k, A k -> bool) m m1 k e :
    m1 = fst (partition f m) ->
    (MapsTo k e m1 <-> MapsTo k e m /\ f k e = true).
  Proof. intros ->. apply filter_iff. Qed.

  Lemma partition_iff_2 (f : forall k, A k -> bool) m m2 k e :
    m2 = snd (partition f m) ->
    (MapsTo k e m2 <-> MapsTo k e m /\ f k e = false).
  Proof.
    intros ->. unfold partition; cbn. rewrite filter_iff, Bool.negb_true_iff.
    reflexivity.
  Qed.

  Lemma partition_Partition (f : forall k, A k -> bool) m m1 m2 :
    partition f m = (m1, m2) -> Partition m m1 m2.
  Proof.
    unfold partition. intros Heq. inversion Heq; subst m1 m2. split.
    - rewrite Disjoint_alt. intros k e e'. rewrite !filter_iff.
      intros [He Hf] [He' Hf']. apply Bool.negb_true_iff in Hf'.
      rewrite (MapsTo_fun m k e e' He He') in Hf. congruence.
    - intros k e. rewrite !filter_iff, Bool.negb_true_iff.
      destruct (f k e); intuition.
  Qed.

  Lemma Partition_In m m1 m2 k :
    Partition m m1 m2 -> In k m -> {In k m1} + {In k m2}.
  Proof.
    intros [_ Hpart] Hmap. destruct (In_dec m1 k) as [Hin|Hnot]; [now left|right].
    destruct Hmap as [e Hmap]. apply Hpart in Hmap. destruct Hmap as [Hmap|Hmap];
      [exfalso; apply Hnot|]; now exists e.
  Defined.

  Lemma Disjoint_sym m1 m2 : Disjoint m1 m2 -> Disjoint m2 m1.
  Proof. unfold Disjoint. firstorder. Qed.

  Lemma Partition_sym m m1 m2 : Partition m m1 m2 -> Partition m m2 m1.
  Proof.
    intros [Hdisj Hpart]. split; [now apply Disjoint_sym|].
    intros k e. rewrite Hpart. tauto.
  Qed.

  Lemma Partition_Empty m m1 m2 :
    Partition m m1 m2 -> (Empty m <-> (Empty m1 /\ Empty m2)).
  Proof.
    intros [_ Hpart]. unfold Empty. setoid_rewrite Hpart. firstorder.
  Qed.

  Lemma Partition_Add m m' x (e : A x) :
    ~ In x m -> Add x e m m' ->
    forall m1 m2, Partition m' m1 m2 ->
    exists m3, (Add x e m3 m1 /\ Partition m m3 m2 \/
                Add x e m3 m2 /\ Partition m m1 m3).
  Proof.
    intros Hfresh Hadd m1 m2 [Hdisj Hpart].
    change (Equal m' (add x e m)) in Hadd.
    assert (Hremove : Equal m (remove x m')).
    { rewrite Hadd. intros k. destruct (E.eq_dec x k) as [Heq|Hneq].
      - subst k. rewrite M.remove_eq_o. now apply not_find_in_iff.
      - rewrite M.remove_neq_o, M.add_neq_o by assumption. reflexivity. }
    assert (Hx : MapsTo x e m').
    { rewrite Hadd. apply add_1. }
    apply Hpart in Hx. destruct Hx as [Hx|Hx].
    - exists (remove x m1). left. split; [|split].
      + intros k. destruct (E.eq_dec x k) as [Heq|Hneq].
        * subst k. rewrite M.add_eq_o. now apply find_1.
        * rewrite M.add_neq_o, M.remove_neq_o by assumption. reflexivity.
      + intros k [Hleft Hright]. apply (Hdisj k). split; [|assumption].
        apply remove_in_iff in Hleft. tauto.
      + intros k v. rewrite Hremove, !remove_mapsto_iff, Hpart.
        split.
        * intros [Hneq [Hleft|Hright]]; [left|right]; auto.
        * intros [[Hneq Hleft]|Hright]; [auto|]. split; [|now right].
          intros Heq. subst k. apply (Hdisj x). split; [now exists e|now exists v].
    - exists (remove x m2). right. split; [|split].
      + intros k. destruct (E.eq_dec x k) as [Heq|Hneq].
        * subst k. rewrite M.add_eq_o. now apply find_1.
        * rewrite M.add_neq_o, M.remove_neq_o by assumption. reflexivity.
      + intros k [Hleft Hright]. apply (Hdisj k). split; [assumption|].
        apply remove_in_iff in Hright. tauto.
      + intros k v. rewrite Hremove, !remove_mapsto_iff, Hpart.
        split.
        * intros [Hneq [Hleft|Hright]]; [left|right]; auto.
        * intros [Hleft|[Hneq Hright]]; [|auto]. split; [|now left].
          intros Heq. subst k. apply (Hdisj x). split; [now exists v|now exists e].
  Qed.

  Lemma Partition_fold {B} (eqA : B -> B -> Prop) {st : Equivalence eqA}
    (f : forall k, A k -> B -> B) :
    (forall k, Proper (eq ==> eqA ==> eqA) (f k)) ->
    transpose_neqkey eqA f ->
    forall m m1 m2 i, Partition m m1 m2 ->
    eqA (fold f m i) (fold f m1 (fold f m2 i)).
  Proof.
    intros Comp Tra m.
    induction m as [m Hempty|m m' IH k e Hfresh Hadd] using map_induction.
    - intros m1 m2 i Hpart.
      destruct (proj1 (Partition_Empty Hpart) Hempty) as [Hempty1 Hempty2].
      transitivity i; [now apply fold_Empty|]. symmetry.
      transitivity (fold f m2 i); apply fold_Empty; assumption.
    - intros m1 m2 i Hpart.
      destruct (Partition_Add Hfresh Hadd Hpart) as [m3 [[Hadd' Hpart']|[Hadd' Hpart']]].
      + assert (Hfresh3 : ~ In k m3).
        { intros [v Hmap]. apply Hfresh. exists v. apply (proj2 (proj2 Hpart' k v)). now left. }
        transitivity (f k e (fold f m i)).
        * eapply fold_Add; eauto.
        * symmetry. transitivity (f k e (fold f m3 (fold f m2 i))).
          -- eapply fold_Add; eauto.
          -- apply Comp; [reflexivity|]. symmetry. now apply IH.
      + assert (Hfresh3 : ~ In k m3).
        { intros [v Hmap]. apply Hfresh. exists v. apply (proj2 (proj2 Hpart' k v)). now right. }
        assert (Hfresh1 : ~ In k m1).
        { intros [v Hmap]. apply Hfresh. exists v. apply (proj2 (proj2 Hpart' k v)). now left. }
        transitivity (f k e (fold f m i)).
        * eapply fold_Add; eauto.
        * transitivity (f k e (fold f m1 (fold f m3 i))).
          -- apply Comp; [reflexivity|]. now apply IH.
          -- transitivity (fold f m1 (f k e (fold f m3 i))).
             ++ symmetry. apply fold_commutes with (eqA := eqA); assumption.
             ++ apply fold_init with (eqA := eqA); [exact Comp|]. symmetry. eapply fold_Add; eauto.
  Qed.

  Lemma Partition_cardinal m m1 m2 : Partition m m1 m2 ->
    cardinal m = cardinal m1 + cardinal m2.
  Proof.
    intros Hpart. rewrite (cardinal_fold m), (cardinal_fold m1).
    transitivity (fold (fun _ _ => S) m1 (fold (fun _ _ => S) m2 0)).
    - apply Partition_fold with (eqA := eq); try assumption.
      + apply eq_equivalence.
      + intros k v w -> acc acc' ->. reflexivity.
      + intros k k' v v' acc Hneq. reflexivity.
    - rewrite <- cardinal_fold.
      apply fold_rel with (R := fun u v => u = v + cardinal m2); auto.
      intros k v acc acc' Hmap Heq. cbn. now rewrite Heq.
  Qed.

  Lemma Partition_partition m m1 m2 : Partition m m1 m2 ->
    let f := fun k (_ : A k) => mem k m1 in
    Equal m1 (fst (partition f m)) /\ Equal m2 (snd (partition f m)).
  Proof.
    intros [Hdisj Hpart] f. unfold partition; cbn. split;
      rewrite Equal_mapsto_iff; intros k e; rewrite filter_iff; unfold f.
    - rewrite <- mem_in_iff, Hpart. split.
      + intros Hmap. split; [now left|now exists e].
      + intros [[Hmap|Hmap] Hin]; [assumption|].
        exfalso. apply (Hdisj k). split; [assumption|now exists e].
    - rewrite Bool.negb_true_iff, <- not_mem_in_iff, Hpart. split.
      + intros Hmap. split; [now right|].
        intros Hin. apply (Hdisj k). split; [assumption|now exists e].
      + intros [[Hmap|Hmap] Hnot]; [|assumption].
        exfalso. apply Hnot. now exists e.
  Qed.

  Lemma update_mapsto_iff m m' k e :
    MapsTo k e (update m m') <->
    MapsTo k e m' \/ (MapsTo k e m /\ ~ In k m').
  Proof.
    unfold update. rewrite !find_mapsto_iff, not_find_in_iff, map2_o.
    destruct (find k m) as [v|], (find k m') as [v'|]; cbn;
      intuition discriminate.
  Qed.

  Lemma update_dec m m' k e : MapsTo k e (update m m') ->
    {MapsTo k e m'} + {MapsTo k e m /\ ~ In k m'}.
  Proof.
    intros Hmap. apply update_mapsto_iff in Hmap.
    destruct (In_dec m' k) as [Hin|Hnot]; [left|right]; intuition.
    exfalso. apply Hnot. now exists e.
  Defined.

  Lemma update_in_iff m m' k :
    In k (update m m') <-> In k m \/ In k m'.
  Proof.
    unfold In at 1. setoid_rewrite update_mapsto_iff. split.
    - intros [e [Hmap|[Hmap Hnot]]]; [right|left]; now exists e.
    - destruct (In_dec m' k) as [[e Hmap]|Hnot].
      + intros _. exists e. now left.
      + intros [[e Hmap]|Hin]; [exists e; now right|contradiction].
  Qed.

  Lemma diff_mapsto_iff m m' k e :
    MapsTo k e (diff m m') <-> MapsTo k e m /\ ~ In k m'.
  Proof.
    unfold diff. rewrite filter_iff, Bool.negb_true_iff, not_mem_in_iff.
    reflexivity.
  Qed.

  Lemma diff_in_iff m m' k : In k (diff m m') <-> In k m /\ ~ In k m'.
  Proof. unfold In at 1 2. setoid_rewrite diff_mapsto_iff. firstorder. Qed.

  Lemma restrict_mapsto_iff m m' k e :
    MapsTo k e (restrict m m') <-> MapsTo k e m /\ In k m'.
  Proof. unfold restrict. rewrite filter_iff, mem_in_iff. reflexivity. Qed.

  Lemma restrict_in_iff m m' k : In k (restrict m m') <-> In k m /\ In k m'.
  Proof. unfold In at 1 2. setoid_rewrite restrict_mapsto_iff. firstorder. Qed.

  Definition filter_dom (f : key -> bool) := filter (fun k _ => f k).
  Definition filter_range (f : forall {k}, A k -> bool) := filter (fun k e => f e).
  Definition for_all_dom (f : key -> bool) := for_all (fun k _ => f k).
  Definition for_all_range (f : forall {k}, A k -> bool) := for_all (fun k e => f e).
  Definition exists_dom (f : key -> bool) := exists_ (fun k _ => f k).
  Definition exists_range (f : forall {k}, A k -> bool) := exists_ (fun k e => f e).
  Definition partition_dom (f : key -> bool) := partition (fun k _ => f k).
  Definition partition_range (f : forall {k}, A k -> bool) := partition (fun k e => f e).

  End Helpers.

  #[global] Instance Disjoint_m A :
    Proper (Equal ==> Equal ==> iff) (@Disjoint A).
  Proof.
    intros m1 m1' Hm1 m2 m2' Hm2. unfold Disjoint.
    setoid_rewrite Hm1. setoid_rewrite Hm2. reflexivity.
  Qed.

  #[global] Instance Partition_m A :
    Proper (Equal ==> Equal ==> Equal ==> iff) (@Partition A).
  Proof.
    intros m m' Hm m1 m1' Hm1 m2 m2' Hm2. unfold Partition.
    setoid_rewrite Hm. setoid_rewrite Hm1. setoid_rewrite Hm2. reflexivity.
  Qed.

  #[global] Instance update_m A :
    Proper (Equal ==> Equal ==> Equal) (@update A).
  Proof.
    intros m m' Hm n n' Hn. rewrite Equal_mapsto_iff. intros k e.
    rewrite !update_mapsto_iff, Hm, Hn. reflexivity.
  Qed.

  #[global] Instance restrict_m A :
    Proper (Equal ==> Equal ==> Equal) (@restrict A).
  Proof.
    intros m m' Hm n n' Hn. rewrite Equal_mapsto_iff. intros k e.
    rewrite !restrict_mapsto_iff, Hm, Hn. reflexivity.
  Qed.

  #[global] Instance diff_m A :
    Proper (Equal ==> Equal ==> Equal) (@diff A).
  Proof.
    intros m m' Hm n n' Hn. rewrite Equal_mapsto_iff. intros k e.
    rewrite !diff_mapsto_iff, Hm, Hn. reflexivity.
  Qed.

End DepMapProperties.
