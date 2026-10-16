From Stdlib Require Import FMapAVL FMapFacts List.
From Stdlib Require Import Structures.Orders Structures.OrdersAlt Structures.OrdersEx.
From Stdlib Require Import Logic.Eqdep_dec.

(** Public interface consumed by dependent map facts and properties. *)
Module Type DepMap.
  Declare Module E : UsualOrderedType.
  Definition key := E.t.
  Parameter t : (key -> Type) -> Type.
  Parameter empty : forall A, t A.
  Parameter add : forall {A} k, A k -> t A -> t A.
  Parameter find : forall {A} k, t A -> option (A k).
  Parameter remove : forall {A}, key -> t A -> t A.
  Parameter mem : forall {A}, key -> t A -> bool.
  Parameter is_empty : forall {A}, t A -> bool.
  Parameter cardinal : forall {A}, t A -> nat.
  Parameter elements : forall {A}, t A -> list (sigT A).
  Parameter fold : forall {A B}, (forall k, A k -> B -> B) -> t A -> B -> B.
  Parameter map : forall {A B}, (forall k, A k -> B k) -> t A -> t B.
  Definition mapi := @map.
  Arguments mapi {A B} f m.
  Parameter map2 : forall {A B C},
    (forall k, option (A k) -> option (B k) -> option (C k)) -> t A -> t B -> t C.
  Parameter equal : forall {A}, (forall k, A k -> A k -> bool) -> t A -> t A -> bool.
  Parameter MapsTo : forall {A} k, A k -> t A -> Prop.
  Definition In {A} (k : key) (m : t A) := exists v, MapsTo k v m.
  Definition Empty {A} (m : t A) := forall k v, ~ MapsTo k v m.
  Definition Equal {A} (m n : t A) := forall k, find k m = find k n.
  Definition Equiv {A} (R : forall k, A k -> A k -> Prop) (m n : t A) :=
    (forall k, In k m <-> In k n) /\
    (forall k v w, MapsTo k v m -> MapsTo k w n -> R k v w).
  Definition Equivb {A} (cmp : forall k, A k -> A k -> bool) :=
    Equiv (fun k v w => cmp k v w = true).

  Axiom find_1 : forall {A} k (v : A k) m, MapsTo k v m -> find k m = Some v.
  Axiom find_2 : forall {A} k (v : A k) m, find k m = Some v -> MapsTo k v m.
  Axiom find_mapsto_iff : forall {A} k (v : A k) m,
    MapsTo k v m <-> find k m = Some v.
  Axiom mem_in_iff : forall {A} k (m : t A), In k m <-> mem k m = true.
  Axiom mem_1 : forall {A} k (m : t A), In k m -> mem k m = true.
  Axiom mem_2 : forall {A} k (m : t A), mem k m = true -> In k m.
  Axiom empty_o : forall {A} k, find k (empty A) = None.
  Axiom empty_1 : forall {A}, Empty (empty A).
  Axiom is_empty_iff : forall {A} (m : t A), Empty m <-> is_empty m = true.
  Axiom is_empty_1 : forall {A} (m : t A), Empty m -> is_empty m = true.
  Axiom is_empty_2 : forall {A} (m : t A), is_empty m = true -> Empty m.
  Axiom add_eq_o : forall {A} k (v : A k) m, find k (add k v m) = Some v.
  Axiom add_neq_o : forall {A} k j (v : A k) m,
    k <> j -> find j (add k v m) = find j m.
  Axiom add_1 : forall {A} k (v : A k) m, MapsTo k v (add k v m).
  Axiom add_2 : forall {A} k j (v : A k) (w : A j) m,
    k <> j -> MapsTo j w m -> MapsTo j w (add k v m).
  Axiom add_3 : forall {A} k j (v : A k) (w : A j) m,
    k <> j -> MapsTo j w (add k v m) -> MapsTo j w m.
  Axiom remove_eq_o : forall {A} k (m : t A), find k (remove k m) = None.
  Axiom remove_neq_o : forall {A} k j (m : t A),
    k <> j -> find j (remove k m) = find j m.
  Axiom remove_1 : forall {A} k (m : t A), ~ In k (remove k m).
  Axiom remove_2 : forall {A} k j (v : A j) m,
    k <> j -> MapsTo j v m -> MapsTo j v (remove k m).
  Axiom remove_3 : forall {A} k j (v : A j) m,
    MapsTo j v (remove k m) -> MapsTo j v m.
  Axiom map_o : forall {A B} (f : forall k, A k -> B k) k m,
    find k (map f m) = option_map (f k) (find k m).
  Axiom map_1 : forall {A B} (f : forall k, A k -> B k) k v m,
    MapsTo k v m -> MapsTo k (f k v) (map f m).
  Axiom map_2 : forall {A B} (f : forall k, A k -> B k) k m,
    In k (map f m) -> In k m.
  Axiom map2_o : forall {A B C} f k (left : t A) (right : t B),
    find k (@map2 A B C f left right) =
    match find k left, find k right with None, None => None | lv, rv => f k lv rv end.
  Axiom map2_1bis : forall {A B C} f k (left : t A) (right : t B),
    f k None None = None ->
    find k (@map2 A B C f left right) = f k (find k left) (find k right).
  Axiom map2_1 : forall {A B C} f k (left : t A) (right : t B),
    In k left \/ In k right ->
    find k (@map2 A B C f left right) = f k (find k left) (find k right).
  Axiom map2_2 : forall {A B C} f k (left : t A) (right : t B),
    In k (@map2 A B C f left right) -> In k left \/ In k right.
  Axiom equal_iff : forall {A} (cmp : forall k, A k -> A k -> bool) (m n : t A),
    Equivb cmp m n <-> equal cmp m n = true.
  Axiom equal_1 : forall {A} (cmp : forall k, A k -> A k -> bool) (m n : t A),
    Equivb cmp m n -> equal cmp m n = true.
  Axiom equal_2 : forall {A} (cmp : forall k, A k -> A k -> bool) (m n : t A),
    equal cmp m n = true -> Equivb cmp m n.
  Axiom elements_iff : forall {A} k (v : A k) m,
    MapsTo k v m <-> List.In (existT A k v) (elements m).
  Axiom elements_1 : forall {A} k (v : A k) m,
    MapsTo k v m -> List.In (existT A k v) (elements m).
  Axiom elements_2 : forall {A} k (v : A k) m,
    List.In (existT A k v) (elements m) -> MapsTo k v m.
  Axiom elements_3w : forall {A} (m : t A),
    NoDup (List.map (@projT1 key A) (elements m)).
  Axiom cardinal_1 : forall {A} (m : t A), cardinal m = length (elements m).
  Axiom fold_1 : forall {A B} (f : forall k, A k -> B -> B) (m : t A) init,
    fold f m init =
      fold_left (fun acc entry => f (projT1 entry) (projT2 entry) acc) (elements m) init.
End DepMap.

(** Finite maps whose value type depends on the key. Keys use Leibniz
    equality, as required to transport values between equal keys.

    Usage: [Module M := DependentMap.Make(Var).]
    Then [M.t A] stores values of type [A k] at key [k], and
    [M.find k (M.add k v (M.empty A)) = Some v].

    The implementation retains FMapAVL's balanced trees. [elements] returns
    dependent pairs, and mapping/folding callbacks receive the key explicitly.
    [map] and [mapi] coincide, since both need the key to specify value types.
    The usual FMapFacts functors do not accept this dependent interface;
    the basic lookup and membership facts are provided below. Further facts,
    induction principles, and helper operations are in [DependentMapProperties]. *)
Module Make (K : UsualOrderedType) <: DepMap.
  Module E := K.
  Module Legacy := Backport_OT(E).
  Module Raw := FMapAVL.Make(Legacy).
  Module RawFacts := FMapFacts.Facts(Raw).

  Definition key := E.t.

  Record map_data (A : key -> Type) := Build_t {
    raw : Raw.t (sigT A);
    well_formed : forall k entry, Raw.MapsTo k entry raw -> projT1 entry = k
  }.
  Definition t := map_data.
  Arguments raw {A} _.
  Arguments well_formed {A} _ k entry _.

  Definition unpack {A} (k : key) (entry : sigT A) : option (A k) :=
    match E.eq_dec (projT1 entry) k with
    | left Heq => Some (eq_rect _ A (projT2 entry) _ Heq)
    | right _ => None
    end.

  Lemma unpack_same {A} k (v : A k) : unpack k (existT A k v) = Some v.
  Proof.
    unfold unpack; cbn.
    destruct (E.eq_dec k k) as [Heq | Hneq]; [|contradiction].
    replace Heq with (@eq_refl key k) by apply (UIP_dec E.eq_dec).
    reflexivity.
  Qed.

  Lemma unpack_some {A} k entry (v : A k) :
    unpack k entry = Some v <-> entry = existT A k v.
  Proof.
    split; [|intros ->; apply unpack_same].
    destruct entry as [j w]. unfold unpack; cbn.
    destruct (E.eq_dec j k) as [Heq | Hneq]; [|discriminate].
    destruct Heq. cbn. intros Heq; now inversion Heq.
  Qed.

  Definition empty (A : key -> Type) : t A.
  Proof.
    refine {| raw := Raw.empty _ |}.
    intros k entry Hmap; now apply Raw.empty_1 in Hmap.
  Defined.

  Definition add {A} (k : key) (v : A k) (m : t A) : t A.
  Proof.
    refine {| raw := Raw.add k (existT A k v) (raw m) |}.
    intros j entry Hmap. apply RawFacts.add_mapsto_iff in Hmap.
    destruct Hmap as [[Heq <-] | [_ Hmap]].
    - exact Heq.
    - exact (well_formed m j entry Hmap).
  Defined.

  Definition find {A} (k : key) (m : t A) : option (A k) :=
    match Raw.find k (raw m) with
    | Some entry => unpack k entry
    | None => None
    end.

  Definition remove {A} (k : key) (m : t A) : t A.
  Proof.
    refine {| raw := Raw.remove k (raw m) |}.
    intros j entry Hmap.
    apply Raw.remove_3 in Hmap. exact (well_formed m j entry Hmap).
  Defined.

  Definition mem {A} (k : key) (m : t A) := Raw.mem k (raw m).
  Definition is_empty {A} (m : t A) := Raw.is_empty (raw m).
  Definition cardinal {A} (m : t A) := Raw.cardinal (raw m).

  Definition elements {A} (m : t A) : list {k : key & A k} :=
    List.map snd (Raw.elements (raw m)).

  Definition fold {A B} (f : forall k, A k -> B -> B) (m : t A) (init : B) : B :=
    Raw.fold (fun _ entry => f (projT1 entry) (projT2 entry)) (raw m) init.

  Definition map {A B} (f : forall k, A k -> B k) (m : t A) : t B.
  Proof.
    refine {| raw := Raw.map
      (fun entry => existT B (projT1 entry) (f (projT1 entry) (projT2 entry)))
      (raw m) |}.
    intros k entry Hmap. apply RawFacts.map_mapsto_iff in Hmap.
    destruct Hmap as [old [-> Hmap]].
    exact (well_formed m k old Hmap).
  Defined.

  Definition mapi := @map.
  Arguments mapi {A B} f m.

  Definition equal {A} (cmp : forall k, A k -> A k -> bool) (m n : t A) : bool :=
    Raw.equal (fun left right =>
      match unpack (projT1 left) right with
      | Some v => cmp (projT1 left) (projT2 left) v
      | None => false
      end) (raw m) (raw n).

  Definition MapsTo {A} (k : key) (v : A k) (m : t A) : Prop :=
    Raw.MapsTo k (existT A k v) (raw m).
  Definition In {A} (k : key) (m : t A) : Prop := exists v, MapsTo k v m.
  Definition Empty {A} (m : t A) : Prop := forall k v, ~ MapsTo k v m.
  Definition Equal {A} (m n : t A) : Prop := forall k, find k m = find k n.

  Definition Equiv {A} (R : forall k, A k -> A k -> Prop) (m n : t A) : Prop :=
    (forall k, In k m <-> In k n) /\
    (forall k v w, MapsTo k v m -> MapsTo k w n -> R k v w).

  Definition Equivb {A} (cmp : forall k, A k -> A k -> bool) : t A -> t A -> Prop :=
    Equiv (fun k v w => cmp k v w = true).


  Lemma find_1 {A} k (v : A k) m : MapsTo k v m -> find k m = Some v.
  Proof.
    intros Hmap. unfold find. rewrite (Raw.find_1 Hmap). apply unpack_same.
  Qed.

  Lemma find_2 {A} k (v : A k) m : find k m = Some v -> MapsTo k v m.
  Proof.
    unfold find, MapsTo.
    destruct (Raw.find k (raw m)) as [entry |] eqn:Hfind; [|discriminate].
    rewrite unpack_some. intros <-. now apply Raw.find_2.
  Qed.

  Lemma find_mapsto_iff {A} k (v : A k) m :
    MapsTo k v m <-> find k m = Some v.
  Proof. split; [apply find_1 | apply find_2]. Qed.

  (** The representation invariant ensures that lookup never loses a binding. *)
  Lemma raw_find {A} k (m : t A) :
    Raw.find k (raw m) = option_map (existT A k) (find k m).
  Proof.
    unfold find. destruct (Raw.find k (raw m)) as [[j v] |] eqn:Hfind;
      [|reflexivity].
    apply Raw.find_2 in Hfind.
    pose proof (well_formed m k (existT A j v) Hfind) as Heq.
    cbn in Heq. subst j. now rewrite unpack_same.
  Qed.

  Lemma in_raw_iff {A} k (m : t A) : In k m <-> Raw.In k (raw m).
  Proof.
    split.
    - intros [v Hmap]. exists (existT A k v). exact Hmap.
    - intros [[j v] Hmap].
      pose proof (well_formed m k (existT A j v) Hmap) as Heq.
      cbn in Heq. subst j. now exists v.
  Qed.

  (* Retain the key of a present entry. In a well-formed map the other
     entry, when present, has the same key. *)
  Definition map2_entry {A B C : key -> Type}
    (f : forall k, option (A k) -> option (B k) -> option (C k))
    (left : option (sigT A)) (right : option (sigT B)) :
    option (sigT C) :=
    match left, right with
    | Some (existT _ k value), other =>
        option_map (existT C k)
          (f k (Some value)
            (match other with Some entry => unpack k entry | None => None end))
    | None, Some (existT _ k value) =>
        option_map (existT C k) (f k None (Some value))
    | None, None => None
    end.

  Lemma map2_entry_same {A B C} f k
    (left : option (A k)) (right : option (B k)) :
    @map2_entry A B C f
      (option_map (existT A k) left) (option_map (existT B k) right) =
    option_map (existT C k)
      (match left, right with None, None => None | _, _ => f k left right end).
  Proof.
    destruct left as [lv|], right as [rv|]; cbn [option_map map2_entry];
      rewrite ?unpack_same; reflexivity.
  Qed.

  Definition map2 {A B C : key -> Type}
    (f : forall k, option (A k) -> option (B k) -> option (C k))
    (left : t A) (right : t B) : t C.
  Proof.
    refine {| raw := Raw.map2 (map2_entry f) (raw left) (raw right) |}.
    intros k entry Hentry. apply Raw.find_1 in Hentry.
    rewrite RawFacts.map2_1bis in Hentry by reflexivity.
    rewrite !raw_find, map2_entry_same in Hentry.
    match type of Hentry with
    | option_map _ ?values = _ => destruct values as [value|]
    end; inversion Hentry; reflexivity.
  Defined.

  Lemma map2_o {A B C} f k (left : t A) (right : t B) :
    find k (@map2 A B C f left right) =
    match find k left, find k right with
    | None, None => None
    | lv, rv => f k lv rv
    end.
  Proof.
    unfold find at 1. cbn [map2 raw].
    rewrite RawFacts.map2_1bis by reflexivity.
    rewrite !raw_find, map2_entry_same.
    destruct (find k left) as [lv|], (find k right) as [rv|]; cbn; try reflexivity.
    all: destruct (f k _ _) as [value|]; cbn; [apply unpack_same|reflexivity].
  Qed.

  Lemma map2_1bis {A B C} f k (left : t A) (right : t B) :
    f k None None = None ->
    find k (@map2 A B C f left right) = f k (find k left) (find k right).
  Proof.
    intros Hnone. rewrite map2_o.
    destruct (find k left), (find k right); auto.
  Qed.

  Lemma map2_1 {A B C} f k (left : t A) (right : t B) :
    In k left \/ In k right ->
    find k (@map2 A B C f left right) = f k (find k left) (find k right).
  Proof.
    rewrite map2_o. intros [[v Hmap] | [v Hmap]];
      apply find_1 in Hmap; rewrite Hmap; [reflexivity | now destruct (find k left)].
  Qed.

  Lemma map2_2 {A B C} f k (left : t A) (right : t B) :
    In k (@map2 A B C f left right) -> In k left \/ In k right.
  Proof.
    rewrite !in_raw_iff. apply Raw.map2_2.
  Qed.

  Lemma mem_in_iff {A} k (m : t A) : In k m <-> mem k m = true.
  Proof. rewrite in_raw_iff. apply RawFacts.mem_in_iff. Qed.

  Lemma mem_1 {A} k (m : t A) : In k m -> mem k m = true.
  Proof. apply mem_in_iff. Qed.

  Lemma mem_2 {A} k (m : t A) : mem k m = true -> In k m.
  Proof. apply mem_in_iff. Qed.

  Lemma empty_o {A} k : find k (empty A) = None.
  Proof. reflexivity. Qed.

  Lemma empty_1 {A} : Empty (empty A).
  Proof. intros k v Hmap. apply find_1 in Hmap. rewrite empty_o in Hmap. discriminate. Qed.

  Lemma is_empty_iff {A} (m : t A) : Empty m <-> is_empty m = true.
  Proof.
    unfold Empty, is_empty. rewrite <- RawFacts.is_empty_iff.
    split.
    - intros Hempty k [j v] Hmap.
      pose proof (well_formed m k (existT A j v) Hmap) as Heq.
      cbn in Heq. subst j. exact (Hempty k v Hmap).
    - intros Hempty k v Hmap. exact (Hempty k (existT A k v) Hmap).
  Qed.

  Lemma is_empty_1 {A} (m : t A) : Empty m -> is_empty m = true.
  Proof. apply is_empty_iff. Qed.

  Lemma is_empty_2 {A} (m : t A) : is_empty m = true -> Empty m.
  Proof. apply is_empty_iff. Qed.

  Lemma add_eq_o {A} k (v : A k) m : find k (add k v m) = Some v.
  Proof.
    unfold find; cbn [add raw].
    rewrite RawFacts.add_eq_o by reflexivity. apply unpack_same.
  Qed.

  Lemma add_neq_o {A} k j (v : A k) m :
    k <> j -> find j (add k v m) = find j m.
  Proof. intros Hneq. unfold find; cbn [add raw]. now rewrite RawFacts.add_neq_o. Qed.

  Lemma add_1 {A} k (v : A k) m : MapsTo k v (add k v m).
  Proof. apply find_2, add_eq_o. Qed.

  Lemma add_2 {A} k j (v : A k) (w : A j) m :
    k <> j -> MapsTo j w m -> MapsTo j w (add k v m).
  Proof. intros Hneq. rewrite !find_mapsto_iff, add_neq_o by assumption. trivial. Qed.

  Lemma add_3 {A} k j (v : A k) (w : A j) m :
    k <> j -> MapsTo j w (add k v m) -> MapsTo j w m.
  Proof. intros Hneq. rewrite !find_mapsto_iff, add_neq_o by assumption. trivial. Qed.

  Lemma remove_eq_o {A} k (m : t A) : find k (remove k m) = None.
  Proof. unfold find; cbn [remove raw]. now rewrite RawFacts.remove_eq_o by reflexivity. Qed.

  Lemma remove_neq_o {A} k j (m : t A) :
    k <> j -> find j (remove k m) = find j m.
  Proof. intros Hneq. unfold find; cbn [remove raw]. now rewrite RawFacts.remove_neq_o. Qed.

  Lemma remove_1 {A} k (m : t A) : ~ In k (remove k m).
  Proof.
    intros [v Hmap]. apply find_1 in Hmap. rewrite remove_eq_o in Hmap. discriminate.
  Qed.

  Lemma remove_2 {A} k j (v : A j) m :
    k <> j -> MapsTo j v m -> MapsTo j v (remove k m).
  Proof. intros Hneq. rewrite !find_mapsto_iff, remove_neq_o by assumption. trivial. Qed.

  Lemma remove_3 {A} k j (v : A j) m :
    MapsTo j v (remove k m) -> MapsTo j v m.
  Proof. apply Raw.remove_3. Qed.

  Lemma map_o {A B} (f : forall k, A k -> B k) k m :
    find k (map f m) = option_map (f k) (find k m).
  Proof.
    unfold find at 1; cbn [map raw]. rewrite RawFacts.map_o, raw_find.
    destruct (find k m) as [v |]; cbn; [apply unpack_same | reflexivity].
  Qed.

  Lemma map_1 {A B} (f : forall k, A k -> B k) k v m :
    MapsTo k v m -> MapsTo k (f k v) (map f m).
  Proof. rewrite !find_mapsto_iff, map_o. intros ->. reflexivity. Qed.

  Lemma map_2 {A B} (f : forall k, A k -> B k) k m : In k (map f m) -> In k m.
  Proof. rewrite !in_raw_iff. apply Raw.map_2. Qed.

  Lemma equal_iff {A} (cmp : forall k, A k -> A k -> bool) (m n : t A) :
    Equivb cmp m n <-> equal cmp m n = true.
  Proof.
    unfold Equivb, Equiv, equal. split.
    - intros [Hdomain Hvalues]. apply Raw.equal_1. split.
      + intros k. rewrite <- !in_raw_iff. apply Hdomain.
      + intros k [j v] [l w] Hv Hw.
        pose proof (well_formed m k _ Hv) as Hleft.
        pose proof (well_formed n k _ Hw) as Hright.
        cbn in Hleft, Hright. subst j l.
        change (match unpack k (existT A k w) with
                | Some w' => cmp k v w' | None => false
                end = true).
        rewrite unpack_same. exact (Hvalues k v w Hv Hw).
    - intros Hequal. apply Raw.equal_2 in Hequal.
      destruct Hequal as [Hdomain Hvalues]. split.
      + intros k. rewrite !in_raw_iff. apply Hdomain.
      + intros k v w Hv Hw.
        specialize (Hvalues k (existT A k v) (existT A k w) Hv Hw).
        change (match unpack k (existT A k w) with
                | Some w' => cmp k v w' | None => false
                end = true) in Hvalues.
        now rewrite unpack_same in Hvalues.
  Qed.

  Lemma equal_1 {A} (cmp : forall k, A k -> A k -> bool) (m n : t A) :
    Equivb cmp m n -> equal cmp m n = true.
  Proof. apply equal_iff. Qed.

  Lemma equal_2 {A} (cmp : forall k, A k -> A k -> bool) (m n : t A) :
    equal cmp m n = true -> Equivb cmp m n.
  Proof. apply equal_iff. Qed.

  Lemma elements_iff {A} k (v : A k) (m : t A) :
    MapsTo k v m <-> List.In (existT A k v) (elements m).
  Proof.
    unfold MapsTo, elements. split.
    - intros Hmap. apply Raw.elements_1, InA_alt in Hmap.
      destruct Hmap as [[j entry] [[Hkey Hvalue] Hin]].
      apply in_map_iff. exists (j, entry). split; [symmetry; exact Hvalue|exact Hin].
    - intros Hin. apply in_map_iff in Hin.
      destruct Hin as [[j entry] [Hvalue Hin]]. cbn in Hvalue. subst entry.
      assert (Hmap : Raw.MapsTo j (existT A k v) (raw m)).
      { apply Raw.elements_2, InA_alt. exists (j, existT A k v).
        split; [split; reflexivity|exact Hin]. }
      pose proof (well_formed m j _ Hmap) as Hkey. cbn in Hkey. now subst j.
  Qed.

  Lemma elements_1 {A} k (v : A k) (m : t A) :
    MapsTo k v m -> List.In (existT A k v) (elements m).
  Proof. apply elements_iff. Qed.

  Lemma elements_2 {A} k (v : A k) (m : t A) :
    List.In (existT A k v) (elements m) -> MapsTo k v m.
  Proof. apply elements_iff. Qed.

  Lemma elements_3w {A} (m : t A) :
    NoDup (List.map (@projT1 key A) (elements m)).
  Proof.
    unfold elements. rewrite map_map.
    assert (Hkeys :
      List.map (fun entry => projT1 (snd entry)) (Raw.elements (raw m)) =
      List.map fst (Raw.elements (raw m))).
    { apply map_ext_in. intros [k entry] Hin. cbn.
      apply (well_formed m k entry), Raw.elements_2, InA_alt.
      exists (k, entry). split; [split; reflexivity | exact Hin]. }
    rewrite Hkeys. clear Hkeys. pose proof (Raw.elements_3w (raw m)) as Hnodup.
    induction Hnodup as [|[k entry] entries Hnot Hnodup IH]; cbn; constructor; auto.
    intros Hin. apply Hnot, InA_alt. apply in_map_iff in Hin.
    destruct Hin as [[j other] [Heq Hin]]. cbn in Heq. subst j.
    exists (k, other). split; [reflexivity | exact Hin].
  Qed.

  Lemma cardinal_1 {A} (m : t A) : cardinal m = length (elements m).
  Proof. unfold cardinal, elements. rewrite length_map. apply Raw.cardinal_1. Qed.

  Lemma fold_1 {A B} (f : forall k, A k -> B -> B) (m : t A) init :
    fold f m init =
      fold_left (fun acc entry => f (projT1 entry) (projT2 entry) acc) (elements m) init.
  Proof.
    unfold fold, elements. rewrite Raw.fold_1.
    generalize (Raw.elements (raw m)), init. intros entries.
    induction entries as [|[k entry] rest IH]; intros acc; cbn; auto.
  Qed.
End Make.

Module StringDepMap := Make(OrdersEx.String_as_OT).
Module NDepMap := Make(OrdersEx.N_as_OT).
Module PositiveDepMap := Make(OrdersEx.Positive_as_OT).
