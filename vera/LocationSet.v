From Stdlib Require Import NArith.
From Stdlib Require Import BinNat.
From Stdlib Require Import FMapAVL.
From Stdlib Require Import FMapFacts.
From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Structures.Orders.
From Stdlib Require Import Structures.OrderedType.
From Stdlib Require Import MSetInterface.
From Stdlib Require Import Lia.

From vera Require Import Verilog.

Module Location.
  Record t := Mk {
    var : Verilog.variable;
    idx : N;
  }.

  Module as_MDT <: MiniDecidableType.
    Definition t := Location.t.
    Definition eq_dec (x y : t) : {x=y} + {x<>y}.
    Proof.
      destruct x as [vx ix], y as [vy iy].
      destruct (Verilog.Variable_as_DT.eq_dec vx vy).
      - destruct (N.eq_dec ix iy).
        + left. subst. reflexivity.
        + right. congruence.
      - right. congruence.
    Qed.
  End as_MDT.

  Module as_DT := Make_UDT(as_MDT).
End Location.

(* The core map: Variable.t -> N (bitmask) *)
Module VarMap_OT.
  Definition t := Verilog.variable.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_dec := Verilog.Variable_as_DT.eq_dec.
  Definition lt := Verilog.Variable_as_OT.lt.
  Definition lt_trans x y z := @StrictOrder_Transitive _ _ Verilog.Variable_as_OT.lt_strorder x y z.
  Definition lt_not_eq : forall x y, lt x y -> ~ eq x y.
  Proof. intros x y Hlt Heq. rewrite Heq in Hlt. exact (@StrictOrder_Irreflexive _ _ Verilog.Variable_as_OT.lt_strorder y Hlt). Qed.
  Definition compare (x y : t) : Compare lt eq x y.
  Proof.
    destruct (Verilog.Variable_as_OT.compare x y) eqn:E.
    - apply EQ. destruct (Verilog.Variable_as_OT.compare_spec x y); [exact H | discriminate E | discriminate E].
    - apply LT. destruct (Verilog.Variable_as_OT.compare_spec x y); [discriminate E | exact H | discriminate E].
    - apply GT. destruct (Verilog.Variable_as_OT.compare_spec x y); [discriminate E | discriminate E | exact H].
  Defined.
  #[global] Instance eq_equiv : Equivalence eq := eq_equivalence.
  #[global] Instance lt_strorder : StrictOrder lt := Verilog.Variable_as_OT.lt_strorder.
  #[global] Instance lt_compat : Proper (eq ==> eq ==> iff) lt := Verilog.Variable_as_OT.lt_compat.
End VarMap_OT.

Module VarMap := FMapAVL.Make(VarMap_OT).
Module VarMapFacts := FMapFacts.WFacts(VarMap).

Print WSets.

Module LocSet <: WSets.
  (* TODO: This allows bitmasks with out-of-bounds bits set. We need the following well-formedness property:
     forall var mask, VarMap.MapsTo var mask masks -> (mask <= N.ones (Verilog.varType v))%N.
  *)
  Definition t := VarMap.t N.
  Module E := Location.as_DT.
  Definition elt := E.t.
  
  Definition empty : t := VarMap.empty N.
  
  Definition mem (loc : elt) (s : t) : bool :=
    match VarMap.find loc.(Location.var) s with
    | Some mask => N.testbit mask loc.(Location.idx)
    | None => false
    end.
  
  Definition In (loc : elt) (s : t) : Prop := mem loc s = true.
  
  Definition add (loc : elt) (s : t) : t :=
    let mask := match VarMap.find loc.(Location.var) s with
                | Some m => N.lor m (N.shiftl 1 loc.(Location.idx))
                | None => N.shiftl 1 loc.(Location.idx)
                end in
    VarMap.add loc.(Location.var) mask s.

  Definition add_variable (v : Verilog.variable) (s : t) : t :=
    VarMap.add v (N.ones (Verilog.varType v)) s.
  
  Definition union (s1 s2 : t) : t :=
    VarMap.map2 (fun o1 o2 =>
      match o1, o2 with
      | Some m1, Some m2 => Some (N.lor m1 m2)
      | Some m1, None => Some m1
      | None, Some m2 => Some m2
      | None, None => None
      end) s1 s2.
  
  Definition inter (s1 s2 : t) : t :=
    VarMap.map2 (fun o1 o2 =>
      match o1, o2 with
      | Some m1, Some m2 =>
          let m := N.land m1 m2 in
          if N.eqb m 0 then None else Some m
      | _, _ => None
      end) s1 s2.
  
  Definition subset (s1 s2 : t) : bool :=
    VarMap.fold (fun v m1 acc =>
      acc && match VarMap.find v s2 with
             | Some m2 => N.eqb (N.land m1 m2) m1
             | None => N.eqb m1 0
             end
    ) s1 true.
  
  Lemma union_spec : forall (s s' : t) (x : elt), In x (union s s') <-> In x s \/ In x s'.
  Proof.
    intros s s' x. unfold In, mem, union.
    rewrite VarMapFacts.map2_1bis; [| reflexivity].
    destruct (VarMap.find (Location.var x) s) as [m1|] eqn:E1;
    destruct (VarMap.find (Location.var x) s') as [m2|] eqn:E2.
    - rewrite N.lor_spec. rewrite orb_true_iff. reflexivity.
    - split; intros H; [left|destruct H; [|discriminate]]; exact H.
    - split; intros H; [right|destruct H; [discriminate|]]; exact H.
    - split; intros H; [discriminate|destruct H; discriminate H].
  Qed.
  
  Definition Subset (s1 s2 : t) := forall x, In x s1 -> In x s2.
  Definition Equal (s1 s2 : t) : Prop := forall x, In x s1 <-> In x s2.
  Definition Empty (s : t) : Prop := forall x, ~ In x s.
  Definition For_all (P : elt -> Prop) (s : t) : Prop := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s : t) : Prop := exists x, In x s /\ P x.
  Definition eq := Equal.

  Definition is_empty (s:t) : bool :=
    VarMap.fold (fun v m acc => acc && N.eqb m 0) s true.
  
  Definition singleton (x:elt) : t :=
    VarMap.add x.(Location.var) (N.shiftl 1 x.(Location.idx)) empty.
    
  Definition remove (x:elt) (s:t) : t :=
    match VarMap.find x.(Location.var) s with
    | Some mask =>
        let new_mask := N.clearbit mask x.(Location.idx) in
        if N.eqb new_mask 0 then VarMap.remove x.(Location.var) s
        else VarMap.add x.(Location.var) new_mask s
    | None => s
    end.
    
  Definition diff (s1 s2:t) : t :=
    VarMap.map2 (fun o1 o2 =>
      match o1, o2 with
      | Some m1, Some m2 =>
          let m := N.ldiff m1 m2 in
          if N.eqb m 0 then None else Some m
      | Some m1, None => Some m1
      | None, _ => None
      end
    ) s1 s2.
    
  Definition equal (s1 s2:t) : bool :=
    subset s1 s2 && subset s2 s1.

  Definition extract_bits (n : N) : list N :=
    let sz := N.to_nat (N.size n) in
    let fix loop (k : nat) :=
      match k with
      | 0%nat => nil
      | S k' => if N.testbit n (N.of_nat k') then N.of_nat k' :: loop k' else loop k'
      end
    in loop sz.

  Definition elements (s:t) : list elt :=
    VarMap.fold (fun v n acc =>
      List.map (fun i => Location.Mk v i) (extract_bits n) ++ acc
    ) s nil.

  Definition fold (A:Type) (f:elt -> A -> A) (s:t) (i:A) : A :=
    List.fold_left (fun a e => f e a) (elements s) i.

  Definition for_all (f:elt -> bool) (s:t) : bool :=
    fold bool (fun x acc => acc && f x) s true.

  Definition exists_ (f:elt -> bool) (s:t) : bool :=
    fold bool (fun x acc => acc || f x) s false.

  Definition filter (f:elt -> bool) (s:t) : t :=
    fold t (fun x acc => if f x then add x acc else acc) s empty.

  Definition partition (f:elt -> bool) (s:t) : t * t :=
    fold (t * t) (fun x '(a, b) => if f x then (add x a, b) else (a, add x b)) s (empty, empty).

  Definition cardinal (s:t) : nat :=
    List.length (elements s).

  Definition choose (s:t) : option elt :=
    match elements s with
    | nil => None
    | x :: _ => Some x
    end.

  Lemma In_compat : Proper (E.eq ==> Logic.eq ==> iff) In.
  Proof.
    intros x y Hxy s1 s2 Hs. subst s2.
    unfold E.eq in Hxy. subst y. reflexivity.
  Qed.

  Lemma eq_equiv : Equivalence Equal.
  Proof.
    split.
    - unfold Reflexive, Equal. tauto.
    - unfold Symmetric, Equal. intros x y H z. rewrite H. tauto.
    - unfold Transitive, Equal. intros x y z H1 H2 w. rewrite H1, H2. tauto.
  Qed.

  Lemma mem_spec : forall (s : t) (x : elt), mem x s = true <-> In x s.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma fold_left_andb_false : forall (l : list (VarMap.key * N)) f,
    List.fold_left (fun a p => a && f (fst p) (snd p)) l false = false.
  Proof.
    induction l; intros; [reflexivity | simpl; apply IHl].
  Qed.

  Lemma fold_left_andb_true : forall (l : list (VarMap.key * N)) (f : VarMap.key -> N -> bool),
    List.fold_left (fun a p => a && f (fst p) (snd p)) l true = true <->
    (forall k v, List.In (k, v) l -> f k v = true).
  Proof.
    induction l as [| [k v] l IH]; intros f.
    - split; intros H; [intros k' v' HIn; destruct HIn | reflexivity].
    - simpl. split; intros H.
      + intros k' v' [HIn | HIn].
        * inversion HIn. subst k' v'.
          destruct (f k v) eqn:E; [reflexivity | rewrite fold_left_andb_false in H; discriminate H].
        * destruct (f k v) eqn:E; [destruct (IH f) as [IH1 _]; apply (IH1 H k' v' HIn) | rewrite fold_left_andb_false in H; discriminate H].
      + destruct (IH f) as [_ IH2]. assert (f k v = true) as E by (apply H; left; reflexivity).
        rewrite E. simpl. apply IH2. intros k' v' HIn. apply H. right. exact HIn.
  Qed.

  Lemma InA_eq_key_elt_In : forall k v l,
    InA (@VarMap.eq_key_elt N) (k, v) l -> List.In (k, v) l.
  Proof.
    intros k v l. induction l as [| [k' v'] l IH]; intros H.
    - inversion H.
    - inversion H; subst.
      + unfold VarMap.eq_key_elt in H1. destruct H1 as [Hk Hv]. simpl in Hk, Hv.
        unfold E.eq in Hk. subst. left. reflexivity.
      + right. apply IH. exact H1.
  Qed.

  Lemma In_InA_eq_key_elt : forall k v l,
    List.In (k, v) l -> InA (@VarMap.eq_key_elt N) (k, v) l.
  Proof.
    intros k v l H. induction l as [| [k' v'] l IH].
    - destruct H.
    - destruct H as [H|H].
      + inversion H. left. unfold VarMap.eq_key_elt. simpl.
        split; reflexivity.
      + right. apply IH. exact H.
  Qed.

  Lemma fold_andb_true : forall (f : VarMap.key -> N -> bool) (m : t),
    VarMap.fold (fun k v acc => acc && f k v) m true = true <->
    (forall k v, VarMap.MapsTo k v m -> f k v = true).
  Proof.
    intros f m.
    rewrite VarMap.fold_1.
    rewrite fold_left_andb_true.
    split; intros H k v HMap.
    - apply H. apply VarMap.elements_1 in HMap.
      apply InA_eq_key_elt_In in HMap. exact HMap.
    - apply H. apply VarMap.elements_2.
      apply In_InA_eq_key_elt. exact HMap.
  Qed.

  Lemma land_eq_m1_iff : forall m1 m2,
    (forall idx, N.testbit m1 idx = true -> N.testbit m2 idx = true) <-> N.land m1 m2 = m1.
  Proof.
    intros m1 m2. split; intros H.
    - apply N.bits_inj. intros idx. rewrite N.land_spec.
      destruct (N.testbit m1 idx) eqn:E.
      + rewrite (H idx E). reflexivity.
      + apply Bool.andb_false_l.
    - intros idx H1. apply N.bits_inj_iff in H. specialize (H idx).
      rewrite N.land_spec in H. rewrite H1 in H.
      destruct (N.testbit m2 idx); [reflexivity | discriminate H].
  Qed.

  Lemma m1_0_iff : forall m1,
    (forall idx, N.testbit m1 idx = true -> False) <-> m1 = 0%N.
  Proof.
    intros m1. split; intros H.
    - apply N.bits_inj. intros idx. rewrite N.bits_0.
      destruct (N.testbit m1 idx) eqn:E; [exfalso; apply (H idx E) | reflexivity].
    - intros idx H1. subst m1. rewrite N.bits_0 in H1. discriminate H1.
  Qed.

  Lemma subset_spec : forall s s' : t, subset s s' = true <-> Subset s s'.
  Proof.
    intros s s'. unfold subset. rewrite fold_andb_true. split; intros H.
    - intros [v idx] HIn. unfold In, mem in *. simpl in HIn.
      destruct (VarMap.find v s) as [m1|] eqn:E1; [|discriminate HIn].
      apply VarMap.find_2 in E1. specialize (H v m1 E1).
      destruct (VarMap.find v s') as [m2|] eqn:E2.
      + unfold In, mem. simpl. rewrite E2. apply N.eqb_eq in H. rewrite <- land_eq_m1_iff in H.
        apply (H idx). exact HIn.
      + apply N.eqb_eq in H. rewrite <- m1_0_iff in H.
        exfalso. apply (H idx HIn).
    - intros v m1 E1. apply VarMap.find_1 in E1.
      destruct (VarMap.find v s') as [m2|] eqn:E2.
      + apply N.eqb_eq. apply land_eq_m1_iff. intros idx H1.
        assert (HIn : In (Location.Mk v idx) s).
        { unfold In, mem. simpl. rewrite E1. exact H1. }
        apply H in HIn. unfold In, mem in HIn. simpl in HIn. rewrite E2 in HIn. exact HIn.
      + apply N.eqb_eq. apply m1_0_iff. intros idx H1.
        assert (HIn : In (Location.Mk v idx) s).
        { unfold In, mem. simpl. rewrite E1. exact H1. }
        apply H in HIn. unfold In, mem in HIn. simpl in HIn. rewrite E2 in HIn. discriminate HIn.
  Qed.

  Lemma equal_spec : forall s s' : t, equal s s' = true <-> Equal s s'.
  Proof.
    intros s s'. unfold equal, Equal.
    rewrite Bool.andb_true_iff.
    rewrite subset_spec, subset_spec.
    unfold Subset. split; intros H.
    - destruct H as [H1 H2]. intros x. split; intros Hx.
      + apply H1. exact Hx.
      + apply H2. exact Hx.
    - split; intros x Hx.
      + apply H. exact Hx.
      + apply H. exact Hx.
  Qed.

  Lemma empty_spec : Empty empty.
  Proof.
    unfold Empty, In, mem, empty.
    intros [vx ix]. simpl.
    discriminate.
  Qed.

  Lemma is_empty_spec : forall s : t, is_empty s = true <-> Empty s.
  Proof.
    intros s. unfold is_empty, Empty.
    rewrite fold_andb_true. split; intros H.
    - intros [v idx] HIn. unfold In, mem in HIn. simpl in HIn.
      destruct (VarMap.find v s) as [m|] eqn:E; [|discriminate HIn].
      apply VarMap.find_2 in E. specialize (H v m E).
      apply N.eqb_eq in H. rewrite <- m1_0_iff in H.
      apply (H idx). exact HIn.
    - intros v m E. apply VarMap.find_1 in E.
      apply N.eqb_eq. apply m1_0_iff. intros idx HIn.
      apply (H (Location.Mk v idx)). unfold In, mem. simpl. rewrite E. exact HIn.
  Qed.

  Lemma shiftl_1_testbit_true : forall a b, N.testbit (N.shiftl 1 a) b = true <-> a = b.
  Proof.
    intros. rewrite N.shiftl_1_l. rewrite N.pow2_bits_eqb. apply N.eqb_eq.
  Qed.

  Lemma add_spec : forall (s : t) (x y : elt), In y (add x s) <-> E.eq y x \/ In y s.
  Proof.
    intros s [vx ix] [vy iy]. unfold In, mem, add, E.eq. simpl.
    destruct (Verilog.Variable_as_DT.eq_dec vy vx).
    - subst vy. rewrite VarMapFacts.add_eq_o; [|reflexivity].
      destruct (VarMap.find vx s) as [m|] eqn:E.
      + rewrite N.lor_spec. split; intros H.
        * apply Bool.orb_prop in H. destruct H as [H|H]; [right; exact H | left; apply shiftl_1_testbit_true in H; subst iy; reflexivity].
        * destruct H as [H|H]; [inversion H; subst iy; apply Bool.orb_true_iff; right; apply shiftl_1_testbit_true; reflexivity | apply Bool.orb_true_iff; left; exact H].
      + split; intros H.
        * left. apply shiftl_1_testbit_true in H. subst iy. reflexivity.
        * destruct H as [H|H]; [inversion H; subst iy; apply shiftl_1_testbit_true; reflexivity | discriminate H].
    - rewrite VarMapFacts.add_neq_o; [|intros Heq; apply n; symmetry; exact Heq].
      split; intros H; [right; exact H | destruct H as [H|H]; [exfalso; apply n; inversion H; reflexivity | exact H]].
  Qed.

  Lemma add_variable_spec : forall (s : t) v (loc : elt),
    (loc.(Location.idx) < Verilog.varType v)%N -> (* TODO : this should be added to the definition of t *)
    In loc (add_variable v s) <-> loc.(Location.var) = v \/ In loc s.
  Proof.
    intros s var [var' idx']. unfold In, mem, add, E.eq, add_variable. simpl.
    destruct (Verilog.Variable_as_DT.eq_dec var' var).
    - subst var'.
      erewrite VarMap.find_1 by now apply VarMap.add_1.
      destruct (N.ltb idx' (Verilog.varType var)) eqn:E.
      + apply N.ltb_lt in E.
        rewrite N.ones_spec_low by assumption.
	intuition.
      + apply N.ltb_ge in E.
        rewrite N.ones_spec_high by assumption.
	intuition lia.
    - rewrite VarMapFacts.add_neq_o by auto.
      intuition.
  Qed.

  Lemma remove_spec : forall (s : t) (x y : elt), In y (remove x s) <-> In y s /\ ~ E.eq y x.
  Proof.
    intros s [vx ix] [vy iy]. unfold In, mem, remove, E.eq. simpl.
    destruct (VarMap.find vx s) as [m|] eqn:E; [|destruct (VarMap.find vy s) as [m2|] eqn:E2; split; intros H; [split; [exact H|intros Heq; inversion Heq; subst; rewrite E in E2; discriminate E2] | destruct H as [H _]; exact H | discriminate H | destruct H as [H _]; discriminate H]].
    destruct (Verilog.Variable_as_DT.eq_dec vy vx).
    - subst vy. destruct (N.eqb (N.clearbit m ix) 0) eqn:Eq0.
      + rewrite VarMapFacts.remove_eq_o; [|reflexivity].
        split; intros H; [discriminate H|].
        destruct H as [H1 Hneq]. unfold In, mem in H1. simpl in H1. rewrite E in H1.
        apply N.eqb_eq in Eq0. assert (Htest: N.testbit (N.clearbit m ix) iy = true).
        { rewrite N.clearbit_eqb. rewrite H1. destruct (N.eqb ix iy) eqn:Eqb; [|reflexivity].
          apply N.eqb_eq in Eqb. exfalso. apply Hneq. subst iy. reflexivity. }
        rewrite Eq0 in Htest. rewrite N.bits_0 in Htest. discriminate Htest.
      + rewrite VarMapFacts.add_eq_o; [|reflexivity].
        rewrite N.clearbit_eqb. split; intros H.
        * apply Bool.andb_true_iff in H. destruct H as [H1 H2]. split; [rewrite E; exact H1 | intros Heq; inversion Heq; subst iy; apply Bool.negb_true_iff in H2; apply N.eqb_neq in H2; apply H2; reflexivity].
        * destruct H as [H1 Hneq]. apply Bool.andb_true_iff. split; [rewrite E in H1; exact H1 | apply Bool.negb_true_iff; apply N.eqb_neq; intros H2; apply Hneq; subst iy; reflexivity].
    - destruct (N.eqb (N.clearbit m ix) 0) eqn:Eq0.
      + rewrite VarMapFacts.remove_neq_o; [|intro Heq; apply n; auto]. destruct (VarMap.find vy s) as [m2|] eqn:E2; split; intros H; [split; [exact H | intros Heq; inversion Heq; subst; apply n; reflexivity] | destruct H as [H _]; exact H | discriminate H | destruct H as [H _]; discriminate H].
      + rewrite VarMapFacts.add_neq_o; [|intro Heq; apply n; auto]. destruct (VarMap.find vy s) as [m2|] eqn:E2; split; intros H; [split; [exact H | intros Heq; inversion Heq; subst; apply n; reflexivity] | destruct H as [H _]; exact H | discriminate H | destruct H as [H _]; discriminate H].
  Qed.

  Lemma singleton_spec : forall x y : elt, In y (singleton x) <-> E.eq y x.
  Proof.
    intros [vx ix] [vy iy]. unfold In, mem, singleton, E.eq. simpl.
    destruct (Verilog.Variable_as_DT.eq_dec vy vx).
    - subst vy. rewrite VarMapFacts.add_eq_o; [|reflexivity].
      split; intros H.
      + apply shiftl_1_testbit_true in H. subst iy. reflexivity.
      + inversion H. apply shiftl_1_testbit_true. reflexivity.
    - rewrite VarMapFacts.add_neq_o; [|intro Heq; apply n; auto].
      rewrite VarMapFacts.empty_o. split; intros H.
      + discriminate H.
      + inversion H. exfalso. apply n. exact H1.
  Qed.

  Lemma inter_spec : forall (s s' : t) (x : elt), In x (inter s s') <-> In x s /\ In x s'.
  Proof.
    intros s s' [vx ix]. unfold In, mem, inter. simpl.
    destruct (VarMap.find vx s) as [m1|] eqn:E1; destruct (VarMap.find vx s') as [m2|] eqn:E2.
    - rewrite (VarMap.map2_1 (fun o1 o2 => match o1, o2 with Some m1, Some m2 => let m := N.land m1 m2 in if N.eqb m 0 then None else Some m | _, _ => None end)); [|left; apply VarMap.find_2 in E1; exists m1; exact E1].
      rewrite E1, E2. simpl. destruct (N.eqb (N.land m1 m2) 0) eqn:Eq0.
      + split; intros H; [discriminate H|].
        destruct H as [H1 H2]. apply N.eqb_eq in Eq0.
        assert (H: N.testbit (N.land m1 m2) ix = true) by (rewrite N.land_spec; rewrite H1, H2; reflexivity).
        rewrite Eq0 in H. rewrite N.bits_0 in H. discriminate H.
      + rewrite N.land_spec. split; intros H; [apply Bool.andb_true_iff in H; destruct H as [H1 H2]; split; [exact H1|exact H2] | destruct H as [H1 H2]; apply Bool.andb_true_iff; split; assumption].
    - rewrite (VarMap.map2_1 (fun o1 o2 => match o1, o2 with Some m1, Some m2 => let m := N.land m1 m2 in if N.eqb m 0 then None else Some m | _, _ => None end)); [|left; apply VarMap.find_2 in E1; exists m1; exact E1].
      rewrite E1, E2. simpl. split; intros H; [discriminate H | destruct H as [_ H]; discriminate H].
    - rewrite (VarMap.map2_1 (fun o1 o2 => match o1, o2 with Some m1, Some m2 => let m := N.land m1 m2 in if N.eqb m 0 then None else Some m | _, _ => None end)); [|right; apply VarMap.find_2 in E2; exists m2; exact E2].
      rewrite E1. simpl. split; intros H; [discriminate H | destruct H as [H _]; discriminate H].
    - destruct (VarMap.find vx (VarMap.map2 (fun o1 o2 => match o1, o2 with Some m1, Some m2 => let m := N.land m1 m2 in if N.eqb m 0 then None else Some m | _, _ => None end) s s')) eqn:E.
      + apply VarMap.find_2 in E. assert (HIn: VarMap.In vx (VarMap.map2 _ s s')) by (exists n; exact E).
        apply VarMap.map2_2 in HIn. destruct HIn as [[m H]|[m H]]; apply VarMap.find_1 in H; [rewrite H in E1|rewrite H in E2]; discriminate.
      + split; intros H; [discriminate H | destruct H as [H _]; discriminate H].
  Qed.

  Lemma diff_spec : forall (s s' : t) (x : elt), In x (diff s s') <-> In x s /\ ~ In x s'.
  Proof.
    intros s s' [vx ix]. unfold In, mem, diff. simpl.
    destruct (VarMap.find vx s) as [m1|] eqn:E1; destruct (VarMap.find vx s') as [m2|] eqn:E2.
    - rewrite (VarMap.map2_1 (fun o1 o2 => match o1, o2 with Some m1, Some m2 => let m := N.ldiff m1 m2 in if N.eqb m 0 then None else Some m | Some m1, None => Some m1 | None, _ => None end)); [|left; apply VarMap.find_2 in E1; exists m1; exact E1].
      rewrite E1, E2. simpl. destruct (N.eqb (N.ldiff m1 m2) 0) eqn:Eq0.
      + split; intros H; [discriminate H|].
        destruct H as [H1 H2]. apply N.eqb_eq in Eq0.
        assert (H: N.testbit (N.ldiff m1 m2) ix = true) by (rewrite N.ldiff_spec; rewrite H1; destruct (N.testbit m2 ix) eqn:Htest; [exfalso; apply H2; reflexivity | reflexivity]).
        rewrite Eq0 in H. rewrite N.bits_0 in H. discriminate H.
      + rewrite N.ldiff_spec. split; intros H; [apply Bool.andb_true_iff in H; destruct H as [H1 Htest]; apply Bool.negb_true_iff in Htest; split; [exact H1 | intros H3; rewrite H3 in Htest; discriminate Htest] | destruct H as [H1 H2]; apply Bool.andb_true_iff; split; [exact H1 | apply Bool.negb_true_iff; destruct (N.testbit m2 ix) eqn:Htest; [exfalso; apply H2; reflexivity | reflexivity]]].
    - rewrite (VarMap.map2_1 (fun o1 o2 => match o1, o2 with Some m1, Some m2 => let m := N.ldiff m1 m2 in if N.eqb m 0 then None else Some m | Some m1, None => Some m1 | None, _ => None end)); [|left; apply VarMap.find_2 in E1; exists m1; exact E1].
      rewrite E1, E2. simpl. split; intros H; [split; [exact H | intros H2; discriminate H2] | destruct H as [H1 H2]; exact H1].
    - rewrite (VarMap.map2_1 (fun o1 o2 => match o1, o2 with Some m1, Some m2 => let m := N.ldiff m1 m2 in if N.eqb m 0 then None else Some m | Some m1, None => Some m1 | None, _ => None end)); [|right; apply VarMap.find_2 in E2; exists m2; exact E2].
      rewrite E1. simpl. split; intros H; [discriminate H | destruct H as [H1 _]; discriminate H1].
    - destruct (VarMap.find vx (VarMap.map2 _ s s')) eqn:E; [|split; intros H; [discriminate H | destruct H as [H1 _]; discriminate H1]].
      apply VarMap.find_2 in E. assert (HIn: VarMap.In vx (VarMap.map2 _ s s')) by (exists n; exact E).
      apply VarMap.map2_2 in HIn. destruct HIn as [[m H]|[m H]]; apply VarMap.find_1 in H; [rewrite H in E1|rewrite H in E2]; discriminate.
  Qed.

  Lemma fold_spec : forall (s : t) (A : Type) (i : A) (f : elt -> A -> A), fold A f s i = fold_left (flip f) (elements s) i.
  Proof. intros s A i f. reflexivity. Qed.

  Lemma cardinal_spec : forall s : t, cardinal s = length (elements s).
  Proof. intros s. unfold cardinal. reflexivity. Qed.

  Lemma extract_bits_loop_spec : forall (n : N) (k : nat) (ix : N),
    List.In ix ((fix loop (k0 : nat) : list N :=
               match k0 with
               | 0%nat => nil
               | S k' =>
                   if N.testbit n (N.of_nat k')
                   then N.of_nat k' :: loop k'
                   else loop k'
               end) k) <->
    (N.testbit n ix = true /\ (ix < N.of_nat k)%N).
  Proof.
    intros n k ix. induction k as [|k' IH].
    - simpl. split.
      + intros H. contradiction H.
      + intros [H1 H2]. lia.
    - destruct (N.testbit n (N.of_nat k')) eqn:E.
      + split; intros H.
        * destruct H as [H | H].
          -- subst ix. split; [exact E | lia].
          -- apply IH in H. destruct H as [H1 H2]. split; [exact H1 | lia].
        * destruct H as [H1 H2].
          assert (H_cases : (ix < N.of_nat k')%N \/ ix = N.of_nat k') by lia.
          destruct H_cases as [H_lt | H_eq].
          -- right. apply IH. split; [exact H1 | exact H_lt].
          -- left. symmetry. exact H_eq.
      + split; intros H.
        * apply IH in H. destruct H as [H1 H2]. split; [exact H1 | lia].
        * destruct H as [H1 H2].
          assert (H_cases : (ix < N.of_nat k')%N \/ ix = N.of_nat k') by lia.
          destruct H_cases as [H_lt | H_eq].
          -- apply IH. split; [exact H1 | exact H_lt].
          -- subst ix. rewrite H1 in E. discriminate E.
  Qed.

  Lemma extract_bits_spec : forall (n:N) (ix:N), List.In ix (extract_bits n) <-> N.testbit n ix = true.
  Proof.
    intros n ix. unfold extract_bits. rewrite extract_bits_loop_spec.
    split; intros H.
    - destruct H as [H1 _]. exact H1.
    - split; [exact H|].
      rewrite N2Nat.id.
      destruct (N.eq_dec n 0) as [Eq | Neq].
      + subst n. rewrite N.bits_0 in H. discriminate H.
      + assert (H_not: ~ (N.log2 n < ix)%N).
        { intros Hlt. apply N.bits_above_log2 in Hlt. rewrite H in Hlt. discriminate Hlt. }
        apply N.nlt_ge in H_not.
        rewrite N.size_log2; [|exact Neq].
        apply N.le_lt_trans with (m := N.log2 n).
        * exact H_not.
        * apply N.lt_succ_diag_r.
  Qed.

  Lemma extract_bits_loop_NoDup : forall (n : N) (k : nat),
    NoDup ((fix loop (k0 : nat) : list N :=
               match k0 with
               | 0%nat => nil
               | S k' =>
                   if N.testbit n (N.of_nat k')
                   then N.of_nat k' :: loop k'
                   else loop k'
               end) k).
  Proof.
    intros n k. induction k as [|k' IH].
    - simpl. apply NoDup_nil.
    - destruct (N.testbit n (N.of_nat k')) eqn:E.
      + apply NoDup_cons; [|exact IH].
        intros H. apply extract_bits_loop_spec in H. destruct H as [_ H]. lia.
      + exact IH.
  Qed.

  Lemma extract_bits_NoDup : forall n, NoDup (extract_bits n).
  Proof. intros n. unfold extract_bits. apply extract_bits_loop_NoDup. Qed.

  Lemma InA_elements_fold_gen : forall l x acc,
    InA E.eq x (List.fold_left (fun a p => List.map (fun i => Location.Mk (fst p) i) (extract_bits (snd p)) ++ a) l acc) <->
    InA E.eq x acc \/ (exists p, List.In p l /\ fst p = Location.var x /\ N.testbit (snd p) (Location.idx x) = true).
  Proof.
    intros l x. induction l as [|p l' IH]; intros acc.
    - simpl. split.
      + intros H. left. exact H.
      + intros [H | [p_bad [H _]]].
        * exact H.
        * destruct H.
    - simpl. rewrite IH. rewrite InA_app_iff.
      split; intros H.
      + destruct H as [[H | H] | [p0 [HIn Hrest]]].
        * right. exists p. split; [left; reflexivity |].
          apply InA_alt in H. destruct H as [y [Heq HIn]].
          apply in_map_iff in HIn. destruct HIn as [i [Hy Hi]].
          subst y. unfold E.eq in Heq. destruct x as [vx ix]. simpl in *.
          injection Heq as Hvx Hix. subst vx.
          split; [reflexivity |].
          apply extract_bits_spec.
          rewrite Hix. exact Hi.
        * left. exact H.
        * right. exists p0. split; [right; exact HIn | exact Hrest].
      + destruct H as [H | [p0 [HIn Hrest]]].
        * left. right. exact H.
        * destruct HIn as [HIn | HIn].
          -- left. left. subst p0. destruct x as [vx ix]. destruct Hrest as [Hvx Hix].
             simpl in Hvx. subst vx.
             apply InA_alt. exists {| Location.var := fst p; Location.idx := ix |}.
             split.
             ++ reflexivity.
             ++ apply in_map_iff. exists ix. split; [reflexivity |].
                apply extract_bits_spec. exact Hix.
          -- right. exists p0. split; [exact HIn | exact Hrest].
  Qed.

  Lemma elements_spec1 : forall (s : t) (x : elt), InA E.eq x (elements s) <-> In x s.
  Proof.
    intros s x. unfold elements. rewrite VarMap.fold_1.
    rewrite InA_elements_fold_gen.
    split; intros H.
    - destruct H as [H | [[k v] [HIn [Heq Htest]]]].
      + inversion H.
      + apply In_InA_eq_key_elt in HIn. apply VarMap.elements_2 in HIn.
        apply VarMap.find_1 in HIn.
        unfold In, mem. simpl in Heq. rewrite Heq in HIn. rewrite HIn. exact Htest.
    - unfold In, mem in H. destruct (VarMap.find (Location.var x) s) as [m|] eqn:E; [|discriminate H].
      apply VarMap.find_2 in E. apply VarMap.elements_1 in E.
      apply InA_eq_key_elt_In in E.
      right. exists (Location.var x, m). split; [exact E | split; [reflexivity | exact H]].
  Qed.

  Lemma NoDup_elements_fold_gen : forall l acc,
    NoDup acc ->
    (forall x, List.In x acc -> forall p, List.In p l -> fst p <> Location.var x) ->
    NoDupA (@VarMap.eq_key N) l ->
    NoDup (List.fold_left (fun a p => List.map (fun i => Location.Mk (fst p) i) (extract_bits (snd p)) ++ a) l acc).
  Proof.
    intros l. induction l as [|p l' IH]; intros acc Hacc Hdisj Hnodup.
    - simpl. exact Hacc.
    - simpl. inversion Hnodup as [| ? ? HnotIn Hnodup']. subst. apply IH.
      + apply NoDup_app.
        * apply FinFun.Injective_map_NoDup.
          -- intros i j Heq. injection Heq as Hidx. exact Hidx.
          -- apply extract_bits_NoDup.
        * exact Hacc.
        * intros x Hmap Hacc_in. apply in_map_iff in Hmap. destruct Hmap as [i [Heq Hi]].
          subst x. assert (Hcontra := Hdisj {| Location.var := fst p; Location.idx := i |} Hacc_in p).
          simpl in Hcontra. apply Hcontra.
          -- left. reflexivity.
          -- reflexivity.
      + intros x H_in p0 Hp0. apply in_app_iff in H_in. destruct H_in as [H_in | H_in].
        * apply in_map_iff in H_in. destruct H_in as [i [Heq Hi]]. subst x.
          simpl. intros H_eq.
          destruct p0 as [k v]. simpl in *. subst k.
          apply HnotIn.
          clear - Hp0. induction l' as [|p1 l1 IHl1].
          -- destruct Hp0.
          -- destruct Hp0 as [H1 | H1].
             ++ subst p1. constructor 1. unfold VarMap.eq_key, VarMap.Raw.Proofs.PX.eqk. simpl. reflexivity.
             ++ constructor 2. apply IHl1. exact H1.
        * apply Hdisj; [exact H_in | right; exact Hp0].
      + exact Hnodup'.
  Qed.

  Lemma NoDup_NoDupA_eq : forall l, NoDup l -> NoDupA E.eq l.
  Proof.
    intros l. induction l as [|e l' IH].
    - intros _. apply NoDupA_nil.
    - intros H. inversion H; subst. constructor 2.
      + intros HIn. apply InA_alt in HIn. destruct HIn as [y [Heq HIn]].
        unfold E.eq in Heq. subst y. contradiction.
      + apply IH. exact H3.
  Qed.

  Lemma elements_spec2w : forall s : t, NoDupA E.eq (elements s).
  Proof.
    intros s. apply NoDup_NoDupA_eq.
    unfold elements. rewrite VarMap.fold_1.
    apply NoDup_elements_fold_gen.
    - apply NoDup_nil.
    - intros x H. contradiction H.
    - apply VarMap.elements_3w.
  Qed.

  Lemma choose_spec1 : forall (s : t) (x : elt), choose s = Some x -> In x s.
  Proof.
    intros s x. unfold choose. destruct (elements s) as [|y l] eqn:E.
    - discriminate.
    - intros H. injection H as Hx. subst x.
      apply elements_spec1. rewrite E. constructor 1. reflexivity.
  Qed.

  Lemma choose_spec2 : forall s : t, choose s = None -> Empty s.
  Proof.
    intros s. unfold choose, Empty. destruct (elements s) as [|y l] eqn:E.
    - intros H x HIn. apply elements_spec1 in HIn. rewrite E in HIn. inversion HIn.
    - intros H. discriminate H.
  Qed.

  Lemma eq_dec : forall x y : t, {Equal x y} + {~ Equal x y}.
  Proof.
    intros x y. destruct (equal x y) eqn:E.
    - left. apply equal_spec. exact E.
    - right. intros H. apply equal_spec in H. rewrite H in E. discriminate E.
  Qed.

  Lemma filter_spec : forall (s : t) (x : elt) (f : elt -> bool), Proper (E.eq ==> Logic.eq) f -> In x (filter f s) <-> In x s /\ f x = true.
  Proof.
    intros s x f Hf. unfold filter.
    rewrite fold_spec.
    unfold flip.
    assert (H_fold: forall l acc, NoDupA E.eq l -> In x (fold_left (fun a e => if f e then add e a else a) l acc) <-> In x acc \/ (InA E.eq x l /\ f x = true)).
    {
      intros l. induction l as [|e l' IH].
      - intros acc Hnodup. simpl. split; intros H; [left; exact H|].
        destruct H as [H | [Hbad _]]; [exact H | inversion Hbad].
      - intros acc Hnodup. simpl. inversion Hnodup as [| ? ? HnotIn Hnodup']. subst.
        rewrite IH; [|exact Hnodup'].
        split; intros H.
        + destruct H as [H | [HIn Hfx]].
          * destruct (f e) eqn:Efe.
            -- apply add_spec in H. destruct H as [Heq | H]; [right; split; [constructor 1; exact Heq | assert (Hfeq: f x = f e) by (apply Hf; exact Heq); rewrite Hfeq; exact Efe] | left; exact H].
            -- left. exact H.
          * right. split; [constructor 2; exact HIn | exact Hfx].
        + destruct H as [H | [HIn Hfx]].
          * left. destruct (f e) eqn:Efe; [apply add_spec; right; exact H | exact H].
          * inversion HIn; subst.
            -- left. destruct (f e) eqn:Efe; [apply add_spec; left; exact H0 | assert (Hfeq: f x = f e) by (apply Hf; exact H0); rewrite Hfeq in Hfx; rewrite Hfx in Efe; discriminate Efe].
            -- right. split; [exact H0 | exact Hfx].
    }
    rewrite H_fold; [|apply elements_spec2w].
    split; intros H.
    - destruct H as [H | H]; [apply empty_spec in H; contradiction H |].
      split; [apply elements_spec1; exact (proj1 H) | exact (proj2 H)].
    - right. split; [apply elements_spec1; exact (proj1 H) | exact (proj2 H)].
  Qed.

  Lemma for_all_spec : forall (s : t) (f : elt -> bool), Proper (E.eq ==> Logic.eq) f -> for_all f s = true <-> For_all (fun x : elt => f x = true) s.
  Proof.
    intros s f Hf. unfold for_all.
    rewrite fold_spec. unfold flip.
    assert (H_fold: forall l acc, fold_left (fun a e => a && f e) l acc = true <-> acc = true /\ forall x, InA E.eq x l -> f x = true).
    {
      intros l. induction l as [|e l' IH].
      - intros acc. simpl. split; intros H.
        + split; [exact H | intros x Hx; inversion Hx].
        + exact (proj1 H).
      - intros acc. simpl. rewrite IH. split; intros H.
        + destruct H as [Hacc Hrest]. apply andb_true_iff in Hacc.
          split; [exact (proj1 Hacc) |].
          intros x Hx. inversion Hx; subst; [assert (Hfeq: f x = f e) by (apply Hf; exact H0); rewrite Hfeq; exact (proj2 Hacc) | apply Hrest; exact H0].
        + destruct H as [Hacc Hrest]. split; [apply andb_true_iff; split; [exact Hacc | apply Hrest; constructor 1; reflexivity] | intros x Hx; apply Hrest; constructor 2; exact Hx].
    }
    rewrite H_fold. split; intros H.
    - destruct H as [_ Hrest]. unfold For_all. intros x HIn.
      apply Hrest. apply elements_spec1. exact HIn.
    - split; [reflexivity |]. intros x HIn.
      apply H. apply elements_spec1. exact HIn.
  Qed.

  Lemma exists_spec : forall (s : t) (f : elt -> bool), Proper (E.eq ==> Logic.eq) f -> exists_ f s = true <-> Exists (fun x : elt => f x = true) s.
  Proof.
    intros s f Hf. unfold exists_.
    rewrite fold_spec. unfold flip.
    assert (H_fold: forall l acc, fold_left (fun a e => a || f e) l acc = true <-> acc = true \/ exists x, InA E.eq x l /\ f x = true).
    {
      intros l. induction l as [|e l' IH].
      - intros acc. simpl. split; intros H.
        + left. exact H.
        + destruct H as [H | [x [Hx _]]]; [exact H | inversion Hx].
      - intros acc. simpl. rewrite IH. split; intros H.
        + destruct H as [Hacc | [x [Hx Hfx]]].
          * apply orb_true_iff in Hacc. destruct Hacc as [Hacc | Hfe]; [left; exact Hacc | right; exists e; split; [constructor 1; reflexivity | exact Hfe]].
          * right. exists x. split; [constructor 2; exact Hx | exact Hfx].
        + destruct H as [Hacc | [x [Hx Hfx]]].
          * left. apply orb_true_iff. left. exact Hacc.
          * inversion Hx; subst; [left; apply orb_true_iff; right; assert (Hfeq: f x = f e) by (apply Hf; exact H0); rewrite <- Hfeq; exact Hfx | right; exists x; split; [exact H0 | exact Hfx]].
    }
    rewrite H_fold. split; intros H.
    - destruct H as [H | [x [Hx Hfx]]]; [discriminate H |].
      unfold Exists. exists x. split; [apply elements_spec1; exact Hx | exact Hfx].
    - destruct H as [x [HIn Hfx]]. right. exists x.
      split; [apply elements_spec1; exact HIn | exact Hfx].
  Qed.

  Lemma partition_spec1 : forall (s : t) (f : elt -> bool), Proper (E.eq ==> Logic.eq) f -> Equal (fst (partition f s)) (filter f s).
  Proof.
    intros s f Hf. unfold partition, filter.
    rewrite fold_spec. rewrite fold_spec. unfold flip.
    assert (H_fold: forall l a b,
      fold_left (fun (p: t*t) e => let (acc_a, acc_b) := p in if f e then (add e acc_a, acc_b) else (acc_a, add e acc_b)) l (a, b) =
      (fold_left (fun acc e => if f e then add e acc else acc) l a,
       fold_left (fun acc e => if negb (f e) then add e acc else acc) l b)).
    {
      intros l. induction l as [|e l' IH]; intros a b.
      - simpl. reflexivity.
      - simpl. destruct (f e) eqn:Efe.
        + rewrite IH. reflexivity.
        + rewrite IH. reflexivity.
    }
    rewrite H_fold. simpl. unfold Equal. intros x. reflexivity.
  Qed.

  Lemma partition_spec2 : forall (s : t) (f : elt -> bool), Proper (E.eq ==> Logic.eq) f -> Equal (snd (partition f s)) (filter (fun x : elt => negb (f x)) s).
  Proof.
    intros s f Hf. unfold partition, filter.
    rewrite fold_spec. rewrite fold_spec. unfold flip.
    assert (H_fold: forall l a b,
      fold_left (fun (p: t*t) e => let (acc_a, acc_b) := p in if f e then (add e acc_a, acc_b) else (acc_a, add e acc_b)) l (a, b) =
      (fold_left (fun acc e => if f e then add e acc else acc) l a,
       fold_left (fun acc e => if negb (f e) then add e acc else acc) l b)).
    {
      intros l. induction l as [|e l' IH]; intros a b.
      - simpl. reflexivity.
      - simpl. destruct (f e) eqn:Efe.
        + rewrite IH. reflexivity.
        + rewrite IH. reflexivity.
    }
    rewrite H_fold. simpl. unfold Equal. intros x. reflexivity.
  Qed.
End LocSet.
