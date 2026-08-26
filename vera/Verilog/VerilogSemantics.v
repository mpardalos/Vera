From Stdlib Require Import BinNat.
From Stdlib Require Import String.
From Stdlib Require Import Nat.
From Stdlib Require Import Structures.OrderedTypeEx.
From Stdlib Require Import Structures.OrdersAlt.
From Stdlib Require Import List.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Relations.
From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Psatz.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Setoid.

From vera Require Import Verilog.
From vera Require Import Variables.
Import Verilog.
From vera Require Import Common.
From vera Require Import Bitvector.
Import (notations) XBV.
Import RawXBV (bit(..)).
From vera Require Import Tactics.
From vera Require Import Decidable.

From Equations Require Import Equations.

From ExtLib Require Import Programming.Show.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Data.Monads.OptionMonad.
From ExtLib Require Import Data.List.

Import ListNotations.
Import MonadLetNotation.
Import SigTNotations.
Import Verilog.Notations.
Local Open Scope monad_scope.
Local Open Scope bv_scope.
Local Open Scope verilog.

Set Bullet Behavior "Strict Subproofs".

Opaque N.add N.sub.

Module RegisterState.
  Definition register_state := forall var, XBV.xbv (Var.varType var).

  #[global]
  Notation t := register_state.

  #[global]
  Notation execution := t.

  Definition get_location (st : t) (loc : Location.t) : RawXBV.bit :=
    XBV.bitOf (Location.idx loc) (st (Location.var loc)).

  Definition get_slice {w} (st : t) (slice : Slice.t w) : XBV.xbv w :=
    XBV.extr (st (Slice.get_var slice)) (Slice.get_lo slice) w.

  Definition empty : RegisterState.t := fun var => XBV.exes (Var.varType var).

  Lemma empty_get var : empty var = XBV.exes (Var.varType var).
  Proof. cbv. reflexivity. Qed.

  Definition set_reg (var : Var.t) (value : XBV.xbv (Var.varType var)) (r : register_state) : register_state :=
    fun var' => match dec (var = var') with
           | left e => match e with
                      | eq_refl => value
                      end
           | right _ => r var'
           end.

  Definition set_location (loc : Location.t) (wf : (Location.idx loc < Var.varType (Location.var loc))%N) (bit : RawXBV.bit) (r : register_state) : register_state :=
    set_reg (Location.var loc) (XBV.set_bit (r (Location.var loc)) (Location.idx loc) bit wf) r.

  Definition set_slice {w} (slice : Slice.t w) (value : XBV.xbv w) (r : register_state) : register_state :=
    set_reg (Slice.get_var slice) (XBV.set_slice (r (Slice.get_var slice)) (Slice.get_lo slice) value (Slice.wf_width slice)) r.

  Lemma set_reg_get_in var val regs :
    set_reg var val regs var = val.
  Proof.
    unfold set_reg.
    autodestruct; [|contradiction].
    rewrite (proof_irrelevance _ e eq_refl).
    reflexivity.
  Qed.

  #[global]
  Hint Rewrite RegisterState.set_reg_get_in : register_state.

  Lemma set_reg_get_out var1 var2 val regs :
    var1 <> var2 ->
    set_reg var1 val regs var2 = regs var2.
  Proof.
    intros.
    unfold set_reg.
    autodestruct; [contradiction|].
    reflexivity.
  Qed.

  #[global]
  Hint Rewrite RegisterState.set_reg_get_out using congruence : register_state.

  Lemma get_location_set_location loc wf bit regs :
    get_location (set_location loc wf bit regs) loc = bit.
  Proof.
    unfold get_location, set_location.
    rewrite set_reg_get_in, XBV.set_bit_get_in. reflexivity.
  Qed.

  Lemma get_slice_set_slice {w} (slice : Slice.t w) value regs :
    get_slice (set_slice slice value regs) slice = value.
  Proof.
    apply XBV.bitOf_ext. intros i Hi.
    unfold get_slice, set_slice.
    rewrite set_reg_get_in.
    rewrite XBV.extr_bitOf.
    - rewrite XBV.set_slice_get_in by exact Hi. reflexivity.
    - exact Hi.
    - apply Slice.wf_width.
  Qed.
                          
  Definition defined_value_for (locs : LocationSet.t) (regs : RegisterState.t) :=
    forall loc, loc ∈ locs -> get_location regs loc <> X.
  
  Lemma defined_value_for_split_iff vars1 vars2 regs :
    (defined_value_for vars1 regs /\ defined_value_for vars2 regs) <->
      (defined_value_for (vars1 ∪ vars2) regs).
  Proof.
    unfold defined_value_for.
    setoid_rewrite LocationSet.union_spec.
    intuition eauto.
  Qed.

  Lemma defined_value_for_subset locs1 locs2 e :
    LocationSet.Subset locs2 locs1 ->
    defined_value_for locs1 e ->
    defined_value_for locs2 e.
  Proof. unfold LocationSet.Subset, defined_value_for. crush. Qed.

  Lemma defined_value_for_empty e :
    defined_value_for LocationSet.empty e.
  Proof. unfold defined_value_for. setoid_rewrite LocationSetFacts.empty_iff. crush. Qed.

  Ltac unpack_defined_value_for :=
    repeat match goal with
      | [ H: defined_value_for (_ ∪ _) _ |- _ ] =>
          rewrite <- defined_value_for_split_iff in H;
          destruct H
      | [ |- defined_value_for (_ ∪ _) _ ] =>
          apply defined_value_for_split_iff; split
      end.

  Definition match_on (locs : LocationSet.t) (e1 e2 : RegisterState.t) : Prop :=
    forall loc, loc ∈ locs -> get_location e1 loc = get_location e2 loc.

  Notation "rs1 =( vars )= rs2" :=
    (match_on vars rs1 rs2)
    (at level 80) : type_scope.

  Lemma match_on_subset vars1 vars2 e1 e2:
    vars1 ⊆ vars2 ->
    e1 =( vars2 )= e2 ->
    e1 =( vars1 )= e2.
  Proof. unfold match_on. crush. Qed.

  Global Instance Proper_match_on_iff :
    Proper (LocationSet.Equal ==> eq ==> eq ==> iff) match_on.
  Proof. unfold match_on. solve_proper. Qed.

  Global Instance Proper_match_on_subset :
    Proper (LocationSet.Subset --> eq ==> eq ==> Basics.impl) match_on.
  Proof. unfold match_on. solve_proper. Qed.

  Global Instance Proper_match_on_subset_flip :
    Proper (LocationSet.Subset ==> eq ==> eq ==> Basics.flip Basics.impl) match_on.
  Proof. unfold match_on. solve_proper. Qed.

  (* Global Instance DefaultRelation_variable_prop :
   *   DefaultRelation (A:=Var.t -> Prop) (pointwise_relation Var.t Basics.impl).
   * Defined. *)
  
  Global Instance Proper_defined_value_for_subset :
    Proper (LocationSet.Subset --> eq ==> Basics.impl) RegisterState.defined_value_for.
  Proof. unfold defined_value_for. solve_proper. Qed.

  Global Instance Proper_defined_value_for_subset_flip :
    Proper (LocationSet.Subset ==> eq ==> Basics.flip Basics.impl) RegisterState.defined_value_for.
  Proof. unfold defined_value_for. solve_proper. Qed.
    
  Global Instance Proper_defined_value_for_iff :
    Proper (LocationSet.Equal ==> eq ==> iff) RegisterState.defined_value_for.
  Proof. unfold defined_value_for. solve_proper. Qed.
  
  Global Instance Proper_defined_value_for_match locs :
    Proper
      (RegisterState.match_on locs ==> iff)
      (RegisterState.defined_value_for locs).
  Proof.
    unfold "_ =( _ )= _", defined_value_for.
    intros e1 e2 He.
    split; intros H loc Hloc_in.
    - insterU H. insterU He.
      rewrite <- He. exact H.
    - insterU H. insterU He.
      rewrite He. exact H.
  Qed.

  Lemma match_on_split_union vars1 vars2 regs1 regs2 :
    regs1 =( vars1 ∪ vars2 )= regs2 <->
      (regs1 =( vars1 )= regs2 /\ regs1 =( vars2 )= regs2).
  Proof.
    unfold "_ =( _ )= _".
    setoid_rewrite LocationSet.union_spec.
    intuition eauto.
  Qed.

  Lemma match_on_trans vars regs1 regs2 regs3 :
    regs1 =( vars )= regs2 ->
    regs2 =( vars )= regs3 ->
    regs1 =( vars )= regs3.
  Proof.
    unfold "_ =( _ )= _".
    intros H12 H23 var HC.
    insterU H12. insterU H23.
    crush.
  Qed.

  Lemma match_on_sym vars regs1 regs2 :
    regs1 =( vars )= regs2 ->
    regs2 =( vars )= regs1.
  Proof.
    unfold "_ =( _ )= _".
    intros H var HC.
    insterU H. crush.
  Qed.

  Lemma match_on_refl C regs :
    regs =( C )= regs.
  Proof. unfold "_ =( _ )= _". crush. Qed.

  Add Parametric Relation (locs : LocationSet.t) :
    RegisterState.t (match_on locs)
    reflexivity proved by (match_on_refl locs)
    symmetry proved by (match_on_sym locs)
    transitivity proved by (match_on_trans locs)
    as match_on_rel.

  Definition defined_match_on vars e1 e2 :=
    e1 =( vars )= e2 /\ RegisterState.defined_value_for vars e1.

  Notation "rs1 =!!( vars )!!= rs2" :=
    (defined_match_on vars rs1 rs2)
    (at level 80) : type_scope.

  Lemma defined_match_on_iff locs e1 e2 :
    e1 =!!( locs )!!= e2 <->
    forall loc, loc ∈ locs ->
      exists b, RawXBV.bit_to_bool (get_location e1 loc) = Some b
         /\ RawXBV.bit_to_bool (get_location e2 loc) = Some b.
  Proof.
    unfold defined_match_on, "_ =( _ )= _", RegisterState.defined_value_for.
    split.
    - intros [Hmatch Hdefined] var HC. insterU Hmatch. insterU Hdefined.
      rewrite <- Hmatch.
      destruct (get_location e1 var).
      + contradiction.
      + simpl. eauto.
      + simpl. eauto.
    - intro H. split.
      + intros var HC. insterU H. destruct H as [? [? ?]].
        eapply RawXBV.bit_to_bool_injective; eauto.
      + intros var HC. insterU H. destruct H as [? [? ?]].
        destruct (get_location e1 var); crush.
  Qed.

  Lemma defined_match_on_trans vars e1 e2 e3:
    e1 =!!( vars )!!= e2 ->
    e2 =!!( vars )!!= e3 ->
    e1 =!!( vars )!!= e3.
  Proof.
    unfold "_ =!!( _ )!!= _".
    intros [] [].
    split.
    - now transitivity e2.
    - eassumption.
  Qed.

  Lemma defined_match_on_sym vars e1 e2:
    e1 =!!( vars )!!= e2 ->
    e2 =!!( vars )!!= e1.
  Proof.
    unfold "_ =!!( _ )!!= _".
    intros [].
    split.
    - now symmetry.
    - now rewrite <- H.
  Qed.

  Add Parametric Relation (locs : LocationSet.t) :
    RegisterState.t (defined_match_on locs)
    symmetry proved by (defined_match_on_sym locs)
    transitivity proved by (defined_match_on_trans locs)
    as execution_defined_match_on_rel.

  Global Instance Proper_defined_match_on_Subset :
    Proper
      (LocationSet.Subset --> eq ==> eq ==> Basics.impl)
      defined_match_on.
  Proof. unfold defined_match_on. solve_proper. Qed.

  Global Instance Proper_defined_match_on_Subset_flip :
    Proper
      (LocationSet.Subset ==> eq ==> eq ==> Basics.flip Basics.impl)
      defined_match_on.
  Proof. unfold defined_match_on. solve_proper. Qed.

  Global Instance Proper_defined_match_on_match_on C:
    Proper
      (RegisterState.match_on C ==> RegisterState.match_on C ==> iff)
      (RegisterState.defined_match_on C).
  Proof. unfold defined_match_on. solve_proper. Qed.

  Definition limit_to_regs (vars : VarSet.t) (regs : RegisterState.t) : RegisterState.t :=
    fun var =>
      match dec (VarSet.In var vars) with
      | left prf => regs var
      | right prf => XBV.exes (Var.varType var)
      end.

  Notation "st // regs" := (limit_to_regs regs st) (at level 20) : verilog_scope.

  Global Instance Proper_limit_to_regs vars :
    Proper
      (RegisterState.match_on (LocationSet.of_varset vars) ==> eq)
      (RegisterState.limit_to_regs vars).
  Proof.
    repeat intro.
    unfold "//", "_ =( _ )= _" in *.
    apply functional_extensionality_dep. intro var.
    autodestruct; try reflexivity.
    apply XBV.bitOf_ext. intros bit_idx Hbit_idx.
    specialize (H (Location.Mk var bit_idx)).
    unfold RegisterState.get_location in H.
    apply H.
    apply LocationSet.of_varset_spec.
    auto.
  Qed.

  Lemma limit_to_regs_twice st regs :
    st // regs // regs = st // regs.
  Proof.
    unfold "//".
    apply functional_extensionality_dep. intros.
    autodestruct; reflexivity.
  Qed.

  Lemma limit_to_regs_empty st : st // VarSet.empty = empty.
  Proof.
    apply functional_extensionality_dep.
    unfold "//", empty.
    setoid_rewrite dec_no; [|VarSet.setdec].
    reflexivity.
  Qed.

  Lemma limit_to_regs_get_skip var var' st vars :
    var <> var' ->
    (st // (VarSet.add var vars)) var' = (st // vars) var'.
  Proof.
    unfold "//". intros Hin.
    destruct (dec (VarSet.In var' vars)).
    - rewrite dec_yes at 1 by VarSet.setdec.
      reflexivity.
    - rewrite dec_no at 1 by VarSet.setdec.
      reflexivity.
  Qed.

  Lemma limit_to_regs_get_in var st vars :
    VarSet.In var vars ->
    (st // vars) var = st var.
  Proof. unfold "//". intros Hin. autodestruct; crush. Qed.

  Lemma limit_to_regs_get_out var st vars :
    ~ VarSet.In var vars ->
    (st // vars) var = XBV.exes (Var.varType var).
  Proof. unfold "//". intros Hin. autodestruct; crush. Qed.

  Lemma limit_to_regs_set_reg_in var x st vars :
    VarSet.In var vars ->
    (RegisterState.set_reg var x st) // vars
      = RegisterState.set_reg var x (st // vars).
  Proof.
   intros.
   apply functional_extensionality_dep. intros var'.
   destruct (dec (VarSet.In var' vars)).
   - rewrite limit_to_regs_get_in by assumption.
     destruct (dec (var' = var)).
     + subst.
       rewrite ! RegisterState.set_reg_get_in.
       reflexivity.
     + rewrite ! RegisterState.set_reg_get_out by auto.
       rewrite limit_to_regs_get_in by auto.
       reflexivity.
   - rewrite limit_to_regs_get_out by assumption.
     rewrite RegisterState.set_reg_get_out by crush.
     rewrite limit_to_regs_get_out by assumption.
     reflexivity.
  Qed.

  Lemma limit_to_regs_set_reg_out var x st vars :
    ~ VarSet.In var vars ->
    (RegisterState.set_reg var x st) // vars
      = st // vars.
  Proof.
    intros.
    apply functional_extensionality_dep. intros var'.
    destruct (dec (VarSet.In var' vars)).
    - rewrite ! limit_to_regs_get_in by assumption.
      rewrite RegisterState.set_reg_get_out by crush.
      reflexivity.
    - rewrite ! limit_to_regs_get_out by assumption.
      reflexivity.
  Qed.

  Lemma set_reg_limit_remove var vars v regs :
    RegisterState.set_reg var v (regs // (VarSet.add var vars)) =
    RegisterState.set_reg var v (regs // vars).
  Proof.
     apply functional_extensionality_dep. intro var'.
     destruct (dec (var' = var)).
     - subst. rewrite ! RegisterState.set_reg_get_in.
       reflexivity.
     - rewrite ! RegisterState.set_reg_get_out by eauto.
       apply limit_to_regs_get_skip. auto.
   Qed.

  Lemma match_on_limit_to_regs_iff r1 r2 l :
    (r1 // l = r2 // l) <-> (r1 =( LocationSet.of_varset l )= r2).
  Proof.
    unfold "//", "_ =( _ )= _".
    split.
    - intros Heq loc Hloc_in.
      apply LocationSet.of_varset_spec in Hloc_in.
      destruct Hloc_in as [Hvar _].
      pose proof (f_equal (fun f => f (Location.var loc)) Heq) as Hv.
      cbn in Hv.
      rewrite (dec_yes Hvar) in Hv.
      unfold get_location. congruence.
    - intros Hmatch.
      apply functional_extensionality_dep.
      intros var.
      destruct (dec (VarSet.In var l)); [|reflexivity].
      apply XBV.bitOf_ext. intros bit_idx Hbit_idx.
      specialize (Hmatch (Location.Mk var bit_idx)).
      unfold get_location in Hmatch. cbn in Hmatch.
      apply Hmatch.
      apply LocationSet.of_varset_spec. auto.
  Qed.

  Lemma limit_to_regs_match_on r l :
    r // l =( LocationSet.of_varset l )= r.
  Proof.
    apply match_on_limit_to_regs_iff.
    apply limit_to_regs_twice.
  Qed.

  Lemma defined_value_for_limit_to_regs vars st :
    RegisterState.defined_value_for (LocationSet.of_varset vars) st ->
    RegisterState.defined_value_for (LocationSet.of_varset vars) (st // vars).
  Proof.
    unfold RegisterState.defined_value_for.
    intros H loc Hin.
    specialize (H loc Hin).
    apply LocationSet.of_varset_spec in Hin.
    destruct Hin as [Hvar _].
    unfold get_location, "//" in *.
    rewrite (dec_yes Hvar).
    assumption.
  Qed.

  Lemma match_on_Empty locs regs1 regs2 :
    LocationSet.Empty locs ->
    regs1 =( locs )= regs2.
  Proof.
    unfold "_ =( _ )= _". intros Hempty loc Hin.
    exfalso. eapply Hempty. eassumption.
  Qed.

  Lemma match_on_empty regs1 regs2 :
    regs1 =( {} )= regs2.
  Proof.
    apply match_on_Empty.
    apply LocationSet.empty_spec.
  Qed.

  (* TODO: These are introduction, not elimination rules. Rename appropriately *)

  Lemma match_on_set_reg_elim2_in C var x regs1 regs2 :
    regs1 =( C )= regs2 ->
    set_reg var x regs1 =( C )= set_reg var x regs2.
  Proof.
    unfold "_ =( _ )= _". intros Hmatch loc Hloc.
    specialize (Hmatch loc Hloc).
    unfold get_location in *.
    destruct (dec (Location.var loc = var)) as [e|n].
    - rewrite e. rewrite ! RegisterState.set_reg_get_in. reflexivity.
    - rewrite ! RegisterState.set_reg_get_out by congruence. assumption.
  Qed.

  Lemma match_on_set_reg_elim2_out C var x y regs1 regs2 :
    LocationSet.Disjoint (LocationSet.of_variable var) C ->
    regs1 =( C )= regs2 ->
    set_reg var x regs1 =( C )= set_reg var y regs2.
  Proof.
    unfold "_ =( _ )= _". intros Hdisj Hmatch loc Hloc.
    specialize (Hmatch loc Hloc).
    unfold get_location in *.
    destruct (dec (Location.var loc = var)) as [e|n].
    - assert (~ LocationSet.In loc (LocationSet.of_variable var)) as Hnotin.
      { intro Hc. eapply Hdisj. apply LocationSet.inter_spec. eauto. }
      rewrite LocationSet.of_variable_spec in Hnotin.
      assert (Var.varType var <= Location.idx loc)%N as Hoob
          by (apply N.nlt_ge; intro Hlt; apply Hnotin; auto).
      rewrite e.
      rewrite ! RegisterState.set_reg_get_in.
      rewrite ! XBV.bitOf_overflow by assumption.
      reflexivity.
    - rewrite ! RegisterState.set_reg_get_out by congruence. assumption.
  Qed.

  Lemma match_on_set_reg_elim2 var x regs1 regs2 :
    set_reg var x regs1 =( LocationSet.of_variable var )= set_reg var x regs2.
  Proof.
    unfold "_ =( _ )= _". intros loc Hloc.
    apply LocationSet.of_variable_spec in Hloc.
    destruct Hloc as [Hvar _].
    unfold get_location.
    rewrite Hvar.
    rewrite ! set_reg_get_in. reflexivity.
  Qed.

  Lemma match_on_set_reg_same var regs :
    set_reg var (regs var) regs =( LocationSet.of_variable var )= regs.
  Proof.
    intros [v bit_idx] Hloc.
    apply LocationSet.of_variable_spec in Hloc. cbn in Hloc.
    destruct Hloc as [Hvar _]. subst v.
    unfold get_location.
    rewrite set_reg_get_in. reflexivity.
  Qed.

  Lemma match_on_set_reg_elim_trans C var x regs1 regs2 :
    LocationSet.Disjoint (LocationSet.of_variable var) C ->
    regs1 =( C )= regs2 ->
    set_reg var x regs1 =( C )= regs2.
  Proof.
    unfold "_ =( _ )= _". intros Hdisj Hmatch loc Hloc.
    specialize (Hmatch loc Hloc).
    unfold get_location in *.
    destruct (dec (Location.var loc = var)) as [e|n].
    - assert (~ LocationSet.In loc (LocationSet.of_variable var)) as Hnotin.
      { intro Hc. eapply Hdisj. apply LocationSet.inter_spec. eauto. }
      rewrite LocationSet.of_variable_spec in Hnotin.
      assert (Var.varType var <= Location.idx loc)%N as Hoob
          by (apply N.nlt_ge; intro Hlt; apply Hnotin; auto).
      rewrite e.
      rewrite RegisterState.set_reg_get_in.
      rewrite ! XBV.bitOf_overflow by assumption.
      reflexivity.
    - rewrite RegisterState.set_reg_get_out by congruence. assumption.
  Qed.

  Lemma match_on_set_reg_elim C var x regs :
    LocationSet.Disjoint (LocationSet.of_variable var) C ->
    set_reg var x regs =( C )= regs.
  Proof.
    unfold "_ =( _ )= _". intros Hdisj loc Hloc.
    unfold get_location.
    destruct (dec (Location.var loc = var)) as [e|n].
    - assert (~ LocationSet.In loc (LocationSet.of_variable var)) as Hnotin.
      { intro Hc. eapply Hdisj. apply LocationSet.inter_spec. eauto. }
      rewrite LocationSet.of_variable_spec in Hnotin.
      assert (Var.varType var <= Location.idx loc)%N as Hoob
          by (apply N.nlt_ge; intro Hlt; apply Hnotin; auto).
      rewrite e.
      rewrite RegisterState.set_reg_get_in.
      rewrite ! XBV.bitOf_overflow by assumption.
      reflexivity.
    - rewrite RegisterState.set_reg_get_out by congruence. reflexivity.
  Qed.

  Lemma match_on_set_location_elim2 loc wf1 wf2 x regs1 regs2 :
    set_location loc wf1 x regs1 =( LocationSet.singleton loc )= set_location loc wf2 x regs2.
  Proof.
    unfold match_on, get_location, set_location. 
    intros loc' Hloc'.
    apply LocationSet.singleton_spec in Hloc'. unfold LocationSet.E.eq in Hloc'.
    subst loc'.
    rewrite ! set_reg_get_in.
    rewrite ! XBV.set_bit_get_in.
    reflexivity.
  Qed.

  Lemma match_on_set_location_same loc wf regs :
    set_location loc wf (get_location regs loc) regs
      =( LocationSet.singleton loc )= regs.
  Proof.
    intros loc' Hloc'.
    apply LocationSet.singleton_spec in Hloc'. unfold LocationSet.E.eq in Hloc'. subst loc'.
    unfold get_location, set_location.
    rewrite set_reg_get_in, XBV.set_bit_get_in. reflexivity.
  Qed.

  Lemma match_on_set_location_elim2_in C loc wf1 wf2 x regs1 regs2 :
    regs1 =( C )= regs2 ->
    set_location loc wf1 x regs1 =( C )= set_location loc wf2 x regs2.
  Proof.
    unfold match_on, get_location, set_location.
    intros Hmatch loc' Hloc'. specialize (Hmatch loc' Hloc').
    destruct (dec (Location.var loc' = Location.var loc)) as [e|n].
    - rewrite e in Hmatch. rewrite e, ! set_reg_get_in.
      destruct (N.eq_dec (Location.idx loc) (Location.idx loc')) as [eidx|nidx].
      + rewrite <- eidx. rewrite ! XBV.set_bit_get_in. reflexivity.
      + rewrite ! XBV.set_bit_get_out by exact nidx. exact Hmatch.
    - rewrite ! set_reg_get_out by congruence. exact Hmatch.
  Qed.

  Lemma match_on_set_location_elim C loc wf x regs :
    LocationSet.Disjoint (LocationSet.singleton loc) C ->
    set_location loc wf x regs =( C )= regs.
  Proof.
    unfold match_on, get_location, set_location.
    intros Hdisj loc' Hloc'.
    destruct (dec (Location.var loc' = Location.var loc)) as [e|n].
    - rewrite e, set_reg_get_in.
      rewrite XBV.set_bit_get_out; [reflexivity|].
      intro Hidx.
      eapply Hdisj. apply LocationSet.inter_spec. split; [|exact Hloc'].
      apply LocationSet.singleton_spec.
      destruct loc, loc'. simpl in *. subst. reflexivity.
    - rewrite set_reg_get_out by congruence. reflexivity.
  Qed.

  Lemma match_on_set_slice_elim2 {w} (slice : Slice.t w) x regs1 regs2 :
    set_slice slice x regs1 =( LocationSet.of_slice slice )= set_slice slice x regs2.
  Proof.
    unfold match_on, get_location, set_slice.
    intros loc Hloc.
    apply LocationSet.of_slice_spec in Hloc.
    unfold Slice.has_location in Hloc. destruct Hloc as [Hvar Hidx].
    rewrite <- Hvar. rewrite ! set_reg_get_in.
    replace (Location.idx loc) with
      (Slice.get_lo slice + (Location.idx loc - Slice.get_lo slice))%N by lia.
    rewrite ! XBV.set_slice_get_in by lia.
    reflexivity.
  Qed.

  Lemma match_on_set_slice_same {w} (slice : Slice.t w) regs :
    set_slice slice (get_slice regs slice) regs
      =( LocationSet.of_slice slice )= regs.
  Proof.
    intros loc Hloc.
    apply LocationSet.of_slice_spec in Hloc.
    unfold Slice.has_location in Hloc. destruct Hloc as [Hvar Hidx].
    unfold get_location, set_slice, get_slice.
    rewrite <- Hvar, set_reg_get_in.
    replace (Location.idx loc) with
      (Slice.get_lo slice + (Location.idx loc - Slice.get_lo slice))%N by lia.
    rewrite XBV.set_slice_get_in by lia.
    rewrite XBV.extr_bitOf.
    - reflexivity.
    - lia.
    - apply Slice.wf_width.
  Qed.

  Lemma get_slice_match {w} (slice : Slice.t w) regs1 regs2 :
    regs1 =( LocationSet.of_slice slice )= regs2 ->
    get_slice regs1 slice = get_slice regs2 slice.
  Proof.
    intros Hmatch. apply XBV.bitOf_ext. intros i Hi.
    unfold get_slice.
    rewrite ! XBV.extr_bitOf.
    - change (get_location regs1 (Location.Mk (Slice.get_var slice) (Slice.get_lo slice + i)) =
        get_location regs2 (Location.Mk (Slice.get_var slice) (Slice.get_lo slice + i))).
      apply Hmatch. apply LocationSet.of_slice_spec.
      unfold Slice.has_location. simpl. split; [reflexivity|lia].
    - exact Hi.
    - apply Slice.wf_width.
    - exact Hi.
    - apply Slice.wf_width.
  Qed.

  Global Instance Proper_get_slice {w} (slice : Slice.t w) :
    Proper (match_on (LocationSet.of_slice slice) ==> eq)
      (fun regs => get_slice regs slice).
  Proof. exact (get_slice_match slice). Qed.

  Lemma match_on_set_slice_elim2_in {w} C (slice : Slice.t w) x regs1 regs2 :
    regs1 =( C )= regs2 ->
    set_slice slice x regs1 =( C )= set_slice slice x regs2.
  Proof.
    unfold match_on, get_location, set_slice.
    intros Hmatch loc Hloc. specialize (Hmatch loc Hloc).
    destruct (dec (Location.var loc = Slice.get_var slice)) as [e|n].
    - rewrite e in Hmatch. rewrite e, ! set_reg_get_in.
      destruct (N.lt_ge_cases (Location.idx loc) (Slice.get_lo slice)).
      + rewrite ! XBV.set_slice_get_out by (left; assumption). exact Hmatch.
      + destruct (N.lt_ge_cases (Location.idx loc) (Slice.get_lo slice + w)).
        * replace (Location.idx loc) with
            (Slice.get_lo slice + (Location.idx loc - Slice.get_lo slice))%N by lia.
          rewrite ! XBV.set_slice_get_in by lia. reflexivity.
        * rewrite ! XBV.set_slice_get_out by (right; assumption). exact Hmatch.
    - rewrite ! set_reg_get_out by congruence. exact Hmatch.
  Qed.

  Lemma match_on_set_slice_elim {w} C (slice : Slice.t w) x regs :
    LocationSet.Disjoint (LocationSet.of_slice slice) C ->
    set_slice slice x regs =( C )= regs.
  Proof.
    unfold match_on, get_location, set_slice.
    intros Hdisj loc Hloc.
    destruct (dec (Location.var loc = Slice.get_var slice)) as [e|n].
    - assert (~ LocationSet.In loc (LocationSet.of_slice slice)) as Hnotin.
      { intro Hin. eapply Hdisj. apply LocationSet.inter_spec. eauto. }
      rewrite LocationSet.of_slice_spec in Hnotin.
      unfold Slice.has_location in Hnotin.
      rewrite e, set_reg_get_in.
      rewrite XBV.set_slice_get_out; [reflexivity|].
      destruct (N.lt_ge_cases (Location.idx loc) (Slice.get_lo slice)); [auto|].
      right. apply N.nlt_ge. intro Hlt. apply Hnotin.
      split; [symmetry; exact e|]. lia.
    - rewrite set_reg_get_out by congruence. reflexivity.
  Qed.

  Lemma match_on_variable r1 r2 var :
    r1 =( LocationSet.of_variable var )= r2 ->
    r1 var = r2 var.
  Proof.
    unfold RegisterState.match_on, get_location.
    intros H.
    apply XBV.bitOf_ext.
    intros idx Hidx.
    specialize (H (Location.Mk var idx)). simpl in H.
    apply H. clear H.
    apply LocationSet.of_variable_spec.
    auto.
  Qed.

  Lemma match_on_singleton r1 r2 loc :
    r1 =( LocationSet.singleton loc )= r2 ->
    XBV.bitOf (Location.idx loc) (r1 (Location.var loc)) 
      = XBV.bitOf (Location.idx loc) (r2 (Location.var loc)).
  Proof.
    intros H. apply H.
    apply LocationSet.singleton_spec.
    reflexivity.
  Qed.

  Ltac unpack_match_on :=
    repeat match goal with
      | [ H: _ =( _ ∪ _ )= _ |- _ ] =>
          apply match_on_split_union in H;
          destruct H
      | [ |- _ =( _ ∪ _ )= _ ] =>
          apply match_on_split_union; split
      | [ |- _ =( {} )= _ ] =>
          solve [apply match_on_empty]
      | [ H: _ =( {} )= _ |- _ ] =>
          clear H
      end.
End RegisterState.

Export (notations) RegisterState.

Module Sort.
  Import Verilog.

  Inductive module_items_sorted : LocationSet.t -> list Verilog.module_item -> Prop :=
    | module_items_sorted_nil vars : module_items_sorted vars []
    | module_items_sorted_cons vars mi mis :
      LocationSet.Subset (module_item_reads mi) vars ->
      LocationSet.Disjoint (module_item_writes mi) vars ->
      module_items_sorted (Verilog.module_item_writes mi ∪ vars) mis ->
      module_items_sorted vars (mi :: mis)
  .

  #[refine]
  Global Instance dec_module_items_sorted vars ms : DecProp (module_items_sorted vars ms) :=
    traceBracket "Check sort" _.
  Proof.
    revert vars.
    induction ms; intros vars.
    - left. constructor.
    - destruct (dec (LocationSet.Subset (Verilog.module_item_reads a) vars));
        [|right; inversion 1; crush].
      destruct (dec (LocationSet.Disjoint (Verilog.module_item_writes a) vars));
        [|right; inversion 1; crush].
      destruct (IHms (Verilog.module_item_writes a ∪ vars));
        [|right; inversion 1; crush].
      left. constructor; auto.
  Defined.

  Lemma module_items_sorted_no_overwrite inputs body :
    module_items_sorted inputs body ->
    LocationSet.Disjoint (module_body_writes body) inputs.
  Proof. induction 1; simpl; LocationSet.setdec. Qed.

  Lemma module_items_sorted_permute_vars l l' body :
    LocationSet.Equal l l' ->
    module_items_sorted l body ->
    module_items_sorted l' body.
  Proof.
    intros Hpermute Hsorted.
    revert l' Hpermute.
    induction Hsorted; intros; constructor.
    - now rewrite <- Hpermute.
    - now rewrite <- Hpermute.
    - apply IHHsorted. LocationSet.setdec.
  Qed.

  Global Instance Proper_module_items_sorted_Equal :
    Proper (LocationSet.Equal ==> eq ==> iff) module_items_sorted.
  Proof.
    intros vars vars' Hvars_eq body body' <-.
    split; intros H.
    - eapply module_items_sorted_permute_vars.
      + eassumption.
      + eassumption.
    - eapply module_items_sorted_permute_vars.
      + symmetry. eassumption.
      + eassumption.
  Qed.

  Global Instance Proper_module_body_writes_Permutation_Equal :
    Proper (@Permutation module_item ==> LocationSet.Equal) module_body_writes.
  Proof.
    intros mis1 mis2 Hmis.
    induction Hmis.
    all: simpl.
    all: LocationSet.setdec.
  Qed.

  Global Instance Proper_module_body_reads_Permutation_Equal :
    Proper (@Permutation module_item ==> LocationSet.Equal) module_body_reads.
  Proof.
    intros mis1 mis2 Hmis.
    induction Hmis.
    all: simpl.
    all: LocationSet.setdec.
  Qed.

  Lemma module_body_writes_app l1 l2 :
    LocationSet.Equal
      (module_body_writes (l1 ++ l2))
      (module_body_writes l1 ∪ module_body_writes l2).
  Proof.
    revert l2.
    induction l1; intros l2; simpl.
    - LocationSet.setdec.
    - rewrite IHl1. LocationSet.setdec.
  Qed.

  Lemma module_body_reads_app l1 l2 :
    LocationSet.Equal
      (module_body_reads (l1 ++ l2))
      (module_body_reads l1 ∪ module_body_reads l2).
  Proof.
    revert l2.
    induction l1; intros l2; simpl.
    - LocationSet.setdec.
    - rewrite IHl1. LocationSet.setdec.
  Qed.

  Lemma module_items_sorted_skip vars_skip vars_rest body :
    LocationSet.Disjoint vars_skip (module_body_reads body) ->
    module_items_sorted (vars_skip ∪ vars_rest) body ->
    module_items_sorted vars_rest body.
  Proof.
    revert vars_skip vars_rest.
    induction body; intros * Hnot_var_in Hsorted; [constructor|].
    inv Hsorted.
    simpl in *.
    constructor.
    - LocationSet.setdec.
    - LocationSet.setdec.
    - eapply IHbody with (vars_skip:=vars_skip).
      + LocationSet.setdec.
      + eapply Proper_module_items_sorted_Equal;
          [idtac|reflexivity|eassumption].
        LocationSet.setdec.
  Qed.

  Lemma module_items_sorted_add extra inputs body :
    LocationSet.Disjoint extra (module_body_writes body) ->
    module_items_sorted inputs body ->
    module_items_sorted (extra ∪ inputs) body.
  Proof.
    intros Hnot_read Hsorted.
    revert extra Hnot_read.
    induction Hsorted; intros; constructor; simpl in Hnot_read.
    - LocationSet.setdec.
    - LocationSet.setdec.
    - setoid_replace
        (module_item_writes mi ∪ extra ∪ vars)
        with
        (extra ∪ module_item_writes mi ∪ vars)
        using relation LocationSet.Equal
        by LocationSet.setdec.
      apply IHHsorted.
      LocationSet.setdec.
  Qed.

  Lemma module_items_sorted_skip1 var_skip vars_rest body :
    ~ LocationSet.In var_skip (module_body_reads body) ->
    module_items_sorted ({ var_skip }%verilog ∪ vars_rest) body ->
    module_items_sorted vars_rest body.
  Proof.
    intros * Hnot_in Hsorted.
    apply module_items_sorted_skip with (vars_skip:={var_skip}).
    - LocationSet.setdec.
    - apply Hsorted.
  Qed.

  Lemma module_items_sorted_app inputs body1 body2 :
    module_items_sorted inputs body1 ->
    module_items_sorted (inputs ∪ module_body_writes body1) body2 ->
    module_items_sorted inputs (body1 ++ body2).
  Proof.
    intro Hsorted1.
    revert body2.
    induction Hsorted1; simpl; intros * Hsorted2.
    - setoid_replace (vars ∪ LocationSet.empty) with vars
        using relation LocationSet.Equal
        in Hsorted2
        by LocationSet.setdec.
      exact Hsorted2.
    - simpl. constructor.
      + assumption.
      + assumption.
      + apply IHHsorted1.
        setoid_replace
          ((module_item_writes mi ∪ vars) ∪ module_body_writes mis)
          with
          (vars ∪ module_item_writes mi ∪ module_body_writes mis)
          using relation LocationSet.Equal
          by LocationSet.setdec.
        exact Hsorted2.
  Qed.

  Lemma module_items_sorted_app_inv_head inputs body1 body2 :
    module_items_sorted inputs (body1 ++ body2) ->
    module_items_sorted inputs body1.
  Proof.
    intros H.
    remember (body1 ++ body2) as body.
    revert body1 body2 Heqbody.
    induction H; intros.
    - symmetry in Heqbody. apply app_eq_nil in Heqbody.
      destruct Heqbody as [-> ->].
      constructor.
    - symmetry in Heqbody. apply app_eq_cons in Heqbody.
      destruct Heqbody as [[-> ->]|[body_middle [-> ->]]].
      + constructor.
      + constructor.
        * assumption.
        * assumption.
        * eapply IHmodule_items_sorted.
          reflexivity.
  Qed.

  Lemma module_items_sorted_app_inv_tail inputs body1 body2 :
    module_items_sorted inputs (body1 ++ body2) ->
    module_items_sorted (inputs ∪ module_body_writes body1) body2.
  Proof.
    intros H.
    remember (body1 ++ body2) as body.
    revert body1 body2 Heqbody.
    induction H; intros.
    - symmetry in Heqbody. apply app_eq_nil in Heqbody.
      destruct Heqbody as [-> ->].
      constructor.
    - symmetry in Heqbody. apply app_eq_cons in Heqbody.
      destruct Heqbody as [[-> ->]|[body_middle [-> ->]]].
      + simpl.
        setoid_replace (vars ∪ { }) with vars
          using relation LocationSet.Equal by LocationSet.setdec.
        constructor.
        all: assumption.
      + simpl.
        setoid_replace
          (vars ∪ module_item_writes mi ∪ module_body_writes body_middle)
          with
          ((module_item_writes mi ∪ vars) ∪ module_body_writes body_middle)
          using relation LocationSet.Equal
          by LocationSet.setdec.
        apply IHmodule_items_sorted.
        reflexivity.
  Qed.

  Equations sort_module_items_split_ready
    (ready : LocationSet.t)
    (chosen : list module_item)
    (skipped : list module_item)
    (mis : list module_item)
    : option (LocationSet.t * list module_item * list module_item) := {
    | ready, chosen, skipped, [] => Some (ready, chosen, skipped)
    | ready, chosen, skipped, (mi :: mis')
      with LocationSet.disjoint (module_item_writes mi) ready,
           LocationSet.subset (module_item_reads mi) ready => {
      | false, _    =>
        (* trace ("Conflict on " ++ to_string mi) *) None (* Conflict *)
      | true, false => (* Not ready *)
        sort_module_items_split_ready ready chosen (mi :: skipped) mis'
      | true, true => (* Ready *)
        sort_module_items_split_ready (module_item_writes mi ∪ ready) (mi :: chosen) skipped mis'
    }
  }.

  (* Having fuel for this is disgusting, yes, but we are
     non-structurally recursing on ms.  We know that
     sort_module_items_select_tailrec returns a smaller list than it
     is given, but proving that at the point of the recursive call
     means either adding a railroad pattern to see the equality and
     use sort_module_items_select_tailrec_perm, OR making
     sort_module_items_select_tailrec return a proof that the list it
     returns is smaller than its argument, which is too much of a
     change to that function.
   *)
  Equations sort_module_items_tailrec
    (fuel : nat)
    (vars_ready : LocationSet.t)
    (ms : list module_item)
    (sorted : list module_item)
    : option (list module_item) by struct fuel := {
      | _, vars_ready, [], sorted => Some (rev sorted)
      | 0, vars_ready, _, sorted => (* trace "Ran out of fuel" *) None
      | (S fuel'), vars_ready, ms, sorted with ((* trace ("Ready: " ++ to_string vars_ready) *) sort_module_items_split_ready vars_ready [] [] ms) => {
        | None => (* trace "Chosing failed" *) None
        | Some (vars_ready', [], rest) =>
          (* trace ("Chosing picked nothing in " ++ to_string rest) *) None
        | Some (vars_ready', chosen, rest) =>
          (* trace ("Chose " ++ to_string chosen) *) (sort_module_items_tailrec fuel' vars_ready' rest (chosen ++ sorted))
      }
    }.

  Definition sort_module_items ready body : option (list module_item) :=
     sort_module_items_tailrec (length body) ready body [].

  Lemma sort_module_items_split_ready_perm ready chosen skipped mis ready' chosen' skipped' :
    sort_module_items_split_ready ready chosen skipped mis = Some (ready', chosen', skipped') ->
    Permutation (chosen ++ skipped ++ mis) (chosen' ++ skipped').
  Proof.
    funelim (sort_module_items_split_ready ready chosen skipped mis); intros Hsplit.
    - (* Done *)
      inv Hsplit.
      rewrite app_nil_r.
      (* rewrite <- ! Permutation_rev. *)
      reflexivity.
    - (* Skip *)
      apply H in Hsplit. cbn in Hsplit.
      rewrite <- Hsplit.
      rewrite Permutation_middle.
      rewrite Permutation_middle.
      reflexivity.
    - (* Ready *)
      apply H in Hsplit. cbn in Hsplit.
      rewrite <- Hsplit.
      rewrite Permutation_middle.
      reflexivity.
    - inv Hsplit.
  Qed.

  Lemma sort_module_items_split_ready_sorted initial_inputs ready chosen skipped mis ready' chosen' rest' :
    module_items_sorted initial_inputs (rev chosen) ->
    LocationSet.Equal (initial_inputs ∪ module_body_writes chosen) ready ->
    sort_module_items_split_ready ready chosen skipped mis = Some (ready', chosen', rest') ->
    module_items_sorted initial_inputs (rev chosen').
  Proof.
    funelim (sort_module_items_split_ready ready chosen skipped mis);
      intros Hsorted Hready Hsplit.
    - inv Hsplit. exact Hsorted.
    - rewrite LocationSet.subset_spec in Heq.
      rewrite LocationSet.disjoint_spec in Heq0.
      eapply H.
      + simpl. apply module_items_sorted_app.
        * assumption.
        * rewrite <- Permutation_rev.
          constructor.
          -- LocationSet.setdec.
          -- LocationSet.setdec.
          -- constructor.
      + simpl. LocationSet.setdec.
      + exact Hsplit.
    - eapply H; eassumption.
    - inv Hsplit.
  Qed.

  Lemma sort_module_items_split_ready_stable initial_inputs ready chosen skipped mis :
    module_items_sorted initial_inputs (rev chosen ++ mis) ->
    LocationSet.Equal ready (initial_inputs ∪ Verilog.module_body_writes chosen) ->
    exists ready',
      LocationSet.Equal ready' (ready ∪ Verilog.module_body_writes mis) /\
      sort_module_items_split_ready ready chosen skipped mis = Some (ready', rev mis ++ chosen, skipped).
  Proof.
    funelim (sort_module_items_split_ready ready chosen skipped mis);
      intros Hsorted Hready_correct.
    - exists ready. split.
      + simpl. LocationSet.setdec.
      + reflexivity.
    - rewrite LocationSet.subset_spec in Heq.
      rewrite LocationSet.disjoint_spec in Heq0.
      simpl in H. rewrite <- app_assoc in H. simpl in H.
      apply H in Hsorted; [|LocationSet.setdec].
      destruct Hsorted as [ready' [Hready' Htail]].
      (* rewrite Hready' in *. clear ready'. *)
      rewrite Htail.
      simpl.
      rewrite <- app_assoc. exists ready'. split.
      + LocationSet.setdec.
      + reflexivity.
    - (* Skip. Impossible *)
      exfalso.
      apply module_items_sorted_app_inv_tail in Hsorted. inv Hsorted.
      rewrite <- Permutation_rev in *.
      rewrite <- Hready_correct in H2.
      apply LocationSet.subset_spec in H2.
      congruence.
    - (* Write conflict. Impossible *)
      exfalso.
      apply module_items_sorted_app_inv_tail in Hsorted. inv Hsorted.
      rewrite <- Permutation_rev in *.
      rewrite <- Hready_correct in H3.
      apply LocationSet.disjoint_spec in H3.
      congruence.
  Qed.

  Lemma sort_module_items_split_ready_writes initial_inputs ready chosen skipped mis ready' chosen' skipped' :
    LocationSet.Equal ready (initial_inputs ∪ module_body_writes chosen) ->
    sort_module_items_split_ready ready chosen skipped mis = Some (ready', chosen', skipped') ->
    LocationSet.Equal ready' (initial_inputs ∪ module_body_writes chosen').
  Proof.
    funelim (sort_module_items_split_ready ready chosen skipped mis); intros Hwrites_ready Hsplit.
    - inv Hsplit. LocationSet.setdec.
    - rewrite LocationSet.subset_spec in Heq.
      rewrite LocationSet.disjoint_spec in Heq0.
      eapply H in Hsplit.
      + exact Hsplit.
      + simpl. LocationSet.setdec.
    - eapply H; eassumption.
    - inv Hsplit.
  Qed.

  Theorem sort_module_items_tailrec_permutation fuel body sorted body' vars_ready :
    sort_module_items_tailrec fuel vars_ready body sorted = Some body' ->
    Permutation (sorted ++ body) body'.
  Proof.
    funelim (sort_module_items_tailrec fuel vars_ready body sorted); simpl.
    - (* Done *)
      intros H. inv H.
      rewrite List.app_nil_r.
      apply Permutation_rev.
    - (* Out of fuel *)
      inversion 1.
    - (* Selected nothing *)
      inversion 1.
    - intros Hrest.
      apply H in Hrest. (* ; [|constructor]. *)
      apply sort_module_items_split_ready_perm in Heq.
      rewrite <- Hrest.
      rewrite Heq.
      rewrite app_assoc.
      apply Permutation_app_tail.
      apply Permutation_app_comm.
    - (* Select failed *)
      inversion 1.
  Qed.

  Theorem sort_module_items_tailrec_sorted fuel initial_inputs ready body sorted_acc sorted:
    module_items_sorted initial_inputs (rev sorted_acc) ->
    LocationSet.Equal (initial_inputs ∪ module_body_writes sorted_acc) ready ->
    sort_module_items_tailrec fuel ready body sorted_acc = Some sorted ->
    module_items_sorted initial_inputs sorted.
  Proof.
    funelim (sort_module_items_tailrec fuel ready body sorted_acc).
    all: simpl.
    all: intros Hsorted Hsub Hsort.
    - inv Hsort. exact Hsorted.
    - inv Hsort.
    - inv Hsort.
    - apply H.
      (* + constructor. *)
      + rewrite rev_app_distr.
        apply module_items_sorted_app.
        * exact Hsorted.
        * eapply sort_module_items_split_ready_sorted in Heq.
          -- exact Heq.
          -- constructor.
          -- rewrite <- Permutation_rev. LocationSet.setdec.
      + rewrite module_body_writes_app.
        apply sort_module_items_split_ready_writes
          with (initial_inputs:= initial_inputs ∪ module_body_writes sorted)
          in Heq.
        * LocationSet.setdec.
        * simpl. LocationSet.setdec.
      + exact Hsort.
    - inv Hsort.
  Qed.

  Lemma sort_module_items_tailrec_stable fuel initial_inputs ready sorted mis :
    module_items_sorted initial_inputs (rev sorted ++ mis) ->
    LocationSet.Equal ready (initial_inputs ∪ Verilog.module_body_writes sorted) ->
    fuel >= length mis ->
    sort_module_items_tailrec fuel ready mis sorted = Some (rev sorted ++ mis).
  Proof.
    funelim (sort_module_items_tailrec fuel ready mis sorted).
    all: intros Hsorted Hready Hfuel.
    - rewrite app_nil_r. reflexivity.
    - simpl in Hfuel. lia.
    - destruct sort_module_items_split_ready_stable
        with
          (initial_inputs:=vars_ready)
          (ready:=vars_ready)
          (chosen:=@nil module_item)
          (skipped:=@nil module_item)
          (mis:=m::l)
        as [sorted' [Hready' Hsorted']].
      + simpl. apply module_items_sorted_app_inv_tail in Hsorted.
        rewrite <- Permutation_rev in Hsorted.
        rewrite Hready.
        exact Hsorted.
      + simpl. LocationSet.setdec.
      + rewrite Hsorted' in Heq. inv Heq.
        rewrite app_nil_r in H1.
        apply app_eq_nil in H1.
        intuition discriminate. 
    - destruct sort_module_items_split_ready_stable
        with
          (initial_inputs:=vars_ready)
          (ready:=vars_ready)
          (chosen:=@nil module_item)
          (skipped:=@nil module_item)
          (mis:=m::l)
        as [sorted' [Hready' Hsorted']].
      + simpl. apply module_items_sorted_app_inv_tail in Hsorted.
        rewrite <- Permutation_rev in Hsorted.
        rewrite Hready.
        exact Hsorted.
      + simpl. LocationSet.setdec.
      + rewrite Hsorted' in Heq; inv Heq.
        rewrite ! app_nil_r in *.
        rewrite H2.
        erewrite H.
        all: try rewrite <- H2.
        all: try rewrite ! rev_app_distr.
        all: try rewrite rev_involutive.
        * reflexivity.
        * exact Hsorted.
        * simpl in Hready'.
          rewrite ! module_body_writes_app.
          rewrite <- Permutation_rev.
          simpl.
          LocationSet.setdec.
        * simpl. lia.
    - destruct sort_module_items_split_ready_stable
        with
          (initial_inputs:=vars_ready)
          (ready:=vars_ready)
          (chosen:=@nil module_item)
          (skipped:=@nil module_item)
          (mis:=m::l)
        as [sorted' [Hready' Hsorted']].
      + simpl. apply module_items_sorted_app_inv_tail in Hsorted.
        rewrite <- Permutation_rev in Hsorted.
        rewrite Hready.
        exact Hsorted.
      + simpl. LocationSet.setdec.
      + rewrite Hsorted' in Heq. inv Heq.
  Qed.

  (******************************************
   *
   * Topological sort specification
   *
   ******************************************)

  Theorem sort_module_items_permutation body body' vars_ready :
    sort_module_items vars_ready body = Some body' ->
    Permutation body body'.
  Proof.
    unfold sort_module_items. intros H.
    apply sort_module_items_tailrec_permutation in H.
    apply H.
  Qed.

  Theorem sort_module_items_sorted inputs body body':
    sort_module_items inputs body = Some body' ->
    module_items_sorted inputs body'.
  Proof.
    unfold sort_module_items.
    intros Hsort.
    eapply sort_module_items_tailrec_sorted in Hsort.
    - exact Hsort.
    - apply module_items_sorted_nil.
    - LocationSet.setdec.
  Qed.

  Theorem sort_module_items_stable inputs body :
    module_items_sorted inputs body ->
    sort_module_items inputs body = Some body.
  Proof.
    unfold sort_module_items.
    intros Hsorted.
    erewrite sort_module_items_tailrec_stable.
    - reflexivity.
    - exact Hsorted.
    - simpl. LocationSet.setdec.
    - lia.
  Qed.

  Section map.
    Context
      (f : module_item -> module_item)
      (f_preserve_reads : forall mi, LocationSet.Equal (module_item_reads (f mi)) (module_item_reads mi))
      (f_preserve_writes : forall mi, LocationSet.Equal (module_item_writes (f mi)) (module_item_writes mi)).

    Lemma sort_module_items_split_ready_map_some ready1 ready1' ready2 chosen skipped mis chosen' skipped' :
      LocationSet.Equal ready1 ready2 ->
      sort_module_items_split_ready ready1 chosen skipped mis
        = Some (ready1', chosen', skipped') ->
      exists ready2',
        LocationSet.Equal ready1' ready2' /\
        sort_module_items_split_ready ready2 (map f chosen) (map f skipped) (map f mis)
          = Some (ready2', map f chosen', map f skipped').
     Proof.
       funelim (sort_module_items_split_ready ready1 chosen skipped mis).
       all: intros Hready Hsort.
       all: simpl; simp sort_module_items_split_ready in *.
       - inv Hsort. exists ready2. split.
         + assumption.
         + reflexivity.
       - setoid_rewrite f_preserve_reads. rewrite Hready in Heq. rewrite Heq.
         setoid_rewrite f_preserve_writes. rewrite Hready in Heq0. rewrite Heq0.
         eapply H.
         + rewrite f_preserve_writes, Hready. reflexivity.
         + exact Hsort.
       - setoid_rewrite f_preserve_reads. rewrite Hready in Heq. rewrite Heq.
         setoid_rewrite f_preserve_writes. rewrite Hready in Heq0. rewrite Heq0.
         apply H. all: assumption.
       - inv Hsort.
     Qed.

    Lemma sort_module_items_split_ready_map_none ready1 ready2 chosen skipped mis :
      LocationSet.Equal ready1 ready2 ->
      sort_module_items_split_ready ready1 chosen skipped mis = None ->
      sort_module_items_split_ready ready2 (map f chosen) (map f skipped) (map f mis) = None.
     Proof.
       funelim (sort_module_items_split_ready ready1 chosen skipped mis).
       all: intros Hready Hsort.
       all: simpl; simp sort_module_items_split_ready in *.
       - inv Hsort.
       - setoid_rewrite f_preserve_reads. rewrite Hready in Heq. rewrite Heq.
         setoid_rewrite f_preserve_writes. rewrite Hready in Heq0. rewrite Heq0.
         eapply H.
         + rewrite f_preserve_writes, Hready. reflexivity.
         + exact Hsort.
       - setoid_rewrite f_preserve_reads. rewrite Hready in Heq. rewrite Heq.
         setoid_rewrite f_preserve_writes. rewrite Hready in Heq0. rewrite Heq0.
         apply H. all: assumption.
       - setoid_rewrite f_preserve_writes. rewrite Hready in Heq. rewrite Heq.
         reflexivity.
     Qed.

    Lemma sort_module_items_tailrec_map_some fuel inputs1 inputs2 mis sorted sorted' :
      LocationSet.Equal inputs1 inputs2 ->
      sort_module_items_tailrec fuel inputs1 mis sorted = Some sorted' ->
      sort_module_items_tailrec fuel inputs2 (map f mis) (map f sorted) = Some (map f sorted').
    Proof.
      funelim (sort_module_items_tailrec fuel inputs1 mis sorted).
      all: intros Hinputs_eq Hsort.
      all: simpl; simp sort_module_items_tailrec; simpl.
      - inv Hsort. rewrite map_rev. reflexivity.
      - inv Hsort.
      - inv Hsort.
      - eapply sort_module_items_split_ready_map_some in Heq; [|exact Hinputs_eq].
        destruct Heq as [ready2' [Hready2' Hsplit]].
        simpl in Hsplit. rewrite Hsplit. simpl.
        replace (f m0 :: map f l1 ++ map f sorted) with (map f (m0 :: l1 ++ sorted))
          by now rewrite <- map_app.
        apply H.
        * assumption. 
        * assumption.
      - inv Hsort.
    Qed.

    Lemma sort_module_items_tailrec_map_none fuel inputs1 inputs2 mis sorted :
      LocationSet.Equal inputs1 inputs2 ->
      sort_module_items_tailrec fuel inputs1 mis sorted = None ->
      sort_module_items_tailrec fuel inputs2 (map f mis) (map f sorted) = None.
    Proof.
      funelim (sort_module_items_tailrec fuel inputs1 mis sorted).
      all: intros Hinputs_eq Hsort.
      all: simpl; simp sort_module_items_tailrec; simpl.
      - inv Hsort.
      - eapply sort_module_items_split_ready_map_some in Heq; [|exact Hinputs_eq].
        destruct Heq as [ready2' [Hready2' Hsplit]].
        simpl in Hsplit. rewrite Hsplit.
        reflexivity.
      - eapply sort_module_items_split_ready_map_some in Heq; [|exact Hinputs_eq].
        destruct Heq as [ready2' [Hready2' Hsplit]].
        simpl in Hsplit. rewrite Hsplit. simpl.
        replace (f m0 :: map f l1 ++ map f sorted) with (map f (m0 :: l1 ++ sorted))
          by now rewrite <- map_app.
        apply H.
        + assumption.
        + assumption.
      - eapply sort_module_items_split_ready_map_none in Heq; [|exact Hinputs_eq].
        simpl in Heq. rewrite Heq.
        reflexivity.
    Qed.

    Lemma sort_module_items_map inputs mis :
      sort_module_items inputs (map f mis)
        = option_map (map f) (sort_module_items inputs mis).
    Proof.
      unfold sort_module_items.
      rewrite length_map.
      destruct (sort_module_items_tailrec (Datatypes.length mis) inputs mis []) eqn:Hsort; simpl.
      - eapply sort_module_items_tailrec_map_some in Hsort; [|reflexivity]. simpl in Hsort.
        exact Hsort.
      - eapply sort_module_items_tailrec_map_none in Hsort; [|reflexivity]. simpl in Hsort.
        exact Hsort.
    Qed.
  End map.

  (* Print Assumptions sort_module_items_stable.
   * Print Assumptions sort_module_items_sorted.
   * Print Assumptions sort_module_items_permutation.
   * Print Assumptions sort_module_items_map. *)

  Definition vmodule_sortable {i o} (v : vmodule i o) : Prop :=
    exists sorted, sort_module_items (LocationSet.of_varset (VarSet.of_list i)) (Verilog.modBody v) = Some sorted.

  (* Checking that typeclasses eauto can indeed find this instance *)
  Goal (forall i o (v : vmodule i o), DecProp (vmodule_sortable v)). typeclasses eauto. Qed.
End Sort.

Module CombinationalOnly.
  Export Sort.

  Definition Process := Verilog.module_item.

  Definition variable_names vars : list string :=
    map Var.varName vars.

  Equations bv_binop {w} : (BV.bitvector w -> BV.bitvector w -> BV.bitvector w) -> XBV.xbv w -> XBV.xbv w -> XBV.xbv w :=
    bv_binop f l r with XBV.to_bv l, XBV.to_bv r => {
      | Some lbv, Some rbv => XBV.from_bv (f lbv rbv)
      | _, _ => XBV.exes (XBV.size l)
      }.

  Equations eval_arithmeticop {n} (op : Verilog.arithmeticop) : XBV.xbv n -> XBV.xbv n -> XBV.xbv n :=
    eval_arithmeticop Verilog.ArithmeticPlus l r := bv_binop (@BV.bv_add _) l r;
    eval_arithmeticop Verilog.ArithmeticMinus l r := bv_binop (fun bvl bvr => BV.bv_add bvl (BV.bv_neg bvr)) l r;
    eval_arithmeticop Verilog.ArithmeticStar l r := bv_binop (@BV.bv_mult _) l r;
  .

  Equations eval_bitwiseop {n} (op : Verilog.bitwiseop) : XBV.xbv n -> XBV.xbv n -> XBV.xbv n :=
    eval_bitwiseop Verilog.BinaryBitwiseAnd l r := XBV.bitwise_binop RawXBV.and_bit l r;
    eval_bitwiseop Verilog.BinaryBitwiseOr l r := XBV.bitwise_binop RawXBV.or_bit l r;
    eval_bitwiseop Verilog.BinaryBitwiseXor l r := XBV.bitwise_binop RawXBV.xor_bit l r;
  .

  Equations eval_shiftop {n1 n2} (op : Verilog.shiftop) : XBV.xbv n1 -> XBV.xbv n2 -> XBV.xbv n1 :=
    eval_shiftop Verilog.BinaryShiftLeft l r with XBV.to_N r := {
      | Some shamt => XBV.shl l shamt
      | None => XBV.exes n1
      };
    eval_shiftop Verilog.BinaryShiftRight l r with XBV.to_N r := {
      | Some shamt => XBV.shr l shamt
      | None => XBV.exes n1
      };
    eval_shiftop Verilog.BinaryShiftLeftArithmetic l r with XBV.to_N r := {
      | Some shamt => XBV.shl l shamt
      | None => XBV.exes n1
      };
  .

  Equations eval_unaryop {n} (op : Verilog.unaryop) (operand : XBV.xbv n) : XBV.xbv (Verilog.unaryop_result op n) :=
    eval_unaryop Verilog.UnaryPlus x := x;
    eval_unaryop Verilog.UnaryNot x := XBV.not x;
    eval_unaryop Verilog.UnaryReduceAnd x := XBV.of_bits [ XBV.fold I RawXBV.and_bit x ] ;
    eval_unaryop Verilog.UnaryLogicalNot x with XBV.to_bv x => {
      | Some bv with BV.is_zero bv => {
        | true => XBV.ones 1
        | false => XBV.zeros 1
      }
      | None => XBV.exes 1
    }
  .

  (* Notation rewriting a b e := (@eq_rect_r _ a _ e b _). *)
  (* Notation with_rewrite e := (eq_rect_r _ e _). *)

  (* TODO: Check that ?: semantics match with standard *)
  Definition eval_conditional {w_cond w} (cond : XBV.xbv w_cond) (ifT : XBV.xbv w) (ifF : XBV.xbv w) : XBV.xbv w :=
      match XBV.to_bv cond with
      | None => XBV.exes (XBV.size ifT)
      | Some cond_bv =>
          if BV.is_zero cond_bv
          then ifF
          else ifT
      end.

  Equations
    eval_expr {w} (regs: RegisterState.t) (e : Verilog.expression w) : XBV.xbv w :=
    eval_expr regs (Verilog.UnaryOp op operand) :=
      let operand_val := eval_expr regs operand in
      (eval_unaryop op operand_val);
    eval_expr regs (Verilog.ArithmeticOp op lhs rhs) :=
      let lhs_val := eval_expr regs lhs in
      let rhs_val := eval_expr regs rhs in
      (eval_arithmeticop op lhs_val rhs_val);
    eval_expr regs (Verilog.BitwiseOp op lhs rhs) :=
      let lhs_val := eval_expr regs lhs in
      let rhs_val := eval_expr regs rhs in
      (eval_bitwiseop op lhs_val rhs_val);
    eval_expr regs (Verilog.ShiftOp op lhs rhs _ _) :=
      let lhs_val := eval_expr regs lhs in
      let rhs_val := eval_expr regs rhs in
      (eval_shiftop op lhs_val rhs_val);
    eval_expr regs (Verilog.Conditional cond tBranch fBranch) :=
      let cond_val := eval_expr regs cond in
      let tBranch_val := eval_expr regs tBranch in
      let fBranch_val := eval_expr regs fBranch in
      (eval_conditional cond_val tBranch_val fBranch_val);
    eval_expr regs (Verilog.RangeSelect (Slice.Mk vec hi lo _)) :=
      let vec_val := regs vec in
      (XBV.extr vec_val lo (1 + hi - lo));
    eval_expr regs (Verilog.BitSelect vec idx) :=
      let vec_val := regs vec in
      let idx_val := eval_expr regs idx in
      match XBV.to_N idx_val with
      | Some idx => XBV.extr vec_val idx 1
      | None => XBV.exes 1
      end;
    eval_expr regs (Verilog.Resize t expr _) :=
      let val := eval_expr regs expr in
      (XBV.resize t val);
    eval_expr regs (Verilog.Concatenation e1 e2) :=
      let val1 := eval_expr regs e1 in
      let val2 := eval_expr regs e2 in
      (XBV.concat val1 val2);
    eval_expr regs (Verilog.Replication count expr) :=
      let expr_val := eval_expr regs expr in
      (XBV.replicate count expr_val);
    eval_expr regs (Verilog.IntegerLiteral _ val) := val ;
    eval_expr regs (Verilog.NamedExpression var) := regs var.

  Equations set_target {w} (regs : RegisterState.t) (target : Verilog.assign_target w) (value : XBV.xbv w) : RegisterState.t :=
    set_target regs (Verilog.AssignVar var) value :=
      RegisterState.set_reg var value regs ;
    set_target regs (Verilog.AssignBit loc wf) value :=
      RegisterState.set_location loc wf (XBV.bitOf 0 value) regs ;
    set_target regs (Verilog.AssignSlice slice) value :=
      RegisterState.set_slice slice value regs ;
    set_target regs (@Verilog.AssignConcat w1 w2 t1 t2) value :=
      set_target (set_target regs t2 (XBV.extr value 0 w2)) t1 (XBV.extr value w2 w1)
    .

  Equations
    exec_statement (regs : RegisterState.t) (stmt : Verilog.statement) : RegisterState.t by struct :=
    exec_statement regs (Verilog.BlockingAssign target _ rhs) :=
      let rhs_val := eval_expr regs rhs in
      set_target regs target rhs_val ;
  .

  Equations
    exec_module_item : RegisterState.t -> Verilog.module_item -> RegisterState.t :=
    exec_module_item st (Verilog.AlwaysComb stmt ) :=
      exec_statement st stmt;
  .

  Equations
    exec_module_body : RegisterState.t -> list Verilog.module_item -> RegisterState.t :=
    exec_module_body regs [] := regs;
    exec_module_body regs (mi :: mis) :=
      let regs' := exec_module_item regs mi in
      exec_module_body regs' mis;
  .

  Definition mk_initial_state {i o} (v : vmodule i o) (regs : RegisterState.t) : RegisterState.t :=
    regs // VarSet.of_list i.

  Lemma initial_state_same {i o1 o2} (v1 : vmodule i o1) (v2 : vmodule i o2) regs :
    mk_initial_state v1 regs = mk_initial_state v2 regs.
  Proof. reflexivity. Qed.

  (* We make a choice here, about how to handle non-sortable
     modules. Originally, this return `option
     RegisterState.t`. Non-sortable modules (writes to inputs,
     multiple drivers, combinational loops) would "abort".  The
     `option` types were quite annoying to deal with, and we need
     special versions of all our operators (`_ =?( _ )?= _` rather
     than `_ =( _ )= _` to handle them).

     Instead of exposing the option types on this function, we can
     kind of "push" the `None`s into the RegisterState, by returning
     a sentinel "empty" state.
  *)

  Definition run_vmodule {i o} (v : vmodule i o) (inputs : RegisterState.t) : RegisterState.t :=
    match sort_module_items (LocationSet.of_varset (VarSet.of_list i)) (Verilog.modBody v) with
    | None => mk_initial_state v inputs
    | Some sorted => exec_module_body (mk_initial_state v inputs) sorted
    end.

  Global Instance Proper_run_vmodule_match_on {i o} (v : vmodule i o) :
    Proper
      (RegisterState.match_on (LocationSet.of_varset (VarSet.of_list i)) ==> eq)
      (run_vmodule v).
  Proof.
    intros r1 r2 Heq.
    unfold run_vmodule.
    unfold mk_initial_state.
    autodestruct.
    - rewrite Heq. reflexivity.
    - rewrite Heq. reflexivity.
  Qed.

  Notation execution := RegisterState.t.

  Definition valid_execution {i o} (v : vmodule i o) (e : execution) :=
    run_vmodule v e =( module_locations v )= e.

  Infix "⇓" := valid_execution (at level 20) : verilog_scope.

  Definition execution_not_x (e : execution) name :=
    ~ XBV.has_x (e name).

  Definition execution_no_exes_for C (e : execution) :=
    forall var, C var -> execution_not_x e var.

  Global Instance Proper_execution_no_exes_for :
    Proper (pointwise_relation Var.t iff ==> eq ==> iff) execution_no_exes_for.
  Proof. repeat intro. subst. crush. Qed.

  Equations
    eval_expr_static {w} (e : Verilog.expression w) : option (XBV.xbv w) :=
    eval_expr_static (Verilog.UnaryOp op operand) :=
      let* operand_val := eval_expr_static operand in
      Some (eval_unaryop op operand_val);
    eval_expr_static (Verilog.ArithmeticOp op lhs rhs) :=
      let* lhs_val := eval_expr_static lhs in
      let* rhs_val := eval_expr_static rhs in
      Some (eval_arithmeticop op lhs_val rhs_val);
    eval_expr_static (Verilog.BitwiseOp op lhs rhs) :=
      let* lhs_val := eval_expr_static lhs in
      let* rhs_val := eval_expr_static rhs in
      Some (eval_bitwiseop op lhs_val rhs_val);
    eval_expr_static (Verilog.ShiftOp op lhs rhs _ _) :=
      let* lhs_val := eval_expr_static lhs in
      let* rhs_val := eval_expr_static rhs in
      Some (eval_shiftop op lhs_val rhs_val);
    eval_expr_static (Verilog.Conditional cond tBranch fBranch) :=
      let* cond_val := eval_expr_static cond in
      let* tBranch_val := eval_expr_static tBranch in
      let* fBranch_val := eval_expr_static fBranch in
      Some (eval_conditional cond_val tBranch_val fBranch_val);
    eval_expr_static (Verilog.RangeSelect _) :=
      None; (* range select is always on a variable *)
    eval_expr_static (Verilog.BitSelect vec idx) :=
      None; (* bit select is always on a variable *)
    eval_expr_static (Verilog.Resize t expr _) :=
      let* val := eval_expr_static expr in
      Some (XBV.resize t val);
    eval_expr_static (Verilog.Concatenation e1 e2) :=
      let* val1 := eval_expr_static e1 in
      let* val2 := eval_expr_static e2 in
      Some (XBV.concat val1 val2);
    eval_expr_static (Verilog.Replication count expr) :=
      let* expr_val := eval_expr_static expr in
      Some (XBV.replicate count expr_val);
    eval_expr_static (Verilog.IntegerLiteral _ val) := Some val ;
    eval_expr_static (Verilog.NamedExpression var) := None.

  Lemma eval_expr_static_spec {w} regs (e : expression w) x :
    eval_expr_static e = Some x ->
    eval_expr regs e = x.
  Proof.
    intros H.
    induction e.
    all: simp eval_expr eval_expr_static in *.
    all: monad_inv.
    all: simpl.
    all: repeat match goal with
         | [ IH : forall x, Some _ = Some _ -> eval_expr _ _ = _ |- _ ] =>
           erewrite IH by reflexivity; clear IH
         end.
    all: reflexivity.
  Qed.
End CombinationalOnly.

Section ExpressionFacts.
  Import CombinationalOnly.

  Lemma eval_arithmeticop_to_bv op w (lhs rhs : BV.bitvector w) :
    exists bv, XBV.to_bv (eval_arithmeticop op (XBV.from_bv lhs) (XBV.from_bv rhs)) = Some bv.
  Proof.
    destruct op.
    all: simp eval_arithmeticop.
    all: match goal with [ |- context[bv_binop ?op ?l ?r] ] =>
           funelim (bv_binop op l r)
         end.
    all: rewrite XBV.xbv_bv_inverse in *.
    all: crush.
  Qed.
  
  Lemma eval_bitwiseop_to_bv op w (lhs rhs : BV.bitvector w) :
    exists bv, XBV.to_bv (eval_bitwiseop op (XBV.from_bv lhs) (XBV.from_bv rhs)) = Some bv.
  Proof.
    destruct op.
    all: autorewrite with eval_bitwiseop xbv.
    all: eauto.
  Qed.
  
  Lemma eval_shiftop_to_bv op w1 w2 (lhs : BV.bitvector w1) (rhs : BV.bitvector w2) :
    exists bv, XBV.to_bv (eval_shiftop op (XBV.from_bv lhs) (XBV.from_bv rhs)) = Some bv.
  Proof.
    destruct op.
    all: autorewrite with eval_shiftop xbv.
    all: eauto.
  Qed.
  Lemma eval_arithmeticop_no_exes op w (lhs rhs : BV.bitvector w) :
    exists bv, eval_arithmeticop op (XBV.from_bv lhs) (XBV.from_bv rhs) = XBV.from_bv bv.
  Proof.
    edestruct eval_arithmeticop_to_bv as [bv Hbv].
    apply XBV.bv_xbv_inverse in Hbv.
    eauto.
  Qed.
  
  Lemma eval_bitwiseop_no_exes op w (lhs rhs : BV.bitvector w) :
    exists bv, eval_bitwiseop op (XBV.from_bv lhs) (XBV.from_bv rhs) = XBV.from_bv bv.
  Proof.
    edestruct eval_bitwiseop_to_bv as [bv Hbv].
    apply XBV.bv_xbv_inverse in Hbv.
    eauto.
  Qed.
  
  Lemma eval_shiftop_no_exes op w1 w2 (lhs : BV.bitvector w1) (rhs : BV.bitvector w2) :
    exists bv, eval_shiftop op (XBV.from_bv lhs) (XBV.from_bv rhs) = XBV.from_bv bv.
  Proof.
    edestruct eval_shiftop_to_bv as [bv Hbv].
    apply XBV.bv_xbv_inverse in Hbv.
    eauto.
  Qed.

  (* Lemma of_bits_to_bv bits :
   *   XBV.of_bits (RawXBV.from_bv bits) = XBV.from_bv (BV.of_bits bits). *)

  Lemma eval_unop_to_bv op w (e : BV.bitvector w) :
    exists bv, XBV.to_bv (eval_unaryop op (XBV.from_bv e)) = Some bv.
  Proof.
    funelim (eval_unaryop op (XBV.from_bv e)).
    all: autorewrite with eval_unaryop xbv in *.
    all: try discriminate; eauto; expect 1.
    - (* And-reduce *) 
      admit.
  Admitted.
  
  Lemma eval_unop_no_exes op w (e : BV.bitvector w) :
    exists bv, eval_unaryop op (XBV.from_bv e) = XBV.from_bv bv.
  Proof.
    edestruct eval_unop_to_bv as [bv Hbv].
    apply XBV.bv_xbv_inverse in Hbv.
    eauto.
  Qed.
  
  Lemma eval_conditional_no_exes w_cond w (cond : BV.bitvector w_cond) (ifT ifF : BV.bitvector w) :
    exists bv, eval_conditional (XBV.from_bv cond) (XBV.from_bv ifT) (XBV.from_bv ifF) = XBV.from_bv bv.
  Proof.
    unfold eval_conditional.
    rewrite XBV.xbv_bv_inverse.
    crush.
  Qed.

  Inductive upper_bound_static {w} (e : expression w) (bound : N) : Prop :=
  | upper_bound_static_eval xbv val
    (Heval : eval_expr_static e = Some xbv)
    (Hto_N : XBV.to_N xbv = Some val)
    (Hbound : (val < bound)%N)
  | upper_bound_static_by_width
    (Hwidth : (2 ^ w < bound)%N).

  Lemma upper_bound_static_spec {w} regs (e : expression w) b val :
    upper_bound_static e b ->
    XBV.to_N (eval_expr regs e) = Some val ->
    (val < b)%N.
  Proof.
    intros H Heval.
    inv H.
    - erewrite eval_expr_static_spec in Heval by eassumption.
      replace val0 with val in * by congruence.
      exact Hbound.
    - transitivity (2 ^ w)%N.
      + eapply XBV.to_N_max_bound. exact Heval.
      + exact Hwidth.
  Qed.
End ExpressionFacts.

Module Facts.
  Import CombinationalOnly.

  Equations read_target {w} (regs : RegisterState.t) (target : Verilog.assign_target w) : XBV.xbv w :=
    read_target regs (Verilog.AssignVar var) := regs var;
    read_target regs (Verilog.AssignBit loc _) :=
      XBV.of_bits [RegisterState.get_location regs loc];
    read_target regs (Verilog.AssignSlice slice) :=
      RegisterState.get_slice regs slice;
    read_target regs (Verilog.AssignConcat lhs rhs) :=
      XBV.concat (read_target regs lhs) (read_target regs rhs).

  Lemma read_target_change_regs {w} (target : Verilog.assign_target w) regs1 regs2 :
    regs1 =( Verilog.assign_target_writes target )= regs2 ->
    read_target regs1 target = read_target regs2 target.
  Proof.
    induction target; intros Hmatch; simp read_target; simpl in Hmatch.
    - apply RegisterState.match_on_variable. exact Hmatch.
    - pose proof (RegisterState.match_on_singleton regs1 regs2 loc Hmatch) as Hbit.
      unfold RegisterState.get_location.
      rewrite Hbit. reflexivity.
    - apply RegisterState.get_slice_match. exact Hmatch.
    - RegisterState.unpack_match_on.
      rewrite IHtarget1 by assumption.
      rewrite IHtarget2 by assumption. reflexivity.
  Qed.

  Add Parametric Morphism : module_body_reads
    with signature (@Permutation Verilog.module_item) ==> LocationSet.Equal
    as module_body_reads_permute.
  Proof.
    intros x y Hpermutation; induction Hpermutation; simpl in *.
    - LocationSet.setdec.
    - erewrite IHHpermutation. reflexivity.
    - LocationSet.setdec.
    - etransitivity; eassumption.
  Qed.

  Add Parametric Morphism : module_body_writes
    with signature (@Permutation Verilog.module_item) ==> LocationSet.Equal
    as module_body_writes_permute.
  Proof.
    intros x y Hpermutation; induction Hpermutation; simpl in *.
    - LocationSet.setdec.
    - erewrite IHHpermutation. reflexivity.
    - LocationSet.setdec.
    - etransitivity; eassumption.
  Qed.

  Lemma eval_expr_change_regs w (e : Verilog.expression w) : forall regs regs',
    regs =(Verilog.expr_reads e)= regs' ->
    eval_expr regs e = eval_expr regs' e.
  Proof.
    intros.
    funelim (eval_expr regs e).
    all: simp eval_expr expr_reads in *; simpl in *.
    all: RegisterState.unpack_match_on.
    all: repeat match goal with [ IH : forall _, _ -> eval_expr _ _ = eval_expr _ _ |- _ ] =>
           erewrite IH by eassumption; clear IH
	 end.
    all: simp eval_expr; simpl; try reflexivity.
    all: expect 3.
    - simp eval_expr. simpl.
      apply XBV.bitOf_ext. intros bit_idx Hbit_idx.
      rewrite ! XBV.extr_bitOf by lia.
      apply (H (Location.Mk vec (lo + bit_idx)%N)).
      apply LocationSet.of_slice_spec.
      unfold Slice.has_location. simpl. split; [reflexivity | lia].
    - (* Literal indices read one bit; dynamic indices read the whole vector. *)
      simp eval_expr. cbv zeta.
      rewrite <- H with (regs' := regs'); cycle 1. {
        destruct idx.
        all: simpl in *.
        all: RegisterState.unpack_match_on.
        all: try assumption.
      }
      destruct (XBV.to_N (eval_expr regs idx)) eqn:Eidx; [|reflexivity].
      rename_match (regs =( _ )= regs') into Hmatch.
      destruct idx.
      all: simpl in Hmatch.
      all: RegisterState.unpack_match_on.
      all: repeat apply_somewhere RegisterState.match_on_variable.
      all: try replace (regs' vec).
      all: try reflexivity.
      all: expect 1.
      simp eval_expr in Eidx.
      rewrite Eidx in Hmatch.
      apply XBV.extr_one_ext.
      destruct (N.ltb_spec n (Var.varType vec)).
      + apply RegisterState.match_on_singleton in Hmatch.
        simpl in Hmatch.
        exact Hmatch.
      + rewrite ! XBV.bitOf_overflow by lia. reflexivity.
    - apply RegisterState.match_on_variable.
      assumption.
  Qed.

  (***** Statements ***********)

  Lemma set_target_preserve {w} target value regs l :
    LocationSet.Disjoint (Verilog.assign_target_writes target) l ->
    set_target (w:=w) regs target value =( l )= regs.
  Proof.
    revert value regs l.
    induction target.
    all: intros.
    all: simpl; simp set_target.
    all: simpl in H.
    - apply RegisterState.match_on_set_reg_elim.
      exact H.
    - apply RegisterState.match_on_set_location_elim.
      exact H.
    - apply RegisterState.match_on_set_slice_elim.
      exact H.
    - rewrite IHtarget1, IHtarget2 by LocationSet.setdec.
      reflexivity.
  Qed.

  Lemma set_target_match_before {w} target value regs reference l :
    LocationSet.Disjoint (Verilog.assign_target_writes target) l ->
    set_target (w:=w) regs target value =( l )= reference ->
    regs =( l )= reference.
  Proof.
    intros Hdisjoint Hmatch loc Hloc.
    rewrite <- (set_target_preserve target value regs l Hdisjoint loc Hloc).
    apply Hmatch. exact Hloc.
  Qed.

  Lemma read_target_set_target {w} (target : Verilog.assign_target w) :
    Verilog.assign_target_wf target ->
    forall regs value,
      read_target (set_target regs target value) target = value.
  Proof.
    intros Hwf.
    induction Hwf; intros *; simp read_target set_target; simpl.
    - apply RegisterState.set_reg_get_in.
    - rewrite RegisterState.get_location_set_location.
      apply XBV.of_bits_bitOf.
    - apply RegisterState.get_slice_set_slice.
    - rewrite IHHwf1.
      erewrite read_target_change_regs.
      2: { apply set_target_preserve. exact Hno_overlap. }
      rewrite IHHwf2.
      apply XBV.concat_extr.
  Qed.

  Lemma set_target_from_state {w} (target : Verilog.assign_target w) :
    Verilog.assign_target_wf target ->
    forall regs reference,
      set_target regs target (read_target reference target)
        =( Verilog.assign_target_writes target )=
      reference.
  Proof.
    intros Hwf.
    induction Hwf; intros *; simp read_target set_target; simpl.
    - rewrite RegisterState.match_on_set_reg_elim2.
      apply RegisterState.match_on_set_reg_same.
    - rewrite RegisterState.match_on_set_location_elim2 with (wf2:=wf).
      apply RegisterState.match_on_set_location_same.
    - rewrite RegisterState.match_on_set_slice_elim2.
      apply RegisterState.match_on_set_slice_same.
    - rewrite XBV.extr_concat_high, XBV.extr_concat_low.
      RegisterState.unpack_match_on.
      + apply IHHwf1.
      + rewrite set_target_preserve by assumption.
        apply IHHwf2.
  Qed.

  Lemma set_target_change_regs {w} target value regs1 regs2 :
    assign_target_wf target ->
    set_target (w:=w) regs1 target value
      =( Verilog.assign_target_writes target )=
    set_target regs2 target value.
  Proof.
    intros target_wf.
    revert value regs1 regs2.
    induction target_wf.
    all: intros.
    all: simp set_target; simpl.
    - apply RegisterState.match_on_set_reg_elim2.
    - apply RegisterState.match_on_set_location_elim2.
    - apply RegisterState.match_on_set_slice_elim2.
    - RegisterState.unpack_match_on.
      + apply IHtarget_wf1.
      + rewrite set_target_preserve by assumption.
        rewrite set_target_preserve with (target:=lhs) by assumption.
        apply IHtarget_wf2.
  Qed.

  Lemma set_target_change_preserve {w} l target value regs1 regs2 :
    regs1 =( l )= regs2 ->
    set_target (w:=w) regs1 target value =( l )= set_target (w:=w) regs2 target value.
  Proof.
    revert value l regs1 regs2.
    induction target.
    all: intros.
    all: simp set_target.
    - apply RegisterState.match_on_set_reg_elim2_in.
      exact H.
    - apply RegisterState.match_on_set_location_elim2_in.
      exact H.
    - apply RegisterState.match_on_set_slice_elim2_in.
      exact H.
  Qed.

  Lemma exec_statement_change_regs stmt regs1 regs2 :
    regs1 =(Verilog.statement_reads stmt)= regs2 ->
    exec_statement regs1 stmt
      =( Verilog.statement_writes stmt )=
    exec_statement regs2 stmt.
  Proof.
    intros Hmatch.
    funelim (exec_statement regs1 stmt); expect 1.
    try rewrite <- Heqcall in *; clear Heqcall.
    simp exec_statement in *; simpl.
    simp exec_statement statement_reads statement_writes in *.
    erewrite eval_expr_change_regs by eassumption.
    apply set_target_change_regs.
    assumption.
  Qed.

  Lemma exec_statement_change_preserve l stmt regs1 regs2 :
    regs1 =( Verilog.statement_reads stmt )= regs2 ->
    regs1 =( l )= regs2 ->
    exec_statement regs1 stmt =( l )= exec_statement regs2 stmt.
  Proof.
    intros Hmatch_other Hmatch_reads.
    destruct stmt; expect 1.
    simp exec_statement. simpl in *.
    erewrite eval_expr_change_regs by eassumption.
    eapply set_target_change_preserve.
    exact Hmatch_reads.
  Qed.

  Lemma exec_statement_change_preserve_reads stmt regs1 regs2 :
    regs1 =( Verilog.statement_reads stmt )= regs2 ->
    exec_statement regs1 stmt =( Verilog.statement_reads stmt )= exec_statement regs2 stmt.
  Proof. auto using exec_statement_change_preserve. Qed.

  Lemma exec_statement_preserve stmt regs  l :
    LocationSet.Disjoint l (Verilog.statement_writes stmt) ->
    regs =( l )= exec_statement regs stmt.
  Proof.
    intros Hdisjoint.
    funelim (exec_statement regs stmt);
      try rewrite <- Heqcall in *; clear Heqcall.
    simpl in *.
    symmetry.
    apply set_target_preserve. symmetry. exact Hdisjoint.
  Qed.

  (***** / statements ***********)

  (***** Module items ***********)

  Lemma exec_module_item_change_regs mi regs1 regs2 :
    regs1 =(Verilog.module_item_reads mi)= regs2 ->
    exec_module_item regs1 mi
      =(Verilog.module_item_writes mi)=
    exec_module_item regs2 mi.
  Proof.
    intros Hmatch.
    funelim (exec_module_item regs1 mi).
    try rewrite <- Heqcall in *; clear Heqcall.
    simp exec_module_item in *; simpl.
    try solve [constructor]; expect 1.
    simp exec_module_item module_item_reads module_item_writes expr_reads in *.
    apply exec_statement_change_regs. assumption.
  Qed.

  Lemma exec_module_item_change_preserve mi regs1 regs2 :
    regs1 =( Verilog.module_item_reads mi )= regs2 ->
    forall l, regs1 =( l )= regs2 ->
    exec_module_item regs1 mi =( l )= exec_module_item regs2 mi.
  Proof.
    intros Hmatch_other Hmatch_reads.
    destruct mi; expect 1.
    simpl in *; simp exec_module_item in *.
    apply exec_statement_change_preserve; assumption.
  Qed.

  Lemma exec_module_item_change_preserve_reads mi regs1 regs2 :
    regs1 =( Verilog.module_item_reads mi )= regs2 ->
    exec_module_item regs1 mi =( Verilog.module_item_reads mi )= exec_module_item regs2 mi.
  Proof. auto using exec_module_item_change_preserve. Qed.

  Lemma exec_module_item_preserve mi regs l :
    LocationSet.Disjoint l (Verilog.module_item_writes mi) ->
    regs =( l )= exec_module_item regs mi.
  Proof.
    intros Hdisjoint Hexec.
    funelim (exec_module_item regs mi);
    try rewrite <- Heqcall in *; clear Heqcall.
    simp module_item_writes expr_reads in *.
    try discriminate; expect 1.
    eapply exec_statement_preserve; eassumption.
  Qed.

  (************* /module items ***********)

  (***** module bodies ***********)

  Lemma exec_module_body_change_preserve body regs1 regs2 :
    regs1 =( Verilog.module_body_reads body )= regs2 ->
    forall l, regs1 =( l )= regs2 ->
    exec_module_body regs1 body =( l )= exec_module_body regs2 body.
  Proof.
    revert regs1 regs2.
    induction body; intros * Hmatch_reads l Hmatch_other.
    - simp exec_module_body.
    - simp exec_module_body in *. simpl in *.
      RegisterState.unpack_match_on.
      eapply IHbody.
      + eapply exec_module_item_change_preserve; assumption.
      + eapply exec_module_item_change_preserve; assumption.
  Qed.

  Lemma exec_module_body_change_regs body regs1 regs2 :
    regs1 =(Verilog.module_body_reads body)= regs2 ->
    exec_module_body regs1 body
      =(Verilog.module_body_writes body)=
    exec_module_body regs2 body.
  Proof.
    intros Hmatch.
    funelim (exec_module_body regs1 body); [crush|].
    try rewrite <- Heqcall in *; clear Heqcall.
    simp exec_module_body in *; simpl in *.
    RegisterState.unpack_match_on.
    - apply exec_module_body_change_preserve.
      + apply exec_module_item_change_preserve; assumption.
      + apply exec_module_item_change_regs; assumption.
    - eapply H. 
      apply exec_module_item_change_preserve; assumption.
  Qed.

  Lemma exec_module_body_change_preserve_reads body regs1 regs2 :
    regs1 =( Verilog.module_body_reads body )= regs2 ->
    exec_module_body regs1 body =( Verilog.module_body_reads body )= exec_module_body regs2 body.
  Proof. auto using exec_module_body_change_preserve. Qed.

  Lemma exec_module_body_preserve body regs l :
    LocationSet.Disjoint l (module_body_writes body) ->
    regs =( l )= exec_module_body regs body.
  Proof.
    intros Hdisjoint.
    funelim (exec_module_body regs body); [reflexivity|].
    try rewrite <- Heqcall in *; clear Heqcall.
    simpl in *.
    try discriminate; try (some_inv; reflexivity); expect 1.
    monad_inv.
    rewrite <- H by LocationSet.setdec.
    eapply exec_module_item_preserve.
    LocationSet.setdec.
  Qed.

  (************* /module bodies ***********)

  (************* modules ***********)

  Lemma run_vmodule_preserve_inputs {i o} (v : vmodule i o) e :
    run_vmodule v e =( LocationSet.of_varset (VarSet.of_list i) )= e.
  Proof.
    unfold vmodule_sortable, run_vmodule, mk_initial_state.
    autodestruct_eqn E.
    - symmetry.
      rewrite <- exec_module_body_preserve.
      + symmetry.
        apply RegisterState.limit_to_regs_match_on.
      + symmetry.
        apply module_items_sorted_no_overwrite.
        eapply sort_module_items_sorted.
        eassumption.
    - apply RegisterState.limit_to_regs_match_on.
  Qed.

  Lemma sortable_decidable {i o} (v : vmodule i o) : { vmodule_sortable v } + { ~ vmodule_sortable v}.
  Proof.
    unfold vmodule_sortable.
    destruct
      (sort_module_items
        (LocationSet.of_varset (VarSet.of_list i)) 
        (modBody v)).
    - left. eexists. reflexivity.
    - right. intros [? ?]. discriminate.
  Qed.

  Lemma admit_run_vmodule {i o} (v : vmodule i o) e:
    v ⇓ run_vmodule v e.
  Proof.
    unfold "⇓".
    (* intros Hsortable. *)
    destruct (sortable_decidable v).
    - setoid_rewrite run_vmodule_preserve_inputs at 2.
      reflexivity.
    - unfold run_vmodule, vmodule_sortable in *.
      destruct (sort_module_items (LocationSet.of_varset (VarSet.of_list i)) (modBody v)).
      + contradict n. eauto.
      + unfold mk_initial_state. rewrite RegisterState.limit_to_regs_twice. reflexivity.
  Qed.

  (************* /modules ***********)

  Lemma set_reg_swap var1 var2 x1 x2 regs :
    var1 <> var2 ->
    RegisterState.set_reg var1 x1 (RegisterState.set_reg var2 x2 regs) =
      RegisterState.set_reg var2 x2 (RegisterState.set_reg var1 x1 regs).
  Proof.
    intro Hneq.
    apply functional_extensionality_dep. intro var.
    destruct (dec (var = var1)), (dec (var = var2)); subst;
      autorewrite with register_state; trivial.
  Qed.

  (* DELETEME: Broken from switch to VarSet. Doesn't seem to be used. *)
  (* Lemma exec_module_body_permute : forall body1 body2 rs0,
   *   Permutation body1 body2 ->
   *   (\* NoDup (Verilog.module_body_writes body1) ->
   *    * NoDup (Verilog.module_body_writes body2) -> *\)
   *   LocationSet.Disjoint (module_body_writes body1) (module_body_reads body1) ->
   *   LocationSet.Disjoint (module_body_writes body2) (module_body_reads body2) ->
   *   exec_module_body rs0 body1 = exec_module_body rs0 body2.
   * Proof.
   *  intros * Hpermute. revert rs0.
   *  induction Hpermute; intros * (\* Hnodup1 Hnodup2 *\) Hdisjoint1 Hdisjoint2.
   *  - simp exec_module_body. reflexivity.
   *  - simp exec_module_body in *. simpl in *.
   *    eapply IHHpermute.
   *    + LocationSet.setdec.
   *    + LocationSet.setdec.
   *  - simp module_body_writes module_body_reads in *.
   *    simp exec_module_body.
   *    simpl.
   *    destruct x as [[x_var x_expr]].
   *    destruct y as [[y_var y_expr]].
   *    simp module_item_writes module_item_reads statement_writes statement_reads expr_reads in *.
   *    simp exec_module_item exec_statement in *; simpl in *.
   *    f_equal.
   *    replace (eval_expr (RegisterState.set_reg _ _ rs0) x_expr) with (eval_expr rs0 x_expr); cycle 1. {
   *      eapply eval_expr_change_regs. symmetry.
   *      eapply RegisterState.match_on_set_reg_elim.
   *      LocationSet.setdec.
   *    }
   *    replace (eval_expr (RegisterState.set_reg _ _ rs0) y_expr) with (eval_expr rs0 y_expr); cycle 1. {
   *      eapply eval_expr_change_regs. symmetry.
   *      eapply RegisterState.match_on_set_reg_elim.
   *      LocationSet.setdec.
   *    }
   *    eapply set_reg_swap. admit. (\* duplicate write *\)
   *  - transitivity (exec_module_body rs0 l').
   *    + eapply IHHpermute1.
   *      * assumption.
   *      * rewrite <- Hpermute1. assumption.
   *    + eapply IHHpermute2.
   *      * erewrite <- Hpermute1. assumption.
   *      * assumption.
   * Admitted. *)
End Facts.

Module DefinedEquivalence.
  Import CombinationalOnly.

  Declare Scope verilog.
  Local Open Scope verilog.

  Record clean_module {i o} (v : vmodule i o) := MkCleanModule { 
    defined_outputs : forall e,
      RegisterState.defined_value_for (LocationSet.of_varset (VarSet.of_list (Verilog.module_inputs v))) e ->
      RegisterState.defined_value_for (module_locations v) (run_vmodule v e)
  }.

  Definition defined_equivalence {i o} (v1 v2 : Verilog.vmodule i o) : Prop :=
      forall init,
        RegisterState.defined_value_for (LocationSet.of_varset (VarSet.of_list i)) init ->
        (run_vmodule v1 init =( LocationSet.of_varset (VarSet.of_list o) )= run_vmodule v2 init).

  Infix "~~" := defined_equivalence (at level 20) : verilog_scope.

  Lemma defined_equivalence_sym {i o} (v1 v2 : vmodule i o):
    v1 ~~ v2 ->
    v2 ~~ v1.
  Proof. unfold "~~". symmetry. auto. Qed.

  Lemma defined_equivalence_trans {i o} (v1 v2 v3 : vmodule i o):
    v1 ~~ v2 -> v2 ~~ v3 -> v1 ~~ v3.
  Proof. unfold "~~". intros. etransitivity. all: auto. Qed.

  Lemma defined_equivalence_refl {i o} (v : vmodule i o) : v ~~ v.
  Proof. unfold "~~". intros. reflexivity. Qed.

  Add Parametric Relation {i o} :
    (Verilog.vmodule i o) defined_equivalence
    reflexivity proved by defined_equivalence_refl
    symmetry proved by defined_equivalence_sym
    transitivity proved by defined_equivalence_trans
    as defined_equivalence_rel.
End DefinedEquivalence.

Module ExactEquivalence.
  Import CombinationalOnly.

  Declare Scope verilog.
  Local Open Scope verilog.

  Definition exact_equivalence {i o} (v1 v2 : Verilog.vmodule i o) : Prop :=
    forall init, run_vmodule v1 init =( LocationSet.of_varset (VarSet.of_list o))= run_vmodule v2 init.

  Infix "~~~" := exact_equivalence (at level 20) : verilog_scope.

  Lemma exact_equivalence_sym {i o} (v1 v2 : vmodule i o) :
    v1 ~~~ v2 ->
    v2 ~~~ v1.
  Proof. unfold "~~~". intros H. symmetry. auto. Qed.

  Lemma exact_equivalence_trans {i o} (v1 v2 v3 : vmodule i o) :
    v1 ~~~ v2 -> v2 ~~~ v3 -> v1 ~~~ v3.
  Proof. unfold "~~~". intros H. etransitivity; eauto. Qed.

  Lemma exact_equivalence_refl {i o} (v : vmodule i o) : v ~~~ v.
  Proof. constructor; reflexivity. Qed.

  Add Parametric Relation {i o} :
    (Verilog.vmodule i o) exact_equivalence
    reflexivity proved by exact_equivalence_refl
    symmetry proved by exact_equivalence_sym
    transitivity proved by exact_equivalence_trans
    as exact_equivalence_rel.

  (* FIXME: This might be needed. Delete if not *)
  (* Global Instance Proper_valid_execution_exact_equivalence {i o} :
   *   Proper (@exact_equivalence i o ==> eq ==> iff) valid_execution.
   * Proof. unfold "~~~", "⇓". solve_proper. Qed. *)

  Lemma equal_exact_equivalence {i o} (v1 v2 : vmodule i o) :
    run_vmodule v1 = run_vmodule v2 ->
    v1 ~~~ v2.
  Proof. unfold "~~~", "⇓". intros <-. reflexivity. Qed.

  Import DefinedEquivalence.

  Lemma exact_equivalence_defined_equivalence {i o} (v1 v2 : vmodule i o) :
    v1 ~~~ v2 ->
    v1 ~~ v2.
  Proof. unfold "~~~", "~~". easy. Qed.

  Lemma exact_by_output_equality {i o} (v1 v2 : vmodule i o) :
    (forall initial, run_vmodule v1 initial =( LocationSet.of_varset (VarSet.of_list o) )= run_vmodule v2 initial) ->
    v1 ~~~ v2.
  Proof. intros H. exact H. Qed.

  (* a ~~~ b -> b ~~ c -> a ~~ c *)
  Global Instance Proper_defined_equivalence_exact_equivalence {i o} :
    Proper
      (@exact_equivalence i o ==> @exact_equivalence i o ==> iff)
      (defined_equivalence).
  Proof. unfold "~~~", "~~". solve_proper. Qed.
End ExactEquivalence.
