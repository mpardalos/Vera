From Stdlib Require Import BinNat.
From Stdlib Require Import String.
From Stdlib Require Import Nat.
From Stdlib Require Import Structures.OrderedTypeEx.
From Stdlib Require Import List.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Relations.
From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Psatz.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Classical.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Setoid.

From vera Require Import Verilog.
From vera Require Import Common.
From vera Require Import Bitvector.
Import (notations) XBV.
Import RawXBV (bit(..)).
From vera Require Import Tactics.
From vera Require Import Decidable.

From Equations Require Import Equations.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Data.Monads.OptionMonad.
From ExtLib Require Import Data.List.

Import ListNotations.
Import MonadLetNotation.
Import SigTNotations.
Local Open Scope monad_scope.
Local Open Scope bv_scope.

Set Bullet Behavior "Strict Subproofs".

Declare Scope verilog.
Local Open Scope verilog.

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


Module RegisterState.
  Module VariableAsMDT <: MiniDecidableType.
    Definition t := Verilog.variable.
    Definition eq_dec (x y : t) := dec (x = y).
  End VariableAsMDT.

  Module VariableAsUDT := Make_UDT(VariableAsMDT).

  Module VariableDepMap := MkDepFunMap(VariableAsUDT).

  Definition register_state := VariableDepMap.t (fun var => XBV.xbv (Verilog.varType var)).

  #[global]
  Notation t := register_state.

  #[global]
  Notation execution := t.

  Definition empty : RegisterState.t :=
    RegisterState.VariableDepMap.empty.

  Lemma empty_get var : empty var = None.
  Proof. cbv. reflexivity. Qed.

  Definition set_reg (var : Verilog.variable) (value : XBV.xbv (Verilog.varType var)) : t -> t :=
    VariableDepMap.insert var value.

  Lemma set_reg_get_in var val regs :
    set_reg var val regs var = Some val.
  Proof.
    unfold set_reg, VariableDepMap.insert.
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
    unfold set_reg, VariableDepMap.insert.
    autodestruct; [contradiction|].
    reflexivity.
  Qed.

  #[global]
  Hint Rewrite RegisterState.set_reg_get_out using congruence : register_state.
                          
  Definition has_value_for (C : Verilog.variable -> Prop) (regs : RegisterState.t) :=
    forall var, C var -> exists xbv, regs var = Some xbv.

  Lemma has_value_for_split_iff (C1 C2 : Verilog.variable -> Prop) regs :
    (has_value_for C1 regs /\ has_value_for C2 regs) <->
      (has_value_for (fun var => C1 var \/ C2 var) regs).
  Proof. unfold has_value_for. crush. Qed.

  Lemma has_value_for_impl C1 C2 e :
    (forall v, C2 v -> C1 v) ->
    has_value_for C1 e ->
    has_value_for C2 e.
  Proof. unfold has_value_for. crush. Qed.

  Ltac unpack_has_value_for :=
    repeat match goal with
      | [ H: has_value_for (fun _ => _ \/ _) _ |- _ ] =>
          rewrite <- has_value_for_split_iff in H;
          destruct H
      | [ H: has_value_for (fun _ => List.In _ (_ ++ _)) _ |- _ ] =>
          setoid_rewrite List.in_app_iff in H
      | [ |- has_value_for (fun _ => List.In _ (_ ++ _)) _ ] =>
          setoid_rewrite List.in_app_iff
      | [ |- has_value_for (fun _ => _ \/ _) _ ] =>
          apply has_value_for_split_iff; split
      end.

  Definition defined_value_for (C : Verilog.variable -> Prop) (regs : RegisterState.t) :=
    forall var, C var -> exists bv, regs var = Some (XBV.from_bv bv).
  
  Lemma defined_value_for_split_iff (C1 C2 : Verilog.variable -> Prop) regs :
    (defined_value_for C1 regs /\ defined_value_for C2 regs) <->
      (defined_value_for (fun var => C1 var \/ C2 var) regs).
  Proof. unfold defined_value_for. crush. Qed.

  Lemma defined_value_for_impl C1 C2 e :
    (forall v, C2 v -> C1 v) ->
    defined_value_for C1 e ->
    defined_value_for C2 e.
  Proof. unfold defined_value_for. crush. Qed.

  Ltac unpack_defined_value_for :=
    repeat match goal with
      | [ H: defined_value_for (fun _ => _ \/ _) _ |- _ ] =>
          rewrite <- defined_value_for_split_iff in H;
          destruct H
      | [ H: defined_value_for (fun _ => List.In _ (_ ++ _)) _ |- _ ] =>
          setoid_rewrite List.in_app_iff in H
      | [ |- defined_value_for (fun _ => List.In _ (_ ++ _)) _ ] =>
          setoid_rewrite List.in_app_iff
      | [ |- defined_value_for (fun _ => _ \/ _) _ ] =>
          apply defined_value_for_split_iff; split
      end.

  Definition match_on (C : Verilog.variable -> Prop) (e1 e2 : RegisterState.t) : Prop :=
    forall var, C var -> e1 var = e2 var.

  Notation "rs1 ={ P }= rs2" :=
    (match_on P rs1 rs2)
    (at level 80) : type_scope.

  Notation "rs1 =( vars )= rs2" :=
    (rs1 ={fun var => In var vars}= rs2)
    (at level 80) : type_scope.

  Lemma match_on_impl C1 C2 e1 e2:
    (forall var, C2 var -> C1 var) ->
    e1 ={ C1 }= e2 ->
    e1 ={ C2 }= e2.
  Proof. unfold match_on. crush. Qed.

  Global Instance Proper_match_on_iff :
    Proper (pointwise_relation Verilog.variable iff ==> eq ==> eq ==> iff) match_on.
  Proof. repeat intro. subst. crush. Qed.

  Global Instance Proper_match_on_impl :
    Proper
      ((pointwise_relation Verilog.variable Basics.impl) --> eq ==> eq ==> Basics.impl)
      match_on.
  Proof. repeat intro. subst. crush. Qed.

  Global Instance DefaultRelation_variable_prop :
    DefaultRelation (A:=Verilog.variable -> Prop) (pointwise_relation Verilog.variable Basics.impl).
  Defined.
  
  Global Instance Proper_defined_value_for_impl :
    Proper
      ((pointwise_relation Verilog.variable Basics.impl) --> eq ==> Basics.impl)
      RegisterState.defined_value_for.
  Proof. repeat intro. subst. crush. Qed.
  
  Global Instance Proper_defined_value_for_iff :
    Proper
      (pointwise_relation Verilog.variable iff ==> eq ==> iff)
      RegisterState.defined_value_for.
  Proof. repeat intro. subst. crush. Qed.
  
  Global Instance Proper_defined_value_for_match C :
    Proper
      (RegisterState.match_on C ==> iff)
      (RegisterState.defined_value_for C).
  Proof.
    unfold "_ ={ _ }= _", defined_value_for.
    repeat intro. split; repeat intro.
    - insterU H. insterU H0.
      rewrite <- H. apply H0.
    - insterU H. insterU H0.
      rewrite H. apply H0.
  Qed.

  Lemma match_on_split_iff C1 C2 regs1 regs2 :
    regs1 ={ fun var => C1 var \/ C2 var }= regs2 <->
      (regs1 ={ C1 }= regs2 /\ regs1 ={ C2 }= regs2).
  Proof. unfold "_ ={ _ }= _". crush. Qed.

  Lemma match_on_app_iff l1 l2 regs1 regs2 :
    (regs1 =( l1 ++ l2 )= regs2) <-> (regs1 =( l1 )= regs2 /\ regs1 =( l2 )= regs2).
  Proof.
    setoid_rewrite List.in_app_iff.
    apply match_on_split_iff.
  Qed.

  Lemma match_on_trans C regs1 regs2 regs3 :
    regs1 ={ C }= regs2 ->
    regs2 ={ C }= regs3 ->
    regs1 ={ C }= regs3.
  Proof.
    unfold "_ ={ _ }= _".
    intros H12 H23 var HC.
    insterU H12. insterU H23.
    crush.
  Qed.

  Lemma match_on_sym C regs1 regs2 :
    regs1 ={ C }= regs2 ->
    regs2 ={ C }= regs1.
  Proof.
    unfold "_ ={ _ }= _".
    intros H var HC.
    insterU H. crush.
  Qed.

  Lemma match_on_refl C regs :
    regs ={ C }= regs.
  Proof. unfold "_ ={ _ }= _". crush. Qed.

  Add Parametric Relation (C : Verilog.variable -> Prop) :
    RegisterState.t (match_on C)
    reflexivity proved by (match_on_refl C)
    symmetry proved by (match_on_sym C)
    transitivity proved by (match_on_trans C)
    as match_on_rel.

  Definition execution_defined_match_on C e1 e2 :=
    e1 ={ C }= e2 /\ RegisterState.defined_value_for C e1.

  Notation "rs1 =!!{ P }!!= rs2" :=
    (execution_defined_match_on P rs1 rs2)
    (at level 80) : type_scope.

  Notation "rs1 =!!( vars )!!= rs2" :=
    (rs1 =!!{fun var => In var vars}!!= rs2)
    (at level 80) : type_scope.

  Lemma defined_match_on_iff C e1 e2 :
    e1 =!!{ C }!!= e2 <->
    forall var, C var -> exists bv, e1 var = Some (XBV.from_bv bv) /\ e2 var = Some (XBV.from_bv bv).
  Proof.
    unfold execution_defined_match_on, "_ ={ _ }= _", RegisterState.defined_value_for.
    split.
    - intros [Hmatch Hdefined] var HC. insterU Hmatch. insterU Hdefined.
      rewrite <- Hmatch. crush.
    - intro H. split.
      + intros var HC. insterU H. destruct H as [? [? ?]]. crush.
      + intros var HC. insterU H. destruct H as [? [? ?]]. crush.
  Qed.

  Lemma execution_defined_match_on_trans C e1 e2 e3:
    e1 =!!{ C }!!= e2 ->
    e2 =!!{ C }!!= e3 ->
    e1 =!!{ C }!!= e3.
  Proof.
    unfold "_ =!!{ _ }!!= _".
    intros [] [].
    split.
    - now transitivity e2.
    - eassumption.
  Qed.

  Lemma execution_defined_match_on_sym C e1 e2:
    e1 =!!{ C }!!= e2 ->
    e2 =!!{ C }!!= e1.
  Proof.
    unfold "_ =!!{ _ }!!= _".
    intros [].
    split.
    - now symmetry.
    - now rewrite <- H.
  Qed.

  Add Parametric Relation (C : Verilog.variable -> Prop) :
    RegisterState.t (execution_defined_match_on C)
    symmetry proved by (execution_defined_match_on_sym C)
    transitivity proved by (execution_defined_match_on_trans C)
    as execution_defiened_match_on_rel.

  Global Instance Proper_has_value_for_impl :
    Proper
      ((pointwise_relation Verilog.variable Basics.impl) --> eq ==> Basics.impl)
      RegisterState.has_value_for.
  Proof. repeat intro. subst. crush. Qed.
  
  Global Instance Proper_has_value_for_iff :
    Proper
      (pointwise_relation Verilog.variable iff ==> eq ==> iff)
      RegisterState.has_value_for.
  Proof.
    unfold pointwise_relation, "_ ={ _ }= _", has_value_for.
    repeat intro. split; repeat intro.
    - subst. setoid_rewrite H in H1. eauto.
    - subst. setoid_rewrite <- H in H1. eauto.
  Qed.
  
  Global Instance Proper_has_value_for_match C :
    Proper
      (RegisterState.match_on C ==> iff)
      (RegisterState.has_value_for C).
  Proof.
    unfold "_ ={ _ }= _", has_value_for.
    repeat intro. split; repeat intro.
    - insterU H. insterU H0.
      rewrite <- H. apply H0.
    - insterU H. insterU H0.
      rewrite H. apply H0.
  Qed.

  Lemma has_value_for_set_reg C regs var x :
    has_value_for C regs ->
    has_value_for C (RegisterState.set_reg var x regs).
  Proof.
    unfold has_value_for.
    intros Hhas_value var' Hvar'.
    destruct Hhas_value with (var:=var'); [assumption|].
    destruct (dec (var' = var)); subst.
    - eexists. rewrite set_reg_get_in; eauto.
    - eexists. rewrite set_reg_get_out; eauto.
  Qed.

  Inductive opt_rel {A} (r : A -> A -> Prop) : option A -> option A -> Prop :=
    | opt_rel_None : opt_rel r None None
    | opt_rel_Some x y : r x y -> opt_rel r (Some x) (Some y)
    .
  
  Definition match_on_opt C := opt_rel (RegisterState.match_on C).
  
  Notation "rs1 =?{ P }?= rs2" :=
    (match_on_opt P rs1 rs2)
    (at level 80) : type_scope.
  
  Notation "rs1 =?( vars )?= rs2" :=
    (rs1 =?{fun var => In var vars}?= rs2)
    (at level 80) : type_scope.
  
  Lemma match_on_opt_refl C r : r =?{ C }?= r.
  Proof.
    unfold "_ =?{ _ }?= _".
    destruct r; constructor; expect 1.
    reflexivity.
  Qed.
  
  Lemma match_on_opt_trans C r1 r2 r3 :
    r1 =?{ C }?= r2 ->
    r2 =?{ C }?= r3 ->
    r1 =?{ C }?= r3.
  Proof.
    unfold "_ =?{ _ }?= _".
    intros H12 H23.
    inv H12; inv H23; constructor; expect 1.
    etransitivity; eassumption.
  Qed.
  
  Lemma match_on_opt_sym C r1 r2 :
    r1 =?{ C }?= r2 ->
    r2 =?{ C }?= r1.
  Proof.
    unfold "_ =?{ _ }?= _".
    intros H12.
    inv H12; constructor; expect 1.
    symmetry. assumption.
  Qed.
    
  Add Parametric Relation (C : Verilog.variable -> Prop) :
    (option RegisterState.t) (match_on_opt C)
    reflexivity proved by (match_on_opt_refl C)
    symmetry proved by (match_on_opt_sym C)
    transitivity proved by (match_on_opt_trans C)
    as match_on_opt_rel.

  Global Instance Proper_match_on_opt_iff :
    Proper (pointwise_relation Verilog.variable iff ==> eq ==> eq ==> iff) match_on_opt.
  Proof.
    repeat intro.
    subst; split; intros Hmatch; inv Hmatch; constructor.
    - now rewrite <- H.
    - now rewrite H.
  Qed.

  Global Instance Proper_match_on_opt_impl :
    Proper
      ((pointwise_relation Verilog.variable Basics.impl) --> eq ==> eq ==> Basics.impl)
      match_on_opt.
  Proof.
    intros C1 C2 Himpl regs1 regs2 [] regs1' regs2' [] Hmatch.
    inv Hmatch; constructor; expect 1.
    now rewrite <- Himpl.
  Qed.

  Lemma match_on_opt_split_iff C1 C2 regs1 regs2 :
    regs1 =?{ fun var => C1 var \/ C2 var }?= regs2 <->
      (regs1 =?{ C1 }?= regs2 /\ regs1 =?{ C2 }?= regs2).
  Proof.
    unfold "_ =?{ _ }?= _".
    split; inversion 1; intuition try (constructor; try crush); expect 1.
    inv H0; try constructor; expect 1.
    inv H1; try constructor; expect 1.
    apply match_on_split_iff. crush.
  Qed.

  Lemma match_on_opt_app_iff l1 l2 regs1 regs2 :
    (regs1 =?( l1 ++ l2 )?= regs2) <-> (regs1 =?( l1 )?= regs2 /\ regs1 =?( l2 )?= regs2).
  Proof.
    setoid_rewrite List.in_app_iff.
    apply match_on_opt_split_iff.
  Qed.

  Definition limit_to_regs (vars : list Verilog.variable) (regs : RegisterState.t) : RegisterState.t :=
    fun var =>
      match dec (In var vars) with
      | left prf => regs var
      | right prf => None
      end.

  Notation "st // regs" := (limit_to_regs regs st) (at level 20) : verilog.

  Lemma limit_to_regs_twice st regs :
    st // regs // regs = st // regs.
  Proof.
    unfold "//".
    apply functional_extensionality_dep. intros.
    autodestruct; reflexivity.
  Qed.

  Lemma limit_to_regs_empty st : st // [] = empty.
  Proof.
    apply functional_extensionality_dep.
    unfold "//", empty, RegisterState.VariableDepMap.empty.
    intros. autodestruct; crush.
  Qed.

  Lemma limit_to_regs_get_skip var var' st vars :
    var <> var' ->
    (st // (var :: vars)) var' = (st // vars) var'.
  Proof. unfold "//". intros Hin. autodestruct; crush. Qed.

  Lemma limit_to_regs_get_in var st vars :
    In var vars ->
    (st // vars) var = st var.
  Proof. unfold "//". intros Hin. autodestruct; crush. Qed.

  Lemma limit_to_regs_get_out var st vars :
    ~ In var vars ->
    (st // vars) var = None.
  Proof. unfold "//". intros Hin. autodestruct; crush. Qed.

  Lemma limit_to_regs_set_reg_in var x st vars :
    In var vars ->
    (RegisterState.set_reg var x st) // vars
      = RegisterState.set_reg var x (st // vars).
  Proof.
   intros.
   apply functional_extensionality_dep. intros var'.
   destruct (dec (In var' vars)).
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
    ~ In var vars ->
    (RegisterState.set_reg var x st) // vars
      = st // vars.
  Proof.
    intros.
    apply functional_extensionality_dep. intros var'.
    destruct (dec (In var' vars)).
    - rewrite ! limit_to_regs_get_in by assumption.
      rewrite RegisterState.set_reg_get_out by crush.
      reflexivity.
    - rewrite ! limit_to_regs_get_out by assumption.
      reflexivity.
  Qed.
  Lemma set_reg_limit_remove var vars v regs :
    RegisterState.set_reg var v (regs // (var :: vars)) =
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
    (r1 // l = r2 // l) <-> (r1 =( l )= r2).
  Proof. Admitted.

  Lemma has_value_for_limit_to_regs vars st :
    RegisterState.has_value_for (fun var => In var vars) st ->
    RegisterState.has_value_for (fun var => In var vars) (st // vars).
  Proof.
    unfold RegisterState.has_value_for, "//".
    intros. autodestruct; crush.
  Qed.

  Lemma match_on_empty C regs1 regs2 :
    (forall var, ~ (C var)) ->
    regs1 ={ C }= regs2.
  Proof. unfold "_ ={ _ }= _". crush. Qed.

  Lemma match_on_set_reg_elim2_in C var x regs1 regs2 :
    regs1 ={ C }= regs2 ->
    set_reg var x regs1 ={ C }= set_reg var x regs2.
  Proof.
    unfold "_ =( _ )= _". intros Hmatch var' Hvar'.
    destruct (dec (var' = var)).
    - subst. rewrite ! RegisterState.set_reg_get_in; crush.
    - subst. rewrite ! RegisterState.set_reg_get_out; crush.
  Qed.

  Lemma match_on_set_reg_elim2_out C var x y regs1 regs2 :
    ~ C var ->
    regs1 ={ C }= regs2 ->
    set_reg var x regs1 ={ C }= set_reg var y regs2.
  Proof.
    unfold "_ =( _ )= _". intros Hvar Hmatch var' Hvar'.
    destruct (dec (var' = var)).
    - subst. rewrite ! RegisterState.set_reg_get_in; crush.
    - subst. rewrite ! RegisterState.set_reg_get_out; crush.
  Qed.

  Lemma match_on_set_reg_elim2 var x regs1 regs2 :
    set_reg var x regs1 =( [var] )= set_reg var x regs2.
  Proof.
    unfold "_ =( _ )= _". intros var' Hvarin. inv Hvarin; [|crush].
    rewrite ! set_reg_get_in. crush.
  Qed.

  Lemma match_on_set_reg_elim C var x regs :
    ~ C var ->
    set_reg var x regs ={ C }= regs.
  Proof.
    unfold "_ ={ _ }= _". intros HnC var' HC.
    erewrite set_reg_get_out by crush.
    crush.
  Qed.

  Ltac unpack_match_on :=
    repeat match goal with
      | [ H: match_on (fun _ => _ \/ _) _ _ |- _ ] =>
          apply match_on_split_iff in H;
          destruct H
      | [ H: match_on (fun _ => List.In _ (_ ++ _)) _ _ |- _ ] =>
          setoid_rewrite List.in_app_iff in H
      | [ |- match_on (fun _ => List.In _ (_ ++ _)) _ _ ] =>
          setoid_rewrite List.in_app_iff
      | [ |- match_on (fun _ => _ \/ _) _ _ ] =>
          apply match_on_split_iff; split
      | [ H: match_on_opt (fun _ => _ \/ _) _ _ |- _ ] =>
          apply match_on_opt_split_iff in H;
          destruct H
      | [ H: match_on_opt (fun _ => List.In _ (_ ++ _)) _ _ |- _ ] =>
          setoid_rewrite List.in_app_iff in H
      | [ |- match_on_opt (fun _ => List.In _ (_ ++ _)) _ _ ] =>
          setoid_rewrite List.in_app_iff
      | [ |- match_on_opt (fun _ => _ \/ _) _ _ ] =>
          apply match_on_opt_split_iff; split
      end.
End RegisterState.

Export (notations) RegisterState.

Module Sort.
  Import Verilog.

  Inductive module_items_sorted : list Verilog.variable -> list Verilog.module_item -> Prop :=
    | module_items_sorted_nil vars : module_items_sorted vars []
    | module_items_sorted_cons vars mi mis :
      list_subset (module_item_reads mi) vars ->
      disjoint (module_item_writes mi) vars ->
      (* disjoint (Verilog.module_body_writes (mi :: mis)) (Verilog.module_item_reads mi) -> *)
      module_items_sorted (Verilog.module_item_writes mi ++ vars) mis ->
      module_items_sorted vars (mi :: mis)
  .

  Global Instance dec_module_items_sorted vars ms : DecProp (module_items_sorted vars ms).
  Proof.
    revert vars.
    induction ms; intros vars.
    - left. constructor.
    - destruct (dec (list_subset (Verilog.module_item_reads a) vars));
        [|right; inversion 1; crush].
      destruct (dec (disjoint (Verilog.module_item_writes a) vars));
        [|right; inversion 1; crush].
      destruct (IHms (Verilog.module_item_writes a ++ vars));
        [|right; inversion 1; crush].
      left. constructor; auto.
  Defined.
  
  Record selection (l : list module_item) :=
    MkSelection {
      mi : module_item;
      rest : list module_item;
      wf : Permutation (mi :: rest) l
    }.

  Lemma module_items_sorted_no_overwrite inputs body :
    module_items_sorted inputs body ->
    disjoint (module_body_writes body) inputs.
  Proof.
    induction 1.
    - constructor.
    - simp module_body_writes.
      unfold disjoint in *.
      rewrite -> Forall_forall in *.
      setoid_rewrite in_app_iff.
      setoid_rewrite in_app_iff in IHmodule_items_sorted.
      crush.
  Qed.
  
  Lemma module_items_sorted_permute_vars l l' body :
    Permutation l l' ->
    module_items_sorted l body ->
    module_items_sorted l' body.
  Proof.
    intros Hpermute Hsorted.
    revert l' Hpermute.
    induction Hsorted; intros; constructor.
    - now rewrite <- Hpermute.
    - now rewrite <- Hpermute.
    - apply IHHsorted.
      apply Permutation_app_head.
      assumption.
  Qed.
  
  Global Instance Proper_module_items_sorted_permute_vars :
    Proper (@Permutation _ ==> eq ==> iff) module_items_sorted.
  Proof.
    repeat intro. subst.
    split; intros.
    - eapply module_items_sorted_permute_vars.
      + eassumption.
      + eassumption.
    - eapply module_items_sorted_permute_vars.
      + symmetry. eassumption.
      + assumption.
  Qed.
  
  Lemma module_items_sorted_skip vars_skip vars_rest body :
    disjoint vars_skip (module_body_reads body) ->
    module_items_sorted (vars_skip ++ vars_rest) body ->
    module_items_sorted vars_rest body.
  Proof.
    revert vars_skip vars_rest.
    induction body; intros * Hnot_var_in Hsorted; [constructor|].
    inv Hsorted.
    simp module_body_reads in *. unpack_in.
    disjoint_saturate.
    constructor.
    - unfold list_subset, disjoint in *.
      rewrite -> Forall_forall in *.
      repeat match goal with [ H : context[In _ (_ ++ _)] |- _ ] =>
        setoid_rewrite in_app_iff in H
      end.
      crush.
    - now symmetry.
    - eapply IHbody with (vars_skip:=vars_skip).
      + now symmetry.
      + rewrite app_assoc.
        setoid_rewrite Permutation_app_comm with (l:=vars_skip).
        rewrite <- app_assoc.
        assumption.
  Qed.
  
  Lemma module_items_sorted_skip1 var_skip vars_rest body :
    ~ In var_skip (module_body_reads body) ->
    module_items_sorted (var_skip :: vars_rest) body ->
    module_items_sorted vars_rest body.
  Proof.
    intros * Hnot_in Hsorted.
    apply module_items_sorted_skip with (vars_skip:=[var_skip]).
    - constructor; crush.
    - simpl. assumption.
  Qed.

  
  Equations sort_module_items_select (vars_ready : list variable) (mis : list module_item) : option (selection mis) := {
    | vars_ready, [] => @None _
    | vars_ready, hd :: tl with
      dec (list_subset (module_item_reads hd) vars_ready),
      dec (disjoint (module_item_writes hd) vars_ready) => {
      | right _, _ => None
      | left _, right _ =>
          let* (MkSelection _ selected selected_tl _) := sort_module_items_select vars_ready tl in
          Some (MkSelection (hd :: tl) selected (hd :: selected_tl) _ )
      | left prf1, left prf2 => Some (MkSelection (hd :: tl) hd tl _)
    }
  }.
  Next Obligation.
    etransitivity. { apply perm_swap. }
    apply perm_skip. assumption.
  Qed.
  
  Equations sort_module_items
    (vars_ready : list variable)
    (mis : list module_item)
    : option (list module_item) by wf (length mis) lt :=
    sort_module_items vars_ready [] := Some [];
    sort_module_items vars_ready mis with (sort_module_items_select vars_ready mis) := {
      | None => None
      | Some (MkSelection _ ready rest _) with (sort_module_items (module_item_writes ready ++ vars_ready) rest) => {
        | None => None
        | Some sorted_rest => Some (ready :: sorted_rest)
      }
    }
  .
  Next Obligation. apply_somewhere Permutation_length. simpl in *. lia. Qed.
  
  Lemma module_items_sorted_select inputs mi mis :
    module_items_sorted inputs (mi :: mis) ->
    sort_module_items_select inputs (mi :: mis) = Some (MkSelection _ mi mis (perm_skip mi (reflexivity mis))).
  Proof.
    intros Hsorted.
    funelim (sort_module_items_select inputs (mi :: mis)); cbn in *.
    - f_equal. f_equal. apply proof_irrelevance.
    - inv Hsorted. contradiction.
    - inv Hsorted. contradiction.
  Qed.

  Lemma module_items_select_ready vars mis mi rest wf :
    sort_module_items_select vars mis = Some (MkSelection mis mi rest wf) ->
    list_subset (module_item_reads mi) vars.
  Proof.
    intros H.
    funelim (sort_module_items_select vars mis);
      rewrite <- Heqcall in *; clear Heqcall.
    - discriminate.
    - inv H. assumption.
    - monad_inv. eauto.
    - discriminate.
  Qed.

  Lemma module_items_select_no_overwrite vars mis mi rest wf :
    sort_module_items_select vars mis = Some (MkSelection mis mi rest wf) ->
    disjoint (module_item_writes mi) vars.
  Proof.
    intros H.
    funelim (sort_module_items_select vars mis);
      rewrite <- Heqcall in *; clear Heqcall.
    - discriminate.
    - inv H. assumption.
    - monad_inv. eauto.
    - discriminate.
  Qed.

  Theorem sort_module_items_permutation body : forall vars_ready body',
    sort_module_items vars_ready body = Some body' ->
    Permutation body body'.
  Proof.
    intros.
    funelim (sort_module_items vars_ready body);
      rewrite <- Heqcall in *; clear Heqcall; try discriminate.
    - inv H. reflexivity.
    - inv H. etransitivity. { symmetry. eassumption. }
      apply perm_skip. eapply Hind. eapply Heq.
  Qed.

  Theorem sort_module_items_sorted inputs body body':
    sort_module_items inputs body = Some body' ->
    module_items_sorted inputs body'.
  Proof.
    intros Hsort.
    funelim (sort_module_items inputs body);
      rewrite <- Heqcall in *; clear Heqcall.
    - inv Hsort. constructor.
    - discriminate.
    - inv Hsort.
      constructor.
      + eapply module_items_select_ready. eassumption.
      + eapply module_items_select_no_overwrite. eassumption.
      + apply Hind. assumption.
    - discriminate.
  Qed.

  Theorem sort_module_items_stable inputs body :
    module_items_sorted inputs body ->
    sort_module_items inputs body = Some body.
  Proof.
    intros Hsorted.
    funelim (sort_module_items inputs body);
      try rewrite <- Heqcall in *; clear Heqcall.
    - reflexivity.
    - rewrite module_items_sorted_select in Heq; crush.
    - rewrite module_items_sorted_select in Heq0 by crush.
      inv Hsorted. inv Heq0.
      rewrite Hind in Heq; crush.
    - rewrite module_items_sorted_select in Heq0 by crush.
      inv Hsorted. inv Heq0.
      rewrite Hind in Heq; crush.
  Qed.
  
  Definition vmodule_sortable (v : vmodule) : Prop :=
    exists sorted, sort_module_items (Verilog.module_inputs v) (Verilog.modBody v) = Some sorted.
  
  (* Checking that typeclasses eauto can indeed find this instance *)
  Goal (forall v, DecProp (vmodule_sortable v)). typeclasses eauto. Qed.
End Sort.

Module CombinationalOnly.
  Export Sort.

  Definition Process := Verilog.module_item.

  Definition variable_names vars : list string :=
    map Verilog.varName vars.

  Equations bv_binop {w} : (BV.bitvector w -> BV.bitvector w -> BV.bitvector w) -> XBV.xbv w -> XBV.xbv w -> XBV.xbv w :=
    bv_binop f l r with XBV.to_bv l, XBV.to_bv r => {
      | Some lbv, Some rbv => XBV.from_bv (f lbv rbv)
      | _, _ => XBV.exes (XBV.size l)
      }.

  Definition bitwise_binop_raw (f : bit -> bit -> bit) (l r : RawXBV.xbv) : RawXBV.xbv :=
    map2 f l r.

  Lemma map2_size {A B C} (f : A -> B -> C) (l : list A) (r : list B) :
    length (map2 f l r) = min (length l) (length r).
  Proof.
    funelim (map2 f l r); simp map2; simpl; try crush.
  Qed.

  Definition bitwise_binop_raw_size f l r :
    RawXBV.size l = RawXBV.size r ->
    RawXBV.size (bitwise_binop_raw f l r) = RawXBV.size l.
  Proof.
    intros.
    unfold RawXBV.size, bitwise_binop_raw in *.
    rewrite map2_size.
    lia.
  Qed.

  Local Obligation Tactic := intros.

  Program Definition bitwise_binop {n} (f : bit -> bit -> bit) (l r : XBV.xbv n) : XBV.xbv n :=
    {| XBV.bv := bitwise_binop_raw f (XBV.bits l) (XBV.bits r) |}.
  Next Obligation.
    rewrite bitwise_binop_raw_size; now rewrite ! XBV.wf.
  Qed.

  Equations and_bit : bit -> bit -> bit :=
    and_bit I I := I;
    and_bit O _ := O;
    and_bit _ O := O;
    and_bit X _ := X;
    and_bit _ X := X.

  Equations or_bit : bit -> bit -> bit :=
    or_bit O O := O;
    or_bit I _ := I;
    or_bit _ I := I;
    or_bit X _ := X;
    or_bit _ X := X.

  Equations eval_arithmeticop {n} (op : Verilog.arithmeticop) : XBV.xbv n -> XBV.xbv n -> XBV.xbv n :=
    eval_arithmeticop Verilog.ArithmeticPlus l r := bv_binop (@BV.bv_add _) l r;
    eval_arithmeticop Verilog.ArithmeticMinus l r := bv_binop (fun bvl bvr => BV.bv_add bvl (BV.bv_neg bvr)) l r;
    eval_arithmeticop Verilog.ArithmeticStar l r := bv_binop (@BV.bv_mult _) l r;
  .

  Equations eval_bitwiseop {n} (op : Verilog.bitwiseop) : XBV.xbv n -> XBV.xbv n -> XBV.xbv n :=
    eval_bitwiseop Verilog.BinaryBitwiseAnd l r := bitwise_binop and_bit l r;
    eval_bitwiseop Verilog.BinaryBitwiseOr l r := bitwise_binop or_bit l r;
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

  Equations eval_unaryop {n} (op : Verilog.unaryop) (operand : XBV.xbv n) : XBV.xbv n :=
    eval_unaryop Verilog.UnaryPlus x := x
  .

  (* Notation rewriting a b e := (@eq_rect_r _ a _ e b _). *)
  (* Notation with_rewrite e := (eq_rect_r _ e _). *)

  Import EqNotations.

  Equations convert {from} (to : N) (value : XBV.xbv from) : XBV.xbv to :=
    convert to value with dec (from < to)%N := {
      | left Hlt => rew _ in XBV.concat (XBV.zeros (to - from)%N) value
      | right Hge with dec (from > to)%N => {
        | left Hgr => XBV.extr value 0 to;
        | right Hle => rew _ in value
        }
      }.
  Next Obligation. crush. Qed.
  Next Obligation. crush. Qed.

  Definition select_bit {w1 w2} (vec : XBV.xbv w1) (idx : XBV.xbv w2) : XBV.xbv 1 :=
    match XBV.to_N idx with
    | None => XBV.of_bits [X]
    | Some n => XBV.of_bits [XBV.bitOf (N.to_nat n) vec]
    end.

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
    eval_expr {w} (regs: RegisterState.t) (e : Verilog.expression w) : option (XBV.xbv w) :=
    eval_expr regs (Verilog.UnaryOp op operand) :=
      let* operand_val := eval_expr regs operand in
      Some (eval_unaryop op operand_val);
    eval_expr regs (Verilog.ArithmeticOp op lhs rhs) :=
      let* lhs_val := eval_expr regs lhs in
      let* rhs_val := eval_expr regs rhs in
      Some (eval_arithmeticop op lhs_val rhs_val);
    eval_expr regs (Verilog.BitwiseOp op lhs rhs) :=
      let* lhs_val := eval_expr regs lhs in
      let* rhs_val := eval_expr regs rhs in
      Some (eval_bitwiseop op lhs_val rhs_val);
    eval_expr regs (Verilog.ShiftOp op lhs rhs) :=
      let* lhs_val := eval_expr regs lhs in
      let* rhs_val := eval_expr regs rhs in
      Some (eval_shiftop op lhs_val rhs_val);
    eval_expr regs (Verilog.Conditional cond tBranch fBranch) :=
      let* cond_val := eval_expr regs cond in
      let* tBranch_val := eval_expr regs tBranch in
      let* fBranch_val := eval_expr regs fBranch in
      Some (eval_conditional cond_val tBranch_val fBranch_val);
    eval_expr regs (Verilog.BitSelect vec idx) :=
      let* vec_val := eval_expr regs vec in
      let* idx_val := eval_expr regs idx in
      Some (select_bit vec_val idx_val);
    eval_expr regs (Verilog.Resize t expr) :=
      let* val := eval_expr regs expr in
      Some (convert t val);
    eval_expr regs (Verilog.Concatenation e1 e2) :=
      let* val1 := eval_expr regs e1 in
      let* val2 := eval_expr regs e2 in
      Some (XBV.concat val1 val2);
    eval_expr regs (Verilog.IntegerLiteral _ val) :=
      Some (XBV.from_bv val) ;
    eval_expr regs (Verilog.NamedExpression var) :=
      regs var.

  Equations
    exec_statement (regs : RegisterState.t) (stmt : Verilog.statement) : option RegisterState.t by struct :=
    exec_statement regs (Verilog.BlockingAssign (Verilog.NamedExpression var) rhs) :=
      let* rhs_val := eval_expr regs rhs in
      Some (RegisterState.set_reg var rhs_val regs) ;
    exec_statement regs (Verilog.BlockingAssign lhs rhs) :=
      None;
  .

  Equations
    exec_module_item : RegisterState.t -> Verilog.module_item -> option RegisterState.t :=
    exec_module_item st (Verilog.AlwaysComb stmt ) :=
      exec_statement st stmt;
  .

  Equations
    exec_module_body : RegisterState.t -> list Verilog.module_item -> option RegisterState.t :=
    exec_module_body regs [] := Some regs;
    exec_module_body regs (mi :: mis) :=
      let* regs' := exec_module_item regs mi in
      exec_module_body regs' mis;
  .

  Definition mk_initial_state (v : Verilog.vmodule) (regs : RegisterState.t) : RegisterState.t :=
    regs // Verilog.module_inputs v.

  Definition run_vmodule (v : Verilog.vmodule) (inputs : RegisterState.t) : option RegisterState.t :=
    let* sorted := sort_module_items (Verilog.module_inputs v) (Verilog.modBody v) in
    exec_module_body (mk_initial_state v inputs) sorted.

  Notation execution := RegisterState.t.

  (* TODO: This could possible use module_body_writes instead of
  module_outputs. That would give us an internal view of the
  module. Instead, here we have a version that views a module as a
  black box.

  Notes:
  - This is the version that we *need* for equivalence.
  - The two versions are identical for modules after assignment-forwarding.
  - The alternative might be useful for defining transformations on
    modules (not sure, things like assignment forwarding don't keep
    the internal state, maybe this is the version we want.)
    *)
  Definition valid_execution (v : Verilog.vmodule) (e : execution) :=
    exists (e' : execution),
      run_vmodule v (e // Verilog.module_inputs v) = Some e'
      /\ RegisterState.has_value_for (fun var => List.In var (Verilog.module_inputs v)) e
      /\ RegisterState.has_value_for (fun var => List.In var (Verilog.module_outputs v)) e
      /\ e' =( Verilog.module_inputs v ++ Verilog.module_outputs v )= e.

  Infix "⇓" := valid_execution (at level 20) : verilog.

  (** All variables of v have a value in the execution *)
  Definition complete_execution (v : Verilog.vmodule) (e : execution) :=
    RegisterState.has_value_for (fun var => In var (Verilog.modVariables v)) e.

  (** All variables of v, *and no other variables*, have a value in the execution *)
  Definition exact_execution (v : Verilog.vmodule) (e : execution) :=
    forall var, In var (Verilog.modVariables v) <-> exists bv, e var = Some bv.

  Definition execution_not_x (e : execution) name :=
    forall v, e name = Some v -> ~ XBV.has_x v.

  Definition execution_no_exes_for C (e : execution) :=
    forall var, C var -> execution_not_x e var.

  Definition execution_no_exes := execution_no_exes_for (fun _ => True).

  Global Instance Proper_execution_no_exes_for :
    Proper (pointwise_relation Verilog.variable iff ==> eq ==> iff) execution_no_exes_for.
  Proof. repeat intro. subst. crush. Qed.

  (* Modules are valid if they run to completion for all complete inputs *)
  Definition valid_module (v : Verilog.vmodule) :=
    forall initial : RegisterState.t,
      (RegisterState.has_value_for (fun var => In var (Verilog.module_inputs v)) initial) ->
      exists final, run_vmodule v initial = Some final.
End CombinationalOnly.

Module Facts.
  Import CombinationalOnly.

  Add Parametric Morphism : Verilog.module_body_reads
    with signature (@Permutation Verilog.module_item) ==> (@Permutation Verilog.variable)
    as module_body_reads_permute.
  Proof.
    intros x y Hpermutation; induction Hpermutation; simp module_body_reads in *.
    - constructor.
    - erewrite IHHpermutation. reflexivity.
    - eapply Permutation_app_swap_app.
    - etransitivity; eassumption.
  Qed.

  Add Parametric Morphism : Verilog.module_body_writes
    with signature (@Permutation Verilog.module_item) ==> (@Permutation Verilog.variable)
    as module_body_writes_permute.
  Proof.
    intros x y Hpermutation; induction Hpermutation; simp module_body_writes in *.
    - constructor.
    - erewrite IHHpermutation. reflexivity.
    - eapply Permutation_app_swap_app.
    - etransitivity; eassumption.
  Qed.

  Lemma eval_expr_change_regs w (e : Verilog.expression w) : forall regs regs',
    regs =(Verilog.expr_reads e)= regs' ->
    eval_expr regs e = eval_expr regs' e.
  Proof.
    induction e; intros; simp eval_expr expr_reads in *;
      RegisterState.unpack_match_on;
      try erewrite IHe with (regs':=regs') by assumption;
      try erewrite IHe1 with (regs':=regs') by assumption;
      try erewrite IHe2 with (regs':=regs') by assumption;
      try erewrite IHe3 with (regs':=regs') by assumption;
      try reflexivity;
      [idtac].
    unfold "_ =( _ )= _" in H. insterU H.
    crush.
  Qed.

  Lemma eval_expr_has_values_some w (e : Verilog.expression w) regs :
    RegisterState.has_value_for (fun var => In var (Verilog.expr_reads e)) regs ->
    exists x, eval_expr regs e = Some x.
  Proof.
    intros Hhas_value.
    induction e; intros; simp eval_expr expr_reads in *;
    RegisterState.unpack_has_value_for;
    try (destruct IHe; [assumption|replace (eval_expr regs e)]);
    try (destruct IHe1; [assumption|replace (eval_expr regs e1)]);
    try (destruct IHe2; [assumption|replace (eval_expr regs e2)]);
    try (destruct IHe3; [assumption|replace (eval_expr regs e3)]);
    simpl; eauto; expect 1.
    apply Hhas_value. crush.
  Qed.

  (***** Statements ***********)

  Lemma exec_statement_change_regs stmt regs1 regs2 :
    regs1 =(Verilog.statement_reads stmt)= regs2 ->
    exec_statement regs1 stmt
      =?(Verilog.statement_writes stmt)?=
    exec_statement regs2 stmt.
  Proof.
    intros Hmatch.
    funelim (exec_statement regs1 stmt);
      try rewrite <- Heqcall in *; clear Heqcall;
      simp exec_statement in *; simpl;
      try solve [constructor]; expect 1.
    simp exec_statement statement_reads statement_writes expr_reads in *.
    erewrite eval_expr_change_regs by eassumption.
    autodestruct_eqn E; constructor; expect 1.
    eapply RegisterState.match_on_set_reg_elim2.
  Qed.

  Lemma exec_statement_change_regs_some stmt regs1 regs2 : forall regs1' regs2',
    regs1 =(Verilog.statement_reads stmt)= regs2 ->
    exec_statement regs1 stmt = Some regs1' ->
    exec_statement regs2 stmt = Some regs2' ->
    regs1' =(Verilog.statement_writes stmt)= regs2'.
  Proof.
    intros * Hmatch Hexec1 Hexec2.
    pose proof (exec_statement_change_regs stmt regs1 regs2 ltac:(assumption)) as H.
    rewrite Hexec1 in H.
    rewrite Hexec2 in H.
    inv H.
    assumption.
  Qed.

  Lemma exec_statement_change_regs_none stmt regs1 regs2 :
    regs1 =(Verilog.statement_reads stmt)= regs2 ->
    exec_statement regs1 stmt = None ->
    exec_statement regs2 stmt = None.
  Proof.
    intros * Hmatch Hexec1.
    pose proof (exec_statement_change_regs stmt regs1 regs2 ltac:(assumption)) as H.
    rewrite Hexec1 in H.
    inv H.
    reflexivity.
  Qed.

  Lemma exec_statement_change_preserve l stmt regs1 regs2 :
    regs1 =( Verilog.statement_reads stmt )= regs2 ->
    regs1 =( l )= regs2 ->
    exec_statement regs1 stmt =?( l )?= exec_statement regs2 stmt.
  Proof.
    intros Hmatch_other Hmatch_reads.
    destruct stmt; expect 1.
    destruct lhs; simp exec_statement; try constructor; expect 1.
    simpl; simp exec_statement statement_writes statement_reads expr_reads in *.
    disjoint_saturate.
    erewrite eval_expr_change_regs by eassumption.
    destruct (eval_expr regs2 rhs); constructor; expect 1.
    apply RegisterState.match_on_set_reg_elim2_in.
    assumption.
  Qed.

  Lemma exec_statement_change_preserve_reads stmt regs1 regs2 :
    regs1 =( Verilog.statement_reads stmt )= regs2 ->
    exec_statement regs1 stmt =?( Verilog.statement_reads stmt )?= exec_statement regs2 stmt.
  Proof. auto using exec_statement_change_preserve. Qed.

  Lemma exec_statement_preserve stmt regs regs' l :
    disjoint l (Verilog.statement_writes stmt) ->
    exec_statement regs stmt = Some regs' ->
    regs =( l )= regs'.
  Proof.
    intros Hdisjoint Hexec.
    funelim (exec_statement regs stmt);
      rewrite <- Heqcall in *; clear Heqcall;
      simp statement_writes expr_reads in *;
      try discriminate; expect 1.
    monad_inv. disjoint_saturate.
    symmetry. apply RegisterState.match_on_set_reg_elim. assumption.
  Qed.

  (***** / statements ***********)

  (***** Module items ***********)

  Lemma exec_module_item_change_regs mi regs1 regs2 :
    regs1 =(Verilog.module_item_reads mi)= regs2 ->
    exec_module_item regs1 mi
      =?(Verilog.module_item_writes mi)?=
    exec_module_item regs2 mi.
  Proof.
    intros Hmatch.
    funelim (exec_module_item regs1 mi);
      try rewrite <- Heqcall in *; clear Heqcall;
      simp exec_module_item in *; simpl;
      try solve [constructor]; expect 1.
    simp exec_module_item module_item_reads module_item_writes expr_reads in *.
    apply exec_statement_change_regs. assumption.
  Qed.

  Lemma exec_module_item_change_regs_some mi regs1 regs2 : forall regs1' regs2',
    regs1 =(Verilog.module_item_reads mi)= regs2 ->
    exec_module_item regs1 mi = Some regs1' ->
    exec_module_item regs2 mi = Some regs2' ->
    regs1' =(Verilog.module_item_writes mi)= regs2'.
  Proof.
    intros * Hmatch Hexec1 Hexec2.
    pose proof (exec_module_item_change_regs mi regs1 regs2 ltac:(assumption)) as H.
    rewrite Hexec1 in H.
    rewrite Hexec2 in H.
    inv H.
    assumption.
  Qed.

  Lemma exec_module_item_change_regs_none mi regs1 regs2 :
    regs1 =(Verilog.module_item_reads mi)= regs2 ->
    exec_module_item regs1 mi = None ->
    exec_module_item regs2 mi = None.
  Proof.
    intros * Hmatch Hexec1.
    pose proof (exec_module_item_change_regs mi regs1 regs2 ltac:(assumption)) as H.
    rewrite Hexec1 in H.
    inv H.
    reflexivity.
  Qed.

  Lemma exec_module_item_change_preserve mi regs1 regs2 :
    regs1 =( Verilog.module_item_reads mi )= regs2 ->
    forall l, regs1 =( l )= regs2 ->
    exec_module_item regs1 mi =?( l )?= exec_module_item regs2 mi.
  Proof.
    intros Hmatch_other Hmatch_reads.
    destruct mi; expect 1.
    simpl; simp exec_module_item module_item_writes module_item_reads expr_reads in *.
    apply exec_statement_change_preserve; assumption.
  Qed.

  Lemma exec_module_item_change_preserve_reads mi regs1 regs2 :
    regs1 =( Verilog.module_item_reads mi )= regs2 ->
    exec_module_item regs1 mi =?( Verilog.module_item_reads mi )?= exec_module_item regs2 mi.
  Proof. auto using exec_module_item_change_preserve. Qed.

  Lemma exec_module_item_preserve mi regs regs' l :
    disjoint l (Verilog.module_item_writes mi) ->
    exec_module_item regs mi = Some regs' ->
    regs =( l )= regs'.
  Proof.
    intros Hdisjoint Hexec.
    funelim (exec_module_item regs mi);
      rewrite <- Heqcall in *; clear Heqcall;
      simp module_item_writes expr_reads in *;
      try discriminate; expect 1.
    eapply exec_statement_preserve; eassumption.
  Qed.

  (************* /module items ***********)

  (***** module bodies ***********)

  Lemma exec_module_body_change_preserve l body regs1 regs2 :
    regs1 =( Verilog.module_body_reads body )= regs2 ->
    regs1 =( l )= regs2 ->
    exec_module_body regs1 body =?( l )?= exec_module_body regs2 body.
  Proof.
    revert l regs1 regs2.
    induction body; intros * Hmatch_reads Hmatch_other.
    - simp exec_module_body. constructor. assumption.
    - simp exec_module_body module_body_reads in *. simpl in *.
      RegisterState.unpack_match_on.
      (* TODO: This is a mess, and needs some tactic work *)
      pose proof (exec_module_item_change_preserve a regs1 regs2 ltac:(assumption)) as Hmatch_mi.
      pose proof Hmatch_mi as Hmatch_mi'. insterU Hmatch_mi'.
      destruct (exec_module_item regs1 a); inv Hmatch_mi'; replace (exec_module_item regs2 a) in *.
      + apply IHbody; eauto; expect 1.
        specialize (Hmatch_mi (Verilog.module_body_reads body) ltac:(assumption)). inv Hmatch_mi.
	assumption.
      + constructor.
  Qed.

  Lemma exec_module_body_change_regs body regs1 regs2 :
    regs1 =(Verilog.module_body_reads body)= regs2 ->
    exec_module_body regs1 body
      =?(Verilog.module_body_writes body)?=
    exec_module_body regs2 body.
  Proof.
    intros Hmatch.
    funelim (exec_module_body regs1 body);
      try rewrite <- Heqcall in *; clear Heqcall;
      simp exec_module_body in *; simpl;
      try (constructor; assumption); expect 1.
    simp module_body_reads module_body_writes in *.
    pose proof (exec_module_item_change_regs mi0 regs regs2 ltac:(RegisterState.unpack_match_on; assumption)) as Hmatch_mi.
    destruct (exec_module_item regs mi0) eqn:Hexec_mi; inv Hmatch_mi; [|constructor].
    RegisterState.unpack_match_on.
    - apply exec_module_body_change_preserve; try assumption; expect 1.
      (* TODO: As above, this needs some work... *)
      pose proof (exec_module_item_change_preserve mi0 _ _ ltac:(eassumption) (Verilog.module_body_reads mis) ltac:(assumption)) as Hmatch_mi.
      replace (exec_module_item regs mi0) in Hmatch_mi.
      replace (exec_module_item regs2 mi0) in Hmatch_mi.
      inv Hmatch_mi.
      assumption.
    - apply H.
      pose proof (exec_module_item_change_preserve mi0 _ _ ltac:(eassumption) (Verilog.module_body_reads mis) ltac:(assumption)) as Hmatch_mi.
      replace (exec_module_item regs mi0) in Hmatch_mi.
      replace (exec_module_item regs2 mi0) in Hmatch_mi.
      inv Hmatch_mi.
      assumption.
  Qed.

  Lemma exec_module_body_change_regs_some body regs1 regs2 : forall regs1' regs2',
    regs1 =(Verilog.module_body_reads body)= regs2 ->
    exec_module_body regs1 body = Some regs1' ->
    exec_module_body regs2 body = Some regs2' ->
    regs1' =(Verilog.module_body_writes body)= regs2'.
  Proof.
    intros * Hmatch Hexec1 Hexec2.
    pose proof (exec_module_body_change_regs body regs1 regs2 ltac:(assumption)) as H.
    rewrite Hexec1 in H.
    rewrite Hexec2 in H.
    inv H.
    assumption.
  Qed.

  Lemma exec_module_body_change_regs_none body regs1 regs2 :
    regs1 =(Verilog.module_body_reads body)= regs2 ->
    exec_module_body regs1 body = None ->
    exec_module_body regs2 body = None.
  Proof.
    intros * Hmatch Hexec1.
    pose proof (exec_module_body_change_regs body regs1 regs2 ltac:(assumption)) as H.
    rewrite Hexec1 in H.
    inv H.
    reflexivity.
  Qed.

  Lemma exec_module_body_change_preserve_reads body regs1 regs2 :
    regs1 =( Verilog.module_body_reads body )= regs2 ->
    exec_module_body regs1 body =?( Verilog.module_body_reads body )?= exec_module_body regs2 body.
  Proof. auto using exec_module_body_change_preserve. Qed.

  Lemma exec_module_body_preserve mi regs regs' l :
    disjoint l (Verilog.module_body_writes mi) ->
    exec_module_body regs mi = Some regs' ->
    regs =( l )= regs'.
  Proof.
    intros Hdisjoint Hexec.
    funelim (exec_module_body regs mi);
      rewrite <- Heqcall in *; clear Heqcall;
      simp module_body_writes expr_reads in *;
      try discriminate; try (some_inv; reflexivity); expect 1.
    monad_inv.
    etransitivity.
    - eapply exec_module_item_preserve; [disjoint_saturate; symmetry; eassumption|].
      eassumption.
    - apply H; [disjoint_saturate; symmetry; assumption|].
      eassumption.
  Qed.

  (************* /module bodies ***********)

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

  Lemma eval_expr_none_inv w rs (e : Verilog.expression w) :
    eval_expr rs e = None ->
    Exists (fun var => rs var = None) (Verilog.expr_reads e).
  Proof.
    rewrite Exists_exists.
    intros. induction e;
      simp eval_expr expr_reads in *;
      repeat setoid_rewrite in_app_iff;
      monad_inv;
      try match goal with
      | [ H : None = None -> _ |- _ ] => edestruct H
      end;
      crush.
  Qed.

  Lemma exec_module_item_none_inv rs1 rs2 x mi :
    exec_module_item rs1 mi = Some x ->
    exec_module_item rs2 mi = None ->
    Exists (fun var => rs2 var = None) (Verilog.module_item_reads mi).
  Proof.
    intros.
    destruct mi as [[? [] rhs]];
      simp exec_module_item exec_statement module_item_reads statement_reads in *;
      try discriminate; [idtac].
    eapply eval_expr_none_inv.
    now monad_inv.
  Qed.

  Lemma eval_expr_change_regs_none w (expr : Verilog.expression w) : forall rs1 rs2,
    eval_expr rs1 expr = None ->
    rs1 =( Verilog.expr_reads expr )= rs2 ->
    eval_expr rs2 expr = None.
  Proof.
    induction expr; intros;
      simp eval_expr expr_reads in *;
      monad_inv; RegisterState.unpack_match_on.
    all:
      match goal with
      | [ Hfail : eval_expr _ ?e = None, IH : context[eval_expr _ ?e = None -> _] |- _] =>
        insterU IH; rewrite IH; crush
      | _ => idtac
      end.
    (* Variable reference is the only interesting case *)
    unfold "_ =( _ )= _" in H0.
    erewrite <- H0; crush.
  Qed.

  Lemma exec_module_body_permute : forall body1 body2 rs0,
    Permutation body1 body2 ->
    NoDup (Verilog.module_body_writes body1) ->
    NoDup (Verilog.module_body_writes body2) ->
    disjoint (Verilog.module_body_writes body1) (Verilog.module_body_reads body1) ->
    disjoint (Verilog.module_body_writes body2) (Verilog.module_body_reads body2) ->
    exec_module_body rs0 body1 = exec_module_body rs0 body2.
  Proof.
   intros * Hpermute. revert rs0.
   induction Hpermute; intros * Hnodup1 Hnodup2 Hdisjoint1 Hdisjoint2.
   - simp exec_module_body. reflexivity.
   - simp exec_module_body module_body_writes module_body_reads in *.
     repeat f_equal.
     apply functional_extensionality. intros regs'.
     disjoint_saturate.
     eapply IHHpermute.
     + eassumption.
     + eassumption.
     + eapply disjoint_sym. eassumption.
     + eapply disjoint_sym. eassumption.
   - simp module_body_writes module_body_reads in *.
     simp exec_module_body.
     destruct (exec_module_item rs0 x) as [rs0x|] eqn:Ex,
              (exec_module_item rs0 y) as [rs0y|] eqn:Ey;
       simpl; simp exec_module_body; simpl.
     + destruct (exec_module_item rs0x y) as [rs0xy|] eqn:Exy,
                (exec_module_item rs0y x) as [rs0yx|] eqn:Eyx; simpl.
       * destruct x as [[? [] x_rhs]];
           simp exec_module_item exec_statement in *; try discriminate.
         destruct y as [[? [] y_rhs]];
           simp exec_module_item exec_statement in *; try discriminate.
         simp module_item_writes module_item_reads statement_writes statement_reads expr_reads in *.
         monad_inv.
         f_equal.
         replace x2 with x; cycle 1. {
           erewrite eval_expr_change_regs with (regs' := rs0) in E2; cycle 1. {
             eapply RegisterState.match_on_set_reg_elim.
             now disjoint_saturate.
           }
           congruence.
         }
         replace x1 with x0; cycle 1. {
           erewrite eval_expr_change_regs with (regs' := rs0) in E1; cycle 1. {
             eapply RegisterState.match_on_set_reg_elim.
             now disjoint_saturate.
           }
           congruence.
         }
         eapply set_reg_swap.
         now disjoint_saturate.
       * exfalso.
         unshelve (epose proof (exec_module_item_change_regs x rs0 rs0y _) as H).
	 -- eapply exec_module_item_preserve; [|eassumption].
	    disjoint_saturate. eassumption.
	 -- rewrite Ex in H. rewrite Eyx in H. inv H.
       * exfalso.
         unshelve (epose proof (exec_module_item_change_regs y rs0 rs0x _) as H).
	 -- eapply exec_module_item_preserve; [|eassumption].
	    disjoint_saturate. eassumption.
	 -- rewrite Ey in H. rewrite Exy in H. inv H.
       * reflexivity.
     + destruct (exec_module_item rs0x y) as [rs0xy|] eqn:Exy; [|reflexivity].
       exfalso.
       unshelve (epose proof (exec_module_item_change_regs y rs0 rs0x _) as H).
       -- eapply exec_module_item_preserve; [|eassumption].
          disjoint_saturate. eassumption.
       -- rewrite Ey in H. rewrite Exy in H. inv H.
     + destruct (exec_module_item rs0y x) as [rs0yx|] eqn:Eyx; [|reflexivity].
       exfalso.
       unshelve (epose proof (exec_module_item_change_regs x rs0 rs0y _) as H).
       -- eapply exec_module_item_preserve; [|eassumption].
          disjoint_saturate. eassumption.
       -- rewrite Ex in H. rewrite Eyx in H. inv H.
     + reflexivity.
   - transitivity (exec_module_body rs0 l').
     + eapply IHHpermute1.
       * assumption.
       * rewrite <- Hpermute1. assumption.
       * assumption.
       * setoid_rewrite <- Hpermute1.
         assumption.
     + eapply IHHpermute2.
       * erewrite <- Hpermute1. assumption.
       * assumption.
       * rewrite <- Hpermute1. assumption.
       * assumption.
  Qed.
End Facts.

Module Clean.
  Import Verilog.
  Import CombinationalOnly.

  Inductive clean_module_item_structure : Verilog.module_item -> Prop :=
    | CleanModuleItem_Assign var rhs :
      ~ In var (expr_reads rhs) ->
      clean_module_item_structure (AlwaysComb (BlockingAssign (NamedExpression var) rhs)).

  Global Instance dec_clean_module_item_structure mi : DecProp (clean_module_item_structure mi).
  Proof.
    destruct mi. destruct s.
    destruct lhs; try solve [right; inversion 1]; [idtac].
    destruct (dec (In var (expr_reads rhs))).
    - right.
      inversion 1. apply_somewhere inj_pair2. subst.
      contradiction.
    - left. constructor; assumption.
  Qed.

  Definition clean_module v := forall e,
    RegisterState.defined_value_for (fun var => In var (Verilog.module_inputs v)) e ->
          (* Runs to completion *)
    exists e', run_vmodule v (e // Verilog.module_inputs v) = Some e'
          (* Does not overwrite its inputs *)
        /\ e =( Verilog.module_inputs v )= e'
          (* Produces defined outputs*)
        /\ RegisterState.defined_value_for (fun var => In var (Verilog.module_outputs v)) e'.

  Lemma clean_module_statically v :
    Forall clean_module_item_structure (Verilog.modBody v) ->
    disjoint (Verilog.module_inputs v) (Verilog.module_outputs v) ->
    NoDup (Verilog.module_body_writes (Verilog.modBody v)) ->
    list_subset (Verilog.module_body_reads (Verilog.modBody v)) (Verilog.module_inputs v) ->
    Permutation (Verilog.module_body_writes (Verilog.modBody v)) (Verilog.module_outputs v) ->
    (exists sorted, sort_module_items (Verilog.module_inputs v) (Verilog.modBody v) = Some sorted) ->
    clean_module v.
  Proof. Admitted.
End Clean.

Module Equivalence.
  Import CombinationalOnly.
  Export Clean.

  Declare Scope verilog.
  Local Open Scope verilog.

  Record equivalent_behaviour (v1 v2 : Verilog.vmodule) : Prop :=
    MkEquivalentBehaviour {
      inputs_same : Verilog.module_inputs v1 = Verilog.module_inputs v2;
      outputs_same : Verilog.module_outputs v1 = Verilog.module_outputs v2;
      clean_left : clean_module v1;
      clean_right : clean_module v2;
      execution_match : forall e,
        RegisterState.defined_value_for
        (fun var => In var (Verilog.module_inputs v1 ++ Verilog.module_outputs v1)) e ->
        (v1 ⇓ e <-> v2 ⇓ e)
    }.

  Infix "~~" := equivalent_behaviour (at level 20) : verilog.

  Lemma equivalent_behaviour_sym v1 v2:
    v1 ~~ v2 ->
    v2 ~~ v1.
  Proof.
    intros [? ? ? ? execution_match].
    constructor.
    - symmetry. assumption.
    - symmetry. assumption.
    - assumption.
    - assumption.
    - intros. symmetry.
      apply execution_match.
      replace (Verilog.module_inputs v1).
      replace (Verilog.module_outputs v1).
      assumption.
  Qed.

  Lemma equivalent_behaviour_trans v1 v2 v3:
    v1 ~~ v2 -> v2 ~~ v3 -> v1 ~~ v3.
  Proof.
    intros [] [].
    constructor.
    - congruence.
    - congruence.
    - assumption.
    - assumption.
    - intros.
      etransitivity.
      + apply execution_match0.
        assumption.
      + apply execution_match1.
        rewrite <- inputs_same0, <- outputs_same0.
        assumption.
  Qed.

  Lemma equivalent_behaviour_refl_cond v v':
    v ~~ v' -> v ~~ v.
  Proof.
    intros [].
    constructor.
    - reflexivity.
    - reflexivity.
    - assumption.
    - assumption.
    - reflexivity.
  Qed.

  Add Parametric Relation :
    Verilog.vmodule equivalent_behaviour
    (* No reflexivity! *)
    symmetry proved by equivalent_behaviour_sym
    transitivity proved by equivalent_behaviour_trans
    as equivalent_behaviour_rel.

End Equivalence.

Module ExactEquivalence.
  Import CombinationalOnly.
  Export Clean.

  Declare Scope verilog.
  Local Open Scope verilog.

  Record exact_equivalence (v1 v2 : Verilog.vmodule) : Prop :=
    MkEquivalentBehaviour {
      inputs_same : Verilog.module_inputs v1 = Verilog.module_inputs v2;
      outputs_same : Verilog.module_outputs v1 = Verilog.module_outputs v2;
      execution_match : forall e, (v1 ⇓ e <-> v2 ⇓ e)
    }.

  Infix "~~~" := exact_equivalence (at level 20) : verilog.

  Lemma exact_equivalence_sym v1 v2:
    v1 ~~~ v2 ->
    v2 ~~~ v1.
  Proof.
    intros [? ? execution_match].
    constructor.
    - symmetry. assumption.
    - symmetry. assumption.
    - symmetry. auto.
  Qed.

  Lemma exact_equivalence_trans v1 v2 v3:
    v1 ~~~ v2 -> v2 ~~~ v3 -> v1 ~~~ v3.
  Proof.
    intros [] [].
    constructor.
    - congruence.
    - congruence.
    - etransitivity; eauto.
  Qed.

  Lemma exact_equivalence_refl v : v ~~~ v.
  Proof. constructor; reflexivity. Qed.

  Add Parametric Relation :
    Verilog.vmodule exact_equivalence
    reflexivity proved by exact_equivalence_refl
    symmetry proved by exact_equivalence_sym
    transitivity proved by exact_equivalence_trans
    as exact_equivalence_rel.

  Global Instance Proper_valid_execution_exact_equivalence :
    Proper (exact_equivalence ==> eq ==> iff) valid_execution.
  Proof.
    repeat intro. subst.
    destruct H. auto.
  Qed.

  Import Equivalence.

  Lemma exact_equivalence_equivalent_behaviour v1 v2 :
    clean_module v1 ->
    clean_module v2 ->
    v1 ~~~ v2 ->
    v1 ~~ v2.
  Proof.
    intros Hclean1 Hclean2 [].
    constructor.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - auto.
  Qed.
End ExactEquivalence.
