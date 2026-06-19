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

From ExtLib Require Import Programming.Show.
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

Module RegisterState.
  Module VariableAsMDT <: MiniDecidableType.
    Definition t := Verilog.variable.
    Definition eq_dec (x y : t) := dec (x = y).
  End VariableAsMDT.

  Module VariableAsUDT := Make_UDT(VariableAsMDT).

  Definition register_state := forall var, XBV.xbv (Verilog.varType var).

  #[global]
  Notation t := register_state.

  #[global]
  Notation execution := t.

  Definition empty : RegisterState.t := fun var => XBV.exes (Verilog.varType var).

  Lemma empty_get var : empty var = XBV.exes (Verilog.varType var).
  Proof. cbv. reflexivity. Qed.

  Definition set_reg (var : Verilog.variable) (value : XBV.xbv (Verilog.varType var)) (r : register_state) : register_state :=
    fun var' => match dec (var = var') with
           | left e => match e with
                      | eq_refl => value
                      end
           | right _ => r var'
           end.

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
                          
  Definition defined_value_for (C : Verilog.variable -> Prop) (regs : RegisterState.t) :=
    forall var, C var -> exists bv, regs var = XBV.from_bv bv.
  
  Lemma defined_value_for_split_iff (C1 C2 : Verilog.variable -> Prop) regs :
    (defined_value_for C1 regs /\ defined_value_for C2 regs) <->
      (defined_value_for (fun var => C1 var \/ C2 var) regs).
  Proof. unfold defined_value_for. crush. Qed.

  Lemma defined_value_for_impl C1 C2 e :
    (forall v, C2 v -> C1 v) ->
    defined_value_for C1 e ->
    defined_value_for C2 e.
  Proof. unfold defined_value_for. crush. Qed.

  Lemma defined_value_for_empty e :
    defined_value_for (fun var => In var []) e.
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
      | [ |- defined_value_for (fun var => In var [] ) _ ] =>
          apply defined_value_for_empty
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

  Global Instance Proper_match_on_impl_contra :
    Proper
      ((pointwise_relation Verilog.variable Basics.impl) --> eq ==> eq ==> Basics.impl)
      match_on.
  Proof. repeat intro. subst. crush. Qed.

  Global Instance Proper_match_on_impl_contra_nested :
    Proper
      ((pointwise_relation Verilog.variable (Basics.flip Basics.impl)) ==> eq ==> eq ==> Basics.impl)
      match_on.
  Proof. repeat intro. subst. crush. Qed.

  Global Instance Proper_match_on_impl_flip :
    Proper
      ((pointwise_relation Verilog.variable Basics.impl) ==> eq ==> eq ==> Basics.flip Basics.impl)
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

  Definition defined_match_on C e1 e2 :=
    e1 ={ C }= e2 /\ RegisterState.defined_value_for C e1.

  Notation "rs1 =!!{ P }!!= rs2" :=
    (defined_match_on P rs1 rs2)
    (at level 80) : type_scope.

  Notation "rs1 =!!( vars )!!= rs2" :=
    (rs1 =!!{fun var => In var vars}!!= rs2)
    (at level 80) : type_scope.

  Lemma defined_match_on_iff C e1 e2 :
    e1 =!!{ C }!!= e2 <->
    forall var, C var -> exists bv, e1 var = XBV.from_bv bv /\ e2 var = XBV.from_bv bv.
  Proof.
    unfold defined_match_on, "_ ={ _ }= _", RegisterState.defined_value_for.
    split.
    - intros [Hmatch Hdefined] var HC. insterU Hmatch. insterU Hdefined.
      rewrite <- Hmatch. crush.
    - intro H. split.
      + intros var HC. insterU H. destruct H as [? [? ?]]. crush.
      + intros var HC. insterU H. destruct H as [? [? ?]]. crush.
  Qed.

  Lemma defined_match_on_trans C e1 e2 e3:
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

  Lemma defined_match_on_sym C e1 e2:
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
    RegisterState.t (defined_match_on C)
    symmetry proved by (defined_match_on_sym C)
    transitivity proved by (defined_match_on_trans C)
    as execution_defined_match_on_rel.

  Definition limit_to_regs (vars : list Verilog.variable) (regs : RegisterState.t) : RegisterState.t :=
    fun var =>
      match dec (In var vars) with
      | left prf => regs var
      | right prf => XBV.exes (Verilog.varType var)
      end.

  Notation "st // regs" := (limit_to_regs regs st) (at level 20) : verilog.

  Global Instance Proper_limit_to_regs regs :
    Proper
      (RegisterState.match_on (fun var => In var regs) ==> eq)
      (RegisterState.limit_to_regs regs).
  Proof.
    repeat intro.
    unfold "//", "_ =( _ )= _" in *.
    apply functional_extensionality_dep. intro var.
    autodestruct; eauto.
  Qed.

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
    unfold "//", empty.
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
    (st // vars) var = XBV.exes (Verilog.varType var).
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
  Proof.
    unfold "//", "_ =( _ )= _".
    split.
    - intros Heq var Hvar_in.
      match type of Heq with
      | ?f1' = ?f2' =>
        remember f1' as f1;
        remember f2' as f2;
	assert (f1 var = f2 var) by now rewrite Heq
      end.
      subst.
      autodestruct; crush.
    - intros Heq.
      apply functional_extensionality_dep.
      intros var. specialize (Heq var).
      autodestruct; crush.
  Qed.

  Lemma limit_to_regs_match_on r l :
    r // l =( l )= r.
  Proof.
    apply match_on_limit_to_regs_iff.
    apply limit_to_regs_twice.
  Qed.

  Lemma defined_value_for_limit_to_regs vars st :
    RegisterState.defined_value_for (fun var => In var vars) st ->
    RegisterState.defined_value_for (fun var => In var vars) (st // vars).
  Proof.
    unfold RegisterState.defined_value_for, "//".
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

  Lemma match_on_set_reg_elim_trans C var x regs1 regs2 :
    ~ C var ->
    regs1 ={ C }= regs2 ->
    set_reg var x regs1 ={ C }= regs2.
  Proof.
    unfold "_ ={ _ }= _". intros HnC Hmatch var' HC.
    erewrite set_reg_get_out by crush.
    crush.
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

  Section mi_show.
    Local Open Scope string.
    Import ShowNotation.
    Global Instance moduleitem_Show : Show module_item :=
      { show u :=
          match u with
    	| Verilog.AlwaysComb (Verilog.BlockingAssign var _) =>
    	  ("always_comb " ++ Verilog.varName var ++ " = ...")%string
          end
      }.
  End mi_show.
  
  Equations sort_module_items_select (vars_ready : list variable) (mis : list module_item) : option (selection mis) := {
    | vars_ready, [] => @None _
    | vars_ready, hd :: tl with
      dec (disjoint (module_item_writes hd) vars_ready),
      dec (list_subset (module_item_reads hd) vars_ready) => {
      (* conflicting write *)
      | right _, _ => None 
      (* No conflicting write, but not ready *)
      | left _, right _ with sort_module_items_select vars_ready tl => {
        | Some (MkSelection _ selected selected_tl _) =>
	    Some (MkSelection (hd :: tl) selected (hd :: selected_tl) _ )
        | None => None
      }
      (* Ready *)
      | left prf1, left prf2 => 
        Some (MkSelection (hd :: tl) hd tl _)
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
    - inv Hsorted. contradiction.
  Qed.

  Lemma module_items_select_ready vars mis mi rest wf :
    sort_module_items_select vars mis = Some (MkSelection mis mi rest wf) ->
    list_subset (module_item_reads mi) vars.
  Proof.
    intros H.
    funelim (sort_module_items_select vars mis);
      rewrite <- Heqcall in *; clear Heqcall.
    all: inv H.
    all: eauto.
  Qed.

  Lemma module_items_select_no_overwrite vars mis mi rest wf :
    sort_module_items_select vars mis = Some (MkSelection mis mi rest wf) ->
    disjoint (module_item_writes mi) vars.
  Proof.
    intros H.
    funelim (sort_module_items_select vars mis);
      rewrite <- Heqcall in *; clear Heqcall.
    all: inv H.
    all: eauto.
  Qed.

  Theorem sort_module_items_permutation body body' vars_ready :
    sort_module_items vars_ready body = Some body' ->
    Permutation body body'.
  Proof.
    intros.
    funelim (sort_module_items vars_ready body);
      rewrite <- Heqcall in *; clear Heqcall.
    all: inv H.
    - reflexivity.
    - rewrite <- wf0.
      apply perm_skip.
      eapply Hind.
      eapply Heq.
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

  Definition selection_map {l} f (s : selection l) : selection (map f l) :=
    let '(MkSelection _ mi rest wf) := s in
    {| mi := f mi; rest := map f rest; wf := Permutation_map f wf |}.

  (* This should be a Proper instance, but the result type depends on
     the second argument, so we can't do it. *)
  Lemma module_items_select_permutation vars1 vars2 l :
    Permutation vars1 vars2 ->
    sort_module_items_select vars1 l = sort_module_items_select vars2 l.
  Proof.
    intros Hpermute.
    induction l.
    all: simp sort_module_items_select.
    1: reflexivity.
    repeat match goal with
           | [ |- context[dec ?P] ] => destruct (dec P)
	   end.
    all: try reflexivity.
    all: simpl.
    all: match goal with
         | [ H1: ?P ?l ?v1, H2: ~ ?P ?l ?v2 |- _] =>
	   exfalso;
	   (rewrite Hpermute in H2 || rewrite <- Hpermute in H2);
	   contradiction
	 | _ => idtac
	 end.
    all: expect 1.
    rewrite <- IHl.
    destruct (sort_module_items_select vars1 l).
    all: reflexivity.
  Qed.

  Lemma module_items_sort_permutation vars1 vars2 l :
    Permutation vars1 vars2 ->
    sort_module_items vars1 l = sort_module_items vars2 l.
  Proof.
    intros Hpermute.
    funelim (sort_module_items vars1 l).
    - reflexivity.
    - simp sort_module_items.
      rewrite <- (module_items_select_permutation _ _ _ Hpermute).
      rewrite Heq.
      reflexivity.
    - simp sort_module_items.
      rewrite <- (module_items_select_permutation _ _ _ Hpermute).
      rewrite Heq0.
      simpl.
      rewrite <- Hind; cycle 1. {
        apply Permutation_app_head.
	apply Hpermute.
      }
      rewrite Heq.
      reflexivity.
    - simp sort_module_items.
      rewrite <- (module_items_select_permutation _ _ _ Hpermute).
      rewrite Heq0.
      simpl.
      rewrite <- Hind; cycle 1. {
        apply Permutation_app_head.
	apply Hpermute.
      }
      rewrite Heq.
      reflexivity.
  Qed.

  Global Instance Proper_module_items_sort_Permutation :
    Proper
      (@Permutation Verilog.variable ==> eq ==> eq)
      sort_module_items.
  Proof.
    intros vars1 vars2 Hpermute l l' <-.
    apply module_items_sort_permutation.
    apply Hpermute.
  Qed.

  Section map.
    Context
      (f : module_item -> module_item)
      (f_preserve_reads : forall mi, Permutation (module_item_reads (f mi)) (module_item_reads mi))
      (f_preserve_writes : forall mi, Permutation (module_item_writes (f mi)) (module_item_writes mi)).

    Lemma sort_module_items_select_map inputs mis :
      sort_module_items_select inputs (map f mis)
        = option_map (selection_map f) (sort_module_items_select inputs mis).
    Proof.
      funelim (sort_module_items_select inputs mis).
      - reflexivity.
      - simpl. simp sort_module_items_select.
        destruct (dec (disjoint (module_item_writes (f hd)) vars_ready)) as [prf1'|prf1'];
          [|exfalso; rewrite f_preserve_writes in prf1'; contradiction].
        destruct (dec (list_subset (module_item_reads (f hd)) vars_ready)) as [prf2'|prf2'];
          [|exfalso; rewrite f_preserve_reads in prf2'; contradiction].
        simpl. f_equal. f_equal. apply proof_irrelevance.
      - simpl. simp sort_module_items_select.
        destruct (dec (disjoint (module_item_writes (f hd)) vars_ready)) as [prf1'|prf1'];
          [exfalso; rewrite f_preserve_writes in prf1'; contradiction|].
        reflexivity.
      - simpl. simp sort_module_items_select.
        destruct (dec (disjoint (module_item_writes (f hd)) vars_ready)) as [prf1'|prf1'];
          [|exfalso; rewrite f_preserve_writes in prf1'; contradiction].
        destruct (dec (list_subset (module_item_reads (f hd)) vars_ready)) as [prf2'|prf2'];
          [exfalso; rewrite f_preserve_reads in prf2'; contradiction|].
        simpl.
        rewrite Hind.
        rewrite Heq.
        simpl.
        f_equal. f_equal. apply proof_irrelevance.
      - simpl. simp sort_module_items_select.
        destruct (dec (disjoint (module_item_writes (f hd)) vars_ready)) as [prf1'|prf1'];
          [|exfalso; rewrite f_preserve_writes in prf1'; contradiction].
        destruct (dec (list_subset (module_item_reads (f hd)) vars_ready)) as [prf2'|prf2'];
          [exfalso; rewrite f_preserve_reads in prf2'; contradiction|].
        simpl.
        rewrite Hind.
        rewrite Heq.
        simpl.
        reflexivity.
    Qed.

    Lemma sort_module_items_map inputs mis :
      sort_module_items inputs (map f mis)
        = option_map (map f) (sort_module_items inputs mis).
    Proof.
      funelim (sort_module_items inputs mis); simp sort_module_items.
      1: reflexivity.
      all: simpl; simp sort_module_items.
      all: replace
             (sort_module_items_select vars_ready (f m :: map f l))
  	   with
             (option_map (selection_map f) (sort_module_items_select vars_ready (m :: l)))
           by (symmetry; exact (sort_module_items_select_map vars_ready (m :: l))).
      - rewrite Heq.
        reflexivity.
      - rewrite Heq0. simpl.
        rewrite <- f_preserve_writes in Hind. rewrite Hind.
        rewrite <- f_preserve_writes in Heq. rewrite Heq.
        reflexivity.
      - rewrite Heq0. simpl.
        rewrite <- f_preserve_writes in Hind. rewrite Hind.
        rewrite <- f_preserve_writes in Heq. rewrite Heq.
        reflexivity.
    Qed.
  End map.

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

  Equations xor_bit : bit -> bit -> bit :=
    xor_bit O O := O;
    xor_bit I I := O;
    xor_bit I O := I;
    xor_bit O I := I;
    xor_bit X _ := X;
    xor_bit _ X := X.

  Equations eval_arithmeticop {n} (op : Verilog.arithmeticop) : XBV.xbv n -> XBV.xbv n -> XBV.xbv n :=
    eval_arithmeticop Verilog.ArithmeticPlus l r := bv_binop (@BV.bv_add _) l r;
    eval_arithmeticop Verilog.ArithmeticMinus l r := bv_binop (fun bvl bvr => BV.bv_add bvl (BV.bv_neg bvr)) l r;
    eval_arithmeticop Verilog.ArithmeticStar l r := bv_binop (@BV.bv_mult _) l r;
  .

  Equations eval_bitwiseop {n} (op : Verilog.bitwiseop) : XBV.xbv n -> XBV.xbv n -> XBV.xbv n :=
    eval_bitwiseop Verilog.BinaryBitwiseAnd l r := bitwise_binop and_bit l r;
    eval_bitwiseop Verilog.BinaryBitwiseOr l r := bitwise_binop or_bit l r;
    eval_bitwiseop Verilog.BinaryBitwiseXor l r := bitwise_binop xor_bit l r;
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
    eval_unaryop Verilog.UnaryPlus x := x;
    eval_unaryop Verilog.UnaryNot x := XBV.not x
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

  Definition select_bit {w1} (vec : XBV.xbv w1) (idx : N) : XBV.xbv 1 :=
    XBV.of_bits [XBV.bitOf (N.to_nat idx) vec].

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
    eval_expr regs (Verilog.RangeSelect vec hi lo _ _) :=
      let vec_val := eval_expr regs vec in
      (XBV.extr vec_val lo (1 + hi - lo));
    eval_expr regs (Verilog.BitSelect_width vec idx _ _) :=
      let vec_val := eval_expr regs vec in
      let idx_val := eval_expr regs idx in
      match XBV.to_N idx_val with
      | Some idx => select_bit vec_val idx
      | None => XBV.exes 1
      end;
    eval_expr regs (Verilog.BitSelect_const vec idx _) :=
      let vec_val := eval_expr regs vec in
      (select_bit vec_val idx);
    eval_expr regs (Verilog.Resize t expr _) :=
      let val := eval_expr regs expr in
      (convert t val);
    eval_expr regs (Verilog.Concatenation e1 e2) :=
      let val1 := eval_expr regs e1 in
      let val2 := eval_expr regs e2 in
      (XBV.concat val1 val2);
    eval_expr regs (Verilog.Replication count expr) :=
      let expr_val := eval_expr regs expr in
      (XBV.replicate count expr_val);
    eval_expr regs (Verilog.IntegerLiteral _ val) :=
      (XBV.from_bv val) ;
    eval_expr regs (Verilog.NamedExpression var) := regs var.

  Equations
    exec_statement (regs : RegisterState.t) (stmt : Verilog.statement) : RegisterState.t by struct :=
    exec_statement regs (Verilog.BlockingAssign var rhs) :=
      let rhs_val := eval_expr regs rhs in
      RegisterState.set_reg var rhs_val regs ;
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

  Definition mk_initial_state (v : Verilog.vmodule) (regs : RegisterState.t) : RegisterState.t :=
    regs // Verilog.module_inputs v.

  Lemma initial_state_same v1 v2 regs :
    Verilog.modVariableDecls v1 = Verilog.modVariableDecls v2 ->
    mk_initial_state v1 regs = mk_initial_state v2 regs.
  Proof.
    unfold mk_initial_state.
    intros.
    erewrite Verilog.module_inputs_same by eassumption.
    reflexivity.
  Qed.

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

  Definition run_vmodule (v : Verilog.vmodule) (inputs : RegisterState.t) : RegisterState.t :=
    match sort_module_items (Verilog.module_inputs v) (Verilog.modBody v) with
    | None => RegisterState.empty
    | Some sorted => exec_module_body (mk_initial_state v inputs) sorted
    end.

  Global Instance Proper_run_vmodule_match_on v :
    Proper
      (RegisterState.match_on (fun var => In var (Verilog.module_inputs v)) ==> eq)
      (run_vmodule v).
  Proof.
    intros r1 r2 Heq.
    unfold run_vmodule.
    unfold mk_initial_state.
    autodestruct.
    - rewrite Heq. reflexivity.
    - reflexivity.
  Qed.

  Notation execution := RegisterState.t.

  Definition valid_execution (v : Verilog.vmodule) (e : execution) :=
    run_vmodule v e =( Verilog.modVariables v )= e.

  Infix "⇓" := valid_execution (at level 20) : verilog.

  Definition execution_not_x (e : execution) name :=
    ~ XBV.has_x (e name).

  Definition execution_no_exes_for C (e : execution) :=
    forall var, C var -> execution_not_x e var.

  Global Instance Proper_execution_no_exes_for :
    Proper (pointwise_relation Verilog.variable iff ==> eq ==> iff) execution_no_exes_for.
  Proof. repeat intro. subst. crush. Qed.
End CombinationalOnly.

Section ExpressionFacts.
  Import CombinationalOnly.

  Lemma bitwise_binop_no_exes (f_bit : bit -> bit -> bit) (f_bool : bool -> bool -> bool) :
    (forall (lb rb : bool), RawXBV.bool_to_bit (f_bool lb rb) = f_bit (RawXBV.bool_to_bit lb) (RawXBV.bool_to_bit rb)) ->
    forall n (l_bv r_bv : BV.bitvector n),
      bitwise_binop f_bit (XBV.from_bv l_bv) (XBV.from_bv r_bv) = XBV.from_bv (BV.map2 f_bool l_bv r_bv).
  Proof.
    intros * Hf *.
    apply XBV.of_bits_equal; simpl.
    destruct l_bv as [l_bv l_bv_wf].
    destruct r_bv as [r_bv r_bv_wf].
    simpl in *.
    unfold bitwise_binop_raw.
    generalize dependent n.
    generalize dependent r_bv.
    induction l_bv; simpl; simp map2; try easy.
    destruct r_bv; simpl; simp map2; try easy.
    specialize (IHl_bv r_bv).
    intros.
    simpl in *. f_equal.
    - auto.
    - unfold BVList.RAWBITVECTOR_LIST.size in *.
      eapply IHl_bv; crush.
  Qed.
  
  Lemma bitwise_and_no_exes w (l_bv r_bv : BV.bitvector w) :
      bitwise_binop and_bit (XBV.from_bv l_bv) (XBV.from_bv r_bv) =
        XBV.from_bv (BV.bv_and l_bv r_bv).
  Proof.
    rewrite bitwise_binop_no_exes with (f_bool := andb).
    - XBV.bitvector_erase. 
      f_equal.
      unfold RawBV.bv_and.
      rewrite wf0, wf1, N.eqb_refl.
      reflexivity.
    - intros [] []; reflexivity.
  Qed.
  
  Lemma bitwise_or_no_exes w (l_bv r_bv : BV.bitvector w) :
      bitwise_binop or_bit (XBV.from_bv l_bv) (XBV.from_bv r_bv) =
        XBV.from_bv (BV.bv_or l_bv r_bv).
  Proof.
    rewrite bitwise_binop_no_exes with (f_bool := orb).
    - XBV.bitvector_erase. 
      f_equal.
      unfold RawBV.bv_or.
      rewrite wf0, wf1, N.eqb_refl.
      reflexivity.
    - intros [] []; reflexivity.
  Qed.

  Lemma bitwise_xor_no_exes w (l_bv r_bv : BV.bitvector w) :
      bitwise_binop xor_bit (XBV.from_bv l_bv) (XBV.from_bv r_bv) =
        XBV.from_bv (BV.bv_xor l_bv r_bv).
  Proof.
    rewrite bitwise_binop_no_exes with (f_bool := xorb).
    - XBV.bitvector_erase. 
      f_equal.
      unfold RawBV.bv_xor.
      rewrite wf0, wf1, N.eqb_refl.
      reflexivity.
    - intros [] []; reflexivity.
  Qed.
  
  (* These lemmas are defined here so this has to stay, but maybe the
     lemmas should also be in Bitvector.v *)
  Hint Rewrite
    bitwise_and_no_exes
    bitwise_or_no_exes
    bitwise_xor_no_exes
    : xbv.

  Definition select_bit_bv {w1} (vec : BV.bitvector w1) (idx : N) : BV.bitvector 1 :=
    BV.of_bits [BV.bitOf (N.to_nat idx) vec].
  
  Lemma select_bit_to_bv w_vec (vec : BV.bitvector w_vec) idx :
    (idx < w_vec)%N ->
    XBV.to_bv (select_bit (XBV.from_bv vec) idx) =
      Some (select_bit_bv vec idx).
  Proof.
    intros H.
    unfold select_bit, select_bit_bv.
    rewrite XBV.bit_of_as_bv by lia.
    generalize (BV.bitOf (n:=w_vec) (N.to_nat idx) vec). intro b.
    apply XBV.to_bv_some_raw_iff.
    simpl.
    unfold RawXBV.to_bv. simpl.
    rewrite RawXBV.bit_to_bool_inverse.
    reflexivity.
  Qed.
  
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
  
  Lemma eval_unop_to_bv op w (e : BV.bitvector w) :
    exists bv, XBV.to_bv (eval_unaryop op (XBV.from_bv e)) = Some bv.
  Proof.
    destruct op.
    all: autorewrite with eval_unaryop xbv.
    all: eauto.
  Qed.
  
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

  Lemma select_bit_no_exes (w_val : N) (vec : BV.bitvector w_val) (idx : N) :
      (idx < w_val)%N ->
      select_bit (XBV.from_bv vec) idx = XBV.from_bv (select_bit_bv vec idx).
  Proof.
    intros.
    eapply XBV.to_bv_injective.
    - apply select_bit_to_bv.
      assumption.
    - apply XBV.xbv_bv_inverse.
  Qed.

  Hint Rewrite select_bit_no_exes using lia : xbv.

  Import SigTNotations.
  Import EqNotations. 

  Equations convert_bv {from} (to : N) (value : BV.bitvector from) : BV.bitvector to :=
    convert_bv to value with dec (from < to)%N := {
      | left Hlt => rew _ in BV.bv_concat (BV.zeros (to - from)%N) value
      | right Hge with dec (from > to)%N => {
        | left Hgr => BV.bv_extr 0 to value;
        | right Hle => rew _ in value
        }
      }.
  Next Obligation. lia. Defined.
  Next Obligation. lia. Defined.
  
  Lemma convert_no_exes w_from w_to (from : BV.bitvector w_from) :
    convert w_to (XBV.from_bv from) = XBV.from_bv (convert_bv w_to from).
  Proof.
    funelim (convert w_to (XBV.from_bv from)); clear Heqcall.
    all: try destruct_rew.
    - autorewrite with xbv.
      funelim (convert_bv (to - from + from) from0); [|lia|lia];
        clear Heqcall.
      apply XBV.of_bits_equal.
      destruct_rew.
      repeat f_equal.
      crush.
    - autorewrite with xbv.
      funelim (convert_bv to from0); [lia| |lia].
      reflexivity.
    - funelim (convert_bv from from0); [lia|lia|].
      now rewrite <- eq_rect_eq.
  Qed.

  Hint Rewrite convert_no_exes : xbv.
  
  Lemma convert_from_bv w_from w_to (from : BV.bitvector w_from) :
    exists bv : BV.bitvector w_to, XBV.to_bv (convert w_to (XBV.from_bv from)) = Some bv.
  Proof.
    funelim (convert w_to (XBV.from_bv from)).
    all: try destruct_rew; simpl.
    all: autorewrite with xbv.
    all: eauto.
  Qed.
  
  Lemma eval_expr_defined w regs e :
      RegisterState.defined_value_for (fun v => List.In v (Verilog.expr_reads e)) regs ->
      exists bv, eval_expr (w:=w) regs e = XBV.from_bv bv.
  Proof.
    funelim (eval_expr regs e).
    all: intros * Hdefined.
    all: simp eval_expr expr_reads in *; simpl in *.
    all: monad_inv.
    all: RegisterState.unpack_defined_value_for.
    all: repeat match goal with
                | [ IH : context[RegisterState.defined_value_for _ _ -> exists _, _] |- _ ] =>
                    let IH' := fresh "IH" in
                    edestruct IH as [? IH']; eauto; clear IH; inv IH'
                end.
    all: repeat match goal with
                | [ e : eval_expr _ _ = XBV.from_bv _ |- _ ] =>
                    rewrite e in *; clear e
                end.
    - (* arithmeticop *) eapply eval_arithmeticop_no_exes.
    - (* bitwiseop *) eapply eval_bitwiseop_no_exes.
    - (* shiftop *) eapply eval_shiftop_no_exes.
    - (* unop *) eapply eval_unop_no_exes.
    - (* conditional *) eapply eval_conditional_no_exes.
    - (* range select *) (* Not sure why it appears 4 times *)
      autorewrite with xbv. eauto.
    - autorewrite with xbv. eauto.
    - autorewrite with xbv. eauto.
    - autorewrite with xbv. eauto.
    - (* bit select (in bounds by literal) *)
      autorewrite with xbv. eauto.
    - (* bit select (in bounds by width) *)
      autorewrite with xbv in E. inv E.
      pose proof (BV.to_N_max_bound _ x).
      autorewrite with xbv. eauto.
    - (* bit select (in bounds by width) *)
      autorewrite with xbv in E. inv E.
    - (* concat *)
      autorewrite with xbv. eauto.
    - (* replicate *)
      autorewrite with xbv. eauto.
    - (* literal *)
      eauto.
    - (* Variable *)
      rename_match (RegisterState.defined_value_for (eq var) regs) into Hvar_defined.
      edestruct Hvar_defined as [bv Hregs_var]; eauto.
    - autorewrite with xbv. eauto.
  Qed.
  
  Lemma eval_expr_no_exes w regs e :
    RegisterState.defined_value_for (fun v => List.In v (Verilog.expr_reads e)) regs ->
    exists bv, XBV.to_bv (eval_expr (w:=w) regs e) = Some bv.
  Proof.
    intros * Hdefined.
    pose proof eval_expr_defined as Hto_bv. insterU Hto_bv. destruct Hto_bv as [bv Hto_bv].
    rewrite Hto_bv.
    rewrite XBV.xbv_bv_inverse.
    eauto.
  Qed.
  
End ExpressionFacts.

(* We duplicate the hints from above because we can't use #[global]
   inside Module *)
#[global]
Hint Rewrite
  bitwise_and_no_exes
  bitwise_or_no_exes
  bitwise_xor_no_exes
  : xbv.
#[global]
Hint Rewrite
  select_bit_no_exes
  convert_no_exes
  using lia
  : xbv.

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
    intros.
    funelim (eval_expr regs e).
    all: simp eval_expr expr_reads in *; simpl in *.
    all: RegisterState.unpack_match_on.
    all: repeat match goal with [ IH : forall _, _ -> eval_expr _ _ = eval_expr _ _ |- _ ] =>
           erewrite IH by eassumption; clear IH
	 end.
    all: simpl; try reflexivity.
    all: expect 1.
    apply H.
    reflexivity.
  Qed.

  (***** Statements ***********)

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
    eapply RegisterState.match_on_set_reg_elim2.
  Qed.

  Lemma exec_statement_change_preserve l stmt regs1 regs2 :
    regs1 =( Verilog.statement_reads stmt )= regs2 ->
    regs1 =( l )= regs2 ->
    exec_statement regs1 stmt =( l )= exec_statement regs2 stmt.
  Proof.
    intros Hmatch_other Hmatch_reads.
    destruct stmt; expect 1.
    destruct lhs; simp exec_statement; try constructor; expect 1.
    simpl; simp exec_statement statement_writes statement_reads expr_reads in *.
    disjoint_saturate.
    erewrite eval_expr_change_regs by eassumption.
    destruct (eval_expr regs2 rhs); expect 1.
    apply RegisterState.match_on_set_reg_elim2_in.
    assumption.
  Qed.

  Lemma exec_statement_change_preserve_reads stmt regs1 regs2 :
    regs1 =( Verilog.statement_reads stmt )= regs2 ->
    exec_statement regs1 stmt =( Verilog.statement_reads stmt )= exec_statement regs2 stmt.
  Proof. auto using exec_statement_change_preserve. Qed.

  Lemma exec_statement_preserve stmt regs  l :
    disjoint l (Verilog.statement_writes stmt) ->
    regs =( l )= exec_statement regs stmt.
  Proof.
    intros Hdisjoint.
    funelim (exec_statement regs stmt).
    try rewrite <- Heqcall in *; clear Heqcall.
    simp statement_writes expr_reads in *.
    symmetry. apply RegisterState.match_on_set_reg_elim.
    now disjoint_saturate.
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
    simpl; simp exec_module_item module_item_writes module_item_reads expr_reads in *.
    apply exec_statement_change_preserve; assumption.
  Qed.

  Lemma exec_module_item_change_preserve_reads mi regs1 regs2 :
    regs1 =( Verilog.module_item_reads mi )= regs2 ->
    exec_module_item regs1 mi =( Verilog.module_item_reads mi )= exec_module_item regs2 mi.
  Proof. auto using exec_module_item_change_preserve. Qed.

  Lemma exec_module_item_preserve mi regs l :
    disjoint l (Verilog.module_item_writes mi) ->
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
    - simp exec_module_body module_body_reads in *. simpl in *.
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
    simp exec_module_body in *; simpl.
    simp module_body_reads module_body_writes in *.
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
    disjoint l (Verilog.module_body_writes body) ->
    regs =( l )= exec_module_body regs body.
  Proof.
    intros Hdisjoint.
    funelim (exec_module_body regs body); [reflexivity|].
    try rewrite <- Heqcall in *; clear Heqcall.
    simp module_body_writes expr_reads in *.
    try discriminate; try (some_inv; reflexivity); expect 1.
    monad_inv.
    etransitivity.
    - eapply exec_module_item_preserve.
      disjoint_saturate. symmetry. eassumption.
    - apply H.
      disjoint_saturate. symmetry. eassumption.
  Qed.

  (************* /module bodies ***********)

  (************* modules ***********)

  Lemma run_vmodule_preserve_inputs v e :
    vmodule_sortable v ->
    run_vmodule v e =( Verilog.module_inputs v )= e.
  Proof.
    unfold vmodule_sortable, run_vmodule.
    intros [sorted Hsort]. rewrite Hsort.
    symmetry.
    unfold mk_initial_state.
    rewrite <- exec_module_body_preserve.
    - symmetry.
      apply RegisterState.limit_to_regs_match_on.
    - symmetry.
      apply module_items_sorted_no_overwrite.
      eapply sort_module_items_sorted.
      eassumption.
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
     simpl.
     eapply IHHpermute.
     + disjoint_saturate. assumption.
     + disjoint_saturate. assumption.
     + disjoint_saturate. symmetry. assumption.
     + disjoint_saturate. symmetry. assumption.
   - simp module_body_writes module_body_reads in *.
     simp exec_module_body.
     simpl.
     destruct x as [[x_var x_expr]].
     destruct y as [[y_var y_expr]].
     simp module_item_writes module_item_reads statement_writes statement_reads expr_reads in *.
     simp exec_module_item exec_statement in *; simpl in *.
     f_equal.
     replace (eval_expr (RegisterState.set_reg _ _ rs0) x_expr) with (eval_expr rs0 x_expr); cycle 1. {
       eapply eval_expr_change_regs. symmetry.
       eapply RegisterState.match_on_set_reg_elim.
       now disjoint_saturate.
     }
     replace (eval_expr (RegisterState.set_reg _ _ rs0) y_expr) with (eval_expr rs0 y_expr); cycle 1. {
       eapply eval_expr_change_regs. symmetry.
       eapply RegisterState.match_on_set_reg_elim.
       now disjoint_saturate.
     }
     eapply set_reg_swap. now disjoint_saturate.
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

  Lemma exec_statement_defined l_before l_after r stmt:
    list_subset (Verilog.statement_reads stmt) l_before ->
    list_subset l_after (Verilog.statement_writes stmt ++ l_before) ->
    RegisterState.defined_value_for
      (fun var : variable => In var l_before)
      r ->
    RegisterState.defined_value_for
      (fun var : variable => In var l_after)
      (exec_statement r stmt).
  Proof.
    intros Hreads_in Hafter_in Hinputs_defined.
    destruct stmt; expect 1.
    simp statement_writes statement_reads exec_statement in *. simpl in *.
    unfold RegisterState.defined_value_for.
    intros var Hvar_in. 
    destruct (dec (var = lhs)).
    - subst. rewrite RegisterState.set_reg_get_in.
      destruct eval_expr_defined with (regs := r) (e := rhs) as [bv Hbv]; expect 2. {
        setoid_rewrite Hreads_in. assumption.
      }
      rewrite Hbv. eauto.
    - rewrite RegisterState.set_reg_get_out by crush.
      apply Hinputs_defined.
      propertize_lists1 Hafter_in.
      edestruct Hafter_in; crush.
  Qed.

  Lemma exec_module_item_defined l_before l_after r mi:
    list_subset (Verilog.module_item_reads mi) l_before ->
    list_subset l_after (Verilog.module_item_writes mi ++ l_before) ->
    RegisterState.defined_value_for
      (fun var : variable => In var l_before)
      r ->
    RegisterState.defined_value_for
      (fun var : variable => In var l_after)
      (exec_module_item r mi).
  Proof.
    destruct mi; expect 1.
    simp module_item_reads module_item_writes exec_module_item in *.
    apply exec_statement_defined.
  Qed.

  Lemma exec_module_body_defined l_before l_after r body:
    module_items_sorted l_before body ->
    list_subset l_after (Verilog.module_body_writes body ++ l_before) ->
    RegisterState.defined_value_for
      (fun var : variable => In var l_before)
      r ->
    RegisterState.defined_value_for
      (fun var : variable => In var l_after)
      (exec_module_body r body).
  Proof.
    revert r l_before l_after. induction body; intros * Hsorted Hafter_in Hinputs_defined.
    - simp exec_module_body module_body_reads module_body_writes in *.
      simpl in *.
      setoid_rewrite Hafter_in.
      assumption.
    - simp exec_module_body module_body_reads module_body_writes in *.
      simpl.
      unpack_list_subset.
      apply IHbody with (l_before := (module_item_writes a ++ l_before)).
      + inv Hsorted. assumption.
      + unfold list_subset in *. rewrite Forall_forall in *.
        repeat setoid_rewrite List.in_app_iff.
        repeat setoid_rewrite List.in_app_iff in Hafter_in.
	intros. insterU Hafter_in. intuition eauto.
      + inv Hsorted.
        eapply exec_module_item_defined; eauto; reflexivity.
  Qed.

  Lemma run_vmodule_defined r v:
    vmodule_sortable v ->
    RegisterState.defined_value_for
      (fun var : variable => In var (Verilog.module_inputs v))
      r ->
    RegisterState.defined_value_for
      (fun var : variable => In var (Verilog.module_body_writes (Verilog.modBody v)))
      (run_vmodule v r).
  Proof.
    intros [sorted Hsort] Hdefined.
    unfold run_vmodule. rewrite Hsort.
    eapply exec_module_body_defined.
    - eapply sort_module_items_sorted. eapply Hsort.
    - rewrite <- sort_module_items_permutation with (body':=sorted) by eassumption.
      apply list_subset_app_r.
    - unfold mk_initial_state.
      rewrite RegisterState.limit_to_regs_match_on.
      apply Hdefined.
  Qed.

  Record clean_module v := MkCleanModule { 
    preserve_inputs : forall e, run_vmodule v e =( Verilog.module_inputs v )= e;
    defined_outputs : forall e,
      RegisterState.defined_value_for (fun var => In var (Verilog.module_inputs v)) e ->
      RegisterState.defined_value_for (fun var => In var (Verilog.modVariables v)) (run_vmodule v e)
  }.

  Lemma clean_module_statically v :
    NoDup (Verilog.module_body_writes (Verilog.modBody v)) ->
    Permutation (Verilog.modVariables v) (Verilog.module_body_writes (Verilog.modBody v) ++ Verilog.module_inputs v) ->
    vmodule_sortable v ->
    clean_module v.
  Proof.
    intros ? Hwrites_outputs [sorted Hsort].
    constructor.
    all: unfold run_vmodule.
    all: rewrite Hsort.
    all: unfold mk_initial_state; simpl.
    - intros e.
      rewrite <- Facts.exec_module_body_preserve.
      + apply RegisterState.limit_to_regs_match_on.
      + symmetry.
        apply module_items_sorted_no_overwrite.
        eapply sort_module_items_sorted.
	apply Hsort.
    - intros e Hdefined.
      setoid_rewrite Hwrites_outputs.
      RegisterState.unpack_defined_value_for.
      + setoid_rewrite (sort_module_items_permutation _ _ _ Hsort).
        eapply exec_module_body_defined.
        * eapply sort_module_items_sorted. eapply Hsort.
        * apply list_subset_app_r.
        * apply RegisterState.defined_value_for_limit_to_regs.
          assumption.
      + rewrite <- Facts.exec_module_body_preserve.
        * apply RegisterState.defined_value_for_limit_to_regs.
	  apply Hdefined.
        * symmetry.
          apply module_items_sorted_no_overwrite.
          eapply sort_module_items_sorted.
          apply Hsort.
  Qed.

  Lemma admit_run_vmodule v e:
    clean_module v ->
    v ⇓ (run_vmodule v e).
  Proof.
    unfold "⇓".
    intros [Hpreserve_inputs Hdefined].
    setoid_rewrite Hpreserve_inputs at 2.
    reflexivity.
  Qed.
End Clean.

Module DefinedEquivalence.
  Import CombinationalOnly.
  Export Clean.

  Declare Scope verilog.
  Local Open Scope verilog.

  Record defined_equivalence (v1 v2 : Verilog.vmodule) : Prop :=
    MkDefinedEquivalence {
      inputs_same : Verilog.module_inputs v1 = Verilog.module_inputs v2;
      outputs_same : Verilog.module_outputs v1 = Verilog.module_outputs v2;
      clean_left : clean_module v1;
      clean_right : clean_module v2;
      execution_match : forall init,
        RegisterState.defined_value_for
          (fun var => In var (Verilog.module_inputs v1)) init ->
          (run_vmodule v1 init =( Verilog.module_outputs v1 )= run_vmodule v2 init)
    }.

  Infix "~~" := defined_equivalence (at level 20) : verilog.

  Lemma defined_equivalence_sym v1 v2:
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
      rewrite <- outputs_same0 in *.
      rewrite <- inputs_same0 in *.
      apply execution_match.
      apply H.
  Qed.

  Lemma defined_equivalence_trans v1 v2 v3:
    v1 ~~ v2 -> v2 ~~ v3 -> v1 ~~ v3.
  Proof.
    intros [] [].
    constructor.
    - congruence.
    - congruence.
    - assumption.
    - assumption.
    - intros.
      rewrite <- inputs_same0 in *.
      rewrite <- outputs_same0 in *.
      etransitivity.
      + apply execution_match0.
        apply H.
      + apply execution_match1.
        apply H.
  Qed.

  Lemma defined_equivalence_refl_cond v v':
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
    Verilog.vmodule defined_equivalence
    (* No reflexivity! *)
    symmetry proved by defined_equivalence_sym
    transitivity proved by defined_equivalence_trans
    as defined_equivalence_rel.
End DefinedEquivalence.

Module ExactEquivalence.
  Import CombinationalOnly.
  Export Clean.

  Declare Scope verilog.
  Local Open Scope verilog.

  (* This is the strongest notion of equivalence before definitional equality.

     The modules contain the exact same variables, and give them the
     exact same values, they might just calculate them in different
     ways. This used to just look at outputs, but, we need
     clean_module to transfer over this, and clean_module looks at
     internal variables.

   *)
  Record exact_equivalence (v1 v2 : Verilog.vmodule) : Prop :=
    MkExactEquivalence {
      same_vars : Verilog.modVariableDecls v1 = Verilog.modVariableDecls v2;
      execution_match : forall init, run_vmodule v1 init =( Verilog.modVariables v1 )= run_vmodule v2 init
    }.

  Infix "~~~" := exact_equivalence (at level 20) : verilog.

  Lemma exact_equivalence_sym v1 v2:
    v1 ~~~ v2 ->
    v2 ~~~ v1.
  Proof.
    intros [? execution_match].
    constructor.
    - symmetry. assumption.
    - symmetry.
      rewrite <- (Verilog.module_variables_same _ _ same_vars0).
      auto.
  Qed.

  Lemma exact_equivalence_trans v1 v2 v3:
    v1 ~~~ v2 -> v2 ~~~ v3 -> v1 ~~~ v3.
  Proof.
    intros [] [].
    constructor.
    - congruence.
    - etransitivity.
      all: rewrite <- (Verilog.module_variables_same _ _ same_vars0) in *.
      all: eauto.
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
    destruct H.
    unfold "⇓".
    rewrite <- (Verilog.module_variables_same _ _ same_vars0).
    setoid_rewrite execution_match0.
    reflexivity.
  Qed.

  Lemma equal_exact_equivalence v1 v2 :
    Verilog.modVariableDecls v1 = Verilog.modVariableDecls v2 ->
    run_vmodule v1 = run_vmodule v2 ->
    v1 ~~~ v2.
  Proof.
    intros Hvars Hmatch.
    constructor; try eassumption; expect 1.
    intros regs.
    unfold "⇓".
    rewrite Hmatch.
    reflexivity.
  Qed.

  Lemma exact_equivalence_same_inputs v1 v2 :
    v1 ~~~ v2 ->
    Verilog.module_inputs v1 = Verilog.module_inputs v2.
  Proof.
    intros [].
    apply Verilog.module_inputs_same.
    apply same_vars0.
  Qed.

  Lemma exact_equivalence_same_outputs v1 v2 :
    v1 ~~~ v2 ->
    Verilog.module_outputs v1 = Verilog.module_outputs v2.
  Proof.
    intros [].
    apply Verilog.module_outputs_same.
    apply same_vars0.
  Qed.

  Lemma exact_equivalence_same_vars v1 v2 :
    v1 ~~~ v2 ->
    Verilog.modVariables v1 = Verilog.modVariables v2.
  Proof.
    intros [].
    apply Verilog.module_variables_same.
    apply same_vars0.
  Qed.

  Import DefinedEquivalence.

  Lemma exact_equivalence_defined_equivalence v1 v2 :
    clean_module v1 ->
    clean_module v2 ->
    v1 ~~~ v2 ->
    v1 ~~ v2.
  Proof.
    intros Hclean1 Hclean2 Hequiv.
    constructor.
    - destruct Hequiv.
      apply Verilog.module_inputs_same.
      apply same_vars0.
    - destruct Hequiv.
      apply Verilog.module_outputs_same.
      apply same_vars0.
    - apply Hclean1.
    - apply Hclean2.
    - intros.
      destruct Hequiv.
      setoid_rewrite Verilog.module_outputs_in_vars.
      apply execution_match0.
  Qed.

  Lemma exact_by_output_equality v1 v2:
    Verilog.modVariableDecls v1 = Verilog.modVariableDecls v2 ->
    (forall initial, run_vmodule v1 initial =( Verilog.modVariables v1 )= run_vmodule v2 initial) ->
    v1 ~~~ v2.
  Proof.
    intros Heqvars Hmatch.
    constructor.
    all: assumption.
  Qed.

  Lemma transfer_clean v1 v2 :
    v1 ~~~ v2 ->
    clean_module v1 ->
    clean_module v2.
  Proof.
    intros [Hsame_vars Hequiv] Hclean1.
    constructor.
    - intros e.
      rewrite <- (Verilog.module_inputs_same _ _ Hsame_vars).
      transitivity (run_vmodule v1 e).
      + setoid_rewrite Verilog.module_input_in_vars.
        symmetry. apply Hequiv.
      + apply preserve_inputs. apply Hclean1.
    - intros e Hinputs_defined.
      specialize (Hequiv e).
      (* rewrite <- Houtput_names. *)
      (* RegisterState.unpack_match_on. *)
      rewrite <- (Verilog.module_variables_same _ _ Hsame_vars).
      rename_match (run_vmodule v1 e =( Verilog.modVariables v1 )= run_vmodule v2 e)
        into Hmatch_outputs.
      rewrite <- Hmatch_outputs.
      apply Hclean1.
      rewrite (Verilog.module_inputs_same _ _ Hsame_vars).
      apply Hinputs_defined.
  Qed.

  (* a ~~~ b -> b ~~ c -> a ~~ c *)
  Global Instance Proper_defined_equivalence_exact_equivalence :
    Proper
      (exact_equivalence ==> exact_equivalence ==> iff)
      (defined_equivalence).
  Proof.
    intros v1 v2 Heq v1' v2' Heq'. split; intro Heq_behaviour.
    - constructor.
      + destruct Heq, Heq', Heq_behaviour.
        apply Verilog.module_inputs_same in same_vars0.
        apply Verilog.module_inputs_same in same_vars1.
        congruence.
      + destruct Heq, Heq', Heq_behaviour.
        apply Verilog.module_outputs_same in same_vars0.
        apply Verilog.module_outputs_same in same_vars1.
        congruence.
      + destruct Heq_behaviour.
        eapply transfer_clean; eassumption.
      + destruct Heq_behaviour.
        eapply transfer_clean; eassumption.
      + intros e Hinputs_defined.
        destruct Heq, Heq', Heq_behaviour.
	transitivity (run_vmodule v1 e). {
	  symmetry. 
	  setoid_rewrite Verilog.module_outputs_in_vars.
	  setoid_rewrite <- (Verilog.module_variables_same _ _ same_vars0).
	  apply execution_match0.
	}
	transitivity (run_vmodule v1' e). {
	  setoid_rewrite <- (Verilog.module_outputs_same _ _ same_vars0).
	  apply execution_match2.
	  setoid_rewrite (Verilog.module_inputs_same _ _ same_vars0).
	  apply Hinputs_defined.
	}
	setoid_rewrite <- (Verilog.module_outputs_same _ _ same_vars0).
	rewrite outputs_same0.
	setoid_rewrite Verilog.module_outputs_in_vars.
	apply execution_match1.
    - constructor.
      + destruct Heq, Heq', Heq_behaviour.
        apply Verilog.module_inputs_same in same_vars0.
        apply Verilog.module_inputs_same in same_vars1.
        congruence.
      + destruct Heq, Heq', Heq_behaviour.
        apply Verilog.module_outputs_same in same_vars0.
        apply Verilog.module_outputs_same in same_vars1.
        congruence.
      + destruct Heq_behaviour.
        eapply transfer_clean.
	* symmetry. eassumption.
	* eassumption. 
      + destruct Heq_behaviour.
        eapply transfer_clean.
	* symmetry. eassumption.
	* eassumption. 
      + intros e Hinputs_defined.
        destruct Heq, Heq', Heq_behaviour.
	transitivity (run_vmodule v2 e). {
	  setoid_rewrite Verilog.module_outputs_in_vars.
	  apply execution_match0.
	}
	transitivity (run_vmodule v2' e). {
	  setoid_rewrite (Verilog.module_outputs_same _ _ same_vars0).
	  apply execution_match2.
	  setoid_rewrite <- (Verilog.module_inputs_same _ _ same_vars0).
	  apply Hinputs_defined.
	}
	symmetry.
	setoid_rewrite (Verilog.module_outputs_same _ _ same_vars0).
	rewrite outputs_same0.
	setoid_rewrite <- (Verilog.module_outputs_same _ _ same_vars1).
	setoid_rewrite Verilog.module_outputs_in_vars.
	apply execution_match1.
  Qed.
End ExactEquivalence.

