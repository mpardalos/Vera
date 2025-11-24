From Stdlib Require Import BinNat.
From Stdlib Require Import String.
From Stdlib Require Import Nat.
From Stdlib Require Import Structures.OrderedTypeEx.
From Stdlib Require Import List.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import ssreflect.
From Stdlib Require Import Relations.
From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Psatz.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Classical.

From vera Require Import Verilog.
From vera Require Import Common.
From vera Require Import Bitvector.
Import (notations) XBV.
Import RawXBV (bit(..)).
From vera Require Import Tactics.
From vera Require Import Decidable.
From vera Require Import VerilogSort.

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
  rewrite ! Forall_app ! Forall_forall.
  crush.
Qed.

Ltac disjoint_saturate :=
  repeat match goal with
         | [ H : disjoint (_ :: _) _ |- _ ] =>
	   inv H
         | [ H : disjoint _ (_ :: _) |- _ ] =>
	   symmetry in H;
	   inv H
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

Module CombinationalOnly.
  Definition Process := Verilog.module_item.

  Section Sorted.
    Equations module_items_sorted : list Verilog.module_item -> Prop :=
      module_items_sorted [] := True;
      module_items_sorted (mi :: mis) :=
        Forall (fun mi' => disjoint (Verilog.module_item_writes mi) (Verilog.module_item_reads mi')) mis
               /\ module_items_sorted mis
    .

    Global Instance dec_module_items_sorted ms : DecProp (module_items_sorted ms).
    Proof.
      induction ms;
        simp module_items_sorted;
        try typeclasses eauto.
    Defined.
  End Sorted.

  Module VariableAsMDT <: MiniDecidableType.
    Definition t := Verilog.variable.
    Definition eq_dec (x y : t) := dec (x = y).
  End VariableAsMDT.

  Module VariableAsUDT := Make_UDT(VariableAsMDT).

  Module VariableDepMap := MkDepFunMap(VariableAsUDT).

  Definition RegisterState := VariableDepMap.t (fun var => XBV.xbv (Verilog.varType var)).

  Definition set_reg (var : Verilog.variable) (value : XBV.xbv (Verilog.varType var)) : RegisterState -> RegisterState :=
    VariableDepMap.insert var value.

  Lemma set_reg_get_in var val regs :
    set_reg var val regs var = Some val.
  Proof.
    unfold set_reg, VariableDepMap.insert.
    autodestruct; [|contradiction].
    rewrite (proof_irrelevance _ e eq_refl).
    reflexivity.
  Qed.

  Lemma set_reg_get_out var1 var2 val regs :
    var1 <> var2 ->
    set_reg var1 val regs var2 = regs var2.
  Proof.
    intros.
    unfold set_reg, VariableDepMap.insert.
    autodestruct; [contradiction|].
    reflexivity.
  Qed.

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
    eval_expr {w} (regs: RegisterState) (e : Verilog.expression w) : option (XBV.xbv w) :=
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
    exec_statement (regs : RegisterState) (stmt : Verilog.statement) : option RegisterState by struct :=
    exec_statement regs (Verilog.BlockingAssign (Verilog.NamedExpression var) rhs) :=
      let* rhs_val := eval_expr regs rhs in
      Some (set_reg var rhs_val regs) ;
    exec_statement regs (Verilog.BlockingAssign lhs rhs) :=
      None;
  .

  Equations
    exec_module_item : RegisterState -> Verilog.module_item -> option RegisterState :=
    exec_module_item st (Verilog.AlwaysComb stmt ) :=
      exec_statement st stmt;
  .

  Equations
    exec_module_body : RegisterState -> list Verilog.module_item -> option RegisterState :=
    exec_module_body regs [] := Some regs;
    exec_module_body regs (mi :: mis) :=
      let* regs' := exec_module_item regs mi in
      exec_module_body regs' mis;
  .

  (** The values of the final state of the execution of module *)
  Definition execution := RegisterState.

  Definition register_state_match_on (C : Verilog.variable -> Prop) (e1 e2 : RegisterState) : Prop :=
    forall var, C var -> e1 var = e2 var.

  Notation "rs1 ={ P }= rs2" :=
    (register_state_match_on P rs1 rs2)
    (at level 80) : type_scope.

  Notation "rs1 =( vars )= rs2" :=
    (rs1 ={fun var => In var vars}= rs2)
    (at level 80) : type_scope.

  Lemma register_state_match_on_impl C1 C2 e1 e2:
    (forall var, C2 var -> C1 var) ->
    e1 ={ C1 }= e2 ->
    e1 ={ C2 }= e2.
  Proof. unfold register_state_match_on. crush. Qed.

  (* `RegisterState`s match on the given set, and both have values for every variable in it (Xs are allowed) *)
  Definition execution_match_on (C : Verilog.variable -> Prop) (e1 e2 : RegisterState) : Prop :=
    forall var, C var -> exists xbv, e1 var = Some xbv /\ e2 var = Some xbv.

  Notation "rs1 =!{ P }!= rs2" :=
    (execution_match_on P rs1 rs2)
    (at level 80) : type_scope.

  Notation "rs1 =!( vars )!= rs2" :=
    (rs1 =!{ fun var => In var vars }!= rs2)
    (at level 80) : type_scope.

  Lemma execution_match_on_impl C1 C2 e1 e2:
    (forall var, C2 var -> C1 var) ->
    e1 =!{ C1 }!= e2 ->
    e1 =!{ C2 }!= e2.
  Proof. unfold execution_match_on. crush. Qed.

  (* `RegisterState`s match on the given set, and both have values for every variable in it (Xs are NOT allowed) *)
  Definition execution_defined_match_on (C : Verilog.variable -> Prop) (e1 e2 : RegisterState) : Prop :=
    forall var, C var -> exists xbv, e1 var = Some xbv /\ e2 var = Some xbv /\ ~ XBV.has_x xbv.

  Notation "rs1 =!!{ P }!!= rs2" :=
    (execution_defined_match_on P rs1 rs2)
    (at level 80) : type_scope.

  Notation "rs1 =!!( vars )!!= rs2" :=
    (rs1 =!!{ fun var => In var vars }!!= rs2)
    (at level 80) : type_scope.

  Lemma execution_defined_match_on_rewrite_left C e1 e1' e2 :
    (forall var, C var -> e1 var = e1' var) ->
    execution_defined_match_on C e1 e2 <-> execution_defined_match_on C e1' e2.
  Proof.
    unfold execution_defined_match_on.
    intros Heq. split; intros Hmatch var HC.
    - rewrite <- Heq; auto.
    - rewrite Heq; auto.
  Qed.
  
  Lemma execution_defined_match_on_rewrite_right C e1 e2 e2' :
    (forall var, C var -> e2 var = e2' var) ->
    execution_defined_match_on C e1 e2 <-> execution_defined_match_on C e1 e2'.
  Proof.
    unfold execution_defined_match_on.
    intros Heq. split; intros Hmatch var HC.
    - rewrite <- Heq; auto.
    - rewrite Heq; auto.
Qed.

  Global Instance execution_match_on_proper :
    Proper (pointwise_relation Verilog.variable iff ==> eq ==> eq ==> iff) execution_match_on.
  Proof. repeat intro. subst. crush. Qed.

  Global Instance register_state_match_on_proper :
    Proper (pointwise_relation Verilog.variable iff ==> eq ==> eq ==> iff) register_state_match_on.
  Proof. repeat intro. subst. crush. Qed.

  Definition limit_to_regs (vars : list Verilog.variable) (regs : RegisterState) : RegisterState :=
    fun var =>
      match dec (In var vars) with
      | left prf => regs var
      | right prf => None
      end.

  Definition mk_initial_state (v : Verilog.vmodule) (regs : RegisterState) : RegisterState :=
    limit_to_regs (Verilog.module_inputs v) regs.

  Definition run_vmodule (v : Verilog.vmodule) (inputs : RegisterState) : option RegisterState :=
    let* sorted := sort_module_items (Verilog.module_inputs v) (Verilog.modBody v) in
    exec_module_body (mk_initial_state v inputs) sorted.

  Definition valid_execution (v : Verilog.vmodule) (e : execution) :=
    exists (e' : execution),
      run_vmodule v e = Some e'
      /\ e' =!( Verilog.module_inputs v ++ Verilog.module_body_writes (Verilog.modBody v))!= e.

  (** All variables of v have a value in the execution *)
  Definition complete_execution (v : Verilog.vmodule) (e : execution) :=
    forall var, In var (Verilog.modVariables v) -> exists bv, e var = Some bv.

  (** All variables of v, *and no other variables*, have a value in the execution *)
  Definition exact_execution (v : Verilog.vmodule) (e : execution) :=
    forall var, In var (Verilog.modVariables v) <-> exists bv, e var = Some bv.

  Definition execution_not_x (e : execution) name :=
    forall v, e name = Some v -> ~ XBV.has_x v.

  Definition execution_no_exes_for C (e : execution) :=
    forall var, C var -> execution_not_x e var.

  Definition execution_no_exes := execution_no_exes_for (fun _ => True).

  Definition no_errors (v : Verilog.vmodule) :=
    forall (initial : RegisterState)
      (input_defined : forall var, exists xbv, initial var = Some xbv -> ~ XBV.has_x xbv),
    exists final, run_vmodule v initial = Some final.
End CombinationalOnly.

Module Facts.
  Import CombinationalOnly.

  Lemma register_state_match_on_empty C regs1 regs2 :
    (forall var, ~ (C var)) ->
    regs1 ={ C }= regs2.
  Proof. unfold "_ ={ _ }= _". crush. Qed.

  Lemma register_state_match_on_split_iff C1 C2 regs1 regs2 :
    register_state_match_on (fun var => C1 var \/ C2 var) regs1 regs2 <->
      (register_state_match_on C1 regs1 regs2 /\ register_state_match_on C2 regs1 regs2).
  Proof. unfold register_state_match_on. crush. Qed.

  Lemma register_state_match_on_app_iff l1 l2 regs1 regs2 :
    (regs1 =( l1 ++ l2 )= regs2) <-> (regs1 =( l1 )= regs2 /\ regs1 =( l2 )= regs2).
  Proof.
    setoid_rewrite List.in_app_iff.
    apply register_state_match_on_split_iff.
  Qed.

  Lemma register_state_match_on_trans C regs1 regs2 regs3 :
    regs1 ={ C }= regs2 ->
    regs2 ={ C }= regs3 ->
    regs1 ={ C }= regs3.
  Proof.
    unfold "_ ={ _ }= _".
    intros H12 H23 var HC.
    insterU H12. insterU H23.
    crush.
  Qed.

  Lemma register_state_match_on_sym C regs1 regs2 :
    regs1 ={ C }= regs2 ->
    regs2 ={ C }= regs1.
  Proof.
    unfold "_ ={ _ }= _".
    intros H var HC.
    insterU H. crush.
  Qed.

  Lemma register_state_match_on_refl C regs :
    regs ={ C }= regs.
  Proof. unfold "_ ={ _ }= _". crush. Qed.

  Add Parametric Relation (C : Verilog.variable -> Prop) :
    RegisterState (register_state_match_on C)
    reflexivity proved by (register_state_match_on_refl C)
    symmetry proved by (register_state_match_on_sym C)
    transitivity proved by (register_state_match_on_trans C)
    as register_state_match_on_rel.

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

  Ltac unpack_verilog_smt_match_states_partial :=
    repeat match goal with
      | [ H: register_state_match_on (fun _ => _ \/ _) _ _ |- _ ] =>
          apply register_state_match_on_split_iff in H;
          destruct H
      | [ H: register_state_match_on (fun _ => List.In _ (_ ++ _)) _ _ |- _ ] =>
          setoid_rewrite List.in_app_iff in H
      | [ |- register_state_match_on (fun _ => List.In _ (_ ++ _)) _ _ ] =>
          setoid_rewrite List.in_app_iff
      | [ |- register_state_match_on (fun _ => _ \/ _) _ _ ] =>
          apply register_state_match_on_split_iff; split
      end.

  Lemma register_state_match_on_set_reg_elim2 var x regs1 regs2 :
    set_reg var x regs1 =( [var] )= set_reg var x regs2.
  Proof.
    unfold "_ =( _ )= _". intros var' Hvarin. inv Hvarin; [|crush].
    rewrite ! set_reg_get_in. crush.
  Qed.

  Lemma register_state_match_on_set_reg_elim C var x regs :
    ~ C var ->
    set_reg var x regs ={ C }= regs.
  Proof.
    unfold "_ ={ _ }= _". intros HnC var' HC.
    erewrite set_reg_get_out by crush.
    crush.
  Qed.

  Lemma eval_expr_change_regs w (e : Verilog.expression w) : forall regs regs',
    regs =(Verilog.expr_reads e)= regs' ->
    eval_expr regs e = eval_expr regs' e.
  Proof.
    induction e; intros; simp eval_expr expr_reads in *;
      unpack_verilog_smt_match_states_partial;
      try erewrite IHe with (regs':=regs') by assumption;
      try erewrite IHe1 with (regs':=regs') by assumption;
      try erewrite IHe2 with (regs':=regs') by assumption;
      try erewrite IHe3 with (regs':=regs') by assumption;
      try reflexivity;
      [idtac].
    unfold "_ =( _ )= _" in H. insterU H.
    crush.
  Qed.

  Lemma exec_statement_change_regs stmt regs1 regs2 : forall regs1' regs2',
    regs1 =(Verilog.statement_reads stmt)= regs2 ->
    exec_statement regs1 stmt = Some regs1' ->
    exec_statement regs2 stmt = Some regs2' ->
    regs1' =(Verilog.statement_writes stmt)= regs2'.
  Proof.
    intros * Hmatch Hexec1 Hexec2.
    funelim (exec_statement regs1 stmt);
      rewrite <- Heqcall in *; try discriminate;
      [idtac].
    clear Heqcall.
    simp exec_statement statement_reads statement_writes expr_reads in *.
    monad_inv.
    erewrite eval_expr_change_regs in E by eassumption.
    replace x0 with x by crush.
    eapply register_state_match_on_set_reg_elim2.
  Qed.

  Lemma exec_module_item_change_regs mi regs1 regs2 : forall regs1' regs2',
    regs1 =(Verilog.module_item_reads mi)= regs2 ->
    exec_module_item regs1 mi = Some regs1' ->
    exec_module_item regs2 mi = Some regs2' ->
    regs1' =(Verilog.module_item_writes mi)= regs2'.
  Proof.
    intros * Hmatch Hexec1 Hexec2.
    funelim (exec_module_item regs1 mi);
      rewrite <- Heqcall in *; try discriminate;
      [idtac].
    simp exec_module_item module_item_reads module_item_writes in *.
    eauto using exec_statement_change_regs.
  Qed.

  Lemma exec_statement_preserve C stmt regs1 regs2 :
    Forall (fun var => ~ C var) (Verilog.statement_writes stmt) ->
    exec_statement regs1 stmt = Some regs2 ->
    regs1 ={ C }= regs2.
  Proof.
    intros H Hexec.
    rewrite Forall_forall in H.
    destruct stmt; destruct lhs; simp exec_statement in *; try discriminate.
    monad_inv.
    symmetry.
    eapply register_state_match_on_set_reg_elim.
    simp statement_writes expr_reads. crush.
  Qed.

  Lemma exec_module_item_preserve mi C regs1 regs2 :
    Forall (fun var => ~ C var) (Verilog.module_item_writes mi) ->
    exec_module_item regs1 mi = Some regs2 ->
    regs1 ={ C }= regs2.
  Proof.
    intros H Hexec.
    funelim (exec_module_item regs1 mi);
      rewrite <- Heqcall in *; clear Heqcall;
      try discriminate; [idtac].
    simp exec_module_item module_item_reads module_item_writes in *.
    eauto using exec_statement_preserve.
  Qed.

  Lemma exec_module_body_preserve body : forall C regs1 regs2,
    Forall (fun var => ~ C var) (Verilog.module_body_writes body) ->
    exec_module_body regs1 body = Some regs2 ->
    regs1 ={ C }= regs2.
  Proof.
    induction body; intros; simp exec_module_body in *.
    - crush.
    - destruct (exec_module_item regs1 a) eqn:E; simpl in *; [|discriminate].
      simp module_body_writes in H. rewrite Forall_app in H. destruct H.
      etransitivity.
      + eapply exec_module_item_preserve; eassumption.
      + eapply IHbody; eassumption.
  Qed.

  Lemma exec_module_body_change_regs body : forall regs1 regs2 regs1' regs2',
    NoDup (Verilog.module_body_writes body) ->
    disjoint (Verilog.module_body_writes body) (Verilog.module_body_reads body) ->
    regs1 =(Verilog.module_body_reads body)= regs2 ->
    exec_module_body regs1 body = Some regs1' ->
    exec_module_body regs2 body = Some regs2' ->
    regs1' =(Verilog.module_body_writes body)= regs2'.
  Proof.
    induction body; intros * Hnodup Ndisjoint Heq Hexec1 Hexec2; simp module_body_writes.
    - apply register_state_match_on_empty.
      crush.
    - simp exec_module_body module_body_reads module_body_writes in *.
      disjoint_saturate.
      apply register_state_match_on_app_iff in Heq. destruct Heq.
      destruct (exec_module_item regs1 a) as [regs1a|] eqn:E1,
               (exec_module_item regs2 a) as [regs2a|] eqn:E2;
        simpl in *; try discriminate; [idtac].
      apply register_state_match_on_app_iff.
      split.
      + etransitivity. {
          symmetry.
          eapply exec_module_body_preserve; [|eapply Hexec1].
          apply Forall_forall. intros.
          eapply disjoint_r_intro; eassumption.
        }
	transitivity regs2a. {
	  eapply exec_module_item_change_regs; eassumption.
	}
	eapply exec_module_body_preserve; [|eapply Hexec2].
        apply Forall_forall. intros.
        eapply disjoint_r_intro; eassumption.
      + eapply (IHbody regs1a regs2a).
        * eassumption.
	* apply disjoint_sym. assumption.
	* transitivity regs1. {
	    symmetry.
	    eapply exec_module_item_preserve.
	    -- apply disjoint_sym. eassumption.
	    -- assumption.
	  }
	  transitivity regs2. { assumption. }
	  eapply exec_module_item_preserve.
	  -- apply disjoint_sym. eassumption.
	  -- assumption.
        * assumption.
	* assumption.
  Qed.

  Lemma set_reg_swap var1 var2 x1 x2 regs :
    var1 <> var2 ->
    set_reg var1 x1 (set_reg var2 x2 regs) = set_reg var2 x2 (set_reg var1 x1 regs).
  Proof.
    intro Hneq.
    apply functional_extensionality_dep. intro var.
    destruct (dec (var = var1)), (dec (var = var2)); subst.
    - contradiction.
    - repeat (rewrite set_reg_get_in || rewrite set_reg_get_out); crush.
    - repeat (rewrite set_reg_get_in || rewrite set_reg_get_out); crush.
    - repeat (rewrite set_reg_get_in || rewrite set_reg_get_out); crush.
  Qed.

  Lemma eval_expr_none_inv w rs (e : Verilog.expression w) :
    eval_expr rs e = None ->
    Exists (fun var => rs var = None) (Verilog.expr_reads e).
  Proof.
    rewrite Exists_exists.
    intros. induction e;
      simp eval_expr expr_reads in *;
      repeat setoid_rewrite in_app_iff;
      monad_inv.
    - edestruct IHe2; crush.
    - edestruct IHe1; crush.
    - edestruct IHe2; crush.
    - edestruct IHe1; crush.
    - edestruct IHe2; crush.
    - edestruct IHe1; crush.
    - edestruct IHe; crush.
    - edestruct IHe3; crush.
    - edestruct IHe2; crush.
    - edestruct IHe1; crush.
    - edestruct IHe2; crush.
    - edestruct IHe1; crush.
    - edestruct IHe2; crush.
    - edestruct IHe1; crush.
    - crush.
    - edestruct IHe; crush.
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
      monad_inv; unpack_verilog_smt_match_states_partial.
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

  Lemma exec_module_item_change_regs_none mi : forall rs1 rs2,
    exec_module_item rs1 mi = None ->
    rs1 =( Verilog.module_item_reads mi )= rs2 ->
    exec_module_item rs2 mi = None.
  Proof.
    destruct mi as [[? [] rhs]]; intros;
      simp
        module_item_reads statement_reads
        exec_module_item exec_statement
      in *; [idtac].
    monad_inv.
    erewrite eval_expr_change_regs_none; crush.
  Qed.

  Lemma exec_module_body_change_regs_none body : forall rs1 rs2,
    exec_module_body rs1 body = None ->
    rs1 =( Verilog.module_body_reads body )= rs2 ->
    exec_module_body rs2 body = None.
  Proof.
    induction body; intros;
      simp module_body_reads exec_module_body in *;
      [crush|].
    unpack_verilog_smt_match_states_partial.
    admit.
  Admitted.

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
	     eapply register_state_match_on_set_reg_elim.
	     now disjoint_saturate.
	   }
	   congruence.
	 }
	 replace x1 with x0; cycle 1. {
	   erewrite eval_expr_change_regs with (regs' := rs0) in E1; cycle 1. {
	     eapply register_state_match_on_set_reg_elim.
	     now disjoint_saturate.
	   }
	   congruence.
	 }
	 eapply set_reg_swap.
	 now disjoint_saturate.
       * exfalso.
         eapply exec_module_item_change_regs_none with (rs2:=rs0) in Eyx. { congruence. }
	 symmetry.
	 eapply exec_module_item_preserve; [apply disjoint_sym|eassumption].
	 now disjoint_saturate.
       * exfalso.
         eapply exec_module_item_change_regs_none with (rs2:=rs0) in Exy. { congruence. }
	 symmetry.
	 eapply exec_module_item_preserve; [apply disjoint_sym|eassumption].
	 now disjoint_saturate.
       * reflexivity.
     + destruct (exec_module_item rs0x y) as [rs0xy|] eqn:Exy; [|reflexivity].
       exfalso.
       eapply exec_module_item_change_regs_none with (rs2:=rs0x) in Ey. { congruence. }
       eapply exec_module_item_preserve; [apply disjoint_sym|eassumption].
       now disjoint_saturate.
     + destruct (exec_module_item rs0y x) as [rs0yx|] eqn:E; [|reflexivity].
       exfalso.
       eapply exec_module_item_change_regs_none with (rs2:=rs0y) in Ex. { congruence. }
       eapply exec_module_item_preserve; [apply disjoint_sym|eassumption].
       now disjoint_saturate.
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
