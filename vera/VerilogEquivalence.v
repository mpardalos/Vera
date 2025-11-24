From vera Require Import Verilog.
From vera Require Import VerilogSMT.
Import (coercions) SMT.
From vera Require Import Common.
Import (coercions) VerilogSMTBijection.
Import VerilogSMTBijection (bij_inverse, bij_apply, bij_wf).
From vera Require VerilogToSMT.
From vera Require SMTQueries.
From vera Require Import Decidable.
From vera Require Import Tactics.

From ExtLib Require Import Data.List.
From ExtLib Require Import Data.Monads.EitherMonad.
From ExtLib Require Import Data.Monads.StateMonad.
From ExtLib Require Import Data.String.
From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.MonadState.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Monoid.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Programming.Show.

From Stdlib Require Import ZArith.
From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Structures.Equalities.

From Equations Require Import Equations.

Import SigTNotations.
Import ListNotations.
Import CommonNotations.
Import MonadLetNotation.
Import FunctorNotation.
Local Open Scope monad_scope.
Local Open Scope string.

Equations mk_var_same (var : Verilog.variable) (m : VerilogSMTBijection.t)
  : sum string SMTLib.term := {
  | var, m with m (TaggedVariable.VerilogLeft, var), m (TaggedVariable.VerilogRight, var) => {
    | Some smt_name1, Some smt_name2 =>
        inr (SMTLib.Term_Eq (SMTLib.Term_Const smt_name1) (SMTLib.Term_Const smt_name2))
    | _, _ => inl "mk_var_same"%string
    }
  }
  .

Equations mk_inputs_same (inputs : list Verilog.variable) (m : VerilogSMTBijection.t)
  : sum string SMTLib.term := {
  | [], m => inr SMTLib.Term_True
  | (var :: vars), m =>
      match
        mk_var_same var m,
        mk_inputs_same vars m
      with
      | inr hd, inr tl =>
          inr (SMTLib.Term_And hd tl)
      | _, _ => inl "err"%string
      end
  }.

Equations mk_var_distinct (var : Verilog.variable) (m : VerilogSMTBijection.t)
  : sum string SMTLib.term := {
  | var, m with m (TaggedVariable.VerilogLeft, var), m (TaggedVariable.VerilogRight, var) => {
    | Some smt_name1, Some smt_name2 =>
        inr (SMTLib.Term_Not (SMTLib.Term_Eq (SMTLib.Term_Const smt_name1) (SMTLib.Term_Const smt_name2)))
    | _, _ => inl "mk_var_distinct"%string
    }
  }
  .

Equations mk_outputs_distinct (inputs : list Verilog.variable) (m : VerilogSMTBijection.t)
  : sum string SMTLib.term := {
  | [], m => inr SMTLib.Term_False
  | (var :: vars), m =>
      match
        mk_var_distinct var m,
        mk_outputs_distinct vars m
      with
      | inr hd, inr tl =>
          inr (SMTLib.Term_Or hd tl)
      | _, _ => inl "err"%string
      end
  }.

Lemma mk_bijection_only_tag tag vars m :
  VerilogToSMT.mk_bijection tag vars = inr m ->
  VerilogSMTBijection.only_tag tag m.
Proof.
  revert m.
  funelim (VerilogToSMT.mk_bijection tag vars); intros.
  - inv H. apply VerilogSMTBijection.only_tag_empty.
  - simp mk_bijection in H0; inv H0; autodestruct.
    eauto using VerilogSMTBijection.only_tag_insert.
Qed.

Lemma verilog_to_smt_only_tag tag start v s :
  VerilogToSMT.verilog_to_smt tag start v = inr s ->
  VerilogSMTBijection.only_tag tag (SMT.nameMap s).
Proof.
  intros.
  unfold VerilogToSMT.verilog_to_smt in *. simpl in *.
  autodestruct_eqn E. cbn.
  eauto using mk_bijection_only_tag.
Qed.

Lemma mk_bijection_min_name tag start vars m var name :
  VerilogToSMT.mk_bijection tag (VerilogToSMT.assign_vars start vars) = inr m ->
  m (tag, var) = Some name ->
  name >= start.
Proof.
  revert m start.
  induction vars; intros * Hfunc Hm; simp assign_vars mk_bijection in *.
  - inv Hfunc. discriminate.
  - monad_inv.
    destruct (dec (a = var)).
    + subst a.
      rewrite VerilogSMTBijection.lookup_insert_in in Hm. inv Hm.
      lia.
    + rewrite VerilogSMTBijection.lookup_insert_out in Hm by crush.
      insterU IHvars.
      crush.
Qed.

Lemma verilog_to_smt_min_name tag start v s var name :
  VerilogToSMT.verilog_to_smt tag start v = inr s ->
  SMT.nameMap s (tag, var) = Some name ->
  name >= start.
Proof.
  intros.
  unfold VerilogToSMT.verilog_to_smt in *. simpl in *.
  autodestruct_eqn E. simpl in *.
  eauto using mk_bijection_min_name.
Qed.

Lemma mk_bijection_max_name vars : forall tag start m var name,
  VerilogToSMT.mk_bijection tag (VerilogToSMT.assign_vars start vars) = inr m ->
  m (tag, var) = Some name ->
  name <= start + length vars.
Proof.
  induction vars;
    intros * Hfunc Hm;
    simp assign_vars mk_bijection in *; simpl in *;
    monad_inv.
  - discriminate.
  - destruct (dec (a = var)).
    + subst a.
      rewrite VerilogSMTBijection.lookup_insert_in in Hm. inv Hm.
      lia.
    + rewrite VerilogSMTBijection.lookup_insert_out in Hm by crush.
      insterU IHvars.
      crush.
Qed.

Lemma verilog_to_smt_max_name tag start s v var name :
  VerilogToSMT.verilog_to_smt tag start v = inr s ->
  SMT.nameMap s (tag, var) = Some name ->
  name <= start + length (Verilog.modVariables v).
Proof.
  intros Hfunc Hm.
  unfold VerilogToSMT.verilog_to_smt in Hfunc.
  monad_inv.
  eapply mk_bijection_max_name; eassumption.
Qed.

Program Definition equivalence_query (verilog1 verilog2 : Verilog.vmodule) : sum string (SMT.smt_with_namemap) :=
  let* inputs_ok1 := assert_dec (Verilog.module_inputs verilog1 = Verilog.module_inputs verilog2) "Inputs don't match" in
  let* outputs_ok1 := assert_dec (Verilog.module_outputs verilog1 = Verilog.module_outputs verilog2) "Outputs don't match" in

  let* ( smt1 ; prf1 ) := sum_with_eqn (VerilogToSMT.verilog_to_smt TaggedVariable.VerilogLeft 0 verilog1) in
  let* ( smt2 ; prf2 ) := sum_with_eqn (VerilogToSMT.verilog_to_smt TaggedVariable.VerilogRight (S (length (Verilog.modVariables verilog1))) verilog2) in

  let nameMap := VerilogSMTBijection.combine (SMT.nameMap smt1) (SMT.nameMap smt2) _ _ in

  let* inputs_same := mk_inputs_same (Verilog.module_inputs verilog1) nameMap in
  let* outputs_distinct := mk_outputs_distinct (Verilog.module_outputs verilog1) nameMap in

  let* sortable1 := assert_dec (VerilogSort.vmodule_sortable verilog1) "Left verilog module is not sortable" in
  let* sortable2 := assert_dec (VerilogSort.vmodule_sortable verilog2) "Right verilog module is not sortable" in
  let* prf1 := assert_dec _ "Unknown variables in inputs_same assertion" in
  let* prf2 := assert_dec _ "Unknown variables in outputs_distinct assertion" in

  ret {|
      SMT.nameMap := nameMap ;
      SMT.query :=
        SMTQueries.add_assertion outputs_distinct
          (SMTQueries.add_assertion inputs_same
             (SMTQueries.combine (SMT.query smt1) (SMT.query smt2))
             prf1
          )
          prf2
    |}
.
Next Obligation.
  (* No shared verilog names *)
  repeat apply_somewhere verilog_to_smt_only_tag.
  unfold VerilogSMTBijection.only_tag in *.
  match goal with
  [ |- ?x = None ] => destruct x eqn:E; [|reflexivity]
  end.
  rewrite VerilogSMTBijection.bij_wf in H, E.
  apply (f_equal (option_map fst)) in H, E.
  insterU X. insterU X0.
  crush.
Qed.
Next Obligation.
  (* No shared smt names *)
  match goal with
  [ |- ?x = None ] => destruct x as [[t' v']|] eqn:E; [|reflexivity]
  end.
  replace t with TaggedVariable.VerilogLeft in *; cycle 1. {
    symmetry.
    eapply verilog_to_smt_only_tag. eassumption.
    rewrite H. reflexivity.
  }
  replace t' with TaggedVariable.VerilogRight in *; cycle 1. {
    symmetry.
    eapply verilog_to_smt_only_tag. eassumption.
    rewrite E. reflexivity.
  }
  rewrite <- VerilogSMTBijection.bij_wf in H, E.
  pose proof (verilog_to_smt_min_name TaggedVariable.VerilogLeft) as Hmin_left. insterU Hmin_left.
  pose proof (verilog_to_smt_min_name TaggedVariable.VerilogRight) as Hmin_right. insterU Hmin_right.
  pose proof (verilog_to_smt_max_name TaggedVariable.VerilogLeft) as Hmax_left. insterU Hmax_left.
  lia.
Qed.
