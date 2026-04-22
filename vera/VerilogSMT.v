From Stdlib Require Import ZArith.
From Stdlib Require Import BinNums.
From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Structures.Equalities.
Import ListNotations.

From Equations Require Import Equations.

From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Bitvector.
From vera Require Import VerilogSemantics.
From vera Require Import Verilog.
From vera Require Import Tactics.
From vera Require SMTQueries.
Import VerilogSemantics.CombinationalOnly.

From vera Require Import BVList.
Import BITVECTOR_LIST.

From vera Require SMTLib.

Import SigTNotations.

Module TaggedVariable.
  Inductive Tag :=
  | VerilogLeft
  | VerilogRight
  .

  #[global] Instance dec_eq_tag (a b : Tag) : DecProp (a = b) :=
    mk_dec_eq.

  Definition t := (Tag * Verilog.variable)%type.

  Definition eq (l r : t) := l = r.

  Definition eq_equiv : Equivalence eq := eq_equivalence.

  Definition eq_dec (x y : t) : { eq x y } + { ~ eq x y } :=
    dec (x = y).
End TaggedVariable.

Module VerilogSMTBijection.
  Include PartialBijection(TaggedVariable)(NatAsUDT).

  Definition only_tag t m := forall tag smtName,
      option_map fst (bij_inverse m smtName) = Some tag ->
      tag = t.

  Lemma only_tag_empty t : only_tag t empty.
  Proof. cbv. discriminate. Qed.

  Lemma only_tag_insert tag name b m :
    only_tag tag m ->
    forall H1 H2,
      only_tag tag (insert (tag, name) b m H1 H2).
  Proof.
    unfold insert, only_tag.
    intros.
    unfold option_map in *.
    repeat (autodestruct_eqn E; cbn in * ); try reflexivity.
    eapply H. now erewrite E.
  Qed.

  Lemma combine_different_tag_left (m1 m2 : t) (t1 t2 : TaggedVariable.Tag) prf1 prf2:
    (t1 <> t2) ->
    only_tag t1 m1 ->
    only_tag t2 m2 ->
    forall n, combine m1 m2 prf1 prf2 (t1, n) = m1 (t1, n).
  Proof.
    intros.
    unfold combine. simpl.
    destruct (m1 (t1, n)) eqn:E1; try reflexivity.
    destruct (m2 (t1, n)) eqn:E2; try reflexivity.
    exfalso.
    apply bij_wf in E2.
    erewrite (H1 t1) in H. contradiction.
    now erewrite E2.
  Qed.

  Lemma combine_different_tag_right (m1 m2 : VerilogSMTBijection.t) (t1 t2 : TaggedVariable.Tag) prf1 prf2:
    (t1 <> t2) ->
    only_tag t1 m1 ->
    only_tag t2 m2 ->
    forall n, VerilogSMTBijection.combine m1 m2 prf1 prf2 (t2, n) = m2 (t2, n).
  Proof.
    intros.
    unfold VerilogSMTBijection.combine. simpl.
    destruct (m1 (t2, n)) eqn:E1; try reflexivity.
    destruct (m2 (t2, n)) eqn:E2; try reflexivity.
    - exfalso.
      apply VerilogSMTBijection.bij_wf in E1.
      erewrite (H0 t2) in H. contradiction.
      now erewrite E1.
    - exfalso.
      apply VerilogSMTBijection.bij_wf in E1.
      erewrite (H0 t2) in H. contradiction.
      now erewrite E1.
  Qed.
End VerilogSMTBijection.

Module SMT.
  Import VerilogSMTBijection (bij_inverse, bij_apply, bij_wf).
  Import (coercions) VerilogSMTBijection.

  Definition match_map_vars (tag : TaggedVariable.Tag) (map : VerilogSMTBijection.t) vars :=
    forall var, (exists smtName, map (tag, var) = Some smtName) <-> (In var vars).

  Record smt_with_namemap :=
    MkSMTWithNameMap
      { query : SMTQueries.query;
        nameMap : VerilogSMTBijection.t;
      }.

  Definition max_declaration (q : SMTQueries.query) : nat :=
    List.list_max (SMTQueries.domain q).

  Lemma max_declaration_domain q name :
    In name (SMTQueries.domain q) ->
    name <= max_declaration q.
  Proof.
    unfold max_declaration, SMTQueries.domain.
    revert name. rewrite <- Forall_forall.
    apply list_max_le.
    trivial.
  Qed.

  Equations default (s : SMTLib.sort) : SMTLib.interp_sort s :=
    default (SMTLib.Sort_Bool) := false;
    default (SMTLib.Sort_BitVec n) := BV.zeros n.

  Import EqNotations.

  Definition execution_of_valuation (tag : TaggedVariable.Tag) (m : VerilogSMTBijection.t) (ρ : SMTLib.valuation) : execution :=
    fun var =>
      match m (tag, var) with
      | Some smtName => XBV.from_bv (ρ (SMTLib.Sort_BitVec (Verilog.varType var)) smtName)
      | None => XBV.exes _
      end
  .

  Lemma execution_of_valuation_defined_value tag (m : VerilogSMTBijection.t) ρ:
    RegisterState.defined_value_for
      (fun var => exists smtName, m (tag, var) = Some smtName)
      (SMT.execution_of_valuation tag m ρ).
  Proof.
    unfold SMT.execution_of_valuation.
    intros var [smtName Hvar].
    rewrite Hvar.
    eauto.
  Qed.

  Definition valuation_of_executions (m : VerilogSMTBijection.t) (e1 e2 : execution) : SMTLib.valuation :=
    fun s smtName =>
      match s as s' return SMTLib.interp_sort s' with
      | SMTLib.Sort_Bool => default _
      | SMTLib.Sort_BitVec w => 
        match bij_inverse m smtName with
	| None => default _
	| Some (tag, verilogVar) =>
	  match dec (Verilog.varType verilogVar = w) with
	  | right _ => default _
	  | left E =>
            let e :=
              match tag with
              | TaggedVariable.VerilogLeft => e1
              | TaggedVariable.VerilogRight => e2
              end
            in
              match XBV.to_bv (e verilogVar) with
              (* TODO: Fix handling of Xs *)
              | None => default _
              | Some val => rew E in val
              end
	  end
	end
      end.

  Lemma execution_of_valuation_left_match_on (m : VerilogSMTBijection.t) e1 e2 l :
    RegisterState.defined_value_for (fun var => In var l) e1 ->
    SMT.match_map_vars TaggedVariable.VerilogLeft m l ->
    SMT.execution_of_valuation TaggedVariable.VerilogLeft m
      (SMT.valuation_of_executions m e1 e2) =( l )= e1.
  Proof.
    unfold SMT.execution_of_valuation, SMT.valuation_of_executions.
    (* intros Hdefined Hexists var Hvar_in. *)
    intros Hdefined Hmatch var Hvar_in.
    pose proof Hvar_in as H.
    apply Hmatch in H. destruct H as [smtName HsmtName].
    rewrite HsmtName.
    rewrite VerilogSMTBijection.bij_wf in HsmtName.
    rewrite HsmtName.
    apply Hdefined in Hvar_in. destruct Hvar_in as [bv Hbv].
    rewrite Hbv, XBV.xbv_bv_inverse.
    autodestruct; [|contradiction].
    rewrite <- eq_rect_eq.
    reflexivity.
  Qed.

  Lemma execution_of_valuation_right_match_on (m : VerilogSMTBijection.t) e1 e2 l :
    RegisterState.defined_value_for (fun var => In var l) e2 ->
    SMT.match_map_vars TaggedVariable.VerilogRight m l ->
    SMT.execution_of_valuation TaggedVariable.VerilogRight m
      (SMT.valuation_of_executions m e1 e2) =( l )= e2.
  Proof.
    unfold SMT.execution_of_valuation, SMT.valuation_of_executions.
    (* intros Hdefined Hexists var Hvar_in. *)
    intros Hdefined Hmatch var Hvar_in.
    pose proof Hvar_in as H.
    apply Hmatch in H. destruct H as [smtName HsmtName].
    rewrite HsmtName.
    rewrite VerilogSMTBijection.bij_wf in HsmtName.
    rewrite HsmtName.
    apply Hdefined in Hvar_in. destruct Hvar_in as [bv Hbv].
    rewrite Hbv, XBV.xbv_bv_inverse.
    autodestruct; [|contradiction].
    rewrite <- eq_rect_eq.
    reflexivity.
  Qed.
End SMT.
