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
From vera Require VerilogSemantics.
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
    List.list_max (List.map fst (SMTQueries.declarations q)).

  Lemma max_declaration_declarations q name s :
    In (name, s) (SMTQueries.declarations q) ->
    name <= max_declaration q.
  Proof.
    unfold max_declaration, SMTQueries.domain.
    destruct q. simpl in *. rewrite List.Forall_forall in *.
    intros Hin_domain. clear wf0. clear assertions.
    revert name s Hin_domain.
    induction declarations; [crush|].
    intros.
    inv Hin_domain; simpl in *; [lia|].
    insterU IHdeclarations.
    lia.
  Qed.

  Lemma max_declaration_domain q name :
    In name (SMTQueries.domain q) ->
    name <= max_declaration q.
  Proof.
    intros Hin_domain.
    pose proof (SMTQueries.wf q) as wf.
    rewrite List.Forall_forall in wf.
    edestruct wf as [s Hin_decls]; [eassumption|].
    eapply max_declaration_declarations.
    eassumption.
  Qed.

  Program Definition valuation_of_execution (tag : TaggedVariable.Tag) (m : VerilogSMTBijection.t) (e : execution) : SMTQueries.valuation :=
    fun n =>
      match bij_inverse m n with
      | None => None
      | Some (t, vname) =>
          if dec (t = tag)
          then
            match e vname with
            | None => None
            | Some x =>
                match XBV.to_bv x with
                (* TODO: Fix handling of Xs *)
                | None => None
                | Some val => Some (SMTLib.Value_BitVec _ val)
                end
            end
          else None
      end.

  Import EqNotations.

  Definition execution_of_valuation (tag : TaggedVariable.Tag) (m : VerilogSMTBijection.t) (v : SMTQueries.valuation) : execution :=
    fun var =>
      match m (tag, var) with
      | Some smtName =>
          match v smtName with
          | Some (SMTLib.Value_BitVec w bv) =>
              match dec (w = Verilog.varType var) with
              | left e => Some (rew e in (XBV.from_bv bv))
              | _ => None
              end
          | _ => None
          end
      | None => None
      end
  .

  Lemma execution_of_valuation_no_exes tag m ρ n xbv :
    SMT.execution_of_valuation tag m ρ n = Some xbv ->
    ~ XBV.has_x xbv.
  Proof.
    unfold execution_of_valuation.
    intros.
    autodestruct.
    simpl.
    rewrite XBV.has_x_to_bv.
    rewrite XBV.xbv_bv_inverse.
    discriminate.
  Qed.

  Lemma execution_of_valuation_some tag (m : VerilogSMTBijection.t) ρ smtName var bv :
    m (tag, var) = Some smtName ->
    ρ smtName = Some (SMTLib.Value_BitVec (Verilog.varType var) bv) ->
    execution_of_valuation tag m ρ var = Some (XBV.from_bv bv).
  Proof.
    unfold execution_of_valuation.
    intros H1 H2.
    rewrite H1; rewrite H2.
    autodestruct; [|contradiction].
    now rewrite <- eq_rect_eq.
  Qed.

  Definition valuation_of_executions (m : VerilogSMTBijection.t) (e1 e2 : execution) : SMTQueries.valuation :=
    fun n =>
      match bij_inverse m n with
      | None => None
      | Some (tag, var) =>
          let e :=
            match tag with
            | TaggedVariable.VerilogLeft => e1
            | TaggedVariable.VerilogRight => e2
            end
          in
          match e var with
          | None => None
          | Some xbv =>
              match XBV.to_bv xbv with
              (* TODO: Fix handling of Xs *)
              | None => None
              | Some val => Some (SMTLib.Value_BitVec _ val)
              end
          end
      end.

  Lemma execution_left_of_valuation_of_executions m v e1 e2 :
    (* TODO: Remove assumption *)
    (forall n xbv, e1 n = Some xbv -> ~ XBV.has_x xbv) ->
    (forall n xbv, e2 n = Some xbv -> ~ XBV.has_x xbv) ->
    match_map_vars TaggedVariable.VerilogLeft m (Verilog.modVariables v) ->
    complete_execution v e1 ->
    execution_of_valuation TaggedVariable.VerilogLeft m (valuation_of_executions m e1 e2) = e1.
  Proof.
    intros * Hno_exes1 Hno_exes2 Hmatch Hcomplete.
    unfold valuation_of_executions.
    unfold execution_of_valuation.
    apply functional_extensionality_dep.
    intros [varName varType].
    autodestruct_eqn E;
      simpl in *; try subst; repeat apply_somewhere inj_pair2; try subst.
    - destruct v1 as [n1 t1]. simpl in *.
      replace n1 with varName in * by (apply bij_wf in E; crush).
      simpl in *.
      replace (e1 {| Verilog.varName := varName; Verilog.varType := t1 |}). repeat f_equal.
      apply XBV.bv_xbv_inverse. assumption.
    - destruct v1 as [n1 t1]. simpl in *.
      replace n1 with varName in * by (apply bij_wf in E; crush).
      rewrite bij_wf in *. congruence.
    - rewrite bij_wf in *. congruence.
    - rewrite bij_wf in *. congruence.
    - destruct v0 as [n1 t1]. simpl in *. replace n1 with varName in * by (apply bij_wf in E; crush).
      apply_somewhere (Hno_exes1 {| Verilog.varName := varName; Verilog.varType := t1 |}).
      now rewrite <- XBV.has_x_to_bv in *.
    - destruct v0 as [n1 t1]. simpl in *. replace n1 with varName in * by (apply bij_wf in E; crush).
      apply_somewhere (Hno_exes2 {| Verilog.varName := varName; Verilog.varType := t1 |}).
      now rewrite <- XBV.has_x_to_bv in *.
    - destruct v0 as [n1 t1]. simpl in *.
      replace n1 with varName in * by (apply bij_wf in E; crush).
      replace t1 with varType in * by (apply bij_wf in E; crush).
      crush.
    - destruct v0 as [n1 t1]. simpl in *.
      replace n1 with varName in * by (apply bij_wf in E; crush).
      replace t1 with varType in * by (apply bij_wf in E; crush).
      rewrite bij_wf in *; congruence.
    - rewrite bij_wf in *; congruence.
    - admit.
  Admitted.

  Lemma execution_right_of_valuation_of_executions m v e1 e2 :
    (* TODO: Remove assumption *)
    (forall n xbv, e1 n = Some xbv -> ~ XBV.has_x xbv) ->
    (forall n xbv, e2 n = Some xbv -> ~ XBV.has_x xbv) ->
    match_map_vars TaggedVariable.VerilogRight m (Verilog.modVariables v) ->
    complete_execution v e2 ->
    execution_of_valuation TaggedVariable.VerilogRight m (valuation_of_executions m e1 e2) = e2.
  Proof. Admitted.

  Lemma valuation_of_executions_some_left var nameSMT xbv bv (m : VerilogSMTBijection.t) e1 e2 :
    e1 var = Some xbv ->
    XBV.to_bv xbv = Some bv ->
    m (TaggedVariable.VerilogLeft, var) = Some nameSMT ->
    (valuation_of_executions m e1 e2) nameSMT =
      Some (SMTLib.Value_BitVec (Verilog.varType var) bv).
  Proof.
    intros Hexec Hexes Hname.
    unfold valuation_of_executions; simpl.

    pose proof (bij_wf m) as Hinverse.
    specialize (Hinverse (TaggedVariable.VerilogLeft, var) nameSMT).
    apply Hinverse in Hname. clear Hinverse.
    rewrite Hname.

    rewrite Hexec.
    rewrite Hexes.
    reflexivity.
  Qed.

  Lemma valuation_of_executions_some_right var nameSMT xbv bv (m : VerilogSMTBijection.t) e1 e2 :
    e2 var = Some xbv ->
    XBV.to_bv xbv = Some bv ->
    m (TaggedVariable.VerilogRight, var) = Some nameSMT ->
    (valuation_of_executions m e1 e2) nameSMT =
      Some (SMTLib.Value_BitVec (Verilog.varType var) bv).
  Proof.
    intros Hexec Hexes Hname.
    unfold valuation_of_executions; simpl.

    pose proof (bij_wf m) as Hinverse.
    specialize (Hinverse (TaggedVariable.VerilogRight, var) nameSMT).
    apply Hinverse in Hname. clear Hinverse.
    rewrite Hname.

    rewrite Hexec.
    rewrite Hexes.
    reflexivity.
  Qed.

  Section inverse.
    Variable m : VerilogSMTBijection.t.
    Variable v : Verilog.vmodule.
    Variable e : execution.
    Variable tag : TaggedVariable.Tag.
    Context (Hcomplete : complete_execution v e).
    Context (Hmatch : match_map_vars tag m (Verilog.modVariables v)).

    Lemma valuation_of_execution_some var nameSMT xbv bv :
      e var = Some (xbv) ->
      XBV.to_bv xbv = Some bv ->
      m (tag, var) = Some nameSMT ->
      (valuation_of_execution tag m e) nameSMT =
        Some (SMTLib.Value_BitVec (Verilog.varType var) bv).
    Proof.
      intros Hexec Hexes Hname.
      unfold valuation_of_execution; simpl.

      pose proof (bij_wf m) as Hinverse.
      specialize (Hinverse (tag, var) nameSMT).
      apply Hinverse in Hname.
      rewrite Hname.

      destruct (dec (tag = tag)); [|contradiction].

      rewrite Hexec.
      rewrite Hexes.
      reflexivity.
    Qed.
  End inverse.
End SMT.
