From Coq Require Import ZArith.
From Coq Require Import BinNums.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.ProofIrrelevance.
Import ListNotations.

From Equations Require Import Equations.

From vera Require Import Common.
From vera Require Import Bitvector.
From vera Require VerilogSemantics.
From vera Require Import Verilog.
From vera Require Import Tactics.
Import VerilogSemantics.CombinationalOnly.
Import VerilogSMTBijection (bij_inverse, bij_apply, bij_wf).
Import (coercions) VerilogSMTBijection.

From SMTCoq Require Import bva.BVList.
Import BITVECTOR_LIST.

From SMTCoqApi Require SMTLib.
From SMTCoqApi Require SMTLibFacts.

Module SMT.
  Definition match_map_verilog (tag : TaggedName.Tag) (map : VerilogSMTBijection.t) verilog :=
    forall verilogName,
      (exists smtName, map (tag, verilogName) = Some smtName)
      <-> (In verilogName (variable_names (Verilog.modVariables verilog))).

  Record smt_with_namemap :=
    MkSMTWithNameMap
      { query : SMTLib.query;
        widths : list (nat * N);
        nameMap : VerilogSMTBijection.t;
      }.

  Remark match_map_verilog_width tag map verilog smtName verilogName :
    match_map_verilog tag map verilog ->
    map (tag, verilogName) = Some smtName ->
    exists width, In (verilogName, width) (variable_widths (Verilog.modVariables verilog)).
  Proof.
    intros H1 H2.
    apply variable_names_widths.
    eapply H1.
    eauto.
  Qed.

  Definition max_var (q : SMTLib.query) : nat :=
    List.list_max (SMTLibFacts.domain q).

  Program Definition valuation_of_execution (m : VerilogSMTBijection.t) (e : execution) : SMTLib.valuation :=
    fun n =>
    match bij_inverse m n with
    | None => None
    | Some (_, vname) =>
        match e vname with
        | None => None
        | Some xbv =>
            match XBV.to_bv xbv with
            (* TODO: Fix handling of Xs *)
            | None => None
            | Some val => Some (SMTLib.Value_BitVec (N.of_nat (length val)) {| bv := val |})
            end
        end
    end.

  Definition execution_of_valuation (tag : TaggedName.Tag) (m : VerilogSMTBijection.t) (v : SMTLib.valuation) : execution :=
      fun vname =>
        match m (tag, vname) with
        | Some smtName =>
            match v smtName with
            | Some (SMTLib.Value_BitVec _ bv) => Some (XBV.from_bv bv)
            | _ => None
            end
        | None => None
        end
    .

  Lemma execution_of_valuation_some tag (m : VerilogSMTBijection.t) ρ smtName vname sz bv :
    m (tag, vname) = Some smtName ->
    ρ smtName = Some (SMTLib.Value_BitVec sz bv) ->
    execution_of_valuation tag m ρ vname = Some (XBV.from_bv bv).
  Proof.
    unfold execution_of_valuation.
    intros H1 H2.
    now (rewrite H1; rewrite H2).
  Qed.

  Program Definition valuation_of_executions (m : VerilogSMTBijection.t) (e1 e2 : execution) : SMTLib.valuation :=
    fun n =>
    match bij_inverse m n with
    | None => None
    | Some (t, vname) =>
        let e :=
          match t with
          | TaggedName.VerilogLeft => e1
          | TaggedName.VerilogRight => e2
          end
        in
        match e vname with
        | None => None
        | Some xbv =>
            match XBV.to_bv xbv with
            (* TODO: Fix handling of Xs *)
            | None => None
            | Some val => Some (SMTLib.Value_BitVec (N.of_nat (length val)) {| bv := val |})
            end
        end
    end.

  Lemma execution_left_of_valuation_of_executions m v e1 e2 :
    (* TODO: Remove assumption *)
    (forall n xbv, e1 n = Some xbv -> ~ XBV.has_x xbv) ->
    (forall n xbv, e2 n = Some xbv -> ~ XBV.has_x xbv) ->
    match_map_verilog TaggedName.VerilogLeft m v ->
    complete_execution v e1 ->
    execution_of_valuation TaggedName.VerilogLeft m (valuation_of_executions m e1 e2) = e1.
  Proof.
    intros * Hno_exes1 Hno_exes2 Hmatch Hcomplete.
    unfold valuation_of_executions.
    unfold execution_of_valuation.
    apply functional_extensionality.
    intros name.
    autodestruct_eqn E; simpl in *; try subst.
    - replace s with name in * by
        (apply bij_wf in E; congruence).
      rewrite E3. f_equal.
      apply XBV.bv_xbv_inverse. assumption.
    - apply bij_wf in E.
      congruence.
    - replace s with name in * by
          (apply bij_wf in E; congruence).
      apply Hno_exes1 in E3.
      rewrite <- XBV.has_x_to_bv in E4.
      contradiction.
    - replace s with name in * by
          (apply bij_wf in E; congruence).
      apply Hno_exes2 in E3.
      rewrite <- XBV.has_x_to_bv in E4.
      contradiction.
    - replace s with name in * by
         (apply bij_wf in E; congruence).
      auto.
    - apply bij_wf in E; congruence.
    - apply bij_wf in E; congruence.
    - destruct (e1 name) as [xbv |] eqn:E1; try reflexivity.
      enough (exists xbv', m (TaggedName.VerilogLeft, name) = Some xbv')
        as [? ?] by congruence.
      destruct (Hmatch name) as [_ H].
      edestruct H as [smtName HsmtName]. {
        unfold complete_execution in Hcomplete.
        apply Hcomplete. exists xbv. auto.
      }
      eauto.
  Qed.

  Lemma execution_right_of_valuation_of_executions m v e1 e2 :
    (* TODO: Remove assumption *)
    (forall n xbv, e1 n = Some xbv -> ~ XBV.has_x xbv) ->
    (forall n xbv, e2 n = Some xbv -> ~ XBV.has_x xbv) ->
    match_map_verilog TaggedName.VerilogRight m v ->
    complete_execution v e2 ->
    execution_of_valuation TaggedName.VerilogRight m (valuation_of_executions m e1 e2) = e2.
  Proof.
    intros * Hno_exes1 Hno_exes2 Hmatch Hcomplete.
    unfold valuation_of_executions.
    unfold execution_of_valuation.
    apply functional_extensionality.
    intros name.
    autodestruct_eqn E; simpl in *; try subst.
    - apply bij_wf in E.
      congruence.
    - replace s with name in * by
        (apply bij_wf in E; congruence).
      rewrite E3. f_equal.
      apply XBV.bv_xbv_inverse. assumption.
    - replace s with name in * by
          (apply bij_wf in E; congruence).
      apply Hno_exes1 in E3.
      rewrite <- XBV.has_x_to_bv in E4.
      contradiction.
    - replace s with name in * by
          (apply bij_wf in E; congruence).
      apply Hno_exes2 in E3.
      rewrite <- XBV.has_x_to_bv in E4.
      contradiction.
    - apply bij_wf in E; congruence.
    - replace s with name in * by
         (apply bij_wf in E; congruence).
      auto.
    - apply bij_wf in E; congruence.
    - destruct (e2 name) as [xbv |] eqn:E1; try reflexivity.
      enough (exists xbv', m (TaggedName.VerilogRight, name) = Some xbv')
        as [? ?] by congruence.
      destruct (Hmatch name) as [_ H].
      edestruct H as [smtName HsmtName]. {
        unfold complete_execution in Hcomplete.
        apply Hcomplete. exists xbv. auto.
      }
      eauto.
  Qed.

  Lemma valuation_of_executions_some_left nameVerilog nameSMT xbv bv (m : VerilogSMTBijection.t) e1 e2 :
    e1 nameVerilog = Some xbv ->
    XBV.to_bv xbv = Some bv ->
    m (TaggedName.VerilogLeft, nameVerilog) = Some nameSMT ->
    (valuation_of_executions m e1 e2) nameSMT =
      Some (SMTLib.Value_BitVec (BV.size bv) (of_bits bv)).
  Proof.
    intros Hexec Hexes Hname.
    unfold valuation_of_executions; simpl.

    pose proof (bij_wf m) as Hinverse.
    specialize (Hinverse (TaggedName.VerilogLeft, nameVerilog) nameSMT).
    apply Hinverse in Hname. clear Hinverse.
    rewrite Hname.

    rewrite Hexec.
    rewrite Hexes.
    repeat f_equal.

    unfold of_bits.

    f_equal.
    apply proof_irrelevance.
  Qed.

  Lemma valuation_of_executions_some_right nameVerilog nameSMT xbv bv (m : VerilogSMTBijection.t) e1 e2 :
    e2 nameVerilog = Some xbv ->
    XBV.to_bv xbv = Some bv ->
    m (TaggedName.VerilogRight, nameVerilog) = Some nameSMT ->
    (valuation_of_executions m e1 e2) nameSMT =
      Some (SMTLib.Value_BitVec (BV.size bv) (of_bits bv)).
  Proof.
    intros Hexec Hexes Hname.
    unfold valuation_of_executions; simpl.

    pose proof (bij_wf m) as Hinverse.
    specialize (Hinverse (TaggedName.VerilogRight, nameVerilog) nameSMT).
    apply Hinverse in Hname. clear Hinverse.
    rewrite Hname.

    rewrite Hexec.
    rewrite Hexes.
    repeat f_equal.

    unfold of_bits.

    f_equal.
    apply proof_irrelevance.
  Qed.

  Section inverse.
    Variable m : VerilogSMTBijection.t.
    Variable v : Verilog.vmodule.
    Variable e : execution.
    Variable tag : TaggedName.Tag.
    Context (Hcomplete : complete_execution v e).
    Context (Hmatch : match_map_verilog tag m v).

    Lemma valuation_of_execution_some nameVerilog nameSMT xbv bv :
      e nameVerilog = Some xbv ->
      XBV.to_bv xbv = Some bv ->
      m (tag, nameVerilog) = Some nameSMT ->
      (valuation_of_execution m e) nameSMT =
        Some (SMTLib.Value_BitVec (BV.size bv) (of_bits bv)).
    Proof.
      intros Hexec Hexes Hname.
      unfold valuation_of_execution; simpl.

      pose proof (bij_wf m) as Hinverse.
      specialize (Hinverse (tag, nameVerilog) nameSMT).
      apply Hinverse in Hname.
      rewrite Hname.

      rewrite Hexec.
      rewrite Hexes.
      repeat f_equal.

      unfold of_bits.

      f_equal.
      apply proof_irrelevance.
    Qed.

    Lemma execution_of_valuation_of_execution :
      (* TODO: Remove assumption *)
      (forall n xbv, e n = Some xbv -> ~ XBV.has_x xbv) -> 
      execution_of_valuation tag m (valuation_of_execution m e) = e.
    Proof.
      intros Hno_exes.
      apply functional_extensionality. intros verilogName.
      unfold execution_of_valuation.
      destruct (m (tag, verilogName)) as [name | ] eqn:Hname; try discriminate.
      - unfold complete_execution in *. 
        unfold match_map_verilog in Hmatch.
        specialize (Hcomplete verilogName). simpl in *.
        destruct Hcomplete as [Hcomplete' _]; clear Hcomplete.
        edestruct Hcomplete' as [xbv Hxbv_val]. { firstorder. }
        clear Hcomplete'.

        unfold valuation_of_execution.

        pose proof (bij_wf m) as Hinverse.
        specialize (Hinverse (tag, verilogName) name).
        apply Hinverse in Hname.
        rewrite Hname.

        rewrite Hxbv_val.

        specialize (Hno_exes verilogName xbv ltac:(assumption)).
        apply XBV.not_has_x_to_bv in Hno_exes.
        destruct Hno_exes as [bv Hno_exes].
        rewrite Hno_exes.
        now erewrite XBV.bv_xbv_inverse.
      - destruct (e verilogName) as [xbv |] eqn:E; try reflexivity.
        enough (exists xbv', m (tag, verilogName) = Some xbv')
          as [? ?] by congruence.
        destruct (Hmatch verilogName) as [_ H].
        edestruct H as [smtName HsmtName]. {
          unfold complete_execution in Hcomplete.
          apply Hcomplete. exists xbv. auto.
        }
        eauto.
    Qed.
  End inverse.
End SMT.
