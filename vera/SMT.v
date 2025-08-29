From Coq Require Import ZArith.
From Coq Require Import BinNums.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.ProofIrrelevance.
From Coq Require Import Structures.Equalities.
Import ListNotations.

From Equations Require Import Equations.

From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Bitvector.
From vera Require VerilogSemantics.
From vera Require Import Verilog.
From vera Require Import Tactics.
Import VerilogSemantics.CombinationalOnly.

From SMTCoq Require Import bva.BVList.
Import BITVECTOR_LIST.

From SMTCoqApi Require SMTLib.
From SMTCoqApi Require SMTLibFacts.

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

  Definition match_map_verilog (tag : TaggedVariable.Tag) (map : VerilogSMTBijection.t) verilog :=
    forall var, (exists smtName, map (tag, var) = Some smtName) <-> (In var (Verilog.modVariables verilog)).

  Record smt_with_namemap :=
    MkSMTWithNameMap
      { query : SMTLib.query;
        widths : list (nat * N);
        nameMap : VerilogSMTBijection.t;
      }.

  Definition max_var (q : SMTLib.query) : nat :=
    List.list_max (SMTLib.domain q).

  Program Definition valuation_of_execution (tag : TaggedVariable.Tag) (m : VerilogSMTBijection.t) (e : execution) : SMTLib.valuation :=
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

  Definition execution_of_valuation (tag : TaggedVariable.Tag) (m : VerilogSMTBijection.t) (v : SMTLib.valuation) : execution :=
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

  Definition valuation_of_executions (m : VerilogSMTBijection.t) (e1 e2 : execution) : SMTLib.valuation :=
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
    match_map_verilog TaggedVariable.VerilogLeft m v ->
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
    match_map_verilog TaggedVariable.VerilogRight m v ->
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
    Context (Hmatch : match_map_verilog tag m v).

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

    Lemma execution_of_valuation_of_execution :
      (* TODO: Remove assumption *)
      (forall n xbv, e n = Some xbv -> ~ XBV.has_x xbv) ->
      execution_of_valuation tag m (valuation_of_execution tag m e) = e.
    Proof.
      intros Hno_exes.
      apply functional_extensionality_dep. intros var.
      unfold execution_of_valuation.
      destruct (m (tag, var)) as [name | ] eqn:Hname; try discriminate.
      - unfold complete_execution in *. 
        unfold match_map_verilog in Hmatch.
        specialize (Hcomplete var). simpl in *.
        destruct Hcomplete as [Hcomplete' _]; clear Hcomplete.
        edestruct Hcomplete' as [[w xbv] Hxbv_val]. { firstorder. }
        clear Hcomplete'.

        unfold valuation_of_execution.

        pose proof (bij_wf m) as Hinverse.
        specialize (Hinverse (tag, var) name).
        apply Hinverse in Hname.
        rewrite Hname.

        rewrite Hxbv_val.

        insterU Hno_exes.
        apply XBV.not_has_x_to_bv in Hno_exes.
        destruct Hno_exes as [bv Hno_exes].
        rewrite Hno_exes.
        destruct (dec (tag = tag)); [|contradiction].
        autodestruct; [|contradiction].
        rewrite <- eq_rect_eq.
        now erewrite XBV.bv_xbv_inverse.
      - destruct (e var) as [xbv |] eqn:E; try reflexivity.
        enough (exists xbv', m (tag, var) = Some xbv')
          as [? ?] by congruence.
        destruct (Hmatch var) as [_ H].
        edestruct H as [smtName HsmtName]. {
          unfold complete_execution in Hcomplete.
          apply Hcomplete. exists xbv. auto.
        }
        eauto.
    Qed.
  End inverse.
End SMT.
