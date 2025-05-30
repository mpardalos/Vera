From vera Require Import Common.
Import (coercions) VerilogSMTBijection.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import VerilogToSMT.
From vera Require Import SMT.
From vera Require Import VerilogSemantics.
From vera Require Import Verilog.
Import CombinationalOnly.
From vera Require Import Bitvector.

From Coq Require List.
From Coq Require String.
From Coq Require Import Logic.ProofIrrelevance.
From Coq Require Import BinNat.

From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.MonadState.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Functor.

From Equations Require Import Equations.

Import List.ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.

Lemma assign_vars_vars start vars :
  List.map fst (assign_vars start vars) = vars.
Proof.
  revert start.
  induction vars; intros;
    simp assign_vars in *; cbn in *.
  - reflexivity.
  - rewrite IHvars. reflexivity.
Qed.

Lemma assign_vars_smtname_start start vars :
  List.Forall (fun n => n >= start) (List.map snd (assign_vars start vars)).
Proof.
  revert start.
  induction vars;
    intros; simp assign_vars in *; cbn in *;
    constructor.
  - lia.
  - specialize (IHvars (S start)).
    revert IHvars.
    eapply List.Forall_impl.
    lia.
Qed.

Lemma assign_vars_smtname_nodup start vars :
  List.NoDup (List.map snd (assign_vars start vars)).
Proof.
  revert start.
  induction vars; intros; simp assign_vars in *; cbn in *;
    constructor.
  - intro contra.
    pose proof (assign_vars_smtname_start (S start) vars).
    eapply List.Forall_forall in H; try eassumption.
    lia.
  - eapply IHvars.
Qed.

Lemma mk_bijection_smt_map_match tag start v m :
  mk_bijection tag (assign_vars start (Verilog.modVariables v)) = inr m ->
  SMT.match_map_verilog tag m v.
Proof.
  Opaque VerilogSMTBijection.lookup_left.
  unfold SMT.match_map_verilog.
  replace (variable_names (Verilog.modVariables v)) with (variable_names (List.map fst (assign_vars start (Verilog.modVariables v))))
    by now rewrite assign_vars_vars.
  remember (assign_vars start (Verilog.modVariables v)) as assignment.
  epose proof (assign_vars_smtname_nodup _ _) as Hnodup;
    rewrite <- Heqassignment in Hnodup.
  clear v start Heqassignment.
  generalize dependent Hnodup.
  generalize dependent m.
  induction assignment; intros * ? Hbijection.
  - simp mk_bijection in *. inv Hbijection.
    split; intros H; cbn in *; solve_by_inverts 2%nat.
  - unfold variable_names.
    destruct a as [var smtName].
    simp mk_bijection in Hbijection; inv Hbijection; autodestruct.
    split; intros H.
    + destruct H as [smtName' H].
      cbn. cbn in H.
      autodestruct; cbn in *; subst.
      * left.
        congruence.
      * right.
        eapply IHassignment; eauto; now some_inv.
    + cbn. autodestruct.
      * eauto.
      * eapply IHassignment; eauto; now some_inv.
Qed.

Lemma verilog_to_smt_map_match tag start v smt :
  verilog_to_smt tag start v = inr smt ->
  SMT.match_map_verilog tag (SMT.nameMap smt) v.
Proof.
  intros.
  funelim (verilog_to_smt tag start v);
    simp verilog_to_smt in *;
    try rewrite Heq in *;
    simpl in *;
    try discriminate.
  autodestruct_eqn E. cbn.
  eauto using mk_bijection_smt_map_match.
Qed.

Lemma mk_bijection_only_tag tag vars m :
  mk_bijection tag vars = inr m ->
  VerilogSMTBijection.only_tag tag m.
Proof.
  revert m.
  funelim (mk_bijection tag vars); intros.
  - inv H. apply VerilogSMTBijection.only_tag_empty.
  - simp mk_bijection in H0; inv H0; autodestruct.
    eauto using VerilogSMTBijection.only_tag_insert.
Qed.

Lemma verilog_to_smt_only_tag tag start v s :
  verilog_to_smt tag start v = inr s ->
  VerilogSMTBijection.only_tag tag (SMT.nameMap s).
Proof.
  intros.
  funelim (verilog_to_smt tag start v);
    simp verilog_to_smt in *;
    try rewrite Heq in *;
    simpl in *;
    try discriminate.
  autodestruct_eqn E. cbn.
  eauto using mk_bijection_only_tag.
Qed.

Inductive verilog_smt_match_value : XBV.t -> SMTLib.value -> Prop :=
| verilog_smt_match_value_intro w xbv bv :
  xbv = XBV.from_sized_bv bv ->
  verilog_smt_match_value xbv (SMTLib.Value_BitVec w bv).

Inductive verilog_smt_match_on_names (st : VerilogState) (ρ : SMTLib.valuation) verilogName smtName :=
| verilog_smt_match_on_names_intro xbv val
    (Hsmtval : ρ smtName = Some val)
    (Hverilogval : regState st verilogName = Some xbv)
    (Hmatchvals : verilog_smt_match_value xbv val).

Definition verilog_smt_match_states
  (tag : TaggedName.Tag)
  (m : VerilogSMTBijection.t)
  (st : VerilogState)
  (ρ : SMTLib.valuation) :=
  forall verilogName smtName,
    m (tag, verilogName) = Some smtName ->
    verilog_smt_match_on_names st ρ verilogName smtName.

Lemma eval_expr_width_correct st expr xbv :
  eval_expr st expr = Some xbv ->
  XBV.size xbv = Verilog.expr_type expr.
Admitted.

Lemma to_bv_from_sized_bv_inverse w (bv : BV.bitvector w) bv' :
  XBV.to_bv (XBV.from_sized_bv bv) = Some bv' ->
  BV.bits bv = bv'.
Proof.
  destruct bv. unfold XBV.from_sized_bv.
  rewrite XBV.xbv_bv_inverse.
  intros H. inv H.
  reflexivity.
Qed.

Lemma bitwise_binop_no_exes (f_bit : XBV.bit -> XBV.bit -> XBV.bit) (f_bool : bool -> bool -> bool) :
  forall l_xbv l_bv r_xbv r_bv,
    XBV.to_bv l_xbv = Some l_bv ->
    XBV.to_bv r_xbv = Some r_bv ->
    (forall (lb rb : bool), (if f_bool lb rb then XBV.I else XBV.O) = f_bit (if lb then XBV.I else XBV.O) (if rb then XBV.I else XBV.O)) ->
    bitwise_binop f_bit l_xbv r_xbv = XBV.from_bv (RawBV.map2 f_bool l_bv r_bv).
Proof.
  intros * Hl Hr Hf.
  unfold RawBV.bv_and.
  pose proof (XBV.bv_xbv_inverse _ _ Hl) as Hl_inverse. subst l_xbv.
  pose proof (XBV.bv_xbv_inverse _ _ Hr) as Hr_inverse. subst r_xbv.
  unfold bitwise_binop.
  clear Hl. clear Hr.
  generalize dependent r_bv.
  induction l_bv; try now simp map2.
  intros r_bv.
  destruct r_bv; try now simp map2.
  specialize (IHl_bv r_bv).
  simpl; simp map2.
  rewrite <- Hf.
  f_equal; eauto.
Qed.

Import EqNotations.
Require Import Program.

Lemma to_sized_bv_to_bv xbv bv :
  XBV.to_sized_bv xbv = Some bv -> XBV.to_bv xbv = Some (BV.bits bv).
Proof.
  (* Dependent types aaaaaaa *)
Admitted.

Lemma bitwise_and_no_exes :
  forall w l_xbv r_xbv (l_bv r_bv : BV.bitvector w)
    (Hsizel : XBV.size l_xbv = w)
    (Hsizer : XBV.size r_xbv = w),
    XBV.to_sized_bv l_xbv = Some (rew <- Hsizel in l_bv) ->
    XBV.to_sized_bv r_xbv = Some (rew <- Hsizer in r_bv) ->
    bitwise_binop and_bit l_xbv r_xbv = XBV.from_sized_bv (BV.bv_and l_bv r_bv).
Proof.
  intros * Hl Hr.
  unfold BV.bv_and, XBV.from_sized_bv in *.
  simpl.
  unfold RawBV.bv_and.
  do 2 rewrite BVList.BITVECTOR_LIST.wf.
  rewrite N.eqb_refl.
  destruct Hsizel, Hsizer.
  unfold "rew <- [ _ ] _ in _" in *.
  rewrite <- eq_rect_eq in *.

  apply bitwise_binop_no_exes; try eassumption.
  - apply to_sized_bv_to_bv. assumption.
  - apply to_sized_bv_to_bv. assumption.
  - intros. autodestruct_eqn E; now simp and_bit.
Qed.

Lemma bitwise_or_no_exes :
  forall l_xbv l_bv r_xbv r_bv,
    (XBV.size l_xbv = XBV.size r_xbv) ->
    XBV.to_bv l_xbv = Some l_bv ->
    XBV.to_bv r_xbv = Some r_bv ->
    bitwise_binop or_bit l_xbv r_xbv = XBV.from_bv (RawBV.bv_or l_bv r_bv).
Proof.
  intros * Hsize Hl Hr.
  unfold RawBV.bv_or.
  erewrite XBV.to_bv_size by eassumption.
  erewrite XBV.to_bv_size by eassumption.
  rewrite Hsize.
  rewrite N.eqb_refl.

  apply bitwise_binop_no_exes; try eassumption.
  intros. autodestruct_eqn E; now simp and_bit.
Qed.

Ltac bv_binop_tac :=
  simp eval_binop in *;
  match goal with
    [ |- context[bv_binop ?op ?l ?r] ] =>
      funelim (bv_binop op l r);
      match goal with
        [ Heqcall': _ = bv_binop op l r |- _ ] =>
          rewrite <- Heqcall' in *;
          clear Heqcall';
          repeat apply_somewhere to_bv_from_sized_bv_inverse;
          subst
      end ;
      [ idtac
      | now (unfold XBV.from_sized_bv in *; rewrite XBV.xbv_bv_inverse in * )
      | now (unfold XBV.from_sized_bv in *; rewrite XBV.xbv_bv_inverse in * )
      ]
  end.

Lemma expr_to_smt_correct vars expr :
  forall t tag m st ρ xbv bv,
    expr_to_smt vars expr = inr t ->
    verilog_smt_match_states tag m st ρ ->
    eval_expr st expr = Some xbv ->
    SMTLib.interp_term ρ t = Some bv ->
    verilog_smt_match_value xbv bv.
Proof.
  Ltac expr_begin_tac :=
    match goal with
    | [ Heval_expr: eval_expr _ _ = Some _ , Hinterp_term : SMTLib.interp_term _ _ = Some _ |- _ ] =>
        cbn in Hinterp_term;
        simp eval_expr in Heval_expr; inv Heval_expr;
        let E := fresh "E" in
        autodestruct_eqn E
    end.

  funelim (expr_to_smt vars expr); intros * Hexpr_to_smt Hmatch_states Heval_expr Hinterp_term;
    inv Hexpr_to_smt; autodestruct_eqn E;
    try match type of Heval_expr with
      | context[Verilog.BinaryOp] => expr_begin_tac
      | context[Verilog.UnaryOp] => expr_begin_tac
      end.
  - (* BinaryPlus *)
    insterU H. inv H. apply_somewhere inj_pair2. subst.
    insterU H0. inv H0. apply_somewhere inj_pair2. subst.
    bv_binop_tac. now constructor.
  - (* BinaryMinus *)
    apply_somewhere inj_pair2. subst.
    insterU H. inv H. apply_somewhere inj_pair2. subst.
    insterU H0. inv H0. apply_somewhere inj_pair2. subst.
    bv_binop_tac. now constructor.
  - (* BinaryStar *)
    insterU H. inv H. apply_somewhere inj_pair2. subst.
    insterU H0. inv H0. apply_somewhere inj_pair2. subst.
    bv_binop_tac. now constructor.
  - (* BinaryBitwiseAnd *)
    insterU H. inv H. apply_somewhere inj_pair2. subst.
    insterU H0. inv H0. apply_somewhere inj_pair2. subst.
    simp eval_binop.
    constructor.
    erewrite bitwise_and_no_exes.
    + admit.
    + admit.
    + admit.
  - admit. (* TODO BinaryBitwiseOr *)
  - admit. (* TODO BinaryShiftRight *)
  - admit. (* TODO BinaryShiftLeft *)
  - admit. (* TODO BinaryShiftLeftArithmetic *)
  - admit. (* TODO UnaryPlus *)
  - admit. (* TODO UnaryMinus *)
  - admit. (* TODO UnaryNegation *)
  - (* TODO: Conditional *)
    expr_begin_tac;
      try solve [eauto];
      try rewrite Bool.negb_true_iff in *; try rewrite Bool.negb_false_iff in *.
    + admit. (* Contradiction 0 <> 0 *)
    + admit. (* Condition is X *)
    + admit. (* Contradiction 0 <> 0 *)
    + admit. (* Condition is X *)
  - (* TODO: BitSelect *)
    expr_begin_tac.
    admit.
  - (* TODO: Concatenation *)
    (* The induction principe does not handle the list correctly, we probably
       need to change the AST a bit *)
    expr_begin_tac.
    admit.
  - (* Verilog.IntegerLiteral *)
    expr_begin_tac.
    now constructor.
  - (* Verilog.NamedExpression *)
    funelim (term_for_name vars t n); rewrite <- Heqcall in *; try discriminate; clear Heqcall.
    destruct Hmatch_states with (verilogName := name) (smtName := n__smt).
    { admit. (* TODO: names in the expression are in the bijection *) }
    inv H0. (* FIXME: don't reference names *)
    expr_begin_tac; congruence.
  - (* TODO: Resize *)
    expr_begin_tac.
    simp convert; unfold convert_clause_1.
    erewrite eval_expr_width_correct by eassumption.
    funelim (cast_from_to (Verilog.expr_type expr) to t0);
      rewrite <- Heqcall in *; clear Heqcall;
      rewrite Heq.
    + eauto.
    + cbn in Hinterp_term. autodestruct_eqn E.
      (* TODO: Truncation implementation matches *) admit.
    + cbn in Hinterp_term. autodestruct_eqn E.
      (* TODO: Extension implementation matches *) admit.
Admitted.

Theorem verilog_to_smt_correct tag start v smt :
  verilog_to_smt tag start v = inr smt ->
  SMTLibFacts.smt_reflect
    (SMT.query smt)
    (fun ρ => valid_execution v (SMT.execution_of_valuation tag (SMT.nameMap smt) ρ)).
Proof.
  funelim (verilog_to_smt tag start v);
    simp verilog_to_smt in *;
    try rewrite Heq in *;
    simpl in *;
    try discriminate.
  autodestruct_eqn E. cbn.
  intros H. inv H. cbn in *.
Admitted.
