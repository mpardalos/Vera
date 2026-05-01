From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import VerilogToSMT.
From vera Require Import VerilogSMT.
From vera Require SMTQueries.
Import (coercions) VerilogSMTBijection.
From vera Require Import VerilogSemantics.
From vera Require Import Verilog.
Import CombinationalOnly.
From vera Require Import Bitvector.
Import RawXBV(bit(..)).
From vera Require Import VerilogToSMT.Match.

From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.MonadState.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Functor.

From Stdlib Require List.
From Stdlib Require Import String.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import NArith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Classes.Morphisms_Prop.
From Stdlib Require Import Setoid.
From Stdlib Require ZifyBool.
From Stdlib Require Import Program.Equality.

From Equations Require Import Equations.

Import List.ListNotations.
Import CommonNotations.
Import MonadLetNotation.
Import FunctorNotation.
Import SigTNotations.
Import EqNotations. 

Local Open Scope list.

Lemma var_to_smt_value var (m : VerilogSMTBijection.t) tag regs ρ t :
    var_to_smt tag m var = inr t ->
    verilog_smt_match_states_partial (fun v => v = var) tag m regs ρ ->
    regs var = Some (XBV.from_bv (SMTLib.interp_term ρ t)).
Proof.
  intros Hsmt Hmatch.
  funelim (var_to_smt tag m var); try rewrite <- Heqcall in *; clear Heqcall; monad_inv.
  simpl.
  unfold verilog_smt_match_states_partial in *.
  unfold verilog_smt_match_on_name in *.
  insterU Hmatch.
  crush.
Qed.

Lemma var_to_smt_valid tag m var t (ρ : SMTLib.valuation) :
  var_to_smt tag m var = inr t ->
  exists smtName, (m (tag, var) = Some smtName /\ ρ (SMTLib.Sort_BitVec (Verilog.varType var)) smtName = SMTLib.interp_term ρ t).
Proof.
  intros Htransf.
  funelim (var_to_smt tag m var); rewrite <- Heqcall in *; monad_inv.
  crush.
Qed.

Lemma arithmeticop_to_smt_value ρ op w (smt_lhs smt_rhs : SMTLib.term (SMTLib.Sort_BitVec w)) :
    eval_arithmeticop op (XBV.from_bv (SMTLib.interp_term ρ smt_lhs)) (XBV.from_bv (SMTLib.interp_term ρ smt_rhs))
      = XBV.from_bv (SMTLib.interp_term ρ (arithmeticop_to_smt op smt_lhs smt_rhs)).
Proof.
  destruct op.
  all: simp eval_arithmeticop arithmeticop_to_smt in *.
  all: cbn [SMTLib.interp_term].
  all: autorewrite with xbv bv_binop in *.
  all: reflexivity.
Qed.

Lemma bitwiseop_to_smt_value ρ op w (smt_lhs smt_rhs : SMTLib.term (SMTLib.Sort_BitVec w)) :
    eval_bitwiseop op (XBV.from_bv (SMTLib.interp_term ρ smt_lhs)) (XBV.from_bv (SMTLib.interp_term ρ smt_rhs))
      = XBV.from_bv (SMTLib.interp_term ρ (bitwiseop_to_smt op smt_lhs smt_rhs)).
Proof.
  destruct op.
  all: simp eval_bitwiseop bitwiseop_to_smt in *.
  all: cbn [SMTLib.interp_term].
  all: autorewrite with xbv bv_binop in *.
  all: reflexivity.
Qed.

Lemma shiftop_to_smt_value ρ op w (smt_lhs smt_rhs : SMTLib.term (SMTLib.Sort_BitVec w)) :
  eval_shiftop op (XBV.from_bv (SMTLib.interp_term ρ smt_lhs)) (XBV.from_bv (SMTLib.interp_term ρ smt_rhs))
    = XBV.from_bv (SMTLib.interp_term ρ (shiftop_to_smt op smt_lhs smt_rhs)).
Proof.
  destruct op.
  all: simp eval_shiftop shiftop_to_smt in *.
  all: cbn [SMTLib.interp_term].
  all: repeat (simpl; autorewrite with xbv bv_binop in *).
  all: eapply XBV.to_bv_injective; [|now eapply XBV.xbv_bv_inverse].
  1: rewrite BV.shr_swap_definition.
  2,3: rewrite BV.shl_swap_definition.
  all: now autorewrite with xbv bv_binop in *.
Qed.

Lemma unaryop_to_smt_value ρ op w (smt_expr : SMTLib.term (SMTLib.Sort_BitVec w)) :
    eval_unaryop op (XBV.from_bv (SMTLib.interp_term ρ smt_expr))
      = XBV.from_bv (SMTLib.interp_term ρ (unaryop_to_smt op smt_expr)).
Proof.
  destruct op.
  all: simp eval_unaryop unaryop_to_smt in *.
  all: cbn [SMTLib.interp_term].
  all: autorewrite with xbv in *.
  all: reflexivity.
Qed.

Lemma conditional_to_smt_value ρ w_cond w
      (smt_cond : SMTLib.term (SMTLib.Sort_BitVec w_cond))
      (smt_ifT smt_ifF : SMTLib.term (SMTLib.Sort_BitVec w)) :
    eval_conditional
      (XBV.from_bv (SMTLib.interp_term ρ smt_cond))
      (XBV.from_bv (SMTLib.interp_term ρ smt_ifT))
      (XBV.from_bv (SMTLib.interp_term ρ smt_ifF)) =
      XBV.from_bv (SMTLib.interp_term ρ (conditional_to_smt w_cond smt_cond smt_ifT smt_ifF)).
Proof.
  unfold eval_conditional in *.
  rewrite XBV.xbv_bv_inverse in *.
  simpl in *.
  unfold BV.is_zero.
  crush.
Qed.

Lemma cast_from_to_value ρ w_from w_to smt_from val_from :
    (w_to > 0)%N ->
    SMTLib.interp_term ρ smt_from = Some (SMTLib.Value_BitVec w_from val_from) ->
    SMTLib.interp_term ρ (cast_from_to w_from w_to smt_from) =
      Some (SMTLib.Value_BitVec w_to (convert_bv w_to val_from)).
Proof.
  intros Hnot_zero Hinterp_from.
  funelim (convert_bv w_to val_from); expect 3.
  all: funelim (cast_from_to from to smt_from); expect 9.
  all: autorewrite with bool_to_prop in *; try lia; expect 3.
  all: simpl; rewrite Hinterp_from.
  all: f_equal.
  all: apply value_bitvec_bits_equal.
  all: try destruct_rew.
  all: simpl.
  all: repeat f_equal; lia.
Qed.

Lemma to_N_convert_bv_extn from to (bv : BV.bitvector from) :
  (to >= from)%N ->
  BV.to_N (convert_bv to bv) = BV.to_N bv.
Proof.
  intros H.
  funelim (convert_bv to bv); try lia.
  - destruct_rew. apply BV.bv_zextn_to_N.
  - destruct_rew. reflexivity.
Qed.

Lemma bitOf_concat_low idx w1 w2 (extn : BV.bitvector w2) (bv : BV.bitvector w1) :
  (N.of_nat idx < w1)%N ->
  BV.bitOf idx (BV.bv_concat extn bv) = BV.bitOf idx bv.
Proof.
  destruct bv as [bv bv_wf].
  destruct extn as [extn extn_wf].
  unfold BV.bitOf, BV.bv_concat, RawBV.bitOf, RawBV.bv_concat, RawBV.size in *.
  simpl.
  intros.
  rewrite List.app_nth1 by lia.
  reflexivity.
Qed.

Lemma nth_rawbv_extract bv : forall idx w,
  idx < w ->
  List.nth idx (BVList.RAWBITVECTOR_LIST.extract bv 0 w) false =
    List.nth idx bv false.
Proof.
  induction bv.
  - crush.
  - intros.
    cbn [List.nth].
    destruct idx.
    + crush.
    + simpl.
      destruct w; [lia|].
      simpl.
      apply IHbv.
      lia.
Qed.

Lemma bitOf_extr_inbounds idx sz w (bv : BV.bitvector w) :
  (sz <= w)%N ->
  (N.of_nat idx < sz)%N ->
  BV.bitOf idx (BV.bv_extr 0 sz bv) = BV.bitOf idx bv.
Proof.
  intros.
  destruct bv as [bv bv_wf].
  unfold BV.bitOf, BV.bv_extr, RawBV.bitOf, RawBV.bv_extr, RawBV.size in *.
  simpl in *.
  autodestruct_eqn E; try crush.
  apply nth_rawbv_extract.
  lia.
Qed.

Lemma bitOf_convert_bv_extn idx from to (bv : BV.bitvector from) :
  (idx < from)%N ->
  (idx < to)%N ->
  BV.bitOf (N.to_nat idx) (convert_bv to bv) = BV.bitOf (N.to_nat idx) bv.
Proof.
  intros.
  funelim (convert_bv to bv).
  - destruct_rew. simpl.
    now rewrite bitOf_concat_low by lia.
  - apply bitOf_extr_inbounds; try crush.
  - destruct_rew. simpl. reflexivity.
Qed.

Lemma smt_select_bit_value ρ w_vec w_idx smt_vec smt_idx val_vec val_idx val :
    SMTLib.interp_term ρ smt_vec = Some (SMTLib.Value_BitVec w_vec val_vec) ->
    SMTLib.interp_term ρ smt_idx = Some (SMTLib.Value_BitVec w_idx val_idx) ->
    XBV.to_bv (select_bit (XBV.from_bv val_vec) (XBV.from_bv val_idx)) =
      Some val ->
    (BV.to_N val_idx < w_vec)%N ->
    SMTLib.interp_term ρ (smt_select_bit w_vec smt_vec w_idx smt_idx) =
      Some (SMTLib.Value_BitVec 1 val).
Proof.
  intros Hinterp_vec Hinterp_idx Heval Hbound.
  unfold select_bit, smt_select_bit in *.
  rewrite XBV.to_N_from_bv in *.
  simpl.
  erewrite ! cast_from_to_value; cycle 1;
    try eassumption; try lia; [idtac].
  destruct (N.eq_dec (N.max w_vec w_idx) (N.max w_vec w_idx)); [|crush].
  rewrite BV.bv_shr_as_select by lia.
  rewrite XBV.bit_of_as_bv in Heval by lia.
  do 2 f_equal.
  destruct_rew.
  rewrite to_N_convert_bv_extn by lia.
  rewrite bitOf_convert_bv_extn by lia.
  (* Ugly, but it's hard to extract a lemma - the widths don't match up *)
  apply XBV.to_bv_some_raw_iff in Heval. simpl in Heval.
  apply BV.of_bits_equal. simpl.
  unfold RawXBV.to_bv, RawBV.of_bits in *; simpl in *.
  rewrite RawXBV.bit_to_bool_inverse in Heval.
  inv Heval. reflexivity.
Qed.

Lemma convert_extend_to_N from to (xbv : XBV.xbv from) val :
  (to >= from)%N ->
  XBV.to_N xbv = Some val ->
  XBV.to_N (convert to xbv) = Some val.
Proof.
  intros.
  funelim (convert to xbv); [idtac|lia|idtac].
  - destruct_rew. simpl. apply XBV.extend_to_N. assumption.
  - destruct_rew. simpl. assumption.
Qed.

Lemma convert_extend_to_N_none from to (xbv : XBV.xbv from) :
  (to >= from)%N ->
  XBV.to_N xbv = None ->
  XBV.to_N (convert to xbv) = None.
Proof.
  intros.
  funelim (convert to xbv).
  - destruct_rew. simpl. apply XBV.extend_to_N_none2. assumption.
  - lia.
  - destruct_rew. simpl. assumption.
Qed.

Lemma convert_shr_convert n1 n2 (xbv : XBV.xbv n1) shamt :
  (n2 >= n1)%N ->
  convert n1 (XBV.shr (convert n2 xbv) shamt) = XBV.shr xbv shamt.
Proof.
  intros.
  funelim (convert n2 xbv); [idtac|lia|idtac].
  all: destruct_rew; simpl.
  - funelim (convert from (XBV.shr (XBV.concat (XBV.zeros (to - from)) value) shamt)); [lia|idtac|lia].
    apply XBV.extr_shr_extend.
  - funelim (convert from (XBV.shr value shamt)); [lia|lia|idtac].
    rewrite <- eq_rect_eq. reflexivity.
Qed.

Lemma convert_shl_convert n1 n2 (xbv : XBV.xbv n1) shamt :
  (n2 >= n1)%N ->
  convert n1 (XBV.shl (convert n2 xbv) shamt) = XBV.shl xbv shamt.
Proof.
  intros.
  funelim (convert n2 xbv); [idtac|lia|idtac].
  all: destruct_rew; simpl.
  - funelim (convert from (XBV.shl (XBV.concat (XBV.zeros (to - from)) value) shamt)); [lia|idtac|lia].
    apply XBV.extr_shl_extend.
  - funelim (convert from (XBV.shl value shamt)); [lia|lia|idtac].
    rewrite <- eq_rect_eq. reflexivity.
Qed.

Lemma convert_exes n1 n2 :
  (n2 <= n1)%N ->
  convert n2 (XBV.exes n1) = XBV.exes n2.
Proof.
  intros. 
  funelim (convert n2 (XBV.exes n1)).
  - lia.
  - apply XBV.extr_exes.
  - destruct_rew. reflexivity.
Qed.

Lemma eval_shiftop_remove_converts w1 w2 op (lhs : XBV.xbv w1) (rhs : XBV.xbv w2) :
  (N.max w1 w2 > 0)%N ->
  convert w1 (eval_shiftop op (convert (N.max w1 w2) lhs) (convert (N.max w1 w2) rhs)) =
  eval_shiftop op lhs rhs.
Proof.
  intros.
  funelim (eval_shiftop op lhs rhs).
  all: simp eval_shiftop.
  all: match type of Heq with
       | (_ = Some _) => apply convert_extend_to_N with (to := N.max n1 n2) in Heq
       | (_ = None) => apply convert_extend_to_N_none with (to := N.max n1 n2) in Heq
       end; [|lia].
  all: rewrite Heq; simpl.
  - apply convert_shr_convert. lia.
  - apply convert_exes. lia.
  - apply convert_shl_convert. lia.
  - apply convert_exes. lia.
  - apply convert_shl_convert. lia.
  - apply convert_exes. lia.
Qed.

Lemma expr_to_smt_value w expr : forall (m : VerilogSMTBijection.t) tag regs ρ t,
    expr_to_smt tag m expr = inr t ->
    verilog_smt_match_states_partial
      (fun v => List.In v (Verilog.expr_reads expr))
      tag m regs ρ ->
    SMTLib.interp_term ρ t =
      (let* xbv := eval_expr (w:=w) regs expr in
       let* bv := XBV.to_bv xbv in
       ret (SMTLib.Value_BitVec _ bv))%monad
.
Proof.
  induction expr.
  all: intros * Hexpr_to_smt Hmatch.
  all: simp expr_reads expr_to_smt eval_expr in *.
  all: unpack_verilog_smt_match_states_partial.
  all: try solve [some_inv]. (* Handle expressions that we abort on *)
  all: simpl in Hexpr_to_smt.
  all: unfold Verilog.expr_type in *.
  all: repeat match type of Hexpr_to_smt with
       | (match ?e with _ => _ end) = inr _ =>
         let E := fresh "E" in destruct e eqn:E
       | inl _ = inr _ => inv Hexpr_to_smt
       | inr _ = inr _ => inv Hexpr_to_smt
       end.
  all: repeat match goal with
  | [ H : context[_ -> SMTLib.interp_term _ _ = _] |- _] => insterU H
  end.
  all: repeat match goal with
       | [ |- context[eval_expr ?r ?e'] ] =>
         edestruct eval_expr_defined with (e := e');
         eauto using verilog_smt_match_states_partial_defined_value_for;
	 expect 1;
         replace (eval_expr r e') in *
       end.
  all: cbn - [SMTLib.interp_term eval_conditional conditional_to_smt XBV.extr N.add] in *.
  all: try rewrite XBV.xbv_bv_inverse in *.
  - (* arithmeticop *)
    edestruct eval_arithmeticop_to_bv as [bv Hbv]. rewrite Hbv.
    eauto using arithmeticop_to_smt_value.
  - (* bitwiseop *)
    edestruct eval_bitwiseop_to_bv as [bv Hbv]. rewrite Hbv.
    now eauto using bitwiseop_to_smt_value.
  - (* shiftop *)
    edestruct eval_shiftop_to_bv as [bv Hbv]. rewrite Hbv.
    edestruct eval_shiftop_to_bv as [bv_out Hbv_out].
    erewrite cast_from_to_value; [|assumption|]; cycle 1.
    + eapply shiftop_to_smt_value.
      * erewrite cast_from_to_value; [reflexivity|lia|].
        apply IHexpr1.
      * erewrite cast_from_to_value; [reflexivity|lia|].
        apply IHexpr2.
      * eassumption.
      * apply Hbv_out.
    + repeat f_equal.
      apply XBV.bv_xbv_inverse in Hbv, Hbv_out.
      apply XBV.from_bv_injective.
      rewrite Hbv.
      rewrite <- convert_no_exes. rewrite Hbv_out.
      rewrite <- ! convert_no_exes.
      eapply eval_shiftop_remove_converts. lia.
  - (* unop *)
    simpl in *; try rewrite XBV.xbv_bv_inverse in *.
    edestruct eval_unop_to_bv as [bv Hbv]. rewrite Hbv.
    now eauto using unaryop_to_smt_value.
  - (* conditional *)
    destruct eval_conditional_no_exes
      with (cond := x) (ifT := x0) (ifF := x1) as [bv Hbv].
    rewrite Hbv. rewrite XBV.xbv_bv_inverse.
    eapply conditional_to_smt_value; try eassumption; expect 1.
    rewrite Hbv, XBV.xbv_bv_inverse.
    reflexivity.
  - (* Range select *)
    rewrite XBV.extr_no_exes by lia.
    rewrite XBV.xbv_bv_inverse.
    cbn [SMTLib.interp_term]. rewrite IHexpr. 
    autodestruct_eqn E; [|lia].
    f_equal.
    apply SMTLib.value_eqb_eq.
    cbn [SMTLib.value_eqb].
    autodestruct; [|lia].
    destruct e. cbn.
    apply BV.bv_eq_reflect.
    f_equal. apply N2Nat.id.
  - (* Bitselect (literal) *)
    erewrite smt_select_bit_value with (val_vec := x) (val_idx := sel);
      eauto; expect 2.
    + rewrite select_bit_no_exes by assumption.
      rewrite XBV.xbv_bv_inverse.
      reflexivity.
    + rewrite select_bit_no_exes by assumption.
      rewrite XBV.xbv_bv_inverse.
      reflexivity.
  - (* Bitselect (width) *)
    erewrite smt_select_bit_value
      with (val_vec := x) (val_idx := x0);
      eauto.
    + simpl.
      rewrite select_bit_no_exes; cycle 1. {
        pose proof (BV.to_N_max_bound _ x0). lia.
      }
      now rewrite XBV.xbv_bv_inverse.
    + rewrite select_bit_no_exes; cycle 1. {
        pose proof (BV.to_N_max_bound _ x0). lia.
      }
      now rewrite XBV.xbv_bv_inverse.
    + pose proof (BV.to_N_max_bound _ x0). lia.
  - (* concat *)
    rewrite XBV.concat_to_bv.
    simpl.
    rewrite IHexpr1, IHexpr2.
    reflexivity.
  - (* literal *)
    reflexivity.
  - (* variable *)
    edestruct Hmatch as [smtName [Heq2 [? ? ? ? Hmatchvals]]]. { repeat econstructor. }
    rewrite Hverilogval.
    inv Hexpr_to_smt.
    funelim (var_to_smt tag m var);
        rewrite <- Heqcall in *; clear Heqcall; [|discriminate].
    unfold verilog_smt_match_states_partial in *.
    edestruct Hmatch as [? [? []]]; [now repeat econstructor|].
    inv Hmatchvals.
    inv H0. simpl.
    replace n_smt with smtName in * by congruence.
    now rewrite Hsmtval, XBV.xbv_bv_inverse.
  - (* resize *)
    rewrite convert_no_exes.
    rewrite XBV.xbv_bv_inverse.
    apply cast_from_to_value; eauto.
Qed.

Lemma expr_to_smt_valid w tag m expr t regs ρ val :
  expr_to_smt (w := w) tag m expr = inr t ->
  SMTLib.interp_term ρ t = Some val ->
  verilog_smt_match_states_partial (fun v => List.In v (Verilog.expr_reads expr)) tag m regs ρ ->
  exists xbv, (eval_expr regs expr = Some xbv /\ verilog_smt_match_value xbv val).
Proof.
  intros * Hexpr_to_smt Hinterp Hmatch_states.
  erewrite expr_to_smt_value in Hinterp; eauto.
  monad_inv.
  eauto using verilog_smt_match_to_bv.
Qed.
