From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import VerilogToSMT.
From vera Require Import VerilogSMT.
From vera Require SMTQueries.
From vera Require Import VerilogSemantics.
From vera Require Import Verilog.
Import CombinationalOnly.
From vera Require Import Bitvector.
Import RawXBV(bit(..)).

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

Lemma var_to_smt_value var tag regs ρ :
    verilog_smt_match_states_partial (fun v => v = var) tag regs ρ ->
    regs var = XBV.from_bv (SMTLib.interp_term ρ (var_to_smt tag var)).
Proof. crush. Qed.

Lemma var_to_smt_valid tag var (ρ : SMTLib.valuation) :
  ρ (verilog_to_smt_var tag var) = SMTLib.interp_term ρ (var_to_smt tag var).
Proof. crush. Qed.

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

Opaque N.sub N.add.

Lemma bv_extr_full n bv :
  n = RawBV.size bv ->
  RawBV.bv_extr 0 n n bv = bv.
Proof.
  intros ->.
  unfold RawBV.bv_extr, RawBV.size.
  rewrite N.add_0_r.
  rewrite N.ltb_irrefl.
  rewrite Nat2N.id.
  induction bv; simpl in *.
  - reflexivity.
  - f_equal. apply IHbv.
Qed.

Lemma cast_from_to_value ρ w_from w_to smt_from :
    (w_to > 0)%N ->
    SMTLib.interp_term ρ (cast_from_to w_from w_to smt_from) = convert_bv w_to (SMTLib.interp_term ρ smt_from).
Proof.
  intros Hnot_zero.
  remember (SMTLib.interp_term ρ smt_from) as val_from eqn:Hinterp_from.
  funelim (convert_bv w_to val_from); expect 3.
  all: funelim (cast_from_to from to smt_from); expect 9.
  all: autorewrite with bool_to_prop in *; try lia; expect 3.
  all: clear Heqcall Heqcall0 Heq Heq0.
  all: apply BV.of_bits_equal.
  all: repeat destruct_rew.
  - f_equal. f_equal. lia.
  - reflexivity.
  - replace (1 + (from - 1) - 0)%N with from by lia.
    apply bv_extr_full.
    symmetry. apply BV.wf.
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

Lemma smt_select_bit_value ρ w_vec w_idx
        (smt_vec : SMTLib.term (SMTLib.Sort_BitVec w_vec))
	(smt_idx : SMTLib.term (SMTLib.Sort_BitVec w_idx)) :
    (BV.to_N (SMTLib.interp_term ρ smt_idx) < w_vec)%N ->
    select_bit (XBV.from_bv (SMTLib.interp_term ρ smt_vec)) (XBV.from_bv (SMTLib.interp_term ρ smt_idx))
      = XBV.from_bv (SMTLib.interp_term ρ (smt_select_bit w_vec smt_vec w_idx smt_idx)).
Proof.
  intros Hbound.
  unfold select_bit, smt_select_bit in *.
  rewrite XBV.to_N_from_bv in *.
  simpl.
  erewrite ! cast_from_to_value; cycle 1;
    try eassumption; try lia; [idtac].
  destruct (N.eq_dec (N.max w_vec w_idx) (N.max w_vec w_idx)); [|crush].
  rewrite BV.bv_shr_as_select by lia.
  apply XBV.of_bits_equal. simpl.
  f_equal.
  rewrite XBV.bit_of_as_bv by lia.
  f_equal.
  rewrite to_N_convert_bv_extn by lia.
  rewrite bitOf_convert_bv_extn by lia.
  reflexivity.
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

Lemma expr_to_smt_value w expr : forall tag regs ρ t,
    expr_to_smt tag expr = inr t ->
    verilog_smt_match_states_partial
      (fun v => List.In v (Verilog.expr_reads expr))
      tag regs ρ ->
    eval_expr (w:=w) regs expr = XBV.from_bv (SMTLib.interp_term ρ t).
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
  all: repeat match goal with
              | [ H : eval_expr _ _ = XBV.from_bv ?x |- _ ] =>
	        rewrite <- H in *; clear x H
	      end.
  all: try (erewrite IHexpr by eauto; clear IHexpr).
  all: try (erewrite IHexpr1 by eauto; clear IHexpr1).
  all: try (erewrite IHexpr2 by eauto; clear IHexpr2).
  all: try (erewrite IHexpr3 by eauto; clear IHexpr3).
  - (* arithmeticop *)
    apply arithmeticop_to_smt_value.
  - (* bitwiseop *)
    apply bitwiseop_to_smt_value.
  - (* shiftop *)
    erewrite cast_from_to_value by assumption.
    rewrite <- convert_no_exes.
    rewrite <- shiftop_to_smt_value.
    rewrite ! cast_from_to_value by lia.
    rewrite <- ! convert_no_exes.
    rewrite eval_shiftop_remove_converts by lia.
    reflexivity.
  - (* unop *)
    apply unaryop_to_smt_value.
  - (* conditional *)
    eapply conditional_to_smt_value.
  - (* Range select *)
    apply XBV.extr_no_exes.
    lia.
  - (* Bitselect (literal) *)
    rewrite <- smt_select_bit_value by (simpl; lia).
    reflexivity.
  - (* Bitselect (width) *)
    apply smt_select_bit_value.
    pose proof (BV.to_N_max_bound _ (SMTLib.interp_term ρ t1)).
    lia.
  - (* concat *)
    apply XBV.concat_no_exes.
  - (* literal *)
    reflexivity.
  - (* variable *)
    apply Hmatch. left. reflexivity.
  - (* resize *)
    rewrite cast_from_to_value by lia.
    apply convert_no_exes.
Qed.

(* DELETEME: Duplicate *)
Lemma expr_to_smt_valid w tag expr t regs ρ :
  expr_to_smt (w := w) tag expr = inr t ->
  verilog_smt_match_states_partial (fun v => List.In v (Verilog.expr_reads expr)) tag regs ρ ->
  eval_expr regs expr = XBV.from_bv (SMTLib.interp_term ρ t).
Proof.
  eapply expr_to_smt_value.
Qed.
