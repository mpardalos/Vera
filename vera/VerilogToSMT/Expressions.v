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

Lemma smtlib_interp_rewrite w1 w2 ρ (E : w1 = w2) t : 
  SMTLib.interp_term ρ (rew [fun n : N => SMTLib.term (SMTLib.Sort_BitVec n)] E in t)
   = rew [fun n => BV.bitvector n] E in SMTLib.interp_term ρ t.
Proof. subst. reflexivity. Qed.

Lemma smt_select_bit_value ρ w (smt_vec : SMTLib.term (SMTLib.Sort_BitVec w)) (idx : N) :
    (idx < w)%N ->
    XBV.of_bits [XBV.bitOf (N.to_nat idx) (XBV.from_bv (SMTLib.interp_term ρ smt_vec))]
      = XBV.from_bv (SMTLib.interp_term ρ (smt_select_bit smt_vec idx)).
Proof.
  intros Hbound.
  unfold smt_select_bit in *. simpl.
  rewrite smtlib_interp_rewrite.
  simpl. rewrite N.add_sub. simpl.
  rewrite BV.bv_extr_one_bit by lia.
  rewrite XBV.bit_of_as_bv by lia.
  XBV.bitvector_erase. reflexivity.
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
  all: simpl in *.
  (* all: unfold Verilog.expr_type in *. *)
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
    apply shiftop_to_smt_value.
  - (* unop *)
    apply unaryop_to_smt_value.
  - (* conditional *)
    eapply conditional_to_smt_value.
  - (* Range select *)
    apply XBV.extr_no_exes.
    lia.
  - (* Bitselect (literal) *)
    unfold select_bit.
    autorewrite with xbv.
    apply smt_select_bit_value.
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
