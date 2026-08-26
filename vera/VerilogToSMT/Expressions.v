From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import VerilogToSMT.
From vera Require Import VerilogSMT.
From vera Require SMTQueries.
From vera Require Import VerilogSemantics.
From vera Require Import Verilog.
From vera Require Import Variables.
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
Import Verilog.Notations.

Local Open Scope list.
Local Open Scope verilog_scope.

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
  all: try reflexivity.
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

Inductive and_reduce_bv_cases {w} : BV.bitvector w -> RawXBV.bit -> Prop :=
  | and_reduce_ones x : x = BV.ones w -> and_reduce_bv_cases x RawXBV.I
  | and_reduce_other x : x <> BV.ones w -> and_reduce_bv_cases x RawXBV.O
  .

Lemma and_reduce_rec_false xbv : RawXBV.fold O and_bit xbv = O.
Proof. induction xbv; simp and_bit; auto. Qed.

Lemma and_reduce_bv_spec {w} (bv : BV.bitvector w) :
  and_reduce_bv_cases bv (XBV.fold I and_bit (XBV.from_bv bv)).
Proof.
  unfold XBV.fold. XBV.bitvector_erase. subst.
  induction bv.
  all: simpl.
  - replace ({| BV.bv := []; BV.wf := eq_refl |}) with (BV.ones 0)
      by now XBV.bitvector_erase.
    apply and_reduce_ones.
    reflexivity.
  - inv IHbv; destruct a; simpl; simp and_bit.
    + rewrite <- H. constructor.
      (* TODO: Most of what happens in these cases should really be part of XBV.bitvector_erase *)
      apply BV.of_bits_equal. simpl.
      apply (f_equal (@BV.bits _)) in H1. simpl in H1.
      unfold RawBV.ones, RawBV.size in *.
      rewrite !Nat2N.id in *. simpl. now f_equal.
    + rewrite and_reduce_rec_false. constructor.
      intros contra. apply (f_equal (@BV.bits _)) in contra. simpl in contra.
      unfold RawBV.ones, RawBV.size in contra.
      rewrite Nat2N.id in contra. discriminate.
    + rewrite <- H. constructor.
      intros contra. apply H1, BV.of_bits_equal.
      apply (f_equal (@BV.bits _)) in contra. simpl in contra.
      unfold RawBV.ones, RawBV.size in *. rewrite !Nat2N.id in *.
      simpl in contra. simpl.
      unfold RawBV.ones, RawBV.size. rewrite Nat2N.id.
      now injection contra.
    + rewrite and_reduce_rec_false. constructor.
      intros contra. apply (f_equal (@BV.bits _)) in contra. simpl in contra.
      unfold RawBV.ones, RawBV.size in contra.
      rewrite Nat2N.id in contra. discriminate.
Qed.

Lemma unaryop_to_smt_value ρ op w (smt_expr : SMTLib.term (SMTLib.Sort_BitVec w)) :
    eval_unaryop op (XBV.from_bv (SMTLib.interp_term ρ smt_expr))
      = XBV.from_bv (SMTLib.interp_term ρ (unaryop_to_smt op smt_expr)).
Proof.
  destruct op.
  all: simp eval_unaryop unaryop_to_smt in *.
  all: cbn [SMTLib.interp_term].
  all: autorewrite with xbv in *.
  all: try reflexivity; expect 2.
  - simpl. unfold BV.is_zero.
    destruct (BV.bv_eq (n:=w) (SMTLib.interp_term ρ smt_expr) (BV.zeros w)).
    + apply XBV.ones_from_bv.
    + apply XBV.zeros_from_bv.
  - destruct (and_reduce_bv_spec (SMTLib.interp_term ρ smt_expr)).
    + subst x. replace (SMTLib.value_eqb _ _) with true
        by (symmetry; now apply SMTLib.value_eqb_refl).
      rewrite <- XBV.ones_from_bv.
      XBV.bitvector_erase. reflexivity.
    + replace (SMTLib.value_eqb _ _) with false
        by (symmetry; now apply SMTLib.value_eqb_neq).
      rewrite <- XBV.zeros_from_bv.
      XBV.bitvector_erase. reflexivity.
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
    XBV.extr (XBV.from_bv (SMTLib.interp_term ρ smt_vec)) idx 1
      = XBV.from_bv (SMTLib.interp_term ρ (smt_select_bit smt_vec idx)).
Proof.
  intros Hbound.
  unfold smt_select_bit in *. simpl.
  rewrite smtlib_interp_rewrite.
  simpl. rewrite N.add_sub. simpl.
  apply XBV.extr_no_exes.
  lia.
Qed.

Lemma expr_to_smt_value w expr : forall tag regs ρ t,
    expr_to_smt tag expr = inr t ->
    verilog_smt_match_states_partial (Verilog.expr_reads expr) tag regs ρ ->
    eval_expr (w:=w) regs expr = XBV.from_bv (SMTLib.interp_term ρ t).
Proof.
  induction expr.
  all: intros * Hexpr_to_smt Hmatch.
  all: try match goal with [slice : Slice.t _ |- _] => destruct slice end.
  all: simpl in *; simp expr_to_smt eval_expr in *.
  all: unpack_verilog_smt_match_states_partial.
  all: expect 12.
  all: try solve [some_inv]. (* Handle expressions that we abort on *)
  all: expect 11.
  all: simpl in *.
  (* all: unfold Verilog.expr_type in *. *)
  all: repeat match type of Hexpr_to_smt with
       | (match ?e with _ => _ end) = inr _ =>
         let E := fresh "E" in destruct e eqn:E
       | inl _ = inr _ => inv Hexpr_to_smt
       | inr _ = inr _ => inv Hexpr_to_smt
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
    unfold verilog_smt_match_states_partial in Hmatch.
    simpl.
    rewrite <- XBV.extr_no_exes by lia.
    change (XBV.extr (regs var) lo (1 + hi - lo))
      with (RegisterState.get_slice regs (Slice.Mk var hi lo wf)).
    erewrite RegisterState.get_slice_match by exact Hmatch.
    reflexivity.
  - (* Bitselect (literal) *)
    destruct expr.
    all: simp expr_to_smt in Hexpr_to_smt.
    all: inv Hexpr_to_smt.
    all: rename_match (_ = inr t) into Hexpr_to_smt.
    all: expect 1.
    simp eval_expr.
    destruct (XBV.to_N x) as [idx|] eqn:Ex.
    all: simpl in Hexpr_to_smt; inv Hexpr_to_smt.
    all: rename_match (_ = inr t) into Hexpr_to_smt.
    all: expect 1.
    destruct (assert_dec (idx < Var.varType vec)%N _).
    all: inv Hexpr_to_smt.
    replace (idx <? Var.varType vec)%N with true in Hmatch by lia.
    (* TODO: Simplify, it shouldn't by unfolding/specializing match_on. *)
    rewrite <- smt_select_bit_value by lia.
    unfold verilog_smt_match_states_partial in Hmatch.
    apply XBV.bitOf_ext. intros bit_idx Hbit_idx.
    rewrite !XBV.extr_bitOf by lia.
    replace (idx + bit_idx)%N with idx by lia.
    specialize (Hmatch (Location.Mk vec idx)).
    unfold RegisterState.get_location in Hmatch.
    apply Hmatch.
    apply LocationSet.singleton_spec. reflexivity.
  - (* concat *)
    apply XBV.concat_no_exes.
  - (* literal *)
    destruct (XBV.to_bv x) eqn:Hbv; simpl in E; inv E. 
    apply XBV.bv_xbv_inverse in Hbv. subst x.
    reflexivity.
  - (* variable *)
    apply XBV.bitOf_ext. intros bit_idx Hbit_idx.
    apply (Hmatch (Location.Mk var bit_idx)).
    apply LocationSet.of_variable_spec. auto.
  - rewrite cast_from_to_value by lia.
    apply convert_no_exes.
Qed.

(* DELETEME: Duplicate *)
Lemma expr_to_smt_valid w tag expr t regs ρ :
  expr_to_smt (w := w) tag expr = inr t ->
  verilog_smt_match_states_partial (Verilog.expr_reads expr) tag regs ρ ->
  eval_expr regs expr = XBV.from_bv (SMTLib.interp_term ρ t).
Proof.
  eapply expr_to_smt_value.
Qed.
