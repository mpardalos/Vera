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
    SMTLib.interp_term ρ t =
      (let* xbv := regs var in
       let* bv := XBV.to_bv xbv in
       ret (SMTLib.Value_BitVec _ bv))%monad.
Proof.
  intros Hsmt Hmatch.
  funelim (var_to_smt tag m var); try rewrite <- Heqcall in *; clear Heqcall; monad_inv.
  unfold verilog_smt_match_states_partial in *.
  insterU Hmatch.
  destruct Hmatch as [smtName [Heq2 [? ? ? ? Hmatchvals]]].
  inv Hmatchvals.
  replace n_smt with smtName in * by congruence.
  simpl.
  rewrite Hverilogval, XBV.xbv_bv_inverse.
  assumption.
Qed.

Lemma var_to_smt_valid tag m var t ρ val :
  var_to_smt tag m var = inr t ->
  SMTLib.interp_term ρ t = Some val ->
  exists smtName, (m (tag, var) = Some smtName /\ ρ smtName = Some val).
Proof.
  intros Htransf Hsat.
  funelim (var_to_smt tag m var); rewrite <- Heqcall in *; monad_inv.
  crush.
Qed.

Lemma cast_from_to_part_eval ρ from to t w1 bv1:
  SMTLib.interp_term ρ (cast_from_to from to t) = Some (SMTLib.Value_BitVec w1 bv1) ->
  exists w2 bv2, SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec w2 bv2).
Proof.
  funelim (cast_from_to from to t); crush.
Qed.

Lemma arithmeticop_to_smt_value ρ op w smt_lhs smt_rhs t val_lhs val_rhs val :
    SMTLib.interp_term ρ smt_lhs = Some (SMTLib.Value_BitVec w val_lhs) ->
    SMTLib.interp_term ρ smt_rhs = Some (SMTLib.Value_BitVec w val_rhs) ->
    arithmeticop_to_smt op smt_lhs smt_rhs = inr t ->
    XBV.to_bv (eval_arithmeticop op (XBV.from_bv val_lhs) (XBV.from_bv val_rhs)) = Some val ->
    SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec w val).
Proof.
  intros Hinterp_lhs Hinterp_rhs Harithmeticop_to_smt Heval.
  destruct op;
    simp eval_arithmeticop arithmeticop_to_smt in *; inv Harithmeticop_to_smt;
    simpl; rewrite Hinterp_lhs; rewrite Hinterp_rhs; autodestruct; try contradiction;
    repeat f_equal; rewrite <- eq_rect_eq.
  - simp bv_binop in *. rewrite ! XBV.xbv_bv_inverse in *. simpl in *.
    rewrite XBV.xbv_bv_inverse in *. now some_inv.
  - simp bv_binop in *. rewrite ! XBV.xbv_bv_inverse in *. simpl in *.
    rewrite XBV.xbv_bv_inverse in *. now some_inv.
  - simp bv_binop in *. rewrite ! XBV.xbv_bv_inverse in *. simpl in *.
    rewrite XBV.xbv_bv_inverse in *. now some_inv.
Qed.

Lemma bitwiseop_to_smt_value ρ op w smt_lhs smt_rhs t val_lhs val_rhs val :
    SMTLib.interp_term ρ smt_lhs = Some (SMTLib.Value_BitVec w val_lhs) ->
    SMTLib.interp_term ρ smt_rhs = Some (SMTLib.Value_BitVec w val_rhs) ->
    bitwiseop_to_smt op smt_lhs smt_rhs = inr t ->
    XBV.to_bv (eval_bitwiseop op (XBV.from_bv val_lhs) (XBV.from_bv val_rhs)) = Some val ->
    SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec w val).
Proof.
  intros Hinterp_lhs Hinterp_rhs Hbitwiseop_to_smt Heval.
  destruct op;
    simp eval_bitwiseop bitwiseop_to_smt in *; inv Hbitwiseop_to_smt;
    simpl; rewrite Hinterp_lhs; rewrite Hinterp_rhs; autodestruct; try contradiction;
    repeat f_equal; rewrite <- eq_rect_eq.
    - erewrite bitwise_and_no_exes in Heval;
        rewrite XBV.xbv_bv_inverse in *;
        (reflexivity || now some_inv).
    - erewrite bitwise_or_no_exes in Heval;
        rewrite XBV.xbv_bv_inverse in *;
        (reflexivity || now some_inv).
Qed.

Lemma shiftop_to_smt_value ρ op w smt_lhs smt_rhs t val_lhs val_rhs val :
    SMTLib.interp_term ρ smt_lhs = Some (SMTLib.Value_BitVec w val_lhs) ->
    SMTLib.interp_term ρ smt_rhs = Some (SMTLib.Value_BitVec w val_rhs) ->
    shiftop_to_smt op smt_lhs smt_rhs = inr t ->
    XBV.to_bv (eval_shiftop op (XBV.from_bv val_lhs) (XBV.from_bv val_rhs)) = Some val ->
    SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec w val).
Proof.
  intros Hinterp_lhs Hinterp_rhs Hshiftop_to_smt Heval.
  destruct op;
    simp eval_shiftop shiftop_to_smt in *; inv Hshiftop_to_smt;
    simpl; rewrite Hinterp_lhs; rewrite Hinterp_rhs; autodestruct; try contradiction;
    repeat f_equal; rewrite <- eq_rect_eq.
  - rewrite XBV.to_N_from_bv in *. simpl in *.
    erewrite XBV.shr_to_bv in *.
    rewrite BV.shr_swap_definition.
    now some_inv.
  - rewrite XBV.to_N_from_bv in *. simpl in *.
    erewrite XBV.shl_to_bv in *.
    rewrite BV.shl_swap_definition.
    now some_inv.
  - rewrite XBV.to_N_from_bv in *. simpl in *.
    erewrite XBV.shl_to_bv in *.
    rewrite BV.shl_swap_definition.
    now some_inv.
Qed.

Lemma unaryop_to_smt_value ρ op w smt_expr t val_expr val :
    SMTLib.interp_term ρ smt_expr = Some (SMTLib.Value_BitVec w val_expr) ->
    unaryop_to_smt op smt_expr = inr t ->
    XBV.to_bv (eval_unaryop op (XBV.from_bv val_expr)) = Some val ->
    SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec w val).
Proof.
  intros Hinterp_expr Hunaryop_to_smt Heval.
  destruct op;
    simp eval_unaryop unaryop_to_smt in *; inv Hunaryop_to_smt;
    simpl; rewrite Hinterp_expr; autodestruct; try contradiction;
    repeat f_equal; try rewrite <- eq_rect_eq.
  - rewrite XBV.xbv_bv_inverse in *. now some_inv.
Qed.

Lemma conditional_to_smt_value ρ w_cond w smt_cond smt_ifT smt_ifF val_cond val_ifT val_ifF val :
    SMTLib.interp_term ρ smt_cond = Some (SMTLib.Value_BitVec w_cond val_cond) ->
    SMTLib.interp_term ρ smt_ifT = Some (SMTLib.Value_BitVec w val_ifT) ->
    SMTLib.interp_term ρ smt_ifF = Some (SMTLib.Value_BitVec w val_ifF) ->
    XBV.to_bv (eval_conditional
                 (XBV.from_bv val_cond)
                 (XBV.from_bv val_ifT)
                 (XBV.from_bv val_ifF)) =
      Some val ->
    SMTLib.interp_term ρ (conditional_to_smt w_cond smt_cond smt_ifT smt_ifF) =
      Some (SMTLib.Value_BitVec w val).
Proof.
  intros Hinterp_cond Hinterp_ifT Hinterp_ifF Heval.
  unfold eval_conditional in *.
  rewrite XBV.xbv_bv_inverse in *.
  simpl in *. rewrite Hinterp_cond, Hinterp_ifT, Hinterp_ifF.
  simpl.
  destruct (N.eq_dec w_cond w_cond); try contradiction.
  replace (rew <- [BVList.BITVECTOR_LIST.bitvector] e in BV.zeros w_cond)
    with (BV.zeros w_cond) by apply eq_rect_eq.
  destruct (BV.is_zero val_cond) eqn:E;
    rewrite XBV.xbv_bv_inverse in Heval; unfold BV.is_zero in *;
    crush.
Qed.

Lemma cast_from_to_value ρ w_from w_to smt_from val_from :
    (w_to > 0)%N ->
    SMTLib.interp_term ρ smt_from = Some (SMTLib.Value_BitVec w_from val_from) ->
    SMTLib.interp_term ρ (cast_from_to w_from w_to smt_from) =
      Some (SMTLib.Value_BitVec w_to (convert_bv w_to val_from)).
Proof.
  intros Hnot_zero Hinterp_from.
  funelim (convert_bv w_to val_from).
  - funelim (cast_from_to from to smt_from);
      [ rewrite N.compare_eq_iff in *; lia
      | rewrite N.compare_lt_iff in *; lia
      |idtac].
    rewrite N.compare_gt_iff in *.
    simpl. rewrite Hinterp_from.
    f_equal.
    apply value_bitvec_bits_equal.
    destruct_rew. simpl.
    repeat f_equal. lia.
  - funelim (cast_from_to from to smt_from);
      [ rewrite N.compare_eq_iff in *; lia
      | rewrite N.compare_lt_iff in *
      | rewrite N.compare_gt_iff in *; lia ].
    simpl. rewrite Hinterp_from.
    f_equal.
    apply value_bitvec_bits_equal.
    simpl.
    repeat f_equal. lia.
  - funelim (cast_from_to from to smt_from);
      [ rewrite N.compare_eq_iff in *
      | rewrite N.compare_lt_iff in *; lia
      | rewrite N.compare_gt_iff in *; lia ].
    simpl. rewrite Hinterp_from.
    f_equal.
    apply value_bitvec_bits_equal.
    destruct_rew.
    reflexivity.
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
  - destruct_rew. simpl.
    funelim (convert from (XBV.shr (XBV.concat (XBV.zeros (to - from)) value) shamt)); [lia|idtac|lia].
    apply XBV.extr_shr_extend.
  - destruct_rew. simpl.
    funelim (convert from (XBV.shr value shamt)); [lia|lia|idtac].
    rewrite <- eq_rect_eq. reflexivity.
Qed.

Lemma convert_shl_convert n1 n2 (xbv : XBV.xbv n1) shamt :
  (n2 >= n1)%N ->
  convert n1 (XBV.shl (convert n2 xbv) shamt) = XBV.shl xbv shamt.
Proof.
  intros.
  funelim (convert n2 xbv); [idtac|lia|idtac].
  - destruct_rew. simpl.
    funelim (convert from (XBV.shl (XBV.concat (XBV.zeros (to - from)) value) shamt)); [lia|idtac|lia].
    apply XBV.extr_shl_extend.
  - destruct_rew. simpl.
    funelim (convert from (XBV.shl value shamt)); [lia|lia|idtac].
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
  - apply convert_extend_to_N with (to := N.max n1 n2) in Heq; [|lia].
    simp eval_shiftop. rewrite Heq. simpl.
    apply convert_shr_convert. lia.
  - apply convert_extend_to_N_none with (to := N.max n1 n2) in Heq; [|lia].
    simp eval_shiftop. rewrite Heq. simpl.
    apply convert_exes. lia.
  - apply convert_extend_to_N with (to := N.max n1 n2) in Heq; [|lia].
    simp eval_shiftop. rewrite Heq. simpl.
    apply convert_shl_convert. lia.
  - apply convert_extend_to_N_none with (to := N.max n1 n2) in Heq; [|lia].
    simp eval_shiftop. rewrite Heq. simpl.
    apply convert_exes. lia.
  - apply convert_extend_to_N with (to := N.max n1 n2) in Heq; [|lia].
    simp eval_shiftop. rewrite Heq. simpl.
    apply convert_shl_convert. lia.
  - apply convert_extend_to_N_none with (to := N.max n1 n2) in Heq; [|lia].
    simp eval_shiftop. rewrite Heq. simpl.
    apply convert_exes. lia.
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
  induction expr; intros * Hexpr_to_smt Hmatch;
    simp expr_reads expr_to_smt eval_expr in *;
    unpack_verilog_smt_match_states_partial.
  - (* arithmeticop *)
    simpl in Hexpr_to_smt.
    destruct (expr_to_smt tag m expr1) eqn:E1; try discriminate.
    destruct (expr_to_smt tag m expr2) eqn:E2; try discriminate.
    insterU IHexpr1.
    insterU IHexpr2.
    edestruct eval_expr_defined with (e := expr1);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr1) in *.
    edestruct eval_expr_defined with (e := expr2);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr2) in *.
    simpl in *.
    rewrite XBV.xbv_bv_inverse in *.
    edestruct eval_arithmeticop_to_bv as [bv Hbv].
    rewrite Hbv.
    now eauto using arithmeticop_to_smt_value.
  - (* bitwiseop *)
    simpl in Hexpr_to_smt.
    destruct (expr_to_smt tag m expr1) eqn:E1; try discriminate.
    destruct (expr_to_smt tag m expr2) eqn:E2; try discriminate.
    insterU IHexpr1.
    insterU IHexpr2.
    edestruct eval_expr_defined with (e := expr1);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr1) in *.
    edestruct eval_expr_defined with (e := expr2);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr2) in *.
    simpl in *.
    rewrite XBV.xbv_bv_inverse in *.
    edestruct eval_bitwiseop_to_bv as [bv Hbv].
    rewrite Hbv.
    now eauto using bitwiseop_to_smt_value.
  - (* shiftop *)
    unfold Verilog.expr_type in *.
    simpl in Hexpr_to_smt.
    destruct (expr_to_smt tag m expr1) eqn:E1; try discriminate.
    destruct (expr_to_smt tag m expr2) eqn:E2; try discriminate.
    autodestruct_eqn E.
    insterU IHexpr1.
    insterU IHexpr2.
    edestruct eval_expr_defined with (e := expr1);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr1) in *.
    edestruct eval_expr_defined with (e := expr2);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr2) in *.
    simpl in *.
    rewrite XBV.xbv_bv_inverse in *.
    edestruct eval_shiftop_to_bv as [bv Hbv].
    rewrite Hbv.
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
    simpl in Hexpr_to_smt.
    destruct (expr_to_smt tag m expr) eqn:E; try discriminate.
    insterU IHexpr.
    edestruct eval_expr_defined with (e := expr);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr) in *.
    simpl in *.
    rewrite XBV.xbv_bv_inverse in *.
    edestruct eval_unop_to_bv as [bv Hbv].
    rewrite Hbv.
    eauto.
    now eauto using unaryop_to_smt_value.
  - (* conditional *)
    simpl in Hexpr_to_smt.
    destruct (expr_to_smt tag m expr1) eqn:E1; try discriminate.
    destruct (expr_to_smt tag m expr2) eqn:E2; try discriminate.
    destruct (expr_to_smt tag m expr3) eqn:E3; try discriminate.
    insterU IHexpr1.
    insterU IHexpr2.
    insterU IHexpr3.
    edestruct eval_expr_defined with (e := expr1);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr1) in *.
    edestruct eval_expr_defined with (e := expr2);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr2) in *.
    edestruct eval_expr_defined with (e := expr3);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr3) in *.
    simpl in *.
    rewrite XBV.xbv_bv_inverse in *.
    inv Hexpr_to_smt.
    destruct eval_conditional_no_exes
      with (cond := x) (ifT := x0) (ifF := x1) as [bv Hbv].
    rewrite conditional_to_smt_value
      with (val_cond := x) (val_ifT := x0) (val_ifF := x1) (val := bv);
      try rewrite Hbv, XBV.xbv_bv_inverse;
      eauto.
  - (* Bitselect (literal) *)
    simpl in Hexpr_to_smt. monad_inv.
    insterU IHexpr.
    edestruct eval_expr_defined with (e := expr);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr) in *.
    erewrite smt_select_bit_value with (val_vec := x) (val_idx := sel); eauto.
    + simpl.
      rewrite select_bit_no_exes by assumption.
      now rewrite XBV.xbv_bv_inverse.
    + rewrite IHexpr. simpl.
      now rewrite XBV.xbv_bv_inverse.
    + rewrite select_bit_no_exes by assumption.
      now rewrite XBV.xbv_bv_inverse.
  - (* Bitselect (width) *)
    simpl in Hexpr_to_smt. monad_inv.
    insterU IHexpr1.
    insterU IHexpr2.
    edestruct eval_expr_defined with (e := expr1);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr1) in *.
    edestruct eval_expr_defined with (e := expr2);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr2) in *.
    simpl in * |-. rewrite XBV.xbv_bv_inverse in *.
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
    simpl in Hexpr_to_smt.
    destruct (expr_to_smt tag m expr1) eqn:E1; try discriminate.
    destruct (expr_to_smt tag m expr2) eqn:E2; try discriminate.
    insterU IHexpr1.
    insterU IHexpr2.
    edestruct eval_expr_defined with (e := expr1);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr1) in *.
    edestruct eval_expr_defined with (e := expr2);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr2) in *.
    simpl in *.
    rewrite XBV.xbv_bv_inverse in *.
    rewrite XBV.concat_to_bv.
    inv Hexpr_to_smt.
    simpl.
    rewrite IHexpr1, IHexpr2.
    reflexivity.
  - (* literal *)
    simpl.
    rewrite XBV.xbv_bv_inverse.
    inv Hexpr_to_smt.
    reflexivity.
  - (* variable *)
    simpl.
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
    simpl in Hexpr_to_smt.
    repeat match type of Hexpr_to_smt with
    | context[match ?c with _ => _ end] =>
        let E := fresh "E" in
        destruct c eqn:E; try discriminate
    | inr _ = inr _ => inv Hexpr_to_smt
    | inl _ = inl _ => inv Hexpr_to_smt
    end.
    insterU IHexpr.
    edestruct eval_expr_defined with (e := expr);
      eauto using verilog_smt_match_states_partial_defined_value_for.
    replace (eval_expr regs expr) in *.
    simpl in *.
    rewrite XBV.xbv_bv_inverse in *.
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
