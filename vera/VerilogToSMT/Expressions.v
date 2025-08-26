From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Tactics.
From vera Require Import VerilogToSMT.
From vera Require Import SMT.
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

From Coq Require List.
From Coq Require Import String.
From Coq Require Import Logic.ProofIrrelevance.
From Coq Require Import NArith.
From Coq Require Import PeanoNat.
From Coq Require Import Morphisms.
From Coq Require Import Classes.Morphisms_Prop.
From Coq Require Import Setoid.
From Coq Require ZifyBool.
From Coq Require Import Program.Equality.

From Equations Require Import Equations.

Import List.ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Import SigTNotations.

Local Open Scope list.

Lemma bitwise_binop_no_exes (f_bit : bit -> bit -> bit) (f_bool : bool -> bool -> bool) :
  (forall (lb rb : bool), RawXBV.bool_to_bit (f_bool lb rb) = f_bit (RawXBV.bool_to_bit lb) (RawXBV.bool_to_bit rb)) ->
  forall n (l_xbv r_xbv : XBV.xbv n) (l_bv r_bv : BV.bitvector n),
    XBV.to_bv l_xbv = Some l_bv ->
    XBV.to_bv r_xbv = Some r_bv ->
    bitwise_binop f_bit l_xbv r_xbv = XBV.from_bv (BV.map2 f_bool l_bv r_bv).
Proof.
  intros * Hf * Hl Hr.
  unfold RawBV.bv_and.
  pose proof (XBV.bv_xbv_inverse _ _ _ Hl) as Hl_inverse. subst l_xbv.
  pose proof (XBV.bv_xbv_inverse _ _ _ Hr) as Hr_inverse. subst r_xbv.
  clear Hl. clear Hr.
  apply XBV.of_bits_equal; simpl.
  destruct l_bv as [l_bv l_bv_wf].
  destruct r_bv as [r_bv r_bv_wf].
  simpl in *.
  unfold bitwise_binop_raw.
  generalize dependent n.
  generalize dependent r_bv.
  induction l_bv; simpl; simp map2; try easy.
  destruct r_bv; simpl; simp map2; try easy.
  specialize (IHl_bv r_bv).
  intros.
  simpl in *. f_equal.
  - auto.
  - unfold BVList.RAWBITVECTOR_LIST.size in *.
    eapply IHl_bv; crush.
Qed.

Import EqNotations.

Lemma bitwise_and_no_exes :
  forall w (l_xbv r_xbv : XBV.xbv w) (l_bv r_bv : BV.bitvector w),
    XBV.to_bv l_xbv = Some l_bv ->
    XBV.to_bv r_xbv = Some r_bv ->
    bitwise_binop and_bit l_xbv r_xbv = XBV.from_bv (BV.bv_and l_bv r_bv).
Proof.
  intros w [] [] [] [] Hl Hr.
  etransitivity. {
    apply bitwise_binop_no_exes with (f_bool:=andb); eauto.
    intros [] []; crush.
  }
  f_equal. apply BV.of_bits_equal. simpl.
  unfold BVList.RAWBITVECTOR_LIST.bv_and.
  replace (BVList.RAWBITVECTOR_LIST.size bv1).
  replace (BVList.RAWBITVECTOR_LIST.size bv2).
  rewrite N.eqb_refl.
  reflexivity.
Qed.

Lemma bitwise_or_no_exes :
  forall w (l_xbv r_xbv : XBV.xbv w) (l_bv r_bv : BV.bitvector w),
    XBV.to_bv l_xbv = Some l_bv ->
    XBV.to_bv r_xbv = Some r_bv ->
    bitwise_binop or_bit l_xbv r_xbv = XBV.from_bv (BV.bv_or l_bv r_bv).
Proof.
  intros w [] [] [] [] Hl Hr.
  etransitivity. {
    apply bitwise_binop_no_exes with (f_bool:=orb); try crush.
    intros [] []; crush.
  }
  f_equal. apply BV.of_bits_equal. simpl.
  unfold BVList.RAWBITVECTOR_LIST.bv_or.
  replace (BVList.RAWBITVECTOR_LIST.size bv1).
  replace (BVList.RAWBITVECTOR_LIST.size bv2).
  rewrite N.eqb_refl.
  reflexivity.
Qed.

Lemma xbv_concat_no_exes w1 w2 (bv1 : BV.bitvector w1) (bv2 : BV.bitvector w2) :
  XBV.concat (XBV.from_bv bv1) (XBV.from_bv bv2) =
    XBV.from_bv (BV.bv_concat bv1 bv2).
Proof.
  destruct bv1 as [bv1 wf1], bv2 as [bv2 wf2].
  apply XBV.of_bits_equal. simpl.
  unfold RawBV.bv_concat, RawXBV.from_bv.
  rewrite <- List.map_app.
  reflexivity.
Qed.

Lemma xbv_concat_to_bv w1 w2 (bv1 : BV.bitvector w1) (bv2 : BV.bitvector w2) :
  XBV.to_bv (XBV.concat (XBV.from_bv bv1) (XBV.from_bv bv2)) =
    Some (BV.bv_concat bv1 bv2).
Proof.
  rewrite xbv_concat_no_exes.
  rewrite XBV.xbv_bv_inverse.
  reflexivity.
Qed.

Lemma rawbv_extr_one_bit (n : N) vec :
  (1 + n <= RawBV.size vec)%N ->
  RawBV.bv_extr n 1 (RawBV.size vec) vec = [RawBV.bitOf (N.to_nat n) vec].
Proof.
  intros. unfold RawBV.bv_extr, RawBV.size in *.
  autodestruct_eqn E; try (rewrite N.ltb_lt in *; lia); clear E.
  replace (N.to_nat (1 + n)) with (S (N.to_nat n)) by lia.
  assert (S (N.to_nat n) <= List.length vec) as H' by lia. clear H. revert H'.
  generalize (N.to_nat n). clear n. intros n H.
  revert vec H.
  induction n; intros.
  { destruct vec; try crush.
    destruct vec; crush.
  }
  destruct vec; try crush.
  simpl.
  rewrite IHn; crush.
Qed.

Definition bit_of_as_bv i w (bv : BV.bitvector w) :
  i < N.to_nat w ->
  XBV.bitOf i (XBV.from_bv bv) = RawXBV.bool_to_bit (BV.bitOf i bv).
Proof.
  destruct bv as [bv bv_wf]. unfold RawBV.size in *.
  unfold XBV.bitOf, RawXBV.bitOf, XBV.from_bv, RawXBV.from_bv, BV.bitOf, RawBV.bitOf;
    simpl.
  intros.
  rewrite List.nth_indep with (d':=O)
    by (rewrite List.map_length; lia).
  replace O with (RawXBV.bool_to_bit false)
    by reflexivity.
  apply List.map_nth.
Qed.

Definition select_bit_bv {w1 w2} (vec : BV.bitvector w1) (idx : BV.bitvector w2) : BV.bitvector 1 :=
  BV.of_bits [BV.bitOf (N.to_nat (BV.to_N idx)) vec].

Lemma to_bv_some_raw_iff w (xbv : XBV.xbv w) (bv : BV.bitvector w) :
  XBV.to_bv xbv = Some bv <-> RawXBV.to_bv (XBV.bits xbv) = Some (BV.bits bv).
Proof. Admitted.

Lemma select_bit_to_bv w_vec w_idx (vec : BV.bitvector w_vec) (idx : BV.bitvector w_idx) :
  (BV.to_N idx < w_vec)%N ->
  XBV.to_bv (select_bit (XBV.from_bv vec) (XBV.from_bv idx)) =
    Some (select_bit_bv vec idx).
Proof.
  intros H.
  unfold select_bit, select_bit_bv.
  rewrite XBV.to_N_from_bv.
  rewrite bit_of_as_bv by lia.
  generalize (BV.bitOf (n:=w_vec) (N.to_nat (BV.to_N idx)) vec). intro b.
  apply to_bv_some_raw_iff.
  simpl.
  unfold RawXBV.to_bv. simpl.
  rewrite RawXBV.bit_to_bool_inverse.
  reflexivity.
Qed.

Lemma value_bitvec_bits_equal n1 n2 bv1 bv2 :
  BV.bits bv1 = BV.bits bv2 ->
  SMTLib.Value_BitVec n1 bv1 = SMTLib.Value_BitVec n2 bv2.
Proof.
  intros H.
  destruct bv1 as [bv1 wf1], bv2 as [bv2 wf2]. cbn in *.
  subst bv2.
  assert (n1 = n2) by crush.
  subst.
  reflexivity.
Qed.

Lemma statically_in_bounds_max_bound {w} max_bound e regs (xbv : XBV.xbv w) val :
  statically_in_bounds max_bound e ->
  eval_expr regs e = Some xbv ->
  XBV.to_N xbv = Some val ->
  (val < max_bound)%N.
Proof.
  unfold statically_in_bounds, static_value.
  intros Hinbounds Heval HtoN.
  inv Hinbounds.
  - destruct e; try crush.
    simp eval_expr in Heval. inv Heval.
    rewrite XBV.to_N_from_bv in HtoN. inv HtoN.
    crush.
  - enough (val < 2 ^ w)%N by lia.
    eauto using XBV.to_N_max_bound.
Qed.

Lemma rawxbv_from_bv_app b1 b2 :
  RawXBV.from_bv (b1 ++ b2)%list = (RawXBV.from_bv b1 ++ RawXBV.from_bv b2)%list.
Proof. unfold RawXBV.from_bv. apply List.map_app. Qed.

Lemma shl_to_bv n vec shamt :
  XBV.to_bv (XBV.shl (XBV.from_bv vec) (BV.to_N shamt)) = Some (BV.bv_shl (n:=n) vec shamt).
Proof.
  unfold BV.to_N, RawBV.to_N, BV.bv_shl, RawBV.bv_shl, RawBV.shl_be.
  intros.
  destruct vec as [vec vec_wf].
  destruct shamt as [shamt shamt_wf].
  rewrite <- XBV.xbv_bv_inverse. f_equal.
  apply XBV.of_bits_equal; simpl.
  rewrite vec_wf, shamt_wf. clear vec_wf shamt_wf.
  rewrite N.eqb_refl. rewrite Nat2N.id. clear n.
  rewrite RawBV.shl_be_nicify.
  generalize (RawBV.list2nat_be shamt). clear shamt. intro i.
  funelim (RawBV.nice_nshl_be vec i);
    repeat progress (simpl in *; simp shl nice_nshl_be in * );
    [crush|crush|].
  rewrite <- H. clear H.
  repeat f_equal.
  induction l; destruct b; crush.
Qed.

Lemma shr_to_bv n vec shamt :
  XBV.to_bv (XBV.shr (XBV.from_bv vec) (BV.to_N shamt)) = Some (BV.bv_shr (n:=n) vec shamt).
Proof.
  unfold BV.to_N, RawBV.to_N, BV.bv_shr, RawBV.bv_shr, RawBV.shr_be.
  intros.
  destruct vec as [vec vec_wf].
  destruct shamt as [shamt shamt_wf].
  rewrite <- XBV.xbv_bv_inverse. f_equal.
  apply XBV.of_bits_equal; simpl.
  rewrite vec_wf, shamt_wf. clear vec_wf shamt_wf.
  rewrite N.eqb_refl. rewrite Nat2N.id. clear n.
  generalize (RawBV.list2nat_be shamt). clear shamt. intro i.
  revert vec.
  induction i; intros.
  - simp shr. crush.
  - simpl.
    rewrite <- IHi. clear IHi.
    destruct vec; simpl; simp shr.
    + destruct i; crush.
    + clear b.
      rewrite rawxbv_from_bv_app. simpl.
      generalize (RawXBV.from_bv vec). clear vec. intro vec.
      revert i.
      induction vec; intros.
      * destruct i; simpl; simp shr; try crush.
        destruct i; simpl; simp shr; try crush.
      * simpl; simp shr.
        destruct i; simpl; simp shr; try crush.
Qed.

Ltac cleanup :=
  repeat match goal with
    | [ H : assert_dec _ _ = inr _ |- _ ] => clear H
    end.

Ltac monad_inv :=
  try discriminate;
  repeat match goal with
    | [ H : (_ ;; _)%monad = _ |- _ ] => inv H
    | [ H : _ = (_ ;; _)%monad |- _ ] => inv H
    | [ H : inl _ = inl _ |- _ ] => inv H
    | [ H : inr _ = inr _ |- _ ] => inv H
    | [ H : ret _ = inr _ |- _ ] => inv H
    | [ H : inr _ = ret _ |- _ ] => inv H
    end;
  let E := fresh "E" in
  autodestruct_eqn E;
  cleanup
.

Lemma var_to_smt_value var (m : VerilogSMTBijection.t) tag regs ρ t :
    var_to_smt tag m var = inr t ->
    verilog_smt_match_states_partial (fun v => v = var) tag m regs ρ ->
    SMTLib.interp_term ρ t = (xbv <- regs var ;; bv <- XBV.to_bv xbv ;; ret (SMTLib.Value_BitVec _ bv))%monad.
Proof.
  intros Hsmt Hmatch.
  funelim (var_to_smt tag m var); try rewrite <- Heqcall in *; clear Heqcall; monad_inv.
  unfold verilog_smt_match_states_partial in *.
  insterU Hmatch.
  destruct Hmatch as [smtName [Heq2 [? ? ? ? Hmatchvals]]].
  inv Hmatchvals.
  replace n__smt with smtName in * by congruence.
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

Lemma bitOf_in_bounds n w (bv : BV.bitvector w) def :
  (n < w)%N ->
  RawXBV.bit_to_bool (XBV.bitOf (N.to_nat n) (XBV.from_bv bv)) = Some (List.nth (N.to_nat n) (BV.bits bv) def).
Proof.
  intros H.
  destruct bv as [bv wf].
  unfold XBV.from_bv, RawXBV.from_bv, XBV.bitOf, RawXBV.bitOf,
    BVList.RAWBITVECTOR_LIST.size in *.
  subst. simpl.
  erewrite List.nth_indep
    by (rewrite List.map_length; lia).
  rewrite List.map_nth.
  rewrite RawXBV.bit_to_bool_inverse.
  reflexivity.
Qed.

Lemma select_bit_no_exes:
  forall (w_val w_sel : N) (vec : BV.bitvector w_val) (idx : BV.bitvector w_sel),
    (BV.to_N idx < w_val)%N ->
    select_bit (XBV.from_bv vec) (XBV.from_bv idx) = XBV.from_bv (select_bit_bv vec idx).
Proof.
  intros.
  eapply XBV.to_bv_injective.
  - apply select_bit_to_bv.
    assumption.
  - apply XBV.xbv_bv_inverse.
Qed.

Equations convert_bv {from} (to : N) (value : BV.bitvector from) : BV.bitvector to :=
  convert_bv to value with dec (from < to)%N := {
    | left Hlt => rew _ in BV.bv_concat (BV.zeros (to - from)%N) value
    | right Hge with dec (from > to)%N => {
      | left Hgr => BV.bv_extr 0 to value;
      | right Hle => rew _ in value
      }
    }.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

Lemma convert_no_exes w_from w_to (from : BV.bitvector w_from) :
  convert w_to (XBV.from_bv from) = XBV.from_bv (convert_bv w_to from).
Proof.
  funelim (convert w_to (XBV.from_bv from));
    destruct_rew; rewrite <- Heqcall; clear Heqcall.
  - rewrite XBV.zeros_from_bv.
    rewrite xbv_concat_no_exes.
    funelim (convert_bv (to - from + from) from0); [|lia|lia].
    rewrite <- Heqcall in *; clear Heqcall.
    apply XBV.of_bits_equal.
    destruct_rew.
    repeat f_equal.
    crush.
  - rewrite XBV.extr_no_exes by crush.
    funelim (convert_bv to from0); [lia| |lia].
    rewrite <- Heqcall in *; clear Heqcall.
    reflexivity.
  - funelim (convert_bv from from0); [lia|lia|].
    rewrite <- Heqcall in *; clear Heqcall.
    now rewrite <- eq_rect_eq.
Qed.

Lemma convert_from_bv w_from w_to (from : BV.bitvector w_from) :
  exists bv : BV.bitvector w_to, XBV.to_bv (convert w_to (XBV.from_bv from)) = Some bv.
Proof.
  funelim (convert w_to (XBV.from_bv from));
    destruct_rew; rewrite <- Heqcall; clear Heqcall.
  - rewrite XBV.zeros_from_bv, XBV.concat_to_bv.
    eauto.
  - rewrite XBV.extr_no_exes by crush.
    rewrite XBV.xbv_bv_inverse.
    eauto.
  - rewrite XBV.xbv_bv_inverse.
    eauto.
Qed.

Lemma eval_binop_to_bv op w (lhs rhs : BV.bitvector w) :
  exists bv, XBV.to_bv (eval_binop op (XBV.from_bv lhs) (XBV.from_bv rhs)) = Some bv.
Proof.
  destruct op; simp eval_binop;
    match goal with
      | [ |- context[bv_binop ?op ?l ?r] ] =>
        funelim (bv_binop op l r);
        rewrite <- Heqcall; clear Heqcall;
        rewrite XBV.xbv_bv_inverse in *;
        crush
      | _ => idtac
    end.
  - (* andb *)
    erewrite bitwise_and_no_exes;
      try erewrite XBV.xbv_bv_inverse;
      try crush.
  - (* orb *)
    erewrite bitwise_or_no_exes;
      try erewrite XBV.xbv_bv_inverse;
      try crush.
  - (* shift right *)
    rewrite XBV.to_N_from_bv.
    simpl.
    rewrite shr_to_bv.
    eauto.
  - (* shift left *)
    rewrite XBV.to_N_from_bv.
    simpl.
    rewrite shl_to_bv.
    eauto.
  - (* shift left (arithmetic) *)
    rewrite XBV.to_N_from_bv.
    simpl.
    rewrite shl_to_bv.
    eauto.
Qed.

Lemma eval_binop_no_exes op w (lhs rhs : BV.bitvector w) :
  exists bv, eval_binop op (XBV.from_bv lhs) (XBV.from_bv rhs) = XBV.from_bv bv.
Proof.
  edestruct eval_binop_to_bv as [bv Hbv].
  exists bv.
  apply XBV.bv_xbv_inverse in Hbv.
  crush.
Qed.

Lemma eval_unop_to_bv op w (e : BV.bitvector w) :
  exists bv, XBV.to_bv (eval_unaryop op (XBV.from_bv e)) = Some bv.
Proof.
  destruct op; simp eval_unaryop.
  - rewrite XBV.xbv_bv_inverse. eauto.
Qed.

Lemma eval_unop_no_exes op w (e : BV.bitvector w) :
  exists bv, eval_unaryop op (XBV.from_bv e) = XBV.from_bv bv.
Proof.
  edestruct eval_unop_to_bv as [bv Hbv].
  exists bv.
  apply XBV.bv_xbv_inverse in Hbv.
  crush.
Qed.

Lemma eval_conditional_no_exes w_cond w (cond : BV.bitvector w_cond) (ifT ifF : BV.bitvector w) :
  exists bv, eval_conditional (XBV.from_bv cond) (XBV.from_bv ifT) (XBV.from_bv ifF) = XBV.from_bv bv.
Proof.
  unfold eval_conditional.
  rewrite XBV.xbv_bv_inverse.
  crush.
Qed.

Ltac unpack_defined_value_for :=
  repeat match goal with
    | [ H: defined_value_for (fun _ => _ \/ _) _ |- _ ] =>
        rewrite <- defined_value_for_split_iff in H;
        destruct H
    | [ H: defined_value_for (fun _ => List.In _ (_ ++ _)) _ |- _ ] =>
        setoid_rewrite List.in_app_iff in H
    end.

Ltac unpack_verilog_smt_match_states_partial :=
  repeat match goal with
    | [ H: verilog_smt_match_states_partial (fun _ => _ \/ _) _ _ _ _ |- _ ] =>
        apply verilog_smt_match_states_partial_split_iff in H;
        destruct H
    | [ H: verilog_smt_match_states_partial (fun _ => List.In _ (_ ++ _)) _ _ _ _ |- _ ] =>
        setoid_rewrite List.in_app_iff in H
    end.

Lemma eval_expr_defined w regs e :
  forall tag m t,
    expr_to_smt tag m e = inr t ->
    defined_value_for (fun v => List.In v (Verilog.expr_reads e)) regs ->
    exists bv, eval_expr (w:=w) regs e = Some (XBV.from_bv bv).
Proof.
  induction e; intros * Hexpr_to_smt Hdefined;
    simp expr_to_smt eval_expr expr_reads in *;
    simpl in *; monad_inv;
    unpack_defined_value_for;
    repeat match goal with
      | [ IH : context[defined_value_for _ _ -> exists _, _] |- _ ] =>
          let IH' := fresh "IH" in
          edestruct IH as [? IH']; eauto; clear IH; inv IH'
      end.
  - (* binop *)
    edestruct eval_binop_no_exes as [bv Hbv].
    exists bv. now rewrite Hbv.
  - (* unop *)
    edestruct eval_unop_no_exes as [bv Hbv].
    exists bv. now rewrite Hbv.
  - (* conditional *)
    edestruct eval_conditional_no_exes as [bv Hbv].
    exists bv. now rewrite Hbv.
  - (* bit select *)
    eapply statically_in_bounds_max_bound in s; eauto using XBV.to_N_from_bv.
    rewrite select_bit_no_exes by assumption.
    eauto.
  - (* concat *)
    rewrite xbv_concat_no_exes.
    eauto.
  - (* literal *)
    eauto.
  - (* variable *)
    unfold defined_value_for in *.
    edestruct H as [? [H1 H2]]; eauto; [idtac].
    rewrite XBV.not_has_x_to_bv in H2.
    destruct H2 as [bv Hbv].
    apply XBV.to_from_bv_inverse in Hbv. subst.
    eauto.
  - rewrite convert_no_exes.
    eauto.
Qed.

Lemma eval_expr_no_exes w regs e :
  forall xbv tag m t,
    defined_value_for (fun v => List.In v (Verilog.expr_reads e)) regs ->
    expr_to_smt tag m e = inr t ->
    eval_expr (w:=w) regs e = Some xbv ->
    exists bv, XBV.to_bv xbv = Some bv.
Proof.
  intros * Hdefined Hexpr_to_smt Heval.
  eapply eval_expr_defined in Hexpr_to_smt; try eassumption.
  rewrite Heval in Hexpr_to_smt.
  destruct Hexpr_to_smt as [? H]. inv H.
  rewrite XBV.xbv_bv_inverse. eauto.
Qed.

Lemma binop_to_smt_value ρ op w smt_lhs smt_rhs t val_lhs val_rhs val :
    SMTLib.interp_term ρ smt_lhs = Some (SMTLib.Value_BitVec w val_lhs) ->
    SMTLib.interp_term ρ smt_rhs = Some (SMTLib.Value_BitVec w val_rhs) ->
    binop_to_smt op smt_lhs smt_rhs = inr t ->
    XBV.to_bv (eval_binop op (XBV.from_bv val_lhs) (XBV.from_bv val_rhs)) = Some val ->
    SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec (Verilog.binop_width op w) val).
Proof.
  intros Hinterp_lhs Hinterp_rhs Hbinop_to_smt Heval.
  destruct op;
    simp eval_binop binop_to_smt in *; inv Hbinop_to_smt;
    simpl; rewrite Hinterp_lhs; rewrite Hinterp_rhs; autodestruct; try contradiction;
    repeat f_equal; rewrite <- eq_rect_eq.
  - simp bv_binop in *. rewrite ! XBV.xbv_bv_inverse in *. simpl in *.
    rewrite XBV.xbv_bv_inverse in *. now some_inv.
  - simp bv_binop in *. rewrite ! XBV.xbv_bv_inverse in *. simpl in *.
    rewrite XBV.xbv_bv_inverse in *. now some_inv.
  - simp bv_binop in *. rewrite ! XBV.xbv_bv_inverse in *. simpl in *.
    rewrite XBV.xbv_bv_inverse in *. now some_inv.
  - erewrite bitwise_and_no_exes in Heval;
      rewrite XBV.xbv_bv_inverse in *;
      (reflexivity || now some_inv).
  - erewrite bitwise_or_no_exes in Heval;
      rewrite XBV.xbv_bv_inverse in *;
      (reflexivity || now some_inv).
  - rewrite XBV.to_N_from_bv in *. simpl in *.
    erewrite shr_to_bv in *.
    now some_inv.
  - rewrite XBV.to_N_from_bv in *. simpl in *.
    erewrite shl_to_bv in *.
    now some_inv.
  - rewrite XBV.to_N_from_bv in *. simpl in *.
    erewrite shl_to_bv in *.
    now some_inv.
Qed.

Lemma unaryop_to_smt_value ρ op w smt_expr t val_expr val :
    SMTLib.interp_term ρ smt_expr = Some (SMTLib.Value_BitVec w val_expr) ->
    unaryop_to_smt op smt_expr = inr t ->
    XBV.to_bv (eval_unaryop op (XBV.from_bv val_expr)) = Some val ->
    SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec (Verilog.unop_width op w) val).
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
  funelim (convert_bv w_to val_from);
    rewrite <- Heqcall in *; clear Heqcall.
  - funelim (cast_from_to from to smt_from);
      rewrite <- Heqcall in *; clear Heqcall;
      [ rewrite N.compare_eq_iff in *; lia
      | rewrite N.compare_lt_iff in *; lia
      |idtac].
    rewrite N.compare_gt_iff in *.
    simpl. rewrite Hinterp_from.
    f_equal.
    apply value_bitvec_bits_equal.
    destruct_rew.
    repeat f_equal. lia.
  - funelim (cast_from_to from to smt_from);
      rewrite <- Heqcall in *; clear Heqcall;
      [ rewrite N.compare_eq_iff in *; lia
      | rewrite N.compare_lt_iff in *
      | rewrite N.compare_gt_iff in *; lia ].
    simpl. rewrite Hinterp_from.
    f_equal.
    apply value_bitvec_bits_equal.
    simpl.
    repeat f_equal. lia.
  - funelim (cast_from_to from to smt_from);
      rewrite <- Heqcall in *; clear Heqcall;
      [ rewrite N.compare_eq_iff in *
      | rewrite N.compare_lt_iff in *; lia
      | rewrite N.compare_gt_iff in *; lia ].
    simpl. rewrite Hinterp_from.
    f_equal.
    apply value_bitvec_bits_equal.
    destruct_rew.
    reflexivity.
Qed.

Lemma rawbv_shr_as_select w vec idx :
  (RawBV.size vec >= 1)%N ->
  RawBV.size vec = RawBV.size idx ->
  w = RawBV.size vec ->
  RawBV.bv_extr 0 1 w (RawBV.bv_shr vec idx) =
    [RawBV.bitOf (RawBV.list2nat_be idx) vec]%list.
Proof.
  intros H1 H2 Heq. subst w.
  assert (RawBV.size (RawBV.bv_shr vec idx) = RawBV.size vec) as H
      by eauto using RawBV.bv_shr_size.
  rewrite <- H.
  rewrite rawbv_extr_one_bit; try crush.
  f_equal.
  unfold RawBV.bv_shr. replace (RawBV.size idx). rewrite N.eqb_refl.
  unfold RawBV.shr_be. simpl.
  unfold RawBV.size in *.
  generalize (RawBV.list2nat_be idx). clear idx H2 H. intro n.
  destruct n, vec; try crush. clear H1.
  unfold RawBV.bitOf.
  rewrite RawBV.shr_be_nicify. simp nice_nshr_be. simpl. clear b.
  funelim (RawBV.nice_nshr_be vec n); simp nice_nshr_be; try crush.
  destruct (RawBV.nice_nshr_be bs n); crush.
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
  f_equal.
  apply value_bitvec_bits_equal.
  destruct_rew.
  rewrite rawbv_shr_as_select by admit.
  rewrite bit_of_as_bv in Heval by lia.
  fold (List.map RawXBV.bool_to_bit [BV.bitOf (n:=w_vec) (N.to_nat (BV.to_N val_idx)) val_vec]) in Heval.
  fold (RawXBV.from_bv [BV.bitOf (n:=w_vec) (N.to_nat (BV.to_N val_idx)) val_vec]) in Heval.
  destruct val as [[ | hd [ | ? ? ] ] val_wf]; [crush| |crush].
  apply XBV.bv_xbv_inverse in Heval.
  simpl in *.
  admit.
Admitted.

Lemma expr_to_smt_value w expr : forall (m : VerilogSMTBijection.t) tag regs ρ t,
    expr_to_smt tag m expr = inr t ->
    verilog_smt_match_states_partial
      (fun v => List.In v (Verilog.expr_reads expr))
      tag m regs ρ ->
    SMTLib.interp_term ρ t =
      (xbv <- eval_expr (w:=w) regs expr ;;
       bv <- XBV.to_bv xbv ;;
       ret (SMTLib.Value_BitVec _ bv))%monad
.
Proof.
  induction expr; intros * Hexpr_to_smt Hmatch;
    simp expr_reads expr_to_smt eval_expr in *;
    unpack_verilog_smt_match_states_partial.
  - (* binop *)
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
    edestruct eval_binop_to_bv as [bv Hbv].
    rewrite Hbv.
    now eauto using binop_to_smt_value.
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
  - (* Bitselect *)
    simpl in Hexpr_to_smt.
    repeat match type of Hexpr_to_smt with
    | context[match ?c with _ => _ end] =>
        let E := fresh "E" in
        destruct c eqn:E; try discriminate
    | inr _ = inr _ => inv Hexpr_to_smt
    | inl _ = inl _ => inv Hexpr_to_smt
    end.
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
        eauto using statically_in_bounds_max_bound, XBV.to_N_from_bv.
      }
      now rewrite XBV.xbv_bv_inverse.
    + rewrite select_bit_no_exes; cycle 1. {
        eauto using statically_in_bounds_max_bound, XBV.to_N_from_bv.
      }
      now rewrite XBV.xbv_bv_inverse.
    + eauto using statically_in_bounds_max_bound, XBV.to_N_from_bv.
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
    rewrite xbv_concat_to_bv.
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
    replace n__smt with smtName in * by congruence.
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
    erewrite cast_from_to_value; eauto; [idtac].
    rewrite convert_no_exes.
    rewrite XBV.xbv_bv_inverse.
    reflexivity.
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
