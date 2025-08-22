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

Lemma xbv_concat_to_bv w1 w2 (bv1 : BV.bitvector w1) (bv2 : BV.bitvector w2) :
  XBV.to_bv (XBV.concat (XBV.from_bv bv1) (XBV.from_bv bv2)) =
    Some (BV.bv_concat bv1 bv2).
Proof.
  rewrite <- XBV.xbv_bv_inverse.
  f_equal.
  destruct bv1 as [bv1 wf1], bv2 as [bv2 wf2].
  apply XBV.of_bits_equal. simpl.
  unfold RawBV.bv_concat, RawXBV.from_bv.
  rewrite <- List.map_app.
  reflexivity.
Qed.

Ltac funelim_plus e :=
  funelim e; destruct_rew;
  match goal with
  | [ Heqcall : _ = e |- _] => rewrite <- Heqcall; clear Heqcall
  | _ => idtac e
  end.

Lemma smt_select_bit_is_bit ρ w_vec vec w_idx idx val :
    SMTLib.interp_term ρ (smt_select_bit w_vec vec w_idx idx) = Some val ->
    exists bit, val = SMTLib.Value_BitVec 1 (BV.of_bits [bit]).
Proof.
  intros H. cbn in H. autodestruct_eqn E.
  destruct (BVList.BITVECTOR_LIST.bv_extr 0 1 (BVList.BITVECTOR_LIST.bv_shr _ _)) as [bv_bit wf_bit].
  do 2 (destruct bv_bit; try crush).
  eexists. f_equal. apply BV.of_bits_equal. reflexivity.
Qed.

Lemma cast_from_to_part_eval ρ from to t val1 :
    SMTLib.interp_term ρ (cast_from_to from to t) = Some val1 ->
    (exists val2, SMTLib.interp_term ρ t = Some val2).
Proof.
  intros H.
  funelim (cast_from_to from to t); rewrite <- Heqcall in *; clear Heqcall.
  - eauto.
  - cbn in H. autodestruct_eqn E. eauto.
  - cbn in H. autodestruct_eqn E. eauto.
Qed.

Lemma smt_select_bit_part_eval_vec ρ w_vec vec w_idx idx val1 :
    SMTLib.interp_term ρ (smt_select_bit w_vec vec w_idx idx) = Some val1 ->
    (exists val2, SMTLib.interp_term ρ vec = Some val2).
Proof.
  intros H. cbn in H. autodestruct_eqn E.
  eauto using cast_from_to_part_eval.
Qed.

Lemma smt_select_bit_part_eval_idx ρ w_vec vec w_idx idx val1 :
    SMTLib.interp_term ρ (smt_select_bit w_vec vec w_idx idx) = Some val1 ->
    (exists val2, SMTLib.interp_term ρ idx = Some val2).
Proof.
  intros H. cbn in H. autodestruct_eqn E.
  eauto using cast_from_to_part_eval.
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

Equations nice_nshr_be : list bool -> nat -> list bool :=
  nice_nshr_be [] _ := [];
  nice_nshr_be bs 0 := bs;
  nice_nshr_be (b :: bs) (S n) := nice_nshr_be bs n ++ [false].

Lemma shr_be_nicify bs n :
  RawBV.nshr_be bs n = nice_nshr_be bs n.
Proof.
  funelim (nice_nshr_be bs n); simp nice_nshr_be in *; simpl in *.
  - induction n; crush.
  - reflexivity.
  - rewrite <- H. clear b H. revert bs.
    induction n; intros; try crush.
    simpl.
    replace (RawBV._shr_be (bs ++ [false])) with (RawBV._shr_be bs ++ [false])%list
      by (destruct bs; crush).
    eapply IHn.
Qed.

Lemma rawbv_shr_as_select vec idx :
  (RawBV.size vec >= 1)%N ->
  RawBV.size vec = RawBV.size idx ->
  RawBV.bv_extr 0 1 (RawBV.size vec) (RawBV.bv_shr vec idx) =
    [RawBV.bitOf (RawBV.list2nat_be idx) vec]%list.
Proof.
  intros H1 H2.
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
  rewrite shr_be_nicify. simp nice_nshr_be. simpl. clear b.
  funelim (nice_nshr_be vec n); simp nice_nshr_be; try crush.
  destruct (nice_nshr_be bs n); crush.
Qed.

Lemma select_bit_to_bv w (vec idx : BV.bitvector w) :
  (BV.to_N idx < w)%N ->
  XBV.to_bv (select_bit (XBV.from_bv vec) (XBV.from_bv idx)) =
    Some (BV.bv_extr 0 1 (BV.bv_shr vec idx)).
Proof.
  intros Hidx.
  unfold select_bit.
  rewrite XBV.to_N_from_bv.
  repeat match goal with
         | [ bv : BV.bitvector _ |- _ ] => destruct bv
         end.
  rewrite <- XBV.xbv_bv_inverse. f_equal.
  apply XBV.of_bits_equal; simpl.
  rewrite <- wf0.
  rewrite rawbv_shr_as_select; try lia.
  unfold XBV.bitOf, BV.to_N, RawBV.to_N in *. simpl in *.
  rewrite Nat2N.id.
  f_equal.
  unfold RawBV.size in *.
  generalize dependent (RawBV.list2nat_be bv). clear wf bv. intros.
  unfold RawXBV.from_bv, RawXBV.bitOf, RawBV.bitOf in *.
  subst.
  rewrite List.nth_indep with (d':=O)
    by (rewrite List.map_length; lia).
  replace O with (RawXBV.bool_to_bit false)
    by reflexivity.
  apply List.map_nth.
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

Lemma value_bitvec_equal_inv n1 n2 bv1 bv2 :
  SMTLib.Value_BitVec n1 bv1 = SMTLib.Value_BitVec n2 bv2 ->
  BV.bits bv1 = BV.bits bv2.
Proof. now inversion 1. Qed.

Lemma cast_from_to_zextn ρ (from to : N) bv_from t :
  (to >= from)%N ->
  SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec from bv_from) ->
  SMTLib.interp_term ρ (cast_from_to from to t) = Some (SMTLib.Value_BitVec _ (BV.bv_concat (BV.zeros (to - from)) bv_from)).
Proof.
  intros.
  destruct bv_from as [bv_from bv_from_wf].
  funelim (cast_from_to from to t); rewrite <- Heqcall in *; clear Heqcall.
  - rewrite N.compare_eq_iff in *. subst.
    replace (SMTLib.interp_term ρ t).
    f_equal. apply value_bitvec_bits_equal.
    rewrite ! N.sub_diag. cbn.
    now rewrite List.app_nil_r.
  - rewrite N.compare_lt_iff in *. crush.
  - rewrite N.compare_gt_iff in *. crush.
Qed.

Corollary cast_from_to_zextn_inv ρ
  (from to : N)
  (bv_from : BV.bitvector from)
  bv_to t :
  (to >= from)%N ->
  SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec from bv_from) ->
  SMTLib.interp_term ρ (cast_from_to from to t) =
    Some (SMTLib.Value_BitVec _ bv_to) ->
  bv_to = BV.bv_concat (BV.zeros (to - from)) bv_from.
Proof.
  intros Hcmp Ht Hcast.
  erewrite cast_from_to_zextn in Hcast; try crush.
  inv Hcast. inversion_sigma. subst.
  now rewrite <- eq_rect_eq.
Qed.

Corollary cast_from_to_zextn_inv_bits ρ
  (from to : N)
  (bv_from : BV.bitvector from)
  (bv_to : BV.bitvector to)
  t :
  (to >= from)%N ->
  SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec from bv_from) ->
  SMTLib.interp_term ρ (cast_from_to from to t) =
    Some (SMTLib.Value_BitVec _ bv_to) ->
  BV.bits bv_to = BV.bits (BV.bv_concat (BV.zeros (to - from)) bv_from).
Proof.
  intros Hcmp Ht Hcast.
  erewrite cast_from_to_zextn in Hcast; try crush.
  inv Hcast. crush.
Qed.

Corollary cast_from_to_zextn_inv_width ρ
  (from to1 to2 : N)
  (bv_from : BV.bitvector from)
  (bv_to : BV.bitvector to2)
  t :
  (to1 > 0)%N ->
  SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec from bv_from) ->
  SMTLib.interp_term ρ (cast_from_to from to1 t) =
    Some (SMTLib.Value_BitVec to2 bv_to) ->
  to1 = to2.
Proof.
  intros Hcmp Ht Hcast.
  funelim (cast_from_to from to1 t); rewrite <- Heqcall in *; clear Heqcall.
  - rewrite N.compare_eq_iff in *. crush.
  - rewrite N.compare_lt_iff in *. crush.
  - rewrite N.compare_gt_iff in *. crush.
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

Lemma xbv_bitof_concat n1 n2 b (xbv1 : XBV.xbv n1) (xbv2 : XBV.xbv n2) :
  (N.of_nat b < n1)%N ->
  XBV.bitOf b (XBV.concat xbv2 xbv1) =
    XBV.bitOf b xbv1.
Proof.
  destruct xbv1 as [xbv1 wf1].
  subst.
  unfold XBV.bitOf, RawXBV.bitOf. simpl.
  intros.
  rewrite List.app_nth1; crush.
Qed.

Lemma select_bit_concat1
  n1 n2 n3 (vec1 : XBV.xbv n1) (vec2 : XBV.xbv n2) (idx : XBV.xbv n3) :
  opt_prop (fun n => n < n1)%N (XBV.to_N idx) ->
  select_bit (XBV.concat vec2 vec1) idx = select_bit vec1 idx.
Proof.
  unfold select_bit. intros H.
  destruct (XBV.to_N idx); simpl in *; try crush.
  rewrite xbv_bitof_concat by lia.
  reflexivity.
Qed.

Lemma select_bit_index_same_value
  n1 n2 n3 (vec : XBV.xbv n1) (idx1 : XBV.xbv n2) (idx2 : XBV.xbv n3) :
  XBV.to_N idx1 = XBV.to_N idx2 ->
  select_bit vec idx1 = select_bit vec idx2.
Proof. unfold select_bit. intros. crush. Qed.

Lemma from_bv_concat n1 n2 (bv1 : BV.bitvector n1) (bv2 : BV.bitvector n2) :
  XBV.from_bv (BV.bv_concat bv1 bv2) = XBV.concat (XBV.from_bv bv1) (XBV.from_bv bv2).
Proof.
  repeat match goal with
         | [ bv : BV.bitvector _ |- _ ] => destruct bv
         end.
  subst.
  apply XBV.of_bits_equal. simpl.
  unfold RawBV.bv_concat, RawXBV.from_bv.
  apply List.map_app.
Qed.

Lemma cast_from_to_up_same_value ρ t from to1 to2 bv1 bv2 :
  (to1 >= from)%N ->
  SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec from bv1) ->
  SMTLib.interp_term ρ (cast_from_to from to1 t) = Some (SMTLib.Value_BitVec to2 bv2) ->
  BV.to_N bv1 = BV.to_N bv2.
Proof.
  intros.
  erewrite cast_from_to_zextn in *; try crush.
  some_inv; rewrite BV.bv_zextn_to_N; crush.
Qed.

Lemma cast_from_to_up_as_concat ρ t from to1 to2 bv1 bv2 :
  (to1 >= from)%N ->
  SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec from bv1) ->
  SMTLib.interp_term ρ (cast_from_to from to1 t) = Some (SMTLib.Value_BitVec to2 bv2) ->
  exists w, (_; bv2) = (_; BV.bv_concat (BV.zeros w) bv1).
Proof.
  intros Hcmp H1 H2.
  funelim (cast_from_to from to1 t); rewrite <- Heqcall in *; clear Heqcall;
    rewrite N.compare_eq_iff in * || rewrite  N.compare_lt_iff in * || rewrite N.compare_gt_iff in *.
  - subst.
    rewrite H1 in H2. clear H1. inv H2.
    exists 0%N. cbn. f_equal.
    apply BV.of_bits_equal. destruct bv1.
    cbn. now rewrite List.app_nil_r.
  - crush.
  - crush.
Qed.

Lemma bitselect_impl_correct:
  forall (w0 w1 : N) (t0 t1 : SMTLib.term) (ρ : SMTLib.valuation)
    (w : N) (bv1ext bv0ext : BVList.BITVECTOR_LIST.bitvector w) (bv1 : BV.bitvector w1) (bv0 : BV.bitvector w0),
    (BV.to_N bv1 < w0)%N ->
    SMTLib.interp_term ρ t0 = Some (SMTLib.Value_BitVec w0 bv0) ->
    SMTLib.interp_term ρ t1 = Some (SMTLib.Value_BitVec w1 bv1) ->
    SMTLib.interp_term ρ (cast_from_to w0 (N.max w0 w1) t0) = Some (SMTLib.Value_BitVec w bv0ext) ->
    SMTLib.interp_term ρ (cast_from_to w1 (N.max w0 w1) t1) = Some (SMTLib.Value_BitVec w bv1ext) ->
    XBV.to_bv (select_bit (XBV.from_bv bv0) (XBV.from_bv bv1)) =
      Some (BVList.BITVECTOR_LIST.bv_extr 0 1  (BVList.BITVECTOR_LIST.bv_shr bv0ext bv1ext)).
Proof.
  intros * Hbounds Ht0 Ht1 Hcast0 Hcast1.
  rewrite <- select_bit_to_bv; cycle 1. {
    erewrite <- cast_from_to_up_same_value with (bv1:=bv1) (bv2:=bv1ext);
      try crush; try lia.
    replace w with (N.max w0 w1)
      by (eapply cast_from_to_zextn_inv_width with (t:=t0); crush).
    lia.
  }

  f_equal.

  transitivity (select_bit (XBV.from_bv bv0ext) (XBV.from_bv bv1)). {
    edestruct cast_from_to_up_as_concat with (t:=t0); [|eassumption|eassumption|]. lia.
    inv H.
    repeat (apply_somewhere inj_pair2; subst).
    rewrite from_bv_concat.
    symmetry. apply select_bit_concat1.
    rewrite XBV.to_N_from_bv. simpl.
    lia.
  }

  eapply select_bit_index_same_value. {
    erewrite cast_from_to_zextn in *; try crush.
    some_inv; now rewrite ! XBV.to_N_from_bv, BV.bv_zextn_to_N.
  }
Qed.

Lemma cast_from_to_correct ρ t from to bv1 v2 :
  (to > 0)%N ->
  SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec from bv1) ->
  SMTLib.interp_term ρ (cast_from_to from to t) = Some v2 ->
  verilog_smt_match_value (convert to (XBV.from_bv bv1)) v2.
Proof.
  intros Hnz Ht Hcast.

  (* expr_begin_tac. *)
  funelim (convert to (XBV.from_bv bv1)); destruct_rew; rewrite <- Heqcall; clear Heqcall.
  + (* Extension *)
    funelim (cast_from_to from to t); rewrite <- Heqcall in *; clear Heqcall;
      (rewrite N.compare_eq_iff in *|| rewrite N.compare_lt_iff in * || rewrite N.compare_gt_iff in * );
      try crush.
    cbn in *; autodestruct_eqn E.
    apply_somewhere inj_pair2. subst.
    eapply verilog_smt_match_to_bv_bits; eauto.
    rewrite XBV.zeros_from_bv.
    apply XBV.concat_to_bv.
  + (* Truncation *)
    funelim (cast_from_to from to t); rewrite <- Heqcall in *; clear Heqcall;
      (rewrite N.compare_eq_iff in *|| rewrite N.compare_lt_iff in * || rewrite N.compare_gt_iff in * );
      try crush.
    cbn in *; autodestruct_eqn E.
    apply_somewhere inj_pair2. subst.
    eapply verilog_smt_match_to_bv_bits.
    * apply XBV.extr_to_bv. lia.
    * simpl. f_equal. lia.
  + funelim (cast_from_to from from t); rewrite <- Heqcall in *; clear Heqcall;
      (rewrite N.compare_eq_iff in *|| rewrite N.compare_lt_iff in * || rewrite N.compare_gt_iff in * );
      try crush.
    rewrite Ht in Hcast. inv Hcast.
    constructor.
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
  generalize (RawBV.list2nat_be shamt). clear shamt. intro i.
  revert vec.
  induction i; intros.
  - simp shl. crush.
  - simpl.
    rewrite <- IHi. clear IHi.
    admit.
Admitted.

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

Lemma binop_to_smt_correct {w} :
  forall op t (m : VerilogSMTBijection.t) regs ρ lhs lhs_smt xbv_lhs bv_lhs rhs rhs_smt xbv_rhs bv_rhs xbv bv,
    eval_expr regs lhs = Some xbv_lhs ->
    SMTLib.interp_term ρ lhs_smt = Some bv_lhs ->
    verilog_smt_match_value (w:=w) xbv_lhs bv_lhs ->

    eval_expr regs rhs = Some xbv_rhs ->
    SMTLib.interp_term ρ rhs_smt = Some bv_rhs ->
    verilog_smt_match_value (w:=w) xbv_rhs bv_rhs ->

    eval_binop op xbv_lhs xbv_rhs = xbv ->
    SMTLib.interp_term ρ t = Some bv ->
    binop_to_smt op lhs_smt rhs_smt = inr t ->

    verilog_smt_match_value xbv bv.
Proof.
  Ltac inv_match_values :=
    repeat match goal with
      | [ H : context[verilog_smt_match_value _ _] |- _ ] => (insterU H || inv H)
      end.

  Ltac inv_dep_pairs :=
    repeat match goal with
    | [ H : {| pr1 := _; pr2 := _ |} = {| pr1 := _; pr2 := _ |} |- _ ] => inv H
    | [ H : (?x; _) = (?x; _) |- _ ] => apply inj_pair2 in H; subst
    end.

  intros.
  destruct op;
  (* funelim (binop_to_smt op lhs_smt rhs_smt); *)
    try discriminate;
    repeat (simp binop_to_smt eval_binop in *; simpl in *; autodestruct_eqn E);
    inv_match_values;
    inv_dep_pairs.
  - simp bv_binop. rewrite ! XBV.xbv_bv_inverse. constructor.
  - simp bv_binop. rewrite ! XBV.xbv_bv_inverse. constructor.
  - simp bv_binop. rewrite ! XBV.xbv_bv_inverse. constructor.
  - apply verilog_smt_match_to_bv.
    erewrite bitwise_and_no_exes
      by (rewrite XBV.xbv_bv_inverse in *; crush).
    rewrite ! XBV.xbv_bv_inverse.
    crush.
  - apply verilog_smt_match_to_bv.
    erewrite bitwise_or_no_exes
      by (rewrite XBV.xbv_bv_inverse in *; crush).
    rewrite ! XBV.xbv_bv_inverse.
    crush.
  - (* Shift right *)
    apply verilog_smt_match_to_bv.
    rewrite ! XBV.to_N_from_bv. simpl.
    apply shr_to_bv.
  - (* Shift left *)
    apply verilog_smt_match_to_bv.
    rewrite ! XBV.to_N_from_bv. simpl.
    apply shl_to_bv.
  - (* Shift left (arithmetic) *)
    apply verilog_smt_match_to_bv.
    rewrite ! XBV.to_N_from_bv. simpl.
    apply shl_to_bv.
Qed.

Lemma binop_to_smt_eval_left ρ op l r t bv :
  binop_to_smt op l r = inr t ->
  SMTLib.interp_term ρ t = Some bv ->
  (exists bv', SMTLib.interp_term ρ l = Some bv').
Proof.
  intros * H1 H2.
  destruct op; simp binop_to_smt in *;
    inv H1; crush.
Qed.

Lemma binop_to_smt_eval_right ρ op l r t bv :
  binop_to_smt op l r = inr t ->
  SMTLib.interp_term ρ t = Some bv ->
  (exists bv', SMTLib.interp_term ρ r = Some bv').
Proof.
  intros * H1 H2.
  destruct op; simp binop_to_smt in *;
    inv H1; crush.
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

Lemma expr_to_smt_correct {w} tag m (expr : Verilog.expression w) :
  forall t regs ρ xbv bv,
    expr_to_smt tag m expr = inr t ->
    verilog_smt_match_states tag m regs ρ ->
    eval_expr regs expr = Some xbv ->
    SMTLib.interp_term ρ t = Some bv ->
    verilog_smt_match_value xbv bv.
Proof.
  Ltac inster_all :=
    unshelve (repeat match goal with
      | [ H : context[verilog_smt_match_value _ _] |- _ ] => (insterU H || inv H)
      | [ H : {| pr1 := _; pr2 := _ |} = {| pr1 := _; pr2 := _ |} |- _ ] => inv H
      | [ H : (?x; _) = (?x; _) |- _ ] => apply inj_pair2 in H; subst
      end); try crush.

  Ltac expr_begin_tac :=
    match goal with
    | [ Heval_expr: eval_expr _ _ = Some _ , Hinterp_term : SMTLib.interp_term _ _ = Some _ |- _ ] =>
        cbn in Hinterp_term;
        simp eval_expr in Heval_expr; inv Heval_expr;
        let E := fresh "E" in
        autodestruct_eqn E
    end; inster_all.

  Ltac bv_binop_tac :=
    apply verilog_smt_match_to_bv;
    simp eval_binop in *;
    match goal with
      [ |- context[bv_binop ?op ?l ?r] ] =>
        funelim (bv_binop op l r);
        match goal with
          [ Heqcall': _ = bv_binop op l r |- _ ] =>
            rewrite <- Heqcall' in *;
            clear Heqcall';
            repeat apply_somewhere XBV.to_from_bv_inverse;
            subst
        end;
        rewrite XBV.xbv_bv_inverse in *;
        repeat apply_somewhere XBV.from_bv_injective;
        subst;
        try crush
    end.

  funelim (expr_to_smt tag m expr); intros * Hexpr_to_smt Hmatch_states Heval_expr Hinterp_term;
    simp expr_to_smt in *; inv Hexpr_to_smt; autodestruct_eqn E.
  - simp eval_expr in Heval_expr. inv Heval_expr. autodestruct_eqn E.
    edestruct binop_to_smt_eval_left with (t:=t); eauto.
    edestruct binop_to_smt_eval_right with (t:=t); eauto.
    expr_begin_tac; [idtac].
    eapply binop_to_smt_correct with (lhs:=lhs) (rhs:=rhs) (lhs_smt:=t0) (rhs_smt:=t1);
      (eauto || constructor).
  - destruct op.
    + simp eval_expr in Heval_expr. inv Heval_expr. autodestruct_eqn E.
      simp unaryop_to_smt in *.
  - (* Conditional *)
    expr_begin_tac;
      try solve [eauto];
      try rewrite Bool.negb_true_iff in *;
      try rewrite Bool.negb_false_iff in *.
    + (* Contradiction 0 <> 0 *)
      apply_somewhere XBV.bv_xbv_inverse.
      apply_somewhere XBV.from_bv_injective.
      subst.
      unfold Verilog.expr_type, SMTLib.value_eqb, BV.is_zero in *.
      autodestruct; try contradiction.
      destruct e.
      crush.
    + (* Condition is X *)
      some_inv; now rewrite XBV.xbv_bv_inverse in *.
    + (* Condition is X *)
      some_inv; now rewrite XBV.xbv_bv_inverse in *.
    + (* Contradiction 0 <> 0 *)
      apply_somewhere XBV.bv_xbv_inverse.
      apply_somewhere XBV.from_bv_injective.
      subst.
      unfold Verilog.expr_type, SMTLib.value_eqb, BV.is_zero in *.
      autodestruct; try contradiction.
      destruct e.
      crush.
    + now rewrite XBV.xbv_bv_inverse in *.
    + now rewrite XBV.xbv_bv_inverse in *.
  - (* BitSelect *)
    clear E.
    unfold smt_select_bit in *.
    edestruct (smt_select_bit_part_eval_idx); eauto.
    edestruct (smt_select_bit_part_eval_vec); eauto.
    expr_begin_tac; [idtac].
    cbn in Hinterp_term; autodestruct_eqn E.
    apply verilog_smt_match_to_bv.
    unfold Verilog.expr_type in *.

    eapply bitselect_impl_correct; try eassumption. {
      eapply statically_in_bounds_max_bound; eauto.
      eapply XBV.to_N_from_bv.
    }
  - (* Concatenation *)
    expr_begin_tac; [idtac].
    apply verilog_smt_match_to_bv.
    apply xbv_concat_to_bv.
  - (* Verilog.IntegerLiteral *)
    expr_begin_tac; [idtac].
    now constructor.
  - (* Verilog.NamedExpression *)
    funelim (var_to_smt tag m var); rewrite <- Heqcall in *; try discriminate; clear Heqcall.
    monad_inv.
    destruct Hmatch_states with (verilogName := var) (smtName := n__smt); eauto.
    expr_begin_tac; [idtac].
    replace bv with (SMTLib.Value_BitVec (Verilog.varType var) bv0) by congruence.
    replace (regs var) in Hverilogval. inv Hverilogval.
    econstructor.
  - (* Resize *)
    unfold Verilog.expr_type in *.
    edestruct (cast_from_to_part_eval); eauto.
    expr_begin_tac; [idtac].
    eapply cast_from_to_correct; eauto.
Qed.

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
  forall (w_val w_sel : N) (vec : XBV.xbv w_val) (idx : XBV.xbv w_sel) vec_bv idx_val,
    XBV.to_bv vec = Some vec_bv ->
    XBV.to_N idx = Some idx_val ->
    (idx_val < w_val)%N ->
    exists bv : BV.bitvector 1, XBV.to_bv (select_bit vec idx) = Some bv.
Proof.
  intros * Hvec Hidx Hmax.
  apply XBV.to_from_bv_inverse in Hvec. subst.
  unfold select_bit. rewrite Hidx. clear Hidx.
  pose proof bitOf_in_bounds.
Admitted.

Lemma convert_from_bv w_from w_to (from : BV.bitvector w_from) :
  exists bv : BV.bitvector w_to, XBV.to_bv (convert w_to (XBV.from_bv from)) = Some bv.
Proof.
  funelim (convert w_to (XBV.from_bv from));
    destruct_rew; rewrite <- Heqcall; clear Heqcall.
  - rewrite XBV.zeros_from_bv, XBV.concat_to_bv.
    crush.
  - rewrite XBV.extr_to_bv by crush.
    crush.
  - rewrite XBV.xbv_bv_inverse.
    crush.
Qed.

(* FIXME: The following two (admitted) expr_to_smt lemmas are (likely) *almost*
   correct, but they are missing a condition about their input state not having
   any Xs.

   I need to find a way to thread the "no exes in the state" invariant through
   the proof. Actually, all I really need is "no exes in the inputs", but that
   might not be that different.
 *)

Lemma eval_binop_no_exes op w (lhs rhs : BV.bitvector w) :
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

Lemma eval_unop_no_exes op w (e : BV.bitvector w) :
  exists bv, XBV.to_bv (eval_unaryop op (XBV.from_bv e)) = Some bv.
Proof.
  destruct op; simp eval_unaryop.
  - rewrite XBV.xbv_bv_inverse. eauto.
Qed.

Lemma eval_expr_no_exes w regs e :
  forall xbv tag m t,
    defined_value_for (fun v => List.In v (Verilog.expr_reads e)) regs ->
    expr_to_smt tag m e = inr t ->
    eval_expr (w:=w) regs e = Some xbv ->
    exists bv, XBV.to_bv xbv = Some bv.
Proof.
  induction e; intros * Hdefined Hexpr_to_smt Heval;
    simp expr_to_smt eval_expr expr_reads in *;
    simpl in *; monad_inv.
  - (* binop *)
    repeat setoid_rewrite List.in_app_iff in Hdefined.
    rewrite <- defined_value_for_split_iff in Hdefined.
    destruct Hdefined as [? ?].
    edestruct IHe1; eauto.
    edestruct IHe2; eauto.
    repeat apply_somewhere XBV.to_from_bv_inverse. subst.
    apply eval_binop_no_exes.
  - (* unop *)
    edestruct IHe; eauto.
    repeat apply_somewhere XBV.to_from_bv_inverse. subst.
    apply eval_unop_no_exes.
  - (* conditional (false) *)
    repeat setoid_rewrite List.in_app_iff in Hdefined.
    rewrite <- ! defined_value_for_split_iff in Hdefined.
    destruct Hdefined as [? [? ?]].
    eapply IHe3; eauto.
  - (* conditional (true) *)
    repeat setoid_rewrite List.in_app_iff in Hdefined.
    rewrite <- ! defined_value_for_split_iff in Hdefined.
    destruct Hdefined as [? [? ?]].
    eapply IHe2; eauto.
  - (* conditional (X) *)
    repeat setoid_rewrite List.in_app_iff in Hdefined.
    rewrite <- ! defined_value_for_split_iff in Hdefined.
    destruct Hdefined as [? [? ?]].
    edestruct IHe1; eauto.
    edestruct IHe2; eauto.
    edestruct IHe3; eauto.
    congruence.
  - (* Bitselect *)
    repeat setoid_rewrite List.in_app_iff in Hdefined.
    rewrite <- defined_value_for_split_iff in Hdefined.
    destruct Hdefined.
    edestruct IHe1; eauto.
    edestruct IHe2; eauto.
    repeat apply_somewhere XBV.to_from_bv_inverse. subst.
    eapply statically_in_bounds_max_bound in s; eauto using XBV.to_N_from_bv.
    eapply select_bit_no_exes.
    + apply XBV.xbv_bv_inverse.
    + apply XBV.to_N_from_bv.
    + assumption.
  - (* concat *)
    repeat setoid_rewrite List.in_app_iff in Hdefined.
    rewrite <- defined_value_for_split_iff in Hdefined.
    destruct Hdefined.
    edestruct IHe1; eauto.
    edestruct IHe2; eauto.
    repeat apply_somewhere XBV.to_from_bv_inverse. subst.
    eexists.
    apply XBV.concat_to_bv.
  - (* literal *)
    eexists. apply XBV.xbv_bv_inverse.
  - (* variable *)
    unfold defined_value_for in *.
    simp expr_reads in Hdefined.
    edestruct Hdefined as [xbv2 [? ?]]; try crush; [idtac].
    replace xbv2 with xbv in * by congruence.
    apply XBV.not_has_x_to_bv.
    assumption.
  - (* resize *)
    edestruct IHe; eauto.
    repeat apply_somewhere XBV.to_from_bv_inverse. subst.
    apply convert_from_bv.
Qed.

Lemma FIXME_expr_to_smt_value w expr : forall (m : VerilogSMTBijection.t) tag regs ρ t,
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
    simp expr_reads expr_to_smt eval_expr in *.
  - (* binop *)
    simpl in *; monad_inv.
    all: admit.
  - (* unop *)
    simpl in *; monad_inv.
    all: admit.
  - (* conditional *)
    simpl in *; monad_inv.
    all: admit.
  - (* Bitselect *)
    simpl in *; monad_inv.
    all: admit.
  - (* concat *)
    simpl in *; monad_inv.
    all: admit.
  - (* literal *)
    simpl in *; monad_inv.
    + simpl. rewrite XBV.xbv_bv_inverse in *.
      some_inv; reflexivity.
    + simpl. rewrite XBV.xbv_bv_inverse in *.
      some_inv.
  - (* variable *)
    edestruct Hmatch as [smtName [Heq2 [? ? ? ? Hmatchvals]]]. { repeat econstructor. }
    simpl in *; monad_inv.
    + funelim (var_to_smt tag m var);
        rewrite <- Heqcall in *; clear Heqcall; [|discriminate].
      inv Hexpr_to_smt.
      simpl.
      replace n__smt with smtName in * by congruence.
      inv Hmatchvals.
      rewrite XBV.xbv_bv_inverse in *.
      crush.
    + inv Hmatchvals.
      rewrite XBV.xbv_bv_inverse in *.
      crush.
  - (* resize *)
    simpl in *; monad_inv.
    all: admit.
Admitted.

Lemma expr_to_smt_valid w tag m expr t regs ρ val :
  expr_to_smt (w := w) tag m expr = inr t ->
  SMTLib.interp_term ρ t = Some val ->
  verilog_smt_match_states_partial (fun v => List.In v (Verilog.expr_reads expr)) tag m regs ρ ->
  exists xbv, (eval_expr regs expr = Some xbv /\ verilog_smt_match_value xbv val).
Proof.
  intros * Hexpr_to_smt Hinterp Hmatch_states.
  erewrite FIXME_expr_to_smt_value in Hinterp; eauto.
  monad_inv.
  eauto using verilog_smt_match_to_bv.
Qed.
