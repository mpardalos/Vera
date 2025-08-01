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
From Coq Require Import Setoid.

From Equations Require Import Equations.

Import List.ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Import SigTNotations.

Local Open Scope list.

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

Lemma assign_vars_fst vars : forall start,
  List.map fst (assign_vars start vars) = vars.
Proof.
  induction vars; intros; simp assign_vars in *; crush.
Qed.

Lemma mk_bijection_smt_map_match tag start v m :
  mk_bijection tag (assign_vars start (Verilog.modVariables v)) = inr m ->
  SMT.match_map_verilog tag m v.
Proof.
  Opaque VerilogSMTBijection.lookup_left.
  unfold SMT.match_map_verilog.
  generalize (Verilog.modVariables v). clear v. intro vars.
  remember (assign_vars start vars) as assignment.
  epose proof (assign_vars_smtname_nodup _ _) as Hnodup;
    rewrite <- Heqassignment in Hnodup.
  epose proof (assign_vars_fst _ _) as Hvars;
    rewrite <- Heqassignment in Hvars.
  clear start Heqassignment.
  generalize dependent Hnodup.
  generalize dependent vars.
  generalize dependent m.
  induction assignment; intros * ? ? Hbijection.
  - simp mk_bijection in *. inv Hbijection.
    split; intros H; cbn in *; solve_by_inverts 2%nat.
  - destruct a as [var smtName].
    simp mk_bijection in Hbijection; inv Hbijection; autodestruct.
    inv Hnodup.
    split; intros H.
    + destruct H as [smtName' H].
      cbn. cbn in H.
      autodestruct; cbn in *; subst.
      * left. congruence.
      * right.
        edestruct IHassignment; eauto.
    + cbn. autodestruct.
      * eauto.
      * eapply IHassignment; eauto; now some_inv.
Qed.

Lemma verilog_to_smt_map_match tag start v smt :
  verilog_to_smt tag start v = inr smt ->
  SMT.match_map_verilog tag (SMT.nameMap smt) v.
Proof.
  intros.
  unfold verilog_to_smt in *. simpl in *.
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
  unfold verilog_to_smt in *. simpl in *.
  autodestruct_eqn E. cbn.
  eauto using mk_bijection_only_tag.
Qed.

Inductive verilog_smt_match_value {w} : XBV.xbv w -> SMTLib.value -> Prop :=
| verilog_smt_match_value_intro bv :
  verilog_smt_match_value (XBV.from_bv bv) (SMTLib.Value_BitVec w bv).

Definition verilog_smt_match_to_bv n (xbv : XBV.xbv n) (bv : BV.bitvector n):
  XBV.to_bv xbv = Some bv ->
  verilog_smt_match_value xbv (SMTLib.Value_BitVec n bv).
Proof.
  intros H.
  apply XBV.bv_xbv_inverse in H.
  subst xbv.
  constructor.
Qed.

Definition verilog_smt_match_to_bv_bits
  n1 n2 (xbv : XBV.xbv n1) (bv1 : BV.bitvector n1) (bv2 : BV.bitvector n2):
  XBV.to_bv xbv = Some bv1 ->
  BV.bits bv1 = BV.bits bv2 ->
  verilog_smt_match_value xbv (SMTLib.Value_BitVec n2 bv2).
Proof.
  destruct bv1 as [bv1 wf1], bv2 as [bv2 wf2]. simpl. intros H1 H2.
  apply XBV.bv_xbv_inverse in H1.
  subst.
  constructor.
Qed.

Inductive verilog_smt_match_on_name (regs : RegisterState) (ρ : SMTLib.valuation) var smtName : Prop :=
| verilog_smt_match_on_names_intro xbv val
    (Hsmtval : ρ smtName = Some val)
    (Hverilogval : regs var = Some xbv)
    (Hmatchvals : verilog_smt_match_value xbv val).

Definition verilog_smt_match_states
  (tag : TaggedVariable.Tag)
  (m : VerilogSMTBijection.t)
  (regs : RegisterState)
  (ρ : SMTLib.valuation) : Prop :=
  forall verilogName smtName,
    m (tag, verilogName) = Some smtName ->
    verilog_smt_match_on_name regs ρ verilogName smtName.

Definition verilog_smt_match_states_partial
  (cond : Verilog.variable -> Prop)
  (tag : TaggedVariable.Tag)
  (m : VerilogSMTBijection.t)
  (regs : RegisterState)
  (ρ : SMTLib.valuation) : Prop :=
  forall var smtName,
    cond var ->
    m (tag, var) = Some smtName ->
    verilog_smt_match_on_name regs ρ var smtName.

(* Written by Claude *in one shot* wat. *)
Instance verilog_smt_match_states_partial_morphism
  (tag : TaggedVariable.Tag)
  (m : VerilogSMTBijection.t)
  (regs : RegisterState)
  (ρ : SMTLib.valuation) :
  Proper (pointwise_relation Verilog.variable iff ==> iff)
    (fun cond => verilog_smt_match_states_partial cond tag m regs ρ).
Proof.
  intros cond1 cond2 H_equiv.
  unfold verilog_smt_match_states_partial.
  split; intros H verilogName smtName.
  - intros H_cond1 H_map.
    apply (H verilogName smtName).
    + apply H_equiv. exact H_cond1.
    + exact H_map.
  - intros H_cond2 H_map.
    apply (H verilogName smtName).
    + apply H_equiv. exact H_cond2.
    + exact H_map.
Qed.

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

Require Import Program.Equality.

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

Require ZifyBool.

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

Check RawBV.nshr_be. (* list bool -> nat -> list bool *)

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

Lemma set_reg_get_in var val regs :
  set_reg var val regs var = Some val.
Proof.
  unfold set_reg, VariableDepMap.insert.
  autodestruct; [|contradiction].
  dependent destruction e.
  reflexivity.
Qed.

Lemma set_reg_get_out var1 var2 val regs :
  var1 <> var2 ->
  set_reg var1 val regs var2 = regs var2.
Proof.
  intros.
  unfold set_reg, VariableDepMap.insert.
  autodestruct; [contradiction|].
  reflexivity.
Qed.

Definition smt_reflect_when
  (C : SMTLib.valuation -> Prop)
  (q : SMTLib.query)
  (P : SMTLib.valuation -> Prop) :=
  forall ρ : SMTLib.valuation,
    C ρ -> (SMTLib.satisfied_by ρ q <-> P ρ).

Lemma verilog_smt_match_states_partial_impl P1 P2 tag m regs ρ :
  (forall x, P2 x -> P1 x) ->
  verilog_smt_match_states_partial P1 tag m regs ρ ->
  verilog_smt_match_states_partial P2 tag m regs ρ.
Proof. crush. Qed.

Lemma expr_to_smt_some w e : forall m tag regs ρ t,
    expr_to_smt tag m (w:=w) e = inr t ->
    verilog_smt_match_states_partial (fun v => List.In v (Verilog.expr_reads e)) tag m regs ρ ->
    (exists bv, SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec w bv)).
Proof.
  induction e; intros;
    simp expr_to_smt in H; inv H; autodestruct_eqn E;
    simp expr_reads in *.
  - edestruct IHe1 as [bv1 Hbv1]; eauto.
    {
      unfold verilog_smt_match_states_partial in *.
      intros.
      eapply H0; eauto.
      apply List.in_app_iff.
      auto.
    }
    edestruct IHe2 as [bv2 Hbv2].
    { eassumption. }
    {
      unfold verilog_smt_match_states_partial in *.
      intros.
      eapply H0; eauto.
      apply List.in_app_iff.
      auto.
    }
    destruct op; simp binop_to_smt in H2; inv H2;
      simpl; rewrite Hbv1; rewrite Hbv2;
      destruct (N.eq_dec w w); try contradiction;
      eexists; reflexivity.
    all: admit. (* Very repetitive from the above. Solve with tactic *)
Admitted.

Lemma var_to_smt_value var (m : VerilogSMTBijection.t) tag regs ρ t :
    var_to_smt tag m var = inr t ->
    verilog_smt_match_states_partial (fun v => v = var) tag m regs ρ ->
    SMTLib.interp_term ρ t = (xbv <- regs var ;; bv <- XBV.to_bv xbv ;; ret (SMTLib.Value_BitVec _ bv))%monad.
Proof.
  intros Hsmt Hmatch.
  funelim (var_to_smt tag m var); try rewrite <- Heqcall in *; clear Heqcall; monad_inv.
  unfold verilog_smt_match_states_partial in *.
  insterU Hmatch. inv Hmatch.
  inv Hmatchvals. simpl.
  rewrite Hverilogval.
  rewrite XBV.xbv_bv_inverse.
  assumption.
Qed.

Lemma TODO_var_to_smt_valid tag m var t ρ val :
  var_to_smt tag m var = inr t ->
  SMTLib.interp_term ρ t = Some val ->
  exists xbv, ((SMT.execution_of_valuation tag m ρ) var = Some xbv /\ verilog_smt_match_value xbv val).
Admitted.

Lemma TODO_expr_to_smt_value w expr (m : VerilogSMTBijection.t) tag regs ρ t :
    expr_to_smt tag m expr = inr t ->
    verilog_smt_match_states_partial (fun v => List.In v (Verilog.expr_reads expr)) tag m regs ρ ->
    SMTLib.interp_term ρ t = (xbv <- eval_expr (w:=w) regs expr ;; bv <- XBV.to_bv xbv ;; ret (SMTLib.Value_BitVec _ bv))%monad.
Proof. Admitted.

Lemma TODO_eval_expr_no_exes w regs e xbv :
  eval_expr (w:=w) regs e = Some xbv ->
  exists bv, XBV.to_bv xbv = Some bv.
Proof. Admitted.

Lemma TODO_expr_to_smt_reads_have_values w regs expr bv :
  eval_expr (w := w) regs expr = Some (XBV.from_bv bv) ->
  List.Forall (fun var => exists bv0, regs var = Some (XBV.from_bv bv0)) (Verilog.expr_reads expr).
Proof. Admitted.

Lemma TODO_expr_to_smt_valid w tag m expr t ρ val :
  expr_to_smt (w := w) tag m expr = inr t ->
  SMTLib.interp_term ρ t = Some val ->
  exists xbv, (eval_expr (SMT.execution_of_valuation tag m ρ) expr = Some xbv /\ verilog_smt_match_value xbv val).
Admitted.

Lemma verilog_smt_match_states_valuation_of_execution_same C tag m r :
  verilog_smt_match_states_partial C tag m r (SMT.valuation_of_execution m r).
Admitted.

Lemma verilog_smt_match_states_valuation_of_execution C tag m r1 r2 :
  (forall var, C var -> r1 var = r2 var) ->
  (forall var, C var -> exists bv, r1 var = Some (XBV.from_bv bv)) ->
  verilog_smt_match_states_partial C tag m r1 (SMT.valuation_of_execution m r2).
Proof.
  unfold verilog_smt_match_states_partial.
  intros Hsame Hsome * Hcond Hmap.
  insterU Hsame. insterU Hsome.
  destruct Hsome as [xbv Hxbv].
  econstructor.
  - eapply SMT.valuation_of_execution_some.
    + rewrite <- Hsame. eassumption.
    + now rewrite XBV.xbv_bv_inverse.
    + eassumption.
  - eassumption.
  - econstructor.
Qed.

Lemma module_item_to_smt_satisfiable
  tag m (mi : Verilog.module_item) inputs outputs :
  disjoint inputs outputs ->
  forall t regs regs',
    transfer_module_item tag m inputs outputs mi = inr t ->
    exec_module_item regs mi = Some regs' ->
    SMTLib.term_satisfied_by (SMT.valuation_of_execution m regs') t.
Proof.
  funelim (transfer_module_item tag m inputs outputs mi); intros; monad_inv; [idtac].
  simp exec_module_item exec_statement in *.
  monad_inv.
  unfold SMTLib.satisfied_by, SMTLib.term_satisfied_by. repeat constructor.
  simpl.
  edestruct TODO_eval_expr_no_exes as [bv_rhs Hbv_rhs]; [eassumption|].
  apply XBV.to_from_bv_inverse in Hbv_rhs. subst x.
  erewrite var_to_smt_value with (var := var) (regs := (set_reg var (XBV.from_bv bv_rhs) regs)); eauto; cycle 1.
  {
    eapply verilog_smt_match_states_valuation_of_execution.
    - intros. subst. reflexivity.
    - intros. subst.
      eexists. eapply set_reg_get_in.
  }
  rewrite set_reg_get_in. simpl. rewrite XBV.xbv_bv_inverse.
  erewrite TODO_expr_to_smt_value with (expr := rhs) (regs := regs); eauto; cycle 1. {
    eapply verilog_smt_match_states_valuation_of_execution; intros.
    - symmetry. apply set_reg_get_out.
      pose proof disjoint_r_intro as Hx. insterU Hx.
      rewrite List.Forall_forall in f. insterU f.
      crush.
    - pose proof TODO_expr_to_smt_reads_have_values as Hinput_values.
      setoid_rewrite List.Forall_forall in Hinput_values.
      eapply Hinput_values; eauto.
  }
  rewrite E. simpl. rewrite XBV.xbv_bv_inverse.
  autodestruct; [|contradiction].
  repeat f_equal. apply BV.bv_eq_reflect. apply eq_rect_eq.
Qed.

Lemma smt_eq_sat_iff ρ l r :
  SMTLib.term_satisfied_by ρ (SMTLib.Term_Eq l r) <->
    (exists v,
        SMTLib.interp_term ρ l = Some v /\
        SMTLib.interp_term ρ r = Some v).
Proof.
  unfold SMTLib.term_satisfied_by.
  split; intros H.
  - inv H. simpl in *. autodestruct_eqn E.
    apply_somewhere SMTLib.value_eqb_eq.
    subst. eauto.
  - destruct H as [v [Hl Hr]].
    repeat constructor. simpl.
    rewrite Hl, Hr.
    repeat f_equal.
    now apply SMTLib.value_eqb_eq.
Qed.

Lemma module_item_to_smt_valid tag m (mi : Verilog.module_item) inputs outputs :
  disjoint inputs outputs ->
  forall ρ t,
    transfer_module_item tag m inputs outputs mi = inr t ->
    SMTLib.term_satisfied_by ρ t ->
    exec_module_item (SMT.execution_of_valuation tag m ρ) mi = Some (SMT.execution_of_valuation tag m ρ).
Proof.
  funelim (transfer_module_item tag m inputs outputs mi); intros * Hdisjoint * Htransf Hsat; monad_inv; [idtac].
  simp exec_module_item exec_statement in *.
  monad_inv.
  rewrite smt_eq_sat_iff in Hsat. destruct Hsat as [v [Ht0 Ht1]].
  edestruct TODO_expr_to_smt_valid as [xbv_expr [Heval_expr Hmatch_expr]]; eauto.
  edestruct TODO_var_to_smt_valid as [xbv_var [Heval_var Hmatch_var]]; eauto.
  rewrite Heval_expr. simpl. f_equal.
  eapply functional_extensionality_dep. intro var'.
  destruct (dec (var = var')); [|now rewrite set_reg_get_out].
  subst. rewrite set_reg_get_in. symmetry.
  edestruct TODO_eval_expr_no_exes; eauto.
  apply XBV.bv_xbv_inverse in H. subst.
  rewrite Heval_var. f_equal.
  inv Hmatch_var. inv Hmatch_expr.
  f_equal.
  apply_somewhere inj_pair2. subst.
  apply_somewhere RawXBV.from_bv_injective.
  now apply BV.of_bits_equal.
Qed.

Definition inputs_of_execution
  (input_vars : list Verilog.variable)
  (e : execution) :
  option (list {n : N & XBV.xbv n}) :=
  List.mapT_list (fun var => match e var with
                          | Some xbv => Some (_; xbv)
                          | None => None
                          end) input_vars.

Lemma mapT_list_eq_nil A B (f : A -> option B) l :
  List.mapT_list f l = Some []%list ->
  l = []%list.
Proof. destruct l; crush. Qed.

Lemma mapT_list_eq_cons A B l : forall (f : A -> option B) l' b,
  List.mapT_list f l = Some (b :: l')%list ->
  exists (a : A) (tl : list A), l = (a :: tl)%list /\ f a = Some b /\ List.mapT_list f tl = Some l'.
Proof.
  destruct l; intros * H; [crush|].
  inv H. autodestruct_eqn E.
  some_inv. eauto.
Qed.

(* TODO: StrFunMap.gsi *)

Lemma exec_statement_reads_has_values_before r1 r2 stmt :
  exec_statement r1 stmt = Some r2 ->
  List.Forall (fun n => exists v, r1 n = v) (Verilog.statement_reads stmt).
Proof.
  rewrite List.Forall_forall.
  eapply exec_statement_elim
    with
    (P := fun regs stmt result =>
            result = Some r2 ->
            forall x, List.In x (Verilog.statement_reads stmt) ->
                 exists v, r1 x = v)
    (P0 := fun regs stmts result =>
             result = Some r2 ->
             forall x, List.In x (Verilog.statement_reads_lst stmts) ->
                  exists v, r1 x = v);
    crush.
Qed.

Lemma TODO_exec_statement_change_vars r1 r2 stmt :
  List.Forall (fun n => r1 n = r2 n) (Verilog.statement_reads stmt) ->
  exec_statement r1 stmt = exec_statement r2 stmt.
Proof. Admitted.

Lemma smt_reflect_when_intro C q P :
  (forall ρ, P ρ -> C ρ) ->
  (forall ρ, SMTLib.satisfied_by ρ q -> C ρ) ->
  smt_reflect_when C q P ->
  SMTLibFacts.smt_reflect q P.
Proof. unfold smt_reflect_when, SMTLibFacts.smt_reflect. firstorder. Qed.

(* TODO: Add this as a check in exec_module_item *)
Lemma TODO_exec_module_item_no_overwrite r1 r2 mi :
  exec_module_item r1 mi = Some r2 ->
  forall n v, r1 n = Some v -> r2 n = Some v.
Proof. Admitted.

Lemma transfer_module_body_satisfiable v :
  forall tag (m : VerilogSMTBijection.t) r1 r2 q,
    transfer_module_body tag m (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
    run_multistep {| regState := r1; pendingProcesses := Verilog.modBody v |} =
      Some {| regState := r2; pendingProcesses := [] |} ->
    SMTLib.satisfied_by (SMT.valuation_of_execution m r2) q.
Proof.
  unfold valid_execution, initial_state.
  generalize dependent (Verilog.module_outputs v). intro inputs.
  generalize dependent (Verilog.module_inputs v). intro outputs.
  generalize dependent (Verilog.modBody v). intro body.
  induction body; intros * Htransfer Hvalid; simp transfer_module_body in *; [some_inv; constructor|].
  simp run_multistep in Hvalid.
  monad_inv. constructor; [|eapply IHbody; eassumption].
  (* TODO:
     Need to be able to either change the valuation in term_satisfied_by, or the final state in module_item_to_smt_satisfiable.
     As discussed with John, it would be nice to be able to say `run_stmt (r1 U r) stmt = Some (r2 U r)`, where r is preserved.
     But it might just be easier to do this thing on the SMT side.
     But this might be useful for other passes.
     But I'm trying to just get this done quickly.
   *)
  enough (SMTLib.term_satisfied_by (SMT.valuation_of_execution m r) t) by admit.
  eapply module_item_to_smt_satisfiable.
  - (* inputs-outputs disjoint, should be easy enough *) admit.
  - eassumption.
  - eassumption.
Admitted.

Lemma transfer_module_body_satisfiable_valid_execution v :
  forall tag (m : VerilogSMTBijection.t) e q,
    transfer_module_body tag m (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
    valid_execution v e ->
    SMTLib.satisfied_by (SMT.valuation_of_execution m e) q.
Proof.
  intros * Htransfer Hvalid.
  inv Hvalid.
  unfold initial_state in *.
  eapply transfer_module_body_satisfiable; eauto.
Qed.

Lemma transfer_module_body_correct v :
  forall tag (m : VerilogSMTBijection.t) q,
    transfer_module_body tag m (Verilog.module_inputs v) (Verilog.module_outputs v) (Verilog.modBody v) = inr q ->
    SMTLibFacts.smt_reflect q (fun ρ => valid_execution v (SMT.execution_of_valuation tag m ρ)).
Proof.
  intros * Htransfer_body.
  split; intro.
  - admit.
  - (* TODO: valuation_of_execution_of_valuation *)
    replace ρ with (SMT.valuation_of_execution m (SMT.execution_of_valuation tag m ρ)) by admit.
    eapply transfer_module_body_satisfiable_valid_execution; eassumption.
Admitted.

Theorem verilog_to_smt_correct tag start v smt :
  verilog_to_smt tag start v = inr smt ->
  SMTLibFacts.smt_reflect
    (SMT.query smt)
    (fun ρ => valid_execution v (SMT.execution_of_valuation tag (SMT.nameMap smt) ρ)).
Proof.
  unfold verilog_to_smt.
  intros H.
  inv H. autodestruct_eqn E. cbn in *.
  eapply transfer_module_body_correct; eassumption.
Qed.
