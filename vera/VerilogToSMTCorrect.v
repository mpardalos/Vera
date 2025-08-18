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
From Hammer Require Import Tactics.

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
  induction vars; sauto rew:db: assign_vars.
Qed.

Lemma assign_vars_smtname_start start vars :
  List.Forall (fun n => n >= start) (List.map snd (assign_vars start vars)).
Proof.
  revert start.
  induction vars; intros.
  - sauto rew:db: assign_vars hint:db: datatypes.
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

Inductive verilog_smt_match_on_name (regs : RegisterState) (ρ : SMTLib.valuation) verilogName smtName : Prop :=
| verilog_smt_match_on_names_intro w xbv val
    (Hsmtval : ρ smtName = Some val)
    (Hverilogval : regs verilogName = Some (w; xbv))
    (Hmatchvals : verilog_smt_match_value xbv val).

Definition verilog_smt_match_states
  (tag : TaggedName.Tag)
  (m : VerilogSMTBijection.t)
  (regs : RegisterState)
  (ρ : SMTLib.valuation) : Prop :=
  forall verilogName smtName,
    m (tag, verilogName) = Some smtName ->
    verilog_smt_match_on_name regs ρ verilogName smtName.

Definition verilog_smt_match_states_partial
  (cond : String.string -> Prop)
  (tag : TaggedName.Tag)
  (m : VerilogSMTBijection.t)
  (regs : RegisterState)
  (ρ : SMTLib.valuation) : Prop :=
  forall verilogName smtName,
    cond verilogName ->
    m (tag, verilogName) = Some smtName ->
    verilog_smt_match_on_name regs ρ verilogName smtName.

(* Written by Claude *in one shot* wat. *)
Instance verilog_smt_match_states_partial_morphism
  (tag : TaggedName.Tag)
  (m : VerilogSMTBijection.t)
  (regs : RegisterState)
  (ρ : SMTLib.valuation) :
  Proper (pointwise_relation String.string iff ==> iff)
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

Lemma binop_to_smt_correct {w} (vars : StrFunMap.t smt_var_info) :
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

Lemma expr_to_smt_correct {w} (vars : StrFunMap.t smt_var_info) (expr : Verilog.expression w) :
  forall t tag (m : VerilogSMTBijection.t) regs ρ xbv bv,
    (forall name, m (tag, name) = option_map fst (vars name)) ->
    expr_to_smt vars expr = inr t ->
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

  funelim (expr_to_smt vars expr); intros * Hmatch_vars Hexpr_to_smt Hmatch_states Heval_expr Hinterp_term;
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
    funelim (var_to_smt vars var); rewrite <- Heqcall in *; try discriminate; clear Heqcall.
    destruct Hmatch_states with (verilogName := Verilog.varName var) (smtName := n__smt).
    { rewrite Hmatch_vars. replace (vars (Verilog.varName var)). reflexivity. }
    (* FIXME: don't reference names *)
    inv H0. 
    expr_begin_tac; [idtac].
    simpl.
    replace bv with (SMTLib.Value_BitVec (Verilog.varType var) bv0) by congruence.
    constructor.
  - (* Resize *)
    unfold Verilog.expr_type in *.
    edestruct (cast_from_to_part_eval); eauto.
    expr_begin_tac; [idtac].

    eapply cast_from_to_correct; eauto.
Qed.

Lemma set_reg_get name w val regs :
  set_reg name val regs name = Some (w; val).
Proof.
  unfold set_reg, StrFunMap.insert.
  now rewrite String.eqb_refl.
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

Lemma expr_to_smt_some w e : forall vars m tag regs ρ t,
    expr_to_smt vars (w:=w) e = inr t ->
    verilog_smt_match_states_partial (fun n : String.string => List.In n (List.map Verilog.varName (Verilog.expr_reads e))) tag m regs ρ ->
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
      rewrite List.in_map_iff in H.
      destruct H as [? [? ?]]. subst.
      rewrite List.in_map_iff.
      setoid_rewrite List.in_app_iff.
      eauto.
    }
    edestruct IHe2 as [bv2 Hbv2].
    { eassumption. }
    {
      unfold verilog_smt_match_states_partial in *.
      intros.
      eapply H0; eauto.
      rewrite List.in_map_iff in H.
      destruct H as [? [? ?]]. subst.
      rewrite List.in_map_iff.
      setoid_rewrite List.in_app_iff.
      eauto.
    }
    destruct op; simp binop_to_smt in H2; inv H2;
      simpl; rewrite Hbv1; rewrite Hbv2;
      destruct (N.eq_dec w w); try contradiction;
      eexists; reflexivity.
    all: admit. (* Very repetitive from the above. Solve with tactic *)
Admitted.

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

Lemma var_to_smt_some var vars (m : VerilogSMTBijection.t) tag regs ρ t :
    var_to_smt vars var = inr t ->
    (forall name, m (tag, name) = option_map fst (vars name)) ->
    verilog_smt_match_states_partial (fun n : String.string => n = Verilog.varName var) tag m regs ρ ->
    (exists bv, SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec (Verilog.varType var) bv)).
Proof.
  intros Hsmt Hnames Hmatch.
  funelim (var_to_smt vars var); try rewrite <- Heqcall in *; clear Heqcall; monad_inv.
  unfold verilog_smt_match_states_partial in *.
  setoid_rewrite Hnames in Hmatch.
  insterU Hmatch.
  replace (vars (Verilog.varName var)) in *. simpl in *. insterU Hmatch.
  (* TODO: width matches between smt and verilog *)
  admit.
Admitted.

Lemma module_item_to_smt_satisfiable
  (vars : StrFunMap.t smt_var_info) (mi : Verilog.module_item) inputs outputs :
  forall t tag (m : VerilogSMTBijection.t) regs regs',
    (forall name, m (tag, name) = option_map fst (vars name)) ->
    transfer_module_item vars inputs outputs mi = inr t ->
    exec_module_item regs mi = Some regs' ->
    SMTLib.satisfied_by (SMT.valuation_of_execution m regs') [t]%list.
Proof.
  funelim (transfer_module_item vars inputs outputs mi); intros; monad_inv; [idtac].
  simp exec_module_item exec_statement in *.
  monad_inv.
  unfold SMTLib.satisfied_by, SMTLib.term_satisfied_by. repeat constructor.
  simpl.
  edestruct var_to_smt_some with (var := var); eauto. 2: rewrite H0.
  { admit. (* state matches valuation on written vars *) }
  edestruct expr_to_smt_some with (e := rhs); eauto. 2: rewrite H1.
  { admit. (* state matches valuation on read-from vars *) }
  rewrite H1.
  repeat f_equal. rewrite SMTLib.value_eqb_eq. f_equal.



  eapply transfer_comb_assignments_elim with
    (var_verilog_to_smt := vars)
    (P0:= fun ss x =>
            forall (t : list SMTLib.term) (tag : TaggedName.Tag) (m : VerilogSMTBijection.t) (regs regs' : RegisterState),
              (forall name : String.string, m (tag, name) = option_map fst (vars name)) ->
              x = inr t ->
              exec_statements regs ss = Some regs' ->
              smt_reflect_when
                (verilog_smt_match_states_partial (fun n : String.string => List.In n (statement_reads_lst ss)) tag m regs) t
                (verilog_smt_match_states_partial (fun n : String.string => List.In n (statement_writes_lst ss)) tag m regs')
    ); intros; try discriminate.
  - simp exec_statement statement_writes statement_reads in *.
  - simp exec_statement statement_writes statement_reads expr_reads in *.
    repeat match goal with
           | [H : (_ ;; _)%monad = _ |- _ ] => inv H
           | [H : inr ?x = inr ?y |- _ ] => inv H
           | [H : inl ?x = inl ?y |- _ ] => inv H
           | [H : inl ?x = inr ?y |- _ ] => inv H
           | [H : inr ?x = inl ?y |- _ ] => inv H
           end; autodestruct_eqn E.
    funelim (term_for_name vars t name); rewrite <- Heqcall in *; clear Heqcall;
      try discriminate.
    inv E0.
    split; intros.
    + unfold verilog_smt_match_states_partial in *; intros.
      inv H1. inv H2; [|now some_inv]. inv H6. autodestruct_eqn E.
      (* TODO: expr_to_smt correct should only need the read names to match *)
      eapply expr_to_smt_correct in E2; eauto; [|admit]. inv E2.
      rewrite SMTLib.value_eqb_eq in *; subst.
      erewrite H, Heq0 in H3. simpl in H3. inv H3.
      repeat econstructor; eauto.
      rewrite set_reg_get. do 2 f_equal.
    + edestruct expr_to_smt_some as [bv Hbv]; [solve[eauto]|solve[eauto]|].
      (* TODO: expr_to_smt correct should only need the read names to match *)
      eapply expr_to_smt_correct with (bv:=((SMTLib.Value_BitVec t bv))) in E2; eauto; [|admit]. inv E1.
      repeat constructor. unfold SMTLib.term_satisfied_by. simpl.
      edestruct H1. {
        repeat econstructor.
      } {
        erewrite H, Heq0. reflexivity.
      } simpl in *.
      rewrite Hsmtval, Hbv.
      repeat f_equal.
      rewrite set_reg_get in Hverilogval. inv Hverilogval.
      apply_somewhere inj_pair2; subst.
      repeat econstructor. unfold SMTLib.term_satisfied_by. simpl.
      rewrite SMTLib.value_eqb_eq.
      inv Hmatchvals. repeat f_equal.
      inv E2. apply_somewhere inj_pair2; subst.
      eapply BV.of_bits_equal.
      apply RawXBV.from_bv_injective.
      auto.
  - unfold verilog_smt_match_states_partial.
    simp exec_statement statement_writes statement_reads in *.
    inv H0. split; intros; (crush || constructor).
  - simp exec_statement statement_writes statement_reads in *.
    repeat match goal with
           | [H : (_ ;; _)%monad = _ |- _ ] => inv H
           end; autodestruct_eqn E.
    (* TODO: exec_statements case *)
    admit.
Admitted.

(* Lemma stmt_to_smt_correct' *)
(*   (vars : StrFunMap.t smt_var_info) (stmt : Verilog.statement) : *)
(*   forall t tag (m : VerilogSMTBijection.t) regs regs', *)
(*     (forall name, m (tag, name) = option_map fst (vars name)) -> *)
(*     transfer_comb_assignments vars stmt = inr t -> *)
(*     exec_statement regs stmt = Some regs' -> *)
(*     forall ρ : SMTLib.valuation, *)
(*       verilog_smt_match_states_partial (fun n => List.In n (statement_reads stmt)) tag m regs ρ -> *)
(*       (SMTLib.satisfied_by ρ t <-> verilog_smt_match_states_partial (fun n => List.In n (statement_writes stmt)) tag m regs' ρ). *)

Definition inputs_of_execution (input_vars : list Verilog.variable) (e : execution) : option (list {n : N & XBV.xbv n}) :=
  List.mapT_list (fun var => match e (Verilog.varName var) with
                          | Some (w; xbv) =>
                              if (w =? Verilog.varWidth var)%N
                              then Some (w; xbv)
                              else None
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

Lemma inputs_of_execution_valid input : forall vars e,
    inputs_of_execution vars e = Some input ->
    input_valid vars input.
Proof.
  unfold input_valid, inputs_of_execution, Verilog.var_names.
  induction input as [|[w bv]]; intros * H.
  - apply mapT_list_eq_nil in H.
    subst. constructor.
  - eapply mapT_list_eq_cons in H.
    destruct H as [n [ns [H1 [H2 H3]]]].
    autodestruct_eqn E. rewrite N.eqb_eq in *.
    crush.
Qed.

(* TODO: StrFunMap.gsi *)

Lemma inputs_of_execution_same_values vars : forall e input,
  inputs_of_execution vars e = Some input ->
  List.Forall (fun n : String.string => StrFunMap.of_list (List.combine (Verilog.var_names vars) input) n = e n) (Verilog.var_names vars).
Proof.
  unfold inputs_of_execution.
  induction vars; intros; [crush|].
  simpl in *. autodestruct_eqn E; [discriminate|].
  inv H1. simpl. rewrite N.eqb_eq in *. subst.
  unfold StrFunMap.insert.
  insterU IHvars.
  rewrite ! List.Forall_forall in *.
  intros ? []; autodestruct_eqn E;
    (rewrite String.eqb_eq in * || rewrite String.eqb_neq in * );
    subst; crush.
Qed.

Lemma exec_statement_reads_has_values_before r1 r2 stmt :
  exec_statement r1 stmt = Some r2 ->
  List.Forall (fun n => exists v, r1 n = v) (statement_reads stmt).
Proof.
  rewrite List.Forall_forall.
  eapply exec_statement_elim
    with
    (P := fun regs stmt result =>
            result = Some r2 ->
            forall x : String.string,
              List.In x (statement_reads stmt) ->
              exists v : option {n : N & XBV.xbv n}, r1 x = v)
    (P0 := fun regs stmts result =>
             result = Some r2 ->
             forall x : String.string,
               List.In x (statement_reads_lst stmts) ->
               exists v : option {n : N & XBV.xbv n}, r1 x = v);
    crush.
Qed.

Lemma TODO_exec_statement_change_vars r1 r2 stmt :
  List.Forall (fun n => r1 n = r2 n) (statement_reads stmt) ->
  exec_statement r1 stmt = exec_statement r2 stmt.
Proof. Admitted.

Lemma valid_execution_single v r1 r2 stmt :
  (* FIXME: statement_reads should only include actual inputs, but currently includes "self" write-reads *)
  (* FIXME: order might be different *)
  Verilog.var_names (Verilog.input_vars (Verilog.modVariables v)) = statement_reads stmt ->
  Verilog.modBody v = [Verilog.AlwaysComb stmt]%list ->
  exec_statement r1 stmt = Some r2 ->
  valid_execution v r2.
Proof.
  unfold valid_execution.
  intros Hinputs Hbody Hexec.
  pose proof exec_statement_reads_has_values_before as Hvals. insterU Hvals.
  destruct (inputs_of_execution (Verilog.input_vars (Verilog.modVariables v)) r1) as [input|] eqn:E.
  {
    exists input. exists ({| regState := r2; pendingProcesses := []%list |}).
    split.
    - eauto using inputs_of_execution_valid.
    - split; [|crush].
      unfold initial_state. rewrite Hbody.
      simp run_multistep exec_module_item.
      rewrite TODO_exec_statement_change_vars with (r2 := r1); cycle 1. {
        rewrite <- Hinputs.
        eauto using inputs_of_execution_same_values.
      }
      rewrite Hexec. simpl. simp run_multistep. reflexivity.
  }
  {
    (* FIXME:
       exec_statement r1 stmt = Some r2 ->
       inputs_of_execution (Verilog.input_vars (Verilog.modVariables v)) r1 <> None
     *)
    admit.
  }
Admitted.

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

Lemma transfer_module_body_satisfiable tag vars v q m ρ :
  transfer_module_body vars (Verilog.modBody v) = inr q ->
  valid_execution v (SMT.execution_of_valuation tag m ρ) ->
  SMTLib.satisfied_by ρ q.
Proof. Admitted.

Lemma transfer_module_body_correct v :
  forall tag vars (m : VerilogSMTBijection.t) stmt q,
    no_errors v ->
    Verilog.modBody v = [Verilog.AlwaysComb stmt]%list ->
    (forall name, m (tag, name) = option_map fst (vars name)) ->
    transfer_module_body vars (Verilog.modBody v) = inr q ->
    SMTLibFacts.smt_reflect
      q
      (fun ρ => valid_execution v (SMT.execution_of_valuation tag m ρ)).
Proof.
  intros * Hnoerrors Hbody Hnames Htransfer_body.
  split; intro.
  - (* FIXME: statement_reads should really be statement_observes *)
    destruct v. simpl in *. subst modBody.
    simp transfer_module_body in *. inv Htransfer_body; autodestruct_eqn E.
    simp transfer_module_item in *.
    rewrite List.app_nil_r in *.
    eapply valid_execution_single; simpl.
    + simpl. admit.
    + trivial.
    + pose proof stmt_to_smt_correct as Hreflect. unfold smt_reflect_when in Hreflect.
      admit.
  - eapply transfer_module_body_satisfiable.
    unfold valid_execution, initial_state in H. destruct H as [input [final [Hvalid [Hrun Hfinal]]]].
    simpl in *. simp run_multistep in Hrun. inv Hrun. autodestruct_eqn E.
    simp run_multistep in H0. inv H0. simpl in *. subst.
    epose proof (TODO_exec_module_item_no_overwrite _ _ (Verilog.AlwaysComb stmt) ltac:(eassumption)) as Hno_overwrite.
    simp exec_module_item in *.
    pose proof stmt_to_smt_correct as Hreflect. unfold smt_reflect_when in Hreflect.
    eapply Hreflect. 1, 2, 3: solve [eauto].
    + (* TODO: Initial state matches *)
      unfold verilog_smt_match_states_partial. intros.
      econstructor; cycle 1.
      *
    + (* TODO: Final state matches *) admit.

Admitted.

Lemma mapT_inv A B : forall l (f : A -> transf B) o,
  List.mapT_list f l = inr o ->
  List.Forall (fun x => exists y, f x = inr y) l.
Proof. induction l; intros; crush. Qed.

Theorem verilog_to_smt_correct tag start v smt :
  verilog_to_smt tag start v = inr smt ->
  SMTLibFacts.smt_reflect
    (SMT.query smt)
    (fun ρ => valid_execution v (SMT.execution_of_valuation tag (SMT.nameMap smt) ρ)).
Proof.
  unfold verilog_to_smt.
  intros H.
  inv H. autodestruct_eqn E. cbn in *.
  admit.
Admitted.
