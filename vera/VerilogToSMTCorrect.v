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
From Coq Require String.
From Coq Require Import Logic.ProofIrrelevance.
From Coq Require Import NArith.
From Coq Require Import PeanoNat.

From Equations Require Import Equations.

Import List.ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Import SigTNotations.

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

Inductive verilog_smt_match_on_names (regs : RegisterState) (ρ : SMTLib.valuation) verilogName smtName :=
| verilog_smt_match_on_names_intro w xbv val
    (Hsmtval : ρ smtName = Some val)
    (Hverilogval : regs verilogName = Some (w; xbv))
    (Hmatchvals : verilog_smt_match_value xbv val).

Definition verilog_smt_match_states
  (tag : TaggedName.Tag)
  (m : VerilogSMTBijection.t)
  (regs : RegisterState)
  (ρ : SMTLib.valuation) :=
  forall verilogName smtName,
    m (tag, verilogName) = Some smtName ->
    verilog_smt_match_on_names regs ρ verilogName smtName.

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

(* Compute RawBV.bv_shr [false; true; false; false]%list [true; false; false; false]%list. *)

Compute
  let vec := [true; true; true; false; false; true]%list in
  let idx := [false; true; true; false; false; false]%list in
  (
    (RawBV.list2nat_be idx),
    RawBV.bv_extr 0 1 (RawBV.size vec) (RawBV.bv_shr vec idx),
    [RawBV.bitOf (RawBV.list2nat_be idx) vec]%list
  ).

Lemma rawbv_extr_one_bit (n : N) vec :
  (1 + n <= RawBV.size vec)%N ->
  RawBV.bv_extr n 1 (RawBV.size vec) vec = [RawBV.bitOf (N.to_nat n) vec]%list.
Proof.
  intros. unfold RawBV.bv_extr, RawBV.size in *.
  autodestruct_eqn E; try (rewrite N.ltb_lt in *; lia); clear E.
  replace (N.to_nat (1 + n)) with (S (N.to_nat n)) by lia.
  assert (S (N.to_nat n) <= length vec) as H' by lia. clear H. revert H'.
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
  funelim (select_bit (XBV.from_bv vec) (XBV.from_bv idx));
    rewrite XBV.xbv_bv_inverse in Heq; inv Heq;
    rewrite <- Heqcall; clear Heqcall.
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

Corollary cast_from_to_zextn_inv ρ (from to : N) bv_from result t :
  (to >= from)%N ->
  SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec from bv_from) ->
  SMTLib.interp_term ρ (cast_from_to from to t) = result ->
  result = Some (SMTLib.Value_BitVec _ (BV.bv_concat (BV.zeros (to - from)) bv_from)).
Admitted.

Lemma to_N_from_bv n (b : BV.bitvector n) : XBV.to_N (XBV.from_bv b) = Some (BV.to_N b).
Proof. unfold XBV.to_N. now rewrite XBV.xbv_bv_inverse. Qed.

Lemma bv_to_N_max_bound n (b : BV.bitvector n) : (BV.to_N b < 2 ^ n)%N.
Proof.
  intros.
  unfold BV.to_N, RawBV.to_N, RawBV.size.
  destruct b. simpl. subst.
  unfold RawBV.size in *.
  replace (2 ^ N.of_nat (length bv))%N with (N.of_nat (2 ^ length bv))
    by now rewrite Nat2N.inj_pow.
  enough (RawBV.list2nat_be bv < 2 ^ (length bv)) by lia.
  induction bv; intros; try crush.
  cbn in *. rewrite ! RawBV._list2nat_be_arith in *.
  crush.
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
    rewrite to_N_from_bv in HtoN. inv HtoN.
    crush.
  - unfold XBV.to_N in *. destruct (XBV.to_bv xbv); try discriminate. inv HtoN.
    enough (BV.to_N b < 2 ^ w)%N by lia.
    apply bv_to_N_max_bound.
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
    repeat match goal with
      | [ H : context[verilog_smt_match_value _ _] |- _ ] => (insterU H || inv H)
      | [ H : {| pr1 := _; pr2 := _ |} = {| pr1 := _; pr2 := _ |} |- _ ] => inv H
      | [ H : (?x; _) = (?x; _) |- _ ] => apply inj_pair2 in H; subst
      end.

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
  - (* BinaryPlus *)
    expr_begin_tac. bv_binop_tac.
  - (* BinaryMinus *)
    expr_begin_tac. bv_binop_tac.
  - (* BinaryStar *)
    expr_begin_tac. bv_binop_tac.
  - (* BinaryBitwiseAnd *)
    expr_begin_tac.
    apply verilog_smt_match_to_bv.
    simp eval_binop.
    erewrite bitwise_and_no_exes;
      rewrite XBV.xbv_bv_inverse in *;
      crush.
  - (* BinaryBitwiseOr *)
    expr_begin_tac.
    apply verilog_smt_match_to_bv.
    simp eval_binop.
    erewrite bitwise_or_no_exes;
      rewrite XBV.xbv_bv_inverse in *;
      crush.
  - admit. (* TODO BinaryShiftRight *)
  - admit. (* TODO BinaryShiftLeft *)
  - admit. (* TODO BinaryShiftLeftArithmetic *)
  - admit. (* TODO UnaryPlus *)
  - admit. (* TODO UnaryMinus *)
  - admit. (* TODO UnaryNegation *)
  - (* Conditional *)
    expr_begin_tac;
      try solve [eauto];
      try rewrite Bool.negb_true_iff in *;
      try rewrite Bool.negb_false_iff in *.
    + (* Contradiction 0 <> 0 *)
      apply_somewhere XBV.bv_xbv_inverse.
      apply_somewhere XBV.from_bv_injective.
      subst.
      unfold Verilog.expr_type in *.
      inv H3. autodestruct; try contradiction.
      destruct e; cbn in *.
      unfold BV.is_zero in *.
      congruence.
    + (* Condition is X *)
      some_inv; now rewrite XBV.xbv_bv_inverse in *.
    + (* Condition is X *)
      some_inv; now rewrite XBV.xbv_bv_inverse in *.
    + (* Contradiction 0 <> 0 *)
      apply_somewhere XBV.bv_xbv_inverse.
      apply_somewhere XBV.from_bv_injective.
      subst.
      unfold Verilog.expr_type in *.
      inv H3. autodestruct; try contradiction.
      destruct e; cbn in *.
      unfold BV.is_zero in *.
      congruence.
    + now rewrite XBV.xbv_bv_inverse in *.
    + now rewrite XBV.xbv_bv_inverse in *.
  - (* TODO: BitSelect *)
    unfold smt_select_bit in *.
    edestruct (smt_select_bit_part_eval_idx); eauto.
    edestruct (smt_select_bit_part_eval_vec); eauto.
    expr_begin_tac.
    cbn in Hinterp_term; autodestruct_eqn E.
    apply verilog_smt_match_to_bv.
    rewrite <- select_bit_to_bv.
    + f_equal.
      simp select_bit; unfold select_bit_clause_1.
      rewrite ! XBV.xbv_bv_inverse. simpl.
      (* Sign extending does not change the nat value *)
      replace (BV.to_N bv4) with (BV.to_N bv0); cycle 1. {
        erewrite cast_from_to_zextn in *; try crush.
        some_inv; now rewrite BV.bv_zextn_to_N.
      }
      unfold XBV.bitOf, RawXBV.bitOf.
      admit.
      (* TODO: select_bit with the original bitvectors is the same as select bit on the zero-extended values. *)
      (* TODO: Should be provable as long as the index is in-bounds. See below *)
    + clear E. eapply statically_in_bounds_max_bound in s; eauto using to_N_from_bv.
      replace (BV.to_N bv4) with (BV.to_N bv0); cycle 1. {
        erewrite cast_from_to_zextn in *; try crush.
        some_inv; now rewrite BV.bv_zextn_to_N.
      }
      enough (Verilog.expr_type vec <= w)%N by lia.
      replace w with (N.max (Verilog.expr_type vec) (Verilog.expr_type idx)) by admit.
      lia.
  - (* Concatenation *)
    expr_begin_tac.
    apply verilog_smt_match_to_bv.
    apply xbv_concat_to_bv.
  - (* Verilog.IntegerLiteral *)
    expr_begin_tac.
    now constructor.
  - (* Verilog.NamedExpression *)
    funelim (term_for_name vars w n); rewrite <- Heqcall in *; try discriminate; clear Heqcall.
    destruct Hmatch_states with (verilogName := name) (smtName := n__smt).
    { rewrite Hmatch_vars. replace (vars name). reflexivity. }
    (* FIXME: don't reference names *)
    inv H0. 
    expr_begin_tac.
    simpl.
    replace bv with (SMTLib.Value_BitVec w bv0) by congruence.
    constructor.
  - (* Resize *)
    unfold Verilog.expr_type in *.
    edestruct (cast_from_to_part_eval); eauto.
    expr_begin_tac.

    (* expr_begin_tac. *)
    funelim (convert w (XBV.from_bv bv0)); destruct_rew; rewrite <- Heqcall; clear Heqcall.
    + (* Extension *)
      funelim (cast_from_to from to t0); rewrite <- Heqcall in *; clear Heqcall;
        (apply_somewhere N.compare_eq_iff || apply_somewhere N.compare_lt_iff || apply_somewhere N.compare_gt_iff);
        try crush.
      cbn in Hinterp_term; autodestruct_eqn E.
      inster_all.
      eapply verilog_smt_match_to_bv_bits; eauto.
      rewrite XBV.zeros_from_bv.
      apply XBV.concat_to_bv.
    + (* Truncation *)
      funelim (cast_from_to from to t0); rewrite <- Heqcall in *; clear Heqcall;
        (apply_somewhere N.compare_eq_iff || apply_somewhere N.compare_lt_iff || apply_somewhere N.compare_gt_iff);
        try crush.
      cbn in Hinterp_term; autodestruct_eqn E.
      (* replace (N.of_nat (N.to_nat (to - 1))) with (to - 1)%N by lia. *)
      inster_all.
      eapply verilog_smt_match_to_bv_bits.
      * apply XBV.extr_to_bv. lia.
      * simpl. f_equal. lia.
    + funelim (cast_from_to from from t0); rewrite <- Heqcall in *; clear Heqcall;
        (apply_somewhere N.compare_eq_iff || apply_somewhere N.compare_lt_iff || apply_somewhere N.compare_gt_iff);
        try crush.
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
