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

Ltac bitvector_erase :=
  repeat match goal with
         | [ xbv : XBV.xbv _ |- _ ] => destruct xbv
         | [ bv : BV.bitvector _ |- _ ] => destruct bv
         | [ H : RawXBV.size ?xbv = 0%N |- _ ] =>
	   destruct xbv; [|discriminate]; clear H; simpl in *
         | [ H : XBV.to_bv _ = None |- _ ] => rewrite <- XBV.has_x_to_bv in H
         | [ H : ?xbv1 = ?xbv2 |- _ ] =>
	   match type of xbv1 with
	   | XBV.xbv _ =>
	     apply (f_equal XBV.bits) in H; simpl in H
	   | BV.bitvector _ =>
	     apply (f_equal BV.bits) in H; simpl in H
           end
         | [ |- ?xbv1 = ?xbv2] =>
	   match type of xbv1 with
	   | XBV.xbv _ => apply XBV.of_bits_equal; simpl
	   | BV.bitvector _ => apply BV.of_bits_equal; simpl
           end
         | [ |- context[rew _ in _] ] => destruct_rew
	 end;
  unfold XBV.has_x, BV.to_N in *; simpl in *.

Lemma Nat2N_inj_le : forall n m, (N.of_nat n <= N.of_nat m)%N <-> n <= m.
Proof. lia. Qed.

Lemma Nat2N_inj_lt : forall n m, (N.of_nat n < N.of_nat m)%N <-> n < m.
Proof. lia. Qed.

Lemma N2Nat_inj_le : forall n m, (N.to_nat n <= N.to_nat m) <-> (n <= m)%N.
Proof. lia. Qed.

Lemma N2Nat_inj_lt : forall n m, (N.to_nat n < N.to_nat m) <-> (n < m)%N.
Proof. lia. Qed.

Hint Rewrite <- Nat2N.inj_add Nat2N.inj_mul Nat2N.inj_sub Nat2N.inj_min Nat2N.inj_max : N_to_nat.
Hint Rewrite N2Nat.id Nat2N.id : N_to_nat.

Ltac N_to_nat :=
  repeat match goal with
         | [ x : N |- _ ] =>
	 let Heqx := fresh "Heq" in
	 let x_temp := fresh x in
	 remember (N.to_nat x) as x_temp eqn:Heqx;
	 apply (f_equal N.of_nat) in Heqx;
	 rewrite N2Nat.id in Heqx;
	 rewrite <- Heqx in *;
	 clear x Heqx;
	 rename x_temp into x
	 end;
  autorewrite with N_to_nat in *;
  repeat match goal with
         | [ H : (_ <= _)%N |- _ ] => apply Nat2N_inj_le in H
         | [ H : (_ < _)%N |- _ ] => apply Nat2N_inj_lt in H
         | [ |- (_ <= _)%N ] => apply N2Nat_inj_le
         | [ |- (_ < _)%N ] => apply N2Nat_inj_lt
	 | _ => progress (autorewrite with N_to_nat in *)
  end.

Ltac destruct_mins := 
    repeat match goal with
           | [ |- context[N.min ?l ?r] ] =>
	     let Heqmin := fresh "Heqmin" in (
	       destruct (N.min_spec l r) as [[? Heqmin]|[? Heqmin]];
	       rewrite Heqmin in *;
	       clear Heqmin;
	       try lia
	     )
           | [ H : context[N.min ?l ?r] |- _ ] =>
	     let Heqmin := fresh "Heqmin" in (
	       destruct (N.min_spec l r) as [[? Heqmin]|[? Heqmin]];
	       rewrite Heqmin in *;
	       clear Heqmin;
	       try lia
	     )
           | [ |- context[Nat.min ?l ?r] ] =>
	     let Heqmin := fresh "Heqmin" in (
	       destruct (Nat.min_spec l r) as [[? Heqmin]|[? Heqmin]];
	       rewrite Heqmin in *;
	       clear Heqmin;
	       try lia
	     )
           | [ H : context[Nat.min ?l ?r] |- _ ] =>
	     let Heqmin := fresh "Heqmin" in (
	       destruct (Nat.min_spec l r) as [[? Heqmin]|[? Heqmin]];
	       rewrite Heqmin in *;
	       clear Heqmin;
	       try lia
	     )
	   end.

Lemma fold_size bv : N.of_nat (List.length bv) = RawXBV.size bv.
Proof. reflexivity. Qed.

Lemma removelast_cons_size b bs : RawXBV.size (List.removelast (b :: bs)) = RawXBV.size bs.
Proof. unfold RawXBV.size. now rewrite removelast_cons_length. Qed.

Hint Rewrite
  fold_size
  @RawXBV.zeros_size @RawXBV.exes_size @RawXBV.ones_size
  @RawXBV.concat_size @RawXBV.extr_width
  @RawXBV.extract_width @RawXBV.extract_size
  Nat2N.id N2Nat.id Nat2N.inj_min
  @removelast_cons_length removelast_cons_size
  : xbv_size.

Hint Rewrite
  N.leb_le N.leb_gt
  Nat.leb_le Nat.leb_gt
  : kill_bools.

Ltac kill_bools := autorewrite with kill_bools in *.

Program Definition empty : XBV.xbv 0 := {| XBV.bv := [] |}.

Lemma xbv_zero_empty (xbv : XBV.xbv 0) : xbv = empty.
Proof. bitvector_erase. reflexivity. Qed.

Lemma raw_xbv_extract_full w (xbv : RawXBV.xbv) :
  w = N.to_nat (RawXBV.size xbv) ->
  RawXBV.extract xbv 0 w = xbv.
Proof.
  intros.
  subst. unfold RawXBV.size. rewrite Nat2N.id.
  funelim (RawXBV.extract xbv 0 (List.length xbv)); crush.
Qed.

Lemma raw_xbv_extract_empty lo sz (xbv : RawXBV.xbv) :
  sz = 0 ->
  RawXBV.extract xbv lo sz = [].
Proof.
  intros. subst.
  funelim (RawXBV.extract xbv lo 0); crush.
Qed.

Lemma raw_xbv_extr_empty lo sz (xbv : RawXBV.xbv) :
  (sz = 0)%N ->
  RawXBV.extr xbv lo sz = [].
Proof.
  intros. subst. unfold RawXBV.extr.
  rewrite raw_xbv_extract_empty by lia.
  unfold RawXBV.exes; simpl. crush.
Qed.

Lemma xbv_extr_full w (xbv : XBV.xbv w) :
  XBV.extr xbv 0 w = xbv.
Proof.
  bitvector_erase. subst.
  unfold RawXBV.extr. unfold RawXBV.size. autodestruct_eqn E; [|crush].
  rewrite Nat2N.id. simpl. clear E.
  funelim (RawXBV.extract bv 0 (List.length bv)); crush.
Qed.

Lemma raw_xbv_concat_empty1 (xbv1 xbv2 : RawXBV.xbv) :
  (RawXBV.size xbv1 = 0)%N ->
  RawXBV.concat xbv1 xbv2 = xbv2.
Proof. intros. unfold RawXBV.concat. destruct xbv1; [|crush]. now rewrite List.app_nil_r. Qed.

Lemma raw_xbv_concat_empty2 (xbv1 xbv2 : RawXBV.xbv) :
  (RawXBV.size xbv2 = 0)%N ->
  RawXBV.concat xbv1 xbv2 = xbv1.
Proof. intros. unfold RawXBV.concat. destruct xbv2; crush. Qed.

Lemma xbv_concat_empty1 w (xbv1 : XBV.xbv 0) (xbv2 : XBV.xbv w) :
  XBV.concat xbv1 xbv2 = xbv2.
Proof. bitvector_erase. unfold RawXBV.concat. now rewrite List.app_nil_r. Qed.

(* Types don't match for this one (w + 0 is not definitionally equal to w) *)
(* Lemma xbv_concat_empty2 w (xbv1 : XBV.xbv w) (xbv2 : XBV.xbv 0) :
 *   XBV.concat xbv1 xbv2 = xbv1.
 * Proof. bitvector_erase. induction bv. crush. Qed. *)

Lemma zeros_from_bv n : XBV.zeros n = XBV.from_bv (BV.zeros n).
Proof.
  apply XBV.of_bits_equal. simpl. unfold RawBV.zeros, RawXBV.zeros.
  induction n using N.peano_ind; simpl.
  - reflexivity.
  - rewrite N2Nat.inj_succ. simpl. crush.
Qed.

Lemma concat_from_bv n1 n2 bv1 bv2 :
  XBV.concat (XBV.from_bv (n:=n1) bv1) (XBV.from_bv (n:=n2) bv2) = XBV.from_bv (BV.bv_concat bv1 bv2).
Proof.
  apply XBV.of_bits_equal. simpl.
  destruct bv1 as [bv1 wf1], bv2 as [bv2 wf2]. subst. simpl.
  revert bv1.
  induction bv2; crush.
Qed.

Lemma concat_from_bv_inv1 n1 n2 (xbv1 : XBV.xbv n1) (xbv2 : XBV.xbv n2) bv :
  XBV.concat xbv1 xbv2 = XBV.from_bv bv ->
  (exists bv1, xbv1 = XBV.from_bv bv1).
Proof.
  destruct (XBV.to_bv xbv1) as [bv1|] eqn:Hbv1; [apply XBV.bv_xbv_inverse in Hbv1; crush|].
  intros. exfalso.

  bitvector_erase. subst.
  apply (f_equal RawXBV.to_bv) in H.
  rewrite RawXBV.xbv_bv_inverse in H.
  rewrite RawXBV.has_x_to_bv in Hbv1.

  clear wf1. revert bv bv1 H Hbv1.
  induction bv0; intros; [crush|].
  unfold RawXBV.to_bv in *. simpl in *.
  autodestruct_eqn E.
  eauto.
Qed.

Lemma concat_from_bv_inv2 n1 n2 (xbv1 : XBV.xbv n1) (xbv2 : XBV.xbv n2) bv :
  XBV.concat xbv1 xbv2 = XBV.from_bv bv ->
  (exists bv2, xbv2 = XBV.from_bv bv2).
Proof.
  destruct (XBV.to_bv xbv2) as [bv2|] eqn:Hbv2; [apply XBV.bv_xbv_inverse in Hbv2; crush|].
  intros. exfalso.

  bitvector_erase. subst.
  apply (f_equal RawXBV.to_bv) in H.
  rewrite RawXBV.xbv_bv_inverse in H.
  rewrite RawXBV.has_x_to_bv in Hbv2.

  clear wf1. revert bv bv1 H Hbv2.
  induction bv0; intros; [crush|].
  unfold RawXBV.to_bv in *. simpl in *.
  autodestruct_eqn E.
  eauto.
Qed.

Lemma concat_to_bv_none1 n1 n2 (xbv1 : XBV.xbv n1) (xbv2 : XBV.xbv n2) :
  XBV.to_bv xbv1 = None ->
  XBV.to_bv (XBV.concat xbv1 xbv2) = None.
Proof.
  intros.
  destruct (XBV.to_bv (XBV.concat xbv1 xbv2)) eqn:E; [exfalso|reflexivity].
  apply XBV.bv_xbv_inverse in E. symmetry in E.
  apply concat_from_bv_inv1 in E. destruct E. subst.
  rewrite XBV.xbv_bv_inverse in H. discriminate.
Qed.

Lemma concat_to_bv_none2 n1 n2 (xbv1 : XBV.xbv n1) (xbv2 : XBV.xbv n2) :
  XBV.to_bv xbv2 = None ->
  XBV.to_bv (XBV.concat xbv1 xbv2) = None.
Proof.
  intros.
  destruct (XBV.to_bv (XBV.concat xbv1 xbv2)) eqn:E; [exfalso|reflexivity].
  apply XBV.bv_xbv_inverse in E. symmetry in E.
  apply concat_from_bv_inv2 in E. destruct E. subst.
  rewrite XBV.xbv_bv_inverse in H. discriminate.
Qed.

Lemma extend_to_N w1 w2 (xbv : XBV.xbv w1) val :
  XBV.to_N xbv = Some val ->
  XBV.to_N (XBV.concat (XBV.zeros w2) xbv) = Some val.
Proof.
  unfold XBV.to_N. intros.
  destruct (XBV.to_bv xbv) as [bv|] eqn:Hbv; [|discriminate].
  apply XBV.bv_xbv_inverse in Hbv. inv H.
  rewrite zeros_from_bv. rewrite concat_from_bv.
  rewrite XBV.xbv_bv_inverse. simpl. f_equal.
  apply BV.bv_zextn_to_N.
Qed.

Lemma extend_to_N_none2 w1 w2 (xbv1 : XBV.xbv w1) (xbv2 : XBV.xbv w2) :
  XBV.to_N xbv2 = None ->
  XBV.to_N (XBV.concat xbv1 xbv2) = None.
Proof.
  unfold XBV.to_N. intros.
  destruct (XBV.to_bv xbv2) eqn:E; simpl in *; [discriminate|].
  rewrite concat_to_bv_none2; crush.
Qed.

Lemma shr_as_concat_gt (n : nat) (xbv : RawXBV.xbv) :
  (List.length xbv < n) ->
  RawXBV.shr xbv n = RawXBV.zeros (RawXBV.size xbv).
Proof.
  funelim (RawXBV.shr xbv n); intros; unfold RawXBV.zeros; simpl in *.
  - destruct bv; crush.
  - reflexivity.
  - insterU H.
    unfold RawXBV.zeros in *.
    rewrite Pnat.SuccNat2Pos.id_succ.
    rewrite Nat2N.id in *.
    simpl. rewrite H.
    clear Heqcall H0 H.
    induction (List.length bs); crush.
Qed.

Lemma shr_as_concat_le (n : nat) (xbv : RawXBV.xbv) :
  (n <= List.length xbv) ->
  RawXBV.shr xbv n =
    RawXBV.concat
      (RawXBV.zeros (N.of_nat n))
      (RawXBV.extr xbv (N.of_nat n) (RawXBV.size xbv - N.of_nat n)).
Proof.
  unfold RawXBV.zeros, RawXBV.concat, RawXBV.extr, RawXBV.size.
  simpl. rewrite Nat2N.id.
  intros.
  autodestruct_eqn E; kill_bools; try lia.
  funelim (RawXBV.shr xbv n); [idtac|crush|idtac].
  + simpl in *.
    rewrite raw_xbv_extract_full. 
    * now rewrite List.app_nil_r. 
    * unfold RawXBV.size. lia.
  + insterU H. simp extract.
    rewrite H. clear H.
    rewrite ! N2Nat.inj_sub, ! Nat2N.id.
    simpl.
    rewrite <- List.app_assoc. f_equal.
    clear E H0 Heqcall. induction n; crush.
Qed.

Lemma shr_as_concat (n : nat) (xbv : RawXBV.xbv) :
  RawXBV.shr xbv n =
    RawXBV.concat
      (RawXBV.zeros (N.of_nat (min (List.length xbv) n)))
      (RawXBV.extr xbv (N.of_nat n) (RawXBV.size xbv - N.of_nat n)).
Proof.
  destruct (Nat.leb n (List.length xbv)) eqn:E; kill_bools.
  - rewrite Nat.min_r by lia.
    apply shr_as_concat_le. lia.
  - rewrite Nat.min_l by lia.
    rewrite shr_as_concat_gt by lia.
    unfold RawXBV.extr.
    autodestruct_eqn Hcmp; [crush|clear Hcmp].
    rewrite raw_xbv_concat_empty2. reflexivity.
    rewrite RawXBV.exes_size. unfold RawXBV.size. lia.
Qed.

Lemma shl_as_concat_gt (n : nat) (xbv : RawXBV.xbv) :
  (List.length xbv < n) ->
  RawXBV.shl xbv n = RawXBV.zeros (RawXBV.size xbv).
Proof.
  funelim (RawXBV.shl xbv n); intros.
  - destruct bv; crush.
  - reflexivity.
  - insterU H.
    autorewrite with xbv_size in *.
    unfold RawXBV.size, RawXBV.zeros in *. cbn [List.length] in *.
    erewrite H by lia. N_to_nat. reflexivity.
Qed.

Lemma rawxbv_extract_remove_last n l:
  n < List.length l ->
  RawXBV.extract (List.removelast l) 0 n = RawXBV.extract l 0 n.
Proof.
  revert n.
  induction l; intros.
  - destruct n; [|crush]. reflexivity.
  - simpl in H.
    destruct n; [rewrite ! raw_xbv_extract_empty; crush|].
    simp extract. destruct l; [crush|].
    simpl. simp extract.
    f_equal. apply IHl. lia.
Qed.

Lemma shl_as_concat_le (n : nat) (xbv : RawXBV.xbv) :
  (n <= List.length xbv) ->
  RawXBV.shl xbv n =
    RawXBV.concat
      (RawXBV.extr xbv 0 (RawXBV.size xbv - N.of_nat n))
      (RawXBV.zeros (N.of_nat n)).
Proof.
  unfold RawXBV.zeros, RawXBV.concat, RawXBV.extr, RawXBV.size.
  simpl. rewrite Nat2N.id.
  intros.
  autodestruct_eqn E; kill_bools; N_to_nat; try lia.
  funelim (RawXBV.shl xbv n); [idtac|crush|idtac].
  + simpl in *.
    rewrite raw_xbv_extract_full. 
    * reflexivity.
    * unfold RawXBV.size. lia.
  + insterU H. simp extract.
    rewrite H by (autorewrite with xbv_size in *; crush).
    clear H. cbn [List.repeat List.app]. do 2 f_equal.
    autorewrite with xbv_size.
    apply rawxbv_extract_remove_last.
    lia.
Qed.

(* TO BE UPDATED *)
Lemma shl_as_concat (n : nat) (xbv : RawXBV.xbv) :
  RawXBV.shl xbv n =
    RawXBV.concat
      (RawXBV.extr xbv 0 (RawXBV.size xbv - N.of_nat n))
      (RawXBV.zeros (N.of_nat (min (List.length xbv) n)))
      .
Proof.
  destruct (Nat.leb n (List.length xbv)) eqn:E; kill_bools.
  - rewrite Nat.min_r by lia.
    apply shl_as_concat_le. lia.
  - rewrite Nat.min_l by lia.
    rewrite shl_as_concat_gt by lia.
    unfold RawXBV.extr.
    autodestruct_eqn Hcmp; kill_bools; [|crush].
    rewrite raw_xbv_concat_empty1. reflexivity.
    autorewrite with xbv_size. unfold RawXBV.size in *. lia.
Qed.

Lemma extract_width x i j :
  (j + i <= List.length x) ->
  List.length (RawXBV.extract x i j) = (Nat.min j (List.length x - i)).
Proof.
  funelim (RawXBV.extract x i j);
    simp extract; simpl in *; try crush.
Qed.

Lemma rawxbv_extr_of_concat_lo xbv_hi xbv_lo lo sz :
  (lo <= RawXBV.size xbv_lo)%N ->
  (lo + sz <= RawXBV.size xbv_lo)%N ->
  RawXBV.extr (RawXBV.concat xbv_hi xbv_lo) lo sz = RawXBV.extr xbv_lo lo sz.
Proof.
  intros Hlo Hhi.
  unfold RawXBV.extr.
  autodestruct_eqn E; kill_bools;
    autorewrite with xbv_size in *;
    try lia; [idtac].
  clear E E0.
  N_to_nat. unfold RawXBV.concat.
  funelim (RawXBV.extract xbv_lo lo sz).
  - simpl in *.
    replace i with 0 by lia.
    replace j with 0 by lia. 
    destruct xbv_hi; simp extract; reflexivity.
  - simpl in *. simp extract. reflexivity.
  - simpl in *. simp extract.
    erewrite H; try crush.
  - simpl in *. simp extract. eapply H; lia.
Qed.

Lemma rawxbv_extr_of_concat_hi xbv_hi xbv_lo lo sz :
  (RawXBV.size xbv_lo <= lo)%N ->
  (lo + sz <= RawXBV.size xbv_lo + RawXBV.size xbv_hi)%N ->
  RawXBV.extr (RawXBV.concat xbv_hi xbv_lo) lo sz =
    RawXBV.extr xbv_hi (lo - RawXBV.size xbv_lo) sz.
Proof.
  intros Hlo Hhi.
  unfold RawXBV.extr.
  autodestruct_eqn E; kill_bools;
    autorewrite with xbv_size in *;
    try lia; [idtac].
  clear E E0.
  unfold RawXBV.size, RawXBV.concat in *.
  N_to_nat.
  funelim (RawXBV.extract (xbv_lo ++ xbv_hi) lo sz); intros.
  - symmetry in H. apply List.app_eq_nil in H.
    destruct H. subst. simp extract. reflexivity.
  - destruct xbv_lo; [|crush]. simpl.
    destruct xbv_hi; now simp extract.
  - destruct xbv_lo; [|crush]. simpl in *. subst.
    simp extract. reflexivity.
  - destruct xbv_lo; simpl in *.
    + subst. simp extract. reflexivity.
    + inv H0. eapply H; crush.
Qed.

Lemma rawxbv_extr_of_concat_mid xbv_hi xbv_lo lo sz :
  (lo <= RawXBV.size xbv_lo)%N ->
  (RawXBV.size xbv_lo <= lo + sz)%N ->
  (lo + sz <= RawXBV.size xbv_lo + RawXBV.size xbv_hi)%N ->
  RawXBV.extr (RawXBV.concat xbv_hi xbv_lo) lo sz =
    RawXBV.concat
      (RawXBV.extr xbv_hi (lo - RawXBV.size xbv_lo)%N (sz - (RawXBV.size xbv_lo - lo))%N)
      (RawXBV.extr xbv_lo lo (RawXBV.size xbv_lo - lo)%N).
Proof.
  intros Hlo Hmid Hhi.
  unfold RawXBV.extr.
  autodestruct_eqn E; kill_bools;
    autorewrite with xbv_size in *;
    try lia; [idtac].
  clear E E0 E1.
  unfold RawXBV.size, RawXBV.concat in *.
  N_to_nat.
  funelim (RawXBV.extract (xbv_lo ++ xbv_hi) lo sz); intros.
  - symmetry in H. apply List.app_eq_nil in H.
    destruct H. subst. simp extract. reflexivity.
  - destruct xbv_lo; [|crush]. simpl.
    destruct xbv_hi; now simp extract.
  - destruct xbv_lo.
    + simpl in *. subst. simpl. simp extract. simpl.
      repeat f_equal.
    + simpl in *. inv H0. simp extract. simpl. f_equal.
      erewrite H by crush.
      repeat f_equal; try crush.
  - destruct xbv_lo; [crush|]. simpl in *. simp extract.
    inv H0. erewrite H by crush.
    f_equal.
Qed.

Lemma rawxbv_extr_of_concat xbv_hi xbv_lo lo sz :
  (lo + sz <= RawXBV.size xbv_hi + RawXBV.size xbv_lo)%N ->
  RawXBV.extr (RawXBV.concat xbv_hi xbv_lo) lo sz =
    RawXBV.concat
      (RawXBV.extr xbv_hi (lo - RawXBV.size xbv_lo) (sz - (RawXBV.size xbv_lo - lo)))%N
      (RawXBV.extr xbv_lo lo (N.min sz (RawXBV.size xbv_lo - lo)))%N.
Proof.
  intros.
  destruct (dec (RawXBV.size xbv_lo <= lo)%N);
    destruct (dec (lo + sz < RawXBV.size xbv_lo))%N; try lia.
  - replace (N.min sz (RawXBV.size xbv_lo - lo)) with (RawXBV.size xbv_lo - lo)%N by lia.
    replace (RawXBV.size xbv_lo - lo)%N with 0%N by lia.
    erewrite rawxbv_extr_of_concat_hi by lia.
    rewrite raw_xbv_concat_empty2 by (autorewrite with xbv_size; lia).
    f_equal. lia.
  - replace (N.min sz (RawXBV.size xbv_lo - lo)) with sz by lia.
    replace (sz - (RawXBV.size xbv_lo - lo))%N with 0%N by lia.
    erewrite rawxbv_extr_of_concat_lo by lia.
    rewrite raw_xbv_concat_empty1 by (autorewrite with xbv_size; lia).
    reflexivity.
  - replace (N.min sz (RawXBV.size xbv_lo - lo)) with (RawXBV.size xbv_lo - lo)%N by lia.
    eapply rawxbv_extr_of_concat_mid; lia.
Qed.

Lemma rawxbv_extr_of_zeros w lo sz :
  (lo + sz <= w)%N ->
  RawXBV.extr (RawXBV.zeros w) lo sz = RawXBV.zeros sz.
Proof.
  intros. unfold RawXBV.extr.
  autorewrite with xbv_size. autodestruct_eqn E; [clear E|crush].
  unfold RawXBV.zeros.
  N_to_nat.
  revert lo sz H.
  induction w; intros; simpl; simp extract.
  - replace sz with 0; crush.
  - destruct lo, sz; simpl; simp extract.
    + reflexivity.
    + erewrite IHw; crush.
    + erewrite IHw; crush.
    + erewrite IHw; crush.
Qed.

Lemma rawxbv_extr_of_extr lo1 lo2 sz1 sz2 xbv :
  (lo1 + sz1 <= RawXBV.size xbv)%N ->
  (lo2 + sz2 <= sz1)%N ->
  RawXBV.extr (RawXBV.extr xbv lo1 sz1) lo2 sz2 = RawXBV.extr xbv (lo1 + lo2) sz2.
Proof.
  intros H0 H1.
  unfold RawXBV.extr.
  autodestruct_eqn E;
    autorewrite with xbv_size kill_bools in *;
    try crush; N_to_nat.
  clear E E0 E1.
  revert sz1 H0 H1.
  funelim (RawXBV.extract xbv (lo1 + lo2) sz2).
  - intros. simp extract. reflexivity.
  - intros.
    replace lo2 with 0 in * by lia.
    destruct (RawXBV.extract (bx :: x') lo1 sz1); simp extract; reflexivity.
  - intros. simpl in *. clear Heqcall.
    replace lo1 with 0 in * by crush.
    replace lo2 with 0 in * by crush.
    destruct sz1; [lia|].
    simp extract.
    erewrite H; crush.
  - intros. simpl in *. clear Heqcall.
    destruct lo1, sz1;
      simpl in *; subst; simp extract.
    + lia.
    + erewrite H; crush.
    + erewrite H; crush.
    + erewrite H; crush.
Qed.

Lemma concat_assoc x1 x2 x3 :
  RawXBV.concat x1 (RawXBV.concat x2 x3) = RawXBV.concat (RawXBV.concat x1 x2) x3.
Proof. unfold RawXBV.concat. now rewrite List.app_assoc. Qed.

Lemma concat_zeros w1 w2 :
  RawXBV.concat (RawXBV.zeros w1) (RawXBV.zeros w2) = RawXBV.zeros (w1 + w2).
Proof.
  unfold RawXBV.zeros, RawXBV.concat.
  rewrite <- List.repeat_app. f_equal. lia.
Qed.

Lemma raw_xbv_shr_overshift xbv shamt :
  (N.of_nat shamt >= RawXBV.size xbv)%N ->
  RawXBV.shr xbv shamt = RawXBV.zeros (RawXBV.size xbv).
Proof.
  intros.
  unfold RawXBV.size, RawXBV.zeros in *.
  N_to_nat.
  funelim (RawXBV.shr xbv shamt).
  - destruct bv; crush.
  - reflexivity.
  - cbn [List.length] in *.
    rewrite H by lia. clear H H0 Heqcall.
    induction (List.length bs); crush.
Qed.

Lemma xbv_shr_overshift w (xbv : XBV.xbv w) shamt :
  (shamt >= w)%N ->
  XBV.shr xbv shamt = XBV.zeros w.
Proof.
  intros.
  bitvector_erase. subst.
  erewrite raw_xbv_shr_overshift; unfold RawXBV.size in *; crush.
Qed.

Lemma extr_shr_extend_overshift w1 w2 (xbv : XBV.xbv w1) shamt  :
  (shamt > w1)%N ->
  XBV.extr (XBV.shr (XBV.concat (XBV.zeros w2) xbv) shamt) 0 w1 =
  XBV.shr xbv shamt.
Proof.
  intros. bitvector_erase.
  destruct (dec (shamt >= w2 + w1))%N.
  - subst.
    rewrite ! raw_xbv_shr_overshift by (autorewrite with xbv_size; crush).
    autorewrite with xbv_size.
    eapply rawxbv_extr_of_zeros. lia.
  - subst.
    rewrite ! raw_xbv_shr_overshift with (xbv:=bv) by (autorewrite with xbv_size; crush).
    rewrite ! shr_as_concat.
    rewrite ! N2Nat.id.
    fold (RawXBV.size bv) in *.
    autorewrite with xbv_size.
    rewrite rawxbv_extr_of_concat with (xbv_lo := bv) by (autorewrite with xbv_size; lia).
    destruct_mins.
    erewrite rawxbv_extr_of_zeros by lia.
    erewrite concat_assoc.
    erewrite concat_zeros.
    erewrite raw_xbv_extr_empty with (xbv := bv) by lia.
    erewrite raw_xbv_concat_empty2 by reflexivity.
    erewrite rawxbv_extr_of_zeros; crush.
Qed.

Lemma extr_shr_extend_no_overshift w1 w2 (xbv : XBV.xbv w1) shamt  :
  (shamt <= w1)%N ->
  XBV.extr (XBV.shr (XBV.concat (XBV.zeros w2) xbv) shamt) 0 w1 =
  XBV.shr xbv shamt.
Proof.
  intros.
  bitvector_erase. subst.
  rewrite ! shr_as_concat.
  rewrite ! N2Nat.id.
  fold (RawXBV.size bv) in *.
  autorewrite with xbv_size.
  rewrite ! rawxbv_extr_of_concat by (autorewrite with xbv_size; lia).
  rewrite rawxbv_extr_of_zeros by (autorewrite with xbv_size; lia).
  rewrite rawxbv_extr_of_zeros by (autorewrite with xbv_size; lia).
  rewrite rawxbv_extr_of_zeros by (autorewrite with xbv_size; lia).
  rewrite concat_assoc.
  rewrite concat_zeros.
  rewrite rawxbv_extr_of_extr by (autorewrite with xbv_size; lia).
  autorewrite with xbv_size.
  f_equal; f_equal; lia.
Qed.

Lemma extr_shr_extend w1 w2 (xbv : XBV.xbv w1) shamt  :
  XBV.extr (XBV.shr (XBV.concat (XBV.zeros w2) xbv) shamt) 0 w1 =
  XBV.shr xbv shamt.
Proof.
  destruct (dec (shamt <= w1))%N.
  - eapply extr_shr_extend_no_overshift. eassumption.
  - eapply extr_shr_extend_overshift. lia.
Qed.


Lemma raw_xbv_shl_overshift xbv shamt :
  (N.of_nat shamt >= RawXBV.size xbv)%N ->
  RawXBV.shl xbv shamt = RawXBV.zeros (RawXBV.size xbv).
Proof.
  intros.
  unfold RawXBV.size, RawXBV.zeros in *.
  N_to_nat.
  funelim (RawXBV.shl xbv shamt).
  - destruct bv; crush.
  - reflexivity.
  - cbn [List.length] in *.
    erewrite H by (autorewrite with xbv_size; crush).
    autorewrite with xbv_size.
    crush.
Qed.

Lemma xbv_shl_overshift w (xbv : XBV.xbv w) shamt :
  (shamt >= w)%N ->
  XBV.shl xbv shamt = XBV.zeros w.
Proof.
  intros.
  bitvector_erase. subst.
  erewrite raw_xbv_shl_overshift; unfold RawXBV.size in *; crush.
Qed.

Lemma extr_shl_extend_overshift w1 w2 (xbv : XBV.xbv w1) shamt  :
  (shamt > w1)%N ->
  XBV.extr (XBV.shl (XBV.concat (XBV.zeros w2) xbv) shamt) 0 w1 =
  XBV.shl xbv shamt.
Proof.
  intros. bitvector_erase.
  destruct (dec (shamt >= w2 + w1))%N.
  - subst.
    rewrite ! raw_xbv_shl_overshift by (autorewrite with xbv_size; crush).
    autorewrite with xbv_size.
    eapply rawxbv_extr_of_zeros. lia.
  - subst.
    rewrite ! raw_xbv_shl_overshift with (xbv:=bv) by (autorewrite with xbv_size; crush).
    rewrite ! shl_as_concat.
    rewrite ! N2Nat.id.
    fold (RawXBV.size bv) in *.
    autorewrite with xbv_size.
    rewrite rawxbv_extr_of_concat with (xbv_lo := bv) by (autorewrite with xbv_size; lia).
    rewrite rawxbv_extr_of_concat_lo by (autorewrite with xbv_size; crush).
    apply rawxbv_extr_of_zeros. lia.
Qed.

Lemma extr_shl_extend_no_overshift w1 w2 (xbv : XBV.xbv w1) shamt  :
  (shamt <= w1)%N ->
  XBV.extr (XBV.shl (XBV.concat (XBV.zeros w2) xbv) shamt) 0 w1 =
  XBV.shl xbv shamt.
Proof.
  intros.
  bitvector_erase. subst.
  rewrite ! shl_as_concat.
  rewrite ! N2Nat.id.
  fold (RawXBV.size bv) in *.
  autorewrite with xbv_size.
  rewrite ! rawxbv_extr_of_concat by (autorewrite with xbv_size; lia).
  rewrite ! rawxbv_extr_of_zeros by (autorewrite with xbv_size; lia).
  rewrite rawxbv_extr_of_extr by (autorewrite with xbv_size; lia).
  autorewrite with xbv_size.
  f_equal.
  - rewrite raw_xbv_concat_empty1 by (autorewrite with xbv_size; lia).
    f_equal; crush.
  - f_equal. crush.
Qed.

Lemma extr_shl_extend w1 w2 (xbv : XBV.xbv w1) shamt :
  XBV.extr (XBV.shl (XBV.concat (XBV.zeros w2) xbv) shamt) 0 w1 =
  XBV.shl xbv shamt.
Proof.
  destruct (dec (shamt <= w1))%N.
  - eapply extr_shl_extend_no_overshift. eassumption.
  - eapply extr_shl_extend_overshift. lia.
Qed.

Lemma extr_exes n1 n2 lo :
  XBV.extr (XBV.exes n1) lo n2 = XBV.exes n2.
Proof.
  bitvector_erase. repeat unfold RawXBV.extr.
  rewrite RawXBV.exes_size.
  autodestruct_eqn E; kill_bools; [|reflexivity].
  unfold RawXBV.exes.

  N_to_nat.
  remember (List.repeat X n1) as xs.	 
  funelim (RawXBV.extract xs lo n2).
  - destruct n1; [|crush].
    replace j with 0; crush.
  - destruct n1; crush.
  - destruct n1; [crush|].
    (* rewrite ! Nat2N.inj_succ in *. *)
    simpl in *. specialize (H n1). insterU H.
    crush.
  - destruct n1; [crush|].
    simpl in *. specialize (H n1). insterU H.
    crush.
Qed.

(* Move me to bitvector *)
Lemma bv_shr_swap_definition w lhs rhs :
  BV.bv_shr (n:=w) lhs rhs = BV.shr lhs (BV.to_N rhs).
Proof.
 bitvector_erase.
 unfold RawBV.bv_shr, RawBV.to_N in *.
 rewrite wf, wf0, N.eqb_refl, Nat2N.id in *.
 clear wf wf0.
 unfold RawBV.shr_be.
 rewrite RawBV.shr_be_nicify.
 generalize dependent (RawBV.list2nat_be bv).
 intros shamt. clear w bv.
 unfold RawBV.size in *.
 funelim (RawBV.shr bv0 shamt).
 - destruct bv; simp nice_nshr_be; reflexivity.
 - simp nice_nshr_be. crush.
 - simp nice_nshr_be. crush.
Qed.

Lemma bv_shl_swap_definition w lhs rhs :
  BV.bv_shl (n:=w) lhs rhs = BV.shl lhs (BV.to_N rhs).
Proof.
 bitvector_erase.
 unfold RawBV.bv_shl, RawBV.to_N in *.
 rewrite wf, wf0, N.eqb_refl, Nat2N.id in *.
 clear wf wf0.
 unfold RawBV.shl_be.
 rewrite RawBV.shl_be_nicify.
 generalize dependent (RawBV.list2nat_be bv).
 intros shamt. clear w bv.
 unfold RawBV.size in *.
 funelim (RawBV.shl bv0 shamt).
 - destruct bv; simp nice_nshl_be; reflexivity.
 - simp nice_nshl_be. crush.
 - simp nice_nshl_be. crush.
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
  rewrite List.map_app.
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

Lemma bv_extr_one_bit (n : N) w (bv : BV.bitvector w) :
  (1 + n <= w)%N ->
  BV.bv_extr n 1 bv = BV.of_bits [BV.bitOf (N.to_nat n) bv].
Proof.
  destruct bv as [bv wf].
  subst. intros.
  apply BV.of_bits_equal.
  simpl.
  unfold BV.bv_extr, RawBV.bv_extr, RawBV.size in *.
  autodestruct_eqn E; try (rewrite N.ltb_lt in *; lia); clear E.
  replace (N.to_nat (1 + n)) with (S (N.to_nat n)) by lia.
  assert (S (N.to_nat n) <= List.length bv) as H' by lia. clear H. revert H'.
  generalize (N.to_nat n). clear n. intros n H.
  revert bv H.
  induction n; intros.
  { destruct bv; try crush.
    destruct bv; crush.
  }
  destruct bv; try crush.
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
    by (rewrite List.length_map; lia).
  replace O with (RawXBV.bool_to_bit false)
    by reflexivity.
  apply List.map_nth.
Qed.

Definition select_bit_bv {w1 w2} (vec : BV.bitvector w1) (idx : BV.bitvector w2) : BV.bitvector 1 :=
  BV.of_bits [BV.bitOf (N.to_nat (BV.to_N idx)) vec].

Lemma to_bv_some_raw_iff w (xbv : XBV.xbv w) (bv : BV.bitvector w) :
  XBV.to_bv xbv = Some bv <-> RawXBV.to_bv (XBV.bits xbv) = Some (BV.bits bv).
Proof.
  (* This is disgusting (written while half asleep) plzfix *)
  split; intros; simpl in *.
  - apply XBV.bv_xbv_inverse in H. subst.
    destruct bv as [bv bv_wf].
    simpl. apply RawXBV.xbv_bv_inverse.
  - apply RawXBV.bv_xbv_inverse in H.
    destruct bv as [bv bv_wf].
    simpl in *.
    funelim (XBV.to_bv xbv).
    + unfold XBV.raw_to_bv_with_proof in *.
      rewrite e in Heq. inv Heq.
      f_equal.
      apply BV.of_bits_equal.
      simpl. destruct_rew.
      destruct v as [v v_wf].
      unfold XBV.bits, XBV.bv, RawBV.of_bits in *. simpl in *. subst.
      rewrite RawXBV.xbv_bv_inverse in e.
      inv e.
      reflexivity.
    + destruct v as [v v_wf].
      simpl in *. subst.
      clear Heq.
      rewrite RawXBV.xbv_bv_inverse in prf.
      discriminate.
Qed.

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


(* Move me to common *)
Lemma map_removelast {A B} (f : A -> B) (l : list A) :
  List.map f (List.removelast l) = List.removelast (List.map f l).
Proof.
  induction l; simpl; [reflexivity|].
  destruct l; simpl in *; [reflexivity|].
  now rewrite IHl.
Qed.

Lemma shl_to_bv n vec shamt :
  XBV.to_bv (XBV.shl (XBV.from_bv vec) shamt) = Some (BV.shl (n:=n) vec shamt).
Proof.
  unfold BV.to_N, BV.shl.
  intros.
  destruct vec as [vec vec_wf].
  rewrite <- XBV.xbv_bv_inverse. f_equal.
  apply XBV.of_bits_equal; simpl.
  generalize dependent (N.to_nat shamt). clear shamt. intro shamt.
  funelim (RawBV.shl vec shamt).
  - reflexivity.
  - reflexivity.
  - insterU H.
    unfold RawXBV.from_bv in *. cbn [List.map].
    simp shl. repeat f_equal.
    rewrite map_removelast in *.
    cbn [List.map] in H.
    apply H.
Qed.

Lemma shr_to_bv n vec shamt :
  XBV.to_bv (XBV.shr (XBV.from_bv vec) shamt) = Some (BV.shr (n:=n) vec shamt).
Proof.
  unfold BV.to_N, BV.shr.
  intros.
  destruct vec as [vec vec_wf].
  rewrite <- XBV.xbv_bv_inverse. f_equal.
  apply XBV.of_bits_equal; simpl.
  generalize dependent (N.to_nat shamt). clear shamt. intro shamt.
  funelim (RawBV.shr vec shamt); simpl; simp shr.
  - reflexivity.
  - reflexivity.
  - unfold RawXBV.from_bv in *.
    rewrite List.map_app. simpl. repeat f_equal.
    eauto.
Qed.

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
    by (rewrite List.length_map; lia).
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
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.

Lemma convert_no_exes w_from w_to (from : BV.bitvector w_from) :
  convert w_to (XBV.from_bv from) = XBV.from_bv (convert_bv w_to from).
Proof.
  funelim (convert w_to (XBV.from_bv from));
    try destruct_rew; clear Heqcall.
  - rewrite XBV.zeros_from_bv.
    rewrite xbv_concat_no_exes. simpl.
    funelim (convert_bv (to - from + from) from0); [|lia|lia].
    clear Heqcall.
    apply XBV.of_bits_equal.
    destruct_rew.
    repeat f_equal.
    crush.
  - rewrite XBV.extr_no_exes by crush.
    funelim (convert_bv to from0); [lia| |lia].
    reflexivity.
  - funelim (convert_bv from from0); [lia|lia|].
    now rewrite <- eq_rect_eq.
Qed.

Lemma convert_from_bv w_from w_to (from : BV.bitvector w_from) :
  exists bv : BV.bitvector w_to, XBV.to_bv (convert w_to (XBV.from_bv from)) = Some bv.
Proof.
  funelim (convert w_to (XBV.from_bv from));
    try destruct_rew; try rewrite <- Heqcall; clear Heqcall; simpl.
  - rewrite XBV.zeros_from_bv, XBV.concat_to_bv.
    eauto.
  - rewrite XBV.extr_no_exes by crush.
    rewrite XBV.xbv_bv_inverse.
    eauto.
  - rewrite XBV.xbv_bv_inverse.
    eauto.
Qed.

Lemma eval_arithmeticop_to_bv op w (lhs rhs : BV.bitvector w) :
  exists bv, XBV.to_bv (eval_arithmeticop op (XBV.from_bv lhs) (XBV.from_bv rhs)) = Some bv.
Proof.
  destruct op; simp eval_arithmeticop.
  - funelim (bv_binop (BV.bv_add (n:=w)) (XBV.from_bv lhs) (XBV.from_bv rhs));
      rewrite XBV.xbv_bv_inverse in *; crush.
  - funelim (bv_binop (fun bvl bvr : BV.bitvector w => BV.bv_subt bvl bvr) (XBV.from_bv lhs) (XBV.from_bv rhs));
      rewrite XBV.xbv_bv_inverse in *;
      crush.
  - funelim (bv_binop (BV.bv_mult (n:=w)) (XBV.from_bv lhs) (XBV.from_bv rhs));
      rewrite XBV.xbv_bv_inverse in *;
      crush.
Qed.

Lemma eval_bitwiseop_to_bv op w (lhs rhs : BV.bitvector w) :
  exists bv, XBV.to_bv (eval_bitwiseop op (XBV.from_bv lhs) (XBV.from_bv rhs)) = Some bv.
Proof.
  destruct op; simp eval_bitwiseop.
  - (* andb *)
    erewrite bitwise_and_no_exes;
      try erewrite XBV.xbv_bv_inverse;
      try crush.
  - (* orb *)
    erewrite bitwise_or_no_exes;
      try erewrite XBV.xbv_bv_inverse;
      try crush.
Qed.

Lemma eval_shiftop_to_bv op w1 w2 (lhs : BV.bitvector w1) (rhs : BV.bitvector w2) :
  exists bv, XBV.to_bv (eval_shiftop op (XBV.from_bv lhs) (XBV.from_bv rhs)) = Some bv.
Proof.
  destruct op; simp eval_shiftop.
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

Lemma eval_arithmeticop_no_exes op w (lhs rhs : BV.bitvector w) :
  exists bv, eval_arithmeticop op (XBV.from_bv lhs) (XBV.from_bv rhs) = XBV.from_bv bv.
Proof.
  edestruct eval_arithmeticop_to_bv as [bv Hbv].
  exists bv.
  apply XBV.bv_xbv_inverse in Hbv.
  crush.
Qed.

Lemma eval_bitwiseop_no_exes op w (lhs rhs : BV.bitvector w) :
  exists bv, eval_bitwiseop op (XBV.from_bv lhs) (XBV.from_bv rhs) = XBV.from_bv bv.
Proof.
  edestruct eval_bitwiseop_to_bv as [bv Hbv].
  exists bv.
  apply XBV.bv_xbv_inverse in Hbv.
  crush.
Qed.

Lemma eval_shiftop_no_exes op w1 w2 (lhs : BV.bitvector w1) (rhs : BV.bitvector w2) :
  exists bv, eval_shiftop op (XBV.from_bv lhs) (XBV.from_bv rhs) = XBV.from_bv bv.
Proof.
  edestruct eval_shiftop_to_bv as [bv Hbv].
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

Lemma cast_from_to_part_eval ρ from to t w1 bv1:
  SMTLib.interp_term ρ (cast_from_to from to t) = Some (SMTLib.Value_BitVec w1 bv1) ->
  exists w2 bv2, SMTLib.interp_term ρ t = Some (SMTLib.Value_BitVec w2 bv2).
Proof.
  funelim (cast_from_to from to t); crush.
Qed.

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
  - (* arithmeticop *)
    edestruct eval_arithmeticop_no_exes as [bv Hbv].
    exists bv. now rewrite Hbv.
  - (* bitwiseop *)
    edestruct eval_bitwiseop_no_exes as [bv Hbv].
    exists bv. now rewrite Hbv.
  - (* shiftop *)
    edestruct eval_shiftop_no_exes as [bv Hbv].
    exists bv. now erewrite Hbv.
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
    erewrite shr_to_bv in *.
    rewrite bv_shr_swap_definition.
    now some_inv.
  - rewrite XBV.to_N_from_bv in *. simpl in *.
    erewrite shl_to_bv in *.
    rewrite bv_shl_swap_definition.
    now some_inv.
  - rewrite XBV.to_N_from_bv in *. simpl in *.
    erewrite shl_to_bv in *.
    rewrite bv_shl_swap_definition.
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

Lemma bv_shr_as_select w (vec : BV.bitvector w) (idx : BV.bitvector w) :
  (w > 0)%N ->
  BV.bv_extr 0 1 (BV.bv_shr vec idx) =
    BV.of_bits [BV.bitOf (N.to_nat (BV.to_N idx)) vec]%list.
Proof.
  intros Hbound.
  rewrite bv_extr_one_bit; try crush.
  apply BV.of_bits_equal. simpl.
  do 2 f_equal.
  unfold BV.bitOf, BV.bv_shr.
  destruct vec as [vec vec_wf].
  destruct idx as [idx idx_wf].
  simpl.
  unfold BV.to_N, RawBV.to_N, BV.bv_shr, RawBV.bv_shr, RawBV.shr_be, RawBV.size in *.
  simpl.
  rewrite vec_wf, idx_wf, N.eqb_refl.
  generalize (RawBV.list2nat_be idx). clear idx idx_wf. intro n.
  destruct n, vec; try crush.
  unfold RawBV.bitOf.
  rewrite RawBV.shr_be_nicify. simp nice_nshr_be. rewrite Nat2N.id. simpl.
  clear b vec_wf.
  funelim (RawBV.nice_nshr_be vec n); simp nice_nshr_be; try crush.
  destruct (RawBV.nice_nshr_be bs n); crush.
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
  rewrite bv_shr_as_select by lia.
  rewrite bit_of_as_bv in Heval by lia.
  do 2 f_equal.
  destruct_rew.
  rewrite to_N_convert_bv_extn by lia.
  rewrite bitOf_convert_bv_extn by lia.
  (* Ugly, but it's hard to extract a lemma - the widths don't match up *)
  apply to_bv_some_raw_iff in Heval. simpl in Heval.
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
  - destruct_rew. simpl. apply extend_to_N. assumption.
  - destruct_rew. simpl. assumption.
Qed.

Lemma convert_extend_to_N_none from to (xbv : XBV.xbv from) :
  (to >= from)%N ->
  XBV.to_N xbv = None ->
  XBV.to_N (convert to xbv) = None.
Proof.
  intros.
  funelim (convert to xbv).
  - destruct_rew. simpl. apply extend_to_N_none2. assumption.
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
    apply extr_shr_extend.
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
    apply extr_shl_extend.
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
  - apply extr_exes.
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
