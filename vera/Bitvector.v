From Stdlib Require Import Arith.
From Stdlib Require Import NArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Psatz.
From Stdlib Require Import String.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Logic.ProofIrrelevance.


From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Data.Monads.OptionMonad.
From ExtLib Require Import Data.List.

From vera Require Import Tactics.
From vera Require Import Common.
From vera Require Import BVList.
From vera Require Import Decidable.

From Equations Require Import Equations.

Import EqNotations.
Import SigTNotations.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope bv_scope.

Set Bullet Behavior "Strict Subproofs".

#[global] Hint Rewrite Nat2N.id N2Nat.id @removelast_cons_length : xbv_size.
Hint Rewrite Nat2N.inj_add Nat2N.inj_mul Nat2N.inj_sub Nat2N.inj_min Nat2N.inj_max : xbv_size.

Module RawBV.
  Include RAWBITVECTOR_LIST.
  Notation t := bitvector.
  (* Definition some_bitvector := {n : _ & bitvector n}. *)
  Definition is_zero (a : bitvector) :=
    bv_eq a (zeros (size a)).

  Definition ones (n : N) := List.repeat true (N.to_nat n).

  Fixpoint of_pos_full (value : positive) : bitvector :=
    match value with
    | xH => [true]
    | (p~1)%positive => true :: of_pos_full p
    | (p~0)%positive => false :: of_pos_full p
    end.

  Definition of_N_full (value : N) : bitvector :=
    match value with
    | N0 => [false]
    | Npos p => of_pos_full p
    end.

  Definition of_pos_fixed (width : N) (value : positive) : bitvector :=
    let bv := of_pos_full value in
    if (N.ltb (size bv) width)
    then bv_concat (zeros (width - size bv)) bv
    else bv_extr 0 width (size bv) bv.

  Definition of_N_fixed (width : N) (value : N) : bitvector :=
    let bv := of_N_full value in
    if (N.ltb (size bv) width)
    then bv_concat (zeros (width - size bv)) bv
    else bv_extr 0 width (size bv) bv.

  Definition to_N (val : bitvector) : N := N.of_nat (list2nat_be val).

  Fixpoint to_string (val : bitvector) : string :=
    match val with
    | [] => ""
    | b::bs => to_string bs ++ (if b then "1" else "0")
    end.

  Definition bv_map2_common_map2 (f : bool -> bool -> bool) (bv1 bv2 : bitvector) :
    map2 f bv1 bv2 = (Common.map2 f bv1 bv2).
  Proof.
    generalize dependent bv2.
    induction bv1; destruct bv2; intros; simp map2; try crush.
  Qed.

  Equations nice_nshl_be : list bool -> nat -> list bool :=
    nice_nshl_be bs 0 := bs;
    nice_nshl_be [] _ := [];
    nice_nshl_be bs (S n) := false :: nice_nshl_be (List.removelast bs) n.

  Lemma shl_be_nicify bs n :
    nshl_be bs n = nice_nshl_be bs n.
  Proof.
    funelim (nice_nshl_be bs n); simp nice_nshl_be in *; simpl in *.
    - reflexivity.
    - induction n; crush.
    - rewrite <- H. clear H Heqcall.
      revert b l.
      induction n; intros.
      + crush.
      + simpl.
        now rewrite IHn.
  Qed.

  Equations nice_nshr_be : list bool -> nat -> list bool :=
    nice_nshr_be [] _ := [];
    nice_nshr_be bs 0 := bs;
    nice_nshr_be (b :: bs) (S n) := nice_nshr_be bs n ++ [false].

  Lemma shr_be_nicify bs n :
    nshr_be bs n = nice_nshr_be bs n.
  Proof.
    funelim (nice_nshr_be bs n); simp nice_nshr_be in *; simpl in *.
    - induction n; crush.
    - reflexivity.
    - rewrite <- H. clear b H Heqcall. revert bs.
      induction n; intros; try crush.
      simpl.
      replace (_shr_be (bs ++ [false])) with (_shr_be bs ++ [false])%list
        by (destruct bs; crush).
      eapply IHn.
  Qed.

  (* bitvectors are little-endian, so shifts are inverted *)
  Equations shl (bv : bitvector) (shamt : nat) : t :=
    shl bv 0 := bv;
    shl [] n := [];
    shl bv (S n) := false :: shl (List.removelast bv) n
  .

  Lemma shl_size bv n : size (shl bv n) = size bv.
  Proof.
    unfold size. f_equal.
    funelim (shl bv n);
      try rewrite <- Heqcall in *; clear Heqcall;
      [crush|crush|].
    cbn [length]. f_equal. rewrite H.
    apply removelast_cons_length.
  Qed.

  #[global] Hint Rewrite shl_size : xbv_size.

  Equations shr (bv : bitvector) (shamt : nat) : bitvector :=
    shr bv 0 := bv;
    shr [] n := [];
    shr (b :: bs) (S n) := shr bs n ++ [false]
  .

  Lemma shr_size bv n : size (shr bv n) = size bv.
  Proof.
    unfold size.
    funelim (shr bv n); simp shr; try crush.
    rewrite List.length_app.
    crush.
  Qed.

  #[global] Hint Rewrite shr_size : xbv_size.

  Lemma pow2_pow i : pow2 i = 2 ^ i.
  Proof.
    induction i; simpl.
    { reflexivity. }
    rewrite IHi. lia.
  Qed.

  Lemma _list2nat_be_arith : forall bs n i,
      _list2nat_be bs n i = n + (2 ^ i) * list2nat_be bs.
  Proof.
    unfold list2nat_be.
    induction bs; intros; try crush.
    simpl.
    rewrite ! IHbs with (i := 1).
    rewrite ! IHbs with (i := (i + 1)).
    rewrite ! pow2_pow.
    rewrite ! Nat.add_1_r.
    crush.
  Qed.

  Lemma _list2nat_be_cons : forall bs1 bs2 n i,
      _list2nat_be (bs1 ++ bs2) n i =
        _list2nat_be bs1 0 i + _list2nat_be bs2 n (i + length bs1).
  Proof.
    induction bs1; intros; try crush.
    simpl.
    rewrite ! IHbs1.
    rewrite ! _list2nat_be_arith.
    rewrite ! pow2_pow.
    rewrite ! Nat.pow_add_r.
    simpl. rewrite ! Nat.add_0_r.
    crush.
  Qed.

  Lemma list2nat_be_cons bs1 bs2 :
      list2nat_be (bs1 ++ bs2) =
        list2nat_be bs1 + 2 ^ (length bs1) * list2nat_be bs2.
  Proof.
    unfold list2nat_be.
    rewrite ! _list2nat_be_cons.
    simpl.
    rewrite ! _list2nat_be_arith.
    crush.
  Qed.

  Lemma _list2nat_be_zeros : forall w n i,
      _list2nat_be (BVList.RAWBITVECTOR_LIST.mk_list_false w) n i = n.
  Proof. induction w; crush. Qed.

  Lemma list2nat_be_zeros : forall w,
      list2nat_be (BVList.RAWBITVECTOR_LIST.mk_list_false w) = 0.
  Proof. unfold list2nat_be. intros. apply _list2nat_be_zeros. Qed.

  Lemma list2nat_be_of_N_full v :
    list2nat_be (of_N_full v) = N.to_nat v.
  Proof.
    unfold of_N_full.
    destruct v; try crush.
    remember (of_pos_full p) as bv.
    generalize dependent p.
    induction bv; intros; destruct p; simpl in *; try discriminate.
    - inv Heqbv. insterU IHbv.
      cbn. rewrite ! _list2nat_be_arith.
      rewrite Pos2Nat.inj_xI.
      rewrite IHbv.
      crush.
    - inv Heqbv. insterU IHbv.
      cbn. rewrite ! _list2nat_be_arith.
      rewrite Pos2Nat.inj_xO.
      rewrite IHbv.
      crush.
    - inv Heqbv. crush.
  Qed.

  Lemma _list2nat_be_of_N_full v : forall n i,
    _list2nat_be (of_N_full v) n i = (pow2 i * N.to_nat v) + n.
  Proof.
    unfold of_N_full.
    destruct v; simpl; intros.
    { intros. lia. }
    remember (of_pos_full p) as bv.
    revert n i. generalize dependent p.
    induction bv; intros; destruct p; simpl in *; try discriminate.
    - inv Heqbv.
      rewrite Pos2Nat.inj_xI.
      erewrite IHbv; try reflexivity.
      rewrite ! pow2_pow in *.
      replace (i + 1) with (S i) by lia.
      rewrite Nat.pow_succ_r'.
      lia.
    - inv Heqbv.
      rewrite Pos2Nat.inj_xO.
      erewrite IHbv; try reflexivity.
      rewrite ! pow2_pow in *.
      replace (i + 1) with (S i) by lia.
      rewrite Nat.pow_succ_r'.
      lia.
    - destruct bv; try discriminate. inv Heqbv.
      simpl. lia.
  Qed.

  Lemma to_N_of_N_full n : to_N (of_N_full n) = n.
  Proof.
    unfold to_N, list2nat_be.
    rewrite _list2nat_be_of_N_full.
    simpl. lia.
  Qed.
End RawBV.

Module BV.
  Include BITVECTOR_LIST.

  Definition is_zero {n} (bv : bitvector n) : bool :=
    bv_eq bv (zeros n).

  Definition to_N {n} (bv : bitvector n) : N :=
    RawBV.to_N (bits bv).

  Lemma of_bits_equal n (bv1 bv2 : bitvector n) :
    bits bv1 = bits bv2 ->
    bv1 = bv2.
  Proof.
    intros.
    destruct bv1 as [bits1 wf1], bv2 as [bits2 wf2].
    simpl in *.
    apply bv_eq_reflect.
    unfold bv_eq, RAWBITVECTOR_LIST.bv_eq.
    simpl. clear wf1 wf2. subst bits2.
    rewrite N.eqb_refl.
    apply RAWBITVECTOR_LIST.List_eq_refl.
  Qed.

  (* Local variant of the tactic. The full version needs XBV so it
    can't be defined here *)
  #[local]
  Ltac bitvector_erase :=
    repeat match goal with
           | [ bv : bitvector _ |- _ ] => destruct bv
           | [ H : ?xbv1 = ?xbv2 |- _ ] =>
  	   match type of xbv1 with
  	   | bitvector _ =>
  	     apply (f_equal bits) in H; simpl in H
             end
           | [ |- ?xbv1 = ?xbv2] =>
  	   match type of xbv1 with
  	   | bitvector _ => apply of_bits_equal; simpl
             end
           | [ |- context[rew _ in _] ] => destruct_rew
  	 end;
    unfold to_N in *; simpl in *.

  Program Definition ones (n : N) : bitvector n :=
    {|
      bv := RawBV.ones n;
    |}.
  Next Obligation.
    unfold RawBV.ones, RawBV.size.
    rewrite List.repeat_length.
    apply N2Nat.id.
  Qed.

  Lemma to_N_max_bound n (b : bitvector n) : (to_N b < 2 ^ n)%N.
  Proof.
    intros.
    unfold to_N, RawBV.to_N, RawBV.size.
    destruct b as [b wf]. simpl. subst.
    unfold RawBV.size in *.
    replace (2 ^ N.of_nat (length b))%N with (N.of_nat (2 ^ length b))
      by now rewrite Nat2N.inj_pow.
    enough (RawBV.list2nat_be b < 2 ^ (length b)) by lia.
    induction b; intros; try crush.
    cbn in *. rewrite ! RawBV._list2nat_be_arith in *.
    crush.
  Qed.

  Lemma bv_zextn_to_N n w (bv : bitvector n):
    to_N (bv_concat (zeros w) bv) =
      to_N bv.
  Proof.
    destruct bv.
    unfold to_N, RawBV.to_N, bv_concat, RawBV.bv_concat, zeros, RawBV.zeros.
    f_equal. simpl.
    rewrite RawBV.list2nat_be_cons.
    rewrite RawBV.list2nat_be_zeros.
    lia.
  Qed.

  Program Definition map2 {n : N} (f : bool -> bool -> bool) (bv1 bv2 : bitvector n) : bitvector n :=
    {| bv := RawBV.map2 f (bits bv1) (bits bv2) |}.
  Next Obligation.
    destruct bv1 as [bv1 wf1].
    destruct bv2 as [bv2 wf2].
    unfold RAWBITVECTOR_LIST.size in *.
    rewrite RawBV.bv_map2_common_map2.
    rewrite map2_length.
    simpl. lia.
  Qed.

  Import Program.

  Lemma zextn_as_concat_bits from w (bv : bitvector from) :
    bits (bv_zextn w bv) = bits (bv_concat bv (zeros w)).
  Proof.
    destruct bv as [bv wf]. simpl.
    unfold RAWBITVECTOR_LIST.bv_zextn,
      RAWBITVECTOR_LIST.zextend,
      RAWBITVECTOR_LIST.zeros,
      RAWBITVECTOR_LIST.bv_concat.
    induction (N.to_nat w); crush.
  Qed.

  #[program]
  Definition shl {n} (bv : bitvector n) (shamt : N) : bitvector n :=
    {| bv := RawBV.shl (bits bv) (N.to_nat shamt) |}.
  Next Obligation. rewrite RawBV.shl_size. apply wf. Qed.

  #[program]
  Definition shr {n} (bv : bitvector n) (shamt : N) : bitvector n :=
    {| bv := RawBV.shr (bits bv) (N.to_nat shamt) |}.
  Next Obligation. rewrite RawBV.shr_size. apply wf. Qed.

  Lemma shr_swap_definition w lhs rhs :
    bv_shr (n:=w) lhs rhs = shr lhs (to_N rhs).
  Proof.
   bitvector_erase.
   unfold RawBV.bv_shr, RawBV.to_N in *.
   rewrite wf0, wf1, N.eqb_refl, Nat2N.id in *.
   clear wf0 wf1.
   unfold RawBV.shr_be.
   rewrite RawBV.shr_be_nicify.
   generalize dependent (RawBV.list2nat_be bv0).
   intros shamt. clear w bv0.
   unfold RawBV.size in *.
   funelim (RawBV.shr bv1 shamt).
   - destruct bv0; simp nice_nshr_be; reflexivity.
   - simp nice_nshr_be. crush.
   - simp nice_nshr_be. crush.
  Qed.
  
  Lemma shl_swap_definition w lhs rhs :
    bv_shl (n:=w) lhs rhs = shl lhs (to_N rhs).
  Proof.
   bitvector_erase.
   unfold RawBV.bv_shl, RawBV.to_N in *.
   rewrite wf0, wf1, N.eqb_refl, Nat2N.id in *.
   clear wf0 wf1.
   unfold RawBV.shl_be.
   rewrite RawBV.shl_be_nicify.
   generalize dependent (RawBV.list2nat_be bv0).
   intros shamt. clear w bv0.
   unfold RawBV.size in *.
   funelim (RawBV.shl bv1 shamt).
   - destruct bv0; simp nice_nshl_be; reflexivity.
   - simp nice_nshl_be. crush.
   - simp nice_nshl_be. crush.
  Qed.
  
  Lemma bv_extr_one_bit (n : N) w (bv : bitvector w) :
    (1 + n <= w)%N ->
    bv_extr n 1 bv = of_bits [bitOf (N.to_nat n) bv].
  Proof.
    destruct bv as [bv wf].
    subst. intros.
    apply of_bits_equal.
    simpl.
    unfold bv_extr, RawBV.bv_extr, RawBV.size in *.
    autodestruct_eqn E; try (rewrite N.ltb_lt in *; lia); clear E.
    replace (N.to_nat (1 + n)) with (S (N.to_nat n)) by lia.
    assert (S (N.to_nat n) <= List.length bv) as H' by lia. clear H. revert H'.
    generalize (N.to_nat n). clear n. intros n H.
    revert bv H.
    induction n; intros.
    { destruct bv0; try crush.
      destruct bv0; crush.
    }
    destruct bv0; try crush.
    simpl.
    rewrite IHn; crush.
  Qed.

  Lemma bv_shr_as_select w (vec : bitvector w) (idx : bitvector w) :
    (w > 0)%N ->
    bv_extr 0 1 (bv_shr vec idx) =
      of_bits [bitOf (N.to_nat (to_N idx)) vec]%list.
  Proof.
    intros Hbound.
    rewrite bv_extr_one_bit; try crush.
    apply of_bits_equal. simpl.
    do 2 f_equal.
    unfold bitOf, bv_shr.
    destruct vec as [vec vec_wf].
    destruct idx as [idx idx_wf].
    simpl.
    unfold to_N, RawBV.to_N, bv_shr, RawBV.bv_shr, RawBV.shr_be, RawBV.size in *.
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
End BV.

Module RawXBV.
  Variant bit := X | I | O.

  Definition bit_to_bool b :=
    match b with
    | I => Some true
    | O => Some false
    | X => None
    end
  .

  Definition bool_to_bit (b : bool) :=
    if b then I else O.

  Lemma bit_to_bool_inverse b :
    bit_to_bool (bool_to_bit b) = Some b.
  Proof. destruct b; crush. Qed.

  Lemma bool_to_bit_inverse b1 b2 :
    bit_to_bool b1 = Some b2 ->
    bool_to_bit b2 = b1.
  Proof. intros. destruct b1, b2; crush. Qed.

  Definition xbv := list bit.

  Definition size (xbv : xbv) := N.of_nat (length xbv).

  Definition of_bits (bs : list bit) : xbv := bs.

  Arguments size / _.

  Lemma fold_size bv : N.of_nat (List.length bv) = size bv.
  Proof. reflexivity. Qed.
  
  Lemma removelast_cons_size b bs : size (List.removelast (b :: bs)) = size bs.
  Proof. unfold size. now rewrite removelast_cons_length. Qed.
  
  #[global] Hint Rewrite fold_size removelast_cons_size : xbv_size.

  Definition exes (count : N) : xbv := List.repeat X (nat_of_N count).
  Definition zeros (count : N) : xbv := List.repeat O (nat_of_N count).
  Definition ones (count : N) : xbv := List.repeat I (nat_of_N count).

  Lemma exes_size {n} : size (exes n) = n.
  Proof.
    unfold exes.
    induction n using N.peano_rect; simpl.
    - reflexivity.
    - rewrite Nnat.N2Nat.inj_succ. simpl in *.
      lia.
  Qed.

  #[global] Hint Rewrite @exes_size : xbv_size.

  Lemma ones_size {n} : size (ones n) = n.
  Proof.
    unfold ones.
    induction n using N.peano_rect; simpl.
    - reflexivity.
    - rewrite Nnat.N2Nat.inj_succ. simpl in *.
      lia.
  Qed.

  #[global] Hint Rewrite @ones_size : xbv_size.

  Lemma zeros_size {n} : size (zeros n) = n.
  Proof.
    unfold zeros.
    induction n using N.peano_rect; simpl.
    - reflexivity.
    - rewrite Nnat.N2Nat.inj_succ. simpl in *.
      lia.
  Qed.

  #[global] Hint Rewrite @zeros_size : xbv_size.

  Definition bit_eq_dec (b1 b2: bit) : { b1 = b2 } + { b1 <> b2 }.
  Proof. unfold decidable. decide equality. Qed.

  Definition eq_dec (bv1 bv2: xbv) : { bv1 = bv2 } + { bv1 <> bv2 }.
  Proof. decide equality. apply bit_eq_dec. Qed.

  Definition from_bv (bv : RawBV.t) : xbv :=
    List.map bool_to_bit bv
  .

  Lemma from_bv_size bv :
    size (from_bv bv) = RawBV.size bv.
  Proof.
    unfold size, RawBV.size.
    induction bv; simpl; lia.
  Qed.

  #[global] Hint Rewrite @from_bv_size : xbv_size.

  Definition to_bv (bv : xbv) : option RawBV.t :=
    mapT bit_to_bool bv
  .

  Lemma to_bv_size xbv : forall rbv,
    to_bv xbv = Some rbv ->
    RawBV.size rbv = size xbv.
  Proof.
    unfold size, RawBV.size.
    induction xbv; cbn; firstorder.
    - some_inv; reflexivity.
    - autodestruct_eqn E.
      apply mapT_list_option_length in E0.
      cbn. lia.
  Qed.

  #[global] Hint Rewrite @to_bv_size : xbv_size.

  Definition replicate (n : N) (b : bit) :=
    List.repeat b (N.to_nat n).

  Lemma replicate_size n b :
    size (replicate n b) = n.
  Proof.
    unfold replicate, size.
    rewrite List.repeat_length.
    apply N2Nat.id.
  Qed.

  #[global] Hint Rewrite @replicate_size : xbv_size.

  Definition has_x (bv : xbv) : Prop :=
    List.Exists (fun b => b = X) bv.

  Lemma has_x_to_bv (bv : xbv) : has_x bv <-> to_bv bv = None.
  Proof.
    repeat (unfold has_x, to_bv; simpl).
    induction bv.
    - split; intros; solve_by_invert.
    - split.
      + intros. inv H.
        * reflexivity.
        * simpl. destruct (bit_to_bool a); try reflexivity.
          destruct IHbv as [forward backward].
          rewrite forward by assumption; reflexivity.
      + intros.
        destruct a; simpl in *.
        * repeat constructor.
        * destruct (mapT_list bit_to_bool bv); try discriminate.
          constructor; apply IHbv; trivial.
        * destruct (mapT_list bit_to_bool bv); try discriminate.
          constructor; apply IHbv; trivial.
  Qed.

  Lemma not_has_x_to_bv (bv : xbv) : ~ (has_x bv) <-> exists v, to_bv bv = Some v.
  Proof.
    rewrite has_x_to_bv.
    destruct (to_bv bv) eqn:E; split; intro H.
    - eauto.
    - discriminate.
    - contradiction.
    - solve_by_inverts 2.
  Qed.

  Lemma from_bv_injective : forall bv1 bv2,
    from_bv bv1 = from_bv bv2 ->
    bv1 = bv2.
  Proof.
    unfold from_bv.
    intros bv1 bv2.
    apply map_injective.
    intros x y.
    destruct x; destruct y; intuition discriminate.
  Qed.

  Lemma bit_to_bool_injective : forall x1 x2 y,
      bit_to_bool x1 = Some y ->
      bit_to_bool x2 = Some y ->
      x1 = x2.
  Proof. destruct x1, x2; intros; simpl in *; congruence. Qed.

  Lemma to_bv_injective : forall xbv1 xbv2 bv,
    to_bv xbv1 = Some bv ->
    to_bv xbv2 = Some bv ->
    xbv1 = xbv2.
  Proof.
    unfold to_bv, mapT in *; simpl in *.
    induction xbv1; intros * H1 H2; simpl in *.
    - inv H1.
      destruct xbv2; trivial.
      inv H2.
      autodestruct_eqn E. discriminate.
    - autodestruct_eqn E.
      destruct xbv2; simpl in *; try discriminate.
      autodestruct_eqn E.
      inv H0.
      f_equal.
      + eapply bit_to_bool_injective; eassumption.
      + eapply IHxbv1; eauto.
  Qed.

  Definition x_binop f l r :=
    match to_bv l, to_bv r with
    | Some l_bv, Some r_bv => from_bv (f l_bv r_bv)
    | _, _ =>
        if Nat.eqb (length l) (length r)
        then exes (size l)
        else nil
    end
  .

  Equations to_bv_same_width (l r : xbv) : option (RawBV.t * RawBV.t) :=
    to_bv_same_width l r with dec (size r = size l), to_bv l, to_bv r => {
      | left e, Some l_bv, Some r_bv => Some (l_bv, r_bv)
      | _, _, _ => None
      }.

  Definition concat (l r : xbv) : xbv := r ++ l.

  Lemma concat_size {l r} : size (concat l r) = (size l + size r)%N.
  Proof. unfold concat, size. rewrite List.length_app. lia. Qed.

  #[global] Hint Rewrite @concat_size : xbv_size.

  Lemma concat_empty1 (x1 x2 : xbv) :
    (size x1 = 0)%N ->
    concat x1 x2 = x2.
  Proof.
    intros. unfold concat, size in *.
    destruct x1; [|simpl in H; lia].
    now rewrite List.app_nil_r.
  Qed.

  Lemma concat_empty2 (x1 x2 : xbv) :
    (size x2 = 0)%N ->
    concat x1 x2 = x1.
  Proof.
    intros. unfold concat, size in *.
    destruct x2; [reflexivity|simpl in H; lia].
  Qed.

  Lemma concat_assoc (x1 x2 x3 : xbv) :
    concat x1 (concat x2 x3) = concat (concat x1 x2) x3.
  Proof. unfold concat. now rewrite List.app_assoc. Qed.

  Lemma concat_zeros (w1 w2 : N) :
    concat (zeros w1) (zeros w2) = zeros (w1 + w2).
  Proof.
    unfold zeros, concat.
    rewrite <- List.repeat_app. f_equal. lia.
  Qed.

  Equations extract (x: xbv) (i j: nat) : xbv :=
    extract [] i j := [];
    extract (bx :: x') 0 0 := [];
    extract (bx :: x') 0 (S j') := bx :: extract x' 0 j';
    extract (bx :: x') (S i') j := extract x' i' j.

  Lemma extract_width x i j :
    length (extract x i j) = Nat.min j (length x - i).
  Proof.
    funelim (extract x i j);
      simp extract; simpl in *; try crush.
  Qed.

  #[global] Hint Rewrite @extract_width : xbv_size.

  Lemma extract_size x i j :
    size (extract x (N.to_nat i) (N.to_nat j)) = (N.min j (size x - i))%N.
  Proof.
    unfold size. rewrite extract_width. lia.
  Qed.

  #[global] Hint Rewrite @extract_size : xbv_size.

  Definition extr (v : xbv) (i j : N) : xbv :=
    if (j + i <=? size v)%N
    then extract v (nat_of_N i) (nat_of_N j)
    else exes j.

  Lemma extr_width x i j :
    size (extr x i j) = j.
  Proof.
    unfold extr, size.
    autodestruct_eqn E.
    - rewrite N.leb_le in E.
      rewrite extract_width; try crush.
    - apply exes_size.
  Qed.

  #[global] Hint Rewrite @extr_width : xbv_size.

  Definition bitOf (n : nat) (v: xbv): bit := nth n v X.

  Lemma xbv_bv_inverse : forall bv,
      to_bv (from_bv bv) = Some bv.
  Proof.
    intros bv. induction bv.
    - reflexivity.
    - simpl in *.
      destruct a.
      + unfold to_bv in *. simpl.
        replace (List.mapT_list bit_to_bool (from_bv bv)) with (Some bv).
        reflexivity.
      + unfold to_bv in *. simpl.
        replace (List.mapT_list bit_to_bool (from_bv bv)) with (Some bv).
        reflexivity.
  Qed.

  #[global] Hint Rewrite @xbv_bv_inverse : xbv_size.

  Lemma bv_xbv_inverse : forall x bv,
      to_bv x = Some bv ->
      from_bv bv = x.
  Proof.
    unfold to_bv, from_bv, mapT.
    induction x; simpl in *; intros.
    - now some_inv.
    - autodestruct_eqn E.
      insterU IHx.
      simpl. f_equal.
      + now destruct a, b.
      + assumption.
  Qed.

  (* bitvectors are little-endian, so shifts are inverted *)
  Equations shl (bv : xbv) (shamt : nat) : xbv :=
    shl bv 0 := bv;
    shl [] n := [];
    shl bv (S n) := O :: shl (List.removelast bv) n
  .

  Lemma shl_size n bv :
    size (shl bv n) = size bv.
  Proof.
    unfold size. f_equal.
    funelim (shl bv n); simp shl; try crush.
    cbn [Datatypes.length]. f_equal.
    rewrite H.
    apply removelast_cons_length.
  Qed.

  #[global] Hint Rewrite @shl_size : xbv_size.

  Lemma shl_overshift xbv shamt :
    (N.of_nat shamt >= size xbv)%N ->
    shl xbv shamt = zeros (size xbv).
  Proof.
    intros.
    unfold size, zeros in *.
    N_to_nat.
    funelim (shl xbv shamt).
    - destruct bv; crush.
    - reflexivity.
    - cbn [List.length] in *.
      erewrite H by (rewrite removelast_cons_length; crush).
      rewrite removelast_cons_length.
      crush.
  Qed.

  Equations shr (bv : xbv) (shamt : nat) : xbv :=
    shr bv 0 := bv;
    shr [] n := [];
    shr (b :: bs) (S n) := shr bs n ++ [O]
  .

  Lemma shr_size n bv :
    size (shr bv n) = size bv.
  Proof.
    unfold size.
    funelim (shr bv n); simp shr; try crush.
    rewrite List.length_app.
    crush.
  Qed.

  #[global] Hint Rewrite @shr_size : xbv_size.

  Lemma shr_overshift xbv shamt :
    (N.of_nat shamt >= size xbv)%N ->
    shr xbv shamt = zeros (size xbv).
  Proof.
    intros.
    unfold size, zeros in *.
    N_to_nat.
    funelim (shr xbv shamt).
    - destruct bv; crush.
    - reflexivity.
    - cbn [List.length] in *.
      rewrite H by lia. clear H H0 Heqcall.
      induction (List.length bs); crush.
  Qed.

  (*
   * Matches this Verilog operation:
   * bv1 === bv2
   *)
  Definition triple_equal (bv1 bv2 : xbv) := bv1 = bv2.

  (*
   * Matches this Verilog operation:
   * (bv1 == bv2) === 1
   *)
  Definition definite_equal (bv1 bv2 : xbv) :=
    exists v, to_bv bv1 = Some v /\ to_bv bv2 = Some v.

  Global Instance dec_eq_bit (b1 b2 : bit) : DecProp (b1 = b2) :=
    mk_dec_eq.

  Global Instance dec_eq_xbv (xbv1 xbv2 : xbv) : DecProp (xbv1 = xbv2) :=
    mk_dec_eq.

  Global Instance dec_has_x xbv : DecProp (has_x xbv) := _.

  Lemma extract_full w (xbv : xbv) :
    w = N.to_nat (size xbv) ->
    extract xbv 0 w = xbv.
  Proof.
    intros.
    subst. unfold size. rewrite Nat2N.id.
    funelim (extract xbv 0 (List.length xbv)); crush.
  Qed.
  
  Lemma extract_empty lo sz (xbv : xbv) :
    sz = 0 ->
    extract xbv lo sz = [].
  Proof.
    intros. subst.
    funelim (extract xbv lo 0); crush.
  Qed.
  
  Lemma extr_empty lo sz (xbv : xbv) :
    (sz = 0)%N ->
    extr xbv lo sz = [].
  Proof.
    intros. subst. unfold extr.
    rewrite extract_empty by lia.
    unfold exes; simpl. crush.
  Qed.

  Lemma shr_as_concat_gt (n : nat) (xbv : xbv) :
    (List.length xbv < n) ->
    shr xbv n = zeros (size xbv).
  Proof.
    funelim (shr xbv n); intros; unfold zeros; simpl in *.
    - destruct bv; crush.
    - reflexivity.
    - insterU H.
      unfold zeros in *.
      rewrite Pnat.SuccNat2Pos.id_succ.
      rewrite Nat2N.id in *.
      simpl. rewrite H.
      clear Heqcall H0 H.
      induction (List.length bs); crush.
  Qed.
  
  Lemma shr_as_concat_le (n : nat) (xbv : xbv) :
    (n <= List.length xbv) ->
    shr xbv n =
      concat
        (zeros (N.of_nat n))
        (extr xbv (N.of_nat n) (size xbv - N.of_nat n)).
  Proof.
    unfold zeros, concat, extr, size.
    simpl. rewrite Nat2N.id.
    intros.
    autodestruct_eqn E; kill_bools; try lia.
    funelim (shr xbv n); [idtac|crush|idtac].
    + simpl in *.
      rewrite extract_full. 
      * now rewrite List.app_nil_r. 
      * unfold size. lia.
    + insterU H. simp extract.
      rewrite H. clear H.
      rewrite ! N2Nat.inj_sub, ! Nat2N.id.
      simpl.
      rewrite <- List.app_assoc. f_equal.
      clear E H0 Heqcall. induction n; crush.
  Qed.
  
  Lemma shr_as_concat (n : nat) (xbv : xbv) :
    shr xbv n =
      concat
        (zeros (N.of_nat (min (List.length xbv) n)))
        (extr xbv (N.of_nat n) (size xbv - N.of_nat n)).
  Proof.
    destruct (Nat.leb n (List.length xbv)) eqn:E; kill_bools.
    - rewrite Nat.min_r by lia.
      apply shr_as_concat_le. lia.
    - rewrite Nat.min_l by lia.
      rewrite shr_as_concat_gt by lia.
      unfold extr.
      autodestruct_eqn Hcmp; kill_bools; [crush|clear Hcmp].
      rewrite concat_empty2. reflexivity.
      rewrite exes_size. unfold size. lia.
  Qed.
  
  Lemma shl_as_concat_gt (n : nat) (xbv : xbv) :
    (List.length xbv < n) ->
    shl xbv n = zeros (size xbv).
  Proof.
    funelim (shl xbv n); intros.
    - destruct bv; crush.
    - reflexivity.
    - insterU H.
      autorewrite with xbv_size in *.
      unfold size, zeros in *.
      cbn [List.length] in *. 
      erewrite H by lia.
      rewrite ! Nat2N.id. reflexivity.
  Qed.
  
  Lemma extract_remove_last n l:
    n < List.length l ->
    extract (List.removelast l) 0 n = extract l 0 n.
  Proof.
    revert n.
    induction l; intros.
    - destruct n; [|crush]. reflexivity.
    - simpl in H.
      destruct n; [rewrite ! extract_empty; crush|].
      simp extract. destruct l; [crush|].
      simpl. simp extract.
      f_equal. apply IHl. lia.
  Qed.
  
  Lemma shl_as_concat_le (n : nat) (xbv : xbv) :
    (n <= List.length xbv) ->
    shl xbv n =
      concat
        (extr xbv 0 (size xbv - N.of_nat n))
        (zeros (N.of_nat n)).
  Proof.
    unfold zeros, concat, extr, size.
    simpl. rewrite Nat2N.id.
    intros.
    autodestruct_eqn E; kill_bools; N_to_nat; try lia.
    funelim (shl xbv n); [idtac|crush|idtac].
    + simpl in *.
      rewrite extract_full. 
      * reflexivity.
      * unfold size. lia.
    + insterU H. simp extract.
      rewrite H by (autorewrite with xbv_size in *; crush).
      clear H. cbn [List.repeat List.app]. do 2 f_equal.
      autorewrite with xbv_size.
      apply extract_remove_last.
      lia.
  Qed.
  
  Lemma shl_as_concat (n : nat) (xbv : xbv) :
    shl xbv n =
      concat
        (extr xbv 0 (size xbv - N.of_nat n))
        (zeros (N.of_nat (min (List.length xbv) n)))
        .
  Proof.
    destruct (Nat.leb n (List.length xbv)) eqn:E; kill_bools.
    - rewrite Nat.min_r by lia.
      apply shl_as_concat_le. lia.
    - rewrite Nat.min_l by lia.
      rewrite shl_as_concat_gt by lia.
      unfold extr.
      autodestruct_eqn Hcmp; kill_bools; [|crush].
      rewrite concat_empty1. reflexivity.
      autorewrite with xbv_size. unfold size in *. lia.
  Qed.
  
  Lemma extr_of_concat_lo xbv_hi xbv_lo lo sz :
    (lo <= size xbv_lo)%N ->
    (lo + sz <= size xbv_lo)%N ->
    extr (concat xbv_hi xbv_lo) lo sz = extr xbv_lo lo sz.
  Proof.
    intros Hlo Hhi.
    unfold extr.
    autodestruct_eqn E; kill_bools;
      autorewrite with xbv_size in *;
      try lia; [idtac].
    clear E E0.
    N_to_nat. unfold concat.
    funelim (extract xbv_lo lo sz).
    - simpl in *.
      replace i with 0 by lia.
      replace j with 0 by lia. 
      destruct xbv_hi; simp extract; reflexivity.
    - simpl in *. simp extract. reflexivity.
    - simpl in *. simp extract.
      erewrite H; try crush.
    - simpl in *. simp extract. eapply H; lia.
  Qed.
  
  Lemma extr_of_concat_hi xbv_hi xbv_lo lo sz :
    (size xbv_lo <= lo)%N ->
    (lo + sz <= size xbv_lo + size xbv_hi)%N ->
    extr (concat xbv_hi xbv_lo) lo sz =
      extr xbv_hi (lo - size xbv_lo) sz.
  Proof.
    intros Hlo Hhi.
    unfold extr.
    autodestruct_eqn E; kill_bools;
      autorewrite with xbv_size in *;
      try lia; [idtac].
    clear E E0.
    unfold size, concat in *.
    N_to_nat.
    funelim (extract (xbv_lo ++ xbv_hi) lo sz); intros.
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
  
  Lemma extr_of_concat_mid xbv_hi xbv_lo lo sz :
    (lo <= size xbv_lo)%N ->
    (size xbv_lo <= lo + sz)%N ->
    (lo + sz <= size xbv_lo + size xbv_hi)%N ->
    extr (concat xbv_hi xbv_lo) lo sz =
      concat
        (extr xbv_hi (lo - size xbv_lo)%N (sz - (size xbv_lo - lo))%N)
        (extr xbv_lo lo (size xbv_lo - lo)%N).
  Proof.
    intros Hlo Hmid Hhi.
    unfold extr.
    autodestruct_eqn E; kill_bools;
      autorewrite with xbv_size in *;
      try lia; [idtac].
    clear E E0 E1.
    unfold size, concat in *.
    N_to_nat.
    funelim (extract (xbv_lo ++ xbv_hi) lo sz); intros.
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
  
  Lemma extr_of_concat xbv_hi xbv_lo lo sz :
    (lo + sz <= size xbv_hi + size xbv_lo)%N ->
    extr (concat xbv_hi xbv_lo) lo sz =
      concat
        (extr xbv_hi (lo - size xbv_lo) (sz - (size xbv_lo - lo)))%N
        (extr xbv_lo lo (N.min sz (size xbv_lo - lo)))%N.
  Proof.
    intros.
    destruct (dec (size xbv_lo <= lo)%N);
      destruct (dec (lo + sz < size xbv_lo))%N; try lia.
    - replace (N.min sz (size xbv_lo - lo)) with (size xbv_lo - lo)%N by lia.
      replace (size xbv_lo - lo)%N with 0%N by lia.
      erewrite extr_of_concat_hi by lia.
      rewrite concat_empty2 by (autorewrite with xbv_size; lia).
      f_equal. lia.
    - replace (N.min sz (size xbv_lo - lo)) with sz by lia.
      replace (sz - (size xbv_lo - lo))%N with 0%N by lia.
      erewrite extr_of_concat_lo by lia.
      rewrite concat_empty1 by (autorewrite with xbv_size; lia).
      reflexivity.
    - replace (N.min sz (size xbv_lo - lo)) with (size xbv_lo - lo)%N by lia.
      eapply extr_of_concat_mid; lia.
  Qed.
  
  Lemma extr_of_zeros w lo sz :
    (lo + sz <= w)%N ->
    extr (zeros w) lo sz = zeros sz.
  Proof.
    intros. unfold extr.
    autorewrite with xbv_size.
    autodestruct_eqn E; kill_bools; [clear E|crush].
    unfold zeros.
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
  
  Lemma extr_of_extr lo1 lo2 sz1 sz2 xbv :
    (lo1 + sz1 <= size xbv)%N ->
    (lo2 + sz2 <= sz1)%N ->
    extr (extr xbv lo1 sz1) lo2 sz2 = extr xbv (lo1 + lo2) sz2.
  Proof.
    intros H0 H1.
    unfold extr.
    autodestruct_eqn E;
      autorewrite with xbv_size kill_bools in *;
      try crush; N_to_nat.
    clear E E0 E1.
    revert sz1 H0 H1.
    funelim (extract xbv (lo1 + lo2) sz2).
    - intros. simp extract. reflexivity.
    - intros.
      replace lo2 with 0 in * by lia.
      destruct (extract (bx :: x') lo1 sz1); simp extract; reflexivity.
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

  Lemma from_bv_app b1 b2 :
    from_bv (b1 ++ b2)%list = (from_bv b1 ++ from_bv b2)%list.
  Proof. unfold from_bv. apply List.map_app. Qed.
End RawXBV.

Module XBV.
  Export RawXBV (bit(..)).

  Record xbv (n : N) :=
    MkBitvector {
        bv : RawXBV.xbv;
        wf : RawXBV.size bv = n
      }.

  Arguments bv {_} _.

  Definition bits {n} (v : xbv n) :=
    bv v.

  Definition size {n} (xbv : xbv n) := n.

  Program Definition of_bits (bs : list RawXBV.bit) : xbv (N.of_nat (length bs)) :=
    {| bv := bs |}.

  Definition bitOf {n} (i : nat) (x: xbv n): RawXBV.bit :=
    RawXBV.bitOf i (bits x).

  Import CommonNotations.
  Import EqNotations.

  Program Definition from_bv {n} (bv : BV.bitvector n) : xbv n :=
    {| bv := RawXBV.from_bv (BV.bits bv); wf := RawXBV.from_bv_size _ |}
  .
  Next Obligation. apply BV.wf. Qed.

  Definition raw_to_bv_with_proof (v : RawXBV.xbv) : {bv : RawBV.bitvector & RawXBV.to_bv v = Some bv } + { RawXBV.to_bv v = None } :=
    match RawXBV.to_bv v as x return _ = x -> _ with
    | Some bv => fun e => inleft (bv; e)
    | None => fun e => inright e
    end eq_refl.

  Equations to_bv {n} : xbv n -> option (BV.bitvector n) :=
    to_bv v with (raw_to_bv_with_proof (bits v)) => {
      | inright prf => None
      | inleft (bv; e) => Some (rew _ in BV.of_bits bv)
      }.
  Next Obligation.
    fold (RawBV.size bv0).
    apply RawXBV.to_bv_size in e.
    erewrite e.
    apply wf.
  Defined. (* Qed blocks this from evaluating *)

  Lemma of_bits_equal n (x1 x2 : xbv n) :
    bits x1 = bits x2 ->
    x1 = x2.
  Proof.
    destruct x1, x2.
    simpl. intros.
    generalize dependent wf0.
    generalize dependent wf1.
    rewrite H. clear H.
    intros. f_equal.
    apply proof_irrelevance.
  Qed.

  Lemma xbv_bv_inverse n (bv : BV.bitvector n) :
      to_bv (from_bv bv) = Some bv.
  Proof.
    funelim (to_bv (from_bv bv)); try rewrite <- Heqcall in *; clear Heqcall; clear Heq.
    - f_equal.
      destruct (to_bv_obligations_obligation_1 n (from_bv bv1) bv0).
      simpl in *.
      apply RawXBV.bv_xbv_inverse in e.
      apply RawXBV.from_bv_injective in e.
      destruct bv1 as [bv1 wf1]. simpl in *.
      subst bv0.
      now apply BV.of_bits_equal.
    - simpl in *.
      now rewrite RawXBV.xbv_bv_inverse in prf.
  Qed.

  Lemma to_bv_bits n x (bv : BV.bitvector n) :
    to_bv x = Some bv ->
    RawXBV.to_bv (bits x) = Some (BV.bits bv).
  Proof.
    intros.
    funelim (to_bv x); rewrite <- Heqcall in *; clear Heqcall; intros; try congruence.
    rewrite e.
    f_equal.
    inv H.
    destruct (to_bv_obligations_obligation_1).
    rewrite <- eq_rect_eq.
    reflexivity.
  Qed.

  Lemma bv_xbv_inverse : forall n (x : xbv n) (bv : BV.bitvector n),
      to_bv x = Some bv ->
      from_bv bv = x.
  Proof.
    intros.
    apply of_bits_equal.
    apply RawXBV.bv_xbv_inverse.
    apply to_bv_bits.
    assumption.
  Qed.

  Lemma to_from_bv_inverse n (x : xbv n) (bv : BV.bitvector n) :
    to_bv x = Some bv ->
    x = from_bv bv.
  Proof.
    intros.
    apply to_bv_bits in H.
    unfold from_bv.
    destruct x as [x_bits x_wf].
    simpl in H.
    apply RawXBV.bv_xbv_inverse in H.
    apply of_bits_equal. simpl.
    auto.
  Qed.

  Definition has_x {n} (v : xbv n) : Prop :=
    RawXBV.has_x (bits v).

  Lemma has_x_to_bv {n} (x : xbv n) : has_x x <-> to_bv x = None.
  Proof.
    unfold has_x. rewrite RawXBV.has_x_to_bv.
    funelim (to_bv x); crush.
  Qed.

  Lemma not_has_x_to_bv {n} (bv : xbv n) : ~ (has_x bv) <-> exists v, to_bv bv = Some v.
  Proof.
    rewrite has_x_to_bv.
    destruct (to_bv bv) eqn:E; split; intro H.
    - eauto.
    - discriminate.
    - contradiction.
    - solve_by_inverts 2.
  Qed.

  Lemma from_bv_injective : forall n (bv1 bv2 : BV.bitvector n),
    from_bv bv1 = from_bv bv2 ->
    bv1 = bv2.
  Proof.
    unfold from_bv.
    intros n bv1 bv2 H.
    inv H.
    apply RawXBV.from_bv_injective in H1.
    apply BV.bv_eq_reflect.
    destruct bv1, bv2; simpl in *.
    unfold BV.bv_eq, RAWBITVECTOR_LIST.bv_eq.
    simpl. clear wf0 wf1. subst.
    rewrite N.eqb_refl.
    apply RAWBITVECTOR_LIST.List_eq_refl.
  Qed.

  Lemma to_bv_injective : forall n (xbv1 xbv2 : xbv n) (bv : BV.bitvector n),
    to_bv xbv1 = Some bv ->
    to_bv xbv2 = Some bv ->
    xbv1 = xbv2.
  Proof.
    intros * H1 H2.
    apply to_bv_bits in H1.
    apply to_bv_bits in H2.
    apply of_bits_equal.
    eapply RawXBV.to_bv_injective; eassumption.
  Qed.

  Definition to_N {n} (x : xbv n) : option N :=
    option_map BV.to_N (to_bv x).

  Lemma to_N_from_bv n (b : BV.bitvector n) : to_N (from_bv b) = Some (BV.to_N b).
  Proof. unfold to_N. now rewrite xbv_bv_inverse. Qed.

  Lemma to_N_max_bound n (b : xbv n) v :
    to_N b = Some v ->
    (v < 2 ^ n)%N.
  Proof.
    unfold to_N.
    intros.
    destruct (to_bv b); try discriminate. inv H.
    apply BV.to_N_max_bound.
  Qed.

  #[global]
  Ltac bitvector_erase :=
    repeat match goal with
           | [ xbv : xbv _ |- _ ] => destruct xbv
           | [ bv : BV.bitvector _ |- _ ] => destruct bv
           | [ H : RawXBV.size ?xbv = 0%N |- _ ] =>
  	   destruct xbv; [|discriminate]; clear H; simpl in *
           | [ H : to_bv _ = None |- _ ] => rewrite <- has_x_to_bv in H
           | [ H : ?xbv1 = ?xbv2 |- _ ] =>
  	   match type of xbv1 with
  	   | xbv _ =>
  	     apply (f_equal bits) in H; simpl in H
  	   | BV.bitvector _ =>
  	     apply (f_equal BV.bits) in H; simpl in H
             end
           | [ |- ?xbv1 = ?xbv2] =>
  	   match type of xbv1 with
  	   | xbv _ => apply of_bits_equal; simpl
  	   | BV.bitvector _ => apply BV.of_bits_equal; simpl
             end
           | [ |- context[rew _ in _] ] => destruct_rew
  	 end;
    unfold has_x, BV.to_N in *; simpl in *.

  Definition extr {n} (x: xbv n) (i j: N) : xbv j :=
    {|
      bv := RawXBV.extr (bits x) i j;
      wf := RawXBV.extr_width _ _ _
    |}.

  Lemma extr_no_exes (n i j : N) (bv : BV.bitvector n) :
    (i + j <= n)%N ->
    extr (from_bv bv) i j = from_bv (BV.bv_extr i j bv).
  Proof.
    intros. destruct bv as [bv wf].
    apply of_bits_equal; simpl.
    unfold RawXBV.extr.
    rewrite RawXBV.from_bv_size. rewrite wf. rewrite <- N.leb_le in H. rewrite N.add_comm in H. rewrite H.
    unfold RAWBITVECTOR_LIST.bv_extr.
    rewrite N.leb_le in H.
    replace (n <? j + i)%N with false; cycle 1. {
      symmetry. apply N.ltb_ge. lia.
    }

    (* Rewrite everything in terms of Nats instead of N *)
    remember (N.to_nat i) as i_nat.
    remember (N.to_nat j) as j_nat.
    replace (N.to_nat (j + i)) with (j_nat + i_nat) by lia.
    unfold RAWBITVECTOR_LIST.size in *.
    assert (j_nat + i_nat <= length bv) by lia.
    clear H Heqi_nat Heqj_nat wf n i j.

    generalize dependent i_nat. generalize dependent j_nat.
    induction bv; simpl in *; intros.
    - simp extract. reflexivity.
    - autodestruct_eqn E;
        try rewrite Nat.add_0_r in *; subst;
        simp extract; simpl;
        repeat f_equal;
        try crush.
      + rewrite IHbv; try crush. now rewrite Nat.add_comm.
      + rewrite IHbv; repeat f_equal; lia.
  Qed.

  Local Obligation Tactic := intros.

  Program Definition concat {n m : N} (l : xbv n) (r : xbv m) : xbv (n + m) :=
    {| bv := RawXBV.concat (bits l) (bits r) |}.
  Next Obligation. now rewrite RawXBV.concat_size, ! wf. Qed.

  Lemma concat_to_bv n1 n2 (bv1 : BV.bitvector n1) (bv2 : BV.bitvector n2) :
    to_bv (concat (from_bv bv1) (from_bv bv2)) = Some (BV.bv_concat bv1 bv2).
  Proof.
    destruct bv1, bv2.
    rewrite <- xbv_bv_inverse. f_equal.
    apply of_bits_equal; simpl.
    unfold RAWBITVECTOR_LIST.bv_concat, RawXBV.from_bv.
    now rewrite map_app.
  Qed.

  Lemma concat_no_exes n1 n2 (bv1 : BV.bitvector n1) (bv2 : BV.bitvector n2) :
    concat (from_bv bv1) (from_bv bv2) = from_bv (BV.bv_concat bv1 bv2).
  Proof.
    destruct bv1 as [bv1 wf1], bv2 as [bv2 wf2].
    apply of_bits_equal. simpl.
    unfold RawBV.bv_concat, RawXBV.from_bv.
    rewrite List.map_app.
    reflexivity.
  Qed.

  Lemma concat_empty1 {w} (x1 : xbv 0) (x2 : xbv w) :
    rew [xbv] (N.add_0_l w) in concat x1 x2 = x2.
  Proof.
    bitvector_erase. unfold RawXBV.concat. now rewrite List.app_nil_r.
  Qed.

  Program Definition replicate (n : N) (b : bit) : xbv n :=
    {| bv := List.repeat b (N.to_nat n) |}.
  Next Obligation. unfold RawXBV.size. rewrite repeat_length. apply N2Nat.id. Qed.

  Definition exes (count : N) : xbv count :=
    {| bv := RawXBV.exes count; wf := RawXBV.exes_size |}.

  Definition ones (count : N) : xbv count :=
    {| bv := RawXBV.ones count; wf := RawXBV.ones_size |}.

  Definition zeros (count : N) : xbv count :=
    {| bv := RawXBV.zeros count; wf := RawXBV.zeros_size |}.

  Lemma exes_to_bv n :
    (n > 0)%N ->
    to_bv (exes n) = None.
  Proof.
    intros.
    unfold exes, RawXBV.exes, replicate.
    apply has_x_to_bv. unfold has_x. simpl.
    unfold RawXBV.has_x.
    induction (N.to_nat n) eqn:E; crush.
  Qed.

  Lemma ones_to_bv n :
    to_bv (ones n) = Some (BV.ones n).
  Proof.
    unfold ones, RawXBV.ones, BV.ones, replicate, RawBV.ones.
    rewrite <- xbv_bv_inverse. f_equal.
    apply of_bits_equal; simpl.
    induction (N.to_nat n); crush.
  Qed.

  Lemma ones_from_bv n :
    ones n = from_bv (BV.ones n).
  Proof.
    eapply to_bv_injective.
    - apply ones_to_bv.
    - eapply xbv_bv_inverse.
  Qed.

  Lemma zeros_to_bv n :
    to_bv (zeros n) = Some (BV.zeros n).
  Proof.
    unfold zeros, RawXBV.zeros, BV.zeros, replicate, RawBV.zeros.
    rewrite <- xbv_bv_inverse. f_equal.
    apply of_bits_equal; simpl.
    induction (N.to_nat n); crush.
  Qed.

  Lemma zeros_from_bv n :
    zeros n = from_bv (BV.zeros n).
  Proof.
    eapply to_bv_injective.
    - apply zeros_to_bv.
    - eapply xbv_bv_inverse.
  Qed.


  #[program]
  Definition shl {n} (bv : xbv n) (shamt : N) : xbv n :=
    {| bv := RawXBV.shl (bits bv) (N.to_nat shamt) |}.
  Next Obligation. rewrite RawXBV.shl_size. apply wf. Qed.

  Lemma shl_overshift {n} (x : xbv n) shamt :
    (shamt >= n)%N ->
    shl x shamt = zeros n.
  Proof.
    intros.
    bitvector_erase. subst.
    erewrite RawXBV.shl_overshift; unfold RawXBV.size in *; crush.
  Qed.

  #[program]
  Definition shr {n} (bv : xbv n) (shamt : N) : xbv n :=
    {| bv := RawXBV.shr (bits bv) (N.to_nat shamt) |}.
  Next Obligation. rewrite RawXBV.shr_size. apply wf. Qed.

  Lemma shr_overshift {n} (x : xbv n) shamt :
    (shamt >= n)%N ->
    shr x shamt = zeros n.
  Proof.
    intros.
    bitvector_erase. subst.
    erewrite RawXBV.shr_overshift; unfold RawXBV.size in *; crush.
  Qed.

  (*
   * Matches this Verilog operation:

   * bv1 === bv2
   *)
  Definition triple_equal {n} (bv1 bv2 : xbv n) := bv1 = bv2.

  (*
   * Matches this Verilog operation:
   * (bv1 == bv2) === 1
   *)
  Definition definite_equal {n} (bv1 bv2 : xbv n ) :=
    exists v, to_bv bv1 = Some v /\ to_bv bv2 = Some v.

  #[global]
  Instance dec_eq_xbv {n} (xbv1 xbv2 : xbv n) : DecProp (xbv1 = xbv2).
  Proof.
    destruct (dec (bits xbv1 = bits xbv2)).
    - left. now apply of_bits_equal.
    - right. crush.
  Qed.

  #[global]
  Instance dec_has_x {n} (x : xbv n) : DecProp (has_x x) := _.

  Lemma shl_to_bv n vec shamt :
    to_bv (shl (from_bv vec) shamt) = Some (BV.shl (n:=n) vec shamt).
  Proof.
    unfold BV.to_N, BV.shl.
    intros.
    destruct vec as [vec vec_wf].
    rewrite <- xbv_bv_inverse. f_equal.
    apply of_bits_equal; simpl.
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
    to_bv (shr (from_bv vec) shamt) = Some (BV.shr (n:=n) vec shamt).
  Proof.
    unfold BV.to_N, BV.shr.
    intros.
    destruct vec as [vec vec_wf].
    rewrite <- xbv_bv_inverse. f_equal.
    apply of_bits_equal; simpl.
    generalize dependent (N.to_nat shamt). clear shamt. intro shamt.
    funelim (RawBV.shr vec shamt); simpl; simp shr.
    - reflexivity.
    - reflexivity.
    - unfold RawXBV.from_bv in *.
      rewrite List.map_app. simpl. repeat f_equal.
      eauto.
  Qed.

  Lemma bitOf_in_bounds n w (bv : BV.bitvector w) def :
    (n < w)%N ->
    RawXBV.bit_to_bool (bitOf (N.to_nat n) (from_bv bv)) = Some (List.nth (N.to_nat n) (BV.bits bv) def).
  Proof.
    intros H.
    destruct bv as [bv wf].
    unfold from_bv, RawXBV.from_bv, bitOf, RawXBV.bitOf,
      BVList.RAWBITVECTOR_LIST.size in *.
    subst. simpl.
    erewrite List.nth_indep
      by (rewrite List.length_map; lia).
    rewrite List.map_nth.
    rewrite RawXBV.bit_to_bool_inverse.
    reflexivity.
  Qed.

  Lemma to_bv_some_raw_iff w (xbv : xbv w) (bv : BV.bitvector w) :
    to_bv xbv = Some bv <-> RawXBV.to_bv (bits xbv) = Some (BV.bits bv).
  Proof.
    (* This is disgusting (written while half asleep) plzfix *)
    split; intros; simpl in *.
    - apply bv_xbv_inverse in H. subst.
      destruct bv as [bv bv_wf].
      simpl. apply RawXBV.xbv_bv_inverse.
    - apply RawXBV.bv_xbv_inverse in H.
      destruct bv as [bv bv_wf].
      simpl in *.
      funelim (to_bv xbv).
      + unfold raw_to_bv_with_proof in *.
        rewrite e in Heq. inv Heq.
        f_equal.
        apply BV.of_bits_equal.
        simpl. destruct_rew.
        destruct v as [v v_wf].
        unfold bits, bv, RawBV.of_bits in *. simpl in *. subst.
        rewrite RawXBV.xbv_bv_inverse in e.
        inv e.
        reflexivity.
      + destruct v as [v v_wf].
        simpl in *. subst.
        clear Heq.
        rewrite RawXBV.xbv_bv_inverse in prf.
        discriminate.
  Qed.

  Lemma concat_from_bv_inv1 n1 n2 (xbv1 : xbv n1) (xbv2 : xbv n2) bv :
    concat xbv1 xbv2 = from_bv bv ->
    (exists bv1, xbv1 = from_bv bv1).
  Proof.
    destruct (to_bv xbv1) as [bv1|] eqn:Hbv1; [apply bv_xbv_inverse in Hbv1; crush|].
    intros. exfalso.
  
    bitvector_erase. subst.
    apply (f_equal RawXBV.to_bv) in H.
    rewrite RawXBV.xbv_bv_inverse in H.
    rewrite RawXBV.has_x_to_bv in Hbv1.
  
    clear wf2. revert bv1 bv2 H Hbv1.
    induction bv0; intros; [crush|].
    unfold RawXBV.to_bv in *. simpl in *.
    autodestruct_eqn E.
    eauto.
  Qed.
  
  Lemma concat_from_bv_inv2 n1 n2 (xbv1 : xbv n1) (xbv2 : xbv n2) bv :
    concat xbv1 xbv2 = from_bv bv ->
    (exists bv2, xbv2 = from_bv bv2).
  Proof.
    destruct (to_bv xbv2) as [bv2|] eqn:Hbv2; [apply bv_xbv_inverse in Hbv2; crush|].
    intros. exfalso.
  
    bitvector_erase. subst.
    apply (f_equal RawXBV.to_bv) in H.
    rewrite RawXBV.xbv_bv_inverse in H.
    rewrite RawXBV.has_x_to_bv in Hbv2.
  
    clear wf2. revert bv1 bv2 H Hbv2.
    induction bv0; intros; [crush|].
    unfold RawXBV.to_bv in *. simpl in *.
    autodestruct_eqn E.
    eauto.
  Qed.
  
  Lemma concat_to_bv_none1 n1 n2 (xbv1 : xbv n1) (xbv2 : xbv n2) :
    to_bv xbv1 = None ->
    to_bv (concat xbv1 xbv2) = None.
  Proof.
    intros.
    destruct (to_bv (concat xbv1 xbv2)) eqn:E; [exfalso|reflexivity].
    apply bv_xbv_inverse in E. symmetry in E.
    apply concat_from_bv_inv1 in E. destruct E. subst.
    rewrite xbv_bv_inverse in H. discriminate.
  Qed.
  
  Lemma concat_to_bv_none2 n1 n2 (xbv1 : xbv n1) (xbv2 : xbv n2) :
    to_bv xbv2 = None ->
    to_bv (concat xbv1 xbv2) = None.
  Proof.
    intros.
    destruct (to_bv (concat xbv1 xbv2)) eqn:E; [exfalso|reflexivity].
    apply bv_xbv_inverse in E. symmetry in E.
    apply concat_from_bv_inv2 in E. destruct E. subst.
    rewrite xbv_bv_inverse in H. discriminate.
  Qed.
  
  Lemma extend_to_N w1 w2 (xbv : xbv w1) val :
    to_N xbv = Some val ->
    to_N (concat (zeros w2) xbv) = Some val.
  Proof.
    unfold to_N. intros.
    destruct (to_bv xbv) as [bv|] eqn:Hbv; [|discriminate].
    apply bv_xbv_inverse in Hbv. inv H.
    rewrite zeros_from_bv. rewrite concat_no_exes.
    rewrite xbv_bv_inverse. simpl. f_equal.
    apply BV.bv_zextn_to_N.
  Qed.
  
  Lemma extend_to_N_none2 w1 w2 (xbv1 : xbv w1) (xbv2 : xbv w2) :
    to_N xbv2 = None ->
    to_N (concat xbv1 xbv2) = None.
  Proof.
    unfold to_N. intros.
    destruct (to_bv xbv2) eqn:E; simpl in *; [discriminate|].
    rewrite concat_to_bv_none2; crush.
  Qed.
  
  Lemma extr_shr_extend_overshift w1 w2 (xbv : xbv w1) shamt  :
    (shamt > w1)%N ->
    extr (shr (concat (zeros w2) xbv) shamt) 0 w1 =
    shr xbv shamt.
  Proof.
    intros. bitvector_erase.
    destruct (dec (shamt >= w2 + w1))%N.
    - subst.
      rewrite ! RawXBV.shr_overshift by (autorewrite with xbv_size in *; crush).
      autorewrite with xbv_size.
      eapply RawXBV.extr_of_zeros. lia.
    - subst.
      rewrite ! RawXBV.shr_overshift with (xbv:=bv0) by (autorewrite with xbv_size; crush).
      rewrite ! RawXBV.shr_as_concat.
      rewrite ! N2Nat.id.
      fold (RawXBV.size bv0) in *.
      autorewrite with xbv_size.
      rewrite RawXBV.extr_of_concat with (xbv_lo := bv0) by (autorewrite with xbv_size; lia).
      destruct_mins.
      erewrite RawXBV.extr_of_zeros by lia.
      erewrite RawXBV.concat_assoc.
      erewrite RawXBV.concat_zeros.
      erewrite RawXBV.extr_empty with (xbv := bv0) by lia.
      erewrite RawXBV.concat_empty2 by reflexivity.
      erewrite RawXBV.extr_of_zeros; crush.
  Qed.
  
  Lemma extr_shr_extend_no_overshift w1 w2 (xbv : xbv w1) shamt  :
    (shamt <= w1)%N ->
    extr (shr (concat (zeros w2) xbv) shamt) 0 w1 =
    shr xbv shamt.
  Proof.
    intros.
    bitvector_erase. subst.
    rewrite ! RawXBV.shr_as_concat.
    rewrite ! N2Nat.id.
    fold (RawXBV.size bv0) in *.
    autorewrite with xbv_size.
    rewrite ! RawXBV.extr_of_concat by (autorewrite with xbv_size; lia).
    rewrite RawXBV.extr_of_zeros by (autorewrite with xbv_size; lia).
    rewrite RawXBV.extr_of_zeros by (autorewrite with xbv_size; lia).
    rewrite RawXBV.extr_of_zeros by (autorewrite with xbv_size; lia).
    rewrite RawXBV.concat_assoc.
    rewrite RawXBV.concat_zeros.
    rewrite RawXBV.extr_of_extr by (autorewrite with xbv_size; lia).
    autorewrite with xbv_size.
    f_equal; f_equal; lia.
  Qed.
  
  Lemma extr_shr_extend w1 w2 (xbv : xbv w1) shamt  :
    extr (shr (concat (zeros w2) xbv) shamt) 0 w1 =
    shr xbv shamt.
  Proof.
    destruct (dec (shamt <= w1))%N.
    - eapply extr_shr_extend_no_overshift. eassumption.
    - eapply extr_shr_extend_overshift. lia.
  Qed.
  
  Lemma extr_shl_extend_overshift w1 w2 (xbv : xbv w1) shamt  :
    (shamt > w1)%N ->
    extr (shl (concat (zeros w2) xbv) shamt) 0 w1 =
    shl xbv shamt.
  Proof.
    intros. bitvector_erase.
    destruct (dec (shamt >= w2 + w1))%N.
    - subst.
      rewrite ! RawXBV.shl_overshift by (autorewrite with xbv_size; crush).
      autorewrite with xbv_size.
      eapply RawXBV.extr_of_zeros. lia.
    - subst.
      rewrite ! RawXBV.shl_overshift with (xbv:=bv0) by (autorewrite with xbv_size; crush).
      rewrite ! RawXBV.shl_as_concat.
      rewrite ! N2Nat.id.
      fold (RawXBV.size bv0) in *.
      autorewrite with xbv_size.
      rewrite RawXBV.extr_of_concat with (xbv_lo := bv0) by (autorewrite with xbv_size; lia).
      rewrite RawXBV.extr_of_concat_lo by (autorewrite with xbv_size; crush).
      apply RawXBV.extr_of_zeros. lia.
  Qed.
  
  Lemma extr_shl_extend_no_overshift w1 w2 (xbv : xbv w1) shamt  :
    (shamt <= w1)%N ->
    extr (shl (concat (zeros w2) xbv) shamt) 0 w1 =
    shl xbv shamt.
  Proof.
    intros.
    bitvector_erase. subst.
    rewrite ! RawXBV.shl_as_concat.
    rewrite ! N2Nat.id.
    fold (RawXBV.size bv0) in *.
    autorewrite with xbv_size.
    rewrite ! RawXBV.extr_of_concat by (autorewrite with xbv_size; lia).
    rewrite ! RawXBV.extr_of_zeros by (autorewrite with xbv_size; lia).
    rewrite RawXBV.extr_of_extr by (autorewrite with xbv_size; lia).
    autorewrite with xbv_size.
    f_equal.
    - rewrite RawXBV.concat_empty1 by (autorewrite with xbv_size; lia).
      f_equal; crush.
    - f_equal. crush.
  Qed.
  
  Lemma extr_shl_extend w1 w2 (xbv : xbv w1) shamt :
    extr (shl (concat (zeros w2) xbv) shamt) 0 w1 =
    shl xbv shamt.
  Proof.
    destruct (dec (shamt <= w1))%N.
    - eapply extr_shl_extend_no_overshift. eassumption.
    - eapply extr_shl_extend_overshift. lia.
  Qed.
  
  Lemma extr_exes n1 n2 lo :
    extr (exes n1) lo n2 = exes n2.
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
      simpl in *. specialize (H n1). insterU H.
      crush.
    - destruct n1; [crush|].
      simpl in *. specialize (H n1). insterU H.
      crush.
  Qed.

  Definition bit_of_as_bv i w (bv : BV.bitvector w) :
    i < N.to_nat w ->
    bitOf i (from_bv bv) = RawXBV.bool_to_bit (BV.bitOf i bv).
  Proof.
    destruct bv as [bv bv_wf]. unfold RawBV.size in *.
    unfold bitOf, RawXBV.bitOf, from_bv, RawXBV.from_bv, BV.bitOf, RawBV.bitOf;
      simpl.
    intros.
    rewrite List.nth_indep with (d':=O)
      by (rewrite List.length_map; lia).
    replace O with (RawXBV.bool_to_bit false)
      by reflexivity.
    apply List.map_nth.
  Qed.
End XBV.
