From Coq Require Import Arith.
From Coq Require Import NArith.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import String.
From Coq Require Import Logic.Decidable.

From SMTCoq Require Import BVList.

From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Data.Monads.OptionMonad.
From ExtLib Require Import Data.List.

From vera Require Import Tactics.
From vera Require Import Common.
From vera Require Import Decidable.

From Equations Require Import Equations.
Set Equations With UIP.

(* Import after Equations, conflicting "UIP" *)
From Coq Require Import Eqdep.
Import EqdepTheory.
Import EqNotations.

Import SigTNotations.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope bv_scope.

Set Bullet Behavior "Strict Subproofs".

Module RawBV.
  Include RAWBITVECTOR_LIST.
  Notation t := bitvector.
  (* Definition some_bitvector := {n : _ & bitvector n}. *)
  Definition is_zero (a : bitvector) :=
    bv_eq a (zeros (size a)).

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

  Lemma pow2_pow i : pow2 i = 2 ^ i.
  Proof.
    induction i; simpl.
    { reflexivity. }
    rewrite IHi. lia.
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
End RawBV.

Module BV.
  Include BITVECTOR_LIST.

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

  Definition is_zero {n} (bv : bitvector n) : bool :=
    bv_eq bv (zeros n).

  Definition to_N {n} (bv : bitvector n) : N :=
    RawBV.to_N (bits bv).

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

  Definition xbv := list bit.

  Definition size (xbv : xbv) := N.of_nat (length xbv).

  Definition of_bits (bs : list bit) : xbv := bs.

  Arguments size / _.

  Fixpoint mk_list_exes (count : nat) : xbv :=
    match count with
    | 0%nat => []
    | S n => X :: mk_list_exes n
    end
  .

  Definition exes (count : N) : xbv := mk_list_exes (nat_of_N count).

  Lemma exes_size {n} : size (exes n) = n.
  Proof.
    unfold exes.
    induction n using N.peano_rect; simpl.
    - reflexivity.
    - rewrite Nnat.N2Nat.inj_succ. simpl in *.
      lia.
  Qed.

  Definition bit_eq_dec (b1 b2: bit) : { b1 = b2 } + { b1 <> b2 }.
  Proof. unfold decidable. decide equality. Qed.

  Definition eq_dec (bv1 bv2: xbv) : { bv1 = bv2 } + { bv1 <> bv2 }.
  Proof. decide equality. apply bit_eq_dec. Qed.

  Definition from_bv (bv : RawBV.t) : xbv :=
    List.map (fun (b: bool) => if b then I else O) bv
  .

  Lemma from_bv_size bv :
    size (from_bv bv) = RawBV.size bv.
  Proof.
    unfold size, RawBV.size.
    induction bv; simpl; lia.
  Qed.

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

  (* Definition from_sized_bv {w} (bv : BV.bitvector w) : xbv := *)
  (*   from_bv (BV.bits bv). *)

  (* Definition to_sized_bv (v : xbv) : option (BV.bitvector (size v)) := *)
  (*   match to_bv v as x return _ = x -> _ with *)
  (*   | Some bv => fun e => Some {| BV.bv := bv; BV.wf := to_bv_size xbv bv e |} *)
  (*   | None => fun e => None *)
  (*   end eq_refl. *)

  (* Import EqNotations. *)

  Equations to_bv_same_width (l r : xbv) : option (RawBV.t * RawBV.t) :=
    to_bv_same_width l r with dec (size r = size l), to_bv l, to_bv r => {
      | left e, Some l_bv, Some r_bv => Some (l_bv, r_bv)
      | _, _, _ => None
      }.

  (* Equations to_sized_bv_same_width (l r : t) : option (BV.bitvector (size l) * BV.bitvector (size l)) := *)
  (*   to_sized_bv_same_width l r with dec (size r = size l), to_sized_bv l, to_sized_bv r => { *)
  (*     | left e, Some l_bv, Some r_bv => Some (l_bv, rew e in r_bv) *)
  (*     | _, _, _ => None *)
  (*     }. *)

  Equations extract (x: xbv) (i j: nat) : xbv :=
    extract [] i j := [];
    extract (bx :: x') 0 0 := [];
    extract (bx :: x') 0 (S j') := bx :: extract x' 0 j';
    extract (bx :: x') (S i') j := extract x' i' j.

  Lemma extract_width x i j :
    j + i <= length x ->
    length (extract x i j) = j.
  Proof.
    funelim (extract x i j);
      simp extract; simpl in *; try crush.
  Qed.

  Definition extr (v : xbv) (i j : N) : xbv :=
    if (j + i <? size v)%N
    then extract v (nat_of_N i) (nat_of_N j)
    else exes j.

  Lemma extr_width x i j :
    size (extr x i j) = j.
  Proof.
    unfold extr, size.
    autodestruct_eqn E.
    - rewrite N.ltb_lt in E.
      rewrite extract_width; try crush.
    - apply exes_size.
  Qed.

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
  Qed.

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
    apply UIP.
  Qed.


  Lemma xbv_bv_inverse n (bv : BV.bitvector n) :
      to_bv (from_bv bv) = Some bv.
  Proof.
    funelim (to_bv (from_bv bv)); rewrite <- Heqcall in *; clear Heqcall; clear Heq.
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

  Definition exes (count : N) : xbv count :=
    {| bv := RawXBV.exes count; wf := RawXBV.exes_size |}.

  Program Definition concat {n m : N} (l : xbv n) (r : xbv m) : xbv (n + m) :=
    {| bv := bv r ++ bv l |}.
  Next Obligation.
    destruct l, r; simpl in *.
    rewrite app_length.
    lia.
  Qed.

  Program Definition replicate (n : N) (b : bit) : xbv n :=
    of_bits (repeat b (N.to_nat n)).
  Next Obligation. rewrite repeat_length. lia. Qed.

  (* Shouldn't this be adding bits at the end? *)
  Definition extend {n} (i : N) (b : bit) (v : xbv n) : xbv (i + n) :=
    rew (N.add_comm n i) in concat v (replicate i b).

  Ltac destruct_rews :=
    repeat match goal with
           | |- context[rew [ _ ] ?e in _ ] =>
               destruct e; simpl
           | [H : context[rew [ _ ] ?e in _ ] |- _ ] =>
               destruct e; simpl
           end.

  Lemma extend_bits w i b (v : xbv w) :
    bits (extend i b v) = repeat b (N.to_nat i) ++ bits v.
  Proof.
    unfold extend, replicate.
    destruct_rews.
    now rewrite repeat_length, N2Nat.id.
  Qed.

  Lemma extend_zero_to_bv n i (bv : BV.bitvector n) :
    to_bv (extend i O (XBV.from_bv bv)) = Some (BV.bv_zextn i bv).
  Proof.
    destruct bv as [bv wf].
    rewrite <- xbv_bv_inverse.
    f_equal.
    apply of_bits_equal; simpl.
    rewrite extend_bits; simpl.
    unfold RawBV.bv_zextn, RAWBITVECTOR_LIST.zextend.
    induction (N.to_nat i); crush.
  Qed.

  Definition zextn {n} (v : xbv n) (i : N) :=
    extend i O v.

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

  Definition extr {n} (x: xbv n) (i j: N) : xbv j :=
    {|
      bv := RawXBV.extr (bits x) i j;
      wf := RawXBV.extr_width _ _ _
    |}.

  Lemma extr_to_bv (n i j : N) (bv : BV.bitvector n) :
    (i + j < n)%N ->
    XBV.to_bv (XBV.extr (XBV.from_bv bv) i j) = Some (BV.bv_extr i j bv).
  Proof.
    intros. destruct bv as [bv wf].
    rewrite <- xbv_bv_inverse. f_equal.
    apply of_bits_equal; simpl.
    unfold RawXBV.extr.
    rewrite RawXBV.from_bv_size. rewrite wf. rewrite <- N.ltb_lt in H. rewrite N.add_comm in H. rewrite H.
    unfold RAWBITVECTOR_LIST.bv_extr.
    rewrite N.ltb_lt in H.
    replace (n <? j + i)%N with false; cycle 1. {
      symmetry. apply N.ltb_ge. lia.
    }

    (* Rewrite everything in terms of Nats instead of N *)
    remember (N.to_nat i) as i_nat.
    remember (N.to_nat j) as j_nat.
    replace (N.to_nat (j + i)) with (j_nat + i_nat) by lia.
    unfold RAWBITVECTOR_LIST.size in *.
    assert (j_nat + i_nat < length bv) by lia.
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
      + rewrite IHbv; try crush. now rewrite Nat.add_comm.
      + rewrite IHbv; repeat f_equal; lia.
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
End XBV.
