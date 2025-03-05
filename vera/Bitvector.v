From Coq Require Import BinNat BinPos.
From Coq Require Import List.
From Coq Require Import Nat.
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

Import SigTNotations.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope bv_scope.

Set Bullet Behavior "Strict Subproofs".

Module BV.
  Include RAWBITVECTOR_LIST.
  Notation t := bitvector.
  (* Definition some_bitvector := {n : _ & bitvector n}. *)
  Definition is_zero (a : bitvector) :=
    bv_eq a (zeros (size a)).

  Equations of_pos_full (value : positive) : bitvector := {
    | xH => [true]
    | (p~1)%positive => bv_concat [true] (of_pos_full p)
    | (p~0)%positive => bv_concat [false] (of_pos_full p)
  }.

  Equations of_N_full (value : N) : bitvector := {
    | N0 => [false]
    | Npos p => of_pos_full p
  }.

  (** We use concat instead of bv_zextn because bv_zextn is broken! It adds
  zeros at the start instead of the end, effectively shifting the value *)
  (* TODO: Report issue with zextn *)
  Definition of_pos_fixed (width : N) (value : positive) : bitvector :=
    let bv := of_pos_full value in
    if (N.ltb (size bv) width)
    then bv_concat bv (zeros (width - size bv))
    else bv_extr 0 width (size bv) bv.

  Definition of_N_fixed (width : N) (value : N) : bitvector :=
    let bv := of_N_full value in
    if (N.ltb (size bv) width)
    then bv_concat bv (zeros (width - size bv))
    else bv_extr 0 width (size bv) bv.

  Fixpoint to_positive (bs : list bool) : positive :=
    match bs with
    | [] => xH (** wrong! *)
    | b :: bs =>
        if b
        then if negb (fold_left orb bs false)
             then xH
             else (to_positive bs)~1
        else (to_positive bs)~0
    end.

  Definition to_N (val : bitvector) : N :=
    if negb (fold_left orb (bits val) false)
    then N0
    else Npos (to_positive (bits val)).

  Fixpoint to_string (val : bitvector) : string :=
    match val with
    | [] => ""
    | b::bs => to_string bs ++ (if b then "1" else "0")
    end.
End BV.

Module XBV.
  Variant bit := X | I | O.

  Definition bit_to_bool b :=
    match b with
    | I => Some true
    | O => Some false
    | X => None
    end
  .

  Definition t := list bit.

  Definition size (xbv : t) := N.of_nat (length xbv).

  Fixpoint mk_list_exes (count : nat) : t :=
    match count with
    | 0%nat => []
    | S n => X :: mk_list_exes n
    end
  .

  Definition exes (count : N) : t := mk_list_exes (nat_of_N count).

  Definition bit_eq_dec (b1 b2: bit) : { b1 = b2 } + { b1 <> b2 }.
  Proof. unfold decidable. decide equality. Qed.

  Definition eq_dec (bv1 bv2: t) : { bv1 = bv2 } + { bv1 <> bv2 }.
  Proof. decide equality. apply bit_eq_dec. Qed.

  Definition from_bv (bv : BV.t) : t :=
    List.map (fun (b: bool) => if b then I else O) bv
  .

  Definition to_bv (bv : t) : option BV.t :=
    mapT bit_to_bool bv
  .

  Definition has_x (bv : t) : Prop :=
    List.Exists (fun b => b = X) bv.

  Lemma has_x_to_bv (bv : t) : has_x bv <-> to_bv bv = None.
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

  Lemma not_has_x_to_bv (bv : t) : ~ (has_x bv) <-> exists v, to_bv bv = Some v.
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
        if (length l) =? (length r)
        then exes (size l)
        else nil
    end
  .

  (* Shouldn't this be adding bits at the end? *)
  Fixpoint extend (xbv : t) (i : nat) (b : bit) :=
    match i with
    | 0 => xbv
    | S n => b :: extend xbv n b
    end
  .

  Definition zextn (xbv : t) (i : N) :=
    extend xbv (nat_of_N i) O.

  Fixpoint extract (x: t) (i j: nat) : t :=
    match x with
    | [] => []
    | bx :: x' =>
        match i with
        | 0      =>
            match j with
            | 0    => []
            | S j' => bx :: extract x' i j'
            end
        | S i'   =>
            match j with
            | 0    => []
            | S j' => extract x' i' j'
            end
        end
    end.

  Definition extr (xbv : t) (i j : N) : t :=
    extract xbv (nat_of_N i) (nat_of_N j).

  Definition bitOf (n : nat) (xbv: t): bit := nth n xbv X.

  Lemma xbv_bv_inverse : forall bv,
      XBV.to_bv (XBV.from_bv bv) = Some bv.
  Proof.
    intros bv. induction bv.
    - reflexivity.
    - simpl in *.
      destruct a.
      + unfold XBV.to_bv in *. simpl.
        replace (List.mapT_list XBV.bit_to_bool (XBV.from_bv bv)) with (Some bv).
        reflexivity.
      + unfold XBV.to_bv in *. simpl.
        replace (List.mapT_list XBV.bit_to_bool (XBV.from_bv bv)) with (Some bv).
        reflexivity.
  Qed.

  Lemma bv_xbv_inverse : forall xbv bv,
      XBV.to_bv xbv = Some bv ->
      XBV.from_bv bv = xbv.
  Proof. Admitted.

  (*
   * Matches this Verilog operation:
   * bv1 === bv2
   *)
  Definition triple_equal (bv1 bv2 : t) := bv1 = bv2.

  (*
   * Matches this Verilog operation:
   * (bv1 == bv2) === 1
   *)
  Definition definite_equal (bv1 bv2 : t) :=
    exists v, to_bv bv1 = Some v /\ to_bv bv2 = Some v.

  #[global]
  Instance dec_eq_bit (b1 b2 : XBV.bit) : DecProp (b1 = b2) :=
    mk_dec_eq.

  #[global]
  Instance dec_eq_xbv (xbv1 xbv2 : XBV.t) : DecProp (xbv1 = xbv2) :=
    mk_dec_eq.

  #[global]
  Instance dec_has_x xbv : DecProp (XBV.has_x xbv) := _.
End XBV.
