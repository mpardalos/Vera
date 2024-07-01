Require Import BinNat.
Require Import BinPos.
Require Import Psatz.
Require Import Structures.OrderedType.
Require Import Program.
Require Import Arith.
From Coq Require Import Logic.ProofIrrelevance.

From Equations Require Import Equations.

Module Bitvector.

  Local Open Scope N.

  (** Unsigned bitvectors *)
  Record bv :=
    BV
      { value : N
      ; width : positive
      ; wf : value < 2 ^ (Npos width)
      }.

  Theorem bv_eq : forall v1 w1 v2 w2 prf1 prf2,
      v1 = v2 ->
      w1 = w2 ->
      BV v1 w1 prf1 = BV v2 w2 prf2.
  Proof.
    intros * Hv Hw.
    subst.
    f_equal.
    apply proof_irrelevance.
  Qed.

  Definition eq_dec : forall (bv1 bv2 : bv), { bv1 = bv2 } + { bv1 <> bv2 }.
  Proof.
    intros.
    destruct bv1, bv2.
    destruct (N.eq_dec value0 value1).
    - subst.
      destruct (Pos.eq_dec width0 width1).
      + subst.
        left.
        f_equal.
        apply proof_irrelevance.
      + right.
        intros contra.
        inversion contra.
        contradiction.
    - right.
      intros contra.
      inversion contra.
      contradiction.
  Qed.

  Program Definition mkBV_check (v : N) (w : positive) :=
    if dec (v <? (Npos (2 ^ w)))%N
    then Some (BV v w _)
    else None.
  Next Obligation. apply N.ltb_lt. auto. Qed.

  Notation mkBV v w := (BV v w ltac:(lia)) (only parsing).

  (** Add the bitvectors, adding a bit to the width to accomodate overflow *)
  Equations bv_add_extend (bv1 bv2 : bv) (width_match : (width bv1 = width bv2)) : bv :=
    bv_add_extend (BV v1 w wf1) (BV v2 ?(w) wf2) eq_refl := BV (v1 + v2) (w + 1) _.
  Next Obligation.
    enough (2 * N.pos (2 ^ w) = N.pos (2 ^ (w + 1))) by lia.
    replace (2 * N.pos (2 ^ w)) with (2 * 2 ^ (Npos w)) by lia.
    replace (N.pos (2 ^ (w + 1))) with (2 ^ (Npos w + 1)) by lia.
    rewrite <- N.pow_succ_r by lia.
    lia.
   Qed.

  Lemma bv_add_extend_width :
    forall (bv1 bv2: bv) (width_match : width bv1 = width bv2),
      width (bv_add_extend bv1 bv2 width_match) = (width bv1 + 1)%positive.
  Proof.
    intros.
    funelim (bv_add_extend bv1 bv2 width_match).
    simp bv_add_extend.
    reflexivity.
  Qed.

  (** Add the bitvectors, truncating the carry bit of the result *)
  Equations bv_add_truncate (bv1 bv2 : bv) (width_match : (width bv1 = width bv2)) : bv :=
    | (BV v1 w wf1), (BV v2 ?(w) wf2), eq_refl => BV ((v1 + v2) mod (2 ^ Npos w)) w _.
  Next Obligation.
    apply N.mod_lt. lia.
  Qed.

  Lemma bv_add_truncate_width :
    forall (bv1 bv2: bv) (width_match : width bv1 = width bv2),
      width (bv_add_truncate bv1 bv2 width_match) = (width bv1)%positive.
  Proof.
    intros.
    funelim (bv_add_truncate bv1 bv2 width_match).
    simp bv_add_truncate.
    simpl.
    reflexivity.
  Qed.
End Bitvector.
