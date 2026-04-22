(**************************************************************************)
(*                                                                        *)
(*     SMTCoq-Api                                                         *)
(*     Copyright (C) 2020 - 2022                                          *)
(*                                                                        *)
(*     Author: Chantal Keller - LMF, Université Paris-Saclay              *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

From Stdlib Require Import Lia.
From Stdlib Require Program.Wf.
From Stdlib Require Import ZArith.

From vera Require Import BVList.
Import BITVECTOR_LIST.

From Stdlib Require Import Program.Equality.

Import EqNotations.
Import List.ListNotations.
Local Open Scope list.

Inductive sort : Set :=
| Sort_Bool
(* SMTLIB says m > 0, but SMTCoq uses N in src/bva/BVList.v *)
| Sort_BitVec (m : N)
.

Definition interp_sort (s : sort) : Type :=
match s with
| Sort_Bool => bool
| Sort_BitVec w => bitvector w
end.

(* Uninterpreted functions. Remarks:
   - predicate symbols are function symbols of codomain Bool
   - variables are function symbols without arguments
 *)
Definition const_sym := nat.

Variant BVUnaryOp : Set :=
  | BVNot
  | BVNeg
.

Variant BVBinOp : Set :=
  | BVAnd
  | BVOr
  | BVXor
  | BVAdd
  | BVMul
  (* | BVUDiv
   * | BVURem *)
  | BVShl
  | BVShr
.

Inductive term : sort -> Type :=
(* Every constant reference is annotated. This corresponds to (as <var> <sort>) in SMTLIB. *)
| Term_Const (s : sort) : const_sym -> term s
| Term_Eq {s} : term s -> term s -> term Sort_Bool
| Term_And : term Sort_Bool -> term Sort_Bool -> term Sort_Bool
| Term_Or : term Sort_Bool -> term Sort_Bool -> term Sort_Bool
| Term_Not : term Sort_Bool -> term Sort_Bool
| Term_ITE {s : sort} : term Sort_Bool -> term s -> term s -> term s
| Term_True : term Sort_Bool
| Term_False : term Sort_Bool
| Term_BVLit w : bitvector w -> term (Sort_BitVec w)
| Term_BVConcat {w1 w2} : term (Sort_BitVec w1) -> term (Sort_BitVec w2) -> term (Sort_BitVec (w1 + w2))
| Term_BVExtract {w} (hi lo : N) (wf : (lo <= hi)%N) : term (Sort_BitVec w) -> term (Sort_BitVec (1 + hi - lo))
| Term_BVUnaryOp {w} : BVUnaryOp -> term (Sort_BitVec w) -> term (Sort_BitVec w)
| Term_BVBinOp {w} : BVBinOp -> term (Sort_BitVec w) -> term (Sort_BitVec w) -> term (Sort_BitVec w)
| Term_BVUlt {w} : term (Sort_BitVec w) -> term (Sort_BitVec w) -> term Sort_Bool
.

Definition dec_sort (s1 s2 : sort) : { s1 = s2 } + { s1 <> s2 }.
Proof. repeat decide equality. Defined.

Definition valuation :=  forall (s : sort) (n : nat), interp_sort s.

(* Interpretation *)
Section Interpretation.
  Definition value_eqb {s} : interp_sort s -> interp_sort s -> bool :=
  match s as s' return interp_sort s' -> interp_sort s' -> bool with
  | Sort_Bool => Bool.eqb
  | Sort_BitVec w => @bv_eq w
  end.

  Lemma value_eqb_eq s v1 v2 : @value_eqb s v1 v2 = true <-> v1 = v2.
  Proof.
    destruct s; simpl in *.
    - apply Bool.eqb_true_iff.
    - apply bv_eq_reflect.
  Qed.

  Lemma value_eqb_refl s v : @value_eqb s v v = true.
  Proof. apply value_eqb_eq. reflexivity. Qed.

  (* TODO: This is probably wrong. *)
  Program Fixpoint bv2nat {m} (bv : bitvector m) {measure (nat_of_N m)} : nat :=
    match bits bv with
    | nil =>
        0
    | (b :: bs) =>
        (if b then 2 ^ (nat_of_N m) else 0) + bv2nat (of_bits bs)
    end
  .
  Next Obligation.
    destruct m.
    - destruct bv0; destruct bv0; simpl in *; discriminate.
    - destruct bv0; destruct bv0; simpl in *; try discriminate.
      unfold RAWBITVECTOR_LIST.size in *; simpl in *.
      inversion Heq_anonymous; subst.
      lia.
  Qed.

  (* TODO: This is probably wrong. *)
  Program Fixpoint nat2bv (n : nat) {measure n} : {m : N & bitvector m} :=
    match n with
    | 0 => existT _ 0%N (of_bits [])
    | _ =>
        let 'existT _ m head := nat2bv (n / 2) in
        (existT _ (m + 1)%N (bv_concat head (of_bits [n mod 2 =? 1])))
    end
  .
  Next Obligation.
    pose proof (Nat.divmod_spec n 1 0 1) as H.
    specialize (H ltac:(lia)).
    destruct (Nat.divmod n 1 0 1).
    simpl in *.
    lia.
  Qed.

  (* Interpretation of terms *)
  Variable ρ : valuation.

  Fixpoint interp_term {s} (t:term s) : (interp_sort s) :=
    match t with
    (* TODO: uninterpreted functions *)
    | Term_Const s n => ρ s n
    | Term_Eq t1 t2 =>
	value_eqb (interp_term t1) (interp_term t2)
    | Term_And t1 t2 => ((interp_term t1) && (interp_term t2))%bool
    | Term_Or t1 t2 =>
      ((interp_term t1) || (interp_term t2))%bool
    | Term_Not t => negb (interp_term t)
    | Term_ITE t1 t2 t3 =>
      if interp_term t1 then interp_term t2 else interp_term t3
    | Term_True => true
    | Term_False => false
    | Term_BVLit w bv => bv
    | Term_BVConcat t1 t2 =>
      bv_concat (interp_term t1) (interp_term t2)
    | Term_BVExtract hi lo _ t =>
      bv_extr lo _ (interp_term t)
    | Term_BVUnaryOp op t =>
      match op with
      | BVNot => bv_not (interp_term t)
      | BVNeg => bv_neg (interp_term t)
      end
    | Term_BVBinOp binop t1 t2 =>
      match binop with
      | BVAnd => bv_and (interp_term t1) (interp_term t2)
      | BVOr => bv_or (interp_term t1) (interp_term t2)
      (* TODO: Follow standard more precisely. This should be an abbreviation:
      (bvxor s t) abbreviates (bvor (bvand s (bvnot t)) (bvand (bvnot s) t))
      *)
      | BVXor => bv_xor (interp_term t1) (interp_term t2)
      | BVAdd => bv_add (interp_term t1) (interp_term t2)
      | BVMul => bv_mult (interp_term t1) (interp_term t2)
      (* Divide does not exist in SMTCoq bitvectors *)
      (* (existT _ (Sort_BitVec m1) (bv_udiv (interp_term t1) (interp_term t2))) *)
      (* (existT _ (Sort_BitVec m1) (bv_rem (interp_term t1) (interp_term t2))) *)
      (* | BVUDiv => None
       * | BVURem => None *)
      | BVShl => bv_shl (interp_term t1) (interp_term t2)
      | BVShr => bv_shr (interp_term t1) (interp_term t2)
      end
    | Term_BVUlt t1 t2 =>
      (bv2nat (interp_term t1) <=? bv2nat (interp_term t2))
    end.

  Definition interp_formula (t:term Sort_Bool) : bool := interp_term t.

End Interpretation.
