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

(* Uninterpreted sorts *)
Definition sort_sym := nat.

Inductive sort : Set :=
| Sort_Bool
| Sort_Int
(* SMTLIB says m > 0, but SMTCoq uses N in src/bva/BVList.v *)
| Sort_BitVec (m : N)
| Sort_Uninterpreted (_:sort_sym)
.

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
  | BVAdd
  | BVMul
  | BVUDiv
  | BVURem
  | BVShl
  | BVShr
.

Inductive term : Type :=
| Term_Const : const_sym -> term
| Term_Int : Z -> term
| Term_Geq : term -> term -> term
| Term_Eq : term -> term -> term
| Term_And : term -> term -> term
| Term_Or : term -> term -> term
| Term_Not : term -> term
| Term_ITE : term -> term -> term -> term
| Term_True : term
| Term_False : term
| Term_BVLit (w: N) : bitvector w -> term
| Term_BVConcat : term -> term -> term
| Term_BVExtract : nat -> nat -> term -> term
| Term_BVUnaryOp : BVUnaryOp -> term -> term
| Term_BVBinOp : BVBinOp -> term -> term -> term
| Term_BVUlt : term -> term -> term
.

Definition dec_sort (s1 s2 : sort) : { s1 = s2 } + { s1 <> s2 }.
Proof. repeat decide equality. Defined.

(* To be able to interpret function symbol application, we introduce
   an informative cast between sorts

   See
   https://www.lri.fr/~keller/Documents-recherche/Publications/thesis13.pdf
   Sec.3.2.2 *)
Section Cast.
  Definition cast_result (A:Type) (n m:A) :=
    option (forall (P:A -> Type), P n -> P m).
  Definition idcast (A:Type) (n:A) : cast_result A n n :=
    Some (fun P x => x).
  Arguments idcast {A n}.

  Fixpoint nat_cast (n m:nat) : cast_result nat n m :=
    match n, m with
    | O, O => idcast
    | S n, S m =>
        match nat_cast n m with
        | Some k => Some (fun P => k (fun x => P (S x)))
        | None => None
        end
    | _, _ => None
    end.

  Lemma nat_cast_refl:
    forall n, nat_cast n n = idcast.
  Proof. induction n as [ |n IHn]; simpl; try rewrite IHn; auto. Qed.

  Fixpoint pos_cast (n m: positive) : cast_result positive n m :=
    match n, m with
    | xH, xH => idcast
    | xO n, xO m =>
        match pos_cast n m with
        | Some k => Some (fun P => k (fun x => P (xO x)))
        | None => None
        end
    | xI n, xI m =>
        match pos_cast n m with
        | Some k => Some (fun P => k (fun x => P (xI x)))
        | None => None
        end
    | _, _ => None
    end.

  Lemma pos_cast_refl:
    forall n, pos_cast n n = idcast.
  Proof. induction n; simpl; try rewrite IHn; auto. Qed.

  Definition N_cast (n m: N) : cast_result N n m :=
    match n, m with
    | N0, N0 => idcast
    | Npos n, Npos m =>
        match pos_cast n m with
        | Some k => Some (fun P => k (fun x => P (Npos x)))
        | None => None
        end
    | _, _ => None
    end.

  Lemma N_cast_refl:
    forall n, N_cast n n = idcast.
  Proof. induction n; simpl; try rewrite pos_cast_refl; try rewrite IHn; auto. Qed.

  Definition cast (A B:sort) : cast_result sort A B :=
    match A, B return cast_result sort A B with
    | Sort_Bool, Sort_Bool => idcast
    | Sort_Int, Sort_Int => idcast
    | Sort_BitVec m1, Sort_BitVec m2 =>
        match N_cast m1 m2 with
        | Some k => Some (fun P => k (fun x => P (Sort_BitVec x)))
        | None => None
        end
    | Sort_Uninterpreted n1, Sort_Uninterpreted n2 =>
        match nat_cast n1 n2 with
        | Some k => Some (fun P => k (fun x => P (Sort_Uninterpreted x)))
        | None => None
        end
    | _, _ => None
    end.

  Lemma cast_refl:
    forall s, cast s s = idcast.
  Proof.
    destruct s as [ | |m|n]; simpl; auto.
    - now rewrite N_cast_refl.
    - now rewrite nat_cast_refl.
  Qed.
End Cast.

(* Interpretation *)
Section Interpretation.

  Variant value : Type :=
    | Value_Bool (b : bool)
    | Value_Int (i : Z)
    | Value_BitVec (w : N) (bv : bitvector w)
  .

  Definition value_eqb (v1 v2 : value) : bool :=
    match v1, v2 with
    | Value_Bool b1, Value_Bool b2 => Bool.eqb b1 b2
    | Value_Int z1, Value_Int z2 => Z.eqb z1 z2
    | Value_BitVec w1 bv1, Value_BitVec w2 bv2 =>
        match N.eq_dec w1 w2 with
        | left eq => bv_eq bv1 (rew <- eq in bv2)
        | right _ => false
        end
    | _, _ => false
    end.

  Lemma value_eqb_eq v1 v2 : value_eqb v1 v2 = true <-> v1 = v2.
  Proof.
    split; intros H.
    - destruct v1, v2; simpl in *; try discriminate.
      + rewrite Bool.eqb_true_iff in H. subst.
        reflexivity.
      + rewrite Z.eqb_eq in H. subst.
        reflexivity.
      + destruct (N.eq_dec w w0); try discriminate.
        subst.
        replace (rew <- [bitvector] eq_refl in bv1) with bv1 in H by reflexivity.
        apply bv_eq_reflect in H. subst.
        reflexivity.
    - subst.
      destruct v2; simpl.
      + rewrite Bool.eqb_true_iff. reflexivity.
      + rewrite Z.eqb_eq. reflexivity.
      + destruct (N.eq_dec w w); try contradiction.
        dependent destruction e.
        replace (rew <- [bitvector] eq_refl in bv0) with bv0 by reflexivity.
        apply bv_eq_refl.
  Qed.

  Lemma value_eqb_refl v : value_eqb v v = true.
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
  Variable interp_const_sym : nat -> option value.

  Fixpoint interp_term (t:term) : option value :=
    match t with
    (* TODO: uninterpreted functions *)
    | Term_Const n => interp_const_sym n
    | Term_Int z => Some (Value_Int z)
    | Term_Geq t1 t2 =>
        match interp_term t1, interp_term t2 with
        | Some (Value_Int z1), Some (Value_Int z2) =>
            Some (Value_Bool (z1 >=? z2)%Z)
        | _, _ => None
        end
    | Term_Eq t1 t2 =>
        match interp_term t1, interp_term t2 with
        | Some v1, Some v2 =>
            Some (Value_Bool (value_eqb v1 v2))
        | _, _ => None
        end
    | Term_And t1 t2 =>
        match interp_term t1, interp_term t2 with
        | Some (Value_Bool b1), Some (Value_Bool b2) =>
            Some (Value_Bool (b1 && b2)%bool)
        | _, _ => None
        end
    | Term_Or t1 t2 =>
        match interp_term t1, interp_term t2 with
        | Some (Value_Bool b1), Some (Value_Bool b2) =>
            Some (Value_Bool (b1 || b2)%bool)
        | _, _ => None
        end
    | Term_Not t =>
        match interp_term t with
        | Some (Value_Bool b) => Some (Value_Bool (negb b))
        | _ => None
        end
    | Term_ITE t1 t2 t3 =>
        match interp_term t1, interp_term t2, interp_term t3 with
        | Some (Value_Bool b1), Some v2, Some v3 =>
            if b1 then Some v2 else Some v3
        | _, _, _ => None
        end
    | Term_True => Some (Value_Bool true)
    | Term_False => Some (Value_Bool false)
    | Term_BVLit w bv =>
        Some (Value_BitVec w bv)
    | Term_BVConcat t1 t2 =>
        match interp_term t1, interp_term t2 with
        | Some (Value_BitVec m1 bv1), Some (Value_BitVec m2 bv2) =>
            Some (Value_BitVec (m1 + m2) (bv_concat bv1 bv2))
        | _, _ => None
        end
    | Term_BVExtract hi lo t =>
        match interp_term t with
        | Some (Value_BitVec m bv) =>
            if (lo <=? hi)
            then Some (Value_BitVec (N_of_nat (hi - lo + 1)) (bv_extr (N_of_nat lo) _ bv))
            else None
        | _ => None
        end
    | Term_BVUnaryOp op t =>
        match interp_term t with
        | Some (Value_BitVec m bv) =>
            match op with
            | BVNot => Some (Value_BitVec m (bv_not bv))
            | BVNeg => Some (Value_BitVec m (bv_neg bv))
            end
        | _ => None
        end
    | Term_BVBinOp binop t1 t2 =>
        match interp_term t1, interp_term t2 with
        | Some (Value_BitVec m1 bv1),
          Some (Value_BitVec m2 bv2_2) =>
            match N.eq_dec m2 m1 with
            | left e =>
                let bv2 : bitvector m1 := eq_rect m2 bitvector bv2_2 m1 e in
                match binop with
                | BVAnd => Some (Value_BitVec m1 (bv_and bv1 bv2))
                | BVOr =>  Some (Value_BitVec m1 (bv_or bv1 bv2))
                | BVAdd => Some (Value_BitVec m1 (bv_add bv1 bv2))
                | BVMul => Some (Value_BitVec m1 (bv_mult bv1 bv2))
                | BVUDiv =>
                    (* Divide does not exist in SMTCoq bitvectors *)
                    (* Some (existT _ (Sort_BitVec m1) (bv_udiv bv1 bv2)) *)
                    None
                | BVURem =>
                    (* Divide does not exist in SMTCoq bitvectors *)
                    (* Some (existT _ (Sort_BitVec m1) (bv_rem bv1 bv2)) *)
                    None
                | BVShl => Some (Value_BitVec m1 (bv_shl bv1 bv2))
                | BVShr => Some (Value_BitVec m1 (bv_shr bv1 bv2))
                end
            | right _ => None
            end
        | _, _ => None
        end
    | Term_BVUlt t1 t2 =>
        match interp_term t1, interp_term t2 with
        | Some (Value_BitVec m1 bv1),
          Some (Value_BitVec m2 bv2) =>
            if (m1 =? m2)%N
            then Some (Value_Bool (bv2nat bv1 <=? bv2nat bv2))
            else None
        | _, _ => None
        end
    end.

  Definition interp_formula (t:term) : bool :=
    match interp_term t with
    | Some (Value_Bool b) => b
    | _ => true
    end.

End Interpretation.
