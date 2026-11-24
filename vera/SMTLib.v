From Stdlib Require Import Lia.
From Stdlib Require Program.Wf.
From Stdlib Require Import ZArith.
From Stdlib Require Import String.
From Stdlib Require Import Morphisms.

From vera Require Import Bitvector.
From vera Require Import Tactics.
From vera Require Import Decidable.

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
| Sort_BitVec w => BV.bitvector w
end.

(* Uninterpreted functions. Remarks:
   - predicate symbols are function symbols of codomain Bool
   - variables are function symbols without arguments
 *)
Record const_sym := MkConstSym {
  symName : string;
  symSort : sort
}.

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
  | BVUDiv
  | BVURem
  | BVShl
  | BVShr
.

Inductive term : sort -> Type :=
(* Every constant reference is annotated. This corresponds to (as <var> <sort>) in SMTLIB. *)
| Term_Const (n : const_sym) : term (symSort n)
| Term_Eq {s} : term s -> term s -> term Sort_Bool
| Term_And : term Sort_Bool -> term Sort_Bool -> term Sort_Bool
| Term_Or : term Sort_Bool -> term Sort_Bool -> term Sort_Bool
| Term_Not : term Sort_Bool -> term Sort_Bool
| Term_ITE {s : sort} : term Sort_Bool -> term s -> term s -> term s
| Term_True : term Sort_Bool
| Term_False : term Sort_Bool
| Term_BVLit w : BV.bitvector w -> term (Sort_BitVec w)
| Term_BVConcat {w1 w2} : term (Sort_BitVec w1) -> term (Sort_BitVec w2) -> term (Sort_BitVec (w1 + w2))
| Term_BVExtract {w} (hi lo : N) (wf : (lo <= hi)%N) : term (Sort_BitVec w) -> term (Sort_BitVec (1 + hi - lo))
| Term_BVUnaryOp {w} : BVUnaryOp -> term (Sort_BitVec w) -> term (Sort_BitVec w)
| Term_BVBinOp {w} : BVBinOp -> term (Sort_BitVec w) -> term (Sort_BitVec w) -> term (Sort_BitVec w)
| Term_BVUlt {w} : term (Sort_BitVec w) -> term (Sort_BitVec w) -> term Sort_Bool
.

Definition dec_sort (s1 s2 : sort) : { s1 = s2 } + { s1 <> s2 }.
Proof. repeat decide equality. Defined.

Instance dec_eq_sort (x y : SMTLib.sort) : DecProp (x = y) :=
  mk_dec_eq!(SMTLib.dec_sort).

Definition valuation :=  forall (n : const_sym), interp_sort (symSort n).

Definition default_valuation : valuation := fun n =>
  match symSort n as s return interp_sort s with
  | Sort_Bool => false
  | Sort_BitVec w => BV.zeros w
  end
.

(* Interpretation *)
Section Interpretation.
  Definition value_eqb {s} : interp_sort s -> interp_sort s -> bool :=
  match s as s' return interp_sort s' -> interp_sort s' -> bool with
  | Sort_Bool => Bool.eqb
  | Sort_BitVec w => @BV.bv_eq w
  end.

  Lemma value_eqb_eq s v1 v2 : @value_eqb s v1 v2 = true <-> v1 = v2.
  Proof.
    destruct s; simpl in *.
    - apply Bool.eqb_true_iff.
    - apply BV.bv_eq_reflect.
  Qed.

  Lemma value_eqb_neq s v1 v2 : @value_eqb s v1 v2 = false <-> v1 <> v2.
  Proof.
    split; intros H.
    - intros contra.
      apply value_eqb_eq in contra.
      congruence.
    - destruct (value_eqb v1 v2) eqn:E; try reflexivity.
      apply value_eqb_eq in E.
      contradiction.
  Qed.

  Lemma value_eqb_refl s v : @value_eqb s v v = true.
  Proof. apply value_eqb_eq. reflexivity. Qed.

  (* TODO: This is probably wrong. *)
  Program Fixpoint bv2nat {m} (bv : BV.bitvector m) {measure (nat_of_N m)} : nat :=
    match BV.bits bv with
    | nil =>
        0
    | (b :: bs) =>
        (if b then 2 ^ (nat_of_N m) else 0) + bv2nat (BV.of_bits bs)
    end
  .
  Next Obligation.
    destruct bv as [bits Hsize]. cbn in *. subst bits.
    unfold BVList.RAWBITVECTOR_LIST.size in Hsize. cbn in Hsize. lia.
  Qed.
  Next Obligation.
    apply Wf.measure_wf. apply Nat.lt_wf_0.
  Qed.

  (* TODO: This is probably wrong. *)
  Program Fixpoint nat2bv (n : nat) {measure n} : {m : N & BV.bitvector m} :=
    match n with
    | 0 => existT _ 0%N (BV.of_bits [])
    | _ =>
        let 'existT _ m head := nat2bv (n / 2) in
        (existT _ (m + 1)%N (BV.bv_concat head (BV.of_bits [n mod 2 =? 1])))
    end
  .
  Next Obligation.
    pose proof (Nat.divmod_spec n 1 0 1) as H.
    specialize (H ltac:(lia)).
    destruct (Nat.divmod n 1 0 1).
    simpl in *.
    lia.
  Qed.
  Next Obligation.
    apply Wf.measure_wf. apply Nat.lt_wf_0.
  Qed.

  Definition divmod_undefined {w} : BV.bitvector w. Admitted.

  (* Interpretation of terms *)
  Variable ρ : valuation.

  Fixpoint interp_term {s} (t:term s) : (interp_sort s) :=
    match t with
    (* TODO: uninterpreted functions *)
    | Term_Const n => ρ n
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
      BV.bv_concat (interp_term t1) (interp_term t2)
    | Term_BVExtract hi lo _ t =>
      BV.bv_extr lo _ (interp_term t)
    | Term_BVUnaryOp op t =>
      match op with
      | BVNot => BV.bv_not (interp_term t)
      | BVNeg => BV.bv_neg (interp_term t)
      end
    | Term_BVBinOp binop t1 t2 =>
      match binop with
      | BVAnd => BV.bv_and (interp_term t1) (interp_term t2)
      | BVOr => BV.bv_or (interp_term t1) (interp_term t2)
      (* TODO: Follow standard more precisely. This should be an abbreviation:
      (bvxor s t) abbreviates (bvor (bvand s (bvnot t)) (bvand (bvnot s) t))
      *)
      | BVXor => BV.bv_xor (interp_term t1) (interp_term t2)
      | BVAdd => BV.bv_add (interp_term t1) (interp_term t2)
      | BVMul => BV.bv_mult (interp_term t1) (interp_term t2)
      | BVUDiv => divmod_undefined
      | BVURem => divmod_undefined
      | BVShl => BV.bv_shl (interp_term t1) (interp_term t2)
      | BVShr => BV.bv_shr (interp_term t1) (interp_term t2)
      end
    | Term_BVUlt t1 t2 =>
      (bv2nat (interp_term t1) <=? bv2nat (interp_term t2))
    end.

  Definition interp_formula (t:term Sort_Bool) : bool := interp_term t.
End Interpretation.

Section queries.
  Definition query := list (term (Sort_Bool)).

  Fixpoint term_domain {s} (t : term s) : list const_sym :=
    match t with
    | Term_Const sym => [sym]
    | Term_Eq l r => term_domain l ++ term_domain r
    | Term_And l r => term_domain l ++ term_domain r
    | Term_Or l r => term_domain l ++ term_domain r
    | Term_Not e => term_domain e
    | Term_ITE c t f => term_domain c ++ term_domain t ++ term_domain f
    | Term_True => []
    | Term_False => []
    | Term_BVLit _ _ => []
    | Term_BVConcat l r => term_domain l ++ term_domain r
    | Term_BVExtract _ _ _ e => term_domain e
    | Term_BVUnaryOp _ e => term_domain e
    | Term_BVBinOp _ l r => term_domain l ++ term_domain r
    | Term_BVUlt l r => term_domain l ++ term_domain r
    end
  .

  Definition query_domain (q : query) : list const_sym :=
    List.concat (List.map term_domain q).

  Definition add_assertion (a : term Sort_Bool) (q : query) : query := a :: q.

  Definition combine (q1 q2: query) : query := q1 ++ q2.
End queries.

Section satisfiability.
  Definition term_satisfied_by (ρ: SMTLib.valuation) (t: SMTLib.term Sort_Bool) : Prop :=
    SMTLib.interp_term ρ t = true.
  
  Definition satisfied_by (ρ: valuation) (q: query): Prop :=
    List.Forall (term_satisfied_by ρ) q.
  
  Definition satisfiable (q: query) : Prop :=
    exists ρ, satisfied_by ρ q.
  
  Definition unsatisfiable (q: query) : Prop :=
    forall ρ, ~ satisfied_by ρ q.
  
  Definition valid (q: query) : Prop :=
    forall ρ, satisfied_by ρ q.
  
  Definition invalid (q: query) : Prop :=
    exists ρ, ~ satisfied_by ρ q.

  Lemma valid_satisfiable q :
    valid q -> satisfiable q.
  Proof.
    unfold valid, satisfiable.
    intros.
    exists default_valuation.
    auto.
  Qed.
  
  Lemma unsatisfiable_invalid q :
    unsatisfiable q -> invalid q.
  Proof.
    unfold valid, satisfiable.
    intros.
    exists default_valuation.
    auto.
  Qed.
End satisfiability.

Infix "⊧" := satisfied_by (at level 20).

Section reflection.
  Definition term_reflect
    (t: term Sort_Bool)
    (P : valuation -> Prop) : Prop :=
    forall ρ, term_satisfied_by ρ t <-> P ρ.

  Definition smt_reflect (q: query) (P : valuation -> Prop): Prop :=
    forall ρ, ρ ⊧ q <-> P ρ.

  Global Typeclasses Transparent term_reflect.

  Global Instance term_reflect_proper :
    Proper
      (eq ==> pointwise_relation valuation iff ==> iff)
      term_reflect.
  Proof.
    unfold
      pointwise_relation,
      term_reflect.
    repeat intro.
    setoid_rewrite H.
    setoid_rewrite H0.
    reflexivity.
  Qed.
  
  Global Instance smt_reflect_proper :
    Proper
      (eq ==> pointwise_relation valuation iff ==> iff)
      smt_reflect.
  Proof.
    unfold pointwise_relation, smt_reflect.
    repeat intro.
    setoid_rewrite H.
    setoid_rewrite H0.
    reflexivity.
  Qed.
  
  Lemma term_reflect_iff t P1 P2 :
    (pointwise_relation _ iff P1 P2) ->
    term_reflect t P1 ->
    term_reflect t P2.
  Proof.
    intros H Hreflect.
    setoid_rewrite <- H.
    assumption.
  Qed.
  
  Lemma term_reflect_and q1 q2 P1 P2 :
    term_reflect q1 P1 ->
    term_reflect q2 P2 ->
    term_reflect (SMTLib.Term_And q1 q2) (fun ρ => P1 ρ /\ P2 ρ).
  Proof.
    unfold term_reflect, term_satisfied_by.
    intros Hrefl1 Hrefl2.
    simpl.
    intros ρ.
    split; intros * H.
    - rewrite <- Hrefl1 by trivial.
      rewrite <- Hrefl2 by trivial.
      generalize dependent (interp_term ρ q1); intro b1; intros.
      generalize dependent (interp_term ρ q2); intro b2; intros.
      now repeat Bool.destr_bool.
    - setoid_rewrite <- Hrefl1 in H; trivial; [].
      setoid_rewrite <- Hrefl2 in H; trivial; [].
      destruct H as [H1 H2].
      rewrite H1, H2.
      reflexivity.
  Qed.
  
  Lemma term_reflect_or q1 q2 P1 P2 :
    term_reflect q1 P1 ->
    term_reflect q2 P2 ->
    term_reflect (SMTLib.Term_Or q1 q2) (fun ρ => P1 ρ \/ P2 ρ).
  Proof.
    unfold term_reflect, term_reflect, term_satisfied_by.
    simpl.
    intros Hrefl1 Hrefl2 ρ.
    specialize (Hrefl1 ρ).
    specialize (Hrefl2 ρ).
    rewrite Bool.orb_true_iff.
    rewrite Hrefl1, Hrefl2.
    reflexivity.
  Qed.

  Lemma concat_conj :
    forall q1 q2 P1 P2,
      smt_reflect q1 P1 ->
      smt_reflect q2 P2 ->
      smt_reflect (combine q1 q2) (fun ρ => P1 ρ /\ P2 ρ).
  Proof.
    unfold smt_reflect, satisfied_by, combine.
    simpl.
    intros.
    setoid_rewrite List.Forall_app.
    firstorder.
  Qed.
  
  Lemma query_domain_app xs ys :
    query_domain (xs ++ ys) = query_domain xs ++ query_domain ys.
  Proof.
    unfold query_domain.
    now rewrite List.map_app, List.concat_app.
  Qed.
  
  Lemma query_domain_cons x xs :
    query_domain (x :: xs) = term_domain x ++ query_domain xs.
  Proof. reflexivity. Qed.
  
  Lemma add_assertion_reflect :
    forall t q P1 P2,
      term_reflect t P1 ->
      smt_reflect q P2 ->
      smt_reflect (add_assertion t q) (fun ρ => P1 ρ /\ P2 ρ).
  Proof.
    unfold smt_reflect, term_reflect, satisfied_by, combine.
    simpl.
    intros.
    setoid_rewrite List.Forall_cons_iff.
    firstorder.
  Qed.
  
  Lemma unsat_smt_reflect_false q :
    unsatisfiable q <-> smt_reflect q (fun _ => False).
  Proof.
    split; intros Hunsat ρ; specialize (Hunsat ρ); tauto.
  Qed.
  
  Lemma smt_reflect_rewrite : forall P2 P1 q,
      (forall ρ, P1 ρ <-> P2 ρ) ->
      (smt_reflect q P1 <-> smt_reflect q P2).
  Proof.
    unfold smt_reflect.
    intros * HP.
    split; intros.
    - rewrite <- HP; eauto.
    - rewrite HP; eauto.
  Qed.
  
  Lemma unsat_negation q P :
    smt_reflect q P ->
    unsatisfiable q ->
    (forall ρ, ~ P ρ).
  Proof.
    unfold smt_reflect, unsatisfiable.
    intros Hreflect Hunsat * contra.
    repeat match goal with
           | [ H : forall (_ : valuation), _ |- _ ] => specialize (H ρ)
           end.
    apply Hreflect in contra; trivial.
    contradiction.
  Qed.
  
  Lemma incompatible_reflect q1 q2 P1 P2 :
    smt_reflect q1 P1 ->
    smt_reflect q2 P2 ->
    (forall ρ, ~ satisfied_by ρ (combine q1 q2)) ->
    (forall ρ, ~ (P1 ρ /\ P2 ρ)).
  Proof.
    intros Hq1P1 Hq2P2 Hunsat.
    eapply unsat_negation.
    - eauto using concat_conj.
    - eauto.
  Qed.

End reflection.
