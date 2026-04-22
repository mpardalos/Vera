From Stdlib Require Import List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import BinNums.
From Stdlib Require Import ZArith.
From Stdlib Require Import Morphisms.

From vera Require Import Tactics.
From vera Require Import Common.
From vera Require Import SMTLib.
From vera Require Import Bitvector.

Import ListNotations.

Fixpoint term_domain {s} (t : term s) : list const_sym :=
  match t with
  | SMTLib.Term_Const _ sym => [sym]
  | SMTLib.Term_Eq l r => term_domain l ++ term_domain r
  | SMTLib.Term_And l r => term_domain l ++ term_domain r
  | SMTLib.Term_Or l r => term_domain l ++ term_domain r
  | SMTLib.Term_Not e => term_domain e
  | SMTLib.Term_ITE c t f => term_domain c ++ term_domain t ++ term_domain f
  | SMTLib.Term_True => []
  | SMTLib.Term_False => []
  | SMTLib.Term_BVLit _ _ => []
  | SMTLib.Term_BVConcat l r => term_domain l ++ term_domain r
  | SMTLib.Term_BVExtract _ _ _ e => term_domain e
  | SMTLib.Term_BVUnaryOp _ e => term_domain e
  | SMTLib.Term_BVBinOp _ l r => term_domain l ++ term_domain r
  | SMTLib.Term_BVUlt l r => term_domain l ++ term_domain r
  end
.

Definition lst_domain {s} (q : list (term s)) : list const_sym :=
  List.concat (List.map term_domain q).

Definition declaration := (nat * SMTLib.sort)%type.

Definition query := list (term (Sort_Bool)).

Definition domain (q : query) : list const_sym := lst_domain q.

Definition default_valuation : valuation := fun s _ =>
  match s with
  | Sort_Bool => false
  | Sort_BitVec w => BV.zeros w
  end
.

Definition term_satisfied_by (ρ: SMTLib.valuation) (t: SMTLib.term Sort_Bool) : Prop :=
  SMTLib.interp_term ρ t = true.

Definition satisfied_by (ρ: valuation) (q: query): Prop :=
  Forall (term_satisfied_by ρ) q.

(* Definition decl_term_satisfied_by (ρ: valuation) (t: decl_term) : Prop :=
 *   valuation_matches_decls ρ (dtDeclarations t) /\
 *     term_satisfied_by ρ (dtTerm t).
 * 
 * 
 * Lemma decl_term_app_wf t1 t2:
 *   Forall (fun n : nat => exists s : SMTLib.sort, In (n, s) (dtDeclarations t1 ++ dtDeclarations t2))
 *     (term_domain (dtTerm t1) ++ term_domain (dtTerm t2)).
 * Proof.
 *   destruct t1, t2. simpl.
 *   apply Forall_app.
 *   rewrite ! Forall_forall in *.
 *   split; intros.
 *   - edestruct dtWf0; eauto.
 *     eexists. apply List.in_app_iff.
 *     eauto.
 *   - edestruct dtWf1; eauto.
 *     eexists. apply List.in_app_iff.
 *     eauto.
 * Qed.
 * 
 * Definition not_decl_term (t : decl_term) : decl_term :=
 *   {|
 *     dtDeclarations := dtDeclarations t;
 *     dtTerm := SMTLib.Term_Not (dtTerm t);
 *     dtWf := dtWf t
 *   |}
 * .
 * 
 * Definition and_decl_term (t1 t2 : decl_term) : decl_term :=
 *   {|
 *     dtDeclarations := dtDeclarations t1 ++ dtDeclarations t2;
 *     dtTerm := SMTLib.Term_And (dtTerm t1) (dtTerm t2);
 *     dtWf := decl_term_app_wf t1 t2
 *   |}
 * .
 * 
 * Definition or_decl_term (t1 t2 : decl_term) : decl_term :=
 *   {|
 *     dtDeclarations := dtDeclarations t1 ++ dtDeclarations t2;
 *     dtTerm := SMTLib.Term_Or (dtTerm t1) (dtTerm t2);
 *     dtWf := decl_term_app_wf t1 t2
 *   |}
 * . *)

Definition term_reflect
  (t: term Sort_Bool)
  (P : valuation -> Prop) : Prop :=
  forall ρ, term_satisfied_by ρ t <-> P ρ.

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

Infix "⊧" := satisfied_by (at level 20).

Definition smt_reflect (q: query) (P : valuation -> Prop): Prop :=
  forall ρ, ρ ⊧ q <-> P ρ.

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

Definition combine (q1 q2: query) : query := q1 ++ q2.

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

Lemma lst_domain_app s xs ys :
  @lst_domain s (xs ++ ys) = lst_domain xs ++ lst_domain ys.
Proof.
  unfold lst_domain.
  now rewrite List.map_app, List.concat_app.
Qed.

Lemma lst_domain_cons s x xs :
  @lst_domain s (x :: xs) = term_domain x ++ lst_domain xs.
Proof. reflexivity. Qed.

Definition add_assertion (a : term Sort_Bool) (q : query) : query := a :: q.

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
  unfold smt_reflect, satisfied_by, combine, unsatisfiable, "⊧".
  intuition eauto; expect 1.
  rewrite <- H. eassumption.
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
