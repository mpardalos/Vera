From Stdlib Require Import List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import BinNums.
From Stdlib Require Import ZArith.
From Stdlib Require Import Morphisms.

From vera Require Import Tactics.
From vera Require Import Common.
From vera Require SMTLib.

Import ListNotations.

Fixpoint term_domain (t : SMTLib.term) : list SMTLib.const_sym :=
  match t with
  | SMTLib.Term_Const sym => [sym]
  | SMTLib.Term_Int _ => []
  | SMTLib.Term_Geq l r => term_domain l ++ term_domain r
  | SMTLib.Term_Eq l r => term_domain l ++ term_domain r
  | SMTLib.Term_And l r => term_domain l ++ term_domain r
  | SMTLib.Term_Or l r => term_domain l ++ term_domain r
  | SMTLib.Term_Not e => term_domain e
  | SMTLib.Term_ITE c t f => term_domain c ++ term_domain t ++ term_domain f
  | SMTLib.Term_True => []
  | SMTLib.Term_False => []
  | SMTLib.Term_BVLit _ _ => []
  | SMTLib.Term_BVConcat l r => term_domain l ++ term_domain r
  | SMTLib.Term_BVExtract _ _ e => term_domain e
  | SMTLib.Term_BVUnaryOp _ e => term_domain e
  | SMTLib.Term_BVBinOp _ l r => term_domain l ++ term_domain r
  | SMTLib.Term_BVUlt l r => term_domain l ++ term_domain r
  end
.

Definition lst_domain (q : list SMTLib.term) : list SMTLib.const_sym :=
  List.concat (List.map term_domain q).

Definition declaration := (nat * SMTLib.sort)%type.

Record query :=
  MkQuery
    {
      declarations : list declaration;
      assertions : list SMTLib.term;
      (* All constants used have been declared *)
      wf : Forall
             (fun n => exists s, In (n, s) declarations)
             (lst_domain assertions)
    }.

Record decl_term :=
  MkDeclTerm
    {
      dtDeclarations : list declaration;
      dtTerm : SMTLib.term;
      (* All constants used have been declared *)
      dtWf : Forall
             (fun n => exists s, In (n, s) dtDeclarations)
             (term_domain dtTerm)
    }.

Definition domain (q : query) : list SMTLib.const_sym := lst_domain (assertions q).

Definition valuation := nat -> option SMTLib.value.

Definition valuation_set_fun (ρ : valuation) (n : nat) (v : SMTLib.value) : valuation :=
  fun n' => if n =? n' then Some v else ρ n.

Hint Unfold valuation_set_fun : core.

Definition default_valuation : valuation := fun _ => None.

Inductive value_has_sort : SMTLib.value -> SMTLib.sort -> Prop :=
| value_has_sort_Bool b : value_has_sort (SMTLib.Value_Bool b) SMTLib.Sort_Bool
| value_has_sort_Int i : value_has_sort (SMTLib.Value_Int i) SMTLib.Sort_Int
| value_has_sort_BitVec w bv : value_has_sort (SMTLib.Value_BitVec w bv) (SMTLib.Sort_BitVec w)
.

Definition valuation_matches_decls (ρ: valuation) (ds: list declaration) : Prop :=
  Forall (fun '(n, s) => exists v, ρ n = Some v /\ value_has_sort v s) ds.

Definition term_satisfied_by (ρ: valuation) (t: SMTLib.term) : Prop :=
    SMTLib.interp_term ρ t = Some (SMTLib.Value_Bool true).

Definition decl_term_satisfied_by (ρ: valuation) (t: decl_term) : Prop :=
  valuation_matches_decls ρ (dtDeclarations t) /\
    term_satisfied_by ρ (dtTerm t).

Definition satisfied_by (ρ: valuation) (q: query): Prop :=
  valuation_matches_decls ρ (declarations q) /\
    Forall (term_satisfied_by ρ) (assertions q).

Lemma decl_term_app_wf t1 t2:
  Forall (fun n : nat => exists s : SMTLib.sort, In (n, s) (dtDeclarations t1 ++ dtDeclarations t2))
    (term_domain (dtTerm t1) ++ term_domain (dtTerm t2)).
Proof.
  destruct t1, t2. simpl.
  apply Forall_app.
  rewrite ! Forall_forall in *.
  split; intros.
  - edestruct dtWf0; eauto.
    eexists. apply List.in_app_iff.
    eauto.
  - edestruct dtWf1; eauto.
    eexists. apply List.in_app_iff.
    eauto.
Qed.

Definition not_decl_term (t : decl_term) : decl_term :=
  {|
    dtDeclarations := dtDeclarations t;
    dtTerm := SMTLib.Term_Not (dtTerm t);
    dtWf := dtWf t
  |}
.

Definition and_decl_term (t1 t2 : decl_term) : decl_term :=
  {|
    dtDeclarations := dtDeclarations t1 ++ dtDeclarations t2;
    dtTerm := SMTLib.Term_And (dtTerm t1) (dtTerm t2);
    dtWf := decl_term_app_wf t1 t2
  |}
.

Definition or_decl_term (t1 t2 : decl_term) : decl_term :=
  {|
    dtDeclarations := dtDeclarations t1 ++ dtDeclarations t2;
    dtTerm := SMTLib.Term_Or (dtTerm t1) (dtTerm t2);
    dtWf := decl_term_app_wf t1 t2
  |}
.

Definition term_reflect_if
  (C : valuation -> Prop)
  (t: SMTLib.term)
  (P : valuation -> Prop) : Prop :=
  forall ρ, C ρ -> term_satisfied_by ρ t <-> P ρ.

Definition term_reflect := term_reflect_if (fun _ => True).

Global Typeclasses Transparent term_reflect.

Global Instance term_reflect_if_proper :
  Proper
    (pointwise_relation valuation iff ==> eq ==> pointwise_relation valuation iff ==> iff)
    term_reflect_if.
Proof.
  unfold
    pointwise_relation,
    term_reflect_if.
  repeat intro.
  setoid_rewrite H.
  setoid_rewrite H0.
  setoid_rewrite H1.
  reflexivity.
Qed.

Lemma term_reflect_if_elim C t P :
  term_reflect_if C t P ->
  (forall ρ, P ρ -> C ρ) ->
  (forall ρ, term_satisfied_by ρ t -> C ρ) ->
  term_reflect t P.
Proof. unfold term_reflect_if. firstorder. Qed.

Lemma term_reflect_if_intro C t P :
  term_reflect t P ->
  term_reflect_if C t P.
Proof. unfold term_reflect_if. firstorder. Qed.

Lemma term_reflect_iff t C P1 P2 :
  (pointwise_relation _ iff P1 P2) ->
  term_reflect_if C t P1 ->
  term_reflect_if C t P2.
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
  unfold term_reflect, term_reflect_if, term_satisfied_by.
  intros Hrefl1 Hrefl2.
  simpl.
  intros ρ _.
  split; intros * H.
  - autodestruct_eqn E.
    Bool.destr_bool.
    crush.
  - setoid_rewrite <- Hrefl1 in H; trivial; [].
    setoid_rewrite <- Hrefl2 in H; trivial; [].
    destruct H as [H1 H2].
    rewrite H1, H2.
    reflexivity.
Qed.

Lemma term_reflect_or C1 C2 q1 q2 P1 P2 :
  term_reflect_if C1 q1 P1 ->
  term_reflect_if C2 q2 P2 ->
  term_reflect_if
    (fun ρ =>
       (exists b, SMTLib.interp_term ρ q1 = Some (SMTLib.Value_Bool b))
       /\ (exists b, SMTLib.interp_term ρ q2 = Some (SMTLib.Value_Bool b))
       /\ C1 ρ
       /\ C2 ρ
    )
    (SMTLib.Term_Or q1 q2)
    (fun ρ => P1 ρ \/ P2 ρ).
Proof.
  unfold term_reflect, term_reflect_if, term_satisfied_by.
  simpl.
  intros Hrefl1 Hrefl2 ρ [[b1 Hb1] [[b2 Hb2] [HC1 HC2]]].
  specialize (Hrefl1 ρ ltac:(trivial)).
  specialize (Hrefl2 ρ ltac:(trivial)).
  rewrite Hb1, Hb2 in *. clear Hb1 Hb2.
  split; intros * H.
  - inv H.
    Bool.destr_bool; crush.
  - setoid_rewrite <- Hrefl1 in H; trivial; [].
    setoid_rewrite <- Hrefl2 in H; trivial; [].
    destruct H as [H|H];
      inv H;
      Bool.destr_bool.
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

Definition smt_reflect_if (C: valuation -> Prop) (q: query) (P : valuation -> Prop): Prop :=
  forall ρ, C ρ -> ρ ⊧ q <-> P ρ.

Definition smt_reflect := smt_reflect_if (fun _ => True).

Global Instance smt_reflect_if_proper :
  Proper
    (pointwise_relation valuation iff ==> eq ==> pointwise_relation valuation iff ==> iff)
    smt_reflect_if.
Proof.
  unfold
    pointwise_relation,
    smt_reflect_if.
  repeat intro.
  setoid_rewrite H.
  setoid_rewrite H0.
  setoid_rewrite H1.
  reflexivity.
Qed.

Global Instance smt_reflect_proper :
  Proper
    (eq ==> pointwise_relation valuation iff ==> iff)
    smt_reflect.
Proof. unfold smt_reflect. typeclasses eauto. Qed.

Lemma smt_reflect_if_elim C t P :
  smt_reflect_if C t P ->
  (forall ρ, P ρ -> C ρ) ->
  (forall ρ, satisfied_by ρ t -> C ρ) ->
  smt_reflect t P.
Proof. unfold smt_reflect_if. firstorder. Qed.

Lemma smt_reflect_if_intro C t P :
  smt_reflect t P ->
  smt_reflect_if C t P.
Proof. unfold smt_reflect_if. firstorder. Qed.

Lemma combine_wf q1 q2 :
  List.Forall
    (fun n : nat => exists s : SMTLib.sort, List.In (n, s) (declarations q1 ++ declarations q2))
    (lst_domain (assertions q1 ++ assertions q2)).
Proof.
  destruct q1, q2.
  unfold lst_domain in *.
  rewrite ! List.Forall_forall in *.
  simpl in *.
  rewrite List.Forall_forall in *.
  intros n H.
  rewrite
    <- List.flat_map_concat_map,
    List.flat_map_app,
    List.in_app_iff
    in *.
  setoid_rewrite List.in_app_iff.
  destruct H.
  - edestruct wf0 as [n' Hwf]; eauto.
  - edestruct wf1 as [n' Hwf]; eauto.
Qed.

Definition combine (q1 q2: query) : query :=
  {|
    declarations := declarations q1 ++ declarations q2;
    assertions := assertions q1 ++ assertions q2;
    wf := combine_wf q1 q2
  |}.

Lemma concat_conj :
  forall q1 q2 P1 P2,
    smt_reflect q1 P1 ->
    smt_reflect q2 P2 ->
    smt_reflect (combine q1 q2) (fun ρ => P1 ρ /\ P2 ρ).
Proof.
  destruct q1, q2.
  unfold smt_reflect, smt_reflect_if, satisfied_by, combine.
  simpl.
  intros.
  setoid_rewrite List.Forall_app.
  firstorder.
Qed.

Lemma lst_domain_app xs ys :
  lst_domain (xs ++ ys) = lst_domain xs ++ lst_domain ys.
Proof.
  unfold lst_domain.
  now rewrite List.map_app, List.concat_app.
Qed.

Lemma lst_domain_cons x xs :
  lst_domain (x :: xs) = term_domain x ++ lst_domain xs.
Proof. reflexivity. Qed.

Program Definition add_assertion
  (a : SMTLib.term)
  (q : query)
  (domain_wf : list_subset (term_domain a) (domain q))
  : query :=
  {|
    assertions := a :: assertions q;
    declarations := declarations q
  |}.
Next Obligation.
  simpl.
  rewrite lst_domain_cons.
  unfold list_subset in domain_wf.
  rewrite List.Forall_app in *.
  destruct q. cbn in *.
  rewrite ! List.Forall_forall in *.
  firstorder.
Qed.

Lemma add_assertion_reflect_if :
  forall t q C P1 P2 domain_wf,
    term_reflect_if C t P1 ->
    smt_reflect_if C q P2 ->
    smt_reflect_if C (add_assertion t q domain_wf) (fun ρ => P1 ρ /\ P2 ρ).
Proof.
  destruct q.
  unfold smt_reflect, smt_reflect_if, term_reflect, satisfied_by, combine.
  simpl.
  intros.
  setoid_rewrite List.Forall_cons_iff.
  firstorder.
Qed.

Lemma add_assertion_reflect :
  forall t q P1 P2 domain_wf,
    term_reflect t P1 ->
    smt_reflect q P2 ->
    smt_reflect (add_assertion t q domain_wf) (fun ρ => P1 ρ /\ P2 ρ).
Proof. intros. apply add_assertion_reflect_if; eassumption. Qed.

Lemma unsat_smt_reflect_false q :
  unsatisfiable q <-> smt_reflect q (fun _ => False).
Proof.
  unfold smt_reflect, satisfied_by, combine.
  simpl.
  intros.
  firstorder.
Qed.

Lemma smt_reflect_if_rewrite : forall C P2 P1 q,
    (forall ρ, C ρ -> P1 ρ <-> P2 ρ) ->
    (smt_reflect_if C q P1 <-> smt_reflect_if C q P2).
Proof.
  unfold smt_reflect, smt_reflect_if.
  intros * HP.
  split; intros.
  - rewrite <- HP; eauto.
  - rewrite HP; eauto.
Qed.

Lemma smt_reflect_rewrite : forall P2 P1 q,
    (forall ρ, P1 ρ <-> P2 ρ) ->
    (smt_reflect q P1 <-> smt_reflect q P2).
Proof. intros. eapply smt_reflect_if_rewrite. eauto. Qed.

Lemma unsat_negation q P :
  smt_reflect q P ->
  unsatisfiable q ->
  (forall ρ, ~ P ρ).
Proof.
  unfold smt_reflect, smt_reflect_if, unsatisfiable.
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
