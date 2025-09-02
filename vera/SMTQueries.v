From Coq Require Import List.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.ProofIrrelevance.
From Coq Require Import BinNums.
From Coq Require Import ZArith.

From SMTCoqApi Require SMTLib.

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

Definition lst_domain (q : list SMTLib.term) : list SMTLib.const_sym := List.concat (List.map term_domain q).

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
  unfold smt_reflect, satisfied_by, combine.
  simpl.
  intros.
  setoid_rewrite List.Forall_app.
  firstorder.
Qed.

Lemma unsat_smt_reflect_false q :
  unsatisfiable q <-> smt_reflect q (fun _ => False).
Proof.
  unfold smt_reflect, satisfied_by, combine.
  simpl.
  intros.
  firstorder.
Qed.

Lemma smt_reflect_rewrite : forall P2 P1 q,
    (forall ρ, P1 ρ <-> P2 ρ) ->
    (smt_reflect q P1 <-> smt_reflect q P2).
Proof.
  unfold smt_reflect.
  intros * HP.
  split; intros Hsmt_reflect ρ.
  - rewrite <- HP.
    apply Hsmt_reflect.
  - rewrite HP.
    apply Hsmt_reflect.
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
  apply Hreflect in contra.
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
