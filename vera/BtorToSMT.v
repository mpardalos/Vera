From Stdlib Require Import BinNat.
From Stdlib Require Import ZArith.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.
From Stdlib Require Import Psatz.
From Stdlib Require Import List.
From Stdlib Require Import Basics.
From Stdlib Require Import Classical.
From Stdlib Require Import Morphisms.

From Equations Require Import Equations.

From ExtLib Require Import Programming.Show.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Data.Monads.OptionMonad.

From vera Require Import Common.
From vera Require Import Tactics.
From vera Require Import Decidable.
From vera Require Btor2.
Module ABtor2 := Btor2.Abstract.
From vera Require Import Bitvector.
From vera Require SMTLib.

Import ListNotations.
Import MonadLetNotation.
Import SigTNotations.
Import EqNotations.
Local Open Scope monad_scope.
Local Open Scope program_scope.

Coercion Npos : positive >-> N.

Implicit Types (env : Btor2.environment).

Arguments N.add _ _ : simpl never.
Arguments N.sub _ _ : simpl never.

Definition transfer_sort (s : Btor2.Sort.t) : SMTLib.sort :=
  match s with
  | Btor2.Sort.BitVec w => SMTLib.Sort_BitVec (Npos w)
  end.

Axiom undef_term : forall {s}, SMTLib.term (transfer_sort s).

Module Tag.
  Inductive tag := Current | Next.

  Definition t := tag.

  Definition tag_name (tag : t) (name : string) : string :=
    ((match tag with Current => "c" | Next => "n" end) ++ "__" ++ name)%string.

  Definition untag_name (name : string) : option (t * string) :=
    match name with
    | String "c" (String "_" (String "_" original)) => Some (Current, original)
    | String "n" (String "_" (String "_" original)) => Some (Next, original)
    | _ => None
    end.

  Lemma untag_tag_name t s : untag_name (tag_name t s) = Some (t, s).
  Proof. destruct t; reflexivity. Qed.

  Lemma tag_name_injective_tag t t' n n' :
    tag_name t n = tag_name t' n' -> t = t'.
  Proof.
    intros H.
    apply f_equal with (f := untag_name) in H.
    rewrite !untag_tag_name in H. congruence.
  Qed.

  Lemma tag_name_injective_name t t' n n' :
    tag_name t n = tag_name t' n' -> n = n'.
  Proof.
    intros H.
    apply f_equal with (f := untag_name) in H.
    rewrite !untag_tag_name in H. congruence.
  Qed.

  Lemma tag_untag_name t n n' :
    untag_name n = Some (t, n') -> tag_name t n' = n.
  Proof.
    unfold untag_name.
    intros H. autodestruct; reflexivity.
  Qed.

  Lemma tag_untag_name_none t n n' :
    untag_name n = None -> tag_name t n' <> n.
  Proof.
    intros H contra.
    apply f_equal with (f := untag_name) in contra.
    rewrite H, untag_tag_name in contra. discriminate.
  Qed.
End Tag.

Section transfer.
  Variable tag : Tag.t.

  Definition transfer_ref {env s} (r : Btor2.Ref.t s) : SMTLib.const_sym :=
    SMTLib.MkConstSym (Tag.tag_name tag (Btor2.Ref.refName r)) (transfer_sort s).

  #[program]
  Fixpoint transfer_expr {env s} (e : ABtor2.expr s) : SMTLib.term (transfer_sort s) :=
    match e in ABtor2.expr t return SMTLib.term (transfer_sort t) with
    | ABtor2.ExprRef r => SMTLib.Term_Const (transfer_ref r)
    | ABtor2.Constant bv => SMTLib.Term_BVLit _ bv
    | ABtor2.Eq lhs rhs => SMTLib.bool_to_bv (SMTLib.Term_Eq (transfer_expr lhs) (transfer_expr rhs))
    | ABtor2.NEq lhs rhs => SMTLib.bool_to_bv (SMTLib.Term_Not (SMTLib.Term_Eq (transfer_expr lhs) (transfer_expr rhs)))
    | ABtor2.Iff lhs rhs => SMTLib.bool_to_bv (SMTLib.Term_Eq (transfer_expr lhs) (transfer_expr rhs))
    | ABtor2.Implies lhs rhs => SMTLib.bool_to_bv (SMTLib.Term_Or (SMTLib.is_zero (transfer_expr lhs)) (SMTLib.is_one (transfer_expr rhs)))
    | ABtor2.UnsignedLt lhs rhs => SMTLib.bool_to_bv (SMTLib.Term_BVUlt (transfer_expr lhs) (transfer_expr rhs))
    | ABtor2.UnsignedGt lhs rhs => SMTLib.bool_to_bv (SMTLib.Term_BVUlt (transfer_expr rhs) (transfer_expr lhs))
    | ABtor2.UnsignedLtE lhs rhs => SMTLib.bool_to_bv (SMTLib.Term_Not (SMTLib.Term_BVUlt (transfer_expr rhs) (transfer_expr lhs)))
    | ABtor2.UnsignedGtE lhs rhs => SMTLib.bool_to_bv (SMTLib.Term_Not (SMTLib.Term_BVUlt (transfer_expr lhs) (transfer_expr rhs)))
    | ABtor2.Add lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVAdd (transfer_expr lhs) (transfer_expr rhs)
    | ABtor2.Sub lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVAdd
        (transfer_expr lhs) (SMTLib.Term_BVUnaryOp SMTLib.BVNeg (transfer_expr rhs))
    | ABtor2.Mul lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVMul (transfer_expr lhs) (transfer_expr rhs)
    | ABtor2.UnsignedDiv lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVUDiv (transfer_expr lhs) (transfer_expr rhs)
    | ABtor2.UnsignedRem lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVURem (transfer_expr lhs) (transfer_expr rhs)
    | ABtor2.And lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVAnd (transfer_expr lhs) (transfer_expr rhs)
    | ABtor2.Or lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVOr (transfer_expr lhs) (transfer_expr rhs)
    | ABtor2.XOr lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVXor (transfer_expr lhs) (transfer_expr rhs)
    | ABtor2.NAnd lhs rhs => SMTLib.Term_BVUnaryOp SMTLib.BVNot
        (SMTLib.Term_BVBinOp SMTLib.BVAnd (transfer_expr lhs) (transfer_expr rhs))
    | ABtor2.NOr lhs rhs => SMTLib.Term_BVUnaryOp SMTLib.BVNot
        (SMTLib.Term_BVBinOp SMTLib.BVOr (transfer_expr lhs) (transfer_expr rhs))
    | ABtor2.XNor lhs rhs => SMTLib.Term_BVUnaryOp SMTLib.BVNot
        (SMTLib.Term_BVBinOp SMTLib.BVXor (transfer_expr lhs) (transfer_expr rhs))
    | ABtor2.Sll lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVShl (transfer_expr lhs) (transfer_expr rhs)
    | ABtor2.Srl lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVShr (transfer_expr lhs) (transfer_expr rhs)
    | ABtor2.Concat lhs rhs => SMTLib.Term_BVConcat (transfer_expr lhs) (transfer_expr rhs)
    | ABtor2.ITE cond ifT ifF => SMTLib.Term_ITE
        (SMTLib.is_one (transfer_expr cond)) (transfer_expr ifT) (transfer_expr ifF)
    | ABtor2.Slice hi lo wf e =>
      rew [fun w => SMTLib.term (SMTLib.Sort_BitVec w)] _ in SMTLib.Term_BVExtract hi lo (proj1 wf) (transfer_expr e)
    | ABtor2.Neg e => SMTLib.Term_BVUnaryOp SMTLib.BVNeg (transfer_expr e)
    | ABtor2.Not e => SMTLib.Term_BVUnaryOp SMTLib.BVNot (transfer_expr e)
    | @ABtor2.Inc _ n e => SMTLib.Term_BVBinOp SMTLib.BVAdd
        (transfer_expr e) (SMTLib.Term_BVLit _ (BV.bv_neg (BV.ones n)))
    | @ABtor2.Dec _ n e => SMTLib.Term_BVBinOp SMTLib.BVAdd
        (transfer_expr e) (SMTLib.Term_BVLit _ (BV.ones n))
    | @ABtor2.RedAnd _ n e => SMTLib.bool_to_bv
        (SMTLib.Term_Eq (transfer_expr e) (SMTLib.Term_BVLit _ (BV.ones n)))
    | @ABtor2.RedOr _ n e => SMTLib.bool_to_bv
        (SMTLib.Term_Not (SMTLib.Term_Eq (transfer_expr e) (SMTLib.Term_BVLit _ (BV.zeros n))))
    | @ABtor2.UnsignedExtend _ m w e =>
        SMTLib.Term_BVConcat (SMTLib.Term_BVLit _ (BV.zeros (Npos w))) (transfer_expr e)
    (* These operations have no direct counterpart in the current SMT AST. *)
    | ABtor2.SignedExtend _ _ | ABtor2.RedXor _
    | ABtor2.SignedGt _ _ | ABtor2.SignedGtE _ _
    | ABtor2.SignedLt _ _ | ABtor2.SignedLtE _ _
    | ABtor2.Rol _ _ | ABtor2.Sra _ _
    | ABtor2.SignedDiv _ _
    | ABtor2.SignedMod _ _ | ABtor2.SignedRem _ _
    | ABtor2.SignedAddOverflow _ _ | ABtor2.UnsignedAddOverflow _ _
    | ABtor2.SignedDivOverflow _ _
    | ABtor2.SignedMulOverflow _ _ | ABtor2.UnsignedMulOverflow _ _
    | ABtor2.SignedSubOverflow _ _ | ABtor2.UnsignedSubOverflow _ _ => undef_term
    end.
  Next Obligation. lia. Qed.
  
  Definition transfer_combinational {env} (var : ABtor2.operatorVar) : SMTLib.term SMTLib.Sort_Bool :=
    SMTLib.Term_Eq
      (SMTLib.Term_Const (SMTLib.MkConstSym (Tag.tag_name tag (ABtor2.operatorName var)) (transfer_sort (ABtor2.operatorSort var))))
      (transfer_expr (ABtor2.operatorExpr var)).
  
  Definition transfer_prop {env} (prop : ABtor2.expr (Btor2.Sort.BitVec 1)) : SMTLib.term SMTLib.Sort_Bool :=
    SMTLib.is_zero (transfer_expr prop).

  Definition transfer_props_hold {env} (props : list (ABtor2.expr (Btor2.Sort.BitVec 1))) : SMTLib.query :=
    map transfer_prop props.

  Definition transfer_props_violated {env} (props : list (ABtor2.expr (Btor2.Sort.BitVec 1))) : SMTLib.query :=
    [ SMTLib.Term_Not (SMTLib.and_all (map transfer_prop props)) ].
End transfer.

Section induction.
  Definition transfer_state_init {env} (var : ABtor2.stateVar) : SMTLib.term SMTLib.Sort_Bool :=
    SMTLib.Term_Eq
      (SMTLib.Term_Const (transfer_ref Tag.Current (ABtor2.stateRef var)))
      (transfer_expr Tag.Current (ABtor2.stateInit var)).

  Definition transfer_state_next {env} (var : ABtor2.stateVar) : SMTLib.term SMTLib.Sort_Bool :=
    SMTLib.Term_Eq
      (SMTLib.Term_Const (transfer_ref Tag.Next (ABtor2.stateRef var)))
      (transfer_expr Tag.Current (ABtor2.stateNext var)).

  (* Look for a bad permitted initial state *)
  Definition query_init_state_bad (b : ABtor2.btor) : SMTLib.query :=
    map transfer_state_init (ABtor2.btorStates b) ++
    map (transfer_combinational Tag.Current) (ABtor2.btorOperators b) ++
    transfer_props_violated Tag.Current (ABtor2.btorProperties b) .

  (* Look for a transition from a good state to a bad state *)
  Definition query_inductive_violation (b : ABtor2.btor) : SMTLib.query :=
    map (transfer_combinational Tag.Current) (ABtor2.btorOperators b) ++
    map (transfer_combinational Tag.Next) (ABtor2.btorOperators b) ++
    map transfer_state_next (ABtor2.btorStates b) ++
    transfer_props_hold Tag.Current (ABtor2.btorProperties b) ++
    transfer_props_violated Tag.Next (ABtor2.btorProperties b).
End induction.

Section prepare_certificate.
  Variable (original : Btor2.Abstract.btor).
  Variable (certificate : Btor2.Raw.btor).

  Let original_states : list string :=
    map Btor2.Abstract.stateName (Btor2.Abstract.btorStates original).

  Let certificate_states : list string :=
    map_opt
      (fun n =>
        match n with
        | Btor2.Raw.StateDecl n s => Some n
        | _ => None
        end)
      certificate.

  (* Name in original * Name in miter *)
  Let matched : list (string * string) :=
    List.combine original_states certificate_states.

  Let cert_rename (n : Btor2.name) : Btor2.name :=
    match find (fun '(_, n') => String.eqb n n') matched with
    | Some (orig_name, _) => orig_name
    (* TODO: Ensure that this doesn't cause unintended conflicts*)
    | None => ("cert__" ++ n)%string
    end.

  Definition prepare_certificate : result Btor2.Abstract.btor :=
    Btor2.Raw.to_abstract (Btor2.Raw.rename cert_rename certificate). 
End prepare_certificate.

Section miter.
  Variable (original : Btor2.Abstract.btor).

  (* Matched names with original where needed *)
  Variable (certificate : Btor2.Abstract.btor).

  Let orig_combinational tag := map (transfer_combinational tag) (ABtor2.btorOperators original).
  Let orig_reset := map transfer_state_init (ABtor2.btorStates original).
  Let orig_transition := map transfer_state_next (ABtor2.btorStates original).
  Let orig_property_holds tag := transfer_props_hold tag (ABtor2.btorProperties original).
  Let orig_property_violated tag := transfer_props_violated tag (ABtor2.btorProperties original).

  Let cert_combinational tag := map (transfer_combinational tag) (ABtor2.btorOperators certificate).
  Let cert_reset := map transfer_state_init (ABtor2.btorStates certificate).
  Let cert_transition := map transfer_state_next (ABtor2.btorStates certificate).
  Let cert_property_holds tag := transfer_props_hold tag (ABtor2.btorProperties certificate).
  Let cert_property_violated tag := transfer_props_violated tag (ABtor2.btorProperties certificate).

  Definition query_refines_property :=
    orig_combinational Tag.Current ++
    cert_combinational Tag.Current ++
    orig_property_holds Tag.Current ++
    cert_property_violated Tag.Current.

  Definition query_refines_reset :=
    orig_combinational Tag.Current ++
    cert_combinational Tag.Current ++
    orig_reset ++
    [ SMTLib.Term_Not (SMTLib.and_all cert_reset) ].

  Definition query_refines_transition :=
    orig_combinational Tag.Current ++
    orig_combinational Tag.Next ++
    orig_transition ++
    cert_combinational Tag.Current ++
    cert_combinational Tag.Next ++
    [ SMTLib.Term_Not (SMTLib.and_all cert_transition) ].
End miter.

Record certificate_check_queries := {
  certificate_basecase : SMTLib.query;
  certificate_induction : SMTLib.query;
  refinement_properties : SMTLib.query;
  refinement_reset : SMTLib.query;
  refinement_transition : SMTLib.query;
}.

Definition get_certificate_check_queries (original certificate : Btor2.Raw.btor) : result certificate_check_queries :=
  let* original' := Btor2.Raw.to_abstract original in
  let* certificate' := prepare_certificate original' certificate in
  ret {|
    certificate_basecase := query_init_state_bad certificate';
    certificate_induction := query_init_state_bad certificate';
    refinement_properties := query_refines_property original' certificate';
    refinement_reset := query_refines_reset original' certificate';
    refinement_transition := query_refines_transition original' certificate';
  |}.

Section correctness.
  Import Btor2.
  Import Btor2.Abstract.
  Import SMTLib (unsatisfiable, satisfiable, satisfied_by, term_reflect, term_satisfied_by).

  Definition state_of_valuation {env} (t : Tag.t) (ρ : SMTLib.valuation) : State.t := fun s r =>
    match s with
    | Sort.BitVec n => ρ (SMTLib.MkConstSym (Tag.tag_name t (Btor2.Ref.refName r)) (SMTLib.Sort_BitVec n))
    end.

  (* Variable valuation_of_state : forall {env}, State.t -> SMTLib.valuation.
   * Axiom valuation_of_state_of_valuation : forall {env} ρ, valuation_of_state (state_of_valuation ρ) = ρ.
   * Axiom state_of_valuation_of_state : forall {env} st, state_of_valuation (valuation_of_state st) = st. *)

  (* Lemma map transfer_state_init (ABtor2.btorStates b) ++
   *    map (transfer_combinational names_current) (ABtor2.btorOperators b) *)

  Theorem transfer_expr_correct env tg ρ n (e : expr (Sort.BitVec n)) :
    (* TODO: state/valuation relation *)
    @SMTLib.interp_term ρ (SMTLib.Sort_BitVec n) (transfer_expr tg e) = eval (state_of_valuation tg ρ) e.
  Proof. Admitted.

  Ltac simpl_reflect :=
    repeat first
      [ apply (proj2 (SMTLib.smt_reflect_singleton _ _))
      | apply SMTLib.term_reflect_not
      | apply (proj2 (SMTLib.and_all_as_smt_reflect _ _))
      | apply SMTLib.smt_reflect_map
      | apply SMTLib.smt_reflect_concat
      ].

  Lemma transfer_combinational_spec env tg var :
    SMTLib.term_reflect
      (transfer_combinational tg var)
      (fun ρ => state_of_valuation tg ρ _ (operatorRef var) = eval (state_of_valuation tg ρ) (operatorExpr var)).
  Proof.
    unfold transfer_state_init.
    eapply SMTLib.term_reflect_proper; [reflexivity|idtac|solve [apply SMTLib.term_reflect_eq]].
    intros ρ. destruct var. destruct operatorSort0.
    setoid_rewrite transfer_expr_correct.
    unfold state_of_valuation, transfer_ref. simpl.
    reflexivity.
  Qed.

  Lemma transfer_prop_spec env tg prop:
    SMTLib.term_reflect
      (transfer_prop tg prop)
      (fun ρ => eval (state_of_valuation tg ρ) prop = BV.zeros 1).
  Proof.
    unfold transfer_prop.
    setoid_rewrite <- transfer_expr_correct with (tg := tg).
    eapply SMTLib.term_reflect_is_zero.
  Qed.

  Lemma transfer_props_hold_spec env tg props :
    SMTLib.smt_reflect
      (transfer_props_hold tg props)
      (fun ρ => Forall (fun (e : expr (Sort.BitVec 1)) => eval (state_of_valuation tg ρ) e = BV.zeros 1) props).
  Proof. simpl_reflect. apply transfer_prop_spec. Qed.

  Lemma transfer_props_violated_spec env tg props :
    SMTLib.smt_reflect
      (transfer_props_violated tg props)
      (fun ρ => ~ Forall (fun (e : expr (Sort.BitVec 1)) => eval (state_of_valuation tg ρ) e = BV.zeros 1) props).
  Proof. simpl_reflect. apply transfer_prop_spec. Qed.

  Lemma transfer_state_init_spec env var :
    SMTLib.term_reflect
      (transfer_state_init var)
      (fun ρ => let st := state_of_valuation Tag.Current ρ in
        st _ (stateRef var) = eval st (stateInit var)).
  Proof.
    unfold transfer_state_init.
    eapply SMTLib.term_reflect_proper; [reflexivity|idtac|solve [apply SMTLib.term_reflect_eq]].
    intros ρ. destruct var. destruct stateSort0.
    setoid_rewrite transfer_expr_correct.
    unfold state_of_valuation, transfer_ref. simpl.
    reflexivity.
  Qed.

  Lemma transfer_state_next_spec env var :
    SMTLib.term_reflect
      (transfer_state_next var)
      (fun ρ => let st t := state_of_valuation t ρ in
        st Tag.Next _ (stateRef var) = eval (st Tag.Current) (stateNext var)).
  Proof.
    unfold transfer_state_next.
    eapply SMTLib.term_reflect_proper; [reflexivity|idtac|solve [apply SMTLib.term_reflect_eq]].
    intros ρ. destruct var. destruct stateSort0.
    setoid_rewrite transfer_expr_correct.
    unfold state_of_valuation, transfer_ref. simpl.
    reflexivity.
  Qed.

  Lemma query_init_state_bad_spec b :
    SMTLib.smt_reflect
      (query_init_state_bad b)
      (fun ρ =>
        let st := state_of_valuation Tag.Current ρ in
        is_initial b st /\ is_valid b st /\ ~ is_safe b st
      ).
  Proof.
    simpl_reflect; expect 3.
    - apply transfer_state_init_spec.
    - apply transfer_combinational_spec.
    - apply transfer_prop_spec.
  Qed.

  Lemma not_and_or_iff P Q : ~ (P /\ Q) <-> (~ P \/ ~ Q).
  Proof. split. { apply not_and_or. } { apply or_not_and. } Qed.

  Lemma NNPP_iff P : ~ ~ P <-> P.
  Proof. split. { apply NNPP. } { firstorder. } Qed.

  Lemma imply_or_iff P Q : (~ P \/ Q) <-> (P -> Q).
  Proof. split. { apply or_to_imply. } { apply imply_to_or. } Qed.

  Hint Rewrite not_and_or_iff NNPP_iff imply_or_iff : classicalize.

  Lemma query_init_state_bad_unsat b :
    SMTLib.unsatisfiable (query_init_state_bad b) ->
    forall ρ,
      let st := state_of_valuation Tag.Current ρ in
      is_initial b st -> is_valid b st -> is_safe b st.
  Proof.
    simpl.
    intros Hunsat ρ Hinitial Hvalid.
    specialize (Hunsat ρ).
    pose proof (query_init_state_bad_spec b).
    unfold SMTLib.smt_reflect in H. rewrite H in Hunsat. clear H.
    autorewrite with classicalize in Hunsat.
    auto.
  Qed.

  Lemma query_inductive_violation_spec b :
    SMTLib.smt_reflect
      (query_inductive_violation b)
      (fun ρ =>
        let st t := state_of_valuation t ρ in
        is_valid b (st Tag.Current)
        /\ is_valid b (st Tag.Next)
        /\ is_next b (st Tag.Current) (st Tag.Next)
        /\ is_safe b (st Tag.Current)
        /\ ~ is_safe b (st Tag.Next)
      ).
  Proof.
    simpl_reflect; expect 5.
    - apply transfer_combinational_spec.
    - apply transfer_combinational_spec.
    - apply transfer_state_next_spec.
    - apply transfer_prop_spec.
    - apply transfer_prop_spec.
  Qed.

  Lemma query_refines_property_spec b1 b2 :
    SMTLib.smt_reflect
      (query_refines_property b1 b2)
      (fun ρ =>
        (* These will be the same, restricted to their own envs *)
        let st1 := state_of_valuation Tag.Current ρ in
        let st2 := state_of_valuation Tag.Current ρ in
        is_valid b1 st1
        /\ is_valid b2 st2
        /\ is_safe b1 st1
        /\ ~ is_safe b2 st2
      ).
  Proof.
    simpl_reflect; expect 4.
    - apply transfer_combinational_spec.
    - apply transfer_combinational_spec.
    - apply transfer_prop_spec.
    - apply transfer_prop_spec.
  Qed.

  Lemma query_refines_reset_spec b1 b2 :
    SMTLib.smt_reflect
      (query_refines_reset b1 b2)
      (fun ρ =>
        (* These will be the same, restricted to their own envs *)
        let st1 := state_of_valuation Tag.Current ρ in
        let st2 := state_of_valuation Tag.Current ρ in
        is_valid b1 st1
        /\ is_valid b2 st2
        /\ is_initial b1 st1
        /\ ~ is_initial b2 st2
      ).
  Proof.
    simpl_reflect; expect 4.
    - apply transfer_combinational_spec.
    - apply transfer_combinational_spec.
    - apply transfer_state_init_spec.
    - apply transfer_state_init_spec.
  Qed.

  Lemma query_refines_transition_spec b1 b2 :
    SMTLib.smt_reflect
      (query_refines_transition b1 b2)
      (fun ρ =>
        (* These will be the same, restricted to their own envs *)
        let st1 t := state_of_valuation t ρ in
        let st2 t := state_of_valuation t ρ in
        is_valid b1 (st1 Tag.Current)
        /\ is_valid b1 (st1 Tag.Next)
        /\ is_next b1 (st1 Tag.Current) (st1 Tag.Next)
        /\ is_valid b2 (st2 Tag.Current)
        /\ is_valid b2 (st2 Tag.Next)
        /\ ~ is_next b2 (st2 Tag.Current) (st2 Tag.Next)
      ).
  Proof.
    simpl_reflect; expect 6.
    - apply transfer_combinational_spec.
    - apply transfer_combinational_spec.
    - apply transfer_state_next_spec.
    - apply transfer_combinational_spec.
    - apply transfer_combinational_spec.
    - apply transfer_state_next_spec.
  Qed.
End correctness.
