From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import ProofIrrelevance.
From Stdlib Require Import Basics.
From Stdlib Require Extraction.
From Stdlib Require Streams.
Import Streams (Stream).
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Relations.Operators_Properties.
(* From Stdlib Require Import BinNums. *)
(* From Stdlib Require Import Program.Equality. *)
(* From Stdlib Require Import ProofIrrelevance. *)
(* From Stdlib Require Import Structures.Orders. *)
(* From Stdlib Require Import Structures.OrdersEx. *)
(* From Stdlib Require Import Structures.OrdersAlt. *)
(* From Stdlib Require Import RelationPairs. *)
(* From Stdlib Require MSets. *)
(* From Stdlib Require Import FMapAVL. *)
(* From Stdlib Require Import FMapFacts. *)
(* From Stdlib Require Import MSetInterface. *)

(* From ExtLib Require Import Programming.Show. *)
From ExtLib Require Import Data.Monads.EitherMonad.
From ExtLib Require Import Data.Monads.StateMonad.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.MonadState.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Data.List.

From vera Require Import Common.
From vera Require Import Tactics.
From vera Require Import Bitvector.
From vera Require Import Decidable.
(* Import (notations) Bitvector.RawBV. *)
(* From vera Require Import Variables. *)

(* From Stdlib Require Import List. *)
(* From Stdlib Require Arith Lia Program. *)
From Stdlib Require Import Structures.Equalities.
(* From Stdlib Require Arith.PeanoNat. *)
From Equations Require Import Equations.

Import ListNotations.
Import MonadLetNotation.
Import SigTNotations.
Import EqNotations.
Local Open Scope monad_scope.
Local Open Scope program_scope.

Module Sort <: UsualDecidableType.
  Inductive sort :=
  | BitVec (n : positive)
  (* | Array (idx elem : sort) *)
  .
  Definition t := sort.
  Include HasUsualEq <+ UsualIsEq.

  Definition eq_dec (x y : t) : {x = y} + {x <> y}.
  Proof. decide equality; apply Pos.eq_dec. Defined.

  #[global]
  Instance dec_eq_sort (x y : t) : DecProp (x = y) :=
    mk_dec_eq(eq_dec).

  Definition interp (s : sort) : Type :=
  match s with
  | BitVec n => BV.bitvector (Npos n)
  (* | Array idx elem => interp idx -> interp elem *)
  end.
End Sort.

Import Sort (BitVec(* , Array *)).

Definition name := string.

Module NameSet := StrSet.

Definition environment := name -> option Sort.t.

Coercion Npos : positive >-> N.

Implicit Types (env : environment).
Existing Class environment.

Module Ref.
  Record ref {env} {s : Sort.t} := Mk {
    refName : name;
    refWf : env refName = Some s
  }.
  Arguments ref {_} _.

  Definition t {env} := ref.

  Definition eqb {env s} (r1 r2 : ref s) : bool := String.eqb r1.(refName) r2.(refName).

  Definition heqb {env s1 s2} (r1 : ref s1) (r2 : ref s2) : bool :=
    if Sort.eq_dec s1 s2 then String.eqb r1.(refName) r2.(refName) else false.

  Lemma eqb_refl {env s} (r : ref s) : eqb r r = true.
  Proof. destruct r. apply String.eqb_refl. Qed.

  Lemma eqb_eq {env s} (r1 r2 : ref s) :
    eqb r1 r2 = true <-> r1 = r2.
  Proof.
    unfold eqb.
    destruct r1, r2. simpl.
    rewrite String.eqb_eq.
    split; intros H.
    - subst. f_equal. apply proof_irrelevance.
    - inversion H. reflexivity.
  Qed.
End Ref.

Module Abstract.
  Inductive expr {env} : Sort.t -> Type :=
  | UnsignedExtend {n : positive} (w : positive) (e : expr (BitVec n)) : expr (BitVec (w + n))
  | SignedExtend {n : positive} (w : positive) (e : expr (BitVec n)) : expr (BitVec (w + n))
  | Slice {n : positive} (hi lo : N) (wf : (lo <= hi < Npos n)%N) (e : expr (BitVec n)) : expr (BitVec (N.succ_pos (hi - lo)))
  | Neg {n} (e : expr (BitVec n)) : expr (BitVec n)
  | Not {n} (e : expr (BitVec n)) : expr (BitVec n)
  | Inc {n} (e : expr (BitVec n)) : expr (BitVec n)
  | Dec {n} (e : expr (BitVec n)) : expr (BitVec n)
  | RedAnd {n} (e : expr (BitVec n)) : expr (BitVec 1)
  | RedOr {n} (e : expr (BitVec n)) : expr (BitVec 1)
  | RedXor {n} (e : expr (BitVec n)) : expr (BitVec 1)
  | Iff (e1 e2 : expr (BitVec 1)) : expr (BitVec 1)
  | Implies (e1 e2 : expr (BitVec 1)) : expr (BitVec 1)
  | Eq {s} (e1 e2 : expr s) : expr (BitVec 1)
  | NEq {s} (e1 e2 : expr s) : expr (BitVec 1)
  | SignedGt {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  | UnsignedGt {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  | SignedGtE {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  | UnsignedGtE {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  | SignedLt {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  | UnsignedLt {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  | SignedLtE {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  | UnsignedLtE {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  | And {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | NAnd {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | Or {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | NOr {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | XOr {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | XNor {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | Rol {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | Sll {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | Sra {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | Srl {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | Add {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | Mul {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | SignedDiv {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | UnsignedDiv {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | SignedMod {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  (* No unsigned mod *)
  | SignedRem {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | UnsignedRem {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | Sub {n} (e1 e2 : expr (BitVec n)) : expr (BitVec n)
  | SignedAddOverflow {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  | UnsignedAddOverflow {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  | SignedDivOverflow {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  (* No unsigned div overflow *)
  | SignedMulOverflow {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  | UnsignedMulOverflow {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  | SignedSubOverflow {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  | UnsignedSubOverflow {n} (e1 e2 : expr (BitVec n)) : expr (BitVec 1)
  | Concat {n m} (e1 : expr (BitVec n)) (e2 : expr (BitVec m)) : expr (BitVec (n + m))
  (* | Read {I E} (arr : expr (Array I E)) (idx : expr I) : expr E *)
  | ITE {n} (cond : expr (BitVec 1)) (ifT ifF : expr (BitVec n)) : expr (BitVec n)
  (* | Write {I E} (arr : expr (Array I E)) (idx : expr I) (elem : expr E) : expr (Array I E) *)
  (* Added for abstract syntax *)
  | Constant {n} (bv : BV.bitvector (Npos n)) : expr (BitVec n)
  | ExprRef {s} (r : Ref.t s) : expr s
  .
  Arguments expr {env} s.

  Record stateVar {env} := {
    stateName : name;
    stateSort : Sort.t;
    stateInit : expr stateSort;
    stateNext : expr stateSort;
    stateWf : env stateName = Some stateSort;
  }.

  Definition stateRef {env} (s : stateVar) := Ref.Mk env (stateSort s) (stateName s) (stateWf s).

  Record operatorVar {env} := {
    operatorName : name;
    operatorSort : Sort.t;
    operatorExpr : expr operatorSort;
    operatorWf : env operatorName = Some operatorSort;
  }.

  Definition operatorRef {env} (op : operatorVar) := Ref.Mk env (operatorSort op) (operatorName op) (operatorWf op).

  Record btor := {
    btorEnv : environment;
    btorInputs : list name;
    btorOperators : list operatorVar;
    btorStates : list stateVar;
    btorProperties : list (expr (BitVec 1)); (* safety property is: all properties are *false* *)
    btorNoDupNames : NoDup (btorInputs ++ map stateName btorStates ++ map operatorName btorOperators);
    btorNamesCovered : forall name sort, btorEnv name = Some sort -> In name (btorInputs ++ map stateName btorStates ++ map operatorName btorOperators);
    btorInputsWf : Forall (fun n => exists s, btorEnv n = Some s) btorInputs
  }.

  Module State.
    Definition state {env} := forall (s : Sort.t) (r : Ref.t s), Sort.interp s.
    Notation t := state.

    Definition set_ref {env s} (r : Ref.t s) (val : Sort.interp s) (st : t) : t :=
      fun s' r' =>
        match Sort.eq_dec s s' with
        | left E =>
          if String.eqb (Ref.refName r) (Ref.refName r')
          then rew [Sort.interp] E in val
          else st s' r'
        | right _ => st s' r'
        end.

    Definition get {env s} (st : t) (r : Ref.t s) :=
      st s r.

    Definition empty_default {env} : t := fun s r =>
      match s with
      | Sort.BitVec n => BV.zeros n
      end.

    Infix "@" := get (at level 5).
  End State.
  Import (notations) State.

  Definition undef {s} : Sort.interp s. Admitted.
  Extract Constant undef =>
    "(fun _ -> failwith ""Unsupported expression in abstract BTOR evaluation"")".

  Fixpoint eval {env : environment} {s} (st : State.t) (e : expr s) : Sort.interp s := 
    match e with
    | Neg e => BV.bv_neg (eval st e)
    | Add lhs rhs => BV.bv_add (eval st lhs) (eval st rhs)
    | _ => undef
    end.

  Section relational.
    Definition has_operator {env} (st : State.t) (var : operatorVar) : Prop :=
      st _ (operatorRef var) = eval st (operatorExpr var).

    Definition has_state_init {env} (st : State.t) (var : stateVar) : Prop :=
      st _ (stateRef var) = eval st (stateInit var).

    Definition has_state_next {env} (st0 st1 : State.t) (var : stateVar) : Prop :=
      st1 _ (stateRef var) = eval st0 (stateNext var).

    Definition holds_prop {env} (st : State.t) (prop : expr (Sort.BitVec 1)) : Prop :=
      eval st prop = BV.zeros 1.

    Definition is_valid b st :=
      Forall (has_operator st) (btorOperators b).

    Definition is_initial b st :=
      Forall (has_state_init st) (btorStates b).

    Definition is_next b (st0 st1 : State.t) :=
      Forall (has_state_next st0 st1) (btorStates b).

    Definition is_valid_initial b st :=
      is_valid b st /\ is_initial b st.

    Definition is_valid_next b (st0 st1 : State.t) :=
      is_valid b st0 /\ is_valid b st1 /\ is_next b st0 st1.

    Definition is_safe b st :=
      Forall (holds_prop st) (btorProperties b).

    Definition reachable_from b (st1 st2 : @State.t (btorEnv b)) : Prop :=
      clos_trans (@State.t (btorEnv b)) (is_valid_next b) st1 st2.

    Variant reachable (b : btor) : @State.t (btorEnv b) -> Prop :=
    | ReachableInitial st : is_valid_initial b st -> reachable b st
    | ReachableFrom st0 st : is_valid_initial b st0 -> reachable_from b st0 st -> reachable b st.

    Definition safe_model (b : btor) : Prop :=
      forall st, reachable b st -> is_safe b st.

    Lemma reachable_valid b st : reachable b st -> is_valid b st.
    Proof.
      destruct 1 as [?| ? ? ? Hreachable].
      - crush.
      - apply clos_trans_tn1 in Hreachable.
        destruct Hreachable.
        all: crush.
    Qed.
  End relational.

  Section executable.
    Definition run_operator {env} (op : operatorVar) (st : State.t) : State.t := 
      State.set_ref (operatorRef op) (eval st (operatorExpr op)) st.

    Definition run_operators {env} := fold_left (flip run_operator).

    Definition run_state_init {env} (s : stateVar) (st : State.t) : State.t := 
      State.set_ref (stateRef s) (eval st (stateInit s)) st.

    Definition run_state_inits {env} := fold_left (flip run_state_init).

    Definition run_state_next {env} (s : stateVar) (st : State.t) : State.t := 
      State.set_ref (stateRef s) (eval st (stateNext s)) st.

    Definition run_state_nexts {env} := fold_left (flip run_state_next).

    Definition value_list {env} := list {s & Ref.t s * Sort.interp s}.

    Definition set_inputs {env} (values : value_list) (s : State.t) : State.t :=
      fold_left (fun acc '(s; (r, v)) => State.set_ref r v acc) values s.

    Definition initial_state (b : btor) : @State.t (btorEnv b) :=
      (run_state_inits (btorStates b) ∘ run_operators (btorOperators b)) State.empty_default.

    Definition next_state (b : btor) (inputs : value_list) : State.t -> State.t :=
      run_state_nexts (btorStates b) ∘ run_operators (btorOperators b) ∘ set_inputs inputs.
  End executable.

  (* TODO: Is reset allowed to read from inputs? Or does it have to be constant?
       Assuming that it has to be constant. Inputs will read from empty_default (0s)
   *)
  CoFixpoint runFrom (b : btor) (st : State.t) (input_stream : Stream value_list) : Stream State.t :=
    Streams.Cons st (runFrom b (next_state b (Streams.hd input_stream) st) (Streams.tl input_stream)).

  Definition run b input_stream := runFrom b (initial_state b) input_stream.
End Abstract.

Module Raw.
  Inductive expr : Type :=
  | UnsignedExtend (w : positive) (e : expr)
  | SignedExtend (w : positive) (e : expr)
  | Slice (hi lo : N) (e : expr)
  | Neg (e : expr)
  | Not (e : expr)
  | Inc (e : expr)
  | Dec (e : expr)
  | RedAnd (e : expr)
  | RedOr (e : expr)
  | RedXor (e : expr)
  | Iff (e1 e2 : expr)
  | Implies (e1 e2 : expr)
  | Eq (e1 e2 : expr)
  | NEq (e1 e2 : expr)
  | SignedGt (e1 e2 : expr)
  | UnsignedGt (e1 e2 : expr)
  | SignedGtE (e1 e2 : expr)
  | UnsignedGtE (e1 e2 : expr)
  | SignedLt (e1 e2 : expr)
  | UnsignedLt (e1 e2 : expr)
  | SignedLtE (e1 e2 : expr)
  | UnsignedLtE (e1 e2 : expr)
  | And (e1 e2 : expr)
  | NAnd (e1 e2 : expr)
  | Or (e1 e2 : expr)
  | NOr (e1 e2 : expr)
  | XOr (e1 e2 : expr)
  | XNor (e1 e2 : expr)
  | Rol (e1 e2 : expr)
  | Sll (e1 e2 : expr)
  | Sra (e1 e2 : expr)
  | Srl (e1 e2 : expr)
  | Add (e1 e2 : expr)
  | Mul (e1 e2 : expr)
  | SignedDiv (e1 e2 : expr)
  | UnsignedDiv (e1 e2 : expr)
  | SignedMod (e1 e2 : expr)
  (* No unsigned mod *)
  | SignedRem (e1 e2 : expr)
  | UnsignedRem (e1 e2 : expr)
  | Sub (e1 e2 : expr)
  | SignedAddOverflow (e1 e2 : expr)
  | UnsignedAddOverflow (e1 e2 : expr)
  | SignedDivOverflow (e1 e2 : expr)
  (* No unsigned div overflow *)
  | SignedMulOverflow  (e1 e2 : expr)
  | UnsignedMulOverflow  (e1 e2 : expr)
  | SignedSubOverflow (e1 e2 : expr)
  | UnsignedSubOverflow (e1 e2 : expr)
  | Concat (e1 : expr) (e2 : expr)
  (* | Read (arr idx : expr) *)
  | ITE (cond : expr) (ifT ifF : expr)
  (* | Write (arr idx elem: expr) *)
  (* Added for abstract syntax *)
  | Constant (bv : RawBV.bitvector)
  | ExprRef (n : name)
  .

  Variant node :=
  | StateDecl (n : name) (s : Sort.t)
  | StateInit (s : Sort.t) (n : name) (e : expr)
  | StateNext (s : Sort.t) (n : name) (e : expr)
  | Operator (s : Sort.t) (n : name) (e : expr)
  | Bad (e : expr)
  .

  Definition btor := list node.

  Fixpoint expr_of_abstract {env s} (e : Abstract.expr s) : expr :=
    match e with
    | Abstract.UnsignedExtend w e => UnsignedExtend w (expr_of_abstract e)
    | Abstract.SignedExtend w e => SignedExtend w (expr_of_abstract e)
    | Abstract.Slice hi lo wf e => Slice hi lo (expr_of_abstract e)
    | Abstract.Neg e => Neg (expr_of_abstract e)
    | Abstract.Not e => Not (expr_of_abstract e)
    | Abstract.Inc e => Inc (expr_of_abstract e)
    | Abstract.Dec e => Dec (expr_of_abstract e)
    | Abstract.RedAnd e => RedAnd (expr_of_abstract e)
    | Abstract.RedOr e => RedOr (expr_of_abstract e)
    | Abstract.RedXor e => RedXor (expr_of_abstract e)
    | Abstract.Iff e1 e2 => Iff (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.Implies e1 e2 => Implies (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.Eq e1 e2 => Eq (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.NEq e1 e2 => NEq (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.SignedGt e1 e2 => SignedGt (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.UnsignedGt e1 e2 => UnsignedGt (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.SignedGtE e1 e2 => SignedGtE (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.UnsignedGtE e1 e2 => UnsignedGtE (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.SignedLt e1 e2 => SignedLt (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.UnsignedLt e1 e2 => UnsignedLt (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.SignedLtE e1 e2 => SignedLtE (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.UnsignedLtE e1 e2 => UnsignedLtE (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.And e1 e2 => And (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.NAnd e1 e2 => NAnd (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.Or e1 e2 => Or (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.NOr e1 e2 => NOr (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.XOr e1 e2 => XOr (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.XNor e1 e2 => XNor (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.Rol e1 e2 => Rol (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.Sll e1 e2 => Sll (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.Sra e1 e2 => Sra (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.Srl e1 e2 => Srl (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.Add e1 e2 => Add (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.Mul e1 e2 => Mul (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.SignedDiv e1 e2 => SignedDiv (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.UnsignedDiv e1 e2 => UnsignedDiv (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.SignedMod e1 e2 => SignedMod (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.SignedRem e1 e2 => SignedRem (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.UnsignedRem e1 e2 => UnsignedRem (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.Sub e1 e2 => Sub (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.SignedAddOverflow e1 e2 => SignedAddOverflow (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.UnsignedAddOverflow e1 e2 => UnsignedAddOverflow (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.SignedDivOverflow e1 e2 => SignedDivOverflow (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.SignedMulOverflow e1 e2 => SignedMulOverflow (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.UnsignedMulOverflow e1 e2 => UnsignedMulOverflow (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.SignedSubOverflow e1 e2 => SignedSubOverflow (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.UnsignedSubOverflow e1 e2 => UnsignedSubOverflow (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.Concat e1 e2 => Concat (expr_of_abstract e1) (expr_of_abstract e2)
    | Abstract.ITE cond ifT ifF => ITE (expr_of_abstract cond) (expr_of_abstract ifT) (expr_of_abstract ifF)
    | Abstract.Constant bv => Constant (BV.bits bv)
    | Abstract.ExprRef r => ExprRef (Ref.refName r)
    end.

  Equations expect_sort {env} (expected : Sort.t)
      (translated : result {s & @Abstract.expr env s}) : result (@Abstract.expr env expected) :=
    expect_sort expected translated :=
      let* (s; e) := translated in
      match Sort.eq_dec s expected with
      | left E => ret (rew [@Abstract.expr env] E in e)
      | right _ => inl "Incompatible BTOR operand sorts"%string
      end.

  Definition unary {env} {f : positive -> positive}
      (op : forall n, Abstract.expr (BitVec n) -> Abstract.expr (BitVec (f n)))
      (translated : result {s & Abstract.expr s}) : result {s & Abstract.expr s} :=
    let* (BitVec n; e) := translated in
    ret (_; op n e).

  Definition unary1 {env}
      (op : Abstract.expr (BitVec 1) -> Abstract.expr (BitVec 1))
      (translated : result {s & Abstract.expr s}) : result {s & Abstract.expr s} :=
    let* e := expect_sort (BitVec 1) translated in
    ret (_; op e).

  Definition binary {env} {f}
      (op : forall n, Abstract.expr (BitVec n) -> Abstract.expr (BitVec n) -> Abstract.expr (BitVec (f n)))
      (lhs rhs : result {s & Abstract.expr s}) : result {s & Abstract.expr s} :=
    let* (BitVec n; lhs) := lhs in
    let* rhs := expect_sort (BitVec n) rhs in
    ret (_; op n lhs rhs).

  Definition binaryCmp {env} {f}
      (op : forall s, Abstract.expr s -> Abstract.expr s -> Abstract.expr (f s))
      (lhs rhs : result {s & Abstract.expr s}) : result {s & Abstract.expr s} :=
    let* (s; lhs) := lhs in
    let* rhs := expect_sort s rhs in
    ret (_; op s lhs rhs).

  Definition binary1 {env}
      (op : Abstract.expr (BitVec 1) -> Abstract.expr (BitVec 1) -> Abstract.expr (BitVec 1))
      (lhs rhs : result {s & Abstract.expr s}) : result {s & Abstract.expr s} :=
    let* lhs := expect_sort (BitVec 1) lhs in
    let* rhs := expect_sort (BitVec 1) rhs in
    ret (_; op lhs rhs).

  Equations expr_to_abstract {env} (rawexpr : expr) : result {s & @Abstract.expr env s} := {
    | UnsignedExtend w e => unary (fun n => @Abstract.UnsignedExtend env n w) (expr_to_abstract e)
    | SignedExtend w e => unary (fun n => @Abstract.SignedExtend env n w) (expr_to_abstract e)
    | Slice hi lo e =>
      let* (BitVec n; e) := expr_to_abstract e in
      let* Hlo := assert_dec (lo <= hi)%N "Invalid BTOR slice bounds"%string in
      let* Hhi := assert_dec (hi < Npos n)%N "Invalid BTOR slice bounds"%string in
      ret (_; Abstract.Slice hi lo (conj Hlo Hhi) e)
    | Neg e => unary (@Abstract.Neg env) (expr_to_abstract e)
    | Not e => unary (@Abstract.Not env) (expr_to_abstract e)
    | Inc e => unary (@Abstract.Inc env) (expr_to_abstract e)
    | Dec e => unary (@Abstract.Dec env) (expr_to_abstract e)
    | RedAnd e => unary (@Abstract.RedAnd env) (expr_to_abstract e)
    | RedOr e => unary (@Abstract.RedOr env) (expr_to_abstract e)
    | RedXor e => unary (@Abstract.RedXor env) (expr_to_abstract e)
    | Iff lhs rhs => binary1 (@Abstract.Iff env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | Implies lhs rhs => binary1 (@Abstract.Implies env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | Eq lhs rhs => binaryCmp (@Abstract.Eq env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | NEq lhs rhs => binaryCmp (@Abstract.NEq env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | SignedGt lhs rhs => binary (@Abstract.SignedGt env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | UnsignedGt lhs rhs => binary (@Abstract.UnsignedGt env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | SignedGtE lhs rhs => binary (@Abstract.SignedGtE env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | UnsignedGtE lhs rhs => binary (@Abstract.UnsignedGtE env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | SignedLt lhs rhs => binary (@Abstract.SignedLt env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | UnsignedLt lhs rhs => binary (@Abstract.UnsignedLt env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | SignedLtE lhs rhs => binary (@Abstract.SignedLtE env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | UnsignedLtE lhs rhs => binary (@Abstract.UnsignedLtE env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | And lhs rhs => binary (@Abstract.And env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | NAnd lhs rhs => binary (@Abstract.NAnd env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | Or lhs rhs => binary (@Abstract.Or env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | NOr lhs rhs => binary (@Abstract.NOr env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | XOr lhs rhs => binary (@Abstract.XOr env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | XNor lhs rhs => binary (@Abstract.XNor env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | Rol lhs rhs => binary (@Abstract.Rol env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | Sll lhs rhs => binary (@Abstract.Sll env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | Sra lhs rhs => binary (@Abstract.Sra env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | Srl lhs rhs => binary (@Abstract.Srl env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | Add lhs rhs => binary (@Abstract.Add env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | Mul lhs rhs => binary (@Abstract.Mul env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | SignedDiv lhs rhs => binary (@Abstract.SignedDiv env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | UnsignedDiv lhs rhs => binary (@Abstract.UnsignedDiv env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | SignedMod lhs rhs => binary (@Abstract.SignedMod env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | SignedRem lhs rhs => binary (@Abstract.SignedRem env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | UnsignedRem lhs rhs => binary (@Abstract.UnsignedRem env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | Sub lhs rhs => binary (@Abstract.Sub env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | SignedAddOverflow lhs rhs => binary (@Abstract.SignedAddOverflow env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | UnsignedAddOverflow lhs rhs => binary (@Abstract.UnsignedAddOverflow env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | SignedDivOverflow lhs rhs => binary (@Abstract.SignedDivOverflow env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | SignedMulOverflow lhs rhs => binary (@Abstract.SignedMulOverflow env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | UnsignedMulOverflow lhs rhs => binary (@Abstract.UnsignedMulOverflow env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | SignedSubOverflow lhs rhs => binary (@Abstract.SignedSubOverflow env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | UnsignedSubOverflow lhs rhs => binary (@Abstract.UnsignedSubOverflow env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | Concat lhs rhs =>
      let* (BitVec n; lhs) := expr_to_abstract lhs in
      let* (BitVec m; rhs) := expr_to_abstract rhs in
      ret (_; Abstract.Concat lhs rhs)
    | ITE cond ifT ifF =>
      let* cond := expect_sort (BitVec 1) (expr_to_abstract cond) in
      let* (BitVec n; ifT) := expr_to_abstract ifT in
      let* ifF := expect_sort (BitVec n) (expr_to_abstract ifF) in
      ret (_; Abstract.ITE cond ifT ifF)
    | Constant bv =>
      match bv with
      | [] => inl "Empty constant in Raw Btor"%string
      | b :: bs => ret (_; Abstract.Constant (BV.of_bits (b :: bs)))
      end
    | ExprRef name =>
      match env name as found return env name = found -> result {s & @Abstract.expr env s} with
      | Some s => fun wf => ret (s; Abstract.ExprRef (Ref.Mk env s name wf))
      | None => fun _ => inl ("Undefined BTOR reference: " ++ name)%string
      end eq_refl
  }.

    (* Definition node_of_abstract {env} (n : Abstract.node) : node :=
     *   match n with
     *   | Abstract.StateDecl n s wf => StateDecl n s
     *   | @Abstract.StateInit _ s n e wf => StateInit s n (expr_of_abstract e)
     *   | @Abstract.StateNext _ s n e wf => StateNext s n (expr_of_abstract e)
     *   | @Abstract.Operator _ s n e wf => Operator s n (expr_of_abstract e)
     *   | Abstract.Bad e => Bad (expr_of_abstract e)
     *   end.

 *     Definition node_to_abstract env (nd : node) : result (@Abstract.node env) :=
     *   match nd with
     *   | StateDecl n s =>
     *     let* wf := assert_dec (env n = Some s) "Invalid state decl"%string in
     *     ret (Abstract.StateDecl n s wf)
     *   | StateInit s n e =>
     *     let* (s'; e') := expr_to_abstract e in
     *     let* wf := assert_dec (env n = Some s') "Invalid state init"%string in
     *     inr (Abstract.StateInit n e' wf)
     *   | StateNext s n e =>
     *     let* (s'; e') := expr_to_abstract e in
     *     let* wf := assert_dec (env n = Some s') "Invalid state next"%string in
     *     ret (Abstract.StateNext n e' wf)
     *   | Operator s n e =>
     *     let* (s'; e') := expr_to_abstract e in
     *     let* wf := assert_dec (env n = Some s') "Invalid operator"%string in
     *     ret (Abstract.Operator n e' wf)
     *   | Bad e =>
     *     let* (s'; e') := expr_to_abstract e in
     *     let* eq := assert_dec (s' = BitVec 1) "Invalid bad node"%string in
     *     ret (Abstract.Bad (rew eq in e'))
     *   end. *)

    Definition add_name (n : name) (s : Sort.t) (env : environment) : environment :=
      fun n' => if String.eqb n n' then Some s else env n'.

    Fixpoint env_of_nodes (nds : list node) : environment :=
      match nds with
      | StateDecl n s :: nds => add_name n s (env_of_nodes nds)
      | StateInit s n e :: nds => env_of_nodes nds
      | StateNext s n e :: nds => env_of_nodes nds
      | Operator s n e :: nds => add_name n s (env_of_nodes nds)
      | Bad e :: nds => env_of_nodes nds
      | [] => fun _ => None
      end.

    Definition of_abstract (b : Abstract.btor) : btor.
    Admitted.

    Definition to_abstract (b : btor) : result Abstract.btor.
    Admitted.

    Section rename.
      Variable (m : name -> name).

      Fixpoint rename_expr (e : expr) : expr :=
        match e with
        | UnsignedExtend w e => UnsignedExtend w (rename_expr e)
        | SignedExtend w e => SignedExtend w (rename_expr e)
        | Slice hi lo e => Slice hi lo (rename_expr e)
        | Neg e => Neg (rename_expr e)
        | Not e => Not (rename_expr e)
        | Inc e => Inc (rename_expr e)
        | Dec e => Dec (rename_expr e)
        | RedAnd e => RedAnd (rename_expr e)
        | RedOr e => RedOr (rename_expr e)
        | RedXor e => RedXor (rename_expr e)
        | Iff e1 e2 => Iff (rename_expr e1) (rename_expr e2)
        | Implies e1 e2 => Implies (rename_expr e1) (rename_expr e2)
        | Eq e1 e2 => Eq (rename_expr e1) (rename_expr e2)
        | NEq e1 e2 => NEq (rename_expr e1) (rename_expr e2)
        | SignedGt e1 e2 => SignedGt (rename_expr e1) (rename_expr e2)
        | UnsignedGt e1 e2 => UnsignedGt (rename_expr e1) (rename_expr e2)
        | SignedGtE e1 e2 => SignedGtE (rename_expr e1) (rename_expr e2)
        | UnsignedGtE e1 e2 => UnsignedGtE (rename_expr e1) (rename_expr e2)
        | SignedLt e1 e2 => SignedLt (rename_expr e1) (rename_expr e2)
        | UnsignedLt e1 e2 => UnsignedLt (rename_expr e1) (rename_expr e2)
        | SignedLtE e1 e2 => SignedLtE (rename_expr e1) (rename_expr e2)
        | UnsignedLtE e1 e2 => UnsignedLtE (rename_expr e1) (rename_expr e2)
        | And e1 e2 => And (rename_expr e1) (rename_expr e2)
        | NAnd e1 e2 => NAnd (rename_expr e1) (rename_expr e2)
        | Or e1 e2 => Or (rename_expr e1) (rename_expr e2)
        | NOr e1 e2 => NOr (rename_expr e1) (rename_expr e2)
        | XOr e1 e2 => XOr (rename_expr e1) (rename_expr e2)
        | XNor e1 e2 => XNor (rename_expr e1) (rename_expr e2)
        | Rol e1 e2 => Rol (rename_expr e1) (rename_expr e2)
        | Sll e1 e2 => Sll (rename_expr e1) (rename_expr e2)
        | Sra e1 e2 => Sra (rename_expr e1) (rename_expr e2)
        | Srl e1 e2 => Srl (rename_expr e1) (rename_expr e2)
        | Add e1 e2 => Add (rename_expr e1) (rename_expr e2)
        | Mul e1 e2 => Mul (rename_expr e1) (rename_expr e2)
        | SignedDiv e1 e2 => SignedDiv (rename_expr e1) (rename_expr e2)
        | UnsignedDiv e1 e2 => UnsignedDiv (rename_expr e1) (rename_expr e2)
        | SignedMod e1 e2 => SignedMod (rename_expr e1) (rename_expr e2)
        | SignedRem e1 e2 => SignedRem (rename_expr e1) (rename_expr e2)
        | UnsignedRem e1 e2 => UnsignedRem (rename_expr e1) (rename_expr e2)
        | Sub e1 e2 => Sub (rename_expr e1) (rename_expr e2)
        | SignedAddOverflow e1 e2 => SignedAddOverflow (rename_expr e1) (rename_expr e2)
        | UnsignedAddOverflow e1 e2 => UnsignedAddOverflow (rename_expr e1) (rename_expr e2)
        | SignedDivOverflow e1 e2 => SignedDivOverflow (rename_expr e1) (rename_expr e2)
        | SignedMulOverflow e1 e2 => SignedMulOverflow (rename_expr e1) (rename_expr e2)
        | UnsignedMulOverflow e1 e2 => UnsignedMulOverflow (rename_expr e1) (rename_expr e2)
        | SignedSubOverflow e1 e2 => SignedSubOverflow (rename_expr e1) (rename_expr e2)
        | UnsignedSubOverflow e1 e2 => UnsignedSubOverflow (rename_expr e1) (rename_expr e2)
        | Concat e1 e2 => Concat (rename_expr e1) (rename_expr e2)
        | ITE cond ifT ifF => ITE (rename_expr cond) (rename_expr ifT) (rename_expr ifF)
        | Constant bv => Constant bv
        | ExprRef n => ExprRef (m n)
        end.

      Definition rename_node (n : node) : node :=
        match n with
        | StateDecl n s => StateDecl (m n) s
        | StateInit s n e => StateInit s (m n) (rename_expr e)
        | StateNext s n e => StateNext s (m n) (rename_expr e)
        | Operator s n e => Operator s (m n) (rename_expr e)
        | Bad e => Bad (rename_expr e)
        end.

      Definition rename := map rename_node.
    End rename.
End Raw.
