From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import ProofIrrelevance.
From Stdlib Require Extraction.
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

Definition environment := name -> option Sort.t.

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

  Variant node {env} :=
  | StateDecl (n : name) (s : Sort.t) (wf : env n = Some s)
  | StateInit {s : Sort.t} (n : name) (e : expr s) (wf : env n = Some s)
  | StateNext {s : Sort.t} (n : name) (e : expr s) (wf : env n = Some s)
  | Operator {s : Sort.t} (n : name) (e : expr s) (wf : env n = Some s)
  | Bad (e : expr (BitVec 1))
  .

  Record btor := {
    btorEnv : environment;
    btorBody : list (@node btorEnv);
  }.

  Module State.
    Definition t {env} := forall (s : Sort.t) (r : Ref.t s), Sort.interp s.

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

    Infix "@" := get (at level 5).
  End State.
  Import (notations) State.

  Definition undef {s} : Sort.interp s. Admitted.
  Extract Constant undef =>
    "(fun _ -> failwith ""Unsupported expression in abstract BTOR evaluation"")".

  Fixpoint eval {env : environment} {s} (st : State.t) (e : expr s) : Sort.interp s :=
    match e with
    | Add lhs rhs => BV.bv_add (eval st lhs) (eval st rhs)
    | _ => undef
    end.

  Fixpoint run {env} (nds : list node) (pending : State.t -> State.t) (st : State.t) : State.t :=
    match nds with
    | [] => pending st
    | (nd :: nds) => match nd with
      | @StateNext _ s n e wf =>
        run nds (State.set_ref (Ref.Mk env s n wf) (eval st e)) st
      | @Operator _ s n e wf =>
        run nds pending (State.set_ref (Ref.Mk env s n wf) (eval st e) st)
      | _ => run nds pending st
      end
    end.

  Definition next {env} (nds : list node) (st : State.t) : State.t :=
    run nds (fun s => s) st.
End Abstract.

Module Raw.
  Inductive expr : Type :=
  | UnsignedExtend (w : positive) (e : expr)
  | SignedExtend (w : positive) (e : expr)
  | Slice (hi lo : N) (e : expr)
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
    | Not e => unary (@Abstract.Not env) (expr_to_abstract e)
    | Inc e => unary (@Abstract.Inc env) (expr_to_abstract e)
    | Dec e => unary (@Abstract.Dec env) (expr_to_abstract e)
    | RedAnd e => unary (@Abstract.RedAnd env) (expr_to_abstract e)
    | RedOr e => unary (@Abstract.RedOr env) (expr_to_abstract e)
    | RedXor e => unary (@Abstract.RedXor env) (expr_to_abstract e)
    | Iff lhs rhs => binary1 (@Abstract.Iff env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | Implies lhs rhs => binary1 (@Abstract.Implies env) (expr_to_abstract lhs) (expr_to_abstract rhs)
    | Eq lhs rhs => binary1 Abstract.Eq (expr_to_abstract lhs) (expr_to_abstract rhs)
    | NEq lhs rhs => binary1 Abstract.NEq (expr_to_abstract lhs) (expr_to_abstract rhs)
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

    Definition node_of_abstract {env} (n : Abstract.node) : node :=
      match n with
      | Abstract.StateDecl n s wf => StateDecl n s
      | @Abstract.StateInit _ s n e wf => StateInit s n (expr_of_abstract e)
      | @Abstract.StateNext _ s n e wf => StateNext s n (expr_of_abstract e)
      | @Abstract.Operator _ s n e wf => Operator s n (expr_of_abstract e)
      | Abstract.Bad e => Bad (expr_of_abstract e)
      end.

    Definition node_to_abstract env (nd : node) : result (@Abstract.node env) :=
      match nd with
      | StateDecl n s =>
        let* wf := assert_dec (env n = Some s) "Invalid state decl"%string in
        ret (Abstract.StateDecl n s wf)
      | StateInit s n e =>
        let* (s'; e') := expr_to_abstract e in
        let* wf := assert_dec (env n = Some s') "Invalid state init"%string in
        inr (Abstract.StateInit n e' wf)
      | StateNext s n e =>
        let* (s'; e') := expr_to_abstract e in
        let* wf := assert_dec (env n = Some s') "Invalid state next"%string in
        ret (Abstract.StateNext n e' wf)
      | Operator s n e =>
        let* (s'; e') := expr_to_abstract e in
        let* wf := assert_dec (env n = Some s') "Invalid operator"%string in
        ret (Abstract.Operator n e' wf)
      | Bad e =>
        let* (s'; e') := expr_to_abstract e in
        let* eq := assert_dec (s' = BitVec 1) "Invalid bad node"%string in
        ret (Abstract.Bad (rew eq in e'))
      end.

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

    Definition of_abstract (b : Abstract.btor) : btor :=
      map node_of_abstract (Abstract.btorBody b).

    Definition to_abstract (b : btor) : result Abstract.btor :=
      let* body := mapT (node_to_abstract (env_of_nodes b)) b in
      ret {| Abstract.btorBody := body |}.
End Raw.
