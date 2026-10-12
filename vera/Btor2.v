(* From Stdlib Require Import String. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import ProofIrrelevance.
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
(* From ExtLib Require Import Structures.Monads. *)
(* From ExtLib Require Import Data.Monads.EitherMonad. *)
(* From ExtLib Require Import Structures.MonadExc. *)
(* From ExtLib Require Import Structures.Monads. *)
(* From ExtLib Require Import Structures.Traversable. *)
From ExtLib Require Import Data.List.

(* From vera Require Import Common. *)
(* From vera Require Import Tactics. *)
From vera Require Import Bitvector.
(* From vera Require Import Decidable. *)
(* Import (notations) Bitvector.RawBV. *)
(* From vera Require Import Variables. *)

(* From Stdlib Require Import List. *)
(* From Stdlib Require Arith Lia Program. *)
From Stdlib Require Import Structures.Equalities.
(* From Stdlib Require Arith.PeanoNat. *)
(* From Equations Require Import Equations. *)

Import ListNotations.
(* Import MonadLetNotation. *)
(* Import SigTNotations. *)
Import EqNotations.
(* Local Open Scope monad_scope. *)

Definition nid := N.

Module Sort <: UsualDecidableType.
  Inductive sort :=
  | BitVec (n : N) (* zero-width allowed? *)
  | Array (idx elem : sort)
  .
  Definition t := sort.
  Include HasUsualEq <+ UsualIsEq.

  Definition eq_dec (x y : t) : {x = y} + {x <> y}.
  Proof. decide equality; apply N.eq_dec. Defined.

  Fixpoint interp (s : sort) : Type :=
  match s with
  | BitVec n => BV.bitvector n
  | Array idx elem => interp idx -> interp elem
  end.
End Sort.

Import Sort (BitVec, Array).

Definition environment := nid -> option Sort.t.

Module Ref.
  Record t {env : environment} {s : Sort.t} := Mk {
    refName : nid;
    refWf : env refName = Some s
  }.
  Arguments t : clear implicits.

  Definition eqb {env s} (r1 r2 : t env s) : bool := N.eqb r1.(refName) r2.(refName).

  Definition heqb {env s1 s2} (r1 : t env s1) (r2 : t env s2) : bool :=
    if Sort.eq_dec s1 s2 then N.eqb r1.(refName) r2.(refName) else false.

  Lemma eqb_refl {env s} (r : t env s) : eqb r r = true.
  Proof. destruct r. apply N.eqb_refl. Qed.

  Lemma eqb_eq {env s} (r1 r2 : t env s) :
    eqb r1 r2 = true <-> r1 = r2.
  Proof.
    unfold eqb.
    destruct r1, r2. simpl.
    rewrite N.eqb_eq.
    split; intros H.
    - subst. f_equal. apply proof_irrelevance.
    - inversion H. reflexivity.
  Qed.
End Ref.

Variant expr {env : environment} : Sort.t -> Type :=
| UnsignedExtend {n : N} (w : N) (e : Ref.t env (BitVec n)) : expr (BitVec (n + w))
| SignedExtend {n : N} (w : N) (e : Ref.t env (BitVec n)) : expr (BitVec (n + w))
| Not {n} (e : Ref.t env (BitVec n)) : expr (BitVec n)
| Inc {n} (e : Ref.t env (BitVec n)) : expr (BitVec n)
| Dec {n} (e : Ref.t env (BitVec n)) : expr (BitVec n)
| RedAnd {n} (e : Ref.t env (BitVec n)) : expr (BitVec 1)
| RedOr {n} (e : Ref.t env (BitVec n)) : expr (BitVec 1)
| RedXor {n} (e : Ref.t env (BitVec n)) : expr (BitVec 1)
| Iff (e1 e2 : Ref.t env (BitVec 1)) : expr (BitVec 1)
| Implies (e1 e2 : Ref.t env (BitVec 1)) : expr (BitVec 1)
| Eq {s} (e1 e2 : Ref.t env s) : expr (BitVec 1)
| NEq {s} (e1 e2 : Ref.t env s) : expr (BitVec 1)
| SignedGt {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| UnsignedGt {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| SignedGtE {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| UnsignedGtE {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| SignedLt {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| UnsignedLt {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| SignedLtE {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| UnsignedLtE {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| And {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| NAnd {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| Or {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| NOr {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| XOr {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| XNor {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| Rol {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| Sll {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| Sra {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| Srl {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| Add {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| Mul {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| SignedDiv {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| UnsignedDiv {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| SignedMod {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
(* No unsigned mod *)
| SignedRem {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| UnsignedRem {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| Sub {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec n)
| SignedAddOverflow {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| UnsignedAddOverflow {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| SignedDivOverflow {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| UnsignedDivOverflow {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| SignedMulOverflow {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| UnsignedMulOverflow {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| SignedSubOverflow {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| UnsignedSubOverflow {n} (e1 e2 : Ref.t env (BitVec n)) : expr (BitVec 1)
| Concat {n m} (e1 : Ref.t env (BitVec n)) (e2 : Ref.t env (BitVec m)) : expr (BitVec (n + m))
| Read {I E} (arr : Ref.t env (Array I E)) (idx : Ref.t env I) : expr E
| ITE {n} (cond : Ref.t env (BitVec 1)) (ifT ifF : Ref.t env (BitVec n)) : expr (BitVec n)
| Write {I E} (arr : Ref.t env (Array I E)) (idx : Ref.t env I) (elem : Ref.t env E) : expr (Array I E)
(* Added for abstract syntax *)
| Constant {n} (bv : BV.bitvector n) : expr (BitVec n)
.
Arguments expr : clear implicits.

Record stateVar (env : environment) := {
  stSort : Sort.t;
  stInit : option (expr env stSort);
  stNext : option (expr env stSort);
}.

Record var (env : environment) := {
  varSort : Sort.t;
  varExpr : expr env varSort;
}.


Inductive property env :=
| Bad (e : expr env (BitVec 1))
.

Variant node {env : environment} :=
| StateDecl (n : nid) (s : Sort.t) (wf : env n = Some s)
| StateInit {s : Sort.t} (n : nid) (e : expr env s) (wf : env n = Some s)
| StateNext {s : Sort.t} (n : nid) (e : expr env s) (wf : env n = Some s)
| Operator {s : Sort.t} (n : nid) (e : expr env s) (wf : env n = Some s)
.

Arguments node : clear implicits.

Definition nodeId {env} (nd : node env) :=
  match nd with
  | StateDecl n _ _ => n
  | StateInit n _ _ => n
  | StateNext n _ _ => n
  | Operator n _ _ => n
  end.

Record btor := {
  btorEnv : environment;
  btorBody : list (node btorEnv)
}.

Module State. Section State.
  Context {env : environment}.

  Definition t := forall (s : Sort.t) (r : Ref.t env s), Sort.interp s.

  Definition set_ref {s} (r : Ref.t env s) (val : Sort.interp s) (st : t) : t :=
    fun s' r' =>
      match Sort.eq_dec s s' with
      | left E =>
        if N.eqb (Ref.refName r) (Ref.refName r')
        then rew [Sort.interp] E in val
        else st s' r'
      | right _ => st s' r'
      end.

  Definition get {s} (st : t) (r : Ref.t env s) :=
    st s r.
End State. End State.

Definition undef {s} : Sort.interp s. Admitted.

Definition eval {env s} (st : @State.t env) (e : expr env s) : Sort.interp s :=
  match e with
  | Add r1 r2 => BV.bv_add (State.get st r1) (State.get st r2)
  | _ => undef
  end.

Definition run_operator_node {env} (nd : node env) (st : State.t) : State.t :=
  match nd with
  | @Operator _ s n e wf => State.set_ref (Ref.Mk env s n wf) (eval st e) st
  | _ => st
  end.

Fixpoint run_operators {env} (nds : list (node env)) (st : State.t) : State.t :=
  match nds with
  | [] => st
  | (nd :: nds) => run_operators nds (run_operator_node nd st)
  end.

Definition run_init_node {env} (nd : node env) (st : State.t) : State.t :=
  match nd with
  | @StateInit _ s n e wf => State.set_ref (Ref.Mk env s n wf) (eval st e) st
  | _ => st
  end.

Fixpoint run_inits {env} (nds : list (node env)) (st : State.t) : State.t :=
  match nds with
  | [] => st
  | (nd :: nds) => run_inits nds (run_operator_node nd st)
  end.

Definition run_state_next_node {env} (st : State.t) (nd : node env) : State.t -> State.t :=
  match nd with
  | @StateNext _ s n e wf => State.set_ref (Ref.Mk env s n wf) (eval st e)
  | _ => (fun st' => st')
  end.

(* Collect all updates, and then run them all together, so that they
   don't influence eachother *)
Definition run_state_nexts {env} (nds : list (node env)) (st : State.t) : State.t :=
  fold_right Basics.apply st (map (run_state_next_node st) nds).
