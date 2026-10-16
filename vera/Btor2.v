From Stdlib Require Import String.
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

From vera Require Import Common.
From vera Require Import Tactics.
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
Import SigTNotations.
Import EqNotations.
(* Local Open Scope monad_scope. *)

Module Sort <: UsualDecidableType.
  Inductive sort :=
  | BitVec (n : positive)
  (* | Array (idx elem : sort) *)
  .
  Definition t := sort.
  Include HasUsualEq <+ UsualIsEq.

  Definition eq_dec (x y : t) : {x = y} + {x <> y}.
  Proof. decide equality; apply Pos.eq_dec. Defined.

  Definition interp (s : sort) : Type :=
  match s with
  | BitVec n => BV.bitvector (Npos n)
  (* | Array idx elem => interp idx -> interp elem *)
  end.
End Sort.

Module Abstract.
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
  
  Record stateVar {env} := {
    stSort : Sort.t;
    stInit : option (expr stSort);
    stNext : option (expr stSort);
  }.
  
  Record var {env} := {
    varSort : Sort.t;
    varExpr : expr varSort;
  }.
  
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

Module Concrete.
  Import Sort (BitVec(* , Array *)).

  Variant nid := MkNid (id : positive).
  Variant sid := MkSid (id : positive).
  
  Variant operation : Type :=
  | UnsignedExtend (w : N) (e : nid)
  | SignedExtend (w : N) (e : nid)
  | Slice (hi lo : N) (e : nid)
  | Not (e : nid)
  | Inc (e : nid)
  | Dec (e : nid)
  | RedAnd (e : nid)
  | RedOr (e : nid)
  | RedXor (e : nid)
  | Iff (e1 e2 : nid)
  | Implies (e1 e2 : nid)
  | Eq (e1 e2 : nid)
  | NEq (e1 e2 : nid)
  | SignedGt (e1 e2 : nid)
  | UnsignedGt (e1 e2 : nid)
  | SignedGtE (e1 e2 : nid)
  | UnsignedGtE (e1 e2 : nid)
  | SignedLt (e1 e2 : nid)
  | UnsignedLt (e1 e2 : nid)
  | SignedLtE (e1 e2 : nid)
  | UnsignedLtE (e1 e2 : nid)
  | And (e1 e2 : nid)
  | NAnd (e1 e2 : nid)
  | Or (e1 e2 : nid)
  | NOr (e1 e2 : nid)
  | XOr (e1 e2 : nid)
  | XNor (e1 e2 : nid)
  | Rol (e1 e2 : nid)
  | Sll (e1 e2 : nid)
  | Sra (e1 e2 : nid)
  | Srl (e1 e2 : nid)
  | Add (e1 e2 : nid)
  | Mul (e1 e2 : nid)
  | SignedDiv (e1 e2 : nid)
  | UnsignedDiv (e1 e2 : nid)
  | SignedMod (e1 e2 : nid)
  (* No unsigned mod *)
  | SignedRem (e1 e2 : nid)
  | UnsignedRem (e1 e2 : nid)
  | Sub (e1 e2 : nid)
  | SignedAddOverflow (e1 e2 : nid)
  | UnsignedAddOverflow (e1 e2 : nid)
  | SignedDivOverflow (e1 e2 : nid)
  (* No unsigned div overflow *)
  | SignedMulOverflow (e1 e2 : nid)
  | UnsignedMulOverflow (e1 e2 : nid)
  | SignedSubOverflow (e1 e2 : nid)
  | UnsignedSubOverflow (e1 e2 : nid)
  | Concat (e1 : nid) (e2 : nid)
  (* | Read (arr : nid) (idx : nid) *)
  | ITE (cond : nid) (ifT ifF : nid)
  (* | Write (arr : nid) (idx : nid) (elem : nid) *)
  .
  
  Variant node :=
  | SortDecl (s : sid) (sort : Sort.t)
  | Operation (i : nid) (s : sid) (op : operation)
  | StateInit (i : nid) (s : sid) (state init : nid)
  | StateNext (i : nid) (s : sid) (state next : nid)
  | Bad (i : nid) (p : nid)
  | Constraint (i : nid) (p : nid)
  | Fair (i : nid) (p : nid)
  | Output (i : nid) (p : nid)
  | Justice (i : nid) (n : positive)
  (* | StateInit (r : ref) (o : operation)
   * | StateNext (r : ref) (o : operation)
   * | Operator (r : ref) (o : operation)
   * | Bad (e : expr (BitVec 1)) *)
  .
  
  (* Record btor := {
   *   btorEnv : environment;
   *   btorBody : list (@node btorEnv);
   * }.
   * 
   * Module State.
   *   Definition t {env} := forall (s : Sort.t) (r : Ref.t s), Sort.interp s.
   * 
   *   Definition set_ref {env s} (r : Ref.t s) (val : Sort.interp s) (st : t) : t :=
   *     fun s' r' =>
   *       match Sort.eq_dec s s' with
   *       | left E =>
   *         if String.eqb (Ref.refName r) (Ref.refName r')
   *         then rew [Sort.interp] E in val
   *         else st s' r'
   *       | right _ => st s' r'
   *       end.
   * 
   *   Definition get {env s} (st : t) (r : Ref.t s) :=
   *     st s r.
   * 
   *   Infix "@" := get (at level 5).
   * End State.
   * Import (notations) State.
   * 
   * Definition undef {s} : Sort.interp s. Admitted.
   * 
   * Fixpoint eval {env : environment} {s} (st : State.t) (e : expr s) : Sort.interp s :=
   *   match e with
   *   | Add lhs rhs => BV.bv_add (eval st lhs) (eval st rhs)
   *   | _ => undef
   *   end.
   * 
   * Fixpoint run {env} (nds : list node) (pending : State.t -> State.t) (st : State.t) : State.t :=
   *   match nds with
   *   | [] => pending st
   *   | (nd :: nds) => match nd with
   *     | @StateNext _ s n e wf =>
   *       run nds (State.set_ref (Ref.Mk env s n wf) (eval st e)) st
   *     | @Operator _ s n e wf => 
   *       run nds pending (State.set_ref (Ref.Mk env s n wf) (eval st e) st)
   *     | _ => run nds pending st
   *     end
   *   end.
   * 
   * Definition next {env} (nds : list node) (st : State.t) : State.t :=
   *   run nds (fun s => s) st. *)
End Concrete.
  
