From Stdlib Require Import ZArith.
From Stdlib Require Import String.
From Stdlib Require Import Psatz.
From Stdlib Require Import List.

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
From vera Require Import Bitvector.
From vera Require SMTQueries.

(* Import ListNotations. *)
Import MonadLetNotation.
Import SigTNotations.
(* Import EqNotations. *)
Local Open Scope monad_scope.

Implicit Types (env : Btor2.environment).

Definition transfer_sort (s : Btor2.Sort.t) : SMTLib.sort :=
  match s with
  | Btor2.Sort.BitVec w => SMTLib.Sort_BitVec w
  end.

Axiom undef_term : forall {s}, SMTLib.term (transfer_sort s).

Definition transfer_ref {env s} (r : Btor2.Ref.t s) : SMTLib.const_sym :=
  SMTLib.MkConstSym (Btor2.Ref.refName r) (transfer_sort s).

Definition bool_to_bv (t : SMTLib.term SMTLib.Sort_Bool) : SMTLib.term (SMTLib.Sort_BitVec 1) :=
  SMTLib.Term_ITE t (SMTLib.Term_BVLit _ (BV.ones 1)) (SMTLib.Term_BVLit _ (BV.zeros 1)).

Fixpoint transfer_expr {env s} (e : Btor2.expr s) : SMTLib.term (transfer_sort s) :=
  match e with
  | Btor2.ExprRef r => SMTLib.Term_Const (transfer_ref r)
  | Btor2.Constant bv => SMTLib.Term_BVLit _ bv
  | Btor2.Eq lhs rhs => bool_to_bv (SMTLib.Term_Eq (transfer_expr lhs) (transfer_expr rhs))
  | Btor2.Add lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVAdd (transfer_expr lhs) (transfer_expr rhs)
  | _ => undef_term
  end.

Definition transfer_combinational {env s} (name : string) (expr : Btor2.expr s) : SMTLib.term SMTLib.Sort_Bool :=
  SMTLib.Term_Eq
    (SMTLib.Term_Const (SMTLib.MkConstSym name (transfer_sort s)))
    (transfer_expr expr).

Definition transfer_state_init {env} (name : string) (stateVar : Btor2.stateVar) : option (SMTLib.term SMTLib.Sort_Bool) :=
  let* (init : Btor2.expr (Btor2.stSort stateVar)) := Btor2.stInit stateVar in
  Some
    (SMTLib.Term_Eq
      (SMTLib.Term_Const (SMTLib.MkConstSym name (transfer_sort (Btor2.stSort stateVar))))
      (transfer_expr init)).

Definition transfer_state_next {env} (name : string) (stateVar : Btor2.stateVar) : option (SMTLib.term SMTLib.Sort_Bool) :=
  let* (next : Btor2.expr (Btor2.stSort stateVar)) := Btor2.stNext stateVar in
  Some
    (SMTLib.Term_Eq
      (SMTLib.Term_Const (SMTLib.MkConstSym (name ++ "_next") (transfer_sort (Btor2.stSort stateVar))))
      (transfer_expr next)).

Definition transfer_prop {env} (prop : Btor2.expr (Btor2.Sort.BitVec 1)) : SMTLib.term SMTLib.Sort_Bool :=
  SMTLib.Term_Eq (transfer_expr prop) (SMTLib.Term_BVLit 1 (BV.ones 1)).

(* Check that all allowed initial states satisfy the required properties  *)
Definition query_init_state_good (b : Btor2.btor) : SMTQueries.query :=
  map (fun '(n, (s; e)) => transfer_combinational n e) (StrMap.elements (Btor2.btorCombinational b)) ++
  map_opt (uncurry transfer_state_init) (StrMap.elements (Btor2.btorState b)) ++
  map transfer_prop (Btor2.btorProps b)
  .

(* Look for a transition from a good state to a bad state *)
Definition query_violation (b : Btor2.btor) : SMTQueries.query :=
  map (fun '(n, (s; e)) => transfer_combinational n e) (StrMap.elements (Btor2.btorCombinational b)) ++
  map_opt (uncurry transfer_state_next) (StrMap.elements (Btor2.btorState b)) ++
  map transfer_prop (Btor2.btorProps b)
  (* TODO: ++ negation of btorProps evaluated on the next state's vars *)
  .
