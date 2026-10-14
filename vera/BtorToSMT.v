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
Import EqNotations.
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

Definition bv_to_bool (t : SMTLib.term (SMTLib.Sort_BitVec 1)) : SMTLib.term SMTLib.Sort_Bool :=
  SMTLib.Term_Eq t (SMTLib.Term_BVLit _ (BV.ones 1)).


Fixpoint transfer_expr {env s} (e : Btor2.expr s) : SMTLib.term (transfer_sort s) :=
  match e with
  | Btor2.ExprRef r => SMTLib.Term_Const (transfer_ref r)
  | Btor2.Constant bv => SMTLib.Term_BVLit _ bv
  | Btor2.Eq lhs rhs => bool_to_bv (SMTLib.Term_Eq (transfer_expr lhs) (transfer_expr rhs))
  | Btor2.Add lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVAdd (transfer_expr lhs) (transfer_expr rhs)
  | Btor2.Slice hi lo wf e => SMTLib.Term_BVExtract hi lo (proj1 wf) (transfer_expr e)
  | Btor2.Not e => SMTLib.Term_BVUnaryOp SMTLib.BVNot (transfer_expr e)
  | @Btor2.UnsignedExtend _ m w e =>
    rew [fun n => SMTLib.term (SMTLib.Sort_BitVec n)] (N.add_comm w m) in
      SMTLib.Term_BVConcat (SMTLib.Term_BVLit _ (BV.zeros w)) (transfer_expr e)
  | _ => undef_term
  end.

Definition transfer_combinational {env} (node : Btor2.node) : option (SMTLib.term SMTLib.Sort_Bool) :=
  match node with
  | @Btor2.Operator _ s n e wf =>
    Some (SMTLib.Term_Eq
      (SMTLib.Term_Const (SMTLib.MkConstSym n (transfer_sort s)))
      (transfer_expr e))
  | _ => None
  end.

Definition transfer_state_init {env} (node : Btor2.node) : option (SMTLib.term SMTLib.Sort_Bool) :=
  match node with
  | @Btor2.StateInit _ s n e wf =>
    Some (SMTLib.Term_Eq
      (SMTLib.Term_Const (SMTLib.MkConstSym n (transfer_sort s)))
      (transfer_expr e))
  | _ => None
  end.

Definition transfer_state_next {env} (node : Btor2.node) : option (SMTLib.term SMTLib.Sort_Bool) :=
  match node with
  | @Btor2.StateNext _ s n e wf =>
    Some (SMTLib.Term_Eq
      (SMTLib.Term_Const (SMTLib.MkConstSym (n ++ "_next") (transfer_sort s)))
      (transfer_expr e))
  | _ => None
  end.

(* Translates the property without flipping. `bad P` becomes just `P` *)
Definition transfer_prop {env} (node : Btor2.node) : option (SMTLib.term SMTLib.Sort_Bool) :=
  match node with
  | Btor2.Bad p => Some (bv_to_bool (transfer_expr p))
  | _ => None
  end.

(* Look for an bad permitted initial state *)
Definition query_init_state_bad (b : Btor2.btor) : SMTQueries.query :=
  map_opt transfer_state_init (Btor2.btorBody b) ++
  map_opt transfer_combinational (Btor2.btorBody b) ++
  map_opt transfer_prop (Btor2.btorBody b).

(* Look for a transition from a good state to a bad state *)
Definition query_inductive_violation (b : Btor2.btor) : SMTQueries.query :=
  map_opt transfer_state_next (Btor2.btorBody b) ++
  map_opt transfer_combinational (Btor2.btorBody b) ++
  map_opt transfer_prop (Btor2.btorBody b) (* FIXME: Evaluate on next state *).
