From Stdlib Require Import BinNat.
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
Module Btor2 := Btor2.Abstract.
From vera Require Import Bitvector.
From vera Require SMTQueries.

(* Import ListNotations. *)
Import MonadLetNotation.
Import SigTNotations.
Import EqNotations.
Local Open Scope monad_scope.

Coercion Npos : positive >-> N.

Implicit Types (env : Btor2.environment).

Arguments N.add _ _ : simpl never.
Arguments N.sub _ _ : simpl never.

Definition transfer_sort (s : Btor2.Sort.t) : SMTLib.sort :=
  match s with
  | Btor2.Sort.BitVec w => SMTLib.Sort_BitVec (Npos w)
  end.

Axiom undef_term : forall {s}, SMTLib.term (transfer_sort s).

Definition bool_to_bv (t : SMTLib.term SMTLib.Sort_Bool) : SMTLib.term (SMTLib.Sort_BitVec 1) :=
  SMTLib.Term_ITE t (SMTLib.Term_BVLit _ (BV.ones 1)) (SMTLib.Term_BVLit _ (BV.zeros 1)).

Definition bv_to_bool (t : SMTLib.term (SMTLib.Sort_BitVec 1)) : SMTLib.term SMTLib.Sort_Bool :=
  SMTLib.Term_Eq t (SMTLib.Term_BVLit _ (BV.ones 1)).

Section transfer.
  Variable name_map : string -> string.

  Definition transfer_ref {env s} (r : Btor2.Ref.t s) : SMTLib.const_sym :=
    SMTLib.MkConstSym (name_map (Btor2.Ref.refName r)) (transfer_sort s).

  #[program]
  Fixpoint transfer_expr {env s} (e : Btor2.expr s) : SMTLib.term (transfer_sort s) :=
    match e in Btor2.expr t return SMTLib.term (transfer_sort t) with
    | Btor2.ExprRef r => SMTLib.Term_Const (transfer_ref r)
    | Btor2.Constant bv => SMTLib.Term_BVLit _ bv
    | Btor2.Eq lhs rhs => bool_to_bv (SMTLib.Term_Eq (transfer_expr lhs) (transfer_expr rhs))
    | Btor2.NEq lhs rhs => bool_to_bv (SMTLib.Term_Not (SMTLib.Term_Eq (transfer_expr lhs) (transfer_expr rhs)))
    | Btor2.Iff lhs rhs => bool_to_bv (SMTLib.Term_Eq (transfer_expr lhs) (transfer_expr rhs))
    | Btor2.Implies lhs rhs => bool_to_bv (SMTLib.Term_Or
        (SMTLib.Term_Not (bv_to_bool (transfer_expr lhs))) (bv_to_bool (transfer_expr rhs)))
    | Btor2.UnsignedLt lhs rhs => bool_to_bv (SMTLib.Term_BVUlt (transfer_expr lhs) (transfer_expr rhs))
    | Btor2.UnsignedGt lhs rhs => bool_to_bv (SMTLib.Term_BVUlt (transfer_expr rhs) (transfer_expr lhs))
    | Btor2.UnsignedLtE lhs rhs => bool_to_bv (SMTLib.Term_Not (SMTLib.Term_BVUlt (transfer_expr rhs) (transfer_expr lhs)))
    | Btor2.UnsignedGtE lhs rhs => bool_to_bv (SMTLib.Term_Not (SMTLib.Term_BVUlt (transfer_expr lhs) (transfer_expr rhs)))
    | Btor2.Add lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVAdd (transfer_expr lhs) (transfer_expr rhs)
    | Btor2.Sub lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVAdd
        (transfer_expr lhs) (SMTLib.Term_BVUnaryOp SMTLib.BVNeg (transfer_expr rhs))
    | Btor2.Mul lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVMul (transfer_expr lhs) (transfer_expr rhs)
    | Btor2.UnsignedDiv lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVUDiv (transfer_expr lhs) (transfer_expr rhs)
    | Btor2.UnsignedRem lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVURem (transfer_expr lhs) (transfer_expr rhs)
    | Btor2.And lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVAnd (transfer_expr lhs) (transfer_expr rhs)
    | Btor2.Or lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVOr (transfer_expr lhs) (transfer_expr rhs)
    | Btor2.XOr lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVXor (transfer_expr lhs) (transfer_expr rhs)
    | Btor2.NAnd lhs rhs => SMTLib.Term_BVUnaryOp SMTLib.BVNot
        (SMTLib.Term_BVBinOp SMTLib.BVAnd (transfer_expr lhs) (transfer_expr rhs))
    | Btor2.NOr lhs rhs => SMTLib.Term_BVUnaryOp SMTLib.BVNot
        (SMTLib.Term_BVBinOp SMTLib.BVOr (transfer_expr lhs) (transfer_expr rhs))
    | Btor2.XNor lhs rhs => SMTLib.Term_BVUnaryOp SMTLib.BVNot
        (SMTLib.Term_BVBinOp SMTLib.BVXor (transfer_expr lhs) (transfer_expr rhs))
    | Btor2.Sll lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVShl (transfer_expr lhs) (transfer_expr rhs)
    | Btor2.Srl lhs rhs => SMTLib.Term_BVBinOp SMTLib.BVShr (transfer_expr lhs) (transfer_expr rhs)
    | Btor2.Concat lhs rhs => SMTLib.Term_BVConcat (transfer_expr lhs) (transfer_expr rhs)
    | Btor2.ITE cond ifT ifF => SMTLib.Term_ITE
        (bv_to_bool (transfer_expr cond)) (transfer_expr ifT) (transfer_expr ifF)
    | Btor2.Slice hi lo wf e =>
      rew [fun w => SMTLib.term (SMTLib.Sort_BitVec w)] _ in SMTLib.Term_BVExtract hi lo (proj1 wf) (transfer_expr e)
    | Btor2.Not e => SMTLib.Term_BVUnaryOp SMTLib.BVNot (transfer_expr e)
    | @Btor2.Inc _ n e => SMTLib.Term_BVBinOp SMTLib.BVAdd
        (transfer_expr e) (SMTLib.Term_BVLit _ (BV.bv_neg (BV.ones n)))
    | @Btor2.Dec _ n e => SMTLib.Term_BVBinOp SMTLib.BVAdd
        (transfer_expr e) (SMTLib.Term_BVLit _ (BV.ones n))
    | @Btor2.RedAnd _ n e => bool_to_bv
        (SMTLib.Term_Eq (transfer_expr e) (SMTLib.Term_BVLit _ (BV.ones n)))
    | @Btor2.RedOr _ n e => bool_to_bv
        (SMTLib.Term_Not (SMTLib.Term_Eq (transfer_expr e) (SMTLib.Term_BVLit _ (BV.zeros n))))
    | @Btor2.UnsignedExtend _ m w e =>
        SMTLib.Term_BVConcat (SMTLib.Term_BVLit _ (BV.zeros (Npos w))) (transfer_expr e)
    (* These operations have no direct counterpart in the current SMT AST. *)
    | Btor2.SignedExtend _ _ | Btor2.RedXor _
    | Btor2.SignedGt _ _ | Btor2.SignedGtE _ _
    | Btor2.SignedLt _ _ | Btor2.SignedLtE _ _
    | Btor2.Rol _ _ | Btor2.Sra _ _
    | Btor2.SignedDiv _ _
    | Btor2.SignedMod _ _ | Btor2.SignedRem _ _
    | Btor2.SignedAddOverflow _ _ | Btor2.UnsignedAddOverflow _ _
    | Btor2.SignedDivOverflow _ _
    | Btor2.SignedMulOverflow _ _ | Btor2.UnsignedMulOverflow _ _
    | Btor2.SignedSubOverflow _ _ | Btor2.UnsignedSubOverflow _ _ => undef_term
    end.
  Next Obligation. lia. Qed.
  
  Definition transfer_combinational {env} (node : Btor2.node) : option (SMTLib.term SMTLib.Sort_Bool) :=
    match node with
    | @Btor2.Operator _ s n e wf =>
      Some (SMTLib.Term_Eq
        (SMTLib.Term_Const (SMTLib.MkConstSym n (transfer_sort s)))
        (transfer_expr e))
    | _ => None
    end.
  
  (* Translates the property without flipping. `bad P` becomes just `P` *)
  Definition transfer_prop {env} (node : Btor2.node) : option (SMTLib.term SMTLib.Sort_Bool) :=
    match node with
    | Btor2.Bad p => Some (bv_to_bool (transfer_expr p))
    | _ => None
    end.
End transfer.

Definition map_current (n : string) := n.
Definition map_next (n : string) := (n ++ "_next")%string.

Definition transfer_state_init {env} (node : Btor2.node) : option (SMTLib.term SMTLib.Sort_Bool) :=
  match node with
  | @Btor2.StateInit _ s n e wf =>
    Some (SMTLib.Term_Eq
      (SMTLib.Term_Const (SMTLib.MkConstSym (map_current n) (transfer_sort s)))
      (transfer_expr map_current e))
  | _ => None
  end.

Definition transfer_state_next {env} (node : Btor2.node) : option (SMTLib.term SMTLib.Sort_Bool) :=
  match node with
  | @Btor2.StateNext _ s n e wf =>
    Some (SMTLib.Term_Eq
      (SMTLib.Term_Const (SMTLib.MkConstSym (map_next n) (transfer_sort s)))
      (transfer_expr map_current e))
  | _ => None
  end.

(* Look for a bad permitted initial state *)
Definition query_init_state_bad (b : Btor2.btor) : SMTQueries.query :=
  map_opt transfer_state_init (Btor2.btorBody b) ++
  map_opt (transfer_combinational map_current) (Btor2.btorBody b) ++
  map_opt (transfer_prop map_current) (Btor2.btorBody b).

(* Look for a transition from a good state to a bad state *)
Definition query_inductive_violation (b : Btor2.btor) : SMTQueries.query :=
  map_opt (transfer_combinational map_current) (Btor2.btorBody b) ++
  map_opt transfer_state_next (Btor2.btorBody b) ++
  (map SMTLib.Term_Not (map_opt (transfer_prop map_current) (Btor2.btorBody b))) ++
  map_opt (transfer_prop map_next) (Btor2.btorBody b).
