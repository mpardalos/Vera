From vvequiv Require Import Common.
From vvequiv Require Import Bitvector.
Import Bitvector (bv, mkBV).

Require Import String.
Require Import ZArith.
Require Import BinNums.
Require Import Psatz.

Require Import List.
Import ListNotations.
From Coq Require Arith Lia Program.
From Coq Require Import Setoid.
From Equations Require Import Equations.

(* This module will be Verilog.Verilog. Redundant, but it is needed for extraction. See Extraction.v *)
Module Verilog.
  Inductive VType :=
    | Logic (hi lo : N).

  (* Equations Derive NoConfusionHom EqDec for VType. *)
  (* Next Obligation. *)
  (*   destruct x as [hi1 lo1]. *)
  (*   destruct y as [hi2 lo2]. *)
  (*   destruct (N.eq_dec hi1 hi2); destruct (N.eq_dec lo1 lo2); subst. *)
  (*   - left. reflexivity. *)
  (*   - right. intros contra. inversion contra. *)
  (*     auto. *)
  (*   - right. intros contra. inversion contra. *)
  (*     auto. *)
  (*   - right. intros contra. inversion contra. *)
  (*     auto. *)
  (* Defined. *)

  Definition vt_width (t : VType) : positive :=
    let (hi, lo) := t in
    let hi' := N.max hi lo in
    let lo' := N.min hi lo in
    Pos.of_succ_nat (N.to_nat (hi' - lo')).

  Definition vt_compatible (t1 t2 : VType) : Prop :=
    vt_width t1 = vt_width t2.

  Declare Scope vtype.
  Delimit Scope vtype with vtype.

  Notation "a ≈ b" := (vt_compatible a b) (at level 100) : vtype.

  Theorem vt_compatible_refl : forall t, (t ≈ t)%vtype.
  Proof. reflexivity. Qed.

  Theorem vt_compatible_symmetry : forall t1 t2,
      (t1 ≈ t2)%vtype ->
      (t2 ≈ t1)%vtype.
  Proof. intros. symmetry. assumption. Qed.

  Theorem vt_compatible_trans : forall t1 t2 t3,
      (t1 ≈ t2)%vtype ->
      (t2 ≈ t3)%vtype ->
      (t1 ≈ t3)%vtype.
  Proof. intros. transitivity (vt_width t2); assumption. Qed.

  Add Parametric Relation : VType vt_compatible
          reflexivity proved by vt_compatible_refl
          symmetry proved by vt_compatible_symmetry
          transitivity proved by vt_compatible_trans
      as vt_compatible_rel
  .

  Ltac crush_vtype :=
    repeat match goal with
      | t : VType |- _ => destruct t
      end;
    repeat match goal with
      | e : (_ ≈ _)%vtype |- _ => unfold "≈"%vtype in e; simpl in e
      end;
    match goal with
    | |- (_ ≈ _)%vtype => unfold "≈"%vtype; simpl
    end; try lia.

  Inductive BinaryOperator := Plus | Minus.

  Set Implicit Arguments.

  Structure VerilogKind :=
    { t :> Type
    ; bv_type : bv -> t
    ; types_compatible : t -> t -> Prop
    ; convert_bv : t -> bv -> bv
    ; convert_bv_correct : forall (ty : t) (v : bv),
        types_compatible (bv_type (convert_bv ty v)) ty
    }.

  Arguments bv_type {_} & _.
  Arguments convert_bv {_} & _.

  Program Definition Untyped : VerilogKind :=
    {| t := unit
    ; types_compatible _ _ := True
    ; bv_type _ := tt
    ; convert_bv _ v := v
    |}.

  Program Definition Typed : VerilogKind :=
    {| t := VType
    ; types_compatible t1 t2 := vt_width t1 = vt_width t2
    ; bv_type v :=
        Verilog.Logic (N.pred (N.pos (Bitvector.width v))) 0
    ; convert_bv ty v :=
        let width__ty := vt_width ty in
        Bitvector.convert width__ty v
    |}.
  Next Obligation. lia. Qed.

  Notation "a ∈ b" := (vt_compatible (@bv_type Typed a) b) (at level 100) : vtype.

  Inductive Expression (k : VerilogKind) : k -> Type :=
  | BinaryOp :
    forall {t}
      (op : BinaryOperator)
      (lhs rhs: Expression k t),
      Expression k t
  | Conversion :
    forall (from_type to_type : k)
      (operand: Expression k from_type),
      Expression k to_type
  | IntegerLiteral :
    forall (value : Bitvector.bv),
      Expression k (bv_type value)
  | VarRef :
    forall (type : k)
      (name : string),
      Expression k type
  .

  Definition SomeExpression := { k : VerilogKind & { t : k & Expression k t}}.
  Definition TypedExpression (t : VType) := Expression Typed t.
  Definition SomeTypedExpression := { t : VType & TypedExpression t }.
  Definition UntypedExpression := Expression Untyped tt.

  Notation UntypedVarRef name := (VarRef Untyped tt name).
  Notation TypedIntegerLiteral t v := (IntegerLiteral Typed t v).
  Notation UntypedIntegerLiteral v := (IntegerLiteral Untyped tt v).

  Set Strict Implicit.

  Inductive Statement (k : VerilogKind) :=
  | Block (body : list (Statement k))
  | BlockingAssign {t : k} (lhs rhs : Expression k t)
  | NonBlockingAssign {t : k} (lhs rhs : Expression k t)
  | If {t : k} (condition : Expression k t) (trueBranch falseBranch : (Statement k))
  .

  Inductive ModuleItem (k: VerilogKind) :=
  | ContinuousAssign {t : k} (lhs rhs : Expression k t)
  | AlwaysFF (body : Statement k)
  .

  Record Port :=
    MkPort
      { portDirection : port_direction
      ; portName : string
      }.

  (** Verilog modules *)
  Record VerilogModule (k: VerilogKind) :=
    MkVerilogModule
      { modName : string
      ; modPorts : list Port
      ; modVariables : StrMap.t VType
      ; modBody : list (ModuleItem k)
      }.

  Record VerilogState k (m : VerilogModule k) :=
    MkVerilogState
      { blockingState : StrMap.t bv
      (* ; nonblockingState : StrMap.t bv *)
      ; blockingState_wf : forall n t (v : bv),
          StrMap.MapsTo n t (modVariables m) ->
          exists v, StrMap.MapsTo n v blockingState /\ (v ∈ t)%vtype
      }
  .

  Unset Implicit Arguments.
  Unset Strict Implicit.

  Module TypedSemantics.
    Equations compute_bin_op {t} :
      BinaryOperator ->
      {v : bv | (v ∈ t)%vtype} ->
      {v : bv | (v ∈ t)%vtype} ->
      {v : bv | (v ∈ t)%vtype} :=
      (* TODO:
    Can/should we unify the behaviour of typed and untyped verilog here?
    - In typed verilog, we should have a proof that the operands are of the same width.
    - In untyped verilog, we need context sensitivity, adding conversions if needed
    - Perhaps we just need to split typed/untyped expression evaluation.
      The rest of the interpreter can be shared
       *)
      compute_bin_op Plus (exist _ v1 prf1) (exist _ v2 prf2) :=
        exist _ (Bitvector.bv_add_truncate v1 v2 _) _;
      (* TODO: Operations other than add *)
      compute_bin_op _ (exist _ v1 _) _ := exist _ v1 _
    .
    Next Obligation.
      unfold vt_compatible in *.
      simpl in *.
      rewrite <- prf1 in *; clear prf1.
      lia.
    Qed.
    Next Obligation.
      rewrite (Bitvector.bv_add_truncate_width v1 v2).
      trivial.
    Qed.

    Program Definition get_var {k} {m : VerilogModule k}
      (st : VerilogState m)
      (n : string)
      (name_present : StrMap.In n (blockingState st)) :
      { v : bv | StrMap.MapsTo n v (blockingState st) } :=
      (match StrMap.find n (blockingState st) as r return (StrMap.find n (blockingState st) = r -> { v : bv | StrMap.MapsTo n v (blockingState st) }) with
       | Some x => fun _ => (@exist _ _ x _)
       | None => fun eq => _
       end) eq_refl
    .
    Next Obligation.
      rewrite StrMapFacts.find_mapsto_iff.
      assumption.
    Qed.
    Next Obligation.
      rewrite <- StrMapFacts.not_find_in_iff in *.
      contradiction.
    Qed.

    Program Fixpoint eval_expression_typed {t : Typed} {m : VerilogModule Typed}
      (st : VerilogState m)
      (expr : Expression Typed t) :
      {v : bv | (@bv_type Typed v ≈ t)%vtype} :=
      match expr with
      | BinaryOp op lhs rhs =>
          compute_bin_op op
            (eval_expression_typed st lhs)
            (eval_expression_typed st rhs)
      | Conversion to_type operand =>
          let (val, prf) := (eval_expression_typed st operand) in
          exist _ (convert_bv to_type val) _
      | IntegerLiteral _ value =>
          exist _ value _
      | VarRef _ t n =>
          let (v, prf) := get_var st n _ in
          exist _ v _
      end
    .
    Next Obligation. crush_vtype. Qed.
    Next Obligation. reflexivity. Qed.
    Next Obligation. (* n is present *) Admitted.
    Next Obligation. (* VarRefs types match declaration, declarations match state *) Admitted.

  End TypedSemantics.

  Example examples : list (VerilogModule Untyped * VerilogModule Untyped) :=
    let l32 := Logic 31 0 in
    let l16 := Logic 15 0 in
    [
      ({|
          modName := "test1a";
          modPorts := [
            MkPort PortIn "in" ;
            MkPort PortOut "out"
          ];
          modVariables := StrMap.from_list [
                              ("in"%string, l32);
                              ("out"%string, l32)
                            ];
          modBody := [
            ContinuousAssign
              (UntypedVarRef "out")
              (BinaryOp Plus (UntypedVarRef "in") (IntegerLiteral _ (mkBV 0 32)))
          ];
        |},
        {|
          modName := "test1b";
          modPorts := [
            MkPort PortIn "in" ;
            MkPort PortOut "out"
          ];
          modVariables := StrMap.from_list [
                              ("in"%string, l32) ;
                              ("out"%string, l32)
                            ];
          modBody := [
            ContinuousAssign
              (UntypedVarRef "out")
              (UntypedVarRef "in")
          ];
        |}
      ) ;
      (***********************************************)
      ({|
          modName := "test2a";
          modPorts := [
            MkPort PortIn "in" ;
            MkPort PortOut "out"
          ];
          modVariables := StrMap.from_list [
                              ("in"%string, l32) ;
                              ("out"%string, l32)
                            ];
          modBody := [
            ContinuousAssign
              (UntypedVarRef "out")
              (BinaryOp Plus
                 (UntypedVarRef "in")
                 (IntegerLiteral _ (mkBV 1 32)))
          ];
        |},
        {|
          modName := "test2b";
          modPorts := [
            MkPort PortIn "in" ;
            MkPort PortOut "out"
          ];
          modVariables := StrMap.from_list [
                              ("in"%string, l32) ;
                              ("out"%string, l32)
                            ];
          modBody := [
            ContinuousAssign
              (UntypedVarRef "out")
              (BinaryOp Plus
                 (IntegerLiteral _ (mkBV 1 32))
                 (UntypedVarRef "in"))
          ];
        |}
      ) ;
      (***********************************************)
      ({|
          modName := "test3a";
          modPorts := [
            MkPort PortIn "in1" ;
            MkPort PortIn "in2" ;
            MkPort PortOut "out"
          ];
          modVariables := StrMap.from_list [
                              ("in1"%string, l32) ;
                              ("in2"%string, l32) ;
                              ("v"%string, l16) ;
                              ("out"%string, l32)
                            ];
          modBody := [
            ContinuousAssign
              (UntypedVarRef "v")
              (UntypedVarRef "in1");
            ContinuousAssign
              (UntypedVarRef "out")
              (BinaryOp Plus
                 (UntypedVarRef "v")
                 (BinaryOp Plus
                    (UntypedVarRef "in2")
                    (IntegerLiteral _ (mkBV 1 32))))
          ];
        |},
        {|
          modName := "test3b";
          modPorts := [
            MkPort PortIn "in1" ;
            MkPort PortIn "in2" ;
            MkPort PortOut "out"
          ];
          modVariables := StrMap.from_list [
                              ("in1"%string, l32) ;
                              ("in2"%string, l32) ;
                              ("out"%string, l32)
                            ];
          modBody := [
            ContinuousAssign
              (UntypedVarRef "out")
              (BinaryOp Plus
                 (UntypedVarRef "in2")
                 (BinaryOp Plus
                    (UntypedVarRef "in2")
                    (IntegerLiteral _ (mkBV 1 32))))
          ];
        |}
      )
    ].
End Verilog.
