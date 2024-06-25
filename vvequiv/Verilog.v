From vvequiv Require Import Common.
From vvequiv Require Import Bitvector.
Import Bitvector (bv, mkBV).

Require Import String.
Require Import ZArith.
Require Import BinNums.

Require Import List.
Import ListNotations.
From Coq Require Arith Lia Program.
From Equations Require Import Equations.

(* This module will be Verilog.Verilog. Redundant, but it is needed for extraction. See Extraction.v *)
Module Verilog.
  Set Implicit Arguments.
  Set Strict Implicit.

  Inductive VType := Logic : N -> N -> VType.

  Equations Derive NoConfusionHom EqDec for VType.
  Next Obligation.
    destruct x as [hi1 lo1].
    destruct y as [hi2 lo2].
    destruct (N.eq_dec hi1 hi2); destruct (N.eq_dec lo1 lo2); subst.
    - left. reflexivity.
    - right. intros contra. inversion contra.
      auto.
    - right. intros contra. inversion contra.
      auto.
    - right. intros contra. inversion contra.
      auto.
  Defined.

  Inductive BinaryOperator := Plus | Minus.

  (* Equations bv_type (idx : Type) (bv : ) *)
  Structure VerilogKind :=
    { t :> Type
    ; bv_type : Bitvector.bv -> t
    }.

  Definition Typed : VerilogKind :=
    {| t := VType
    ; bv_type v := Verilog.Logic (N.pred (N.pos (Bitvector.width v))) 0
    |}.

  Definition Untyped : VerilogKind :=
    {| t := unit
    ; bv_type _ := tt
    |}.

  Arguments bv_type {_} & _.

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

  Record Var :=
    MkVar
      { varType : VType
      ; varName : string
      }.

  (** Verilog modules *)
  Record VerilogModule (k: VerilogKind) :=
    MkVerilogModule
      { modName : string
      ; modPorts : list Port
      ; modVariables : list Var
      ; modBody : list (ModuleItem k)
      }.

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
          modVariables := [
            MkVar l32 "in" ;
            MkVar l32 "out"
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
          modVariables := [
            MkVar l32 "in" ;
            MkVar l32 "out"
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
          modVariables := [
            MkVar l32 "in" ;
            MkVar l32 "out"
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
          modVariables := [
            MkVar l32 "in" ;
            MkVar l32 "out"
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
          modVariables := [
            MkVar l32 "in1" ;
            MkVar l32 "in2" ;
            MkVar l16 "v" ;
            MkVar l32 "out"
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
          modVariables := [
            MkVar l32 "in1" ;
            MkVar l32 "in2" ;
            MkVar l32 "out"
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
