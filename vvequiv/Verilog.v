From vvequiv Require Import Common.
From vvequiv Require Import Bitvector.
Import Bitvector (bv).

Require Import String.
Require Import ZArith.
Require Import BinNums.

Require Import List.
Import ListNotations.
From Coq Require Arith Lia Program.
From Equations Require Import Equations.

(* This module will be Verilog.Verilog. Redundant, but it is needed for extraction. See Extraction.v *)
Module Verilog.
  Inductive vtype := Logic : N -> N -> vtype.

  Equations Derive NoConfusionHom EqDec for vtype.
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

  Inductive expression :=
  | BinaryOp : BinaryOperator -> expression -> expression -> expression
  | IntegerLiteral : positive -> N -> expression
  | NamedExpression : string -> expression
  .

  Record variable :=
    MkVariable
      { varType : vtype
      ; varName : string
      }.

  Record port :=
    MkPort
      { portDirection : port_direction
      ; portName : string
      }.

  Inductive module_item : Set :=
  | ContinuousAssign : expression -> expression -> module_item
  .

  (** Verilog modules *)
  Record vmodule : Set :=
    MkMod
      { modName : string
      ; modPorts : list port
      ; modVariables : list variable
      ; modBody : list module_item
      }.

  Example examples : list (vmodule * vmodule) :=
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
            MkVariable l32 "in" ;
            MkVariable l32 "out"
          ];
          modBody := [
            ContinuousAssign
              (NamedExpression "out")
              (BinaryOp Plus (NamedExpression "in") (IntegerLiteral 32 0))
          ];
        |},
        {|
          modName := "test1b";
          modPorts := [
            MkPort PortIn "in" ;
            MkPort PortOut "out"
          ];
          modVariables := [
            MkVariable l32 "in" ;
            MkVariable l32 "out"
          ];
          modBody := [
            ContinuousAssign
              (NamedExpression "out")
              (NamedExpression "in")
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
            MkVariable l32 "in" ;
            MkVariable l32 "out"
          ];
          modBody := [
            ContinuousAssign
              (NamedExpression "out")
              (BinaryOp Plus
                 (NamedExpression "in")
                 (IntegerLiteral 32 1))
          ];
        |},
        {|
          modName := "test2b";
          modPorts := [
            MkPort PortIn "in" ;
            MkPort PortOut "out"
          ];
          modVariables := [
            MkVariable l32 "in" ;
            MkVariable l32 "out"
          ];
          modBody := [
            ContinuousAssign
              (NamedExpression "out")
              (BinaryOp Plus
                 (IntegerLiteral 32 1)
                 (NamedExpression "in"))
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
            MkVariable l32 "in1" ;
            MkVariable l32 "in2" ;
            MkVariable l16 "v" ;
            MkVariable l32 "out"
          ];
          modBody := [
            ContinuousAssign
              (NamedExpression "v")
              (NamedExpression "in1");
            ContinuousAssign
              (NamedExpression "out")
              (BinaryOp Plus
                 (NamedExpression "v")
                 (BinaryOp Plus
                    (NamedExpression "in2")
                    (IntegerLiteral 32 1)))
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
            MkVariable l32 "in1" ;
            MkVariable l32 "in2" ;
            MkVariable l32 "out"
          ];
          modBody := [
            ContinuousAssign
              (NamedExpression "out")
              (BinaryOp Plus
                 (NamedExpression "in2")
                 (BinaryOp Plus
                    (NamedExpression "in2")
                    (IntegerLiteral 32 1)))
          ];
        |}
      )
    ].
End Verilog.

Module TypedVerilog.
  Export Verilog(vtype(..), BinaryOperator(..), variable(..), port(..)).

  (* Equations bv_type (idx : Type) (bv : ) *)
  Structure VerilogKind :=
    { t :> Type
    ; bv_type : Bitvector.bv -> t
    }.

  Definition vtype_kind : VerilogKind :=
    {| t := vtype
    ; bv_type v := Verilog.Logic (N.pred (N.pos (Bitvector.width v))) 0
    |}.

  Definition unit_kind : VerilogKind :=
    {| t := unit
    ; bv_type _ := tt
    |}.

  Inductive Expression {kind : VerilogKind} : kind -> Type :=
  | BinaryOp :
    forall {t}
      (op : BinaryOperator)
      (lhs rhs: Expression t),
      Expression t
  | Conversion :
    forall (from_type to_type : kind)
      (operand: Expression from_type),
      Expression to_type
  | IntegerLiteral :
    forall (value : Bitvector.bv),
      Expression (bv_type kind value)
  | NamedExpression :
    forall (type : kind)
      (name : string),
      Expression type
  .

  Definition SomeExpression := { k : VerilogKind & { t : k & Expression t}}.
  Definition TypedExpression (t : vtype) := @Expression vtype_kind t.
  Definition SomeTypedExpression := { t : vtype & TypedExpression t }.
  Definition UntypedExpression := @Expression unit_kind tt.

  Inductive Statement :=
  | Block (body : list Statement)
  | BlockingAssign {k : VerilogKind} {t : k} (lhs rhs : Expression t)
  | NonBlockingAssign {k : VerilogKind} {t : k} (lhs rhs : Expression t)
  | If {k : VerilogKind} {t : k} (condition : Expression t) (trueBranch falseBranch : Statement)
  .

  Inductive ModuleItem :=
  | ContinuousAssign {k : VerilogKind} {t : k} (lhs rhs : Expression t)
  | AlwaysFF (body : Statement)
  .

  (** Verilog modules *)
  Record vmodule :=
    MkMod
      { modName : string
      ; modPorts : list port
      ; modVariables : list variable
      ; modBody : list ModuleItem
      }.
End TypedVerilog.
