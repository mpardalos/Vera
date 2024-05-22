Require Import Common.

Require Import String.
Require Import ZArith.
Require Import BinNums.

Require Import List.
Import ListNotations.

(* This module will be Verilog.Verilog. Redundant, but it is needed for extraction. See Extraction.v *)
Module Verilog.
  Inductive vtype := Logic : N -> N -> vtype.

  Inductive op := Plus | Minus.

  Inductive expression :=
  | BinaryOp : vtype -> op -> expression -> expression -> expression
  | Conversion : vtype -> expression -> expression
  | IntegerLiteral : positive -> N -> expression
  | NamedExpression : vtype -> string -> expression
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

  Example examples : list (Verilog.vmodule * Verilog.vmodule) :=
    let l32 := Logic 31 0 in
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
              (NamedExpression l32 "out")
              (BinaryOp l32 Plus (NamedExpression l32 "in") (IntegerLiteral 32 0))
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
              (NamedExpression l32 "out")
              (NamedExpression l32 "in")
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
              (NamedExpression l32 "out")
              (BinaryOp l32 Plus
                 (NamedExpression l32 "in")
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
              (NamedExpression l32 "out")
              (BinaryOp l32 Plus
                 (IntegerLiteral 32 1)
                 (NamedExpression l32 "in"))
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
            MkVariable l32 "out"
          ];
          modBody := [
            ContinuousAssign
              (NamedExpression l32 "out")
              (BinaryOp l32 Plus
                 (NamedExpression l32 "in1")
                 (BinaryOp l32 Plus
                    (NamedExpression l32 "in2")
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
              (NamedExpression l32 "out")
              (BinaryOp l32 Plus
                 (NamedExpression l32 "in2")
                 (BinaryOp l32 Plus
                    (NamedExpression l32 "in2")
                    (IntegerLiteral 32 1)))
          ];
        |}
      )
    ].
End Verilog.
