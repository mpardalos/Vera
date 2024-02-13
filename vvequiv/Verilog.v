Require Import String.
Require Import ZArith.
Require Import BinNums.

Require Import List.
Import ListNotations.

Inductive vtype := Logic : Z -> Z -> vtype.

Inductive direction := In | Out.

Inductive op := Plus | Minus.

Inductive expression :=
| BinaryOp : op -> expression -> expression -> expression
| Conversion : vtype -> expression -> expression
| IntegerLiteral : Z -> Z -> expression
| NamedExpression : string -> expression
.

Record variable :=
  MkVariable
    { varType : vtype
    ; varName : string
    }.

Record port :=
  MkPort
    { portDirection : direction
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

Example examples : list Verilog.vmodule := [
    {|
      modName := "test1";
      modPorts := [
        MkPort In "in" ;
        MkPort Out "out"
      ];
      modVariables := [
        MkVariable (Logic 31 0) "in" ;
        MkVariable (Logic 31 0) "out"
      ];
      modBody := [
        ContinuousAssign
          (NamedExpression "out")
          (NamedExpression "in")
      ];
    |} ;
    (***********************************************)
    {|
      modName := "test2";
      modPorts := [
        MkPort In "in" ;
        MkPort Out "out"
      ];
      modVariables := [
        MkVariable (Logic 31 0) "in" ;
        MkVariable (Logic 31 0) "out"
      ];
      modBody := [
        ContinuousAssign
          (NamedExpression "out")
          (BinaryOp Plus
             (NamedExpression "in")
             (IntegerLiteral 32 1))
      ];
    |} ;
    (***********************************************)
    {|
      modName := "test3";
      modPorts := [
        MkPort In "in1" ;
        MkPort In "in2" ;
        MkPort Out "out"
      ];
      modVariables := [
        MkVariable (Logic 31 0) "in1" ;
        MkVariable (Logic 31 0) "in2" ;
        MkVariable (Logic 31 0) "out"
      ];
      modBody := [
        ContinuousAssign
          (NamedExpression "out")
          (BinaryOp Plus
             (NamedExpression "in1")
             (BinaryOp Plus
                (NamedExpression "in2")
                (IntegerLiteral 32 1)))
      ];
    |}
  ].
