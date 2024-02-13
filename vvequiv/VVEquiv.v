Require Import String.
Require Import ZArith.

Module Verilog.
  Inductive vtype := Logic : Z -> Z -> vtype.

  Inductive direction := In | Out.

  Inductive op := Plus | Minus.

  Inductive expression :=
  | BinaryOp : op -> expression -> expression -> expression
  | Conversion : vtype -> expression -> expression
  | IntegerLiteral : Z -> expression
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
End Verilog.

Require Import List.
Import ListNotations.
Import Verilog.

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
             (IntegerLiteral 1))
      ];
    |}
  ].
