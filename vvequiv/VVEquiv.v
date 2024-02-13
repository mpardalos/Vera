Require Import String.
Require Import ZArith.
Require Import BinNums.

Require Import List.
Import ListNotations.

Module Verilog.
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
      |}
    ].
End Verilog.

Module Netlist.
  Inductive nltype := Logic : Z -> nltype.

  (* Inductive register :=. *)

  Record constant :=
    Constant
      { constWidth : positive
      ; constValue : positive
      }.

  (** These are not registers, just names used to connect the netlist graph *)
  Record variable :=
    Var
      { varType : nltype
      ; varName : Z
      }.

  Inductive input :=
  | InVar : variable -> input
  | InConstant : constant -> input
  .

  Inductive output :=
  | OutVar : variable -> output
  .

  Inductive cell :=
  | Add : output -> input -> input -> cell
  | Subtract : output -> input -> input -> cell
  | Id : output -> input -> cell
  .

  Record circuit :=
    Circuit
      { circuitName : string
      ; circuitVariables : list variable
      ; circuitCells : list cell
      }.

  Example examples : list circuit :=
    let v0 := Var (Logic 32) 0 in
    let v1 := Var (Logic 32) 1 in
    let v2 := Var (Logic 32) 2 in
    [ {| circuitName := "test1";
        circuitVariables := [v0; v1];
        circuitCells := [Id (OutVar v0) (InVar v1)]
      |}
      ;
      {| circuitName := "test2";
        circuitVariables := [v0; v1; v2];
        circuitCells := [Add (OutVar v0) (InVar v1) (InVar v2)]
      |}
    ].
End Netlist.
