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
      { varName : string
      ; varType : vtype
      ; varId : Z
      }.

  Record port :=
    MkPort
      { portId : Z
      ; portDirection : direction
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
