Require Import String.
Require Import ZArith.

Module Verilog.
  Inductive vtype :=
  | Reg : Z -> Z -> vtype
  | Logic : Z -> Z -> vtype
  .

  Inductive op := Plus | Minus.

  Inductive expression :=
  | BinaryOp : op -> expression -> expression -> expression
  | Conversion : vtype -> expression -> expression
  | IntegerLiteral : Z -> expression
  .
End Verilog.
