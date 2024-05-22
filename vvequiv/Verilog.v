Require Import Common.

Require Import String.
Require Import ZArith.
Require Import BinNums.

Require Import List.
Import ListNotations.

(* This module will be Verilog.Verilog. Redundant, but it is needed for extraction. See Extraction.v *)
Module Verilog.
  Variant is_typed := Typed | Untyped.

  Inductive vtype := Logic : N -> N -> vtype.

  Inductive op := Plus | Minus.

  Definition if_typed (t : is_typed) (x: Type) :=
    match t with
    | Typed => x
    | Untyped => unit
    end
  .

  Definition if_typed_opt (t : is_typed) (x: Type) :=
    match t with
    | Typed => x
    | Untyped => option x
    end
  .


  Inductive expression (t: is_typed) :=
  | BinaryOp : if_typed t vtype -> op -> expression t -> expression t -> expression t
  | Conversion : if_typed t vtype -> expression t -> expression t
  | IntegerLiteral : positive -> N -> expression t
  | NamedExpression : if_typed t vtype -> string -> expression t
  .

  Record variable (t: is_typed) :=
    MkVariable
      { varType : if_typed_opt t vtype
      ; varName : string
      }.

  Check varType.

  Arguments varType [_] _.
  Arguments varName [_] _.

  Record port :=
    MkPort
      { portDirection : port_direction
      ; portName : string
      }.


  Inductive module_item (t: is_typed) : Type :=
  | ContinuousAssign : expression t -> expression t -> module_item t
  .

  (** Verilog modules *)
  Record vmodule (t : is_typed) : Type :=
    MkMod
      { modName : string
      ; modPorts : list port
      ; modVariables : list (variable t)
      ; modBody : list (module_item t)
      }.

  Arguments modName [_] _.
  Arguments modPorts [_] _.
  Arguments modVariables [_] _.
  Arguments modBody [_] _.

  Example untyped_examples : list (Verilog.vmodule Untyped * Verilog.vmodule Untyped) :=
    let l32 := Logic 31 0 in
    [
      (MkMod Untyped
          "test1a"
          [
            MkPort PortIn "in" ;
            MkPort PortOut "out"
          ]
          [
            MkVariable Untyped (Some l32) "in" ;
            MkVariable Untyped (Some l32) "out"
          ]
          [
            ContinuousAssign Untyped
              (NamedExpression Untyped tt "out")
              (BinaryOp Untyped tt Plus (NamedExpression Untyped tt "in") (IntegerLiteral Untyped 32 0))
          ]
        ,
        {|
          modName := "test1b";
          modPorts := [
            MkPort PortIn "in" ;
            MkPort PortOut "out"
          ];
          modVariables := [
            MkVariable Untyped (Some l32) "in" ;
            MkVariable Untyped (Some l32) "out"
          ];
          modBody := [
            ContinuousAssign
              Untyped
              (NamedExpression Untyped tt "out")
              (NamedExpression Untyped tt "in")
          ];
        |}
      )
    ]
  .

  Example examples : list (Verilog.vmodule Typed * Verilog.vmodule Typed) :=
    let l32 := Logic 31 0 in
    [
      ({|
          modName := "test1a";
          modPorts := [
            MkPort PortIn "in" ;
            MkPort PortOut "out"
          ];
          modVariables := [
            MkVariable Typed l32 "in" ;
            MkVariable Typed l32 "out"
          ];
          modBody := [
            ContinuousAssign
              Typed
              (NamedExpression Typed l32 "out")
              (BinaryOp Typed l32 Plus (NamedExpression Typed l32 "in") (IntegerLiteral Typed 32 0))
          ];
        |},
        {|
          modName := "test1b";
          modPorts := [
            MkPort PortIn "in" ;
            MkPort PortOut "out"
          ];
          modVariables := [
            MkVariable Typed l32 "in" ;
            MkVariable Typed l32 "out"
          ];
          modBody := [
            ContinuousAssign
              Typed
              (NamedExpression Typed l32 "out")
              (NamedExpression Typed l32 "in")
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
            MkVariable Typed l32 "in" ;
            MkVariable Typed l32 "out"
          ];
          modBody := [
            ContinuousAssign
              Typed
              (NamedExpression Typed l32 "out")
              (BinaryOp Typed l32 Plus
                 (NamedExpression Typed l32 "in")
                 (IntegerLiteral Typed 32 1))
          ];
        |},
        {|
          modName := "test2b";
          modPorts := [
            MkPort PortIn "in" ;
            MkPort PortOut "out"
          ];
          modVariables := [
            MkVariable Typed l32 "in" ;
            MkVariable Typed l32 "out"
          ];
          modBody := [
            ContinuousAssign
              Typed
              (NamedExpression Typed l32 "out")
              (BinaryOp Typed l32 Plus
                 (IntegerLiteral Typed 32 1)
                 (NamedExpression Typed l32 "in"))
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
            MkVariable Typed l32 "in1" ;
            MkVariable Typed l32 "in2" ;
            MkVariable Typed l32 "out"
          ];
          modBody := [
            ContinuousAssign
              Typed
              (NamedExpression Typed l32 "out")
              (BinaryOp Typed l32 Plus
                 (NamedExpression Typed l32 "in1")
                 (BinaryOp Typed l32 Plus
                    (NamedExpression Typed l32 "in2")
                    (IntegerLiteral Typed 32 1)))
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
            MkVariable Typed l32 "in1" ;
            MkVariable Typed l32 "in2" ;
            MkVariable Typed l32 "out"
          ];
          modBody := [
            ContinuousAssign
              Typed
              (NamedExpression Typed l32 "out")
              (BinaryOp Typed l32 Plus
                 (NamedExpression Typed l32 "in2")
                 (BinaryOp Typed l32 Plus
                    (NamedExpression Typed l32 "in2")
                    (IntegerLiteral Typed 32 1)))
          ];
        |}
      )
    ].
End Verilog.
