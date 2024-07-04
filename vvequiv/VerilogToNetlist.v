Require Import Verilog.
Require Import Netlist.
Require Import Bitvector.
Require Import Common.

Require Import ZArith.
Require Import BinNums.
Require Import BinIntDef.
Require Import String.
Require Import FSets.

Require Import List.
Import ListNotations.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.MonadState.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Data.Monads.StateMonad.
From ExtLib Require Import Data.Monads.EitherMonad.
From ExtLib Require Import Data.List.
Import MonadNotation.
Import FunctorNotation.
Open Scope monad_scope.
Require Import Program.

Record transf_state :=
  TransfState
    { nextName : name
    ; nameMap : StrMap.t name
    ; vars : NameMap.t Netlist.nltype
    ; cells : list Netlist.cell
    ; substitutionsBlocking : NameMap.t Netlist.input
    ; substitutionsNonblocking : NameMap.t Netlist.input
    }.

Definition transf : Type -> Type := stateT transf_state (sum string).

Instance Monad_transf : Monad transf := Monad_stateT transf_state (Monad_either string).

Definition fresh_name : transf name :=
  modify (fun s =>
            {| nextName := Pos.succ (nextName s)
            ; nameMap := nameMap s
            ; vars := vars s
            ; cells := cells s
            ; substitutionsBlocking := substitutionsBlocking s
            ; substitutionsNonblocking := substitutionsNonblocking s
            |}) ;;
  gets nextName .

Definition transfer_name (vname : string) : transf name :=
  names <- gets nameMap ;;
  match StrMap.find vname names with
  | Some n => ret n
  | None =>
      n <- fresh_name ;;
      modify (fun s =>
                {| nextName := nextName s
                ; nameMap := StrMap.add vname n (nameMap s)
                ; vars := vars s
                ; cells := cells s
                ; substitutionsBlocking := substitutionsBlocking s
                ; substitutionsNonblocking := substitutionsNonblocking s
                |}
        ) ;;
      ret n
  end.

Definition put_var (varName : name) (varType : Netlist.nltype) : transf () :=
  modify (fun s =>
            {| nextName := nextName s
            ; nameMap := nameMap s
            ; vars := NameMap.add varName varType (vars s)
            ; cells := cells s
            ; substitutionsBlocking := substitutionsBlocking s
            ; substitutionsNonblocking := substitutionsNonblocking s
            |}) ;;
  ret ()
.

Definition put_cells (cs : list Netlist.cell) : transf () :=
  modify (fun s =>
            {| nextName := nextName s
            ; nameMap := nameMap s
            ; vars := vars s
            ; cells := cells s ++ cs
            ; substitutionsBlocking := substitutionsBlocking s
            ; substitutionsNonblocking := substitutionsNonblocking s
            |}) ;;
  ret ()
.

Definition set_substitution_blocking (lhs : name) (rhs : Netlist.input) : transf () :=
  modify (fun s =>
            {| nextName := nextName s
            ; nameMap := nameMap s
            ; vars := vars s
            ; cells := cells s
            ; substitutionsBlocking := NameMap.add lhs rhs (substitutionsBlocking s)
            ; substitutionsNonblocking := substitutionsNonblocking s
            |}) ;;
  ret ()
.

Definition set_substitution_nonblocking (lhs : name) (rhs : Netlist.input) : transf () :=
  modify (fun s =>
            {| nextName := nextName s
            ; nameMap := nameMap s
            ; vars := vars s
            ; cells := cells s
            ; substitutionsBlocking := substitutionsBlocking s
            ; substitutionsNonblocking := NameMap.add lhs rhs (substitutionsNonblocking s)
            |}) ;;
  ret ()
.

Definition fresh (t : Netlist.nltype) : transf (Netlist.variable) :=
  name <- fresh_name ;;
  put_var name t ;;
  ret {| Netlist.varType := t; Netlist.varName := name |}
.

Definition transfer_type (type : Verilog.vtype) : Netlist.nltype :=
  (* Probably wrong but good enough for now*)
  match type with
  | Verilog.Logic N0 N0 => (Netlist.Logic 1)
  | Verilog.Logic (Npos n) N0 => (Netlist.Logic (n + 1))
  | Verilog.Logic N0 (Npos n) => (Netlist.Logic (n + 1))
  | Verilog.Logic (Npos n1) (Npos n2) => (Netlist.Logic (n1 - n2 + 1))
  end
.

Definition transfer_variables (vars : list Verilog.variable) : transf () :=
  mapT (fun v =>
          name <- transfer_name (Verilog.varName v) ;;
          put_var name (transfer_type (Verilog.varType v))
    ) vars ;;
  ret ()
.

Definition transfer_ports (ports : list Verilog.port) : transf (list (name * port_direction)) :=
  mapT (fun p =>
          name <- transfer_name (Verilog.portName p) ;;
          ret (name, Verilog.portDirection p)
    ) ports
.

Definition unsupported_expression_error : string := "Unsupported expression".

Definition binop :=
  forall (out : Netlist.output) (in1 in2 : Netlist.input),
       Netlist.input_width in1 = Netlist.input_width in2 ->
       Netlist.input_width in1 = Netlist.output_width out -> Netlist.cell.

Definition transfer_bin_op (op : Verilog.op) : binop :=
  match op with
  | Verilog.Plus => Netlist.Add
  | Verilog.Minus => Netlist.Subtract
  end
.

Equations transfer_expression : TypedVerilog.expression -> transf Netlist.input :=
| TypedVerilog.IntegerLiteral w v with Bitvector.mkBV_check v w => {
  | None => raise  "Invalid bitvector (value might be too long for the number of bits)"%string
  | Some bv => ret (Netlist.InConstant bv)
  }
| TypedVerilog.NamedExpression type name =>
    let t := transfer_type type in
    n <- transfer_name name ;;
    st <- get ;;
    match NameMap.find n (substitutionsBlocking st) with
    | Some e => ret e
    | None => ret (Netlist.InVar {| Netlist.varType := t; Netlist.varName := n |})
    end
| TypedVerilog.BinaryOp t op e1 e2 =>
    v1 <- transfer_expression e1 ;;
    v2 <- transfer_expression e2 ;;
    v__result <- fresh (transfer_type t) ;;
    if Pos.eq_dec (Netlist.input_width v1) (Netlist.input_width v2)
    then
      if Pos.eq_dec (Netlist.input_width v1) (Netlist.output_width (Netlist.OutVar v__result))
      then
        put_cells [transfer_bin_op op (Netlist.OutVar v__result) v1 v2 _ _] ;;
        ret (Netlist.InVar v__result)
      else raise "Nope"%string
    else
      raise "Nope"%string
| TypedVerilog.Conversion v_t__from v_t__to e =>
    v__expr <- transfer_expression e ;;
    v__result <- fresh (transfer_type v_t__to) ;;
    put_cells [Netlist.Convert (Netlist.OutVar v__result) v__expr] ;;
    ret (Netlist.InVar v__result)
.

(*
  Translated from the following
https://github.com/CakeML/hardware/blob/8264e60f0f9d503c9d971991cf181012276f0c9b/compiler/RTLCompilerScript.sml#L233-L295
*)

Equations transfer_statement : TypedVerilog.Statement -> transf () :=
| TypedVerilog.Block body =>
    mapT transfer_statement body ;;
    ret ()
| TypedVerilog.NonBlockingAssign (TypedVerilog.NamedExpression t__lhs vname__lhs) rhs =>
    name__lhs <- transfer_name vname__lhs ;;
    input__rhs <- transfer_expression rhs ;;
    set_substitution_nonblocking name__lhs input__rhs
| TypedVerilog.BlockingAssign (TypedVerilog.NamedExpression t__lhs vname__lhs) rhs =>
    name__lhs <- transfer_name vname__lhs ;;
    input__rhs <- transfer_expression rhs ;;
    set_substitution_blocking name__lhs input__rhs
| TypedVerilog.BlockingAssign lhs rhs =>
    raise "Invalid lhs for blocking assignment"%string
| TypedVerilog.NonBlockingAssign lhs rhs =>
    raise "Invalid lhs for non-blocking assignment"%string
| TypedVerilog.If condition trueBranch falseBranch =>
    raise "Conditionals not yet implemented"%string
.

Equations transfer_module_item : TypedVerilog.module_item -> transf () :=
| TypedVerilog.AlwaysFF body => transfer_statement body
| TypedVerilog.ContinuousAssign (TypedVerilog.NamedExpression type name) from =>
    raise "Continuous assignment not implemented"%string
    (* t <- transfer_type type ;; *)
    (* n <- transfer_name name ;; *)
    (* let outVar := Netlist.OutVar {| Netlist.varType := t; Netlist.varName := n |} in *)
    (* result <- transfer_expression from ;; *)
    (* if Pos.eq_dec (Netlist.input_width result) (Netlist.output_width outVar) *)
    (* then put_cells [ Netlist.Id outVar result _] *)
    (* else raise "Nope"%string *)
| TypedVerilog.ContinuousAssign _to _from =>
    raise "Invalid target for assign expression"%string
.

Equations mk_register : Netlist.input -> Netlist.register_declaration :=
| Netlist.InConstant bv =>
    {| Netlist.init := bv
    ; Netlist.driver := Netlist.InConstant bv
    |}
| Netlist.InVar v =>
    {| Netlist.init := Bitvector.mkBV 0 (Netlist.type_width (Netlist.varType v))
    ; Netlist.driver := Netlist.InVar v
    |}
.

Definition transfer_module (vmodule : TypedVerilog.vmodule) : transf Netlist.circuit :=
  transfer_variables (TypedVerilog.modVariables vmodule) ;;
  ports <- transfer_ports (TypedVerilog.modPorts vmodule) ;;
  mapT transfer_module_item (TypedVerilog.modBody vmodule) ;;

  finalState <- get ;;

  ret {| Netlist.circuitName := TypedVerilog.modName vmodule
      ; Netlist.circuitPorts := NameMap.from_list ports
      ; Netlist.circuitRegisters :=
          NameMap.map mk_register
            (NameMap.combine
               (substitutionsNonblocking finalState)
               (substitutionsBlocking finalState))
      ; Netlist.circuitVariables := vars finalState
      ; Netlist.circuitCells := cells finalState
      |}
.

Definition verilog_to_netlist (start_name: positive) (vmodule : TypedVerilog.vmodule) : sum string (Netlist.circuit * name) :=
  let result :=
    runStateT
      (transfer_module vmodule)
      {| nextName := start_name
      ; nameMap := StrMap.empty name
      ; vars := NameMap.empty _
      ; cells := []
      ; substitutionsBlocking := NameMap.empty _
      ; substitutionsNonblocking := NameMap.empty _
      |} in
  match result with
  | inl err => inl err
  | inr (circuit, final_state) => inr (circuit, nextName final_state)
  end
.

Section Examples.

  Import TypedVerilog.

  Let l n := Verilog.Logic (n - 1) 0.

  Let l32 := l 32.

  (* TODO: Nicer printing, match with parsing *)
  Notation "'BV v w" := (Bitvector.BV v w _) (at level 200, only printing).

  Let verilog1 :=
        {|
          TypedVerilog.modName := "test1a";
          TypedVerilog.modPorts := [
            Verilog.MkPort PortIn "in" ;
            Verilog.MkPort PortOut "out"
          ];
          TypedVerilog.modVariables := [
            Verilog.MkVariable l32 "in" ;
            Verilog.MkVariable l32 "out";
            Verilog.MkVariable l32 "v1"
          ];
          modBody := [
            AlwaysFF (
                Block [
                    NonBlockingAssign
                      (NamedExpression (l 32) "v1")
                      (IntegerLiteral 32 42) ;
                    BlockingAssign
                      (NamedExpression l32 "v1")
                      (BinaryOp l32 Plus
                         (NamedExpression l32 "in")
                         (BinaryOp l32 Plus (IntegerLiteral 32 1) (IntegerLiteral 32 1))) ;
                    BlockingAssign
                      (NamedExpression l32 "out")
                      (BinaryOp l32 Plus
                         (NamedExpression l32 "v1")
                         (IntegerLiteral 32 1))
                  ]
              )
          ];
        |}.

  Compute
    match verilog_to_netlist 1 verilog1 with
    | inl e => inl e
    | inr (x, _) =>
        inr (
            NameMap.elements (Netlist.circuitPorts x),
            NameMap.elements (Netlist.circuitVariables x),
            NameMap.elements (Netlist.circuitRegisters x),
            Netlist.circuitCells x
          )
    end.
End Examples.
