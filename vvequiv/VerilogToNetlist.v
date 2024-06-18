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
    { nextName : name;
      nameMap : StrMap.t name;
      vars : list Netlist.variable
    }.

Definition transf : Type -> Type := stateT transf_state (sum string).

Instance Monad_transf : Monad transf := Monad_stateT transf_state (Monad_either string).

Definition fresh_name : transf name :=
  s <- get ;;
  let s' := {| nextName := Pos.succ (nextName s) ; nameMap := nameMap s; vars := vars s |} in
  put s' ;;
  ret (nextName s)
.

Definition transfer_name (vname : string) : transf name :=
  st0 <- get ;;
  match StrMap.find vname (nameMap st0) with
  | Some n => ret n
  | None =>
      n <- fresh_name ;;
      st1 <- get ;;
      put {|
          nextName := nextName st1 ;
          nameMap := StrMap.add vname n (nameMap st1) ;
          vars := vars st1
        |} ;;
      ret n
  end.

Definition put_var (v : Netlist.variable) : transf () :=
  st <- get ;;
  put {| nextName := nextName st; nameMap := nameMap st; vars := vars st ++ [ v ] |}
.

Definition fresh (t : Netlist.nltype) : transf (Netlist.variable) :=
  name <- fresh_name ;;
  let var := {| Netlist.varType := t; Netlist.varName := name |} in
  put_var var ;;
  ret var
.

Definition transfer_type (type : Verilog.vtype) : transf Netlist.nltype :=
  (* Probably wrong but good enough for now*)
  match type with
  | Verilog.Logic N0 N0 => ret (Netlist.Logic 1)
  | Verilog.Logic (Npos n) N0 => ret (Netlist.Logic (n + 1))
  | Verilog.Logic N0 (Npos n) => ret (Netlist.Logic (n + 1))
  | Verilog.Logic (Npos n1) (Npos n2) => ret (Netlist.Logic (n1 - n2 + 1))
  end
.

Definition transfer_variables (vars : list Verilog.variable) : transf (list Netlist.variable) :=
  mapT (fun v =>
          name <- transfer_name (Verilog.varName v) ;;
          type <- transfer_type (Verilog.varType v) ;;
          ret (Netlist.Var type name)
    ) vars
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

Definition invalid_bitvector_error : string := "Invalid bitvector (value might be too long for the number of bits)".

Equations transfer_expression : TypedVerilog.expression -> transf (list Netlist.cell * Netlist.input) :=
| TypedVerilog.IntegerLiteral w v =>
    match Bitvector.mkBV_check v w with
    | None => raise invalid_bitvector_error
    | Some bv => ret ([], Netlist.InConstant bv)
    end
| TypedVerilog.NamedExpression type name =>
    t <- transfer_type type ;;
    n <- transfer_name name ;;
    ret ([], Netlist.InVar {| Netlist.varType := t; Netlist.varName := n |})
| TypedVerilog.BinaryOp t op e1 e2 =>
    pair1 <- transfer_expression e1 ;;
    let (cells1, v1) := pair1 in
    pair2 <- transfer_expression e2 ;;
    let (cells2, v2) := pair2 in
    t__result <- transfer_type t ;;
    v__result <- fresh t__result ;;
    if Pos.eq_dec (Netlist.input_width v1) (Netlist.input_width v2)
    then
      if Pos.eq_dec (Netlist.input_width v1) (Netlist.output_width (Netlist.OutVar v__result))
      then
        let cells__op := [transfer_bin_op op (Netlist.OutVar v__result) v1 v2 _ _] in
        let cells := cells1 ++ cells2 ++ cells__op in
        ret (cells, Netlist.InVar v__result)
      else raise "Nope"%string
    else
      raise "Nope"%string
| TypedVerilog.Conversion v_t__from v_t__to e =>
    pair <- transfer_expression e ;;
    let (cells__expr, v__expr) := pair in
    nl_t__from <- transfer_type v_t__from ;;
    nl_t__to <- transfer_type v_t__to ;;
    v__result <- fresh nl_t__to ;;
    let cells__conv := [Netlist.Convert (Netlist.OutVar v__result) v__expr] in
    let cells := (cells__expr ++ cells__conv) in
    ret (cells, Netlist.InVar v__result)
.

Definition invalid_assign_err : string := "Invalid target for assign expression".

(*
  Translated from the following
https://github.com/CakeML/hardware/blob/8264e60f0f9d503c9d971991cf181012276f0c9b/compiler/RTLCompilerScript.sml#L233-L295
*)

Equations transfer_statement : TypedVerilog.Statement -> transf (list Netlist.cell) :=
| TypedVerilog.Block body => fmap (@List.concat _) (mapT transfer_statement body)
| TypedVerilog.BlockingAssign lhs rhs => _
| TypedVerilog.NonBlockingAssign lhs rhs => _
| TypedVerilog.If condition trueBranch falseBranch => _
.

Equations transfer_module_item : TypedVerilog.module_item -> transf (list Netlist.cell) :=
| TypedVerilog.AlwaysAtClock body => transfer_statement body
| TypedVerilog.ContinuousAssign (TypedVerilog.NamedExpression type name) from =>
    t <- transfer_type type ;;
    n <- transfer_name name ;;
    let outVar := Netlist.OutVar {| Netlist.varType := t; Netlist.varName := n |} in
    pair <- transfer_expression from ;;
    let (cells, result) := pair in
    if Pos.eq_dec (Netlist.input_width result) (Netlist.output_width outVar)
    then
      ret (cells ++ [ Netlist.Id outVar result _])
    else raise "Nope"%string
| TypedVerilog.ContinuousAssign _to _from => raise invalid_assign_err
.

Definition transfer_body (items : list TypedVerilog.module_item) : transf (list Netlist.cell) :=
  fmap (fun l => concat l) (mapT transfer_module_item items)
.

Definition transfer_module (vmodule : TypedVerilog.vmodule) : transf Netlist.circuit :=
  sourceVars <- transfer_variables (TypedVerilog.modVariables vmodule) ;;
  ports <- transfer_ports (TypedVerilog.modPorts vmodule) ;;
  cells <- transfer_body (TypedVerilog.modBody vmodule) ;;
  st <- get ;;
  let vars := sourceVars ++ vars st in
  ret {| Netlist.circuitName := TypedVerilog.modName vmodule;
        Netlist.circuitPorts := NameMap.from_list ports;
        Netlist.circuitRegisters := NameMap.empty _;
        Netlist.circuitVariables := NameMap.from_list (List.map (fun var => (Netlist.varName var, Netlist.varType var)) vars);
        Netlist.circuitCells := cells
      |}
.

Definition verilog_to_netlist (start_name: positive) (vmodule : TypedVerilog.vmodule) : sum string (Netlist.circuit * positive) :=
  let result := runStateT (transfer_module vmodule) {| nextName := start_name; nameMap := StrMap.empty name; vars := [] |} in
  match result with
  | inl err => inl err
  | inr (result, final_state) => inr (result, nextName final_state)
  end
.
