Require Import Verilog.
Require Import Netlist.

Require Import ZArith.
Require Import BinIntDef.
Require Import String.
Require Import FSets.
Require Import FMaps.

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
Open Scope monad_scope.
Require Import Program.

Module StrMap := FMapList.Make(String_as_OT).

Record transf_state :=
  TransfState
    { nextName : N;
      nameMap : StrMap.t N
    }.

Definition transf : Type -> Type := stateT transf_state (sum string).

Instance Monad_transf : Monad transf := Monad_stateT transf_state (Monad_either string).

Definition fresh : transf N :=
  s <- get ;;
  let s' := {| nextName := N.succ (nextName s) ; nameMap := nameMap s |} in
  put s' ;;
  ret (nextName s)
.

Definition transfer_name (name : string) : transf N :=
  st <- get ;;
  match StrMap.find name (nameMap st) with
  | Some n => ret n
  | None =>
      n <- fresh ;;
      put {|
          nextName := (nextName st) ;
          nameMap := StrMap.add name n (nameMap st)
        |} ;;
      ret n
  end.


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
          name <- fresh ;;
          type <- (transfer_type (Verilog.varType v)) ;;
          ret (Netlist.Var type name)
    ) vars
.

Definition unsupported_expression_error : string := "Unsupported expression".

Definition transfer_expression_to (var : Netlist.variable) (expr : Verilog.expression) : transf (list Netlist.cell) :=
  match expr return transf (list Netlist.cell) with
  | Verilog.IntegerLiteral w v =>
      ret [
          Netlist.Id
            (Netlist.OutVar var)
            (Netlist.InConstant {| Netlist.constWidth := w; Netlist.constValue := v |}) ]
  | _ => raise unsupported_expression_error
  end
.

Definition invalid_assign_err : string := "Invalid target for assign expression".

Program Definition transfer_module_item (item : Verilog.module_item) : transf (list Netlist.cell) :=
  match item with
  | Verilog.ContinuousAssign (Verilog.NamedExpression name) from =>
      n <- transfer_name name ;;
      transfer_expression_to (Netlist.Var _ n) from
  | Verilog.ContinuousAssign to from => raise invalid_assign_err
  end
.
Next Obligation. Admitted.

Definition transfer_body (items : list Verilog.module_item) : transf (list Netlist.cell) :=
  fmap (fun l => concat l) (mapT transfer_module_item items)
.

Definition transfer_module (vmodule : Verilog.vmodule) : transf Netlist.circuit :=
  vars <- transfer_variables (Verilog.modVariables vmodule) ;;
  cells <- transfer_body (Verilog.modBody vmodule) ;;
  ret {| Netlist.circuitName := Verilog.modName vmodule;
    Netlist.circuitVariables := vars;
    Netlist.circuitCells := cells
  |}
.

Definition verilog_to_netlist (vmodule : Verilog.vmodule) : sum string Netlist.circuit :=
  evalStateT (transfer_module vmodule) {| nextName := 0; nameMap := StrMap.empty N |}.
