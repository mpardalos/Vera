Require Verilog.
Require Netlist.
Require Import ZArith.

Require Import List.
Import ListNotations.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Data.Monads.StateMonad.
From ExtLib Require Import Data.List.
Import MonadNotation.

Definition transf := state Z.

Definition fresh := mkState (fun n => (n, n+1)).

Definition transfer_type (type : Verilog.vtype) : transf Netlist.nltype :=
  match type with
  | Verilog.Logic hi lo => ret (Netlist.Logic (hi - lo + 1))
  end
.

Open Scope monad_scope.

Definition transfer_variables (vars : list Verilog.variable) : transf (list Netlist.variable) :=
  mapT (fun v =>
          type <- (transfer_type (Verilog.varType v)) ;;
          ret (Netlist.Var type 0)
    ) vars
.

Definition transfer_module_item (item : Verilog.module_item) : transf (list Netlist.cell) :=
  match item with
  | Verilog.ContinuousAssign to from => ret []
  end
.

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
