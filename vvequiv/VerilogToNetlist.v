Require Verilog.
Require Netlist.
Require Import ZArith.

Require Import List.
Import ListNotations.

Definition transfer_type (type : Verilog.vtype) : Netlist.nltype :=
  match type with
  | Verilog.Logic hi lo => Netlist.Logic (hi - lo + 1)
  end
.

Definition transfer_variables (vars : list Verilog.variable) : list Netlist.variable :=
  List.map (fun v => Netlist.Var (transfer_type (Verilog.varType v)) 0) vars
.

Definition transfer_module_item (item : Verilog.module_item) : list Netlist.cell :=
  match item with
  | Verilog.ContinuousAssign to from => []
  end
.

Definition transfer_body (items : list Verilog.module_item) : list Netlist.cell :=
  List.flat_map transfer_module_item items
.

Definition transfer_module (vmodule : Verilog.vmodule) : Netlist.circuit :=
  let vars := transfer_variables (Verilog.modVariables vmodule) in
  let cells := transfer_body (Verilog.modBody vmodule) in
  {| Netlist.circuitName := Verilog.modName vmodule;
    Netlist.circuitVariables := vars;
    Netlist.circuitCells := cells
  |}
.
