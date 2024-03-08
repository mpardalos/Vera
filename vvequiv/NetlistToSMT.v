Require Import Names.
Require Import Netlist.
Require Import SMT.
Require Import String.
Require Import BinNums.
Require Import BinPos.
Require Import Common.

Require Import List.
Import ListNotations.

Definition input_formula (input : Netlist.input) : QFBV.formula :=
  match input with
  | Netlist.InVar (Netlist.Var _ name) => QFBV.BVVar name
  | Netlist.InConstant constant => QFBV.BVLit constant
  end
.

Definition output_name (output : Netlist.output) : name :=
  match output with
  | Netlist.OutVar (Netlist.Var _ varName) => varName
  end
.

Definition nltype_sort (t : Netlist.nltype) : Core.SMTSort :=
  match t with
  | Netlist.Logic sz => Core.SBitVector sz
  end
.

Definition cell_formula (cell : Netlist.cell) : name * QFBV.formula :=
  match cell with
  | Netlist.Add out l r =>
      let l_formula := input_formula l in
      let r_formula := input_formula r in
      (output_name out, QFBV.BVAdd l_formula r_formula)
  | Netlist.Subtract out l r =>
      let l_formula := input_formula l in
      let r_formula := input_formula r in
      (output_name out, QFBV.BVAdd l_formula (QFBV.BVNeg r_formula))
  | Netlist.Id out in_ =>
      let formula := input_formula in_ in
      (output_name out, formula)
  end
.

Fixpoint netlist_to_formulas_acc
  (acc : NameMap.t QFBV.formula)
  (cells : list Netlist.cell)
  : NameMap.t QFBV.formula :=
  match cells with
  | [] => acc
  | c::cs =>
      let (name, formula) := cell_formula c in
      netlist_to_formulas_acc (NameMap.add name formula acc) cs
  end
.

Definition netlist_to_formulas (nl : Netlist.circuit) : NameMap.t QFBV.formula :=
  netlist_to_formulas_acc (NameMap.empty _) (Netlist.circuitCells nl)
.

Definition netlist_declarations (nl : Netlist.circuit) : list Core.formula :=
  List.map
    (fun (var : Netlist.variable) =>
       Core.CDeclare (Netlist.varName var) (nltype_sort (Netlist.varType var))
    )
    (Netlist.circuitVariables nl)
.

(** Map each variable in the netlist to a bitvector formula *)
Definition netlist_to_smt (nl : Netlist.circuit) : Core.smt_netlist :=
  let formulas := netlist_to_formulas nl in
  let declarations := netlist_declarations nl in
  let assertions := List.map
                      (fun (it : name * QFBV.formula) =>
                         let (n, formula) := it in
                         Core.CEqual (QFBV.BVVar n) formula)
                      (NameMap.elements formulas) in
  {| Core.smtnlName := Netlist.circuitName nl
  ; Core.smtnlPorts := Netlist.circuitPorts nl
  ; Core.smtnlFormulas := declarations ++ assertions
  |}
.
