Require Import Netlist.
Require Import SMT.
Require Import String.
Require Import BinNums.
Require Import BinPos.
Require Import Common.

Require Import List.
Import ListNotations.

Definition input_formula (input : Netlist.input) : SMT.qfbv name :=
  match input with
  | Netlist.InVar (Netlist.Var _ n) => SMT.BVVar n
  | Netlist.InConstant constant => SMT.BVLit constant
  end
.

Definition output_name (output : Netlist.output) : name :=
  match output with
  | Netlist.OutVar (Netlist.Var _ varName) => varName
  end
.

Definition nltype_sort (t : Netlist.nltype) : SMT.sort :=
  match t with
  | Netlist.Logic sz => SMT.SBitVector sz
  end
.

Definition cell_formula (cell : Netlist.cell) : name * SMT.qfbv name :=
  match cell with
  | Netlist.Add out l r =>
      let l_formula := input_formula l in
      let r_formula := input_formula r in
      (output_name out, SMT.BVAdd l_formula r_formula)
  | Netlist.Subtract out l r =>
      let l_formula := input_formula l in
      let r_formula := input_formula r in
      (output_name out, SMT.BVAdd l_formula (SMT.BVNeg r_formula))
  | Netlist.Id out in_ =>
      let formula := input_formula in_ in
      (output_name out, formula)
  end
.

Fixpoint netlist_to_formulas_acc
  (acc : NameMap.t (SMT.qfbv name))
  (cells : list Netlist.cell)
  : NameMap.t (SMT.qfbv name) :=
  match cells with
  | [] => acc
  | c::cs =>
      let (name, formula) := cell_formula c in
      netlist_to_formulas_acc (NameMap.add name formula acc) cs
  end
.

Definition netlist_to_formulas (nl : Netlist.circuit) : NameMap.t (SMT.qfbv name) :=
  netlist_to_formulas_acc (NameMap.empty _) (Netlist.circuitCells nl)
.

Definition netlist_declarations (nl : Netlist.circuit) : list (SMT.formula name) :=
  List.map
    (fun (var : Netlist.variable) =>
       SMT.CDeclare (Netlist.varName var) (nltype_sort (Netlist.varType var))
    )
    (Netlist.circuitVariables nl)
.

(** Map each variable in the netlist to a bitvector formula *)
Definition netlist_to_smt (nl : Netlist.circuit) : SMT.smt_netlist name :=
  let formulas := netlist_to_formulas nl in
  let declarations := netlist_declarations nl in
  let assertions := List.map
                      (fun (it : name * (SMT.qfbv name)) =>
                         let (n, formula) := it in
                         SMT.CEqual (SMT.BVVar n) formula)
                      (NameMap.elements formulas) in
  {| SMT.smtnlName := Netlist.circuitName nl
  ; SMT.smtnlPorts := Netlist.circuitPorts nl
  ; SMT.smtnlFormulas := declarations ++ assertions
  |}
.