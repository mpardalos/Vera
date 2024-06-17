Require Import Netlist.
Require Import SMT.
Require Import String.
Require Import BinNums.
Require Import BinPos.
Require Import Common.
Require Import Coq.NArith.BinNat.
Require Import Coq.PArith.BinPos.


Require Import List.
Import ListNotations.
From Equations Require Import Equations.

Local Open Scope positive.

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

Equations cell_formula : Netlist.cell -> name * SMT.qfbv name :=
  cell_formula (Netlist.Add out l r _ _) :=
    let l_formula := input_formula l in
    let r_formula := input_formula r in
    (output_name out, SMT.BVAdd l_formula r_formula);
  cell_formula (Netlist.Subtract out l r _ _) :=
    let l_formula := input_formula l in
    let r_formula := input_formula r in
    (output_name out, SMT.BVAdd l_formula (SMT.BVNeg r_formula));
  cell_formula (Netlist.Id out in_ _) :=
    let formula := input_formula in_ in
    (output_name out, formula);
  cell_formula (Netlist.Convert out in_) :=
    let from := Netlist.input_width in_ in
    let to := Netlist.output_width out in
    let in_formula := input_formula in_ in
    let formula :=
      if to <? from
      then SMT.BVExtract (Npos to - 1) 0 in_formula
      else SMT.BVZeroExtend (to - from) in_formula
    in
    (output_name out, formula)
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
    (fun (var : (name * Netlist.nltype)) =>
       let (varName, varType) := var in
       SMT.CDeclare varName (nltype_sort varType)
    )
    (NameMap.elements (Netlist.circuitVariables nl))
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
  ; SMT.smtnlPorts := NameMap.elements (Netlist.circuitPorts nl)
  ; SMT.smtnlFormulas := declarations ++ assertions
  |}
.
