From Coq Require Import BinNums.
From Coq Require Import BinNat.
From Coq Require Import BinPos.

From vvequiv Require Import Netlist.
From vvequiv Require Import Common.
From vvequiv Require Import Bitvector.

From Equations Require Import Equations.

Import Bitvector (bv, mkBV).
Import Netlist.

(** Based on Lööw (2021) Lutsig: a verified Verilog compiler for verified circuit development, ACM. *)

Definition RandomSource := nat -> bool.

Definition ExternalState := NameMap.t bv.

Definition RegisterState := NameMap.t bv.

Definition VariableState := NameMap.t bv.

Record CircuitState :=
  MkCircuitState
    { external : ExternalState
    ; registers : RegisterState
    ; variables : VariableState
    }
.

Set Primitive Projections.

Equations varWidth : variable -> positive :=
  varWidth (Var (Logic w) _) := w.

Equations input_run : CircuitState -> input -> bv :=
  input_run st (InConstant c) := c;
  input_run st (InVar v) :=
    (* TODO: Statically guarantee that this lookup can't fail so that we can
    avoid returning a meaningless zero *)
    opt_or_else
      (opt_or
         (NameMap.find v.(varName) st.(registers))
         (NameMap.find v.(varName) st.(variables)))
      (mkBV 0%N (varWidth v)).

Equations cell_run : CircuitState -> cell -> CircuitState :=
  cell_run st (Add (OutVar (Var _ out)) in1 in2) :=
    let val1 := input_run st in1 in
    let val2 := input_run st in2 in
    (* let result := bv_add val1 val2 in *)
    let result := (mkBV 0%N 32%positive) in
    MkCircuitState
      (external st)
      (registers st)
      (NameMap.add out result (variables st));
  (* TODO: Cells other than Add *)
  cell_run st _ := st.


Equations circuit_run
  (fext : ExternalState)
  (fbits : RandomSource)
  (st: CircuitState)
  (c : circuit)
  : CircuitState :=
  circuit_run fext fbits st (Circuit _ _ vars regs cells) := st.
