Require Import Bitvector.
Import Bitvector (bv(..)).
Require Import Common.

Require Import String.
Require Import ZArith.
Require Import BinNums.

From Equations Require Import Equations.

Require Import List.
Import ListNotations.

(* This module will be Netlist.Netlist. Redundant, but it is needed for extraction. See Extraction.v *)
Module Netlist.
  Inductive nltype := Logic : positive -> nltype.

  Equations type_width : nltype -> positive :=
    type_width (Logic w) := w.

  (** These are not registers, just names used to connect the netlist graph *)
  Record variable :=
    Var
      { varType : nltype
      ; varName : name
      }.

  Arguments Var _ _%positive.

  Inductive input :=
  | InVar : variable -> input
  | InConstant : bv -> input
  .

  Equations input_width : input -> positive :=
    input_width (InVar (Var (Logic w) _)) := w;
    input_width (InConstant (BV _ w _)) := w.

  Inductive output :=
  | OutVar : variable -> output
  .

  Equations output_width : output -> positive :=
    output_width (OutVar (Var (Logic w) _)) := w.

  Inductive cell :=
  | Add
      (out : output)
      (in1 in2 : input)
      (inputs_match : input_width in1 = input_width in2)
      (output_match : input_width in1 = output_width out)
  | Subtract
      (out : output)
      (in1 in2 : input)
      (inputs_match : input_width in1 = input_width in2)
      (output_match : input_width in1 = output_width out)
  | Mux
      (out : output)
      (select in1 in2 : input)
      (select_width : input_width select = 1%positive)
      (inputs_match : input_width in1 = input_width in2)
      (output_match : input_width in1 = output_width out)
  | Id
      (out : output)
      (in1 : input)
      (output_match : input_width in1 = output_width out)
  | Convert
      (out : output)
      (in1 : input)
  .

  Equations cell_output : cell -> output :=
  | Add o _ _ _ _ => o
  | Subtract o _ _ _ _ => o
  | Mux o _ _ _ _ _ _ => o
  | Id o _ _ => o
  | Convert o _ => o
  .

  Record register_declaration :=
    MkRegister
      { init : bv
      ; driver : Netlist.input
      }
  .

  Definition register_width (reg : register_declaration) :=
    input_width (driver reg).

  Record circuit :=
    Circuit
      { circuitName : string
      ; circuitPorts : NameMap.t port_direction
      ; circuitVariables : NameMap.t nltype
      ; circuitRegisters : NameMap.t register_declaration
      ; circuitCells : list cell
      }.

  Equations input_in_circuit : circuit -> input -> Prop :=
  | _, InConstant _ => True
  | c, InVar (Var t n) => NameMap.MapsTo n t (circuitVariables c).


  Equations output_in_circuit : circuit -> output -> Prop :=
  | c, OutVar (Var t n) => NameMap.MapsTo n t (circuitVariables c).


  Equations cell_in_circuit : circuit -> cell -> Prop :=
  | c, Add out in1 in2 _ _ =>
      output_in_circuit c out
      /\ input_in_circuit c in1
      /\ input_in_circuit c in2
  | c, Subtract out in1 in2 _ _ =>
      output_in_circuit c out
      /\ input_in_circuit c in1
      /\ input_in_circuit c in2
  | c, Mux out select in1 in2 _ _ _ =>
      output_in_circuit c out
      /\ input_in_circuit c select
      /\ input_in_circuit c in1
      /\ input_in_circuit c in2
  | c, Id out in1 _ =>
      output_in_circuit c out
      /\ input_in_circuit c in1
  | c, Convert out in1 =>
      output_in_circuit c out
      /\ input_in_circuit c in1
  .

  Record circuit_wf (c : circuit) :=
    MkCircuitWf
      { circuit_cells_wf : Forall (cell_in_circuit c) (circuitCells c)
      }.

End Netlist.
