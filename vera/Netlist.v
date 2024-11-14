From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import BinNums.

From nbits Require Import NBits.
Local Open Scope bits_scope.
From mathcomp Require Import seq.

From vera Require Import Common.
From vera Require Import Verilog.

From Equations Require Import Equations.

Require Import List.
Import ListNotations.

(* This module will be Netlist.Netlist. Redundant, but it is needed for extraction. See Extraction.v *)
Module Netlist.
  Definition nltype := nat.

  (** These are not registers, just names used to connect the netlist graph *)
  Record variable :=
    Var
      { varType : nltype
      ; varName : name
      }.

  Arguments Var _ _%positive.

  Inductive input :=
  | InVar : variable -> input
  | InConstant : bits -> input
  .

  Equations input_type : input -> nltype :=
    input_type (InVar (Var w _)) := w;
    input_type (InConstant v) := size v.

  Inductive output :=
  | OutVar : variable -> output
  .

  Equations output_type : output -> nltype :=
    output_type (OutVar (Var w _)) := w.

  Inductive cell :=
  | BinaryCell
      (operator : Verilog.op)
      (out : output)
      (in1 in2 : input)
  | BitSelect
      (out : output)
      (in_vec in_idx : input)
      (output_width : output_type out = 1)
  | Mux
      (out : output)
      (select in1 in2 : input)
      (select_width : input_type select = 1)
      (inputs_match : input_type in1 = input_type in2)
      (output_match : input_type in1 = output_type out)
  | Id
      (out : output)
      (in1 : input)
      (output_match : input_type in1 = output_type out)
  | Convert
      (out : output)
      (in1 : input)
  .

  Equations cell_output : cell -> output :=
  | BinaryCell _ o _ _ => o
  | BitSelect o _ _ _ => o
  | Mux o _ _ _ _ _ _ => o
  | Id o _ _ => o
  | Convert o _ => o
  .

  Record register_declaration :=
    MkRegister
      { init : bits
      ; driver : Netlist.input
      }
  .

  Definition register_width (reg : register_declaration) :=
    input_type (driver reg).

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
  | c, BinaryCell op out in1 in2 =>
      output_in_circuit c out
      /\ input_in_circuit c in1
      /\ input_in_circuit c in2
  | c, Mux out select in1 in2 _ _ _ =>
      output_in_circuit c out
      /\ input_in_circuit c select
      /\ input_in_circuit c in1
      /\ input_in_circuit c in2
  | c, BitSelect out in_vec in_idx _ =>
      output_in_circuit c out
      /\ input_in_circuit c in_vec
      /\ input_in_circuit c in_idx
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


Module NetlistNotations.
  Notation "${ v }" :=
    (Netlist.InConstant v)
      (at level 1, only printing, format "'${' v '}'").
  Notation "$ n" :=
    (Netlist.OutVar {| Netlist.varType := _; Netlist.varName := n |})
      (at level 1, only printing, format "'$' n").
  Notation "$ n" :=
    (Netlist.InVar {| Netlist.varType := _; Netlist.varName := n |})
      (at level 1, only printing, format "'$' n").
  Notation "a <- Mux( b , c , d  )" :=
    (Netlist.Mux a b c d _ _ _)
      (at level 200, only printing).
  Notation "a <- BinaryCell( b , c , d  )" :=
    (Netlist.BinaryCell a b c d _ _)
      (at level 200, only printing).
End NetlistNotations.
