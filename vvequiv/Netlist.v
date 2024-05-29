Require Import Bitvector.
Import Bitvector (bv).
Require Import Common.

Require Import String.
Require Import ZArith.
Require Import BinNums.

Require Import List.
Import ListNotations.

(* This module will be Netlist.Netlist. Redundant, but it is needed for extraction. See Extraction.v *)
Module Netlist.
  Inductive nltype := Logic : positive -> nltype.

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

  Inductive output :=
  | OutVar : variable -> output
  .

  Inductive cell :=
  | Add : output -> input -> input -> cell
  | Subtract : output -> input -> input -> cell
  | Id : output -> input -> cell
  | Convert : nltype -> nltype -> output -> input -> cell
  .

  Definition cell_output (c : cell) : output :=
    match c with
    | Add o _ _ => o
    | Subtract o _ _ => o
    | Id o _ => o
    | Convert _ _ o _ => o
    end
  .

  Inductive register_declaration :=
    MkRegister
      (reg_type : nltype)
      (reg_name : name)
      (init : bv)
      (driver : name).

  Record circuit :=
    Circuit
      { circuitName : string
      ; circuitPorts : list (name * port_direction)
      ; circuitVariables : list variable
      ; circuitRegisters : list register_declaration
      ; circuitCells : list cell
      }.
End Netlist.
