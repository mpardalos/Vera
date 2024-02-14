Require Import String.
Require Import ZArith.
Require Import BinNums.

Require Import List.
Import ListNotations.

(* This module will be Netlist.Netlist. Redundant, but it is needed for extraction. See Extraction.v *)
Module Netlist.
  Inductive nltype := Logic : positive -> nltype.

  (* Inductive register :=. *)

  Record constant :=
    Constant
      { constWidth : positive
      ; constValue : N
      }.

  (** These are not registers, just names used to connect the netlist graph *)
  Record variable :=
    Var
      { varType : nltype
      ; varName : N
      }.

  Inductive input :=
  | InVar : variable -> input
  | InConstant : constant -> input
  .

  Inductive output :=
  | OutVar : variable -> output
  .

  Inductive cell :=
  | Add : output -> input -> input -> cell
  | Subtract : output -> input -> input -> cell
  | Id : output -> input -> cell
  .

  Record circuit :=
    Circuit
      { circuitName : string
      ; circuitVariables : list variable
      ; circuitCells : list cell
      }.

  Example examples : list circuit :=
    let v0 := Var (Logic 32) 0 in
    let v1 := Var (Logic 32) 1 in
    let v2 := Var (Logic 32) 2 in
    [ {| circuitName := "test1";
        circuitVariables := [v0; v1];
        circuitCells := [Id (OutVar v0) (InVar v1)]
      |}
      ;
      {| circuitName := "test2";
        circuitVariables := [v0; v1; v2];
        circuitCells := [Add (OutVar v0) (InVar v1) (InVar v2)]
      |}
    ].
End Netlist.
