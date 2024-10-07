open Format
open Vera

let bitvector fmt (bv : bits) = fprintf fmt "%d'd%d" (N.of_nat (size bv)) (N.of_nat (bits_to_nat bv))

let nltype fmt (t : Netlist.nltype) =
  (* nltype gets extracted to just int *)
  fprintf fmt "logic[%d]" (int_from_nat t)

let variable fmt (v : Netlist.variable) =
  fprintf fmt "%a <%d>" nltype v.varType v.varName

let input fmt (i : Netlist.input) =
  match i with
  | InVar v -> variable fmt v
  | InConstant c -> fprintf fmt "{%a}" bitvector c

let output fmt (o : Netlist.output) = variable fmt o

let registerPair fmt (rp : name * Netlist.register_declaration) =
  let name, r = rp in
  fprintf fmt "<%d> (init: %a) <- %a" name bitvector r.init input r.driver

let variablePair fmt (var : name * Netlist.nltype) =
  fprintf fmt "%a <%d>" nltype (snd var) (fst var)

let port fmt (v : int * port_direction) =
  match v with
  | n, PortOut -> fprintf fmt "Out <%d>" n
  | n, PortIn -> fprintf fmt "In <%d>" n

let cell fmt (c : Netlist.cell) =
  match c with
  | Add (out, in1, in2) ->
      fprintf fmt "%a <- Add(%a, %a)" output out input in1 input in2
  | Subtract (out, in1, in2) ->
      fprintf fmt "%a <- Subtract(%a, %a)" output out input in1 input in2
  | Multiply (out, in1, in2) ->
      fprintf fmt "%a <- Multiply(%a, %a)" output out input in1 input in2
  | ShiftLeft (out, in1, in2) ->
      fprintf fmt "%a <- ShiftLeft(%a, %a)" output out input in1 input in2
  | ShiftRight (out, in1, in2) ->
      fprintf fmt "%a <- ShiftRight(%a, %a)" output out input in1 input in2
  | Id (out, in1) -> fprintf fmt "%a <- Id(%a)" output out input in1
  | Convert (out, in1) -> fprintf fmt "%a <- Convert(%a)" output out input in1
  | Mux (out, select, ifT, ifF) ->
      fprintf fmt "%a <- Mux(%a, %a, %a)" output out input select input ifT
        input ifF

let circuit fmt (c : Netlist.circuit) =
  fprintf fmt "Netlist.circuit %s {@." (Util.lst_to_string c.circuitName);
  fprintf fmt "    @[<v>";
  fprintf fmt "ports = [@,    @[<v>%a@]@,];"
    (pp_print_list port ~pp_sep:Util.colon_sep)
    (NameMap.elements c.circuitPorts);
  fprintf fmt "@,";
  fprintf fmt "variables = [@,    @[<v>%a@]@,];"
    (pp_print_list variablePair ~pp_sep:Util.colon_sep)
    (NameMap.elements c.circuitVariables);
  fprintf fmt "@,";
  fprintf fmt "registers = [@,    @[<v>%a@]@,];"
    (pp_print_list registerPair ~pp_sep:Util.colon_sep)
    (NameMap.elements c.circuitRegisters);
  fprintf fmt "@,";
  fprintf fmt "cells = [@,    @[<v>%a@]@,];"
    (pp_print_list cell ~pp_sep:Util.colon_sep)
    c.circuitCells;
  fprintf fmt "@]@.}"
