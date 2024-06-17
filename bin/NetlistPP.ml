open Format
open VVEquiv

let nltype fmt (t : Netlist.nltype) =
  (* nltype gets extracted to just int *)
  fprintf fmt "logic[%d]" t

let variable fmt (v : Netlist.variable) =
  fprintf fmt "%a <%d>" nltype v.varType v.varName

let variablePair fmt (var : (name * Netlist.nltype)) =
  fprintf fmt "%a <%d>" nltype (snd var) (fst var)

let port fmt (v : int * port_direction) =
  match v with
  | n, PortOut -> fprintf fmt "Out <%d>" n
  | n, PortIn -> fprintf fmt "In <%d>" n

let bitvector fmt (bv : Bitvector.bv) = fprintf fmt "%d'd%d" bv.width bv.value

let input fmt (i : Netlist.input) =
  match i with InVar v -> variable fmt v | InConstant c -> bitvector fmt c

let output fmt (o : Netlist.output) = variable fmt o

let cell fmt (c : Netlist.cell) =
  match c with
  | Add (out, in1, in2) ->
      fprintf fmt "%a <- Add(%a, %a)" output out input in1 input in2
  | Subtract (out, in1, in2) ->
      fprintf fmt "%a <- Subtract(%a, %a)" output out input in1 input in2
  | Id (out, in1) -> fprintf fmt "%a <- Id(%a)" output out input in1
  | Convert (out, in1) ->
      fprintf fmt "%a <- Convert(%a)" output out input in1

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
  fprintf fmt "cells = [@,    @[<v>%a@]@,];"
    (pp_print_list cell ~pp_sep:Util.colon_sep)
    c.circuitCells;
  fprintf fmt "@]@.}"
