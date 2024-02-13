open Format

let nltype fmt (t : Netlist.nltype) =
  (* nltype gets extracted to just int *)
  fprintf fmt "logic[%d]" t

let variable fmt (v : Netlist.variable) =
  fprintf fmt "%a <%d>" nltype v.varType v.varName

let constant fmt (c : Netlist.constant) =
  fprintf fmt "%d'd%d" c.constWidth c.constValue

let input fmt (i : Netlist.input) =
  match i with InVar v -> variable fmt v | InConstant c -> constant fmt c

let output fmt (o : Netlist.output) = variable fmt o

let cell fmt (c : Netlist.cell) =
  match c with
  | Add (out, in1, in2) ->
      fprintf fmt "%a <- Add(%a, %a)" output out input in1 input in2
  | Subtract (out, in1, in2) ->
      fprintf fmt "%a <- Subtract(%a, %a)" output out input in1 input in2
  | Id (out, in1) -> fprintf fmt "%a <- Id(%a)" output out input in1

let circuit fmt (c : Netlist.circuit) =
  fprintf fmt "Netlist.circuit %s {@." (Util.lst_to_string c.circuitName);
  fprintf fmt "    @[<v>";
  fprintf fmt "variables = [@,    @[<v>%a@]@,];"
    (pp_print_list variable ~pp_sep:Util.colon_sep)
    c.circuitVariables;
  fprintf fmt "@,";
  fprintf fmt "cells = [@,    @[<v>%a@]@,];"
    (pp_print_list cell ~pp_sep:Util.colon_sep)
    c.circuitCells;
  fprintf fmt "@]@.}"
