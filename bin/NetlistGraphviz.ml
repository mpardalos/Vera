open Format
open Vera

let bitvector fmt (bv : bits) =
  fprintf fmt "%d'd%d" (N.of_nat (size bv)) (N.of_nat (bits_to_nat bv))

let declare_variable fmt (v : Netlist.variable) =
  fprintf fmt "v%d [label=\"v%d<%d>\"]" v.varName v.varName
    (int_from_nat v.varType)

let variable fmt (v : Netlist.variable) = fprintf fmt "v%d" v.varName
let variableName fmt (n : name) = fprintf fmt "v%d" n

let variablePair fmt (var : name * Netlist.nltype) =
  variable fmt { varName = fst var; varType = snd var }

let output fmt (o : Netlist.output) = variable fmt o

let port fmt (v : int * port_direction) =
  match v with
  | n, PortOut -> fprintf fmt "%a -> OUT;" variableName n
  | n, PortIn -> fprintf fmt "IN -> %a;" variableName n

let next_name = ref 0

let cell_input fmt (c_name : string) (i : Netlist.input) =
  let input_node =
    match i with
    | InVar v -> asprintf "%a" variable v
    | InConstant c ->
        let idx = !next_name in
        next_name := !next_name + 1;
        let constant_name = sprintf "constant_%d" idx in
        fprintf fmt "%s [label=\"%a\"]" constant_name bitvector c;
        constant_name
  in
  fprintf fmt "%s -> %s;@," input_node c_name

let cell_output fmt (c_name : string) (o : Netlist.output) =
  fprintf fmt "%s -> %a;@," c_name variable o

let cell_node fmt name label =
  fprintf fmt "%s [label=\"%s\", shape=rectangle];@," name label

let cell fmt (c : Netlist.cell) =
  let idx = !next_name in
  next_name := !next_name + 1;
  match c with
  | BinaryCell (op, out, in1, in2) ->
      let name = sprintf "BinaryCell_%d" idx in
      cell_node fmt name (asprintf "%a" VerilogPP.operator op);
      cell_input fmt name in1;
      cell_input fmt name in2;
      cell_output fmt name out;
  | Id (out, in1) ->
      let name = sprintf "Id_%d" idx in
      cell_node fmt name "Id";
      cell_input fmt name in1;
      cell_output fmt name out;
  | BitSelect (out, in_vec, in_idx) ->
      let name = sprintf "BitSelect_%d" idx in
      cell_node fmt name "BitSelect";
      cell_input fmt name in_vec;
      cell_input fmt name in_idx;
      cell_output fmt name out;
  | Convert (out, in1) ->
      let name = sprintf "Convert_%d" idx in
      cell_node fmt name "Convert";
      cell_input fmt name in1;
      cell_output fmt name out;
  | Mux (out, select, ifT, ifF) ->
      let name = sprintf "Mux_%d" idx in
      cell_node fmt name "Mux";
      cell_input fmt name select;
      cell_input fmt name ifT;
      cell_input fmt name ifF;
      cell_output fmt name out

let circuit fmt (c : Netlist.circuit) =
  fprintf fmt "digraph %s {@.    @[<v>" (Util.lst_to_string c.circuitName);
  fprintf fmt "{ rank=source IN [shape=diamond]; }@,";
  fprintf fmt "{ rank=sink OUT [shape=diamond]; }@,";
  fprintf fmt "%a@," (pp_print_list port) (NameMap.elements c.circuitPorts);
  fprintf fmt "@,";
  fprintf fmt "%a@," (pp_print_list cell) c.circuitCells;
  fprintf fmt "@]@.}"

(* fprintf fmt "Netlist.circuit %s {@." (Util.lst_to_string c.circuitName); *)
(* fprintf fmt "    @[<v>"; *)
(* fprintf fmt "ports = [@,    @[<v>%a@]@,];" *)
(*   (pp_print_list port ~pp_sep:Util.colon_sep) *)
(*   (NameMap.elements c.circuitPorts); *)
(* fprintf fmt "@,"; *)
(* fprintf fmt "variables = [@,    @[<v>%a@]@,];" *)
(*   (pp_print_list variablePair ~pp_sep:Util.colon_sep) *)
(*   (NameMap.elements c.circuitVariables); *)
(* fprintf fmt "@,"; *)
(* fprintf fmt "registers = [@,    @[<v>%a@]@,];" *)
(*   (pp_print_list registerPair ~pp_sep:Util.colon_sep) *)
(*   (NameMap.elements c.circuitRegisters); *)
(* fprintf fmt "@,"; *)
(* fprintf fmt "cells = [@,    @[<v>%a@]@,];" *)
(*   (pp_print_list cell ~pp_sep:Util.colon_sep) *)
(*   c.circuitCells; *)
(* fprintf fmt "@]@.}" *)
