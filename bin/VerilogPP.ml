open Format
open VVEquiv

let direction fmt d =
  match d with
  | PortIn -> fprintf fmt "In"
  | PortOut -> fprintf fmt "Out"

let vtype fmt t =
  match t with
  | TypedVerilog.Logic (high, low) -> fprintf fmt "logic[%d:%d]" high low

let port (fmt : formatter) (p : TypedVerilog.port) =
  fprintf fmt "%a %s" direction p.portDirection (Util.lst_to_string p.portName)

let variable (fmt : formatter) (p : TypedVerilog.variable) =
  fprintf fmt "%a %s" vtype p.varType (Util.lst_to_string p.varName)

let operator fmt = function
  | TypedVerilog.Plus -> fprintf fmt "+"
  | TypedVerilog.Minus -> fprintf fmt "-"

let rec expression fmt e =
  Format.fprintf fmt "@[";
  (match e with
  | TypedVerilog.IntegerLiteral (sz, n) -> fprintf fmt "%d'd%d" sz n
  | TypedVerilog.Conversion (t, e) ->
      fprintf fmt "( %a )@ as@ ( %a )" expression e vtype t
  | TypedVerilog.BinaryOp (_, op, l, r) ->
      fprintf fmt "( %a )@ %a@ ( %a )" expression l operator op expression r
  | TypedVerilog.NamedExpression (t, name) -> fprintf fmt "%a %s" vtype t (Util.lst_to_string name));
  Format.fprintf fmt "@]"

let mod_item (fmt : formatter) (i : TypedVerilog.module_item) =
  match i with
  | TypedVerilog.ContinuousAssign (l, r) ->
      fprintf fmt "assign (%a) = (@[ %a @])" expression l expression r

let vmodule (fmt : formatter) (m : TypedVerilog.vmodule) =
  fprintf fmt "TypedVerilog.module %s {@." (Util.lst_to_string m.modName);
  fprintf fmt "    @[<v>";
  fprintf fmt "ports = [@,    @[<v>%a@]@,];"
    (pp_print_list port ~pp_sep:Util.colon_sep)
    m.modPorts;
  fprintf fmt "@,";
  fprintf fmt "variables = [@,    @[<v>%a@]@,];"
    (pp_print_list variable ~pp_sep:Util.colon_sep)
    m.modVariables;
  fprintf fmt "@,";
  fprintf fmt "body = [@,    @[<v>%a@]@,];"
    (pp_print_list mod_item ~pp_sep:Util.colon_sep)
    m.modBody;
  fprintf fmt "@]@.}"
