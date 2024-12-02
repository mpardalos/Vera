open Format
open Vera

let direction fmt d =
  match d with PortIn -> fprintf fmt "In" | PortOut -> fprintf fmt "Out"

let rec expression fmt e =
  Format.fprintf fmt "@[";
  (match e with
   | TypedVerilog.IntegerLiteral (w, v) ->
       fprintf fmt "%d'd%d" w (bits_to_int v)
   | TypedVerilog.Annotation (t, e) ->
       fprintf fmt "( %a@ as@ %a )" expression e VerilogPP.vtype t
   | TypedVerilog.BinaryOp (_, op, l, r) ->
       fprintf fmt "( %a@ %a@ %a )" expression l VerilogPP.operator op
         expression r
   | TypedVerilog.BitSelect (target, index) ->
       fprintf fmt "%a[%a]" expression target expression index
   | TypedVerilog.Conditional (cond, t, f) ->
       fprintf fmt "( %a ?@ %a :@ %a )" expression cond expression t expression f
   | TypedVerilog.NamedExpression (t, name) ->
       fprintf fmt "%s%a" (Util.lst_to_string name) VerilogPP.vtype t);
  Format.fprintf fmt "@]"

let rec statement (fmt : formatter) (s : TypedVerilog.statement) =
  match s with
  | TypedVerilog.Block body ->
      fprintf fmt "begin @,    @[<v>%a@]@,end"
        (pp_print_list statement ~pp_sep:Util.colon_sep)
        body
  | TypedVerilog.BlockingAssign (lhs, rhs) ->
      fprintf fmt "%a = %a" expression lhs expression rhs
  | TypedVerilog.NonBlockingAssign (lhs, rhs) ->
      fprintf fmt "%a <= %a" expression lhs expression rhs
  | TypedVerilog.If (cond, trueBranch, falseBranch) ->
      fprintf fmt "if %a then %a else %a" expression cond statement trueBranch
        statement falseBranch

let mod_item (fmt : formatter) (i : TypedVerilog.module_item) =
  match i with
  | TypedVerilog.Initial body ->
      fprintf fmt "initial %a" statement body
  | TypedVerilog.AlwaysComb body ->
      fprintf fmt "always_comb %a" statement body
  | TypedVerilog.AlwaysFF body ->
      fprintf fmt "always_ff (@posedge clk) %a" statement body

let vmodule (fmt : formatter) (m : TypedVerilog.vmodule) =
  fprintf fmt "TypedVerilog.module %s {@." (Util.lst_to_string m.modName);
  fprintf fmt "    @[<v>";
  fprintf fmt "ports = [@,    @[<v>%a@]@,];"
    (pp_print_list VerilogPP.port ~pp_sep:Util.colon_sep)
    m.modPorts;
  fprintf fmt "@,";
  fprintf fmt "variables = [@,    @[<v>%a@]@,];"
    (pp_print_list VerilogPP.variable ~pp_sep:Util.colon_sep)
    m.modVariables;
  fprintf fmt "@,";
  fprintf fmt "body = [@,    @[<v>%a@]@,];"
    (pp_print_list mod_item ~pp_sep:Util.colon_sep)
    m.modBody;
  fprintf fmt "@]@.}"
