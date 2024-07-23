open Format
open VVEquiv

let direction fmt d =
  match d with
  | PortIn -> fprintf fmt "In"
  | PortOut -> fprintf fmt "Out"

let vtype fmt t =
  match t with
  | Verilog.Logic (high, low) -> fprintf fmt "logic[%d:%d]" high low

let port (fmt : formatter) (p : Verilog.port) =
  fprintf fmt "%a %s" direction p.portDirection (Util.lst_to_string p.portName)

let variable (fmt : formatter) (p : Verilog.variable) =
  fprintf fmt "%s" (Util.lst_to_string p.varName)

let operator fmt = function
  | Verilog.Plus -> fprintf fmt "+"
  | Verilog.Minus -> fprintf fmt "-"

let rec expression fmt e =
    Format.fprintf fmt "@[";
    (match e with
    | Verilog.IntegerLiteral v -> fprintf fmt "%d'd%d" v.width v.value
    | Verilog.BinaryOp (op, l, r) ->
        fprintf fmt "( %a )@ %a@ ( %a )" expression l operator op expression r
    | Verilog.NamedExpression name -> fprintf fmt "%s" (Util.lst_to_string name));
    Format.fprintf fmt "@]"

let rec statement (fmt : formatter) (s : Verilog.statement) =
  match s with
  | Verilog.Block body ->
      fprintf fmt "begin @,    @[<v>%a@,end"
        (pp_print_list statement ~pp_sep:Util.colon_sep)
        body
  | Verilog.BlockingAssign (lhs, rhs) ->
      fprintf fmt "%a = %a" expression lhs expression rhs
  | Verilog.NonBlockingAssign (lhs, rhs) ->
      fprintf fmt "%a <= %a" expression lhs expression rhs
  | Verilog.If (cond, trueBranch, falseBranch) ->
      fprintf fmt "if %a then %a else %a" expression cond statement trueBranch
        statement falseBranch

let mod_item (fmt : formatter) (i : Verilog.module_item) =
  match i with
  | Verilog.ContinuousAssign (l, r) ->
      fprintf fmt "assign (%a) = (@[ %a @])" expression l expression r
  | Verilog.AlwaysFF body ->
      fprintf fmt "always_ff (@posedge clk) %a" statement body

let vmodule (fmt : formatter) (m : Verilog.vmodule) =
  fprintf fmt "Verilog.module %s {@." (Util.lst_to_string m.modName);
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
