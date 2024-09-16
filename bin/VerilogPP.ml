open Format
open Vera

let direction fmt d =
  match d with PortIn -> fprintf fmt "In" | PortOut -> fprintf fmt "Out"

let vtype fmt t =
  match t with Verilog.Logic (high, low) -> fprintf fmt "[%d:%d]" high low

let port (fmt : formatter) (p : Verilog.port) =
  fprintf fmt "%a %s" direction p.portDirection (Util.lst_to_string p.portName)

let variable (fmt : formatter) (p : Verilog.variable) =
  fprintf fmt "%s%a" (Util.lst_to_string p.varName) vtype p.varType

let net_type (fmt : formatter) (t : Verilog.coq_StorageType) =
  match t with
  | Verilog.Reg -> fprintf fmt "reg"
  | Verilog.Wire -> fprintf fmt "wire"

let operator fmt = function
  | Verilog.Plus -> fprintf fmt "+"
  | Verilog.Minus -> fprintf fmt "-"
  | Verilog.Multiply -> fprintf fmt "*"
  | Verilog.ShiftLeft -> fprintf fmt "<<"
  | Verilog.ShiftRight -> fprintf fmt ">>"

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

let optionally (f : formatter -> 'a -> unit) (fmt : formatter) (v : 'a option) =
  match v with Some x -> f fmt x | None -> ()

let optionally_space (f : formatter -> 'a -> unit) (fmt : formatter) (v : 'a option) =
  match v with Some x -> fprintf fmt "%a " f x | None -> ()

let raw_declaration (fmt : formatter) (decl : Verilog.raw_declaration) =
  fprintf fmt "%a%a %a%s"
    (optionally_space direction) decl.rawDeclPortDeclaration
    net_type decl.rawDeclStorageType
    (optionally_space vtype) decl.rawDeclType
    (Util.lst_to_string decl.rawDeclName)

let raw_mod_item (fmt : formatter)
    (m : (Verilog.module_item, Verilog.raw_declaration) sum) =
  match m with
  | Inl item -> mod_item fmt item
  | Inr decl -> raw_declaration fmt decl

let raw_vmodule (fmt : formatter) (m : Verilog.raw_vmodule) =
  fprintf fmt "module %s();@." (Util.lst_to_string m.rawModName);
  (* fprintf fmt "   @[<v>"; *)
  fprintf fmt "@,    @[<v>%a@]@,"
    (pp_print_list raw_mod_item ~pp_sep:Util.colon_sep)
    m.rawModBody;
  fprintf fmt "@]@.endmodule"
