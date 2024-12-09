open Format
open Vera

let operator fmt = function
  | Verilog.BinaryPlus -> fprintf fmt "+"
  | Verilog.BinaryMinus -> fprintf fmt "-"
  | Verilog.BinaryStar -> fprintf fmt "*"
  | Verilog.BinarySlash -> fprintf fmt "/"
  | Verilog.BinaryPercent -> fprintf fmt "%%"
  | Verilog.BinaryEqualsEquals -> fprintf fmt "=="
  | Verilog.BinaryNotEquals -> fprintf fmt "!="
  | Verilog.BinaryEqualsEqualsEquals -> fprintf fmt "==="
  | Verilog.BinaryNotEqualsEquals -> fprintf fmt "!=="
  | Verilog.BinaryWildcardEqual -> fprintf fmt "==?"
  | Verilog.BinaryWildcardNotEqual -> fprintf fmt "!=?"
  | Verilog.BinaryLogicalAnd -> fprintf fmt "&&"
  | Verilog.BinaryLogicalOr -> fprintf fmt "||"
  | Verilog.BinaryExponent -> fprintf fmt "**"
  | Verilog.BinaryLessThan -> fprintf fmt "<"
  | Verilog.BinaryLessThanEqual -> fprintf fmt "<="
  | Verilog.BinaryGreaterThan -> fprintf fmt ">"
  | Verilog.BinaryGreaterThanEqual -> fprintf fmt ">="
  | Verilog.BinaryBitwiseAnd -> fprintf fmt "&"
  | Verilog.BinaryBitwiseOr -> fprintf fmt "|"
  | Verilog.BinaryBitwiseXor -> fprintf fmt "^"
  | Verilog.BinaryXNor -> fprintf fmt "^~"
  | Verilog.BinaryShiftRight -> fprintf fmt ">>"
  | Verilog.BinaryShiftLeft -> fprintf fmt "<<"
  | Verilog.BinaryShiftRightArithmetic -> fprintf fmt ">>>"
  | Verilog.BinaryShiftLeftArithmetic -> fprintf fmt "<<<"
  | Verilog.BinaryLogicalImplication -> fprintf fmt "->"
  | Verilog.BinaryLogicalEquivalence -> fprintf fmt "<->"

let direction fmt d =
  match d with PortIn -> fprintf fmt "In" | PortOut -> fprintf fmt "Out"

let vtype fmt t = fprintf fmt "<%d>" t

let vector_declaration fmt t =
  match t with
  | Verilog.Vector (high, low) -> fprintf fmt "[%d:%d]" high low
  | Verilog.Scalar -> ()

let port (fmt : formatter) (p : Verilog.port) =
  fprintf fmt "%a %s" direction p.portDirection (Util.lst_to_string p.portName)

let variable (fmt : formatter) (p : UntypedVerilog.variable) =
  fprintf fmt "%s%a"
    (Util.lst_to_string p.varName)
    vector_declaration p.varVectorDeclaration

let net_type (fmt : formatter) (t : UntypedVerilog.coq_StorageType) =
  match t with
  | Verilog.Reg -> fprintf fmt "reg"
  | Verilog.Wire -> fprintf fmt "wire"

module Untyped = struct
  let rec expression fmt e =
    Format.fprintf fmt "@[";
    (match e with
    | UntypedVerilog.IntegerLiteral v ->
        fprintf fmt "%d'd%d" (Vera.BV.size v) (bits_to_int v)
    | UntypedVerilog.BitSelect (target, index) ->
        fprintf fmt "%a[%a]" expression target expression index
    | UntypedVerilog.Conditional (cond, t, f) ->
        fprintf fmt "( %a ?@ %a :@ %a )" expression cond expression t expression
          f
    | UntypedVerilog.BinaryOp (op, l, r) ->
        fprintf fmt "( %a@ %a@ %a )" expression l operator op expression r
    | UntypedVerilog.NamedExpression (_, name) ->
        fprintf fmt "%s" (Util.lst_to_string name)
    | UntypedVerilog.Resize (n, e) ->
        fprintf fmt "( %a@ as@ %a )" expression e vtype n);
    Format.fprintf fmt "@]"

  let rec statement (fmt : formatter) (s : UntypedVerilog.statement) =
    match s with
    | UntypedVerilog.Block body ->
        fprintf fmt "begin @,    @[<v>%a@]@,end"
          (pp_print_list statement ~pp_sep:Util.colon_sep)
          body
    | UntypedVerilog.BlockingAssign (lhs, rhs) ->
        fprintf fmt "%a = %a" expression lhs expression rhs
    | UntypedVerilog.NonBlockingAssign (lhs, rhs) ->
        fprintf fmt "%a <= %a" expression lhs expression rhs
    | UntypedVerilog.If (cond, trueBranch, falseBranch) ->
        fprintf fmt "if %a then %a else %a" expression cond statement trueBranch
          statement falseBranch

  let mod_item (fmt : formatter) (i : UntypedVerilog.module_item) =
    match i with
    | UntypedVerilog.Initial body -> fprintf fmt "initial %a" statement body
    | UntypedVerilog.AlwaysComb body ->
        fprintf fmt "always_comb %a" statement body
    | UntypedVerilog.AlwaysFF body ->
        fprintf fmt "always_ff @(posedge clk) %a" statement body

  let vmodule (fmt : formatter) (m : UntypedVerilog.vmodule) =
    fprintf fmt "UntypedVerilog.module %s {@." (Util.lst_to_string m.modName);
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

  let optionally (f : formatter -> 'a -> unit) (fmt : formatter) (v : 'a option)
      =
    match v with Some x -> f fmt x | None -> ()

  let optionally_space (f : formatter -> 'a -> unit) (fmt : formatter)
      (v : 'a option) =
    match v with Some x -> fprintf fmt "%a " f x | None -> ()
end

module Typed = struct
  open Format
  open Vera

  let direction fmt d =
    match d with PortIn -> fprintf fmt "In" | PortOut -> fprintf fmt "Out"

  let rec expression fmt e =
    Format.fprintf fmt "@[";
    (match e with
    | Verilog.IntegerLiteral v ->
        fprintf fmt "%d'd%d" (Vera.BV.size v) (bits_to_int v)
    | Verilog.Resize (t, e) ->
        fprintf fmt "( %a@ as@ %a )" expression e vtype t
    | Verilog.BinaryOp (op, l, r) ->
        fprintf fmt "( %a@ %a@ %a )" expression l operator op expression r
    | Verilog.BitSelect (target, index) ->
        fprintf fmt "%a[%a]" expression target expression index
    | Verilog.Conditional (cond, t, f) ->
        fprintf fmt "( %a ?@ %a :@ %a )" expression cond expression t expression
          f
    | Verilog.NamedExpression (t, name) ->
        fprintf fmt "%s%a" (Util.lst_to_string name) vtype t);
    Format.fprintf fmt "@]"

  let rec statement (fmt : formatter) (s : Verilog.statement) =
    match s with
    | Verilog.Block body ->
        fprintf fmt "begin @,    @[<v>%a@]@,end"
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
    | Verilog.Initial body -> fprintf fmt "initial %a" statement body
    | Verilog.AlwaysComb body ->
        fprintf fmt "always_comb %a" statement body
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
end
