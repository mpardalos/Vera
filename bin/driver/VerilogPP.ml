open Format
open Vera

let arithmeticop fmt = function
  | Verilog.ArithmeticPlus -> fprintf fmt "+"
  | Verilog.ArithmeticMinus -> fprintf fmt "-"
  | Verilog.ArithmeticStar -> fprintf fmt "*"
  (* | Verilog.BinarySlash -> fprintf fmt "/" *)
  (* | Verilog.BinaryPercent -> fprintf fmt "%%" *)

let bitwiseop fmt = function
  | Verilog.BinaryBitwiseAnd -> fprintf fmt "&"
  | Verilog.BinaryBitwiseOr -> fprintf fmt "|"
  (* | Verilog.BinaryBitwiseXor -> fprintf fmt "^" *)
  (* | Verilog.BinaryXNor -> fprintf fmt "^~" *)

let shiftop fmt = function
  | Verilog.BinaryShiftRight -> fprintf fmt ">>"
  | Verilog.BinaryShiftLeft -> fprintf fmt "<<"
  (* | Verilog.BinaryShiftRightArithmetic -> fprintf fmt ">>>" *)
  | Verilog.BinaryShiftLeftArithmetic -> fprintf fmt "<<<"

  (* | Verilog.BinaryEqualsEquals -> fprintf fmt "==" *)
  (* | Verilog.BinaryNotEquals -> fprintf fmt "!=" *)
  (* | Verilog.BinaryEqualsEqualsEquals -> fprintf fmt "===" *)
  (* | Verilog.BinaryNotEqualsEquals -> fprintf fmt "!==" *)
  (* | Verilog.BinaryWildcardEqual -> fprintf fmt "==?" *)
  (* | Verilog.BinaryWildcardNotEqual -> fprintf fmt "!=?" *)
  (* | Verilog.BinaryLogicalAnd -> fprintf fmt "&&" *)
  (* | Verilog.BinaryLogicalOr -> fprintf fmt "||" *)
  (* | Verilog.BinaryExponent -> fprintf fmt "**" *)
  (* | Verilog.BinaryLessThan -> fprintf fmt "<" *)
  (* | Verilog.BinaryLessThanEqual -> fprintf fmt "<=" *)
  (* | Verilog.BinaryGreaterThan -> fprintf fmt ">" *)
  (* | Verilog.BinaryGreaterThanEqual -> fprintf fmt ">=" *)
  (* | Verilog.BinaryLogicalImplication -> fprintf fmt "->" *)
  (* | Verilog.BinaryLogicalEquivalence -> fprintf fmt "<->" *)

(* let unaryop fmt = function *)
(*   | Verilog.UnaryPlus -> fprintf fmt "+" *)
(*   | Verilog.UnaryMinus -> fprintf fmt "-" *)
(*   | Verilog.UnaryNegation -> fprintf fmt "!" *)

let direction fmt d =
  match d with PortIn -> fprintf fmt "In" | PortOut -> fprintf fmt "Out"

let vtype fmt t = fprintf fmt "<%d>" t

let vector_declaration fmt t =
  match t with
  | Verilog.Vector (high, low) -> fprintf fmt "[%d:%d]" high low
  | Verilog.Scalar -> ()

let port_declaration fmt = function
  | None -> ()
  | Some Vera.PortIn -> fprintf fmt "input"
  | Some Vera.PortOut -> fprintf fmt "output"

let variable_declaration (fmt : formatter) (var : Verilog.variable_declaration) =
  fprintf fmt "%s%a %a"
    (Util.lst_to_string var.varDeclName)
    vector_declaration var.varDeclVectorDeclaration
    port_declaration var.varDeclPort

let net_type (fmt : formatter) (t : Verilog.coq_StorageType) =
  match t with
  | Verilog.Reg -> fprintf fmt "reg"
  | Verilog.Wire -> fprintf fmt "wire"

module Raw = struct
  let rec expression fmt e =
    Format.fprintf fmt "@[";
    (match e with
    | RawVerilog.IntegerLiteral v ->
        fprintf fmt "%d'b%s" (Vera.RawBV.size v) (Util.lst_to_string (Vera.bits_to_binary_string v))
    | RawVerilog.BitSelect (target, index) ->
        fprintf fmt "%a[%a]" expression target expression index
    | RawVerilog.Concatenation (lhs, rhs) ->
        fprintf fmt "{%a %a}" expression lhs expression rhs
    | RawVerilog.Conditional (cond, t, f) ->
        fprintf fmt "( %a ?@ %a :@ %a )" expression cond expression t expression
          f
    | RawVerilog.ArithmeticOp (op, l, r) ->
        fprintf fmt "( %a@ %a@ %a )" expression l arithmeticop op expression r
    | RawVerilog.BitwiseOp (op, l, r) ->
        fprintf fmt "( %a@ %a@ %a )" expression l bitwiseop op expression r
    | RawVerilog.ShiftOp (op, l, r) ->
        fprintf fmt "( %a@ %a@ %a )" expression l shiftop op expression r
    | RawVerilog.UnaryOp ((* op, *) e) ->
        (* fprintf fmt "( %a@ %a )" unaryop op expression e *)
        fprintf fmt "( +@ %a )" expression e
    | RawVerilog.NamedExpression var ->
        fprintf fmt "%s" (Util.lst_to_string var.varName)
    | RawVerilog.Resize (n, e) ->
        fprintf fmt "( %a@ as@ %a )" expression e vtype n);
    Format.fprintf fmt "@]"

  let rec statement (fmt : formatter) (s : RawVerilog.statement) =
    match s with
    | RawVerilog.Block body ->
        fprintf fmt "begin @,    @[<v>%a@]@,end"
          (pp_print_list statement ~pp_sep:Util.colon_sep)
          body
    | RawVerilog.BlockingAssign (lhs, rhs) ->
        fprintf fmt "%a = %a" expression lhs expression rhs
    | RawVerilog.NonBlockingAssign (lhs, rhs) ->
        fprintf fmt "%a <= %a" expression lhs expression rhs
    | RawVerilog.If (cond, trueBranch, falseBranch) ->
        fprintf fmt "if %a then %a else %a" expression cond statement trueBranch
          statement falseBranch

  let mod_item (fmt : formatter) (i : RawVerilog.module_item) =
    match i with
    | RawVerilog.Initial body -> fprintf fmt "initial %a" statement body
    | RawVerilog.AlwaysComb body ->
        fprintf fmt "always_comb %a" statement body
    | RawVerilog.AlwaysFF body ->
        fprintf fmt "always_ff @(posedge clk) %a" statement body

  let vmodule (fmt : formatter) (m : RawVerilog.vmodule) =
    fprintf fmt "RawVerilog.module %s {@." (Util.lst_to_string m.modName);
    fprintf fmt "    @[<v>";
    fprintf fmt "variables = [@,    @[<v>%a@]@,];"
      (pp_print_list variable_declaration ~pp_sep:Util.colon_sep)
      m.modVariableDecls;
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
    | Verilog.IntegerLiteral (_, v) ->
        fprintf fmt "%d'b%s" (Vera.RawBV.size v) (Util.lst_to_string (Vera.bits_to_binary_string v))
    | Verilog.Resize (_, t, e) ->
        fprintf fmt "( %a@ as@ %a )" expression e vtype t
    | Verilog.ArithmeticOp (_, op, l, r) ->
        fprintf fmt "( %a@ %a@ %a )" expression l arithmeticop op expression r
    | Verilog.BitwiseOp (_, op, l, r) ->
        fprintf fmt "( %a@ %a@ %a )" expression l bitwiseop op expression r
    | Verilog.ShiftOp (_, _, op, l, r) ->
        fprintf fmt "( %a@ %a@ %a )" expression l shiftop op expression r
    | Verilog.UnaryOp (_, e) ->
        (* fprintf fmt "( %a@ %a )" unaryop op expression e *)
        fprintf fmt "( +@ %a )" expression e
    | Verilog.BitSelect (_, _, target, index) ->
        fprintf fmt "%a[%a]" expression target expression index
    | Verilog.Concatenation (_, _, lhs, rhs) ->
        fprintf fmt "{%a %a}" expression lhs expression rhs
    | Verilog.Conditional (_, _, cond, t, f) ->
        fprintf fmt "( %a ?@ %a :@ %a )" expression cond expression t expression
          f
    | Verilog.NamedExpression {varName; varType} ->
        fprintf fmt "%s%a" (Util.lst_to_string varName) vtype varType);
    Format.fprintf fmt "@]"

  let rec statement (fmt : formatter) (s : Verilog.statement) =
    match s with
    | Verilog.Block body ->
        fprintf fmt "begin @,    @[<v>%a@]@,end"
          (pp_print_list statement ~pp_sep:Util.colon_sep)
          body
    | Verilog.BlockingAssign (_, lhs, rhs) ->
        fprintf fmt "%a = %a" expression lhs expression rhs
    | Verilog.NonBlockingAssign (_, lhs, rhs) ->
        fprintf fmt "%a <= %a" expression lhs expression rhs
    | Verilog.If (_, cond, trueBranch, falseBranch) ->
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
    fprintf fmt "@,";
    fprintf fmt "variables = [@,    @[<v>%a@]@,];"
      (pp_print_list variable_declaration ~pp_sep:Util.colon_sep)
      m.modVariableDecls;
    fprintf fmt "@,";
    fprintf fmt "body = [@,    @[<v>%a@]@,];"
      (pp_print_list mod_item ~pp_sep:Util.colon_sep)
      m.modBody;
    fprintf fmt "@]@.}"
end
