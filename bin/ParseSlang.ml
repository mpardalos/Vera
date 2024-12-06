open Yojson.Safe.Util

(* module Monad (M : sig *)
(*   type 'a m *)

(*   val bind : 'a m -> ('a -> 'b m) -> 'b m *)
(*   val ret : 'a -> 'a m *)
(* end) = *)
(* struct *)
(*   include M *)

(*   let ( >>= ) = bind *)
(*   let ( let* ) = bind *)
(*   let ( =<< ) a b = b >>= a *)

(*   let fmap f x = *)
(*     let* xval = x in *)
(*     ret (f xval) *)

(*   let ( <$> ) = fmap *)
(*   let ( <&> ) x f = fmap f x *)

(*   let ( >=> ) f g x = *)
(*     let* y = f x in *)
(*     g y *)
(* end *)

(* module ResultMonad = Monad (struct *)
(*   type 'a m = ('a, string) result *)

(*   let bind x f = match x with Ok v -> f v | Error e -> Error e *)
(*   let ret x = Ok x *)
(* end) *)

(* open ResultMonad *)

exception SlangUnexpectedValue of string * string

let () =
  Printexc.register_printer (function
    | SlangUnexpectedValue (expected, got) ->
        Some
          (Printf.sprintf
             "Unexpected value during slang parsing:\n\
              Expected '%s', but got '%s'" expected got)
    | _ -> None (* for other exceptions *))

let not_null msg = function
  | `Null -> raise (SlangUnexpectedValue (msg, "null"))
  | _ -> ()

let expect_value a b = if a = b then () else raise (SlangUnexpectedValue (a, b))

let expect_kind a json =
  not_null a json;
  json |> member "kind" |> to_string |> expect_value a

let parse_port json =
  expect_kind "Port" json;
  let name = json |> member "name" |> to_string |> Util.string_to_lst in
  let direction =
    match json |> member "direction" |> to_string with
    | "In" -> Vera.PortIn
    | "Out" -> Vera.PortOut
    | str ->
        raise (Failure (Format.sprintf "Unexpected port direction: %s" str))
  in
  { Vera.Verilog.portDirection = direction; Vera.Verilog.portName = name }

let read_type_as_vector = function
  | "logic" -> Vera.Verilog.Scalar
  | str -> (
      try
        Scanf.sscanf str "logic[%d:%d]" (fun hi lo ->
            Vera.Verilog.Vector (hi, lo))
      with Scanf.Scan_failure _ ->
        raise (SlangUnexpectedValue ("logic[%d:%d]", str)))

let read_type_as_width = function
  | "logic" -> 1
  | str -> (
      try
        Scanf.sscanf str "logic[%d:%d]" (fun hi lo -> max hi lo - min hi lo + 1)
      with Scanf.Scan_failure _ ->
        raise (SlangUnexpectedValue ("logic[%d:%d]", str)))

let parse_variable json =
  expect_kind "Variable" json;
  let name = json |> member "name" |> to_string |> Util.string_to_lst in
  let vector_declaration =
    json |> member "type" |> to_string |> read_type_as_vector
  in
  {
    Vera.Verilog.varName = name;
    Vera.Verilog.varStorageType = Vera.Verilog.Reg;
    Vera.Verilog.varVectorDeclaration = vector_declaration;
  }

let parse_net json =
  expect_kind "Net" json;
  let name = json |> member "name" |> to_string |> Util.string_to_lst in
  let vector_declaration =
    json |> member "type" |> to_string |> read_type_as_vector
  in
  {
    Vera.Verilog.varName = name;
    Vera.Verilog.varStorageType = Vera.Verilog.Wire;
    Vera.Verilog.varVectorDeclaration = vector_declaration;
  }

let read_constant const_str =
  let const_str = String.trim const_str in

  (* Regex patterns for different constant formats *)
  let sized_decimal_re = Str.regexp "^\\([0-9]+\\)'d\\([0-9]+\\)$" in
  let sized_binary_re = Str.regexp "^\\([0-9]+\\)'b\\([01]+\\)$" in
  let sized_hex_re = Str.regexp "^\\([0-9]+\\)'h\\([0-9a-fA-F]+\\)$" in
  let unsized_decimal_re = Str.regexp "^\\([0-9]+\\)$" in
  let unsized_prefixed_decimal_re = Str.regexp "^'d\\([0-9]+\\)$" in
  let unsized_prefixed_binary_re = Str.regexp "^'b\\([01]+\\)$" in
  let unsized_prefixed_hex_re = Str.regexp "^'h\\([0-9a-fA-F]+\\)$" in

  try
    (* Try matching sized and unsized formats *)
    if Str.string_match sized_decimal_re const_str 0 then
      let width = int_of_string (Str.matched_group 1 const_str) in
      let value = int_of_string (Str.matched_group 2 const_str) in
      Vera.bits_from_int width value
    else if Str.string_match sized_binary_re const_str 0 then
      let width = int_of_string (Str.matched_group 1 const_str) in
      let value = int_of_string ("0b" ^ Str.matched_group 2 const_str) in
      Vera.bits_from_int width value
    else if Str.string_match sized_hex_re const_str 0 then
      let width = int_of_string (Str.matched_group 1 const_str) in
      let value = int_of_string ("0x" ^ Str.matched_group 2 const_str) in
      Vera.bits_from_int width value
    else if Str.string_match unsized_decimal_re const_str 0 then
      let value = int_of_string const_str in
      Vera.bits_from_int 32 value (* Default to 32-bit for unsized decimal *)
    else if Str.string_match unsized_prefixed_decimal_re const_str 0 then
      let value = int_of_string (Str.matched_group 1 const_str) in
      Vera.bits_from_int 32 value (* Default to 32-bit for unsized decimal *)
    else if Str.string_match unsized_prefixed_binary_re const_str 0 then
      let value = int_of_string ("0b" ^ Str.matched_group 1 const_str) in
      Vera.bits_from_int 32 value (* Default to 32-bit for unsized binary *)
    else if Str.string_match unsized_prefixed_hex_re const_str 0 then
      let value = int_of_string ("0x" ^ Str.matched_group 1 const_str) in
      Vera.bits_from_int 32 value (* Default to 32-bit for unsized hex *)
    else raise (SlangUnexpectedValue ("constant", const_str))
  with
  | Failure _ -> raise (SlangUnexpectedValue ("constant", const_str))
  | Not_found -> raise (SlangUnexpectedValue ("constant", const_str))

let read_binary_op = function
  | "LogicalShiftLeft" -> Vera.Verilog.BinaryShiftLeft
  | "Add" -> Vera.Verilog.BinaryPlus
  | "Subtract" -> Vera.Verilog.BinaryMinus
  | "Multiply" -> Vera.Verilog.BinaryStar
  | "LessThan" -> Vera.Verilog.BinaryLessThan
  | "LessThanEqual" -> Vera.Verilog.BinaryLessThanEqual
  | "GreaterThan" -> Vera.Verilog.BinaryGreaterThan
  | "Equality" -> Vera.Verilog.BinaryEqualsEquals
  | "LogicalAnd" -> Vera.Verilog.BinaryLogicalAnd
  | str -> raise (SlangUnexpectedValue ("binary operator", str))

let read_name str = Scanf.sscanf str "%d %s" (fun _ n -> n)

let rec parse_expression json =
  not_null "expression" json;
  match json |> member "kind" |> to_string with
  | "NamedValue" ->
      let name = read_name (json |> member "symbol" |> to_string) in
      Vera.Verilog.NamedExpression ((), Util.string_to_lst name)
  | "ConditionalOp" ->
      let cond =
        json |> member "conditions" |> to_list |> List.hd |> member "expr"
        |> parse_expression
      in
      let ifTrue = json |> member "left" |> parse_expression in
      let ifFalse = json |> member "left" |> parse_expression in
      Vera.Verilog.Conditional (cond, ifTrue, ifFalse)
  | "ElementSelect" ->
      let value = json |> member "value" |> parse_expression in
      let selector = json |> member "selector" |> parse_expression in
      Vera.Verilog.BitSelect (value, selector)
  | "IntegerLiteral" ->
      let constant_str = json |> member "constant" |> to_string in
      Vera.Verilog.IntegerLiteral (read_constant constant_str)
  | "Conversion" ->
      let conversion_type =
        json |> member "type" |> to_string |> read_type_as_width
      in
      let operand = json |> member "operand" |> parse_expression in
      Vera.Verilog.Resize (conversion_type, operand)
  | "BinaryOp" ->
      let op = json |> member "op" |> to_string |> read_binary_op in
      let lhs = json |> member "left" |> parse_expression in
      let rhs = json |> member "right" |> parse_expression in
      Vera.Verilog.BinaryOp (op, lhs, rhs)
  | kind -> Vera.Verilog.NamedExpression ((), Util.string_to_lst kind)

let rec parse_statement json =
  not_null "statement" json;
  match json |> member "kind" |> to_string with
  | "ExpressionStatement" ->
      let expr = json |> member "expr" in
      expect_kind "Assignment" expr;
      let lhs = parse_expression (expr |> member "left") in
      let rhs = parse_expression (expr |> member "right") in
      Vera.Verilog.BlockingAssign (lhs, rhs)
  | "Block" ->
      json |> member "blockKind" |> to_string |> expect_value "Sequential";
      let body =
        match json |> member "body" |> member "kind" |> to_string with
        | "List" ->
            json |> member "body" |> member "list" |> to_list
            |> List.map parse_statement
        | _ -> [ parse_statement (json |> member "body") ]
      in
      Vera.Verilog.Block body
  | "Conditional" ->
      let cond =
        json |> member "conditions" |> to_list |> List.hd |> member "expr"
        |> parse_expression
      in
      let ifTrue = json |> member "ifTrue" |> parse_statement in
      let ifFalse =
        match json |> member "ifFalse" with
        | `Null -> Vera.Verilog.Block []
        | stmt -> parse_statement stmt
      in
      Vera.Verilog.If (cond, ifTrue, ifFalse)
  | str -> raise (SlangUnexpectedValue ("statement kind", str))

let parse_continuous_assign json =
  expect_kind "ContinuousAssign" json;
  let assignment = json |> member "assignment" in
  expect_kind "Assignment" assignment;
  let lhs = parse_expression (assignment |> member "left") in
  let rhs = parse_expression (assignment |> member "right") in
  Vera.Verilog.AlwaysComb (Vera.Verilog.BlockingAssign (lhs, rhs))

let parse_procedural_block json =
  expect_kind "ProceduralBlock" json;
  let body = json |> member "body" in
  match json |> member "procedureKind" |> to_string with
  | "AlwaysComb" -> Vera.Verilog.AlwaysComb (parse_statement body)
  | "AlwaysFF" | "Always" ->
      expect_kind "Timed" body;
      expect_kind "SignalEvent" (body |> member "timing");
      expect_kind "NamedValue" (body |> member "timing" |> member "expr");
      body |> member "timing" |> member "expr" |> member "symbol" |> to_string
      |> read_name |> expect_value "clk";
      Vera.Verilog.AlwaysFF (parse_statement (body |> member "stmt"))
  | "Initial" ->
      let body = json |> member "body" |> parse_statement in
      Vera.Verilog.Initial body
  | str ->
      raise (SlangUnexpectedValue ("AlwaysComb, AlwaysFF, or Initial", str))

let collect_instance_member (ports : Vera.Verilog.port list ref)
    (variables : Vera.Verilog.variable list ref)
    (body : Vera.Verilog.module_item list ref) json =
  match to_string (member "kind" json) with
  | "Port" -> ports := List.append !ports [ parse_port json ]
  | "Variable" -> variables := List.append !variables [ parse_variable json ]
  | "Net" -> variables := List.append !variables [ parse_net json ]
  | "ContinuousAssign" ->
      body := List.append !body [ parse_continuous_assign json ]
  | "ProceduralBlock" ->
      body := List.append !body [ parse_procedural_block json ]
  | kind ->
      raise
        (Failure (Format.sprintf "Unexpected instance member kind: %s" kind))

let parse_instance_body (json : Yojson.Safe.t) : Vera.Verilog.vmodule =
  expect_kind "InstanceBody" json;
  let name = json |> member "name" |> to_string in
  let ports_ref = ref [] in
  let variables_ref = ref [] in
  let body_ref = ref [] in
  List.iter
    (collect_instance_member ports_ref variables_ref body_ref)
    (json |> member "members" |> to_list);
  {
    modName = Util.string_to_lst name;
    modPorts = !ports_ref;
    modVariables = !variables_ref;
    modBody = !body_ref;
  }

let parse_slang (json : Yojson.Safe.t) : Vera.Verilog.vmodule =
  expect_kind "Root" json;
  parse_instance_body
    (json |> member "members" |> to_list
    |> List.filter (fun m -> to_string (member "kind" m) = "Instance")
    |> List.hd |> member "body")

let parse_verilog_file (path : string) : Vera.Verilog.vmodule =
  let slang_out =
    Unix.open_process_in (Format.sprintf "slang --quiet --ast-json - %s" path)
  in
  let slang_json = Yojson.Safe.from_channel slang_out in
  parse_slang slang_json
