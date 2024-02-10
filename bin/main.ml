let lst_to_string lst = String.of_seq (List.to_seq lst)
let string_to_lst s = List.of_seq (String.to_seq s)

module FromJson = struct
  open VVEquiv

  exception UnexpectedJson of (string * Yojson.Safe.t)
  exception UnexpectedKind of (string * string)
  exception UnknownType of string
  exception UnknownOp of string
  exception UnknownValue of (string * string)

  let missing_key ((k : string), (j : Yojson.Safe.t)) =
    UnexpectedJson (Printf.sprintf "No key '%s'" k, j)

  let assoc_lookup key assoc =
    Option.map snd (List.find_opt (fun (k, _) -> String.equal k key) assoc)

  let get_key key = function
    | `Assoc lst as json -> (
        match assoc_lookup key lst with
        | Some x -> x
        | None -> raise (missing_key (key, json)))
    | json -> raise (missing_key (key, json))

  let as_string = function
    | `String s -> s
    | json -> raise (UnexpectedJson ("string", json))

  let as_int = function
    | `Int n -> n
    | json -> raise (UnexpectedJson ("int", json))

  let as_list = function
    | `List l -> l
    | json -> raise (UnexpectedJson ("list", json))

  let read_op = function "Add" -> Verilog.Plus | op -> raise (UnknownOp op)

  let read_type (s : string) : Verilog.vtype =
    Scanf.sscanf s "%s@[%d:%d]" (fun t n1 n2 ->
        match t with
        | "reg" | "logic" -> Verilog.Logic (n1, n2)
        | _ -> raise (UnknownType s))

  let read_value (s : string) : int =
    try Scanf.sscanf s "%d'd%d" (fun _length value -> value)
    with Scanf.Scan_failure _ -> Scanf.sscanf s "%d" (fun value -> value)

  let read_symbol s : int * string = Scanf.sscanf s "%d %s" (fun n s -> (n, s))

  let rec read_expression (json : Yojson.Safe.t) : Verilog.expression =
    match as_string (get_key "kind" json) with
    | "BinaryOp" ->
        let op = read_op (as_string (get_key "op" json)) in
        let left_json = get_key "left" json in
        let right_json = get_key "right" json in
        Verilog.BinaryOp
          (op, read_expression left_json, read_expression right_json)
    (* | "NamedValue" -> _ *)
    | "Conversion" ->
        let operand_json = get_key "operand" json in
        let type_str = as_string (get_key "type" json) in
        Verilog.Conversion (read_type type_str, read_expression operand_json)
    | "IntegerLiteral" ->
        Verilog.IntegerLiteral (read_value (as_string (get_key "value" json)))
    | k -> raise (UnexpectedKind ("expression kind", k))

  let assert_kind expected_kind json =
    let kind = as_string (get_key "kind" json) in
    if not (String.equal expected_kind kind) then
      raise (UnexpectedKind (expected_kind, kind))

  let assert_kind_one_of expected_kinds json =
    let kind = as_string (get_key "kind" json) in
    let rec go ks =
      match ks with
      | k :: ks -> if String.equal k kind then () else go ks
      | [] -> raise (UnexpectedKind (String.concat "|" expected_kinds, kind))
    in
    go expected_kinds

  let read_port json : Verilog.port =
    assert_kind "Port" json;
    let direction_str = as_string (get_key "direction" json) in
    let portDirection =
      match direction_str with
      | "Out" -> Verilog.Out
      | "In" -> Verilog.In
      | _ -> raise (UnknownValue ("direction", direction_str))
    in
    let symbol_str = as_string (get_key "internalSymbol" json) in
    let portId, _ = read_symbol symbol_str in
    { portDirection; portId }

  let read_variable json : Verilog.variable =
    assert_kind_one_of [ "Variable"; "Net" ] json;
    let type_str = as_string (get_key "type" json) in
    let varType = read_type type_str in
    let varId = as_int (get_key "addr" json) in
    let varName = string_to_lst (as_string (get_key "name" json)) in
    { varType; varId; varName }

  let read_module (json : Yojson.Safe.t) : Verilog.vmodule =
    assert_kind "InstanceBody" json;
    let name = as_string (get_key "name" json) in
    let members = as_list (get_key "members" json) in
    List.fold_left
      (fun (acc : Verilog.vmodule) item_json ->
        try
          let port = read_port item_json in
          { acc with modPorts = acc.modPorts @ [ port ] }
        with UnexpectedKind _ -> (
          try
            let var = read_variable item_json in
            { acc with modVariables = acc.modVariables @ [ var ] }
          with UnexpectedKind (_, k) ->
            let _ = Printf.eprintf "Skipping module item of kind %s" k in
            acc))
      { modName = string_to_lst name; modPorts = []; modVariables = [] }
      members

  let read_ast (json : Yojson.Safe.t) : Verilog.vmodule list =
    let members = as_list (get_key "members" json) in
    List.filter_map
      (fun m ->
        let kind = as_string (get_key "kind" m) in
        if String.equal kind "Instance" then
          let body = get_key "body" m in
          Some (read_module body)
        else (
          Printf.printf "kind=%s\n" kind;
          None))
      members
end

module VerilogPP = struct
  open VVEquiv
  open Format

  let direction fmt d =
    match d with
    | Verilog.In -> fprintf fmt "In"
    | Verilog.Out -> fprintf fmt "Out"

  let vtype fmt t =
    match t with
    | Verilog.Logic (high, low) -> fprintf fmt "logic[%d:%d]" high low

  let port (fmt : formatter) (p : Verilog.port) =
    fprintf fmt "%a <%d>" direction p.portDirection p.portId

  let variable (fmt : formatter) (p : Verilog.variable) =
    fprintf fmt "%a %s<%d>" vtype p.varType (lst_to_string p.varName) p.varId

  let colon_sep fmt () = fprintf fmt ";@ "

  let vmodule (fmt : formatter) (m : Verilog.vmodule) =
    fprintf fmt "Verilog.module %s @[{ ports = [@[%a@]];@,variables = [@[%a@]] }@]"
      (lst_to_string m.modName)
      (pp_print_list port ~pp_sep:colon_sep)
      m.modPorts
      (pp_print_list variable ~pp_sep:colon_sep)
      m.modVariables
end

let usage_msg = "vvequiv <file.sv>"
let input_file = ref ""

let anon_fun arg =
  if !input_file == "" then input_file := arg
  else raise (Arg.Bad "Invalid positional args")

let read_command_output (cmd : string) : string =
  let chan = Unix.open_process_in cmd in
  In_channel.input_all chan

let () =
  Arg.parse [] anon_fun usage_msg;
  if !input_file == "" then raise (Arg.Bad "No input file");
  let ast_json_str =
    read_command_output
      (Printf.sprintf "slang --quiet --ast-json - %s" !input_file)
  in
  let ast_json = Yojson.Safe.from_string ast_json_str in
  try
    let modules = FromJson.read_ast ast_json in
    Format.printf "%d\n%a\n" (List.length modules)
      (Format.pp_print_list VerilogPP.vmodule)
      modules
  with
  | FromJson.UnexpectedJson (msg, json) ->
      Format.printf "Unexpected json: %s\n%a" msg Yojson.Safe.pp json
  | FromJson.UnexpectedKind (expected, got) ->
      Format.printf "Unexpected kind: Expected %s but got %s\n" expected got
