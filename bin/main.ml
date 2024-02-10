let lst_to_string (lst : char list) : string =
  List.fold_left (fun (s : string) (c : char) -> s ^ String.make 1 c) "" lst

module FromJson = struct
  open VVEquiv

  exception UnexpectedJson of (string * Yojson.Safe.t)
  exception UnexpectedKind of string
  exception UnknownType of string
  exception UnknownOp of string

  let missing_key ((k : string), (j : Yojson.Safe.t)) =
    UnexpectedJson (Printf.sprintf "No key '%s'" k, j)

  let assoc_lookup (key : 'a) (assoc : ('a * 'b) list) : 'b option =
    Option.map snd (List.find_opt (fun (k, _) -> k == key) assoc)

  let get_key key = function
    | `Assoc lst as json -> (
        match assoc_lookup key lst with
        | Some x -> x    | json -> raise (UnexpectedJson ("string", json))

  let as_int = function
    | `Int n -> n
    | json -> raise (UnexpectedJson ("int", json))

  let as_list = function
    | `List l -> l
    | json -> raise (UnexpectedJson ("list", json))

  let read_op = function "Add" -> Verilog.Plus | op -> raise (UnknownOp op)

  let read_type (s : string) : Verilog.vtype =
    Scanf.sscanf s "%s@[%d, %d]" (fun t n1 n2 ->
        match t with
        | "reg" | "logic" -> Verilog.Logic (n1, n2)
        | _ -> raise (UnknownType s))

  let read_value (s : string) : int =
    try Scanf.sscanf s "%d'd%d" (fun _length value -> value)
    with Scanf.Scan_failure _ -> Scanf.sscanf s "%d" (fun value -> value)

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
    | k -> raise (UnexpectedKind k)

  let read_module (json : Yojson.Safe.t) : Verilog.vmodule =
    { modName = []; modPorts = []; modVariables = [] }

  let read_ast (json : Yojson.Safe.t) : Verilog.vmodule list =
    let members = as_list (get_key "members" json) in
    List.filter_map
      (fun m ->
        let kind = as_string (get_key "kind" m) in
        let body = get_key "body" m in
        if kind == "Instance" then Some (read_module body) else None)
      members
end

module VerilogPP = struct
  open VVEquiv

  let vmodule (fmt : Format.formatter) (m : Verilog.vmodule) =
    Format.pp_print_string fmt (lst_to_string m.modName)
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
    Format.printf "%a\n" (Format.pp_print_list VerilogPP.vmodule) modules;
  with FromJson.UnexpectedJson (msg, json) ->
    Format.printf "Unexpected json: %s\n%a" msg Yojson.Safe.pp json
