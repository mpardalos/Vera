let lst_to_string lst = String.of_seq (List.to_seq lst)
let string_to_lst s = List.of_seq (String.to_seq s)

module FromJson = struct
  open VVEquiv

  type parse_error =
    | UnexpectedJson of (string * Yojson.Safe.t)
    | UnexpectedKind of (string * string)
    | UnknownType of string
    | UnknownOp of string
    | UnknownValue of (string * string)
    | UnknownModuleItem of string option

  let pp_parse_error fmt err =
    match err with
    | UnexpectedJson (msg, json) ->
        Format.fprintf fmt "Unexpected json: %s\n%a" msg Yojson.Safe.pp json
    | UnexpectedKind (expected, got) ->
        Format.fprintf fmt "Unexpected kind: Expected %s but got %s\n" expected
          got
    | UnknownModuleItem None -> Format.fprintf fmt "Could not parse module item"
    | UnknownModuleItem (Some k) ->
        Format.fprintf fmt "Could not parse module item of kind %s" k
    | _ -> ()

  type 'a result = ('a, parse_error) Result.t

  let ( let* ) = Result.bind
  let ( >>= ) = Result.bind
  let ( =<< ) a b = b >>= a

  let missing_key ((k : string), (j : Yojson.Safe.t)) =
    UnexpectedJson (Printf.sprintf "No key '%s'" k, j)

  let assoc_lookup key assoc =
    Option.map snd (List.find_opt (fun (k, _) -> String.equal k key) assoc)

  let get_key key = function
    | `Assoc lst as json -> (
        match assoc_lookup key lst with
        | Some x -> Ok x
        | None -> Error (missing_key (key, json)))
    | json -> Error (missing_key (key, json))

  let as_string = function
    | `String s -> Ok s
    | json -> Error (UnexpectedJson ("string", json))

  let as_int = function
    | `Int n -> Ok n
    | json -> Error (UnexpectedJson ("int", json))

  let as_list = function
    | `List l -> Ok l
    | json -> Error (UnexpectedJson ("list", json))

  let read_op = function
    | "Add" -> Ok Verilog.Plus
    | "Minus" -> Ok Verilog.Minus
    | op -> Error (UnknownOp op)

  let read_type (s : string) : Verilog.vtype result =
    try
      Scanf.sscanf s "%s@[%d:%d]" (fun t n1 n2 ->
          match t with
          | "reg" | "logic" | "logic signed" | "reg signed" ->
              Ok (Verilog.Logic (n1, n2))
          | _ -> Error (UnknownType s))
    with End_of_file | Scanf.Scan_failure _ ->
      Error (UnknownValue ("type", s))

  let read_value (s : string) : int result =
    try Scanf.sscanf s "%d'd%d" (fun _length value -> Ok value)
    with End_of_file | Scanf.Scan_failure _ -> (
      try Scanf.sscanf s "%d" (fun value -> Ok value)
      with End_of_file | Scanf.Scan_failure _ ->
        Error (UnknownValue ("value", s)))

  let read_symbol s : (int * string) result =
    try Scanf.sscanf s "%d %s" (fun n s -> Ok (n, s))
    with Scanf.Scan_failure _ -> Error (UnknownValue ("symbol", s))

  let rec read_expression (json : Yojson.Safe.t) : Verilog.expression result =
    let* kind = as_string =<< get_key "kind" json in
    match kind with
    | "BinaryOp" ->
        let* op = read_op =<< (as_string =<< get_key "op" json) in
        let* left_expression = read_expression =<< get_key "left" json in
        let* right_expression = read_expression =<< get_key "right" json in
        Ok (Verilog.BinaryOp (op, left_expression, right_expression))
    | "NamedValue" ->
        let* _, name = read_symbol =<< (as_string =<< get_key "symbol" json) in
        Ok (Verilog.NamedExpression (string_to_lst name))
    | "Conversion" ->
        let* operand = read_expression =<< get_key "operand" json in
        let* conversion_type =
          read_type =<< (as_string =<< get_key "type" json)
        in
        Ok (Verilog.Conversion (conversion_type, operand))
    | "IntegerLiteral" ->
        let* value = read_value =<< (as_string =<< get_key "value" json) in
        Ok (Verilog.IntegerLiteral value)
    | k -> Error (UnexpectedKind ("expression kind", k))

  let assert_kind expected_kind json =
    let* kind = as_string =<< get_key "kind" json in
    if String.equal expected_kind kind then Ok ()
    else Error (UnexpectedKind (expected_kind, kind))

  let assert_kind_one_of expected_kinds json =
    let* kind = as_string =<< get_key "kind" json in
    let rec go ks =
      match ks with
      | k :: ks -> if String.equal k kind then Ok () else go ks
      | [] -> Error (UnexpectedKind (String.concat "|" expected_kinds, kind))
    in
    go expected_kinds

  let read_port json : Verilog.port result =
    let* () = assert_kind "Port" json in
    let* direction_str = as_string =<< get_key "direction" json in
    let* portDirection =
      match direction_str with
      | "Out" -> Ok Verilog.Out
      | "In" -> Ok Verilog.In
      | _ -> Error (UnknownValue ("direction", direction_str))
    in
    let* symbol_str = as_string =<< get_key "internalSymbol" json in
    let* portId, _ = read_symbol symbol_str in
    Ok { Verilog.portDirection; portId }

  let read_variable json : Verilog.variable result =
    let* () = assert_kind_one_of [ "Variable"; "Net" ] json in
    let* type_str = as_string =<< get_key "type" json in
    let* varType = read_type type_str in
    let* varId = as_int =<< get_key "addr" json in
    let* varName =
      Result.map string_to_lst (as_string =<< get_key "name" json)
    in
    Ok { Verilog.varType; varId; varName }

  let read_continuous_assign json : Verilog.module_item result =
    let* () = assert_kind "ContinuousAssign" json in
    let* assignment = get_key "assignment" json in
    let* left = read_expression =<< get_key "left" assignment in
    let* right = read_expression =<< get_key "right" assignment in
    Ok (Verilog.ContinuousAssign (left, right))

  (** Try all alternatives in order, return the first Ok value, if none are Ok,
  then return the default value *)
  let rec first_successful (default : 'b result) (fs : ('a -> 'b result) list)
      (a : 'a) : 'b result =
    match fs with
    | [] -> default
    | hd :: tl -> (
        match hd a with
        | Ok b -> Ok b
        | Error _ -> first_successful default tl a)

  let read_module_item json =
    let kind = Result.to_option (as_string =<< get_key "kind" json) in
    first_successful (Error (UnknownModuleItem kind))
      [
        (fun () ->
          let* var = read_variable json in
          Ok (`Variable var));
        (fun () ->
          let* port = read_port json in
          Ok (`Port port));
        (fun () ->
          let* ca = read_continuous_assign json in
          Ok (`ModuleItem ca));
      ]
      ()

  let read_module (json : Yojson.Safe.t) : Verilog.vmodule result =
    let* () = assert_kind "InstanceBody" json in
    let* name = as_string =<< get_key "name" json in
    let* members = as_list =<< get_key "members" json in
    Ok
      (List.fold_left
         (fun (acc : Verilog.vmodule) item_json ->
           match read_module_item item_json with
           | Ok (`Port port) -> { acc with modPorts = acc.modPorts @ [ port ] }
           | Ok (`Variable var) ->
               { acc with modVariables = acc.modVariables @ [ var ] }
           | Ok (`ModuleItem mi) -> { acc with modBody = acc.modBody @ [ mi ] }
           | Error err ->
               Format.eprintf "Skipped module item: %a\n" pp_parse_error err;
               acc)
         {
           Verilog.modName = string_to_lst name;
           modPorts = [ { Verilog.portDirection = Out; portId = 0 } ];
           modVariables = [];
           modBody = [];
         }
         members)

  let read_ast (json : Yojson.Safe.t) : Verilog.vmodule list result =
    let* members = as_list =<< get_key "members" json in
    Ok
      (List.filter_map
         (fun m ->
           let result =
             let* kind = as_string =<< get_key "kind" m in
             if String.equal kind "Instance" then
               let* body = get_key "body" m in
               read_module body
             else Error (UnexpectedKind ("Instance", kind))
           in
           match result with
           | Ok it -> Some it
           | Error err ->
               Format.eprintf "Skipped top-level item: %a\n" pp_parse_error err;
               None)
         members)
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

  let operator fmt = function
    | Verilog.Plus -> fprintf fmt "+"
    | Verilog.Minus -> fprintf fmt "-"

  let colon_sep fmt () = fprintf fmt ";@ "

  let rec expression fmt e =
    Format.fprintf fmt "@[";
    (match e with
    | Verilog.IntegerLiteral n -> fprintf fmt "%d" n
    | Verilog.Conversion (t, e) ->
        fprintf fmt "( %a )@ as@ ( %a )" expression e vtype t
    | Verilog.BinaryOp (op, l, r) ->
        fprintf fmt "( %a )@ %a@ ( %a )" expression l operator op expression r
    | Verilog.NamedExpression name -> fprintf fmt "%s" (lst_to_string name));
    Format.fprintf fmt "@]"

  let mod_item (fmt : formatter) (i : Verilog.module_item) =
    match i with
    | Verilog.ContinuousAssign (l, r) ->
        fprintf fmt "assign %a = %a" expression l expression r

  let vmodule (fmt : formatter) (m : Verilog.vmodule) =
    fprintf fmt "Verilog.module %s {@." (lst_to_string m.modName);
    fprintf fmt "    @[<v>";
    fprintf fmt "ports = [@,    @[<v>%a@]@,];"
      (pp_print_list port ~pp_sep:colon_sep)
      m.modPorts;
    fprintf fmt "@,";
    fprintf fmt "variables = [@,    @[<v>%a@]@,];"
      (pp_print_list variable ~pp_sep:colon_sep)
      m.modVariables;
    fprintf fmt "@,";
    fprintf fmt "body = [@,    @[<v>%a@]@,];"
      (pp_print_list mod_item ~pp_sep:colon_sep)
      m.modBody;
    fprintf fmt "@]@.}"
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
  match FromJson.read_ast ast_json with
  | Ok modules ->
      Format.printf "%a\n" (Format.pp_print_list VerilogPP.vmodule) modules
  | Error err ->
      Format.printf "Failed to parse: %a\n" FromJson.pp_parse_error err
