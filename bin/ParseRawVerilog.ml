let translate_direction = function
  | RawVerilog.Input -> Vera.PortIn
  | RawVerilog.Output -> Vera.PortOut

let type_to_vector_declaration = function
  | RawVerilog.Logic (hi, lo) ->
      Vera.Verilog.Vector (hi, lo)
  | RawVerilog.Reg (hi, lo) ->
      Vera.Verilog.Vector (hi, lo)
  | RawVerilog.Wire (hi, lo) ->
      Vera.Verilog.Vector (hi, lo)

let type_to_storage_type = function
  | RawVerilog.Logic _ -> Vera.Verilog.Reg
  | RawVerilog.Reg _ -> Vera.Verilog.Reg
  | RawVerilog.Wire _ -> Vera.Verilog.Wire

let translate_ports (ports : RawVerilog.port_declaration list) :
    Vera.Verilog.port list * Vera.Verilog.variable list =
  ports
  |> List.map (fun (p : RawVerilog.port_declaration) ->
         ( {
             Vera.Verilog.portDirection = translate_direction p.direction;
             Vera.Verilog.portName = Util.string_to_lst p.name;
           },
           {
             Vera.Verilog.varVectorDeclaration = type_to_vector_declaration p.net_type;
             Vera.Verilog.varStorageType = type_to_storage_type p.net_type;
             Vera.Verilog.varName = Util.string_to_lst p.name;
           } ))
  |> List.split

let collect_ports (body : RawVerilog.module_item list) =
  body
  |> List.concat_map (function
       | RawVerilog.NetDeclaration { port = Some dir; net_type; declarations }
         ->
           List.map
             (fun (d : RawVerilog.declaration) ->
               ( {
                   Vera.Verilog.portDirection = translate_direction dir;
                   Vera.Verilog.portName = Util.string_to_lst d.name;
                 },
                 {
                   Vera.Verilog.varVectorDeclaration = type_to_vector_declaration net_type;
                   Vera.Verilog.varStorageType = type_to_storage_type net_type;
                   Vera.Verilog.varName = Util.string_to_lst d.name;
                 } ))
             declarations
       | _ -> [])
  |> List.split

let collect_variables (body : RawVerilog.module_item list) =
  body
  |> List.concat_map (function
       | RawVerilog.NetDeclaration { port = None; net_type; declarations } ->
           List.map
             (fun (d : RawVerilog.declaration) ->
               {
                 Vera.Verilog.varVectorDeclaration = type_to_vector_declaration net_type;
                 Vera.Verilog.varStorageType = type_to_storage_type net_type;
                 Vera.Verilog.varName = Util.string_to_lst d.name;
               })
             declarations
       | _ -> [])

let translate_binary_operator = function
  | RawVerilog.BinaryPlus -> Vera.Verilog.BinaryPlus
  | RawVerilog.BinaryMinus -> Vera.Verilog.BinaryMinus
  | RawVerilog.BinaryStar -> Vera.Verilog.BinaryStar
  | RawVerilog.BinarySlash -> Vera.Verilog.BinarySlash
  | RawVerilog.BinaryPercent -> Vera.Verilog.BinaryPercent
  | RawVerilog.BinaryEqualsEquals -> Vera.Verilog.BinaryEqualsEquals
  | RawVerilog.BinaryNotEquals -> Vera.Verilog.BinaryNotEquals
  | RawVerilog.BinaryEqualsEqualsEquals -> Vera.Verilog.BinaryEqualsEqualsEquals
  | RawVerilog.BinaryNotEqualsEquals -> Vera.Verilog.BinaryNotEqualsEquals
  | RawVerilog.BinaryWildcardEqual -> Vera.Verilog.BinaryWildcardEqual
  | RawVerilog.BinaryWildcardNotEqual -> Vera.Verilog.BinaryWildcardNotEqual
  | RawVerilog.BinaryLogicalAnd -> Vera.Verilog.BinaryLogicalAnd
  | RawVerilog.BinaryLogicalOr -> Vera.Verilog.BinaryLogicalOr
  | RawVerilog.BinaryExponent -> Vera.Verilog.BinaryExponent
  | RawVerilog.BinaryLessThan -> Vera.Verilog.BinaryLessThan
  | RawVerilog.BinaryLessThanEqual -> Vera.Verilog.BinaryLessThanEqual
  | RawVerilog.BinaryGreaterThan -> Vera.Verilog.BinaryGreaterThan
  | RawVerilog.BinaryGreaterThanEqual -> Vera.Verilog.BinaryGreaterThanEqual
  | RawVerilog.BinaryBitwiseAnd -> Vera.Verilog.BinaryBitwiseAnd
  | RawVerilog.BinaryBitwiseOr -> Vera.Verilog.BinaryBitwiseOr
  | RawVerilog.BinaryBitwiseXor -> Vera.Verilog.BinaryBitwiseXor
  | RawVerilog.BinaryXNor -> Vera.Verilog.BinaryXNor
  | RawVerilog.BinaryShiftRight -> Vera.Verilog.BinaryShiftRight
  | RawVerilog.BinaryShiftLeft -> Vera.Verilog.BinaryShiftLeft
  | RawVerilog.BinaryShiftRightArithmetic ->
      Vera.Verilog.BinaryShiftRightArithmetic
  | RawVerilog.BinaryShiftLeftArithmetic ->
      Vera.Verilog.BinaryShiftLeftArithmetic
  | RawVerilog.BinaryLogicalImplication -> Vera.Verilog.BinaryLogicalImplication
  | RawVerilog.BinaryLogicalEquivalence -> Vera.Verilog.BinaryLogicalEquivalence

let rec translate_stmt = function
  | RawVerilog.Block body -> Vera.Verilog.Block (List.map translate_stmt body)
  | RawVerilog.Assign { assignment_type = RawVerilog.Blocking; lhs; rhs } ->
      Vera.Verilog.BlockingAssign (translate_expr lhs, translate_expr rhs)
  | RawVerilog.Assign { assignment_type = RawVerilog.NonBlocking; lhs; rhs } ->
      Vera.Verilog.NonBlockingAssign (translate_expr lhs, translate_expr rhs)
  | RawVerilog.If { condition; if_branch; else_branch } ->
      Vera.Verilog.If
        ( translate_expr condition,
          translate_stmt if_branch,
          Option.fold ~none:(Vera.Verilog.Block []) ~some:translate_stmt
            else_branch )

and translate_expr = function
  | RawVerilog.BinaryOp { operator; lhs; rhs } ->
      Vera.Verilog.BinaryOp
        ( translate_binary_operator operator,
          translate_expr lhs,
          translate_expr rhs )
  | RawVerilog.Conditional { condition; true_branch; false_branch } ->
      Vera.Verilog.Conditional
        ( translate_expr condition,
          translate_expr true_branch,
          translate_expr false_branch )
  | RawVerilog.BitSelect { target; index } ->
      Vera.Verilog.BitSelect (translate_expr target, translate_expr index)
  | RawVerilog.Identifier name ->
      Vera.Verilog.NamedExpression ((), Util.string_to_lst name)
  | RawVerilog.Literal { width; value } ->
      Vera.Verilog.IntegerLiteral (Vera.bits_from_int width value)
  | e ->
      Format.eprintf "Unsupported expression: %a" RawVerilog.pp_expression e;
      raise (Failure "")

let check_clocking = function
  | RawVerilog.ClockingEdge (RawVerilog.Posedge, "clk") -> true
  | RawVerilog.ClockingStar -> true
  | _ -> false

let translate_body (body : RawVerilog.module_item list) =
  body
  |> List.filter_map (function
       | RawVerilog.NetDeclaration _ -> None
       | RawVerilog.AlwaysFF (clocking, stmt) ->
           if check_clocking clocking then
             Some (Vera.Verilog.AlwaysFF (translate_stmt stmt))
           else raise (Failure "Unsupported clocking declaration")
       | RawVerilog.AlwaysComb stmt ->
           Some (Vera.Verilog.AlwaysComb (translate_stmt stmt))
       | RawVerilog.ContinuousAssign (lhs, rhs) ->
           Some
             (Vera.Verilog.AlwaysComb
                (Vera.Verilog.BlockingAssign
                   (translate_expr lhs, translate_expr rhs)))
       | RawVerilog.Initial stmt ->
           Some (Vera.Verilog.Initial (translate_stmt stmt)))

let parse_raw_verilog (rv : RawVerilog.vmodule) : Vera.Verilog.vmodule =
  let signature_ports, signature_vars = translate_ports rv.ports in
  let body_ports, body_port_vars = collect_ports rv.body in
  let modName = Util.string_to_lst rv.name in
  let body_vars = collect_variables rv.body in
  let modBody = translate_body rv.body in
  {
    modName;
    modPorts = signature_ports @ body_ports;
    modVariables = signature_vars @ body_port_vars @ body_vars;
    modBody;
  }
