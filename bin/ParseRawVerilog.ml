let translate_direction = function
  | RawVerilog.Input -> Vera.PortIn
  | RawVerilog.Output -> Vera.PortOut

let type_to_vector_declaration = function
  | RawVerilog.Logic (hi, lo) ->
      Vera.UntypedVerilog.Vector (hi, lo)
  | RawVerilog.Reg (hi, lo) ->
      Vera.UntypedVerilog.Vector (hi, lo)
  | RawVerilog.Wire (hi, lo) ->
      Vera.UntypedVerilog.Vector (hi, lo)

let type_to_storage_type = function
  | RawVerilog.Logic _ -> Vera.UntypedVerilog.Reg
  | RawVerilog.Reg _ -> Vera.UntypedVerilog.Reg
  | RawVerilog.Wire _ -> Vera.UntypedVerilog.Wire

let translate_ports (ports : RawVerilog.port_declaration list) :
    Vera.UntypedVerilog.port list * Vera.UntypedVerilog.variable list =
  ports
  |> List.map (fun (p : RawVerilog.port_declaration) ->
         ( {
             Vera.UntypedVerilog.portDirection = translate_direction p.direction;
             Vera.UntypedVerilog.portName = Util.string_to_lst p.name;
           },
           {
             Vera.UntypedVerilog.varVectorDeclaration = type_to_vector_declaration p.net_type;
             Vera.UntypedVerilog.varStorageType = type_to_storage_type p.net_type;
             Vera.UntypedVerilog.varName = Util.string_to_lst p.name;
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
                   Vera.UntypedVerilog.portDirection = translate_direction dir;
                   Vera.UntypedVerilog.portName = Util.string_to_lst d.name;
                 },
                 {
                   Vera.UntypedVerilog.varVectorDeclaration = type_to_vector_declaration net_type;
                   Vera.UntypedVerilog.varStorageType = type_to_storage_type net_type;
                   Vera.UntypedVerilog.varName = Util.string_to_lst d.name;
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
                 Vera.UntypedVerilog.varVectorDeclaration = type_to_vector_declaration net_type;
                 Vera.UntypedVerilog.varStorageType = type_to_storage_type net_type;
                 Vera.UntypedVerilog.varName = Util.string_to_lst d.name;
               })
             declarations
       | _ -> [])

let translate_binary_operator = function
  | RawVerilog.BinaryPlus -> Vera.UntypedVerilog.BinaryPlus
  | RawVerilog.BinaryMinus -> Vera.UntypedVerilog.BinaryMinus
  | RawVerilog.BinaryStar -> Vera.UntypedVerilog.BinaryStar
  | RawVerilog.BinarySlash -> Vera.UntypedVerilog.BinarySlash
  | RawVerilog.BinaryPercent -> Vera.UntypedVerilog.BinaryPercent
  | RawVerilog.BinaryEqualsEquals -> Vera.UntypedVerilog.BinaryEqualsEquals
  | RawVerilog.BinaryNotEquals -> Vera.UntypedVerilog.BinaryNotEquals
  | RawVerilog.BinaryEqualsEqualsEquals -> Vera.UntypedVerilog.BinaryEqualsEqualsEquals
  | RawVerilog.BinaryNotEqualsEquals -> Vera.UntypedVerilog.BinaryNotEqualsEquals
  | RawVerilog.BinaryWildcardEqual -> Vera.UntypedVerilog.BinaryWildcardEqual
  | RawVerilog.BinaryWildcardNotEqual -> Vera.UntypedVerilog.BinaryWildcardNotEqual
  | RawVerilog.BinaryLogicalAnd -> Vera.UntypedVerilog.BinaryLogicalAnd
  | RawVerilog.BinaryLogicalOr -> Vera.UntypedVerilog.BinaryLogicalOr
  | RawVerilog.BinaryExponent -> Vera.UntypedVerilog.BinaryExponent
  | RawVerilog.BinaryLessThan -> Vera.UntypedVerilog.BinaryLessThan
  | RawVerilog.BinaryLessThanEqual -> Vera.UntypedVerilog.BinaryLessThanEqual
  | RawVerilog.BinaryGreaterThan -> Vera.UntypedVerilog.BinaryGreaterThan
  | RawVerilog.BinaryGreaterThanEqual -> Vera.UntypedVerilog.BinaryGreaterThanEqual
  | RawVerilog.BinaryBitwiseAnd -> Vera.UntypedVerilog.BinaryBitwiseAnd
  | RawVerilog.BinaryBitwiseOr -> Vera.UntypedVerilog.BinaryBitwiseOr
  | RawVerilog.BinaryBitwiseXor -> Vera.UntypedVerilog.BinaryBitwiseXor
  | RawVerilog.BinaryXNor -> Vera.UntypedVerilog.BinaryXNor
  | RawVerilog.BinaryShiftRight -> Vera.UntypedVerilog.BinaryShiftRight
  | RawVerilog.BinaryShiftLeft -> Vera.UntypedVerilog.BinaryShiftLeft
  | RawVerilog.BinaryShiftRightArithmetic ->
      Vera.UntypedVerilog.BinaryShiftRightArithmetic
  | RawVerilog.BinaryShiftLeftArithmetic ->
      Vera.UntypedVerilog.BinaryShiftLeftArithmetic
  | RawVerilog.BinaryLogicalImplication -> Vera.UntypedVerilog.BinaryLogicalImplication
  | RawVerilog.BinaryLogicalEquivalence -> Vera.UntypedVerilog.BinaryLogicalEquivalence

let rec translate_stmt = function
  | RawVerilog.Block body -> Vera.UntypedVerilog.Block (List.map translate_stmt body)
  | RawVerilog.Assign { assignment_type = RawVerilog.Blocking; lhs; rhs } ->
      Vera.UntypedVerilog.BlockingAssign (translate_expr lhs, translate_expr rhs)
  | RawVerilog.Assign { assignment_type = RawVerilog.NonBlocking; lhs; rhs } ->
      Vera.UntypedVerilog.NonBlockingAssign (translate_expr lhs, translate_expr rhs)
  | RawVerilog.If { condition; if_branch; else_branch } ->
      Vera.UntypedVerilog.If
        ( translate_expr condition,
          translate_stmt if_branch,
          Option.fold ~none:(Vera.UntypedVerilog.Block []) ~some:translate_stmt
            else_branch )

and translate_expr = function
  | RawVerilog.BinaryOp { operator; lhs; rhs } ->
      Vera.UntypedVerilog.BinaryOp
        ( translate_binary_operator operator,
          translate_expr lhs,
          translate_expr rhs )
  | RawVerilog.Conditional { condition; true_branch; false_branch } ->
      Vera.UntypedVerilog.Conditional
        ( translate_expr condition,
          translate_expr true_branch,
          translate_expr false_branch )
  | RawVerilog.BitSelect { target; index } ->
      Vera.UntypedVerilog.BitSelect (translate_expr target, translate_expr index)
  | RawVerilog.Identifier name ->
      Vera.UntypedVerilog.NamedExpression ((), Util.string_to_lst name)
  | RawVerilog.Literal { width; value } ->
      Vera.UntypedVerilog.IntegerLiteral (Vera.bits_from_int width value)
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
             Some (Vera.UntypedVerilog.AlwaysFF (translate_stmt stmt))
           else raise (Failure "Unsupported clocking declaration")
       | RawVerilog.AlwaysComb stmt ->
           Some (Vera.UntypedVerilog.AlwaysComb (translate_stmt stmt))
       | RawVerilog.ContinuousAssign (lhs, rhs) ->
           Some
             (Vera.UntypedVerilog.AlwaysComb
                (Vera.UntypedVerilog.BlockingAssign
                   (translate_expr lhs, translate_expr rhs)))
       | RawVerilog.Initial stmt ->
           Some (Vera.UntypedVerilog.Initial (translate_stmt stmt)))

let parse_raw_verilog (rv : RawVerilog.vmodule) : Vera.UntypedVerilog.vmodule =
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
