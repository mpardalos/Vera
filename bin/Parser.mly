%token EOF
%token MODULE
%token ENDMODULE
%token REG
%token WIRE
%token OUTPUT
%token INPUT
%token ASSIGN
%token ALWAYS
%token ALWAYS_FF
%token POSEDGE
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token LBRACE
%token RBRACE
%token BEGIN
%token END
%token SEMICOLON
%token COLON
%token COMMA
%token EQUALS
%token LESSTHANEQUAL
%token GREATERTHANEQUAL
%token PLUS
%token MINUS
%token MULTIPLY
%token DIVIDE
%token SHIFTLEFT
%token SHIFTRIGHT
%token AT
%token <string> IDENTIFIER
%token <int> NUMBER
%token <int * int> SIZED_NUMBER

%left PLUS MINUS
%left MULTIPLY DIVIDE
%left SHIFTLEFT SHIFTRIGHT

%start <VVEquiv.Verilog.raw_vmodule> vmodule_only
%type <VVEquiv.Verilog.raw_vmodule> vmodule

%start <(VVEquiv.Verilog.module_item, VVEquiv.Verilog.raw_declaration) VVEquiv.sum> module_item_only
%type <(VVEquiv.Verilog.module_item, VVEquiv.Verilog.raw_declaration) VVEquiv.sum> module_item

%start <VVEquiv.Verilog.statement> statement_only
%type <VVEquiv.Verilog.statement> statement

%start <VVEquiv.Verilog.expression> expression_only
%type <VVEquiv.Verilog.expression> expression

%%

let only(x) :=
    | x=x; EOF; { x }

let many(x) :=
  | { [] }
  | x=x; xs=many(x); { x :: xs }

let sepBy(x, sep) :=
  | { [] }
  | x=x; sep; xs=sepBy(x, sep); { x :: xs }
  | x=x; { [ x ] }

let optional(x) :=
  | x=x; { Some x }
  | { None }

let vmodule_only := x = only(vmodule); { x }

let module_port := direction = port_direction; name = IDENTIFIER;
    { { VVEquiv.Verilog.portDirection = direction
      ; VVEquiv.Verilog.portName = Util.string_to_lst name
      }
    }

let module_ports := LPAREN; args = sepBy(module_port, COMMA); RPAREN;
  { args }

let vmodule :=
  MODULE; name = IDENTIFIER; ports = module_ports; SEMICOLON; body = many(module_item); ENDMODULE;
    {
      { VVEquiv.Verilog.rawModName = (Util.string_to_lst name)
      ; VVEquiv.Verilog.rawModPorts = ports
      ; VVEquiv.Verilog.rawModBody = body
      }
    }

let module_item_only := x = only(module_item); { x }

let always_ff := ALWAYS | ALWAYS_FF

let port_direction :=
  | INPUT; { VVEquiv.PortIn }
  | OUTPUT; { VVEquiv.PortOut }

let net_type :=
  | REG; { VVEquiv.Verilog.Reg }
  | WIRE; { VVEquiv.Verilog.Wire }

let vtype := LBRACKET; hi = NUMBER; COLON; lo = NUMBER; RBRACKET;
  { VVEquiv.Verilog.Logic (hi, lo) }

let module_item :=
  | port = optional(port_direction); net_type = net_type; vtype = optional(vtype); name = IDENTIFIER; SEMICOLON;
    {
      VVEquiv.Inr ({ rawDeclStorageType = net_type
                   ; rawDeclPortDeclaration = port
                   ; rawDeclName = Util.string_to_lst name
                   ; rawDeclType = vtype
                  })
    }
  | ASSIGN; lhs = expression; EQUALS; rhs = expression; SEMICOLON;
    { VVEquiv.Inl (VVEquiv.Verilog.ContinuousAssign (lhs, rhs)) }
  | always_ff; AT; LPAREN; POSEDGE; clkname = IDENTIFIER; RPAREN; body = statement;
    { VVEquiv.Inl (VVEquiv.Verilog.AlwaysFF body) }

let statement_only := x = only(statement); { x }

let statement :=
  | lhs = expression; LESSTHANEQUAL; rhs = expression; SEMICOLON;
    { VVEquiv.Verilog.NonBlockingAssign (lhs, rhs) }
  | lhs = expression; EQUALS; rhs = expression; SEMICOLON;
    { VVEquiv.Verilog.BlockingAssign (lhs, rhs) }
  | BEGIN; body = many(statement); END;
    { VVEquiv.Verilog.Block body }

let expression_only := x = only(expression); { x }

let expression :=
  | ident = IDENTIFIER;
    {
      VVEquiv.Verilog.NamedExpression (Util.string_to_lst ident)
    }
  | n = NUMBER;
    {
      VVEquiv.Verilog.IntegerLiteral ({ value = n; width = 32 })
    }
  | (sz, v) = SIZED_NUMBER;
    {
      VVEquiv.Verilog.IntegerLiteral ({ value = v; width = sz })
    }
  | l = expression; PLUS; r = expression;
    {
      VVEquiv.Verilog.BinaryOp (VVEquiv.Verilog.Plus, l, r)
    }
  | l = expression; MINUS; r = expression;
    {
      VVEquiv.Verilog.BinaryOp (VVEquiv.Verilog.Minus, l, r)
    }
  | l = expression; MULTIPLY; r = expression;
    {
      VVEquiv.Verilog.BinaryOp (VVEquiv.Verilog.Multiply, l, r)
    }
  | l = expression; SHIFTLEFT; r = expression;
    {
      VVEquiv.Verilog.BinaryOp (VVEquiv.Verilog.ShiftLeft, l, r)
    }
  | l = expression; SHIFTRIGHT; r = expression;
    {
      VVEquiv.Verilog.BinaryOp (VVEquiv.Verilog.ShiftRight, l, r)
    }
  | LPAREN; e = expression; RPAREN;
    { e }
