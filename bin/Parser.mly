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

%start <Vera.Verilog.raw_vmodule> vmodule_only
%type <Vera.Verilog.raw_vmodule> vmodule

%start <(Vera.Verilog.module_item, Vera.Verilog.raw_declaration) Vera.sum> module_item_only
%type <(Vera.Verilog.module_item, Vera.Verilog.raw_declaration) Vera.sum> module_item

%start <Vera.Verilog.statement> statement_only
%type <Vera.Verilog.statement> statement

%start <Vera.Verilog.expression> expression_only
%type <Vera.Verilog.expression> expression

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
    { { Vera.Verilog.portDirection = direction
      ; Vera.Verilog.portName = Util.string_to_lst name
      }
    }

let module_ports := LPAREN; args = sepBy(module_port, COMMA); RPAREN;
  { args }

let vmodule :=
  MODULE; name = IDENTIFIER; ports = module_ports; SEMICOLON; body = many(module_item); ENDMODULE;
    {
      { Vera.Verilog.rawModName = (Util.string_to_lst name)
      ; Vera.Verilog.rawModPorts = ports
      ; Vera.Verilog.rawModBody = body
      }
    }

let module_item_only := x = only(module_item); { x }

let always_ff := ALWAYS | ALWAYS_FF

let port_direction :=
  | INPUT; { Vera.PortIn }
  | OUTPUT; { Vera.PortOut }

let net_type :=
  | REG; { Vera.Verilog.Reg }
  | WIRE; { Vera.Verilog.Wire }

let vtype := LBRACKET; hi = NUMBER; COLON; lo = NUMBER; RBRACKET;
  { Vera.Verilog.Logic (Vera.N.to_nat hi, Vera.N.to_nat lo) }

let module_item :=
  | port = optional(port_direction); net_type = net_type; vtype = optional(vtype); name = IDENTIFIER; SEMICOLON;
    {
      Vera.Inr ({ rawDeclStorageType = net_type
                   ; rawDeclPortDeclaration = port
                   ; rawDeclName = Util.string_to_lst name
                   ; rawDeclType = vtype
                  })
    }
  | ASSIGN; lhs = expression; EQUALS; rhs = expression; SEMICOLON;
    { Vera.Inl (Vera.Verilog.ContinuousAssign (lhs, rhs)) }
  | always_ff; AT; LPAREN; POSEDGE; clkname = IDENTIFIER; RPAREN; body = statement;
    { Vera.Inl (Vera.Verilog.AlwaysFF body) }

let statement_only := x = only(statement); { x }

let statement :=
  | lhs = expression; LESSTHANEQUAL; rhs = expression; SEMICOLON;
    { Vera.Verilog.NonBlockingAssign (lhs, rhs) }
  | lhs = expression; EQUALS; rhs = expression; SEMICOLON;
    { Vera.Verilog.BlockingAssign (lhs, rhs) }
  | BEGIN; body = many(statement); END;
    { Vera.Verilog.Block body }

let expression_only := x = only(expression); { x }

let expression :=
  | ident = IDENTIFIER;
    {
      Vera.Verilog.NamedExpression (Util.string_to_lst ident)
    }
  | n = NUMBER;
    {
      Vera.Verilog.IntegerLiteral (Vera.bits_from_int 32 n)
    }
  | (sz, v) = SIZED_NUMBER;
    {
      Vera.Verilog.IntegerLiteral (Vera.bits_from_int sz v)
    }
  | l = expression; PLUS; r = expression;
    {
      Vera.Verilog.BinaryOp (Vera.Verilog.Plus, l, r)
    }
  | l = expression; MINUS; r = expression;
    {
      Vera.Verilog.BinaryOp (Vera.Verilog.Minus, l, r)
    }
  | l = expression; MULTIPLY; r = expression;
    {
      Vera.Verilog.BinaryOp (Vera.Verilog.Multiply, l, r)
    }
  | l = expression; SHIFTLEFT; r = expression;
    {
      Vera.Verilog.BinaryOp (Vera.Verilog.ShiftLeft, l, r)
    }
  | l = expression; SHIFTRIGHT; r = expression;
    {
      Vera.Verilog.BinaryOp (Vera.Verilog.ShiftRight, l, r)
    }
  | LPAREN; e = expression; RPAREN;
    { e }
