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
%token AT
%token <string> IDENTIFIER
%token <int> NUMBER
%token <int * int> SIZED_NUMBER

%left PLUS MINUS

%start <VVEquiv.Verilog.vmodule> vmodule_only
%type <VVEquiv.Verilog.vmodule> vmodule

%start <VVEquiv.Verilog.module_item> module_item_only
%type <VVEquiv.Verilog.module_item> module_item

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

let vmodule_only := x = only(vmodule); { x }

let module_args := LPAREN; RPAREN

let vmodule :=
  MODULE; name = IDENTIFIER; module_args; SEMICOLON; body = many(module_item); ENDMODULE;
    {
      { VVEquiv.Verilog.modName = (Util.string_to_lst name)
      ; VVEquiv.Verilog.modPorts = []
      ; VVEquiv.Verilog.modVariables = []
      ; VVEquiv.Verilog.modBody = body
      }
    }

let module_item_only := x = only(module_item); { x }

let always_ff := ALWAYS | ALWAYS_FF

let module_item :=
  | ASSIGN; lhs = expression; EQUALS; rhs = expression; SEMICOLON;
    { VVEquiv.Verilog.ContinuousAssign (lhs, rhs) }
  | always_ff; AT; LPAREN; POSEDGE; clkname = IDENTIFIER; RPAREN; body = statement;
    { VVEquiv.Verilog.AlwaysFF body }

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
  | LPAREN; e = expression; RPAREN;
    { e }
