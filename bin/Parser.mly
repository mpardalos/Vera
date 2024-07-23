%token EOF
%token MODULE
%token ENDMODULE
%token REG
%token WIRE
%token OUTPUT
%token INPUT
%token POSEDGE
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token LBRACE
%token RBRACE
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

%start <VVEquiv.Verilog.expression> expression_only

%type <VVEquiv.Verilog.expression> expression

%%

let expression_only := e = expression; EOF; { e }

let expression :=
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
