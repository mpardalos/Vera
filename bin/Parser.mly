%token EOF
%token MODULE
%token ENDMODULE
%token REG
%token WIRE
%token IF
%token ELSE
%token LOGIC
%token OUTPUT
%token INPUT
%token ASSIGN
%token ALWAYS
%token ALWAYS_FF
%token INITIAL
%token POSEDGE
%token NEGEDGE
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
/* %token LBRACE */
/* %token RBRACE */
%token BEGIN
%token END
%token SEMICOLON
%token QUESTIONMARK
%token COLON
%token COMMA
%token EQUALS

%token PLUS (* '+' *)
%token MINUS (* '-' *)
%token STAR (* '*' *)
%token SLASH (* '/' *)
%token PERCENT (* '%' *)
%token EQUALSEQUALS (* '==' *)
%token NOTEQUALS (* '!=' *)
%token EQUALSEQUALSEQUALS (* '===' *)
%token NOTEQUALSEQUALS (* '!==' *)
%token WILDCARDEQUAL (* '==?' *)
%token WILDCARDNOTEQUAL (* '!=?' *)
%token LOGICALAND (* '&&' *)
%token LOGICALOR (* '||' *)
%token EXPONENT (* '**' *)
%token LESSTHAN (* '<' *)
%token LESSTHANEQUAL (* '<=' *)
%token GREATERTHAN (* '>' *)
%token GREATERTHANEQUAL (* '>=' *)
%token BITWISEAND (* '&' *)
%token BITWISEOR (* '|' *)
%token BITWISEXOR (* '^' *)
%token BITWISEXNOR (* '^~', '~^' *)
%token SHIFTRIGHT (* '>>' *)
%token SHIFTLEFT (* '<<' *)
%token SHIFTRIGHTARITHMETIC (* '>>>' *)
%token SHIFTLEFTARITHMETIC (* '<<<' *)
%token LOGICALIMPLICATION (* '->' *)
%token LOGICALEQUIVALENCE (* '<->' *)

%token AT
%token <string> IDENTIFIER
%token <int> NUMBER
%token <int * int> SIZED_NUMBER

%left EXPONENT
%left STAR SLASH PERCENT
%left PLUS MINUS
%left SHIFTLEFT SHIFTRIGHT SHIFTLEFTARITHMETIC SHIFTRIGHTARITHMETIC
%left LESSTHAN LESSTHANEQUAL GREATERTHAN GREATERTHANEQUAL
%left EQUALSEQUALS NOTEQUALS EQUALSEQUALSEQUALS NOTEQUALSEQUALS WILDCARDEQUAL WILDCARDNOTEQUAL
%left BITWISEAND
%left BITWISEXOR BITWISEXNOR
%left BITWISEOR
%left LOGICALAND
%left LOGICALOR
// ?: (Conditional operator)
%left LOGICALIMPLICATION LOGICALEQUIVALENCE


%start <RawVerilog.vmodule> vmodule_only
%type <RawVerilog.vmodule> vmodule

%start <RawVerilog.module_item> module_item_only
%type <RawVerilog.module_item> module_item

%start <RawVerilog.statement> statement_only
%type <RawVerilog.statement> statement

%start <RawVerilog.expression> expression_only
%type <RawVerilog.expression> expression

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

let port_declaration := direction = port_direction; net_type = net_type; name = IDENTIFIER;
    {
      {
        RawVerilog.direction = direction;
        net_type;
        name
      }
    }

let module_ports := LPAREN; args = sepBy(port_declaration, COMMA); RPAREN;
  { args }

let vmodule :=
  MODULE; name = IDENTIFIER; ports = module_ports; SEMICOLON; body = many(module_item); ENDMODULE;
    {
      { RawVerilog.name = name
      ; RawVerilog.ports = ports
      ; RawVerilog.body = body
      }
    }

let module_item_only := x = only(module_item); { x }

let always_ff := ALWAYS | ALWAYS_FF

let port_direction :=
  | INPUT; { RawVerilog.Input }
  | OUTPUT; { RawVerilog.Output }

let net_type :=
  | REG; LBRACKET; high = NUMBER; COLON; low = NUMBER; RBRACKET; { RawVerilog.Logic (high, low); }
  | REG; { RawVerilog.Logic (0, 0); }
  | WIRE; LBRACKET; high = NUMBER; COLON; low = NUMBER; RBRACKET; { RawVerilog.Logic (high, low); }
  | WIRE; { RawVerilog.Logic (0, 0); }
  | LOGIC; LBRACKET; high = NUMBER; COLON; low = NUMBER; RBRACKET; { RawVerilog.Logic (high, low); }
  | LOGIC; { RawVerilog.Logic (0, 0); }

let edge :=
  | POSEDGE; { RawVerilog.Posedge }
  | NEGEDGE; { RawVerilog.Negedge }

let clocking :=
  | AT; LPAREN; edge = edge; name = IDENTIFIER; RPAREN; { RawVerilog.ClockingEdge (edge, name) }
  | AT; LPAREN; STAR; RPAREN; { RawVerilog.ClockingStar }

let declaration :=
  | name = IDENTIFIER;
    { { name; initialization = None }}
  | name = IDENTIFIER; EQUALS; initialization = expression;
    { { name; initialization = Some initialization } }

let module_item :=
  | port = optional(port_direction); net_type = net_type; declarations = sepBy(declaration, COMMA); SEMICOLON;
    {
      RawVerilog.NetDeclaration {
          port;
          net_type;
          declarations;
      }
    }
  | ASSIGN; lhs = lhs_expression; EQUALS; rhs = expression; SEMICOLON;
    { RawVerilog.ContinuousAssign (lhs, rhs) }
  | always_ff; clocking = clocking; body = statement;
    { RawVerilog.AlwaysFF (clocking, body) }
  | INITIAL; body = statement;
    { RawVerilog.Initial body }

let statement_only := x = only(statement); { x }

let statement :=
  | lhs = lhs_expression; EQUALS; rhs = expression; SEMICOLON;
    { RawVerilog.Assign { assignment_type = RawVerilog.Blocking; lhs; rhs  } }
  | lhs = lhs_expression; LESSTHANEQUAL; rhs = expression; SEMICOLON;
    { RawVerilog.Assign { assignment_type = RawVerilog.NonBlocking; lhs; rhs  } }
  | IF; condition = expression; if_branch = statement; ELSE; else_branch = statement;
    { RawVerilog.If { condition; if_branch; else_branch = Some else_branch } }
  | IF; condition = expression; if_branch = statement;
    { RawVerilog.If { condition; if_branch; else_branch = None } }
  | BEGIN; body = many(statement); END;
    { RawVerilog.Block body }

let expression_only := x = only(expression); { x }

%inline binary_operator :
  | (* '+' *)        PLUS;                 { RawVerilog.BinaryPlus                 }
  | (* '-' *)        MINUS;                { RawVerilog.BinaryMinus                }
  | (* '*' *)        STAR;                 { RawVerilog.BinaryStar                 }
  | (* '/' *)        SLASH;                { RawVerilog.BinarySlash                }
  | (* '%' *)        PERCENT;              { RawVerilog.BinaryPercent              }
  | (* '==' *)       EQUALSEQUALS;         { RawVerilog.BinaryEqualsEquals         }
  | (* '!=' *)       NOTEQUALS;            { RawVerilog.BinaryNotEquals            }
  | (* '===' *)      EQUALSEQUALSEQUALS;   { RawVerilog.BinaryEqualsEqualsEquals   }
  | (* '!==' *)      NOTEQUALSEQUALS;      { RawVerilog.BinaryNotEqualsEquals      }
  | (* '==?' *)      WILDCARDEQUAL;        { RawVerilog.BinaryWildcardEqual        }
  | (* '!=?' *)      WILDCARDNOTEQUAL;     { RawVerilog.BinaryWildcardNotEqual     }
  | (* '&&' *)       LOGICALAND;           { RawVerilog.BinaryLogicalAnd           }
  | (* '||' *)       LOGICALOR;            { RawVerilog.BinaryLogicalOr            }
  | (* '**' *)       EXPONENT;             { RawVerilog.BinaryExponent             }
  | (* '<' *)        LESSTHAN;             { RawVerilog.BinaryLessThan             }
  | (* '<=' *)       LESSTHANEQUAL;        { RawVerilog.BinaryLessThanEqual        }
  | (* '>' *)        GREATERTHAN;          { RawVerilog.BinaryGreaterThan          }
  | (* '>=' *)       GREATERTHANEQUAL;     { RawVerilog.BinaryGreaterThanEqual     }
  | (* '&' *)        BITWISEAND;           { RawVerilog.BinaryBitwiseAnd           }
  | (* '|' *)        BITWISEOR;            { RawVerilog.BinaryBitwiseOr            }
  | (* '^' *)        BITWISEXOR;           { RawVerilog.BinaryBitwiseXor           }
  | (* '^~', '~^' *) BITWISEXNOR;          { RawVerilog.BinaryXNor                 }
  | (* '>>' *)       SHIFTRIGHT;           { RawVerilog.BinaryShiftRight           }
  | (* '<<' *)       SHIFTLEFT;            { RawVerilog.BinaryShiftLeft            }
  | (* '>>>' *)      SHIFTRIGHTARITHMETIC; { RawVerilog.BinaryShiftRightArithmetic }
  | (* '<<<' *)      SHIFTLEFTARITHMETIC;  { RawVerilog.BinaryShiftLeftArithmetic  }
  | (* '->' *)       LOGICALIMPLICATION;   { RawVerilog.BinaryLogicalImplication   }
  | (* '<->' *)      LOGICALEQUIVALENCE;   { RawVerilog.BinaryLogicalEquivalence   }


let lhs_expression :=
  | ident = IDENTIFIER;
    {
      RawVerilog.Identifier ident
    }
  | value = NUMBER;
    {
      RawVerilog.Literal { width = 32; value }
    }
  | target = expression; LBRACKET; index = expression; RBRACKET;
    {
      RawVerilog.BitSelect { target; index }
    }
  | target = expression; LBRACKET; low = expression; COLON; high = expression; RBRACKET;
    {
      RawVerilog.RangeSelect { target; low; high }
    }
  | (width, value) = SIZED_NUMBER;
    {
      RawVerilog.Literal { width; value }
    }
  | LPAREN; e = expression; RPAREN;
    { e }

let expression :=
  | ident = IDENTIFIER;
    {
      RawVerilog.Identifier ident
    }
  | value = NUMBER;
    {
      RawVerilog.Literal { width = 32; value }
    }
  | target = expression; LBRACKET; index = expression; RBRACKET;
    {
      RawVerilog.BitSelect { target; index }
    }
  | target = expression; LBRACKET; low = expression; COLON; high = expression; RBRACKET;
    {
      RawVerilog.RangeSelect { target; low; high }
    }
  | (width, value) = SIZED_NUMBER;
    {
      RawVerilog.Literal { width; value }
    }
  | lhs = expression; operator = binary_operator; rhs = expression;
    {
      RawVerilog.BinaryOp { lhs; operator; rhs }
    }
  | condition = expression; QUESTIONMARK; true_branch = expression; COLON; false_branch = expression;
    {
      RawVerilog.Conditional { condition; true_branch; false_branch }
    }
  | LPAREN; e = expression; RPAREN;
    { e }
