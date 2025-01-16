type identifier = string [@@deriving show]
type direction = Input | Output [@@deriving show]

type net_type = Logic of int * int | Reg of int * int | Wire of int * int
[@@deriving show]

type port_declaration = {
  direction : direction;
  net_type : net_type;
  name : identifier;
}
[@@deriving show]

type assignment_type = Blocking | NonBlocking [@@deriving show]
type constant = { width : int; value : int } [@@deriving show]
type constant_expression = Literal of constant [@@deriving show]

type unary_operator =
  | UnaryPlus (* + *)
  | UnaryMinus (* - *)
  | UnaryBang (* ! *)
  | UnaryTilde (* ~ *)
  | UnaryAnd (* & *)
  | UnaryNand (* ~& *)
  | UnaryOr (* | *)
  | UnaryNor (* ~| *)
  | UnaryXor (* ^ *)
  | UnaryXNor (* ~^ , ^~ *)
[@@deriving show]

type binary_operator =
  | BinaryPlus (* '+' *)
  | BinaryMinus (* '-' *)
  | BinaryStar (* '*' *)
  | BinarySlash (* '/' *)
  | BinaryPercent (* '%' *)
  | BinaryEqualsEquals (* '==' *)
  | BinaryNotEquals (* '!=' *)
  | BinaryEqualsEqualsEquals (* '===' *)
  | BinaryNotEqualsEquals (* '!==' *)
  | BinaryWildcardEqual (* '==?' *)
  | BinaryWildcardNotEqual (* '!=?' *)
  | BinaryLogicalAnd (* '&&' *)
  | BinaryLogicalOr (* '||' *)
  | BinaryExponent (* '**' *)
  | BinaryLessThan (* '<' *)
  | BinaryLessThanEqual (* '<=' *)
  | BinaryGreaterThan (* '>' *)
  | BinaryGreaterThanEqual (* '>=' *)
  | BinaryBitwiseAnd (* '&' *)
  | BinaryBitwiseOr (* '|' *)
  | BinaryBitwiseXor (* '^' *)
  | BinaryXNor (* '^~', '~^' *)
  | BinaryShiftRight (* '>>' *)
  | BinaryShiftLeft (* '<<' *)
  | BinaryShiftRightArithmetic (* '>>>' *)
  | BinaryShiftLeftArithmetic (* '<<<' *)
  | BinaryLogicalImplication (* '->' *)
  | BinaryLogicalEquivalence (* '<->' *)
[@@deriving show]

type expression =
  | Conditional of conditional_expression
  | UnaryOp of unary_expression
  | BinaryOp of binary_expression
  | Identifier of identifier
  | BitSelect of bit_select_expression
  | RangeSelect of range_select_expression
  | Literal of constant
[@@deriving show]

and conditional_expression = {
  condition : expression;
  true_branch : expression;
  false_branch : expression;
}
[@@deriving show]

and unary_expression = { operator : unary_operator; operand : expression }
[@@deriving show]

and binary_expression = {
  operator : binary_operator;
  lhs : expression;
  rhs : expression;
}
[@@deriving show]

and bit_select_expression = { target : expression; index : expression }
[@@deriving show]

and range_select_expression = {
  target : expression;
  high : expression;
  low : expression;
}
[@@deriving show]

type statement =
  | Assign of assign_statement
  | If of if_statement
  | Block of statement list
[@@deriving show]

and if_statement = {
  condition : expression;
  if_branch : statement;
  else_branch : statement option;
}
[@@deriving show]

and assign_statement = {
  assignment_type : assignment_type;
  lhs : expression;
  rhs : expression;
}
[@@deriving show]

type declaration = { name : identifier; initialization : expression option }
[@@deriving show]

type net_declaration = {
  port : direction option;
  net_type : net_type;
  declarations : declaration list;
}
[@@deriving show]

type edge = Posedge | Negedge [@@deriving show]

type clocking = ClockingStar | ClockingEdge of edge * identifier
[@@deriving show]

type module_item =
  | NetDeclaration of net_declaration
  | AlwaysFF of clocking * statement
  | AlwaysComb of statement
  | ContinuousAssign of expression * expression
  | Initial of statement
[@@deriving show]

type vmodule = {
  name : identifier;
  ports : port_declaration list;
  body : module_item list;
}
[@@deriving show]
