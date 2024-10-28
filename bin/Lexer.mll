{
open Format
open Lexing
open Parser

exception SyntaxError of string

let token_fmt fmt = function
    | EOF -> fprintf fmt "EOF"
    | MODULE -> fprintf fmt "MODULE"
    | ENDMODULE -> fprintf fmt "ENDMODULE"
    | REG -> fprintf fmt "REG"
    | WIRE -> fprintf fmt "WIRE"
    | IF -> fprintf fmt "IF"
    | ELSE -> fprintf fmt "ELSE"
    | LOGIC -> fprintf fmt "LOGIC"
    | OUTPUT -> fprintf fmt "OUTPUT"
    | INPUT -> fprintf fmt "INPUT"
    | ASSIGN -> fprintf fmt "ASSIGN"
    | ALWAYS -> fprintf fmt "ALWAYS"
    | ALWAYS_FF -> fprintf fmt "ALWAYS_FF"
    | INITIAL -> fprintf fmt "INITIAL"
    | POSEDGE -> fprintf fmt "POSEDGE"
    | NEGEDGE -> fprintf fmt "NEGEDGE"
    | LPAREN -> fprintf fmt "LPAREN"
    | RPAREN -> fprintf fmt "RPAREN"
    | LBRACKET -> fprintf fmt "LBRACKET"
    | RBRACKET -> fprintf fmt "RBRACKET"
    | BEGIN -> fprintf fmt "BEGIN"
    | END -> fprintf fmt "END"
    | SEMICOLON -> fprintf fmt "SEMICOLON"
    | QUESTIONMARK -> fprintf fmt "QUESTIONMARK"
    | COLON -> fprintf fmt "COLON"
    | COMMA -> fprintf fmt "COMMA"
    | EQUALS -> fprintf fmt "EQUALS"
    | PLUS -> fprintf fmt "PLUS"
    | MINUS -> fprintf fmt "MINUS"
    | STAR -> fprintf fmt "STAR"
    | SLASH -> fprintf fmt "SLASH"
    | PERCENT -> fprintf fmt "PERCENT"
    | EQUALSEQUALS -> fprintf fmt "EQUALSEQUALS"
    | NOTEQUALS -> fprintf fmt "NOTEQUALS"
    | EQUALSEQUALSEQUALS -> fprintf fmt "EQUALSEQUALSEQUALS"
    | NOTEQUALSEQUALS -> fprintf fmt "NOTEQUALSEQUALS"
    | WILDCARDEQUAL -> fprintf fmt "WILDCARDEQUAL"
    | WILDCARDNOTEQUAL -> fprintf fmt "WILDCARDNOTEQUAL"
    | LOGICALAND -> fprintf fmt "LOGICALAND"
    | LOGICALOR -> fprintf fmt "LOGICALOR"
    | EXPONENT -> fprintf fmt "EXPONENT"
    | LESSTHAN -> fprintf fmt "LESSTHAN"
    | LESSTHANEQUAL -> fprintf fmt "LESSTHANEQUAL"
    | GREATERTHAN -> fprintf fmt "GREATERTHAN"
    | GREATERTHANEQUAL -> fprintf fmt "GREATERTHANEQUAL"
    | BITWISEAND -> fprintf fmt "BITWISEAND"
    | BITWISEOR -> fprintf fmt "BITWISEOR"
    | BITWISEXOR -> fprintf fmt "BITWISEXOR"
    | BITWISEXNOR -> fprintf fmt "BITWISEXNOR"
    | SHIFTRIGHT -> fprintf fmt "SHIFTRIGHT"
    | SHIFTLEFT -> fprintf fmt "SHIFTLEFT"
    | SHIFTRIGHTARITHMETIC -> fprintf fmt "SHIFTRIGHTARITHMETIC"
    | SHIFTLEFTARITHMETIC -> fprintf fmt "SHIFTLEFTARITHMETIC"
    | LOGICALIMPLICATION -> fprintf fmt "LOGICALIMPLICATION"
    | LOGICALEQUIVALENCE -> fprintf fmt "LOGICALEQUIVALENCE"
    | AT -> fprintf fmt "AT"
    | IDENTIFIER n -> fprintf fmt "IDENTIFIER(%s)" n
    | NUMBER v -> fprintf fmt "CONSTANT(%d)" v
    | SIZED_NUMBER (s,v) -> fprintf fmt "SIZED_CONSTANT(%d, %d)" s v
}

let identifier_start_char = ['A'-'Z' 'a'-'z' '_']
let identifier_char =  identifier_start_char | ['0'-'9' '$']
let simple_identifier = identifier_start_char ( identifier_char )*

let hex_base = "'h" | "'H"
let hex_digit = ['0'-'9' 'a'-'f' 'A'-'F']
let hex_value = hex_digit+

let decimal_base = "'d" | "'D"
let decimal_digit = ['0'-'9']
let decimal_value = decimal_digit+

let size = decimal_value

let sized_hex_number = size hex_base hex_value
let unsized_hex_number = hex_base hex_value

let sized_decimal_number = size decimal_base decimal_value
let unsized_decimal_number = decimal_base decimal_value
let unmarked_decimal_number = decimal_value

let whitespace = [ ' ' '\t' ]+
let newline =  "\r\n" | '\r' | '\n'

rule read = parse
    | eof { EOF }
    | newline { new_line lexbuf; read lexbuf }
    | whitespace { read lexbuf }
    | "//" { read_single_line_comment lexbuf }
    | "module" { MODULE }
    | "endmodule" { ENDMODULE }
    | "reg" { REG }
    | "wire" { WIRE }
    | "if" { IF }
    | "else" { ELSE }
    | "logic" { LOGIC }
    | "input" { INPUT }
    | "assign" { ASSIGN }
    | "always" { ALWAYS }
    | "always_ff" { ALWAYS_FF }
    | "initial" { INITIAL }
    | "output" { OUTPUT }
    | "posedge" { POSEDGE }
    | "negedge" { NEGEDGE }
    | '(' { LPAREN }
    | ')' { RPAREN }
    | '[' { LBRACKET }
    | ']' { RBRACKET }
    | "begin" { BEGIN }
    | "end" { END }
    | ';' { SEMICOLON }
    | '?' { QUESTIONMARK }
    | ':' { COLON }
    | ',' { COMMA }
    | '=' { EQUALS }
    | '+' { PLUS }
    | '-' { MINUS }
    | '*' { STAR }
    | '/' { SLASH }
    | '%' { PERCENT }
    | "==" { EQUALSEQUALS }
    | "!=" { NOTEQUALS }
    | "===" { EQUALSEQUALSEQUALS }
    | "!==" { NOTEQUALSEQUALS }
    | "==?" { WILDCARDEQUAL }
    | "!=?" { WILDCARDNOTEQUAL }
    | "&&" { LOGICALAND }
    | "||" { LOGICALOR }
    | "**" { EXPONENT }
    | '<' { LESSTHAN }
    | "<=" { LESSTHANEQUAL }
    | '>' { GREATERTHAN }
    | ">=" { GREATERTHANEQUAL }
    | '&' { BITWISEAND }
    | '|' { BITWISEOR }
    | '^' { BITWISEXOR }
    | "^~" { BITWISEXNOR }
    | "~^" { BITWISEXNOR }
    | ">>" { SHIFTRIGHT }
    | "<<" { SHIFTLEFT }
    | ">>>" { SHIFTRIGHTARITHMETIC }
    | "<<<" { SHIFTLEFTARITHMETIC }
    | "->" { LOGICALIMPLICATION }
    | "<->" { LOGICALEQUIVALENCE }
    | '@' { AT }
    | simple_identifier { IDENTIFIER (Lexing.lexeme lexbuf) }
    | sized_hex_number { Scanf.sscanf (Lexing.lexeme lexbuf) "%d'h%x" (fun s v -> SIZED_NUMBER (s, v)) }
    | unsized_hex_number { Scanf.sscanf (Lexing.lexeme lexbuf) "'h%x" (fun v -> NUMBER v)}
    | sized_decimal_number { Scanf.sscanf (Lexing.lexeme lexbuf) "%d'd%d" (fun s v -> SIZED_NUMBER (s, v)) }
    | unsized_decimal_number { Scanf.sscanf (Lexing.lexeme lexbuf) "'d%d" (fun v -> NUMBER v)}
    | unmarked_decimal_number { Scanf.sscanf (Lexing.lexeme lexbuf) "%d" (fun v -> NUMBER v)}
and read_single_line_comment = parse
  | newline { new_line lexbuf; read lexbuf }
  | _ { read_single_line_comment lexbuf }
