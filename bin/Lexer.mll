{
open Format
open Parser

exception SyntaxError of string

let token_fmt fmt = function
    | EOF -> fprintf fmt "EOF"
    | MODULE  -> fprintf fmt "MODULE"
    | ENDMODULE  -> fprintf fmt "ENDMODULE"
    | REG -> fprintf fmt "REG"
    | WIRE -> fprintf fmt "WIRE"
    | INPUT -> fprintf fmt "INPUT"
    | ASSIGN -> fprintf fmt "ASSIGN"
    | ALWAYS -> fprintf fmt "ALWAYS"
    | ALWAYS_FF -> fprintf fmt "ALWAYS_FF"
    | POSEDGE -> fprintf fmt "POSEDGE"
    | OUTPUT -> fprintf fmt "OUTPUT"
    | LPAREN -> fprintf fmt "LPAREN"
    | RPAREN -> fprintf fmt "RPAREN"
    | LBRACKET -> fprintf fmt "LBRACKET"
    | RBRACKET -> fprintf fmt "RBRACKET"
    | LBRACE -> fprintf fmt "LBRACE"
    | RBRACE -> fprintf fmt "RBRACE"
    | BEGIN -> fprintf fmt "BEGIN"
    | END -> fprintf fmt "END"
    | SEMICOLON -> fprintf fmt "SEMICOLON"
    | COLON -> fprintf fmt "COLON"
    | COMMA -> fprintf fmt "COMMA"
    | EQUALS -> fprintf fmt "EQUALS"
    | LESSTHANEQUAL -> fprintf fmt "LESSTHANEQUAL"
    | GREATERTHANEQUAL -> fprintf fmt "GREATERTHANEQUAL"
    | PLUS -> fprintf fmt "PLUS"
    | MINUS -> fprintf fmt "MINUS"
    | MULTIPLY -> fprintf fmt "MULTIPLY"
    | DIVIDE -> fprintf fmt "DIVIDE"
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

let whitespace = [' ' '\t' '\n' '\r']+
let newline = '\n'

rule read = parse
    | eof { EOF }
    | whitespace { read lexbuf }
    | "//" { read_single_line_comment lexbuf }
    | "module" { MODULE }
    | "endmodule" { ENDMODULE }
    | "reg" { REG }
    | "wire" { WIRE }
    | "input" { INPUT }
    | "assign" { ASSIGN }
    | "always" { ALWAYS }
    | "always_ff" { ALWAYS_FF }
    | "output" { OUTPUT }
    | "posedge" { POSEDGE }
    | '(' { LPAREN }
    | ')' { RPAREN }
    | '[' { LBRACKET }
    | ']' { RBRACKET }
    | '{' { LBRACE }
    | '}' { RBRACE }
    | "begin" { BEGIN }
    | "end" { END }
    | ';' { SEMICOLON }
    | ':' { COLON }
    | ',' { COMMA }
    | '=' { EQUALS }
    | '+' { PLUS }
    | '-' { MINUS }
    | '*' { MULTIPLY }
    | '/' { DIVIDE }
    | '@' { AT }
    | "<=" { LESSTHANEQUAL }
    | ">=" { GREATERTHANEQUAL }
    | simple_identifier { IDENTIFIER (Lexing.lexeme lexbuf) }
    | sized_hex_number { Scanf.sscanf (Lexing.lexeme lexbuf) "%d'h%x" (fun s v -> SIZED_NUMBER (s, v)) }
    | unsized_hex_number { Scanf.sscanf (Lexing.lexeme lexbuf) "'h%x" (fun v -> NUMBER v)}
    | sized_decimal_number { Scanf.sscanf (Lexing.lexeme lexbuf) "%d'd%d" (fun s v -> SIZED_NUMBER (s, v)) }
    | unsized_decimal_number { Scanf.sscanf (Lexing.lexeme lexbuf) "'d%d" (fun v -> NUMBER v)}
    | unmarked_decimal_number { Scanf.sscanf (Lexing.lexeme lexbuf) "%d" (fun v -> NUMBER v)}
and read_single_line_comment = parse
  | newline { read lexbuf }
  | _ { read_single_line_comment lexbuf }
