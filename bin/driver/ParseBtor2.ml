open Vera.Concrete

exception Parse_error of int * string

let () =
  Printexc.register_printer (function
    | Parse_error (line, message) ->
        Some (Printf.sprintf "BTOR parse error on line %d: %s" line message)
    | _ -> None)

let error line message = raise (Parse_error (line, message))

let natural line token =
  if token = "" || not (String.for_all (fun c -> c >= '0' && c <= '9') token) then
    error line (Printf.sprintf "expected a nonnegative decimal integer, got %S" token);
  Z.of_string token

let positive line token =
  let value = natural line token in
  if Z.sign value = 0 then
    error line (Printf.sprintf "expected a positive integer, got %S" token);
  value

let operation line opcode args =
  let id = positive line in
  let nat = natural line in
  match opcode, args with
  | "uext", [e; w] -> UnsignedExtend (nat w, id e)
  | "sext", [e; w] -> SignedExtend (nat w, id e)
  | "slice", [e; hi; lo] -> Slice (nat hi, nat lo, id e)
  | "not", [e] -> Not (id e)
  | "inc", [e] -> Inc (id e)
  | "dec", [e] -> Dec (id e)
  | "redand", [e] -> RedAnd (id e)
  | "redor", [e] -> RedOr (id e)
  | "redxor", [e] -> RedXor (id e)
  | "iff", [l; r] -> Iff (id l, id r)
  | "implies", [l; r] -> Implies (id l, id r)
  | "eq", [l; r] -> Eq (id l, id r)
  | "neq", [l; r] -> NEq (id l, id r)
  | "sgt", [l; r] -> SignedGt (id l, id r)
  | "ugt", [l; r] -> UnsignedGt (id l, id r)
  | "sgte", [l; r] -> SignedGtE (id l, id r)
  | "ugte", [l; r] -> UnsignedGtE (id l, id r)
  | "slt", [l; r] -> SignedLt (id l, id r)
  | "ult", [l; r] -> UnsignedLt (id l, id r)
  | "slte", [l; r] -> SignedLtE (id l, id r)
  | "ulte", [l; r] -> UnsignedLtE (id l, id r)
  | "and", [l; r] -> And (id l, id r)
  | "nand", [l; r] -> NAnd (id l, id r)
  | "or", [l; r] -> Or (id l, id r)
  | "nor", [l; r] -> NOr (id l, id r)
  | "xor", [l; r] -> XOr (id l, id r)
  | "xnor", [l; r] -> XNor (id l, id r)
  | "rol", [l; r] -> Rol (id l, id r)
  | "sll", [l; r] -> Sll (id l, id r)
  | "sra", [l; r] -> Sra (id l, id r)
  | "srl", [l; r] -> Srl (id l, id r)
  | "add", [l; r] -> Add (id l, id r)
  | "mul", [l; r] -> Mul (id l, id r)
  | "sdiv", [l; r] -> SignedDiv (id l, id r)
  | "udiv", [l; r] -> UnsignedDiv (id l, id r)
  | "smod", [l; r] -> SignedMod (id l, id r)
  | "srem", [l; r] -> SignedRem (id l, id r)
  | "urem", [l; r] -> UnsignedRem (id l, id r)
  | "sub", [l; r] -> Sub (id l, id r)
  | "saddo", [l; r] -> SignedAddOverflow (id l, id r)
  | "uaddo", [l; r] -> UnsignedAddOverflow (id l, id r)
  | "sdivo", [l; r] -> SignedDivOverflow (id l, id r)
  | "smulo", [l; r] -> SignedMulOverflow (id l, id r)
  | "umulo", [l; r] -> UnsignedMulOverflow (id l, id r)
  | "ssubo", [l; r] -> SignedSubOverflow (id l, id r)
  | "usubo", [l; r] -> UnsignedSubOverflow (id l, id r)
  | "concat", [l; r] -> Concat (id l, id r)
  | "ite", [cond; ifT; ifF] -> ITE (id cond, id ifT, id ifF)
  | _ -> error line (Printf.sprintf "unsupported operation or wrong operand count: %s" opcode)

(* Parse the concrete AST's fields only; do not resolve or renumber references. *)
let parse_line line text =
  let text =
    match String.index_opt text ';' with
    | Some i -> String.sub text 0 i
    | None -> text
  in
  let tokens = Str.split (Str.regexp "[ \t\r]+") text in
  let id = positive line in
  let node =
    match tokens with
    | [] -> None
    | [i; "sort"; "bitvec"; width] -> Some (SortDecl (id i, id width))
    | [i; "init"; s; state; init] -> Some (StateInit (id i, id s, id state, id init))
    | [i; "next"; s; state; next] -> Some (StateNext (id i, id s, id state, id next))
    | [i; "bad"; p] -> Some (Bad (id i, id p))
    | [i; "constraint"; p] -> Some (Constraint (id i, id p))
    | [i; "fair"; p] -> Some (Fair (id i, id p))
    | [i; "output"; p] -> Some (Output (id i, id p))
    | [i; "justice"; n] -> Some (Justice (id i, id n))
    | i :: opcode :: s :: args -> Some (Operation (id i, id s, operation line opcode args))
    | _ -> error line "expected a node ID, opcode, and operands"
  in
  node

let parse_string text =
  String.split_on_char '\n' text
  |> List.mapi (fun i line -> parse_line (i + 1) line)
  |> List.filter_map Fun.id

let parse_channel channel =
  let rec loop line nodes =
    match input_line channel with
    | text ->
        let nodes = match parse_line line text with
          | Some node -> node :: nodes
          | None -> nodes
        in
        loop (line + 1) nodes
    | exception End_of_file -> List.rev nodes
  in
  loop 1 []

let parse_file filename =
  let channel = open_in filename in
  Fun.protect ~finally:(fun () -> close_in channel)
    (fun () -> parse_channel channel)
