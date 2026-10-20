(* Adapted from origin/sequential's concrete BTOR parser. *)
open Vera.Btor2.Raw

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

module IdMap = Map.Make (Z)

type value_kind = State | Input | Expression
type entry = Sort of Z.t | Value of Z.t * value_kind | Statement

type parser = {
  mutable entries : entry IdMap.t;
  mutable body : node list;
}

let name id = "i" ^ Z.to_string id

(* A single optional symbol is accepted but does not determine the name. *)
let operands line count args =
  if List.length args = count then args
  else if List.length args = count + 1 then
    List.filteri (fun i _ -> i < count) args
  else error line "wrong operand count"

let equal_width line expected actual =
  if not (Z.equal expected actual) then
    error line (Printf.sprintf "expected bitvector width %s, got %s"
      (Z.to_string expected) (Z.to_string actual))

let find line parser token =
  let id = positive line token in
  match IdMap.find_opt id parser.entries with
  | Some entry -> id, entry
  | None -> error line ("undefined or forward reference: " ^ token)

let sort line parser token =
  match find line parser token with
  | _, Sort width -> width
  | _ -> error line ("not a sort ID: " ^ token)

let value line parser token =
  match find line parser token with
  | id, Value (width, kind) -> width, ExprRef (name id), kind
  | _ -> error line ("not a value ID: " ^ token)

let operation line parser result opcode args =
  let operand token =
    let width, expr, _ = value line parser token in width, expr
  in
  let unary boolean ctor =
    match operands line 1 args with
    | [e] ->
        let width, e = operand e in
        equal_width line (if boolean then Z.one else width) result;
        ctor width e
    | _ -> assert false
  in
  let binary boolean ctor =
    match operands line 2 args with
    | [l; r] ->
        let width, l = operand l in
        let right_width, r = operand r in
        equal_width line width right_width;
        equal_width line (if boolean then Z.one else width) result;
        ctor width l r
    | _ -> assert false
  in
  let logical ctor =
    binary true (fun width l r -> equal_width line Z.one width; ctor l r)
  in
  match opcode with
  | "not" -> unary false (fun _ e -> Not e)
  | "inc" -> unary false (fun _ e -> Inc e)
  | "dec" -> unary false (fun _ e -> Dec e)
  | "redand" -> unary true (fun _ e -> RedAnd e)
  | "redor" -> unary true (fun _ e -> RedOr e)
  | "redxor" -> unary true (fun _ e -> RedXor e)
  | "iff" -> logical (fun l r -> Iff (l, r))
  | "implies" -> logical (fun l r -> Implies (l, r))
  | "eq" -> binary true (fun _ l r -> Eq (l, r))
  | "neq" -> binary true (fun _ l r -> NEq (l, r))
  | "sgt" -> binary true (fun _ l r -> SignedGt (l, r))
  | "ugt" -> binary true (fun _ l r -> UnsignedGt (l, r))
  | "sgte" -> binary true (fun _ l r -> SignedGtE (l, r))
  | "ugte" -> binary true (fun _ l r -> UnsignedGtE (l, r))
  | "slt" -> binary true (fun _ l r -> SignedLt (l, r))
  | "ult" -> binary true (fun _ l r -> UnsignedLt (l, r))
  | "slte" -> binary true (fun _ l r -> SignedLtE (l, r))
  | "ulte" -> binary true (fun _ l r -> UnsignedLtE (l, r))
  | "and" -> binary false (fun _ l r -> And (l, r))
  | "nand" -> binary false (fun _ l r -> NAnd (l, r))
  | "or" -> binary false (fun _ l r -> Or (l, r))
  | "nor" -> binary false (fun _ l r -> NOr (l, r))
  | "xor" -> binary false (fun _ l r -> XOr (l, r))
  | "xnor" -> binary false (fun _ l r -> XNor (l, r))
  | "rol" -> binary false (fun _ l r -> Rol (l, r))
  | "sll" -> binary false (fun _ l r -> Sll (l, r))
  | "sra" -> binary false (fun _ l r -> Sra (l, r))
  | "srl" -> binary false (fun _ l r -> Srl (l, r))
  | "add" -> binary false (fun _ l r -> Add (l, r))
  | "mul" -> binary false (fun _ l r -> Mul (l, r))
  | "sdiv" -> binary false (fun _ l r -> SignedDiv (l, r))
  | "udiv" -> binary false (fun _ l r -> UnsignedDiv (l, r))
  | "smod" -> binary false (fun _ l r -> SignedMod (l, r))
  | "srem" -> binary false (fun _ l r -> SignedRem (l, r))
  | "urem" -> binary false (fun _ l r -> UnsignedRem (l, r))
  | "sub" -> binary false (fun _ l r -> Sub (l, r))
  | "saddo" -> binary true (fun _ l r -> SignedAddOverflow (l, r))
  | "uaddo" -> binary true (fun _ l r -> UnsignedAddOverflow (l, r))
  | "sdivo" -> binary true (fun _ l r -> SignedDivOverflow (l, r))
  | "smulo" -> binary true (fun _ l r -> SignedMulOverflow (l, r))
  | "umulo" -> binary true (fun _ l r -> UnsignedMulOverflow (l, r))
  | "ssubo" -> binary true (fun _ l r -> SignedSubOverflow (l, r))
  | "usubo" -> binary true (fun _ l r -> UnsignedSubOverflow (l, r))
  | "uext" | "sext" ->
      (match operands line 2 args with
      | [e; amount] ->
          let width, e = operand e in
          let amount = natural line amount in
          equal_width line (Z.add width amount) result;
          if Z.equal amount Z.zero then e
          else if opcode = "uext" then UnsignedExtend (amount, e)
          else SignedExtend (amount, e)
      | _ -> assert false)
  | "slice" ->
      (match operands line 3 args with
      | [e; hi; lo] ->
          let width, e = operand e in
          let hi = natural line hi and lo = natural line lo in
          if Z.gt lo hi || Z.geq hi width then error line "invalid slice bounds";
          equal_width line (Z.succ (Z.sub hi lo)) result;
          Slice (hi, lo, e)
      | _ -> assert false)
  | "concat" ->
      (match operands line 2 args with
      | [l; r] ->
          let lw, l = operand l and rw, r = operand r in
          equal_width line (Z.add lw rw) result;
          Concat (l, r)
      | _ -> assert false)
  | "ite" ->
      (match operands line 3 args with
      | [cond; if_t; if_f] ->
          let cw, cond = operand cond in
          let tw, if_t = operand if_t and fw, if_f = operand if_f in
          equal_width line Z.one cw;
          equal_width line result tw;
          equal_width line result fw;
          ITE (cond, if_t, if_f)
      | _ -> assert false)
  | _ -> error line ("unsupported operation: " ^ opcode)

let constant line width opcode args =
  let literal () = match operands line 1 args with
    | [text] -> text | _ -> assert false
  in
  let value = match opcode with
    | "zero" | "one" | "ones" ->
        ignore (operands line 0 args);
        if opcode = "zero" then Z.zero else if opcode = "one" then Z.one else Z.minus_one
    | "const" ->
        let text = literal () in
        if not (String.for_all (fun c -> c = '0' || c = '1') text) then
          error line "invalid binary constant";
        equal_width line width (Z.of_int (String.length text));
        Z.of_string_base 2 text
    | "consth" ->
        let text = literal () in
        if text = "" || not (String.for_all (function
          | '0'..'9' | 'a'..'f' | 'A'..'F' -> true | _ -> false) text) then
          error line "invalid hexadecimal constant";
        Z.of_string_base 16 text
    | "constd" ->
        let text = literal () in
        if String.length text > 0 && text.[0] = '-' then
          Z.neg (natural line (String.sub text 1 (String.length text - 1)))
        else natural line text
    | _ -> assert false
  in
  let required_bits = if Z.sign value < 0 then
      Z.of_int (1 + Z.numbits (Z.pred (Z.neg value)))
    else Z.of_int (Z.numbits value)
  in
  if Z.gt required_bits width then error line "constant does not fit its sort";
  if not (Z.fits_int width) then error line "constant width is too large to materialize";
  Constant (List.init (Z.to_int width) (Z.testbit value))

let parse_line parser line text =
  let text = match String.index_opt text ';' with
    | Some i -> String.sub text 0 i | None -> text
  in
  match Str.split (Str.regexp "[ \t\r]+") text with
  | [] -> ()
  | id :: opcode :: args ->
      let id = positive line id in
      (* The resolution map already contains every earlier line's ID. *)
      (match IdMap.max_binding_opt parser.entries with
      | Some (previous, _) when Z.leq id previous ->
          error line "IDs must be unique and strictly increasing"
      | _ -> ());
      let entry, node = match opcode, args with
        | "sort", "bitvec" :: args ->
            (match operands line 1 args with
            | [width] -> Sort (positive line width), None
            | _ -> assert false)
        | "sort", _ -> error line "only bitvector sorts are supported"
        | ("constraint" | "fair" | "justice" | "output"), _ ->
            error line ("unsupported node: " ^ opcode)
        | ("state" | "input"), args ->
            (match operands line 1 args with
            | [sid] ->
                let width = sort line parser sid in
                Value (width, if opcode = "state" then State else Input),
                Some (StateDecl (name id, width))
            | _ -> assert false)
        | ("init" | "next"), args ->
            (match operands line 3 args with
            | [sid; target; source] ->
                let width = sort line parser sid in
                let tw, _, kind = value line parser target in
                if kind <> State then error line "init/next target must be a state";
                let sw, source, _ = value line parser source in
                equal_width line width tw;
                equal_width line width sw;
                let target = name (positive line target) in
                Statement, Some (if opcode = "init" then StateInit (width, target, source)
                  else StateNext (width, target, source))
            | _ -> assert false)
        | "bad", args ->
            (match operands line 1 args with
            | [source] ->
                let width, source, _ = value line parser source in
                equal_width line Z.one width;
                Statement, Some (Bad source)
            | _ -> assert false)
        | _, sid :: args ->
            let width = sort line parser sid in
            let expr = match opcode with
              | "const" | "constd" | "consth" | "zero" | "one" | "ones" ->
                  constant line width opcode args
              | _ -> operation line parser width opcode args
            in
            Value (width, Expression), Some (Operator (width, name id, expr))
        | _ -> error line "expected a sort ID and operands"
      in
      parser.entries <- IdMap.add id entry parser.entries;
      Option.iter (fun nd -> parser.body <- nd :: parser.body) node
  | _ -> error line "expected a node ID, opcode, and operands"

let create () = { entries = IdMap.empty; body = [] }

let finish parser = List.rev parser.body

let parse_string text =
  let parser = create () in
  String.split_on_char '\n' text |> List.iteri (fun i text -> parse_line parser (i + 1) text);
  finish parser

let parse_channel channel =
  let parser = create () in
  let rec loop line =
    match input_line channel with
    | text -> parse_line parser line text; loop (line + 1)
    | exception End_of_file -> finish parser
  in
  loop 1

let parse_file filename =
  let channel = open_in filename in
  Fun.protect ~finally:(fun () -> close_in channel)
    (fun () -> parse_channel channel)
