open Format
open Driver
open Cmdliner

let ( >>= ) (x : ('err, 'a) Vera.sum) (f : 'a -> ('err, 'b) Vera.sum) =
  match x with Vera.Inl e -> Vera.Inl e | Vera.Inr x -> f x

let ( let* ) = ( >>= )
let ( =<< ) a b = b >>= a
let ret x = Vera.Inr x

let fmap f x =
  let* xval = x in
  ret (f xval)

let ( <$> ) = fmap
let ( <&> ) x f = fmap f x

let ( >=> ) (f : 'a -> ('err, 'b) Vera.sum) (g : 'b -> ('err, 'c) Vera.sum)
    (x : 'a) : ('err, 'c) Vera.sum =
  let* y = f x in
  g y

let usage_and_exit () =
  eprintf "Usage: %s <command> [args]\n" Sys.argv.(0);
  eprintf "\n";
  eprintf "Commands:\n";
  eprintf "  compare <filename1> <filename2>\n";
  eprintf "  lower <level> <filename>\n";
  eprintf "  parse_custom <filename>\n";
  eprintf "  parse_slang <filename>\n";
  eprintf "\n";
  eprintf "Arguments:\n";
  eprintf "  level: parsed|typed|netlist|smt_netlist|smt\n";
  exit 1

module VerilogParser (P : sig
  type parsed

  val pp : formatter -> parsed -> unit
  val parse_file : string -> parsed
end) =
struct
  include P

  let run_parser_command = function
    | [ filename ] ->
        let m = P.parse_file filename in
        printf "%a\n" P.pp m
    | _ -> usage_and_exit ()
end

module MyVerilogParser = VerilogParser (struct
  type parsed = Vera.UntypedVerilog.vmodule

  let pp = VerilogPP.Untyped.vmodule

  let parse_file filename =
    let print_position outx (lexbuf : Lexing.lexbuf) =
      let pos = lexbuf.lex_curr_p in
      fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum
        (pos.pos_cnum - pos.pos_bol + 1)
    in
    let lexbuf = Lexing.from_channel (open_in filename) in
    Lexing.set_filename lexbuf filename;
    try
      ParseRawVerilog.parse_raw_verilog (Parser.vmodule_only Lexer.read lexbuf)
    with
    | Lexer.SyntaxError msg ->
        printf "%a: %s\n" print_position lexbuf msg;
        exit (-1)
    | Parser.Error ->
        printf "%a: syntax error\n" print_position lexbuf;
        exit (-1)
end)

module SlangVerilogParser = VerilogParser (struct
  type parsed = Vera.Verilog.vmodule

  let pp = VerilogPP.Typed.vmodule
  let parse_file = ParseSlang.parse_verilog_file
end)

let module_of_file = SlangVerilogParser.parse_file

let typed_module_of_file f =
  let m = module_of_file f in
  let* () = Vera.tc_vmodule m in
  ret m

let canonical_module_of_file =
  typed_module_of_file >=> Vera.canonicalize_verilog

let smt_of_file filename =
  (* Need to tag it as left or right, doesn't matter here because we only
      translate one module *)
  Vera.verilog_to_smt VerilogLeft (Vera.int_to_nat 0)
  =<< canonical_module_of_file filename

let compare solver filename1 filename2 =
  let queryResult =
    Vera.equivalence_query (module_of_file filename1) (module_of_file filename2)
  in
  match queryResult with
  | Vera.Inl err -> printf "Error: %s\n" (Util.lst_to_string err)
  | Vera.Inr query -> (
      match solver query with
      | SMTLIB.UNSAT, out ->
          printf "Equivalent (UNSAT)\n";
          printf "%s\n" out
      | SMTLIB.SAT, out ->
          printf "Non-equivalent (SAT)\n";
          printf "%s\n" out
      | SMTLIB.Error, out ->
          printf "Error\n";
          printf "%s\n" out)

let rec lower level filename =
  let display_or_error pp result =
    match result with
    | Vera.Inl err -> printf "Error: %s\n" (Util.lst_to_string err)
    | Vera.Inr x -> printf "%a\n" pp x
  in
  match level with
  | `Parsed ->
      display_or_error VerilogPP.Typed.vmodule
        (Vera.Inr (module_of_file filename))
  | `Typed ->
      display_or_error VerilogPP.Typed.vmodule (typed_module_of_file filename)
  | `Canonical ->
      display_or_error VerilogPP.Typed.vmodule
        (canonical_module_of_file filename)
  | `SMT -> display_or_error SMTPP.SMTLib.query (smt_of_file filename)
  | `All ->
      printf "\n-- parsed -- \n";
      lower `Parsed filename;
      printf "\n-- typed --\n";
      lower `Typed filename;
      printf "\n-- canonical --\n";
      lower `Canonical filename;
      printf "\n-- smt --\n";
      lower `SMT filename

let compare_cmd =
  let open Cmdliner.Term.Syntax in
  let solver_enum =
    Arg.enum
      [
        ("z3", SMTLIB.run_query_z3);
        ("cvc5", SMTLIB.run_query_cvc5);
        ("bitwuzla", SMTLIB.run_query_bitwuzla);
      ]
  in
  Cmd.v (Cmd.info "compare")
  @@
  let+ solver =
    Arg.(
      required
      & opt (some solver_enum) None
      & info [ "s"; "solver" ] ~docv:"SOLVER" ~doc:"Solver to use (z3, cvc5)")
  and+ file_left =
    Arg.(
      required
      & pos 0 (some file) None
      & info [] ~docv:"FILE_LEFT" ~doc:"First verilog file to compare")
  and+ file_right =
    Arg.(
      required
      & pos 1 (some file) None
      & info [] ~docv:"FILE_RIGHT" ~doc:"Second verilog file to compare")
  in
  compare solver file_left file_right

let lower_cmd =
  let open Cmdliner.Term.Syntax in
  let lower_level =
    Arg.enum
      [
        ("parsed", `Parsed);
        ("typed", `Typed);
        ("canonical", `Canonical);
        ("smt", `SMT);
        ("all", `All);
      ]
  in
  Cmd.v (Cmd.info "lower")
  @@
  let+ lower_level =
    Arg.(
      required
      & pos 0 (some lower_level) None
      & info [] ~docv:"LEVEL" ~doc:"Level to lower to")
  and+ file = Arg.(required & pos 1 (some file) None & info [] ~docv:"FILE") in
  lower lower_level file

let vera_cmd = Cmd.group (Cmd.info "vera") [ lower_cmd; compare_cmd ]
let () = Cmd.eval vera_cmd |> exit
