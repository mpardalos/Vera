open Format
open Driver

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
  eprintf "  compare <verafile> <filename1> <filename2>\n";
  eprintf "  lower <level> <filename>\n";
  eprintf "  parse_custom <filename>\n";
  eprintf "  parse_slang <filename>\n";
  eprintf "\n";
  eprintf "Arguments:\n";
  eprintf "  level: parsed|typed|netlist|smt_netlist|smt\n";
  exit 1

let read_verafile filename : (string * string) list * (string * string) list =
  let channel = open_in filename in
  let rec read_verafile_lines acc_in acc_out =
    try
      let line = input_line channel in
      match String.split_on_char ' ' (String.trim line) with
      | [ "IN"; l; r ] ->
          read_verafile_lines (List.append acc_in [ (l, r) ]) acc_out
      | [ "OUT"; l; r ] ->
          read_verafile_lines acc_in (List.append acc_out [ (l, r) ])
      | [] | [ "" ] -> read_verafile_lines acc_in acc_out
      | _ -> raise (Failure (String.cat "Invalid line in .vera file: " line))
    with End_of_file -> (acc_in, acc_out)
  in
  read_verafile_lines [] []

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

let () =
  let module_of_file = SlangVerilogParser.parse_file in
  let typed_module_of_file f =
    let m = module_of_file f in
    let* () = Vera.tc_vmodule m in
    ret m
  in
  let canonical_module_of_file =
    typed_module_of_file >=> Vera.canonicalize_verilog
  in
  let smt_netlist_of_file = canonical_module_of_file >=> Vera.verilog_to_smt in
  let smt_formulas_of_file filename =
    Vera.SMT.smtnlFormulas <$> smt_netlist_of_file filename
  in

  let lower =
    let display_or_error pp result =
      match result with
      | Vera.Inl err -> printf "Error: %s\n" (Util.lst_to_string err)
      | Vera.Inr x -> printf "%a\n" pp x
    in
    function
    | [ "parsed"; filename ] ->
        display_or_error VerilogPP.Typed.vmodule
          (Vera.Inr (module_of_file filename))
    | [ "typed"; filename ] ->
        display_or_error VerilogPP.Typed.vmodule (typed_module_of_file filename)
    | [ "canonical"; filename ] ->
        display_or_error VerilogPP.Typed.vmodule
          (canonical_module_of_file filename)
    | [ "smt_netlist"; filename ] ->
        display_or_error SMTPP.StrSMT.smt_netlist (smt_netlist_of_file filename)
    | [ "smt"; filename ] ->
        display_or_error
          (pp_print_list SMTPP.StrSMT.smt ~pp_sep:Util.newline_sep)
          (smt_formulas_of_file filename)
    | [ "all"; filename ] ->
        printf "\n-- parsed -- \n";
        display_or_error VerilogPP.Typed.vmodule
          (Vera.Inr (module_of_file filename));
        printf "\n-- typed --\n";
        display_or_error VerilogPP.Typed.vmodule (typed_module_of_file filename);
        printf "\n-- canonical --\n";
        display_or_error VerilogPP.Typed.vmodule
          (canonical_module_of_file filename);
        printf "\n-- smt_netlist --\n";
        display_or_error SMTPP.StrSMT.smt_netlist (smt_netlist_of_file filename);
        printf "\n-- smt_formulas --\n";
        display_or_error
          (pp_print_list SMTPP.StrSMT.smt ~pp_sep:Util.newline_sep)
          (smt_formulas_of_file filename)
    | [ stage; _filename ] ->
        eprintf "Unknown stage: %s\n" stage;
        usage_and_exit ()
    | _ -> usage_and_exit ()
  in

  let compare = function
    | [ verafile_filename; filename1; filename2 ] -> (
        let in_matches_str, out_matches_str = read_verafile verafile_filename in
        let in_matches =
          List.map
            (fun (l, r) -> (Util.string_to_lst l, Util.string_to_lst r))
            in_matches_str
        in
        let out_matches =
          List.map
            (fun (l, r) -> (Util.string_to_lst l, Util.string_to_lst r))
            out_matches_str
        in

        let queryResult =
          Vera.equivalence_query in_matches out_matches
            (module_of_file filename1) (module_of_file filename2)
        in
        match queryResult with
        | Vera.Inl err -> printf "Error: %s\n" (Util.lst_to_string err)
        | Vera.Inr query -> (
            match SMTLIB.run_query_z3 query with
            | SMTLIB.UNSAT, out ->
                printf "Equivalent (UNSAT)\n";
                printf "%s\n" out
            | SMTLIB.SAT, out ->
                printf "Non-equivalent (SAT)\n";
                printf "%s\n" out
            | SMTLIB.Error, out ->
                printf "Error\n";
                printf "%s\n" out))
    | _ -> usage_and_exit ()
  in

  match Array.to_list Sys.argv with
  | _prog :: "parse_custom" :: rest -> MyVerilogParser.run_parser_command rest
  | _prog :: "compare" :: rest -> compare rest
  | _prog :: "lower" :: rest -> lower rest
  | _prog :: cmd :: _ ->
      eprintf "Unknown command: %s\n" cmd;
      usage_and_exit ()
  | _ -> usage_and_exit ()
