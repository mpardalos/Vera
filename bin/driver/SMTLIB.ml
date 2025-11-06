open SMTPP

type sat_result = SAT | UNSAT | Error

let def_read_output out =
  match String.split_on_char '\n' out with
  | "sat" :: _ -> SAT
  | "unsat" :: _ -> UNSAT
  | _ -> Error

let run_solver (run_cmd : string -> string) ?(read_output = def_read_output) q =
  let smt_channel = open_out "vera_query.smt" in
  let smt_fmt = Format.formatter_of_out_channel smt_channel in

  Format.fprintf smt_fmt "(set-info :smt-lib-version 2.6)\n";
  Format.fprintf smt_fmt "(set-logic QF_BV)\n";
  SMTLib.query smt_fmt q;
  Format.fprintf smt_fmt "(check-sat)\n";
  close_out smt_channel;

  let solver_out = Unix.open_process_in (run_cmd "vera_query.smt") in
  let full_output = In_channel.input_all solver_out in
  (read_output full_output, full_output)

let run_query_z3 = run_solver (Format.sprintf "z3 -model %s")
let run_query_cvc5 = run_solver (Format.sprintf "cvc5 --dump-models %s")
let run_query_bitwuzla = run_solver (Format.sprintf "bitwuzla --produce-models --print-model %s")
