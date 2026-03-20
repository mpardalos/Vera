open SMTPP

type sat_result = SAT | UNSAT | Error

let def_read_output out =
  match String.split_on_char '\n' out with
  | "sat" :: _ -> SAT
  | "unsat" :: _ -> UNSAT
  | _ -> Error

let run_solver (run_cmd : string) ?(read_output = def_read_output) q =
  let (solver_out, solver_in) = Unix.open_process run_cmd in
  let smt_fmt = Format.formatter_of_out_channel solver_in in
  SMTLib.query smt_fmt q;
  close_out solver_in;
  let full_output = In_channel.input_all solver_out in
  let _ = Unix.close_process (solver_out, solver_in) in
  (read_output full_output, full_output)

let run_query_z3 = run_solver "z3 -model -in"
let run_query_cvc5 = run_solver "cvc5 --dump-models"
let run_query_bitwuzla = run_solver "bitwuzla --produce-models --print-model"
let run_query_dummy = run_solver "cat >/dev/null"
