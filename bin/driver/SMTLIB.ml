open SMTPP

let run_solver (run_cmd : string) q =
  let solver_out, solver_in = Unix.open_process run_cmd in
  let smt_fmt = Format.formatter_of_out_channel solver_in in
  SMTLib.query smt_fmt q;
  close_out solver_in;
  let full_output = In_channel.input_all solver_out in
  let _ = Unix.close_process (solver_out, solver_in) in
  match String.split_on_char '\n' full_output with
  | "sat" :: _ -> "Non-equivalent"
  | "unsat" :: _ -> "Equivalent"
  | _ -> "Error"

let run_query_z3 = run_solver "z3 -model -in"
let run_query_cvc5 = run_solver "cvc5 --dump-models"
let run_query_bitwuzla = run_solver "bitwuzla --produce-models --print-model"
let run_query_dummy = fun s : string -> "I'm a dummy"
