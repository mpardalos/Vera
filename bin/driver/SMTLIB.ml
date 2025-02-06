open SMTPP
open Format

type sat_result = SAT | UNSAT | Error

let run_query_z3 q =
  let smt_channel = open_out "vera_query.smt" in
  let smt_fmt = Format.formatter_of_out_channel smt_channel in

  Format.fprintf smt_fmt "(set-info :smt-lib-version 2.6)\n";
  SMTLib.query smt_fmt q;
  Format.fprintf smt_fmt "(check-sat)\n";
  close_out smt_channel;

  let solver_out =
    Unix.open_process_in (Format.sprintf "z3 -model vera_query.smt")
  in
  match In_channel.input_line solver_out with
  | Some "sat" -> (SAT, In_channel.input_all solver_out)
  | Some "unsat" -> (UNSAT, In_channel.input_all solver_out)
  | Some line -> (Error, line ^ "\n" ^ In_channel.input_all solver_out)
  | None -> (Error, In_channel.input_all solver_out)
