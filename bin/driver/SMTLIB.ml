open SMTPP
open Format

type sat_result = SAT | UNSAT | Error

let run_query_z3 q =
  let smt_channel = open_out "vera_query.smt" in
  let smt_fmt = Format.formatter_of_out_channel smt_channel in

  Format.fprintf smt_fmt "(set-info :smt-lib-version 2.6)\n";
  List.iter (fun expr -> Format.fprintf smt_fmt "%a\n" SMTPP.StrSMT.smt expr) q;
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

let run_query_z3_lwt q =
  let open Lwt.Syntax in
  let smt_channel = open_out "vera_query.smt" in
  let smt_fmt = Format.formatter_of_out_channel smt_channel in

  Format.fprintf smt_fmt "(set-info :smt-lib-version 2.6)\n";
  List.iter (fun expr -> Format.fprintf smt_fmt "%a\n" SMTPP.StrSMT.smt expr) q;
  Format.fprintf smt_fmt "(check-sat)\n";
  close_out smt_channel;

  let solver_out =
    (Lwt_process.open_process_in ("z3", [| "-model"; "vera_query.smt" |]))
      #stdout
  in
  let* sat_line = Lwt_io.read_line solver_out in
  let* rest = Lwt_io.read solver_out in
  Lwt.return
    ( (match sat_line with "sat" -> SAT | "unsat" -> UNSAT | _ -> Error),
      sat_line ^ "\n" ^ rest )
