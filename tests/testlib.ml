open Format
open Driver

let ( / ) = Fpath.( / )
let ( // ) = Fpath.( // )
let v = Fpath.v

let blif_to_verilog blif_path verilog_path =
  Lwt_process.shell
    (asprintf "yosys --commands 'read_blif %a; write_verilog %a'" Fpath.pp
       blif_path Fpath.pp verilog_path)
  |> Lwt_process.open_process_in
  |> fun p -> p#stdout |> Lwt_io.read

let get_verilog_inputs verilog_path =
  let open Lwt.Syntax in
  let* output =
    Lwt_process.shell
      (asprintf
         "slang -q --ast-json - '%a' | jq -r '.members[1].body.members[] | \
          select(.kind == \"Port\" and .direction == \"In\") | .name'"
         Fpath.pp verilog_path)
    |> Lwt_process.open_process_in
    |> fun p -> p#stdout |> Lwt_io.read
  in
  output |> String.trim |> String.split_on_char '\n' |> Lwt.return

let get_verilog_outputs verilog_path =
  let open Lwt.Syntax in
  let* output =
    Lwt_process.shell
      (asprintf
         "slang -q --ast-json - '%a' | jq -r '.members[1].body.members[] | \
          select(.kind == \"Port\" and .direction == \"Out\") | .name'"
         Fpath.pp verilog_path)
    |> Lwt_process.open_process_in
    |> fun p -> p#stdout |> Lwt_io.read
  in
  output |> String.trim |> String.split_on_char '\n' |> Lwt.return

let setup () =
  let project_root =
    Unix.open_process_in "git rev-parse --show-toplevel"
    |> In_channel.input_line
    |> function
    | Some l -> v l
    | None -> raise (Failure "git rev-parse failed")
  in
  Sys.chdir (Fpath.to_string (project_root / "tests"));
  printf "Project root: %a\n" Fpath.pp project_root;
  printf "Running in:   %s\n%!" (Sys.getcwd ())

let mkdir_p path permissions =
  if not (Sys.file_exists path) then Sys.mkdir path permissions

let test_verilog_blif (name : string) verilog_path blif_path : unit Lwt.t =
  let open Lwt.Syntax in
  let out_path = v "results" / name in
  mkdir_p "results" 0o755;
  mkdir_p (Fpath.to_string out_path) 0o755;

  let verilog_path = v "testfiles" // v verilog_path in
  let blif_path = v "testfiles" // v blif_path in

  let blif_as_verilog_path =
    Fpath.add_ext ".v" (out_path / Fpath.basename blif_path)
  in

  let* _ =
    Lwt_unix.system
      (asprintf "cp %a %a" Fpath.pp verilog_path Fpath.pp out_path)
  in

  let _ = blif_to_verilog blif_path blif_as_verilog_path in

  let* verilog_inputs =
    get_verilog_inputs verilog_path
    |> Lwt.map (List.sort compare)
    |> Lwt.map (List.map Util.string_to_lst)
  in
  let* verilog_outputs =
    get_verilog_outputs verilog_path
    |> Lwt.map (List.sort compare)
    |> Lwt.map (List.map Util.string_to_lst)
  in
  let* blif_inputs =
    get_verilog_inputs blif_as_verilog_path
    |> Lwt.map (List.sort compare)
    |> Lwt.map (List.map Util.string_to_lst)
  in
  let* blif_outputs =
    get_verilog_outputs blif_as_verilog_path
    |> Lwt.map (List.sort compare)
    |> Lwt.map (List.map Util.string_to_lst)
  in

  let in_matches = List.combine verilog_inputs blif_inputs in
  let out_matches = List.combine verilog_outputs blif_outputs in

  let queryResult =
    Vera.equivalence_query in_matches out_matches
      (ParseSlang.parse_verilog_file (Fpath.to_string verilog_path))
      (ParseSlang.parse_verilog_file (Fpath.to_string blif_as_verilog_path))
  in

  let smt_solver_out =
    Out_channel.open_text (Fpath.to_string (out_path / "smt_out"))
  in

  match queryResult with
  | Vera.Inl err ->
      raise (Failure (asprintf "Error: %s\n" (Util.lst_to_string err)))
  | Vera.Inr query -> (
      let cwd_before = Sys.getcwd () in
      Sys.chdir (Fpath.to_string out_path);
      let* result, full_output = SMTLIB.run_query_z3_lwt query in
      Sys.chdir cwd_before;
      match result with
      | SMTLIB.UNSAT ->
          printf "UNSAT";
          Out_channel.output_string smt_solver_out full_output;
          Lwt.return ()
      | SMTLIB.SAT ->
          printf "SAT";
          Out_channel.output_string smt_solver_out full_output;
          raise (Failure "Failed (Non-equivalent)")
      | SMTLIB.Error ->
          printf "Error";
          Out_channel.output_string smt_solver_out full_output;
          raise (Failure "SMT Solver error"))
