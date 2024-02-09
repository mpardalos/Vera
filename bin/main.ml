(* let lst_to_string (lst : char list) : string = *)
(*   List.fold_left (fun (s : string) (c : char) -> s ^ (String.make 1 c)) "" lst; *)
(* ;; *)

let usage_msg = "vvequiv <file.sv>"
let input_file = ref ""

let anon_fun arg =
  if !input_file == "" then input_file := arg
  else raise (Arg.Bad "Invalid positional args")

let read_command_output (cmd : string) : string =
  let chan = Unix.open_process_in cmd in
  In_channel.input_all chan

let () =
  Arg.parse [] anon_fun usage_msg;
  if !input_file == "" then raise (Arg.Bad "No input file");
  let ast_json_str =
    read_command_output
      (Printf.sprintf "slang --quiet --ast-json - %s" !input_file)
  in
  let ast_json = Yojson.Safe.from_string ast_json_str in
  Format.printf "%a\n" Yojson.Safe.pp ast_json
