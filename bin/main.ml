let lst_to_string (lst : char list) : string =
  List.fold_left (fun (s : string) (c : char) -> s ^ (String.make 1 c)) "" lst
;;

print_endline (lst_to_string VVEquiv.program_name)
