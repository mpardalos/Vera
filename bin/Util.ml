let lst_to_string lst = String.of_seq (List.to_seq lst)
let string_to_lst s = List.of_seq (String.to_seq s)

let colon_sep fmt () = Format.fprintf fmt ";@ "
let comma_sep fmt () = Format.fprintf fmt ";@ "
let newline_sep fmt () = Format.fprintf fmt "@."
