open Vera.Concrete
module Parser = Driver.ParseBtor2
let z = Z.of_int

let () =
  (* Every concrete constructor must survive printing and parsing unchanged. *)
  let l = z 19 and r = z 23 in
  let operations = [
    UnsignedExtend (Z.zero, l); SignedExtend (z 4, l); Slice (z 7, Z.zero, l);
    Not l;
    Inc l;
    Dec l;
    RedAnd l;
    RedOr l;
    RedXor l;
    Iff (l, r);
    Implies (l, r);
    Eq (l, r);
    NEq (l, r);
    SignedGt (l, r);
    UnsignedGt (l, r);
    SignedGtE (l, r);
    UnsignedGtE (l, r);
    SignedLt (l, r);
    UnsignedLt (l, r);
    SignedLtE (l, r);
    UnsignedLtE (l, r);
    And (l, r);
    NAnd (l, r);
    Or (l, r);
    NOr (l, r);
    XOr (l, r);
    XNor (l, r);
    Rol (l, r);
    Sll (l, r);
    Sra (l, r);
    Srl (l, r);
    Add (l, r);
    Mul (l, r);
    SignedDiv (l, r);
    UnsignedDiv (l, r);
    SignedMod (l, r);
    SignedRem (l, r);
    UnsignedRem (l, r);
    Sub (l, r);
    SignedAddOverflow (l, r);
    UnsignedAddOverflow (l, r);
    SignedDivOverflow (l, r);
    SignedMulOverflow (l, r);
    UnsignedMulOverflow (l, r);
    SignedSubOverflow (l, r);
    UnsignedSubOverflow (l, r);
    Concat (l, r);
    ITE (z 5, l, r)
  ] in
  let nodes = [SortDecl (z 7, z 8)] @
    List.mapi (fun i op -> Operation (z (100 + i), z 7, op)) operations @
    [StateInit (z 200, z 7, l, r); StateNext (z 201, z 7, l, r);
     Bad (z 202, l); Constraint (z 203, l); Fair (z 204, l);
     Output (z 205, l); Justice (z 206, z 2)] in
  let printed = Format.asprintf "%a" Driver.Btor2PP.btor nodes in
  assert (Parser.parse_string printed = nodes);

  (* Whitespace, comments, supplied IDs, and operand order. *)
  let input = "; comment\r\n\n 42 add\t7 19 23 ; sum\r\n\
    51 slice 3 42 7 0\n52 uext 9 42 0\n53 sext 9 42 4\n\
    54 ite 7 6 19 23\n7 sort bitvec 8" in
  assert (Parser.parse_string input =
    [Operation (z 42, z 7, Add (l, r));
     Operation (z 51, z 3, Slice (z 7, Z.zero, z 42));
     Operation (z 52, z 9, UnsignedExtend (Z.zero, z 42));
     Operation (z 53, z 9, SignedExtend (z 4, z 42));
     Operation (z 54, z 7, ITE (z 6, l, r)); SortDecl (z 7, z 8)]);
  assert (Parser.parse_string " ; empty\n\t\r\n" = []);
  let huge = "123456789012345678901234567890" in
  assert (Parser.parse_string (huge ^ " bad 19") = [Bad (Z.of_string huge, l)]);

  List.iter (fun invalid ->
    match Parser.parse_string ("; first line\n\n" ^ invalid) with
    | _ -> failwith ("Accepted malformed input: " ^ invalid)
    | exception Parser.Parse_error (line, message) ->
        assert (line = 3); assert (message <> ""))
    ["0 bad 1"; "1 bad 0"; "-1 bad 2"; "1 bad -2";
     "1 add 0 2 3"; "1 sort bitvec 0"; "1 sort array 2 3";
     "1 bad 0x10"; "1 bad +2"; "1 bad 2_000";
     "1 uext 2 3 -1"; "1 slice 2 3 -1 0";
     "1 add 2 3"; "1 add 2 3 4 5"; "1 ite 2 3 4";
     "1 mystery 2 3"; "1 bad"; "1"; "1 justice 0"];

  let filename = Filename.temp_file "vera-btor-parser" ".btor2" in
  Fun.protect ~finally:(fun () -> Sys.remove filename) (fun () ->
    let channel = open_out filename in
    Fun.protect ~finally:(fun () -> close_out channel)
      (fun () -> output_string channel printed);
    assert (Parser.parse_file filename = nodes))
