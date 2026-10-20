module Zarith_Z = Z
open Vera.Btor2.Raw
module Z = Zarith_Z
module Parser = Driver.ParseBtor2
let z = Z.of_int
let reference id = ExprRef ("i" ^ string_of_int id)

let () =
  let model = Parser.parse_string
    "; a model\r\n1 sort bitvec 8\n2 sort bitvec 1\n\n     3 consth 1 53 value\n4 state 1 state_name\n5 init 1 4 3\n     6 input 1 input_name\n7 add 1 4 6\n8 next 1 4 7\n     9 eq 2 7 3\n10 bad 9 ; property\n" in
  let bits = [true; true; false; false; true; false; true; false] in
  assert (model =
    [Operator (z 8, "i3", Constant bits); StateDecl ("i4", z 8);
     StateInit (z 8, "i4", reference 3); StateDecl ("i6", z 8);
     Operator (z 8, "i7", Add (reference 4, reference 6));
     StateNext (z 8, "i4", reference 7);
     Operator (z 1, "i9", Eq (reference 7, reference 3));
     Bad (reference 9)]);
  let printed = Format.asprintf "%a" Driver.Btor2PP.btor model in
  let reparsed = Parser.parse_string printed in
  let printed_again = Format.asprintf "%a" Driver.Btor2PP.btor reparsed in
  assert ((Parser.parse_string printed_again) = reparsed);
  let filename = Filename.temp_file "vera-btor-parser" ".btor2" in
  Fun.protect ~finally:(fun () -> Sys.remove filename) (fun () ->
    let channel = open_out filename in
    Fun.protect ~finally:(fun () -> close_out channel) (fun () -> output_string channel printed);
    assert ((Parser.parse_file filename) = reparsed));
  assert ((Parser.parse_string " ; empty\n\t\r\n") = []);
  let huge = "123456789012345678901234567890" in
  assert ((Parser.parse_string ("1 sort bitvec 1\n" ^ huge ^ " input 1")) =
    [StateDecl ("i" ^ huge, z 1)])

let () =
  let prefix = "1 sort bitvec 8\n2 sort bitvec 1\n3 sort bitvec 4\n    4 sort bitvec 16\n5 sort bitvec 9\n10 input 1\n11 input 1\n    12 input 2\n13 input 2\n14 input 3\n" in
  let l = reference 10 and r = reference 11 in
  let a = reference 12 and b = reference 13 in
  let cases = [
    "not 1 10", 8, Not l;
    "inc 1 10", 8, Inc l;
    "dec 1 10", 8, Dec l;
    "redand 2 10", 1, RedAnd l;
    "redor 2 10", 1, RedOr l;
    "redxor 2 10", 1, RedXor l;
    "iff 2 12 13", 1, Iff (a, b);
    "implies 2 12 13", 1, Implies (a, b);
    "eq 2 10 11", 1, Eq (l, r);
    "neq 2 10 11", 1, NEq (l, r);
    "sgt 2 10 11", 1, SignedGt (l, r);
    "ugt 2 10 11", 1, UnsignedGt (l, r);
    "sgte 2 10 11", 1, SignedGtE (l, r);
    "ugte 2 10 11", 1, UnsignedGtE (l, r);
    "slt 2 10 11", 1, SignedLt (l, r);
    "ult 2 10 11", 1, UnsignedLt (l, r);
    "slte 2 10 11", 1, SignedLtE (l, r);
    "ulte 2 10 11", 1, UnsignedLtE (l, r);
    "and 1 10 11", 8, And (l, r);
    "nand 1 10 11", 8, NAnd (l, r);
    "or 1 10 11", 8, Or (l, r);
    "nor 1 10 11", 8, NOr (l, r);
    "xor 1 10 11", 8, XOr (l, r);
    "xnor 1 10 11", 8, XNor (l, r);
    "rol 1 10 11", 8, Rol (l, r);
    "sll 1 10 11", 8, Sll (l, r);
    "sra 1 10 11", 8, Sra (l, r);
    "srl 1 10 11", 8, Srl (l, r);
    "add 1 10 11", 8, Add (l, r);
    "mul 1 10 11", 8, Mul (l, r);
    "sdiv 1 10 11", 8, SignedDiv (l, r);
    "udiv 1 10 11", 8, UnsignedDiv (l, r);
    "smod 1 10 11", 8, SignedMod (l, r);
    "srem 1 10 11", 8, SignedRem (l, r);
    "urem 1 10 11", 8, UnsignedRem (l, r);
    "sub 1 10 11", 8, Sub (l, r);
    "saddo 2 10 11", 1, SignedAddOverflow (l, r);
    "uaddo 2 10 11", 1, UnsignedAddOverflow (l, r);
    "sdivo 2 10 11", 1, SignedDivOverflow (l, r);
    "smulo 2 10 11", 1, SignedMulOverflow (l, r);
    "umulo 2 10 11", 1, UnsignedMulOverflow (l, r);
    "ssubo 2 10 11", 1, SignedSubOverflow (l, r);
    "usubo 2 10 11", 1, UnsignedSubOverflow (l, r);
    "uext 5 10 1", 9, UnsignedExtend (z 1, l);
    "sext 1 10 0", 8, l;
    "slice 3 10 6 3", 4, Slice (z 6, z 3, l);
    "concat 4 10 11", 16, Concat (l, r);
    "ite 1 12 10 11", 8, ITE (a, l, r)
  ] in
  List.iter (fun (text, width, expected) ->
    let model = Parser.parse_string (prefix ^ "20 " ^ text) in
    assert (List.hd (List.rev model) = Operator (z width, "i20", expected));
    let printed = Format.asprintf "%a" Driver.Btor2PP.btor model in
    let reparsed = Parser.parse_string printed in
    assert (Parser.parse_string (Format.asprintf "%a" Driver.Btor2PP.btor reparsed) = reparsed)) cases

let () =
  let cases = [
    "const 1 01010011", 83; "constd 1 83", 83; "consth 1 053", 83;
    "consth 1 aF", 175; "constd 1 -1", 255; "constd 1 -128", 128;
    "constd 1 255", 255; "zero 1", 0; "one 1", 1; "ones 1", 255
  ] in
  List.iter (fun (text, number) ->
    let model = Parser.parse_string ("1 sort bitvec 8\n2 " ^ text) in
    let bits = List.init 8 (Z.testbit (z number)) in
    assert (model = [Operator (z 8, "i2", Constant bits)])) cases

let () =
  let prefix = "1 sort bitvec 8\n2 sort bitvec 1\n3 input 1\n4 state 1\n    5 zero 1\n6 input 2\n" in
  let invalid = [
    "0 bad 6"; "6 bad 6"; "2 bad 6"; "-1 bad 6";
    "7 bad 0"; "7 bad -6"; "7 bad 8"; "7 bad 1"; "7 bad 3";
    "7 add 99 3 5"; "7 add 3 3 5"; "7 add 2 3 5";
    "7 add 1 3 6"; "7 add 1 3"; "7 add 1 3 5 a b";
    "7 redand 1 3"; "7 iff 2 3 5"; "7 eq 1 3 5";
    "7 slice 1 3 8 1"; "7 slice 1 3 2 3"; "7 slice 1 3 3 0";
    "7 uext 1 3 1"; "7 uext 1 3 -1"; "7 concat 1 3 5";
    "7 ite 1 3 3 5"; "7 ite 1 6 3 6";
    "7 init 1 3 5"; "7 next 1 5 3"; "7 next 2 4 6"; "7 next 1 4 6";
    "7 sort bitvec 0"; "7 sort array 1 1"; "7 input 0";
    "7 const 1 001"; "7 const 1 0000000x"; "7 constd 1 256";
    "7 constd 1 -129"; "7 constd 1 +1"; "7 constd 1 -";
    "7 consth 1 100"; "7 consth 1 0xF"; "7 const 1";
    "7 constraint 6"; "7 fair 6"; "7 justice 1 6"; "7 output 3";
    "7 mystery 1 3"; "7"; "7 bad 0x6"
  ] in
  List.iter (fun text ->
    match Parser.parse_string (prefix ^ text) with
    | _ -> failwith ("Accepted malformed input: " ^ text)
    | exception Parser.Parse_error (line, message) ->
        assert (line = 7); assert (message <> "")) invalid;
  (* Statement IDs cannot be used as expressions or reused. *)
  List.iter (fun tail ->
    match Parser.parse_string (prefix ^ "7 bad 6\n" ^ tail) with
    | _ -> failwith ("Accepted malformed input: " ^ tail)
    | exception Parser.Parse_error (line, _) -> assert (line = 8))
    ["8 not 2 7"; "7 bad 6"]

let () =
  let raw = Parser.parse_string
    "1 sort bitvec 1\n2 zero 1\n3 state 1\n4 init 1 3 2\n\
     5 not 1 3\n6 next 1 3 5\n7 bad 5\n" in
  let abstract : Vera.Btor2.Abstract.btor =
    match Vera.Btor2.Raw.to_abstract raw with
    | Vera.Inr model -> model
    | Vera.Inl error -> failwith error
  in
  assert (Vera.Btor2.Raw.of_abstract abstract = raw);
  List.iter (fun malformed ->
    match Vera.Btor2.Raw.to_abstract malformed with
    | Vera.Inl _ -> ()
    | Vera.Inr _ -> failwith "Rocq accepted an invalid raw AST")
    [[Operator (z 1, "empty", Constant [])];
     [Bad (ExprRef "missing")];
     [Operator (z 1, "mismatch", Add (Constant [false], Constant [false; true]))]];
  let nested =
    [StateDecl ("s", z 4);
     StateInit (z 4, "s", Constant [false; false; false; false]);
     StateNext (z 4, "s", Add (ExprRef "s", Constant [true; false; false; false]));
     Bad (RedOr (Not (ExprRef "s")))] in
  let parsed = Parser.parse_string (Format.asprintf "%a" Driver.Btor2PP.btor nested) in
  match Vera.Btor2.Raw.to_abstract parsed with
  | Vera.Inr _ -> ()
  | Vera.Inl error -> failwith error
