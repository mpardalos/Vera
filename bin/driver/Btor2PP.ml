open Format
module Zarith_Z = Z
open Vera

let bitvector fmt bits =
  List.iter (fun bit -> pp_print_char fmt (if bit then '1' else '0'))
    (List.rev bits)

(* [sid] is the result sort's line ID; [reference] prints a relocated node ID. *)
let expression sid reference fmt e =
  let unary op r = fprintf fmt "%s %a %a" op Zarith_Z.pp_print sid reference r in
  let binary op l r =
    fprintf fmt "%s %a %a %a" op Zarith_Z.pp_print sid reference l reference r
  in
  let ternary op a b c =
    fprintf fmt "%s %a %a %a %a" op Zarith_Z.pp_print sid
      reference a reference b reference c
  in
  match e with
  | UnsignedExtend (_, w, r) ->
      unary "uext" r; fprintf fmt " %a" Zarith_Z.pp_print w
  | SignedExtend (_, w, r) ->
      unary "sext" r; fprintf fmt " %a" Zarith_Z.pp_print w
  | Not (_, r) -> unary "not" r
  | Inc (_, r) -> unary "inc" r
  | Dec (_, r) -> unary "dec" r
  | RedAnd (_, r) -> unary "redand" r
  | RedOr (_, r) -> unary "redor" r
  | RedXor (_, r) -> unary "redxor" r
  | Iff (l, r) -> binary "iff" l r
  | Implies (l, r) -> binary "implies" l r
  | Eq0 (_, l, r) -> binary "eq" l r
  | NEq (_, l, r) -> binary "neq" l r
  | SignedGt (_, l, r) -> binary "sgt" l r
  | UnsignedGt (_, l, r) -> binary "ugt" l r
  | SignedGtE (_, l, r) -> binary "sgte" l r
  | UnsignedGtE (_, l, r) -> binary "ugte" l r
  | SignedLt (_, l, r) -> binary "slt" l r
  | UnsignedLt (_, l, r) -> binary "ult" l r
  | SignedLtE (_, l, r) -> binary "slte" l r
  | UnsignedLtE (_, l, r) -> binary "ulte" l r
  | And (_, l, r) -> binary "and" l r
  | NAnd (_, l, r) -> binary "nand" l r
  | Or (_, l, r) -> binary "or" l r
  | NOr (_, l, r) -> binary "nor" l r
  | XOr (_, l, r) -> binary "xor" l r
  | XNor (_, l, r) -> binary "xnor" l r
  | Rol (_, l, r) -> binary "rol" l r
  | Sll (_, l, r) -> binary "sll" l r
  | Sra (_, l, r) -> binary "sra" l r
  | Srl (_, l, r) -> binary "srl" l r
  | Add (_, l, r) -> binary "add" l r
  | Mul (_, l, r) -> binary "mul" l r
  | SignedDiv (_, l, r) -> binary "sdiv" l r
  | UnsignedDiv (_, l, r) -> binary "udiv" l r
  | SignedMod (_, l, r) -> binary "smod" l r
  | SignedRem (_, l, r) -> binary "srem" l r
  | UnsignedRem (_, l, r) -> binary "urem" l r
  | Sub (_, l, r) -> binary "sub" l r
  | SignedAddOverflow (_, l, r) -> binary "saddo" l r
  | UnsignedAddOverflow (_, l, r) -> binary "uaddo" l r
  | SignedDivOverflow (_, l, r) -> binary "sdivo" l r
  | SignedMulOverflow (_, l, r) -> binary "smulo" l r
  | UnsignedMulOverflow (_, l, r) -> binary "umulo" l r
  | SignedSubOverflow (_, l, r) -> binary "ssubo" l r
  | UnsignedSubOverflow (_, l, r) -> binary "usubo" l r
  | Concat (_, _, l, r) -> binary "concat" l r
  | Read (_, _, arr, idx) -> binary "read" arr idx
  | ITE (_, cond, ifT, ifF) -> ternary "ite" cond ifT ifF
  | Write (_, _, arr, idx, elem) -> ternary "write" arr idx elem
  | Constant (_, bits) ->
      fprintf fmt "const %a %a" Zarith_Z.pp_print sid bitvector bits

(* State declarations precede operators, which retain their body order and must
   only refer to states or earlier operators. Updates follow all operators.
   Source node IDs (including zero) are relocated into a single fresh namespace
   shared by sorts, expressions and update lines. *)
let btor fmt model =
  let next_id = ref Zarith_Z.one in
  let sorts = Hashtbl.create 16 in
  let nodes = Hashtbl.create 16 in
  let emit line =
    let id = !next_id in
    next_id := Zarith_Z.succ id;
    fprintf fmt "%a %t\n" Zarith_Z.pp_print id line;
    id
  in
  let rec sort s =
    match Hashtbl.find_opt sorts s with
    | Some id -> id
    | None ->
        let id = match s with
          | Coq_Sort.BitVec n ->
              if Zarith_Z.sign n <= 0 then
                invalid_arg "Btor2PP: bitvector widths must be positive";
              emit (fun fmt -> fprintf fmt "sort bitvec %a" Zarith_Z.pp_print n)
          | Coq_Sort.Array (idx, elem) ->
              let idx = sort idx in
              let elem = sort elem in
              emit (fun fmt -> fprintf fmt "sort array %a %a"
                Zarith_Z.pp_print idx Zarith_Z.pp_print elem)
        in
        Hashtbl.add sorts s id;
        id
  in
  let reference fmt n =
    match Hashtbl.find_opt nodes n with
    | Some id -> Zarith_Z.pp_print fmt id
    | None -> invalid_arg (asprintf "Btor2PP: undeclared or forward reference %a"
        Zarith_Z.pp_print n)
  in
  let declare n line =
    if Hashtbl.mem nodes n then
      invalid_arg (asprintf "Btor2PP: duplicate node %a" Zarith_Z.pp_print n);
    let id = emit line in
    Hashtbl.add nodes n id
  in
  List.iter (function
    | StateDecl (n, s) ->
        let sid = sort s in
        declare n (fun fmt -> fprintf fmt "state %a" Zarith_Z.pp_print sid)
    | _ -> ()) model.btorBody;
  List.iter (function
    | Operator (s, n, e) ->
        let sid = sort s in
        declare n (fun fmt -> expression sid reference fmt e)
    | _ -> ()) model.btorBody;
  let update op s n e =
    let sid = sort s in
    let value = emit (fun fmt -> expression sid reference fmt e) in
    ignore (emit (fun fmt -> fprintf fmt "%s %a %a %a" op
      Zarith_Z.pp_print sid reference n Zarith_Z.pp_print value))
  in
  List.iter (function
    | StateInit (s, n, e) -> update "init" s n e
    | StateNext (s, n, e) -> update "next" s n e
    | _ -> ()) model.btorBody
