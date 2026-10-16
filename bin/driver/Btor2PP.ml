open Format
module Zarith_Z = Z
open Vera

let bitvector fmt bits =
  List.iter (fun bit -> pp_print_char fmt (if bit then '1' else '0'))
    (List.rev bits)

(* State declarations precede operators, which retain their body order and must
   only refer to states or earlier operators. Updates follow all operators.
   Source names are relocated into a single fresh namespace
   shared by sorts, expressions and update lines. *)
let btor fmt model =
  let next_id = ref Zarith_Z.one in
  let sorts = Hashtbl.create 16 in
  let nodes = Hashtbl.create 16 in
  let lines = ref [] in
  let names = Hashtbl.create 16 in
  let name_line id n =
    let previous = Option.value (Hashtbl.find_opt names id) ~default:[] in
    Hashtbl.replace names id (n :: previous)
  in
  let emit line =
    let id = !next_id in
    next_id := Zarith_Z.succ id;
    lines := (id, line) :: !lines;
    id
  in
  let rec sort s =
    match Hashtbl.find_opt sorts s with
    | Some id -> id
    | None ->
        let id = 
              if Zarith_Z.sign s <= 0 then
                invalid_arg "Btor2PP: bitvector widths must be positive";
              emit (fun fmt -> fprintf fmt "sort bitvec %a" Zarith_Z.pp_print s)
        in
        Hashtbl.add sorts s id;
        id
  in
  let reference n =
    match Hashtbl.find_opt nodes n with
    | Some id -> id
    | None -> invalid_arg (asprintf "Btor2PP: undeclared or forward reference %S" n)
  in
  let check_name n =
    if Hashtbl.mem nodes n then
      invalid_arg (asprintf "Btor2PP: duplicate node %S" n)
  in
  (* Temporary flattening for printing. Move this into a verified Rocq pass
     when the BTOR lowering is implemented. Each occurrence is emitted anew. *)
  let rec emit_expr e =
    let line s body =
      let sid = sort s in
      emit (fun fmt -> body fmt sid)
    in
    let unary s op e =
      let e = emit_expr e in
      line s (fun fmt sid -> fprintf fmt "%s %a %a" op
        Zarith_Z.pp_print sid Zarith_Z.pp_print e)
    in
    let binary s op l r =
      let l = emit_expr l in
      let r = emit_expr r in
      line s (fun fmt sid -> fprintf fmt "%s %a %a %a" op
        Zarith_Z.pp_print sid Zarith_Z.pp_print l Zarith_Z.pp_print r)
    in
    let ternary s op a b c =
      let a = emit_expr a in
      let b = emit_expr b in
      let c = emit_expr c in
      line s (fun fmt sid -> fprintf fmt "%s %a %a %a %a" op
        Zarith_Z.pp_print sid Zarith_Z.pp_print a
        Zarith_Z.pp_print b Zarith_Z.pp_print c)
    in
    let bv n = n in
    let bool = bv Zarith_Z.one in
    match e with
    | ExprRef (_, n) -> reference n
    | Constant (n, bits) ->
        line (bv n) (fun fmt sid ->
          fprintf fmt "const %a %a" Zarith_Z.pp_print sid bitvector bits)
    | UnsignedExtend (n, w, e) | SignedExtend (n, w, e) as expr ->
        let op = match expr with UnsignedExtend _ -> "uext" | _ -> "sext" in
        let e = emit_expr e in
        line (bv (Zarith_Z.add n w)) (fun fmt sid ->
          fprintf fmt "%s %a %a %a" op Zarith_Z.pp_print sid
            Zarith_Z.pp_print e Zarith_Z.pp_print w)
    | Slice (_, hi, lo, e) ->
        let e = emit_expr e in
        line (bv (Zarith_Z.sub (Zarith_Z.succ hi) lo)) (fun fmt sid ->
          fprintf fmt "slice %a %a %a %a" Zarith_Z.pp_print sid
            Zarith_Z.pp_print e Zarith_Z.pp_print hi Zarith_Z.pp_print lo)
    | Not (n, r) -> unary (bv n) "not" r
    | Inc (n, r) -> unary (bv n) "inc" r
    | Dec (n, r) -> unary (bv n) "dec" r
    | RedAnd (_, r) -> unary bool "redand" r
    | RedOr (_, r) -> unary bool "redor" r
    | RedXor (_, r) -> unary bool "redxor" r
    | Iff (l, r) -> binary bool "iff" l r
    | Implies (l, r) -> binary bool "implies" l r
    | Eq0 (_, l, r) -> binary bool "eq" l r
    | NEq (_, l, r) -> binary bool "neq" l r
    | SignedGt (_, l, r) -> binary bool "sgt" l r
    | UnsignedGt (_, l, r) -> binary bool "ugt" l r
    | SignedGtE (_, l, r) -> binary bool "sgte" l r
    | UnsignedGtE (_, l, r) -> binary bool "ugte" l r
    | SignedLt (_, l, r) -> binary bool "slt" l r
    | UnsignedLt (_, l, r) -> binary bool "ult" l r
    | SignedLtE (_, l, r) -> binary bool "slte" l r
    | UnsignedLtE (_, l, r) -> binary bool "ulte" l r
    | And (n, l, r) -> binary (bv n) "and" l r
    | NAnd (n, l, r) -> binary (bv n) "nand" l r
    | Or (n, l, r) -> binary (bv n) "or" l r
    | NOr (n, l, r) -> binary (bv n) "nor" l r
    | XOr (n, l, r) -> binary (bv n) "xor" l r
    | XNor (n, l, r) -> binary (bv n) "xnor" l r
    | Rol (n, l, r) -> binary (bv n) "rol" l r
    | Sll (n, l, r) -> binary (bv n) "sll" l r
    | Sra (n, l, r) -> binary (bv n) "sra" l r
    | Srl (n, l, r) -> binary (bv n) "srl" l r
    | Add (n, l, r) -> binary (bv n) "add" l r
    | Mul (n, l, r) -> binary (bv n) "mul" l r
    | SignedDiv (n, l, r) -> binary (bv n) "sdiv" l r
    | UnsignedDiv (n, l, r) -> binary (bv n) "udiv" l r
    | SignedMod (n, l, r) -> binary (bv n) "smod" l r
    | SignedRem (n, l, r) -> binary (bv n) "srem" l r
    | UnsignedRem (n, l, r) -> binary (bv n) "urem" l r
    | Sub (n, l, r) -> binary (bv n) "sub" l r
    | SignedAddOverflow (_, l, r) -> binary bool "saddo" l r
    | UnsignedAddOverflow (_, l, r) -> binary bool "uaddo" l r
    | SignedDivOverflow (_, l, r) -> binary bool "sdivo" l r
    | SignedMulOverflow (_, l, r) -> binary bool "smulo" l r
    | UnsignedMulOverflow (_, l, r) -> binary bool "umulo" l r
    | SignedSubOverflow (_, l, r) -> binary bool "ssubo" l r
    | UnsignedSubOverflow (_, l, r) -> binary bool "usubo" l r
    | Concat (n, m, l, r) -> binary (bv (Zarith_Z.add n m)) "concat" l r
    (* | Read (_, elem, arr, idx) -> binary elem "read" arr idx *)
    | ITE (n, cond, ifT, ifF) -> ternary (bv n) "ite" cond ifT ifF
    (* | Write (idx_sort, elem, arr, idx, value) -> ternary (Coq_Sort.Array (idx_sort, elem)) "write" arr idx value *)
  in
  List.iter (function
    | StateDecl (n, s) ->
        let sid = sort s in
        check_name n;
        let id = emit (fun fmt -> fprintf fmt "state %a" Zarith_Z.pp_print sid) in
        name_line id n;
        Hashtbl.add nodes n id
    | _ -> ()) model.btorBody;
  List.iter (function
    | Operator (_, n, e) ->
        check_name n;
        let id = emit_expr e in
        name_line id n;
        Hashtbl.add nodes n id
    | _ -> ()) model.btorBody;
  let update op s n e =
    let sid = sort s in
    let target = reference n in
    let value = emit_expr e in
    let id = emit (fun fmt -> fprintf fmt "%s %a %a %a" op
      Zarith_Z.pp_print sid Zarith_Z.pp_print target Zarith_Z.pp_print value) in
    name_line id n
  in
  List.iter (function
    | StateInit (s, n, e) -> update "init" s n e
    | StateNext (s, n, e) -> update "next" s n e
    | Bad e ->
        let value = emit_expr e in
        ignore (emit (fun fmt -> fprintf fmt "bad %a" Zarith_Z.pp_print value))
    | _ -> ()) model.btorBody;
  (* References can give an existing line additional source names. *)
  List.iter (fun (id, line) ->
    fprintf fmt "%a %t" Zarith_Z.pp_print id line;
    (match Hashtbl.find_opt names id with
    | Some ns ->
        fprintf fmt " ; %s" (String.concat ", " (List.map String.escaped (List.rev ns)))
    | None -> ());
    pp_print_char fmt '\n') (List.rev !lines)
