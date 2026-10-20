open Format
module Z = Z
open Vera.Btor2.Raw

let bitvector fmt bits =
  List.iter (fun bit -> pp_print_char fmt (if bit then '1' else '0')) (List.rev bits)

(* Flatten expressions left-to-right without CSE. Sorts and nodes share IDs. *)
let btor fmt (model : btor) =
  let next_id = ref Z.one in
  let sorts = Hashtbl.create 16 in
  let names = Hashtbl.create 16 in
  let lines = ref [] in
  let emit line =
    let id = !next_id in
    next_id := Z.succ id;
    lines := (id, line) :: !lines;
    id
  in
  let sort width =
    if Z.sign width <= 0 then invalid_arg "Btor2PP: bitvector widths must be positive";
    match Hashtbl.find_opt sorts width with
    | Some id -> id
    | None ->
        let id = emit (fun fmt -> fprintf fmt "sort bitvec %a" Z.pp_print width) in
        Hashtbl.add sorts width id;
        id
  in
  let check_width expected actual =
    if not (Z.equal expected actual) then invalid_arg "Btor2PP: incompatible operand sorts"
  in
  let reference name =
    match Hashtbl.find_opt names name with
    | Some value -> value
    | None -> invalid_arg (asprintf "Btor2PP: undeclared or forward reference %S" name)
  in
  let add_name name value =
    if Hashtbl.mem names name then invalid_arg (asprintf "Btor2PP: duplicate name %S" name);
    Hashtbl.add names name value
  in
  let rec expr e =
    let line width body =
      let sid = sort width in
      width, emit (fun fmt -> body fmt sid)
    in
    let unary boolean opcode e =
      let width, id = expr e in
      line (if boolean then Z.one else width) (fun fmt sid ->
        fprintf fmt "%s %a %a" opcode Z.pp_print sid Z.pp_print id)
    in
    let binary boolean opcode lhs rhs =
      let lw, lhs = expr lhs in
      let rw, rhs = expr rhs in
      check_width lw rw;
      if opcode = "iff" || opcode = "implies" then check_width Z.one lw;
      line (if boolean then Z.one else lw) (fun fmt sid ->
        fprintf fmt "%s %a %a %a" opcode Z.pp_print sid Z.pp_print lhs Z.pp_print rhs)
    in
    match e with
    | ExprRef name -> let width, id, _ = reference name in width, id
    | Constant bits ->
        line (Z.of_int (List.length bits)) (fun fmt sid ->
          fprintf fmt "const %a %a" Z.pp_print sid bitvector bits)
    | UnsignedExtend (amount, e) | SignedExtend (amount, e) as whole ->
        if Z.sign amount <= 0 then invalid_arg "Btor2PP: extension amount must be positive";
        let width, id = expr e in
        let opcode = match whole with UnsignedExtend _ -> "uext" | _ -> "sext" in
        line (Z.add width amount) (fun fmt sid ->
          fprintf fmt "%s %a %a %a" opcode Z.pp_print sid Z.pp_print id Z.pp_print amount)
    | Slice (hi, lo, e) ->
        let width, id = expr e in
        if Z.sign lo < 0 || Z.lt hi lo || Z.geq hi width then
          invalid_arg "Btor2PP: invalid slice bounds";
        line (Z.succ (Z.sub hi lo)) (fun fmt sid ->
          fprintf fmt "slice %a %a %a %a" Z.pp_print sid Z.pp_print id Z.pp_print hi Z.pp_print lo)
    | Not e -> unary false "not" e
    | Inc e -> unary false "inc" e
    | Dec e -> unary false "dec" e
    | RedAnd e -> unary true "redand" e
    | RedOr e -> unary true "redor" e
    | RedXor e -> unary true "redxor" e
    | Iff (lhs, rhs) -> binary true "iff" lhs rhs
    | Implies (lhs, rhs) -> binary true "implies" lhs rhs
    | Eq (lhs, rhs) -> binary true "eq" lhs rhs
    | NEq (lhs, rhs) -> binary true "neq" lhs rhs
    | SignedGt (lhs, rhs) -> binary true "sgt" lhs rhs
    | UnsignedGt (lhs, rhs) -> binary true "ugt" lhs rhs
    | SignedGtE (lhs, rhs) -> binary true "sgte" lhs rhs
    | UnsignedGtE (lhs, rhs) -> binary true "ugte" lhs rhs
    | SignedLt (lhs, rhs) -> binary true "slt" lhs rhs
    | UnsignedLt (lhs, rhs) -> binary true "ult" lhs rhs
    | SignedLtE (lhs, rhs) -> binary true "slte" lhs rhs
    | UnsignedLtE (lhs, rhs) -> binary true "ulte" lhs rhs
    | And (lhs, rhs) -> binary false "and" lhs rhs
    | NAnd (lhs, rhs) -> binary false "nand" lhs rhs
    | Or (lhs, rhs) -> binary false "or" lhs rhs
    | NOr (lhs, rhs) -> binary false "nor" lhs rhs
    | XOr (lhs, rhs) -> binary false "xor" lhs rhs
    | XNor (lhs, rhs) -> binary false "xnor" lhs rhs
    | Rol (lhs, rhs) -> binary false "rol" lhs rhs
    | Sll (lhs, rhs) -> binary false "sll" lhs rhs
    | Sra (lhs, rhs) -> binary false "sra" lhs rhs
    | Srl (lhs, rhs) -> binary false "srl" lhs rhs
    | Add (lhs, rhs) -> binary false "add" lhs rhs
    | Mul (lhs, rhs) -> binary false "mul" lhs rhs
    | SignedDiv (lhs, rhs) -> binary false "sdiv" lhs rhs
    | UnsignedDiv (lhs, rhs) -> binary false "udiv" lhs rhs
    | SignedMod (lhs, rhs) -> binary false "smod" lhs rhs
    | SignedRem (lhs, rhs) -> binary false "srem" lhs rhs
    | UnsignedRem (lhs, rhs) -> binary false "urem" lhs rhs
    | Sub (lhs, rhs) -> binary false "sub" lhs rhs
    | SignedAddOverflow (lhs, rhs) -> binary true "saddo" lhs rhs
    | UnsignedAddOverflow (lhs, rhs) -> binary true "uaddo" lhs rhs
    | SignedDivOverflow (lhs, rhs) -> binary true "sdivo" lhs rhs
    | SignedMulOverflow (lhs, rhs) -> binary true "smulo" lhs rhs
    | UnsignedMulOverflow (lhs, rhs) -> binary true "umulo" lhs rhs
    | SignedSubOverflow (lhs, rhs) -> binary true "ssubo" lhs rhs
    | UnsignedSubOverflow (lhs, rhs) -> binary true "usubo" lhs rhs
    | Concat (lhs, rhs) ->
        let lw, lhs = expr lhs in
        let rw, rhs = expr rhs in
        line (Z.add lw rw) (fun fmt sid ->
          fprintf fmt "concat %a %a %a" Z.pp_print sid Z.pp_print lhs Z.pp_print rhs)
    | ITE (cond, if_t, if_f) ->
        let cw, cond = expr cond in
        let tw, if_t = expr if_t in
        let fw, if_f = expr if_f in
        check_width Z.one cw;
        check_width tw fw;
        line tw (fun fmt sid ->
          fprintf fmt "ite %a %a %a %a" Z.pp_print sid Z.pp_print cond Z.pp_print if_t Z.pp_print if_f)
  in
  (* Declare states first, preserve operator order, then emit updates/properties. *)
  List.iter (function
    | StateDecl (name, width) ->
        let sid = sort width in
        let id = emit (fun fmt -> fprintf fmt "state %a" Z.pp_print sid) in
        add_name name (width, id, true)
    | _ -> ()) model;
  List.iter (function
    | Operator (width, name, e) ->
        let actual, id = expr e in
        check_width width actual;
        add_name name (width, id, false)
    | _ -> ()) model;
  let update opcode width name e =
    let target_width, target, is_state = reference name in
    if not is_state then invalid_arg "Btor2PP: init/next target must be a state";
    check_width width target_width;
    let actual, value = expr e in
    check_width width actual;
    let sid = sort width in
    ignore (emit (fun fmt -> fprintf fmt "%s %a %a %a" opcode
      Z.pp_print sid Z.pp_print target Z.pp_print value))
  in
  List.iter (function
    | StateInit (width, name, e) -> update "init" width name e
    | StateNext (width, name, e) -> update "next" width name e
    | Bad e ->
        let width, id = expr e in
        check_width Z.one width;
        ignore (emit (fun fmt -> fprintf fmt "bad %a" Z.pp_print id))
    | _ -> ()) model;
  List.iter (fun (id, line) -> fprintf fmt "%a %t\n" Z.pp_print id line) (List.rev !lines)
