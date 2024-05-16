open Format
open VVEquiv

module type Formattable = sig
  type t

  val format : formatter -> t -> unit
end

(* let name fmt n = fprintf fmt "v%d" n *)

module SMT (Name : Formattable) = struct

  let rec qfbv fmt = function
    | VVEquiv.SMT.BVAdd (l, r) -> fprintf fmt "(bvadd %a %a)" qfbv l qfbv r
    | VVEquiv.SMT.BVNeg f -> fprintf fmt "(bvneg %a)" qfbv f
    | VVEquiv.SMT.BVLit v -> fprintf fmt "(_ bv%d %d)" v.value v.width
    | VVEquiv.SMT.BVVar n -> Name.format fmt n

  let sort fmt bv_sz = fprintf fmt "(_ BitVec %d)" bv_sz

  let smt fmt = function
    | VVEquiv.SMT.CDeclare (n, s) ->
        fprintf fmt "(declare-const %a %a)" Name.format n sort s
    | VVEquiv.SMT.CEqual (l, r) ->
        fprintf fmt "(assert (= %a %a))" qfbv l qfbv r
    | VVEquiv.SMT.CDistinct (l, r) ->
        fprintf fmt "(assert (distinct %a %a))" qfbv l qfbv r


  let smt_netlist fmt (m : Name.t SMT.smt_netlist) =
    let formula_helper ports _ f =
      match f with
      | VVEquiv.SMT.CDeclare (n, _) -> (
          match List.find_opt (fun p -> fst p == n) ports with
          | Some (_, PortIn) -> fprintf fmt "%a ; In" smt f
          | Some (_, PortOut) -> fprintf fmt "%a ; Out" smt f
          | None -> smt fmt f)
      | _ -> smt fmt f
    in
    fprintf fmt ";; SMTNetlist '%s'\n" (Util.lst_to_string m.smtnlName);
    List.iter
      (fun f -> fprintf fmt "%a\n" (formula_helper m.smtnlPorts) f)
      m.smtnlFormulas
end

