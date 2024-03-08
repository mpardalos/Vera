open Format
open VVEquiv

let name fmt n = fprintf fmt "v%d" n

module QFBV = struct
  let rec formula fmt = function
    | QFBV.BVAdd (l, r) -> fprintf fmt "(bvadd %a %a)" formula l formula r
    | QFBV.BVNeg f -> fprintf fmt "(bvneg %a)" formula f
    | QFBV.BVLit v -> fprintf fmt "(_ bv%d %d)" v.value v.width
    | QFBV.BVVar n -> name fmt n
end

module Core = struct
  let sort fmt bv_sz = fprintf fmt "(_ BitVec %d)" bv_sz

  let formula fmt = function
    | Core.CDeclare (n, s) -> fprintf fmt "(declare-const %a %a)" name n sort s
    | Core.CEqual (l, r) ->
        fprintf fmt "(assert (= %a %a))" QFBV.formula l QFBV.formula r
    | Core.CDistinct (l, r) ->
        fprintf fmt "(assert (distinct %a %a))" QFBV.formula l QFBV.formula r

  let formula_helper ports fmt f =
    match f with
    | Core.CDeclare (n, _) -> (
        match List.find_opt (fun p -> fst p == n) ports with
        | Some (_, PortIn) -> fprintf fmt "%a ; In" formula f
        | Some (_, PortOut) -> fprintf fmt "%a ; Out" formula f
        | None -> formula fmt f)
    | _ -> formula fmt f

  let smt_netlist fmt (m : Core.smt_netlist) =
    fprintf fmt ";; SMTNetlist '%s'\n" (Util.lst_to_string m.smtnlName);
    List.iter (fun f ->
      fprintf fmt "%a\n" (formula_helper m.smtnlPorts) f
    ) m.smtnlFormulas
end
