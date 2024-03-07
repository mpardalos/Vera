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
end
