open Format
open Vera

module SMTLib = struct
 let var (nameMap : (char list) NatFunMap.t) fmt nameIdx =
    match nameMap nameIdx with
    | Some n -> fprintf fmt "%s" (Util.lst_to_string n)
    | None -> fprintf fmt "v%d" (int_from_nat nameIdx)

  let bitvector fmt bits =
    fprintf fmt "#b%s"
      (Util.lst_to_string (map (function true -> '1' | false -> '0') bits))

  let sort fmt = function
    | Sort_Bool -> fprintf fmt "bool"
    | Sort_Int -> fprintf fmt "int"
    | Sort_BitVec m -> fprintf fmt "(_ BitVec %d)" m
    | Sort_Uninterpreted s -> fprintf fmt "s%d" (int_from_nat s)

  let unaryOp fmt = function
    | BVNot -> fprintf fmt "bv_not"
    | BVNeg -> fprintf fmt "bv_neg"

  let binaryOp fmt = function
    | BVAnd -> fprintf fmt "bv_and"
    | BVOr -> fprintf fmt "bv_or"
    | BVAdd -> fprintf fmt "bv_add"
    | BVMul -> fprintf fmt "bv_mul"
    | BVUDiv -> fprintf fmt "bv_udiv"
    | BVURem -> fprintf fmt "bv_urem"
    | BVShl -> fprintf fmt "bv_shl"
    | BVShr -> fprintf fmt "bv_shr"

  let rec term varNames fmt = function
    | Term_Fun ((name, _), []) -> var varNames fmt name
    | Term_Fun ((name, _), args) ->
        fprintf fmt "(%a %a)" (var varNames) name
          (pp_print_list (term varNames))
          args
    | Term_Int n -> fprintf fmt "%d" n
    | Term_Geq (l, r) ->
        fprintf fmt "(geq %a %a)" (term varNames) l (term varNames) r
    | Term_Eq (l, r) ->
        fprintf fmt "(= %a %a)" (term varNames) l (term varNames) r
    | Term_And (l, r) ->
        fprintf fmt "(and %a %a)" (term varNames) l (term varNames) r
    | Term_Not t -> fprintf fmt "(not %a)" (term varNames) t
    | Term_ITE (t1, t2, t3) ->
        fprintf fmt "(ite %a %a %a)" (term varNames) t1 (term varNames) t2
          (term varNames) t3
    | Term_BVLit bv -> bitvector fmt bv
    | Term_BVConcat (l, r) ->
        fprintf fmt "(bv_concat %a %a)" (term varNames) l (term varNames) r
    | Term_BVExtract (lo, hi, t) ->
        fprintf fmt "(bv_extract %d %d %a)" (int_from_nat lo) (int_from_nat hi)
          (term varNames) t
    | Term_BVUnaryOp (op, t) ->
        fprintf fmt "(%a %a)" unaryOp op (term varNames) t
    | Term_BVBinOp (op, t1, t2) ->
        fprintf fmt "(%a %a %a)" binaryOp op (term varNames) t1 (term varNames)
          t2
    | Term_BVUlt (t1, t2) ->
        fprintf fmt "(bv_ult %a %a)" (term varNames) t1 (term varNames) t2

  let declaration varNames fmt (name, s) =
    fprintf fmt "(declare-const %a %a)" (var varNames) name sort s

  let assertion varNames fmt t = fprintf fmt "(assert %a)" (term varNames) t

  let rec query fmt (query : SMT.smtlib_query) =
    fprintf fmt "%a\n%a"
      (pp_print_list (declaration query.nameSMTToVerilog))
      query.declarations
      (pp_print_list (assertion query.nameSMTToVerilog))
      query.assertions
end
