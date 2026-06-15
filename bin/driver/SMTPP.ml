open Format
open Vera

module SMTLib = struct
  let sort fmt = function
    | Sort_BitVec n -> fprintf fmt "(_ BitVec %a)" Z.pp_print n
    | _ -> failwith "Unexpected sort"

  let varName (nameMap : VerilogSMTBijection.t) fmt nameIdx =
    match nameMap.bij_inverse nameIdx with
    | Some (VerilogLeft, n) -> fprintf fmt "|l_%s|" (Util.lst_to_string n.varName)
    | Some (VerilogRight, n) ->
        fprintf fmt "|r_%s|" (Util.lst_to_string n.varName)
    | None -> fprintf fmt "|v%a|" Z.pp_print (int_from_nat nameIdx)

  let var (nameMap : VerilogSMTBijection.t) fmt ((nameIdx, s) : smtname * sort) =
    fprintf fmt "(as %a %a)" (varName nameMap) nameIdx sort s 

  let bitvector fmt (bits : bool list) =
    fprintf fmt "#b%s"
      (String.of_seq
         (List.to_seq
            (map (function true -> '1' | false -> '0') (List.rev bits))))

  let unaryOp fmt = function
    | BVNot -> fprintf fmt "bvnot"
    | BVNeg -> fprintf fmt "bvneg"

  let binaryOp fmt = function
    | BVAnd -> fprintf fmt "bvand"
    | BVOr -> fprintf fmt "bvor"
    | BVXor -> fprintf fmt "bvxor"
    | BVAdd -> fprintf fmt "bvadd"
    | BVMul -> fprintf fmt "bvmul"
    | BVShl -> fprintf fmt "bvshl"
    | BVShr -> fprintf fmt "bvlshr"

  let rec term varNames fmt = function
    | Term_Const (s, name) -> var varNames fmt (name, s)
    | Term_Eq (_s, l, r) ->
        fprintf fmt "(= %a %a)" (term varNames) l (term varNames) r
    | Term_And (l, r) ->
        fprintf fmt "(and %a %a)" (term varNames) l (term varNames) r
    | Term_Or (l, r) ->
        fprintf fmt "(or %a %a)" (term varNames) l (term varNames) r
    | Term_Not t -> fprintf fmt "(not %a)" (term varNames) t
    | Term_ITE (_s, t1, t2, t3) ->
        fprintf fmt "(ite %a %a %a)" (term varNames) t1 (term varNames) t2
          (term varNames) t3
    | Term_True -> fprintf fmt "true"
    | Term_False -> fprintf fmt "false"
    | Term_BVLit (_, bv) -> bitvector fmt bv
    | Term_BVConcat (_, _, l, r) ->
        fprintf fmt "(concat %a %a)" (term varNames) l (term varNames) r
    | Term_BVExtract (_, lo, hi, t) ->
        fprintf fmt "((_ extract %a %a) %a)" Z.pp_print (int_from_nat lo)
          Z.pp_print (int_from_nat hi) (term varNames) t
    | Term_BVUnaryOp (_, op, t) ->
        fprintf fmt "(%a %a)" unaryOp op (term varNames) t
    | Term_BVBinOp (_, op, t1, t2) ->
        fprintf fmt "(%a %a %a)" binaryOp op (term varNames) t1 (term varNames)
          t2
    | Term_BVUlt (_, t1, t2) ->
        fprintf fmt "(bvult %a %a)" (term varNames) t1 (term varNames) t2

  module SMTNameMap = struct
    include Map.Make(struct type t = smtname let compare = compare end)
    let combine = union (fun _ s _ -> Some s)
  end

  let rec collect_declarations_term : term -> sort SMTNameMap.t = function
    | Term_Const (s, name) -> SMTNameMap.singleton name s
    | Term_Eq (_s, l, r) ->
        SMTNameMap.combine (collect_declarations_term l) (collect_declarations_term r)
    | Term_And (l, r) ->
        SMTNameMap.combine (collect_declarations_term l) (collect_declarations_term r)
    | Term_Or (l, r) ->
        SMTNameMap.combine (collect_declarations_term l) (collect_declarations_term r)
    | Term_Not t -> collect_declarations_term t
    | Term_ITE (_s, t1, t2, t3) ->
        SMTNameMap.combine
          (SMTNameMap.combine (collect_declarations_term t1) (collect_declarations_term t2))
          (collect_declarations_term t3)
    | Term_True -> SMTNameMap.empty
    | Term_False -> SMTNameMap.empty
    | Term_BVLit (_, _bv) -> SMTNameMap.empty
    | Term_BVConcat (_, _, l, r) ->
        SMTNameMap.combine (collect_declarations_term l) (collect_declarations_term r)
    | Term_BVExtract (_, _lo, _hi, t) -> collect_declarations_term t
    | Term_BVUnaryOp (_, _, t) -> collect_declarations_term t
    | Term_BVBinOp (_, _op, t1, t2) ->
        SMTNameMap.combine (collect_declarations_term t1) (collect_declarations_term t2)
    | Term_BVUlt (_, t1, t2) ->
        SMTNameMap.combine (collect_declarations_term t1) (collect_declarations_term t2)

  let collect_declarations : query -> sort SMTNameMap.t =
    List.fold_left (fun acc t -> SMTNameMap.combine acc (collect_declarations_term t)) SMTNameMap.empty

  let declaration nameMap fmt (v, s) =
    fprintf fmt "(declare-const %a %a)" (varName nameMap) v sort s

  let assertion varNames fmt t = fprintf fmt "(assert %a)" (term varNames) t

  let raw_query fmt (query : smt_with_namemap) =
    pp_print_list
      (declaration query.nameMap)
      fmt
      (collect_declarations query.assertions |> SMTNameMap.to_seq |> List.of_seq)
      ~pp_sep:pp_force_newline;
    pp_force_newline fmt ();
    pp_force_newline fmt ();
    pp_print_list (assertion query.nameMap) fmt query.assertions
      ~pp_sep:pp_force_newline

  let query fmt (query : smt_with_namemap) =
    fprintf fmt "(set-info :smt-lib-version 2.6)\n";
    fprintf fmt "(set-logic QF_BV)\n";
    raw_query fmt query;
    fprintf fmt "(check-sat)\n";
    fprintf fmt "(exit)\n"
end
