open Format
module Zarith_Z = Z
open Vera

module SMTLib = struct
  let sort fmt = function
    | Vera.Sort_BitVec n -> fprintf fmt "(_ BitVec %a)" Zarith_Z.pp_print n
    | _ -> failwith "Unexpected sort"

  let varName fmt smtname =
    fprintf fmt "|%s|" smtname

  let var fmt (sym : const_sym) =
    fprintf fmt "(as %a %a)" varName sym.symName sort sym.symSort 

  let bitvector fmt (bits : bool list) =
    fprintf fmt "#b%s"
      (String.of_seq
         (List.to_seq
            (List.map (function true -> '1' | false -> '0') (List.rev bits))))

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

  let rec term fmt = function
    | Term_Const sym -> var fmt sym
    | Term_Eq (_s, l, r) ->
        fprintf fmt "(= %a %a)" term l term r
    | Term_And (l, r) ->
        fprintf fmt "(and %a %a)" term l term r
    | Term_Or (l, r) ->
        fprintf fmt "(or %a %a)" term l term r
    | Term_Not t -> fprintf fmt "(not %a)" term t
    | Term_ITE (_s, t1, t2, t3) ->
        fprintf fmt "(ite %a %a %a)" term t1 term t2
          term t3
    | Term_True -> fprintf fmt "true"
    | Term_False -> fprintf fmt "false"
    | Term_BVLit (_, bv) -> bitvector fmt bv
    | Term_BVConcat (_, _, l, r) ->
        fprintf fmt "(concat %a %a)" term l term r
    | Term_BVExtract (_, lo, hi, t) ->
        fprintf fmt "((_ extract %a %a) %a)" Zarith_Z.pp_print (int_from_nat lo)
          Zarith_Z.pp_print (int_from_nat hi) term t
    | Term_BVUnaryOp (_, op, t) ->
        fprintf fmt "(%a %a)" unaryOp op term t
    | Term_BVBinOp (_, op, t1, t2) ->
        fprintf fmt "(%a %a %a)" binaryOp op term t1 term
          t2
    | Term_BVUlt (_, t1, t2) ->
        fprintf fmt "(bvult %a %a)" term t1 term t2

  module SMTVarSet = Set.Make(struct type t = const_sym let compare = compare end)

  let rec collect_declarations_term : term -> SMTVarSet.t = function
    | Term_Const sym -> SMTVarSet.singleton sym
    | Term_Eq (_s, l, r) ->
        SMTVarSet.union (collect_declarations_term l) (collect_declarations_term r)
    | Term_And (l, r) ->
        SMTVarSet.union (collect_declarations_term l) (collect_declarations_term r)
    | Term_Or (l, r) ->
        SMTVarSet.union (collect_declarations_term l) (collect_declarations_term r)
    | Term_Not t -> collect_declarations_term t
    | Term_ITE (_s, t1, t2, t3) ->
        SMTVarSet.union
          (SMTVarSet.union (collect_declarations_term t1) (collect_declarations_term t2))
          (collect_declarations_term t3)
    | Term_True -> SMTVarSet.empty
    | Term_False -> SMTVarSet.empty
    | Term_BVLit (_, _bv) -> SMTVarSet.empty
    | Term_BVConcat (_, _, l, r) ->
        SMTVarSet.union (collect_declarations_term l) (collect_declarations_term r)
    | Term_BVExtract (_, _lo, _hi, t) -> collect_declarations_term t
    | Term_BVUnaryOp (_, _, t) -> collect_declarations_term t
    | Term_BVBinOp (_, _op, t1, t2) ->
        SMTVarSet.union (collect_declarations_term t1) (collect_declarations_term t2)
    | Term_BVUlt (_, t1, t2) ->
        SMTVarSet.union (collect_declarations_term t1) (collect_declarations_term t2)

  let collect_declarations : query -> SMTVarSet.t =
    List.fold_left (fun acc t -> SMTVarSet.union acc (collect_declarations_term t)) SMTVarSet.empty

  let declaration fmt sym =
    fprintf fmt "(declare-const %a %a)" varName sym.symName sort sym.symSort

  let assertion fmt t = fprintf fmt "(assert %a)" term t

  let raw_query fmt (query : query) =
    pp_print_list
      declaration
      fmt
      (collect_declarations query |> SMTVarSet.to_seq |> List.of_seq)
      ~pp_sep:pp_force_newline;
    pp_force_newline fmt ();
    pp_force_newline fmt ();
    pp_print_list assertion fmt query
      ~pp_sep:pp_force_newline

  let query fmt (query : query) =
    fprintf fmt "(set-info :smt-lib-version 2.6)\n";
    fprintf fmt "(set-logic QF_BV)\n";
    raw_query fmt query;
    fprintf fmt "(check-sat)\n";
    fprintf fmt "(exit)\n"
end
