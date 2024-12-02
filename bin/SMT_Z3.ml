open Format

type var_context = (char list, Z3.Expr.expr) Hashtbl.t

let rec qfbv_formula_to_z3 (var_ctx : var_context) (z3_ctx : Z3.context)
    (formula : char list Vera.SMT.qfbv) : Z3.Expr.expr =
  match formula with
  | Vera.SMT.BVAdd (l, r) ->
      Z3.BitVector.mk_add z3_ctx
        (qfbv_formula_to_z3 var_ctx z3_ctx l)
        (qfbv_formula_to_z3 var_ctx z3_ctx r)
  | Vera.SMT.BVMul (l, r) ->
      Z3.BitVector.mk_mul z3_ctx
        (qfbv_formula_to_z3 var_ctx z3_ctx l)
        (qfbv_formula_to_z3 var_ctx z3_ctx r)
  | Vera.SMT.BVNeg f ->
      Z3.BitVector.mk_neg z3_ctx (qfbv_formula_to_z3 var_ctx z3_ctx f)
  | Vera.SMT.BVShl (l, r) ->
      Z3.BitVector.mk_shl z3_ctx
        (qfbv_formula_to_z3 var_ctx z3_ctx l)
        (qfbv_formula_to_z3 var_ctx z3_ctx r)
  | Vera.SMT.BVLShr (l, r) ->
      Z3.BitVector.mk_lshr z3_ctx
        (qfbv_formula_to_z3 var_ctx z3_ctx l)
        (qfbv_formula_to_z3 var_ctx z3_ctx r)
  | Vera.SMT.BVLit (w, v) ->
      Z3.BitVector.mk_numeral z3_ctx
        (sprintf "%d" (Vera.bits_to_int v))
        w
  | Vera.SMT.BVVar n -> Hashtbl.find var_ctx n
  | Vera.SMT.BVZeroExtend (num, f) ->
      Z3.BitVector.mk_zero_ext z3_ctx num
        (qfbv_formula_to_z3 var_ctx z3_ctx f)
  | Vera.SMT.BVExtract (hi, lo, f) ->
      Z3.BitVector.mk_extract z3_ctx hi lo
        (qfbv_formula_to_z3 var_ctx z3_ctx f)
  | Vera.SMT.CoreEq (l, r) ->
      Z3.Boolean.mk_eq z3_ctx
        (qfbv_formula_to_z3 var_ctx z3_ctx l)
        (qfbv_formula_to_z3 var_ctx z3_ctx r)
  | Vera.SMT.CoreNot e ->
      Z3.Boolean.mk_not z3_ctx (qfbv_formula_to_z3 var_ctx z3_ctx e)
  | Vera.SMT.CoreITE (select, ifT, ifF) ->
      Z3.Boolean.mk_ite z3_ctx
        (qfbv_formula_to_z3 var_ctx z3_ctx select)
        (qfbv_formula_to_z3 var_ctx z3_ctx ifT)
        (qfbv_formula_to_z3 var_ctx z3_ctx ifF)
(* Z3.BitVector.mk_numeral z3_ctx (sprintf "%d" v.value) v.width *)

let smt_formula_to_z3 (var_ctx : var_context) (z3_ctx : Z3.context)
    (formula : char list Vera.SMT.formula) : Z3.Expr.expr option =
  match formula with
  | Vera.SMT.CDeclare (n, s) ->
      let expr =
        Z3.BitVector.mk_const_s z3_ctx (Util.lst_to_string n) s
      in
      Hashtbl.replace var_ctx n expr;
      None
  (* replace means add or replace if present *)
  | Vera.SMT.CEqual (l, r) ->
      Some
        (Z3.Boolean.mk_eq z3_ctx
           (qfbv_formula_to_z3 var_ctx z3_ctx l)
           (qfbv_formula_to_z3 var_ctx z3_ctx r))
  | Vera.SMT.CDistinct (l, r) ->
      Some
        (Z3.Boolean.mk_distinct z3_ctx
           [
             qfbv_formula_to_z3 var_ctx z3_ctx l;
             qfbv_formula_to_z3 var_ctx z3_ctx r;
           ])

let smt_to_z3 (z3_ctx : Z3.context) (formulas : char list Vera.SMT.formula list)
    : Z3.Expr.expr list =
  let var_ctx = Hashtbl.create 20 in
  List.filter_map (smt_formula_to_z3 var_ctx z3_ctx) formulas

let z3_model_fmt fmt (model : Z3.Model.model) =
  List.iter
    (fun decl ->
      let name = Z3.FuncDecl.get_name decl in
      let sort = Z3.FuncDecl.get_range decl in
      if Z3.Sort.get_sort_kind sort = Z3enums.BV_SORT then
        let size = Z3.BitVector.get_size sort in
        let value =
          Z3.Model.eval model (Z3.FuncDecl.apply decl []) true |> Option.get
        in
        fprintf fmt "%s = %d'%s\n" (Z3.Symbol.to_string name) size
          (Z3.Expr.to_string value))
    (Z3.Model.get_const_decls model)

type query_result =
  | SAT of Z3.Model.model option
  | UNSAT
  | UNKNOWN

let run_query (query : char list Vera.SMT.formula list) =
  List.iter (printf "%a\n" SMTPP.StrSMT.smt) query;
  let z3_ctx = Z3.mk_context [] in
  let z3_solver = Z3.Solver.mk_solver z3_ctx None in
  let z3_exprs = smt_to_z3 z3_ctx query in
  Z3.Solver.add z3_solver z3_exprs;
  match Z3.Solver.check z3_solver [] with
  | Z3.Solver.UNSATISFIABLE -> UNSAT
  | Z3.Solver.SATISFIABLE -> SAT (Z3.Solver.get_model z3_solver)
  | Z3.Solver.UNKNOWN -> UNKNOWN
