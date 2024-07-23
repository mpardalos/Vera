open Format

module IntSMT = SMTPP.SMT (struct
  type t = int

  let format fmt n = fprintf fmt "v%d" n
                  end)

let ( >>= ) (x : ('err, 'a) VVEquiv.sum) (f : 'a -> ('err, 'b) VVEquiv.sum) =
  match x with VVEquiv.Inl e -> VVEquiv.Inl e | VVEquiv.Inr x -> f x

let ( let* ) = ( >>= )
let ( =<< ) a b = b >>= a
let ret x = VVEquiv.Inr x

type var_context = (int, Z3.Expr.expr) Hashtbl.t

let rec qfbv_formula_to_z3 (var_ctx : var_context) (z3_ctx : Z3.context)
          (formula : int VVEquiv.SMT.qfbv) : Z3.Expr.expr =
  match formula with
  | VVEquiv.SMT.BVAdd (l, r) ->
      Z3.BitVector.mk_add z3_ctx
        (qfbv_formula_to_z3 var_ctx z3_ctx l)
        (qfbv_formula_to_z3 var_ctx z3_ctx r)
  | VVEquiv.SMT.BVNeg f ->
      Z3.BitVector.mk_neg z3_ctx (qfbv_formula_to_z3 var_ctx z3_ctx f)
  | VVEquiv.SMT.BVLit v ->
      Z3.BitVector.mk_numeral z3_ctx (sprintf "%d" v.value) v.width
  | VVEquiv.SMT.BVVar n -> Hashtbl.find var_ctx n
  | VVEquiv.SMT.BVZeroExtend (num, f) ->
      Z3.BitVector.mk_zero_ext z3_ctx num (qfbv_formula_to_z3 var_ctx z3_ctx f)
  | VVEquiv.SMT.BVExtract (hi, lo, f) ->
      Z3.BitVector.mk_extract z3_ctx hi lo (qfbv_formula_to_z3 var_ctx z3_ctx f)
  | VVEquiv.SMT.CoreITE (select, ifT, ifF) ->
      Z3.Boolean.mk_ite z3_ctx
        (qfbv_formula_to_z3 var_ctx z3_ctx select)
        (qfbv_formula_to_z3 var_ctx z3_ctx ifT)
        (qfbv_formula_to_z3 var_ctx z3_ctx ifF)
(* Z3.BitVector.mk_numeral z3_ctx (sprintf "%d" v.value) v.width *)

let smt_formula_to_z3 (var_ctx : var_context) (z3_ctx : Z3.context)
      (formula : int VVEquiv.SMT.formula) : Z3.Expr.expr option =
  match formula with
  | VVEquiv.SMT.CDeclare (n, s) ->
      let expr = Z3.BitVector.mk_const_s z3_ctx (sprintf "v%d" n) s in
      Hashtbl.replace var_ctx n expr;
      None
  (* replace means add or replace if present *)
  | VVEquiv.SMT.CEqual (l, r) ->
      Some
        (Z3.Boolean.mk_eq z3_ctx
           (qfbv_formula_to_z3 var_ctx z3_ctx l)
           (qfbv_formula_to_z3 var_ctx z3_ctx r))
  | VVEquiv.SMT.CDistinct (l, r) ->
      Some
        (Z3.Boolean.mk_distinct z3_ctx
           [
             qfbv_formula_to_z3 var_ctx z3_ctx l;
             qfbv_formula_to_z3 var_ctx z3_ctx r;
        ])

let smt_to_z3 (z3_ctx : Z3.context) (formulas : int VVEquiv.SMT.formula list) :
    Z3.Expr.expr list =
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

let coq_verilog_examples () =
  List.iter
    (fun (v1, v2) ->
      let result =
        printf "\n-- Verilog a --\n";
        printf "%a\n" VerilogPP.vmodule v1;
        printf "\n-- Verilog b --\n";
        printf "%a\n" VerilogPP.vmodule v2;
        printf "\n---------------------------\n";
        printf "\n-- TypedVerilog a --\n";
        let* typed_v1 = VVEquiv.tc_vmodule v1 in
        printf "%a\n" TypedVerilogPP.vmodule typed_v1;
        printf "\n-- TypedVerilog b --\n";
        let* typed_v2 = VVEquiv.tc_vmodule v2 in
        printf "%a\n" TypedVerilogPP.vmodule typed_v2;
        printf "\n---------------------------\n";
        let* nl1, st = VVEquiv.verilog_to_netlist 1 typed_v1 in
        let* nl2, _ = VVEquiv.verilog_to_netlist st.nextName typed_v2 in
        printf "\n-- Netlist a --\n";
        printf "%a\n" NetlistPP.circuit nl1;
        printf "\n-- Netlist b --\n";
        printf "%a\n" NetlistPP.circuit nl2;
        printf "\n---------------------------\n";
        let* query = VVEquiv.equivalence_query v1 v2 in
        printf "\n-- SMT Query --\n";
        List.iter (printf "%a\n" IntSMT.smt) query;
        let z3_ctx = Z3.mk_context [] in
        let z3_exprs = smt_to_z3 z3_ctx query in
        (* List.iter *)
        (*   (fun e -> printf "%s\n" (Z3.AST.to_string (Z3.Expr.ast_of_expr e))) *)
        (*   z3_exprs; *)
        printf "\n---------------------------\n";
        printf "\n-- SMT Result --\n";
        let z3_solver = Z3.Solver.mk_solver z3_ctx None in
        Z3.Solver.add z3_solver z3_exprs;
        (match Z3.Solver.check z3_solver [] with
         | Z3.Solver.UNSATISFIABLE -> printf "Equivalent (UNSAT)\n"
         | Z3.Solver.SATISFIABLE -> (
           printf "Non-equivalent (SAT)\n";
           match Z3.Solver.get_model z3_solver with
           | None -> printf "No counterexample provided.\n"
           | Some model -> printf "Model:\n---\n%a\n---\n" z3_model_fmt model)
         | Z3.Solver.UNKNOWN -> printf "Unknown\n");
        printf
          "\n==========================================================\n\n";
        ret ()
      in
      match result with
      | VVEquiv.Inl err -> printf "Error: %s\n" (Util.lst_to_string err)
      | _ -> ())
    VVEquiv.Verilog.examples

let dump_lex () =
  let filename = Sys.argv.(1) in
  let channel = open_in filename in
  let lexbuf = Lexing.from_channel channel in
  let rec print_tokens () : unit =
    let token = Lexer.read lexbuf in
    printf "%a " Lexer.token_fmt token;
    match token with
    | Parser.EOF -> ()
    | _ -> print_tokens ()
  in
  print_tokens ();
  printf "\n\n";
  close_in channel

(* open Core *)
open Lexer
open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let dump_parse () =
  let filename = Sys.argv.(1) in
  let channel = open_in filename in
  let lexbuf = Lexing.from_channel channel in
  let out =
    try Parser.expression_only Lexer.read lexbuf with
    | SyntaxError msg ->
        printf "%a: %s\n" print_position lexbuf msg;
        exit (-1)
    | Parser.Error ->
        printf "%a: syntax error\n" print_position lexbuf;
        exit (-1)
  in
  printf "%a\n" VerilogPP.expression out ;
  close_in channel

let () = dump_parse ()
