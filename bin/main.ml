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

let dump_lex () =
  let filename = Sys.argv.(1) in
  let channel = open_in filename in
  let lexbuf = Lexing.from_channel channel in
  let rec print_tokens () : unit =
    let token = Lexer.read lexbuf in
    printf "%a " Lexer.token_fmt token;
    match token with Parser.EOF -> () | _ -> print_tokens ()
  in
  print_tokens ();
  printf "\n\n";
  close_in channel

let print_position outx (lexbuf : Lexing.lexbuf) =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)


let do_parse parse_func lexbuf =
  try parse_func Lexer.read lexbuf with
  | Lexer.SyntaxError msg ->
      printf "%a: %s\n" print_position lexbuf msg;
      exit (-1)
  | Parser.Error ->
      printf "%a: syntax error\n" print_position lexbuf;
      exit (-1)

let dump_parse () =
  let filename = Sys.argv.(2) in
  let channel = open_in filename in
  let lexbuf = Lexing.from_channel channel in

  let test_parse parse_func pp lexbuf =
    printf "%a\n" pp (do_parse parse_func lexbuf)
  in

  match Sys.argv.(1) with
  | "expression" ->
      test_parse Parser.expression_only VerilogPP.expression lexbuf
  | "statement" -> test_parse Parser.statement_only VerilogPP.statement lexbuf
  | "module_item" ->
      test_parse Parser.module_item_only VerilogPP.raw_mod_item lexbuf
  | "module" -> test_parse Parser.vmodule_only VerilogPP.raw_vmodule lexbuf
  | _ ->
      printf "Unknown parse type: %s\n" Sys.argv.(1);
      close_in channel

let parse_module () =
  let lexbuf = Lexing.from_channel (open_in (Sys.argv.(1))) in
  let raw_module = do_parse Parser.vmodule_only lexbuf in
  let clean_module = VVEquiv.parse_raw_verilog raw_module in
  match clean_module with
  | VVEquiv.Inl err -> printf "Raw verilog parsing error: %s\n" (Util.lst_to_string err)
  | VVEquiv.Inr m -> printf "%a\n" VerilogPP.vmodule m

let () = parse_module ()
