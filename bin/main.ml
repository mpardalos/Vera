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

let fmap f x =
  let* xval = x in
  ret (f xval)

let ( <$> ) = fmap
let ( <&> ) x f = fmap f x

let ( >=> ) (f : 'a -> 'b VVEquiv.result) (g : 'b -> 'c VVEquiv.result) (x : 'a)
    : 'c VVEquiv.result =
  let* y = f x in
  g y

type var_context = (int, Z3.Expr.expr) Hashtbl.t

let rec qfbv_formula_to_z3 (var_ctx : var_context) (z3_ctx : Z3.context)
    (formula : int VVEquiv.SMT.qfbv) : Z3.Expr.expr =
  match formula with
  | VVEquiv.SMT.BVAdd (l, r) ->
      Z3.BitVector.mk_add z3_ctx
        (qfbv_formula_to_z3 var_ctx z3_ctx l)
        (qfbv_formula_to_z3 var_ctx z3_ctx r)
  | VVEquiv.SMT.BVMul (l, r) ->
      Z3.BitVector.mk_mul z3_ctx
        (qfbv_formula_to_z3 var_ctx z3_ctx l)
        (qfbv_formula_to_z3 var_ctx z3_ctx r)
  | VVEquiv.SMT.BVNeg f ->
      Z3.BitVector.mk_neg z3_ctx (qfbv_formula_to_z3 var_ctx z3_ctx f)
  | VVEquiv.SMT.BVShl (l, r) ->
      Z3.BitVector.mk_shl z3_ctx
        (qfbv_formula_to_z3 var_ctx z3_ctx l)
        (qfbv_formula_to_z3 var_ctx z3_ctx r)
  | VVEquiv.SMT.BVLShr (l, r) ->
      Z3.BitVector.mk_lshr z3_ctx
        (qfbv_formula_to_z3 var_ctx z3_ctx l)
        (qfbv_formula_to_z3 var_ctx z3_ctx r)
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

let () =
  let usage_and_exit () =
    eprintf "Usage: %s <command> [args]\n" Sys.argv.(0);
    eprintf "\n";
    eprintf "Commands:\n";
    eprintf "  lex <filename>\n";
    eprintf "  parse <filename>\n";
    eprintf "  lower <level> <filename>\n";
    eprintf "\n";
    eprintf "Arguments:\n";
    eprintf "  parse_raw_type: expression|statement|module_item|module\n";
    eprintf "  level: parsed|typed|netlist|smt_netlist|smt\n";
    exit 1
  in

  let lex = function
    | [ filename ] ->
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
    | [] -> eprintf "Missing filename\n"
    | _ -> eprintf "Too many arguments\n"
  in

  let print_position outx (lexbuf : Lexing.lexbuf) =
    let pos = lexbuf.lex_curr_p in
    fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum
      (pos.pos_cnum - pos.pos_bol + 1)
  in

  let parse_file parse_func filename =
    let lexbuf = Lexing.from_channel (open_in filename) in
    try parse_func Lexer.read lexbuf with
    | Lexer.SyntaxError msg ->
        printf "%a: %s\n" print_position lexbuf msg;
        exit (-1)
    | Parser.Error ->
        printf "%a: syntax error\n" print_position lexbuf;
        exit (-1)
  in

  let parse_raw = function
    | [ parse_type; filename ] -> (
        let test_parse parse_func pp =
          printf "%a\n" pp (parse_file parse_func filename)
        in

        match parse_type with
        | "expression" -> test_parse Parser.expression_only VerilogPP.expression
        | "statement" -> test_parse Parser.statement_only VerilogPP.statement
        | "module_item" ->
            test_parse Parser.module_item_only VerilogPP.raw_mod_item
        | "module" -> test_parse Parser.vmodule_only VerilogPP.raw_vmodule
        | _ ->
            printf "Unknown parse type: %s\n" parse_type;
            usage_and_exit ())
    | _ -> usage_and_exit ()
  in

  let lower =
    let display_or_error pp result =
      match result with
      | VVEquiv.Inl err -> printf "Error: %s\n" (Util.lst_to_string err)
      | VVEquiv.Inr x -> printf "%a\n" pp x
    in

    let module_of_file (filename : string) :
        VVEquiv.Verilog.vmodule VVEquiv.result =
      let raw_module = parse_file Parser.vmodule_only filename in
      VVEquiv.parse_raw_verilog raw_module
    in

    let typed_module_of_file = module_of_file >=> VVEquiv.tc_vmodule in
    let netlist_of_file =
      typed_module_of_file >=> VVEquiv.verilog_to_netlist 1 >=> fun x ->
      ret (fst x)
    in
    let smt_netlist_of_file filename =
      VVEquiv.netlist_to_smt <$> netlist_of_file filename
    in
    let smt_formulas_of_file filename =
      VVEquiv.SMT.smtnlFormulas <$> smt_netlist_of_file filename
    in
    function
    | [ "parsed"; filename ] ->
        display_or_error VerilogPP.vmodule (module_of_file filename)
    | [ "typed"; filename ] ->
        display_or_error TypedVerilogPP.vmodule (typed_module_of_file filename)
    | [ "netlist"; filename ] ->
        display_or_error NetlistPP.circuit (netlist_of_file filename)
    | [ "smt_netlist"; filename ] ->
        display_or_error IntSMT.smt_netlist (smt_netlist_of_file filename)
    | [ "smt"; filename ] ->
        display_or_error
          (pp_print_list IntSMT.smt ~pp_sep:Util.newline_sep)
          (smt_formulas_of_file filename)
    | [ "all"; filename ] ->
        printf "\n-- parsed -- \n";
        display_or_error VerilogPP.vmodule (module_of_file filename);
        printf "\n-- typed --\n";
        display_or_error TypedVerilogPP.vmodule (typed_module_of_file filename);
        printf "\n-- netlist --\n";
        display_or_error NetlistPP.circuit (netlist_of_file filename);
        printf "\n-- smt_netlist --\n";
        display_or_error IntSMT.smt_netlist (smt_netlist_of_file filename);
        printf "\n-- smt_formulas --\n";
        display_or_error
          (pp_print_list IntSMT.smt ~pp_sep:Util.newline_sep)
          (smt_formulas_of_file filename)
    | [ stage; _filename ] ->
        eprintf "Unknown stage: %s\n" stage;
        usage_and_exit ()
    | _ -> usage_and_exit ()
  in

  let compare = function
    | [ filename1; filename2 ] -> (
        let queryResult =
          let* module1 =
            VVEquiv.parse_raw_verilog (parse_file Parser.vmodule_only filename1)
          in
          let* module2 =
            VVEquiv.parse_raw_verilog (parse_file Parser.vmodule_only filename2)
          in
          VVEquiv.equivalence_query module1 module2
        in
        match queryResult with
        | VVEquiv.Inl err -> printf "Error: %s\n" (Util.lst_to_string err)
        | VVEquiv.Inr query ->
            List.iter (printf "%a\n" IntSMT.smt) query;
            let z3_ctx = Z3.mk_context [] in
            let z3_solver = Z3.Solver.mk_solver z3_ctx None in
            let z3_exprs = smt_to_z3 z3_ctx query in
            Z3.Solver.add z3_solver z3_exprs;
            (match Z3.Solver.check z3_solver [] with
            | Z3.Solver.UNSATISFIABLE -> printf "Equivalent (UNSAT)\n"
            | Z3.Solver.SATISFIABLE -> (
                printf "Non-equivalent (SAT)\n";
                match Z3.Solver.get_model z3_solver with
                | None -> printf "No counterexample provided.\n"
                | Some model ->
                    printf "Model:\n---\n%a\n---\n" z3_model_fmt model)
            | Z3.Solver.UNKNOWN -> printf "Unknown\n");
            printf
              "\n==========================================================\n\n"
        )
    | _ -> usage_and_exit ()
  in

  printf "\n\n";
  match Array.to_list Sys.argv with
  | _prog :: "parse_raw" :: rest -> parse_raw rest
  | _prog :: "lex" :: rest -> lex rest
  | _prog :: "compare" :: rest -> compare rest
  | _prog :: "lower" :: rest -> lower rest
  | _prog :: cmd :: _ ->
      eprintf "Unknown command: %s\n" cmd;
      usage_and_exit ()
  | _ -> usage_and_exit ()
