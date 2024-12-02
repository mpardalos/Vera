open Format
open Vera

module type Formattable = sig
  type t

  val format : formatter -> t -> unit
end

(* let name fmt n = fprintf fmt "v%d" n *)

module SMT (Name : Formattable) = struct
  let rec qfbv fmt = function
    | Vera.SMT.BVAdd (l, r) -> fprintf fmt "(bvadd %a %a)" qfbv l qfbv r
    | Vera.SMT.BVMul (l, r) -> fprintf fmt "(bvmult %a %a)" qfbv l qfbv r
    | Vera.SMT.BVNeg f -> fprintf fmt "(bvneg %a)" qfbv f
    | Vera.SMT.BVShl (l, r) -> fprintf fmt "(bvshl %a %a)" qfbv l qfbv r
    | Vera.SMT.BVLShr (l, r) -> fprintf fmt "(bvlshr %a %a)" qfbv l qfbv r
    | Vera.SMT.BVLit (w, v) -> fprintf fmt "(_ bv%d %d)" (bits_to_int v) w
    | Vera.SMT.BVVar n -> Name.format fmt n
    | Vera.SMT.BVZeroExtend (num, f) ->
        fprintf fmt "((_ zero_extend %d) %a)" num qfbv f
    | Vera.SMT.BVExtract (hi, lo, f) ->
        fprintf fmt "((_ extract %d %d) %a)" hi lo qfbv f
    | Vera.SMT.CoreEq (l, r) ->
        fprintf fmt "(= %a %a)" qfbv l qfbv r
    | Vera.SMT.CoreNot e ->
        fprintf fmt "(not %a)" qfbv e
    | Vera.SMT.CoreITE (cond, ifT, ifF) ->
        fprintf fmt "(ite %a %a %a)" qfbv cond qfbv ifT qfbv ifF

  let sort fmt bv_sz = fprintf fmt "(_ BitVec %d)" bv_sz

  let smt fmt = function
    | Vera.SMT.CDeclare (n, s) ->
        fprintf fmt "(declare-const %a %a)" Name.format n sort s
    | Vera.SMT.CEqual (l, r) ->
        fprintf fmt "(assert (= %a %a))" qfbv l qfbv r
    | Vera.SMT.CDistinct (l, r) ->
        fprintf fmt "(assert (distinct %a %a))" qfbv l qfbv r

  let smt_netlist fmt (m : Name.t SMT.smt_netlist) =
    let formula_helper ports _ f =
      match f with
      | Vera.SMT.CDeclare (n, _) -> (
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

module StrSMT = SMT (struct
  type t = char list

  let format fmt n = fprintf fmt "%s" (Util.lst_to_string n)
end)
