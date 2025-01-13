From vera Require Import Verilog.
From vera Require Import SMT.
From vera Require Import Common.
From vera Require VerilogTypecheck.
From vera Require VerilogCanonicalize.
From vera Require VerilogToSMT.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Data.Monads.EitherMonad.
Import MonadNotation.
Open Scope monad_scope.
Require Import ZArith.
Require Import String.
Require Import List.
Import ListNotations.
Import EqNotations.

Section prefixing.
  Variable prefix : string.

  Definition prefix_name (name : string) : string :=
    prefix ++ "##" ++ name.

  Equations prefix_names_qfbv : SMT.qfbv string -> SMT.qfbv string := {
    | SMT.BVVar n => SMT.BVVar (prefix_name n)
    | SMT.BVOr l r => SMT.BVOr (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVAnd l r => SMT.BVAnd (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVAdd l r => SMT.BVAdd (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVMul l r => SMT.BVMul (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVNeg e => SMT.BVNeg (prefix_names_qfbv e)
    | SMT.BVNot e => SMT.BVNot (prefix_names_qfbv e)
    | SMT.BVShl l r => SMT.BVShl (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVLShr l r => SMT.BVLShr (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVLit val => SMT.BVLit val
    | SMT.BVZeroExtend count e => SMT.BVZeroExtend count (prefix_names_qfbv e)
    | SMT.BVExtract lo hi e => SMT.BVExtract lo hi (prefix_names_qfbv e)
    | SMT.BVConcat l r => SMT.BVConcat (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.CoreEq l r => SMT.CoreEq (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.CoreNot e => SMT.CoreNot (prefix_names_qfbv e)
    | SMT.CoreITE cond ifT ifF => SMT.CoreITE (prefix_names_qfbv cond) (prefix_names_qfbv ifT) (prefix_names_qfbv ifF)
    }.

  Equations prefix_names_formula : SMT.formula string -> SMT.formula string := {
    | SMT.CDeclare name sort => SMT.CDeclare (prefix_name name) sort
    | SMT.CEqual l r => SMT.CEqual (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.CDistinct l r => SMT.CDistinct (prefix_names_qfbv l) (prefix_names_qfbv r)
    }.

  Definition prefix_names_formulas : list (SMT.formula string) -> list (SMT.formula string) :=
    List.map prefix_names_formula.

  Definition prefix_names_smt_netlist (smtnl : SMT.smt_netlist string) : SMT.smt_netlist string :=
    {| SMT.smtnlName := SMT.smtnlName smtnl ;
      SMT.smtnlPorts := List.map (fun '(name, dir) => (prefix_name name, dir) ) (SMT.smtnlPorts smtnl) ;
      SMT.smtnlFormulas := List.map prefix_names_formula (SMT.smtnlFormulas smtnl)
    |}.
End prefixing.


Definition prefix_pair (prefix_left prefix_right : string): (string * string) -> (string * string) :=
  fun '(n1, n2) => (prefix_name prefix_left n1, prefix_name prefix_right n2).

Definition mk_equivalence_formulas
  (input_pairs output_pairs : list (string * string))
  (smtnl1 smtnl2 : SMT.smt_netlist string)
  : sum string (list (SMT.formula string)) :=

  let port_map1 := StrMap.from_list (SMT.smtnlPorts smtnl1) in
  let port_map2 := StrMap.from_list (SMT.smtnlPorts smtnl2) in
  let input_pairs_ok :=
    List.fold_right andb true
      (List.map
         (fun '(name1, name2) =>
            match StrMap.find name1 port_map1, StrMap.find name2 port_map2 with
            | Some PortIn, Some PortIn => true
            | _, _ => false
            end) input_pairs)
  in
  let output_pairs_ok :=
    List.fold_right andb true
      (List.map
         (fun '(name1, name2) =>
            match StrMap.find name1 port_map1, StrMap.find name2 port_map2 with
            | Some PortOut, Some PortOut => true
            | _, _ => false
            end) output_pairs)
  in

  if (input_pairs_ok && output_pairs_ok)%bool
  then
    let inputs_same := map (fun '(in1, in2) => SMT.CEqual (SMT.BVVar in1) (SMT.BVVar in2)) input_pairs in
    let outputs_different := map (fun '(in1, in2) => SMT.CDistinct (SMT.BVVar in1) (SMT.BVVar in2)) output_pairs in
    inr (inputs_same ++ outputs_different)
  else
    inl "Could not match ports"%string
.

Definition equivalence_query
  (input_pairs output_pairs : list (string * string))
  (verilog1 verilog2 : Verilog.vmodule)
  : sum string (list (SMT.formula string)) :=

  VerilogTypecheck.tc_vmodule verilog1 ;;
  VerilogTypecheck.tc_vmodule verilog2 ;;

  canonical_verilog1 <- VerilogCanonicalize.canonicalize_verilog verilog1 ;;
  canonical_verilog2 <- VerilogCanonicalize.canonicalize_verilog verilog2 ;;

  unsafe_smt_netlist1 <- VerilogToSMT.verilog_to_smt canonical_verilog1 ;;
  unsafe_smt_netlist2 <- VerilogToSMT.verilog_to_smt canonical_verilog2 ;;

  let (prefix1, prefix2) :=
    if (SMT.smtnlName unsafe_smt_netlist1 =? SMT.smtnlName unsafe_smt_netlist2)%string
    then (SMT.smtnlName unsafe_smt_netlist1 ++ "_1", SMT.smtnlName unsafe_smt_netlist2 ++ "_2")%string
    else (SMT.smtnlName unsafe_smt_netlist1, SMT.smtnlName unsafe_smt_netlist2)
  in

  let prefixed_smt_netlist1 := prefix_names_smt_netlist prefix1 unsafe_smt_netlist1 in
  let prefixed_smt_netlist2 := prefix_names_smt_netlist prefix2 unsafe_smt_netlist2 in

  let formulas1 := SMT.smtnlFormulas prefixed_smt_netlist1 in
  let formulas2 := SMT.smtnlFormulas prefixed_smt_netlist2 in

  let input_pairs_prefixed := List.map (prefix_pair prefix1 prefix2) input_pairs in
  let output_pairs_prefixed := List.map (prefix_pair prefix1 prefix2) output_pairs in

  equivalence_formulas <- mk_equivalence_formulas input_pairs_prefixed output_pairs_prefixed prefixed_smt_netlist1 prefixed_smt_netlist2 ;;
  (** Add equivalence queries *)
  ret (formulas1 ++ formulas2 ++ equivalence_formulas)
.
