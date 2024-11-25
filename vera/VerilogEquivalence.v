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

Definition mk_equivalence_formulas (smtnl1 smtnl2 : SMT.smt_netlist string) : sum string (list (SMT.formula string)) :=
  let inputs1 := filter (fun '(_, dir) => is_port_in dir) (SMT.smtnlPorts smtnl1) in
  let inputs2 := filter (fun '(_, dir) => is_port_in dir) (SMT.smtnlPorts smtnl2) in
  let outputs1 := filter (fun '(_, dir) => is_port_out dir) (SMT.smtnlPorts smtnl1) in
  let outputs2 := filter (fun '(_, dir) => is_port_out dir) (SMT.smtnlPorts smtnl2) in
  if negb (length inputs1 =? length inputs2) then inl "Input counts do not match"%string
  else if negb (length outputs1 =? length outputs2) then inl "Output counts do not match"%string
       else let input_pairs: list ((string * port_direction) * (string * port_direction)) := combine inputs1 inputs2 in
            let output_pairs: list ((string * port_direction) * (string * port_direction)) := combine outputs1 outputs2 in
            let inputs_same :=
              map
                (fun '((in1, _), (in2, _)) =>
                   SMT.CEqual (SMT.BVVar in1) (SMT.BVVar in2))
                input_pairs in
            let outputs_different :=
              map (fun '((in1, _), (in2, _)) =>
                     SMT.CDistinct (SMT.BVVar in1) (SMT.BVVar in2))
                output_pairs in
            inr (inputs_same ++ outputs_different)
.

Section prefixing.
  Variable prefix : string.

  Equations prefix_names_qfbv : SMT.qfbv string -> SMT.qfbv string := {
    | SMT.BVVar n => SMT.BVVar (prefix ++ n)%string
    | SMT.BVAdd l r => SMT.BVAdd (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVMul l r => SMT.BVMul (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVNeg e => SMT.BVNeg (prefix_names_qfbv e)
    | SMT.BVShl l r => SMT.BVShl (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVLShr l r => SMT.BVLShr (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.BVLit val => SMT.BVLit val
    | SMT.BVZeroExtend count e => SMT.BVZeroExtend count (prefix_names_qfbv e)
    | SMT.BVExtract lo hi e => SMT.BVExtract lo hi (prefix_names_qfbv e)
    | SMT.CoreEq l r => SMT.CoreEq (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.CoreNot e => SMT.CoreNot (prefix_names_qfbv e)
    | SMT.CoreITE cond ifT ifF => SMT.CoreITE (prefix_names_qfbv cond) (prefix_names_qfbv ifT) (prefix_names_qfbv ifF)
    }.

  Equations prefix_names_formula : SMT.formula string -> SMT.formula string := {
    | SMT.CDeclare name sort => SMT.CDeclare (prefix ++ name)%string sort
    | SMT.CEqual l r => SMT.CEqual (prefix_names_qfbv l) (prefix_names_qfbv r)
    | SMT.CDistinct l r => SMT.CDistinct (prefix_names_qfbv l) (prefix_names_qfbv r)
    }.

  Definition prefix_names_formulas : list (SMT.formula string) -> list (SMT.formula string) :=
    List.map prefix_names_formula.

  Definition prefix_names_smt_netlist (smtnl : SMT.smt_netlist string) : SMT.smt_netlist string :=
    {| SMT.smtnlName := SMT.smtnlName smtnl ;
      SMT.smtnlPorts := List.map (fun '(name, dir) => ((prefix ++ name)%string, dir) ) (SMT.smtnlPorts smtnl) ;
      SMT.smtnlFormulas := List.map prefix_names_formula (SMT.smtnlFormulas smtnl)
    |}.
End prefixing.

Definition equivalence_query
  (verilog1 verilog2 : Verilog.vmodule)
  : sum string (list (SMT.formula string)) :=

  typed_verilog1 <- VerilogTypecheck.tc_vmodule verilog1 ;;
  typed_verilog2 <- VerilogTypecheck.tc_vmodule verilog2 ;;
  canonical_verilog1 <- VerilogCanonicalize.canonicalize_verilog typed_verilog1 ;;
  canonical_verilog2 <- VerilogCanonicalize.canonicalize_verilog typed_verilog2 ;;
  unsafe_smt_netlist1 <- VerilogToSMT.verilog_to_smt canonical_verilog1 ;;
  let prefixed_smt_netlist1 := prefix_names_smt_netlist
                                 ((SMT.smtnlName unsafe_smt_netlist1) ++ "##")
                                 unsafe_smt_netlist1 in
  unsafe_smt_netlist2 <- VerilogToSMT.verilog_to_smt canonical_verilog2 ;;
  let prefixed_smt_netlist2 := prefix_names_smt_netlist
                                 ((SMT.smtnlName unsafe_smt_netlist2) ++ "##")
                                 unsafe_smt_netlist2 in

  let formulas1 := SMT.smtnlFormulas prefixed_smt_netlist1 in
  let formulas2 := SMT.smtnlFormulas prefixed_smt_netlist2 in
  equivalence_formulas <- mk_equivalence_formulas prefixed_smt_netlist1 prefixed_smt_netlist2 ;;
  (** Add equivalence queries *)
  ret (formulas1 ++ formulas2 ++ equivalence_formulas)
.
