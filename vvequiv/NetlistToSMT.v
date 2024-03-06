Require Import Names.
Require Import Netlist.
Require Import SMT.

(** Map each variable in the netlist to a bitvector formula *)
Definition netlist_to_smt (nl : Netlist.circuit) : NameMap.t QFBV.formula := NameMap.empty _.
