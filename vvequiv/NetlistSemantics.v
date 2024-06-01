From Coq Require Import BinNums.
From Coq Require Import BinNat.
From Coq Require Import BinPos.
From Coq Require Import List.
From Coq Require FMaps.
From Coq Require FMapFacts.

From vvequiv Require Import Netlist.
From vvequiv Require Import Common.
From vvequiv Require Import Bitvector.

From Equations Require Import Equations.

Import Bitvector.
Import Netlist.

(** Based on Lööw (2021) Lutsig: a verified Verilog compiler for verified circuit development, ACM. *)

Definition RandomSource := nat -> bool.

Equations input_port_in_map : NameMap.t bv -> (name * port_direction) -> Prop :=
| map, (n, PortIn) => NameMap.In n map
| map, (n, PortOut) => True.

Record ExternalState (c : circuit) :=
  MkExternalState
    { external_state_map :> NameMap.t bv
    ; external_state_match_circuit : Forall (input_port_in_map external_state_map) (circuitPorts c)
    }.

Arguments MkExternalState [_] _ _.

Equations register_in_map : NameMap.t bv -> register_declaration -> Prop :=
| map, MkRegister (Logic w) n _ _ => exists bv, NameMap.MapsTo n bv map /\ width bv = w.

Record RegisterState (c : circuit) :=
  MkRegisterState
    { register_state_map :> NameMap.t bv
    ; register_state_wf : Forall (register_in_map register_state_map) (circuitRegisters c)
    }.

Arguments MkRegisterState [_] _ _.

Equations variable_in_map : NameMap.t bv -> variable -> Prop :=
| map, Var (Logic w) n => exists bv, NameMap.MapsTo n bv map /\ width bv = w.

Record VariableState (c : circuit) :=
  MkVariableState
    { variable_state_map :> NameMap.t bv
    ; variable_state_wf : Forall (variable_in_map variable_state_map) (circuitVariables c)
    }.

Arguments MkVariableState [_] _ _.

Record CircuitState (c : circuit) :=
  MkCircuitState
    { external : ExternalState c
    ; registers : RegisterState c
    ; variables : VariableState c
    }
.

Arguments MkCircuitState [_].
Arguments external [_] _.
Arguments registers [_] _.
Arguments variables [_] _.

Set Primitive Projections.

Equations varWidth : variable -> positive :=
  varWidth (Var (Logic w) _) := w.

Equations var_reg_match : variable -> register_declaration -> Prop :=
| Var var_type var_name, MkRegister reg_type reg_name _ _ =>
    var_type = reg_type /\ var_name = reg_name.

Equations input_in_circuit : circuit -> input -> Prop :=
| _, InConstant _ => True
| c, InVar v => In v (circuitVariables c) \/ Exists (var_reg_match v) (circuitRegisters c).

Equations output_in_circuit : circuit -> output -> Prop :=
| c, OutVar v => In v (circuitVariables c) \/ Exists (var_reg_match v) (circuitRegisters c).

Equations cell_in_circuit : circuit -> cell -> Prop :=
| c, Add out in1 in2 _ _ =>
    output_in_circuit c out
    /\ input_in_circuit c in1
    /\ input_in_circuit c in2
| c, Subtract out in1 in2 _ _ =>
    output_in_circuit c out
    /\ input_in_circuit c in1
    /\ input_in_circuit c in2
| c, Id out in1 _ =>
    output_in_circuit c out
    /\ input_in_circuit c in1
| c, Convert out in1 =>
    output_in_circuit c out
    /\ input_in_circuit c in1
.

Set Equations With UIP.

Equations input_run {c} (st : CircuitState c) (i : input) (input_wf : input_in_circuit c i) : bv :=
  input_run st (InConstant const) _ := const;
  input_run st (InVar v) input_wf
    with NameMap.find v.(varName) st.(registers), NameMap.find v.(varName) st.(variables) => {
    | Some x, _ => x
    | _, Some x => x
    | None, None => _
    }.
Next Obligation.
Admitted.
(*   exfalso. *)
(*   rewrite <- NameMapFacts.not_find_in_iff in *. *)
(*   destruct input_wf. *)
(*   - apply Evariables. clear Evariables. clear Eregisters. *)
(*     destruct st as [exts regs vars]. simpl in *. *)
(*     destruct vars as [var_map vars_wf]. *)
(*     simpl. *)
(*     rewrite Forall_forall in vars_wf. *)
(*     apply vars_wf in H. clear vars_wf. *)
(*     funelim (variable_in_map var_map v). *)
(*     simp variable_in_map in H. *)
(*     destruct H as [bv [Hmap _]]. *)
(*     eexists. eauto. *)
(*   - apply Eregisters. clear Evariables. clear Eregisters. *)
(*     rewrite Exists_exists in H. *)
(*     destruct H as [r [H1 H2]]. *)
(*     destruct st as [exts regs vars]. simpl in *. *)
(*     destruct regs as [reg_map regs_wf]. *)
(*     simpl in *. *)
(*     rewrite Forall_forall in regs_wf. *)
(*     apply regs_wf in H1. *)
(*     funelim (register_in_map reg_map r). *)
(*     funelim (var_reg_match v (MkRegister (Logic w) n init driver)). *)
(*     simp register_in_map in *. *)
(*     simp var_reg_match in *. *)
(*     simpl in *. *)
(*     inversion H2; subst. *)
(*     destruct H1 as [bv [Hmap _]]. *)
(*     eexists. eassumption. *)
(* Defined. *)

Lemma input_run_width : forall {c} (st : CircuitState c) i input_wf,
    width (input_run st i input_wf) = input_width i.
Proof.
  intros.
  funelim (input_width i).
  - simp input_run.
    simpl.
    unfold input_run_clause_2_clause_1.
    destruct (NameMap.find varName0 (registers st)) eqn:Ereg.
    + admit.
    + destruct (NameMap.find varName0 (variables st)) eqn:Evars.
      * admit.
      * inversion input_wf.
        rewrite <- NameMapFacts.not_find_in_iff in Evars.
  - simp input_run. reflexivity.
Admitted.

Lemma variable_in_map_extend_other : forall (k : NameMap.key) (t : nltype) (n : name) (x: bv) (m : NameMap.t bv),
    n <> k -> variable_in_map m (Var t n) -> variable_in_map (NameMap.add k x m) (Var t n).
Proof.
  intros * Hdiff Hin.
  funelim (variable_in_map m (Var t n)).
  inversion H; subst; clear H.
  simp variable_in_map in *.
  destruct Hin as [bv [Hmap Hwidth]].
  exists bv.
  intuition eauto using NameMap.add_2.
Qed.

Lemma variable_in_map_extend_same : forall (n k : name) (w : positive) (x: bv) (m : NameMap.t bv),
    width x = w ->
    variable_in_map m (Var (Logic w) n) ->
    variable_in_map (NameMap.add k x m) (Var (Logic w) n).
Proof.
  intros * Heq Hin. subst.
  funelim (variable_in_map m (Var (Logic (width x)) n)).
  inversion H; subst; clear H.
  simp variable_in_map in *.
  destruct Hin as [xprev [Hmap Hwidth]].
  destruct (Pos.eq_dec n0 k).
  - subst.
    exists x.
    intuition.
    apply NameMapFacts.add_mapsto_iff.
    intuition eauto.
  - exists xprev.
    intuition.
    apply NameMapFacts.add_mapsto_iff.
    intuition eauto.
Qed.

Lemma variable_in_map_extend : forall (n k : name) (w : positive) (x: bv) (m : NameMap.t bv),
    (n <> k \/ width x = w) ->
    variable_in_map m (Var (Logic w) n) ->
    variable_in_map (NameMap.add k x m) (Var (Logic w) n).
Proof.
  intros * H1 H2.
  destruct H1.
  - auto using variable_in_map_extend_other.
  - auto using variable_in_map_extend_same.
Qed.

Ltac simpl_list_props := repeat (try rewrite Forall_forall in *; try rewrite Exists_exists in *).

Equations cell_run {c} (st : CircuitState c) (cl : cell) (cell_wf : cell_in_circuit c cl) : CircuitState c :=
  cell_run st (Add (OutVar (Var _ out)) in1 in2 inputs_match output_match) cell_wf :=
    let val1 := input_run st in1 _ in
    let val2 := input_run st in2 _ in
    let result := bv_add_truncate val1 val2 _ in
    MkCircuitState
      (external st)
      (registers st)
      (MkVariableState (NameMap.add out result (variables st)) _);
  (* TODO: Cells other than Add *)
  cell_run st _ _ := st.
Next Obligation.
  simp cell_in_circuit in cell_wf.
  decompose [and] cell_wf.
  assumption.
Qed.
Next Obligation.
  simp cell_in_circuit in cell_wf.
  decompose [and] cell_wf.
  assumption.
Qed.
Next Obligation.
  repeat rewrite input_run_width.
  assumption.
Qed.
Next Obligation.
  destruct st as [exts regs vars].
  destruct vars as [vars_map vars_wf].
  simpl in *.
  pose proof vars_wf as vars_wf_forall.
  simpl_list_props.
  intros [[xwidth] xname] Hin.
  destruct (Pos.eq_dec xname out).
  - subst.
    apply variable_in_map_extend_same.
    + rewrite bv_add_truncate_width.
      rewrite input_run_width.
      admit. (* Need that circuitVariables is a map from names to types (equal names -> equal types) *)
    + auto.
  - auto using variable_in_map_extend_other.
Admitted.

Equations circuit_run
  (fext : ExternalState)
  (fbits : RandomSource)
  (st: CircuitState)
  (c : circuit)
  : CircuitState :=
  circuit_run fext fbits st (Circuit _ _ vars regs cells) := st.
