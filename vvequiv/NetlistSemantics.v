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
    ; external_state_match_circuit :
      forall n, NameMap.In n (circuitPorts c) -> NameMap.In n external_state_map
    }.

Arguments MkExternalState [_] _ _.

Record RegisterState (c : circuit) :=
  MkRegisterState
    { register_state_map :> NameMap.t bv
    ; register_state_wf :
      forall n t i d,
        NameMap.MapsTo n (MkRegister t i d) (circuitRegisters c)
        -> (exists v, NameMap.MapsTo n v register_state_map /\ (width v = type_width t))

    }.

Arguments MkRegisterState [_] _ _.

Equations variable_in_map : NameMap.t bv -> variable -> Prop :=
| map, Var (Logic w) n => exists bv, NameMap.MapsTo n bv map /\ width bv = w.

Record VariableState (c : circuit) :=
  MkVariableState
    { variable_state_map :> NameMap.t bv
    ; variable_state_wf :
      forall n t,
        NameMap.MapsTo n t (circuitVariables c)
        -> (exists v, NameMap.MapsTo n v variable_state_map /\ (width v = type_width t))
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

Equations input_in_circuit : circuit -> input -> Prop :=
| _, InConstant _ => True
| c, InVar (Var t n) => NameMap.MapsTo n t (circuitVariables c).


Equations output_in_circuit : circuit -> output -> Prop :=
| c, OutVar (Var t n) => NameMap.MapsTo n t (circuitVariables c).


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


Equations input_run {c} (st : CircuitState c) (i : input) (input_wf : input_in_circuit c i) : bv :=
  input_run st (InConstant const) _ := const;
  input_run st (InVar (Var t n)) wf with NameMap.find n (variables st) => {
    | Some x := x;
    | None with (_ : False) => { | ! }
    }
.
Next Obligation.
  (* Lookup always succeeds *)
Admitted.


(* Lemma input_width : forall c n t1 t2, input_in_circuit c (Var t1 n) -> NameMap.MapsTo n t2 (circuitVariables c) -> t1 = t2. *)

Lemma input_run_width : forall {c} (st : CircuitState c) i input_wf,
    width (input_run st i input_wf) = input_width i.
Proof.
  intros.
  destruct st as [exts regs [vars vars_wf]].
  funelim (input_width i).
  - simp input_run.
    unfold input_run_clause_2.
    simpl.
    assert (exists b, NameMap.find varName0 vars = Some b) as [b Hb]. {
      simp input_in_circuit in input_wf.
      edestruct vars_wf as [b' [Hvars Hwidth]]; eauto.
    }
    destruct (NameMap.find varName0 vars) eqn:E. 2: solve [discriminate].
    inversion Hb; subst; clear Hb.
    simp input_in_circuit in input_wf.
    edestruct vars_wf as [b' [Hvars Hwidth]]; eauto.
    replace b with b'.
    + simp type_width in *.
    + rewrite <- NameMapFacts.find_mapsto_iff in E.
      eauto using NameMapFacts.MapsTo_fun.
  - simp input_run. reflexivity.
Qed.

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
  compare n0 k; intros E.
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

(* Ltac simpl_list_props := repeat (try rewrite Forall_forall in *; try rewrite Exists_exists in .*)

Ltac inv_circuit_state st :=
  destruct st as [[exts exts_wf] [regs regs_wf] [vars vars_wf]].

Lemma circuit_to_state_variables : forall c (st: CircuitState c) n t,
    NameMap.MapsTo n t (circuitVariables c) ->
    exists v, (NameMap.MapsTo n v (variables st) /\ width v = type_width t).
Proof.
  intros * H.
  inv_circuit_state st.
  simpl in *.
  edestruct vars_wf as [v [Hvars _]]; eauto.
Qed.

(* Lemma state_to_circuit_variables : forall c (st: CircuitState c) n v, *)
(*     NameMap.MapsTo n v (variables st) -> *)
(*     NameMap.MapsTo n (Logic (width v)) (circuitVariables c). *)
(* Proof. *)
(*   intros * H. *)
(*   inv_circuit_state st. *)
(*   destruct (vars_wf n (Logic (width v))) as [_ vars_wf_to]. *)
(*   eauto. *)
(* Qed. *)

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
  compare n out; intros E.
  + subst. eexists.
    NameMapFacts.map_iff.
    intuition eauto.
    rewrite bv_add_truncate_width.
    rewrite input_run_width.
    rewrite output_match.
    inversion cell_wf as [Hout _]. clear cell_wf.
    funelim (output_width _).
    inversion eqargs; subst; clear eqargs.
    clear inputs_match. clear output_match. clear in1. clear in2.
    simp output_in_circuit in *.
    destruct t as [w'].
    assert (Logic w = Logic w') as Hw by eauto using NameMapFacts.MapsTo_fun.
    inversion Hw; subst; clear Hw.
    simp type_width.
    trivial.
  + edestruct circuit_to_state_variables as [v [Hv_in Hv_width]]; eauto.
    exists v.
    erewrite NameMapFacts.add_mapsto_iff.
    intuition eauto.
Qed.

Equations circuit_run
  (fext : ExternalState)
  (fbits : RandomSource)
  (st: CircuitState)
  (c : circuit)
  : CircuitState :=
  circuit_run fext fbits st (Circuit _ _ vars regs cells) := st.
