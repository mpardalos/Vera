From Coq Require Import BinNums.
From Coq Require Import BinNat.
From Coq Require Import BinPos.
From Coq Require FMaps.
From Coq Require FMapFacts.
From Coq Require Import List.
From Coq Require Import ssreflect.
Import ListNotations.

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

Set Primitive Projections.

Equations varWidth : variable -> positive :=
  varWidth (Var (Logic w) _) := w.

Equations get_var {c} (st : CircuitState c) (n : name) (name_present : NameMap.In n (variables st)) : { v : bv | NameMap.MapsTo n v (variables st) } :=
  get_var st n prf :=
    (match NameMap.find n (variables st) as r return (_ = r -> _) with
     | Some x => fun eq => (@exist _ _ x eq)
     | None => fun eq => False_rec _ _
     end) eq_refl.
Next Obligation.
  rewrite <- NameMapFacts.not_find_in_iff in *.
  contradiction.
Qed.

Equations input_run {c} (st : CircuitState c) (i : input) (input_wf : input_in_circuit c i) : bv :=
  input_run st (InConstant const) _ := const;
  input_run st (InVar (Var t n)) i_wf := proj1_sig (get_var st n _).
Next Obligation.
  unfold NameMap.In.
  edestruct circuit_to_state_variables.
  - simp input_in_circuit in *.
  - intuition eauto.
Qed.

Lemma input_run_width : forall {c} (st : CircuitState c) i input_wf,
    width (input_run st i input_wf) = input_width i.
Proof.
  intros.
  funelim (input_width i); simp input_run; last done.
  case (get_var st varName0 (input_run_obligations_obligation_1 c st (Logic w) varName0 input_wf)) => x Hx /=.
  inversion input_wf as [input_wf'] => {input_wf}.
  rewrite <- NameMapFacts.find_mapsto_iff in input_wf'.
  edestruct circuit_to_state_variables as [x' [Hin Hwidth]]; first by eauto.
  simp type_width in *.
  replace x with x'; first done.
  eauto using NameMapFacts.MapsTo_fun.
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
  compare n0 k => E.
  - subst.
    exists x.
    intuition.
    apply NameMapFacts.add_mapsto_iff.
    auto.
  - exists xprev.
    intuition.
    apply NameMapFacts.add_mapsto_iff.
    auto.
Qed.

Lemma variable_in_map_extend
  (n k : name)
  (w : positive)
  (x: bv)
  (m : NameMap.t bv) :
  (n <> k \/ width x = w) ->
  variable_in_map m (Var (Logic w) n) ->
  variable_in_map (NameMap.add k x m) (Var (Logic w) n).
Proof.
  move => [? | ?] H2.
  all: auto using variable_in_map_extend_other, variable_in_map_extend_same.
Qed.

(* Ltac simpl_list_props := repeat (try rewrite Forall_forall in *; try rewrite Exists_exists in .*)

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
    rewrite bv_add_truncate_width input_run_width output_match.
    destruct cell_wf as [Hout _].
    funelim (output_width _).
    injection eqargs as <- <-.
    (* clear inputs_match. clear output_match. clear in1. clear in2. *)
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

Equations list_with_in' {A} (full_list : list A) (l : list A) (prev : {l1 : list A | full_list = l1 ++ l}) : list {x : A | In x full_list} :=
  list_with_in' full_list nil (@exist _ _) := nil;
  list_with_in' full_list (hd :: tl) (@exist prev prf) := (@exist _ _ hd _) :: (list_with_in' full_list tl _) .
Next Obligation. eauto with datatypes. Qed.
Next Obligation. exists (prev ++ [hd]). eauto with datatypes. Qed.

Equations list_with_in {A} (full_list : list A) : (list { x : A | In x full_list }) :=
  list_with_in full_list := list_with_in' full_list full_list (@exist _ _ nil _).

Equations circuit_run
  (c : { c: circuit | circuit_wf c })
  (fext : ExternalState (proj1_sig c))
  (fbits : RandomSource)
  (st: CircuitState (proj1_sig c))
  : CircuitState (proj1_sig c) :=
  circuit_run (@exist (Circuit _ _ vars regs cells) c_wf) fext fbits st_init :=
    List.fold_left (fun st cell => cell_run st (proj1_sig cell) _) (list_with_in cells) st_init.
Next Obligation.
  destruct c_wf.
  rewrite Forall_forall in *.
  eauto.
Qed.
