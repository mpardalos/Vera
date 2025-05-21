From vera Require Import Common.
From vera Require Import Tactics.
From vera Require Import VerilogToSMT.
From vera Require Import SMT.
From vera Require Import VerilogSemantics.
Import CombinationalOnly.

From Coq Require List.

From Equations Require Import Equations.

Theorem verilog_to_smt_map_match tag start v smt :
  verilog_to_smt tag start v = inr smt ->
  SMT.match_map_verilog tag (SMT.nameMap smt) v.
Proof.
  unfold SMT.match_map_verilog.
  intros.
  funelim (verilog_to_smt tag start v);
    simp verilog_to_smt in *;
    try rewrite Heq in *;
    simpl in *;
    try discriminate.
  autodestruct_eqn E.
  simpl.
  Set Nested Proofs Allowed.
  Lemma ind : forall vars tag var_start verilogName,
             (exists smtName : nat,
                 VerilogSMTBijection.lookup_left
                   (List.map (fun '(vname, smtname, _) => (tag, vname, smtname))
                      (transfer_vars var_start vars))
                   (tag, verilogName) = Some smtName) <->
               List.In verilogName
                 (VerilogSemantics.CombinationalOnly.variable_names vars).
  Proof.
    induction vars;
      intros; simpl in *;
      [ firstorder; discriminate | ].
    destruct a; simpl in *.
    destruct (TaggedName.dec_eq_tag tag tag); try contradiction.
    destruct (dec (verilogName = varName));
      simpl in *; subst;
      firstorder.
    - eauto.
    - eauto.
    - right. rewrite <- IHvars. eauto.
    - subst. contradiction.
    - rewrite IHvars. assumption.
  Qed.
  Unset Nested Proofs Allowed.
  apply ind.
Qed.

Theorem verilog_to_smt_correct tag start v smt :
  verilog_to_smt tag start v = inr smt ->
  SMTLibFacts.smt_reflect
    (SMT.query smt)
    (fun ρ => valid_execution v (SMT.execution_of_valuation tag (SMT.nameMap smt) ρ)).
Proof.
  intros.
  funelimverilog_to_smt tag start v

Lemma verilog_to_smt_only_tag t n v s :
  verilog_to_smt t n v = inr s ->
  VerilogSMTBijection.only_tag t (SMT.nameMap s).
Admitted.
