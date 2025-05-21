From Coq Require Import BinIntDef.
From Coq Require Import BinNums.
From Coq Require Import FSets.
From Coq Require Import List.
From Coq Require Import Program.
From Coq Require Import Psatz.
From Coq Require Import String.
From Coq Require Import ZArith.

From Equations Require Import Equations.
From ExtLib Require Import Data.List.
From ExtLib Require Import Data.Monads.EitherMonad.
From ExtLib Require Import Data.Monads.StateMonad.
From ExtLib Require Import Data.String.
From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.MonadState.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Monoid.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Programming.Show.

From SMTCoqApi Require SMTLib.

From vera Require Import Verilog.
From vera Require Import Common.
Import (coercions) VerilogSMTBijection.
From vera Require EnvStack.
From vera Require Import Bitvector.
From vera Require Import SMT.
From vera Require Import Decidable.
From vera Require Import Tactics.

Import ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.

Local Definition smtname := nat.
Local Definition width := N.

Definition transf := sum string.

Definition cast_from_to (from to: N) (expr : SMTLib.term) : SMTLib.term :=
  match N.compare to from with
  | Lt => SMTLib.Term_BVExtract (nat_of_N (to - 1)) 0 expr
  | Gt => SMTLib.Term_BVConcat (SMTLib.Term_BVLit (BV.zeros (to - from))) expr
  | Eq => expr
  end
.

Definition smt_var_info : Type := (smtname * width).

Section expr_to_smt.
  Variable var_verilog_to_smt : StrFunMap.t smt_var_info.

  Definition term_for_name (t : Verilog.vtype) (name : string) : transf SMTLib.term :=
    match var_verilog_to_smt name with
    | None => raise ("Name not declared: " ++ name)%string
    | Some (n__smt, width) =>
        if (width =? t)%N
        then ret (SMTLib.Term_Const n__smt)
        else raise ("Incorrect sort for " ++ name)%string
    end.


  Equations expr_to_smt : Verilog.expression -> transf SMTLib.term :=
    expr_to_smt (Verilog.UnaryOp Verilog.UnaryPlus operand) :=
      expr_to_smt operand ;
    expr_to_smt (Verilog.UnaryOp Verilog.UnaryMinus operand) :=
      operand__smt <- expr_to_smt operand ;;
      ret (SMTLib.Term_BVUnaryOp SMTLib.BVNeg operand__smt);
    expr_to_smt (Verilog.UnaryOp Verilog.UnaryNegation operand) :=
      operand__smt <- expr_to_smt operand ;;
      ret (SMTLib.Term_BVUnaryOp SMTLib.BVNot operand__smt);
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryPlus lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (SMTLib.Term_BVBinOp SMTLib.BVAdd lhs__smt rhs__smt);
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryMinus lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (SMTLib.Term_BVBinOp SMTLib.BVAdd lhs__smt (SMTLib.Term_BVUnaryOp SMTLib.BVNeg rhs__smt));
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryStar lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (SMTLib.Term_BVBinOp SMTLib.BVMul lhs__smt rhs__smt);
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryShiftLeft lhs rhs) :=
      let t__lhs := Verilog.expr_type lhs in
      let t__rhs := Verilog.expr_type rhs in
      let t__shift := N.max t__lhs t__rhs in
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (cast_from_to t__shift t__lhs
             (SMTLib.Term_BVBinOp SMTLib.BVShl
                (cast_from_to t__lhs t__shift lhs__smt)
                (cast_from_to t__rhs t__shift rhs__smt)));
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryShiftLeftArithmetic lhs rhs) :=
      let t__lhs := Verilog.expr_type lhs in
      let t__rhs := Verilog.expr_type rhs in
      let t__shift := N.max t__lhs t__rhs in
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (cast_from_to t__shift t__lhs
             (SMTLib.Term_BVBinOp SMTLib.BVShl
                (cast_from_to t__lhs t__shift lhs__smt)
                (cast_from_to t__rhs t__shift rhs__smt)));
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryShiftRight lhs rhs) :=
      let t__lhs := Verilog.expr_type lhs in
      let t__rhs := Verilog.expr_type rhs in
      let t__shift := N.max t__lhs t__rhs in
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (cast_from_to t__shift t__lhs
             (SMTLib.Term_BVBinOp SMTLib.BVShr
                (cast_from_to t__lhs t__shift lhs__smt)
                (cast_from_to t__rhs t__shift rhs__smt)));
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryBitwiseOr lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (SMTLib.Term_BVBinOp SMTLib.BVOr lhs__smt rhs__smt);
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryBitwiseAnd lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret (SMTLib.Term_BVBinOp SMTLib.BVAnd lhs__smt rhs__smt);
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryGreaterThan lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      raise "todo"%string;
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryLessThan lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      raise "todo"%string;
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryLessThanEqual lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      raise "todo"%string;
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryEqualsEquals lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      raise "todo"%string;
    expr_to_smt (Verilog.BinaryOp Verilog.BinaryLogicalAnd lhs rhs) :=
      lhs__smt <- expr_to_smt lhs ;;
      rhs__smt <- expr_to_smt rhs ;;
      raise "todo"%string;
    expr_to_smt (Verilog.BinaryOp op _ _) :=
      raise ("Unsupported operator in SMT: " ++ to_string op)%string;
    expr_to_smt (Verilog.Concatenation []) :=
      raise "Unsupported empty concatenation in SMT"%string;
    expr_to_smt (Verilog.Concatenation (hd :: tl)) :=
      hd__smt <- expr_to_smt hd ;;
      tl__smt <- mapT expr_to_smt tl ;;
      ret (fold_left SMTLib.Term_BVConcat tl__smt hd__smt);
    expr_to_smt (Verilog.Conditional cond ifT ifF) :=
      let t__cond := Verilog.expr_type cond in
      condval__smt <- expr_to_smt cond ;;
      ifT__smt <- expr_to_smt ifT ;;
      ifF__smt <- expr_to_smt ifF ;;
      let cond__smt := SMTLib.Term_Not
                       (SMTLib.Term_Eq
                          condval__smt
                          (SMTLib.Term_BVLit (BV.zeros t__cond)))
      in
      ret (SMTLib.Term_ITE cond__smt ifT__smt ifF__smt);
    expr_to_smt (Verilog.BitSelect vec idx) :=
      let t__vec := Verilog.expr_type vec in
      let t__idx := Verilog.expr_type idx in
      let t__shift := N.max t__vec t__idx in
      vec__smt <- expr_to_smt vec ;;
      idx__smt <- expr_to_smt idx ;;
      ret (SMTLib.Term_BVExtract 0 0
             (SMTLib.Term_BVBinOp SMTLib.BVShr
                (cast_from_to t__vec t__shift vec__smt)
                (cast_from_to t__idx t__shift idx__smt)));
    expr_to_smt (Verilog.Resize to expr) :=
      let from := Verilog.expr_type expr in
      expr__smt <- expr_to_smt expr ;;
      ret (cast_from_to from to expr__smt);
    expr_to_smt (Verilog.IntegerLiteral val) :=
      ret (SMTLib.Term_BVLit val);
    expr_to_smt (Verilog.NamedExpression t n) :=
      term_for_name t n
  .

  Equations transfer_comb_assignments : Verilog.statement -> transf (list SMTLib.term) :=
    transfer_comb_assignments (Verilog.Block stmts) =>
      lists <- mapT transfer_comb_assignments stmts ;;
      ret (concat lists) ;
    transfer_comb_assignments (Verilog.BlockingAssign (Verilog.NamedExpression t name) rhs) =>
      lhs__smt <- term_for_name t name ;;
      rhs__smt <- expr_to_smt rhs ;;
      ret [SMTLib.Term_Eq lhs__smt rhs__smt];
    transfer_comb_assignments _ =>
      raise "VerilogToSMT: Invalid expression in always_comb block"%string
  .
End expr_to_smt.

Definition transfer_ports (ports : list Verilog.port) : list (string * port_direction) :=
  map (fun '(Verilog.MkPort dir name) => (name, dir)) ports.

Equations transfer_initial (stmt : Verilog.statement) : transf (list SMTLib.term) :=
  transfer_initial (Verilog.Block stmts) =>
    lists <- mapT transfer_initial stmts ;;
    ret (concat lists) ;
  transfer_initial (Verilog.BlockingAssign
                      (Verilog.NamedExpression _ n)
                      (Verilog.IntegerLiteral val)) =>
    (* raise "VerilogToSMT: initial block blegh"%string; *)
    ret [] ;
  transfer_initial (Verilog.BlockingAssign
                      (Verilog.NamedExpression _ n)
                      (Verilog.Resize _ (Verilog.IntegerLiteral val))) =>
    (* raise "VerilogToSMT: initial block blegh"%string; *)
    ret [] ;
  transfer_initial _ =>
    raise "VerilogToSMT: Invalid expression in initial block"%string
.

Equations transfer_var (name__smt : smtname) (var : Verilog.variable) : (string * smtname * width) :=
  | name__smt, (Verilog.MkVariable vec storage name) =>
      (name, name__smt, (Verilog.vector_declaration_width vec)).

Equations transfer_vars (start : nat) (vars : list Verilog.variable) : list (string * smtname * width) :=
  | start, var :: rest =>
      transfer_var start var :: (transfer_vars (1 + start) rest)
  | start, nil => nil.

Definition mk_var_map (vars : list (string * smtname * width)) : StrFunMap.t (smtname * width) :=
  List.fold_right
    (fun '(verilog__name, smt__name, sort) acc => StrFunMap.insert verilog__name (smt__name, sort) acc)
    StrFunMap.empty vars.

Definition mk_bijection (name_tag : TaggedName.Tag) (vars : list (string * smtname * width)) : transf VerilogSMTBijection.t :=
  let var_pairs := map (fun '(vname, smtname, _) => (name_tag, vname, smtname)) vars in
  nodup_left <- assert_dec (NoDup (map fst var_pairs)) "Duplicate verilog name in var_pairs"%string ;;
  nodup_right <- assert_dec (NoDup (map snd var_pairs)) "Duplicate smt name in var_decls"%string ;;
  ret (VerilogSMTBijection.from_pairs var_pairs nodup_left nodup_right).

Lemma mk_bijection_map_match tag var_start vmodule m :
  mk_bijection tag (transfer_vars var_start (Verilog.modVariables vmodule)) = inr m ->
  SMT.match_map_verilog tag m vmodule.
Proof.
  intros.
  unfold mk_bijection in H. inv H. autodestruct.
  unfold SMT.match_map_verilog.
  unfold VerilogSMTBijection.from_pairs. simpl.
  clear n. (* the tags are all the same *)
  rewrite map_map in n0; simpl in n0.
  generalize dependent (Verilog.modVariables vmodule); intros l.
  induction l.
  - intros; split; intros H; solve_by_inverts 2%nat.
  - intros; split; intros H.
    + destruct H as [smtName H].
      simp transfer_vars in *.
      rewrite List.map_cons in H.
      rewrite VerilogSMTBijection.lookup_left_some_iff in H.
      admit.
    + admit.
Admitted.

Equations verilog_to_smt (name_tag : TaggedName.Tag) (var_start : nat) (vmodule : Verilog.vmodule)
  : transf SMT.smt_with_namemap :=
  verilog_to_smt name_tag var_start vmodule with Verilog.modBody vmodule := {
    | [ Verilog.Initial initial_body;
        Verilog.AlwaysFF (Verilog.Block []);
        Verilog.AlwaysComb always_comb_body
      ] =>
        let smt_var_list := transfer_vars var_start (Verilog.modVariables vmodule) in
        let var_map := mk_var_map smt_var_list in
        nameMap <- mk_bijection name_tag smt_var_list ;;
        initial_smt <- transfer_initial initial_body ;;
        always_comb_smt <- transfer_comb_assignments var_map always_comb_body ;;
        inr {|
            SMT.nameMap := nameMap;
            SMT.widths := List.map (fun '(_, smtname, width) => (smtname, width)) smt_var_list;
            SMT.query := initial_smt ++ always_comb_smt;
          |}
    | _ => raise "Non-canonical verilog passed to verilog_to_smt"%string
    }.


Lemma verilog_to_smt_map_match tag start v smt :
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
                   (map (fun '(vname, smtname, _) => (tag, vname, smtname))
                      (transfer_vars var_start vars))
                   (tag, verilogName) = Some smtName) <->
               In verilogName
                 (VerilogSemantics.CombinationalOnly.variable_names vars).
  Proof.
    induction vars;
      intros; simpl in *;
      [ firstorder; discriminate | ].
    destruct a; simpl in *.
    destruct (TaggedName.dec_eq_tag tag tag); try contradiction.
    destruct (dec_eq_string verilogName varName);
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
