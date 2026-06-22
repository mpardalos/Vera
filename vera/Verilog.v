From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import BinNums.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import ProofIrrelevance.
From Stdlib Require Import Structures.Orders.
From Stdlib Require Import Structures.OrdersEx.
From Stdlib Require Import RelationPairs.
From Stdlib Require MSets.

From ExtLib Require Import Programming.Show.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Data.Monads.EitherMonad.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.Monads.

From vera Require Import Common.
From vera Require Import Tactics.
From vera Require Import Bitvector.
From vera Require Import Decidable.
Import (notations) Bitvector.RawBV.

From Stdlib Require Import List.
From Stdlib Require Arith Lia Program.
From Stdlib Require Import Structures.Equalities.
From Stdlib Require Arith.PeanoNat.
From Equations Require Import Equations.

Import ListNotations.
Import MonadLetNotation.
Import SigTNotations.
Local Open Scope monad_scope.

#[global]
Declare Scope verilog_scope.

#[global]
Delimit Scope verilog_scope with verilog.

Local Open Scope verilog_scope.

Module VerilogCommon.
  Variant arithmeticop :=
    | ArithmeticPlus (* '+' *)
    | ArithmeticMinus (* '-' *)
    | ArithmeticStar (* '*' *)
    (* | ArithmeticSlash (* '/' *) *)
    (* | ArithmeticPercent (* '%' *) *)
    (* | BinaryExponent (* '**' *) *)
    .

Variant bitwiseop :=
    | BinaryBitwiseAnd (* '&' *)
    | BinaryBitwiseOr (* '|' *)
    | BinaryBitwiseXor (* '^' *)
  .

  (* Variant logicalop :=
   *   | BinaryEqualsEquals (\* '==' *\)
   *   | BinaryEqualsEqualsEquals (\* '===' *\)
   *   | BinaryGreaterThan (\* '>' *\)
   *   | BinaryGreaterThanEqual (\* '>=' *\)
   *   | BinaryLessThan (\* '<' *\)
   *   | BinaryLessThanEqual (\* '<=' *\)
   *   | BinaryLogicalAnd (\* '&&' *\)
   *   | BinaryLogicalEquivalence (\* '<->' *\)
   *   | BinaryLogicalImplication (\* '->' *\)
   *   | BinaryLogicalOr (\* '||' *\)
   *   | BinaryNotEquals (\* '!=' *\)
   *   | BinaryNotEqualsEquals (\* '!==' *\)
   *   | BinaryWildcardEqual (\* '==?' *\)
   *   | BinaryWildcardNotEqual (\* '!=?' *\)
   *   | BinaryXNor (\* '^~', '~^' *\)
   * . *)

  Variant shiftop :=
    | BinaryShiftRight (* '>>' *)
    | BinaryShiftLeft (* '<<' *)
    (* | BinaryShiftRightArithmetic (* '>>>' *) *)
    | BinaryShiftLeftArithmetic (* '<<<' *)
  .

  Variant unaryop :=
    | UnaryPlus (* +  *)
    (* | UnaryMinus (* -  *) *)
    | UnaryNot (* ~  *)
    (* | UnaryReduce... (* ~  *) *)
    (* | UnaryReduce... (* &  *) *)
    (* | UnaryReduce... (* ~& *) *)
    (* | UnaryReduce... (* |  *) *)
    (* | UnaryReduce... (* ~| *) *)
    (* | UnaryReduce... (* ^  *) *)
    (* | UnaryReduce... (* ~^ *) *)
    (* | UnaryReduce... (* ^~ *) *)
  .

  Variant vector_declaration :=
    | Scalar
    | Vector (msb : N) (lsb : N).

  Equations vector_declaration_width : vector_declaration -> N :=
    vector_declaration_width Scalar := 1%N ;
    vector_declaration_width (Vector hi lo) := 1%N + (N.max hi lo) - (N.min hi lo).

  Lemma vector_declaration_width_gt v : (vector_declaration_width v > 0)%N.
  Proof. funelim (vector_declaration_width v); lia. Qed.

  Variant StorageType := Reg | Wire.

  Record variable_declaration :=
    MkVariableDeclaration
      { varDeclPort : option port_direction
      ; varDeclVectorDeclaration : vector_declaration
      ; varDeclStorageType : StorageType
      ; varDeclName : string
      }.

  Definition varDeclWidth (v : variable_declaration) : N := vector_declaration_width (varDeclVectorDeclaration v).

  Definition vtype := N.

  Definition name := string.

  Record variable :=
    MkVariable
      { varName : name
      ; varType : vtype

      (*
      Seems weird to use `N` and then add this proof, when we could
      just use `positive` instead.

      Verilog does not have zero-width vectors. But SMTLIB does, and
      both it, and out bitvector library use `N`. So it is convenient
      to use `N` for Verilog too. Most things work without this proof
      (there is no reason why Verilog couldn't have zero-width
      BVs). But sometimes it comes up (see
      `execution_match_on_verilog_smt_match_states_partial`).
      *)

      ; varTypeWf : (varType > 0)%N
      }.

  Definition combine_compare (c1 c2 : comparison) : comparison :=
    match c1 with
    | Eq => c2
    | _ => c1
    end.

  Module Variable_as_MDT <: MiniDecidableType.
    Definition t := variable.

    Definition eq_dec (x y : variable) : {x=y} + {x<>y}.
    Proof.
      refine (match dec (varName x = varName y), dec (varType x = varType y) with
              | left _, left _ => left _
              | _, _ => right _
    	    end).
      all: destruct x, y.
      all: simpl in *.
      - subst. f_equal. apply proof_irrelevance.
      - crush.
      - crush.
    Qed.
  End Variable_as_MDT.

  Module Variable_as_DT := Make_UDT(Variable_as_MDT).

  #[global]
  Instance dec_eq_variable (x y : variable) : DecProp (x = y) :=
    Variable_as_DT.eq_dec x y.

  Module Variable_as_OT <: UsualOrderedType.
    Include Variable_as_DT.

    Definition lt :=
      (relation_disjunction (String_as_OT.lt @@ varName)
        (relation_conjunction (Logic.eq @@ varName) (N.lt @@ varType)))%signature.

    Global Instance lt_strorder : StrictOrder lt.
    Proof.
      split.
      - intros [n t] [nameLt|[nameEq typeLt]].
        + apply (@StrictOrder_Irreflexive _ String_as_OT.lt _ n). exact nameLt.
        + apply (@StrictOrder_Irreflexive _ N_as_OT.lt _ t).
	  exact typeLt.
      - intros [n1 t1] [n2 t2] [n3 t3] [nameLt12|[nameEq12 typeLt12]] [nameLt23|[nameEq23 typeLt23]].
        all: repeat match goal with [ e : (Logic.eq @@ _)%signature _ _ |- _] =>
	  cbv in e; subst
	end.
        + left.
	  eapply (@StrictOrder_Transitive _ String_as_OT.lt _ n1 n2 n3 nameLt12 nameLt23).
        + left. exact nameLt12.
        + left. exact nameLt23.
	+ right. split.
	  * reflexivity.
	  * exact (@StrictOrder_Transitive _ N_as_OT.lt _ t1 t2 t3 typeLt12 typeLt23).
    Qed.

    Global Instance lt_compat : Proper (eq==>eq==>iff) lt.
    Proof. intros x x' <- y y' <-. reflexivity. Qed.

    Definition compare v1 v2 :=
      combine_compare
        (String_as_OT.compare (varName v1) (varName v2))
        (varType v1 ?= varType v2)%N.

     Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
     Proof.
       intros [n1 t1] [n2 t2]. unfold compare, combine_compare. simpl.
       unfold CompSpec.
       destruct (String_as_OT.compare_spec n1 n2) as [cmp_n|cmp_n|cmp_n];
         [|crush|crush].
       unfold String_as_OT.eq in cmp_n. subst.
       destruct (N_as_OT.compare_spec t1 t2); [|crush|crush].
       subst.
       constructor. cbv. f_equal.
       apply proof_irrelevance.
     Qed.
  End Variable_as_OT.

  Module VariableSet.
    Include MSetAVL.Make(Variable_as_OT).
    Include MSetDecide.Decide.

    Definition disjoint (a b : t) := is_empty (inter a b).
    Definition Disjoint (a b : t) : Prop := Empty (inter a b).

    Lemma disjoint_spec (a b : t) : disjoint a b = true <-> Disjoint a b.
    Proof.
      unfold disjoint, Disjoint.
      rewrite is_empty_spec.
      reflexivity.
    Qed.

    Global Instance Disjoint_m : Proper (Equal ==> Equal ==> iff) Disjoint.
    Proof.
      unfold Disjoint.
      intros x y Hxy a b Hab.
      setoid_rewrite <- Hxy.
      setoid_rewrite <- Hab.
      reflexivity.
    Qed.

    Global Instance disjoint_m : Proper (Equal ==> Equal ==> Logic.eq) disjoint.
    Proof.
      unfold disjoint.
      intros x y Hxy a b Hab.
      setoid_rewrite <- Hxy.
      setoid_rewrite <- Hab.
      reflexivity.
    Qed.

    Lemma Disjoint_sym a b : Disjoint a b -> Disjoint b a.
    Proof. unfold Disjoint. fsetdec. Qed.
    
    Add Parametric Relation : t Disjoint
      symmetry proved by Disjoint_sym
      as Disjoint_rel.

    Global Instance dec_vs_In (v : variable) (a : t) : DecProp (In v a).
    Proof.
      destruct (VariableSet.mem v a) eqn:E.
      - left. now apply VariableSet.mem_spec.
      - right. intros contra. apply VariableSet.mem_spec in contra.
        congruence.
    Qed.

    Global Instance dec_vs_disjoint (a b : VariableSet.t) : DecProp (VariableSet.Disjoint a b).
    Proof.
      destruct (VariableSet.disjoint a b) eqn:E.
      - left. now apply VariableSet.disjoint_spec.
      - right. intros contra. apply VariableSet.disjoint_spec in contra.
        congruence.
    Qed.

    Global Instance dec_vs_subset (a b : VariableSet.t) : DecProp (VariableSet.Subset a b).
    Proof.
      destruct (VariableSet.subset a b) eqn:E.
      - left. now apply VariableSet.subset_spec.
      - right. intros contra. apply VariableSet.subset_spec in contra.
        congruence.
    Qed.

    Global Instance dec_vs_Equal (a b : VariableSet.t) : DecProp (VariableSet.Equal a b).
    Proof.
      destruct (VariableSet.equal a b) eqn:E.
      - left. now apply VariableSet.equal_spec.
      - right. intros contra. apply VariableSet.equal_spec in contra.
        congruence.
    Qed.

    (* This is the version with nice recursion, which we want for inductive proofs, but is not tail-recursive *)
    Equations of_list : list variable -> t := {
      | [] => empty
      | (x :: xs) => add x (of_list xs)
    }.

    (* This is the tail-recursive version, which we want for performance, but is annoying in proofs.
       TODO: Profile and swap to this if we need it
     *)
    (* Definition of_list l := fold_right add empty l. *)

    Lemma In_of_list {a l} :
      List.In a l ->
      In a (VariableSet.of_list l).
    Proof.
      induction l; intros H; inv H.
      all: simp of_list.
      - fsetdec.
      - insterU IHl. fsetdec.
    Qed.

    Lemma subset_of_list {l1 l2} :
      list_subset l1 l2 ->
      VariableSet.Subset (VariableSet.of_list l1) (VariableSet.of_list l2).
    Proof.
      revert l2. induction l1; intros l2 Hsub.
      - inv Hsub. fsetdec.
      - inv Hsub. fold (list_subset l1 l2) in *.
        simp of_list.
	insterU IHl1.
	apply In_of_list in H1.
	fsetdec.
    Qed.

    Global Instance of_list_subset :
      Proper
        (@list_subset variable ==> VariableSet.Subset)
        VariableSet.of_list.
    Proof. intros l1 l2 Hsub. now apply subset_of_list. Qed.

    Module Notations.
      Infix "∪" := union (at level 20, right associativity) : verilog_scope.
      Infix "∩" := inter (at level 20, right associativity) : verilog_scope.
      Infix "⊆" := Subset (at level 20, right associativity) : verilog_scope.
      Infix "∈" := In (at level 20, right associativity) : verilog_scope.
      Notation "{ }" := empty : verilog_scope.
      Notation "{ v }" := (singleton v) : verilog_scope.
    End Notations.

    Lemma subset_singleton_iff x s : Subset (singleton x) s <-> In x s.
    Proof. split; fsetdec. Qed.

    Ltac setdec :=
      unfold Disjoint in *;
      (* setdec can't handle Subset under binders, so we simplify some special cases.
         (Mostly used for the (~ Subset _ _) case)
      *)
      repeat match goal with
             | H : context[Subset (singleton _) _] |- _ => setoid_rewrite subset_singleton_iff in H
             | |- context[Subset (singleton _) _] => setoid_rewrite subset_singleton_iff
	     end;
      fsetdec.
  End VariableSet.

  Definition variable_of_decl (decl : variable_declaration) : variable :=
    {| varName := varDeclName decl
    ; varType := varDeclWidth decl
    ; varTypeWf := vector_declaration_width_gt _
    |}.

  Equations inputs_of_decls : list variable_declaration -> list variable := {
    | [] => []
    | d::ds with varDeclPort d => {
      | Some PortIn => variable_of_decl d :: inputs_of_decls ds
      | _ => inputs_of_decls ds
    }
  }.

  Equations outputs_of_decls : list variable_declaration -> list variable := {
    | [] => []
    | d::ds with varDeclPort d => {
      | Some PortOut => variable_of_decl d :: outputs_of_decls ds
      | _ => outputs_of_decls ds
    }
  }.

  Section show.
    Local Open Scope string.
    Import ShowNotation.

    Global Instance variable_Show : Show variable :=
      { show v := (varName v ++ "[" ++ to_string (N.to_nat (varType v - 1)) ++ ":0]")%string } .

    Global Instance arithmeticop_Show : Show arithmeticop :=
      { show u :=
          match u with
          | ArithmeticPlus => "+"
          | ArithmeticMinus => "-"
          | ArithmeticStar => "*"
          (* | BinarySlash => "/" *)
          (* | BinaryPercent => "%" *)
          (* | BinaryExponent => "**" *)
          end
      }.

    Global Instance shiftop_Show : Show shiftop :=
      { show u :=
          match u with
          | BinaryShiftRight => ">>"
          | BinaryShiftLeft => "<<"
          (* | BinaryShiftRightArithmetic => ">>>" *)
          | BinaryShiftLeftArithmetic => "<<<"
          end
      }.

    Global Instance bitwiseop_Show : Show bitwiseop :=
      { show u :=
          match u with
          | BinaryBitwiseAnd => "&"
          | BinaryBitwiseOr => "|"
          | BinaryBitwiseXor => "^"
          end
      }.

    Global Instance unaryop_Show : Show unaryop :=
      { show u :=
          match u with
          | UnaryPlus => "+"
          | UnaryNot => "~"
          (* | UnaryMinus => "-" *)
          end
      }.
  End show.

End VerilogCommon.

Module Verilog.
  Include VerilogCommon.

  (* Definition static_value {w} (expr : Verilog.expression w) : option (BV.bitvector w) :=
   *   match expr with
   *   | Verilog.IntegerLiteral _ val => Some val
   *   | _ => None
   *   end.
   * 
   * Definition statically_in_bounds {w} (max_val : N) (expr : Verilog.expression w) : Prop :=
   *   opt_prop (fun v => (BV.to_N v) < max_val)%N (static_value expr) \/ ((2 ^ w) < max_val)%N. *)

  (* Need to use these in the definition of expression below, but it created a cycle.
     Can we define mutually inductive/recursive datatypes/functions?
     We should probably define it as an inductive instead

     Inductive statically_in_bounds (max_val : N) (expr : Verilog.expresssion w) : Prop
     | statically_in_bounds_size :
       (2 ^ w < max_val)%N -> statically_in_bounds max_val expr
     | statically_in_bounds_constant :
       (BV.to_N bv < max_val)%N -> statically_in_bounds max_val (IntegerLiteral w bv)

     but how to define this mutually with expression? if I just add it in a `with` clause I get

       Parameters should be syntactically the same for each inductive type.
       Type "expression" has no parameters
       but type "statically_in_bounds" has parameters
       "(max_val : N) (expr : Verilog.expresssion w)".

     and even if I try to eliminate the parameters like this:

       with statically_in_bounds : N -> expression 1 -> Prop :=
          | statically_in_bounds_size :
            (2 ^ w < max_val)%N -> statically_in_bounds max_val expr
          | statically_in_bounds_constant :
            (BV.to_N bv < max_val)%N -> statically_in_bounds max_val (IntegerLiteral w bv)

     I get:
       
       The reference expression was not found in the current environment.
   *)

  Inductive expression : N -> Type :=
  | ArithmeticOp {w} (op : arithmeticop) : expression w -> expression w -> expression w
  | BitwiseOp {w} (op : bitwiseop) : expression w -> expression w -> expression w
  | ShiftOp {w1 w2}
    (op : shiftop)
    (lhs : expression w1)
    (rhs : expression w2)
    (wf_lhs : (w1 > 0)%N)
    (wf_rhs : (w2 > 0)%N)
    : expression w1
  | UnaryOp {w} (op : unaryop) : expression w -> expression w
  | Conditional {w_val w_cond : N} : expression w_cond -> expression w_val -> expression w_val -> expression w_val
  | RangeSelect {w_val}
    (val : expression w_val)
    (hi lo : N)
    (wf_hi : (hi < w_val)%N)
    (wf_lo : (lo <= hi)%N)
    : expression (1 + hi - lo)%N
  | BitSelect_const {w_val}
    (val : expression w_val)
    (sel : N)
    (wf : (sel < w_val)%N)
    : expression 1
  | BitSelect_width {w_val w_sel}
    (val : expression w_val)
    (sel : expression w_sel)
    (wf_val : (2 ^ w_sel <= w_val)%N)
    (wf_nonzero : (w_sel > 0)%N)
    : expression 1
  (* We break up the concatenation to make the type more convenient *)
  | Concatenation {w1 w2} (e1 : expression w1) (e2 : expression w2) : expression (w1 + w2)
  | Replication {w} (count : N) (e : expression w) : expression (count * w)
  | IntegerLiteral (w : N) : BV.bitvector w -> expression w
  | NamedExpression (var : Verilog.variable) : expression (Verilog.varType var)
  | Resize {w_from} (w_to : N) (from : expression w_from) (wf : (w_to > 0)%N) : expression w_to
  .

  Definition expr_type {w} (e : expression w) := w.

  Inductive statement :=
  | BlockingAssign (lhs : Verilog.variable) (rhs : expression (Verilog.varType lhs))
  .

  Inductive module_item :=
  | AlwaysComb : statement -> module_item
  .

  (** Verilog modules *)
  Record vmodule :=
    MkMod
      { modName : name
      ; modVariableDecls : list variable_declaration
      ; modBody : list module_item
      }
  .

  Definition modVariables (v : vmodule) : list variable :=
    map variable_of_decl (modVariableDecls v).

  Module Notations.
    Notation "[ hi .: lo ]" :=
      (Vector hi lo)
        (format "[ hi '.:' lo ]").
  End Notations.

  Definition module_inputs (v : Verilog.vmodule) : list variable :=
    inputs_of_decls (modVariableDecls v).

  Definition module_outputs (v : Verilog.vmodule) : list variable :=
    outputs_of_decls (modVariableDecls v).

  Lemma module_input_in_vars v :
    list_subset (Verilog.module_inputs v) (Verilog.modVariables v).
  Proof.
    apply Forall_forall.
    unfold Verilog.module_inputs, Verilog.modVariables.
    generalize (modVariableDecls v). intros decls var Hvar_in. 
    funelim (inputs_of_decls decls); rewrite <- Heqcall in *; crush.
  Qed.

  Lemma module_outputs_in_vars v :
    list_subset (Verilog.module_outputs v) (Verilog.modVariables v).
  Proof.
    apply Forall_forall.
    unfold Verilog.module_outputs, Verilog.modVariables.
    generalize (modVariableDecls v). intros decls var Hvar_in. 
    funelim (outputs_of_decls decls); rewrite <- Heqcall in *; crush.
  Qed.

  Lemma module_inputs_same v1 v2 :
    modVariableDecls v1 = modVariableDecls v2 ->
    module_inputs v1 = module_inputs v2.
  Proof. unfold module_inputs. crush. Qed.

  Lemma module_outputs_same v1 v2 :
    modVariableDecls v1 = modVariableDecls v2 ->
    module_outputs v1 = module_outputs v2.
  Proof. unfold module_outputs. crush. Qed.

  Lemma module_variables_same v1 v2 :
    modVariableDecls v1 = modVariableDecls v2 ->
    modVariables v1 = modVariables v2.
  Proof. unfold modVariables. crush. Qed.

  Definition var_names : list variable -> list name :=
    map varName.

  Import Verilog.VariableSet.Notations.
  Local Open Scope verilog.

  Fixpoint expr_reads {w} (e : Verilog.expression w) : VariableSet.t :=
    match e with
    | (Verilog.UnaryOp op operand) => expr_reads operand
    | (Verilog.ArithmeticOp op lhs rhs) => expr_reads lhs ∪ expr_reads rhs
    | (Verilog.BitwiseOp op lhs rhs) => expr_reads lhs ∪ expr_reads rhs
    | (Verilog.ShiftOp op lhs rhs _ _) => expr_reads lhs ∪ expr_reads rhs
    | (Verilog.Conditional cond tBranch fBranch) => expr_reads cond ∪ expr_reads tBranch ∪ expr_reads fBranch
    | (Verilog.RangeSelect vec hi lo _ _) => expr_reads vec
    | (Verilog.BitSelect_width vec idx _ _) => expr_reads vec ∪ expr_reads idx
    | (Verilog.BitSelect_const vec idx _) => expr_reads vec
    | (Verilog.Resize t expr _) => expr_reads expr
    | (Verilog.Concatenation e1 e2) => expr_reads e1 ∪ expr_reads e2
    | (Verilog.Replication _ e) => expr_reads e
    | (Verilog.IntegerLiteral _ val) => VariableSet.empty
    | (Verilog.NamedExpression var) => { var }
    end.

  Definition statement_reads (s : Verilog.statement) : VariableSet.t :=
    match s with
    | (Verilog.BlockingAssign lhs rhs) => expr_reads rhs  (* ONLY looking at rhs here *)
    end.

  Definition statement_writes (s : Verilog.statement) : VariableSet.t :=
    match s with
    | (Verilog.BlockingAssign lhs rhs) => { lhs } (* ONLY looking at lhs here *)
    end.

  Definition module_item_reads (mi : Verilog.module_item) : VariableSet.t :=
    match mi with
    | (Verilog.AlwaysComb stmt) => statement_reads stmt
    end.

  Definition module_item_writes (mi : Verilog.module_item) : VariableSet.t :=
    match mi with
    | (Verilog.AlwaysComb stmt) => statement_writes stmt
    end.

  Fixpoint module_body_reads (mis : list Verilog.module_item) : VariableSet.t :=
    match mis with
    | [] => {}
    | (hd :: tl) => module_item_reads hd ∪ module_body_reads tl
    end.

  Fixpoint module_body_writes (mis : list Verilog.module_item) : VariableSet.t :=
    match mis with
    | [] => {}
    | (hd :: tl) => module_item_writes hd ∪ module_body_writes tl
    end.
End Verilog.

Module RawVerilog.
  Include VerilogCommon.

  Inductive expression : Type :=
  | ArithmeticOp (op : arithmeticop) (lhs rhs : expression)
  | BitwiseOp (op : bitwiseop) (lhs rhs : expression)
  | ShiftOp (op : shiftop) (lhs rhs : expression)
  | UnaryOp (op : unaryop) (expr : expression)
  | Conditional (cond ifT ifF : expression)
  | RangeSelect (vec hi lo : expression)
  | BitSelect (vec idx : expression)
  (* We break up the concatenation to make the type more convenient *)
  | Concatenation (lhs rhs : expression)
  | Replication (count : N) (expr : expression)
  | IntegerLiteral (val : RawBV.bitvector)
  | NamedExpression (var : variable)
  | Resize (to : N) (expr : expression)
  .

  Inductive statement :=
  | BlockingAssign (lhs rhs : expression)
  .

  Inductive module_item :=
  | AlwaysComb : statement -> module_item
  .

  (** Verilog modules *)
  Record vmodule :=
    MkMod
      { modName : name
      ; modVariableDecls : list variable_declaration
      ; modBody : list module_item
      }
  .

  Definition modVariables (v : vmodule) : list variable :=
    map variable_of_decl (modVariableDecls v).

  Definition module_inputs (v : vmodule) : list variable :=
    inputs_of_decls (modVariableDecls v).

  Definition module_outputs (v : vmodule) : list variable :=
    outputs_of_decls (modVariableDecls v).

  Lemma module_input_in_vars v :
    list_subset (module_inputs v) (modVariables v).
  Proof.
    apply List.Forall_forall.
    unfold module_inputs, modVariables.
    generalize (modVariableDecls v). intros decls var Hvar_in. 
    funelim (inputs_of_decls decls); rewrite <- Heqcall in *; crush.
  Qed.

  Lemma module_outputs_in_vars v :
    list_subset (module_outputs v) (modVariables v).
  Proof.
    apply List.Forall_forall.
    unfold module_outputs, modVariables.
    generalize (modVariableDecls v). intros decls var Hvar_in. 
    funelim (outputs_of_decls decls); rewrite <- Heqcall in *; crush.
  Qed.

End RawVerilog.

Module Typecheck.

Definition transf := sum string.

Equations cast_width {w1} (err : string) (w2 : N) (e : Verilog.expression w1)
  : transf (Verilog.expression w2) :=
| err, w2, e with (N.eq_dec w1 w2) => {
  | left eq_refl => inr e
  | right _ => inl (err
    ++ " (Tried to use expression of width "
    ++ to_string (N.to_nat w1) ++ " as width " ++ to_string (N.to_nat w2) ++ ")")%string
}.

Equations tc_expr (expr : RawVerilog.expression) : transf { w & Verilog.expression w } := {
| RawVerilog.ArithmeticOp op lhs rhs =>
  let* (w_lhs; t_lhs) := tc_expr lhs in
  let* (w_rhs; t_rhs) := tc_expr rhs in
  let* t_rhs' := cast_width ("Different widths in " ++ to_string op) w_lhs t_rhs in
  inr (_; Verilog.ArithmeticOp op t_lhs t_rhs')
| RawVerilog.BitwiseOp op lhs rhs =>
  let* (w_lhs; t_lhs) := tc_expr lhs in
  let* (w_rhs; t_rhs) := tc_expr rhs in
  let* t_rhs' := cast_width ("Different widths in " ++ to_string op) w_lhs t_rhs in
  inr (_; Verilog.BitwiseOp op t_lhs t_rhs')
| RawVerilog.ShiftOp op lhs rhs =>
  let* (w_lhs; t_lhs) := tc_expr lhs in
  let* wf_lhs := assert_dec (w_lhs > 0)%N "0 width not allowed in shift"%string in
  let* (w_rhs; t_rhs) := tc_expr rhs in
  let* wf_rhs := assert_dec (w_rhs > 0)%N "0 width not allowed in shift"%string in
  inr (_; Verilog.ShiftOp op t_lhs t_rhs wf_lhs wf_rhs)
| RawVerilog.UnaryOp op expr =>
  let* (w_expr; t_expr) := tc_expr expr in
  inr (_; Verilog.UnaryOp op t_expr)
| RawVerilog.Conditional cond ifTrue ifFalse =>
  let* (w_cond; t_cond) := tc_expr cond in
  let* (w_ifTrue; t_ifTrue) := tc_expr ifTrue in
  let* (w_ifFalse; t_ifFalse) := tc_expr ifFalse in
  let* t_ifFalse' := cast_width "Different widths in conditional" w_ifTrue t_ifFalse in
  inr (_; Verilog.Conditional t_cond t_ifTrue t_ifFalse')
| RawVerilog.RangeSelect vec (RawVerilog.IntegerLiteral hi_lit) (RawVerilog.IntegerLiteral lo_lit) =>
  let* (w_vec; t_vec) := tc_expr vec in
  let hi := RawBV.to_N hi_lit in
  let lo := RawBV.to_N lo_lit in
  let* wf_hi := assert_dec _ "High bound of range select must be in-bounds"%string in
  let* wf_lo := assert_dec _ "Low bound of range select must be in-bounds"%string in
  inr (_; Verilog.RangeSelect t_vec hi lo wf_hi wf_lo) ;
| RawVerilog.RangeSelect vec _ _ =>
  raise "Range select must have literal bounds"%string ;
| RawVerilog.BitSelect vec idx =>
  let* (w_vec; t_vec) := tc_expr vec in
  match idx with
  | RawVerilog.IntegerLiteral lit =>
    let* wf := assert_dec
      (BV.to_N (BV.of_bits lit) < w_vec)%N
      ("bit-select index out of bounds (literal)")%string in
    inr (1%N; Verilog.BitSelect_const t_vec (BV.to_N (BV.of_bits lit)) wf)
  | _ =>
    let* (w_idx; t_idx) := tc_expr idx in
    let* wf_value := assert_dec _ "bit-select index out of bounds (width)"%string in
    let* wf_nonzero := assert_dec _ "bit-select index is zero-width"%string in
    inr (1%N; Verilog.BitSelect_width t_vec t_idx wf_value wf_nonzero)
  end
| RawVerilog.Concatenation lhs rhs =>
  let* (w_lhs; t_lhs) := tc_expr lhs in
  let* (w_rhs; t_rhs) := tc_expr rhs in
  inr (_; Verilog.Concatenation t_lhs t_rhs)
| RawVerilog.Replication count expr =>
  let* (w_expr; t_expr) := tc_expr expr in
  inr (_; Verilog.Replication count t_expr)
| RawVerilog.IntegerLiteral bits =>
  inr (_; Verilog.IntegerLiteral _ (BV.of_bits bits))
| RawVerilog.NamedExpression var =>
  inr (_; Verilog.NamedExpression var)
| RawVerilog.Resize to expr =>
  let* (w_expr; t_expr) := tc_expr expr in
  let* wf := assert_dec (to > 0)%N "Cannot resize to 0"%string in
  inr (_; Verilog.Resize to t_expr wf)
}.

Equations tc_statement : RawVerilog.statement -> transf Verilog.statement := {
| RawVerilog.BlockingAssign (RawVerilog.NamedExpression var) rhs =>
  let* (w_rhs; t_rhs) := tc_expr rhs in
  let* t_rhs' := cast_width "Different widths in blocking assign" (Verilog.varType var) t_rhs in
  inr (Verilog.BlockingAssign var t_rhs')
| RawVerilog.BlockingAssign lhs rhs =>
  inl "Unsupported assignment target"%string
}
.

Equations tc_module_item : RawVerilog.module_item -> transf Verilog.module_item := {
| RawVerilog.AlwaysComb stmt =>
  let* t_stmt := tc_statement stmt in
  inr (Verilog.AlwaysComb t_stmt)
}.

Equations tc_module_item_lst : list RawVerilog.module_item -> transf (list Verilog.module_item) := {
| [] => inr []
| (mi :: mis) =>
  let* t_mi := tc_module_item mi in
  let* t_mis := tc_module_item_lst mis in
  inr (t_mi :: t_mis)
}.

Definition tc_vmodule (m : RawVerilog.vmodule) : transf Verilog.vmodule :=
  trace ("Typecheck " ++ RawVerilog.modName m) (
    let* t_modBody := tc_module_item_lst (RawVerilog.modBody m) in
    inr {|
        Verilog.modName := RawVerilog.modName m;
        Verilog.modVariableDecls := RawVerilog.modVariableDecls m;
        Verilog.modBody := t_modBody
    |}
  )
.
End Typecheck.
