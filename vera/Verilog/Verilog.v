From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import BinNums.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import ProofIrrelevance.
From Stdlib Require Import Structures.Orders.
From Stdlib Require Import Structures.OrdersEx.
From Stdlib Require Import Structures.OrdersAlt.
From Stdlib Require Import RelationPairs.
From Stdlib Require MSets.
From Stdlib Require Import FMapAVL.
From Stdlib Require Import FMapFacts.
From Stdlib Require Import MSetInterface.

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
From vera Require Import Variables.

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

Module Notations.
  Import LocationSet.
  Infix "∪" := union (at level 20, right associativity) : verilog_scope.
  Infix "∩" := inter (at level 20, right associativity) : verilog_scope.
  Infix "⊆" := Subset (at level 20, right associativity) : verilog_scope.
  Infix "∈" := In (at level 20, right associativity) : verilog_scope.
  Notation "{ }" := empty : verilog_scope.
  Notation "{ v }" := (singleton v) : verilog_scope.
End Notations.

Import Notations.

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

  Definition name := string.

  Definition variable_of_decl (decl : variable_declaration) : Var.t :=
    {| Var.varName := varDeclName decl
    ; Var.varType := varDeclWidth decl
    ; Var.varTypeWf := vector_declaration_width_gt _
    |}.

  Equations inputs_of_decls : list variable_declaration -> list Var.t := {
    | [] => []
    | d::ds with varDeclPort d => {
      | Some PortIn => variable_of_decl d :: inputs_of_decls ds
      | _ => inputs_of_decls ds
    }
  }.

  Equations outputs_of_decls : list variable_declaration -> list Var.t := {
    | [] => []
    | d::ds with varDeclPort d => {
      | Some PortOut => variable_of_decl d :: outputs_of_decls ds
      | _ => outputs_of_decls ds
    }
  }.

  Section show.
    Local Open Scope string.
    Import ShowNotation.

    Global Instance variable_Show : Show Var.t :=
      { show v := (Var.varName v ++ "[" ++ to_string (N.to_nat (Var.varType v - 1)) ++ ":0]")%string } .

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
  | NamedExpression (var : Var.t) : expression (Var.varType var)
  | Resize {w_from} (w_to : N) (from : expression w_from) (wf : (w_to > 0)%N) : expression w_to
  .

  Definition expr_type {w} (e : expression w) := w.

  Inductive assign_target : N -> Type :=
  | AssignVar (var : Var.t) : assign_target (Var.varType var)
  | AssignBit (loc : Location.t) (wf : (Location.idx loc < Var.varType (Location.var loc))%N) : assign_target 1
  .

  Inductive statement :=
  | BlockingAssign {w} (lhs : assign_target w) (rhs : expression w)
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

  Definition modVariables (v : vmodule) : list Var.t :=
    map variable_of_decl (modVariableDecls v).

  Definition module_inputs (v : Verilog.vmodule) : list Var.t :=
    inputs_of_decls (modVariableDecls v).

  Definition module_outputs (v : Verilog.vmodule) : list Var.t :=
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

  Definition var_names : list Var.t -> list name :=
    map Var.varName.

  Local Open Scope verilog.

  Fixpoint expr_reads {w} (e : Verilog.expression w) : LocationSet.t :=
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
    | (Verilog.IntegerLiteral _ val) => { }
    | (Verilog.NamedExpression var) => LocationSet.of_variable var
    end.

  Definition assign_target_writes {w} (a : assign_target w) : LocationSet.t :=
    match a with
    | Verilog.AssignVar v => LocationSet.of_variable v
    | Verilog.AssignBit loc _ => { loc }
    end.

  Definition statement_reads (s : Verilog.statement) : LocationSet.t :=
    match s with
    | (Verilog.BlockingAssign lhs rhs) => expr_reads rhs  (* ONLY looking at rhs here *)
    end.

  Definition statement_writes (s : Verilog.statement) : LocationSet.t :=
    match s with
    | (Verilog.BlockingAssign lhs rhs) => assign_target_writes lhs (* ONLY looking at lhs here *)
    end.

  Definition module_item_reads (mi : Verilog.module_item) : LocationSet.t :=
    match mi with
    | (Verilog.AlwaysComb stmt) => statement_reads stmt
    end.

  Definition module_item_writes (mi : Verilog.module_item) : LocationSet.t :=
    match mi with
    | (Verilog.AlwaysComb stmt) => statement_writes stmt
    end.

  Fixpoint module_body_reads (mis : list Verilog.module_item) : LocationSet.t :=
    match mis with
    | [] => {}
    | (hd :: tl) => module_item_reads hd ∪ module_body_reads tl
    end.

  Fixpoint module_body_writes (mis : list Verilog.module_item) : LocationSet.t :=
    match mis with
    | [] => {}
    | (hd :: tl) => module_item_writes hd ∪ module_body_writes tl
    end.

  Lemma empty_in_bounds : LocationSet.InBounds { }.
  Proof. intros loc Hin. exfalso. eapply LocationSet.empty_spec. eassumption. Qed.

  Lemma expr_reads_in_bounds {w} (e : Verilog.expression w) :
    LocationSet.InBounds (expr_reads e).
  Proof.
    induction e; simpl.
    all: repeat apply LocationSet.union_in_bounds.
    all: auto using LocationSet.of_variable_in_bounds, empty_in_bounds.
  Qed.

  Lemma statement_reads_in_bounds s : LocationSet.InBounds (statement_reads s).
  Proof. destruct s; apply expr_reads_in_bounds. Qed.

  Lemma assign_target_writes_in_bounds w a : LocationSet.InBounds (assign_target_writes (w:=w) a).
  Proof.
    destruct a.
    - apply LocationSet.of_variable_in_bounds.
    - apply LocationSet.singleton_in_bounds. exact wf.
  Qed.
  
  Lemma statement_writes_in_bounds s : LocationSet.InBounds (statement_writes s).
  Proof. destruct s; apply assign_target_writes_in_bounds. Qed.

  Lemma module_item_reads_in_bounds mi : LocationSet.InBounds (module_item_reads mi).
  Proof. destruct mi; apply statement_reads_in_bounds. Qed.

  Lemma module_item_writes_in_bounds mi : LocationSet.InBounds (module_item_writes mi).
  Proof. destruct mi; apply statement_writes_in_bounds. Qed.

  Lemma module_body_reads_in_bounds mis : LocationSet.InBounds (module_body_reads mis).
  Proof.
    induction mis; simpl.
    - apply empty_in_bounds.
    - apply LocationSet.union_in_bounds; auto using module_item_reads_in_bounds.
  Qed.

  Lemma module_body_writes_in_bounds mis : LocationSet.InBounds (module_body_writes mis).
  Proof.
    induction mis; simpl.
    - apply empty_in_bounds.
    - apply LocationSet.union_in_bounds; auto using module_item_writes_in_bounds.
  Qed.
End Verilog.

#[global] Hint Resolve
  Verilog.empty_in_bounds
  Verilog.expr_reads_in_bounds
  Verilog.statement_reads_in_bounds
  Verilog.statement_writes_in_bounds
  Verilog.module_item_reads_in_bounds
  Verilog.module_item_writes_in_bounds
  Verilog.module_body_reads_in_bounds
  Verilog.module_body_writes_in_bounds
  LocationSet.of_varset_in_bounds
  LocationSet.of_variable_in_bounds
  LocationSet.union_in_bounds
  : core.

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
  | NamedExpression (var : Var.t)
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

  Definition modVariables (v : vmodule) : list Var.t :=
    map variable_of_decl (modVariableDecls v).

  Definition module_inputs (v : vmodule) : list Var.t :=
    inputs_of_decls (modVariableDecls v).

  Definition module_outputs (v : vmodule) : list Var.t :=
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
  let* t_rhs' := cast_width "Different widths in blocking assign" (Var.varType var) t_rhs in
  inr (Verilog.BlockingAssign (Verilog.AssignVar var) t_rhs')
| RawVerilog.BlockingAssign (RawVerilog.BitSelect (RawVerilog.NamedExpression var) (RawVerilog.IntegerLiteral idx_bits)) rhs =>
  let* (w_rhs; t_rhs) := tc_expr rhs in
  let* t_rhs' := cast_width "Different widths in blocking assign" 1 t_rhs in
  let idx := RawBV.to_N idx_bits in
  let* wf := assert_dec _ "Bit-select index (lhs) out of bounds"%string in
  inr (Verilog.BlockingAssign (Verilog.AssignBit (Location.Mk var idx) wf) t_rhs')
| RawVerilog.BlockingAssign (RawVerilog.Concatenation _ _) rhs =>
  inl "TODO: Assign to concatenation"%string
| RawVerilog.BlockingAssign (RawVerilog.RangeSelect _ _ _) rhs =>
  inl "TODO: Assign to range-select"%string
| RawVerilog.BlockingAssign (RawVerilog.BitSelect _ _) rhs =>
  inl "Unsupported assignment target (invalid bit-select)"%string
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
