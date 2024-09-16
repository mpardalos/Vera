From vera Require Import Verilog.
From vera Require Import Netlist.
From vera Require Import Bitvector.
From vera Require Import Common.
Import CommonNotations.
From vera Require EnvStack.

From Coq Require Import ZArith.
From Coq Require Import BinNums.
From Coq Require Import BinIntDef.
From Coq Require Import String.
From Coq Require Import FSets.
From Coq Require Import Psatz.

Require Import List.
Import ListNotations.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.MonadState.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Structures.Monoid.
From ExtLib Require Import Data.Monads.StateMonad.
From ExtLib Require Import Data.Monads.EitherMonad.
From ExtLib Require Import Data.List.
From ExtLib Require Import Data.String.
Import MonadNotation.
Import FunctorNotation.
Open Scope monad_scope.
Require Import Program.

From Equations Require Import Equations.

Record transf_state :=
  TransfState
    { nextName : name
    ; nameMap : StrMap.t name
    ; vars : NameMap.t Netlist.nltype
    ; cells : list Netlist.cell
    ; substitutionsBlocking : EnvStack.t Netlist.input
    ; substitutionsNonblocking : EnvStack.t Netlist.input
    }.

Definition transf : Type -> Type := stateT transf_state (sum string).

Instance Monad_transf : Monad transf := Monad_stateT transf_state (Monad_either string).

Let run_transf_test {T} (a : transf T) :=
      runStateT
        a
        {| nextName := 1%positive
        ; nameMap := StrMap.empty name
        ; vars := NameMap.empty _
        ; cells := []
        ; substitutionsBlocking := EnvStack.empty _
        ; substitutionsNonblocking := EnvStack.empty _
        |}.

Definition fresh_name : transf name :=
  modify (fun s =>
            {| nextName := Pos.succ (nextName s)
            ; nameMap := nameMap s
            ; vars := vars s
            ; cells := cells s
            ; substitutionsBlocking := substitutionsBlocking s
            ; substitutionsNonblocking := substitutionsNonblocking s
            |}) ;;
  gets nextName .

Definition transfer_name (vname : string) : transf name :=
  names <- gets nameMap ;;
  match StrMap.find vname names with
  | Some n => ret n
  | None =>
      n <- fresh_name ;;
      modify (fun s =>
                {| nextName := nextName s
                ; nameMap := StrMap.add vname n (nameMap s)
                ; vars := vars s
                ; cells := cells s
                ; substitutionsBlocking := substitutionsBlocking s
                ; substitutionsNonblocking := substitutionsNonblocking s
                |}
        ) ;;
      ret n
  end.

Definition put_var (varName : name) (varType : Netlist.nltype) : transf () :=
  modify (fun s =>
            {| nextName := nextName s
            ; nameMap := nameMap s
            ; vars := NameMap.add varName varType (vars s)
            ; cells := cells s
            ; substitutionsBlocking := substitutionsBlocking s
            ; substitutionsNonblocking := substitutionsNonblocking s
            |}) ;;
  ret ()
.

Definition put_cells (cs : list Netlist.cell) : transf () :=
  modify (fun s =>
            {| nextName := nextName s
            ; nameMap := nameMap s
            ; vars := vars s
            ; cells := cells s ++ cs
            ; substitutionsBlocking := substitutionsBlocking s
            ; substitutionsNonblocking := substitutionsNonblocking s
            |}) ;;
  ret ()
.

Definition set_substitution_blocking (lhs : name) (rhs : Netlist.input) : transf () :=
  modify (fun s =>
            {| nextName := nextName s
            ; nameMap := nameMap s
            ; vars := vars s
            ; cells := cells s
            ; substitutionsBlocking := EnvStack.add lhs rhs (substitutionsBlocking s)
            ; substitutionsNonblocking := substitutionsNonblocking s
            |}) ;;
  ret ()
.

Definition set_substitution_nonblocking (lhs : name) (rhs : Netlist.input) : transf () :=
  modify (fun s =>
            {| nextName := nextName s
            ; nameMap := nameMap s
            ; vars := vars s
            ; cells := cells s
            ; substitutionsBlocking := substitutionsBlocking s
            ; substitutionsNonblocking := EnvStack.add lhs rhs (substitutionsNonblocking s)
            |}) ;;
  ret ()
.

Definition push_block : transf () :=
  modify (fun s =>
            {| nextName := nextName s
            ; nameMap := nameMap s
            ; vars := vars s
            ; cells := cells s
            ; substitutionsBlocking := EnvStack.push (substitutionsBlocking s)
            ; substitutionsNonblocking := EnvStack.push (substitutionsNonblocking s)
            |}) ;;
  ret ()
.

Definition pop_block : transf (NameMap.t Netlist.input * NameMap.t Netlist.input) :=
  s <- get ;;
  let (mBlockingEnv, substitutionsBlocking') := EnvStack.pop (substitutionsBlocking s) in
  let (mNonblockingEnv, substitutionsNonblocking') := EnvStack.pop (substitutionsNonblocking s) in
  match mBlockingEnv, mNonblockingEnv with
  | Some benv, Some nbenv =>
      modify (fun s =>
                {| nextName := nextName s
                ; nameMap := nameMap s
                ; vars := vars s
                ; cells := cells s
                ; substitutionsBlocking := substitutionsBlocking'
                ; substitutionsNonblocking := substitutionsNonblocking'
                |}) ;;
      ret (benv, nbenv)
  | _, _ =>
      raise "pop_block with an empty stack"%string
  end
.

Definition transfer_scoped {A} (f : transf A) : transf (A * (NameMap.t Netlist.input * NameMap.t Netlist.input)) :=
  push_block ;;
  result <- f ;;
  assigns <- pop_block ;;
  ret (result, assigns)
.

Program Definition fresh (t : Netlist.nltype) : transf {v : Netlist.variable | Netlist.varType v = t} :=
  name <- fresh_name ;;
  put_var name t ;;
  ret {! {| Netlist.varType := t; Netlist.varName := name |} }
.

Definition transfer_type (type : Verilog.vtype) : Netlist.nltype :=
  (* Probably wrong but good enough for now*)
  match type with
  | Verilog.Logic N0 N0 => (Netlist.Logic 1)
  | Verilog.Logic (Npos n) N0 => (Netlist.Logic (n + 1))
  | Verilog.Logic N0 (Npos n) => (Netlist.Logic (n + 1))
  | Verilog.Logic (Npos n1) (Npos n2) => (Netlist.Logic (n1 - n2 + 1))
  end
.

Definition transfer_variables (vars : list Verilog.variable) : transf () :=
  mapT (fun v =>
          name <- transfer_name (Verilog.varName v) ;;
          put_var name (transfer_type (Verilog.varType v))
    ) vars ;;
  ret ()
.

Definition transfer_ports (ports : list Verilog.port) : transf (list (name * port_direction)) :=
  mapT (fun p =>
          name <- transfer_name (Verilog.portName p) ;;
          ret (name, Verilog.portDirection p)
    ) ports
.

Definition unsupported_expression_error : string := "Unsupported expression".

Definition binop :=
  forall (out : Netlist.output) (in1 in2 : Netlist.input),
       Netlist.input_width in1 = Netlist.input_width in2 ->
       Netlist.input_width in1 = Netlist.output_width out -> Netlist.cell.

Definition transfer_bin_op (op : Verilog.op) : binop :=
  match op with
  | Verilog.Plus => Netlist.Add
  | Verilog.Minus => Netlist.Subtract
  | Verilog.Multiply => Netlist.Multiply
  | Verilog.ShiftLeft => Netlist.ShiftLeft
  | Verilog.ShiftRight => Netlist.ShiftRight
  end
.

Equations transfer_expression : TypedVerilog.expression -> transf Netlist.input :=
| TypedVerilog.IntegerLiteral v => ret (Netlist.InConstant v)
| TypedVerilog.NamedExpression type name =>
    let t := transfer_type type in
    n <- transfer_name name ;;
    st <- get ;;
    match EnvStack.lookup n (substitutionsBlocking st) with
    | Some e => ret e
    | None => ret (Netlist.InVar {| Netlist.varType := t; Netlist.varName := n |})
    end
| TypedVerilog.BinaryOp t op e1 e2 =>
    v1 <- transfer_expression e1 ;;
    v2 <- transfer_expression e2 ;;
    '{! v__result } <- fresh (transfer_type t) ;;
    if Pos.eq_dec (Netlist.input_width v1) (Netlist.input_width v2)
    then
      if Pos.eq_dec (Netlist.input_width v1) (Netlist.output_width (Netlist.OutVar v__result))
      then
        put_cells [transfer_bin_op op (Netlist.OutVar v__result) v1 v2 _ _] ;;
        ret (Netlist.InVar v__result)
      else raise "Incorrect output width in Verilog BinaryOp"%string
    else
      raise "Incompatible argument widths in Verilog BinaryOp"%string
| TypedVerilog.Conversion v_t__from v_t__to e =>
    v__expr <- transfer_expression e ;;
    '{! v__result } <- fresh (transfer_type v_t__to) ;;
    put_cells [Netlist.Convert (Netlist.OutVar v__result) v__expr] ;;
    ret (Netlist.InVar v__result)
.

Definition namemap_union {A B} (l : NameMap.t A) (r : NameMap.t B)
  : NameMap.t (option A * option B) :=
  NameMap.map2
    (fun lv rv =>
       match lv, rv with
       | None, None => None
       | _, _ => Some (lv, rv)
       end)
    l r.

Definition decide_or_fail {P : Prop} (dec : { P } + { ~ P }) (msg : string) : transf P :=
  match dec with
  | left prf => ret prf
  | right _ => raise msg
  end
.

Ltac crush_nl :=
  repeat match goal with
    | t : Netlist.nltype |- _ => destruct t; simpl
    (* | i : Netlist.input |- _ => destruct i; simpl *)
    | o : Netlist.output |- _ => destruct o; simpl
    end;
  (* repeat match goal with *)
  (*   | e : (_ ≈ _)%vtype |- _ => unfold "≈"%vtype in e; simpl in e *)
  (*   end; *)
  try lia.

Program Definition merge_if
  (cond : Netlist.input)
  (defaults : NameMap.t Netlist.input)
  (substitutionsTrue substitutionsFalse : NameMap.t Netlist.input)
  : transf () :=
  cond_ok <- decide_or_fail
              (Pos.eq_dec (Netlist.input_width cond) 1)
              "if condition must have width 1" ;;
  let substitutions_combined : NameMap.t (option Netlist.input * option Netlist.input) :=
    namemap_union substitutionsTrue substitutionsFalse in

  traverse_namemap_with_key (
      fun (n : name) (it : (option Netlist.input * option Netlist.input)) =>
        st <- get ;;
        let (trueBranch, falseBranch) := it in
        let default :=
          opt_or
            (NameMap.find n defaults)
            (option_map (fun t => Netlist.InVar (Netlist.Var t n))
              (NameMap.find n (vars st)))
        in
        match default, trueBranch, falseBranch with
        | _, Some t, Some f =>
            width_ok <- decide_or_fail
                        (Pos.eq_dec (Netlist.input_width t) (Netlist.input_width f))
                        "Incompatible widths in conditional";;
            let out := {| Netlist.varType := (Netlist.input_type t); Netlist.varName := n|} in
            put_cells [Netlist.Mux (Netlist.OutVar out) cond t f _ _ _] ;;
            set_substitution_blocking n (Netlist.InVar out)
        | Some def, Some t, None =>
            width_ok <- decide_or_fail
                        (Pos.eq_dec (Netlist.input_width def) (Netlist.input_width t))
                        "Incompatible widths in conditional";;
            let out := {| Netlist.varType := (Netlist.input_type t); Netlist.varName := n|} in
            put_cells [Netlist.Mux (Netlist.OutVar out) cond t def _ _ _] ;;
            set_substitution_blocking n (Netlist.InVar out)
        | Some def, None, Some f =>
            width_ok <- decide_or_fail
                        (Pos.eq_dec (Netlist.input_width def) (Netlist.input_width f))
                        "Incompatible widths in conditional";;
            let out := {| Netlist.varType := (Netlist.input_type f); Netlist.varName := n|} in
            put_cells [Netlist.Mux (Netlist.OutVar out) cond def f _ _ _] ;;
            set_substitution_blocking n (Netlist.InVar out)
        | _, _, _ => raise "Invalid state in merge_if"%string
        end
    ) substitutions_combined ;;
  ret ()
.
Next Obligation. (* Width *) Admitted.
Next Obligation. intuition discriminate. Qed.
Next Obligation. intuition discriminate. Qed.
Next Obligation. intuition discriminate. Qed.

Infix "<++>" := (monoid_plus Monoid_string_append) (at level 99).

(*
  Translated from the following
https://github.com/CakeML/hardware/blob/8264e60f0f9d503c9d971991cf181012276f0c9b/compiler/RTLCompilerScript.sml#L233-L295
*)
Equations transfer_statement : TypedVerilog.Statement -> transf () :=
| TypedVerilog.Block body =>
    mapT transfer_statement body ;;
    ret ()
| TypedVerilog.NonBlockingAssign (TypedVerilog.NamedExpression t__lhs vname__lhs) rhs =>
    name__lhs <- transfer_name vname__lhs ;;
    input__rhs <- transfer_expression rhs ;;
    set_substitution_nonblocking name__lhs input__rhs
| TypedVerilog.NonBlockingAssign lhs rhs =>
    raise "Invalid lhs for non-blocking assignment"%string
| TypedVerilog.BlockingAssign (TypedVerilog.NamedExpression t__lhs vname__lhs) rhs =>
    name__lhs <- transfer_name vname__lhs ;;
    input__rhs <- transfer_expression rhs ;;
    set_substitution_blocking name__lhs input__rhs
| TypedVerilog.BlockingAssign lhs rhs =>
    raise "Invalid lhs for blocking assignment"%string
| TypedVerilog.If condition trueBranch falseBranch =>
    st <- get ;;
    let defaults := EnvStack.flatten (substitutionsBlocking st) in
    (* @raise _ _ _ () ("defaults has length "%string <++> (nat2string10 (NameMap.cardinal defaults))) ;; *)
    condInput <- transfer_expression condition ;;
    '(_, (blockingTrue, nonblockingTrue)) <- transfer_scoped (transfer_statement trueBranch) ;;
    '(_, (blockingFalse, nonblockingFalse)) <- transfer_scoped (transfer_statement falseBranch) ;;
    merge_if condInput defaults blockingTrue blockingFalse ;;
    merge_if condInput defaults nonblockingTrue nonblockingFalse ;;
    ret ()
.

Equations transfer_module_item : TypedVerilog.module_item -> transf () :=
| TypedVerilog.AlwaysFF body => transfer_statement body
| TypedVerilog.ContinuousAssign (TypedVerilog.NamedExpression type name) from =>
    let t := transfer_type type in
    n <- transfer_name name ;;
    let outVar := Netlist.OutVar {| Netlist.varType := t; Netlist.varName := n |} in
    result <- transfer_expression from ;;
    if Pos.eq_dec (Netlist.input_width result) (Netlist.output_width outVar)
    then put_cells [ Netlist.Id outVar result _]
    else raise "Nope"%string
| TypedVerilog.ContinuousAssign _to _from =>
    raise "Invalid target for assign expression"%string
.

Equations mk_register : Netlist.input -> Netlist.register_declaration :=
| Netlist.InConstant bv =>
    {| Netlist.init := bv
    ; Netlist.driver := Netlist.InConstant bv
    |}
| Netlist.InVar v =>
    {| Netlist.init := Bitvector.mkBV 0 (Netlist.type_width (Netlist.varType v))
    ; Netlist.driver := Netlist.InVar v
    |}
.

Definition transfer_module (vmodule : TypedVerilog.vmodule) : transf Netlist.circuit :=
  transfer_variables (TypedVerilog.modVariables vmodule) ;;
  ports <- transfer_ports (TypedVerilog.modPorts vmodule) ;;
  mapT transfer_module_item (TypedVerilog.modBody vmodule) ;;

  finalState <- get ;;

  ret {| Netlist.circuitName := TypedVerilog.modName vmodule
      ; Netlist.circuitPorts := NameMap.from_list ports
      ; Netlist.circuitRegisters :=
          NameMap.map mk_register
            (NameMap.combine
               (EnvStack.flatten (substitutionsNonblocking finalState))
               (EnvStack.flatten (substitutionsBlocking finalState)))
      ; Netlist.circuitVariables := vars finalState
      ; Netlist.circuitCells := cells finalState
      |}
.

Definition verilog_to_netlist (start_name: positive) (vmodule : TypedVerilog.vmodule) : sum string (Netlist.circuit * transf_state) :=
  let result :=
    runStateT
      (transfer_module vmodule)
      {| nextName := start_name
      ; nameMap := StrMap.empty name
      ; vars := NameMap.empty _
      ; cells := []
      ; substitutionsBlocking := EnvStack.empty _
      ; substitutionsNonblocking := EnvStack.empty _
      |} in
  match result with
  | inl err => inl err
  | inr (circuit, final_state) => inr (circuit, final_state)
  end
.
