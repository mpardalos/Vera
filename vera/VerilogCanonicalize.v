From Coq Require Import List.
From Coq Require Import Program.
From Coq Require Import String.

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
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Programming.Show.

From SMTCoq Require Import BVList.
Import BITVECTOR_LIST (bitvector).

From vera Require Import Verilog.
From vera Require Import Common.
From vera Require EnvStack.

Import ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.

Module StrEnvStack := EnvStack.M(StrMap).

Record state :=
  TransfState
    { substitutionsBlocking : StrEnvStack.t TypedVerilog.expression
    ; substitutionsNonblocking : StrEnvStack.t TypedVerilog.expression
    }.

Definition empty_state :=
  {| substitutionsBlocking := StrEnvStack.empty _
  ; substitutionsNonblocking := StrEnvStack.empty _
  |}.

Definition transf : Type -> Type := stateT state (sum string).

Global Instance Monad_transf : Monad transf := Monad_stateT state (Monad_either string).

Definition run_transf {T} (a : transf T) : sum string (T * state) := runStateT a empty_state.

Definition exec_transf {T} (a : transf T) : sum string state := execStateT a empty_state.

Definition eval_transf {T} (a : transf T) : sum string T := evalStateT a empty_state.

Definition set_substitution_blocking (lhs : string) (rhs : TypedVerilog.expression) : transf () :=
  modify (fun s =>
            {| substitutionsBlocking := StrEnvStack.add lhs rhs (substitutionsBlocking s)
            ; substitutionsNonblocking := substitutionsNonblocking s
            |}) ;;
  ret ()
.

Definition set_substitution_nonblocking (lhs : string) (rhs : TypedVerilog.expression) : transf () :=
  modify (fun s =>
            {| substitutionsBlocking := substitutionsBlocking s
            ; substitutionsNonblocking := StrEnvStack.add lhs rhs (substitutionsNonblocking s)
            |}) ;;
  ret ()
.

Definition push_block : transf () :=
  modify (fun s =>
            {| substitutionsBlocking := StrEnvStack.push (substitutionsBlocking s)
            ; substitutionsNonblocking := StrEnvStack.push (substitutionsNonblocking s)
            |}) ;;
  ret ()
.

Definition pop_block : transf (StrMap.t TypedVerilog.expression * StrMap.t TypedVerilog.expression) :=
  s <- get ;;
  let (mBlockingEnv, substitutionsBlocking') := StrEnvStack.pop (substitutionsBlocking s) in
  let (mNonblockingEnv, substitutionsNonblocking') := StrEnvStack.pop (substitutionsNonblocking s) in
  match mBlockingEnv, mNonblockingEnv with
  | Some benv, Some nbenv =>
      modify (fun s =>
                {| substitutionsBlocking := substitutionsBlocking'
                ; substitutionsNonblocking := substitutionsNonblocking'
                |}) ;;
      ret (benv, nbenv)
  | _, _ =>
      raise "pop_block with an empty stack"%string
  end
.

Definition add_initial_statements (statements : list TypedVerilog.Statement) : transf () :=
  modify (fun s =>
            {| substitutionsBlocking := StrEnvStack.push (substitutionsBlocking s)
            ; substitutionsNonblocking := StrEnvStack.push (substitutionsNonblocking s)
            |}) ;;
  ret ()
.

Definition transfer_scoped {A} (f : transf A) : transf (A * (StrMap.t TypedVerilog.expression * StrMap.t TypedVerilog.expression)) :=
  push_block ;;
  result <- f ;;
  assigns <- pop_block ;;
  ret (result, assigns)
.

Equations transfer_expression : TypedVerilog.expression -> transf TypedVerilog.expression :=
| TypedVerilog.NamedExpression t n =>
    st <- get ;;
    match StrEnvStack.lookup n (substitutionsBlocking st) with
    | Some e => ret e
    | None => ret (TypedVerilog.NamedExpression t n)
    end
| e => ret e
.

Definition decide_or_fail {P : Prop} (dec : { P } + { ~ P }) (msg : string) : transf P :=
  match dec with
  | left prf => ret prf
  | right _ => raise msg
  end
.

Program Definition merge_if
  (setter : string -> TypedVerilog.expression -> transf ())
  (cond : TypedVerilog.expression)
  (defaults substitutionsTrue substitutionsFalse : StrMap.t TypedVerilog.expression)
  : transf () :=
  let substitutions_combined :=
    StrMap.elements (StrMap.union_both defaults (StrMap.union_both substitutionsTrue substitutionsFalse)) in

  mapT (
      fun  (it : (string * (option TypedVerilog.expression * option (option TypedVerilog.expression * option TypedVerilog.expression)))) =>
        let '(n, (default, branches )) := it in
        match branches with
        | Some (trueBranch, falseBranch) =>
            match trueBranch, falseBranch with
            | Some t, Some f =>
                (* width_ok <- decide_or_fail *)
                (*              (eq_dec (TypedVerilog.expr_type t) (TypedVerilog.expr_type f)) *)
                (*              "Incompatible widths in conditional";; *)
                setter n (TypedVerilog.Conditional cond t f)
            | Some t, None =>
                let def := opt_or_else default (TypedVerilog.NamedExpression (TypedVerilog.expr_type t) n) in
                setter n (TypedVerilog.Conditional cond t def)
            | None, Some f =>
                let def := opt_or_else default (TypedVerilog.NamedExpression (TypedVerilog.expr_type f) n) in
                setter n (TypedVerilog.Conditional cond def f)
            | None, None => raise "Invalid state in merge_if"%string
            end
        | None => ret ()
        end
    ) substitutions_combined ;;
  ret ()
.

(*
  Translated from the following
https://github.com/CakeML/hardware/blob/8264e60f0f9d503c9d971991cf181012276f0c9b/compiler/RTLCompilerScript.sml#L233-L295
*)
Equations transfer_statement : TypedVerilog.Statement -> transf () :=
| TypedVerilog.Block body =>
    mapT transfer_statement body ;;
    ret ()
| TypedVerilog.NonBlockingAssign (TypedVerilog.NamedExpression t__lhs name__lhs) rhs =>
    input__rhs <- transfer_expression rhs ;;
    set_substitution_nonblocking name__lhs input__rhs
| TypedVerilog.NonBlockingAssign lhs rhs =>
    raise "Invalid lhs for non-blocking assignment"%string
| TypedVerilog.BlockingAssign (TypedVerilog.NamedExpression t__lhs name__lhs) rhs =>
    input__rhs <- transfer_expression rhs ;;
    set_substitution_blocking name__lhs input__rhs
| TypedVerilog.BlockingAssign lhs rhs =>
    raise "Invalid lhs for blocking assignment"%string
| TypedVerilog.If condition trueBranch falseBranch =>
    st <- get ;;
    let defaults := StrEnvStack.flatten (substitutionsBlocking st) in
    condInput <- transfer_expression condition ;;
    '(_, (blockingTrue, nonblockingTrue)) <- transfer_scoped (transfer_statement trueBranch) ;;
    '(_, (blockingFalse, nonblockingFalse)) <- transfer_scoped (transfer_statement falseBranch) ;;
    merge_if set_substitution_blocking condInput defaults blockingTrue blockingFalse ;;
    merge_if set_substitution_nonblocking condInput defaults nonblockingTrue nonblockingFalse ;;
    ret ()
.

Definition substitution : Type := string * TypedVerilog.expression.


Definition transfer_all_always_ff (items : list TypedVerilog.module_item) : transf () :=
  mapT
    (fun it =>
       match it with
       | TypedVerilog.AlwaysFF body => transfer_statement body
       | _ => ret ()
       end) items ;;
  ret ()
.

Definition transfer_all_always_comb (items : list TypedVerilog.module_item) : transf () :=
  mapT
    (fun it =>
       match it with
       | TypedVerilog.AlwaysComb body => transfer_statement body
       | _ => ret ()
       end) items ;;
  ret ()
.

Definition collect_initial_statements (items : list TypedVerilog.module_item) : list TypedVerilog.Statement :=
  let stmts := map
    (fun it =>
       match it with
       | TypedVerilog.Initial (TypedVerilog.Block stmts) => stmts
       | TypedVerilog.Initial stmt => [stmt]
       | _ => []
       end) items in
  concat stmts
.


Definition substitutions_from_state (st : state) : list substitution :=
  let subsBlocking := StrEnvStack.flatten (substitutionsBlocking st) in
  let subsNonblocking := StrEnvStack.flatten (substitutionsNonblocking st) in
  StrMap.elements (StrMap.combine subsNonblocking subsBlocking)
.

Definition substitutions_to_assignments
  (assignment : TypedVerilog.expression -> TypedVerilog.expression -> TypedVerilog.Statement)
  (subs : list substitution)
  : list TypedVerilog.Statement :=
  map (fun '(lhs, rhs) =>
         assignment
           (* TODO: Keep the original type, rather than getting it from rhs *)
           (TypedVerilog.NamedExpression (TypedVerilog.expr_type rhs) lhs)
           rhs) subs.

Definition canonicalize_module (vmodule : TypedVerilog.vmodule) : sum string TypedVerilog.vmodule :=
  let initial_body := collect_initial_statements (TypedVerilog.modBody vmodule) in

  always_ff_final_state <- exec_transf (transfer_all_always_ff (TypedVerilog.modBody vmodule)) ;;
  let always_ff_subs := substitutions_from_state always_ff_final_state in
  let always_ff_body := substitutions_to_assignments TypedVerilog.NonBlockingAssign always_ff_subs in

  always_comb_final_state <- exec_transf (transfer_all_always_comb (TypedVerilog.modBody vmodule)) ;;
  let always_comb_subs := substitutions_from_state always_comb_final_state in
  let always_comb_body := substitutions_to_assignments TypedVerilog.BlockingAssign always_comb_subs in

  let body := [
      TypedVerilog.Initial (TypedVerilog.Block initial_body);
      TypedVerilog.AlwaysFF (TypedVerilog.Block always_ff_body);
      TypedVerilog.AlwaysComb (TypedVerilog.Block always_comb_body)
    ] in
  ret
    {|
      TypedVerilog.modName := TypedVerilog.modName vmodule;
      TypedVerilog.modPorts := TypedVerilog.modPorts vmodule;
      TypedVerilog.modVariables := TypedVerilog.modVariables vmodule;
      TypedVerilog.modBody := body
    |}
.

Definition canonicalize_verilog := canonicalize_module.
