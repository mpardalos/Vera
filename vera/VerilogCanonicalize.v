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
From vera Require Import Decidable.
From vera Require EnvStack.

Import ListNotations.
Import CommonNotations.
Import MonadNotation.
Import FunctorNotation.
Import SigTNotations.
Local Open Scope monad_scope.

Module StrEnvStack := EnvStack.M(StrMap).

Record state :=
  TransfState
    { substitutionsBlocking : StrEnvStack.t {w & Verilog.expression w}
    ; substitutionsNonblocking : StrEnvStack.t {w & Verilog.expression w}
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

Definition set_substitution_blocking {w} (lhs : string) (rhs : Verilog.expression w) : transf () :=
  modify (fun s =>
            {| substitutionsBlocking := StrEnvStack.add lhs (w; rhs) (substitutionsBlocking s)
            ; substitutionsNonblocking := substitutionsNonblocking s
            |}) ;;
  ret ()
.

Definition set_substitution_nonblocking {w} (lhs : string) (rhs : Verilog.expression w) : transf () :=
  modify (fun s =>
            {| substitutionsBlocking := substitutionsBlocking s
            ; substitutionsNonblocking := StrEnvStack.add lhs (w; rhs) (substitutionsNonblocking s)
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

Definition pop_block : transf (StrMap.t {w & Verilog.expression w} * StrMap.t {w & Verilog.expression w}) :=
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

Definition add_initial_statements (statements : list Verilog.statement) : transf () :=
  modify (fun s =>
            {| substitutionsBlocking := StrEnvStack.push (substitutionsBlocking s)
            ; substitutionsNonblocking := StrEnvStack.push (substitutionsNonblocking s)
            |}) ;;
  ret ()
.

Definition transfer_scoped {A} (f : transf A) : transf (A * (StrMap.t {w & Verilog.expression w} * StrMap.t {w & Verilog.expression w})) :=
  push_block ;;
  result <- f ;;
  assigns <- pop_block ;;
  ret (result, assigns)
.

Import EqNotations.

Equations transfer_expression {w} : Verilog.expression w -> transf (Verilog.expression w) :=
| Verilog.NamedExpression t n =>
    st <- get ;;
    match StrEnvStack.lookup n (substitutionsBlocking st) with
    | Some (w'; e) =>
        match dec (w' = t) with
        | right _ => raise "oops"%string
        | left E => ret (rew E in e)
        end
    | None => ret (Verilog.NamedExpression t n)
    end
| e => ret e
.

Definition decide_or_fail (P : Prop) `{ DecProp P } (msg : string) : transf P :=
  match dec P with
  | left prf => ret prf
  | right _ => raise msg
  end
.

Definition merge_if
  (setter : forall {w}, string -> Verilog.expression w -> transf ())
  {w} (cond : Verilog.expression w)
  (defaults substitutionsTrue substitutionsFalse : StrMap.t {w & Verilog.expression w})
  : transf () :=
  let substitutions_combined :=
    StrMap.elements (StrMap.union_both defaults (StrMap.union_both substitutionsTrue substitutionsFalse)) in

  mapT (
      fun  (it : (string * (option {w & Verilog.expression w} * option (option {w & Verilog.expression w} * option {w & Verilog.expression w})))) =>
        let '(n, (default, branches )) := it in
        match branches with
        | Some (trueBranch, falseBranch) =>
            match trueBranch, falseBranch with
            | Some (wt; t), Some (wf; f) =>
                width_ok <- decide_or_fail (wf = wt) "Incompatible widths in conditional";;
                setter n (Verilog.Conditional cond t (rew width_ok in f))
            | Some (w; t), None =>
                let '(w'; def) := opt_or_else default (w; Verilog.NamedExpression w n) in
                width_ok <- decide_or_fail _ "Incompatible widths in conditional";;
                setter n (Verilog.Conditional cond t (rew width_ok in def))
            | None, Some (_; f) =>
                let '(w'; def) := opt_or_else default (w; Verilog.NamedExpression w n) in
                width_ok <- decide_or_fail _ "Incompatible widths in conditional";;
                setter n (Verilog.Conditional cond def (rew width_ok in f))
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
Equations transfer_statement : Verilog.statement -> transf () :=
| Verilog.Block body =>
    mapT transfer_statement body ;;
    ret ()
| Verilog.NonBlockingAssign (Verilog.NamedExpression t__lhs name__lhs) rhs =>
    input__rhs <- transfer_expression rhs ;;
    set_substitution_nonblocking name__lhs input__rhs
| Verilog.NonBlockingAssign lhs rhs =>
    raise "Invalid lhs for non-blocking assignment"%string
| Verilog.BlockingAssign (Verilog.NamedExpression t__lhs name__lhs) rhs =>
    input__rhs <- transfer_expression rhs ;;
    set_substitution_blocking name__lhs input__rhs
| Verilog.BlockingAssign lhs rhs =>
    raise "Invalid lhs for blocking assignment"%string
| Verilog.If condition trueBranch falseBranch =>
    st <- get ;;
    let defaults := StrEnvStack.flatten (substitutionsBlocking st) in
    condInput <- transfer_expression condition ;;
    '(_, (blockingTrue, nonblockingTrue)) <- transfer_scoped (transfer_statement trueBranch) ;;
    '(_, (blockingFalse, nonblockingFalse)) <- transfer_scoped (transfer_statement falseBranch) ;;
    merge_if (@set_substitution_blocking) condInput defaults blockingTrue blockingFalse ;;
    merge_if (@set_substitution_nonblocking) condInput defaults nonblockingTrue nonblockingFalse ;;
    ret ()
.

Definition substitution : Type := string * {w & Verilog.expression w}.

Definition transfer_all_always_ff (items : list Verilog.module_item) : transf () :=
  mapT
    (fun it =>
       match it with
       | Verilog.AlwaysFF body => transfer_statement body
       | _ => ret ()
       end) items ;;
  ret ()
.

Definition transfer_all_always_comb (items : list Verilog.module_item) : transf () :=
  mapT
    (fun it =>
       match it with
       | Verilog.AlwaysComb body => transfer_statement body
       | _ => ret ()
       end) items ;;
  ret ()
.

Definition collect_initial_statements (items : list Verilog.module_item) : list Verilog.statement :=
  let stmts := map
    (fun it =>
       match it with
       | Verilog.Initial (Verilog.Block stmts) => stmts
       | Verilog.Initial stmt => [stmt]
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
  (assignment : forall {w}, Verilog.expression w -> Verilog.expression w -> Verilog.statement)
  (subs : list substitution)
  : list Verilog.statement :=
  map (fun '(lhs, (w; rhs)) =>
         assignment
           (* TODO: Keep the original type, rather than getting it from rhs *)
           (Verilog.NamedExpression (Verilog.expr_type rhs) lhs) rhs) subs.

Definition canonicalize_module (vmodule : Verilog.vmodule) : sum string Verilog.vmodule :=
  let initial_body := collect_initial_statements (Verilog.modBody vmodule) in

  always_ff_final_state <- exec_transf (transfer_all_always_ff (Verilog.modBody vmodule)) ;;
  let always_ff_subs := substitutions_from_state always_ff_final_state in
  let always_ff_body := substitutions_to_assignments (@Verilog.NonBlockingAssign) always_ff_subs in

  always_comb_final_state <- exec_transf (transfer_all_always_comb (Verilog.modBody vmodule)) ;;
  let always_comb_subs := substitutions_from_state always_comb_final_state in
  let always_comb_body := substitutions_to_assignments (@Verilog.BlockingAssign) always_comb_subs in

  let body := [
      Verilog.Initial (Verilog.Block initial_body);
      Verilog.AlwaysFF (Verilog.Block always_ff_body);
      Verilog.AlwaysComb (Verilog.Block always_comb_body)
    ] in
  ret
    {|
      Verilog.modName := Verilog.modName vmodule;
      Verilog.modVariables := Verilog.modVariables vmodule;
      Verilog.modBody := body
    |}
.

Definition canonicalize_verilog := canonicalize_module.
