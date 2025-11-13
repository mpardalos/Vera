From Equations Require Import Equations.
From Stdlib Require List.
From Stdlib Require Import Lia.

From ExtLib Require Import Structures.Monads.

From vera Require Import Common.
From vera Require Import Decidable.
From vera Require Import Verilog.
Import Verilog.

Import CommonNotations.
Import List.ListNotations.
Local Open Scope list.
Import MonadLetNotation.
Local Open Scope monad_scope.

Section Ready.
  Context (regs_ready : variable -> Prop).

  Definition expr_is_ready {w} (e : expression w) : Prop :=
    List.Forall regs_ready (expr_reads e).

  Definition statement_is_ready (s : statement) : Prop :=
    List.Forall regs_ready (statement_reads s).

  Definition module_item_is_ready (mi : module_item) : Prop :=
    List.Forall regs_ready (module_item_reads mi).
End Ready.

Equations sort_module_items_insert
  (regs_ready : list variable)
  (mi : module_item)(mis : list module_item)
  : list module_item :=
sort_module_items_insert vars_ready mi mis with dec (module_item_is_ready (fun var => List.In var vars_ready) mi) :=
  sort_module_items_insert vars_ready mi mis (left prf) := mi :: mis;
  sort_module_items_insert vars_ready mi [] (right prf) := [mi];
  sort_module_items_insert vars_ready mi (hd :: tl) (right prf) :=
    hd :: sort_module_items_insert (module_item_writes hd ++ vars_ready) mi tl
.

Record selection (l : list module_item) :=
  MkSelection {
    mi : module_item;
    rest : list module_item;
    wf : S (length rest) = length l
  }.

Equations sort_module_items_select (vars_ready : list variable) (mis : list module_item) : option (selection mis) := {
  | vars_ready, [] => @None _
  | vars_ready, hd :: tl with dec (module_item_is_ready (fun var => List.In var vars_ready) hd) => {
    | left prf => Some (MkSelection (hd :: tl) hd tl _)
    | right _ =>
        let* (MkSelection _ selected selected_tl _) := sort_module_items_select vars_ready tl in
        Some (MkSelection (hd :: tl) selected (hd :: selected_tl) _)
  }
}.

Equations sort_module_items
  (vars_ready : list variable)
  (mis : list module_item)
  : option (list module_item)
  by wf (length mis) lt := {
  | vars_ready, [] => Some []
  | vars_ready, hd :: tl =>
    let* (MkSelection _ ready rest _) := sort_module_items_select vars_ready (hd :: tl) in
    let* sorted_rest := sort_module_items (module_item_writes ready ++ vars_ready) rest in
    Some (ready :: sorted_rest)
  }.

Definition vmodule_sortable (v : vmodule) : Prop :=
  exists sorted, sort_module_items (Verilog.module_inputs v) (Verilog.modBody v) = Some sorted.
