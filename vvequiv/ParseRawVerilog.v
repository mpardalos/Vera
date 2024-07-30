From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import BinNat.
Import ListNotations.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.MonadState.
From ExtLib Require Import Structures.MonadExc.
From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Import Data.Monads.StateMonad.
From ExtLib Require Import Data.Monads.EitherMonad.
From ExtLib Require Import Data.List.
From ExtLib Require Import Structures.Reducible.
Import MonadNotation.
Open Scope monad_scope.

From vvequiv Require Import Verilog.

Definition Result := sum string.

Definition add_module_item (item : Verilog.module_item) (m: Verilog.vmodule) : Verilog.vmodule :=
  {| Verilog.modName := Verilog.modName m
  ; Verilog.modPorts := Verilog.modPorts m
  ; Verilog.modVariables := Verilog.modVariables m
  ; Verilog.modBody := item :: Verilog.modBody m
  |}
.

Definition add_port (port : Verilog.port) (m: Verilog.vmodule) : Verilog.vmodule :=
  {| Verilog.modName := Verilog.modName m
  ; Verilog.modPorts := port :: Verilog.modPorts m
  ; Verilog.modVariables := Verilog.modVariables m
  ; Verilog.modBody := Verilog.modBody m
  |}
.

Definition add_variable (var : Verilog.variable) (m: Verilog.vmodule) : Verilog.vmodule :=
  {| Verilog.modName := Verilog.modName m
  ; Verilog.modPorts := Verilog.modPorts m
  ; Verilog.modVariables := var :: Verilog.modVariables m
  ; Verilog.modBody := Verilog.modBody m
  |}
.

Equations parse_optional_type (mType : option Verilog.vtype) : Verilog.vtype := {
  | None => Verilog.Logic 0 0
  | Some t => t
  }.

Equations add_raw_module_item
  : (Verilog.module_item + Verilog.raw_declaration) -> Verilog.vmodule -> Result Verilog.vmodule := {
  | inl item, m =>
      ret (add_module_item item m)
  | inr (Verilog.MkRawDeclaration storage_type None name type), m =>
      ret (add_variable (Verilog.MkVariable (parse_optional_type type) storage_type name) m)
  | inr (Verilog.MkRawDeclaration storage_type (Some dir) name type), m =>
      ret (add_variable
             (Verilog.MkVariable (parse_optional_type type) storage_type name)
             (add_port
                (Verilog.MkPort dir name)
                m))
  }
.

Definition parse_raw_verilog (m: Verilog.raw_vmodule) : Result Verilog.vmodule :=
  foldM
    add_raw_module_item
    (ret
       {| Verilog.modName := Verilog.rawModName m
       ; Verilog.modPorts := []
       ; Verilog.modVariables := []
       ; Verilog.modBody := []
       |})
    (Verilog.rawModBody m).
