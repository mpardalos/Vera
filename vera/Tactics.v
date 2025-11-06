From Stdlib Require Export Lia.
Import EqNotations.

From vera Require Import Decidable.

From ExtLib Require Import Structures.Monads.

Import MonadLetNotation.
Import SigTNotations.

(* This needs to be defined here, because monad_inv depends on it *)
Program Definition sum_with_eqn {A B} (s : sum A B) : sum A { x : B & s = inr x } :=
  match s with
  | inr x => inr (x; _)
  | inl e => inl e
  end.

(* This tactic due to Clement Pit-Claudel with some minor additions by JDP to
   allow the result to be named: https://pit-claudel.fr/clement/MSc/#org96a1b5f *)
Inductive Learnt {A: Type} (a: A) :=
  | AlreadyKnown : Learnt a.

Ltac learn_tac fact name :=
  lazymatch goal with
  | [ H: Learnt fact |- _ ] =>
    fail 0 "fact" fact "has already been learnt"
  | _ => let type := type of fact in
        lazymatch goal with
        | [ H: @Learnt type _ |- _ ] =>
          fail 0 "fact" fact "of type" type "was already learnt through" H
        | _ => let learnt := fresh "Learn" in
              pose proof (AlreadyKnown fact) as learnt; pose proof fact as name
        end
  end.

Tactic Notation "learn" constr(fact) := let name := fresh "H" in learn_tac fact name.
Tactic Notation "learn" constr(fact) "as" simple_intropattern(name) := learn_tac fact name.

Ltac unfold_rec c := unfold c; fold c.

Ltac inv H := inversion H; subst; clear H.

Ltac some_inv :=
  multimatch goal with
  | H : ?T |- _ =>
      match type of T with
      | Prop => inv H
      end
  end.

Ltac solve_by_inverts n :=
  match goal with
  | H : ?T |- _ =>
      match type of T with
      | Prop =>
          inversion H;
          match n with
          | S (S (?n')) =>
              subst;
              try constructor;
              try easy;
              try eauto;
              solve_by_inverts (S n')
          end
      end
  end.

Ltac solve_by_invert := solve_by_inverts 1.

Ltac autodestruct :=
  repeat match goal with
    | [ H : context [ match ?x with _ => _ end ] |- _ ] =>
        destruct x; try discriminate
    | [ |- context [ match ?x with _ => _ end ] ] =>
        destruct x; try discriminate
    | [ H : inr _ = inr _ |- _ ] =>
        inv H
    | [ H : Some _ = Some _ |- _ ] =>
        inv H
    end.

Ltac autodestruct_eqn name :=
  repeat match goal with
    | [ H : context [ match ?x with _ => _ end ] |- _ ] =>
        let E := fresh name in
        destruct x eqn:E; try discriminate
    | [ |- context [ match ?x with _ => _ end ] ] =>
        let E := fresh name in
        destruct x eqn:E; try discriminate
    | [ H : inr _ = inr _ |- _ ] =>
        inv H
    | [ H : Some _ = Some _ |- _ ] =>
        inv H
    | [ H: context[sumbool_rec _ _ _  (?d ?a ?b)] |- _ ] =>
        destruct (d a b); cbn in H; try (congruence || contradiction || discriminate)
    | [ |- context[sumbool_rec _ _ _  (?d ?a ?b)] ] =>
        destruct (d a b); try (congruence || contradiction || discriminate)
    end.

Ltac monad_cleanup :=
  repeat match goal with
    | [ H : assert_dec _ _ = inr _ |- _ ] => clear H
    end.

Ltac monad_inv :=
  try discriminate;
  repeat match goal with
    | [ H : (_ ;; _)%monad = _ |- _ ] => inv H
    | [ H : _ = (_ ;; _)%monad |- _ ] => inv H
    | [ H : inl _ = inl _ |- _ ] => inv H
    | [ H : inr _ = inr _ |- _ ] => inv H
    | [ H : ret _ = inr _ |- _ ] => inv H
    | [ H : inr _ = ret _ |- _ ] => inv H
    end;
  let E := fresh "E" in
  autodestruct_eqn E;
  repeat match goal with
    | [ E : sum_with_eqn ?x = inr _, e : ?x = inr _ |- _ ] =>
        rewrite e in E; simpl in E; inv E
    end;
  monad_cleanup
.


Ltac reductio_ad_absurdum :=
  match goal with
  | [ |- ?g ] => destruct (dec g); try assumption; exfalso
  end.

Ltac apply_somewhere f :=
  multimatch goal with
  | [ H : _ |- _] => apply f in H
  end.

Ltac destruct_rew :=
  match goal with
  | [H : context[rew [ _ ] ?E in _] |- _] =>
      destruct E; simpl in H
  | [H : context[rew dependent [ _ ] ?E in _] |- _] =>
      destruct E; simpl in H
  | [|- context[rew [ _ ] ?E in _]] =>
      destruct E; simpl
  | [|- context[rew dependent [ _ ] ?E in _]] =>
      destruct E; simpl
  end.

(* Stuff every "finisher" tactic you can think of in here *)
Ltac crush :=
  let E := fresh "E" in
  solve [
      (simpl in * + idtac);
      try destruct_rew;
      try autodestruct_eqn E;
      repeat progress (
          discriminate
          || lia
          || congruence
          || auto
          || eauto
          || firstorder
          || cbn in *
    )].

Ltac insterU' tac H :=
  repeat match type of H with
    | forall x : ?T, _ =>
        match type of T with
        | Prop => (specialize (H ltac:(solve [tac])) || fail 1)
        | _ =>
            let x := fresh "x" in
            evar (x : T);
            let x' := eval unfold x in x in
              clear x; specialize (H x')
        end
    end.

(**
 * "inster" tactics based on CPDT (http://adam.chlipala.net/cpdt/html/Match.html)
 *)

(** Instantiate the parameters of a hypothesis as far as possible using `tac' to
    solve goals *)
Tactic Notation "insterU" hyp(H) "by" tactic(tac) := insterU' tac H.

(** Instantiate the parameters of a hypothesis as far as possible *)
Tactic Notation "insterU" hyp(H) := insterU' crush H.

Ltac insterKeep' tac H :=
  let H' := fresh "H'" in
  generalize H; intro H'; insterU H' by tac.

(** Like insterU, but keep an uninstantiated copy of `H' *)
Tactic Notation "insterKeep" hyp(H) "by" tactic(tac) := insterKeep' tac H.

(** Like insterU, but keep an uninstantiated copy of `H' *)
Tactic Notation "insterKeep" hyp(H) := insterKeep' crush H.
