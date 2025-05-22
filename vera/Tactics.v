From Coq Require Export Lia.

From vera Require Import Decidable.

(* Stuff every "finisher" tactic you can think of in here *)
Ltac crush :=
  solve [repeat progress (
             discriminate
             || lia
             || congruence
             || auto
             || eauto
             || firstorder
    )].


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

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
    match type of T with Prop =>
      inversion H;
      match n with S (S (?n')) => subst; try constructor; try contradiction; try discriminate; solve_by_inverts (S n') end
    end
  end.

Ltac solve_by_invert := solve_by_inverts 1.

Ltac inv H := inversion H; subst; clear H.

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
    end.

Ltac reductio_ad_absurdum :=
  match goal with
  | [ |- ?g ] => destruct (dec g); try assumption; exfalso
  end.

Ltac apply_somewhere f :=
  multimatch goal with
  | [ H : _ |- _] => apply f in H
  end.
