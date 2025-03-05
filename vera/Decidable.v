From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import BinNums.
From Coq Require Import BinNat.
From Coq Require Import BinInt.
From Coq Require Import PeanoNat.

Class DecProp (P : Prop) := dec : { P } + { ~ P } .

Arguments dec _ {_}.

Notation mk_dec_eq :=
  ltac:(unfold DecProp in *; repeat (decide equality || eauto))
         (only parsing).

Notation "mk_dec_eq!( x )" :=
  ltac:(unfold DecProp in *; eauto using x; repeat (decide equality || eauto))
         (only parsing).

Notation "mk_dec_eq( x )" :=
  ltac:(unfold DecProp in *; eauto using x)
         (only parsing).

Instance dec_not {P} `{DecProp P} : DecProp (~ P ).
Proof. firstorder. Qed.

Instance dec_and {P Q} `{DecProp P, DecProp Q} : DecProp ( P /\ Q ).
Proof. firstorder. Qed.

Instance dec_or {P Q} `{DecProp P, DecProp Q} : DecProp ( P \/ Q ).
Proof. firstorder. Qed.

Instance dec_impl {P Q} `{DecProp P, DecProp Q} : DecProp ( P -> Q ).
Proof. firstorder. Qed.

Instance dec_iff {P Q} `{DecProp P, DecProp Q} : DecProp ( P <-> Q ).
Proof. firstorder. Qed.

Instance dec_eq_string (x y : string) : DecProp (x = y) :=
  mk_dec_eq(String.string_dec).

Instance dec_eq_nat (x y : nat) : DecProp (x = y) :=
  mk_dec_eq(Nat.eq_dec).

Instance dec_eq_N (x y : N) : DecProp (x = y) :=
  mk_dec_eq(N.eq_dec).

Instance dec_eq_Z (x y : Z) : DecProp (x = y) :=
  mk_dec_eq(Z.eq_dec).

Instance dec_eq_opt {A} `{forall (x y : A), DecProp (x = y)} (x y : option A) : DecProp (x = y) :=
  mk_dec_eq.

Instance dec_eq_pair {A B}
  `{forall (x y : A), DecProp (x = y)}
  `{forall (x y : B), DecProp (x = y)}
  (x y : (A * B)) : DecProp (x = y) :=
  mk_dec_eq.

Instance dec_eq_list {A} `{forall (x y : A), DecProp (x = y)} (x y : list A) : DecProp (x = y) :=
  mk_dec_eq!(list_eq_dec).

Instance dec_Forall {A} {P : A -> Prop} {decP : forall x, DecProp (P x)} l :
  DecProp (Forall P l).
Proof.
  induction l.
  - left. constructor.
  - destruct IHl.
    + destruct (dec (P a)).
      * left. constructor; assumption.
      * right. inversion 1. contradiction.
    + right. inversion 1. contradiction.
Qed.

Instance dec_Exists {A} {P : A -> Prop} {decP : forall x, DecProp (P x)} l :
  DecProp (Exists P l).
Proof.
  intros.
  induction l.
  - right. inversion 1.
  - destruct (decP a).
    + left. auto.
    + destruct IHl.
      * left. auto.
      * right. inversion 1; subst; contradiction.
Qed.

Instance dec_NoDup {A}
  `{a_dec : forall (x y: A), DecProp (x = y)}
  (l : list A) :
  DecProp ( List.NoDup l ).
Proof.
  induction l.
  - repeat constructor.
  - destruct IHl as [ IHl | IHl ].
    + edestruct (List.in_dec a_dec a l).
      * right. inversion 1. contradiction.
      * left. constructor; assumption.
    + right. inversion 1. contradiction.
Qed.

Definition assert_dec {E} (P : Prop) `{ DecProp P } (err : E) : sum E P :=
  match dec P with
  | right _ => inl err
  | left prf => inr prf
  end.
