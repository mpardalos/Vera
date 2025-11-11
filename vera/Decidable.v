From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import BinNums.
From Stdlib Require Import BinNat.
From Stdlib Require Import BinInt.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

From vera Require SMTLib.

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

Instance dec_False : DecProp (False).
Proof. firstorder. Qed.

Instance dec_True : DecProp (True).
Proof. firstorder. Qed.

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

Instance dec_eq_bool (x y : bool) : DecProp (x = y) :=
  mk_dec_eq(Bool.bool_dec).

Instance dec_eq_string (x y : string) : DecProp (x = y) :=
  mk_dec_eq(String.string_dec).

Instance dec_eq_nat (x y : nat) : DecProp (x = y) :=
  mk_dec_eq(Nat.eq_dec).

Instance dec_eq_N (x y : N) : DecProp (x = y) :=
  mk_dec_eq(N.eq_dec).

Instance dec_eq_Z (x y : Z) : DecProp (x = y) :=
  mk_dec_eq(Z.eq_dec).

Instance dec_lt_N (x y : N) : DecProp (x < y)%N.
Proof.
  destruct (x <? y)%N eqn:E.
  - left. now apply N.ltb_lt in E.
  - right. now apply N.ltb_nlt in E.
Defined.

Instance dec_le_N (x y : N) : DecProp (x <= y)%N.
Proof.
  destruct (x <=? y)%N eqn:E.
  - left. now apply N.leb_le in E.
  - right. now apply N.leb_nle in E.
Defined.

Instance dec_ge_N (x y : N) : DecProp (x >= y)%N.
Proof.
  destruct (x <? y)%N eqn:E.
  - right. apply N.ltb_lt in E. lia.
  - left. apply N.ltb_nlt in E. lia.
Defined.

Instance dec_gt_N (x y : N) : DecProp (x > y)%N.
Proof.
  destruct (x <=? y)%N eqn:E.
  - right. apply N.leb_le in E. lia.
  - left. apply N.leb_nle in E. lia.
Defined.

Instance dec_eq_opt {A} `{forall (x y : A), DecProp (x = y)} (x y : option A) : DecProp (x = y) :=
  mk_dec_eq.

Instance dec_eq_pair {A B}
  `{forall (x y : A), DecProp (x = y)}
  `{forall (x y : B), DecProp (x = y)}
  (x y : (A * B)) : DecProp (x = y) :=
  mk_dec_eq.

Instance dec_eq_list {A} `{forall (x y : A), DecProp (x = y)} (x y : list A) : DecProp (x = y) :=
  mk_dec_eq!(list_eq_dec).

Instance dec_eq_sort (x y : SMTLib.sort) : DecProp (x = y) :=
  mk_dec_eq!(SMTLib.dec_sort).

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

Instance dec_In A {dec_x : forall (x y : A), DecProp (x = y)} l (x : A) :
  DecProp (In x l).
Proof. induction l; firstorder. Qed.

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

Lemma exists_impl A (P Q : A -> Prop) :
  (forall x, P x -> Q x) ->
  (exists x, P x) ->
  (exists x, Q x).
Proof. firstorder. Qed.

Instance dec_exists_Some {A} `{forall (x y : A), DecProp (x = y)} (o : option A) :
  DecProp (exists (x : A), o = Some x).
Proof.
  destruct o.
  - left. eauto.
  - right. intros []. discriminate.
  (* induction l as [|[a' b']].
   * - firstorder.
   * - destruct (dec (a = a')).
   *   + left. subst. eauto with datatypes.
   *   + destruct IHl.
   *     * left. eapply exists_impl; [|eapply e].
   *       firstorder; congruence.
   *     * right. intro contra. apply n0. clear n0.
   *       eapply exists_impl; [|eapply contra].
   *       firstorder; congruence. *)
Qed.

Instance dec_exists_In_pair_l {A B} `{forall (x y : A), DecProp (x = y)} `{forall (x y : B), DecProp (x = y)} (b : B) l :
  DecProp (exists (a : A), In (a, b) l).
Proof.
  induction l as [|[a' b']].
  - firstorder.
  - destruct (dec (b = b')).
    + left. subst. eauto with datatypes.
    + destruct IHl.
      * left. eapply exists_impl; [|eapply e].
        firstorder.
      * right. intro contra. apply n0. clear n0.
        eapply exists_impl; [|eapply contra].
        firstorder; congruence.
Qed.

Instance dec_exists_In_pair_r {A B} `{forall (x y : A), DecProp (x = y)} `{forall (x y : B), DecProp (x = y)} (a : A) l :
  DecProp (exists (b : B), In (a, b) l).
Proof.
  induction l as [|[a' b']].
  - firstorder.
  - destruct (dec (a = a')).
    + left. subst. eauto with datatypes.
    + destruct IHl.
      * left. eapply exists_impl; [|eapply e].
        firstorder; congruence.
      * right. intro contra. apply n0. clear n0.
        eapply exists_impl; [|eapply contra].
        firstorder; congruence.
Qed.


Definition assert_dec {E} (P : Prop) `{ DecProp P } (err : E) : sum E P :=
  match dec P with
  | right _ => inl err
  | left prf => inr prf
  end.

Definition opt_dec (P : Prop) `{DecProp P} : option P :=
  match dec P with
  | right _ => None
  | left prf => Some prf
  end.
