Module DN.

(** This file contains some lemmas and derived tactics that are used to handle double negations during a proof. *)

Definition ret_ {A : Prop} : A -> ~~A.                     tauto. Defined.
Definition bind_ {A B : Prop} : ~~A -> (A -> ~~B) -> ~~B.  tauto. Defined.
Definition remove_ {A B} : ~~A -> (A -> ~B) -> ~B.         tauto. Defined.
Definition lem_ X : ~~(X \/ ~X).                           tauto. Defined.
Definition dne_ X : ~~(~~X -> X).                          tauto. Defined.

Ltac ret := apply ret_.

Ltac bind H := try match goal with
  | h : _ |- ~ ~ _ => apply (bind_ H); clear H; intros H; try tauto
  end.

Ltac lem P := apply (bind_ (lem_ P)); try tauto.

Ltac dne P := apply (bind_ (dne_ P)); try tauto.

Ltac remove_dn :=
  repeat match goal with
  | H : ~ ~ _ |- False
    => apply H; clear H; intros H
  | H : ~ ~ _ |- _ -> False
    => intros G; apply H; clear H; intros H; revert G
  | H : ~ ~ _ |- ~ _
  => intros G; apply H; clear H; intros H; revert G
  end.
End DN.
