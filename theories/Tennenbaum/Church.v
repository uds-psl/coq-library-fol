From FOL Require Import FullSyntax Arithmetics Theories.
From Undecidability.Shared Require Import ListAutomation.
From FOL.Tennenbaum Require Import NumberUtils DN_Utils Formulas SyntheticInType Peano.
From FOL.Incompleteness Require Import qdec sigma1 ctq.

(* Require Import FOL Tarski Deduction Peano Formulas NumberTheory Synthetic DecidabilityFacts. *)
Require Import Lia.
From Equations Require Import Equations.

Import Vector.VectorNotations.

Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).

Definition unary α := bounded 1 α.
Definition binary α := bounded 2 α.

Section ChurchThesis.
Existing Instance PA_preds_signature.
Existing Instance PA_funcs_signature.

Context {peirce : peirce}.
Instance ff : falsity_flag := falsity_on.

(** Church's Thesis *)

(** CT_Q  *)

(** CT_Q internalizes computability, by claiming that every function
    nat -> nat is computable in a model of computation. In this case,
    the model of computaion is based on arithmetic: It represents
    functions by formulas in the language of PA in such a way that a
    weak fragment (Q ⊆ PA) can prove the agreement of the formula
    with the function on every input.
 *)

Notation Q := Qeq.

Definition represents φ f := forall x, Q ⊢ ∀ φ[num x .: $0..] ↔ $0 == num (f x).
Definition CT_Q := forall f : nat -> nat, exists φ, bounded 2 φ /\ Σ1 φ /\ represents φ f.
(** WCT_Q is a weaker Version of CT_Q, where the existence of the formula
    is only given potentially (i.e. behing a double negation).
 *)
Definition WCT_Q := forall f : nat -> nat, ~~exists φ, bounded 2 φ /\ Σ1 φ /\ represents φ f.

Lemma prime_div_relation :
  CT_Q -> exists Π, bounded 2 Π /\ Σ1 Π /\
    forall x, Q ⊢ ∀ Π[num x .: $0..] ↔ $0 == num (Irred x).
Proof.
  intros ct. apply ct.
Qed.

(** Strong Representability *)

Definition strong_repr ϕ (p : nat -> Prop) :=
  (forall x, p x -> Q ⊢ ϕ[(num x)..]) /\ (forall x, ~ p x -> Q ⊢ ¬ϕ[(num x)..]).
Definition RT_strong :=
  forall p : nat -> Prop, Dec p -> exists ϕ, bounded 1 ϕ /\ Σ1 ϕ /\ strong_repr ϕ p.
Definition WRT_strong :=
  forall p : nat -> Prop, Dec p -> ~ ~ exists ϕ, bounded 1 ϕ /\ Σ1 ϕ /\ strong_repr ϕ p.

(** Weak Representability *)

Definition weak_repr ϕ (p : nat -> Prop) := (forall x, p x <-> Q ⊢ ϕ[(num x)..]).
Definition RT_weak :=
  forall p : nat -> Prop, enumerable p -> exists ϕ, bounded 1 ϕ /\ Σ1 ϕ /\ weak_repr ϕ p.
Definition WRT_weak :=
  forall p : nat -> Prop, enumerable p -> ~ ~ exists ϕ, bounded 1 ϕ /\ Σ1 ϕ /\ weak_repr ϕ p.

Definition RT := RT_strong /\ RT_weak.

Lemma prv_split α β Γ :
  Γ ⊢ α ↔ β <-> Γ ⊢ (α → β) /\ Γ ⊢ (β → α).
Proof.
 split; intros H.
  - split.
    + eapply CE1. apply H.
    + eapply CE2. apply H.
  - now constructor.
Qed.

Lemma CT_WCT :
  CT_Q -> WCT_Q.
Proof. intros ct f. specialize (ct f). tauto. Qed.

Hint Resolve CT_WCT : core.

(** Strong part of the representability theorem.  *)
Lemma CT_RTs :
  CT_Q -> RT_strong.
Proof.
  intros ct p Dec_p.
  destruct (Dec_decider_nat _ Dec_p) as [f Hf].
  destruct (ct f) as [ϕ (bϕ2 & Sϕ & Hϕ)].
  exists ϕ[$0 .: (num 0) ..].
  assert (forall a b c, ϕ[a .: b .: c..] = ϕ[a .: b..]) as Help.
  { intros *. eapply bounded_subst; eauto.
    intros [|[]]; simpl; lia || reflexivity. }
  repeat split.
  { eapply subst_bound; eauto. 
    intros [|[]] ?; try lia; simpl; solve_bounds. }
  { now apply Σ1_subst. }
  all: intros x; specialize (Hϕ x).
  all: eapply AllE with (t := num 0) in Hϕ; cbn -[Q] in Hϕ.
  all: asimpl; asimpl in Hϕ.
  all: rewrite !num_subst in *; rewrite Help in *.
  all: apply prv_split in Hϕ; destruct Hϕ as [H1 H2].
  - intros px%Hf. symmetry in px.
    eapply num_eq with (Gamma := Q) in px; [|firstorder].
    eapply IE. cbn -[Qeq num].
    apply H2. apply px.
  - intros npx. assert (0 <> f x) as E by firstorder.
    apply num_neq with (Gamma := Q)in E; [|firstorder].
    apply II. eapply IE.
    {eapply Weak; [apply E|now right]. }
    eapply IE; [|apply Ctx; now left].
    eapply Weak.
    + cbn -[Q num]. apply H1.
    + now right.
Qed.


Lemma WCT_WRTs :
  WCT_Q -> WRT_strong.
Proof.
  intros wct p Dec_p.
  destruct (Dec_decider_nat _ Dec_p) as [f Hf].
  apply (DN.bind_ (wct f)).
  intros [ϕ (bϕ2 & Sϕ & Hϕ)]. DN.ret.
  exists ϕ[$0 .: (num 0) ..].
  assert (forall a b c, ϕ[a .: b .: c..] = ϕ[a .: b..]) as Help.
  { intros *. eapply bounded_subst; eauto.
    intros [|[]]; simpl; lia || reflexivity. }
  repeat split.
  { eapply subst_bound; eauto. 
    intros [|[]] ?; try lia; simpl; solve_bounds. }
  { now apply Σ1_subst. }
  all: intros x; specialize (Hϕ x).
  all: eapply AllE with (t := num 0) in Hϕ; cbn -[Q] in Hϕ.
  all: asimpl; asimpl in Hϕ.
  all: rewrite !num_subst in *; rewrite Help in *.
  all: apply prv_split in Hϕ; destruct Hϕ as [H1 H2].
  - intros px%Hf. symmetry in px.
    eapply num_eq with (Gamma := Q) in px; [|firstorder].
    eapply IE. cbn -[Q num].
    apply H2. apply px.
  - intros npx. assert (0 <> f x) as E by firstorder.
    apply num_neq with (Gamma := Q) in E; [|firstorder].
    apply II. eapply IE.
    {eapply Weak; [apply E|now right]. }
    eapply IE; [|apply Ctx; now left].
    eapply Weak.
    + cbn -[Q num]. apply H1.
    + now right.
Qed.

(** Weak part of the representability theorem.  *)
Lemma CT_RTw :
  CT_Q -> RT_weak.
Proof.
  intros ct p Hp. unfold weak_repr.
  apply ctq_weak_repr; auto.
Qed.



End ChurchThesis.
