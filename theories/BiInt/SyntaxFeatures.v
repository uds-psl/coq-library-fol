Require Import Coq.Vectors.Vector.
Local Notation vec := Vector.t.
Require Import Ensembles.
(* From Equations Require Export Equations. *)

From Undecidability.FOL Require Import Syntax.Facts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
From FOL Require Import BiInt.BiInt.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Import BiIntSyntax.

Section BiIntSyntaxFeatures.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Existing Instance falsity_on.

  (* Induction principle for terms *)

  Inductive ForallT {A : Type} (P : A -> Type) : forall {n}, t A n -> Type :=
  | ForallT_nil : ForallT P (@Vector.nil A)
  | ForallT_cons : forall n (x : A) (l : t A n), P x -> ForallT P l -> ForallT P (@Vector.cons A x n l).

  Inductive vec_in {A : Type} (a : A) : forall {n}, t A n -> Type :=
  | vec_inB {n} (v : t A n) : vec_in a (Vector.cons A a n v)
  | vec_inS a' {n} (v : t A n) : vec_in a v -> vec_in a (Vector.cons A a' n v).
  Hint Constructors vec_in : core.

  Lemma term_rectT' (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (ForallT p v) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. fix strong_term_ind' 1. destruct t as [n | F v].
    - apply f1.
    - apply f2. induction v.
      + econstructor.
      + econstructor. now eapply strong_term_ind'. eauto.
  Qed.

  Lemma term_rectT (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inversion X; subst; eauto.
  Qed.

  Lemma term_indT (p : term -> Prop) :
    (forall x, p (var x)) -> (forall F v (IH : forall t, Vector.In t v -> p t), p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rectT'.
    - apply f1.
    - intros. apply f2. intros t. induction 1 ; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; subst; eauto. decide equality.
  Qed.

Lemma strong_term_indT' (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (ForallT p v) -> p (func F v)) -> forall (t : term), p t.
Proof.
  intros f1 f2. fix strong_term_ind' 1. destruct t as [n| F v].
  - apply f1.
  - apply f2. induction v.
    + econstructor.
    + econstructor. now eapply strong_term_ind'. eauto.
Qed.

Ltac resolve_existT := try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2; [subst | try (eauto || now intros; decide equality)]
  end.

Ltac inv H :=
  inversion H; subst; resolve_existT.

Lemma strong_term_indT (p : term -> Type) :
     (forall x, p ($x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
Proof.
intros f1 f2. eapply strong_term_indT'.
- apply f1.
- intros. apply f2. intros t. induction 1 ; inv X ; eauto.
Qed.

Fixpoint DN_form (n : nat) (A : form) : form :=
match n with
 | 0 => A
 | S m =>  (¬ (∞ (DN_form m A)))
end.

Inductive DN_clos_set (Γ : @Ensemble form): @Ensemble form :=
  | InitClo : forall A, Ensembles.In _ Γ A -> DN_clos_set Γ A
  | IndClo : forall A,  DN_clos_set Γ A -> DN_clos_set Γ (¬ (∞ A)).

  Lemma form_subst_help phi :
    phi[up ↑][$0..] = phi.
  Proof.
    rewrite subst_comp. apply subst_id. now intros [].
  Qed.

Hypothesis eq_dec_funcs : eq_dec Σ_funcs.
Hypothesis eq_dec_preds : eq_dec Σ_preds.

Lemma eq_dec_term : forall x y : term, {x = y}+{x <> y}.
Proof.
apply dec_term ; auto.
Qed.

Lemma eq_dec_form : forall x y : form, {x = y}+{x <> y}.
Proof.
apply dec_form ; auto.
- intros ; induction x ; destruct y ; try (now left ; auto).
  all: right ; intro ; discriminate.
- intros ; induction x ; destruct y ; try (now left ; auto).
  all: right ; intro ; discriminate.
Qed.

  Lemma form_all phi :
    { psi | phi = ∀ psi } + (~ exists psi, phi = ∀ psi).
  Proof.
    destruct phi; try destruct q. 1-3,5: right; intros [psi H]; discriminate.
    left. exists phi. reflexivity.
  Qed.

  Lemma form_ex phi :
    { psi | phi = ∃ psi } + (~ exists psi, phi = ∃ psi).
  Proof.
    destruct phi; try destruct q. 1-4: right; intros [psi H]; discriminate.
    left. exists phi. reflexivity.
  Qed.

End BiIntSyntaxFeatures.


(* Section PredicateSubstitution.

(* Atom substitution. *)

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

Fixpoint atom_subst {ff : falsity_flag} (s : forall (P : Σ_preds), Vector.t (@term Σ_funcs) (ar_preds P) -> form) (phi : form) :=
    match phi with
    | falsity => falsity
    | atom P t => s P t
    | bin b phi psi => bin b (atom_subst s phi) (atom_subst s psi)
    | quant q phi => quant q (atom_subst s phi) 
    end.

  Notation "phi [ s '/atom' ]" := (atom_subst s phi) (at level 7, left associativity) : subst_scope.

  Definition atom_subst_respects  (s : forall (P : Σ_preds), Vector.t (@term Σ_funcs) (ar_preds P) -> form)
    := forall P v sigma, (s P v)[sigma>> var] = s P (map (subst_term (sigma >> var)) v).

  Definition atom_subst_respects_strong (s : forall (P : Σ_preds), Vector.t (@term Σ_funcs) (ar_preds P) -> form)
    := forall P v sigma, (s P v)[sigma] = s P (map (subst_term (sigma)) v).

  Lemma atom_subst_strong_to_normal s :  atom_subst_respects_strong s ->  atom_subst_respects s.
  Proof.
  intros. intro. intros. auto.
  Qed.

  Lemma atom_subst_id phi : phi[ atom /atom] = phi.
  Proof.
    induction phi.
    - easy.
    - cbn. easy.
    - cbn. easy.
    - cbn. rewrite IHphi1. now rewrite IHphi2.
    - cbn. now rewrite IHphi.
  Qed.

  Lemma up_var_comp rho x : (up (rho >> var)) x = ((fun n => match n with 0 => 0 | S n => S (rho n) end) >>var) x.
  Proof.
    now destruct x.
  Qed.

  Lemma atom_subst_comp s rho phi : atom_subst_respects s -> phi[s/atom][rho>>var] = phi[rho>>var][s/atom].
  Proof.
  intros Hresp.
  induction phi in s,rho,Hresp|-*.
  - easy.
  - easy.
  - cbn.  easy.
  - cbn. rewrite IHphi1. 1: now rewrite IHphi2. easy.
  - cbn. f_equal. rewrite ! (subst_ext _ _ _ (up_var_comp _) ). rewrite IHphi. 1:easy.
    easy.
  Qed.

  Lemma atom_subst_comp_strong s rho phi :
    atom_subst_respects_strong s -> phi[s/atom][rho] = phi[rho][s/atom].
  Proof.
  intros Hresp.
  induction phi in s,rho,Hresp|-*.
  - easy.
  - cbn. easy.
  - cbn. easy.
  - cbn. rewrite IHphi1. 1: now rewrite IHphi2. easy.
  - cbn. now rewrite IHphi.
  Qed.

End PredicateSubstitution.

#[global] Notation "phi [ s '/atom' ]" := (atom_subst s phi) (at level 7, left associativity) : subst_scope. *)

