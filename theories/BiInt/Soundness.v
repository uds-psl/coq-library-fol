Require Import List.
Require Import Ensembles.
Require Import Lia.

From Undecidability.FOL Require Import Syntax.Facts.

From FOL Require Import GenT Gen.
From FOL Require Import BiInt.BiInt SyntaxFeatures HilbertCalc KripkeSemantics.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Import BiIntSyntax.

(* ** Soundness **)

Section Soundness_LEM.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Existing Instance falsity_on.

Axiom LEM : forall P, P \/ ~ P.

Lemma ksat_dec : forall (A : form) D (M : kmodel D) u rho,
    (ksat _ u rho A) \/ ((ksat _ u rho A) -> False).
Proof.
intros. apply LEM.
Qed.

Lemma Ax_valid : forall A, Axioms A -> kvalid A.
Proof.
intros A AX. inversion AX ; subst ; intros w M u rho ; cbn ; intros ; auto.
- apply ksat_mon with v ; auto.
- apply H0 with v1 ; auto. apply reach_tran with v0 ; auto. apply reach_refl.
- destruct H4. apply H0 ; auto. apply (reach_tran H1 H3). apply H2 ; auto.
- destruct H0 ; auto.
- destruct H0 ; auto.
- split. apply H0 ; auto. apply (reach_tran H1 H3). apply H2 ; auto.
- inversion H0.
(* Bi int axioms *)
- destruct (ksat_dec B v rho) ; auto. right. intro H2.
  apply H1. apply H2 ; auto. apply reach_refl.
- intros H1. apply H0. intros. apply H1 with v0 ; auto. apply reach_refl.
- intro. apply H0. intros.
  pose (ksat_dec C v0 rho). destruct o ; auto. exfalso.
  assert (~ ~ ((exists v, reachable v v0 /\ ksat _ v rho A0 /\ ~ ksat _ v rho B) \/ ~ (exists v, reachable v v0 /\ ksat _ v rho A0 /\ ~ ksat _ v rho B))) by tauto.
  apply H5. intros [(v1 & H6 & H7 & H8)|H6].
  + apply H1 in H7 as [H7|H7]; try tauto.
    * apply H4. now apply ksat_mon with v1.
    * now apply reach_tran with v0.
  + apply H3. intros. pose (ksat_dec B v1 rho).
    destruct o. auto. contradict H6. now exists v1.
- pose (@H0 v0 H1). pose (ksat_dec B v0 rho).
  destruct o ; auto.
  exfalso. apply f. intro. apply H3, H4; trivial. apply reach_refl.
(* Quantifiers *)
- apply H0 ; auto. apply ksat_comp ; auto.
- apply ksat_comp. unfold funcomp. eapply (ksat_ext v). 2: eapply (H0 (eval rho _)).
  intros. unfold scons. destruct x ; auto.
- apply ksat_comp in H0. eexists (eval rho t). eapply (ksat_ext v). 2: eapply H0.
  unfold funcomp. intros. unfold scons. destruct x ; auto.
Qed.

Lemma Soundness : forall Γ A, FOBIH_prv Γ A -> loc_conseq Γ A.
Proof.
intros Γ A Hprv. induction Hprv; subst; cbn; intros D M u rho HX.
(* Id *)
- apply HX ; auto.
(* Ax *)
- apply Ax_valid ; auto.
(* MP *)
- unfold kvalid_ctx in IHHprv1,IHHprv2. pose (IHHprv1 _ _ _ _ HX). pose (IHHprv2 _ _ _ _ HX).
  simpl in k. apply k ; auto. apply reach_refl.
(* DN *)
- cbn. intros.
  assert (J1: kvalid_ctx (Empty_set _) A). apply IHHprv.
  apply H0. intros. apply J1 ; auto. intros. inversion H3.
(* Gen *)
- intro d. unfold kvalid_ctx in IHHprv. apply IHHprv. intros. inversion H. destruct H0 ; subst.
  apply HX in H1. apply ksat_comp. simpl. unfold funcomp. simpl. auto.
(* EC *)
- intros w Ha0 Ha1. unfold loc_conseq in IHHprv. destruct Ha1.
  assert (J2: forall psi : form, (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) psi -> (ksat _ u (x .: rho)) psi). intros.
  destruct H0. destruct H0. subst. apply HX in H1. apply ksat_comp.
  simpl. unfold funcomp. simpl. auto. pose (IHHprv _ _ u (x .: rho) J2).
  simpl in k. apply k in H ; auto. apply ksat_comp in H. unfold funcomp in H. simpl in H. auto.
Qed.

End Soundness_LEM.
