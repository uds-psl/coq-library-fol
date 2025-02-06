Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

From Undecidability.FOL Require Import Syntax.Facts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.

From FOL Require Import GenT Gen.
From FOL Require Import BiInt.BiInt SyntaxFeatures HilbertCalc RemoveList LogicProp.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Import BiIntSyntax.


Section Properties.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Existing Instance falsity_on.

  Context {eq_dec_preds : eq_dec Σ_preds}.
  Context {eq_dec_funcs : eq_dec Σ_funcs}.

Notation "x 'el' L" := (List.In x L) (at level 70).
Notation "T |- phi" := (FOBIH_prv T phi) (at level 80).
Notation adj T phi := (fun psi => T psi \/ psi = phi).


Lemma Thm_irrel : forall A B Γ, FOBIH_prv Γ (A → (B → A)).
Proof.
intros A B Γ. apply Ax ; eapply A1 ; reflexivity.
Qed.

Lemma imp_Id_gen : forall A Γ, FOBIH_prv Γ (A → A).
Proof.
intros.
eapply MP. eapply MP.
apply Ax ; eapply A2 ; reflexivity.
apply Ax ; eapply A1 ; reflexivity.
eapply MP.
apply Ax ; eapply A1 ; reflexivity.
apply Ax ; apply A1 with (⊥ → ⊥) ⊥ ; reflexivity.
Qed.

Lemma comm_And_obj : forall A B Γ,
    FOBIH_prv Γ ((A ∧ B) → (B ∧ A)).
Proof.
intros A B Γ. eapply MP. eapply MP.
apply Ax ; eapply A8 ; reflexivity.
apply Ax ; eapply A7 ; reflexivity.
apply Ax ; eapply A6 ; reflexivity.
Qed.

Lemma comm_Or_obj : forall A B Γ, FOBIH_prv Γ (A ∨ B →  B ∨ A).
Proof.
intros A B Γ. eapply MP. eapply MP.
apply Ax ; eapply A5 ; reflexivity.
apply Ax ; eapply A4 ; reflexivity.
apply Ax ; eapply A3 ; reflexivity.
Qed.

Lemma comm_Or : forall A B Γ, FOBIH_prv Γ (A ∨ B) -> FOBIH_prv Γ (B ∨ A).
Proof.
intros A B Γ D. eapply MP. apply comm_Or_obj. auto.
Qed.

Lemma EFQ : forall A Γ, FOBIH_prv Γ (⊥ →  A).
Proof.
intros A Γ. apply Ax. eapply A9 ; reflexivity.
Qed.

Lemma Imp_trans_help7 : forall x y z Γ, FOBIH_prv Γ ((x → (y → (z → y)))).
Proof.
intros. eapply  MP. all: apply Ax ; eapply A1 ; reflexivity.
Qed.

Lemma Imp_trans_help8 : forall x y z Γ,
  FOBIH_prv Γ ((((x → (y → z)) → (x → y)) → ((x → (y → z)) → (x → z)))).
Proof.
intros. eapply  MP. all: apply Ax ; eapply A2 ; reflexivity.
Qed.

Lemma Imp_trans_help9 : forall x y z u Γ,
  FOBIH_prv Γ ((x → ((y → (z → u)) → ((y → z) → (y → u))))).
Proof.
intros. eapply  MP. all: apply Ax.
eapply A1 ; reflexivity. eapply A2 ; reflexivity.
Qed.

Lemma Imp_trans_help14 : forall x y z u Γ,
  FOBIH_prv Γ ((x → (y → (z → (u → z))))).
Proof.
intros. eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Imp_trans_help7.
Qed.

Lemma Imp_trans_help35 : forall x y z Γ, FOBIH_prv Γ ((x → ((y → x) → z)) → (x → z)).
Proof.
intros. eapply  MP. apply Imp_trans_help8. apply Imp_trans_help7.
Qed.

Lemma Imp_trans_help37 : forall x y z u Γ, FOBIH_prv Γ (((x → ((y → (z → y)) → u)) → (x → u))).
Proof.
intros. eapply  MP. apply Imp_trans_help8. apply Imp_trans_help14.
Qed.

Lemma Imp_trans_help54 : forall x y z u Γ,
  FOBIH_prv Γ ((((x → (y → z)) → (((x → y) → (x → z)) → u)) → ((x → (y → z)) → u))).
Proof.
intros. eapply  MP. apply Imp_trans_help8. apply Imp_trans_help9.
Qed.

Lemma Imp_trans_help170 : forall x y z Γ, FOBIH_prv Γ ((x → y) → ((z → x) → (z → y))).
Proof.
intros. eapply  MP. apply Imp_trans_help35. apply Imp_trans_help9.
Qed.

Lemma Imp_trans_help410 : forall x y z Γ,
  FOBIH_prv Γ ((((x → y) → z) → (y → z))).
Proof.
intros. eapply MP. apply Imp_trans_help37. apply Imp_trans_help170.
Qed.

Lemma Imp_trans_help427 : forall x y z u Γ,
  FOBIH_prv Γ ((x → (((y → z) → u) → (z → u)))).
Proof.
intros. eapply  MP. apply Ax ; eapply A1 ; reflexivity. apply Imp_trans_help410.
Qed.

Lemma Imp_trans : forall A B C Γ, FOBIH_prv Γ ((A → B) →  (B → C) → (A → C)).
Proof.
intros. eapply  MP. eapply  MP. apply Imp_trans_help54. apply Imp_trans_help427.
apply Imp_trans_help170.
Qed.

Lemma monotR_Or : forall A B Γ ,
    FOBIH_prv Γ (A →  B) ->
    forall C, FOBIH_prv Γ ((A ∨ C) →  (B ∨ C)).
Proof.
intros A B Γ D C. eapply MP. eapply MP.
apply Ax ; eapply A5 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans. exact D.
apply Ax ; eapply A3 ; reflexivity.
apply Ax ; eapply A4 ; reflexivity.
Qed.

Lemma monotL_Or : forall A B Γ,
    FOBIH_prv Γ (A →  B) ->
    forall C, FOBIH_prv Γ ((C ∨ A) →  (C ∨ B)).
Proof.
intros A B Γ D C. eapply MP. eapply MP.
apply Ax ; eapply A5 ; reflexivity.
apply Ax ; eapply A3 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans. exact D.
apply Ax ; eapply A4 ; reflexivity.
Qed.

Lemma monot_Or2 : forall A B Γ, FOBIH_prv Γ (A →  B) ->
    forall C, FOBIH_prv Γ ((A ∨ C) →  (C ∨ B)).
Proof.
intros A B Γ D C.
eapply MP. eapply MP.
apply Ax ; eapply A5 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans. exact D.
apply Ax ; eapply A4 ; reflexivity.
apply Ax ; eapply A3 ; reflexivity.
Qed.

Lemma A10 : forall Γ A, FOBIH_prv Γ (A → ⊤).
Proof.
intros. eapply MP. apply Thm_irrel. apply imp_Id_gen.
Qed.

Lemma prv_Top : forall Γ , FOBIH_prv Γ ⊤.
Proof.
apply imp_Id_gen.
Qed.

Lemma absorp_Or1 : forall A Γ ,
    FOBIH_prv Γ (A ∨ ⊥) ->
    FOBIH_prv Γ A.
Proof.
intros A Γ D. eapply MP. eapply MP. eapply MP.
apply Ax ; eapply A5 ; reflexivity.
apply imp_Id_gen. apply EFQ. auto.
Qed.

Lemma absorp_Or2 : forall A Γ ,
    FOBIH_prv Γ (⊥ ∨ A) ->
    FOBIH_prv Γ A.
Proof.
intros A Γ D. eapply MP. eapply MP. eapply MP.
apply Ax ; eapply A5 ; reflexivity.
apply EFQ. apply imp_Id_gen. auto.
Qed.

Lemma Imp_And : forall A B C Γ, FOBIH_prv Γ ((A →  (B →  C)) → ((A ∧ B) →  C)).
Proof.
intros A B C Γ. eapply MP. eapply MP. apply Imp_trans. eapply MP. apply Imp_trans.
apply Ax ; eapply A6 ; reflexivity.
eapply MP. eapply MP.
apply Ax ; eapply A2 ; reflexivity.
apply Ax ; eapply A2 ; reflexivity.
eapply MP.
apply Ax ; eapply A1 ; reflexivity.
apply Ax ; eapply A7 ; reflexivity.
Qed.

Lemma Contr_Bot : forall A Γ, FOBIH_prv Γ (A ∧ (¬ A) →  (⊥)).
Proof.
intros A Γ . eapply MP. eapply MP. apply Imp_trans.
apply comm_And_obj. eapply MP. apply Imp_And.
apply imp_Id_gen.
Qed.

(* The next proof is rather obscure, as it was generated by prover9. *)

Lemma And_Imp : forall A B C Γ, FOBIH_prv Γ (((A ∧ B) →  C) → (A → (B →  C))).
Proof.
intros.
eapply MP.
- eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. eapply MP.
  1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity.
- eapply MP.
  { eapply MP. eapply MP. eapply MP. eapply MP.
  eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP.
  apply Ax ; eapply A1 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity. eapply MP. eapply MP.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP.
  apply Ax ; eapply A1 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity. eapply MP. eapply MP.
  eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity. eapply MP.
  eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. eapply MP. apply Ax ; eapply A8 ; reflexivity. eapply MP. eapply MP.
  apply Ax ; eapply A2 ; reflexivity. apply Ax ; eapply A1 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. eapply MP.
  1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity. eapply MP.
  eapply MP. apply Ax ; eapply A2 ; reflexivity. eapply MP. apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity. apply Ax ; eapply A7 ; reflexivity.
  apply Ax ; eapply A6 ; reflexivity. eapply MP. eapply MP.
  eapply MP. apply Ax ; eapply A2 ; reflexivity. apply Ax ; eapply A8 ; reflexivity. eapply MP.
  apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A7 ; reflexivity. eapply MP. eapply MP.
  eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A6 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity. eapply MP. apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity. apply Ax ; eapply A8 ; reflexivity. eapply MP.
  apply Ax ; eapply A1 ; reflexivity. eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity. apply Ax ; eapply A1 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity. }
  { eapply MP. eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. eapply MP.
  1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity. 
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity. }
Unshelve. all: auto.
Qed.


Theorem FOBIH_Detachment_Theorem : forall A B Γ,
           FOBIH_prv Γ (A → B) ->
           FOBIH_prv  (Union _ Γ  (Singleton _ (A))) B.
Proof.
intros A B Γ D. eapply MP. apply (@FOBIH_monot _ _ Γ (A → B)) ; auto.
intros C HC. apply Union_introl ; auto.
apply Id. apply Union_intror. apply In_singleton.
Qed.

Theorem FOBIH_Deduction_Theorem : forall A B Γ,
           FOBIH_prv (Union _ Γ  (Singleton _ (A))) B ->
           FOBIH_prv Γ (A →  B).
Proof.
intros. remember (Union form Γ (Singleton form A)) as L.
revert L B H A Γ HeqL.
intros L B D. induction D ; intros C Γ0 id ; subst.
(* Id *)
- inversion H ; subst ; cbn.
  + eapply MP. apply Thm_irrel. apply Id ; auto.
  + inversion H0 ; subst. apply imp_Id_gen.
(* Ax *)
- eapply MP. apply Thm_irrel. apply Ax ; assumption.
(* MP *)
- eapply MP. eapply MP. apply Imp_trans. eapply MP.
  eapply MP. apply Ax ; eapply A8 ; reflexivity. apply imp_Id_gen.
  apply IHD2 ; auto. eapply MP. apply Imp_And. apply IHD1 ; auto.
(* DN *)
- eapply MP. apply Thm_irrel. apply DN ; auto.
(* Gen *)
- assert (FOBIH_prv (fun x : form => exists B : form, x = B[↑] /\ Ensembles.In form Γ0 B) ((subst_form ↑ C) → A)).
  apply IHD. apply Extensionality_Ensembles. split ; intro ; intro ; unfold In in *.
  destruct H as (B & HB0 & HB1) ; subst. inversion HB1 ; subst. left ; exists B ; firstorder.
  inversion H ; subst. right ; apply In_singleton. inversion H ; subst.
  destruct H0 as (B & HB0 & HB1) ; subst. exists B ; split ; auto. left ; auto.
  inversion H0 ; subst. exists C ; firstorder. right ; apply In_singleton.
  eapply MP. apply Ax ; eapply QA1 with C A. reflexivity.
  apply Gen ; auto.
(* EC *)
- assert (FOBIH_prv (fun x : form => exists B : form, x = B[↑] /\ Ensembles.In form Γ0 B) (C[↑] → A → B[↑])).
  apply IHD. apply Extensionality_Ensembles. split ; intro ; intro ; unfold In in *.
  destruct H as (E & HE0 & HE1) ; subst. inversion HE1 ; subst. left ; exists E ; firstorder.
  inversion H ; subst. right ; apply In_singleton. inversion H ; subst.
  destruct H0 as (E & HE0 & HE1) ; subst. exists E ; split ; auto. left ; auto.
  inversion H0 ; subst. exists C ; firstorder. right ; apply In_singleton.
  eapply MP. apply And_Imp. eapply MP. eapply MP. apply Imp_trans.
  apply comm_And_obj. eapply MP. apply Imp_And. apply EC. eapply MP.
  apply And_Imp. eapply MP. eapply MP. apply Imp_trans. apply comm_And_obj.
  eapply MP. apply Imp_And. auto.
Qed.

Theorem gen_FOBIH_Detachment_Theorem : forall A B Γ,
  pair_der Γ (Singleton _ (A → B)) ->
      pair_der (Union form Γ (Singleton form A))  (Singleton _ B).
Proof.
intros A B Γ wpair. unfold pair_der. exists [B]. repeat split.
apply NoDup_cons. intro. inversion H. apply NoDup_nil. intros. inversion H ; auto.
subst. cbn. apply In_singleton. inversion H0.
cbn. eapply MP. apply Ax ; eapply A3 ; reflexivity.
destruct wpair as (l & Hl0 & Hl1 & Hl2). destruct l ; cbn in *.
eapply MP. apply EFQ. apply (@FOBIH_monot _ _ _ _ Hl2).
intros C HC ; left ; auto.
destruct l. cbn in *. assert (Singleton form (A → B) f). apply Hl1 ; auto.
inversion H ; subst. apply absorp_Or1 in Hl2. apply FOBIH_Detachment_Theorem in Hl2 ; auto.
exfalso. cbn in *. assert (Singleton form (A → B) f). apply Hl1 ; auto.
assert (Singleton form (A → B) f0). apply Hl1 ; auto. inversion H ; subst.
inversion H0 ; subst. inversion Hl0 ; subst. apply H3 ; apply in_eq.
Qed.

Theorem gen_FOBIH_Deduction_Theorem : forall A B Γ,
  pair_der (Union form Γ (Singleton form A)) (Singleton _ B) ->
      pair_der Γ (Singleton _ (A → B)).
Proof.
intros A B Γ wpair. unfold pair_der. cbn. exists [(A → B)]. repeat split.
apply NoDup_cons. intro. inversion H. apply NoDup_nil. intros. inversion H ; auto.
subst. apply In_singleton. inversion H0.
eapply MP. apply Ax ; eapply A3 ; reflexivity.
apply FOBIH_Deduction_Theorem.
destruct wpair as (l & Hl0 & Hl1 & Hl2). destruct l ; cbn in *.
eapply MP. apply EFQ. auto.
destruct l. cbn in *. assert (Singleton form B f). apply Hl1 ; auto.
inversion H ; subst. apply absorp_Or1 in Hl2 ; auto.
exfalso. cbn in *. assert (Singleton form B f). apply Hl1 ; auto.
assert (Singleton form B f0). apply Hl1 ; auto. inversion H ; subst.
inversion H0 ; subst. inversion Hl0 ; subst. apply H3 ; apply in_eq.
Qed.









Section remove_stuff.

Lemma In_remove : forall (A : form) B (l : list (form)), List.In A (remove (eq_dec_form eq_dec_funcs eq_dec_preds) B l) -> List.In A l.
Proof.
intros A B. induction l.
- cbn. auto.
- intro. cbn in H. destruct (eq_dec_form eq_dec_funcs eq_dec_preds B a).
  * subst. apply in_cons. apply IHl. assumption.
  * inversion H.
    + subst. apply in_eq.
    + subst. apply in_cons. apply IHl. auto.
Qed.

Lemma InT_remove : forall (A : form) B (l : list (form)), InT A (remove (eq_dec_form eq_dec_funcs eq_dec_preds) B l) -> InT A l.
Proof.
intros A B. induction l.
- cbn. auto.
- intro. cbn in X. destruct (eq_dec_form eq_dec_funcs eq_dec_preds B a).
  * subst. apply InT_cons. apply IHl. assumption.
  * inversion X.
    + subst. apply InT_eq.
    + subst. apply InT_cons. apply IHl. auto.
Qed.

Lemma NoDup_remove : forall A (l : list (form)), NoDup l -> NoDup (remove (eq_dec_form eq_dec_funcs eq_dec_preds) A l).
Proof.
intro A. induction l.
- intro. cbn. apply NoDup_nil.
- intro H. cbn. destruct (eq_dec_form eq_dec_funcs eq_dec_preds A a).
  * subst. apply IHl. inversion H. assumption.
  * inversion H. subst. apply NoDup_cons. intro. apply H2. apply In_remove with (B:= A).
    assumption. apply IHl. assumption.
Qed.

Lemma remove_disj : forall l B Γ, FOBIH_prv Γ (list_disj l → B ∨ (list_disj (remove (eq_dec_form eq_dec_funcs eq_dec_preds) B l))).
Proof.
induction l.
- intros. cbn. apply Ax ; eapply A4 ; reflexivity.
- intros. pose (IHl B Γ). cbn. destruct (eq_dec_form eq_dec_funcs eq_dec_preds B a).
  * subst. cbn. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
    apply Ax ; eapply A3 ; reflexivity. auto.
  * cbn. eapply MP. eapply MP. apply Imp_trans. eapply MP. eapply MP.
    apply Ax ; eapply A5 ; reflexivity. apply Ax ; eapply A3 ; reflexivity.
    eapply MP. eapply MP. apply Imp_trans. auto. apply Ax ; eapply A4 ; reflexivity.
    eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity. eapply MP. eapply MP.
    apply Imp_trans. apply Ax ; eapply A3 ; reflexivity. apply Ax ; eapply A4 ; reflexivity.
    apply monotL_Or. apply Ax ; eapply A4 ; reflexivity.
Qed.

End remove_stuff.







Section list_disj_stuff.

Lemma Id_list_disj : forall Γ l0 l1,
  FOBIH_prv Γ (list_disj l0 → list_disj (l0 ++ l1)).
Proof.
induction l0 ; intros.
- cbn. apply EFQ.
- cbn. apply monotL_Or. apply IHl0.
Qed.

Lemma list_disj_app : forall l0 Γ A l1,
  FOBIH_prv Γ (A → list_disj (l0 ++ l1)) -> FOBIH_prv Γ (A → ((list_disj l0) ∨ (list_disj l1))).
Proof.
induction l0.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans. exact H.
  apply Ax ; eapply A4 ; reflexivity.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans. exact H. eapply MP.
  eapply MP. apply Imp_trans. apply monotL_Or. apply IHl0. apply imp_Id_gen.
  eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
  eapply MP. eapply MP. apply Imp_trans. apply Ax ; eapply A3 ; reflexivity.
  apply Ax ; eapply A3 ; reflexivity. apply monotR_Or.
  apply Ax ; eapply A4 ; reflexivity.
Qed.

Lemma list_disj_app0 : forall l0 Γ A l1,
  FOBIH_prv Γ (A → ((list_disj l0) ∨ (list_disj l1))) -> FOBIH_prv Γ (A → list_disj (l0 ++ l1)).
Proof.
induction l0.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans. exact H. eapply MP.
  eapply MP. apply Ax ; eapply A5 ; reflexivity. apply EFQ. apply imp_Id_gen.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans. exact H. eapply MP.
  eapply MP. apply Imp_trans. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
  apply monotL_Or. apply Ax ; eapply A3 ; reflexivity. eapply MP. eapply MP.
  apply Imp_trans. apply Ax ; eapply A4 ; reflexivity. apply Ax ; eapply A4 ; reflexivity.
  apply monotL_Or. apply IHl0. apply imp_Id_gen.
Qed.

Lemma list_disj_remove_app : forall l0 l1 Γ A,
FOBIH_prv Γ (list_disj (l0 ++ remove_list l0 l1) → A ∨ (list_disj (l0 ++ remove (eq_dec_form eq_dec_funcs eq_dec_preds) A (remove_list l0 l1)))).
Proof.
induction l0 ; cbn ; intros.
- apply remove_disj.
- eapply MP. eapply MP. apply Imp_trans. apply monotL_Or. eapply MP.
  eapply MP. apply Imp_trans. eapply MP. eapply MP. apply Imp_trans.
  eapply MP. eapply MP. apply Imp_trans. apply list_disj_app. apply imp_Id_gen.
  apply monotL_Or. apply remove_disj. eapply MP. eapply MP.
  apply Ax ; eapply A5 ; reflexivity. eapply MP. eapply MP. apply Imp_trans.
  apply Ax ; eapply A3 ; reflexivity. apply Ax ; eapply A4 ; reflexivity.
  apply monotL_Or. apply Ax ; eapply A4 ; reflexivity.
  apply monotL_Or. apply list_disj_app0. apply imp_Id_gen. 
  eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
  eapply MP. eapply MP. apply Imp_trans.
  apply Ax ; eapply A3 ; reflexivity. apply Ax ; eapply A4 ; reflexivity.
  apply monotL_Or. apply Ax ; eapply A4 ; reflexivity.
Qed.

Lemma Id_list_disj_remove : forall Γ l0 l1,
  FOBIH_prv Γ (list_disj l1 → list_disj (l0 ++ remove_list l0 l1)).
Proof.
induction l0 ; cbn ; intros.
- apply imp_Id_gen.
- eapply MP. eapply MP. apply Imp_trans. apply IHl0. apply list_disj_remove_app.
Qed.

Lemma der_list_disj_remove1 : forall Γ A l0 l1,
    FOBIH_prv Γ (A → list_disj l0) ->
    FOBIH_prv Γ (A → list_disj (l0 ++ remove_list l0 l1)).
Proof.
intros Γ A. induction l0 ; cbn in * ; intros.
- eapply MP. eapply MP. apply Imp_trans. exact H. apply EFQ.
- eapply MP. eapply MP. apply Imp_trans. exact H. apply monotL_Or.
  apply Id_list_disj.
Qed.

Lemma der_list_disj_remove2 : forall Γ A l0 l1,
    FOBIH_prv Γ (A → list_disj l1) ->
    FOBIH_prv Γ (A → list_disj (l0 ++ remove_list l0 l1)).
Proof.
intros. eapply MP. eapply MP. apply Imp_trans. exact H.
eapply MP. eapply MP. apply Imp_trans. apply Id_list_disj_remove.
apply imp_Id_gen.
Qed.

Lemma der_list_disj_bot : forall l Γ,
  FOBIH_prv Γ (list_disj l) -> FOBIH_prv Γ (list_disj (remove (eq_dec_form eq_dec_funcs eq_dec_preds) ⊥ l)).
Proof.
induction l ; cbn ; intros ; auto.
destruct (eq_dec_form eq_dec_funcs eq_dec_preds ⊥ a) ; subst.
- apply IHl. apply absorp_Or2 ; auto.
- eapply MP. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
  apply Ax ; eapply A3 ; reflexivity. eapply MP. eapply MP. apply Imp_trans.
  apply FOBIH_Deduction_Theorem. apply IHl. apply Id. right ; apply In_singleton.
  apply Ax ; eapply A4 ; reflexivity. auto.
Qed.

Lemma list_disj_remove_form : forall l Γ A,
  FOBIH_prv Γ (list_disj l) -> FOBIH_prv Γ (A ∨ list_disj (remove (eq_dec_form eq_dec_funcs eq_dec_preds) A l)).
Proof.
intros. pose (remove_disj l A Γ). apply FOBIH_Detachment_Theorem in f.
apply FOBIH_comp with (Γ':=Γ) in f ; auto. intros. inversion H0 ; subst.
apply Id ; auto. inversion H1 ; subst ; auto.
Qed.

Lemma list_disj_In0 : forall l Γ A,
  List.In A l ->
  FOBIH_prv Γ (A → list_disj l).
Proof.
induction l ; cbn ; intros ; try contradiction.
destruct H ; subst ; cbn in *.
- apply Ax ; eapply A3 ; reflexivity.
- eapply MP. eapply MP. apply Imp_trans.
  apply IHl ; auto. apply Ax ; eapply A4 ; reflexivity.
Qed.

Lemma list_disj_In : forall l Γ A,
  List.In A l ->
  FOBIH_prv Γ (A ∨ list_disj l) ->
  FOBIH_prv Γ (list_disj l).
Proof.
induction l ; cbn ; intros ; try contradiction.
eapply MP. eapply MP. eapply MP.
apply Ax ; eapply A5 ; reflexivity.
destruct H ; subst.
apply Ax ; eapply A3 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans.
apply list_disj_In0 ; auto. exact i. apply Ax ; eapply A4 ; reflexivity.
apply imp_Id_gen. auto.
Qed.

Lemma list_disj_app_distr : forall Γ l0 l1,
  FOBIH_prv Γ (list_disj l0 ∨ list_disj l1) ->
  FOBIH_prv Γ (list_disj (l0 ++ l1)).
Proof.
intros. eapply MP. apply list_disj_app0. apply imp_Id_gen. auto.
Qed.

Lemma list_disj_In_prv : forall Γ l0 l1,
  (forall A, List.In A l0 -> List.In A l1) ->
  FOBIH_prv Γ (list_disj l0) ->
  FOBIH_prv Γ (list_disj l1).
Proof.
intros Γ l0. revert l0 Γ. induction l0 ; cbn ; intros.
- eapply MP. apply EFQ. auto.
- eapply MP. eapply MP. eapply MP.
  apply Ax ; eapply A5 ; reflexivity.
  apply list_disj_In0 ; auto. apply FOBIH_Deduction_Theorem.
  apply IHl0 ; auto. apply Id ; right ; apply In_singleton. auto.
Qed.

Lemma list_disj_nodup : forall Γ l,
  FOBIH_prv Γ (list_disj l) ->
  FOBIH_prv Γ (list_disj (nodup (eq_dec_form eq_dec_funcs eq_dec_preds) l)).
Proof.
intros Γ l. revert Γ. induction l ; cbn ; intros ; auto.
destruct (in_dec (eq_dec_form eq_dec_funcs eq_dec_preds) a l).
- apply IHl ; auto. eapply MP. eapply MP. eapply MP.
  apply Ax ; eapply A5 ; reflexivity.
  apply list_disj_In0 ; exact i. apply imp_Id_gen.
  auto.
- cbn. eapply MP. eapply MP. eapply MP.
  apply Ax ; eapply A5 ; reflexivity.
  apply Ax ; eapply A3 ; reflexivity.
  eapply MP. eapply MP. apply Imp_trans.
  apply FOBIH_Deduction_Theorem. apply IHl. apply Id.
  right ; apply In_singleton.
  apply Ax ; eapply A4 ; reflexivity.
  auto.
Qed.

Lemma forall_list_disj : forall l Γ A,
  FOBIH_prv Γ (list_disj l) ->
  (forall B, List.In B l -> FOBIH_prv Γ (B → A)) ->
  FOBIH_prv Γ A.
Proof.
induction l ; cbn ; intros ; auto.
- eapply MP. apply EFQ. auto.
- eapply MP. eapply MP. eapply MP.
  apply Ax ; eapply A5 ; reflexivity.
  apply H0. left ; reflexivity.
  apply FOBIH_Deduction_Theorem. apply IHl.
  apply Id. right ; apply In_singleton.
  intros. apply FOBIH_monot with Γ. apply H0 ; auto.
  intros C HC ; left ; auto. auto.
Qed.

End list_disj_stuff.







Section list_conj_stuff.

Lemma list_conj_in_list : forall Γ l A,
  List.In A l ->
  FOBIH_prv Γ ((list_conj l) → A).
Proof.
induction l.
- intros. inversion H.
- intros. cbn. inversion H. subst. apply Ax ; eapply A6 ; reflexivity. apply IHl in H0.
  eapply MP. eapply MP. apply Imp_trans. apply Ax ; eapply A7 ; reflexivity. auto.
Qed.

Lemma finite_context_list_conj : forall Γ A,
  FOBIH_prv Γ A ->
  forall l, (forall A : form, (Γ A -> List.In A l) * (List.In A l -> Γ A)) ->
  FOBIH_prv (Singleton _ (list_conj l)) A.
Proof.
intros. apply (@FOBIH_comp _ _ _ _ H (Singleton form (list_conj l))). intros B HB.
eapply MP. apply list_conj_in_list. apply H0 ; exact HB.
apply Id. apply In_singleton.
Qed.

Lemma der_list_conj_finite_context : forall l (Γ : Ensemble _),
  (forall B : form, (Γ B -> List.In B l) * (List.In B l -> Γ B)) ->
  FOBIH_prv Γ (list_conj l).
Proof.
induction l ; intros.
- cbn. apply prv_Top.
- cbn. destruct (In_dec l a).
  + assert (forall B : form, (Γ B -> List.In B l) * (List.In B l -> Γ B)).
     intros. split ; intro. apply H in H0. inversion H0. subst. auto. auto.
     apply H. apply in_cons ; auto. pose (IHl Γ H0).
     eapply MP. eapply MP. eapply MP. apply Ax ; eapply A8 ; reflexivity.
     eapply MP. apply Thm_irrel. apply Id. apply H ; apply in_eq. apply imp_Id_gen. auto. 
  + assert (J1: (forall B : form, ((fun x : form => Ensembles.In form Γ x /\ x <> a) B -> List.In B l) * (List.In B l -> (fun x : form => Ensembles.In form Γ x /\ x <> a) B))).
     intros. split ; intro. destruct H0. apply H in H0. inversion H0. subst. exfalso. apply H1 ; auto. auto.
     split. apply H. apply in_cons ; auto. intro. subst. auto.
     pose (IHl (fun x => Ensembles.In _ Γ x /\ x <> a) J1).
     eapply MP. eapply MP. eapply MP. apply Ax ; eapply A8 ; reflexivity.
     eapply MP. apply Thm_irrel. apply Id. apply H ; apply in_eq. apply imp_Id_gen.
     apply FOBIH_monot with (Γ1:=Γ) in f0. apply f0. intros C HC.
     inversion HC. auto.
Qed.

Lemma list_conj_finite_context : forall l (Γ : Ensemble _) A,
  (forall B : form, (Γ B -> List.In B l) * (List.In B l -> Γ B)) ->
  FOBIH_prv (Singleton _ (list_conj l)) A ->
  FOBIH_prv Γ A.
Proof.
intros.
apply FOBIH_comp with (Γ:=(Singleton form (list_conj l))) ; auto.
intros. inversion H1 ; subst. apply der_list_conj_finite_context.
intro B ; split ; intro HB ; apply H ; auto.
Qed.

End list_conj_stuff.




Section Prv.

  Lemma prv_ctx (T : form -> Prop) phi :
    T phi -> T |- phi.
  Proof.
    intros H. apply Id. auto.
  Qed.

  Lemma prv_weak T T' A :
    T |- A -> Included _ T T' -> T' |- A.
  Proof.
    intros H1 H2. eapply FOBIH_monot in H1; eassumption.
  Qed.

  Lemma prv_MP {T : form -> Prop} {phi} psi :
    T |- psi → phi -> T |- psi -> T |- phi.
  Proof.
    intros H1 H2. eapply MP ; auto.
    - exact H1.
    - auto.
  Qed.

  Lemma prv_DT T A B :
    adj T A |- B <-> T |- A → B.
  Proof.
    split; intros HT.
    - apply FOBIH_Deduction_Theorem.
      eapply prv_weak; try apply HT. intros C [HC| ->]; [ left | right ]; trivial. constructor.
    - apply prv_MP with A; try (apply prv_ctx; now right). eapply prv_weak; try apply HT. firstorder.
  Qed.

  Lemma prv_compact T A :
    T |- A -> exists L, (forall B, B el L -> T B) /\ (fun B => B el L) |- A.
  Proof.
    intros (T' & H1 & H2 & L & HL) % FOBIH_finite. exists L. split; intuition.
    - apply HL in H ; apply H1 ; auto.
    - eapply prv_weak; try apply H2. intros B HB. unfold Ensembles.In.
      apply HL ; auto.
  Qed.

  Lemma prv_cut T T' A :
    T |- A -> (forall B, T B -> T' |- B) -> T' |- A.
  Proof.
    intros [L [H1 H2]] % prv_compact H. induction L in A, H1, H2 |- *.
    - eapply prv_weak; try apply H2. intros B [].
    - eapply prv_MP; try apply (IHL (a → A)).
      + intros B HB. apply H1. now right.
      + apply prv_DT. eapply prv_weak; try apply H2. intros B [->| HB]; cbn; intuition.
      + apply H, H1. now left.
  Qed.

  Lemma prv_EI {T : form -> Prop} {phi} t :
    T |- phi[t..] -> T |- ∃ phi.
  Proof.
    intros H. eapply prv_MP; try apply H. constructor 2.
    econstructor 16 ; reflexivity.
  Qed.

   Lemma prv_EE T A B :
    (fun C => exists C', C = C'[↑] /\ T C') |- A → B[↑] -> T |- (∃ A) → B.
  Proof.
    intros H. eapply EC; try apply ECRule_I ; auto.
  Qed.

  Lemma prv_AI T A :
    (fun C => exists C', C = C'[↑] /\ T C') |- A -> T |- ∀ A.
  Proof.
    intros H. eapply Gen; try apply GenRule_I ; auto.
  Qed.

  Lemma prv_AE {T : form -> Prop} {phi} t :
    T |- ∀ phi -> T |- phi[t..].
  Proof.
    intros H. eapply prv_MP; try apply H. constructor 2.
    econstructor 15 ; reflexivity.
  Qed.

  Lemma prv_DI1 T A B :
    T |- A -> T |- A ∨ B.
  Proof.
    intros H. eapply prv_MP; try apply H. constructor 2.
    econstructor 3 ; reflexivity.
  Qed.

  Lemma prv_DI2 T A B :
    T |- B -> T |- A ∨ B.
  Proof.
    intros H. eapply prv_MP; try apply H. constructor 2.
    econstructor 4 ; reflexivity.
  Qed.

  Lemma prv_DE T phi psi theta :
    T |- phi ∨ psi -> adj T phi |- theta -> adj T psi |- theta -> T |- theta.
  Proof.
    intros H1 H2 H3. eapply prv_MP. eapply prv_MP. eapply prv_MP.
    - constructor 2. econstructor 5 ; reflexivity.
    - apply prv_DT. apply H2.
    - apply prv_DT. apply H3.
    - apply H1.
  Qed.

  Lemma prv_CI T A B :
    T |- A -> T |- B -> T |- A ∧ B.
  Proof.
    intros H1 H2. eapply prv_MP. eapply prv_MP. eapply prv_MP.
    - constructor 2. econstructor 8 ; reflexivity.
    - apply prv_DT. apply prv_ctx. now right.
    - eapply MP. apply Thm_irrel. auto.
    - apply H1.
  Qed.

  Lemma prv_CE1 T A B :
    T |- A ∧ B -> T |- A.
  Proof.
    intros H. eapply prv_MP; try apply H. constructor 2.
    econstructor 6 ; reflexivity.
  Qed.

  Lemma prv_CE2 T A B :
    T |- A ∧ B -> T |- B.
  Proof.
    intros H. eapply prv_MP; try apply H. constructor 2.
    econstructor 7 ; reflexivity.
  Qed.

  Lemma prv_exp T A :
    T |- ⊥ -> T |- A.
  Proof.
    intros H. eapply prv_MP; try apply H. constructor 2.
    econstructor 9 ; reflexivity.
  Qed.

  Lemma prv_cas_car T A B C :
    T |- A → B → C <-> T |- B ∧ A → C.
  Proof.
    split; intros H.
    - apply prv_DT. eapply prv_MP. eapply prv_MP.
      + eapply prv_weak; try apply H. firstorder.
      + eapply prv_CE2, prv_ctx. now right.
      + eapply prv_CE1, prv_ctx. now right.
    - apply prv_DT. apply -> prv_DT. eapply prv_MP.
      + eapply prv_weak; try apply H. firstorder.
      + apply prv_CI; apply prv_ctx; firstorder.
  Qed.

  Lemma prv_list_conj T L :
    (forall A, A el L -> T |- A) -> T |- list_conj L.
  Proof.
    intros H. induction L.
    - apply prv_Top.
    - cbn. apply prv_CI.
      + apply H. now left.
      + apply IHL. firstorder.
  Qed.

  Lemma prv_list_conj' T L A :
    A el L -> adj T (list_conj L) |- A.
  Proof.
    induction L; cbn; try tauto. intros [-> | H].
    - eapply prv_CE1. apply prv_ctx. now right.
    - apply prv_DT in IHL; trivial. eapply prv_MP.
      + eapply prv_weak; try apply IHL. firstorder.
      + eapply prv_CE2. apply prv_ctx. now right.
  Qed.

  Lemma prv_list_disj T L A :
    A el L -> T |- A -> T |- list_disj L.
  Proof.
    induction L; cbn; try now intros []. intros [-> |H] HA.
    - apply prv_DI1. apply HA.
    - apply prv_DI2. now apply IHL.
  Qed.

  Lemma list_disj_mono T L L' :
    incl L L' -> T |- list_disj L -> T |- list_disj L'.
  Proof.
    induction L in T |- *; cbn; intros H1 H2.
    - apply prv_exp. apply H2.
    - eapply prv_DE; try apply H2.
      + apply prv_list_disj with a; try firstorder. apply prv_ctx. now right.
      + apply IHL; try firstorder. apply prv_ctx. now right.
  Qed.

  Lemma Lext_ex_der {T L1 L2 psi} c :
    T |- list_conj (∃ psi :: psi[$c..] :: L1) → list_disj L2
        -> T |- list_conj L1 → psi[$c..] → list_disj L2.
  Proof.
    intros H. apply prv_DT. apply -> prv_DT. apply prv_DT in H.
    eapply prv_cut; try apply H. intros B [HB | ->].
    - apply prv_ctx. left. now left.
    - cbn. apply prv_CI; try apply prv_CI.
      + eapply prv_EI. apply prv_ctx. now right.
      + apply prv_ctx. now right.
      + apply prv_ctx. left. now right.
  Qed.

  Lemma Lext_all_der {T L1 L2 psi} c :
    T |- list_conj L1 → list_disj (∀ psi :: psi[$c..] :: L2)
        -> T |- list_conj L1 → psi[$c..] ∨ list_disj L2.
  Proof.
    intros H. apply prv_DT. apply prv_DT in H.
    cbn in H. eapply prv_DE; try apply H.
    - apply prv_DI1. apply prv_AE. apply prv_ctx. now right.
    - apply prv_ctx. now right.
  Qed.

End Prv.





Section Bi_Int.

Theorem dual_residuation_obj : forall A B C,
  (FOBIH_prv (Empty_set _) ((A --< B) → C) ->
      FOBIH_prv (Empty_set _) (A → ((B ∨ C)))).
Proof.
intros A B C D. eapply MP. eapply MP. apply Imp_trans.
eapply MP. eapply MP. apply Imp_trans. apply Ax ; eapply BA1 ; reflexivity.
apply comm_Or_obj. apply monot_Or2. auto.
Qed.

Lemma DN_to_form : forall A Γ, FOBIH_prv Γ ((¬ (∞ A)) → A).
Proof.
intros A Γ. eapply MP. eapply MP. apply And_Imp. eapply MP.
eapply MP. apply Imp_trans. eapply MP. eapply MP.
apply Ax ; eapply A8 ; reflexivity. apply Ax ; eapply A7 ; reflexivity.
apply Ax ; eapply A6 ; reflexivity. eapply MP. apply Imp_And.
eapply MP. eapply MP. apply Imp_trans. apply imp_Id_gen.
eapply MP. eapply MP. apply Imp_trans. eapply MP.
apply Imp_trans. apply imp_Id_gen. eapply MP.
eapply MP. apply Imp_trans. apply imp_Id_gen.
apply Ax ; eapply BA4 ; reflexivity. apply prv_Top.
Qed.

Theorem dual_residuation : forall A B C,
  FOBIH_prv (Empty_set _) ((A --< B) → C) <-> FOBIH_prv (Empty_set _) (A → ((B ∨ C))).
Proof.
intros A B C. split.
- intro D. eapply MP. eapply MP. apply Imp_trans.
  eapply MP. eapply MP. apply Imp_trans.
  apply Ax ; eapply BA1 ; reflexivity. apply comm_Or_obj.
  apply monot_Or2 ; auto.
- intro D. eapply MP. eapply MP. apply Imp_trans.
  eapply MP. eapply MP. apply Imp_trans.
  apply Ax ; eapply BA1 ; reflexivity. apply monotL_Or.
  apply Ax ; eapply BA3 ; reflexivity.
  eapply MP. eapply MP. apply Imp_trans. apply monotL_Or.
  eapply MP. eapply MP. apply Imp_trans.
  eapply MP. eapply MP. apply Ax ; eapply A8 ; reflexivity.
  apply Ax ; eapply BA2 ; reflexivity. eapply MP. apply Thm_irrel.
  apply DN. exact D. apply Contr_Bot.
  eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
  apply imp_Id_gen. apply Ax ; eapply A9 ; reflexivity.
Qed.

Lemma AThm_irrel : forall A B Γ, FOBIH_prv Γ ((A --< B) → A).
Proof.
intros A B Γ. apply FOBIH_monot with (Γ:= Empty_set _).
apply dual_residuation. apply Ax ; eapply A4 ; reflexivity.
intros C HC ; inversion HC.
Qed.

Theorem dual_residuation_gen : forall A B C,
  pair_der (Empty_set _) (Singleton _ ((A --< B) → C))  <-> pair_der (Empty_set _) (Singleton _ (A → ((B ∨ C)))).
Proof.
intros A B C. split.
- intro. exists [(A → (B ∨ C))]. repeat split.
  * apply NoDup_cons. intro. inversion H0. apply NoDup_nil.
  * intros. inversion H0. subst. cbn. apply In_singleton. inversion H1.
  * destruct H as (l & H0 & H1 & H2). cbn. eapply MP. apply Ax ; eapply A3 ; reflexivity.
    apply dual_residuation. destruct l ; cbn in *.
    + eapply MP. apply Ax ; eapply A9 ; reflexivity. auto.
    + destruct l ; cbn in *. apply absorp_Or1 in H2. assert (Singleton form ((A --< B) → C) f).
       apply H1 ; auto. inversion H ; subst ; auto. exfalso. inversion H0 ; subst.
       apply H4. assert (Singleton form ((A --< B) → C) f). apply H1 ; auto. inversion H ; subst.
       assert (Singleton form ((A --< B) → C) f0). apply H1 ; auto. inversion H3 ; subst. apply in_eq.
- intro. exists  [((A --< B) → C)]. repeat split.
  * apply NoDup_cons. intro. inversion H0. apply NoDup_nil.
  * intros. inversion H0. subst. cbn. apply In_singleton. inversion H1.
  * destruct H as (l & H0 & H1 & H2). cbn. eapply MP. apply Ax ; eapply A3 ; reflexivity.
    apply dual_residuation. destruct l ; cbn in *.
    + eapply MP. apply Ax ; eapply A9 ; reflexivity. auto.
    + destruct l ; cbn in *. apply absorp_Or1 in H2. assert (Singleton form (A → B ∨ C) f).
       apply H1 ; auto. inversion H ; subst ; auto. exfalso. inversion H0 ; subst.
       apply H4. assert (Singleton form (A → B ∨ C) f). apply H1 ; auto. inversion H ; subst.
       assert (Singleton form (A → B ∨ C) f0). apply H1 ; auto. inversion H3 ; subst. apply in_eq.
Qed.

Lemma BiLEM : forall A Γ, FOBIH_prv Γ (A ∨ (∞ A)).
Proof.
intros. apply FOBIH_monot with (Γ:=Empty_set _).
eapply MP. rewrite <- dual_residuation. apply imp_Id_gen.
apply prv_Top. intros B HB ; inversion HB.
Qed.

Theorem FOBIH_Dual_Detachment_Theorem : forall A B Δ,
           FOBIH_prv (Singleton _ (A --< B)) (list_disj Δ) ->
           FOBIH_prv (Singleton _ A) (B ∨ (list_disj Δ)).
Proof.
intros A B Δ D.
apply FOBIH_monot with (Γ1:=Union _ (Empty_set form) (Singleton _ (A --< B))) in D.
apply FOBIH_Deduction_Theorem in D. apply dual_residuation in D.
apply FOBIH_Detachment_Theorem in D. apply (FOBIH_monot D).
intros C HC ; inversion HC ; [ inversion H | auto].
intros C HC ; right ; auto.
Qed.

Theorem FOBIH_Dual_Deduction_Theorem : forall A B Δ,
           FOBIH_prv (Singleton _ A) (B ∨ (list_disj Δ)) ->
           FOBIH_prv (Singleton _ (A --< B)) (list_disj Δ).
Proof.
intros A B Δ D.
apply FOBIH_monot with (Γ1:=Union _ (Empty_set form) (Singleton _ A)) in D.
apply FOBIH_Deduction_Theorem in D. apply dual_residuation in D.
apply FOBIH_Detachment_Theorem in D. apply (FOBIH_monot D).
intros C HC ; inversion HC ; [ inversion H | auto].
intros C HC ; right ; auto.
Qed.

Theorem gen_FOBIH_Dual_Detachment_Theorem : forall A B Δ,
  pair_der (Singleton _ (A --< B)) Δ ->
      pair_der (Singleton _ A) (Union _ (Singleton _ B) Δ).
Proof.
intros A B Δ wpair. destruct wpair. destruct H. destruct H0. cbn in H0. cbn in H1.
exists (B :: (remove (eq_dec_form eq_dec_funcs eq_dec_preds) B x)). repeat split.
apply NoDup_cons. apply remove_In. apply NoDup_remove. assumption.
intros. inversion H2 ; subst ; cbn ; auto. left. apply In_singleton.
right. apply H0. apply In_remove with (B:=B). assumption.
cbn. eapply MP. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
apply Ax ; eapply A3 ; reflexivity. apply remove_disj.
apply FOBIH_Dual_Detachment_Theorem ; auto.
Qed.

Theorem gen_FOBIH_Dual_Deduction_Theorem : forall A B Δ,
  pair_der (Singleton _ A) (Union _ (Singleton _ B) Δ) ->
      pair_der (Singleton _ (A --< B)) Δ.
Proof.
intros A B Δ wpair. destruct wpair. destruct H. destruct H0. cbn in H0. cbn in H1.
exists (remove (eq_dec_form eq_dec_funcs eq_dec_preds) B x). repeat split.
apply NoDup_remove. assumption.
intros. cbn. pose (H0 A0). pose (@In_remove _ _ _ H2). apply u in i.
destruct i. inversion H3. subst. exfalso. pose (remove_In (eq_dec_form eq_dec_funcs eq_dec_preds) x x0).
apply n. assumption. assumption.
apply FOBIH_Dual_Deduction_Theorem. eapply MP. apply remove_disj. auto.
Qed.

Theorem Constant_Domain_Ax : forall A B, FOBIH_prv (Empty_set _) ((∀(A ∨ B[↑])) → ((∀ A) ∨ B)).
Proof.
intros. eapply MP. eapply MP. apply Imp_trans. 2: apply comm_Or_obj.
apply dual_residuation. apply FOBIH_Deduction_Theorem.
apply Gen. apply FOBIH_monot with (Γ:=(Union _ (Empty_set _) (Singleton form ((∀ A[up ↑] ∨ B[↑][up ↑]) --< B[↑])))).
apply FOBIH_Detachment_Theorem. apply dual_residuation.
eapply MP. eapply MP. apply Imp_trans. 2: apply comm_Or_obj.
apply Ax. apply QA2 with (A[up ↑] ∨ B[↑][up ↑]) (var 0). cbn.
rewrite up_decompose. rewrite subst_var. rewrite up_decompose. rewrite subst_var. auto.
intros C HC ; inversion HC ; [ inversion H | inversion H ; subst ].
eexists ; split ; [ | right ; cbn ; apply In_singleton] ; cbn ; auto.
Qed.

Theorem dual_MP : forall A B Δ,
  pair_der (Singleton _ (A --< B)) Δ ->
  pair_der (Singleton _ B) Δ ->
      pair_der (Singleton _ A) Δ.
Proof.
intros.
destruct H as (x & K0 & K1 & K2).
destruct H0 as (x0 & K3 & K4 & K5).
exists (x ++ remove_list x x0). repeat split.
apply add_remove_list_preserve_NoDup ; auto.
intros C HC. destruct (in_app_or _ _ _ HC) ; auto.
apply In_remove_list_In_list in H ; auto.
assert (FOBIH_prv (Singleton form (A --< B)) (list_disj (x ++ remove_list x x0))).
apply FOBIH_monot with (Γ:=(Union _ (Empty_set _) (Singleton form (A --< B)))).
apply FOBIH_Detachment_Theorem. apply der_list_disj_remove1.
apply FOBIH_Deduction_Theorem. apply FOBIH_monot with (Γ:=Singleton form (A --< B)) ; auto.
intros C HC ; inversion HC ; right ; apply In_singleton.
intros C HC ; inversion HC ; [inversion H | auto].
assert (FOBIH_prv (Singleton form B) (list_disj (x ++ remove_list x x0))).
apply FOBIH_monot with (Γ:=(Union _ (Empty_set _) (Singleton form B))).
apply FOBIH_Detachment_Theorem. apply der_list_disj_remove2.
apply FOBIH_Deduction_Theorem. apply FOBIH_monot with (Γ:=Singleton form B) ; auto.
intros C HC ; inversion HC ; right ; apply In_singleton.
intros C HC ; inversion HC ; [inversion H0 | auto].
apply FOBIH_monot with (Γ:=(Union _ (Empty_set _) (Singleton form A))).
apply FOBIH_Detachment_Theorem.
eapply MP. eapply MP. apply Imp_trans. apply Ax ; eapply BA1 ; reflexivity.
eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
apply FOBIH_Deduction_Theorem. apply FOBIH_monot with (Γ:=Singleton form B) ; auto.
intros C HC ; inversion HC ; right ; apply In_singleton.
apply FOBIH_Deduction_Theorem. apply FOBIH_monot with (Γ:=Singleton form (A --< B)) ; auto.
intros C HC ; inversion HC ; right ; apply In_singleton.
intros C HC ; inversion HC ; [inversion H1 | auto].
Qed.

Lemma monoR_Excl : forall A B C,
  (FOBIH_prv (Empty_set _) (A →  B)) ->
  (FOBIH_prv (Empty_set _) ((A --< C) →  (B --< C))).
Proof.
intros. apply dual_residuation.
eapply MP. eapply MP. apply Imp_trans. exact H.
apply Ax ; eapply BA1 ; reflexivity.
Qed.

Lemma monoL_Excl : forall A B C,
  (FOBIH_prv (Empty_set _) (A →  B)) ->
  (FOBIH_prv (Empty_set _) ((C --< B) →  (C --< A))).
Proof.
intros. apply dual_residuation.
eapply MP. eapply MP. apply Imp_trans.
apply Ax ; eapply BA1 ; reflexivity.
eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans. exact H.
apply Ax ; eapply A3 ; reflexivity.
apply Ax ; eapply A4 ; reflexivity.
Qed.


Theorem Dual_Constant_Domain : forall A B, Singleton _ (((∃ A) ∧ B) --< ∃ A ∧ (B)[↑]) |- ⊥.
Proof.
intros.
apply FOBIH_monot with (Γ:= Union _ (Empty_set _) (Singleton form ((∃ A) ∧ B --< (∃ A ∧ B[↑])))).
apply FOBIH_Detachment_Theorem. apply dual_residuation.
eapply MP. eapply MP. apply Imp_trans.
2: apply Ax ; eapply A3 ; reflexivity.
eapply MP. apply Imp_And.
apply EC ; cbn. repeat apply FOBIH_Deduction_Theorem.
apply prv_EI with ($0) ; cbn.
rewrite up_decompose. rewrite subst_var. rewrite up_decompose. rewrite subst_var.
apply prv_CI ; apply Id. left ; right ; apply In_singleton. right ; apply In_singleton.
intros C HC ; inversion HC ; [ inversion H | inversion H ; apply In_singleton].
Qed.


End Bi_Int.

(* Having Cut is quite convenient. *)

Lemma Or_imp_assoc : forall A B C D Γ,
  FOBIH_prv Γ (A → ((B ∨ C) ∨ D)) ->
  FOBIH_prv Γ (A → (B ∨ (C ∨ D))).
Proof.
intros. eapply MP. eapply MP. apply Imp_trans. exact H.
eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
apply Ax ; eapply A3 ; reflexivity. eapply MP. eapply MP.
apply Imp_trans. apply Ax ; eapply A3 ; reflexivity.
apply Ax ; eapply A4 ; reflexivity. eapply MP.
eapply MP. apply Imp_trans. apply Ax ; eapply A4 ; reflexivity.
apply Ax ; eapply A4 ; reflexivity.
Qed.

Lemma Cut : forall (Γ Δ: @Ensemble (form)) A,
        pair_der (Union _ Γ (Singleton _ A)) Δ  ->
        pair_der Γ (Union _ Δ (Singleton _ A))  ->
        pair_der Γ Δ.
Proof.
intros.
destruct H. destruct H0. destruct H. destruct H1. destruct H0. destruct H3.
simpl in H2. simpl in H4. simpl in H3. simpl in H1.
exists ((remove( eq_dec_form eq_dec_funcs eq_dec_preds) A x0) ++ (remove_list (remove (eq_dec_form eq_dec_funcs eq_dec_preds) A x0) x)). repeat split.
apply add_remove_list_preserve_NoDup ; auto.
apply NoDup_remove ; auto. simpl. intros. apply in_app_or in H5. destruct H5.
apply in_remove in H5. destruct H5. apply H3 in H5. inversion H5 ; auto. subst.
inversion H7 ; subst ; exfalso ; auto. apply In_remove_list_In_list in H5.
apply H1 in H5. auto. simpl.
apply FOBIH_Deduction_Theorem in H2.
pose (Id_list_disj_remove Γ (remove (eq_dec_form eq_dec_funcs eq_dec_preds) A x0) x).
pose (@list_disj_remove_form _ _ A H4).
assert (J1: FOBIH_prv Γ (list_disj (remove (eq_dec_form eq_dec_funcs eq_dec_preds) A x0) → list_disj (remove (eq_dec_form eq_dec_funcs eq_dec_preds) A x0 ++ remove_list (remove (eq_dec_form eq_dec_funcs eq_dec_preds) A x0) x))).
apply Id_list_disj.
eapply MP. 2: exact f0.
eapply MP. 2: exact J1.
eapply MP. apply Ax ; eapply A5 ; reflexivity.
eapply MP. 2: exact f.
eapply MP. apply Imp_trans. auto.
Qed.


End Properties.



