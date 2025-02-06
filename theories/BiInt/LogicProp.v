Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.

From Undecidability.FOL Require Import Syntax.Facts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.

From FOL Require Import GenT Gen.
From FOL Require Import BiInt.BiInt SyntaxFeatures HilbertCalc.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Import BiIntSyntax.

Section Logic.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Existing Instance falsity_on.

  Context {eq_dec_preds : eq_dec Σ_preds}.
  Context {eq_dec_funcs : eq_dec Σ_funcs}.

(* Monotonicity holds. *)

Theorem FOBIH_monot : forall Γ A,
          FOBIH_prv Γ A ->
          forall Γ1, (Included _ Γ Γ1) ->
          FOBIH_prv Γ1 A.
Proof.
intros Γ A D0. induction D0 ; intros Γ1 incl.
(* Id *)
- apply Id ; auto.
(* Ax *)
- apply Ax ; auto.
(* MP *)
- apply MP with A ; auto.
(* DN *)
- apply DN ; auto.
(* Gen *)
- apply Gen. apply IHD0.
  intros B HB ; destruct HB as (C & HC0 & HC1) ; subst.
  exists C ; split ; auto.
(* EC *)
- eapply EC. apply IHD0.
  intros D HD ; destruct HD as (C & HC0 & HC1) ; subst.
  exists C ; split ; auto.
Qed.

(* Variable substitutions preserve provability. *)

Lemma subst_Ax : forall A f, (Axioms A) -> (Axioms A[f]).
Proof.
intros A f Ax.
destruct Ax ; subst ; [ eapply A1 ; reflexivity | eapply A2 ; reflexivity | eapply A3 ; reflexivity |
eapply A4 ; reflexivity | eapply A5 ; reflexivity | eapply A6 ; reflexivity |
eapply A7 ; reflexivity | eapply A8 ; reflexivity | eapply A9 ; reflexivity |
eapply BA1 ; reflexivity | eapply BA2 ; reflexivity | eapply BA3 ; reflexivity | eapply BA4 ; reflexivity | | | ].
- apply QA1 with (A0[f]) (B[up f]). cbn. rewrite up_form. reflexivity.
- apply QA2 with (A0[up f]) (subst_term f t). cbn. f_equal.
  rewrite subst_comp. unfold funcomp. rewrite subst_comp. unfold funcomp.
  apply subst_ext. intros. destruct n ; simpl ; auto. unfold funcomp. rewrite subst_term_comp.
  rewrite subst_term_id ; auto.
- apply QA3 with (A0[up f]) (subst_term f t). cbn. f_equal.
  rewrite subst_comp. unfold funcomp. rewrite subst_comp. unfold funcomp.
  apply subst_ext. intros. destruct n ; cbn ; auto. unfold funcomp. rewrite subst_term_comp.
  rewrite subst_term_id ; auto.
Qed.

Theorem FOBIH_subst : forall Γ A f, FOBIH_prv Γ A ->
    FOBIH_prv (fun x : form => exists B : form, x = B[f] /\ Ensembles.In _ Γ B) (A[f]).
Proof.
intros Γ A f D. revert f. induction D ; intro f.
(* Id *)
- apply Id ; exists A ; auto.
(* Ax *)
- apply Ax ; apply subst_Ax ; auto.
(* MP *)
- pose (IHD1 f). pose (IHD2 f). eapply MP. exact f0. exact f1.
(* DN *)
- pose (IHD f). apply DN. apply (FOBIH_monot f0).
  intros B HB ; destruct HB as (C & H0 & H1) ; subst ; inversion H1.
(* Gen *)
- pose (IHD (up f)). cbn in *. apply Gen.
  apply (FOBIH_monot f0). intros C HC ; destruct HC as (B & HB1 & HB2) ; subst.
  destruct HB2 as (C & HC1 & HC2) ; subst. exists C[f] ; split ; auto.
  apply up_form. exists C ; split ; auto.
(* EC *)
- pose (IHD (up f)). cbn in *. eapply EC. rewrite up_form in f0.
  apply (FOBIH_monot f0). intros C HC ; destruct HC as (E & HE1 & HE2) ; subst.
  destruct HE2 as (C & HC1 & HC2) ; subst. exists C[f] ; split ; auto.
  apply up_form. exists C ; split ; auto.
Qed.

(* Compositionality holds. *)

Theorem FOBIH_comp : forall Γ A,
          FOBIH_prv Γ A ->
          forall Γ', (forall B, Γ B -> FOBIH_prv Γ' B) ->
          FOBIH_prv Γ' A.
Proof.
intros Γ A D0. induction D0 ; intros Γ' derall ; auto.
(* Ax *)
- apply Ax ; auto.
(* MP *)
- apply MP with A ; auto.
(* DN *)
- apply DN ; auto.
(* Gen *)
- apply Gen. apply IHD0 ; intros. destruct H as (C & HC0 & HC1) ; subst.
  apply derall in HC1. apply FOBIH_subst ; auto.
(* EC *)
- eapply EC. apply IHD0 ; intros. destruct H as (C & HC0 & HC1) ; subst.
  apply derall in HC1. apply FOBIH_subst ; auto.
Qed.

(*

(* Atom substitution preserves provability. *)

(* Strong version *)

Lemma atom_subst_Ax : forall A f, (atom_subst_respects_strong f) -> (Axioms A) -> (Axioms A[f /atom]).
Proof.
intros A f resp Ax. revert resp. revert f. destruct Ax ; intros f resp ; subst ; cbn ;
[ eapply A1 ; reflexivity | eapply A2 ; reflexivity | eapply A3 ; reflexivity |
eapply A4 ; reflexivity | eapply A5 ; reflexivity | eapply A6 ; reflexivity |
eapply A7 ; reflexivity | eapply A8 ; reflexivity | eapply A9 ; reflexivity | eapply A10 ; reflexivity |
eapply BA1 ; reflexivity | eapply BA2 ; reflexivity | eapply BA3 ; reflexivity | eapply BA4 ; reflexivity | | | ].
- apply QA1 with (A0[f /atom]) (B[f /atom ]).
  repeat rewrite atom_subst_comp_strong ; auto.
- apply QA2 with (A0[f /atom ]) t.
  rewrite atom_subst_comp_strong ; auto.
- apply QA3 with (A0[f /atom ]) t.
  rewrite atom_subst_comp_strong ; auto.
Qed.

Theorem FOBIH_struct : forall Γ A f,
  (atom_subst_respects_strong f) ->
  (FOBIH_prv Γ A) ->
  FOBIH_prv (fun x : form => exists B : form, x = B[ f /atom] /\ In form Γ B) A[ f /atom].
Proof.
intros Γ A f resp D. revert f resp. induction D ; cbn ; intros f resp.
(* Id *)
- apply Id ; exists A ; auto.
(* Ax *)
- apply Ax ; apply atom_subst_Ax ; auto.
(* MP *)
- eapply MP. apply IHD1 ; auto. apply IHD2 ; auto.
(* DN *)
- apply DN. apply (FOBIH_monot _ _ (IHD f resp)) ; auto.
  intros C HC. destruct HC as (B & HB0 & HB1) ; inversion HB1.
(* Gen *)
- apply Gen. apply (FOBIH_monot _ _ (IHD f resp)).
  intros C HC. destruct HC as (B & HB0 & HB1) ; subst. destruct HB1 as (C & HC0 & HC1) ; subst.
  exists C[f /atom]. split. rewrite atom_subst_comp_strong ; auto. exists C. split ; auto.
(* EC *)
- eapply EC. cbn in IHD. rewrite atom_subst_comp_strong ; auto. apply (FOBIH_monot _ _ (IHD f resp)).
  intros C HC. destruct HC as (E & HE0 & HE1) ; subst. destruct HE1 as (C & HC0 & HC1) ; subst.
  exists C[f /atom]. split. rewrite atom_subst_comp_strong ; auto. exists C. split ; auto.
Qed. *)

(* It is a finite logic. *)

Lemma List_Reverse_arrow : forall l0 Γ0 Γ1,
  (Included form Γ0 (fun x : form => exists B : form, x = B[↑] /\ Ensembles.In _ Γ1 B)) ->
  (forall A : form, (Γ0 A -> List.In A l0) * (List.In A l0 -> Γ0 A)) ->
      (exists l1, (map (subst_form ↑) l1 = l0) /\ (forall y, List.In y l1 -> Ensembles.In _ Γ1 y)).
Proof.
induction l0 ; intros.
- exists []. split ; auto. intros. inversion H1.
- destruct (@In_dec form) with a l0 ; [ apply eq_dec_form ; auto | | ].
  + assert (J1: forall A : form, (Γ0 A -> List.In A l0) * (List.In A l0 -> Γ0 A)).
     intros. split ; intro. apply H0 in H1. inversion H1. subst. auto. auto.
     apply H0. apply in_cons. auto.
     pose (IHl0 Γ0 Γ1 H J1). destruct e. destruct H1. subst. pose (H0 a).
     destruct p. assert (List.In a (a :: map (subst_form ↑) x)). apply in_eq.
     apply γ in H1. apply H in H1. unfold In in H1. destruct H1. destruct H1. subst.
     exists (x0 :: x). simpl. split ; auto. intros. destruct H1 ; subst ; auto.
  + assert (J1: Included form (fun x : form => x <> a /\ Ensembles.In form Γ0 x)
     (fun x : form => exists B : form, x = B[↑] /\ Ensembles.In form Γ1 B)).
     intro. intros. unfold In in H1. destruct H1. apply H in H2. auto.
     assert (J2: (forall A : form, ((fun x : form => x <> a /\ Ensembles.In form Γ0 x) A -> List.In A l0) *
     (List.In A l0 -> (fun x : form => x <> a /\ Ensembles.In form Γ0 x) A))).
     intros. split. intro. destruct H1. apply H0 in H2. inversion H2. exfalso ; auto. auto.
     intros. split. intro. subst. auto. assert (List.In A (a :: l0)). apply in_cons ; auto.
     apply H0 in H2. auto.
     pose (IHl0 (fun x => x <> a /\ Ensembles.In _ Γ0 x) Γ1 J1 J2). destruct e. destruct H1. subst.
     pose (H0 a). destruct p. assert (List.In a (a :: map (subst_form ↑) x)). apply in_eq.
     apply γ in H1. apply H in H1. unfold In in H1. destruct H1. destruct H1. subst.
     exists (x0 :: x). simpl. split ; auto. intros. destruct H1 ; subst ; auto.
Qed.

Theorem FOBIH_finite : forall Γ A,
          (FOBIH_prv Γ A) ->
          exists Fin, Included _ Fin Γ /\
                          FOBIH_prv Fin A /\
                          exists l, forall A, (Fin A -> List.In A l) * (List.In A l -> Fin A).
Proof.
intros Γ A D0. induction D0.
(* Id *)
- exists (fun x => x = A). repeat split.
  + intros C HC ; inversion HC ; auto.
  + apply Id ; unfold Ensembles.In ; auto.
  + exists [A]. intro ; split ; intro ; subst. apply in_eq.
     inversion H0 ; auto. inversion H1.
(* Ax *)
- exists (Empty_set _). repeat split.
  intros C HC ; inversion HC.
  apply Ax ; auto.
  exists []. intro ; split ; intro H0 ; inversion H0.
(* MP *)
- destruct IHD0_1 as (Fin0 & HF00 & HF01 & (l0 & Hl0)) ;
  destruct IHD0_2 as (Fin1 & HF10 & HF11 & (l1 & Hl1)).
  exists (Union _ Fin0 Fin1). repeat split.
  intros C HC ; inversion HC ; auto.
  eapply MP. apply (FOBIH_monot HF01).
  intros C HC ; left ; auto.
  apply (FOBIH_monot HF11). intros C HC ; right ; auto.
  exists (l0 ++ l1). intro C ; split ; intro H. apply in_or_app.
  inversion H ; subst ; firstorder. apply in_app_or in H ; destruct H.
  left ; firstorder. right ; firstorder.
(* DN *)
- destruct IHD0 as (Fin0 & HF00 & HF01 & (l0 & Hl0)). exists (Empty_set _). repeat split.
  intros B HB ; inversion HB. apply DN ; auto. exists []. intro B. split ; intro HB ; inversion HB.
(* Gen *)
- destruct IHD0 as (Fin & HF0 & HF1 & (l & Hl)).
  destruct (@List_Reverse_arrow l Fin Γ) as (l0 & Hl00 & Hl01) ; subst ; auto.
  exists (fun y => List.In y l0). repeat split.
  intros C HC ; auto.
  apply Gen. apply (FOBIH_monot HF1) ; auto.
  intros C HC. unfold In. apply Hl in HC. apply in_map_iff in HC.
  destruct HC. exists x ; auto ; split ; firstorder.
  exists l0 ; auto.
(* EC *)
- destruct IHD0 as (Fin & HF0 & HF1 & (l & Hl)).
  destruct (@List_Reverse_arrow l Fin Γ) as (l0 & Hl00 & Hl01) ; subst ; auto.
  exists (fun y => List.In y l0). repeat split.
  intros C HC ; auto.
  apply EC. apply (FOBIH_monot HF1) ; auto.
  intros C HC. unfold In. apply Hl in HC. apply in_map_iff in HC.
  destruct HC. exists x ; auto ; split ; firstorder.
  exists l0 ; auto.
Qed.

End Logic.
