From FOL Require Import FullSyntax Arithmetics Theories.
From FOL.Tennenbaum Require Import SyntheticInType NumberUtils Peano.
From Undecidability.Shared Require Import ListAutomation.
From FOL.Incompleteness Require Import qdec.
Require Import List Lia.
Import Vector.VectorNotations.
Import ListNotations ListAutomationNotations.

Require Import Setoid Morphisms.

Notation Q := Qeq.
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).


Lemma switch_nat_num α rho (n : nat) :
  sat interp_nat rho (α[(num n)..]) <-> sat interp_nat (n.:rho) α.
Proof.
  split; intros H.
  - rewrite <- (inu_nat_id n). erewrite <-eval_num. apply sat_single, H.
  - apply sat_single. setoid_rewrite eval_num. now setoid_rewrite inu_nat_id.
Qed.

#[global] Existing Instance PA_preds_signature.
#[global] Existing Instance PA_funcs_signature.

Definition unary α := bounded 1 α.
Definition binary α := bounded 2 α.

(** PA and Q are consistent in Coq. *)

Lemma PA_consistent : ~ PAeq ⊢TI ⊥.
Proof.
  intros H. eapply tsoundness in H.
  2: instantiate (1 := fun _ => 0).
  apply H.
  intros ax Hax.
  now apply PA_std_axioms.
Qed.

Corollary Q_consistent : ~ Q ⊢I ⊥.
Proof.
  intros H. eapply soundness in H. 
  eapply (H nat interp_nat (fun _ => 0)).
  intros ax Hax.
  now apply Q_std_axioms.
Qed.

(* Numerals are closed terms. *)

Lemma closed_num n k : bounded_t k (num n).
Proof.
  eapply bounded_up_t. instantiate (1 := 0).
  induction n; cbn; now solve_bounds. lia.
Qed.

Lemma vec_map_preimage {X N} (v : Vector.t term N) f (x : X) :
  Vector.In x (Vector.map f v) -> exists t, Vector.In t v /\ x = f t.
Proof.
  induction v; cbn; intros H.
  - inversion H.
  - inversion H.
    exists h. split. constructor. reflexivity.
    apply Eqdep_dec.inj_pair2_eq_dec in H3. subst.
    destruct (IHv H2) as [t Ht].
    exists t. split. constructor. all: try apply Ht.
    decide equality.
Qed.

Lemma subst_bound_t t N B sigma :
  bounded_t N t ->
  (forall n, n < N -> bounded_t B (sigma n) ) -> bounded_t B (t`[sigma]).
Proof.
  induction 1 as [| f v H IH]; intros HN; cbn.
  - now apply HN.
  - constructor. intros s (t & Ht & ->)%vec_map_preimage.
    now apply IH.
Qed.

Lemma subst_bound phi :
  forall sigma N B, bounded N phi ->
  (forall n, n < N -> bounded_t B (sigma n) ) -> bounded B phi[sigma].
Proof.
  intros sigma N B H1 H2. eapply subst_bounded_max; eauto.
Qed.
