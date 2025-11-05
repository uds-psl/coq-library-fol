From Equations Require Import Equations.
Require Equations.Type.DepElim.
From FOL.Proofmode Require Import Theories ProofMode.
From FOL Require Import FullSyntax Arithmetics.

Require FOL.Proofmode.Hoas.
Require Import String List.

Import ListNotations.
Open Scope string_scope.

(** * Löb's Theorem *)

Existing Instance PA_funcs_signature.
Existing Instance PA_preds_signature.
Existing Instance full_operators.
Existing Instance falsity_on.

Instance eqdec_funcs : EqDec PA_funcs_signature.
Proof. intros x y; decide equality. Qed.

Instance eqdec_preds : EqDec PA_preds_signature.
Proof. intros x y. destruct x, y. now left. Qed.

Section Löb.

  Variables pei: peirce.
  Variables T: form -> Prop.

  (** ** Derivability Conditions *)

  Variables box: form -> form.
  Notation "□ A" := (box A) (at level 5, no associativity).

  Variables necessitation: forall A, T ⊩ A -> T ⊩ □A.
  Variables internal_necessitation: forall A, T ⊩ (□A → □□A).
  Variables box_distr: forall A B, T ⊩ (□(A → B) → □A → □B).

  Variables modal_fixpoint: forall P, exists ψ, T ⊩ (ψ ↔ (□ψ → P)).

  (** ** Proof of Löb's Theorem *)

  Lemma Lob's_lemma P:
    exists ψ, T ⊩ (ψ ↔ (□ψ → P)) /\ T ⊩ (□ψ → □P).
  Proof.
    destruct (modal_fixpoint P) as [ψ equiv]. exists ψ. split; first assumption.
    apply T_CE1 in equiv as H2.
    apply necessitation in H2.
    assert (H4: T ⊩ (□ψ → □(□ψ → P))).
    fstart. now fapply box_distr. 
    specialize (box_distr (□ψ) P) as H5.
    assert (H6: T ⊩ (□ψ → □(□ψ) → □P)).
    fstart. fintros "H1". fapply H5. fapply H4. (* fapply "H1" diverges *)
    fstop. apply T_Ctx. eapply contains_extend1.
    fstart. fintros "H". fapply H6.
    - fstop. apply T_Ctx. eapply contains_extend1.
    - fapply internal_necessitation. fstop. apply T_Ctx.
      eapply contains_extend1.
  Qed. 

  Lemma Lob's_theorem P:
    (T ⊩ (□P → P)) -> T ⊩ P.
  Proof.
    intros HLöb. destruct (Lob's_lemma  P) as [ψ [Hequiv Hlem]].
    assert (T ⊩ (□ψ → P)) as H10.
    fstart. fintros "H". fapply HLöb. fapply Hlem.
    fstop. apply T_Ctx. eapply contains_extend1.
    apply T_CE2 in Hequiv as H11.
    assert (T ⊩ ψ) as H12.
    eapply T_IE; first eassumption. assumption.
    eapply T_IE; first eassumption. apply necessitation. assumption.
  Qed.

(** ** Internal Löb's Theorem *)

  Lemma int_Lob's_theorem P:
    T ⊩ (□(□P → P) → □P).
  Proof.
    destruct (modal_fixpoint P) as [ψ equiv]. 
    assert (T ⊩ (ψ → □ψ → P)) as H1.
    now eapply T_CE1. 
    apply necessitation in H1.
    assert (T ⊩ (□ψ → □((□ ψ) → P))) as H2.
    now fapply box_distr.
    assert (T ⊩ (□ψ → □(□ψ) → □P)) as H3.
    apply T_II. apply switch_imp_T in H2. 
    now fapply box_distr.
    assert (T ⊩ (□ψ → □P)) as H4.
    fstart. fintros "H". 
    fapply H3; last fapply internal_necessitation.
    1-2: fstop; apply T_Ctx; apply contains_extend1.
    assert (T ⊩ ((□P → P) → (□ψ → P))) as H5.
    fstart. fintros "Hf" "Hψ". fapply "Hf". fapply H4.
    fstop. apply T_Ctx. apply contains_extend1.
    assert (T ⊩ ((□P → P) → ψ)) as H6.
    apply T_CE2 in equiv.
    fstart. fintros "H". fapply equiv. fapply H5.
    fstop. apply T_Ctx. apply contains_extend1.
    assert (T ⊩ (□(□P → P) → □ψ)) as H7.
    fapply box_distr. now apply necessitation.
    fstart. fintros "H". fapply H4. fapply H7.
    fstop. apply T_Ctx. apply contains_extend1.
  Qed.

  Corollary Lob's_theorem_from_int P:
    T ⊩ (□P → P) -> T ⊩ P.
  Proof.
    intros HLöb. assert (T ⊩ □(□P → P)) as Hint.
    now apply necessitation.
    enough (T ⊩ □P) as HBox.
    now fapply HLöb.
    now fapply int_Lob's_theorem.
  Qed.

(** ** Gödel's Second Incompleteness Theorem *)

  Corollary Godel's_second_incompleteness_theorem:
    ~T ⊢T ⊥ -> ~T ⊢T ¬□ ⊥.
  Proof.
    intros Hconsistent [A [Hincl HprovCons]].
    apply Hconsistent. apply Lob's_theorem. 
    exists A. split; assumption.
  Qed.
      
End Löb.