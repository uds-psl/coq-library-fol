From Equations Require Import Equations.
From FOL.HilbertSystem Require Import hilbert_system.
From Undecidability.FOL Require Import Arithmetics.Robinson.
From FOL Require Import ProofMode.
From Stdlib Require Import String List.

Section ND_Hil_equiv.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {eq_dec: EqDec form}.
  Existing Instance falsity_on.

  (** * Equivalence Proof of Hilbert System and ND *)
  (** ** Preliminary Facts *)
  Lemma axiom_inclusion {p: peirce} A φ:
      hilAx p φ -> A ⊢H φ.
  Proof.
      intros Hax. eapply (HilAx _ 0 Hax).
  Qed.

  Lemma operational_K {p: peirce} A φ ψ:
      A ⊢H φ -> A ⊢H ψ → φ.
  Proof.
      intros Hφ. eapply MP; first eassumption.
      apply axiom_inclusion. constructor.
  Qed.

  Lemma operational_S {p: peirce} A φ ψ τ:
      A ⊢H (φ → ψ → τ) -> A ⊢H (φ → ψ) -> A ⊢H (φ → τ).
  Proof.
      intros H1 H2. eapply MP.
      2: { eapply MP; last eapply (axiom_inclusion A (HS _ _ _)). eassumption. }
      assumption.
  Qed.

  Lemma identity {p: peirce} A φ:
      A ⊢H φ → φ.
  Proof.
      eapply MP; last eapply MP.
      3: { eapply (axiom_inclusion A (HS φ (φ → φ) φ)). }
      1-2: apply (axiom_inclusion A (HK _ _)).
  Qed.

  Theorem deduction_theorem {p: peirce} A φ ψ: 
      (φ::A) ⊢H ψ -> A ⊢H φ → ψ.
  Proof.
      induction 1 as [φ' ψ' p _ IH1 _ IH2 | φ' n | ψ' p HA].
          - eapply operational_S; eassumption.
          - apply operational_K. apply HilAx. assumption.
          - destruct (eq_dec φ ψ').
              + rewrite e. eapply identity.
              + cbn in HA. assert (In ψ' A) by intuition congruence.
                apply operational_K. apply ThAx. assumption.
  Qed.

  Section CompatibilityLemmas.

      (** ** Compatibility Lemmas *)

      Context {p: peirce}.

      Lemma compat_IE A φ ψ:
          A ⊢H φ → ψ -> A ⊢H φ -> A ⊢H ψ.
      Proof.
          intros Himpl Hφ. eapply MP; eassumption.
      Qed.

      Lemma forall_times_once n φ:
          ∀ (forall_times n φ) = forall_times (S n) φ.
      Proof.
          cbn. easy.
      Qed.

      Lemma compat_AllI A φ:
          map (subst_form ↑) A ⊢H φ -> A ⊢H ∀ φ.
      Proof.
          induction 1 as [φ ψ p _ IH1 _  IH2 | φ n p Hax | φ p HA].
              - eapply MP; first eapply IH1.
                eapply MP; first eapply IH2.
                apply (HilAx _ 0). constructor.
              - rewrite forall_times_once. apply (HilAx _ _). assumption.
              - assert (exists τ, (subst_form ↑) τ = φ /\ In τ A) as [τ [<- Hτ]].
                apply in_map_iff. assumption.
                eapply MP.
                2: { eapply (HilAx _ 0). eapply AllG. }
                apply ThAx. assumption.
      Qed.

      Lemma compat_AllE A φ t:
          A ⊢H ∀ φ -> A ⊢H φ[t..].
      Proof.
          intros HAll. eapply MP; first eassumption.
          apply (HilAx _ 0). constructor.
      Qed.

      Lemma compat_ExI A φ t:
          A ⊢H φ[t..] -> A ⊢H ∃ φ.
      Proof.
          intros Hφ. eapply MP; first eassumption.
          apply (HilAx _ 0). constructor.
      Qed.

      Lemma compat_ExE A φ ψ:
          A ⊢H ∃ φ -> (φ::(map (subst_form ↑) A)) ⊢H ψ[↑] -> A ⊢H ψ.
      Proof.
          intros Hex Hψ. apply deduction_theorem in Hψ.
          apply compat_AllI in Hψ.
          eapply MP; first eapply Hψ.
          eapply MP; first eapply Hex.
          apply (HilAx _ 0). constructor.
      Qed.

      Lemma compat_Exp A φ:
          A ⊢H ⊥ -> A ⊢H φ.
      Proof.
          intros Hbot. eapply MP; first eassumption.
          apply (HilAx _ 0). constructor.
      Qed.

      Lemma compat_ctx A φ:
          In φ A -> A ⊢H φ.
      Proof.
          intros HA. apply ThAx. assumption.
      Qed.

      Lemma compat_CI A φ ψ:
          A ⊢H φ -> A ⊢H ψ -> A ⊢H φ ∧ ψ.
      Proof.
          intros Hφ Hψ. eapply MP.
          2: { eapply MP; first eapply Hφ. eapply (HilAx _ 0).
              econstructor. }
          assumption.
      Qed.

      Lemma compat_CE1 A φ ψ:
          A ⊢H φ ∧ ψ -> A ⊢H φ.
      Proof.
          intros Hconj. eapply MP; first eassumption.
          eapply (HilAx _ 0). constructor.
      Qed.

      Lemma compat_CE2 A φ ψ:
          A ⊢H φ ∧ ψ -> A ⊢H ψ.
      Proof.
          intros Hconj. eapply MP; first eassumption.
          eapply (HilAx _ 0). constructor.
      Qed.

      Lemma compat_DI1 A φ ψ:
          A ⊢H φ -> A ⊢H φ ∨ ψ.
      Proof.
          intros Hφ. eapply MP; first eassumption.
          apply (HilAx _ 0). constructor.
      Qed.

      Lemma compat_DI2 A φ ψ:
          A ⊢H ψ -> A ⊢H φ ∨ ψ.
      Proof.
          intros Hψ. eapply MP; first eassumption.
          apply (HilAx _ 0). constructor.
      Qed.

      Lemma compat_DE A φ ψ τ:
          A ⊢H φ ∨ ψ -> (φ::A) ⊢H τ -> (ψ::A) ⊢H τ -> A ⊢H τ.
      Proof.
          intros Hdisj Hφ Hψ. apply deduction_theorem in Hφ, Hψ.
          eapply MP; first eapply Hψ.
          eapply MP; first eapply Hφ.
          eapply MP; first eapply Hdisj.
          apply (HilAx _ 0). constructor.
      Qed.

      Lemma compat_Pc A φ ψ:
          A ⊢HC (((φ → ψ) → φ) → φ).
      Proof.
          apply axiom_inclusion. constructor.
      Qed.

  End CompatibilityLemmas.


  Theorem ND_to_Hil: 
      forall (p : peirce) (A : list form) (φ : form), A ⊢ φ -> A ⊢H φ.
  Proof.
      apply (@prv_ind_full _ _ (fun p A φ => A ⊢H φ)); intros p A φ.
          - intros ψ _ IH. apply deduction_theorem. assumption.
          - intros ψ _ IH1 _ IH2. eapply compat_IE; eassumption.
          - intros _ IH. apply compat_AllI. assumption.
          - intros t _ IH. apply compat_AllE. assumption.
          - intros t _ IH. eapply compat_ExI. eassumption.
          - intros ψ _ IH1 _ IH2. eapply compat_ExE; eassumption.
          - intros _ IH. apply compat_Exp. assumption.
          - intros HA. apply compat_ctx. assumption.
          - intros ψ _ IH1 _ IH2. apply compat_CI; assumption.
          - intros ψ _ IH. eapply compat_CE1. eassumption.
          - intros ψ _ IH. eapply compat_CE2. eassumption.
          - intros ψ _ IH. apply compat_DI1. assumption.
          - intros ψ _ IH. apply compat_DI2. assumption.
          - intros ψ τ _ IH1 _ IH2 _ IH3. eapply compat_DE; eassumption.
          - apply compat_Pc.
  Qed.

  Section SoundnessLemmas.

    (** ** Soundness Lemmas *)

    Context {p: peirce}.

    Lemma sound_HK A φ ψ:
      A ⊢ φ → ψ → φ.
    Proof.
      fstart. fintros "Hφ" "Hψ". fapply "Hφ".
    Qed.

    Lemma sound_HS A φ ψ τ:
      A ⊢ (φ → ψ → τ) → (φ → ψ) → φ → τ.
    Proof.
      fstart. fintros "f" "g" "Hφ". fapply "f".
        - fapply "Hφ".
        - fapply "g". fapply "Hφ".
    Qed.

    Lemma sound_CI A φ ψ:
      A ⊢ φ → ψ → φ ∧ ψ.
    Proof.
      fstart. fintros "Hφ" "Hψ". fsplit.
        - fapply "Hφ".
        - fapply "Hψ".
    Qed.

    Lemma sound_CE1 A φ ψ:
      A ⊢ φ ∧ ψ → φ.
    Proof.
      fstart. fintros "[Hφ Hψ]". fapply "Hφ".
    Qed.

    Lemma sound_CE2 A φ ψ:
      A ⊢ φ ∧ ψ → ψ.
    Proof.
      fstart. fintros "[Hφ Hψ]". fapply "Hψ".
    Qed.

    Lemma sound_DI1 A φ ψ:
      A ⊢ φ → (φ ∨ ψ).
    Proof.
      fstart. fintros "Hφ". fleft. fapply "Hφ".
    Qed.

    Lemma sound_DI2 A φ ψ:
      A ⊢ ψ → (φ ∨ ψ).
    Proof.
      fstart. fintros "Hψ". fright. fapply "Hψ".
    Qed.

    Lemma sound_DE A φ ψ τ:
      A ⊢ φ ∨ ψ → (φ → τ) → (ψ → τ) → τ.
    Proof.
      fstart. fintros "[Hφ|Hψ]"; fintros "f" "g".
        - fapply "f". fapply "Hφ".
        - fapply "g". fapply "Hψ".
    Qed.

    Lemma sound_Ebot A φ:
      A ⊢ ⊥ → φ.
    Proof.
      fstart. fintros "H⊥". fexfalso. fapply "H⊥".
    Qed.

    Lemma sound_AllE A φ t:
      A ⊢ (∀ φ) → φ[t..].
    Proof.
      fstart. fintros "Hφ". fapply "Hφ".
    Qed.

    Lemma sound_AllG A φ:
      A ⊢ φ → ∀ φ[↑].
    Proof.
      fstart. fintros "Hφ" x. fapply "Hφ".
    Qed.

    Lemma sound_AllD A φ ψ:
      A ⊢ (∀ φ → ψ) → (∀ φ) → ∀ ψ.
    Proof.
      fstart. fintros "Himpl" "Hφ" x.
      fspecialize ("Himpl" x). fapply "Himpl".
      fapply "Hφ".
    Qed.

    Lemma sound_ExI A φ t:
      A ⊢ φ[t..] → ∃ φ.
    Proof.
      fstart. fintros "Hφ". fexists t. fapply "Hφ".
    Qed.

    Lemma sound_ExE A φ ψ:
      A ⊢ (∃ φ) → (∀ φ → ψ[↑]) → ψ.
    Proof.
      fstart. fintros "[x Hφ]" "f". fapply ("f" x).
      fapply "Hφ".
    Qed.

    Lemma sound_PC A φ ψ:
      A ⊢C (((φ → ψ) → φ) → φ).
    Proof.
      apply Pc.
    Qed.

    Lemma empty_context_AllI φ:
      nil ⊢ φ -> nil ⊢ ∀ φ.
    Proof.
      intros Hall. apply AllI. cbn. assumption.
    Qed.

    Corollary empty_context_forall_times_intro φ n:
      nil ⊢ φ -> nil ⊢ forall_times n φ.
    Proof.
      intros Hφ. induction n as [| n IH]; cbn.
        - assumption.
        - apply empty_context_AllI. assumption.
    Qed.

    Lemma quantifed_hilAx_derivable φ n:
      hilAx p φ -> nil ⊢ forall_times n φ.
    Proof.
      intros Hax. apply empty_context_forall_times_intro. inversion Hax.
        - apply sound_HK.
        - apply sound_HS.
        - apply sound_CI.
        - apply sound_CE1.
        - apply sound_CE2.
        - apply sound_DI1.
        - apply sound_DI2.
        - apply sound_DE.
        - apply sound_Ebot.
        - apply sound_AllE.
        - apply sound_AllG.
        - apply sound_AllD.
        - apply sound_ExI.
        - apply sound_ExE.
        - apply sound_PC.
    Qed.

  End SoundnessLemmas.

  (** ** Equivalence Proof *)

  Theorem Hil_to_ND (p: peirce) φ A:
    A ⊢H φ -> A ⊢ φ.
  Proof.
    induction 1 as [φ ψ p' _ IH1 _ IH2 | φ n Hφ | φ Hincl].
      - eapply IE; eassumption.
      - eapply Weak.
        + eapply quantifed_hilAx_derivable. assumption.
        + easy.
      - apply Ctx. assumption.
  Qed.

  Corollary Hil_ND_agree (p: peirce) φ A:
    A ⊢H φ <-> A ⊢ φ.
  Proof.
      split.
      - apply Hil_to_ND.
      - intros Hφ. apply (@ND_to_Hil p _ _); assumption.
  Qed.

  Corollary Hil_ND_agree_theories (p: peirce) φ T:
    T ⊢HT φ <-> T ⊢T φ.
  Proof.
    split.
      - intros [A [HA HDer]]. exists A. split; first assumption.
        apply Hil_ND_agree; assumption.
      - intros [A [HA Hder]]. exists A. split; first eassumption.
        destruct (Hil_ND_agree p φ A). easy.
  Qed.

End ND_Hil_equiv.



