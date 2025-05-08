From FOL Require Import FullSyntax Arithmetics ProofMode.
From FOL.Incompleteness Require Import Axiomatisations sigma1 qdec utils.
From Undecidability.FOL.Utils Require Import FriedmanTranslation.
Require Import Lia.
(** * Utilities *)
(** ** Translation between Classical and Intuitionistic Reasoning *)
Section Translations.

    Existing Instance PA_funcs_signature.
    Existing Instance PA_preds_signature.
    Existing Instance full_operators.
    Existing Instance falsity_on.

    Lemma Σ1_convervativity' {pei: peirce} (ϕ: form):
        Σ1 ϕ -> bounded 0 ϕ -> Qeq ⊢C ϕ -> Qeq ⊢ ϕ.
    Proof.
        intros HΣ1 HB Hclass. destruct pei; first assumption.
        apply Σ1_conservativity; assumption.
    Qed.

    Lemma peirce_to_class {pei: peirce} (ϕ: form) T:
        T ⊢ ϕ -> T ⊢C ϕ.
    Proof.
        destruct pei; first easy. apply prv_intu_peirce.
    Qed.

    Lemma peirce_to_class_theory {pei: peirce} (ϕ: form) T:
        T ⊢T ϕ -> T ⊢TC ϕ.
    Proof.
        intros [L HL]. exists L. split; first easy.
        now apply peirce_to_class.
    Qed.

End Translations.
(** ** Utilities on Robinson Arithmetic *)
Section Robinson_facts.
    
    Existing Instance PA_funcs_signature.
    Existing Instance PA_preds_signature.
    Existing Instance full_operators.
    Existing Instance falsity_on.

    Lemma Qeq_consistent {p: peirce}:
        ~Qeq ⊢ ⊥.
    Proof.
        intros HderBot. enough (FalseSat: interp_nat ⊨= ⊥).
        - cbn in FalseSat. apply FalseSat. easy.
        - apply Σ1_soundness. 2-3: try constructor; auto.
          constructor. apply Qdec_bot.
    Qed.

    Lemma Qeq_generalisation {p: peirce} φ:
        Qeq ⊢ φ -> Qeq ⊢ ∀ φ.
    Proof.
        intros Hφ. apply AllI. 
        now assert (List.map (subst_form ↑) Qeq = Qeq) as -> by easy.
    Qed.

End Robinson_facts.

(** ** Utilities for Formulas *)
Lemma subst_bound_1 {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} {ops : operators} {flag : falsity_flag} 
    (ψ: form) (x: term) (sigma: nat -> term):
    bounded 1 ψ -> ψ[x..] = ψ[x .: sigma].
Proof.
    intro HBound. eapply bounded_subst; first eassumption.
    intros k Hk. destruct k; first easy. lia.
Qed.
      
Lemma subst_bound_2 {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} {ops : operators} {flag : falsity_flag} 
    (ψ: form) (x y: term) (sigma: nat -> term):
    bounded 2 ψ -> ψ[x .: y..] = ψ[x .: y .: sigma].
Proof.
    intro HBound. eapply bounded_subst; first eassumption.
    intros k Hk. destruct k; first easy.
    destruct k; first easy. lia.
Qed.

Inductive aand (P Q R : Prop) :=
      cconj : P -> Q -> R -> aand P Q R.

Lemma form_inv {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} {ops : operators} {flag : falsity_flag} phi1 phi2 :
      phi1 = phi2 ->
      match phi1, phi2 with
      | falsity, falsity => True
      | atom _ P1 args1, atom _ P2 args2 => True
      | bin falsity_on o1 phi1' phi2', bin falsity_on o2 phi1'' phi2'' =>
            aand (o1 = o2) (phi1' = phi1'') (phi2' = phi2'')
      | bin falsity_off o1 phi1' phi2', bin falsity_off o2 phi1'' phi2'' =>
          aand (o1 = o2) (phi1' = phi1'') (phi2' = phi2'')
      | quant falsity_on o1 phi, quant falsity_on o2 phi' =>
            o1 = o2 /\ phi = phi'
      | quant falsity_off o1 phi, quant falsity_off o2 phi' =>
          o1 = o2 /\ phi = phi'
      | _, _ => False
      end.
Proof.
      intros H. destruct phi1; subst; eauto.
      all: destruct b; econstructor; eauto.
Qed.

Section Formula_facts.

    Existing Instance PA_funcs_signature.
    Existing Instance PA_preds_signature.
    Existing Instance full_operators.

    Definition impl_dec {ff: falsity_flag}:
        forall (φ ψ: form), {τ & ψ = τ → φ} + ({τ & ψ = τ → φ} -> False).
    Proof.
        intros φ ψ. destruct ψ as [| ff P ts | ff b τ χ | ff q τ].
            * right. intros [τ Hτ]. congruence.
            * right. intros [τ Hτ]. congruence.
            * destruct b. 1-2: right; intros [τ' Hτ']; congruence.
              destruct (dec_form _ _ _ _  χ φ).
                + left. exists τ. congruence.
                + right. intros [τ' Hτ']. apply n.
                  destruct ff; eapply form_inv in Hτ' as []; congruence.
            * right. intros [τ' Hτ']. congruence.
    Qed.

    Lemma list_theory_provability {p: peirce} {ff: falsity_flag} A φ:
    A ⊢ φ <-> list_theory A ⊢T φ.
    Proof.
        split; intros H.
        - exists A. eauto.
        - destruct H as [B [HBIncl HBderiv]]. eapply Weak; first eassumption.
        eauto.
    Qed.
    
End Formula_facts.